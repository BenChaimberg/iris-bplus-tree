From iris.algebra Require Import numbers.
From iris.heap_lang Require Export proofmode notation.
From iris.proofmode Require Export proofmode.
From iris.prelude Require Import options.
Require Import NaryTree.
Require Import BPlusTree.

Section nary_tree.
  Context (b : nat).

  Fixpoint insert_list_spec (target : Z) (l : list Z) : list Z :=
    match l with
    | [] => [target]
    | x :: xs => if Z.eqb x target
               then x :: xs
               else if Z.ltb x target
                    then x :: insert_list_spec target xs
                    else target :: x :: xs
    end.

    Fixpoint insert_nary_tree_spec (target : Z) (t : nary_tree) : nary_tree * option nary_tree :=
      match t with
      | leaf (low, high) vals =>
          let new_vals := insert_list_spec target vals in
          if Z.ltb b (length new_vals)
          then
            let left_vals := firstn (b/2) new_vals in
            let right_vals := skipn (b/2) new_vals in
            let left_interval := (hd low left_vals, List.last left_vals high) in
            let right_interval := (hd low right_vals, List.last right_vals high) in
            (leaf left_interval left_vals, Some (leaf right_interval right_vals))
          else
            (leaf (hd low new_vals, List.last new_vals high) new_vals, None)
      | node (low, high) branches =>
          let new_branches :=
            ((fix insert_aux (l : list nary_tree) :=
                match l with
                | [] => []
                | t :: [] =>
                    let (new_t1, new_t2) := insert_nary_tree_spec target t in
                    match new_t2 with
                    | None => [new_t1]
                    | Some new_t2' => new_t1 :: [new_t2']
                    end
                | t :: ts =>
                    let (low, high) := nary_tree_interval t in
                    if andb (Z.leb low target) (Z.leb target high)
                    then let (new_t1, new_t2) := insert_nary_tree_spec target t in
                         match new_t2 with
                         | None => new_t1 :: ts
                         | Some new_t2' => new_t1 :: new_t2' :: ts
                         end
                    else t :: insert_aux ts
                end) branches) in
          if Z.ltb b (length new_branches)
          then
            let left_branches := firstn (b/2) new_branches in
            let right_branches := skipn (b/2) new_branches in
            let left_interval_low :=
              match head (map fst (map nary_tree_interval left_branches)) with
              | None => low
              | Some x => x
              end
            in
            let left_interval_high :=
              match last (map snd (map nary_tree_interval left_branches)) with
              | None => high
              | Some x => x
              end
            in
            let right_interval_low :=
              match head (map fst (map nary_tree_interval right_branches)) with
              | None => low
              | Some x => x
              end
            in
            let right_interval_high :=
              match last (map snd (map nary_tree_interval right_branches)) with
              | None => high
              | Some x => x
              end
            in
            (node (left_interval_low, left_interval_high) left_branches,
              Some (node (right_interval_low, right_interval_high) right_branches))
          else
            let new_low :=
              match head (map fst (map nary_tree_interval new_branches)) with
              | None => low
              | Some x => x
              end
            in
            let new_high :=
              match last (map snd (map nary_tree_interval new_branches)) with
              | None => high
              | Some x => x
              end
            in
            (node (new_low, new_high) new_branches, None)
      end.

  (* Definition insert_bplus_tree_spec (target : Z) (t : bplus_tree) := *)
  (*   match t with *)
  (*   | root_leaf (low, high) vals => *)
  (*       let new_vals := insert_list_spec target vals in *)
  (*       if Z.ltb b (length new_vals) *)
  (*       then *)
  (*         let left_vals := firstn (b/2) new_vals in *)
  (*         let right_vals := skipn (b/2) new_vals in *)
  (*         let left_interval := (low, List.last left_vals high) in *)
  (*         let right_interval := (hd low right_vals, high) in *)
  (*         (* TODO: should change interval *) *)
  (*         root_node (low, high) (leaf left_interval left_vals :: [leaf right_interval right_vals]) *)
  (*       else *)
  (*         root_leaf (low, high) new_vals *)
  (*   | root_node interval branches => *)
  (*       let new_branches := *)
  (*         ((fix insert_aux (l : list nary_tree) := *)
  (*             match l with *)
  (*             | [] => [] *)
  (*             | t :: ts => *)
  (*                 let (low, high) := (match t with leaf interval _ | node interval _ => interval end) in *)
  (*                 if andb (Z.leb low target) (Z.leb target high) *)
  (*                 then *)
  (*                   let (new_t1, new_t2) := insert_nary_tree_spec target t in *)
  (*                   match new_t2 with *)
  (*                   | None => new_t1 :: ts *)
  (*                   | Some new_t2' => new_t1 :: new_t2' :: ts *)
  (*                   end *)
  (*                 else t :: insert_aux ts *)
  (*             end) branches) in *)
  (*       (* TODO: should change interval *) *)
  (*       if Z.leb b (length new_branches) *)
  (*       then *)
  (*         root_node interval *)
  (*           ([node interval (firstn (b/2) new_branches)] ++ [node interval (skipn (b/2) new_branches)]) *)
  (*       else *)
  (*         root_node interval branches *)
  (*   end. *)
End nary_tree.

Section bplus_tree.
  Section bplus_tree_algos.
    Context (b : nat).

    Definition insert_list : val :=
      rec: "insert_list" "arg" :=
        let: "p" := Fst "arg" in
        let: "target" := Snd "arg" in
        match: "p" with
          NONE =>
            let: "ptr" := ref ("target", NONEV) in
            SOME "ptr"
        | SOME "l" =>
            let: "val" := Fst !"l" in
            if: "val" = "target"
            then SOME "l"
            else
              if: (BinOp LtOp "val" "target")
              then let: "new" := "insert_list" (Snd !"l", "target") in
                   "l" <- ("val", "new");;
                   SOME "l"
              else SOME (ref ("target", SOME "l"))
        end.

    Definition length_list : val :=
      rec: "length_list" "p" :=
        match: "p" with
          NONE => #0
        | SOME "l" => #1 + "length_list" (Snd !"l")
        end.

    Definition split_list : val :=
      rec: "split_list" "arg" :=
        let: "p" := Fst "arg" in
        let: "n" := Snd "arg" in
        if: "n" = #0
        then (NONEV, "p")
        else
          match: "p" with
            NONE => (NONEV, NONEV)
          | SOME "l" =>
              let: "x" := Fst !"l" in
              let: "rest" := Snd !"l" in
              let: "rec" := "split_list" ("rest", "n" - #1) in
              "l" <- ("x", Fst "rec") ;;
              (SOME "l", Snd "rec")
          end.

    Definition head_list : val :=
      rec: "head_list" "arg" :=
        match: Fst "arg" with
          NONE => Snd "arg"
        | SOME "l" => Fst !"l"
        end.

    Definition last_list : val :=
      rec: "last_list" "arg" :=
        match: Fst "arg" with
          NONE => Snd "arg"
        | SOME "l" =>
            match: Snd !"l" with
              NONE => Fst !"l"
            | SOME "l'" => "last_list" (SOME "l'", Snd "arg")
            end
        end.

    Definition headopt_list : val :=
      rec: "headopt_list" "l" :=
        match: "l" with
          NONE => NONE
        | SOME "l" => SOME (Fst !"l")
        end.

    Definition lastopt_list : val :=
      rec: "lastopt_list" "l" :=
        match: "l" with
          NONE => NONE
        | SOME "l" =>
            match: Snd !"l" with
              NONE => SOME (Fst !"l")
            | SOME "l'" => "lastopt_list" (SOME "l'")
            end
        end.

    Definition interval_nary_tree : val :=
      rec: "interval_nary_tree" "t" :=
        match: "t" with
          InjL "ptr" => Fst !"ptr"
        | InjR "ptr" => Fst !"ptr"
        end.

    Definition insert_nary_tree : val :=
      rec: "insert_nary_tree" "arg" :=
        let: "t" := Fst "arg" in
        let: "target" := Snd "arg" in
        match: "t" with
          InjL "ptr" =>
            let: "lhd" := Snd !"ptr" in
            let: "interval" := Fst !"ptr" in
            let: "new" := insert_list ("lhd", "target") in
            if: #b < length_list "new"
            then
              let: "newlpair" := split_list ("new", #(b/2)) in
              let: "newhead1" := head_list (Fst "newlpair", Fst "interval") in
              let: "newlast1" := last_list (Fst "newlpair", Snd "interval") in
              let: "newhead2" := head_list (Snd "newlpair", Fst "interval") in
              let: "newlast2" := last_list (Snd "newlpair", Snd "interval") in
              let: "newleaf" := ref (("newhead2", "newlast2"), Snd "newlpair") in
              "ptr" <- (("newhead1", "newlast1"), Fst "newlpair") ;;
              (token_leaf_e "ptr", SOME (token_leaf_e "newleaf"))
            else
              let: "head" := head_list ("new", Fst "interval") in
              let: "last" := last_list ("new", Snd "interval") in
              "ptr" <- (("head", "last"), "new") ;;
              (token_leaf_e "ptr", NONEV)
        | InjR "ptr" =>
            let: "lhd" := Snd !"ptr" in
            let: "new" :=
              (rec: "insert_node_list" "arg" :=
                 let: "p" := Fst "arg" in
                 let: "target" := Snd "arg" in
                 match: "p" with
                   NONE =>
                     NONE
                 | SOME "l" =>
                     match: Snd !"l" with
                       NONE =>
                         let: "newt" := "insert_nary_tree" (Fst !"l", "target") in
                         match: Snd "newt" with
                           NONE => "l" <- (Fst "newt", NONE)
                         | SOME "newt2" =>
                             let: "l'" := ref ("newt2", NONE) in
                             "l" <- (Fst "newt", SOME "l'")
                         end
                     | SOME "_" =>
                         let: "thd" := Fst !"l" in
                         let: "interval" := interval_nary_tree "thd" in
                         let: "low" := Fst "interval" in
                         let: "high" := Snd "interval" in
                         (if: (BinOp LeOp "low" "target") && (BinOp LeOp "target" "high")
                          then let: "newt" := "insert_nary_tree" ("thd", "target") in
                               match: Snd "newt" with
                                 NONE => "l" <- (Fst "newt", Snd !"l")
                               | SOME "newt2" =>
                                   let: "l'" := ref ("newt2", Snd !"l") in
                                   "l" <- (Fst "newt", SOME "l'")
                               end
                          else let: "newl" := "insert_node_list" (Snd !"l", "target") in
                               "l" <- ("thd", "newl"))
                     end ;; SOME "l"
                 end) ("lhd", "target") in
            let: "interval" := Fst !"ptr" in
            if: #b < length_list "new"
            then
              let: "newlpair" := split_list ("new", #(b/2)) in
              let: "newheadleft" :=
                match: headopt_list (Fst "newlpair") with
                  NONE => Fst "interval"
                | SOME "t" => Fst (interval_nary_tree "t")
                end in
              let: "newlastleft" :=
                match: lastopt_list (Fst "newlpair") with
                  NONE => Snd "interval"
                | SOME "t" => Snd (interval_nary_tree "t")
                end in
              let: "newheadright" :=
                match: headopt_list (Snd "newlpair") with
                  NONE => Fst "interval"
                | SOME "t" => Fst (interval_nary_tree "t")
                end in
              let: "newlastright" :=
                match: lastopt_list (Snd "newlpair") with
                  NONE => Snd "interval"
                | SOME "t" => Snd (interval_nary_tree "t")
                end in
              let: "newbranch" := ref (("newheadright", "newlastright"), Snd "newlpair") in
              "ptr" <- (("newheadleft", "newlastleft"), Fst "newlpair") ;;
              (token_branch_e "ptr", SOME (token_branch_e "newbranch"))
            else
              let: "newhead" :=
                match: headopt_list "new" with
                  NONE => Fst "interval"
                | SOME "t" => Fst (interval_nary_tree "t")
                end in
              let: "newlast" :=
                match: lastopt_list "new" with
                  NONE => Snd "interval"
                | SOME "t" => Snd (interval_nary_tree "t")
                end in
              "ptr" <- (("newhead", "newlast"), "new") ;;
              (token_branch_e "ptr", NONEV)
        end%E.

  End bplus_tree_algos.

  Section bplus_tree_proofs.
    Context `{!heapGS Σ}.
    Notation iProp := (iProp Σ).

    Variable b : nat.
    Hypothesis beven : Zeven b.
    Hypothesis bpos : 0 < b.
    Lemma bge2 : 2 <= b.
    Proof using beven bpos.
      induction b using nat_strong_ind.
      destruct n; [lia|].
      destruct n.
      { unfold Zeven in beven.
        unfold Z.of_nat in beven.
        unfold Pos.of_succ_nat in beven.
        done. }
      lia.
    Qed.

    Lemma insert_list_spec_proof (v : val) (l : list tval) (target : tval):
      {{{ is_list v (map (fun (x : tval) => #x) l) }}} insert_list (v, (#target))%V {{{ r, RET r; is_list r (map (fun (x : tval) => #x) (insert_list_spec target l)) }}}.
    Proof.
      clear bpos.
      iIntros (Φ) "Hl HPost".
      iInduction l as [|x l] "IH" forall (Φ v); wp_rec; wp_pures.
      - iDestruct "Hl" as "->".
        wp_alloc ptr as "Hptr"; wp_pures.
        iApply "HPost".
        iExists ptr, (InjLV #()).
        iFrame.
        done.
      - iDestruct "Hl" as (l' ?) "(-> & Hl' & Hl)".
        wp_match; wp_load; wp_pures.
        destruct (bool_decide (#x = #target)) eqn:?.
        + wp_pures.
          iApply "HPost".
          cbn; rewrite (bool_decide_true_Zeqb _ _ Heqb0).
          iExists l', hd'.
          iFrame.
          done.
        + wp_pures.
          destruct (bool_decide (Z.lt x target)) eqn:?; wp_pures.
          * wp_bind (insert_list _); wp_load; wp_pures.
            iApply ("IH" with "[Hl]"); [done|].
            iNext.
            iIntros (?) "Hr".
            wp_store; wp_pure.
            iApply "HPost".
            unfold insert_list_spec.
            rewrite (bool_decide_false_Zeqb _ _ Heqb0).
            rewrite bool_decide_eq_true in Heqb1;
              apply Z.ltb_lt in Heqb1;
              rewrite Heqb1.
            iExists l', r.
            iFrame.
            done.
          * wp_alloc new as "Hnew"; wp_pure.
            iApply "HPost".
            unfold insert_list_spec;
              specialize (bool_decide_false_Zeqb _ _ Heqb0) as ?;
              rewrite bool_decide_eq_false in Heqb1;
              assert (Z.le target x) by lia;
              apply Z.leb_le in H0;
              rewrite Z.leb_antisym in H0;
              symmetry in H0;
              apply negb_sym in H0;
              cbn in H0;
              rewrite H H0.
            iExists new, (InjRV #l').
            iFrame.
            iSplitR; [done|].
            iExists l', hd'.
            iFrame.
            done.
    Qed.

    Lemma length_list_spec_proof (v : val) (l : list val):
      {{{ is_list v l }}} length_list v {{{ r, RET #r; ⌜r = Z.of_nat (length l)⌝ ∗ is_list v l }}}.
    Proof.
      iIntros (Φ) "Hl HPost".

      iInduction l as [] "IH" forall (Φ v).
      - iDestruct "Hl" as "->".
        wp_rec; wp_pures.
        iApply ("HPost" $! 0).
        done.
      - iDestruct "Hl" as (l' ?) "(-> & Hl' & Hl)".
        wp_rec; wp_load; wp_pure; wp_bind (length_list _).
        iApply ("IH" with "[Hl]"); [iFrame|].
        iNext.
        iIntros (?) "[-> Hl]".
        wp_pure.
        iApply ("HPost" $! (1 + length l)%Z).
        iSplitR;
          [ iPureIntro; rewrite Z.add_1_l Nat2Z.inj_succ; done
          | iExists l', hd'; iFrame; done ].
    Qed.

    Lemma firstn_nil {A} n : @firstn A n [] = [].
    Proof. induction n; done. Qed.

    Lemma skipn_nil {A} n : @skipn A n [] = [].
    Proof. induction n; done. Qed.

    Lemma split_list_spec_proof (v : val) (l : list val) (n : nat):
      {{{ is_list v l }}} split_list (v, #(Z.of_nat n))%V {{{ r, RET (r.1, r.2); is_list r.1 (firstn n l) ∗ is_list r.2 (skipn n l) }}}.
    Proof.
      clear bpos.
      iIntros (Φ) "Hl HPost".
      iInduction n as [] "IH" forall (Φ v l).
      - wp_rec; wp_pures.
        iApply ("HPost" $! (InjLV #(), v)).
        unfold take, drop.
        cbn.
        iFrame.
        done.
      - wp_rec; wp_pures;
          destruct l.
        + iDestruct "Hl" as "->".
          wp_pures.
          iApply ("HPost" $! (InjLV #(), InjLV #())).
          rewrite firstn_nil skipn_nil.
          done.

        + iDestruct "Hl" as (l' ?) "(-> & Hl' & Hl)".
          wp_load; wp_load; wp_pures; wp_bind (split_list _).
          replace (Z.sub (S n) 1) with (Z.of_nat n) by lia.
          iApply ("IH" with "[Hl]"); [done|].
          iNext.
          iIntros (?) "[Hr1 Hr2]".
          wp_store; wp_pures.
          iApply ("HPost" $! (InjRV #l', r.2)).
          iSplitL "Hl' Hr1"; [iExists l', r.1; iFrame; done|].
          done.
    Qed.

    Lemma head_list_spec_proof (v : val) (l : list val) (d : val):
      {{{ is_list v l }}} head_list (v, d)%V {{{ r, RET r; ⌜r = hd d l⌝ ∗ is_list v l }}}.
    Proof.
      iIntros (Φ) "Hl HPost".
      wp_lam; wp_pures.
      destruct l as [|x l].
      - iDestruct "Hl" as "->".
        wp_pures.
        iApply "HPost".
        done.
      - iDestruct "Hl" as (l' ?) "(-> & Hl' & Hl)".
        wp_load; wp_pures.
        iApply "HPost".
        iSplitR; [done|].
        iExists l', hd'.
        iFrame; done.
    Qed.

    Lemma last_list_spec_proof (v : val) (l : list val) (d : val):
      {{{ is_list v l }}} last_list (v, d)%V {{{ r, RET r; ⌜r = List.last l d⌝ ∗ is_list v l }}}.
    Proof.
      iIntros (Φ) "Hl HPost".
      iInduction l as [|x l] "IH" forall (v);
        wp_rec; wp_pures.
      - iDestruct "Hl" as "->".
        wp_pures.
        iApply "HPost".
        iFrame; done.
      - iDestruct "Hl" as (l' ?) "(-> & Hl' & Hl)".
        wp_load; wp_pures.
        destruct l as [|x' l].
        + iDestruct "Hl" as "->".
          wp_load; wp_pures.
          iApply "HPost".
          iSplitR; [done|].
          iExists l', NONEV.
          iFrame; done.
        + iDestruct "Hl" as (l'' ?) "(-> & Hl'' & Hl)".
          wp_pures.
          iApply ("IH" with "[Hl Hl'']"); [iExists l'', hd'0; iFrame; done|].
          iNext.
          iIntros (?) "[-> Hl'']".
          iApply "HPost".
          iSplitR; [done|].
          iExists l', (SOMEV #l'').
          iFrame; done.
    Qed.

    Lemma headopt_list_spec_proof (v : val) (l : list val):
      {{{ is_list v l }}} headopt_list v%V {{{ r, RET r; ⌜r = match head l with None => NONEV | Some x => SOMEV x end⌝ ∗ is_list v l }}}.
    Proof.
      iIntros (Φ) "Hl HPost".
      wp_lam; wp_pures.
      destruct l as [|x l].
      - iDestruct "Hl" as "->".
        wp_pures.
        iApply "HPost".
        done.
      - iDestruct "Hl" as (l' ?) "(-> & Hl' & Hl)".
        wp_load; wp_pures.
        iApply "HPost".
        iSplitR; [done|].
        iExists l', hd'.
        iFrame; done.
    Qed.

    Lemma lastopt_list_spec_proof (v : val) (l : list val):
      {{{ is_list v l }}} lastopt_list v%V {{{ r, RET r; ⌜r = match last l with None => NONEV | Some x => SOMEV x end⌝ ∗ is_list v l }}}.
    Proof.
      iIntros (Φ) "Hl HPost".
      iInduction l as [|x l] "IH" forall (v);
        wp_lam; wp_pures.
      - iDestruct "Hl" as "->".
        wp_pures.
        iApply "HPost"; done.
      - iDestruct "Hl" as (l' ?) "(-> & Hl' & Hl)".
        wp_load; wp_pures.
        destruct l as [|x' l].
        + iDestruct "Hl" as "->".
          wp_load; wp_pures.
          iApply "HPost".
          iSplitR; [done|].
          iExists l', NONEV.
          iFrame; done.
        + iDestruct "Hl" as (l'' ?) "(-> & Hl'' & Hl)".
          wp_pures.
          iApply ("IH" with "[Hl'' Hl]"); [iExists l'', hd'0; iFrame; done|].
          iNext.
          iIntros (?) "[% Hl'']".
          iApply "HPost".
          iSplitR; [done|].
          iExists l', (SOMEV #l''); iFrame; done.
    Qed.

    Lemma interval_nary_tree_spec_proof (v : val) (t : nary_tree) :
      {{{ is_node v t }}} interval_nary_tree v%V {{{ r, RET (#r.1, #r.2); is_node v t ∗ ⌜r = nary_tree_interval t⌝ }}}.
      iIntros (?) "Hv HPost".
      destruct t; destruct interval as [low high].
      - iDestruct "Hv" as (ptr leaves) "(-> & Hptr & Hleaves)".
        wp_rec; wp_load; wp_pures.
        iApply ("HPost" $! (low, high)).
        iSplitL; [iExists ptr, leaves; iFrame|]; done.
      - iDestruct "Hv" as (ptr ns branches) "(-> & Hptr & Hns & Hbranches)".
        wp_rec; wp_load; wp_pures.
        iApply ("HPost" $! (low, high)).
        iSplitL; [iExists ptr, ns, branches; iFrame|]; done.
    Qed.

    Lemma branch_node_list_lengths : forall ns ts,
      (fix branch_node_list (ns0 : list val) (ts0 : list nary_tree) {struct ts0} : iProp :=
         match ns0 with
         | [] => match ts0 with
                | [] => True
                | _ :: _ => False
                end
         | n :: ns1 =>
             match ts0 with
             | [] => False
             | t :: ts1 => is_node n t ∗ branch_node_list ns1 ts1
             end
         end) ns ts -∗
        (fix branch_node_list (ns0 : list val) (ts0 : list nary_tree) {struct ts0} : iProp :=
         match ns0 with
         | [] => match ts0 with
                | [] => True
                | _ :: _ => False
                end
         | n :: ns1 =>
             match ts0 with
             | [] => False
             | t :: ts1 => is_node n t ∗ branch_node_list ns1 ts1
             end
         end) ns ts ∗ ⌜length ns = length ts⌝.
    Proof.
      iIntros (? ?).
      iInduction ts as [|thd trest] "IH'" forall (ns);
        destruct ns as [|nhd nrest]; [done|done|done|].
      iIntros "[Hnhd Hnrest]".
      iDestruct ("IH'" with "Hnrest") as "[Hnrest %]".
      iSplitL; [iFrame|].
      cbn.
      rewrite H.
      done.
    Qed.

    Lemma branch_node_split n ns ts :
      (fix branch_node_list (ns1 : list val) (ts0 : list nary_tree) {struct ts0} : iProp :=
         match ns1 with
         | [] => match ts0 with
                | [] => True
                | _ :: _ => False
                end
         | n :: ns2 =>
             match ts0 with
             | [] => False
             | t :: ts1 => is_node n t ∗ branch_node_list ns2 ts1
             end
         end) ns ts -∗
        (fix branch_node_list (ns1 : list val) (ts0 : list nary_tree) {struct ts0} : iProp :=
           match ns1 with
           | [] => match ts0 with
                  | [] => True
                  | _ :: _ => False
                  end
           | n :: ns2 =>
               match ts0 with
               | [] => False
               | t :: ts1 => is_node n t ∗ branch_node_list ns2 ts1
               end
           end) (take n ns) (take n ts) ∗
        (fix branch_node_list (ns1 : list val) (ts0 : list nary_tree) {struct ts0} : iProp :=
           match ns1 with
           | [] => match ts0 with
                  | [] => True
                  | _ :: _ => False
                  end
           | n :: ns2 =>
               match ts0 with
               | [] => False
               | t :: ts1 => is_node n t ∗ branch_node_list ns2 ts1
               end
           end) (drop n ns) (drop n ts).
    Proof.
      iIntros "Hns".
      iInduction n as [] "IH" forall (ts ns); [repeat rewrite take_0; repeat rewrite drop_0; iFrame|].
      destruct ns as [|nhd nrest]; destruct ts as [|thd trest]; [repeat rewrite take_nil;done|done|done|].
      cbn; fold (@take val) (@take nary_tree) (@drop val) (@drop nary_tree).
      iDestruct "Hns" as "[Hnhd Hnrest]".
      iFrame.
      iApply "IH"; done.
    Qed.

    Lemma branch_node_snoc xs xlast ys ylast :
      ((fix branch_node_list (ns1 : list val) (ts0 : list nary_tree) {struct ts0} :
         iProp :=
          match ns1 with
          | [] => match ts0 with
                 | [] => True%I
                 | _ :: _ => False%I
                 end
          | n :: ns2 =>
              match ts0 with
              | [] => False%I
              | t :: ts1 => (is_node n t ∗ branch_node_list ns2 ts1)%I
              end
          end) (xs ++ [xlast]) (ys ++ [ylast]) -∗
         (fix branch_node_list (ns1 : list val) (ts0 : list nary_tree) {struct ts0} :
           iProp :=
            match ns1 with
            | [] => match ts0 with
                   | [] => True%I
                   | _ :: _ => False%I
                   end
            | n :: ns2 =>
                match ts0 with
                | [] => False%I
                | t :: ts1 => (is_node n t ∗ branch_node_list ns2 ts1)%I
                end
            end) xs ys ∗ is_node xlast ylast).
    Proof.
      iIntros "H".
      iInduction ys as [|y ys] "IH" forall (xs);
        destruct xs as [|x xs].
      - iDestruct "H" as "[? _]"; iFrame.
      - destruct xs; cbn; iDestruct "H" as "[_ ?]"; done.
      - destruct ys; cbn; iDestruct "H" as "[_ ?]"; done.
      - iDestruct "H" as "[Hxy H]".
        iEval (fold (@app val); fold (@app nary_tree)) in "H".
        iFrame.
        iApply ("IH" with "H").
    Qed.

    Lemma branch_node_snoc' xs xlast ys ylast :
      (fix branch_node_list (ns1 : list val) (ts0 : list nary_tree) {struct ts0} :
        iProp :=
         match ns1 with
         | [] => match ts0 with
                | [] => True%I
                | _ :: _ => False%I
                end
         | n :: ns2 =>
             match ts0 with
             | [] => False%I
             | t :: ts1 => (is_node n t ∗ branch_node_list ns2 ts1)%I
             end
         end) xs ys ∗ is_node xlast ylast -∗
        (fix branch_node_list (ns1 : list val) (ts0 : list nary_tree) {struct ts0} :
          iProp :=
           match ns1 with
           | [] => match ts0 with
                  | [] => True%I
                  | _ :: _ => False%I
                  end
           | n :: ns2 =>
               match ts0 with
               | [] => False%I
               | t :: ts1 => (is_node n t ∗ branch_node_list ns2 ts1)%I
               end
           end) (xs ++ [xlast]) (ys ++ [ylast]).
    Proof.
      iIntros "H".
      iInduction ys as [|y ys] "IH" forall (xs);
        destruct xs as [|x xs].
      - iDestruct "H" as "[_ ?]"; iFrame.
      - destruct xs; cbn; iDestruct "H" as "[? _]"; done.
      - destruct ys; cbn; iDestruct "H" as "[? _]"; done.
      - iDestruct "H" as "[[Hxy H] Hxylast]".
        iFrame.
        iApply ("IH" with "[$]").
    Qed.

    Lemma hd_map_comm {A B} (f : A -> B) (l : list A) (d : A) (fd : B) :
      fd = f d -> hd (fd) (map f l) = f (hd d l).
    Proof. destruct l; [done|auto]. Qed.

    Lemma head_map_comm {A B} (f : A -> B) (l : list A) :
      head (map f l) = match head l with None => None | Some x => Some (f x) end.
    Proof. destruct l; [done|auto]. Qed.

    Lemma Listlast_map_comm {A B} (f : A -> B) (l : list A) (d : A) (fd : B) :
      fd = f d -> List.last (map f l) fd = f (List.last l d).
    Proof.
      induction l; [done|].
      destruct l; [auto|done].
    Qed.

    Lemma last_map_comm {A B} (f : A -> B) (l : list A) :
      last (map f l) = match last l with None => None | Some x => Some (f x) end.
    Proof.
      induction l; [done|].
      destruct l; [auto|done].
    Qed.

    Lemma ge_1_S n :
      1 <= n -> exists m, n = S m.
    Proof.
      clear bpos.
      intros.
      destruct n; [lia|exists n; done].
    Qed.

    Lemma take_b2_cons {A} (l : list A) : b < length l -> (exists x l', take (b/2) l = x :: l').
    Proof using beven bpos.
      intro.
      assert (1 < 2) by lia.
      specialize (Nat.div_lt b 2 bpos H0) as b2ltb.
      specialize (take_length l (b/2)) as take_len.
      specialize (b2ge1 _ beven bpos) as ?.
      assert (0 < b/2) by lia.
      destruct (take (b/2) l);
        [ rewrite nil_length in take_len; lia | eauto ].
    Qed.

    Lemma take_b2_snoc {A} (l : list A) : b < length l -> (exists x l', take (b/2) l = l' ++ [x]).
    Proof using beven bpos.
      intro.
      assert (1 < 2) by lia.
      specialize (Nat.div_lt b 2 bpos H0) as b2ltb.
      specialize (take_length l (b/2)) as take_len.
      specialize (b2ge1 _ beven bpos) as ?.
      assert (0 < b/2) by lia.
      destruct (destruct_list_back (take (b/2) l)) as [[x [init ?]]|];
        subst; rewrite e in take_len; rewrite e;
        [ eauto | rewrite nil_length in take_len; lia ].
    Qed.

    Lemma drop_b2_cons {A} (l : list A) : b < length l -> (exists x l', drop (b/2) l = x :: l').
    Proof using bpos.
      intro.
      assert (1 < 2) by lia.
      specialize (Nat.div_lt b 2 bpos H0) as b2ltb.
      specialize (drop_length l (b/2)) as drop_len.
      destruct (drop (b/2) l);
        [ rewrite nil_length in drop_len; lia | eauto ].
    Qed.

    Lemma drop_b2_snoc {A} (l : list A) : b < length l -> (exists x l', drop (b/2) l = l' ++ [x]).
    Proof using bpos.
      intro.
      assert (1 < 2) by lia.
      specialize (Nat.div_lt b 2 bpos H0) as b2ltb.
      specialize (drop_length l (b/2)) as drop_len.
      destruct (destruct_list_back (drop (b/2) l)) as [[x [init ?]]|];
        subst; rewrite e in drop_len; rewrite e;
        [ eauto | rewrite nil_length in drop_len; lia ].
    Qed.

    Lemma cons_snoc {A} (l : list A) head tail : l = head :: tail -> exists init last, l = init ++ [last].
    Proof.
      destruct (destruct_list_back l) as [[last [init ?]]|];
        intro; subst;
        [exists init, last|]; done.
    Qed.

    Lemma Z2N_b2 : Z.div b 2 = Z.of_nat (b / 2).
    Proof. symmetry; apply Znat.Nat2Z.inj_div. Qed.

    Lemma insert_nary_tree_spec_proof (t : nary_tree) (t_wf : nary_tree_wf_no_len b t) (v : val) (target : tval) :
      {{{ is_node v t }}}
        insert_nary_tree (v, #target)%V
        {{{ r, RET (r.1, r.2);
            is_node r.1 (insert_nary_tree_spec target t).1 ∗
              ((∃ (t2 : nary_tree),
                   ⌜(insert_nary_tree_spec target t).2 = Some t2⌝ ∗
                     ∃ (r2 : val), ⌜r.2 = SOMEV r2⌝ ∗ is_node r2 t2) ∨
                 (⌜(insert_nary_tree_spec target t).2 = None⌝ ∗ ⌜r.2 = NONEV⌝))
        }}}.
    Proof using bpos beven.
      iIntros (Φ) "Hv HPost".

      iInduction t as [(low & high)|(low & high) ts] "IH" using nary_tree_ind' forall (Φ v).
      - iPoseProof (tree_leaf_token_leaf with "Hv") as (?) "->".
        iDestruct "Hv" as (? ?) "(% & Hptr & Hlhd)".
        assert (x = #ptr) by (unfold token_leaf_v in H; congruence); subst; clear H.
        wp_rec; wp_load; wp_load; wp_pures; wp_bind (insert_list _).
        iApply (insert_list_spec_proof with "Hlhd").
        iNext.
        iIntros (?) "Hr".
        wp_pures; wp_bind (length_list _).
        iApply (length_list_spec_proof with "Hr").
        iNext.
        iIntros (?) "[% Hr]".
        wp_pure.
        destruct (bool_decide (Z.lt b r0)) eqn:?.
        + wp_pures.
          rewrite Z2N_b2.
          wp_bind (split_list _);
            iApply (split_list_spec_proof with "Hr");
            iNext;
            iIntros (?) "[Hr1 Hr2]".
          wp_pures;
            wp_bind (head_list _);
            iApply (head_list_spec_proof with "Hr1");
            iNext;
            iIntros (?) "[-> Hr1]".
          wp_pures;
            wp_bind (last_list _);
            iApply (last_list_spec_proof with "Hr1");
            iNext;
            iIntros (?) "[-> Hr1]".
          wp_pures;
            wp_bind (head_list _);
            iApply (head_list_spec_proof with "Hr2");
            iNext;
            iIntros (?) "[-> Hr2]".
          wp_pures;
            wp_bind (last_list _);
            iApply (last_list_spec_proof with "Hr2");
            iNext;
            iIntros (?) "[-> Hr2]".

          wp_alloc ptr' as "Hptr'"; wp_store; wp_pures.
          iApply ("HPost" $! (InjLV #ptr, InjRV (InjLV #ptr'))).
          rewrite map_length in H; subst r0.
          rewrite bool_decide_eq_true in Heqb0;
            apply Z.ltb_lt in Heqb0.
          repeat rewrite firstn_map;
            repeat rewrite skipn_map;
            rewrite (hd_map_comm _ _ low _ eq_refl);
            rewrite (Listlast_map_comm _ _ high _ eq_refl).
          iSplitL "Hptr Hr1".
          { cbn; rewrite Heqb0.
            iExists ptr, r1.1.
            iSplitR; [done|].
            iSplitL "Hptr"; done. }
          iLeft.
          remember (insert_list_spec target vals) as new_vals.
          iExists (leaf (hd low (drop (b/2) new_vals), List.last (drop (b/2) new_vals) high) (drop (b/2) new_vals)).
          iSplitR; [cbn; rewrite <- Heqnew_vals; rewrite Heqb0; done|].
          iExists (InjLV #ptr').
          iSplitR; [done|].
          iExists ptr', r1.2.
          repeat rewrite firstn_map;
            repeat rewrite skipn_map;
            rewrite (hd_map_comm _ _ low _ eq_refl);
            rewrite (Listlast_map_comm _ _ high _ eq_refl).
          iFrame; done.

        + wp_pures;
            wp_bind (head_list _);
            iApply (head_list_spec_proof with "Hr");
            iNext;
            iIntros (?) "[-> Hr]".
          wp_pures;
            wp_bind (last_list _);
            iApply (last_list_spec_proof with "Hr");
            iNext;
            iIntros (?) "[-> Hr]".

          wp_store; wp_pures.
          iApply ("HPost" $! (token_leaf_v #ptr, NONEV)).
          apply bool_decide_eq_false_1 in Heqb0;
              assert (Z.le r0 b) by lia;
              apply Z.leb_le in H0;
              rewrite Z.leb_antisym in H0;
              symmetry in H0;
              apply negb_sym in H0;
              cbn in H0.
          rewrite map_length in H; subst r0.
          iSplitL.
          { unfold insert_nary_tree_spec.
            rewrite H0.
            iExists ptr, r.
            rewrite (hd_map_comm _ _ low _ eq_refl);
              rewrite (Listlast_map_comm _ _ high _ eq_refl).
            iFrame; done. }
          iRight.
          cbn.
          rewrite H0.
          done.

      - iPoseProof (tree_node_token_branch with "Hv") as (?) "->".
        iDestruct "Hv" as (ptr lhd ns) "(% & Hptr & Hlhd & Hns)"; fold is_node.
        assert (x = #ptr) by (unfold token_branch_v in H; congruence); subst.
        wp_rec; wp_load; wp_proj; wp_let; wp_pure; wp_pure.
        iEval (cbn) in "HPost".

        wp_bind ((rec: "insert_node_list" "arg" := _) (lhd, #target))%V.
        iAssert (
            ∀ Φ',
              is_list lhd ns ∗
                (fix branch_node_list (ns0 : list val) (ts0 : list nary_tree) {struct ts0} : iProp :=
                   match ns0 with
                   | [] => match ts0 with
                          | [] => True
                          | _ :: _ => False
                          end
                   | n :: ns1 =>
                       match ts0 with
                       | [] => False
                       | t :: ts1 => is_node n t ∗ branch_node_list ns1 ts1
                       end
                   end) ns ts -∗
                (∀ r : val,
                    (∃ ns,
                        is_list r ns ∗
                          (fix branch_node_list (ns0 : list val) (ts0 : list nary_tree) {struct ts0} : iProp :=
                             match ns0 with
                             | [] => match ts0 with
                                    | [] => True
                                    | _ :: _ => False
                                    end
                             | n :: ns1 =>
                                 match ts0 with
                                 | [] => False
                                 | t :: ts1 => is_node n t ∗ branch_node_list ns1 ts1
                                 end
                             end) ns
                          ((fix insert_aux (l : list nary_tree) : list nary_tree :=
                              match l with
                              | [] => []
                              | [t] =>
                                  let (new_t1, new_t2) := insert_nary_tree_spec target t in
                                  match new_t2 with
                                  | Some new_t2' => [new_t1; new_t2']
                                  | None => [new_t1]
                                  end
                              | t :: (_ :: _) as ts0 =>
                                  let (low0, high0) := nary_tree_interval t in
                                  if (low0 <=? target)%Z && (target <=? high0)%Z
                                  then
                                    let (new_t1, new_t2) := insert_nary_tree_spec target t in
                                    match new_t2 with
                                    | Some new_t2' => new_t1 :: new_t2' :: ts0
                                    | None => new_t1 :: ts0
                                    end
                                  else t :: insert_aux ts0
                              end) ts)) -∗ Φ' r) -∗
                WP (rec: "insert_node_list" "arg" :=
                 let: "p" := Fst "arg" in
                 let: "target" := Snd "arg" in
                 match: "p" with
                   NONE =>
                     NONE
                 | SOME "l" =>
                     match: Snd !"l" with
                       NONE =>
                         let: "newt" := insert_nary_tree (Fst !"l", "target") in
                         match: Snd "newt" with
                           NONE => "l" <- (Fst "newt", NONE)
                         | SOME "newt2" =>
                             let: "l'" := ref ("newt2", NONE) in
                             "l" <- (Fst "newt", SOME "l'")
                         end
                     | SOME "_" =>
                         let: "thd" := Fst !"l" in
                         let: "interval" := interval_nary_tree "thd" in
                         let: "low" := Fst "interval" in
                         let: "high" := Snd "interval" in
                         (if: (BinOp LeOp "low" "target") && (BinOp LeOp "target" "high")
                          then let: "newt" := insert_nary_tree ("thd", "target") in
                               match: Snd "newt" with
                                 NONE => "l" <- (Fst "newt", Snd !"l")
                               | SOME "newt2" =>
                                   let: "l'" := ref ("newt2", Snd !"l") in
                                   "l" <- (Fst "newt", SOME "l'")
                               end
                          else let: "newl" := "insert_node_list" (Snd !"l", "target") in
                               "l" <- ("thd", "newl"))
                     end ;; SOME "l"
                 end)%V (lhd, #target)%V
                {{ v, Φ' v}}
          )%I as "IH'".
        { iIntros (Φ') "[Hlhd Hns] HPost".
          inversion_clear t_wf
            as [| ? ? ? ? _ _ trees_wf _];
            subst intervals.

          iInduction ts as [|thd trest] "IH'" forall (Φ' ns lhd);
            destruct ns as [|nhd nrest]; [|done|done|].
          - iDestruct "Hlhd" as "->".
            wp_pures.
            iApply "HPost".
            iExists [].
            done.

          - iDestruct "Hns" as "[Hnhd Hnrest]".
            destruct trest as [|tsnd]; destruct nrest as [|nsnd]; [|done|done|];
              iEval (rewrite big_opL_cons) in "IH";
              iDestruct "IH" as "[IHthd IHtrest]";
              apply Forall_cons in trees_wf;
              destruct trees_wf as [thd_wf trest_wf];
              apply nary_tree_wf_remove_len in thd_wf.
            + iDestruct "Hlhd" as (l0 ?) "(-> & Hl0 & ->)".
              wp_load; wp_load; wp_pures; wp_bind (insert_nary_tree _).
              iApply ("IHthd" $! thd_wf with "Hnhd").
              iNext.
              iIntros (?) "[Hr1 Hr2]".
              iDestruct "Hr2" as "[(% & % & % & -> & Hr2) | (% & ->)]";
                destruct (insert_nary_tree_spec target thd) as [new_t1 new_t2];
                cbn in H0; subst.
              * wp_alloc lr2 as "Hlr2"; wp_store; wp_pure.
                iApply "HPost".
                iExists (r.1 :: r2 :: []).
                iSplitL "Hl0 Hlr2";
                  [iExists l0, (SOMEV #lr2); iFrame; iSplitR; [done|]; iExists lr2, NONEV; iFrame; done|].
                iFrame; done.
              * wp_store; wp_pure.
                iApply "HPost".
                iExists [r.1].
                iSplitL "Hl0"; [iExists l0, NONEV; iFrame; done|].
                iFrame; done.

            + iDestruct "Hlhd" as (l1 ?) "(-> & Hl1 & Hhd')".
              iDestruct "Hhd'" as (l2 ?) "(-> & Hl2 & Hhd')".
              wp_load; wp_load; wp_pures.
              wp_bind (interval_nary_tree _);
                iApply (interval_nary_tree_spec_proof with "Hnhd");
                iNext;
                iIntros ((low', high')) "[Hnhd %]";
                destruct H0.

              wp_pures.
              destruct (bool_decide (Z.le low' target)) eqn:?; wp_pures.
              -- destruct (bool_decide (Z.le target high')) eqn:?; wp_pures.
                 ++ wp_bind (insert_nary_tree _);
                      iApply ("IHthd" $! thd_wf with "Hnhd");
                      iNext;
                      iIntros (?) "[Hr1 Hr2]".
                    wp_pures.
                    apply bool_decide_eq_true_1 in Heqb0;
                      apply Z.leb_le in Heqb0;
                      rewrite Heqb0.
                    apply bool_decide_eq_true_1 in Heqb1;
                      apply Z.leb_le in Heqb1;
                      rewrite Heqb1.

                    iDestruct "Hr2" as "[(% & % & % & -> & Hr2) | (% & ->)]";
                      destruct (insert_nary_tree_spec target thd) as [new_t1 new_t2];
                      cbn in H0; subst.
                    ** wp_load; wp_alloc l3 as "Hl3"; wp_store; wp_pure.
                       iApply "HPost".
                       iExists (r.1 :: r2 :: nsnd :: nrest).
                       iSplitL "Hl1 Hl3 Hl2 Hhd'";
                         [iExists l1, (SOMEV #l3); iFrame; iSplitR; [done|]; iExists l3, (SOMEV #l2); iFrame; iSplitR; [done|]; iExists l2, hd'0; iFrame; done|].
                       iFrame; done.
                    ** wp_load; wp_store; wp_pure.
                       iApply "HPost".
                       iExists (r.1 :: nsnd :: nrest).
                       iSplitL "Hl1 Hl2 Hhd'";
                         [iExists l1, (SOMEV #l2); iFrame; iSplitR; [done|]; iExists l2, hd'0; iFrame; done|].
                       iFrame; done.

                 ++ wp_load; wp_pure; wp_pure.
                    wp_bind ((rec: "insert_node_list" "arg" := _) (SOMEV #l2, #target))%V.
                    iApply ("IH'" $! trest_wf _ (nsnd :: nrest) (SOMEV #l2) with "[] [Hl2 Hhd'] [Hnrest]"); try done.
                    { iExists l2, hd'0; iFrame; done. }
                    iIntros (?) "[% [Hr Hns]]".
                    wp_store; wp_pure.
                    iApply "HPost".
                    apply bool_decide_eq_true_1 in Heqb0;
                      apply Z.leb_le in Heqb0;
                      rewrite Heqb0.
                    apply bool_decide_eq_false_1 in Heqb1;
                      assert (Z.lt high' target) by lia;
                      apply Z.ltb_lt in H0;
                      rewrite Z.ltb_antisym in H0;
                      symmetry in H0;
                      apply negb_sym in H0;
                      cbn in H0;
                      rewrite H0.
                    iExists (nhd :: ns).
                    iFrame.
                    iExists l1, r; iFrame; done.

              -- wp_load; wp_pure; wp_pure;
                   wp_bind ((rec: "insert_node_list" "arg" := _) (SOMEV #l2, #target))%V.
                 iApply ("IH'" $! trest_wf _ (nsnd :: nrest) with "[] [Hl2 Hhd'] [Hnrest]"); try done.
                 { iExists l2, hd'0; iFrame; done. }
                 iIntros (?) "[% [Hr Hns]]".
                 wp_store; wp_pures.
                 iApply "HPost".

                 apply bool_decide_eq_false_1 in Heqb0;
                   assert (Z.lt target low') by lia;
                   apply Z.ltb_lt in H0;
                   rewrite Z.ltb_antisym in H0;
                   symmetry in H0;
                   apply negb_sym in H0;
                   cbn in H0;
                   rewrite H0.
                 iExists (nhd :: ns).
                 iFrame.
                 iExists l1, r; iFrame; done. }

        iClear "IH".
        iApply ("IH'" with "[Hlhd Hns]"); iClear "IH'".
        { iFrame. }
        iIntros (r) "Hr".
        iDestruct "Hr" as (?) "[Hr Hns0]".

        wp_load; wp_pures; wp_bind (length_list _).
        iApply (length_list_spec_proof with "Hr").
        iNext.
        iIntros (?) "[% Hr]".
        wp_pure.
        remember (fix branch_node_list (ns1 : list val) (ts0 : list nary_tree) {struct ts0} : iProp :=
                 match ns1 with
                 | [] => match ts0 with
                         | [] => True
                         | _ :: _ => False
                         end
                 | n :: ns2 =>
                     match ts0 with
                     | [] => False
                     | t :: ts1 => is_node n t ∗ branch_node_list ns2 ts1
                     end
                 end)%I as branch_node_list.
        remember ((fix insert_aux (l : list nary_tree) : list nary_tree :=
                     match l with
                     | [] => []
                     | [t] =>
                         let (new_t1, new_t2) := insert_nary_tree_spec target t in
                         match new_t2 with
                         | Some new_t2' => [new_t1; new_t2']
                         | None => [new_t1]
                         end
                     | t :: (_ :: _) as ts0 =>
                         let (low0, high0) := nary_tree_interval t in
                         if (low0 <=? target)%Z && (target <=? high0)%Z
                         then
                           let (new_t1, new_t2) := insert_nary_tree_spec target t in
                           match new_t2 with
                           | Some new_t2' => new_t1 :: new_t2' :: ts0
                           | None => new_t1 :: ts0
                           end
                         else t :: insert_aux ts0
                     end) ts) as new_ts.
        destruct (bool_decide (Z.lt b r0)) eqn:?.
        + wp_pures; wp_bind (split_list _).
          rewrite Z2N_b2.
          iApply (split_list_spec_proof with "Hr").
          iNext.
          iIntros (?) "[Hr1 Hr2]".

          iPoseProof ((branch_node_list_lengths ns0 new_ts) with "[Hns0]") as "[Hns0 %Heqlengths]";
            [rewrite Heqbranch_node_list; done|].
          iPoseProof ((branch_node_split (b/2)) with "Hns0") as "[Hnstake Hnsdrop]";
            iEval (rewrite <- Heqbranch_node_list) in "Hnstake Hnsdrop".
          assert (b < length new_ts) as bltlengthnew_ts by (rewrite bool_decide_eq_true in Heqb0; lia);
            specialize (take_b2_cons new_ts bltlengthnew_ts) as [tthd [ttrest take_new_ts_cons]];
            specialize (take_b2_snoc new_ts bltlengthnew_ts) as [ttlast [ttrest' take_new_ts_snoc]];
            specialize (drop_b2_cons new_ts bltlengthnew_ts) as [dthd [dtrest drop_new_ts_cons]];
            specialize (drop_b2_snoc new_ts bltlengthnew_ts) as [dtlast [dtrest' drop_new_ts_snoc]];
            clear bltlengthnew_ts.
          assert (b < length ns0) as bltlengthns0 by (rewrite bool_decide_eq_true in Heqb0; lia);
            specialize (take_b2_cons ns0 bltlengthns0) as [tnhd [tnrest take_ns0_cons]];
            specialize (take_b2_snoc ns0 bltlengthns0) as [tnlast [tnrest' take_ns0_snoc]];
            specialize (drop_b2_cons ns0 bltlengthns0) as [dnhd [dnrest drop_ns0_cons]];
            specialize (drop_b2_snoc ns0 bltlengthns0) as [dnlast [dnrest' drop_ns0_snoc]].

          wp_pures;
            wp_bind (headopt_list _);
            iApply (headopt_list_spec_proof with "Hr1");
            iNext;
            iIntros (?) "[-> Hr1]";
            rewrite take_new_ts_cons;
            rewrite take_ns0_cons;
            wp_pures;
            wp_bind (interval_nary_tree _);
            iEval (rewrite Heqbranch_node_list) in "Hnstake";
            iDestruct "Hnstake" as "[Htnhd Htnsrest]";
            iApply (interval_nary_tree_spec_proof with "Htnhd");
            iNext;
            iIntros ((thdlow, thdhigh)) "[Htnhd %]";
            iCombine "Htnhd Htnsrest" as "Hnstake";
            assert (is_node tnhd tthd ∗ branch_node_list tnrest ttrest -∗
                      branch_node_list (tnhd :: tnrest) (tthd :: ttrest)) as Heqnstake
            by (rewrite Heqbranch_node_list; done);
            iPoseProof (Heqnstake with "[Hnstake]") as "Hnstake"; [rewrite Heqbranch_node_list; iFrame|];
            rewrite <- take_new_ts_cons;
            rewrite <- take_ns0_cons.

          wp_pures;
            wp_bind (lastopt_list _);
            iApply (lastopt_list_spec_proof with "Hr1");
            iNext;
            iIntros (?) "[-> Hr1]";
            rewrite take_new_ts_snoc;
            rewrite take_ns0_snoc;
            wp_pures;
            iEval (rewrite last_snoc);
            wp_pures;
            wp_bind (interval_nary_tree _);
            iEval (rewrite Heqbranch_node_list) in "Hnstake";
            iDestruct (branch_node_snoc with "Hnstake") as "[Htnsrest Htnlast]";
            iApply (interval_nary_tree_spec_proof with "Htnlast");
            iNext;
            iIntros ((tlastlow, tlasthigh)) "[Htnlast %]";
            iCombine "Htnsrest Htnlast" as "Hnstake";
            iPoseProof (branch_node_snoc' with "[Hnstake]") as "Hnstake"; [iFrame|];
            iEval (rewrite <- Heqbranch_node_list) in "Hnstake";
            rewrite <- take_new_ts_snoc;
            rewrite <- take_ns0_snoc.

          wp_pures;
            wp_bind (headopt_list _);
            iApply (headopt_list_spec_proof with "Hr2");
            iNext;
            iIntros (?) "[-> Hr2]";
            rewrite drop_new_ts_cons;
            rewrite drop_ns0_cons;
            wp_pures;
            wp_bind (interval_nary_tree _);
            iEval (rewrite Heqbranch_node_list) in "Hnsdrop";
            iDestruct "Hnsdrop" as "[Hdnhd Hdnsrest]";
            iApply (interval_nary_tree_spec_proof with "Hdnhd");
            iNext;
            iIntros ((dthdlow, dthdhigh)) "[Hdnhd %]";
            iCombine "Hdnhd Hdnsrest" as "Hnsdrop";
            assert (is_node dnhd dthd ∗ branch_node_list dnrest dtrest -∗
                      branch_node_list (dnhd :: dnrest) (dthd :: dtrest)) as Heqnsdrop
              by (rewrite Heqbranch_node_list; done);
            iPoseProof (Heqnsdrop with "[Hnsdrop]") as "Hnsdrop";
              [rewrite Heqbranch_node_list; iFrame|];
            rewrite <- drop_new_ts_cons;
            rewrite <- drop_ns0_cons.

          wp_pures;
            wp_bind (lastopt_list _);
            iApply (lastopt_list_spec_proof with "Hr2");
            iNext;
            iIntros (?) "[-> Hr2]";
            rewrite drop_new_ts_snoc;
            rewrite drop_ns0_snoc;
            wp_pures;
            iEval (rewrite last_snoc);
            wp_pures;
            wp_bind (interval_nary_tree _);
            iEval (rewrite Heqbranch_node_list) in "Hnsdrop";
            iDestruct (branch_node_snoc with "Hnsdrop") as "[Hnsrest Hnlast]";
            iApply (interval_nary_tree_spec_proof with "Hnlast");
            iNext;
            iIntros ((dtlastlow, dtlasthigh)) "[Hnlast %]";
            iCombine "Hnsrest Hnlast" as "Hnsdrop";
            iPoseProof (branch_node_snoc' with "Hnsdrop") as "Hnsdrop";
            rewrite <- drop_new_ts_snoc;
            rewrite <- drop_ns0_snoc.

          wp_pures; wp_alloc ptr' as "Hptr'"; wp_store; wp_pures.
          iApply ("HPost" $! (token_branch_v #ptr, token_branch_v (SOMEV #ptr'))).
          subst r0;
            rewrite bool_decide_eq_true in Heqb0;
            apply Z.ltb_lt in Heqb0;
            rewrite <- Heqlengths, Heqb0.

          iSplitL "Hptr Hr1 Hnstake".
          { iExists ptr, r1.1, (take (b/2) ns0).
            fold is_node; rewrite <- Heqbranch_node_list.
            repeat rewrite head_map_comm last_map_comm.
            rewrite take_new_ts_cons;
              rewrite take_ns0_cons;
              iEval (rewrite head_cons);
              rewrite <- take_new_ts_cons;
              rewrite <- take_ns0_cons.
            rewrite take_new_ts_snoc;
              rewrite take_ns0_snoc;
              iEval (rewrite last_snoc);
              rewrite <- take_new_ts_snoc;
              rewrite <- take_ns0_snoc.
            destruct H1, H2.
            iFrame; done. }

          iLeft.
          repeat rewrite head_map_comm last_map_comm.
          rewrite <- Heqbranch_node_list.
          rewrite drop_new_ts_cons;
            rewrite drop_ns0_cons;
            iEval (rewrite head_cons);
            rewrite <- drop_new_ts_cons;
            rewrite <- drop_ns0_cons.
          rewrite drop_new_ts_snoc;
            rewrite drop_ns0_snoc;
            iEval (rewrite last_snoc);
            rewrite <- drop_new_ts_snoc;
            rewrite <- drop_ns0_snoc.

          iExists (node (fst (nary_tree_interval dthd), snd (nary_tree_interval dtlast)) (drop (b/2) new_ts)).
          iSplitR; [done|].
          iExists (token_branch_v #ptr').
          iSplitR; [done|].
          iExists ptr', r1.2, (drop (b/2) ns0).
          fold is_node.
          rewrite <- Heqbranch_node_list.
          destruct H3, H4.
          iFrame; done.

        + iPoseProof ((branch_node_list_lengths ns0 new_ts) with "[Hns0]") as "[Hns %Heqlengths]";
            [rewrite Heqbranch_node_list; done|];
            rewrite <- Heqbranch_node_list.

          destruct new_ts as [|thd trest];
            destruct ns0 as [|nhd nrest];
            [|rewrite Heqbranch_node_list; done|rewrite Heqbranch_node_list; done|].
          * wp_pures;
              wp_bind (headopt_list _);
              iApply (headopt_list_spec_proof with "Hr");
              iNext;
              iIntros (?) "[-> Hr]";
              iEval (rewrite head_nil).

            wp_pures;
              wp_bind (lastopt_list _);
              iApply (lastopt_list_spec_proof with "Hr");
              iNext;
              iIntros (?) "[-> Hr]";
              iEval (rewrite last_nil).

            wp_store; wp_pures.

            iApply ("HPost" $! (token_branch_v #ptr, NONEV)).
            apply bool_decide_eq_false_1 in Heqb0;
              assert (Z.le r0 b) by lia;
              apply Z.leb_le in H1;
              rewrite Z.leb_antisym in H1;
              symmetry in H1;
              apply negb_sym in H1;
              cbn in H1;
              subst r0;
              rewrite H1.

            iSplitL; [iExists ptr, r, []; iFrame; done|].
            iRight.
            done.

          * wp_pures;
              wp_bind (headopt_list _);
              iApply (headopt_list_spec_proof with "Hr");
              iNext;
              iIntros (?) "[-> Hr]";
              iEval (rewrite head_cons);
              wp_pures;
              wp_bind (interval_nary_tree _);
              iEval (rewrite Heqbranch_node_list) in "Hns";
              iDestruct "Hns" as "[Hnhd Hnsrest]";
              iApply (interval_nary_tree_spec_proof with "Hnhd");
              iNext;
              iIntros ((hdlow, hdhigh)) "[Hnhd %]";
              iCombine "Hnhd Hnsrest" as "Hns";
              assert (is_node nhd thd ∗ branch_node_list nrest trest -∗
                        branch_node_list (nhd :: nrest) (thd :: trest)) as Heqnbranches
                by (rewrite Heqbranch_node_list; done);
              iPoseProof (Heqnbranches with "[Hns]") as "Hns";
              [rewrite Heqbranch_node_list; iFrame|].

            destruct (cons_snoc (thd :: trest) _ _ eq_refl) as [tlast [tinit Heqts]].
            destruct (cons_snoc (nhd :: nrest) _ _ eq_refl) as [nlast [ninit Heqns]].

            rewrite Heqts Heqns;
              wp_pures;
              wp_bind (lastopt_list _);
              iApply (lastopt_list_spec_proof with "Hr");
              iNext;
              iIntros (?) "[-> Hr]";
              iEval (rewrite last_snoc);
              wp_pures;
              wp_bind (interval_nary_tree _);
              iEval (rewrite Heqbranch_node_list) in "Hns";
              iDestruct (branch_node_snoc with "Hns") as "[Hnsrest Hnlast]";
              iApply (interval_nary_tree_spec_proof with "Hnlast");
              iNext;
              iIntros ((lastlow, lasthigh)) "[Hnlast %]";
              iCombine "Hnsrest Hnlast" as "Hns";
              iPoseProof (branch_node_snoc' with "Hns") as "Hns";
              rewrite <- Heqts, <- Heqns.

            wp_store; wp_pures.
            iApply ("HPost" $! (token_branch_v #ptr, NONEV)).
            apply bool_decide_eq_false_1 in Heqb0;
              assert (Z.le r0 b) by lia;
              apply Z.leb_le in H3;
              rewrite Z.leb_antisym in H3;
              symmetry in H3;
              apply negb_sym in H3;
              cbn in H3;
              rewrite <- Heqlengths;
              subst r0;
              rewrite H3.

            repeat rewrite head_map_comm last_map_comm;
              rewrite head_cons;
              rewrite Heqts;
              rewrite last_snoc;
              rewrite <- Heqts.

            destruct H1, H2.
            iSplitL; [iExists ptr, r, (nhd :: nrest); iFrame; done|].
            iRight; done.
    Qed.

  End bplus_tree_proofs.
End bplus_tree.
