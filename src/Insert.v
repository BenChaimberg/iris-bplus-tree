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

  Fixpoint insert_nary_tree_spec (target : Z) (t : nary_tree) : nary_tree * option nary_tree :=
    match t with
    | leaf (low, high) vals =>
        let new_vals := insert_list_spec target vals in
        if Z.ltb b (length new_vals)
        then
          let left_vals := firstn (b/2) new_vals in
          let right_vals := skipn (b/2) new_vals in
          let left_interval := (low, List.last left_vals high) in
          let right_interval := (hd low right_vals, high) in
          (* TODO: fix interval *)
          (leaf (low, high) left_vals, Some (leaf (low, high) right_vals))
        else
          (leaf (low, high) new_vals, None)
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
                  let (low, high) := (match t with leaf interval _ | node interval _ => interval end) in
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
          let left_interval := (low, (List.last (map snd (map nary_tree_interval left_branches)) high)) in
          let right_interval := (hd low (map fst (map nary_tree_interval right_branches)), high) in
          (* TODO: should change intervals *)
          (node (low, high) left_branches, Some (node (low, high) right_branches))
        else
          (node (low, high) new_branches, None)
    end.

    Definition insert_nary_tree : val :=
      rec: "insert_nary_tree" "arg" :=
        let: "t" := Fst "arg" in
        let: "target" := Snd "arg" in
        match: "t" with
          InjL "ptr" =>
            let: "lhd" := Snd !"ptr" in
            let: "new" := insert_list ("lhd", "target") in
            (* TODO: should change interval here *)
            if: #b < length_list "new"
            then
              let: "newlpair" := split_list ("new", #(b/2)) in
              let: "newleaf" := ref (Fst !"ptr", Snd "newlpair") in
              "ptr" <- (Fst !"ptr", Fst "newlpair") ;;
              (token_leaf_e "ptr", SOME (token_leaf_e "newleaf"))
            else
              "ptr" <- (Fst !"ptr", "new") ;;
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
                         let: "interval" :=
                           match: "thd" with
                             InjL "ptr" => Fst !"ptr"
                           | InjR "ptr" => Fst !"ptr"
                           end in
                         let: "low" := Fst "interval" in
                         let: "high" := Snd "interval" in
                         (if: (BinOp LeOp "low" "target") && (BinOp LeOp "target" "high")
                          then let: "newt" := "insert_nary_tree" ("thd", "target") in
                               (* TODO: should change interval here *)
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
            if: #b < length_list "new"
            then
              let: "newlpair" := split_list ("new", #(b/2)) in
              let: "newbranch" := ref (Fst !"ptr", Snd "newlpair") in
              "ptr" <- (Fst !"ptr", Fst "newlpair") ;;
              (token_branch_e "ptr", SOME (token_branch_e "newbranch"))
            else
              "ptr" <- (Fst !"ptr", "new") ;;
              (token_branch_e "ptr", NONEV)
        end%E.

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

    Lemma branch_node_split ns ts n :
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
    Proof using bpos.
      iIntros (Φ) "Hv HPost".

      iInduction t as [(low & high)|(low & high) ts] "IH" using nary_tree_ind' forall (Φ v).
      - iPoseProof (tree_leaf_token_leaf with "Hv") as (?) "->".
        iDestruct "Hv" as (? ?) "(% & Hptr & Hlhd)".
        assert (x = #ptr) by (unfold token_leaf_v in H; congruence); subst; clear H.
        wp_rec; wp_load; wp_pures; wp_bind (insert_list _).
        iApply (insert_list_spec_proof with "Hlhd").
        iNext.
        iIntros (?) "Hr".
        wp_pures; wp_bind (length_list _).
        iApply (length_list_spec_proof with "Hr").
        iNext.
        iIntros (?) "[% Hr]".
        wp_pure.
        destruct (bool_decide (Z.lt b r0)) eqn:?.
        + wp_pure; wp_bind (split_list _); wp_pure.
          replace (Z.div b 2) with (Z.of_nat (b `div` 2)); [|admit]. (* TODO: just annoying arithmetic *)
          iApply (split_list_spec_proof with "Hr").
          iNext.
          iIntros (?) "[Hr1 Hr2]".
          wp_load; wp_alloc ptr' as "Hptr'"; wp_load; wp_store; wp_pures.
          iApply ("HPost" $! (InjLV #ptr, InjRV (InjLV #ptr'))).
          rewrite map_length in H; subst r0.
          rewrite bool_decide_eq_true in Heqb0;
            apply Z.ltb_lt in Heqb0.
          iSplitL "Hptr Hr1".
          { cbn; rewrite Heqb0.
            iExists ptr, r1.1.
            iSplitR; [done|].
            iSplitL "Hptr"; [done|].
            rewrite firstn_map; done. }
          iLeft.
          iExists (leaf (low, high) (drop (b `div` 2) (insert_list_spec target vals))).
          iSplitR. { cbn; rewrite Heqb0; cbn; done. }
          iExists (InjLV #ptr').
          iSplitR; [done|].
          iExists ptr', r1.2.
          rewrite skipn_map.
          iFrame.
          done.

        + wp_load; wp_store; wp_pures.
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
            iFrame.
            done. }
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
                                  let (low0, high0) :=
                                    match t with
                                    | leaf interval _ | node interval _ => interval
                                    end in
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
                         let: "interval" :=
                           match: "thd" with
                             InjL "ptr" => Fst !"ptr"
                           | InjR "ptr" => Fst !"ptr"
                           end in
                         let: "low" := Fst "interval" in
                         let: "high" := Snd "interval" in
                         (if: (BinOp LeOp "low" "target") && (BinOp LeOp "target" "high")
                          then let: "newt" := insert_nary_tree ("thd", "target") in
                               (* TODO: should change interval here *)
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
              destruct thd.
              * destruct interval as [low' high'].
                iDestruct "Hnhd" as (ptr' leaves) "(-> & Hptr' & Hleaves)".
                wp_load; wp_pures.
                destruct (bool_decide (Z.le low' target)) eqn:?; wp_pures.
                -- destruct (bool_decide (Z.le target high')) eqn:?; wp_pures.
                   ++ wp_bind (insert_nary_tree _).
                      iApply ("IHthd" $! thd_wf with "[Hptr' Hleaves]").
                      { iExists ptr', leaves; iFrame; done. }
                      iNext.
                      iIntros (?) "[Hr1 Hr2]".
                      apply bool_decide_eq_true_1 in Heqb0;
                           apply Z.leb_le in Heqb0;
                           rewrite Heqb0.
                         apply bool_decide_eq_true_1 in Heqb1;
                           apply Z.leb_le in Heqb1;
                           rewrite Heqb1.
                      iDestruct "Hr2" as "[(% & % & % & -> & Hr2) | (% & ->)]";
                        destruct (insert_nary_tree_spec target (leaf (low', high') l)) as [new_t1 new_t2];
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
                      iExists (token_leaf_v #ptr' :: ns).
                      iFrame.
                      iSplitL "Hl1 Hr"; [iExists l1, r; iFrame; done|].
                      iExists ptr', leaves; iFrame; done.
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
                   iExists (token_leaf_v #ptr' :: ns).
                   iFrame.
                   iSplitL "Hl1 Hr"; [iExists l1, r; iFrame; done|].
                   iExists ptr', leaves; iFrame; done.

              * admit. (* TODO: repeat for node (or find a better way to get interval out) *) }

        iClear "IH".
        iApply ("IH'" with "[Hlhd Hns]"); iClear "IH'".
        { iFrame. }
        iIntros (r) "Hr".
        iDestruct "Hr" as (?) "[Hr Hns0]".

        wp_pures; wp_bind (length_list _).
        iApply (length_list_spec_proof with "Hr").
        iNext.
        iIntros (?) "[% Hr]".
        wp_pure.
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
                         let (low0, high0) :=
                           match t with
                           | leaf interval _ | node interval _ => interval
                           end in
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
        + wp_pure; wp_bind (split_list _); wp_pure.
          replace (Z.div b 2) with (Z.of_nat (b `div` 2)); [|admit]. (* TODO: just annoying arithmetic *)
          iApply (split_list_spec_proof with "Hr").
          iNext.
          iIntros (?) "[Hr1 Hr2]".
          wp_load; wp_alloc ptr' as "Hptr'"; wp_load; wp_store; wp_pures.
          iApply ("HPost" $! (token_branch_v #ptr, token_branch_v (SOMEV #ptr'))).
          subst r0.
          rewrite bool_decide_eq_true in Heqb0;
            apply Z.ltb_lt in Heqb0.
          iPoseProof ((branch_node_list_lengths ns0 new_ts) with "Hns0") as "[Hns0 %Heqlengths]".
          rewrite <- Heqlengths, Heqb0.
          iPoseProof ((branch_node_split ns0 new_ts (b/2)) with "Hns0") as "[Htakens Hdropns]".

          iSplitL "Hptr Hr1 Htakens".
          { cbn.
            iExists ptr, r1.1, (take (b/2) ns0).
            iFrame.
            done. }
          iLeft.
          iExists (node (low, high) (drop (b/2) new_ts)).
          iSplitR; [done|].
          iExists (token_branch_v #ptr').
          iSplitR; [done|].
          iExists ptr', r1.2, (drop (b/2) ns0).
          iFrame.
          done.

        + wp_load; wp_store; wp_pures.
          iApply ("HPost" $! (token_branch_v #ptr, NONEV)).
          apply bool_decide_eq_false_1 in Heqb0;
            assert (Z.le r0 b) by lia;
            apply Z.leb_le in H1;
            rewrite Z.leb_antisym in H1;
            symmetry in H1;
            apply negb_sym in H1;
            cbn in H1.
          subst r0.
          iPoseProof ((branch_node_list_lengths ns0 new_ts) with "Hns0") as "[Hns0 %Heqlengths]".
          rewrite <- Heqlengths, H1.

          iSplitL "Hptr Hr Hns0"; [iExists ptr, r, ns0; iFrame; done|].
          iRight.
          done.
    Admitted.

  End bplus_tree_proofs.
End bplus_tree.
