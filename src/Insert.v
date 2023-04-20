From iris.algebra Require Import numbers.
From iris.heap_lang Require Export proofmode notation.
From iris.proofmode Require Export proofmode.
From iris.prelude Require Import options.
Require Import NaryTree.
Require Import BPlusTree.

Section nary_tree.

  Fixpoint Insert_list (target : Z) (l : list Z) : list Z :=
    match l with
    | [] => [target]
    | x :: xs => if Z.eqb x target
               then x :: xs
               else if Z.ltb x target
                    then x :: Insert_list target xs
                    else target :: x :: xs
    end.

  Fixpoint Insert_nary_tree (target : Z) (t : nary_tree) : nary_tree :=
    match t with
    | leaf interval vals => leaf interval (Insert_list target vals)
    | node interval branches =>
        node interval
          ((fix insert_aux (l : list nary_tree) :=
              match l with
              | [] => [leaf (target, target) [target]]
              | t :: ts =>
                  let (low, high) := (match t with leaf interval _ | node interval _ => interval end) in
                  if andb (Z.leb low target) (Z.leb target high)
                  then Insert_nary_tree target t :: ts
                  else t :: insert_aux ts
              end) branches)
    end.
End nary_tree.

Section bplus_tree.
  Section bplus_tree_algos.

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

    Definition insert_bplus_tree : val :=
      rec: "insert_bplus_tree" "arg" :=
        let: "t" := Fst "arg" in
        let: "target" := Snd "arg" in
        match: "t" with
          InjL "ptr" =>
            let: "lhd" := Snd !"ptr" in
            let: "new" := insert_list ("lhd", "target") in
            (* should change interval here *)
            "ptr" <- (Fst !"ptr", "new") ;;
            "t"
        | InjR "ptr" =>
            let: "lhd" := Snd !"ptr" in
            let: "new" :=
              (rec: "insert_node_list" "arg" :=
                 let: "p" := Fst "arg" in
                 let: "target" := Snd "arg" in
                 match: "p" with
                   NONE =>
                     let: "l" := SOME (ref ("target", NONE)) in
                     let: "t" := ref (("target", "target"), "l") in
                     SOME (ref (token_leaf_e "t", NONE))
                 | SOME "l" =>
                     let: "val" := Fst !"l" in
                     let: "interval" :=
                       match: "val" with
                         InjL "ptr" => Fst !"ptr"
                       | InjR "ptr" => Fst !"ptr"
                       end in
                     let: "low" := Fst "interval" in
                     let: "high" := Snd "interval" in
                     let: "new" :=
                       if: (BinOp LeOp "low" "target") && (BinOp LeOp "target" "high")
                       then "insert_bplus_tree" ("val", "target")
                       else "insert_node_list" (Snd !"l", "target") in
                     "l" <- ("val", "new") ;;
                     SOME "l"
                 end) ("lhd", "target") in
            "ptr" <- (Fst !"ptr", "new") ;;
            token_branch_e "ptr"
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

    Lemma insert_list_spec (v : val) (l : list tval) (target : tval):
      {{{ is_list v (map (fun (x : tval) => #x) l) }}} insert_list (v, (#target))%V {{{ r, RET r; is_list r (map (fun (x : tval) => #x) (Insert_list target l)) }}}.
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
            unfold Insert_list.
            rewrite (bool_decide_false_Zeqb _ _ Heqb0).
            rewrite bool_decide_eq_true in Heqb1;
              apply Z.ltb_lt in Heqb1;
              rewrite Heqb1.
            iExists l', r.
            iFrame.
            done.
          * wp_alloc new as "Hnew"; wp_pure.
            iApply "HPost".
            unfold Insert_list;
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

    Lemma insert_nary_tree_spec (t : nary_tree) (t_wf : nary_tree_wf_no_len b t) (v : val) (target : tval) :
      {{{ is_node v t }}} insert_bplus_tree (v, #target)%V {{{ r, RET r; is_node r (Insert_nary_tree target t) }}}.
    Proof using bpos.
      iIntros (Φ) "Hv HPost".

      iInduction t as [(low & high)|(low & high) ts] "IH" using nary_tree_ind' forall (v).
      - iPoseProof (tree_leaf_token_leaf with "Hv") as (?) "->".
        iDestruct "Hv" as (? ?) "(% & Hptr & Hlhd)".
        assert (x = #ptr) by (unfold token_leaf_v in H; congruence); subst.
        wp_rec; wp_load; wp_pures; wp_bind (insert_list _).
        iApply (insert_list_spec with "Hlhd").
        iNext.
        iIntros (?) "Hr".
        wp_load; wp_store.
        iApply "HPost".
        iExists ptr, r.
        iFrame.
        done.
      - iPoseProof (tree_node_token_branch with "Hv") as (?) "->".
        iDestruct "Hv" as (ptr lhd ns) "(% & Hptr & Hlhd & Hns)".
        fold is_node.
        assert (x = #ptr) by (unfold token_branch_v in H; congruence); subst.
        wp_rec; wp_load; wp_proj; wp_let; wp_pure; wp_pure.
        iEval (cbn) in "HPost".

        wp_bind ((rec: "insert_node_list" "arg" := _) (lhd, #target))%V.
        iAssert (∀ Φ',
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
                 (∃ (ns0 : list val),
                     is_list r ns0 ∗
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
                               end) ns0
                            ((fix insert_aux (l0 : list nary_tree) : list nary_tree :=
                                match l0 with
                                | [] => [leaf (target, target)%Z [target]]
                                | t :: ts0 =>
                                    let (low0, high0) :=
                                      match t with
                                      | leaf interval _ | node interval _ => interval
                                      end in
                                    if (low0 <=? target)%Z && (target <=? high0)%Z
                                    then Insert_nary_tree target t :: ts0
                                    else t :: insert_aux ts0
                                end) ts)) -∗ Φ' r) -∗
              WP (rec: "insert_node_list" "arg" :=
        let: "p" := Fst "arg" in
        let: "target" := Snd "arg" in
        match: "p" with
          InjL <> =>
            let: "l" := InjR (ref ("target", InjL #())) in
            let: "t" := ref ("target", "target", "l") in InjR (ref (InjL "t", InjL #()))
        | InjR "l" =>
          let: "val" := Fst ! "l" in
          let: "interval" := match: "val" with
                               InjL "ptr" => Fst ! "ptr"
                             | InjR "ptr" => Fst ! "ptr"
                             end in
          let: "low" := Fst "interval" in
          let: "high" := Snd "interval" in
          let: "new" := if: if: "low" ≤ "target" then "target" ≤ "high" else #false
                        then insert_bplus_tree ("val", "target")
                        else "insert_node_list" (Snd ! "l", "target") in
          "l" <- ("val", "new");; InjR "l"
        end)%V (lhd, #target)%V
              {{ v, Φ' v}}
          )%I as "IH'".
        { iIntros (Φ') "[Hlhd Hns] HPost".

          iInduction ts as [|thd trest] "IH'" forall (ns lhd).
          - destruct ns as [|nhd nrest]; [|done].
            iDestruct "Hlhd" as "->".

            wp_alloc newl as "Hnewl";
              wp_alloc newt as "Hnewt";
              wp_alloc newts as "Hnewts";
              wp_pure.
            iApply "HPost".
            iExists [ token_leaf_v #newt ].
            iFrame.
            iSplitL "Hnewts"; [iExists newts, (InjLV #()); iFrame; done|].
            iExists newt, (InjRV #newl).
            iFrame.
            iSplitR; [done|].
            iExists newl, (InjLV #()).
            iFrame.
            done.
        - admit. }

        iApply ("IH'" with "[Hlhd Hns]").
        { iFrame. }
        
        iIntros (r) "Hr".
        wp_load; wp_store; wp_pure.
        iApply "HPost".
        iDestruct "Hr" as (ns0) "[Hr Hns0]".
        iExists ptr, r, ns0.
        iFrame.
        done.

    Admitted.

  End bplus_tree_proofs.
End bplus_tree.
