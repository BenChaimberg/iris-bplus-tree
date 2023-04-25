From iris.algebra Require Import numbers.
From iris.heap_lang Require Export proofmode notation.
From iris.proofmode Require Export proofmode.
From iris.prelude Require Import options.
Require Import NaryTree.
Require Import BPlusTree.

Section bplus_tree.
  Section bplus_tree_algos.
    
    Definition search_list : val :=
      rec: "search_list" "arg" :=
        let: "p" := Fst "arg" in
        let: "target" := Snd "arg" in
        match: "p" with
          NONE => #false
        | SOME "l" =>
            let: "val" := Fst !"l" in
            if: "val" = "target"
            then #true
            else "search_list" (Snd !"l", "target")
        end.

    Definition search_bplus_tree : val :=
      rec: "search_bplus_tree" "arg" :=
        let: "t" := Fst "arg" in
        let: "target" := Snd "arg" in
        match: "t" with
          InjL "ptr" =>
            let: "lhd" := Snd !"ptr" in
            search_list ("lhd", "target")
        | InjR "ptr" =>
            let: "lhd" := Snd !"ptr" in
            (rec: "search_node_list" "arg" :=
               let: "p" := Fst "arg" in
               let: "target" := Snd "arg" in
               match: "p" with
                 NONE => #false
               | SOME "l" =>
                   let: "val" := Fst !"l" in
                   let: "interval" :=
                     match: "val" with
                       InjL "ptr" => Fst !"ptr"
                     | InjR "ptr" => Fst !"ptr"
                     end in
                   let: "low" := Fst "interval" in
                   let: "high" := Snd "interval" in
                   if: (BinOp LeOp "low" "target") && (BinOp LeOp "target" "high")
                   then "search_bplus_tree" ("val", "target")
                   else "search_node_list" (Snd !"l", "target")
               end) ("lhd", "target")
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

    Lemma search_list_spec (v : val) (l : list tval) (target : tval):
      {{{ is_list v (map (fun (x : tval) => (#x)) l) }}} search_list (v, (#target))%V {{{ r, RET r; ⌜ r = #(In_list target l) ⌝ ∗ is_list v (map (fun (x : tval) => (#x)) l) }}}.
    Proof.
      iIntros (Φ) "Hl HPost".
      iInduction l as [|x l] "IH" forall (Φ v); wp_rec; wp_pures.
      - iDestruct "Hl" as "->".
        wp_match.
        iApply "HPost".
        iSplitL; [|done].
        iPureIntro.
        done.
      - iDestruct "Hl" as (l' ?) "(-> & Hl' & Hl)".
        wp_match; wp_load; wp_pures.
        destruct (bool_decide (#x = #target)) eqn:?.
        + wp_pures.
          iApply "HPost".
          iSplitR "Hl' Hl".
          2:(iExists l', hd'; iFrame; done).
          iPureIntro.
          cbn.
          rewrite (bool_decide_true_Zeqb _ _ Heqb0).
          done.
        + wp_pures; wp_load; wp_pures.
          iApply ("IH" $! Φ hd' with "Hl").
          iNext.
          iIntros (?) "[% Hl]".
          iApply "HPost".
          iClear "IH".
          iSplitR.
          * iPureIntro.
            unfold In_list.
            rewrite (bool_decide_false_Zeqb _ _ Heqb0).
            cbn.
            done.
          * iExists l', hd'.
            iFrame.
            done.
    Qed.

    Lemma search_nary_tree_spec (t : nary_tree) (t_wf : nary_tree_wf_no_len t) (v : val) (target : nat) :
      {{{ is_node v t }}} search_bplus_tree (v, #target)%V {{{ r, RET r; ⌜ r = #(In_nary_tree target t) ⌝ ∗ is_node v t }}}.
    Proof using bpos.
      iIntros (Φ) "Hv HPost".

      iInduction t as [(low & high)|(low & high) ts] "IH" using nary_tree_ind' forall (v).
      - iPoseProof (tree_leaf_token_leaf with "Hv") as (?) "->".
        iDestruct "Hv" as (? ?) "(% & Hptr & Hlhd)".
        assert (x = #ptr) by (unfold token_leaf_v in H; congruence); subst.
        wp_rec; wp_load; wp_pures.
        iApply (search_list_spec with "Hlhd").
        iNext.
        iIntros (?) "[% Hlhd]".
        iApply "HPost".
        iSplitR; [done|].
        iExists ptr, lhd.
        iFrame.
        done.

      - iPoseProof (tree_node_token_branch with "Hv") as (?) "->".
        iDestruct "Hv" as (ptr lhd ns) "(% & Hptr & Hlhd & Hns)".
        assert (x = #ptr) by (unfold token_branch_v in H; congruence); subst.
        wp_rec; wp_load; wp_proj; wp_let; wp_pure; wp_pure.
        iEval (cbn) in "HPost".

        iAssert (
            (is_list lhd ns ∗
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
               ▷ (∀ r : val,
                   ⌜r =
                     #((fix In_aux (l0 : list nary_tree) : bool :=
                          match l0 with
                          | [] => false
                          | t0 :: ts0 => In_nary_tree target t0 || In_aux ts0
                          end) ts)⌝ ∗ is_list lhd ns ∗
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
                          end) ns ts -∗ Φ r) -∗
               WP (rec: "search_node_list" "arg" :=
                     let: "p" := Fst "arg" in
                     let: "target" := Snd "arg" in
                     match: "p" with
                       InjL <> => #false
                     | InjR "l" =>
                         let: "val" := Fst ! "l" in
                         let: "interval" := match: "val" with
                                              InjL "ptr" => Fst ! "ptr"
                                            | InjR "ptr" => Fst ! "ptr"
                                            end in
                         let: "low" := Fst "interval" in
                         let: "high" := Snd "interval" in
                         if: if: "low" ≤ "target" then "target" ≤ "high" else #false
                         then search_bplus_tree ("val", "target") else "search_node_list" (Snd ! "l", "target")
                     end)%V (lhd, #target)%V
               {{ v, Φ v }})
          )%I as "IH'".
        { iIntros "[Hlhd Hns] HPost".
          inversion_clear t_wf
            as [| ? ? ? ? _ _ trees_wf intervals_sorted ];
            subst intervals.
          iInduction ts as [|thd trest] "IH'" forall (ns lhd).
          + destruct ns as [|nhd nrest]; [|done].
            iDestruct "Hlhd" as "->".
            wp_pures.
            iApply "HPost".
            done.
          + destruct ns as [|nhd nrest]; [done|].
            iEval (rewrite big_opL_cons) in "IH".
            iDestruct "IH" as "[IHthd IHtrest]".
            apply Forall_cons in trees_wf.
            destruct trees_wf as [t_wf ts_wf].
            iSpecialize ("IH'" $! ts_wf).

            iDestruct "Hlhd" as (l0 ?) "(-> & Hl0 & Hnrest)".
            destruct thd.
            * destruct interval as [low' high'].
              iDestruct "Hns" as "[Hthd Hns]".
              iDestruct "Hthd" as (ptr' leaves) "(-> & Hptr' & Hleaves)".
              wp_load; wp_load; wp_pures.
              destruct (bool_decide (Z.le low' target)) eqn:?; wp_pures.
              -- destruct (bool_decide (Z.le target high')) eqn:?; wp_pures.
                 ++ iApply ("IHthd" $! t_wf with "[Hptr' Hleaves]").
                    { iExists ptr', leaves.
                      iFrame.
                      done. }
                    iNext.
                    iIntros (?) "(% & Hptr')".
                    iApply "HPost".
                    iSplitR.
                    { iPureIntro.
                      cbn.
                      apply bool_decide_eq_true_1 in Heqb0.
                      apply bool_decide_eq_true_1 in Heqb1.

                      assert ((fix In_aux (l1 : list nary_tree) : bool :=
                                 match l1 with
                                 | [] => false
                                 | t0 :: ts => In_nary_tree target t0 || In_aux ts
                                 end) trest = false) as not_in_others.
                      { apply (nary_tree_in_interval_not_in_others _ (leaf (low', high') l)).
                        - constructor; done.
                        - done.
                        - done. }
                      rewrite not_in_others.
                      rewrite orb_false_r.
                      done. }
                    iSplitL "Hl0 Hnrest".
                    { iExists l0, hd'.
                      iFrame.
                      done. }
                    iFrame.

                 ++ wp_load; wp_pure; wp_pure.
                    cbn in intervals_sorted;
                      destruct intervals_sorted as [_ intervals_sorted].

                    iSpecialize ("IH'" $! intervals_sorted).
                    iApply ("IH'" $! nrest hd' with "[] [Hnrest] [Hns]"); [|done|done|].
                    { iApply "IHtrest". }
                    iNext.
                    iIntros (?) "(% & Hhd' & Hnrest)".
                    iApply "HPost".
                    iSplitR.
                    { iPureIntro.
                      enough (In_list target l = false) as not_in_l.
                      { cbn.
                        rewrite not_in_l.
                        rewrite orb_false_l.
                        done. }
                      assert (Z.lt high' target).
                      { apply bool_decide_eq_false_1 in Heqb1.
                        lia. }
                      inversion t_wf; subst.
                      apply (target_above_not_in_list _ high' _); done. }
                    iFrame.
                    iSplitL "Hl0 Hhd'".
                    { iExists l0, hd'.
                      iFrame.
                      done. }
                    iExists ptr', leaves.
                    iFrame.
                    done.

              -- wp_load; wp_pure; wp_pure.
                 cbn in intervals_sorted;
                   destruct intervals_sorted as [_ intervals_sorted].

                 iSpecialize ("IH'" $! intervals_sorted).
                 iApply ("IH'" $! nrest hd' with "[] [Hnrest] [Hns]"); [|done|done|].
                 { iApply "IHtrest". }
                 iNext.
                 iIntros (?) "(% & Hhd' & Hnrest)".
                 iApply "HPost".
                 iSplitR.
                 { iPureIntro.
                   enough (In_list target l = false) as not_in_l.
                   { cbn.
                     rewrite not_in_l.
                     rewrite orb_false_l.
                     done. }
                   assert (Z.lt target low').
                   { apply bool_decide_eq_false_1 in Heqb0.
                     lia. }
                   inversion t_wf; subst.
                   apply (target_below_not_in_list _ low' _); done. }
                 iFrame.
                 iSplitL "Hl0 Hhd'".
                 { iExists l0, hd'.
                   iFrame.
                   done. }
                 iExists ptr', leaves.
                 iFrame.
                 done.

            * destruct interval as [low' high'].
              iDestruct "Hns" as "[Hthd Hns]".
              iDestruct "Hthd" as (ptr' leaves) "(% & -> & Hptr' & Hleaves)".
              wp_load; wp_load; wp_pures.
              destruct (bool_decide (Z.le low' target)) eqn:?; wp_pures.
              -- destruct (bool_decide (Z.le target high')) eqn:?; wp_pures.
                 ++ iApply ("IHthd" $! t_wf with "[Hptr' Hleaves]").
                    { iExists ptr', leaves, ns.
                      iFrame.
                      done. }

                    iNext.
                    iIntros (?) "(% & Hptr')".
                    iApply "HPost".
                    iSplitR.
                    { iPureIntro.
                      cbn.
                      apply bool_decide_eq_true_1 in Heqb0.
                      apply bool_decide_eq_true_1 in Heqb1.

                      assert ((fix In_aux (l1 : list nary_tree) : bool :=
                                 match l1 with
                                 | [] => false
                                 | t0 :: ts => In_nary_tree target t0 || In_aux ts
                                 end) trest = false) as not_in_others.
                      { apply (nary_tree_in_interval_not_in_others _ (node (low', high') l)).
                        - constructor; done.
                        - done.
                        - done. }
                      rewrite not_in_others.
                      rewrite orb_false_r.
                      done. }
                    iSplitL "Hl0 Hnrest".
                    { iExists l0, hd'.
                      iFrame.
                      done. }
                    iFrame.

                 ++ wp_load; wp_pure; wp_pure.
                    cbn in intervals_sorted;
                      destruct intervals_sorted as [_ intervals_sorted].

                    iSpecialize ("IH'" $! intervals_sorted).
                    iApply ("IH'" $! nrest hd' with "[] [Hnrest] [Hns]"); [|done|done|].
                    { iApply "IHtrest". }
                    iNext.
                    iIntros (?) "(% & Hhd' & Hnrest)".
                    iApply "HPost".
                    iSplitR.
                    { iPureIntro.
                      enough (In_nary_tree target (node (low', high') l) = false) as not_in_l.
                      { cbn; cbn in not_in_l.
                        rewrite not_in_l.
                        rewrite orb_false_l.
                        done. }
                      assert (Z.lt high' target).
                      { apply bool_decide_eq_false_1 in Heqb1.
                        lia. }
                      inversion t_wf; subst.
                      apply target_above_below_not_in_node; [|right]; done. }
                    iFrame.
                    iSplitL "Hl0 Hhd'".
                    { iExists l0, hd'.
                      iFrame.
                      done. }
                    iExists ptr', leaves, ns.
                    iFrame.
                    done.

              -- wp_load; wp_pure; wp_pure.
                 cbn in intervals_sorted;
                   destruct intervals_sorted as [_ intervals_sorted].

                 iSpecialize ("IH'" $! intervals_sorted).
                 iApply ("IH'" $! nrest hd' with "[] [Hnrest] [Hns]"); [|done|done|].
                 { iApply "IHtrest". }
                 iNext.
                 iIntros (?) "(% & Hhd' & Hnrest)".
                 iApply "HPost".
                 iSplitR.
                 { iPureIntro.
                   enough (In_nary_tree target (node (low', high') l) = false) as not_in_l.
                   { cbn; cbn in not_in_l.
                     rewrite not_in_l.
                     rewrite orb_false_l.
                     done. }
                   assert (Z.lt target low').
                   { apply bool_decide_eq_false_1 in Heqb0.
                     lia. }
                   inversion t_wf; subst.
                   apply target_above_below_not_in_node; [|left]; done. }
                 iFrame.
                 iSplitL "Hl0 Hhd'".
                 { iExists l0, hd'.
                   iFrame.
                   done. }
                 iExists ptr', leaves, ns.
                 iFrame.
                 done. }

        iApply ("IH'" with "[Hlhd Hns]").
        { iFrame. }
        iNext.
        iIntros (r) "(% & Hlhd & Hns)".
        iApply "HPost".
        iSplitR; [done|].
        iExists ptr, lhd, ns.
        iFrame.
        done.
    Qed.

    Theorem search_bplus_tree_spec (t : tree_spec) (t_wf : tree_spec_wf b t) (v : val) (target : nat) :
      {{{ is_bplus_tree b v t t_wf }}} search_bplus_tree (v, #target)%V {{{ r, RET r; ⌜ r = #(In_bplus_tree target t) ⌝ ∗ is_bplus_tree b v t t_wf }}}.
    Proof using bpos.
      iIntros (Φ) "Hv HPost".

      destruct t as [[low high] | ].
      - iPoseProof ((tree_root_leaf_token_leaf b _ _ _ _ t_wf) with "Hv") as (?) "->".
        iDestruct "Hv" as (? ?) "(% & Hptr & Hlhd)".
        assert (x = #ptr) by (unfold token_leaf_v in H; congruence); subst.
        wp_rec; wp_load; wp_pures.
        iApply (search_list_spec with "Hlhd").
        iNext.
        iIntros (?) "[% Hlhd]".
        iApply "HPost".
        iSplitR; [done|].
        iExists ptr, lhd.
        iFrame.
        done.
      - iApply (search_nary_tree_spec (node interval l) with "[Hv]").
        { inversion t_wf; constructor; try done.
          apply (Forall_impl _ _ _ H4 (nary_tree_wf_remove_len b)); done. }
        { done. }
        iNext.
        iIntros (?) "[% Hv]".
        iApply "HPost".
        iFrame.
        done.
    Qed.

  End bplus_tree_proofs.
End bplus_tree.
