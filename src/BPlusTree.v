From iris.algebra Require Import numbers.
From iris.heap_lang Require Export proofmode notation.
From iris.proofmode Require Export proofmode.
From iris.prelude Require Import options.
Import Decidable.

Section nary_tree.
  Context (A:Set).
  Context (eqb_A : A -> A -> bool).
  Hypothesis (eqb_refl : forall a, eqb_A a a = true).
  Hypothesis (eqb_eq : forall a a', eqb_A a a' = true <-> a = a').
  Hypothesis (eqb_dec : forall a a', decidable (eqb_A a a' = true)).
  Context (ord_A : A -> A -> Prop).
  Definition ordeq_A (a a' : A) :=
    eqb_A a a' = true \/ ord_A a a'.
  Hypothesis (ord_trans : Transitive ord_A).

  Inductive nary_tree : Set :=
  | leaf (interval : A * A) (l : list A) : nary_tree
  | node (interval : A * A) (l : list nary_tree) : nary_tree.

  Fixpoint nary_tree_ind'
    (P : nary_tree -> Prop)
    (Pleaf : forall interval vals, P (leaf interval vals))
    (Pnode : forall interval trees, Forall P trees -> P (node interval trees))
    (t : nary_tree) : P t :=
    match t with
    | leaf interval vals => Pleaf interval vals
    | node interval trees =>
        Pnode interval trees
          ((fix nary_tree_ind_aux (l : list nary_tree) : Forall P l :=
             match l with
             | [] => Forall_nil_2 P
             | t :: ts => Forall_cons_2 _ _ _ (nary_tree_ind' P Pleaf Pnode t) (nary_tree_ind_aux ts)
             end) trees)
    end.

  Fixpoint list_sorted (l : list A) :=
    match l with
    | [] => True
    | x :: l =>
        match l with
        | [] => True
        | y :: _ => ord_A x y /\ list_sorted l
        end
    end.

  Fixpoint nary_tree_wf (t : nary_tree) :=
    match t with
    | leaf (low, high) vals =>
        ordeq_A low high /\
          hd low vals = low /\
          List.last vals high = high /\
          list_sorted vals
    | node (low, high) trees =>
        let intervals :=
          map (fun t =>
                 match t with
                 | leaf (low', high') _
                 | node (low', high') _ => (low', high')
                 end)
            trees
        in
        Forall (fun (interval : A * A) =>
                  let (low', high') := interval in
                  ord_A low low' /\ ord_A high' high)
          intervals /\
          (fix trees_wf (l : list nary_tree) : Prop :=
             match l with
             | [] => True
             | t :: rest => nary_tree_wf t /\ trees_wf rest
             end) trees /\
          (fix intervals_sorted (l : list (A * A)) : Prop :=
             match l with
             | [] => True
             | (_, high') :: rest =>
                 match rest with
                 | [] => True
                 | (low', high'') :: rest' =>
                     ord_A high' low'
                 end /\ intervals_sorted rest
             end) intervals
    end.

  Lemma nary_tree_wf_branches interval branches (wf : nary_tree_wf (node interval branches)) :
    Forall (fun t => nary_tree_wf t) branches.
  Proof.
    cbn in wf.
    destruct interval as [low high].
    destruct wf as (_ & wf_branches & _).
    induction branches.
    - done.
    - destruct wf_branches as (wf_a & wf_branches).
      constructor; [done|].
      apply IHbranches.
      done.
  Qed.

  Axiom destruct_list_back : forall (l : list A), {x:A & {init:list A | l = init ++ [x] }}+{l = [] }.

  Definition nary_tree_interval t : (A * A) :=
    match t with
    | leaf i _ => i
    | node i _ => i
    end.

  Fixpoint size (t : nary_tree) : nat :=
    match t with
    | leaf _ l => List.length l
    | node _ l => list_sum (map size l)
    end.

  Fixpoint In_list (v : A) (l : list A) :=
    match l with
    | [] => false
    | x :: xs => orb (eqb_A x v) (In_list v xs)
    end.

  Lemma In_list_split : ∀ (x : A) (l : list A), In_list x l = true → ∃ l1 l2 : list A, l = l1 ++ x :: l2.
  Admitted.

  Lemma In_list_sorted_interval l target : list_sorted l -> In_list target l = true -> ordeq_A (hd target l) target.
  Proof using ord_trans eqb_refl eqb_eq eqb_dec.
    intros sorted_l in_target_l.
    destruct l; [done|].
    cbn.
    apply (orb_prop) in in_target_l.
    destruct in_target_l.
    - left.
      done.
    - apply In_list_split in H.
      destruct H as (l' & ? & ->).
      induction l'.
      + destruct sorted_l as (? & _).
        right.
        done.
      + apply IHl'.
        destruct sorted_l as (ord_a_a0 & sorted_l).
        cbn in sorted_l.
        cbn.
        destruct (l' ++ target :: x); [done|].
        destruct sorted_l as (ord_a0_a1 & ?).
        split; [|done].
        apply (ord_trans _ _ _ ord_a_a0 ord_a0_a1).
  Qed.

  Fixpoint In_tree (v : A) (t : nary_tree) {struct t} : bool :=
    match t with
    | leaf _ l => In_list v l
    | node _ l =>
        (fix In_aux (l : list nary_tree) :=
           match l with
           | [] => false
           | t :: ts => orb (In_tree v t) (In_aux ts)
           end) l
    end.

  Lemma nary_tree_in_interval_not_in_others target interval branch branches (wf : nary_tree_wf (node interval (branch :: branches))) :
    ordeq_A (fst (nary_tree_interval branch)) target /\ ordeq_A target (snd (nary_tree_interval branch)) ->
    false = (fix In_aux (l : list nary_tree) :=
           match l with
           | [] => false
           | t :: ts => orb (In_tree target t) (In_aux ts)
           end) branches.
  Proof.
    intros (? & ?).
    destruct interval.
    cbn in wf.
    destruct wf as (_ & [wf_branch wf_branches] & wf).
    induction branches as [|branch' branches]; [done|].
    destruct branch, branch'.
    - destruct interval as (low & high), interval0 as (low' & high').
      destruct wf_branches as [wf_branch' wf_branches].
      specialize (IHbranches wf_branches).
      cbn in wf.
      destruct wf as (ord_high_low' & wf).
      destruct wf_branch' as (ordeq_low'_high' & _ & _ & sorted_l0).
      assert (ord_A high high') as ord_high_high'.
      { destruct ordeq_low'_high' as [eqb_low'_high' | ord_low'_high'].
        - apply eqb_eq in eqb_low'_high'; subst.
          done.
        - apply (ord_trans _ _ _ ord_high_low' ord_low'_high'). }
      assert (match
                 map
                   (λ t : nary_tree,
                      match t with
                      | leaf (low', high') _ | node (low', high') _ => (low', high')
                      end) branches
               with
               | [] => True
               | (low', _) :: _ => ord_A high low'
               end).
      { destruct branches; [done|].
        destruct wf as (wf & _).
        destruct n, interval;
          cbn in *;
          apply (ord_trans _ _ _ ord_high_high' wf). }
      specialize (IHbranches (conj H1 (proj2 wf)));
        clear H1 wf.
      rewrite <- IHbranches, orb_false_r.
      destruct (In_list target l0) eqn:?; [|done];
        exfalso.
      specialize (In_list_sorted_interval _ _ sorted_l0 Heqb)as ord_low'_target.
  Admitted.

End nary_tree.

Section bplus_tree.
  Definition token_leaf_e v := InjL v.
  Definition token_branch_e v := InjR v.
  Definition token_leaf_v v := InjLV v.
  Definition token_branch_v v := InjRV v.

  (* Variable tval : Set. *)
  (* Declare Scope tval_scope. *)
  (* Delimit Scope tval_scope with t. *)
  (* Variable teqb : tval -> tval -> bool. *)
  (* Variable tord : tval -> tval -> Prop. *)
  (* Notation "v1 < v2" := (tord v1 v2) : tval_scope. *)
  (* Variable tval_val : tval -> val. *)
  (* Notation "# v" := (tval_val v) : tval_scope. *)
  (* Context (tval_dec : forall (v1 v2 : tval), Decision (v1 = v2)). *)

  Definition tval := nat.
  Variable (ninf pinf : tval).
  Definition teqb := Nat.eqb.
  Definition tord := Nat.lt.
  Axiom pinf_max : forall v, (tord v pinf).
  Axiom ninf_minax : forall v, (tord ninf v).
  Definition tree_spec := nary_tree tval.

  Section bplus_tree_model.
    Context `{!heapGS Σ}.
    Notation iProp := (iProp Σ).

    Variable b : nat.
    Hypothesis beven : Zeven b.

    Fixpoint is_list (hd : val) (xs : list val) : iProp :=
      match xs with
      | [] => ⌜hd = NONEV⌝
      | x :: xs => ∃ (l : loc) hd', ⌜hd = SOMEV #l⌝ ∗ l ↦ (x, hd') ∗ is_list hd' xs
    end%I.

    Definition leaf_node v (t : tree_spec) (interval : tval * tval) (vals : list tval) :=
      let (low, high) := interval in
      (∃ (ptr : loc) (lhd : val), ⌜ size _ t < b ⌝ ∗ ⌜ v = token_leaf_v #ptr ⌝ ∗ ptr ↦ ((#low, #high), lhd) ∗ is_list lhd (map (fun (x : tval) => #x) vals))%I.

    Definition branch_node v (t : nary_tree tval) (* (t_wf : nary_tree_wf _ tord t) *) (interval : tval * tval) ts node_size_min (is_node : forall (_ : val) (t : nary_tree tval), (* nary_tree_wf _ _ t ->  *)iProp) :=
      let (low, high) := interval in
      (∃ (ptr : loc) l (ns : list val),
          (* these two should be moved to spec *)
          ⌜ size _ t >= b ⌝ ∗
          ⌜ node_size_min <= length ns <= b ⌝ ∗
          (* the rest are fine ? *)
          ⌜ v = token_branch_v #ptr ⌝ ∗
          ⌜ length ns = length ts ⌝ ∗
          ptr ↦ (((#low), (#high)), l) ∗
          is_list l ns ∗
          ((fix branch_node_list (ns : list val) (ts : list tree_spec) {struct ts} : iProp :=
              match ns, ts with
              | [], [] => True
              | n :: ns, t :: ts => is_node n t ∗ branch_node_list ns ts
              | _, _ => False
              end)
             ns ts))%I.

    Fixpoint is_node (v : val) (t : nary_tree tval) (* (t_wf : nary_tree_wf _ _ t) *) {struct t} : iProp :=
      match t with
      | leaf _ interval l => leaf_node v t (* t_wf *) interval l
      | node _ interval ts =>
         let (low, high) := interval in
         (∃ (ptr : loc) l (ns : list val),
             (* these two should be moved to spec *)
             ⌜ size _ t >= b ⌝ ∗
             ⌜ b / 2 <= length ns <= b ⌝ ∗
             (* the rest are fine ? *)
             ⌜ v = token_branch_v #ptr ⌝ ∗
             ⌜ length ns = length ts ⌝ ∗
             ptr ↦ (((#low), (#high)), l) ∗
             is_list l ns ∗
             ((fix branch_node_list (ns : list val) (ts : list tree_spec) {struct ts} : iProp :=
                 match ns, ts with
                 | [], [] => True
                 | n :: ns, t :: ts => is_node n t ∗ branch_node_list ns ts
                 | _, _ => False
                 end)
                ns ts))
           end%I.

    Record Tree : Set :=
      mkTree {
          tree : nary_tree tval;
          tree_wf : nary_tree_wf _ teqb tord tree
        }.

    Definition is_bplus_tree (v : val) (t : Tree) : iProp :=
      match (tree t) with
      | leaf _ interval l => leaf_node v (tree t) interval l
      | node _ interval ts => branch_node v (tree t) interval ts 2 is_node
      end%I.

  End bplus_tree_model.

  Section bplus_tree_algos.
    Definition new_bplus_tree : val :=
      λ: "_",
        let: "ptr" := ref ((#ninf, #pinf), NONEV) in
        token_leaf_e "ptr".

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
            let: "f" :=
            rec: "search_node_list" "arg" :=
              let: "p" := Fst "arg" in
              let: "target" := Snd "arg" in
              match: "p" with
                NONE => #false
              | SOME "l" =>
                  let: "val" := Fst !"l" in
                  match: "val" with
                    InjL "ptr" =>
                      let: "interval" := Fst !"ptr" in
                      let: "low" := Fst "interval" in
                      let: "high" := Snd "interval" in
                      if: (BinOp LeOp "low" "target") && (BinOp LeOp "target" "high")
                      then "search_bplus_tree" ("val", "target")
                      else "search_node_list" (Snd !"l", "target")
                  | InjR "ptr" =>
                      let: "interval" := Fst !"ptr" in
                      let: "low" := Fst "interval" in
                      let: "high" := Snd "interval" in
                      if: (BinOp LeOp "low" "target") && (BinOp LeOp "target" "high")
                      then "search_bplus_tree" ("val", "target")
                      else "search_node_list" (Snd !"l", "target")
                  end
              end in
              "f" ("lhd", "target")
        end%E.

  End bplus_tree_algos.

  Section bplus_tree_proofs.
    Context `{!heapGS Σ}.
    Notation iProp := (iProp Σ).

    Variable b : nat.
    Hypothesis beven : Zeven b.
    Hypothesis bpos : 0 < b.

    Definition empty_tree := leaf tval (ninf, pinf) [].
    Lemma empty_tree_wf : nary_tree_wf _ teqb tord empty_tree.
    Proof.
      repeat split; auto.
      right.
      apply (pinf_max ninf).
    Qed.

    Theorem new_bplus_tree_spec:
      {{{ True }}} new_bplus_tree #() {{{ v, RET v; is_bplus_tree b v {| tree := empty_tree; tree_wf := empty_tree_wf |} }}}.
    Proof using bpos.
      iIntros (Φ) "_ HPost".
      wp_lam; wp_alloc ptr; wp_pures.
      iApply "HPost".
      iExists ptr, NONEV.
      iSplitR; [done|].
      iSplitR; [done|].
      iSplitL; [done|].
      done.
    Qed.

    Lemma tree_leaf_token_leaf v low high l (wf : (nary_tree_wf _ _ _ (leaf _ (low, high) l))):
      is_bplus_tree b v {| tree := leaf _ (low, high) l; tree_wf := wf |} ⊢ ∃ x, ⌜ v = token_leaf_v x ⌝.
    Proof.
      iIntros "Hv".
      iDestruct "Hv" as (? ?) "[% [% Hv]]".
      iExists #ptr.
      done.
    Qed.

    Lemma tree_node_token_branch v low high l (wf : nary_tree_wf _ _ _ (node _ (low, high) l)):
      is_bplus_tree b v {| tree := node _ (low, high) l; tree_wf := wf |} ⊢ ∃ x, ⌜ v = token_branch_v x ⌝.
    Proof.
      iIntros "Hv".
      iDestruct "Hv" as (? ? ? ?) "(_ & ? & _)".
      iExists #ptr.
      done.
    Qed.

    Lemma bool_decide_true_eqb (x y : nat) :
      bool_decide (#x = #y) = true -> Nat.eqb x y = true.
    Proof.
      clear bpos.
      intro.
      apply bool_decide_eq_true_1 in H.
      injection H as H.
      assert (x = y) by lia; subst.
      rewrite Nat.eqb_refl.
      done.
    Qed.

    Lemma bool_decide_false_eqb (x y : nat) :
      bool_decide (#x = #y) = false -> Nat.eqb x y = false.
    Proof.
      clear bpos.
      intro.
      apply bool_decide_eq_false in H.
      assert (not (Z.of_nat x = Z.of_nat y)) by congruence.
      assert (not (x = y)) by auto.
      apply Nat.eqb_neq in H1.
      done.
    Qed.

    Lemma search_list_spec (v : val) (l : list tval) (target : tval):
      {{{ is_list v (map (fun (x : tval) => (#x)) l) }}} search_list (v, (#target))%V {{{ r, RET r; ⌜ r = #(In_list _ teqb target l) ⌝ ∗ is_list v (map (fun (x : tval) => (#x)) l) }}}.
    Proof.
      clear bpos.
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
          cbn; unfold teqb.
          rewrite (bool_decide_true_eqb _ _ Heqb0).
          done.
        + wp_pures; wp_load; wp_pures.
          iApply ("IH" $! Φ hd' with "Hl").
          iNext.
          iIntros (?) "[% Hl]".
          iApply "HPost".
          iClear "IH".
          iSplitR.
          * iPureIntro.
            unfold In_list, teqb.
            rewrite (bool_decide_false_eqb _ _ Heqb0).
            cbn.
            done.
          * iExists l', hd'.
            iFrame.
            done.
    Qed.

    Theorem search_bplus_tree_spec (t : Tree) (v : val) (target : nat) :
      {{{ is_bplus_tree b v t }}} search_bplus_tree (v, #target)%V {{{ r, RET r; ⌜ r = #(In_tree _ teqb target (tree t)) ⌝ ∗ is_bplus_tree b v t }}}.
    Proof using bpos.
      iIntros (Φ) "Hv HPost".
      iLöb as "IH" forall (v t).

      destruct t.
      destruct (tree0) as [(low & high)|(low & high) ts] eqn:?.
      - iPoseProof (tree_leaf_token_leaf with "Hv") as (?) "->".
        iDestruct "Hv" as (? ?) "(% & % & Hptr & Hlhd)".
        assert (x = #ptr) by (unfold token_leaf_v in H0; congruence); subst.
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
        iDestruct "Hv" as (ptr lhd ns) "(% & % & % & % & Hptr & Hlhd & Hns)".
        assert (x = #ptr) by (unfold token_branch_v in H1; congruence); subst.
        iInduction ns as [|nhd nrest] "IH'"; [rewrite nil_length in H0; lia|].
        destruct ts as [|thd trest]; [rewrite nil_length in H2; lia|].
        iDestruct "Hlhd" as (l0 ?) "(-> & Hl0 & Hnrest)".
        iDestruct "Hns" as "[Hthd Htrest]".
        destruct thd.
        + destruct interval as [low' high'].
          iDestruct "Hthd" as (ptr' leaves) "(% & -> & Hptr' & Hleaves)".
          wp_rec; wp_load; wp_load; wp_load; wp_pures.
          destruct (bool_decide (Z.le (Z.of_nat low') (Z.of_nat target))) eqn:?; wp_pures.
          * destruct (bool_decide (Z.le (Z.of_nat target) (Z.of_nat high'))) eqn:?; wp_pures.
            -- iClear "IH'".
               iApply ("IH" $! (token_leaf_v #ptr') {| tree := (leaf _ (low', high') l); tree_wf := _ |} with "[Hptr' Hleaves]").
               { iExists ptr', leaves.
                 iSplitR; [done|].
                  iSplitR; [done|].
                  iSplitL "Hptr'"; [done|].
                  done. }
                iNext.
                iIntros (?) "[% Htree]".
                iApply "HPost".
                iSplitR.
                { iPureIntro.
                  cbn.
                  apply bool_decide_eq_true_1 in Heqb0.
                  apply bool_decide_eq_true_1 in Heqb1.
                  assert (low' <= target) by lia.
                  assert (target <= high') by lia.
                  assert (ordeq_A _ teqb tord low' target).
                  { destruct H5.
                    - left.
                      apply Nat.eqb_refl.
                    - right.
                      unfold tord.
                      lia. }
                  assert (ordeq_A _ teqb tord target high').
                  { destruct H6.
                    - left.
                      apply Nat.eqb_refl.
                    - right.
                      unfold tord.
                      lia. }
                  rewrite <- (nary_tree_in_interval_not_in_others _ _ _ target (low, high) (leaf tval (low', high') l) trest tree_wf0 (conj H7 H8)).
                  rewrite orb_false_r.
                  done. }
                iExists ptr, (InjRV #l0), (token_leaf_v #ptr' :: nrest).
                iSplitR; [done|].
                iSplitR; [done|].
                iSplitR; [done|].
                iSplitR; [done|].
                iSplitL "Hptr"; [done|].
                iSplitL "Hl0 Hnrest".
                { iExists l0, hd'.
                  iFrame.
                  done. }
                iSplitL "Htree"; [done|].
                done.
            --
    Admitted.

  End bplus_tree_proofs.
End bplus_tree.
