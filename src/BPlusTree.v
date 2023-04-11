From iris.algebra Require Import numbers.
From iris.heap_lang Require Export proofmode notation.
From iris.proofmode Require Export proofmode.
From iris.prelude Require Import options.

Section nary_tree.
  Context (A:Set).
  Context (beq_A : A -> A -> bool).
  Context (ord_A : A -> A -> Prop).

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

  Fixpoint nary_tree_wf (t : nary_tree) :=
    match t with
    | leaf (low, high) vals => Forall (fun a' => ord_A low a' /\ ord_A a' high) vals
    | node (low, high) trees =>
        (fix nary_tree_wf_aux (l : list nary_tree) : Prop :=
           match l with
           | [] => True
           | t :: ts =>
               nary_tree_wf t /\
                 match t with
                 | leaf (low', high') _ => ord_A low low' /\ ord_A high' high
                 | node (low', high') _ => ord_A low low' /\ ord_A high' high
                 end /\
                 nary_tree_wf_aux ts
           end) trees
    end.

  Lemma nary_tree_wf_branches interval branches (wf : nary_tree_wf (node interval branches)) :
    Forall (fun t => nary_tree_wf t) branches.
  Proof.
    induction branches.
    - done.
    - cbn in wf.
      destruct interval as [low high].
      destruct wf as (wf_a & ? & wf_branches).
      constructor; [done|].
      apply IHbranches.
      done.
  Qed.

  Record Tree : Set :=
    mkTree {
        tree : nary_tree;
        tree_wf : nary_tree_wf tree
      }.

  Fixpoint size (t : nary_tree) : nat :=
    match t with
    | leaf _ l => List.length l
    | node _ l => list_sum (map size l)
    end.

  Fixpoint In_list (v : A) (l : list A) :=
    match l with
    | [] => false
    | x :: xs => orb (beq_A x v) (In_list v xs)
    end.

  Fixpoint In_tree (v : A) (t : nary_tree) {struct t} : bool :=
    match t with
    | leaf _ l => In_list v l
    | node _ l => (fix In_aux (l : list nary_tree) :=
                  match l with
                  | [] => false
                  | t :: ts => orb (In_tree v t) (In_aux ts)
                  end) l
    end.
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
  Axiom pinf_max : forall v, (v < pinf).
  Axiom ninf_minax : forall v, (ninf < v).
  Definition tree_spec := Tree tval tord.

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
      (∃ (ptr : loc) (lhd : val), ⌜ size _ (tree _ _ t) < b ⌝ ∗ ⌜ v = token_leaf_v #ptr ⌝ ∗ ptr ↦ ((#low, #high), lhd) ∗ is_list lhd (map (fun (x : tval) => #x) vals))%I.

    Definition branch_node v (t : nary_tree tval) (* (t_wf : nary_tree_wf _ tord t) *) (interval : tval * tval) ts node_size_min (is_node : forall (_ : val) (t : nary_tree tval), nary_tree_wf _ _ t -> iProp) :=
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
              | n :: ns, t :: ts => is_node n (tree _ _ t) (tree_wf _ _ t) ∗ branch_node_list ns ts
              | _, _ => False
              end)
             ns ts))%I.

    Fixpoint is_node (v : val) (t : nary_tree tval) (t_wf : nary_tree_wf _ _ t) {struct t} : iProp :=
      match t as t0 return t = t0 -> iProp with
      | leaf _ interval l => fun _ => leaf_node v {| tree := t; tree_wf := t_wf |} interval l
      | node _ interval ts => fun t_t0 =>
          let t_wf' := nary_tree_wf_branches
                         tval
                         tord
                         interval
                         ts
                         (eq_rect
                            t
                            _
                            t_wf
                            (node _ interval ts)
                            t_t0) in
          let trees := ((fix is_node_list (ts : list (nary_tree tval)) (ts_wf : Forall (fun t => nary_tree_wf _ _ t) ts) : list tree_spec :=
              match ts as ts0 return ts = ts0 -> list tree_spec with
              | [] => fun _ => []
              | t' :: ts' =>
                  fun ts_ts0 =>
                    let ts_wf_cons := Forall_cons_1
                                        (fun x => nary_tree_wf _ _ x)
                                        t'
                                        ts'
                                        (eq_rect ts _ ts_wf (t' :: ts') ts_ts0) in
                    let t'_wf := proj1 ts_wf_cons in
                    let ts'_wf := proj2 ts_wf_cons in
                    {| tree := t'; tree_wf := t'_wf |} :: is_node_list ts' ts'_wf
              end eq_refl) ts t_wf') in
          branch_node v t interval trees (b / 2) is_node
      end eq_refl%I.

    Definition is_bplus_tree (v : val) (t : tree_spec) (* (t_wf : nary_tree_wf _ tord t) *) : iProp :=
      match t with
      | leaf _ interval l => leaf_node v t interval l
      | node _ interval ts => branch_node v t interval ts 2 is_node
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
    Lemma empty_tree_wf : nary_tree_wf _ tord empty_tree.
    Proof. apply Forall_nil_2. Qed.

    Theorem new_bplus_tree_spec:
      {{{ True }}} new_bplus_tree #() {{{ v, RET v; is_bplus_tree b v empty_tree (* empty_tree_wf *) }}}.
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

    Lemma tree_leaf_token_leaf v low high l (* (wf : (nary_tree_wf _ _ (leaf _ (low, high) l))) *):
      is_bplus_tree b v (leaf _ (low, high) l) (* wf *) ⊢ ∃ x, ⌜ v = token_leaf_v x ⌝.
    Proof.
      iIntros "Hv".
      iDestruct "Hv" as (? ?) "[% [% Hv]]".
      iExists #ptr.
      done.
    Qed.

    Lemma tree_node_token_branch v low high l (* (wf : nary_tree_wf _ _ (node _ (low, high) l)) *):
      is_bplus_tree b v (node _ (low, high) l) (* wf *) ⊢ ∃ x, ⌜ v = token_branch_v x ⌝.
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

    Theorem search_bplus_tree_spec (t : tree_spec) (* (wf : nary_tree_wf _ _ t) *) (v : val) (target : nat) :
      {{{ is_bplus_tree b v t (* wf *) }}} search_bplus_tree (v, #target)%V {{{ r, RET r; ⌜ r = #(In_tree _ teqb target t) ⌝ ∗ is_bplus_tree b v t (* wf *) }}}.
    Proof using bpos.
      iIntros (Φ) "Hv HPost".
      iLöb as "IH" forall (v t).
      
      destruct t as [(low & high)|(low & high) ts].
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
               iApply ("IH" $! (token_leaf_v #ptr') (leaf _ (low', high') l) with "[Hptr' Hleaves]").
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
                  cbn in *.
                  
                
    Qed.

  End bplus_tree_proofs.
End bplus_tree.
