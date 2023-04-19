From iris.algebra Require Import numbers.
From iris.heap_lang Require Export proofmode notation.
From iris.proofmode Require Export proofmode.
From iris.prelude Require Import options.
Import Decidable.
Require Import NaryTree.

Theorem nat_strong_ind:
  forall P : nat -> Prop,
    (forall n : nat, (forall k : nat, (k < n -> P k)) -> P n) ->
    forall n : nat, P n.
Proof.
  intros P IH n.
  enough (H0: forall k, k <= n -> P k) by (apply H0; done).
  induction n.
  - intros.
    assert (k = 0) by lia; subst.
    apply IH.
    lia.
  - intros.
    apply IH.
    intros.
    assert (k0 <= n) by lia.
    apply (IHn _ H1).
Qed.

Section bplus_tree.
  Definition token_leaf_e v := InjL v.
  Definition token_branch_e v := InjR v.
  Definition token_leaf_v v := InjLV v.
  Definition token_branch_v v := InjRV v.

  Definition tval := nat.
  Variable (ninf pinf : tval).
  Definition teqb := Nat.eqb.
  Definition tord := Nat.lt.
  Axiom pinf_max : forall v, (tord v pinf).
  Axiom ninf_minax : forall v, (tord ninf v).

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

  Definition tree_spec := bplus_tree.
  Definition tree_spec_wf := bplus_tree_wf b.

  Section bplus_tree_model.
    Context `{!heapGS Σ}.
    Notation iProp := (iProp Σ).

    Fixpoint is_list (hd : val) (xs : list val) : iProp :=
      match xs with
      | [] => ⌜hd = NONEV⌝
      | x :: xs => ∃ (l : loc) hd', ⌜hd = SOMEV #l⌝ ∗ l ↦ (x, hd') ∗ is_list hd' xs
    end%I.

    Definition leaf_node v (interval : tval * tval) (vals : list tval) :=
      let (low, high) := interval in
      (∃ (ptr : loc) (lhd : val), ⌜ v = token_leaf_v #ptr ⌝ ∗ ptr ↦ ((#low, #high), lhd) ∗ is_list lhd (map (fun (x : tval) => #x) vals))%I.

    Fixpoint is_node (v : val) (t : nary_tree) {struct t} : iProp :=
      match t with
      | leaf interval l => leaf_node v interval l
      | node interval ts =>
         let (low, high) := interval in
         (∃ (ptr : loc) l (ns : list val),
             ⌜ v = token_branch_v #ptr ⌝ ∗
             ptr ↦ (((#low), (#high)), l) ∗
             is_list l ns ∗
             ((fix branch_node_list (ns : list val) (ts : list nary_tree) {struct ts} : iProp :=
                 match ns, ts with
                 | [], [] => True
                 | n :: ns, t :: ts => is_node n t ∗ branch_node_list ns ts
                 | _, _ => False
                 end)
                ns ts))
           end%I.

    Definition is_bplus_tree (v : val) (t : tree_spec) (t_wf : tree_spec_wf t) : iProp :=
      match t with
      | root_leaf interval l => leaf_node v interval l
      | root_node interval ts => is_node v (node interval ts)
      end%I.

  End bplus_tree_model.

  Section bplus_tree_proofs.
    Context `{!heapGS Σ}.
    Notation iProp := (iProp Σ).

    Lemma tree_root_leaf_token_leaf v low high l (wf : (tree_spec_wf (root_leaf (low, high) l))):
      is_bplus_tree v (root_leaf (low, high) l) wf ⊢ ∃ x, ⌜ v = token_leaf_v x ⌝.
    Proof.
      iIntros "Hv".
      iDestruct "Hv" as (? ?) "[% Hv]".
      iExists #ptr.
      done.
    Qed.

    Lemma tree_leaf_token_leaf v low high l :
      is_node v (leaf (low, high) l) ⊢ ∃ x, ⌜ v = token_leaf_v x ⌝.
    Proof.
      iIntros "Hv".
      iDestruct "Hv" as (? ?) "[% Hv]".
      iExists #ptr.
      done.
    Qed.

    Lemma tree_root_node_token_branch v low high l (wf : tree_spec_wf (root_node (low, high) l)):
      is_bplus_tree v (root_node (low, high) l) wf ⊢ ∃ x, ⌜ v = token_branch_v x ⌝.
    Proof.
      iIntros "Hv".
      iDestruct "Hv" as (? ? ? ?) "(_ & ? & _)".
      iExists #ptr.
      done.
    Qed.

    Lemma tree_node_token_branch v low high l :
      is_node v (node (low, high) l) ⊢ ∃ x, ⌜ v = token_branch_v x ⌝.
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

  End bplus_tree_proofs.
End bplus_tree.
