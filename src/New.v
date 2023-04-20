From iris.algebra Require Import numbers.
From iris.heap_lang Require Export proofmode notation.
From iris.proofmode Require Export proofmode.
From iris.prelude Require Import options.
Require Import NaryTree.
Require Import BPlusTree.

Section bplus_tree.
  Variable (ninf pinf : tval).
  Axiom pinf_max : forall v, (Z.lt v pinf).
  Axiom ninf_minax : forall v, (Z.lt ninf v).

  Variable b : nat.
  Hypothesis beven : Zeven b.
  Hypothesis bpos : 0 < b.

  Section bplus_tree_algos.
    Definition new_bplus_tree : val :=
      λ: "_",
        let: "ptr" := ref ((#ninf, #pinf), NONEV) in
        token_leaf_e "ptr".

  End bplus_tree_algos.

  Section bplus_tree_proofs.
    Context `{!heapGS Σ}.
    Notation iProp := (iProp Σ).

    Definition empty_tree := root_leaf (ninf, pinf) [].
    Lemma empty_tree_wf : tree_spec_wf b empty_tree.
    Proof using beven bpos.
      constructor; try done.
      - specialize (pinf_max ninf) as ?.
        lia.
      - split; try done.
        specialize (bge2).
        cbn.
        lia.
    Qed.

    Theorem new_bplus_tree_spec:
      {{{ True }}} new_bplus_tree #() {{{ v, RET v; is_bplus_tree b v empty_tree empty_tree_wf }}}.
    Proof using bpos.
      iIntros (Φ) "_ HPost".
      wp_lam; wp_alloc ptr; wp_pures.
      iApply "HPost".
      iExists ptr, NONEV.
      iSplitR; [done|].
      iSplitL; [done|].
      done.
    Qed.
  End bplus_tree_proofs.
End bplus_tree.
