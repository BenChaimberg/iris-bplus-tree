From iris.algebra Require Import numbers.
From iris.heap_lang Require Export proofmode notation.
From iris.proofmode Require Export proofmode.
From iris.prelude Require Import options.
Require Import NaryTree.
Require Import BPlusTree.

Section bplus_tree.
  Section bplus_tree_algos.

    Definition insert_bplus_tree : val :=
      rec: "insert_bplus_tree" "arg" :=
        #().
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

    Theorem insert_bplus_tree_spec (t : tree_spec) (t_wf : tree_spec_wf b t) (v : val) (target : nat) :
      {{{ is_bplus_tree b v t t_wf }}} insert_bplus_tree (v, #target)%V {{{ r, RET r; ⌜ r = #(In_bplus_tree target t) ⌝ ∗ is_bplus_tree b v t t_wf }}}.
    Proof.
    Admitted.

  End bplus_tree_proofs.
End bplus_tree.
