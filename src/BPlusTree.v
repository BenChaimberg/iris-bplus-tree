From iris.algebra Require Import numbers.
From iris.heap_lang Require Export proofmode notation lang.
From iris.proofmode Require Export proofmode.
From iris.heap_lang Require Import proofmode.
From iris.prelude Require Import options.

Section nary_tree.
  Context (A:Set).

  Inductive nary_tree : Set :=
  | leaf : list A -> nary_tree
  | node : list nary_tree -> nary_tree.

  Fixpoint size (t : nary_tree) : nat :=
    match t with
    | leaf l => List.length l
    | node l => list_sum (map size l)
    end.

  Fixpoint In (v : A) (t : nary_tree) {struct t} : Prop :=
    match t with
    | leaf l => List.In v l
    | node l => (fix In_list (l : list nary_tree) :=
                  match l with
                  | [] => False
                  | t :: ts => In v t \/ In_list ts
                  end) l
    end.
End nary_tree.

Section bplus_tree_algos.
  Definition new_bplus_tree : val :=
    λ: "_", ref NONEV.

End bplus_tree_algos.

Section bplus_tree_model.
  Context `{!heapGS Σ}.
  Notation iProp := (iProp Σ).

  Variable b : nat.
  Hypothesis beven : Zeven b.

  Definition tree_spec := nary_tree val.

  Fixpoint is_list (hd : val) (xs : list val) : iProp :=
    match xs with
    | [] => ⌜hd = NONEV⌝
    | x :: xs => ∃ (l : loc) hd', ⌜hd = SOMEV #l⌝ ∗ l ↦ (x,hd') ∗ is_list hd' xs
  end%I.

  Fixpoint is_node (v : val) (t : tree_spec) {struct t} : iProp :=
    match t with
    | leaf _ l => ⌜ size _ t < b ⌝ -∗ is_list v l
    | node _ ts =>
        ⌜ size _ t >= b ⌝ -∗
          (∃ (ns : list val),
              ⌜ b / 2 <= length ns <= b ⌝ ∗
              ⌜ length ns = length ts ⌝ ∗
              is_list v ns ∗
              ((fix is_internal_node_list (ns : list val) (ts : list tree_spec) {struct ts} : iProp :=
                  match ns, ts with
                  | [], [] => True
                  | n :: ns, t :: ts => is_node n t ∗ is_internal_node_list ns ts
                  | _, _ => False
                end)
                 ns ts))
    end%I.

  Definition is_root_node (v : val) (t : tree_spec) : iProp :=
    match t with
    | leaf _ l => ⌜ size _ t < b ⌝ -∗ is_list v l
    | node _ ts =>
        ⌜ size _ t >= b ⌝ -∗
          (∃ ns : list val,
              ⌜ 2 <= length ns <= b ⌝ ∗
              is_list v ns ∗
              ((fix is_branching_root_node_list (ns : list val) (ts : list tree_spec) :=
                 match ns, ts with
                 | [], [] => True
                 | n :: ns, t :: ts => is_node n t ∗ is_branching_root_node_list ns ts
                 | _, _ => False
                 end)
                 ns ts))
    end%I.

  Definition is_bplus_tree (v : val) (t : tree_spec) : iProp :=
    (∃ (l : loc) (r : val), ⌜v = #l⌝ ∗ l ↦ r ∗ is_root_node r t)%I.

End bplus_tree_model.

Section bplus_tree_proofs.
  Context `{!heapGS Σ}.
  Notation iProp := (iProp Σ).

  Variable b : nat.
  Hypothesis beven : Zeven b.

  Theorem new_bplus_tree_spec:
    {{{ True }}} new_bplus_tree #() {{{ v, RET v; is_bplus_tree b v (leaf val []) }}}.
  Proof.
    iIntros (Φ) "_ HPost".
    wp_lam; wp_alloc v.
    iApply "HPost".
    iExists v, NONEV.
    iFrame.
    done.
  Qed.

End bplus_tree_proofs.
