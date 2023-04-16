From iris.algebra Require Import numbers.
From iris.heap_lang Require Export proofmode notation.
From iris.proofmode Require Export proofmode.
From iris.prelude Require Import options.
Import Decidable.

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

Section nary_tree.
  Definition A := nat.
  Definition eqb_A := Nat.eqb.
  Definition ord_A := Nat.lt.
  Definition ordeq_A := Nat.le.

  Context (b : nat).

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
  
  Inductive nary_tree_wf' : nary_tree -> Prop :=
    | leaf_wf low high vals :
        ordeq_A low high ->
          hd low vals = low ->
          List.last vals high = high ->
          (** hidden so we don't need to deal with root node shenanigans *)
          (* b / 2 <= length vals <= b -> *)
          list_sorted vals ->
          nary_tree_wf' (leaf (low, high) vals)
    | node_wf low high trees :
        let intervals :=
          map (fun t =>
                 match t with
                 | leaf (low', high') _
                 | node (low', high') _ => (low', high')
                 end)
            trees
        in
        (** hidden because really hard to maintain *)
        (* b / 2 <= length trees <= b -> *)
        ordeq_A low high ->
        Forall (fun (interval : A * A) =>
                  let (low', high') := interval in
                  ord_A low low' /\ ord_A high' high)
          intervals ->
        Forall nary_tree_wf' trees ->
        (fix intervals_sorted (l : list (A * A)) : Prop :=
           match l with
           | [] => True
           | (_, high') :: rest =>
               match rest with
               | [] => True
               | (low', high'') :: rest' =>
                   ord_A high' low'
               end /\ intervals_sorted rest
           end) intervals ->
        nary_tree_wf' (node (low, high) trees).

  Lemma nary_tree_wf_branches interval branches (wf : nary_tree_wf' (node interval branches)) :
    Forall nary_tree_wf' branches.
  Proof.
    destruct interval as [low high].
    inversion wf; subst.
    done.
  Qed.

  Lemma destruct_list_back : forall (l : list A), {x:A & {init:list A | l = init ++ [x] }}+{l = [] }.
  Proof.
    induction l.
    - right.
      done.
    - left.
      destruct IHl.
      + destruct s as [x [init ->]].
        exists x, (a :: init).
        done.
      + rewrite e.
        exists a, [].
        done.
  Qed.

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
  Proof.
    intros x l in_x_l.
    induction l; [done|].
    cbn in in_x_l.
    apply orb_prop in in_x_l.
    destruct in_x_l.
    - exists [], l.
      unfold eqb_A in H.
      apply beq_nat_true in H; subst.
      done.
    - destruct (IHl H) as (l1 & l2 & ->).
      exists (a :: l1), l2.
      done.
  Qed.

  Lemma In_list_sorted_interval l target : list_sorted l -> In_list target l = true -> ordeq_A (hd target l) target.
  Proof.
    clear b.
    intros sorted_l in_target_l.
    destruct l; [done|].
    cbn.
    apply (orb_prop) in in_target_l.
    destruct in_target_l.
    - apply beq_nat_true in H.
      unfold ordeq_A.
      lia.
    - apply In_list_split in H.
      destruct H as (l' & ? & ->).
      induction l'.
      + destruct sorted_l as (? & _).
        unfold ord_A, ordeq_A in *.
        lia.
      + apply IHl'.
        destruct sorted_l as (ord_a_a0 & sorted_l).
        cbn in sorted_l.
        cbn.
        destruct (l' ++ target :: x); [done|].
        destruct sorted_l as (ord_a0_a1 & ?).
        split; [|done].
        unfold ord_A in *.
        lia.
  Qed.

  Lemma target_above_not_in_list target high vals:
    high < target ->
    List.last vals high = high ->
    list_sorted vals ->
    In_list target vals = false.
  Proof.
    intros high_lt_target last_vals_high sorted_vals.
    destruct (destruct_list_back vals) as [[x [init ?]]|]; subst; [|done].
    rewrite last_last in last_vals_high; subst.
    induction init.
    - cbn.
      rewrite orb_false_r.
      unfold eqb_A.
      enough (high ≠ target) by (apply Nat.eqb_neq; done).
      lia.
    - assert (list_sorted (init ++ [high])).
      { cbn in sorted_vals.
        assert (exists y l, init ++ [high] = y :: l).
        { destruct init.
          - exists high, []; done.
          - exists a0, (init ++ [high]); done. }
        destruct H as (? & ? & ?).
        rewrite H in sorted_vals.
        destruct sorted_vals as (_ & ?).
        rewrite H.
        done. }
      specialize (IHinit H).
      cbn.
      rewrite IHinit.
      rewrite orb_false_r.
      clear H IHinit.
      induction init.
      + cbn in sorted_vals.
        enough (a ≠ target).
        { apply Nat.eqb_neq; done. }
        unfold ord_A in sorted_vals.
        lia.
      + apply IHinit.
        cbn in sorted_vals.
        destruct sorted_vals as [? sorted_vals].
        cbn.
        assert (exists y l, init ++ [high] = y :: l).
        { destruct init.
          - exists high, []; done.
          - exists a1, (init ++ [high]); done. }
        destruct H0 as (? & ? & ?).
        rewrite H0 in sorted_vals; rewrite H0.
        destruct sorted_vals.
        unfold ord_A in *.
        split; [lia|done].
  Qed.

  Lemma target_below_not_in_list target low vals:
    target < low ->
    hd low vals = low ->
    list_sorted vals ->
    In_list target vals = false.
  Proof.
    intros target_let_low hd_vals_low sorted_vals.
    destruct vals; [done|].
    cbn in *; subst.
    assert (eqb_A low target = false).
    { enough (low ≠ target).
      { apply Nat.eqb_neq; done. }
      lia. }
    rewrite H.
    rewrite orb_false_l.
    induction vals; [done|].
    cbn.
    destruct sorted_vals as [? sorted_vals].
    assert (eqb_A a target = false).
    { enough (a ≠ target).
      { apply Nat.eqb_neq; done. }
      unfold ord_A in *.
      lia. }
    rewrite H1.
    rewrite orb_false_l.
    apply IHvals.
    cbn in sorted_vals.
    destruct vals; [done|].
    unfold ord_A in *.
    destruct sorted_vals.
    split; [lia|done].
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

  Lemma target_below_not_in_node target t:
    nary_tree_wf' t ->
    ord_A target (fst (nary_tree_interval t)) ->
    In_tree target t = false.
  Proof.
    intros.
    induction t using nary_tree_ind';
      destruct interval as [low high].
    - cbn.
      inversion H; subst.
      apply (target_below_not_in_list _ low); done.
    - cbn.
      induction trees as [|t trees]; [done|].
      assert (In_tree target t = false).
      { apply Forall_cons in H1.
        inversion H; subst.
        apply Forall_cons in H7.
        destruct H7.
        apply (proj1 H1); [done|].
        cbn in H0.
        cbn in intervals.
        apply Forall_cons in H6.
        destruct H6.
        destruct t;
          destruct interval as [low' high'];
          cbn;
          unfold ord_A, ordeq_A in *;
          lia. }
      rewrite H2.
      rewrite orb_false_l.
      apply IHtrees.
      + apply Forall_cons in H1.
        destruct H1.
        done.
      + inversion H; subst.
        constructor.
        * done.
        * cbn in intervals.
          apply Forall_cons in H7.
          destruct H7.
          done.
        * apply Forall_cons in H8.
          destruct H8.
          done.
        * cbn in intervals, H9.
          destruct t;
            destruct interval;
            destruct H9;
            done.
      + cbn in H0; cbn.
        done.
  Qed.

  Lemma target_above_not_in_node target t:
    nary_tree_wf' t ->
    ord_A (snd (nary_tree_interval t)) target ->
    In_tree target t = false.
  Proof.
    intros.
    induction t using nary_tree_ind';
      destruct interval as [low high].
    - cbn.
      inversion H; subst.
      apply (target_above_not_in_list _ high); done.
    - cbn.
      induction trees as [|t trees]; [done|].
      assert (In_tree target t = false).
      { apply Forall_cons in H1.
        inversion H; subst.
        apply Forall_cons in H7.
        destruct H7.
        apply (proj1 H1); [done|].
        cbn in H0.
        cbn in intervals.
        apply Forall_cons in H6.
        destruct H6.
        destruct t;
          destruct interval as [low' high'];
          cbn;
          unfold ord_A, ordeq_A in *;
          lia. }
      rewrite H2.
      rewrite orb_false_l.
      apply IHtrees.
      + apply Forall_cons in H1.
        destruct H1.
        done.
      + inversion H; subst.
        constructor.
        * done.
        * cbn in intervals.
          apply Forall_cons in H7.
          destruct H7.
          done.
        * apply Forall_cons in H8.
          destruct H8.
          done.
        * cbn in intervals, H9.
          destruct t;
            destruct interval;
            destruct H9;
            done.
      + cbn in H0; cbn.
        done.
  Qed.

  Lemma nary_tree_in_interval_not_in_others target interval branch branches (wf : nary_tree_wf' (node interval (branch :: branches))) :
    ordeq_A (fst (nary_tree_interval branch)) target /\ ordeq_A target (snd (nary_tree_interval branch)) ->
    (fix In_aux (l : list nary_tree) :=
           match l with
           | [] => false
           | t :: ts => orb (In_tree target t) (In_aux ts)
           end) branches = false.
  Proof.
    intros (? & ?).
    inversion wf; subst;
      clear wf H3 low high H4.
    apply Forall_cons in H5.
    destruct H5 as [wf_branch wf_branches].
    induction branches as [|branch' branches]; [done|].
    apply Forall_cons in wf_branches.
    destruct wf_branches as [wf_branch' wf_branches].

    destruct branch, branch'.
    - destruct interval as (low & high), interval0 as (low' & high').
      inversion wf_branch'; subst.

      assert ((fix In_aux (l : list nary_tree) : bool :=
                 match l with
                 | [] => false
                 | t :: ts => In_tree target t || In_aux ts
                 end) branches = false).
      { apply IHbranches; clear IHbranches.
        - done.
        - cbn.
          cbn in intervals, H6.
          destruct H6 as (? & ? & ?).
          split; [|done].
          destruct branches; [done|].
          cbn in H2; cbn.
          destruct n;
            destruct interval;
            unfold ord_A, ordeq_A in *;
            lia. }
      rewrite H1.
      clear H1 IHbranches.
      rewrite orb_false_r.

      cbn in intervals, H6.
      destruct H6 as (ord_high_low' & _).
      cbn; cbn in H0.

      assert (ord_A target low') as ord_target_low'
          by (unfold ord_A, ordeq_A in *; lia).

      apply (target_below_not_in_list _ low'); done.

    - destruct interval as (low & high), interval0 as (low' & high').
      inversion wf_branch'; subst.

      assert ((fix In_aux (l : list nary_tree) : bool :=
                 match l with
                 | [] => false
                 | t :: ts => In_tree target t || In_aux ts
                 end) branches = false).
      { apply IHbranches; clear IHbranches.
        - done.
        - cbn.
          cbn in intervals, H6.
          destruct H6 as (? & ? & ?).
          split; [|done].
          destruct branches; [done|].
          cbn in H2; cbn.
          destruct n;
            destruct interval;
            unfold ord_A, ordeq_A in *;
            lia. }
      rewrite H1.
      clear H1 IHbranches.
      rewrite orb_false_r.

      cbn in intervals, H6.
      destruct H6 as (ord_high_low' & _).
      cbn in H0.
      assert (ord_A target low') as ord_target_low'
          by (unfold ord_A, ordeq_A in *; lia).

      apply (target_below_not_in_node); done.

    - destruct interval as (low & high), interval0 as (low' & high').
      inversion_clear wf_branch' as [? ? ? ordeq_low'_high' hd_vals_low' last_vals_high' sorted_vals |].

      assert ((fix In_aux (l : list nary_tree) : bool :=
                 match l with
                 | [] => false
                 | t :: ts => In_tree target t || In_aux ts
                 end) branches = false)
        as not_in_branches.
      { apply IHbranches; clear IHbranches.
        - done.
        - cbn.
          cbn in intervals, H6.
          destruct H6 as (? & ? & ?).
          split; [|done].
          destruct branches; [done|].
          cbn in H2; cbn.
          destruct n;
            destruct interval;
            unfold ord_A, ordeq_A in *;
            lia. }
      rewrite not_in_branches.
      rewrite orb_false_r.

      cbn in intervals, H6.
      destruct H6 as (ord_high_low' & _).
      cbn; cbn in H0.

      assert (ord_A target low') as ord_target_low'
          by (unfold ord_A, ordeq_A in *; lia).

      apply (target_below_not_in_list _ low'); done.
    - destruct interval as (low & high), interval0 as (low' & high').
      inversion wf_branch'; subst.

      assert ((fix In_aux (l : list nary_tree) : bool :=
                 match l with
                 | [] => false
                 | t :: ts => In_tree target t || In_aux ts
                 end) branches = false).
      { apply IHbranches; clear IHbranches.
        - done.
        - cbn.
          cbn in intervals, H6.
          destruct H6 as (? & ? & ?).
          split; [|done].
          destruct branches; [done|].
          cbn in H2; cbn.
          destruct n;
            destruct interval;
            unfold ord_A, ordeq_A in *;
            lia. }
      rewrite H1.
      clear H1 IHbranches.
      rewrite orb_false_r.

      cbn in intervals, H6.
      destruct H6 as (ord_high_low' & _).
      cbn in H0.
      assert (ord_A target low') as ord_target_low'
          by (unfold ord_A, ordeq_A in *; lia).

      apply (target_below_not_in_node); done.
  Qed.

End nary_tree.

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

  Lemma b2pos : 0 < b / 2.
  Proof using beven bpos.
    induction b using nat_strong_ind.
    destruct n; [done|].
    destruct n; [done|].
    destruct n; [cbn; lia|].
    assert (S n < S (S (S n))) by lia.
    assert (Zeven (S n)).
    { apply Zodd_pred in beven.
      apply Zeven_pred in beven.
      assert (Z.pred (Z.pred (S (S (S n)))) = S n) by lia.
      rewrite <- H1.
      done. }
    assert (0 < S n) by lia.
    specialize (H (S n) H0 H1 H2).
    assert (2 ≠ 0) by lia.
    assert (S n ≤ S (S (S n))) by lia.
    specialize (Nat.div_le_mono (S n) (S (S (S n))) 2 H3 H4) as ?.
    lia.
  Qed.

  Definition tree_spec := nary_tree.
  Definition tree_spec_wf := nary_tree_wf'.

  Section bplus_tree_model.
    Context `{!heapGS Σ}.
    Notation iProp := (iProp Σ).

    Fixpoint is_list (hd : val) (xs : list val) : iProp :=
      match xs with
      | [] => ⌜hd = NONEV⌝
      | x :: xs => ∃ (l : loc) hd', ⌜hd = SOMEV #l⌝ ∗ l ↦ (x, hd') ∗ is_list hd' xs
    end%I.

    Definition leaf_node v (t : tree_spec) (* (t_wf : tree_spec_wf t) *) (interval : tval * tval) (vals : list tval) :=
      let (low, high) := interval in
      (∃ (ptr : loc) (lhd : val), ⌜ size t < b ⌝ ∗ ⌜ v = token_leaf_v #ptr ⌝ ∗ ptr ↦ ((#low, #high), lhd) ∗ is_list lhd (map (fun (x : tval) => #x) vals))%I.

    Definition branch_node v (t : tree_spec) (* (t_wf : tree_spec_wf t) *) (interval : tval * tval) ts (is_node : forall (_ : val) (t : tree_spec), (* tree_spec_wf t ->  *)iProp) :=
      let (low, high) := interval in
      (∃ (ptr : loc) l (ns : list val),
          ⌜ v = token_branch_v #ptr ⌝ ∗
          ptr ↦ (((#low), (#high)), l) ∗
          is_list l ns ∗
          ((fix branch_node_list (ns : list val) (ts : list tree_spec) {struct ts} : iProp :=
              match ns, ts with
              | [], [] => True
              | n :: ns, t :: ts => is_node n t ∗ branch_node_list ns ts
              | _, _ => False
              end)
             ns ts))%I.

    Lemma S_cong m n :
      m = n -> S m = S n.
    Proof. clear bpos. lia. Qed.

    Lemma branch_node_lengths_eq is_node ns ts :
      (((fix branch_node_list (ns : list val) (ts : list tree_spec) {struct ts} : iProp :=
          match ns, ts with
          | [], [] => True
          | n :: ns, t :: ts => is_node n t ∗ branch_node_list ns ts
          | _, _ => False
          end)
         ns ts) ⊢ ⌜ length ns = length ts ⌝)%I.
    Proof.
      iIntros "Hnodes".
      iInduction ns as [] "IH" forall (ts).
      - destruct ts; done.
      - destruct ts; [done|].
        iDestruct "Hnodes" as "[_ Hnodes]".
        iSpecialize ("IH" $! ts with "Hnodes").
        cbn.
        iDestruct "IH" as "->".
        done.
    Qed.

    Fixpoint is_node (v : val) (t : tree_spec) (* (t_wf : tree_spec_wf t) *) {struct t} : iProp :=
      match t with
      | leaf interval l => leaf_node v t interval l
      | node interval ts =>
         let (low, high) := interval in
         (∃ (ptr : loc) l (ns : list val),
             ⌜ v = token_branch_v #ptr ⌝ ∗
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
          tree : tree_spec;
          tree_wf : tree_spec_wf tree
        }.

    Definition is_bplus_tree (v : val) (t : Tree) : iProp :=
      match (tree t) with
      | leaf interval l => leaf_node v (tree t) interval l
      | node interval ts => branch_node v (tree t) interval ts is_node
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


    Definition empty_tree := leaf (ninf, pinf) [].
    Lemma empty_tree_wf : tree_spec_wf empty_tree.
    Proof.
      clear bpos beven.
      constructor; try done.
      specialize (pinf_max ninf) as ?.
      unfold ordeq_A, tord in *.
      lia.
    Qed.

    Theorem new_bplus_tree_spec:
      {{{ True }}} new_bplus_tree #() {{{ v, RET v; is_bplus_tree v {| tree := empty_tree; tree_wf := empty_tree_wf |} }}}.
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

    Lemma tree_leaf_token_leaf v low high l (wf : (tree_spec_wf (leaf (low, high) l))):
      is_bplus_tree v {| tree := leaf (low, high) l; tree_wf := wf |} ⊢ ∃ x, ⌜ v = token_leaf_v x ⌝.
    Proof.
      iIntros "Hv".
      iDestruct "Hv" as (? ?) "[% [% Hv]]".
      iExists #ptr.
      done.
    Qed.

    Lemma tree_node_token_branch v low high l (wf : tree_spec_wf (node (low, high) l)):
      is_bplus_tree v {| tree := node (low, high) l; tree_wf := wf |} ⊢ ∃ x, ⌜ v = token_branch_v x ⌝.
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
      {{{ is_list v (map (fun (x : tval) => (#x)) l) }}} search_list (v, (#target))%V {{{ r, RET r; ⌜ r = #(In_list target l) ⌝ ∗ is_list v (map (fun (x : tval) => (#x)) l) }}}.
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
          cbn; unfold eqb_A.
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
            unfold In_list, eqb_A.
            rewrite (bool_decide_false_eqb _ _ Heqb0).
            cbn.
            done.
          * iExists l', hd'.
            iFrame.
            done.
    Qed.

    Theorem search_bplus_tree_spec (t : Tree) (v : val) (target : nat) :
      {{{ is_bplus_tree v t }}} search_bplus_tree (v, #target)%V {{{ r, RET r; ⌜ r = #(In_tree target (tree t)) ⌝ (* ∗ is_bplus_tree v t *) }}}.
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
        done.

      - iPoseProof (tree_node_token_branch with "Hv") as (?) "->".
        iDestruct "Hv" as (ptr lhd ns) "(% & Hptr & Hlhd & Hns)".
        assert (x = #ptr) by (unfold token_branch_v in H; congruence); subst.
        wp_rec; wp_load; wp_proj; wp_let; wp_pure; wp_pure.
        iEval (unfold tree) in "HPost".
        iClear "Hptr".
        iInduction ts as [|thd trest] "IH'" forall (ns lhd).
        + destruct ns as [|nhd nrest]; [|done].
          iDestruct "Hlhd" as "->".
          wp_pures.
          iApply "HPost".
          done.
        + destruct ns as [|nhd nrest]; [done|].
          iDestruct "Hlhd" as (l0 ?) "(-> & Hl0 & Hnrest)".
          destruct thd.
          * destruct interval as [low' high'].
            iDestruct "Hns" as "[Hthd Hns]".
            iDestruct "Hthd" as (ptr' leaves) "(% & -> & Hptr' & Hleaves)".
            wp_load; wp_load; wp_pures.
            destruct (bool_decide (Z.le (Z.of_nat low') (Z.of_nat target))) eqn:?; wp_pures.
            -- destruct (bool_decide (Z.le (Z.of_nat target) (Z.of_nat high'))) eqn:?; wp_pures.
               ++ iClear "IH'".
                  assert (tree_spec_wf (leaf (low', high') l)) as leaf_wf.
                  { inversion_clear tree_wf0
                      as [| ? ? ? ? ord_low_high intervals_in_interval trees_wf intervals_sorted ].
                    apply Forall_cons in trees_wf.
                    destruct trees_wf.
                    done. }
                  iApply ("IH" $! (token_leaf_v #ptr') {| tree := (leaf (low', high') l); tree_wf := leaf_wf |} with "[Hptr' Hleaves]").
                  { iExists ptr', leaves.
                    iSplitR; [done|].
                    iSplitR; [done|].
                    iSplitL "Hptr'"; [done|].
                    done. }
                  iNext.
                  iIntros (?) "%".
                  iApply "HPost".
                  iPureIntro.
                  cbn.
                  apply bool_decide_eq_true_1 in Heqb0.
                  apply bool_decide_eq_true_1 in Heqb1.
                  assert (low' <= target) as low'_le_target by lia.
                  assert (target <= high') as target_le_high' by lia.
                  assert (ordeq_A low' target) as ordeq_low'_target.
                  { destruct low'_le_target.
                    - left.
                    - right.
                      lia. }
                  assert (ordeq_A target high') as ordeq_target_high'.
                  { destruct target_le_high'.
                    - left.
                    - right.
                      lia. }
                  rewrite (nary_tree_in_interval_not_in_others target (low, high) (leaf (low', high') l) trest tree_wf0 (conj ordeq_low'_target ordeq_target_high')).
                  rewrite orb_false_r.
                  done.

               ++ wp_load; wp_pure; wp_pure.
                  assert (tree_spec_wf (node (low, high) trest)) as x_wf.
                  { inversion_clear tree_wf0
                      as [| ? ? ? ? ord_low_high intervals_in_interval trees_wf intervals_sorted ].
                    cbn in intervals.
                    apply Forall_cons in intervals_in_interval.
                    destruct intervals_in_interval.
                    apply Forall_cons in trees_wf.
                    destruct trees_wf.
                    cbn in intervals_sorted.
                    destruct intervals_sorted.
                    apply node_wf; try done. }

                  iApply ("IH'" $! x_wf nrest hd' with "[Hnrest] [Hns]");
                    iClear "IH'";
                    try iFrame.
                  iIntros (?) "%".
                  iApply "HPost".
                  iPureIntro.
                  enough (In_list target l = false) as not_in_l.
                  { cbn.
                    rewrite not_in_l.
                    rewrite orb_false_l.
                    done. }
                  assert (high' < target).
                  { apply bool_decide_eq_false_1 in Heqb1.
                    lia. }
                  inversion_clear tree_wf0
                      as [| ? ? ? ? ord_low_high intervals_in_interval trees_wf intervals_sorted ].
                  apply Forall_cons in trees_wf.
                  destruct trees_wf as [leaf_wf _].
                  inversion leaf_wf; subst.
                  apply (target_above_not_in_list _ high' _); done.

            -- wp_load; wp_pure; wp_pure.
               assert (tree_spec_wf (node (low, high) trest)) as x_wf.
               { inversion_clear tree_wf0
                      as [| ? ? ? ? ord_low_high intervals_in_interval trees_wf intervals_sorted ].
                    cbn in intervals.
                    apply Forall_cons in intervals_in_interval.
                    destruct intervals_in_interval.
                    apply Forall_cons in trees_wf.
                    destruct trees_wf.
                    cbn in intervals_sorted.
                    destruct intervals_sorted.
                    apply node_wf; try done. }
               iApply ("IH'" $! x_wf nrest hd' with "[Hnrest] [Hns]");
                 iClear "IH'";
                 try iFrame.
               iIntros (?) "%".
               iApply "HPost".
               iPureIntro.
               enough (In_list target l = false) as not_in_l.
               { cbn.
                 rewrite not_in_l.
                 rewrite orb_false_l.
                 done. }
               assert (target < low').
               { apply bool_decide_eq_false_1 in Heqb0.
                 lia. }
               inversion_clear tree_wf0
                 as [| ? ? ? ? ord_low_high intervals_in_interval trees_wf intervals_sorted ].
               apply Forall_cons in trees_wf.
               destruct trees_wf as [leaf_wf _].
               inversion leaf_wf; subst.
               apply (target_below_not_in_list _ low' _); done.

          * destruct interval as [low' high'].
            iDestruct "Hns" as "[Hthd Hns]".
            iDestruct "Hthd" as (ptr' leaves) "(% & -> & Hptr' & Hleaves)".
            wp_load; wp_load; wp_pures.
            destruct (bool_decide (Z.le (Z.of_nat low') (Z.of_nat target))) eqn:?; wp_pures.
            -- destruct (bool_decide (Z.le (Z.of_nat target) (Z.of_nat high'))) eqn:?; wp_pures.
               
               ++ iClear "IH'".
                  assert (tree_spec_wf (node (low', high') l)) as node_wf.
                  { inversion_clear tree_wf0
                      as [| ? ? ? ? ord_low_high intervals_in_interval trees_wf intervals_sorted ].
                    apply Forall_cons in trees_wf.
                    destruct trees_wf.
                    done. }
                  iApply ("IH" $! (token_branch_v #ptr') {| tree := (node (low', high') l); tree_wf := node_wf |} with "[Hptr' Hleaves]").
                  { cbn.
                    iExists ptr', leaves, ns.
                    iSplitR; [done|].
                    iSplitL "Hptr'"; [done|].
                    done. }
                  iNext.
                  iIntros (?) "%".
                  iApply "HPost".
                  iPureIntro.
                  cbn.

                  apply bool_decide_eq_true_1 in Heqb0.
                  apply bool_decide_eq_true_1 in Heqb1.
                  assert (low' <= target) as low'_le_target by lia.
                  assert (target <= high') as target_le_high' by lia.
                  assert (ordeq_A low' target) as ordeq_low'_target.
                  { destruct low'_le_target.
                    - left.
                    - right.
                      lia. }
                  assert (ordeq_A target high') as ordeq_target_high'.
                  { destruct target_le_high'.
                    - left.
                    - right.
                      lia. }

                  rewrite (nary_tree_in_interval_not_in_others target (low, high) (node (low', high') l) trest tree_wf0 (conj ordeq_low'_target ordeq_target_high')).
                  rewrite orb_false_r.
                  done.

               ++ wp_load; wp_pure; wp_pure.
                  assert (tree_spec_wf (node (low, high) trest)) as x_wf.
                  { inversion_clear tree_wf0
                      as [| ? ? ? ? ord_low_high intervals_in_interval trees_wf intervals_sorted ].
                    cbn in intervals.
                    apply Forall_cons in intervals_in_interval.
                    destruct intervals_in_interval.
                    apply Forall_cons in trees_wf.
                    destruct trees_wf.
                    cbn in intervals_sorted.
                    destruct intervals_sorted.
                    apply node_wf; try done. }

                  iApply ("IH'" $! x_wf nrest hd' with "[Hnrest] [Hns]");
                    iClear "IH'";
                    try iFrame.
                  iIntros (?) "%".
                  iApply "HPost".
                  iPureIntro.

                  enough (In_tree target (node (low', high') l) = false) as not_in_l.
                  { cbn; cbn in not_in_l.
                    rewrite not_in_l.
                    rewrite orb_false_l.
                    done. }

                  assert (high' < target).
                  { apply bool_decide_eq_false_1 in Heqb1.
                    lia. }
                  inversion_clear tree_wf0
                      as [| ? ? ? ? ord_low_high intervals_in_interval trees_wf intervals_sorted ].
                  apply Forall_cons in trees_wf.
                  destruct trees_wf as [node_wf _].

                  apply (target_above_not_in_node target); try done.

            -- wp_load; wp_pure; wp_pure.
               assert (tree_spec_wf (node (low, high) trest)) as x_wf.
               { inversion_clear tree_wf0
                      as [| ? ? ? ? ord_low_high intervals_in_interval trees_wf intervals_sorted ].
                    cbn in intervals.
                    apply Forall_cons in intervals_in_interval.
                    destruct intervals_in_interval.
                    apply Forall_cons in trees_wf.
                    destruct trees_wf.
                    cbn in intervals_sorted.
                    destruct intervals_sorted.
                    apply node_wf; try done. }
               iApply ("IH'" $! x_wf nrest hd' with "[Hnrest] [Hns]");
                 iClear "IH'";
                 try iFrame.
               iIntros (?) "%".
               iApply "HPost".
               iPureIntro.

               enough (In_tree target (node (low', high') l) = false) as not_in_l.
               { cbn; cbn in not_in_l.
                 rewrite not_in_l.
                 rewrite orb_false_l.
                 done. }

               assert (target < low').
               { apply bool_decide_eq_false_1 in Heqb0.
                 lia. }
               inversion_clear tree_wf0
                 as [| ? ? ? ? ord_low_high intervals_in_interval trees_wf intervals_sorted ].
               apply Forall_cons in trees_wf.
               destruct trees_wf as [leaf_wf _].
               inversion leaf_wf; subst.
               apply (target_below_not_in_node); done.
    Qed.               

  End bplus_tree_proofs.
End bplus_tree.
