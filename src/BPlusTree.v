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
  
  Inductive nary_tree_wf : nary_tree -> Prop :=
    | leaf_wf low high vals :
        ordeq_A low high ->
          hd low vals = low ->
          List.last vals high = high ->
          (** hidden so we don't need to deal with root node shenanigans *)
          (* b / 2 <= length vals <= b -> *)
          list_sorted vals ->
          nary_tree_wf (leaf (low, high) vals)
    | node_wf low high trees :
        let intervals :=
          map (fun t =>
                 match t with
                 | leaf (low', high') _
                 | node (low', high') _ => (low', high')
                 end)
            trees
        in
        b / 2 <= length trees <= b ->
        ordeq_A low high ->
        Forall (fun (interval : A * A) =>
                  let (low', high') := interval in
                  ord_A low low' /\ ord_A high' high)
          intervals ->
        Forall nary_tree_wf trees ->
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
        nary_tree_wf (node (low, high) trees).

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

  Lemma leaf_wf_remove_length t :
    nary_tree_wf t ->
    forall low high vals,
      t = leaf (low, high) vals ->
      ordeq_A low high /\
        hd low vals = low /\
        List.last vals high = high /\
        list_sorted vals.
  Proof.
    destruct t as [[low' high'] vals'|].
    - intros t_wf ? ? ? Heqleaf.
      inversion Heqleaf; subst.
      inversion t_wf; done.
    - discriminate.
  Qed.

  Lemma node_wf_remove_length t :
    nary_tree_wf t ->
    forall low high trees,
      t = node (low, high) trees ->
        let intervals :=
          map (fun t =>
                 match t with
                 | leaf (low', high') _
                 | node (low', high') _ => (low', high')
                 end)
            trees
        in
        ordeq_A low high /\
        Forall (fun (interval : A * A) =>
                  let (low', high') := interval in
                  ord_A low low' /\ ord_A high' high)
          intervals /\
        Forall nary_tree_wf trees /\
        (fix intervals_sorted (l : list (A * A)) : Prop :=
           match l with
           | [] => True
           | (_, high') :: rest =>
               match rest with
               | [] => True
               | (low', high'') :: rest' =>
                   ord_A high' low'
               end /\ intervals_sorted rest
           end) intervals.
  Proof.
    destruct t as [|[low' high'] trees'].
    - discriminate.
    - intros t_wf ? ? ? Heqnode.
      inversion Heqnode; subst.
      inversion t_wf; done.
  Qed.

  Lemma target_above_below_not_in_node target t:
    nary_tree_wf t ->
    (ord_A target (fst (nary_tree_interval t)) \/ ord_A (snd (nary_tree_interval t)) target) ->
    In_tree target t = false.
  Proof.
    intros t_wf ord_target_low_high.
    unfold ord_A in ord_target_low_high.
    specialize (leaf_wf_remove_length _ t_wf) as leaf_wf.
    specialize (node_wf_remove_length _ t_wf) as node_wf.
    clear t_wf.

    induction t as [? | interval trees IH] using nary_tree_ind';
      destruct interval as [low high];
      cbn in ord_target_low_high.
    - destruct (leaf_wf _ _ _ eq_refl) as (? & ? & ? & ?).
      destruct ord_target_low_high as [ord_target_low | ord_high_target];
        [ apply (target_below_not_in_list _ low) | apply (target_above_not_in_list _ high)];
        done.
    - cbn.
      induction trees as [|t trees]; [done|].
      replace (In_tree target t) with false.
      2:{ apply Forall_cons in IH.
          destruct (node_wf _ _ _ eq_refl) as (? & intervals_in_interval & trees_wf & ?).
          apply Forall_cons in trees_wf.
          destruct trees_wf.
          symmetry.
          apply (proj1 IH); [|apply leaf_wf_remove_length|apply node_wf_remove_length]; try done.
          apply Forall_cons in intervals_in_interval.
          destruct intervals_in_interval.
          destruct t;
            destruct interval as [low' high'];
            cbn;
            unfold ord_A, ordeq_A in *;
            lia. }

      rewrite orb_false_l.
      apply IHtrees.
      + apply Forall_cons in IH.
        destruct IH.
        done.
      + discriminate.
      + intros ? ? ? Heqnode.
        inversion Heqnode; subst.
        destruct (node_wf _ _ _ eq_refl) as (? & intervals_in_interval & trees_wf & intervals_sorted).
        apply Forall_cons in trees_wf.
        destruct trees_wf.
        apply Forall_cons in intervals_in_interval.
        destruct intervals_in_interval.
        destruct t;
          destruct interval;
          destruct intervals_sorted;
          done.
  Qed.

  Lemma nary_tree_in_interval_not_in_others target branch branches :
    let intervals :=
      map (fun t =>
             match t with
             | leaf (low', high') _
             | node (low', high') _ => (low', high')
             end)
        (branch :: branches)
    in
    Forall nary_tree_wf (branch :: branches) ->
    (fix intervals_sorted (l : list (A * A)) : Prop :=
       match l with
       | [] => True
       | (_, high') :: rest =>
           match rest with
           | [] => True
           | (low', _) :: _ => ord_A high' low'
           end ∧ intervals_sorted rest
       end) intervals ->
    ordeq_A (fst (nary_tree_interval branch)) target /\ ordeq_A target (snd (nary_tree_interval branch)) ->
    (fix In_aux (l : list nary_tree) :=
           match l with
           | [] => false
           | t :: ts => orb (In_tree target t) (In_aux ts)
           end) branches = false.
  Proof.
    intros intervals wf_branches intervals_sorted (? & ?).
    apply Forall_cons in wf_branches;
      destruct wf_branches as [wf_branch wf_branches].
    induction branches as [|branch' branches]; [done|].
    apply Forall_cons in wf_branches;
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
          cbn in intervals, intervals_sorted.
          destruct intervals_sorted as (? & ? & ?).
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

      cbn in intervals, intervals_sorted.
      destruct intervals_sorted as (ord_high_low' & _).
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
          cbn in intervals, intervals_sorted.
          destruct intervals_sorted as (? & ? & ?).
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

      cbn in intervals, intervals_sorted.
      destruct intervals_sorted as (ord_high_low' & _).
      cbn in H0.
      assert (ord_A target low') as ord_target_low'
          by (unfold ord_A, ordeq_A in *; lia).

      apply (target_above_below_not_in_node); [|left]; done.

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
          cbn in intervals, intervals_sorted.
          destruct intervals_sorted as (? & ? & ?).
          split; [|done].
          destruct branches; [done|].
          cbn in H2; cbn.
          destruct n;
            destruct interval;
            unfold ord_A, ordeq_A in *;
            lia. }
      rewrite not_in_branches.
      rewrite orb_false_r.

      cbn in intervals, intervals_sorted.
      destruct intervals_sorted as (ord_high_low' & _).
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
          cbn in intervals, intervals_sorted.
          destruct intervals_sorted as (? & ? & ?).
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

      cbn in intervals, intervals_sorted.
      destruct intervals_sorted as (ord_high_low' & _).
      cbn in H0.
      assert (ord_A target low') as ord_target_low'
          by (unfold ord_A, ordeq_A in *; lia).

      apply (target_above_below_not_in_node); [|left]; done.
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

  Definition tree_spec := nary_tree.
  Definition tree_spec_wf := nary_tree_wf b.

  Section bplus_tree_model.
    Context `{!heapGS Σ}.
    Notation iProp := (iProp Σ).

    Fixpoint is_list (hd : val) (xs : list val) : iProp :=
      match xs with
      | [] => ⌜hd = NONEV⌝
      | x :: xs => ∃ (l : loc) hd', ⌜hd = SOMEV #l⌝ ∗ l ↦ (x, hd') ∗ is_list hd' xs
    end%I.

    Definition leaf_node v (t : tree_spec) (interval : tval * tval) (vals : list tval) :=
      let (low, high) := interval in
      (∃ (ptr : loc) (lhd : val), ⌜ size t < b ⌝ ∗ ⌜ v = token_leaf_v #ptr ⌝ ∗ ptr ↦ ((#low, #high), lhd) ∗ is_list lhd (map (fun (x : tval) => #x) vals))%I.

    Definition branch_node v (t : tree_spec) (interval : tval * tval) ts (is_node : forall (_ : val) (t : tree_spec), iProp) :=
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

    Fixpoint is_node (v : val) (t : tree_spec) {struct t} : iProp :=
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

    Definition is_bplus_tree (v : val) (t : tree_spec) (t_wf : tree_spec_wf t) : iProp :=
      match t with
      | leaf interval l => leaf_node v t interval l
      | node interval ts => branch_node v t interval ts is_node
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
      {{{ True }}} new_bplus_tree #() {{{ v, RET v; is_bplus_tree v empty_tree empty_tree_wf }}}.
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
      is_bplus_tree v (leaf (low, high) l) wf ⊢ ∃ x, ⌜ v = token_leaf_v x ⌝.
    Proof.
      iIntros "Hv".
      iDestruct "Hv" as (? ?) "[% [% Hv]]".
      iExists #ptr.
      done.
    Qed.

    Lemma tree_node_token_branch v low high l (wf : tree_spec_wf (node (low, high) l)):
      is_bplus_tree v (node (low, high) l) wf ⊢ ∃ x, ⌜ v = token_branch_v x ⌝.
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

    Theorem search_bplus_tree_spec (t : tree_spec) (t_wf : tree_spec_wf t) (v : val) (target : nat) :
      {{{ is_bplus_tree v t t_wf }}} search_bplus_tree (v, #target)%V {{{ r, RET r; ⌜ r = #(In_tree target t) ⌝ ∗ is_bplus_tree v t t_wf }}}.
    Proof using bpos.
      iIntros (Φ) "Hv HPost".

      iInduction t as [(low & high)|(low & high) ts] "IH" using nary_tree_ind' forall (v).
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
        iDestruct "Hv" as (ptr lhd ns) "(% & Hptr & Hlhd & Hns)".
        assert (x = #ptr) by (unfold token_branch_v in H; congruence); subst.
        wp_rec; wp_load; wp_proj; wp_let; wp_pure; wp_pure.
        iEval (cbn) in "HPost".

        iAssert (
            (is_list lhd ns ∗
               (fix branch_node_list (ns0 : list val) (ts0 : list tree_spec) {struct ts0} : iProp :=
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
                          | t0 :: ts0 => In_tree target t0 || In_aux ts0
                          end) ts)⌝ ∗ is_list lhd ns ∗
                       (fix branch_node_list (ns0 : list val) (ts0 : list tree_spec) {struct ts0} : iProp :=
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
            as [| ? ? ? ? _ _ _ trees_wf intervals_sorted ];
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
              iDestruct "Hthd" as (ptr' leaves) "(% & -> & Hptr' & Hleaves)".
              wp_load; wp_load; wp_pures.
              destruct (bool_decide (Z.le (Z.of_nat low') (Z.of_nat target))) eqn:?; wp_pures.
              -- destruct (bool_decide (Z.le (Z.of_nat target) (Z.of_nat high'))) eqn:?; wp_pures.
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

                      assert ((fix In_aux (l1 : list nary_tree) : bool :=
                                 match l1 with
                                 | [] => false
                                 | t0 :: ts => In_tree target t0 || In_aux ts
                                 end) trest = false) as not_in_others.
                      { apply (nary_tree_in_interval_not_in_others b _ (leaf (low', high') l)).
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
                      assert (high' < target).
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
                   assert (target < low').
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
              destruct (bool_decide (Z.le (Z.of_nat low') (Z.of_nat target))) eqn:?; wp_pures.
              -- destruct (bool_decide (Z.le (Z.of_nat target) (Z.of_nat high'))) eqn:?; wp_pures.
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

                      assert ((fix In_aux (l1 : list nary_tree) : bool :=
                                 match l1 with
                                 | [] => false
                                 | t0 :: ts => In_tree target t0 || In_aux ts
                                 end) trest = false) as not_in_others.
                      { apply (nary_tree_in_interval_not_in_others b _ (node (low', high') l)).
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
                      enough (In_tree target (node (low', high') l) = false) as not_in_l.
                      { cbn; cbn in not_in_l.
                        rewrite not_in_l.
                        rewrite orb_false_l.
                        done. }
                      assert (high' < target).
                      { apply bool_decide_eq_false_1 in Heqb1.
                        lia. }
                      inversion t_wf; subst.
                      apply (target_above_below_not_in_node b); [|right]; done. }
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
                   enough (In_tree target (node (low', high') l) = false) as not_in_l.
                   { cbn; cbn in not_in_l.
                     rewrite not_in_l.
                     rewrite orb_false_l.
                     done. }
                   assert (target < low').
                   { apply bool_decide_eq_false_1 in Heqb0.
                     lia. }
                   inversion t_wf; subst.
                   apply (target_above_below_not_in_node b); [|left]; done. }
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

  End bplus_tree_proofs.
End bplus_tree.
