From iris.proofmode Require Export proofmode.

Section nary_tree.
  Context (b : nat).

  Inductive nary_tree : Set :=
  | leaf (interval : Z * Z) (l : list Z) : nary_tree
  | node (interval : Z * Z) (l : list nary_tree) : nary_tree.

  Inductive bplus_tree : Set :=
  | root_leaf (interval : Z * Z) (l : list Z) : bplus_tree
  | root_node (interval : Z * Z) (l : list nary_tree) : bplus_tree.

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

  Fixpoint list_sorted (l : list Z) :=
    match l with
    | [] => True
    | x :: l =>
        match l with
        | [] => True
        | y :: _ => Z.lt x y /\ list_sorted l
        end
    end.

  Definition nary_tree_interval t : (Z * Z) :=
    match t with
    | leaf i _ => i
    | node i _ => i
    end.
  
  Inductive nary_tree_wf : nary_tree -> Prop :=
  | leaf_wf low high vals :
    Z.le low high ->
    hd low vals = low ->
    List.last vals high = high ->
    b / 2 <= length vals <= b ->
    list_sorted vals ->
    nary_tree_wf (leaf (low, high) vals)
  | node_wf low high trees :
    let intervals := map nary_tree_interval trees in
    b / 2 <= length trees <= b ->
    Z.le low high ->
    Forall (fun (interval : Z * Z) =>
              let (low', high') := interval in
              Z.le low low' /\ Z.le high' high)
      intervals ->
    Forall nary_tree_wf trees ->
    (fix intervals_sorted (l : list (Z * Z)) : Prop :=
       match l with
       | [] => True
       | (_, high') :: rest =>
           match rest with
           | [] => True
           | (low', high'') :: rest' =>
               Z.lt high' low'
           end /\ intervals_sorted rest
       end) intervals ->
    nary_tree_wf (node (low, high) trees).

  Inductive nary_tree_wf_no_len : nary_tree -> Prop :=
  | leaf_wf_nl low high vals :
    Z.le low high ->
    hd low vals = low ->
    List.last vals high = high ->
    list_sorted vals ->
    nary_tree_wf_no_len (leaf (low, high) vals)
  | node_wf_nl low high trees :
    let intervals := map nary_tree_interval trees in
    Z.le low high ->
    Forall (fun (interval : Z * Z) =>
              let (low', high') := interval in
              Z.le low low' /\ Z.le high' high)
      intervals ->
    Forall nary_tree_wf_no_len trees ->
    (fix intervals_sorted (l : list (Z * Z)) : Prop :=
       match l with
       | [] => True
       | (_, high') :: rest =>
           match rest with
           | [] => True
           | (low', high'') :: rest' =>
               Z.lt high' low'
           end /\ intervals_sorted rest
       end) intervals ->
    nary_tree_wf_no_len (node (low, high) trees).

  Lemma nary_tree_wf_remove_len t (t_wf : nary_tree_wf t) : (nary_tree_wf_no_len t).
  Proof.
    induction t using nary_tree_ind'; inversion t_wf; subst; constructor; try done.
    clear H2 H3 H4 H6 intervals t_wf.
    induction trees; [done|].
    apply Forall_cons in H, H5; destruct H, H5.
    constructor; auto.
  Qed.

  Inductive bplus_tree_wf : bplus_tree -> Prop :=
  | root_leaf_wf low high vals :
    Z.le low high ->
    hd low vals = low ->
    List.last vals high = high ->
    0 <= length vals <= b - 1 ->
    list_sorted vals ->
    bplus_tree_wf (root_leaf (low, high) vals)
  | root_node_wf low high trees :
    let intervals := map nary_tree_interval trees in
    2 <= length trees <= b ->
    Z.le low high ->
    Forall (fun (interval : Z * Z) =>
              let (low', high') := interval in
              Z.le low low' /\ Z.le high' high)
      intervals ->
    Forall nary_tree_wf trees ->
    (fix intervals_sorted (l : list (Z * Z)) : Prop :=
       match l with
       | [] => True
       | (_, high') :: rest =>
           match rest with
           | [] => True
           | (low', high'') :: rest' =>
               Z.lt high' low'
           end /\ intervals_sorted rest
       end) intervals ->
    bplus_tree_wf (root_node (low, high) trees).

  Lemma destruct_list_back {A} : forall (l : list A), {x:A & {init:list A | l = init ++ [x] }}+{l = [] }.
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

  Fixpoint size (t : nary_tree) : nat :=
    match t with
    | leaf _ l => List.length l
    | node _ l => list_sum (map size l)
    end.

  Fixpoint In_list (v : Z) (l : list Z) :=
    match l with
    | [] => false
    | x :: xs => orb (Z.eqb x v) (In_list v xs)
    end.

  Lemma target_above_not_in_list target high vals:
    Z.lt high target ->
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
      enough (high ≠ target) by (apply Z.eqb_neq; done).
      lia.
    - assert (list_sorted (init ++ [high])).
      { cbn in sorted_vals.
        assert (exists y l, init ++ [high] = y :: l).
        { destruct init.
          - exists high, []; done.
          - exists z, (init ++ [high]); done. }
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
        { apply Z.eqb_neq; done. }
        lia.
      + apply IHinit.
        cbn in sorted_vals.
        destruct sorted_vals as [? sorted_vals].
        cbn.
        assert (exists y l, init ++ [high] = y :: l).
        { destruct init.
          - exists high, []; done.
          - exists z, (init ++ [high]); done. }
        destruct H0 as (? & ? & ?).
        rewrite H0 in sorted_vals; rewrite H0.
        destruct sorted_vals.
        split; [lia|done].
  Qed.

  Lemma target_below_not_in_list target low vals:
    Z.lt target low ->
    hd low vals = low ->
    list_sorted vals ->
    In_list target vals = false.
  Proof.
    intros target_let_low hd_vals_low sorted_vals.
    destruct vals; [done|].
    cbn in *; subst.
    assert (Z.eqb low target = false).
    { enough (low ≠ target).
      { apply Z.eqb_neq; done. }
      lia. }
    rewrite H.
    rewrite orb_false_l.
    induction vals; [done|].
    cbn.
    destruct sorted_vals as [? sorted_vals].
    assert (Z.eqb a target = false).
    { enough (a ≠ target).
      { apply Z.eqb_neq; done. }
      lia. }
    rewrite H1.
    rewrite orb_false_l.
    apply IHvals.
    cbn in sorted_vals.
    destruct vals; [done|].
    destruct sorted_vals.
    split; [lia|done].
  Qed.

  Fixpoint In_nary_tree (v : Z) (t : nary_tree) {struct t} : bool :=
    match t with
    | leaf _ l => In_list v l
    | node _ l =>
        (fix In_aux (l : list nary_tree) :=
           match l with
           | [] => false
           | t :: ts => orb (In_nary_tree v t) (In_aux ts)
           end) l
    end.

  Definition In_bplus_tree (v : Z) (t : bplus_tree) : bool :=
    match t with
    | root_leaf _ l => In_list v l
    | root_node _ l =>
        (fix In_aux (l : list nary_tree) :=
           match l with
           | [] => false
           | t :: ts => orb (In_nary_tree v t) (In_aux ts)
           end) l
    end.

  Lemma target_above_below_not_in_node target t:
    nary_tree_wf_no_len t ->
    (Z.lt target (fst (nary_tree_interval t)) \/ Z.lt (snd (nary_tree_interval t)) target) ->
    In_nary_tree target t = false.
  Proof.
    intros t_wf ord_target_low_high.

    induction t as [? | interval trees IH] using nary_tree_ind';
      destruct interval as [low high];
      cbn in ord_target_low_high.
    - inversion t_wf.
      destruct ord_target_low_high as [ord_target_low | ord_high_target];
        [ apply (target_below_not_in_list _ low) | apply (target_above_not_in_list _ high)];
        done.
    - cbn.
      induction trees as [|t trees]; [done|].
      replace (In_nary_tree target t) with false.
      2:{ apply Forall_cons in IH.
          inversion_clear t_wf as [|? ? ? ? _ intervals_in_interval trees_wf _].
          apply Forall_cons in trees_wf.
          destruct trees_wf.
          symmetry.
          apply (proj1 IH); [done|].
          apply Forall_cons in intervals_in_interval.
          destruct t;
            destruct interval as [low' high'];
            cbn in intervals_in_interval;
            destruct intervals_in_interval;
            cbn;
            lia. }

      rewrite orb_false_l.
      apply IHtrees.
      + apply Forall_cons in IH.
        destruct IH.
        done.
      + inversion_clear t_wf as [|? ? ? ? ? intervals_in_interval trees_wf intervals_sorted].
        apply Forall_cons in trees_wf.
        destruct trees_wf.
        apply Forall_cons in intervals_in_interval.
        destruct intervals_in_interval.
        destruct t;
          destruct interval;
          destruct intervals_sorted;
          constructor;
          done.
  Qed.

  Lemma nary_tree_in_interval_not_in_others target branch branches :
    let intervals := map nary_tree_interval (branch :: branches) in
    Forall nary_tree_wf_no_len (branch :: branches) ->
    (fix intervals_sorted (l : list (Z * Z)) : Prop :=
       match l with
       | [] => True
       | (_, high') :: rest =>
           match rest with
           | [] => True
           | (low', _) :: _ => Z.lt high' low'
           end ∧ intervals_sorted rest
       end) intervals ->
    Z.le (fst (nary_tree_interval branch)) target /\ Z.le target (snd (nary_tree_interval branch)) ->
    (fix In_aux (l : list nary_tree) :=
           match l with
           | [] => false
           | t :: ts => orb (In_nary_tree target t) (In_aux ts)
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
                 | t :: ts => In_nary_tree target t || In_aux ts
                 end) branches = false).
      { apply IHbranches; clear IHbranches.
        - done.
        - cbn.
          cbn in intervals, intervals_sorted.
          destruct intervals_sorted as (? & ? & ?).
          split; [|done].
          destruct branches; [done|].
          destruct n;
            destruct interval;
            cbn in H2, H3; cbn;
            lia. }
      rewrite H1.
      clear H1 IHbranches.
      rewrite orb_false_r.

      cbn in intervals, intervals_sorted.
      destruct intervals_sorted as (ord_high_low' & _).
      cbn; cbn in H0.

      assert (Z.lt target low') as ord_target_low'
          by lia.

      apply (target_below_not_in_list _ low'); done.

    - destruct interval as (low & high), interval0 as (low' & high').
      inversion wf_branch'; subst.

      assert ((fix In_aux (l : list nary_tree) : bool :=
                 match l with
                 | [] => false
                 | t :: ts => In_nary_tree target t || In_aux ts
                 end) branches = false).
      { apply IHbranches; clear IHbranches.
        - done.
        - cbn.
          cbn in intervals, intervals_sorted.
          destruct intervals_sorted as (? & ? & ?).
          split; [|done].
          destruct branches; [done|].
          destruct n;
            destruct interval;
            cbn in H2, H3; cbn;
            lia. }
      rewrite H1.
      clear H1 IHbranches.
      rewrite orb_false_r.

      cbn in intervals, intervals_sorted.
      destruct intervals_sorted as (ord_high_low' & _).
      cbn in H0.
      assert (Z.lt target low') as ord_target_low'
          by lia.

      apply (target_above_below_not_in_node); [|left]; done.

    - destruct interval as (low & high), interval0 as (low' & high').
      inversion_clear wf_branch' as [? ? ? ordeq_low'_high' hd_vals_low' last_vals_high' sorted_vals |].

      assert ((fix In_aux (l : list nary_tree) : bool :=
                 match l with
                 | [] => false
                 | t :: ts => In_nary_tree target t || In_aux ts
                 end) branches = false)
        as not_in_branches.
      { apply IHbranches; clear IHbranches.
        - done.
        - cbn.
          cbn in intervals, intervals_sorted.
          destruct intervals_sorted as (? & ? & ?).
          split; [|done].
          destruct branches; [done|].
          destruct n;
            destruct interval;
            cbn in H2, H3; cbn;
            lia. }
      rewrite not_in_branches.
      rewrite orb_false_r.

      cbn in intervals, intervals_sorted.
      destruct intervals_sorted as (ord_high_low' & _).
      cbn; cbn in H0.

      assert (Z.lt target low') as ord_target_low'
          by lia.

      apply (target_below_not_in_list _ low'); done.
    - destruct interval as (low & high), interval0 as (low' & high').
      inversion wf_branch'; subst.

      assert ((fix In_aux (l : list nary_tree) : bool :=
                 match l with
                 | [] => false
                 | t :: ts => In_nary_tree target t || In_aux ts
                 end) branches = false).
      { apply IHbranches; clear IHbranches.
        - done.
        - cbn.
          cbn in intervals, intervals_sorted.
          destruct intervals_sorted as (? & ? & ?).
          split; [|done].
          destruct branches; [done|].
          destruct n;
            destruct interval;
            cbn in H2, H3; cbn;
            lia. }
      rewrite H1.
      clear H1 IHbranches.
      rewrite orb_false_r.

      cbn in intervals, intervals_sorted.
      destruct intervals_sorted as (ord_high_low' & _).
      cbn in H0.
      assert (Z.lt target low') as ord_target_low'
          by lia.

      apply (target_above_below_not_in_node); [|left]; done.
  Qed.

End nary_tree.
