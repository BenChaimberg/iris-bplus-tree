From iris.algebra Require Import numbers.
From iris.heap_lang Require Export proofmode notation.
From iris.proofmode Require Export proofmode.
From iris.prelude Require Import options.
Require Import NaryTree.
Require Import BPlusTree.

Section nary_tree.
  Context (b : nat).
  Context (beven : Zeven b).
  Context (bpos : 0 < b).

  Fixpoint insert_list_spec (target : Z) (l : list Z) : list Z :=
    match l with
    | [] => [target]
    | x :: xs => if Z.eqb x target
               then x :: xs
               else if Z.ltb x target
                    then x :: insert_list_spec target xs
                    else target :: x :: xs
    end.

    Fixpoint insert_nary_tree_spec (target : Z) (t : nary_tree) : nary_tree * option nary_tree :=
      match t with
      | leaf (low, high) vals =>
          let new_vals := insert_list_spec target vals in
          if Z.ltb b (length new_vals)
          then
            let left_vals := firstn (b/2) new_vals in
            let right_vals := skipn (b/2) new_vals in
            let left_interval := (hd low left_vals, List.last left_vals high) in
            let right_interval := (hd low right_vals, List.last right_vals high) in
            (leaf left_interval left_vals, Some (leaf right_interval right_vals))
          else
            (leaf (hd low new_vals, List.last new_vals high) new_vals, None)
      | node (low, high) branches =>
          let new_branches :=
            ((fix insert_aux (l : list nary_tree) :=
                match l with
                | [] => []
                | t :: [] =>
                    let (new_t1, new_t2) := insert_nary_tree_spec target t in
                    match new_t2 with
                    | None => [new_t1]
                    | Some new_t2' => new_t1 :: [new_t2']
                    end
                | t :: ts =>
                    let (low, high) := nary_tree_interval t in
                    if Z.leb target high
                    then let (new_t1, new_t2) := insert_nary_tree_spec target t in
                         match new_t2 with
                         | None => new_t1 :: ts
                         | Some new_t2' => new_t1 :: new_t2' :: ts
                         end
                    else t :: insert_aux ts
                end) branches) in
          if Z.ltb b (length new_branches)
          then
            let left_branches := firstn (b/2) new_branches in
            let right_branches := skipn (b/2) new_branches in
            let left_interval_low :=
              match head (map fst (map nary_tree_interval left_branches)) with
              | None => low
              | Some x => x
              end
            in
            let left_interval_high :=
              match last (map snd (map nary_tree_interval left_branches)) with
              | None => high
              | Some x => x
              end
            in
            let right_interval_low :=
              match head (map fst (map nary_tree_interval right_branches)) with
              | None => low
              | Some x => x
              end
            in
            let right_interval_high :=
              match last (map snd (map nary_tree_interval right_branches)) with
              | None => high
              | Some x => x
              end
            in
            (node (left_interval_low, left_interval_high) left_branches,
              Some (node (right_interval_low, right_interval_high) right_branches))
          else
            let new_low :=
              match head (map fst (map nary_tree_interval new_branches)) with
              | None => low
              | Some x => x
              end
            in
            let new_high :=
              match last (map snd (map nary_tree_interval new_branches)) with
              | None => high
              | Some x => x
              end
            in
            (node (new_low, new_high) new_branches, None)
      end.

    Definition insert_bplus_tree_spec (target : Z) (t : bplus_tree) :=
      match t with
      | root_leaf (low, high) vals =>
          let new_vals := insert_list_spec target vals in
          if Z.leb b (length new_vals)
          then
            let left_vals := firstn (b/2) new_vals in
            let right_vals := skipn (b/2) new_vals in
            let left_interval := (hd low left_vals, List.last left_vals high) in
            let right_interval := (hd low right_vals, List.last right_vals high) in
            root_node (hd low left_vals, List.last right_vals high)
              (leaf left_interval left_vals :: leaf right_interval right_vals :: [])
          else
            root_leaf (hd low new_vals, List.last new_vals high) new_vals
      | root_node (low, high) branches =>
          let new_branches :=
            ((fix insert_aux (l : list nary_tree) :=
                match l with
                | [] => []
                | t :: [] =>
                    let (new_t1, new_t2) := insert_nary_tree_spec target t in
                    match new_t2 with
                    | None => [new_t1]
                    | Some new_t2' => new_t1 :: [new_t2']
                    end
                | t :: ts =>
                    let (low, high) := nary_tree_interval t in
                    if Z.leb target high
                    then let (new_t1, new_t2) := insert_nary_tree_spec target t in
                         match new_t2 with
                         | None => new_t1 :: ts
                         | Some new_t2' => new_t1 :: new_t2' :: ts
                         end
                    else t :: insert_aux ts
                end) branches) in
          if Z.ltb b (length new_branches)
          then
            let left_branches := firstn (b/2) new_branches in
            let right_branches := skipn (b/2) new_branches in
            let left_interval_low :=
              match head (map fst (map nary_tree_interval left_branches)) with
              | None => low
              | Some x => x
              end
            in
            let left_interval_high :=
              match last (map snd (map nary_tree_interval left_branches)) with
              | None => high
              | Some x => x
              end
            in
            let right_interval_low :=
              match head (map fst (map nary_tree_interval right_branches)) with
              | None => low
              | Some x => x
              end
            in
            let right_interval_high :=
              match last (map snd (map nary_tree_interval right_branches)) with
              | None => high
              | Some x => x
              end
            in
            root_node (left_interval_low, right_interval_high)
              (node (left_interval_low, left_interval_high) left_branches :: node (right_interval_low, right_interval_high) right_branches :: [])
          else
            let new_low :=
              match head (map fst (map nary_tree_interval new_branches)) with
              | None => low
              | Some x => x
              end
            in
            let new_high :=
              match last (map snd (map nary_tree_interval new_branches)) with
              | None => high
              | Some x => x
              end
            in
            root_node (new_low, new_high) new_branches
      end.
    Lemma take_b2_cons' {A} (l : list A) : b <= length l -> (exists x l', take (b/2) l = x :: l').
    Proof using beven bpos.
      intro.
      assert (1 < 2) by lia.
      specialize (Nat.div_lt b 2 bpos H0) as b2ltb.
      specialize (take_length l (b/2)) as take_len.
      specialize (b2ge1 _ beven bpos) as ?.
      assert (0 < b/2) by lia.
      destruct (take (b/2) l);
        [ rewrite nil_length in take_len; lia | eauto ].
    Qed.

    Lemma take_b2_cons {A} (l : list A) : b < length l -> (exists x l', take (b/2) l = x :: l').
    Proof using beven bpos. intros; assert (b <= length l) by lia; apply take_b2_cons'; done. Qed.

    Lemma take_b2_snoc' {A} (l : list A) : b <= length l -> (exists x l', take (b/2) l = l' ++ [x]).
    Proof using beven bpos.
      intro.
      assert (1 < 2) by lia.
      specialize (Nat.div_lt b 2 bpos H0) as b2ltb.
      specialize (take_length l (b/2)) as take_len.
      specialize (b2ge1 _ beven bpos) as ?.
      assert (0 < b/2) by lia.
      destruct (destruct_list_back (take (b/2) l)) as [[x [init ?]]|];
        subst; rewrite e in take_len; rewrite e;
        [ eauto | rewrite nil_length in take_len; lia ].
    Qed.

    Lemma take_b2_snoc {A} (l : list A) : b < length l -> (exists x l', take (b/2) l = l' ++ [x]).
    Proof using beven bpos. intros; assert (b <= length l) by lia; apply take_b2_snoc'; done. Qed.

    Lemma drop_b2_cons' {A} (l : list A) : b <= length l -> (exists x l', drop (b/2) l = x :: l').
    Proof using bpos.
      intro.
      assert (1 < 2) by lia.
      specialize (Nat.div_lt b 2 bpos H0) as b2ltb.
      specialize (drop_length l (b/2)) as drop_len.
      destruct (drop (b/2) l);
        [ rewrite nil_length in drop_len; lia | eauto ].
    Qed.

    Lemma drop_b2_cons {A} (l : list A) : b < length l -> (exists x l', drop (b/2) l = x :: l').
    Proof using beven bpos. intros; assert (b <= length l) by lia; apply drop_b2_cons'; done. Qed.

    Lemma drop_b2_snoc' {A} (l : list A) : b <= length l -> (exists x l', drop (b/2) l = l' ++ [x]).
    Proof using bpos.
      intro.
      assert (1 < 2) by lia.
      specialize (Nat.div_lt b 2 bpos H0) as b2ltb.
      specialize (drop_length l (b/2)) as drop_len.
      destruct (destruct_list_back (drop (b/2) l)) as [[x [init ?]]|];
        subst; rewrite e in drop_len; rewrite e;
        [ eauto | rewrite nil_length in drop_len; lia ].
    Qed.

    Lemma drop_b2_snoc {A} (l : list A) : b < length l -> (exists x l', drop (b/2) l = l' ++ [x]).
    Proof using bpos. intros; assert (b <= length l) by lia; apply drop_b2_snoc'; done. Qed.

    Lemma list_sorted_cons x l : list_sorted (x :: l) -> list_sorted l.
    Proof. destruct l; [|intros []]; done. Qed.

    Lemma insert_list_sorted l target : list_sorted l -> list_sorted (insert_list_spec target l).
    Proof.
      clear bpos.
      induction l as [|x l]; [done|].
      cbn.
      intros H.
      destruct l as [|y l].
      - destruct (Z.eqb x target) eqn:?; [done|].
        destruct (Z.ltb x target) eqn:?.
        + apply Z.ltb_lt in Heqb1; done.
        + cbn; lia.
      - destruct (Z.eqb x target) eqn:?; [done|].
        destruct (Z.ltb x target) eqn:?.
        + destruct (insert_list_spec target (y :: l)) eqn:?; [done|].
          destruct H.
          cbn.
          split.
          * assert (z = y \/ z = target).
            { cbn in Heql0; destruct (Z.eqb y target) eqn:?; destruct (Z.ltb y target) eqn:?; inversion Heql0; auto. }
            destruct H1; subst; auto.
            apply Z.ltb_lt in Heqb1; done.
          * apply (IHl H0).
        + cbn.
          destruct H.
          specialize (IHl H0).
          split; [lia|].
          split; [lia|].
          done.
    Qed.

    Lemma split_list_sorted l n : list_sorted l -> forall x y, In x (take n l) -> In y (drop n l) -> (x < y)%Z.
    Proof.
      clear bpos.
      revert l.
      induction n; [intros; rewrite take_0 in H0; cbn in H0; done|].
      intros l sorted_l x y in_x in_y.
      destruct l; [rewrite take_nil in in_x; done|].
      cbn in in_x; fold (@take Z) in in_x;
        cbn in in_y; fold (@drop Z) in in_y.
      destruct in_x.
      - subst.
        clear IHn.
        revert dependent n;
          induction l;
          intros;
          [rewrite drop_nil in in_y; done|].
        assert (list_sorted (x :: l)).
        { cbn; cbn in sorted_l.
          destruct l; [done|].
          destruct sorted_l as [? []].
          split; [lia|done]. }
        destruct n.
        + destruct in_y; [subst; destruct sorted_l; lia|].
          apply (IHl H 0); rewrite drop_0; done.
        + cbn in in_y; fold (@drop Z) in in_y.
          apply (IHl H n in_y).
      - apply (IHn l); auto.
        cbn in sorted_l; destruct l; destruct sorted_l; cbn; done.
    Qed.

    Lemma last_cons_cons {A} : ∀ (x1 x2 : A) (l0 : list A), List.last (x1 :: x2 :: l0) = List.last (x2 :: l0).
    Proof. clear beven bpos; done. Qed.

    Lemma list_sorted_hd_lt_last l d1 d2 : list_sorted l -> (d1 <= d2)%Z -> (hd d1 l <= List.last l d2)%Z.
    Proof.
      clear beven bpos.
      intro sorted_l.
      specialize (split_list_sorted l 1 sorted_l (hd d1 l) (List.last l d2)) as ?.
      destruct l as [|x l]; [cbn; done|].
      destruct l as [|y l]; [cbn; done|].
      specialize (H (or_introl eq_refl)).
      assert (In (List.last (x :: y :: l) d2) (drop 1 (x :: y :: l))).
      { clear H sorted_l.
        rewrite last_cons_cons skipn_cons drop_0.
        destruct (destruct_list_back l) as [[z [init ?]]|]; rewrite e; [|cbn; auto].
        rewrite app_comm_cons last_last.
        apply in_or_app.
        right; cbn; auto. }
      specialize (H H0); lia.
    Qed.

    Lemma list_sorted_take_sorted l n : list_sorted l -> list_sorted (take n l).
    Proof.
      revert l.
      induction n; [done|].
      destruct l as [|x l]; [done|].
      intro sorted_xl.
      rewrite firstn_cons.
      destruct l as [|y l]; [rewrite take_nil; done|].
      destruct n; [done|].
      rewrite firstn_cons.
      specialize (IHn (y :: l) (list_sorted_cons _ _ sorted_xl)).
      rewrite firstn_cons in IHn.
      destruct sorted_xl.
      split; done.
    Qed.

    Lemma list_sorted_drop_sorted l n : list_sorted l -> list_sorted (drop n l).
    Proof.
      revert l.
      induction n; intros; [rewrite drop_0; done|].
      destruct l as [|x l]; [done|].
      rewrite skipn_cons.
      apply IHn.
      apply (list_sorted_cons _ _ H).
    Qed.

    Lemma root_leaf_wf_split_length interval l target : tree_spec_wf b (root_leaf interval l) -> b <= length (insert_list_spec target l) -> b = length (insert_list_spec target l).
    Proof using bpos.
      intros t_wf inserted_length.
      inversion_clear t_wf as [? ? ? _ _ _ ? _|]; subst.
      clear beven; revert dependent b.
      induction l as [|x l]; intros; cbn in inserted_length.
      - cbn; lia.
      - cbn.
        destruct (Z.eqb x target); [lia|].
        destruct (Z.ltb x target);
          cbn in inserted_length; cbn in H; cbn;
          [|lia].
        specialize (IHl (pred b0));
          rewrite <- IHl;
          lia.
    Qed.

    Lemma hd_map_comm {A B} (f : A -> B) (l : list A) (d : A) (fd : B) :
      fd = f d -> hd (fd) (map f l) = f (hd d l).
    Proof. destruct l; [done|auto]. Qed.

    Lemma head_map_comm {A B} (f : A -> B) (l : list A) :
      head (map f l) = match head l with None => None | Some x => Some (f x) end.
    Proof. destruct l; [done|auto]. Qed.

    Lemma Listlast_map_comm {A B} (f : A -> B) (l : list A) (d : A) (fd : B) :
      fd = f d -> List.last (map f l) fd = f (List.last l d).
    Proof.
      induction l; [done|].
      destruct l; [auto|done].
    Qed.

    Lemma last_map_comm {A B} (f : A -> B) (l : list A) :
      last (map f l) = match last l with None => None | Some x => Some (f x) end.
    Proof.
      induction l; [done|].
      destruct l; [auto|done].
    Qed.

    Lemma insert_list_hd (target : Z) (l : list Z) d :
      let new_l := insert_list_spec target l in
      hd d new_l = hd d l \/ hd d new_l = target.
    Proof.
      destruct l; cbn; [auto|].
      destruct (z =? target)%Z; [cbn; auto|].
      destruct (z <? target)%Z; cbn; auto.
    Qed.

    Lemma inserted_list_cons target l : exists x rest, insert_list_spec target l = x :: rest.
    Proof.
      destruct l; cbn; [eauto|].
      destruct (z =? target)%Z; cbn; [eauto|].
      destruct (z <? target)%Z; cbn; eauto.
    Qed.

    Lemma insert_list_last (target : Z) (l : list Z) d :
      let new_l := insert_list_spec target l in
      List.last new_l d = List.last l d \/ List.last new_l d = target.
    Proof.
      destruct (destruct_list_back l) as [[z [init ?]]|]; rewrite e; [|cbn; auto]; clear e.
      rewrite last_last.
      induction init as [|z' mid]; cbn.
      - destruct (z =? target)%Z; cbn; [auto|].
        destruct (z <? target)%Z; cbn; auto.
      - destruct (z' =? target)%Z; [rewrite app_comm_cons; rewrite last_last; auto|].
        destruct (z' <? target)%Z.
        + cbn. destruct IHmid; rewrite H;
            destruct (inserted_list_cons target (mid ++ [z])) as [? [? ->]]; auto.
        + repeat rewrite app_comm_cons; rewrite last_last; auto.
    Qed.

    Lemma take_cons {A} (l : list A) n x rest : 1 <= n -> take n l = x :: rest -> exists rest', l = x :: rest'.
    Proof.
      intros nge1 Htake.
      destruct l; [rewrite take_nil in Htake; discriminate|].
      exists l.
      destruct n; [done|].
      rewrite firstn_cons in Htake.
      congruence.
    Qed.

    Lemma snoc_eq {A} (l l' : list A) x y : l ++ [x] = l' ++ [y] -> x = y.
    Proof.
      revert l'.
      induction l; destruct l'; cbn; intros; auto.
      - congruence.
      - inversion H; apply app_cons_not_nil in H2; done.
      - inversion H; apply app_eq_nil in H2; destruct H2; done.
      - inversion H; apply (IHl l'); done.
    Qed.

    Lemma drop_snoc {A} (l : list A) n x init : 1 <= n -> drop n l = init ++ [x] -> exists init', l = init' ++ [x].
    Proof.
      clear bpos.
      intros nge1 Hdrop.
      destruct (destruct_list_back l) as [[z [init' ?]]|]; rewrite e;  rewrite e in Hdrop.
      2:{ rewrite drop_nil in Hdrop.
          specialize (app_cons_not_nil init [] x) as ?.
          contradiction. }
      exists init'.
      apply app_inv_head_iff.
      assert (n <= length init').
      { clear nge1 e; revert dependent n.
        induction init'.
        - cbn; destruct n; [done|].
          rewrite skipn_cons; rewrite drop_nil.
          intros.
          apply app_cons_not_nil in Hdrop; done.
        - intros.
          destruct n; [cbn; lia|].
          rewrite skipn_cons in Hdrop.
          apply IHinit' in Hdrop.
          cbn; lia. }
      rewrite drop_app_le in Hdrop; [|done].
      apply snoc_eq in Hdrop; congruence.
    Qed.

    Lemma is_sorted_hd_last_contra x l : list_sorted (x :: l ++ [x]) -> False.
    Proof.
      clear bpos.
      intros.
      induction l.
      - cbn in H; lia.
      - apply IHl.
        destruct H.
        cbn; cbn in H0.
        destruct (l ++ [x]); auto.
        destruct H0.
        split; [lia|done].
    Qed.

    Lemma insert_list_hd_last_same_single (target : Z) (l : list Z) d d' :
      let new_l := insert_list_spec target l in
      list_sorted (insert_list_spec target l) ->
      hd d new_l = target -> List.last new_l d' = target ->
      new_l = [target].
    Proof.
      intros ? sorted_l hd_target last_target.
      destruct l; auto.
      destruct (destruct_list_back l) as [[z' [init' ?]]|]; subst l.
      - cbn in new_l, sorted_l;
          destruct (z =? target)%Z eqn:?, (z <? target)%Z eqn:?;
          subst new_l;
          cbn in hd_target.
        + rewrite app_comm_cons in last_target;
            rewrite last_last in last_target;
            rewrite hd_target last_target in sorted_l.
          apply is_sorted_hd_last_contra in sorted_l;
            contradiction.
        + rewrite app_comm_cons in last_target;
            rewrite last_last in last_target;
            rewrite hd_target last_target in sorted_l.
          apply is_sorted_hd_last_contra in sorted_l;
            contradiction.
        + rewrite Z.eqb_neq in Heqb0;
            congruence.
        + repeat rewrite app_comm_cons in last_target;
            rewrite last_last in last_target;
            rewrite last_target in sorted_l.
          rewrite app_comm_cons in sorted_l;
            apply is_sorted_hd_last_contra in sorted_l;
            contradiction.
      - cbn in new_l;
          destruct (z =? target)%Z eqn:?, (z <? target)%Z;
          cbn in hd_target, last_target;
          subst;
          auto;
          rewrite Z.eqb_neq in Heqb0;
          contradiction.
    Qed.

    Lemma insert_nary_tree_interval_Some (target : Z) (t : nary_tree) (t_wf : nary_tree_wf_no_len t) :
      let old_interval := nary_tree_interval t in
      let (new_tree_left, new_tree_right_opt) := insert_nary_tree_spec target t in
      forall new_tree_right, Some new_tree_right = new_tree_right_opt ->
      let new_interval_left := nary_tree_interval new_tree_left in
      let new_interval_right := nary_tree_interval new_tree_right in
      (new_interval_left.1 = old_interval.1 /\ new_interval_right.2 = old_interval.2)
      \/ (new_interval_left.1 = target /\ (target < old_interval.1)%Z /\ new_interval_right.2 = old_interval.2)
      \/ (new_interval_left.1 = old_interval.1 /\ (old_interval.2 < target)%Z /\ new_interval_right.2 = target).
    Proof.
    Admitted.

    Lemma insert_nary_tree_interval_None (target : Z) (t : nary_tree) (t_wf : nary_tree_wf_no_len t) :
      let old_interval := nary_tree_interval t in
      let (new_tree_left, new_tree_right_opt) := insert_nary_tree_spec target t in
      None = new_tree_right_opt ->
      let new_interval := nary_tree_interval new_tree_left in
      (new_interval.1 = old_interval.1 /\ new_interval.2 = old_interval.2)
      \/ (new_interval.1 = target /\ (target < old_interval.1)%Z /\ new_interval.2 = old_interval.2)
      \/ (new_interval.1 = old_interval.1 /\ (old_interval.2 < target)%Z /\ new_interval.2 = target).
    Admitted.

    Lemma insert_nary_tree_interval_list (target : Z) (ts : list nary_tree) (ts_wf : Forall nary_tree_wf_no_len ts) low high :
      let new_ts := (fix insert_aux (l : list nary_tree) : list nary_tree :=
                       match l with
                       | [] => []
                       | [t] =>
                           let (new_t1, new_t2) := insert_nary_tree_spec target t in
                           match new_t2 with
                           | Some new_t2' => [new_t1; new_t2']
                           | None => [new_t1]
                           end
                       | t :: (_ :: _) as ts0 =>
                           let (low0, high0) := nary_tree_interval t in
                           if (target <=? high0)%Z
                           then
                             let (new_t1, new_t2) := insert_nary_tree_spec target t in
                             match new_t2 with
                             | Some new_t2' => new_t1 :: new_t2' :: ts0
                             | None => new_t1 :: ts0
                             end
                           else t :: insert_aux ts0
                       end) ts in
      let old_interval :=
        ((match head (map fst (map nary_tree_interval ts)) with None => low | Some x => x end),
          (match last (map snd (map nary_tree_interval ts)) with None => high | Some x => x end))
      in
      let new_interval :=
        ((match head (map fst (map nary_tree_interval new_ts)) with None => low | Some x => x end),
          (match last (map snd (map nary_tree_interval new_ts)) with None => high | Some x => x end))
      in
      (new_interval.1 = old_interval.1 /\ new_interval.2 = old_interval.2) \/
        (new_interval.1 = target /\ (target < old_interval.1)%Z /\ new_interval.2 = old_interval.2) \/
        (new_interval.1 = old_interval.1 /\ (old_interval.2 < target)%Z /\ new_interval.2 = target).
    Admitted.
    Lemma insert_nary_tree_interval_Some_inside (target : Z) (t : nary_tree) (t_wf : nary_tree_wf_no_len t) :
      let old_interval := nary_tree_interval t in
      let (new_tree_left, new_tree_right_opt) := insert_nary_tree_spec target t in
      forall new_tree_right, Some new_tree_right = new_tree_right_opt ->
      let new_interval_left := nary_tree_interval new_tree_left in
      let new_interval_right := nary_tree_interval new_tree_right in
      (new_interval_left.2 < new_interval_right.1)%Z.
    Admitted.

    Definition insert_nary_tree_wf_no_len (target : Z) (t : nary_tree) (t_wf : nary_tree_wf_no_len t) : nary_tree_wf_no_len (insert_nary_tree_spec target t).1 /\ match (insert_nary_tree_spec target t).2 with Some t' => nary_tree_wf_no_len t' | None => True end.
      induction t as [[low high]|[low high] ts] using nary_tree_ind'.
      - admit.
      - cbn.
        remember ((fix insert_aux (l : list nary_tree) : list nary_tree :=
             match l with
             | [] => []
             | [t] =>
                 let (new_t1, new_t2) := insert_nary_tree_spec target t in
                 match new_t2 with
                 | Some new_t2' => [new_t1; new_t2']
                 | None => [new_t1]
                 end
             | t :: (_ :: _) as ts0 =>
                 let (low0, high0) := nary_tree_interval t in
                 if Z.leb target high0
                 then
                  let (new_t1, new_t2) := insert_nary_tree_spec target t in
                  match new_t2 with
                  | Some new_t2' => new_t1 :: new_t2' :: ts0
                  | None => new_t1 :: ts0
                  end
                 else t :: insert_aux ts0
             end) ts) as new_ts.
        destruct (Z.ltb b (length new_ts)) eqn:Hblt.
        + cbn.
          admit.
        + cbn.
          clear Hblt.
          inversion_clear t_wf
            as [| ? ? ? ? low_le_high intervals_in_interval trees_wf intervals_sorted].
          assert (match last (map snd intervals) with Some x => x | None => high end = high) as high_last by admit.
          revert dependent new_ts.
          induction ts as [|thd trest].
          * intros; rewrite Heqnew_ts; cbn; split; [constructor|]; done.
          * intros.
            cbn in intervals.
            destruct (nary_tree_interval thd) as [low' high'] eqn:?.
            apply Forall_cons in H, intervals_in_interval, trees_wf.
            cbn in high_last.
            destruct H as [Hthd Htrest],
                intervals_in_interval as [intint_thd intint_trest],
                  trees_wf as [thd_wf trest_wf],
                    intervals_sorted as [intsort_thd intsort_trest].
            specialize (Hthd thd_wf).
            remember ((fix insert_aux (l : list nary_tree) : list nary_tree :=
                               match l with
                               | [] => []
                               | [t] =>
                                   let (new_t1, new_t2) := insert_nary_tree_spec target t in
                                   match new_t2 with
                                   | Some new_t2' => [new_t1; new_t2']
                                   | None => [new_t1]
                                   end
                               | t :: (_ :: _) as ts0 =>
                                   let (low0, high0) := nary_tree_interval t in
                                   if (target <=? high0)%Z
                                   then
                                    let (new_t1, new_t2) := insert_nary_tree_spec target t in
                                    match new_t2 with
                                    | Some new_t2' => new_t1 :: new_t2' :: ts0
                                    | None => new_t1 :: ts0
                                    end
                                   else t :: insert_aux ts0
                               end) trest) as new_trest.
            assert (match last (map snd (map nary_tree_interval trest)) with
                    | Some x => x
                    | None => high
                    end = high)
              as high_last'
              by (destruct trest; [|cbn in high_last; cbn]; done).
            specialize (IHtrest Htrest intint_trest trest_wf intsort_trest high_last' new_trest eq_refl).
            destruct IHtrest as [IHtrest _].
            split; [|done].
            constructor.
            -- specialize (insert_nary_tree_interval_list target (thd :: trest) (Forall_cons_2 _ _ _ thd_wf trest_wf) low high) as new_ts_interval.
               cbn in new_ts_interval.
               rewrite <- Heqnew_trest in new_ts_interval.
               rewrite Heqp in new_ts_interval.
               rewrite <- Heqnew_ts in new_ts_interval.
               destruct new_ts_interval as [[-> ->] | [(-> & Htargetltold & ->) | (-> & Holdlttarget & ->)]].
               ++ rewrite high_last; cbn; inversion thd_wf; subst; inversion Heqp; lia.
               ++ rewrite high_last; cbn in Htargetltold; cbn; inversion thd_wf; subst; inversion Heqp; lia.
               ++ rewrite high_last in Holdlttarget; cbn; inversion thd_wf; subst; inversion Heqp; lia.
            -- inversion_clear IHtrest as [| ? ? ? ? _ intint_new_trest _ _].
               destruct trest.
               ++ destruct (insert_nary_tree_spec target thd) eqn:?; cbn in Hthd; destruct Hthd.
                  destruct o; subst new_ts; cbn.
                  ** specialize (insert_nary_tree_interval_Some_inside target thd thd_wf)
                       as new_ts_interval;
                       cbn in new_ts_interval;
                       rewrite Heqp0 in new_ts_interval;
                       specialize (new_ts_interval n0 eq_refl).
                     revert new_ts_interval.
                     inversion_clear H; inversion_clear H0;
                       cbn; intro;
                       apply Forall_cons_2; try apply Forall_cons_2;
                       try lia; done.
                  ** inversion_clear H; cbn; apply Forall_cons_2; try lia; done.
               ++ destruct ((target <=? high')%Z) eqn:?.
                  ** destruct (insert_nary_tree_spec target thd) eqn:?; destruct o; subst new_ts.
                     --- specialize (insert_nary_tree_interval_Some_inside target thd thd_wf)
                           as new_ts_interval;
                           cbn in new_ts_interval;
                           rewrite Heqp0 in new_ts_interval;
                           specialize (new_ts_interval n1 eq_refl).
                         specialize (insert_nary_tree_interval_Some target thd thd_wf)
                           as new_ts_interval';
                           rewrite Heqp0 in new_ts_interval';
                           cbn in new_ts_interval';
                           specialize (new_ts_interval' n1 eq_refl).
                         cbn; rewrite high_last'.
                         clear dependent new_trest.
                         (* all good here but need to destruct everything and lia *)
                         admit.
                     --- admit.
                  ** assert (not (new_trest = [])).
                     { intro; subst new_trest; destruct trest.
                       + destruct (insert_nary_tree_spec target n); destruct o; discriminate.
                       + destruct (nary_tree_interval n); destruct (target <=? z0)%Z; [|discriminate].
                         destruct (insert_nary_tree_spec target n); destruct o; discriminate. }
                     subst new_ts intervals0; cbn; apply Forall_cons; repeat split.
                     --- rewrite Heqp; cbn; split; [done|].
                         destruct new_trest; [done|].
                         specialize (insert_nary_tree_interval_list target (n :: trest) trest_wf low high)
                               as new_trest_interval;
                               cbn in new_trest_interval;
                               rewrite <- Heqnew_trest in new_trest_interval.
                         cbn in intsort_thd.
                         destruct (nary_tree_interval n0) eqn:?.
                         cbn in new_trest_interval, intsort_thd; cbn.
                         rewrite Heqp0; cbn.
                         rewrite Heqp0 in new_trest_interval; cbn in new_trest_interval.
                         rewrite Z.leb_gt in Heqb0.
                         destruct intint_thd.
                         rewrite high_last' in new_trest_interval.
                         destruct new_trest_interval as [[? ->] | [(? & _ & ->) | (? & ? & ->)]]; lia.
                     --- assert (forall interval : Z * Z,
                                    (let (low', high') := interval in
                                     (match head (map fst (map nary_tree_interval new_trest)) with
                                      | Some x => x
                                      | None => low
                                      end ≤ low')%Z
                                     ∧ (high'
                                          ≤ match last (map snd (map nary_tree_interval new_trest)) with
                                          | Some x => x
                                          | None => high
                                          end)%Z) ->
                                    (let (low'0, high'0) := interval in
                                     ((nary_tree_interval thd).1 ≤ low'0)%Z
                                     ∧ (high'0
                                          ≤ match last ((nary_tree_interval thd).2 :: map snd (map nary_tree_interval new_trest)) with
                                          | Some x => x
                                          | None => high
                                          end)%Z)).
                         { intros; destruct interval; destruct H0.
                           split.
                           - specialize (insert_nary_tree_interval_list target (n :: trest) trest_wf low high)
                               as new_trest_interval;
                               cbn in new_trest_interval;
                               rewrite <- Heqnew_trest in new_trest_interval.
                             cbn in intsort_thd.
                             destruct (nary_tree_interval n) eqn:?.
                             cbn in new_trest_interval, intsort_thd.
                             rewrite Heqp; cbn.
                             rewrite Z.leb_gt in Heqb0.
                             destruct new_trest_interval as [[? ?] | [(? & Htargetltold & ?) | (? & ? & ?)]];
                               inversion thd_wf; subst thd; cbn in Heqp; inversion Heqp; lia.
                           - destruct new_trest; done. }
                         apply (Forall_impl _ _ _ intint_new_trest H0).
            -- inversion_clear IHtrest as [| ? ? ? ? _ _ new_trest_wf _].
               rewrite Heqnew_ts.
               destruct trest.
               ++ destruct (insert_nary_tree_spec target thd); cbn in Hthd; destruct Hthd.
                  destruct o; apply Forall_cons_2; auto.
               ++ destruct ((target <=? high')%Z).
                  ** destruct (insert_nary_tree_spec target thd); cbn in Hthd; destruct Hthd.
                     destruct o; apply Forall_cons_2; auto.
                  ** apply Forall_cons; auto.
            -- inversion_clear IHtrest as [| ? ? ? ? _ _ _ intsort_new_trest].
               subst intervals0.
               rewrite Heqnew_ts.
               destruct trest.
               ++ destruct (insert_nary_tree_spec target thd) eqn:?; cbn in Hthd; destruct Hthd.
                  destruct o.
                  ** specialize (insert_nary_tree_interval_Some_inside target thd thd_wf) as new_ts_interval.
                     cbn in new_ts_interval; rewrite Heqp0 in new_ts_interval; specialize (new_ts_interval n0 eq_refl).
                     cbn;
                       destruct (nary_tree_interval n), (nary_tree_interval n0);
                       done.
                  ** cbn; destruct (nary_tree_interval n); done.
               ++ destruct ((target <=? high')%Z) eqn:?.
                  ** destruct (insert_nary_tree_spec target thd) eqn:?; cbn in Hthd; destruct Hthd.
                     destruct o.
                     --- specialize (insert_nary_tree_interval_Some_inside target thd thd_wf) as new_ts_interval.
                         cbn in new_ts_interval; rewrite Heqp0 in new_ts_interval; specialize (new_ts_interval n1 eq_refl).
                         destruct (nary_tree_interval n0) eqn:?,
                           (nary_tree_interval n1) eqn:?,
                           (nary_tree_interval n) eqn:?;
                           cbn; rewrite Heqp1 Heqp2 Heqp3.
                         cbn in intsort_trest; rewrite Heqp3 in intsort_trest; destruct intsort_trest.
                         specialize (insert_nary_tree_interval_Some target thd thd_wf) as new_ts_interval'.
                         rewrite Heqp0 in new_ts_interval';
                           cbn in new_ts_interval';
                           specialize (new_ts_interval' n1 eq_refl);
                           rewrite Heqp Heqp1 Heqp2 in new_ts_interval';
                           cbn in new_ts_interval'.
                         repeat split; [done| |done|done].
                         destruct new_ts_interval' as [[? ->] | [(? & Htargetltold & ?) | (? & ? & ?)]].
                         +++ cbn in intsort_thd; rewrite Heqp3 in intsort_thd; lia.
                         +++ cbn in intsort_thd; rewrite Heqp3 in intsort_thd; lia.
                         +++ rewrite Z.leb_le in Heqb0.
                             lia.
                     --- specialize (insert_nary_tree_interval_None target thd thd_wf) as new_ts_interval.
                         cbn in new_ts_interval; rewrite Heqp0 in new_ts_interval; specialize (new_ts_interval eq_refl).
                         destruct (nary_tree_interval n0) eqn:?,
                           (nary_tree_interval n) eqn:?;
                           cbn; rewrite Heqp1 Heqp2.
                         cbn in intsort_trest; rewrite Heqp2 in intsort_trest; destruct intsort_trest.
                         rewrite Heqp in new_ts_interval; cbn in new_ts_interval.
                         cbn in intsort_thd; rewrite Heqp2 in intsort_thd.
                         repeat split; [|done|done].
                         destruct new_ts_interval as [[? ->] | [(? & Htargetltold & ?) | (? & ? & ?)]]; lia.
                  ** cbn; rewrite Heqp.
                     split; [|done].
                     specialize (insert_nary_tree_interval_list target (n :: trest) trest_wf low high) as new_ts_interval.
                     cbn in new_ts_interval; rewrite <- Heqnew_trest in new_ts_interval.
                     destruct (nary_tree_interval n) eqn:?.
                     cbn in intsort_thd; rewrite Heqp0 in intsort_thd.
                     destruct new_trest; [done|].
                     cbn; cbn in new_ts_interval.
                     destruct (nary_tree_interval n0) eqn:?.
                     cbn in new_ts_interval.
                     destruct new_ts_interval as [[? _] | [(? & Htargetltold & _) | (? & ? & _)]].
                     --- lia.
                     --- rewrite Z.leb_gt in Heqb0; lia.
                     --- lia.
    Admitted.

    Definition insert_bplus_tree_wf (target : Z) (t : tree_spec) (t_wf : tree_spec_wf b t) : (tree_spec_wf b (insert_bplus_tree_spec target t)).
      destruct t as [[low high]|[low high] ts].
      - cbn; destruct (Z.leb b (length (insert_list_spec target l))) eqn:Hble.
        + rewrite Z.leb_le in Hble;
            assert (b <= length (insert_list_spec target l)) as Hble' by lia.
          inversion t_wf; subst.
          specialize (insert_list_sorted _ target H6) as inserted_list_sorted.
          constructor.
          * specialize (bge2 b beven bpos) as ?.
            cbn; lia.
          * destruct (take_b2_cons' (insert_list_spec target l) Hble') as (thd & trest & Hthdtrest);
              cbn in Hthdtrest; rewrite Hthdtrest.
            destruct (drop_b2_snoc' (insert_list_spec target l) Hble') as (dlast & dinit & Hdinitdlast);
              cbn in Hdinitdlast; rewrite Hdinitdlast.
            cbn; rewrite last_last.
            specialize (in_eq thd trest) as ?;
              specialize (in_elt dlast dinit []) as ?.
            rewrite <- Hthdtrest in H; rewrite <- Hdinitdlast in H0.
            specialize (split_list_sorted _ _ inserted_list_sorted _ _ H H0).
            lia.

          * repeat constructor; try lia.
            -- destruct (take_b2_snoc' (insert_list_spec target l) Hble') as (tlast & tinit & Htinittlast);
                 cbn in Htinittlast; rewrite Htinittlast.
               destruct (drop_b2_snoc' (insert_list_spec target l) Hble') as (dlast & dinit & Hdinitdlast);
                 cbn in Hdinitdlast; rewrite Hdinitdlast.
               repeat rewrite last_last.
               specialize (in_elt tlast tinit []) as ?;
                 specialize (in_elt dlast dinit []) as ?;
                 rewrite <- Htinittlast in H;
                 rewrite <- Hdinitdlast in H0.
               specialize (split_list_sorted _ _ inserted_list_sorted _ _ H H0);
                 lia.
            -- destruct (take_b2_cons' (insert_list_spec target l) Hble') as (thd & trest & Hts);
                 cbn in Hts; rewrite Hts.
               destruct (drop_b2_cons' (insert_list_spec target l) Hble') as (dhd & drest & Hds);
                 cbn in Hds; rewrite Hds.
               cbn.
               specialize (in_eq thd trest) as ?;
                 specialize (in_eq dhd drest) as ?;
                 rewrite <- Hts in H;
                 rewrite <- Hds in H0.
               specialize (split_list_sorted _ _ inserted_list_sorted _ _ H H0);
                 lia.

          * constructor; [|constructor]; [| |done].
            -- constructor.
               ++ specialize (list_sorted_take_sorted _ (b/2) inserted_list_sorted) as ?.
                  apply list_sorted_hd_lt_last; done.
               ++ destruct (take (Nat.divmod b 1 0 1).1 (insert_list_spec target l)); done.
               ++ destruct (destruct_list_back (take (Nat.divmod b 1 0 1).1 (insert_list_spec target l)))
                    as [[last [init ?]]|];
                    rewrite e; [repeat rewrite last_last|cbn]; done.
               ++ assert (b/2 < b) by (apply Nat.div_lt; lia).
                  assert (b/2 <= length (insert_list_spec target l)) by lia.
                  rewrite (take_length_le (insert_list_spec target l) (b/2));
                    [lia|done].
               ++ apply (list_sorted_take_sorted _ (b/2) inserted_list_sorted).
            -- constructor.
               ++ specialize (list_sorted_drop_sorted _ (b/2) inserted_list_sorted) as ?.
                  apply list_sorted_hd_lt_last; done.
               ++ destruct (drop (Nat.divmod b 1 0 1).1 (insert_list_spec target l)); done.
               ++ destruct (destruct_list_back (drop (Nat.divmod b 1 0 1).1 (insert_list_spec target l)))
                    as [[last [init ?]]|];
                    rewrite e; [repeat rewrite last_last|cbn]; done.
               ++ rewrite (drop_length (insert_list_spec target l) (b/2)).
                  specialize (root_leaf_wf_split_length _ _ target t_wf Hble') as ?.
                  enough (b/2 + b/2 <= length (insert_list_spec target l) <= b + b/2); [lia|].
                  rewrite <- H.
                  rewrite <- Nat.div2_div;
                    specialize (Zeven_div2 _ beven) as ?;
                    replace (Nat.div2 b + Nat.div2 b) with (2 * Nat.div2 b) by lia;
                    rewrite <- nat_N_Z in H0;
                    rewrite <- N2Z.inj_div2 in H0;
                    replace (2%Z) with (Z.of_N 2) in H0 by lia;
                    rewrite <- N2Z.inj_mul in H0;
                    apply N2Z.inj in H0;
                    rewrite N.div2_div in H0;
                    replace (2%N) with (N.of_nat 2) in H0 by lia;
                    rewrite <- Nat2N.inj_div in H0;
                    rewrite <- Nat2N.inj_mul in H0;
                    apply Nat2N.inj in H0;
                    rewrite H0;
                    rewrite Nat.div2_double.
                  lia.
               ++ apply (list_sorted_drop_sorted _ (b/2) inserted_list_sorted).
          * cbn; split; auto.
            destruct (take_b2_snoc' (insert_list_spec target l) Hble') as (tlast & tinit & Hts);
              cbn in Hts; rewrite Hts.
            destruct (drop_b2_cons' (insert_list_spec target l) Hble') as (dhd & drest & Hds);
              cbn in Hds; rewrite Hds.
            rewrite last_last; cbn.
            specialize (in_elt tlast tinit []) as ?;
              specialize (in_eq dhd drest) as ?;
              rewrite <- Hts in H;
              rewrite <- Hds in H0.
            specialize (split_list_sorted _ _ inserted_list_sorted _ _ H H0).
            lia.
        + inversion t_wf; subst.
          specialize (insert_list_sorted _ target H6) as inserted_list_sorted.
          constructor.
          * apply (list_sorted_hd_lt_last _ low high inserted_list_sorted H2).
          * destruct (insert_list_spec target l); done.
          * destruct (destruct_list_back (insert_list_spec target l))
              as [[last [init ?]]|];
              rewrite e; [repeat rewrite last_last|cbn]; done.
          * rewrite Z.leb_gt in Hble; lia.
          * done.

      - cbn.
        remember ((fix insert_aux (l : list nary_tree) : list nary_tree :=
             match l with
             | [] => []
             | [t] =>
                 let (new_t1, new_t2) := insert_nary_tree_spec target t in
                 match new_t2 with
                 | Some new_t2' => [new_t1; new_t2']
                 | None => [new_t1]
                 end
             | t :: (_ :: _) as ts0 =>
                 let (low0, high0) := nary_tree_interval t in
                 if Z.leb target high0
                 then
                  let (new_t1, new_t2) := insert_nary_tree_spec target t in
                  match new_t2 with
                  | Some new_t2' => new_t1 :: new_t2' :: ts0
                  | None => new_t1 :: ts0
                  end
                 else t :: insert_aux ts0
             end) ts) as new_ts.
        destruct (Z.ltb b (length new_ts)) eqn:Hblt.
        + rewrite Z.ltb_lt in Hblt.
          assert (b < length new_ts) as Hblt' by lia.
          assert (b <= length new_ts) as Hble by lia.
          inversion_clear t_wf
            as [| ? ? ? ? ? ? intervals_in_interval trees_wf intervals_sorted];
            subst intervals.
          constructor.
          * specialize (bge2 b beven bpos); cbn; lia.
          * destruct (take_b2_cons' new_ts Hble) as (thd & trest & Hts);
              cbn in Hts; rewrite Hts.
            destruct (drop_b2_snoc' new_ts Hble) as (dlast & dinit & Hds);
              cbn in Hds; rewrite Hds.
            cbn; repeat rewrite last_map_comm; rewrite last_snoc.
            specialize (in_eq thd trest) as ?;
              specialize (in_elt dlast dinit []) as ?.
            rewrite <- Hts in H1; rewrite <- Hds in H2.
            admit.
          * cbn.
            repeat constructor; try done.
            -- destruct (take_b2_snoc' new_ts Hble) as (tlast & tinit & Hts);
                 cbn in Hts; rewrite Hts.
               destruct (drop_b2_snoc' new_ts Hble) as (dlast & dinit & Hds);
                 cbn in Hds; rewrite Hds.
               repeat rewrite last_map_comm; repeat rewrite last_snoc.
               admit.
            -- destruct (take_b2_cons' new_ts Hble) as (thd & trest & Hts);
                 cbn in Hts; rewrite Hts.
               destruct (drop_b2_cons' new_ts Hble) as (dhd & drest & Hds);
                 cbn in Hds; rewrite Hds.
               cbn.
               admit.
          * constructor; [|constructor]; [| |done].
            -- constructor.
               ++ assert (b/2 < b) by (apply Nat.div_lt; lia).
                  assert (b/2 <= length new_ts) by lia.
                  rewrite (take_length_le new_ts (b/2));
                    [lia|done].
               ++ destruct (take_b2_snoc' new_ts Hble) as (tlast & tinit & Hts);
                    cbn in Hts; rewrite Hts;
                    repeat rewrite last_map_comm; rewrite last_snoc;
                    rewrite <- Hts.
                  destruct (take_b2_cons' new_ts Hble) as (thd & trest & Hts');
                    cbn in Hts'; rewrite Hts';
                    cbn.
                  admit.
               ++ admit.
               ++ admit.
               ++ admit.
            -- admit.
          * cbn.
            destruct (take_b2_snoc' new_ts Hble) as (tlast & tinit & Hts);
              cbn in Hts; rewrite Hts.
            destruct (drop_b2_cons' new_ts Hble) as (dhd & drest & Hds);
              cbn in Hds; rewrite Hds.
            repeat rewrite last_map_comm; rewrite last_snoc; cbn.
            admit.
        + admit.
    Admitted.

End nary_tree.

Section bplus_tree.
  Section bplus_tree_algos.
    Context (b : nat).

    Definition insert_list : val :=
      rec: "insert_list" "arg" :=
        let: "p" := Fst "arg" in
        let: "target" := Snd "arg" in
        match: "p" with
          NONE =>
            let: "ptr" := ref ("target", NONEV) in
            SOME "ptr"
        | SOME "l" =>
            let: "val" := Fst !"l" in
            if: "val" = "target"
            then SOME "l"
            else
              if: (BinOp LtOp "val" "target")
              then let: "new" := "insert_list" (Snd !"l", "target") in
                   "l" <- ("val", "new");;
                   SOME "l"
              else SOME (ref ("target", SOME "l"))
        end.

    Definition length_list : val :=
      rec: "length_list" "p" :=
        match: "p" with
          NONE => #0
        | SOME "l" => #1 + "length_list" (Snd !"l")
        end.

    Definition split_list : val :=
      rec: "split_list" "arg" :=
        let: "p" := Fst "arg" in
        let: "n" := Snd "arg" in
        if: "n" = #0
        then (NONEV, "p")
        else
          match: "p" with
            NONE => (NONEV, NONEV)
          | SOME "l" =>
              let: "x" := Fst !"l" in
              let: "rest" := Snd !"l" in
              let: "rec" := "split_list" ("rest", "n" - #1) in
              "l" <- ("x", Fst "rec") ;;
              (SOME "l", Snd "rec")
          end.

    Definition head_list : val :=
      rec: "head_list" "arg" :=
        match: Fst "arg" with
          NONE => Snd "arg"
        | SOME "l" => Fst !"l"
        end.

    Definition last_list : val :=
      rec: "last_list" "arg" :=
        match: Fst "arg" with
          NONE => Snd "arg"
        | SOME "l" =>
            match: Snd !"l" with
              NONE => Fst !"l"
            | SOME "l'" => "last_list" (SOME "l'", Snd "arg")
            end
        end.

    Definition headopt_list : val :=
      rec: "headopt_list" "l" :=
        match: "l" with
          NONE => NONE
        | SOME "l" => SOME (Fst !"l")
        end.

    Definition lastopt_list : val :=
      rec: "lastopt_list" "l" :=
        match: "l" with
          NONE => NONE
        | SOME "l" =>
            match: Snd !"l" with
              NONE => SOME (Fst !"l")
            | SOME "l'" => "lastopt_list" (SOME "l'")
            end
        end.

    Definition interval_nary_tree : val :=
      rec: "interval_nary_tree" "t" :=
        match: "t" with
          InjL "ptr" => Fst !"ptr"
        | InjR "ptr" => Fst !"ptr"
        end.

    Definition insert_nary_tree : val :=
      rec: "insert_nary_tree" "arg" :=
        let: "t" := Fst "arg" in
        let: "target" := Snd "arg" in
        match: "t" with
          InjL "ptr" =>
            let: "lhd" := Snd !"ptr" in
            let: "interval" := Fst !"ptr" in
            let: "new" := insert_list ("lhd", "target") in
            if: #b < length_list "new"
            then
              let: "newlpair" := split_list ("new", #(b/2)) in
              let: "newhead1" := head_list (Fst "newlpair", Fst "interval") in
              let: "newlast1" := last_list (Fst "newlpair", Snd "interval") in
              let: "newhead2" := head_list (Snd "newlpair", Fst "interval") in
              let: "newlast2" := last_list (Snd "newlpair", Snd "interval") in
              let: "newleaf" := ref (("newhead2", "newlast2"), Snd "newlpair") in
              "ptr" <- (("newhead1", "newlast1"), Fst "newlpair") ;;
              (token_leaf_e "ptr", SOME (token_leaf_e "newleaf"))
            else
              let: "head" := head_list ("new", Fst "interval") in
              let: "last" := last_list ("new", Snd "interval") in
              "ptr" <- (("head", "last"), "new") ;;
              (token_leaf_e "ptr", NONEV)
        | InjR "ptr" =>
            let: "lhd" := Snd !"ptr" in
            let: "new" :=
              (rec: "insert_node_list" "arg" :=
                 let: "p" := Fst "arg" in
                 let: "target" := Snd "arg" in
                 match: "p" with
                   NONE =>
                     NONE
                 | SOME "l" =>
                     match: Snd !"l" with
                       NONE =>
                         let: "newt" := "insert_nary_tree" (Fst !"l", "target") in
                         match: Snd "newt" with
                           NONE => "l" <- (Fst "newt", NONE)
                         | SOME "newt2" =>
                             let: "l'" := ref ("newt2", NONE) in
                             "l" <- (Fst "newt", SOME "l'")
                         end
                     | SOME "_" =>
                         let: "thd" := Fst !"l" in
                         let: "interval" := interval_nary_tree "thd" in
                         let: "low" := Fst "interval" in
                         let: "high" := Snd "interval" in
                         (if: (BinOp LeOp "target" "high")
                          then let: "newt" := "insert_nary_tree" ("thd", "target") in
                               match: Snd "newt" with
                                 NONE => "l" <- (Fst "newt", Snd !"l")
                               | SOME "newt2" =>
                                   let: "l'" := ref ("newt2", Snd !"l") in
                                   "l" <- (Fst "newt", SOME "l'")
                               end
                          else let: "newl" := "insert_node_list" (Snd !"l", "target") in
                               "l" <- ("thd", "newl"))
                     end ;; SOME "l"
                 end) ("lhd", "target") in
            let: "interval" := Fst !"ptr" in
            if: #b < length_list "new"
            then
              let: "newlpair" := split_list ("new", #(b/2)) in
              let: "newheadleft" :=
                match: headopt_list (Fst "newlpair") with
                  NONE => Fst "interval"
                | SOME "t" => Fst (interval_nary_tree "t")
                end in
              let: "newlastleft" :=
                match: lastopt_list (Fst "newlpair") with
                  NONE => Snd "interval"
                | SOME "t" => Snd (interval_nary_tree "t")
                end in
              let: "newheadright" :=
                match: headopt_list (Snd "newlpair") with
                  NONE => Fst "interval"
                | SOME "t" => Fst (interval_nary_tree "t")
                end in
              let: "newlastright" :=
                match: lastopt_list (Snd "newlpair") with
                  NONE => Snd "interval"
                | SOME "t" => Snd (interval_nary_tree "t")
                end in
              let: "newbranch" := ref (("newheadright", "newlastright"), Snd "newlpair") in
              "ptr" <- (("newheadleft", "newlastleft"), Fst "newlpair") ;;
              (token_branch_e "ptr", SOME (token_branch_e "newbranch"))
            else
              let: "newhead" :=
                match: headopt_list "new" with
                  NONE => Fst "interval"
                | SOME "t" => Fst (interval_nary_tree "t")
                end in
              let: "newlast" :=
                match: lastopt_list "new" with
                  NONE => Snd "interval"
                | SOME "t" => Snd (interval_nary_tree "t")
                end in
              "ptr" <- (("newhead", "newlast"), "new") ;;
              (token_branch_e "ptr", NONEV)
        end%E.

    Fixpoint make_list (l : list expr) : expr :=
      match l with
      | [] => NONE
      | x :: l' =>
          let: "loc" := ref (x, make_list l') in
          SOME "loc"
      end%E.

    Definition insert_bplus_tree : val :=
      rec: "insert_bplus_tree" "arg" :=
        let: "t" := Fst "arg" in
        let: "target" := Snd "arg" in
        match: "t" with
          InjL "ptr" =>
            let: "lhd" := Snd !"ptr" in
            let: "interval" := Fst !"ptr" in
            let: "new" := insert_list ("lhd", "target") in
            if: BinOp LeOp #b (length_list "new")
            then
              let: "newlpair" := split_list ("new", #(b/2)) in
              let: "newheadleft" := head_list (Fst "newlpair", Fst "interval") in
              let: "newlastleft" := last_list (Fst "newlpair", Snd "interval") in
              let: "newheadright" := head_list (Snd "newlpair", Fst "interval") in
              let: "newlastright" := last_list (Snd "newlpair", Snd "interval") in
              let: "newleaf" := ref (("newheadright", "newlastright"), Snd "newlpair") in
              let: "newrootlist" := make_list (token_leaf_e "ptr" :: token_leaf_e "newleaf" :: []) in
              let: "newroot" := ref (("newheadleft", "newlastright"), "newrootlist")  in
              "ptr" <- (("newheadleft", "newlastleft"), Fst "newlpair") ;;
              token_branch_e "newroot"
            else
              let: "head" := head_list ("new", Fst "interval") in
              let: "last" := last_list ("new", Snd "interval") in
              "ptr" <- (("head", "last"), "new") ;;
              token_leaf_e "ptr"
        | InjR "ptr" =>
            let: "lhd" := Snd !"ptr" in
            let: "new" :=
              (rec: "insert_node_list" "arg" :=
                 let: "p" := Fst "arg" in
                 let: "target" := Snd "arg" in
                 match: "p" with
                   NONE =>
                     NONE
                 | SOME "l" =>
                     match: Snd !"l" with
                       NONE =>
                         let: "newt" := insert_nary_tree (Fst !"l", "target") in
                         match: Snd "newt" with
                           NONE => "l" <- (Fst "newt", NONE)
                         | SOME "newt2" =>
                             let: "l'" := ref ("newt2", NONE) in
                             "l" <- (Fst "newt", SOME "l'")
                         end
                     | SOME "_" =>
                         let: "thd" := Fst !"l" in
                         let: "interval" := interval_nary_tree "thd" in
                         let: "low" := Fst "interval" in
                         let: "high" := Snd "interval" in
                         (if: BinOp LeOp "target" "high"
                          then let: "newt" := insert_nary_tree ("thd", "target") in
                               match: Snd "newt" with
                                 NONE => "l" <- (Fst "newt", Snd !"l")
                               | SOME "newt2" =>
                                   let: "l'" := ref ("newt2", Snd !"l") in
                                   "l" <- (Fst "newt", SOME "l'")
                               end
                          else let: "newl" := "insert_node_list" (Snd !"l", "target") in
                               "l" <- ("thd", "newl"))
                     end ;; SOME "l"
                 end) ("lhd", "target") in
            let: "interval" := Fst !"ptr" in
            if: #b < length_list "new"
            then
              let: "newlpair" := split_list ("new", #(b/2)) in
              let: "newheadleft" :=
                match: headopt_list (Fst "newlpair") with
                  NONE => Fst "interval"
                | SOME "t" => Fst (interval_nary_tree "t")
                end in
              let: "newlastleft" :=
                match: lastopt_list (Fst "newlpair") with
                  NONE => Snd "interval"
                | SOME "t" => Snd (interval_nary_tree "t")
                end in
              let: "newheadright" :=
                match: headopt_list (Snd "newlpair") with
                  NONE => Fst "interval"
                | SOME "t" => Fst (interval_nary_tree "t")
                end in
              let: "newlastright" :=
                match: lastopt_list (Snd "newlpair") with
                  NONE => Snd "interval"
                | SOME "t" => Snd (interval_nary_tree "t")
                end in
              let: "newbranch" := ref (("newheadright", "newlastright"), Snd "newlpair") in
              let: "newrootlist" := make_list (token_branch_e "ptr" :: token_branch_e "newbranch" :: []) in
              let: "newroot" := ref (("newheadleft", "newlastright"), "newrootlist")  in
              "ptr" <- (("newheadleft", "newlastleft"), Fst "newlpair") ;;
              token_branch_e "newroot"
            else
              let: "newhead" :=
                match: headopt_list "new" with
                  NONE => Fst "interval"
                | SOME "t" => Fst (interval_nary_tree "t")
                end in
              let: "newlast" :=
                match: lastopt_list "new" with
                  NONE => Snd "interval"
                | SOME "t" => Snd (interval_nary_tree "t")
                end in
              "ptr" <- (("newhead", "newlast"), "new") ;;
              token_branch_e "ptr"
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

    Lemma insert_list_spec_proof (v : val) (l : list tval) (target : tval):
      {{{ is_list v (map (fun (x : tval) => #x) l) }}} insert_list (v, (#target))%V {{{ r, RET r; is_list r (map (fun (x : tval) => #x) (insert_list_spec target l)) }}}.
    Proof.
      clear bpos.
      iIntros (Φ) "Hl HPost".
      iInduction l as [|x l] "IH" forall (Φ v); wp_rec; wp_pures.
      - iDestruct "Hl" as "->".
        wp_alloc ptr as "Hptr"; wp_pures.
        iApply "HPost".
        iExists ptr, (InjLV #()).
        iFrame.
        done.
      - iDestruct "Hl" as (l' ?) "(-> & Hl' & Hl)".
        wp_match; wp_load; wp_pures.
        destruct (bool_decide (#x = #target)) eqn:?.
        + wp_pures.
          iApply "HPost".
          cbn; rewrite (bool_decide_true_Zeqb _ _ Heqb0).
          iExists l', hd'.
          iFrame.
          done.
        + wp_pures.
          destruct (bool_decide (Z.lt x target)) eqn:?; wp_pures.
          * wp_bind (insert_list _); wp_load; wp_pures.
            iApply ("IH" with "[Hl]"); [done|].
            iNext.
            iIntros (?) "Hr".
            wp_store; wp_pure.
            iApply "HPost".
            unfold insert_list_spec.
            rewrite (bool_decide_false_Zeqb _ _ Heqb0).
            rewrite bool_decide_eq_true in Heqb1;
              apply Z.ltb_lt in Heqb1;
              rewrite Heqb1.
            iExists l', r.
            iFrame.
            done.
          * wp_alloc new as "Hnew"; wp_pure.
            iApply "HPost".
            unfold insert_list_spec;
              specialize (bool_decide_false_Zeqb _ _ Heqb0) as ?;
              rewrite bool_decide_eq_false in Heqb1;
              assert (Z.le target x) by lia;
              apply Z.leb_le in H0;
              rewrite Z.leb_antisym in H0;
              symmetry in H0;
              apply negb_sym in H0;
              cbn in H0;
              rewrite H H0.
            iExists new, (InjRV #l').
            iFrame.
            iSplitR; [done|].
            iExists l', hd'.
            iFrame.
            done.
    Qed.

    Lemma length_list_spec_proof (v : val) (l : list val):
      {{{ is_list v l }}} length_list v {{{ r, RET #r; ⌜r = Z.of_nat (length l)⌝ ∗ is_list v l }}}.
    Proof.
      iIntros (Φ) "Hl HPost".

      iInduction l as [] "IH" forall (Φ v).
      - iDestruct "Hl" as "->".
        wp_rec; wp_pures.
        iApply ("HPost" $! 0).
        done.
      - iDestruct "Hl" as (l' ?) "(-> & Hl' & Hl)".
        wp_rec; wp_load; wp_pure; wp_bind (length_list _).
        iApply ("IH" with "[Hl]"); [iFrame|].
        iNext.
        iIntros (?) "[-> Hl]".
        wp_pure.
        iApply ("HPost" $! (1 + length l)%Z).
        iSplitR;
          [ iPureIntro; rewrite Z.add_1_l Nat2Z.inj_succ; done
          | iExists l', hd'; iFrame; done ].
    Qed.

    Lemma firstn_nil {A} n : @firstn A n [] = [].
    Proof. induction n; done. Qed.

    Lemma skipn_nil {A} n : @skipn A n [] = [].
    Proof. induction n; done. Qed.

    Lemma split_list_spec_proof (v : val) (l : list val) (n : nat):
      {{{ is_list v l }}} split_list (v, #(Z.of_nat n))%V {{{ r, RET (r.1, r.2); is_list r.1 (firstn n l) ∗ is_list r.2 (skipn n l) }}}.
    Proof.
      clear bpos.
      iIntros (Φ) "Hl HPost".
      iInduction n as [] "IH" forall (Φ v l).
      - wp_rec; wp_pures.
        iApply ("HPost" $! (InjLV #(), v)).
        unfold take, drop.
        cbn.
        iFrame.
        done.
      - wp_rec; wp_pures;
          destruct l.
        + iDestruct "Hl" as "->".
          wp_pures.
          iApply ("HPost" $! (InjLV #(), InjLV #())).
          rewrite firstn_nil skipn_nil.
          done.

        + iDestruct "Hl" as (l' ?) "(-> & Hl' & Hl)".
          wp_load; wp_load; wp_pures; wp_bind (split_list _).
          replace (Z.sub (S n) 1) with (Z.of_nat n) by lia.
          iApply ("IH" with "[Hl]"); [done|].
          iNext.
          iIntros (?) "[Hr1 Hr2]".
          wp_store; wp_pures.
          iApply ("HPost" $! (InjRV #l', r.2)).
          iSplitL "Hl' Hr1"; [iExists l', r.1; iFrame; done|].
          done.
    Qed.

    Lemma head_list_spec_proof (v : val) (l : list val) (d : val):
      {{{ is_list v l }}} head_list (v, d)%V {{{ r, RET r; ⌜r = hd d l⌝ ∗ is_list v l }}}.
    Proof.
      iIntros (Φ) "Hl HPost".
      wp_lam; wp_pures.
      destruct l as [|x l].
      - iDestruct "Hl" as "->".
        wp_pures.
        iApply "HPost".
        done.
      - iDestruct "Hl" as (l' ?) "(-> & Hl' & Hl)".
        wp_load; wp_pures.
        iApply "HPost".
        iSplitR; [done|].
        iExists l', hd'.
        iFrame; done.
    Qed.

    Lemma last_list_spec_proof (v : val) (l : list val) (d : val):
      {{{ is_list v l }}} last_list (v, d)%V {{{ r, RET r; ⌜r = List.last l d⌝ ∗ is_list v l }}}.
    Proof.
      iIntros (Φ) "Hl HPost".
      iInduction l as [|x l] "IH" forall (v);
        wp_rec; wp_pures.
      - iDestruct "Hl" as "->".
        wp_pures.
        iApply "HPost".
        iFrame; done.
      - iDestruct "Hl" as (l' ?) "(-> & Hl' & Hl)".
        wp_load; wp_pures.
        destruct l as [|x' l].
        + iDestruct "Hl" as "->".
          wp_load; wp_pures.
          iApply "HPost".
          iSplitR; [done|].
          iExists l', NONEV.
          iFrame; done.
        + iDestruct "Hl" as (l'' ?) "(-> & Hl'' & Hl)".
          wp_pures.
          iApply ("IH" with "[Hl Hl'']"); [iExists l'', hd'0; iFrame; done|].
          iNext.
          iIntros (?) "[-> Hl'']".
          iApply "HPost".
          iSplitR; [done|].
          iExists l', (SOMEV #l'').
          iFrame; done.
    Qed.

    Lemma headopt_list_spec_proof (v : val) (l : list val):
      {{{ is_list v l }}} headopt_list v%V {{{ r, RET r; ⌜r = match head l with None => NONEV | Some x => SOMEV x end⌝ ∗ is_list v l }}}.
    Proof.
      iIntros (Φ) "Hl HPost".
      wp_lam; wp_pures.
      destruct l as [|x l].
      - iDestruct "Hl" as "->".
        wp_pures.
        iApply "HPost".
        done.
      - iDestruct "Hl" as (l' ?) "(-> & Hl' & Hl)".
        wp_load; wp_pures.
        iApply "HPost".
        iSplitR; [done|].
        iExists l', hd'.
        iFrame; done.
    Qed.

    Lemma lastopt_list_spec_proof (v : val) (l : list val):
      {{{ is_list v l }}} lastopt_list v%V {{{ r, RET r; ⌜r = match last l with None => NONEV | Some x => SOMEV x end⌝ ∗ is_list v l }}}.
    Proof.
      iIntros (Φ) "Hl HPost".
      iInduction l as [|x l] "IH" forall (v);
        wp_lam; wp_pures.
      - iDestruct "Hl" as "->".
        wp_pures.
        iApply "HPost"; done.
      - iDestruct "Hl" as (l' ?) "(-> & Hl' & Hl)".
        wp_load; wp_pures.
        destruct l as [|x' l].
        + iDestruct "Hl" as "->".
          wp_load; wp_pures.
          iApply "HPost".
          iSplitR; [done|].
          iExists l', NONEV.
          iFrame; done.
        + iDestruct "Hl" as (l'' ?) "(-> & Hl'' & Hl)".
          wp_pures.
          iApply ("IH" with "[Hl'' Hl]"); [iExists l'', hd'0; iFrame; done|].
          iNext.
          iIntros (?) "[% Hl'']".
          iApply "HPost".
          iSplitR; [done|].
          iExists l', (SOMEV #l''); iFrame; done.
    Qed.

    Lemma interval_nary_tree_spec_proof (v : val) (t : nary_tree) :
      {{{ is_node v t }}} interval_nary_tree v%V {{{ r, RET (#r.1, #r.2); is_node v t ∗ ⌜r = nary_tree_interval t⌝ }}}.
    Proof.
      iIntros (?) "Hv HPost".
      destruct t; destruct interval as [low high].
      - iDestruct "Hv" as (ptr leaves) "(-> & Hptr & Hleaves)".
        wp_rec; wp_load; wp_pures.
        iApply ("HPost" $! (low, high)).
        iSplitL; [iExists ptr, leaves; iFrame|]; done.
      - iDestruct "Hv" as (ptr ns branches) "(-> & Hptr & Hns & Hbranches)".
        wp_rec; wp_load; wp_pures.
        iApply ("HPost" $! (low, high)).
        iSplitL; [iExists ptr, ns, branches; iFrame|]; done.
    Qed.

    Lemma branch_node_list_lengths : forall ns ts,
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
         end) ns ts ∗ ⌜length ns = length ts⌝.
    Proof.
      iIntros (? ?).
      iInduction ts as [|thd trest] "IH'" forall (ns);
        destruct ns as [|nhd nrest]; [done|done|done|].
      iIntros "[Hnhd Hnrest]".
      iDestruct ("IH'" with "Hnrest") as "[Hnrest %]".
      iSplitL; [iFrame|].
      cbn.
      rewrite H.
      done.
    Qed.

    Lemma branch_node_split n ns ts :
      (fix branch_node_list (ns1 : list val) (ts0 : list nary_tree) {struct ts0} : iProp :=
         match ns1 with
         | [] => match ts0 with
                | [] => True
                | _ :: _ => False
                end
         | n :: ns2 =>
             match ts0 with
             | [] => False
             | t :: ts1 => is_node n t ∗ branch_node_list ns2 ts1
             end
         end) ns ts -∗
        (fix branch_node_list (ns1 : list val) (ts0 : list nary_tree) {struct ts0} : iProp :=
           match ns1 with
           | [] => match ts0 with
                  | [] => True
                  | _ :: _ => False
                  end
           | n :: ns2 =>
               match ts0 with
               | [] => False
               | t :: ts1 => is_node n t ∗ branch_node_list ns2 ts1
               end
           end) (take n ns) (take n ts) ∗
        (fix branch_node_list (ns1 : list val) (ts0 : list nary_tree) {struct ts0} : iProp :=
           match ns1 with
           | [] => match ts0 with
                  | [] => True
                  | _ :: _ => False
                  end
           | n :: ns2 =>
               match ts0 with
               | [] => False
               | t :: ts1 => is_node n t ∗ branch_node_list ns2 ts1
               end
           end) (drop n ns) (drop n ts).
    Proof.
      iIntros "Hns".
      iInduction n as [] "IH" forall (ts ns); [repeat rewrite take_0; repeat rewrite drop_0; iFrame|].
      destruct ns as [|nhd nrest]; destruct ts as [|thd trest]; [repeat rewrite take_nil;done|done|done|].
      cbn; fold (@take val) (@take nary_tree) (@drop val) (@drop nary_tree).
      iDestruct "Hns" as "[Hnhd Hnrest]".
      iFrame.
      iApply "IH"; done.
    Qed.

    Lemma branch_node_snoc xs xlast ys ylast :
      ((fix branch_node_list (ns1 : list val) (ts0 : list nary_tree) {struct ts0} :
         iProp :=
          match ns1 with
          | [] => match ts0 with
                 | [] => True%I
                 | _ :: _ => False%I
                 end
          | n :: ns2 =>
              match ts0 with
              | [] => False%I
              | t :: ts1 => (is_node n t ∗ branch_node_list ns2 ts1)%I
              end
          end) (xs ++ [xlast]) (ys ++ [ylast]) -∗
         (fix branch_node_list (ns1 : list val) (ts0 : list nary_tree) {struct ts0} :
           iProp :=
            match ns1 with
            | [] => match ts0 with
                   | [] => True%I
                   | _ :: _ => False%I
                   end
            | n :: ns2 =>
                match ts0 with
                | [] => False%I
                | t :: ts1 => (is_node n t ∗ branch_node_list ns2 ts1)%I
                end
            end) xs ys ∗ is_node xlast ylast).
    Proof.
      iIntros "H".
      iInduction ys as [|y ys] "IH" forall (xs);
        destruct xs as [|x xs].
      - iDestruct "H" as "[? _]"; iFrame.
      - destruct xs; cbn; iDestruct "H" as "[_ ?]"; done.
      - destruct ys; cbn; iDestruct "H" as "[_ ?]"; done.
      - iDestruct "H" as "[Hxy H]".
        iEval (fold (@app val); fold (@app nary_tree)) in "H".
        iFrame.
        iApply ("IH" with "H").
    Qed.

    Lemma branch_node_snoc' xs xlast ys ylast :
      (fix branch_node_list (ns1 : list val) (ts0 : list nary_tree) {struct ts0} :
        iProp :=
         match ns1 with
         | [] => match ts0 with
                | [] => True%I
                | _ :: _ => False%I
                end
         | n :: ns2 =>
             match ts0 with
             | [] => False%I
             | t :: ts1 => (is_node n t ∗ branch_node_list ns2 ts1)%I
             end
         end) xs ys ∗ is_node xlast ylast -∗
        (fix branch_node_list (ns1 : list val) (ts0 : list nary_tree) {struct ts0} :
          iProp :=
           match ns1 with
           | [] => match ts0 with
                  | [] => True%I
                  | _ :: _ => False%I
                  end
           | n :: ns2 =>
               match ts0 with
               | [] => False%I
               | t :: ts1 => (is_node n t ∗ branch_node_list ns2 ts1)%I
               end
           end) (xs ++ [xlast]) (ys ++ [ylast]).
    Proof.
      iIntros "H".
      iInduction ys as [|y ys] "IH" forall (xs);
        destruct xs as [|x xs].
      - iDestruct "H" as "[_ ?]"; iFrame.
      - destruct xs; cbn; iDestruct "H" as "[? _]"; done.
      - destruct ys; cbn; iDestruct "H" as "[? _]"; done.
      - iDestruct "H" as "[[Hxy H] Hxylast]".
        iFrame.
        iApply ("IH" with "[$]").
    Qed.

    Lemma ge_1_S n :
      1 <= n -> exists m, n = S m.
    Proof.
      clear bpos.
      intros.
      destruct n; [lia|exists n; done].
    Qed.

    Lemma cons_snoc {A} (l : list A) head tail : l = head :: tail -> exists init last, l = init ++ [last].
    Proof.
      destruct (destruct_list_back l) as [[last [init ?]]|];
        intro; subst;
        [exists init, last|]; done.
    Qed.

    Lemma Z2N_b2 : Z.div b 2 = Z.of_nat (b / 2).
    Proof. symmetry; apply Znat.Nat2Z.inj_div. Qed.

    Lemma insert_nary_tree_spec_proof (t : nary_tree) (t_wf : nary_tree_wf_no_len t) (v : val) (target : tval) :
      {{{ is_node v t }}}
        insert_nary_tree b (v, #target)%V
        {{{ r, RET (r.1, r.2);
            is_node r.1 (insert_nary_tree_spec b target t).1 ∗
              ((∃ (t2 : nary_tree),
                   ⌜(insert_nary_tree_spec b target t).2 = Some t2⌝ ∗
                     ∃ (r2 : val), ⌜r.2 = SOMEV r2⌝ ∗ is_node r2 t2) ∨
                 (⌜(insert_nary_tree_spec b target t).2 = None⌝ ∗ ⌜r.2 = NONEV⌝))
        }}}.
    Proof using bpos beven.
      iIntros (Φ) "Hv HPost".

      iInduction t as [(low & high)|(low & high) ts] "IH" using nary_tree_ind' forall (Φ v).
      - iPoseProof (tree_leaf_token_leaf with "Hv") as (?) "->".
        iDestruct "Hv" as (? ?) "(% & Hptr & Hlhd)".
        assert (x = #ptr) by (unfold token_leaf_v in H; congruence); subst; clear H.
        wp_rec; wp_load; wp_load; wp_pures; wp_bind (insert_list _).
        iApply (insert_list_spec_proof with "Hlhd").
        iNext.
        iIntros (?) "Hr".
        wp_pures; wp_bind (length_list _).
        iApply (length_list_spec_proof with "Hr").
        iNext.
        iIntros (?) "[% Hr]".
        wp_pure.
        destruct (bool_decide (Z.lt b r0)) eqn:?.
        + wp_pures.
          rewrite Z2N_b2.
          wp_bind (split_list _);
            iApply (split_list_spec_proof with "Hr");
            iNext;
            iIntros (?) "[Hr1 Hr2]".
          wp_pures;
            wp_bind (head_list _);
            iApply (head_list_spec_proof with "Hr1");
            iNext;
            iIntros (?) "[-> Hr1]".
          wp_pures;
            wp_bind (last_list _);
            iApply (last_list_spec_proof with "Hr1");
            iNext;
            iIntros (?) "[-> Hr1]".
          wp_pures;
            wp_bind (head_list _);
            iApply (head_list_spec_proof with "Hr2");
            iNext;
            iIntros (?) "[-> Hr2]".
          wp_pures;
            wp_bind (last_list _);
            iApply (last_list_spec_proof with "Hr2");
            iNext;
            iIntros (?) "[-> Hr2]".

          wp_alloc ptr' as "Hptr'"; wp_store; wp_pures.
          iApply ("HPost" $! (InjLV #ptr, InjRV (InjLV #ptr'))).
          rewrite map_length in H; subst r0.
          rewrite bool_decide_eq_true in Heqb0;
            apply Z.ltb_lt in Heqb0.
          repeat rewrite firstn_map;
            repeat rewrite skipn_map;
            rewrite (hd_map_comm _ _ low _ eq_refl);
            rewrite (Listlast_map_comm _ _ high _ eq_refl).
          iSplitL "Hptr Hr1".
          { cbn; rewrite Heqb0.
            iExists ptr, r1.1.
            iSplitR; [done|].
            iSplitL "Hptr"; done. }
          iLeft.
          remember (insert_list_spec target vals) as new_vals.
          iExists (leaf (hd low (drop (b/2) new_vals), List.last (drop (b/2) new_vals) high) (drop (b/2) new_vals)).
          iSplitR; [cbn; rewrite <- Heqnew_vals; rewrite Heqb0; done|].
          iExists (InjLV #ptr').
          iSplitR; [done|].
          iExists ptr', r1.2.
          repeat rewrite firstn_map;
            repeat rewrite skipn_map;
            rewrite (hd_map_comm _ _ low _ eq_refl);
            rewrite (Listlast_map_comm _ _ high _ eq_refl).
          iFrame; done.

        + wp_pures;
            wp_bind (head_list _);
            iApply (head_list_spec_proof with "Hr");
            iNext;
            iIntros (?) "[-> Hr]".
          wp_pures;
            wp_bind (last_list _);
            iApply (last_list_spec_proof with "Hr");
            iNext;
            iIntros (?) "[-> Hr]".

          wp_store; wp_pures.
          iApply ("HPost" $! (token_leaf_v #ptr, NONEV)).
          apply bool_decide_eq_false_1 in Heqb0;
              assert (Z.le r0 b) by lia;
              apply Z.leb_le in H0;
              rewrite Z.leb_antisym in H0;
              symmetry in H0;
              apply negb_sym in H0;
              cbn in H0.
          rewrite map_length in H; subst r0.
          iSplitL.
          { unfold insert_nary_tree_spec.
            rewrite H0.
            iExists ptr, r.
            rewrite (hd_map_comm _ _ low _ eq_refl);
              rewrite (Listlast_map_comm _ _ high _ eq_refl).
            iFrame; done. }
          iRight.
          cbn.
          rewrite H0.
          done.

      - iPoseProof (tree_node_token_branch with "Hv") as (?) "->".
        iDestruct "Hv" as (ptr lhd ns) "(% & Hptr & Hlhd & Hns)"; fold is_node.
        assert (x = #ptr) by (unfold token_branch_v in H; congruence); subst.
        wp_rec; wp_load; wp_proj; wp_let; wp_pure; wp_pure.
        iEval (cbn) in "HPost".

        wp_bind ((rec: "insert_node_list" "arg" := _) (lhd, #target))%V.
        iAssert (
            ∀ Φ',
              is_list lhd ns ∗
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
                (∀ r : val,
                    (∃ ns,
                        is_list r ns ∗
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
                             end) ns
                          ((fix insert_aux (l : list nary_tree) : list nary_tree :=
                              match l with
                              | [] => []
                              | [t] =>
                                  let (new_t1, new_t2) := insert_nary_tree_spec b target t in
                                  match new_t2 with
                                  | Some new_t2' => [new_t1; new_t2']
                                  | None => [new_t1]
                                  end
                              | t :: (_ :: _) as ts0 =>
                                  let (low0, high0) := nary_tree_interval t in
                                  if (target <=? high0)%Z
                                  then
                                    let (new_t1, new_t2) := insert_nary_tree_spec b target t in
                                    match new_t2 with
                                    | Some new_t2' => new_t1 :: new_t2' :: ts0
                                    | None => new_t1 :: ts0
                                    end
                                  else t :: insert_aux ts0
                              end) ts)) -∗ Φ' r) -∗
                WP (rec: "insert_node_list" "arg" :=
                 let: "p" := Fst "arg" in
                 let: "target" := Snd "arg" in
                 match: "p" with
                   NONE =>
                     NONE
                 | SOME "l" =>
                     match: Snd !"l" with
                       NONE =>
                         let: "newt" := insert_nary_tree b (Fst !"l", "target") in
                         match: Snd "newt" with
                           NONE => "l" <- (Fst "newt", NONE)
                         | SOME "newt2" =>
                             let: "l'" := ref ("newt2", NONE) in
                             "l" <- (Fst "newt", SOME "l'")
                         end
                     | SOME "_" =>
                         let: "thd" := Fst !"l" in
                         let: "interval" := interval_nary_tree "thd" in
                         let: "low" := Fst "interval" in
                         let: "high" := Snd "interval" in
                         (if: BinOp LeOp "target" "high"
                          then let: "newt" := insert_nary_tree b ("thd", "target") in
                               match: Snd "newt" with
                                 NONE => "l" <- (Fst "newt", Snd !"l")
                               | SOME "newt2" =>
                                   let: "l'" := ref ("newt2", Snd !"l") in
                                   "l" <- (Fst "newt", SOME "l'")
                               end
                          else let: "newl" := "insert_node_list" (Snd !"l", "target") in
                               "l" <- ("thd", "newl"))
                     end ;; SOME "l"
                 end)%V (lhd, #target)%V
                {{ v, Φ' v}}
          )%I as "IH'".
        { iIntros (Φ') "[Hlhd Hns] HPost".
          inversion_clear t_wf
            as [| ? ? ? ? _ _ trees_wf _];
            subst intervals.

          iInduction ts as [|thd trest] "IH'" forall (Φ' ns lhd);
            destruct ns as [|nhd nrest]; [|done|done|].
          - iDestruct "Hlhd" as "->".
            wp_pures.
            iApply "HPost".
            iExists [].
            done.

          - iDestruct "Hns" as "[Hnhd Hnrest]".
            destruct trest as [|tsnd]; destruct nrest as [|nsnd]; [|done|done|];
              iEval (rewrite big_opL_cons) in "IH";
              iDestruct "IH" as "[IHthd IHtrest]";
              apply Forall_cons in trees_wf;
              destruct trees_wf as [thd_wf trest_wf].
            + iDestruct "Hlhd" as (l0 ?) "(-> & Hl0 & ->)".
              wp_load; wp_load; wp_pures; wp_bind (insert_nary_tree b _).
              iApply ("IHthd" $! thd_wf with "Hnhd").
              iNext.
              iIntros (?) "[Hr1 Hr2]".
              iDestruct "Hr2" as "[(% & % & % & -> & Hr2) | (% & ->)]";
                destruct (insert_nary_tree_spec b target thd) as [new_t1 new_t2];
                cbn in H0; subst.
              * wp_alloc lr2 as "Hlr2"; wp_store; wp_pure.
                iApply "HPost".
                iExists (r.1 :: r2 :: []).
                iSplitL "Hl0 Hlr2";
                  [iExists l0, (SOMEV #lr2); iFrame; iSplitR; [done|]; iExists lr2, NONEV; iFrame; done|].
                iFrame; done.
              * wp_store; wp_pure.
                iApply "HPost".
                iExists [r.1].
                iSplitL "Hl0"; [iExists l0, NONEV; iFrame; done|].
                iFrame; done.

            + iDestruct "Hlhd" as (l1 ?) "(-> & Hl1 & Hhd')".
              iDestruct "Hhd'" as (l2 ?) "(-> & Hl2 & Hhd')".
              wp_load; wp_load; wp_pures.
              wp_bind (interval_nary_tree _);
                iApply (interval_nary_tree_spec_proof with "Hnhd");
                iNext;
                iIntros ((low', high')) "[Hnhd %]";
                destruct H0.

              wp_pures.
              destruct (bool_decide (Z.le target high')) eqn:?; wp_pures.
              ++ wp_bind (insert_nary_tree b _);
                   iApply ("IHthd" $! thd_wf with "Hnhd");
                   iNext;
                   iIntros (?) "[Hr1 Hr2]".
                 wp_pures.
                 apply bool_decide_eq_true_1 in Heqb0;
                   apply Z.leb_le in Heqb0;
                   rewrite Heqb0.

                 iDestruct "Hr2" as "[(% & % & % & -> & Hr2) | (% & ->)]";
                   destruct (insert_nary_tree_spec b target thd) as [new_t1 new_t2];
                   cbn in H0; subst.
                 ** wp_load; wp_alloc l3 as "Hl3"; wp_store; wp_pure.
                    iApply "HPost".
                    iExists (r.1 :: r2 :: nsnd :: nrest).
                    iSplitL "Hl1 Hl3 Hl2 Hhd'";
                      [iExists l1, (SOMEV #l3); iFrame; iSplitR; [done|]; iExists l3, (SOMEV #l2); iFrame; iSplitR; [done|]; iExists l2, hd'0; iFrame; done|].
                    iFrame; done.
                 ** wp_load; wp_store; wp_pure.
                    iApply "HPost".
                    iExists (r.1 :: nsnd :: nrest).
                    iSplitL "Hl1 Hl2 Hhd'";
                      [iExists l1, (SOMEV #l2); iFrame; iSplitR; [done|]; iExists l2, hd'0; iFrame; done|].
                    iFrame; done.

              ++ wp_load; wp_pure; wp_pure.
                 wp_bind ((rec: "insert_node_list" "arg" := _) (SOMEV #l2, #target))%V.
                 iApply ("IH'" $! trest_wf _ (nsnd :: nrest) (SOMEV #l2) with "[] [Hl2 Hhd'] [Hnrest]"); try done.
                 { iExists l2, hd'0; iFrame; done. }
                 iIntros (?) "[% [Hr Hns]]".
                 wp_store; wp_pure.
                 iApply "HPost".
                 apply bool_decide_eq_false_1 in Heqb0;
                   assert (Z.lt high' target) by lia;
                   apply Z.ltb_lt in H0;
                   rewrite Z.ltb_antisym in H0;
                   symmetry in H0;
                   apply negb_sym in H0;
                   cbn in H0;
                   rewrite H0.
                 iExists (nhd :: ns).
                 iFrame.
                 iExists l1, r; iFrame; done. }

        iClear "IH".
        iApply ("IH'" with "[Hlhd Hns]"); iClear "IH'".
        { iFrame. }
        iIntros (r) "Hr".
        iDestruct "Hr" as (?) "[Hr Hns0]".

        wp_load; wp_pures; wp_bind (length_list _).
        iApply (length_list_spec_proof with "Hr").
        iNext.
        iIntros (?) "[% Hr]".
        wp_pure.
        remember (fix branch_node_list (ns1 : list val) (ts0 : list nary_tree) {struct ts0} : iProp :=
                 match ns1 with
                 | [] => match ts0 with
                         | [] => True
                         | _ :: _ => False
                         end
                 | n :: ns2 =>
                     match ts0 with
                     | [] => False
                     | t :: ts1 => is_node n t ∗ branch_node_list ns2 ts1
                     end
                 end)%I as branch_node_list.
        remember ((fix insert_aux (l : list nary_tree) : list nary_tree :=
                     match l with
                     | [] => []
                     | [t] =>
                         let (new_t1, new_t2) := insert_nary_tree_spec b target t in
                         match new_t2 with
                         | Some new_t2' => [new_t1; new_t2']
                         | None => [new_t1]
                         end
                     | t :: (_ :: _) as ts0 =>
                         let (low0, high0) := nary_tree_interval t in
                         if (target <=? high0)%Z
                         then
                           let (new_t1, new_t2) := insert_nary_tree_spec b target t in
                           match new_t2 with
                           | Some new_t2' => new_t1 :: new_t2' :: ts0
                           | None => new_t1 :: ts0
                           end
                         else t :: insert_aux ts0
                     end) ts) as new_ts.
        destruct (bool_decide (Z.lt b r0)) eqn:?.
        + wp_pures; wp_bind (split_list _).
          rewrite Z2N_b2.
          iApply (split_list_spec_proof with "Hr").
          iNext.
          iIntros (?) "[Hr1 Hr2]".

          iPoseProof ((branch_node_list_lengths ns0 new_ts) with "[Hns0]") as "[Hns0 %Heqlengths]";
            [rewrite Heqbranch_node_list; done|].
          iPoseProof ((branch_node_split (b/2)) with "Hns0") as "[Hnstake Hnsdrop]";
            iEval (rewrite <- Heqbranch_node_list) in "Hnstake Hnsdrop".
          assert (b < length new_ts) as bltlengthnew_ts by (rewrite bool_decide_eq_true in Heqb0; lia);
            specialize (take_b2_cons b beven bpos new_ts bltlengthnew_ts) as [tthd [ttrest take_new_ts_cons]];
            specialize (take_b2_snoc b beven bpos new_ts bltlengthnew_ts) as [ttlast [ttrest' take_new_ts_snoc]];
            specialize (drop_b2_cons b beven bpos new_ts bltlengthnew_ts) as [dthd [dtrest drop_new_ts_cons]];
            specialize (drop_b2_snoc b bpos new_ts bltlengthnew_ts) as [dtlast [dtrest' drop_new_ts_snoc]];
            clear bltlengthnew_ts.
          assert (b < length ns0) as bltlengthns0 by (rewrite bool_decide_eq_true in Heqb0; lia);
            specialize (take_b2_cons b beven bpos ns0 bltlengthns0) as [tnhd [tnrest take_ns0_cons]];
            specialize (take_b2_snoc b beven bpos ns0 bltlengthns0) as [tnlast [tnrest' take_ns0_snoc]];
            specialize (drop_b2_cons b beven bpos ns0 bltlengthns0) as [dnhd [dnrest drop_ns0_cons]];
            specialize (drop_b2_snoc b bpos ns0 bltlengthns0) as [dnlast [dnrest' drop_ns0_snoc]].

          wp_pures;
            wp_bind (headopt_list _);
            iApply (headopt_list_spec_proof with "Hr1");
            iNext;
            iIntros (?) "[-> Hr1]";
            rewrite take_new_ts_cons;
            rewrite take_ns0_cons;
            wp_pures;
            wp_bind (interval_nary_tree _);
            iEval (rewrite Heqbranch_node_list) in "Hnstake";
            iDestruct "Hnstake" as "[Htnhd Htnsrest]";
            iApply (interval_nary_tree_spec_proof with "Htnhd");
            iNext;
            iIntros ((thdlow, thdhigh)) "[Htnhd %]";
            iCombine "Htnhd Htnsrest" as "Hnstake";
            assert (is_node tnhd tthd ∗ branch_node_list tnrest ttrest -∗
                      branch_node_list (tnhd :: tnrest) (tthd :: ttrest)) as Heqnstake
            by (rewrite Heqbranch_node_list; done);
            iPoseProof (Heqnstake with "[Hnstake]") as "Hnstake"; [rewrite Heqbranch_node_list; iFrame|];
            rewrite <- take_new_ts_cons;
            rewrite <- take_ns0_cons.

          wp_pures;
            wp_bind (lastopt_list _);
            iApply (lastopt_list_spec_proof with "Hr1");
            iNext;
            iIntros (?) "[-> Hr1]";
            rewrite take_new_ts_snoc;
            rewrite take_ns0_snoc;
            wp_pures;
            iEval (rewrite last_snoc);
            wp_pures;
            wp_bind (interval_nary_tree _);
            iEval (rewrite Heqbranch_node_list) in "Hnstake";
            iDestruct (branch_node_snoc with "Hnstake") as "[Htnsrest Htnlast]";
            iApply (interval_nary_tree_spec_proof with "Htnlast");
            iNext;
            iIntros ((tlastlow, tlasthigh)) "[Htnlast %]";
            iCombine "Htnsrest Htnlast" as "Hnstake";
            iPoseProof (branch_node_snoc' with "[Hnstake]") as "Hnstake"; [iFrame|];
            iEval (rewrite <- Heqbranch_node_list) in "Hnstake";
            rewrite <- take_new_ts_snoc;
            rewrite <- take_ns0_snoc.

          wp_pures;
            wp_bind (headopt_list _);
            iApply (headopt_list_spec_proof with "Hr2");
            iNext;
            iIntros (?) "[-> Hr2]";
            rewrite drop_new_ts_cons;
            rewrite drop_ns0_cons;
            wp_pures;
            wp_bind (interval_nary_tree _);
            iEval (rewrite Heqbranch_node_list) in "Hnsdrop";
            iDestruct "Hnsdrop" as "[Hdnhd Hdnsrest]";
            iApply (interval_nary_tree_spec_proof with "Hdnhd");
            iNext;
            iIntros ((dthdlow, dthdhigh)) "[Hdnhd %]";
            iCombine "Hdnhd Hdnsrest" as "Hnsdrop";
            assert (is_node dnhd dthd ∗ branch_node_list dnrest dtrest -∗
                      branch_node_list (dnhd :: dnrest) (dthd :: dtrest)) as Heqnsdrop
              by (rewrite Heqbranch_node_list; done);
            iPoseProof (Heqnsdrop with "[Hnsdrop]") as "Hnsdrop";
              [rewrite Heqbranch_node_list; iFrame|];
            rewrite <- drop_new_ts_cons;
            rewrite <- drop_ns0_cons.

          wp_pures;
            wp_bind (lastopt_list _);
            iApply (lastopt_list_spec_proof with "Hr2");
            iNext;
            iIntros (?) "[-> Hr2]";
            rewrite drop_new_ts_snoc;
            rewrite drop_ns0_snoc;
            wp_pures;
            iEval (rewrite last_snoc);
            wp_pures;
            wp_bind (interval_nary_tree _);
            iEval (rewrite Heqbranch_node_list) in "Hnsdrop";
            iDestruct (branch_node_snoc with "Hnsdrop") as "[Hnsrest Hnlast]";
            iApply (interval_nary_tree_spec_proof with "Hnlast");
            iNext;
            iIntros ((dtlastlow, dtlasthigh)) "[Hnlast %]";
            iCombine "Hnsrest Hnlast" as "Hnsdrop";
            iPoseProof (branch_node_snoc' with "Hnsdrop") as "Hnsdrop";
            rewrite <- drop_new_ts_snoc;
            rewrite <- drop_ns0_snoc.

          wp_pures; wp_alloc ptr' as "Hptr'"; wp_store; wp_pures.
          iApply ("HPost" $! (token_branch_v #ptr, token_branch_v (SOMEV #ptr'))).
          subst r0;
            rewrite bool_decide_eq_true in Heqb0;
            apply Z.ltb_lt in Heqb0;
            rewrite <- Heqlengths, Heqb0.

          iSplitL "Hptr Hr1 Hnstake".
          { iExists ptr, r1.1, (take (b/2) ns0).
            fold is_node; rewrite <- Heqbranch_node_list.
            repeat rewrite head_map_comm last_map_comm.
            rewrite take_new_ts_cons;
              rewrite take_ns0_cons;
              iEval (rewrite head_cons);
              rewrite <- take_new_ts_cons;
              rewrite <- take_ns0_cons.
            rewrite take_new_ts_snoc;
              rewrite take_ns0_snoc;
              iEval (rewrite last_snoc);
              rewrite <- take_new_ts_snoc;
              rewrite <- take_ns0_snoc.
            destruct H1, H2.
            iFrame; done. }

          iLeft.
          repeat rewrite head_map_comm last_map_comm.
          rewrite <- Heqbranch_node_list.
          rewrite drop_new_ts_cons;
            rewrite drop_ns0_cons;
            iEval (rewrite head_cons);
            rewrite <- drop_new_ts_cons;
            rewrite <- drop_ns0_cons.
          rewrite drop_new_ts_snoc;
            rewrite drop_ns0_snoc;
            iEval (rewrite last_snoc);
            rewrite <- drop_new_ts_snoc;
            rewrite <- drop_ns0_snoc.

          iExists (node (fst (nary_tree_interval dthd), snd (nary_tree_interval dtlast)) (drop (b/2) new_ts)).
          iSplitR; [done|].
          iExists (token_branch_v #ptr').
          iSplitR; [done|].
          iExists ptr', r1.2, (drop (b/2) ns0).
          fold is_node.
          rewrite <- Heqbranch_node_list.
          destruct H3, H4.
          iFrame; done.

        + iPoseProof ((branch_node_list_lengths ns0 new_ts) with "[Hns0]") as "[Hns %Heqlengths]";
            [rewrite Heqbranch_node_list; done|];
            rewrite <- Heqbranch_node_list.

          destruct new_ts as [|thd trest];
            destruct ns0 as [|nhd nrest];
            [|rewrite Heqbranch_node_list; done|rewrite Heqbranch_node_list; done|].
          * wp_pures;
              wp_bind (headopt_list _);
              iApply (headopt_list_spec_proof with "Hr");
              iNext;
              iIntros (?) "[-> Hr]";
              iEval (rewrite head_nil).

            wp_pures;
              wp_bind (lastopt_list _);
              iApply (lastopt_list_spec_proof with "Hr");
              iNext;
              iIntros (?) "[-> Hr]";
              iEval (rewrite last_nil).

            wp_store; wp_pures.

            iApply ("HPost" $! (token_branch_v #ptr, NONEV)).
            apply bool_decide_eq_false_1 in Heqb0;
              assert (Z.le r0 b) by lia;
              apply Z.leb_le in H1;
              rewrite Z.leb_antisym in H1;
              symmetry in H1;
              apply negb_sym in H1;
              cbn in H1;
              subst r0;
              rewrite H1.

            iSplitL; [iExists ptr, r, []; iFrame; done|].
            iRight.
            done.

          * wp_pures;
              wp_bind (headopt_list _);
              iApply (headopt_list_spec_proof with "Hr");
              iNext;
              iIntros (?) "[-> Hr]";
              iEval (rewrite head_cons);
              wp_pures;
              wp_bind (interval_nary_tree _);
              iEval (rewrite Heqbranch_node_list) in "Hns";
              iDestruct "Hns" as "[Hnhd Hnsrest]";
              iApply (interval_nary_tree_spec_proof with "Hnhd");
              iNext;
              iIntros ((hdlow, hdhigh)) "[Hnhd %]";
              iCombine "Hnhd Hnsrest" as "Hns";
              assert (is_node nhd thd ∗ branch_node_list nrest trest -∗
                        branch_node_list (nhd :: nrest) (thd :: trest)) as Heqnbranches
                by (rewrite Heqbranch_node_list; done);
              iPoseProof (Heqnbranches with "[Hns]") as "Hns";
              [rewrite Heqbranch_node_list; iFrame|].

            destruct (cons_snoc (thd :: trest) _ _ eq_refl) as [tlast [tinit Heqts]].
            destruct (cons_snoc (nhd :: nrest) _ _ eq_refl) as [nlast [ninit Heqns]].

            rewrite Heqts Heqns;
              wp_pures;
              wp_bind (lastopt_list _);
              iApply (lastopt_list_spec_proof with "Hr");
              iNext;
              iIntros (?) "[-> Hr]";
              iEval (rewrite last_snoc);
              wp_pures;
              wp_bind (interval_nary_tree _);
              iEval (rewrite Heqbranch_node_list) in "Hns";
              iDestruct (branch_node_snoc with "Hns") as "[Hnsrest Hnlast]";
              iApply (interval_nary_tree_spec_proof with "Hnlast");
              iNext;
              iIntros ((lastlow, lasthigh)) "[Hnlast %]";
              iCombine "Hnsrest Hnlast" as "Hns";
              iPoseProof (branch_node_snoc' with "Hns") as "Hns";
              rewrite <- Heqts, <- Heqns.

            wp_store; wp_pures.
            iApply ("HPost" $! (token_branch_v #ptr, NONEV)).
            apply bool_decide_eq_false_1 in Heqb0;
              assert (Z.le r0 b) by lia;
              apply Z.leb_le in H3;
              rewrite Z.leb_antisym in H3;
              symmetry in H3;
              apply negb_sym in H3;
              cbn in H3;
              rewrite <- Heqlengths;
              subst r0;
              rewrite H3.

            repeat rewrite head_map_comm last_map_comm;
              rewrite head_cons;
              rewrite Heqts;
              rewrite last_snoc;
              rewrite <- Heqts.

            destruct H1, H2.
            iSplitL; [iExists ptr, r, (nhd :: nrest); iFrame; done|].
            iRight; done.
    Qed.

    Definition is_bplus_tree_no_wf (v : val) (t : tree_spec) :=
      match t with
      | root_leaf interval l => leaf_node v interval l
      | root_node interval ts => is_node v (node interval ts)
      end.

    Lemma insert_bplus_tree_spec_proof_no_wf (t : tree_spec) (t_wf : tree_spec_wf b t) (v : val) (target : tval) :
      {{{ is_bplus_tree b v t t_wf }}}
        insert_bplus_tree b (v, #target)%V
        {{{ r, RET r; is_bplus_tree_no_wf r (insert_bplus_tree_spec b target t) }}}.
    Proof using bpos beven.
      iIntros (Φ) "Hv HPost".

      destruct t as [[low high] | [low high] ts].
      - iPoseProof ((tree_root_leaf_token_leaf b _ _ _ _ t_wf) with "Hv") as (?) "->".
        iDestruct "Hv" as (? ?) "(% & Hptr & Hlhd)".
        assert (x = #ptr) by (unfold token_leaf_v in H; congruence); subst; clear H.
        wp_rec; wp_load; wp_load; wp_pures; wp_bind (insert_list _).
        iApply (insert_list_spec_proof with "Hlhd").
        iNext.
        iIntros (?) "Hr".
        wp_pures; wp_bind (length_list _).
        iApply (length_list_spec_proof with "Hr").
        iNext.
        iIntros (?) "[% Hr]".
        wp_pure.
        destruct (bool_decide (Z.le b r0)) eqn:?.
        + wp_pures.
          rewrite Z2N_b2.
          wp_bind (split_list _);
            iApply (split_list_spec_proof with "Hr");
            iNext;
            iIntros (?) "[Hr1 Hr2]".
          wp_pures;
            wp_bind (head_list _);
            iApply (head_list_spec_proof with "Hr1");
            iNext;
            iIntros (?) "[-> Hr1]".
          wp_pures;
            wp_bind (last_list _);
            iApply (last_list_spec_proof with "Hr1");
            iNext;
            iIntros (?) "[-> Hr1]".
          wp_pures;
            wp_bind (head_list _);
            iApply (head_list_spec_proof with "Hr2");
            iNext;
            iIntros (?) "[-> Hr2]".
          wp_pures;
            wp_bind (last_list _);
            iApply (last_list_spec_proof with "Hr2");
            iNext;
            iIntros (?) "[-> Hr2]".

          wp_alloc newleaf as "Hnewleaf";
            wp_alloc newlmid as "Hnewlmid";
            wp_alloc newlhd as "Hnewlhd";
            wp_alloc newroot as "Hnewroot";
            wp_store;
            wp_pures.
          iApply "HPost".
          iEval (cbn).
          rewrite map_length in H; subst r0.
          rewrite bool_decide_eq_true in Heqb0;
            apply Z.leb_le in Heqb0.
          iEval (rewrite Heqb0).
          repeat rewrite firstn_map;
            repeat rewrite skipn_map;
            repeat rewrite (hd_map_comm _ _ low _ eq_refl);
            repeat rewrite (Listlast_map_comm _ _ high _ eq_refl).

          iExists newroot, (SOMEV #newlhd), (token_leaf_v #ptr :: token_leaf_v #newleaf :: []).
          iFrame.
          iSplitR; [done|].
          iSplitL "Hnewlhd Hnewlmid";
            [ iExists newlhd, (SOMEV #newlmid);
              iFrame; iSplitR; [done|];
              iExists newlmid, NONEV;
              iFrame; done |].
          iSplitL "Hptr Hr1";
          [ iExists ptr, r1.1;
            iSplitR; [done|];
            iFrame; done |].
          iSplitL; [|done].
          iExists newleaf, r1.2;
            iSplitR; [done|];
            iFrame; done.

        + wp_pures;
            wp_bind (head_list _);
            iApply (head_list_spec_proof with "Hr");
            iNext;
            iIntros (?) "[-> Hr]".
          wp_pures;
            wp_bind (last_list _);
            iApply (last_list_spec_proof with "Hr");
            iNext;
            iIntros (?) "[-> Hr]".

          wp_store; wp_pures.
          iApply "HPost".
          unfold is_bplus_tree_no_wf, insert_bplus_tree_spec.
          apply bool_decide_eq_false_1 in Heqb0;
            assert (Z.lt r0 b) by lia;
            apply Z.ltb_lt in H0;
            rewrite Z.ltb_antisym in H0;
            symmetry in H0;
            apply negb_sym in H0;
            cbn in H0;
            rewrite map_length in H;
            subst r0;
            rewrite H0.
          iExists ptr, r;
            rewrite (hd_map_comm _ _ low _ eq_refl);
            rewrite (Listlast_map_comm _ _ high _ eq_refl);
            iFrame; done.

      - iPoseProof (tree_node_token_branch with "Hv") as (?) "->".
        iDestruct "Hv" as (ptr lhd ns) "(-> & Hptr & Hlhd & Hns)"; fold is_node.
        wp_rec; wp_load; wp_proj; wp_let; wp_pure; wp_pure.
        iEval (cbn) in "HPost".

        wp_bind ((rec: "insert_node_list" "arg" := _) (lhd, #target))%V.
        iAssert (
            ∀ Φ',
              is_list lhd ns ∗
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
                (∀ r : val,
                    (∃ ns,
                        is_list r ns ∗
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
                             end) ns
                          ((fix insert_aux (l : list nary_tree) : list nary_tree :=
                              match l with
                              | [] => []
                              | [t] =>
                                  let (new_t1, new_t2) := insert_nary_tree_spec b target t in
                                  match new_t2 with
                                  | Some new_t2' => [new_t1; new_t2']
                                  | None => [new_t1]
                                  end
                              | t :: (_ :: _) as ts0 =>
                                  let (low0, high0) := nary_tree_interval t in
                                  if (target <=? high0)%Z
                                  then
                                    let (new_t1, new_t2) := insert_nary_tree_spec b target t in
                                    match new_t2 with
                                    | Some new_t2' => new_t1 :: new_t2' :: ts0
                                    | None => new_t1 :: ts0
                                    end
                                  else t :: insert_aux ts0
                              end) ts)) -∗ Φ' r) -∗
                WP (rec: "insert_node_list" "arg" :=
                 let: "p" := Fst "arg" in
                 let: "target" := Snd "arg" in
                 match: "p" with
                   NONE =>
                     NONE
                 | SOME "l" =>
                     match: Snd !"l" with
                       NONE =>
                         let: "newt" := insert_nary_tree b (Fst !"l", "target") in
                         match: Snd "newt" with
                           NONE => "l" <- (Fst "newt", NONE)
                         | SOME "newt2" =>
                             let: "l'" := ref ("newt2", NONE) in
                             "l" <- (Fst "newt", SOME "l'")
                         end
                     | SOME "_" =>
                         let: "thd" := Fst !"l" in
                         let: "interval" := interval_nary_tree "thd" in
                         let: "low" := Fst "interval" in
                         let: "high" := Snd "interval" in
                         (if: BinOp LeOp "target" "high"
                          then let: "newt" := insert_nary_tree b ("thd", "target") in
                               match: Snd "newt" with
                                 NONE => "l" <- (Fst "newt", Snd !"l")
                               | SOME "newt2" =>
                                   let: "l'" := ref ("newt2", Snd !"l") in
                                   "l" <- (Fst "newt", SOME "l'")
                               end
                          else let: "newl" := "insert_node_list" (Snd !"l", "target") in
                               "l" <- ("thd", "newl"))
                     end ;; SOME "l"
                 end)%V (lhd, #target)%V
                {{ v, Φ' v}}
          )%I as "Hinsert_node_list".
        { iIntros (Φ') "[Hlhd Hns] HPost".
          inversion_clear t_wf
            as [| ? ? ? ? _ _ _ trees_wf _];
            subst intervals.

          iInduction ts as [|thd trest] "IH'" forall (Φ' ns lhd);
            destruct ns as [|nhd nrest]; [|done|done|].
          - iDestruct "Hlhd" as "->".
            wp_pures.
            iApply "HPost".
            iExists [].
            done.

          - iDestruct "Hns" as "[Hnhd Hnrest]".
            destruct trest as [|tsnd]; destruct nrest as [|nsnd]; [|done|done|];
              apply Forall_cons in trees_wf;
              destruct trees_wf as [thd_wf trest_wf];
              apply nary_tree_wf_remove_len in thd_wf.
            + iDestruct "Hlhd" as (l0 ?) "(-> & Hl0 & ->)".
              wp_load; wp_load; wp_pures; wp_bind (insert_nary_tree b _).
              iApply ((insert_nary_tree_spec_proof _ thd_wf) with "Hnhd").
              iNext.
              iIntros (?) "[Hr1 Hr2]".
              iDestruct "Hr2" as "[(% & % & % & -> & Hr2) | (% & ->)]";
                destruct (insert_nary_tree_spec b target thd) as [new_t1 new_t2];
                cbn in H; subst.
              * wp_alloc lr2 as "Hlr2"; wp_store; wp_pure.
                iApply "HPost".
                iExists (r.1 :: r2 :: []).
                iSplitL "Hl0 Hlr2";
                  [iExists l0, (SOMEV #lr2); iFrame; iSplitR; [done|]; iExists lr2, NONEV; iFrame; done|].
                iFrame; done.
              * wp_store; wp_pure.
                iApply "HPost".
                iExists [r.1].
                iSplitL "Hl0"; [iExists l0, NONEV; iFrame; done|].
                iFrame; done.

            + iDestruct "Hlhd" as (l1 ?) "(-> & Hl1 & Hhd')".
              iDestruct "Hhd'" as (l2 ?) "(-> & Hl2 & Hhd')".
              wp_load; wp_load; wp_pures.
              wp_bind (interval_nary_tree _);
                iApply (interval_nary_tree_spec_proof with "Hnhd");
                iNext;
                iIntros ((low', high')) "[Hnhd %]";
                destruct H.

              wp_pures.
              destruct (bool_decide (Z.le target high')) eqn:?; wp_pures.
              ++ wp_bind (insert_nary_tree b _);
                   iApply ((insert_nary_tree_spec_proof _ thd_wf) with "Hnhd");
                   iNext;
                   iIntros (?) "[Hr1 Hr2]".
                 wp_pures.
                 apply bool_decide_eq_true_1 in Heqb0;
                   apply Z.leb_le in Heqb0;
                   rewrite Heqb0.

                 iDestruct "Hr2" as "[(% & % & % & -> & Hr2) | (% & ->)]";
                   destruct (insert_nary_tree_spec b target thd) as [new_t1 new_t2];
                   cbn in H; subst.
                 ** wp_load; wp_alloc l3 as "Hl3"; wp_store; wp_pure.
                    iApply "HPost".
                    iExists (r.1 :: r2 :: nsnd :: nrest).
                    iSplitL "Hl1 Hl3 Hl2 Hhd'";
                      [iExists l1, (SOMEV #l3); iFrame; iSplitR; [done|]; iExists l3, (SOMEV #l2); iFrame; iSplitR; [done|]; iExists l2, hd'0; iFrame; done|].
                    iFrame; done.
                 ** wp_load; wp_store; wp_pure.
                    iApply "HPost".
                    iExists (r.1 :: nsnd :: nrest).
                    iSplitL "Hl1 Hl2 Hhd'";
                      [iExists l1, (SOMEV #l2); iFrame; iSplitR; [done|]; iExists l2, hd'0; iFrame; done|].
                    iFrame; done.

              ++ wp_load; wp_pure; wp_pure.
                 wp_bind ((rec: "insert_node_list" "arg" := _) (SOMEV #l2, #target))%V.
                 iApply ("IH'" $! trest_wf _ (nsnd :: nrest) (SOMEV #l2) with "[Hl2 Hhd'] [Hnrest]"); try done.
                 { iExists l2, hd'0; iFrame; done. }
                 iIntros (?) "[% [Hr Hns]]".
                 wp_store; wp_pure.
                 iApply "HPost".
                 apply bool_decide_eq_false_1 in Heqb0;
                   assert (Z.lt high' target) by lia;
                   apply Z.ltb_lt in H;
                   rewrite Z.ltb_antisym in H;
                   symmetry in H;
                   apply negb_sym in H;
                   cbn in H;
                   rewrite H.
                 iExists (nhd :: ns).
                 iFrame.
                 iExists l1, r; iFrame; done. }
        iApply ("Hinsert_node_list" with "[Hlhd Hns]"); [iFrame|];
          iClear "Hinsert_node_list";
          iIntros (r) "Hr";
          iDestruct "Hr" as (?) "[Hr Hns0]".

        wp_load; wp_pures; wp_bind (length_list _).
        iApply (length_list_spec_proof with "Hr").
        iNext.
        iIntros (?) "[% Hr]".
        wp_pure.
        remember (fix branch_node_list (ns1 : list val) (ts0 : list nary_tree) {struct ts0} : iProp :=
                 match ns1 with
                 | [] => match ts0 with
                         | [] => True
                         | _ :: _ => False
                         end
                 | n :: ns2 =>
                     match ts0 with
                     | [] => False
                     | t :: ts1 => is_node n t ∗ branch_node_list ns2 ts1
                     end
                 end)%I as branch_node_list.
        remember ((fix insert_aux (l : list nary_tree) : list nary_tree :=
                     match l with
                     | [] => []
                     | [t] =>
                         let (new_t1, new_t2) := insert_nary_tree_spec b target t in
                         match new_t2 with
                         | Some new_t2' => [new_t1; new_t2']
                         | None => [new_t1]
                         end
                     | t :: (_ :: _) as ts0 =>
                         let (low0, high0) := nary_tree_interval t in
                         if (target <=? high0)%Z
                         then
                           let (new_t1, new_t2) := insert_nary_tree_spec b target t in
                           match new_t2 with
                           | Some new_t2' => new_t1 :: new_t2' :: ts0
                           | None => new_t1 :: ts0
                           end
                         else t :: insert_aux ts0
                     end) ts) as new_ts.
        destruct (bool_decide (Z.lt b r0)) eqn:?.
        + wp_pures; wp_bind (split_list _).
          rewrite Z2N_b2.
          iApply (split_list_spec_proof with "Hr").
          iNext.
          iIntros (?) "[Hr1 Hr2]".

          iPoseProof ((branch_node_list_lengths ns0 new_ts) with "[Hns0]") as "[Hns0 %Heqlengths]";
            [rewrite Heqbranch_node_list; done|].
          iPoseProof ((branch_node_split (b/2)) with "Hns0") as "[Hnstake Hnsdrop]";
            iEval (rewrite <- Heqbranch_node_list) in "Hnstake Hnsdrop".
          assert (b < length new_ts) as bltlengthnew_ts by (rewrite bool_decide_eq_true in Heqb0; lia);
            specialize (take_b2_cons b beven bpos new_ts bltlengthnew_ts) as [tthd [ttrest take_new_ts_cons]];
            specialize (take_b2_snoc b beven bpos new_ts bltlengthnew_ts) as [ttlast [ttrest' take_new_ts_snoc]];
            specialize (drop_b2_cons b beven bpos new_ts bltlengthnew_ts) as [dthd [dtrest drop_new_ts_cons]];
            specialize (drop_b2_snoc b bpos new_ts bltlengthnew_ts) as [dtlast [dtrest' drop_new_ts_snoc]];
            clear bltlengthnew_ts.
          assert (b < length ns0) as bltlengthns0 by (rewrite bool_decide_eq_true in Heqb0; lia);
            specialize (take_b2_cons b beven bpos ns0 bltlengthns0) as [tnhd [tnrest take_ns0_cons]];
            specialize (take_b2_snoc b beven bpos ns0 bltlengthns0) as [tnlast [tnrest' take_ns0_snoc]];
            specialize (drop_b2_cons b beven bpos ns0 bltlengthns0) as [dnhd [dnrest drop_ns0_cons]];
            specialize (drop_b2_snoc b bpos ns0 bltlengthns0) as [dnlast [dnrest' drop_ns0_snoc]].

          wp_pures;
            wp_bind (headopt_list _);
            iApply (headopt_list_spec_proof with "Hr1");
            iNext;
            iIntros (?) "[-> Hr1]";
            rewrite take_new_ts_cons;
            rewrite take_ns0_cons;
            wp_pures;
            wp_bind (interval_nary_tree _);
            iEval (rewrite Heqbranch_node_list) in "Hnstake";
            iDestruct "Hnstake" as "[Htnhd Htnsrest]";
            iApply (interval_nary_tree_spec_proof with "Htnhd");
            iNext;
            iIntros ((thdlow, thdhigh)) "[Htnhd %]";
            iCombine "Htnhd Htnsrest" as "Hnstake";
            assert (is_node tnhd tthd ∗ branch_node_list tnrest ttrest -∗
                      branch_node_list (tnhd :: tnrest) (tthd :: ttrest)) as Heqnstake
            by (rewrite Heqbranch_node_list; done);
            iPoseProof (Heqnstake with "[Hnstake]") as "Hnstake"; [rewrite Heqbranch_node_list; iFrame|];
            rewrite <- take_new_ts_cons;
            rewrite <- take_ns0_cons.

          wp_pures;
            wp_bind (lastopt_list _);
            iApply (lastopt_list_spec_proof with "Hr1");
            iNext;
            iIntros (?) "[-> Hr1]";
            rewrite take_new_ts_snoc;
            rewrite take_ns0_snoc;
            wp_pures;
            iEval (rewrite last_snoc);
            wp_pures;
            wp_bind (interval_nary_tree _);
            iEval (rewrite Heqbranch_node_list) in "Hnstake";
            iDestruct (branch_node_snoc with "Hnstake") as "[Htnsrest Htnlast]";
            iApply (interval_nary_tree_spec_proof with "Htnlast");
            iNext;
            iIntros ((tlastlow, tlasthigh)) "[Htnlast %]";
            iCombine "Htnsrest Htnlast" as "Hnstake";
            iPoseProof (branch_node_snoc' with "[Hnstake]") as "Hnstake"; [iFrame|];
            iEval (rewrite <- Heqbranch_node_list) in "Hnstake";
            rewrite <- take_new_ts_snoc;
            rewrite <- take_ns0_snoc.

          wp_pures;
            wp_bind (headopt_list _);
            iApply (headopt_list_spec_proof with "Hr2");
            iNext;
            iIntros (?) "[-> Hr2]";
            rewrite drop_new_ts_cons;
            rewrite drop_ns0_cons;
            wp_pures;
            wp_bind (interval_nary_tree _);
            iEval (rewrite Heqbranch_node_list) in "Hnsdrop";
            iDestruct "Hnsdrop" as "[Hdnhd Hdnsrest]";
            iApply (interval_nary_tree_spec_proof with "Hdnhd");
            iNext;
            iIntros ((dthdlow, dthdhigh)) "[Hdnhd %]";
            iCombine "Hdnhd Hdnsrest" as "Hnsdrop";
            assert (is_node dnhd dthd ∗ branch_node_list dnrest dtrest -∗
                      branch_node_list (dnhd :: dnrest) (dthd :: dtrest)) as Heqnsdrop
              by (rewrite Heqbranch_node_list; done);
            iPoseProof (Heqnsdrop with "[Hnsdrop]") as "Hnsdrop";
              [rewrite Heqbranch_node_list; iFrame|];
            rewrite <- drop_new_ts_cons;
            rewrite <- drop_ns0_cons.

          wp_pures;
            wp_bind (lastopt_list _);
            iApply (lastopt_list_spec_proof with "Hr2");
            iNext;
            iIntros (?) "[-> Hr2]";
            rewrite drop_new_ts_snoc;
            rewrite drop_ns0_snoc;
            wp_pures;
            iEval (rewrite last_snoc);
            wp_pures;
            wp_bind (interval_nary_tree _);
            iEval (rewrite Heqbranch_node_list) in "Hnsdrop";
            iDestruct (branch_node_snoc with "Hnsdrop") as "[Hnsrest Hnlast]";
            iApply (interval_nary_tree_spec_proof with "Hnlast");
            iNext;
            iIntros ((dtlastlow, dtlasthigh)) "[Hnlast %]";
            iCombine "Hnsrest Hnlast" as "Hnsdrop";
            iPoseProof (branch_node_snoc' with "Hnsdrop") as "Hnsdrop";
            rewrite <- drop_new_ts_snoc;
            rewrite <- drop_ns0_snoc.

          wp_alloc newbranch as "Hnewbranch";
            wp_alloc newlmid as "Hnewlmid";
            wp_alloc newlhd as "Hnewlhd";
            wp_alloc newroot as "Hnewroot";
            wp_store;
            wp_pures.

          iApply "HPost".
          subst r0;
            rewrite bool_decide_eq_true in Heqb0;
            apply Z.ltb_lt in Heqb0;
            rewrite <- Heqlengths, Heqb0.

          iExists newroot, (SOMEV #newlhd), (token_branch_v #ptr :: token_branch_v #newbranch :: []).
          fold is_node; rewrite <- Heqbranch_node_list.
          repeat rewrite head_map_comm last_map_comm.
          rewrite take_new_ts_cons;
            rewrite take_ns0_cons;
            iEval (rewrite head_cons);
            rewrite <- take_new_ts_cons;
            rewrite <- take_ns0_cons.
          rewrite take_new_ts_snoc;
            rewrite take_ns0_snoc;
            iEval (rewrite last_snoc);
            rewrite <- take_new_ts_snoc;
            rewrite <- take_ns0_snoc.
          rewrite drop_new_ts_cons;
            rewrite drop_ns0_cons;
            iEval (rewrite head_cons);
            rewrite <- drop_new_ts_cons;
            rewrite <- drop_ns0_cons.
          rewrite drop_new_ts_snoc;
            rewrite drop_ns0_snoc;
            iEval (rewrite last_snoc);
            rewrite <- drop_new_ts_snoc;
            rewrite <- drop_ns0_snoc.
          destruct H0, H1, H2, H3.

          iSplitR; [done|].
          iSplitL "Hnewroot"; [done|].
          iSplitL "Hnewlhd Hnewlmid";
            [iExists newlhd, (SOMEV #newlmid); iFrame; iSplitR; [done|]; iExists newlmid, NONEV; iFrame; done|].
          iSplitL "Hptr Hr1 Hnstake";
            [iExists ptr, r1.1, (take (b/2) ns0)
            |iSplitL; [|done]; iExists newbranch, r1.2, (drop (b/2) ns0)];
            iFrame; done.

        + iPoseProof ((branch_node_list_lengths ns0 new_ts) with "[Hns0]") as "[Hns %Heqlengths]";
            [rewrite Heqbranch_node_list; done|];
            rewrite <- Heqbranch_node_list.

          destruct new_ts as [|thd trest];
            destruct ns0 as [|nhd nrest];
            [|rewrite Heqbranch_node_list; done|rewrite Heqbranch_node_list; done|].
          * wp_pures;
              wp_bind (headopt_list _);
              iApply (headopt_list_spec_proof with "Hr");
              iNext;
              iIntros (?) "[-> Hr]";
              iEval (rewrite head_nil).
            wp_pures;
              wp_bind (lastopt_list _);
              iApply (lastopt_list_spec_proof with "Hr");
              iNext;
              iIntros (?) "[-> Hr]";
              iEval (rewrite last_nil).
            wp_store; wp_pures.

            iApply "HPost".
            apply bool_decide_eq_false_1 in Heqb0;
              assert (Z.le r0 b) by lia;
              apply Z.leb_le in H0;
              rewrite Z.leb_antisym in H0;
              symmetry in H0;
              apply negb_sym in H0;
              cbn in H0;
              subst r0;
              rewrite H0.
            iExists ptr, r, [];
              iFrame;
              done.

          * wp_pures;
              wp_bind (headopt_list _);
              iApply (headopt_list_spec_proof with "Hr");
              iNext;
              iIntros (?) "[-> Hr]";
              iEval (rewrite head_cons);
              wp_pures;
              wp_bind (interval_nary_tree _);
              iEval (rewrite Heqbranch_node_list) in "Hns";
              iDestruct "Hns" as "[Hnhd Hnsrest]";
              iApply (interval_nary_tree_spec_proof with "Hnhd");
              iNext;
              iIntros ((hdlow, hdhigh)) "[Hnhd %]";
              iCombine "Hnhd Hnsrest" as "Hns";
              assert (is_node nhd thd ∗ branch_node_list nrest trest -∗
                        branch_node_list (nhd :: nrest) (thd :: trest)) as Heqnbranches
                by (rewrite Heqbranch_node_list; done);
              iPoseProof (Heqnbranches with "[Hns]") as "Hns";
              [rewrite Heqbranch_node_list; iFrame|].

            destruct (cons_snoc (thd :: trest) _ _ eq_refl) as [tlast [tinit Heqts]].
            destruct (cons_snoc (nhd :: nrest) _ _ eq_refl) as [nlast [ninit Heqns]].

            rewrite Heqts Heqns;
              wp_pures;
              wp_bind (lastopt_list _);
              iApply (lastopt_list_spec_proof with "Hr");
              iNext;
              iIntros (?) "[-> Hr]";
              iEval (rewrite last_snoc);
              wp_pures;
              wp_bind (interval_nary_tree _);
              iEval (rewrite Heqbranch_node_list) in "Hns";
              iDestruct (branch_node_snoc with "Hns") as "[Hnsrest Hnlast]";
              iApply (interval_nary_tree_spec_proof with "Hnlast");
              iNext;
              iIntros ((lastlow, lasthigh)) "[Hnlast %]";
              iCombine "Hnsrest Hnlast" as "Hns";
              iPoseProof (branch_node_snoc' with "Hns") as "Hns";
              rewrite <- Heqts, <- Heqns.

            wp_store; wp_pures.
            iApply "HPost".
            apply bool_decide_eq_false_1 in Heqb0;
              assert (Z.le r0 b) by lia;
              apply Z.leb_le in H2;
              rewrite Z.leb_antisym in H2;
              symmetry in H2;
              apply negb_sym in H2;
              cbn in H2;
              rewrite <- Heqlengths;
              subst r0;
              rewrite H2.

            repeat rewrite head_map_comm last_map_comm;
              rewrite head_cons;
              rewrite Heqts;
              rewrite last_snoc;
              rewrite <- Heqts.

            destruct H0, H1.
            iExists ptr, r, (nhd :: nrest);
              iFrame;
              done.
    Qed.

    Theorem insert_bplus_tree_spec_proof (t : tree_spec) (t_wf : tree_spec_wf b t) (v : val) (target : tval) :
      {{{ is_bplus_tree b v t t_wf }}}
        insert_bplus_tree b (v, #target)%V
        {{{ r, RET r; is_bplus_tree b r (insert_bplus_tree_spec b target t) (insert_bplus_tree_wf b beven bpos target t t_wf) }}}.
    Proof.
      iIntros (Φ) "Hv HPost".
      iApply (insert_bplus_tree_spec_proof_no_wf with "Hv").
      done.
    Qed.

  End bplus_tree_proofs.
End bplus_tree.
