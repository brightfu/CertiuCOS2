Require Import include_frm.
Require Import join_lib.

Lemma ex_join1_auto:
  forall (A B T : Type) (MC : PermMap A B T) a b c d ab cd m,
      join ab cd m ->
      join c d cd ->
      join a b ab ->
    exists cc, join c a cc.
  intros.
  geat.
Qed.  

Lemma ex_join1:
    forall a b c d ab cd m,
      HalfPermMap.join ab cd m ->
      HalfPermMap.join c d cd ->
      HalfPermMap.join a b ab ->
    exists cc, join c a cc.
  intros.
  eapply ex_join1_auto.
  exact H.
  exact H0.
  eauto.
Qed.

Lemma ex_join2_auto:
  forall (A B T : Type) (MC : PermMap A B T) a b c d ab cd m,
    join ab cd m ->
    join c d cd ->
    join a b ab ->
    exists cc, join b d cc.
  intros.
  geat.
Qed.  
  
Lemma ex_join2:
    forall a b c d ab cd m,
      HalfPermMap.join ab cd m ->
      HalfPermMap.join c d cd ->
      HalfPermMap.join a b ab ->
    exists cc, join b d cc.
  intros.
  eapply ex_join2_auto.
  exact H.
  eauto.
  eauto.
Qed.

Local Ltac infer_merge x y t ::=
      match goal with
        | F:get x t = ?b1 |- _ =>
          match goal with 
            | F1:get y t = ?b2 |- _ =>
              match constr:(b1, b2) with
                | (Some ?v1, Some ?v2) =>
                  match goal with
                    | Hn:usePerm = false
                      |- _ => generalize (merge_sem1' Hn F F1); intro
                    | Hn:usePerm = true
                      |- _ =>
                      let H' := fresh in
                      generalize (merge_semp x y t Hn); intro H';
                      try (rewrite F in H'); try (rewrite F1 in H');
                      (let Hs := fresh in
                       destruct (same v1 v2) eqn:Hs; rewrite_same;
                       [ let H1 := fresh in
                         destruct (isRw v1) eqn:H1;
                         [ 
                         | assert (isRw (flip v1) = true) by
                             join_tactics.veg.jeauto2 ]
                       | tryfalse ])
                  end
                | (Some ?v1, None) =>
                  generalize (merge_sem_none2 F1 F); intro
                | (None, Some ?v2) =>
                  generalize (merge_sem_none1 F F1); intro
                | (None, None) =>
                  generalize (merge_sem_none3 F F1); intro
              end
          end
      end.
(** TODO: update infer_merge, test it and place in join_lib **)

Lemma merge_false_is_true_auto:
  forall (A B T : Type) (MC : PermMap A B T) b a,
    usePerm = true ->
    isRw b = false ->
    merge (sig a b) (sig a b) = sig a (flip b).
  intros.
  hy.
Qed.  
  
Lemma merge_false_is_true:
    forall b o a,
      HalfPermMap.merge (HalfPermMap.sig (b, o) (false, a))
                        (HalfPermMap.sig (b, o) (false, a)) = HalfPermMap.sig (b, o) (true, a).
  intros.
  assert (merge (sig (b,o) (false, a)) (sig (b,o) (false, a)) = sig (b, o) (flip (false, a))).
  {
    eapply merge_false_is_true_auto; ica.
  }
  unfold flip in H.
  simpl in H.
  unfold HalfPermMap.flip in H.
  simpl in H.
  auto.
Qed.  

Lemma merge_join_auto:
  forall (A B T : Type) (MC : PermMap A B T) x1 x2 m1 x x0 m2 m3,
    usePerm = true ->
    join x1 x2 m1 ->
    join x x0 m2 ->
    join m1 m2 m3 ->
    join (merge x x1) (merge x0 x2) m3.
  intros.
  hy.
Qed.

Lemma merge_join:
  forall x1 x2 m1 x x0 m2 m3,
    HalfPermMap.join x1 x2 m1 ->
    HalfPermMap.join x x0 m2 ->
    HalfPermMap.join m1 m2 m3 ->
    HalfPermMap.join (HalfPermMap.merge x x1) (HalfPermMap.merge x0 x2) m3.
  intros.
  assert (join (merge x x1) (merge x0 x2) m3).
  {
    eapply merge_join_auto; auto.
    eauto.
    eauto.
    eauto.
  }
  eauto.
Qed.  

Lemma join_merge_auto:
  forall (A B T : Type) (MC : PermMap A B T) x1 x2 m1 x x0 m2 m3,
    usePerm = true ->
    join x1 x2 m1 ->
    join x x0 m2 ->
    join m1 m2 m3 ->
    join x0 x2 (merge x0 x2).
  hy.
Qed.  

Lemma join_merge:
  forall x1 x2 m1 x x0 m2 m3,
    HalfPermMap.join x1 x2 m1 ->
    HalfPermMap.join x x0 m2 ->
    HalfPermMap.join m1 m2 m3 ->
    HalfPermMap.join x0 x2 (HalfPermMap.merge x0 x2).
  intros.
  assert (join x0 x2 (merge x0 x2)).
  {
    eapply join_merge_auto; ica.
  }
  auto.
Qed.

Lemma join_false_is_true_auto:
  forall (A B T : Type) (MC : PermMap A B T) p a,
    usePerm = true ->
    isRw a = false ->
    join (sig p a)
         (sig p a) (sig p (flip a)).
  hy.
Qed.  

Lemma join_false_is_true:
  forall p a,
    HalfPermMap.join (HalfPermMap.sig p (false, a))
                     (HalfPermMap.sig p (false, a)) (HalfPermMap.sig p (true, a)).
  intros.
  assert (join (sig p (false, a)) (sig p (false, a)) (sig p (flip (false, a)))).
  {
    eapply join_false_is_true_auto; ica.
  }
  unfold flip in H; simpl in H.
  unfold HalfPermMap.flip in H; simpl in H.
  auto.
Qed.  

Lemma join_merge2_auto:
  forall (A B T : Type) (MC : PermMap A B T) x0 x3 x4 x1 x2 x m,
    usePerm = true ->
    join x x0 m ->
    join x3 x4 x ->
    join x1 x2 x0 ->
    join (merge x3 x1) (merge x4 x2) m.
  hy.
Qed.
  
Lemma join_merge2:
  forall x0 x3 x4 x1 x2 x m,
    HalfPermMap.join x x0 m ->
    HalfPermMap.join x3 x4 x ->
    HalfPermMap.join x1 x2 x0 ->
    HalfPermMap.join (merge x3 x1) (merge x4 x2) m.
  intros.
  assert (join (merge x3 x1) (merge x4 x2) m) by (eapply join_merge2_auto; ica).
  auto.
Qed.

Lemma join_false_val_eq_auto:
  forall (A B T : Type) (MC : PermMap A B T) l v1 v2 m3,
    usePerm = true ->
    isRw v1 = false ->
    isRw v2 = false ->
    join (sig l v1) (sig l v2) m3 ->
    v1 = v2.
  intros.
  infer' (pnil, sig l v1, sig l v2, join (sig l v1) (sig l v2) m3) l;
  crush.
Qed.
  
Lemma join_false_val_eq:
  forall l v1 v2 m3,
    HalfPermMap.join (HalfPermMap.sig l (false, v1)) (HalfPermMap.sig l (false, v2)) m3 ->
    v1 = v2.
  intros.
  assert ((false, v1) = (false, v2)).
  {
    eapply join_false_val_eq_auto; ica.
  }
  inverts H0.
  auto.
Qed. 
