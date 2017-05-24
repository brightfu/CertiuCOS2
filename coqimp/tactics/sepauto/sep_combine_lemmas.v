Require Import include_frm.
Require Import base_tac.
Require Import seplog_tactics.
Require Import sep_join_lemmas.

Lemma ptomval_same_value_same:
  forall l v1 v2 m1 m2 m3,
    ptomval l false v1 m1 -> ptomval l false v2 m2 -> join m1 m2 m3 -> v1 = v2.
Proof.
  intros.
  unfold ptomval in *.
  subst .
  unfold join,sig in *; simpl in *.
  eapply join_false_val_eq.
  eauto.
Qed.

Lemma ptomval_leneq_samels:
  forall l1 l2 l m x x0,
    join x x0 m ->
    length l1 = length l2 ->
    ptomvallist l false l1 x0 ->
    ptomvallist l false l2  x  ->
    l1 = l2.
Proof.
  intro.
  induction l1.
  intros.
  destruct l2;
  inversion H0.
  auto.
  intro.
  induction l2.
  intros.
  inversion H0.
  intros.
  unfold ptomvallist in *.
  fold ptomvallist in *.
  destruct l; simpljoin.


  lets aa: ex_join1 H H1 H2.
  lets bb: ex_join2 H H1 H2.
  destruct aa as (cc & aa).
  destruct bb as (dd & bb).
  cut (a = a0).
  intros.
  assert (l1 = l2).
  unfold join in *; simpl in *.
  
  
  eapply IHl1.
  3:eauto.
  3:eauto.
  2:auto.
  eauto.
  subst;
  auto.
  unfold ptomval in *.
  eapply ptomval_same_value_same.
  eauto.
  eauto.
  eauto.
Qed.


Lemma ptomvallist_f2t:
  forall l m1 m2 m3 p,
    ptomvallist p false l m1 ->
    ptomvallist p false l m2 ->
    join m1 m2 m3 ->
    ptomvallist p true l m3.
Proof.
  induction l.
  intros.
  simpl in *.
  subst.
  jeat .

  intros.
  unfold ptomvallist in *.
  fold ptomvallist in *.
  destruct p.
  simpljoin.
  eexists.
  eexists.
  splits.

  Focus 2.
  unfold ptomval in *.
  instantiate (1 := merge x x1).
  subst.
  unfold merge, sig; simpl.
  apply merge_false_is_true.

  unfold join, merge in *; simpl in *.

  eapply merge_join; eauto.
 
  eapply IHl.
  eauto.
  exact H5.

  unfold join, merge in *; simpl in *.

  eapply join_merge; eauto.

Qed.


Lemma combine_ro2rw_p1:
  forall l t v v',
    l # t |-r-> v ** l # t |-r-> v' ==> l#t |-> v .
Proof.
  intros.
  simpl in H.
  simpljoin.
  unfold emposabst in *.
  unfold mapstoval in *.
  simpljoin.
  destruct s as [[[[[[]]]]]].
  simpl in *.
  subst x2.
  subst x3.
  
  splits; eauto.
  unfold mapstoval.
  eexists.
  splits.
  eauto.
  
  assert (encode_val t v' = encode_val t v).
  eapply ptomval_leneq_samels.

  eauto.
  rewrite encode_val_length.
  rewrite encode_val_length.
  auto.
  eauto.
  eauto.
  rewrite H in H3.
  eapply ptomvallist_f2t.
  3:eauto.
  eauto.
  eauto.
  unfolds.
  jeat.
Qed.


Lemma combine_ro2rw_p1_frm:
  forall l t v v' p,
    l # t |-r-> v ** l # t |-r-> v' ** p ==> l#t |-> v ** p.
Proof.
  intros.
  sep_cancel 3%nat 2%nat.
  eapply combine_ro2rw_p1.
  eauto.
Qed.

Lemma combine_ro2rw_p2:
  forall l t v v' s,
    s|=l # t |-r-> v ** l # t |-r-> v' -> encode_val t v = encode_val t v' .
Proof.
  intros.
  simpl in H.
  simpljoin.
  unfold emposabst in *.
  unfold mapstoval in *.
  simpljoin.
  destruct s as [[[[[[]]]]]].
  simpl in *.
  subst x2.
  subst x3.
  
  apply map_join_comm in H0. 
  eapply  ptomval_leneq_samels.
  eauto.
  rewrite encode_val_length.
  rewrite encode_val_length.
  auto.
  eauto.
  eauto.
Qed.

Lemma combine_ro2rw_p2_frm:
  forall l t v v' s p,
    s|=l # t |-r-> v ** l # t |-r-> v' ** p -> encode_val t v = encode_val t v' .
Proof.
  intros.
  sep lift 3%nat in H.
  simpl in H.
  simpljoin.
  unfold emposabst in *.
  unfold mapstoval in *.
  simpljoin.
  destruct s as [[[[[[]]]]]].
  simpl in *.
  subst x8.
  subst x9.
  
  apply map_join_comm in H5. 
  eapply  ptomval_leneq_samels.
  exact H5.
  eauto.
  rewrite encode_val_length.
  rewrite encode_val_length.
  auto.
  eauto.
  eauto.
Qed.

Lemma combine_ro2rw:
  forall l t v v',
    l # t |-r-> v ** l # t |-r-> v' ==> l#t |-> v ** [|encode_val t v = encode_val t v' |].
Proof.
  intros.
  sep auto.
  eapply combine_ro2rw_p1.
  eauto.
  eapply combine_ro2rw_p2.
  eauto.
Qed.

Lemma encode_val_eq_amapsto_eq: forall t v l v',
       encode_val t v = encode_val t v' ->
       l # t |-r-> v ==> l # t |-r-> v' .
Proof.
  intros.
  simpl in *.
  simpljoin.
  splits; auto.
  unfold mapstoval in *.
  simpljoin.
  eexists; splits; eauto.
  rewrite <- H.
  auto.
Qed.

Lemma ptomval_t2f:
  forall p a x,
    ptomval p true a x ->
    exists x1 x2, join x1 x2 x /\ ptomval p false a x1 /\ ptomval p false a x2.
Proof.
  intros.
  unfolds in H.
  subst x.
  eexists (sig p (false, a)).
  eexists (sig p (false, a)).
  splits.

  unfold join,sig; simpl.
  eapply join_false_is_true.
  unfolds; simpl; auto.
  unfolds; simpl; auto.
Qed.

Lemma ptomvallist_t2f:
  forall l p m,
    ptomvallist p true l m ->
    exists m1 m2, join m1 m2 m /\ ptomvallist p false l m1 /\ ptomvallist p false l m2.
Proof.
  induction l.
  intros.
  
  unfolds in H.
  subst m.
  eexists emp.
  eexists emp.
  splits; simpl; auto.
  jeat.
  intros.
  unfold1 ptomvallist in *.
  destruct p.
  simpljoin.
  lets bbb: IHl H1.
  simpljoin.

  apply ptomval_t2f in H0.
  simpljoin.
  eexists (merge x3 x1).
  eexists (merge x4 x2).
  splits.

  unfold join in *; simpl in *.
  eapply join_merge2; eauto.
  exists x3 x1.
  splits; auto.
  eapply join_merge.
  apply join_comm in H2.
  eauto.
  apply join_comm in H0.
  eauto.
  apply join_comm in H.
  eauto.

  exists x4 x2.
  splits; auto.

  eapply join_merge.
  eauto.
  eauto.

  apply join_comm in H.
  eauto.
Qed.


Lemma separate_rw2ro:
  forall l t v ,
    l#t |-> v  ==> l # t |-r-> v ** l # t |-r-> v .
Proof.
  intros.
  simpl in *.
  simpljoin.  
  unfolds in H.
  simpljoin.
  apply ptomvallist_t2f in H1.
  simpljoin.
  
  do 6 eexists.
  splits.
  instantiate (1 := (getmem s)).
  auto.
  apply H.
  
  eauto.
  instantiate (2:= emp).
  instantiate (1:= emp).
  2:eauto.
  eauto.
  Focus 3.
  unfolds.
  eexists; splits; auto.
  destruct s as [[[[[[]]]]]].
  simpl.
  eauto.
  Focus 2.
  splits.
  unfolds.
  eexists; splits; auto.
  destruct s as [[[[[[]]]]]].
  simpl.
  auto.
  destruct s as [[[[[[]]]]]].
  simpl.
  unfolds; auto.
  unfolds in H0.
  rewrite H0.
  jeat.

  destruct s as [[[[[[]]]]]].
  simpl.
  unfolds; auto.
Qed.

Lemma combine_ro2rw':
  forall l t v v',
    encode_val t v = encode_val t v' ->
    l#t |-> v ==>l # t |-r-> v ** l # t |-r-> v'  .
Proof.
  intros.
  apply separate_rw2ro in H0.
  sep_cancel 1%nat 1%nat.
  eapply encode_val_eq_amapsto_eq.
  eauto.
  auto.
Qed.

Theorem StarMono : 
  forall P Q P' Q',
    P ==> P' -> Q ==> Q' -> P ** Q ==> P' ** Q'.
Proof.
  intros.
  simpl in *.
  simpljoin.
  do 6 eexists; splits; eauto.
Qed.


Lemma combine_ro2rw_frm:
  forall l t v v' p,
    l # t |-r-> v ** l # t |-r-> v' ** p ==> l#t |-> v ** [|encode_val t v = encode_val t v' |] ** p.
Proof.
  intros.
  sep lift 3%nat.
  sep lift 3%nat in H.
  eapply StarMono.
  intro.
  intro; eauto.
  intro.
  intros.
  apply combine_ro2rw.
  eauto.
  eauto.
Qed.  

Lemma combine_ro2rw'_frm:
  forall l t v v' p,
    encode_val t v = encode_val t v' ->
    l#t |-> v ** p==>l # t |-r-> v ** l # t |-r-> v' ** p .
Proof.
  intros.
  sep lift 2%nat in H0.
  sep lift 3%nat.
  eapply StarMono.
  intro.
  eauto.
  apply combine_ro2rw'.
  auto.
  auto.
Qed.

Lemma separate_rw2ro_frm:
  forall l t v p,
    l#t |-> v **p ==> l # t |-r-> v ** l # t |-r-> v **p.
Proof.
  intros.
  sep lift 2%nat in H.
  sep lift 3%nat .
  eapply StarMono.
  intro.
  intro; eauto.
  intro.
  intros.
  eapply separate_rw2ro.
  eauto.
  eauto.
Qed.

(* PV version *)

Lemma PV_combine_ro:
  forall l t v v',
    PV l @ t |-r-> v  ** PV l @ t |-r->v' ==> PV l @ t |-> v ** [|encode_val t v = encode_val t v' |].
Proof.
  intros.
  unfold Aptrmapsto in *.
  unfold addrval_to_addr.
  destruct l.
  apply combine_ro2rw.
  eauto.
Qed.

Lemma PV_combine_ro_p1:
  forall l t v v',
    PV l @ t |-r-> v  ** PV l @ t |-r->v' ==> PV l @ t |-> v .
Proof.
  intros.
  unfold Aptrmapsto in *.
  unfold addrval_to_addr.
  destruct l.
  eapply combine_ro2rw_p1.
  eauto.
Qed.


Lemma PV_combine_ro_p2:
  forall l t v v' s,
    s |= PV l @ t |-r-> v  ** PV l @ t |-r->v' ->
                                         encode_val t v = encode_val t v'.
Proof.
  intros.
  unfold Aptrmapsto in *.
  unfold addrval_to_addr.
  destruct l.
  eapply combine_ro2rw_p2.
  eauto.
Qed.


Lemma PV_combine_ro_frm:
  forall l t v v' p,
    PV l @ t |-r-> v  ** PV l @ t |-r->v' ** p ==> PV l @ t |-> v ** [|encode_val t v = encode_val t v' |] ** p.
Proof.
  intros.
  sep lift 3%nat in H.
  sep lift 3%nat .
  eapply StarMono.
  intro.
  intros; eauto.
  intro.
  intros.
  apply PV_combine_ro.
  eauto.
  auto.
Qed.

Lemma PV_combine_ro_frm_p1:
  forall l t v v' p,
    PV l @ t |-r-> v  ** PV l @ t |-r->v' ** p ==> PV l @ t |-> v  ** p.
Proof.
  intros.
  sep lift 3%nat in H.
  sep lift 2%nat .
  eapply StarMono.
  intro.
  intros; eauto.
  intro.
  intros.
  eapply PV_combine_ro_p1.
  eauto.
  eauto.
Qed.

Lemma PV_combine_ro_frm_p2:
  forall l t v v' p s,
    s|=PV l @ t |-r-> v  ** PV l @ t |-r->v' ** p ->
    encode_val t v = encode_val t v' .
Proof.
  intros.
  unfold Aptrmapsto in *.
  destruct l.
  eapply combine_ro2rw_p2_frm.
  eauto.
Qed.

  
Lemma PV_separate_rw:
  forall l t v ,
    PV l @ t |-> v ==> PV l @ t |-r-> v  ** PV l @ t |-r->v .
Proof.
  intros.
  unfold Aptrmapsto in *.
  unfold addrval_to_addr.
  destruct l.
  apply separate_rw2ro.
  eauto.
Qed.

Lemma PV_separate_rw_frm:
  forall l t v  p,
     PV l @ t |-> v ** p ==>  PV l @ t |-r-> v  ** PV l @ t |-r->v ** p .
Proof.
  intros.
  sep lift 2%nat in H.
  sep lift 3%nat .
  eapply StarMono.
  intro.
  intros; eauto.
  intro.
  intros.
  apply PV_separate_rw.
  eauto.
  auto.
Qed.

Lemma PV_change_val:
  forall l t b v v',
    encode_val t v = encode_val t v'  ->
    PV l @ t |=> v @ b  ==> PV l @ t |=> v' @b  .
Proof.
  intros.
  split.
  intros.
  simpl in *.
  unfold mapstoval in *.
  simpljoin.
  destruct s as [[[[[[]]]]]].
  simpl in *.
  rewrite <- H.
  eexists; splits; eauto.
  rewrite <- H.
  auto.
  intros.
  simpl in *.
  unfold mapstoval in *.
  simpljoin.
  destruct s as [[[[[[]]]]]].
  simpl in *.
  auto.
Qed.
 
Lemma PV_change_val_frm:
  forall l t b v v' p,
    encode_val t v = encode_val t v'  ->
    PV l @ t |=> v @ b **p ==> PV l @ t |=> v' @b **p .
Proof.
  intros.
  sep lift 2%nat in H0.
  sep lift 2%nat.
  eapply StarMono.
  intro.
  eauto.
  apply PV_change_val.
  eauto.
  auto.
Qed.


Lemma PV_combine_ro':
  forall l t v v',
    encode_val t v = encode_val t v' ->
    PV l @ t |-> v ==> PV l @ t |-r-> v ** PV l @ t |-r-> v'  .
Proof.
  intros.
  apply PV_separate_rw in H0.
  sep_cancel 1%nat 1%nat.
  eauto.
  auto.
  eapply PV_change_val.
  eauto.
  auto.
Qed.

Lemma PV_combine_ro'_frm:
  forall l t v v' p,
    encode_val t v = encode_val t v' ->
    PV l @ t |-> v ** p ==> PV l @ t |-r-> v ** PV l @ t |-r-> v'  ** p.
Proof.
  intros.
  sep lift 2%nat in H0.
  sep lift 3%nat.
  eapply StarMono.
  intro.
  eauto.
  apply PV_combine_ro'.
  auto.
  auto.
Qed.  

(* addr_eq  *)

Lemma LR_addr_eq :
  forall s x t l l',
    s |= Alvarenv x t l ** Alvarenv x t l' -> l = l'.
Proof.
  intros.
  simpl in H.
  simpljoin.
  destruct s as [[[[[[]]]]]].
  simpl in *.
  subst.
  rewrite H3 in H4.
  inverts H4.
  auto.
Qed.

Lemma LR_addr_eq_frm:
  forall s x t l l' p,
    s |= Alvarenv x t l ** Alvarenv x t l' ** p -> l = l'.
Proof.
  intros.
  simpl in H.
  simpljoin.
  destruct s as [[[[[[]]]]]].
  simpl in *.
  subst.
  rewrite H3 in H8.
  inverts H8.
  auto.
Qed.

Lemma GR_addr_eq :
  forall s x t l l',
    s |= Agvarenv x t l ** Agvarenv x t l' -> l = l'.
Proof.
  intros.
  simpl in H.
  simpljoin.
  destruct s as [[[[[[]]]]]].
  simpl in *.
  subst.
  rewrite H3 in H4.
  inverts H4.
  auto.
Qed.


Lemma GR_addr_eq_frm:
  forall s x t l l' p,
    s |= Agvarenv x t l ** Agvarenv x t l' ** p -> l = l'.
Proof.
  intros.
  simpl in H.
  simpljoin.
  destruct s as [[[[[[]]]]]].
  simpl in *.
  subst.
  rewrite H3 in H8.
  inverts H8.
  auto.
Qed.

(* LV version *)

Lemma LV_combine_ro_p1:
  forall l t v v',
    LV l @ t |-r-> v  ** LV l @ t |-r->v' ==> LV l @ t |-> v .
Proof.
  intros.
  unfold Alvarmapsto in *.
  sep normal in H.
  sep destruct H.
  assert ( x = x0).
  
  unfold Alvarenv' in H.
  sep lift 3%nat in H.
  apply LR_addr_eq_frm in H.

  unfold addrval_to_addr in H.
  inverts H.
  auto.
  subst x0.
  
  sep eexists.
  sep lifts (2::nil)%nat.
  eapply PV_combine_ro_frm_p1.
  sep_cancel 2%nat 2%nat.

  sep_cancel 3%nat 1%nat.
  simpl in *.
  simpljoin.
  destruct s as [[[[[[]]]]]].
  simpl in *.
  subst .
  eexists; splits; eauto.

  Local Ltac getempenv :=
    match goal with
      | H : emposabst ?a |- _ => unfolds in H; getempenv
      | |- emposabst ?a => unfolds; getempenv
      | _ => try subst; jeat
    end.
  getempenv.
  getempenv.

  
Qed.

Lemma LV_combine_ro_p2:
  forall l t v v' s,
    s |= LV l @ t |-r-> v  ** LV l @ t |-r->v' ->
                                         encode_val t v = encode_val t v'.
Proof.
  intros.
  unfold Alvarmapsto in *.
  sep normal in H.
  sep destruct H.

  eapply PV_combine_ro_frm_p2.
  assert (x = x0).
  sep lift 3%nat in H.
  apply LR_addr_eq_frm in H.
  unfold addrval_to_addr in H.
  inverts H.
  auto.
  
  sep lifts (4::2::nil)%nat in H.
  subst x0.
  exact H.
Qed.


Lemma LV_combine_ro:
  forall l t v v',
    LV l @ t |-r-> v  ** LV l @ t |-r->v' ==> LV l @ t |-> v ** [|encode_val t v = encode_val t v' |].
Proof.
  intros.
  sep auto.
  eapply LV_combine_ro_p1.
  eauto.
  eapply LV_combine_ro_p2.
  eauto.
Qed.

Lemma LV_combine_ro_frm_p1:
  forall l t v v' p,
    LV l @ t |-r-> v  ** LV l @ t |-r->v' ** p ==> LV l @ t |-> v  ** p.
Proof.
  intros.
  sep lift 3%nat in H.
  sep lift 2%nat .
  eapply StarMono.
  intro.
  intros; eauto.
  intro.
  intros.
  eapply LV_combine_ro_p1.
  eauto.
  eauto.
Qed.

Lemma LV_combine_ro_frm_p2:
  forall l t v v' p s,
    s|=LV l @ t |-r-> v  ** LV l @ t |-r->v' ** p ->
    encode_val t v = encode_val t v' .
Proof.
  intros.
  unfold Alvarmapsto in *.
  sep normal in H.
  sep destruct H.
  assert ( x0 = x).
  sep lift 3%nat in H.
  apply LR_addr_eq_frm in H.
  unfold addrval_to_addr in H.
  inverts H.
  auto.
  subst x0.

  eapply PV_combine_ro_frm_p2.
  sep lifts (4::2::nil)%nat in H.
  eauto.
Qed.



Lemma LV_combine_ro_frm:
  forall l t v v' p,
    LV l @ t |-r-> v  ** LV l @ t |-r->v' ** p ==> LV l @ t |-> v ** [|encode_val t v = encode_val t v' |] ** p.
Proof.
  intros.
  sep lift 3%nat in H.
  sep lift 3%nat .
  eapply StarMono.
  intro.
  intros; eauto.
  intro.
  intros.
  apply LV_combine_ro.
  eauto.
  auto.
Qed.

Lemma LV_separate_rw:
  forall l t v ,
    LV l @ t |-> v ==> LV l @ t |-r-> v  ** LV l @ t |-r->v .
Proof.
  intros.
  unfold Alvarmapsto in *.
  sep normal.
  sep destruct H.
  sep eexists.
  sep lift 2%nat in H.
  apply PV_separate_rw_frm in H.
  sep_cancel 1%nat 2%nat.
  sep_cancel 1%nat 3%nat.
  destruct s as [[[[[[]]]]]].
  
  simpl in *.
  simpljoin.
  do 6 eexists.
  splits ;eauto.
  getempenv.
  getempenv.
Qed.

Lemma LV_separate_rw_frm:
  forall l t v  p,
     LV l @ t |-> v ** p ==>  LV l @ t |-r-> v  ** LV l @ t |-r->v ** p .
Proof.
  intros.
  sep lift 2%nat in H.
  sep lift 3%nat .
  eapply StarMono.
  intro.
  intros; eauto.
  intro.
  intros.
  apply LV_separate_rw.
  eauto.
  auto.
Qed.
 
 
Lemma LV_change_val:
  forall l t b v v',
    encode_val t v = encode_val t v'  ->
    LV l @ t |=> v @ b  ==> LV l @ t |=> v' @b  .
Proof.
  intros.
  unfold Alvarmapsto in *.
  sep destruct H0.
  sep eexists.
  sep lift 2%nat in H0.
  sep lift 2%nat.
  eapply StarMono.
  intro.
  intros.
  eapply PV_change_val.
  eauto.
  eauto.
  eauto.
  eauto.
Qed.

 
Lemma LV_change_val_frm:
  forall l t b v v' p,
    encode_val t v = encode_val t v'  ->
    LV l @ t |=> v @ b **p ==> LV l @ t |=> v' @b **p .
Proof.
  intros.
  sep lift 2%nat in H0.
  sep lift 2%nat.
  eapply StarMono.
  intro.
  eauto.
  apply LV_change_val.
  eauto.
  auto.
Qed.

 
Lemma LV_combine_ro':
  forall l t v v',
    encode_val t v = encode_val t v' ->
    LV l @ t |-> v ==> LV l @ t |-r-> v ** LV l @ t |-r-> v'  .
Proof.
  intros.
  apply LV_separate_rw in H0.
  sep_cancel 1%nat 1%nat.
  eauto.
  auto.
  eapply LV_change_val.
  eauto.
  auto.
Qed.

Lemma LV_combine_ro'_frm:
  forall l t v v' p,
    encode_val t v = encode_val t v' ->
    LV l @ t |-> v ** p ==> LV l @ t |-r-> v ** LV l @ t |-r-> v'  ** p.
Proof.
  intros.
  sep lift 2%nat in H0.
  sep lift 3%nat.
  eapply StarMono.
  intro.
  eauto.
  apply LV_combine_ro'.
  auto.
  auto.
Qed.  

(* GV version *)

Lemma GV_combine_ro_p1:
  forall l t v v',
    GV l @ t |-r-> v  ** GV l @ t |-r->v' ==> GV l @ t |-> v .
Proof.
  intros.
  unfold Agvarmapsto in *.
  sep normal in H.
  sep destruct H.
  assert ( x = x0).
  
  unfold Alvarenv' in H.
  sep lift 3%nat in H.
  apply GR_addr_eq_frm in H.

  unfold addrval_to_addr in H.
  inverts H.
  auto.
  subst x0.
  
  sep eexists.
  sep lifts (2::nil)%nat.
  eapply PV_combine_ro_frm_p1.
  sep_cancel 2%nat 2%nat.

  sep_cancel 3%nat 1%nat.
  simpl in *.
  simpljoin.
  destruct s as [[[[[[]]]]]].
  simpl in *.
  subst .
  eexists; splits; eauto.
  getempenv.
  getempenv.
Qed.

Lemma GV_combine_ro_p2:
  forall l t v v' s,
    s |= GV l @ t |-r-> v  ** GV l @ t |-r->v' ->
                                         encode_val t v = encode_val t v'.
Proof.
  intros.
  unfold Agvarmapsto in *.
  sep normal in H.
  sep destruct H.

  eapply PV_combine_ro_frm_p2.
  assert (x = x0).
  sep lift 3%nat in H.
  apply GR_addr_eq_frm in H.
  unfold addrval_to_addr in H.
  inverts H.
  auto.
  
  sep lifts (4::2::nil)%nat in H.
  subst x0.
  exact H.
Qed.


Lemma GV_combine_ro:
  forall l t v v',
    GV l @ t |-r-> v  ** GV l @ t |-r->v' ==> GV l @ t |-> v ** [|encode_val t v = encode_val t v' |].
Proof.
  intros.
  sep auto.
  eapply GV_combine_ro_p1.
  eauto.
  eapply GV_combine_ro_p2.
  eauto.
Qed.

Lemma GV_combine_ro_frm_p1:
  forall l t v v' p,
    GV l @ t |-r-> v  ** GV l @ t |-r->v' ** p ==> GV l @ t |-> v  ** p.
Proof.
  intros.
  sep lift 3%nat in H.
  sep lift 2%nat .
  eapply StarMono.
  intro.
  intros; eauto.
  intro.
  intros.
  eapply GV_combine_ro_p1.
  eauto.
  eauto.
Qed.

Lemma GV_combine_ro_frm_p2:
  forall l t v v' p s,
    s|=GV l @ t |-r-> v  ** GV l @ t |-r->v' ** p ->
    encode_val t v = encode_val t v' .
Proof.
  intros.
  unfold Agvarmapsto in *.
  sep normal in H.
  sep destruct H.
  assert ( x0 = x).
  sep lift 3%nat in H.
  apply GR_addr_eq_frm in H.
  unfold addrval_to_addr in H.
  inverts H.
  auto.
  subst x0.

  eapply PV_combine_ro_frm_p2.
  sep lifts (4::2::nil)%nat in H.
  eauto.
Qed.

Lemma GV_combine_ro_frm:
  forall l t v v' p,
    GV l @ t |-r-> v  ** GV l @ t |-r->v' ** p ==> GV l @ t |-> v ** [|encode_val t v = encode_val t v' |] ** p.
Proof.
  intros.
  sep lift 3%nat in H.
  sep lift 3%nat .
  eapply StarMono.
  intro.
  intros; eauto.
  intro.
  intros.
  apply GV_combine_ro.
  eauto.
  auto.
Qed.


Lemma GV_separate_rw:
  forall l t v ,
    GV l @ t |-> v ==> GV l @ t |-r-> v  ** GV l @ t |-r->v .
Proof.
  intros.
  unfold Agvarmapsto in *.
  sep normal.
  sep destruct H.
  sep eexists.
  sep lift 2%nat in H.
  apply PV_separate_rw_frm in H.
  sep_cancel 1%nat 2%nat.
  sep_cancel 1%nat 3%nat.
  destruct s as [[[[[[]]]]]].
  
  simpl in *.
  simpljoin.
  do 6 eexists.
  splits ;eauto.
  getempenv.
  getempenv.
Qed.

Lemma GV_separate_rw_frm:
  forall l t v  p,
     GV l @ t |-> v ** p ==>  GV l @ t |-r-> v  ** GV l @ t |-r->v ** p .
Proof.
  intros.
  sep lift 2%nat in H.
  sep lift 3%nat .
  eapply StarMono.
  intro.
  intros; eauto.
  intro.
  intros.
  apply GV_separate_rw.
  eauto.
  auto.
Qed.


Lemma mapstoval_change_val:
  forall l t b v v',
    encode_val t v = encode_val t v'  ->
    l # t |=> v @ b <==> l#t |=> v' @ b .
Proof.
  intros.
  split.
  intros.
  simpl in *.
  unfold mapstoval in *.
  simpljoin.
  destruct s as [[[[[[]]]]]].
  simpl in *.
  rewrite <- H.
  splits; auto.
  eexists; splits; eauto.
  rewrite <- H.
  auto.
  intros.
  simpl in *.
  unfold mapstoval in *.
  simpljoin.
  destruct s as [[[[[[]]]]]].
  simpl in *.
  rewrite H.
  splits; auto.
  eexists; splits; eauto.
Qed.


 
Lemma GV_change_val:
  forall l t b v v',
    encode_val t v = encode_val t v'  ->
    GV l @ t |=> v @ b  ==> GV l @ t |=> v' @b  .
Proof.
  intros.
  unfold Agvarmapsto in *.
  sep destruct H0.
  sep eexists.
  sep lift 2%nat in H0.
  sep lift 2%nat.
  eapply StarMono.
  intro.
  intros.
  eapply PV_change_val.
  eauto.
  eauto.
  eauto.
  eauto.
Qed.
 
 
Lemma GV_change_val_frm:
  forall l t b v v' p,
    encode_val t v = encode_val t v'  ->
    GV l @ t |=> v @ b **p ==> GV l @ t |=> v' @b **p .
Proof.
  intros.
  sep lift 2%nat in H0.
  sep lift 2%nat.
  eapply StarMono.
  intro.
  eauto.
  apply GV_change_val.
  eauto.
  auto.
Qed.


Lemma GV_combine_ro':
  forall l t v v',
    encode_val t v = encode_val t v' ->
    GV l @ t |-> v ==> GV l @ t |-r-> v ** GV l @ t |-r-> v'  .
Proof.
  intros.
  apply GV_separate_rw in H0.
  sep_cancel 1%nat 1%nat.
  eauto.
  auto.
  eapply GV_change_val.
  eauto.
  auto.
Qed.

Lemma GV_combine_ro'_frm:
  forall l t v v' p,
    encode_val t v = encode_val t v' ->
    GV l @ t |-> v ** p ==> GV l @ t |-r-> v ** GV l @ t |-r-> v'  ** p.
Proof.
  intros.
  sep lift 2%nat in H0.
  sep lift 3%nat.
  eapply StarMono.
  intro.
  eauto.
  apply GV_combine_ro'.
  auto.
  auto.
Qed.  

