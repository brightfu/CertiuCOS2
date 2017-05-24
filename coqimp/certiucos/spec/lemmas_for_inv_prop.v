(*
  This file contains some lemmas defined by zhanghui,
  these lemmas should be moved to corresponding files later.
 *)
Require Import include_frm.
Require Import os_ucos_h.
Require Import sep_auto.

Require Import join_lib.
(*Require Import base_tac.
Require Import os_inv.
Require Import os_code_defs.
Require Import abs_op.
Require Import Maps.
 *)


Local Open Scope Z_scope.
Local Open Scope int_scope.


Lemma rule_type_val_match_encode_val_length_eq :
  forall t v1 v2 vl1 vl2,
    rule_type_val_match t v1 = true ->
    rule_type_val_match t v2 = true ->
    encode_val t v1 = vl1 ->
    encode_val t v2 = vl2 ->
    length vl1 = length vl2.
Proof.
  intros.
  destruct t, v1, v2;
    simpl in H, H0; tryfalse;
    simpl in H1, H2; try(destruct a); try (destruct a0); substs; auto.
Qed.

Lemma join_sig_eq_auto :
  forall (A B T : Type) (MC : PermMap A B T) l a b m1 m2 m3 x1 x2,
    usePerm = true ->
    isRw a = false ->
    isRw b = false ->
    join (sig l a) x1 m1 ->
    join (sig l b) x2 m2 ->
    join m1 m2 m3 ->
    a = b.
  intros.
  let i := calc_ins_for_context in
  infer' i l; crush.
Qed.  

Lemma join_sig_eq :
  forall l a b m1 m2 m3 x1 x2,
    join (sig l (false, a)) x1 m1 ->
    join (sig l (false, b)) x2 m2 ->
    join m1 m2 m3 ->
    a = b.
  intros.
  assert ((false, a) = (false, b)).
  {
    eapply join_sig_eq_auto; ica.
  }
  inverts H2; auto.
Qed.  

Lemma ptomvallist_false_join_vl_eq :
  forall vl1 vl2 l m1 m2 m3,
    ptomvallist l false vl1 m1 ->
    ptomvallist l false vl2 m2 ->
    length vl1 = length vl2 ->
    join m1 m2 m3 ->
    vl1 = vl2.
Proof.
  inductions vl1; intros.
  destruct vl2; auto.
  simpl in H1; inversion H1.

  destruct vl2.
  simpl in H1; inversion H1.

  simpl in H1; inverts H1.
  simpl in H; destruct l.

  do 3 destruct H; destruct H1.
  simpl in H0; do 3 destruct H0; destruct H5.

  unfold ptomval in H1, H5; substs.
  assert(a = m).
  eapply join_sig_eq; eauto.

  substs.
  assert(vl1 = vl2).
  assert(exists mx, join x0 x2 mx).
  geat.
  destruct H1.
  apply IHvl1 with (m1:=x0) (m2:=x2) (m3:=x) (l:=(b,o+1)); auto.
  substs; auto.
Qed.

Lemma join_sig_false_sig_true_auto :
  forall (A B T : Type) (MC : PermMap A B T) l a m1 m2 m x1 x2 x,
    usePerm = true ->
    isRw a = false ->
    join m1 m2 m ->
    join (sig l a) x1 m1 ->
    join (sig l a) x2 m2 ->
    join x1 x2 x ->
    join (sig l (flip a)) x m.
  Ltac infer ::= infer_v.
  hy.
  Ltac infer ::= infer_q.
Qed.
  

Lemma join_sig_false_sig_true :
  forall l a m1 m2 m x1 x2 x,
    join m1 m2 m ->
    join (sig l (false, a)) x1 m1 ->
    join (sig l (false, a)) x2 m2 ->
    join x1 x2 x ->
    join (sig l (true, a)) x m.
Proof.
  intros.
  assert (join (sig l (flip (false, a))) x m).
  {
    eapply join_sig_false_sig_true_auto; ica.
  }
  unfold flip in H3.
  simpl in H3.
  unfold HalfPermMap.flip in H3.
  simpl in H3.
  auto.
Qed.  

Lemma ptomvallist_false_true :
  forall vl l m1 m2 m3,
    ptomvallist l false vl m1 ->
    ptomvallist l false vl m2 ->
    join m1 m2 m3 ->
    ptomvallist l true vl m3.
Proof.
  inductions vl; intros.
  simpl in *; substs.
  geat.

  destruct l.
  unfold ptomvallist in H, H0; fold ptomvallist in H, H0.
  do 3 destruct H; destruct H2.
  do 3 destruct H0; destruct H4.
  unfold ptomval in *.
  
  substs.
  assert(exists m, join x0 x2 m).
  geat.
  destruct H2.
  unfold ptomvallist; fold ptomvallist.
  exists (sig (b, o) (true, a)) x.
  split.

  eapply join_sig_false_sig_true; eauto.
  split.
  unfolds; auto.
  lets Hx: IHvl H3 H5 H2; auto.
Qed.


Lemma byte_repr_int_unsigned_eq :
  forall i1 i2,
    Int.unsigned i1 <= Byte.max_unsigned ->
    Int.unsigned i2 <= Byte.max_unsigned ->
    Byte.repr (Int.unsigned i1) = Byte.repr (Int.unsigned i2) ->
    i1 = i2.
Proof.
  intros.
  assert(Byte.unsigned (Byte.repr (Int.unsigned i1)) = Byte.unsigned (Byte.repr (Int.unsigned i2))).
  rewrite H1; auto.
  do 2 rewrite Byte.unsigned_repr in H2.
  assert(Int.repr (Int.unsigned i1) = Int.repr (Int.unsigned i2)).
  rewrite H2; auto.
  do 2 rewrite Int.repr_unsigned in H3.
  auto.
  split; auto.
  pose proof Int.unsigned_range i2.
  destruct H3; auto.
  split; auto.
  pose proof Int.unsigned_range i1.
  destruct H3; auto.
  split; auto.
  pose proof Int.unsigned_range i1.
  destruct H3; auto.
Qed.

Lemma byte_repr_eq :
  forall z1 z2,
    0 <= z1 <= Byte.max_unsigned ->
    0 <= z2 <= Byte.max_unsigned ->
    Byte.repr z1 = Byte.repr z2 ->
    z1 = z2.
Proof.
  intros.
  assert(Byte.unsigned (Byte.repr z1) = Byte.unsigned (Byte.repr z2)).
  rewrite H1; auto.
  do 2 rewrite Byte.unsigned_repr in H2; auto.
Qed.

Lemma div_256_byte_repr_eq :
  forall z1 z2,
    z1 / 256 = z2 / 256 ->
    Byte.repr z1 = Byte.repr z2 ->
    z1 = z2.
Proof.
  intros.
  assert (Byte.unsigned (Byte.repr z1) = Byte.unsigned (Byte.repr z2)).
  rewrite H0; auto.
  do 2 rewrite Byte.unsigned_repr_eq in H1.
  unfold Byte.modulus in H1.
  unfold two_power_nat in H1; simpl in H1.
  clear H0.
  assert(256 <> 0) by omega.
  pose proof Z.div_mod z1 256 H0.
  pose proof Z.div_mod z2 256 H0.
  rewrite H in H2.
  rewrite H1 in H2.
  rewrite <- H2 in H3.
  auto.
Qed.

Lemma z_le_int16_max_div_256_byte_max :
  forall z,
    z <= Int16.max_unsigned ->
    z / 256  <= Byte.max_unsigned.
Proof.
  intros.
  unfold Int16.max_unsigned in H.
  simpl in H.
  unfold Byte.max_unsigned; simpl.
  
  replace 255 with (65535 / 256).
  apply Z.div_le_mono.
  omega.
  auto.
  compute; auto.
Qed.

Lemma zero_le_int_unsigned_div_256 :
  forall i,
    0 <= Int.unsigned i / 256.
Proof.
  intros.
  pose proof Int.unsigned_range i.
  destruct H.
  replace 0 with (0 / 256).
  apply Z.div_le_mono.
  omega.
  auto.
  compute; auto.
Qed.

Lemma zero_le_int_unsigned_div_256_256_256 :
  forall i,
    0 <= Int.unsigned i / 256 / 256 / 256.
Proof.
  intros.
  pose proof Int.unsigned_range i.
  destruct H.
  replace 0 with (0 / 256 / 256 / 256).
  apply Z.div_le_mono.
  omega.
  apply Z.div_le_mono.
  omega.
  apply Z.div_le_mono.
  omega.
  auto.
  compute; auto.
Qed.

Lemma z_le_int_max_div_256_256_256_byte_max :
  forall z,
    z <= Int.max_unsigned ->
    z / 256 / 256 / 256 <= Byte.max_unsigned.
Proof.
  intros.
  unfold Int.max_unsigned in H.
  simpl in H.
  unfold Byte.max_unsigned; simpl.
  
  replace 255 with (4294967295 / 256 / 256 / 256).
  apply Z.div_le_mono.
  omega.
  apply Z.div_le_mono.
  omega.
  apply Z.div_le_mono.
  omega.
  auto.
  compute; auto.
Qed.

Lemma rule_type_val_match_encode_val_eq :
  forall t v1 v2,
    rule_type_val_match t v1 = true ->
    rule_type_val_match t v2 = true ->
    encode_val t v1 = encode_val t v2 ->
    v1 = v2.
Proof.
  intros.
  destruct t, v1, v2;
    simpl in H, H0; tryfalse;
    auto;
    simpl in H1; try (destruct a); try (destruct a0); tryfalse.
  remember(Byte.repr (Int.unsigned i)) as X;
    remember(Byte.repr (Int.unsigned i0)) as Y.
  inversion H1; substs.
  
  destruct (Int.unsigned i <=? Byte.max_unsigned) eqn : eq1; tryfalse.
  destruct (Int.unsigned i0 <=? Byte.max_unsigned) eqn : eq2; tryfalse.    
  apply byte_repr_int_unsigned_eq in H3; substs; auto.
  apply Z.leb_le in eq1.
  auto.
  apply Z.leb_le in eq2.
  auto.

  remember (Byte.repr (Int.unsigned i)) as X1.
  remember (Byte.repr (Int.unsigned i / 256)) as X2.
  remember (Byte.repr (Int.unsigned i0)) as Y1.
  remember (Byte.repr (Int.unsigned i0 / 256)) as Y2.
  inverts H1; substs.

  destruct (Int.unsigned i <=? Int16.max_unsigned) eqn : eq1; tryfalse.
  destruct (Int.unsigned i0 <=? Int16.max_unsigned) eqn : eq2; tryfalse.
  apply Z.leb_le in eq1.
  apply Z.leb_le in eq2.
  
  apply byte_repr_eq in H3.

  assert(Int.unsigned i = Int.unsigned i0).
  eapply div_256_byte_repr_eq; eauto.
  assert(Int.repr (Int.unsigned i) = Int.repr (Int.unsigned i0)).
  rewrite H1; auto.
  do 2 rewrite Int.repr_unsigned in H4.
  substs; auto.
  
  split.
  apply zero_le_int_unsigned_div_256; auto.
  apply z_le_int16_max_div_256_byte_max; auto.

  split.
  apply zero_le_int_unsigned_div_256; auto.
  apply z_le_int16_max_div_256_byte_max; auto.

  remember (Byte.repr (Int.unsigned i)) as X1.
  remember (Byte.repr (Int.unsigned i / 256)) as X2.
  remember (Byte.repr (Int.unsigned i / 256 / 256)) as X3.
  remember (Byte.repr (Int.unsigned i / 256 / 256 / 256)) as X4.    
  remember (Byte.repr (Int.unsigned i0)) as Y1.
  remember (Byte.repr (Int.unsigned i0 / 256)) as Y2.
  remember (Byte.repr (Int.unsigned i0 / 256 / 256)) as Y3.
  remember (Byte.repr (Int.unsigned i0 / 256 / 256 / 256)) as Y4.
  inverts H1; substs.

  apply byte_repr_eq in H5.
  lets Hx: div_256_byte_repr_eq H5 H4.
  lets Hx1: div_256_byte_repr_eq Hx H3.
  lets Hx2: div_256_byte_repr_eq Hx1 H2.
  assert(Int.repr (Int.unsigned i) = Int.repr (Int.unsigned i0)).
  rewrite Hx2; auto.
  do 2 rewrite Int.repr_unsigned in H1; substs; auto.

  split.
  apply zero_le_int_unsigned_div_256_256_256.

  apply z_le_int_max_div_256_256_256_byte_max; auto.
  apply Int.unsigned_range_2.

  split.
  apply zero_le_int_unsigned_div_256_256_256.
  apply z_le_int_max_div_256_256_256_byte_max; auto.
  apply Int.unsigned_range_2.

  inverts H1; substs; auto.
  inverts H1; substs; auto.
Qed.


(** already in os_inv.v **)
(* Lemma node_OS_TCB_dup_false : *)
(*   forall p a1 a2 P s, *)
(*     s |= node p a1 OS_TCB ** node p a2 OS_TCB ** P -> *)
(*     False. *)
(* Proof. *)
(* (* *)
(*   intros. *)
(*   unfold node in H. *)
(*   unfold Astruct in H. *)
(*   sep normal in H. *)
(*   do 2 destruct H. *)
(*   sep split in H. *)
(*   unfold OS_TCB in H. *)
(*   unfold Astruct' in H. *)
(*   mytac. *)
(*   destruct a1. *)
(*   simpl in H2; tryfalse. *)
(*   destruct a2. *)
(*   simpl in H3; tryfalse. *)
(*   sep normal in H. *)
(*   sep remember (1::3::nil)%nat in H. *)
(*   clear HeqH0. *)
(*   inverts H1. *)
(*   sep remember (3::nil)%nat in H. *)
(*   destruct_s s. *)
(*   simpl_sat H; mytac. *)
(*   simpl in H2, H3; mytac. *)
(*   clear - H H2 H8. *)
(*   simpl in H8; mytac. *)
(*   apply MemMod.join_disj_meq in H1; destruct H1. *)
(*   Require Import common. *)
(*   eapply mapstoval_disj_false with (m1:=x0) (m2:=x2); eauto. *)
(*   simpl; omega. *)
(* Qed. *)
(*  *) *)
(* Admitted. *)

Lemma join_sig_false_true_auto :
  forall (A B T : Type) (MC : PermMap A B T) l a,
    usePerm = true ->
    isRw a = false ->
    join (sig l a) (sig l a) (sig l (flip a)).
  intros.
  hy.
Qed.

Lemma join_sig_false_true :
  forall l a,
    join (sig l (false, a)) (sig l (false, a)) (sig l (true, a)).
Proof.
  intros.
  assert (flip (false, a) = (true, a)).
  {
    unfold flip; simpl.
    ica.
  }
  eapply join_sig_false_true_auto; ica.
Qed.  

Lemma join_split :
  forall (m1:mem) m2 m m11 m12 m21 m22,
    join m1 m2 m ->
    join m11 m12 m1 ->
    join m21 m22 m2 ->
    exists mx1 mx2, join m11 m21 mx1 /\ join m12 m22 mx2 /\ join mx1 mx2 m.
  intros.
  geat.
Qed.

Lemma ptomvallist_split :
  forall vl l m,
    ptomvallist l true vl m ->
    exists m1 m2, ptomvallist l false vl m1 /\ ptomvallist l false vl m2 /\ join m1 m2 m.
Proof.
  inductions vl; intros.
  simpl in H; substs.
  simpl.
  do 2 eexists; splits; eauto.
  geat.

  unfold ptomvallist in H; fold ptomvallist in H; destruct l.
  simpljoin.
  unfold ptomvallist; fold ptomvallist.

  unfold ptomval in H0.
  
  lets Hx: join_sig_false_true (b, o) a.
  lets Hx1: IHvl H1.
  simpljoin.
  
  lets Hx2: join_split H Hx H4.
  simpljoin.
  unfold ptomval.
  exists x x3.
  split.
  do 2 eexists; splits; eauto.
  split; auto.
  do 2 eexists;  eauto.
Qed.



Lemma read_only_split_vptr:
  forall s x t v P,
    s |= GV x @ Tptr t |-> Vptr v ** P ->
    s |= (GV x @ Tptr t |-r-> Vptr v) **
      (GV x @ Tptr t |-r-> Vptr v) ** P.
Proof.
  intros.
  destruct_s s.
  simpl in H.
  simpljoin.
  unfold mapstoval in H9.
  simpljoin.
  
  lets Hx: ptomvallist_split H1.
  simpljoin.
  simpl.
  assert(x8 = x0).
  geat.
  substs.
  
  assert(exists xx, join x2 xx m /\ join x5 x1 xx).
  geat.
  destruct H9.
  destruct H9.
  exists x2 x6 m x3 x4 o.
  splits; eauto.
  exists x13 empmem x2 x2 empabst empabst; exists x3.
  splits; eauto.
  geat.
  unfold emposabst in *.
  substs.
  geat.
  eexists.
  splits; eauto.
  unfolds; auto.
  unfolds.
  eexists; splits; eauto.
  unfolds; auto.

  exists x5 x1 x6 empabst o o.
  splits; eauto.
  unfold emposabst in *.
  substs.
  geat.
  geat.

  exists x13 empmem x5 x5 empabst empabst; exists empabst.
  splits; eauto.
  geat.
  geat.
  eexists; splits; eauto.
  unfolds; auto.
  unfolds; eexists; splits; eauto.
  unfolds; auto.
  unfold emposabst in *; subst.
  assert(x4 = o).
  geat.
  substs; auto.
Qed.

Lemma ptomval_false_join_eq :
  forall l v1 v2 m1 m2 m3,
    ptomval l false v1 m1 -> ptomval l false v2 m2 ->
    join m1 m2 m3 -> v1 = v2.
Proof.
  intros.
  unfold ptomval in *.
  substs.
  unfold join in H1.
  simpl in H1.
  unfold HalfPermMap.join in H1.
  destruct H1.
  pose proof H l.
  unfold sig in H1; simpl in H1.
  pose proof map_get_sig l (false, v1).
  unfold get in H2; simpl in H2.
  unfold HalfPermMap.get in H2.
  unfold sig in H2; simpl in H2.
  rewrite H2 in H1.
  pose proof map_get_sig l (false, v2).
  unfold get in H3; simpl in H3.
  unfold HalfPermMap.get in H3.
  unfold sig in H3; simpl in H3.
  rewrite H3 in H1.
  auto.
Qed.
(* end *)
