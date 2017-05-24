Require Import ucos_include. 
Require Import oscore_common.
Require Import OSQPostPure.
Require Import inv_prop.

Open Scope code_scope.
Open Scope Z_scope.
Open Scope int_scope.
Open Scope list_scope.

(*lemmas*)
Lemma dllseg_vptr :
  forall s head headprev tail tailnext l t pre next P x1,
    s |= dllseg head headprev tail (Vptr x1) l t pre next ** P -> tailnext <> Vnull -> exists x, head = Vptr x.
Proof.
  intros.
  destruct l.
  simpl in H; simpljoin.
  eauto.

  unfold dllseg in H; fold dllseg in H.
  unfold node in H.
  simpl in H; simpljoin.
  eauto.
Qed.


Lemma rule_type_val_match_int8_intro :
  forall i,
    Int.unsigned i <= 255 -> rule_type_val_match Int8u (Vint32 i) = true.
Proof.
  intros.
  simpl.
  unfold Byte.max_unsigned; simpl.
  apply Z.leb_le in H.
  rewrite H; auto.
Qed.


Lemma OSMapVallist_bound :
  forall n (i:int32),
    (n < 8)%nat -> exists i, nth_val' n OSMapVallist = Vint32 i /\ (Int.unsigned i) <= 128. 
Proof.
  intros.
  destruct n.
  simpl; exists ($1); split; mauto.
  destruct n.
  simpl; exists ($2); split; mauto.
  destruct n.
  simpl; exists ($4); split; mauto.
  destruct n.
  simpl; exists ($8); split; mauto.
  destruct n.
  simpl; exists ($16); split; mauto.
  destruct n.
  simpl; exists ($32); split; mauto.
  destruct n.
  simpl; exists ($64); split; mauto.
  destruct n.
  simpl; exists ($128); split; mauto.
  omega.
Qed.

Lemma RL_Tbl_Grp_P_update_nth_val_or :
  forall rtbl rgrp prio x y bitx bity row,
    RL_Tbl_Grp_P rtbl rgrp ->
    0 <= Int.unsigned prio < 64 ->
    array_type_vallist_match Int8u rtbl ->
    length rtbl = 8%nat ->
    rule_type_val_match Int8u rgrp = true ->
    y = (Z.to_nat (Int.unsigned (prio>>ᵢ $ 3))) ->
    row = (nth_val' y rtbl) ->
    x = (Z.to_nat (Int.unsigned (prio&ᵢ$ 7))) ->
    bitx = (nth_val' x OSMapVallist) ->
    bity = (nth_val' y OSMapVallist) ->
    RL_Tbl_Grp_P (update_nth_val y rtbl (val_inj (or row bitx))) (val_inj (or rgrp bity)).
Proof.
  intros.
  unfold RL_Tbl_Grp_P; intros.
  unfold RL_Tbl_Grp_P in H.
  
  assert(exists row, nth_val' y rtbl = Vint32 row /\ Int.unsigned row <= 255).
  apply array_int8u_nth_lt_len; auto.
  substs.
  rewrite H2.
  clear - H0.
  mauto.

  destruct H12 as (row' & nth_val'_row & row_le_255).
  rewrite nth_val'_row in H5.
  inverts H5.

  assert(exists bitx, nth_val' x OSMapVallist = Vint32 bitx /\ Int.unsigned bitx <= 128).
  eapply OSMapVallist_bound; auto.
  clear - H6 H0.
  substs.
  eapply z_le_7_imp_n.
  mauto.
  destruct H5 as (bitx' & nth_val_bitx & bitx_le_128).
  rewrite nth_val_bitx in H7; inverts H7.
  clear H5.

  assert(exists bity, nth_val' y OSMapVallist = Vint32 bity /\ Int.unsigned bity <= 128).
  eapply OSMapVallist_bound; auto.
  clear - H4 H0.
  substs.
  eapply z_le_7_imp_n.
  mauto.
  destruct H5 as (bity' & nth_val_bity & bity_le_128).
  rewrite nth_val_bity in H8; inverts H8.
  clear H5.

  assert(exists rgrp', rgrp = Vint32 rgrp' /\ Int.unsigned rgrp' <= 255).
  clear - H3.
  unfolds in H3.
  destruct rgrp; tryfalse.
  eexists; split; eauto.
  apply int_true_le255; auto.
  destruct H5 as (rgrp' & Hxx & rgrp_le255).
  subst rgrp.
  
  assert(y = n \/ y <> n) by tauto.
  destruct H5.
  substs.
  lets Hins : nth_upd_eq H10.
  simpl in Hins.
  simpl in H11.
  inverts Hins.
  inverts H11.
  
  rewrite Int.and_commut.
  rewrite Int.and_or_distrib.
  split.
  split.
  intros.
  apply int_or_zero_split in H4.
  destruct H4.
  lets Hf : math_prop_neq_zero H0.
  assert(bity' = ($ 1<<ᵢ(prio >>ᵢ $ 3))).
  eapply math_mapval_core_prop; auto.
  clear - H0.
  mauto.
  substs.
  tryfalse.

  intros.
  apply int_or_zero_split in H4.
  destruct H4.
  assert(bitx' = ($ 1<<ᵢ(prio&ᵢ$ 7))).
  eapply math_mapval_core_prop; auto.
  clear - H0.
  mauto.
  substs.
  symmetry in H6.
  apply math_prop_neq_zero2 in H6.
  tryfalse.
  auto.
  
  split.
  intros.
  assert(bitx' = ($ 1<<ᵢ(prio&ᵢ$ 7))).
  eapply math_mapval_core_prop; auto.
  clear - H0.
  mauto.
  substs.
  apply int_ltu_true; auto.
  intros.
  rewrite math_prop_eq; auto.
  assert(bity' = ($ 1<<ᵢ(prio >>ᵢ $ 3))).
  eapply math_mapval_core_prop; auto.
  clear - H0.
  mauto.
  substs.
  rewrite Int.and_idem.
  rewrite Int.or_commut.
  rewrite Int.or_and_absorb.
  auto.

  subst y x.
  assert(n <> Z.to_nat (Int.unsigned (prio >>ᵢ $ 3))).
  auto.
  lets Hex : nth_upd_neq H4 H10.
  simpl in H11.
  inverts H11.

  assert (Vint32 rgrp' = Vint32 rgrp') by auto.
  lets Hexz : H H9 Hex H6.
  destruct Hexz as (He1 & He2).
  split.
  split.
  intros.
  apply He1.
  rewrite Int.and_commut in H7.
  rewrite Int.and_or_distrib in H7.
  
  lets Hc : math_and_zero H0 H9 H4.
  assert(bity' = ($ 1<<ᵢ(prio >>ᵢ $ 3))).
  eapply math_mapval_core_prop; auto.
  clear - H0.
  mauto.
  substs.
  rewrite Hc in H7.
  rewrite Int.or_zero in H7.
  rewrite Int.and_commut.
  auto.
  intros.
  lets Hc : math_and_zero H0 H9 H4.
  rewrite Int.and_commut .
  rewrite Int.and_or_distrib .
  assert(bity' = ($ 1<<ᵢ(prio >>ᵢ $ 3))).
  eapply math_mapval_core_prop; auto.
  clear - H0.
  mauto.
  substs.
  rewrite Hc.
  rewrite Int.or_zero.
  rewrite Int.and_commut.
  apply He1; auto.
  lets Hc : math_and_zero H0 H9 H4.
  split.
  intros.
  apply He2.
  assert(bity' = ($ 1<<ᵢ(prio >>ᵢ $ 3))).
  eapply math_mapval_core_prop; auto.
  clear - H0.
  mauto.
  substs.
  rewrite Int.and_commut in H7.
  rewrite Int.and_or_distrib in H7.
  rewrite Hc in H7.
  rewrite Int.or_zero in H7.
  rewrite Int.and_commut.
  auto.
  intros.
  rewrite Int.and_commut .
  rewrite Int.and_or_distrib .
  assert(bity' = ($ 1<<ᵢ(prio >>ᵢ $ 3))).
  eapply math_mapval_core_prop; auto.
  clear - H0.
  mauto.
  substs.
  rewrite Hc.
  rewrite Int.or_zero.
  rewrite Int.and_commut.
  apply He2; auto.
Qed.

Lemma RL_RTbl_PrioTbl_P_update_nth_val :
  forall prio rtbl ptbl vhold tid row bitx,
    0 <= Int.unsigned prio < 64 ->
    length ptbl = 64%nat ->
    array_type_vallist_match (Tptr os_ucos_h.OS_TCB) ptbl ->
    length rtbl = 8%nat ->
    array_type_vallist_match Tint8 rtbl ->
    RL_RTbl_PrioTbl_P rtbl ptbl vhold ->
    tid <> vhold ->
    nth_val' (Z.to_nat (Int.unsigned (prio >>ᵢ $ 3))) rtbl = Vint32 row ->
    nth_val' (Z.to_nat (Int.unsigned (prio&ᵢ$ 7))) OSMapVallist = Vint32 bitx ->
    
    RL_RTbl_PrioTbl_P
      (update_nth_val (Z.to_nat (Int.unsigned (prio >>ᵢ $ 3))) rtbl
                      (val_inj (or (Vint32 row) (Vint32 bitx))))
      (update_nth_val (Z.to_nat (Int.unsigned prio)) ptbl (Vptr tid)) vhold.
Proof.
  intros.
  unfold RL_RTbl_PrioTbl_P in *.
  intros.
  assert (p = prio \/ p <> prio) by tauto.
  destruct H10.
  substs.
  exists tid.
  split; auto.
  apply nth_val'_imp_nth_val_vptr.
  rewrite len_lt_update_get_eq; auto.
  rewrite H0.
  clear - H.
  mauto.

  lets Hx: new_rtbl.prio_set_rdy_in_tbl_rev p prio rtbl H8 H.
  change (nat_of_Z OS_RDY_TBL_SIZE) with 8%nat in Hx.
  lets Hx2: Hx H3 H2 H10.
  unfold new_rtbl.set_rdy in Hx2.
  rewrite <- H6 in H9.
  assert (bitx = ($ 1<<ᵢ(prio&ᵢ$ 7))).
  eapply math_mapval_core_prop; eauto.
  clear - H.
  mauto.
  substs.
  apply Hx2 in H9.
  apply H4 in H9; auto.
  destruct H9.
  exists x.
  destruct H9.
  split; auto.
  apply nth_upd_neqrev; auto.
  clear - H10 H H8.
  assert (Int.unsigned p <> Int.unsigned prio).
  intro.
  apply H10.
  assert (Int.repr (Int.unsigned p) = Int.repr (Int.unsigned prio)).
  rewrite H0; auto.
  do 2 rewrite Int.repr_unsigned in H1.
  auto.
  intro.
  apply H0.
  apply Z2Nat.inj.
  mauto.
  mauto.
  auto.
Qed.

Lemma Astruct_PV_dup_false :
  forall s p x1 tail v P,
    s
      |= Astruct p OS_TCB_flag
      (x1::tail) **
      PV p @ Tint8 |-> v ** P ->
    False.
Proof.
  intros.
  destruct_s s.
  unfold Astruct in H.
  unfold OS_TCB_flag in H.
  unfold Astruct' in H.
  destruct p.
  sep remember (1::3::nil)%nat in H.
  clear HeqH0.
  assert ((b, i2) <> (b, i2)).
  eapply pv_false; eauto.
  unfold array_struct; intro.
  destruct H1; simpljoin; tryfalse.
  destruct H1; simpljoin; tryfalse.
  unfold array_struct; intro.
  destruct H1; simpljoin; tryfalse.
  destruct H1; simpljoin; tryfalse.
  tryfalse.
Qed.

Lemma array_type_vallist_match_vptr_update_nth_val :
  forall l n t a,
         array_type_vallist_match (Tptr t ) l -> (n < (length l))%nat ->
        (* (Int.unsigned x) <= Byte.max_unsigned -> *)
         array_type_vallist_match (Tptr t) (update_nth_val n l (Vptr a)).
Proof.
  inductions l; intros.
  simpl; auto.

  destruct n.
  simpl.
  simpl in H; simpljoin.
  auto.

  simpl in H.
  simpl.
  simpljoin; split.
  auto.
  simpl in H0.
  assert(n < length l)%nat by omega.
  eapply IHl; eauto.
Qed.

(*
Lemma array_type_vallist_match_int8u_update_nth_val :
  forall l n x,
    array_type_vallist_match Int8u l -> (n < (length l))%nat ->
    (Int.unsigned x) <= Byte.max_unsigned ->
    array_type_vallist_match Int8u (update_nth_val n l (Vint32 x)).
Proof.
  inductions l; intros.
  simpl; auto.

  destruct n.
  simpl.
  apply Z.leb_le in H1.
  rewrite H1.
  simpl in H.
  simpljoin.
  auto.

  simpl in H.
  simpl.
  simpljoin.
  auto.
  simpl in H0.
  assert(n < length l)%nat by omega.
  eapply IHl; eauto.
Qed.
*)
(*end of lemmas*)
