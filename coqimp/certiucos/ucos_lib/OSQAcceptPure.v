Require Import ucos_include.

Open Scope code_scope.
Open Scope Z_scope.
Open Scope int_scope.

Lemma rh_tcbls_mqls_p_getmsg_hold:
  forall mqls tcbls ct a v vl qmax wl,
    RH_TCBList_ECBList_P mqls tcbls ct ->
    EcbMod.get mqls a =
    Some
      (absmsgq (v:: vl) qmax, wl) -> 
    RH_TCBList_ECBList_P (EcbMod.set mqls a (absmsgq vl qmax, wl)) tcbls ct.
Proof.
  intros.
  unfold RH_TCBList_ECBList_P in *.
  destruct H as (Hr1 & Hr2 & Hr3 & Hr4).
  splits.
  destruct Hr1.
  splits; intros.
  destruct (tidspec.beq a eid) eqn : eq1.
  unfold get in *; simpl in *.
  lets Hts :  tidspec.beq_true_eq  eq1 .
  substs.
  rewrite EcbMod.set_a_get_a in H2; auto.
  destruct H2; inverts H2; eauto.
  rewrite EcbMod.set_a_get_a' in H2; auto.
  eapply H; eauto.
  destruct (tidspec.beq a eid) eqn : eq1.
  lets Hts :  tidspec.beq_true_eq  eq1 .
  substs.
  rewrite EcbMod.set_a_get_a; auto.
  apply H1 in H2; auto.
  do 4 destruct H2.
  unfold get in *; simpl in *.
  rewrite H2 in H0; inverts H0.
  eauto.
  rewrite EcbMod.set_a_get_a'; auto.
  eapply H1; eauto.
  destruct Hr2.
  splits; intros.
  destruct (tidspec.beq a eid) eqn : eq1.
    lets Hts :  tidspec.beq_true_eq  eq1; substs.
  rewrite EcbMod.set_a_get_a in H2; auto.
  destruct H2; inverts H2; eauto.
  rewrite EcbMod.set_a_get_a' in H2; auto.
  eapply H; eauto.
  destruct (tidspec.beq a eid) eqn : eq1.
    lets Hts :  tidspec.beq_true_eq  eq1 ; subst.
  rewrite EcbMod.set_a_get_a; auto.
  apply H1 in H2; auto.
  do 3 destruct H2.
  unfold get in *; simpl in *.
  rewrite H2 in H0; inverts H0.
  eauto.
  rewrite EcbMod.set_a_get_a'; auto.
  eapply H1; eauto.
  destruct Hr3.
  splits; intros.
  destruct (tidspec.beq a eid) eqn : eq1.
  lets Hts :  tidspec.beq_true_eq  eq1; substs.
  rewrite EcbMod.set_a_get_a in H2; auto.
  destruct H2; inverts H2; eauto.
  rewrite EcbMod.set_a_get_a' in H2; auto.
  eapply H; eauto.
  destruct (tidspec.beq a eid) eqn : eq1.
      lets Hts :  tidspec.beq_true_eq  eq1; substs.
  rewrite EcbMod.set_a_get_a; auto.
  apply H1 in H2; auto.
  do 3 destruct H2.
  unfold get in *; simpl in *.
rewrite H2 in H0; inverts H0.
  eauto.
  rewrite EcbMod.set_a_get_a'; auto.
  eapply H1; eauto.
  destruct Hr4.
  splits; intros.
  destruct (tidspec.beq a eid) eqn : eq1.
  lets Hts :  tidspec.beq_true_eq  eq1; substs.
  rewrite EcbMod.set_a_get_a in H2; auto.
  destruct H2; inverts H2; eauto.
  rewrite EcbMod.set_a_get_a' in H2; auto.
  eapply H; eauto.
  destruct (tidspec.beq a eid) eqn : eq1.
  lets Hts :  tidspec.beq_true_eq  eq1; substs.
  rewrite EcbMod.set_a_get_a; auto.
  apply H1 in H2; auto.
  do 4 destruct H2.
  unfold get in *; simpl in *.
  rewrite H2 in H0; inverts H0.
  eauto.
  rewrite EcbMod.set_a_get_a'; auto.
  eapply H1; eauto.

  
  elim H1; intros.
  unfold RH_TCBList_ECBList_MUTEX_OWNER in *.
  intros.

  assert (eid = a \/ eid <> a) by tauto.
  destruct H5; intros.
  subst eid.
  rewrite EcbMod.set_a_get_a in H4.
  inversion H4.
  apply CltEnvMod.beq_refl.
  rewrite EcbMod.set_a_get_a' in H4.
  eapply H3; eauto.
  apply tidspec.neq_beq_false; auto.
Qed.

Open Scope int_scope.
Lemma msgqnode_p_nomsg:
  forall qptr qst qend qin qout size qens qblk mblk ml A l,
    Int.ltu ($ 0) qens = false ->
    RLH_ECBData_P
      ( 
        DMsgQ l (qptr
                   :: qst
                   :: qend
                   :: qin
                   :: qout
                   :: Vint32 size :: Vint32 qens :: Vptr qblk :: nil)
              mblk ml) A ->
    exists qmax wl, A = (absmsgq nil qmax,wl).
Proof.
  intros.
  unfolds in H0.
  destruct A.
  destruct e; tryfalse.
  simp join.
  funfold H0.
  funfold H1.
  funfold H2.
  lets Heq : int_ltu_false_eq0 H.
  rewrite Heq in H1.
  apply eq_sym in H1.
  apply zof_nat_eq_zero_zero in H1.
  apply length_zero_nil in H1.
  subst l0.
  eauto.
Qed.


Lemma msgqnode_p_hold_end:
  forall b sti qens outi qend qptr qst qin qsize qblk  mblk ml hml hsize wl l,
    id_addrval qblk msgqueuetbl os_ucos_h.OS_Q_FREEBLK = Some (b, sti) -> 
    Int.ltu ($ 0) qens =true ->
    qend = Vptr (b, (outi +ᵢ  Int.mul ($ 1) ($ 4))) -> 
    WellformedOSQ
      (qptr
         :: qst
         :: qend
         :: qin
         :: Vptr (b, outi)
         :: Vint32 qsize :: Vint32 qens :: Vptr qblk :: nil) -> 
    RLH_ECBData_P
      (DMsgQ l
             (qptr
                :: qst
                :: qend
                :: qin
                :: Vptr (b, outi)
                :: Vint32 qsize :: Vint32 qens :: Vptr qblk :: nil)
             mblk ml)
      (absmsgq (nth_val' (Z.to_nat ((Int.unsigned outi - Int.unsigned sti) / 4)) ml
                         :: hml) hsize, wl) ->
    RLH_ECBData_P 
      (DMsgQ l
             (qptr
                :: qst
                :: qend
                :: qin
                :: qst
                :: Vint32 qsize
                :: Vint32 (qens -ᵢ $ 1) :: Vptr qblk :: nil)
             mblk ml ) (absmsgq hml hsize, wl).
Proof.
  introv Hid Hint Hqend Hwl Hrl .
  funfold Hwl.
  destruct Hrl.
  destruct H0 as (Hm1 & Hm2 & Hm3 & Hecb).
  funfold H.
  funfold Hm1.
  funfold Hm2.
  unfold arrayelem_addr_right in *.
  unfold qend_right, ptr_offset_right,ptr_minus,  distance in *.
  simp join.
  fsimpl.
  simpl in *.
  destruct x5.
  apply eq_sym in H5.
  subst i0.
  inverts Hid.
  remember ( i1+ᵢ($ 4+ᵢInt.zero)) as k.
  inverts H5.
  assert (Int.mul ($ 1) ($ 4) = $ 4).
  clear -i.
  mauto.
  rewrite H5 in *.
  rewrite <- H4 in *.
  rewrite Int.repr_unsigned in *.
  assert (Int.unsigned ($ 4) = 4)%Z.
  clear -i.
  mauto.
  rewrite H8 in *.
  clear H5 H8.
  splits.
  unfolds.
  do 7 eexists;splits; try solve [  unfolds; simpl; eauto].
  assert (Int.unsigned (Int.divu ($ 4-ᵢ$ 4) ($ 4)) = 0)%Z.
  clear.
  int auto.
  int auto.
  rewrite Zdiv_0_l.
  omega.
  simpl.
  rewrite Zdiv_0_l.
  omega.
  rewrite H5 in *.
  clear H5.
  splits.
  splits.
  introv Hlt.
  lets Hed :  math_le_xyz H1 H  H21; eauto.
  rewrite Int.repr_unsigned; eauto.    
  destruct Hed as   (Has & Hass & Hsd) .
  apply z_split in Has.
  destruct Has as [Has1 | Has2].
  lets Hef : int_ltu_eq_false Hint.
  apply H15 in Has1.
  destruct Has1.
  rewrite Hef in H5.
  destruct H5; tryfalse.
  destruct H5 as (Hs1 & Hs2).
  rewrite <- Hass in Hs2.
 
  remember ( ∘(Int.unsigned (Int.divu (outi-ᵢ$ 4) ($ 4)))) as N.
  remember (∘(Int.unsigned (Int.divu (i-ᵢ$ 4) ($ 4))))  as M.
   destruct H13 as (His & Hsi).
  lets Hlss : isptr_length_nth His.
  rewrite vallist_seg_Sn in Hs2.
  simpl in Hs2.
  inverts Hs2; auto.
  rewrite Int.unsigned_repr in Hsd.
  rewrite <- Hsd in Hlss.
  auto.
  clear -N.
  mauto.
  apply H14 in Has2.
  rewrite <- Hass in Has2.
  rewrite vallist_seg_Sn in Has2.
  simpl in Has2.
  inverts Has2; auto.
  rewrite Int.unsigned_repr in Hsd.
  rewrite Hsd .
   destruct H13 as (His & Hsi).
  lets Hlss : isptr_length_nth His.
  auto.
  clear -l.
  mauto.
  introv Hf.
  assert ( 0 <= Int.unsigned (Int.divu (i-ᵢ$ 4) ($ 4)) )%Z.
  apply Int.unsigned_range.
  false.
  omega.
  introv Hf.
  lets Hed :  math_le_xyz H1 H  H21; eauto.
  rewrite Int.repr_unsigned; auto.
  rewrite Hf in *.
  assert (0<=Int.unsigned (Int.divu (outi-ᵢ$ 4) ($ 4)) )%Z as Has.
  apply Int.unsigned_range.
  assert (0<Int.unsigned (Int.divu (outi-ᵢ$ 4) ($ 4)) \/
          0=Int.unsigned (Int.divu (outi-ᵢ$ 4) ($ 4)) )%Z as Hc.
  omega.
  destruct Hc as [Hc1 | Hc2].
  apply H14 in Hc1.
  destruct Hed as (He1 & He2 & He3).
  rewrite vallist_seg_eqnil in *.
  rewrite <- He2 in Hc1.
  rewrite vallist_seg_Sn in Hc1.
  simpl in Hc1.
  inverts Hc1.
  left.
  splits; auto.
  simpl in H0.
  clear - H0.
  mauto.
  destruct H13 as (His & Hsi).
  lets Hlss : isptr_length_nth His.
  rewrite He3.
  rewrite Int.unsigned_repr.
  auto.
  clear -l.
  mauto.
  apply H15 in Hc2.
  left.
  destruct Hc2.
  destruct H5.
  inverts H8.
  destruct H5.
  destruct Hed as (He1 & He2 & He3).
  rewrite vallist_seg_eqnil in *.
  rewrite <- He2 in H8.
  rewrite vallist_seg_Sn in H8.
  simpl in H8.
  inverts H8.
  simpl in H0.
  split; auto.
  clear - H0.
  mauto.
  destruct H13 as (His & Hsi).
  lets Hlss : isptr_length_nth His.
  rewrite He3.
  rewrite Int.unsigned_repr.
  auto.
  clear -l.
  mauto.
  destruct H13.
  auto.
  unfolds.
  eexists.
  splits.
  unfolds; simpl; auto.
  eapply int_list_length_dec; auto.
  unfolds.
  eexists.
  splits; try unfolds; simpl; eauto.
  rewrite Int.repr_unsigned; auto.
  intros.
  eapply Hm3.
  introv Hf; tryfalse.
  intros.
  apply Hecb in H5.
  tryfalse.
Qed.


Lemma msgqnode_p_hold_no_end: 
  forall b sti qens outi qend qptr qst qin qsize qblk mblk ml hml hsize wl l,
    id_addrval qblk msgqueuetbl os_ucos_h.OS_Q_FREEBLK = Some (b, sti) -> 
    length ml = ∘OS_MAX_Q_SIZE ->
    WellformedOSQ
      (qptr
         :: qst
         :: qend
         :: qin
         :: Vptr (b, outi)
         :: Vint32 qsize :: Vint32 qens :: Vptr qblk :: nil) -> 
    RLH_ECBData_P
      (DMsgQ l
             (qptr
                :: qst
                :: qend
                :: qin
                :: Vptr (b, outi)
                :: Vint32 qsize :: Vint32 qens :: Vptr qblk :: nil)
             mblk ml)
      (absmsgq (nth_val' (Z.to_nat ((Int.unsigned outi - Int.unsigned sti) / 4)) ml
                         :: hml) hsize, wl) ->
    RLH_ECBData_P 
      (DMsgQ l
             (qptr
                :: qst
                :: qend
                :: qin
                :: Vptr (b, outi  +ᵢ  Int.mul ($ 1) ($ 4))
                :: Vint32 qsize
                :: Vint32 (qens  -ᵢ  $ 1) :: Vptr qblk :: nil)
             mblk ml ) (absmsgq hml hsize, wl).
Proof.
  introv Hid  Hlen Hwl Hrl .
  funfold Hwl.
  destruct Hrl.
  destruct H0 as (Hm1 & Hm2 & Hm3 & Hecb).
  funfold H.
  funfold Hm1.
  funfold Hm2.
  unfold arrayelem_addr_right in *.
  unfold qend_right, ptr_offset_right,ptr_minus,  distance in *.
  simp join.
  fsimpl.
  simpl in *.
  destruct x5.
  apply eq_sym in H5.
  subst i0.
  inverts Hid.
  remember ( i2+ᵢ($ 4+ᵢInt.zero)) as k.
  inverts H5.
  assert (Int.mul ($ 1) ($ 4) = $ 4).
  clear -i.
  mauto.
  rewrite H5 in *.
  rewrite <- H4 in *.
  rewrite Int.repr_unsigned in *.
  assert (Int.unsigned ($ 4) = 4).
  clear -i.
  mauto.
  rewrite H8 in *.
  clear H5 H8.
  splits.
  unfolds.
  do 7 eexists;splits; try solve [  unfolds; simpl; eauto].
  splits.
  splits.
  introv Hlt.

  
  lets Hed :  math_xyz_prop2'  H1 H  Hlt; eauto.
  destruct Hed as   (Has & Hass & Hsd) .
  lets Hls : H12 Has.
  assert ( Int.unsigned ($ 4) = 4).
  clear -i.
  mauto.
  rewrite H5 in *.
  clear H5.
  rewrite  <- Hsd in Hls.
  rewrite <- Hass .
  eapply  vallistseg_n_m_split; eauto.
  unfold nat_of_Z.
  apply le_change.
  eapply Z2Nat.inj_le; try omega;try apply Int.unsigned_range.
  destruct H13.
  rewrite Hlen.
  unfold OS_MAX_Q_SIZE in H11.
  unfold Pos.to_nat.
  simpl.
  eapply math_le_trans; eauto.
  introv Hf.
  lets Heas :math_xyz_prop3' Hf; eauto.
  destruct Heas as (Hdisj & Hseq & He).
  assert ( Int.unsigned ($ 4) = 4).
  clear -i.
  mauto.
  rewrite H5 in *.
  clear H5.
  rewrite <- Hseq in *.
  rewrite <- He in *.
  destruct Hdisj as [Hd1 | Hd2].
  lets Hls : H14 Hd1.
  eapply vallist_seg_ltunm_prop; eauto.
  eapply list_maxsize_le; eauto.
  lets Hrs : H15 Hd2.
  destruct Hrs.
  destruct H5 as (Hf1 & Hf2).
  inverts Hf2.
  destruct H5 as (Hf1 & Hf2).
  rewrite Hd2 in *.
  eapply vallist_seg_ltunm_prop; eauto.
  eapply list_maxsize_le; eauto.
  introv Hf.
  lets Heas :math_xyz_prop4' Hf; eauto.
  destruct Heas as (Hdisj & Hseq & He).
  assert ( Int.unsigned ($ 4) = 4).
  clear -i.
  mauto.
  rewrite H5 in *.
  clear H5.
  rewrite Hf.
  rewrite <- Hseq in *.
  rewrite <- He in *.
  lets Hres : H12 Hdisj.
  rewrite Hf in Hres.
  rewrite <- Hseq in Hres.
  rewrite vallist_seg_Sn in Hres.
  inverts Hres.
  left.
  simpl in H0.
  splits; auto.
  clear - H0.
  mauto.
  rewrite Hseq.
  rewrite <- Hf.
  rewrite Hlen.
  unfold OS_MAX_Q_SIZE in H11.
  unfold Pos.to_nat.
  simpl.
  eapply  math_le_trans; eauto.
  destruct H13; auto.
  unfolds.
  eexists.
  splits.
  unfolds; simpl;  eauto.
  eapply int_list_length_dec; auto.
  unfolds.
  eexists.
  splits; try unfolds; simpl; eauto.
  rewrite Int.repr_unsigned; auto.
  intros.
  eapply Hm3.
  introv Hf; tryfalse.
  intros.
  apply Hecb in H5.
  tryfalse.
Qed.
 

Lemma h_has_same_msg: 
  forall b qptr qst qend qin outi qsize qens qblk sti l  qblkm vl hml,
    Int.ltu ($ 0) qens = true ->
    id_addrval qblk msgqueuetbl os_ucos_h.OS_Q_FREEBLK = Some (b, sti) ->
    length vl = ∘OS_MAX_Q_SIZE ->
    WellformedOSQ
      (qptr
         :: qst
         :: qend
         :: qin
         :: Vptr (b, outi)
         :: qsize :: Vint32 qens :: Vptr qblk:: nil) ->
    RLH_ECBData_P (DMsgQ l
                         (qptr
                            :: qst
                            :: qend
                            :: qin
                            :: Vptr (b, outi)
                            :: qsize :: Vint32 qens :: Vptr qblk:: nil) 
                         qblkm vl) hml -> 
    exists vl' max wl, hml = (absmsgq ((nth_val' (Z.to_nat ((Int.unsigned outi - Int.unsigned sti) / 4)) vl) :: vl')  max , wl).
Proof.
  introv Hint Hid  Hlen Hwl Hrl .
  funfold Hwl.
  unfold arrayelem_addr_right in *.
  unfold qend_right, ptr_offset_right,ptr_minus,  distance in *.
  simp join.
  fsimpl.
  simpl in *.
  destruct x5.
  apply eq_sym in Hid.
   inverts Hid.
  remember ( i2+ᵢ($ 4+ᵢInt.zero)) as k.
  inverts H5.
  destruct hml.
  destruct e; tryfalse.
  destruct Hrl as (Hm1 & Hm2 & Hm3).
  destruct Hm3 as (Hm3 & _).
  funfold Hm1.
  funfold Hm2.
  funfold Hm3.
  unfold distance in *.
  simpl in *.
  rewrite Int.repr_unsigned in *.
  lets Hes : int_nat_ltu_lt H7 Hint.
  lets Hls : list_length_lt Hes.
  destruct Hls as (xx & ll & lt).
  subst l0.
  assert ( Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4)) >
       Int.unsigned (Int.divu (outi-ᵢ$ 4) ($ 4)) \/
          Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4)) <
          Int.unsigned (Int.divu (outi-ᵢ$ 4) ($ 4)) \/
          Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4)) =
        Int.unsigned (Int.divu (outi-ᵢ$ 4) ($ 4)) ) by omega.
  destruct H5 as [Ha1 | [Ha2 | Ha3] ].
  apply H19 in Ha1.
  lets Has : vallist_seg_prop_eq Ha1.
  lets Heq :  math_out_start_eq'  H10 H2 H11; eauto.
  rewrite <- Heq.
  subst xx.
  do 3 eexists; eauto.
  apply H21 in Ha2.
  lets Heq :  math_out_start_eq' H10 H2  H11; eauto.
  rewrite <- Heq.
  remember (vallist_seg 0 ∘(Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4))) vl) as ls.
  assert ( (∘(Int.unsigned m) <= length vl)%nat).
  eapply list_maxsize_le; eauto.
  lets Hdas: vallist_seg_prop  H2 H5.
  lets Hsp : list_append_split Hdas Ha2.
  simp join.
  rewrite app_comm_cons in Ha2.
  apply app_inv_tail in Ha2.
  lets Has : vallist_seg_prop_eq Ha2.
  subst xx.
  do 3 eexists; eauto.
  apply H22 in Ha3.
  destruct Ha3.
  simp join; tryfalse.
  destruct H5.
  lets Heq :  math_out_start_eq' H10 H2  H11; eauto.
  rewrite <- Heq.
  remember (vallist_seg 0 ∘(Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4))) vl) as ls.
  assert ( (∘(Int.unsigned m) <= length vl)%nat).
  eapply list_maxsize_le; eauto.
  lets Hdas: vallist_seg_prop  H2 H16.
  lets Hsp : list_append_split Hdas H9.
  simp join.
  rewrite app_comm_cons in H9.
  apply app_inv_tail in H9.
  lets Has : vallist_seg_prop_eq H9.
  subst xx.
  do 3 eexists; eauto.
Qed.


Lemma get_wellformedosq_end:
  forall x qptr st b i qin qout size ens qfr, 
    ens = Vint32 x ->
    
    Int.ltu Int.zero x = true ->  
    WellformedOSQ
      (qptr
         :: st
         :: Vptr (b, i  +ᵢ Int.mul ($ 1) ($ 4))
         :: qin :: qout :: size :: ens :: qfr :: nil) -> 
    WellformedOSQ
      (qptr
         :: st
         :: Vptr (b, i +ᵢ Int.mul ($ 1) ($ 4))
         :: qin
         :: st
         :: size
         :: val_inj (memory.sub ens (Vint32 (Int.repr 1)) Tint16)
         :: qfr :: nil).
Proof.
  intros.
  unfold WellformedOSQ in *.
  simp join.
  unfold V_OSQEnd in *.
  unfold V_OSQSize in *.
  unfold V_OSQStart in *.
  unfold V_OSQOut in *.
  unfold V_qfreeblk in *.
  simpl in *.
  unfold V_OSQIn in *;simpl in *.
  inverts H3.
  inverts H4.
  inverts H5.
  inverts H6.
  inverts H1.
  do 7 eexists;splits;eauto.
  splits;auto.
  unfolds.
  exists 0%nat.
  inverts H2.
  splits;try unfolds;simpl;auto.
  destruct x5.
  rewrite Pos.eqb_refl.
  rewrite Int.sub_idem.
  unfold Int.modu.
  rewrite Int.unsigned_repr.
  unfold Int.zero.
  rewrite Int.unsigned_repr.
  assert (0 mod 4 = 0).
  unfold Z.modulo.
  unfold Z.div_eucl.
  auto.
  rewrite H.
  split.
  unfolds.
  remember (zlt (Int.unsigned i0) (Int.unsigned i0)) as X.
  destruct X;auto.
  omega.
  auto.
  rewrite max_unsigned_val.
  omega.
  rewrite max_unsigned_val.
  omega.
  destruct x5.
  rewrite Pos.eqb_refl.
  simpl.
  assert ((Int.unsigned (Int.divu (i0 -ᵢ i0) ($ 4))) = 0).
  rewrite Int.sub_idem.
  unfold Int.divu.
  unfold Int.zero.
  rewrite Int.unsigned_repr.
  rewrite Int.unsigned_repr.
  rewrite Int.unsigned_repr.
  auto.
  rewrite max_unsigned_val.
  omega.
  rewrite max_unsigned_val.
  omega.
  rewrite Int.unsigned_repr.
  rewrite Int.unsigned_repr.
  assert (0/4 =0).
  auto.
  rewrite H.
  rewrite max_unsigned_val.
  omega.
  rewrite max_unsigned_val.
  omega.
  rewrite max_unsigned_val.
  omega.
  destruct x6.
  rewrite H.
  simpl.
  auto.
  clear -H8.
  remember (Int.unsigned x4) as X.
  clear -H8.
  unfold nat_of_Z.
  assert (Z.to_nat 1 = 1%nat).
  simpl; auto.
  rewrite <- H.
  eapply Z2Nat.inj_le; try omega.
Qed.



Lemma get_wellformedosq_end':
  forall x qptr st b i qin size ens qfr qend, 
    ens = Vint32 x ->
    qend <> Vptr (b, i +ᵢ Int.mul ($ 1) ($ 4)) ->
    WellformedOSQ
      (qptr
         :: st
         :: qend
         :: qin :: Vptr (b, i) :: size :: ens :: qfr :: nil) -> 
    WellformedOSQ
      (qptr
         :: st
         :: qend
         :: qin
         :: Vptr (b, i +ᵢ Int.mul ($ 1) ($ 4))
         :: size
         :: val_inj (memory.sub ens (Vint32 (Int.repr 1)) Tint16)
         :: qfr :: nil).
Proof.  
  introv Hens Hq.
  intros.
  funfold H.
  unfold WellformedOSQ in *.  
  do 7 eexists;splits;eauto;try  unfolds; simpl; eauto.
  splits;auto.
  unfolds.
  unfold qend_right in *.
  unfold arrayelem_addr_right  in *.
  destruct H9.
  destruct H10.
  unfold ptr_offset_right in *.
  unfold ptr_minus in *.
  destruct x1.
  destruct x2.
  destruct x5.
  destruct x6.
  simpl in H5.
  inverts H5.
  remember ((b =? b2)%positive ) as Hbool.
  destruct Hbool; simp join; tryfalse.
  rewrite Pos2Z.inj_eqb in HeqHbool.
  apply eq_sym in HeqHbool.
  apply Z.eqb_eq in HeqHbool.
  inverts HeqHbool.
  remember ((b1 =? b2)%positive ) as Hbool.
  destruct Hbool; simp join; tryfalse.
  rewrite Pos2Z.inj_eqb in HeqHbool.
  apply eq_sym in HeqHbool.
  apply Z.eqb_eq in HeqHbool.
  inverts HeqHbool.
   remember ((b0 =? b2)%positive ) as Hbool.
  destruct Hbool; simp join; tryfalse.
  rewrite Pos2Z.inj_eqb in HeqHbool.
  apply eq_sym in HeqHbool.
  apply Z.eqb_eq in HeqHbool.
  inverts HeqHbool.
  simpl in *.
  rewrite H7 in *.
  clear H7.
  assert (Int.mul ($ 1) ($ 4) = $ 4 ).
  clear - i.
  int auto.
  rewrite H7 in *.
  exists ( ∘(Int.unsigned (Int.divu ((i+ᵢ$ 4)-ᵢ$ 4) ($ 4)))).
  invertsall.
  assert (i0 <> i+ᵢ$ 4).
  intro Hf.
  apply Hq.
  subst .
  auto.
  lets (Hrs1 & Hrs2 & Hrs3) : math_lt_mod_lt   H0  H3 H1 H11; eauto.
  splits;eauto.
  rewrite H4; auto.
Qed.



Lemma msgqlist_p_compose:
  forall  p qid mqls qptrl1 qptrl2 i i1 a x3 p' v'41 
          msgqls1 msgqls2 msgq mqls1 mqls2 mq mqls' tcbls,
    R_ECB_ETbl_P qid
                 (V$OS_EVENT_TYPE_Q
                   :: Vint32 i :: Vint32 i1 :: Vptr a :: x3 :: p' :: nil, v'41) tcbls ->
    ECBList_P p (Vptr qid) qptrl1 msgqls1 mqls1 tcbls->
    ECBList_P p' Vnull qptrl2 msgqls2 mqls2 tcbls->
    RLH_ECBData_P msgq mq ->
    EcbMod.joinsig qid mq mqls2 mqls'->
    EcbMod.join mqls1 mqls' mqls ->
    ECBList_P p Vnull (qptrl1 ++ ((V$OS_EVENT_TYPE_Q
                                    :: Vint32 i :: Vint32 i1 :: Vptr a :: x3 :: p' :: nil, v'41)::nil) ++ qptrl2) (msgqls1 ++ (msgq::nil) ++msgqls2) mqls tcbls.
Proof.
  intros.
  simpl.
  eapply ecblist_p_compose; eauto.
  simpl.
  eexists; splits; eauto.
  do 3 eexists; splits; eauto.
  unfolds; simpl; auto.
Qed.

Lemma osq_same_blk_st_out'
: forall (qptr qst qend qin qout qsz qen : val) 
         (b : block) (i : int32),
    WellformedOSQ
      (qptr
         :: qst :: qend :: qin :: qout :: qsz :: qen :: Vptr (b,i) :: nil) ->
    exists i', qout = Vptr (b, i').
Proof.
  introv Hwf.
  funfold Hwf.
  simpl in H5.
  funfold H9.
  funfold H10.
  unfold ptr_offset_right in *.
  unfold ptr_minus in *.
  inverts H5.
  unfolds in H8.
  simpl in *.
  simp join.
  rewrite H5 in *.
  destruct x1.
  destruct x2.
  remember ((b0 =? b)%positive ) as Hbool.
  destruct Hbool; tryfalse.
  simp join.
  rewrite Pos2Z.inj_eqb in HeqHbool.
  apply eq_sym in HeqHbool.
  apply Z.eqb_eq in HeqHbool.
  apply eq_sym in HeqHbool.
  inverts HeqHbool.
  remember ((b1 =? b0)%positive ) as Hbool.
  destruct Hbool; tryfalse.
  simp join.
  rewrite Pos2Z.inj_eqb in HeqHbool.
  apply eq_sym in HeqHbool.
  apply Z.eqb_eq in HeqHbool.
  inverts HeqHbool.
  eauto.
Qed.

    
Lemma wellq_props:
  forall x12 x11 x5 x6 v'49 x i2 i1  v'47 x13 x14 v2 v'46,
    length v2 = ∘OS_MAX_Q_SIZE ->
    Int.ltu ($ 0) i1 = true ->
    RLH_ECBData_P
      (DMsgQ (Vptr (v'47, Int.zero))
             (x12
                :: x11
                :: x5
                :: x6
                :: Vptr (v'49, x)
                :: Vint32 i2
                :: Vint32 i1 :: Vptr (v'49, Int.zero) :: nil)
             (x13 :: x14 :: nil) v2) v'46 ->
    WellformedOSQ
      (x12
         :: x11
         :: x5
         :: x6
         :: Vptr (v'49, x)
         :: Vint32 i2
         :: Vint32 i1 :: Vptr (v'49, Int.zero) :: nil) ->
    Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero)) <= Int.unsigned x /\
    4 * ((Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4) =
    Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero)) /\
    (Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4 < 20 /\
    (Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4 < Z.of_nat (length v2) /\
    rule_type_val_match (Void) ∗
                        (nth_val'
                           (Z.to_nat
                              ((Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4))
                           v2) = true.
Proof.
  introv Hlen Hint Hrl  Hwf.
  Definition auxand P Q :=  P /\ Q.
  assert (auxand (Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero)) <= Int.unsigned x)
                 (4 * ((Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4) =
                  Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero)) /\
                  (Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4 < 20 /\
                  (Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4 <
                  Z.of_nat (length v2) /\
                  rule_type_val_match (Void) ∗
                                      (nth_val'
                                         (Z.to_nat
                                            ((Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4))
                                         v2) = true
                 )).
  funfold Hwf.
  unfold arrayelem_addr_right in *.
  unfold qend_right, ptr_offset_right,ptr_minus,  distance in *.
  simp join.
  fsimpl.
  inverts H5.
  unfolds in Hrl.
  destruct v'46.
  destruct e; tryfalse.
  destruct Hrl as (Hm1 & Hm2 & Hm3).
  destruct Hm3 as (Hm3 & _).
  funfold Hm1.
  funfold Hm2.
  funfold Hm3.
  unfold distance in *.
  simpl in H7, H10, H18, H20, H21.
  rewrite Int.repr_unsigned in *.
  assert ((Int.zero+ᵢ($ 4+ᵢInt.zero)) = $4).
  clear -x.
  mauto.
  rewrite H1 in *.
  clear H1.
  assert (Int.unsigned ($ 4) =4).
  clear -x.
  mauto.
  rewrite H1 in *.
  clear H1.
  splits.
  clear -H.
  int auto.
  apply eq_sym.
  eapply Z_div_exact_2; try omega.
  eapply math_prop_int_modu; eauto.
  eapply math_prop_ltu_20; eauto.
  rewrite Hlen.
  unfold OS_MAX_Q_SIZE.
  simpl.
  eapply math_prop_ltu_20; eauto.
  assert (Int.unsigned ($4) = 4). 
  clear -x.
  mauto.
  assert ( Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4)) >
           Int.unsigned (Int.divu (x-ᵢ$ 4) ($ 4))  \/
         Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4)) <
         Int.unsigned (Int.divu (x-ᵢ$ 4) ($ 4)) \/
         Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4)) =
           Int.unsigned (Int.divu (x-ᵢ$ 4) ($ 4))) by omega.
  lets Hes : int_nat_ltu_lt H5 Hint. 
  lets Hls : list_length_lt Hes.
  destruct Hls as (xx & ll & lt).
  subst l.
  destruct H9 as [Ha1 | [ Ha2 | Ha3]].
  apply H18 in Ha1.
  lets Has : vallist_seg_prop_eq Ha1.
  lets Heq :  math_out_start_eq'   H11; eauto.
  rewrite H1 in *.
    rewrite <- Heq.
  rewrite <- Has.
  simpl in H19.
  destruct H19.
  simpl.
  clear - H9.
  pauto.
  apply H20 in Ha2.
  lets Heq :  math_out_start_eq'   H11; eauto.
  rewrite H1 in *.
  rewrite <- Heq.
  remember (vallist_seg 0 ∘(Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4))) v2) as ls.
  assert ( (∘( ( Int.unsigned m)) <= length v2)%nat).
  eapply list_maxsize_le; eauto.
  lets Hdas: vallist_seg_prop H2 H9; eauto.
  lets Hsp : list_append_split Hdas Ha2.
  simp join.
  simpl in H19.
  destruct H19.
  apply vallist_seg_prop_eq in H16.
  rewrite <- H16.
  simpl.
  clear -H7.
  pauto.
  apply H21 in Ha3.
  lets Heq :  math_out_start_eq'   H11; eauto.
  destruct Ha3 as [Haa | Ha3].
  simp join; tryfalse.
  destruct Ha3 as (Heqa & Ha3).
  rewrite H1 in *.
  rewrite <- Heq.
  remember (vallist_seg 0 ∘(Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4))) v2) as ls.
  assert ( (∘( ( Int.unsigned m)) <= length v2)%nat).
  eapply list_maxsize_le; eauto.
  lets Hdas: vallist_seg_prop H2 H9; eauto.
  lets Hsp : list_append_split Hdas Ha3.
  simp join.
  simpl in H19.
  destruct H19.
  apply vallist_seg_prop_eq in H16.
  rewrite <- H16.
  simpl.
  clear -H7.
  pauto.
  auto.
Qed.

Close Scope code_scope.
Close Scope int_scope.
Close Scope Z_scope.
(*
Lemma qacc_absinfer_no_msg:
  forall P mqls x qmaxlen wl, 
    can_change_aop P ->  
    EcbMod.get mqls x = Some (absmsgq nil qmaxlen,wl) -> 
    absinfer
      (<|| qacc (Vptr x :: nil) ||>  ** HECBList mqls ** P) 
      (<|| END Some Vnull ||>  ** HECBList mqls ** P).
Proof.
  infer_solver 2%nat.
Qed.

Lemma qacc_absinfer_get_msg:
  forall P mqls x qmaxlen wl v vl v1 v3 v4 , 
    can_change_aop P ->  
    EcbMod.get mqls x = Some (absmsgq (v::vl) qmaxlen,wl) -> 
    absinfer
      (<|| qacc (Vptr x :: nil) ||>  ** 
           HECBList mqls **  HTCBList v1 ** HTime v3 ** HCurTCB v4 ** P) 
      (<|| END Some v ||>  ** HECBList (EcbMod.set mqls x (absmsgq vl qmaxlen,wl)) **  HTCBList v1 ** HTime v3 ** HCurTCB v4 ** P).
Proof.
  infer_solver 3%nat.
Qed.

  Lemma qacc_absinfer_null:
    forall P, can_change_aop P ->
              absinfer (<|| qacc (Vnull :: nil) ||>  ** P) (<|| END (Some Vnull) ||> ** P).
  Proof.
    intros.
    unfold qacc.
    eapply absinfer_trans; auto.
    eapply absinfer_choice1; eauto.
    eapply absinfer_prim; auto.
    
    unfolds; intros.
    destruct s as [[[[]]]].
    simpl in H0; mytac.
    exists O (END Some Vnull).
    split.
    eapply hmstep_merge_emp.
    constructors.
    unfolds; auto.
    apply eqdomO_same.
    apply eqtid_same.
    unfolds; intros; rewrite OSAbstMod.emp_sem.
    destruct(OSAbstMod.get O a); auto.

    sep auto.
  Qed.

  
  Lemma qacc_absinfer_no_q :
    forall P mqls x,
      can_change_aop P ->
      (~ exists a b wl,EcbMod.get mqls x = Some (absmsgq a b,wl)) ->
      absinfer (<|| qacc (Vptr x :: nil) ||> ** HECBList mqls ** P)
               (<|| END Some Vnull ||> ** HECBList mqls ** P).
  Proof.
    intros.
    unfold qacc.
    eapply absinfer_trans.
    eapply absinfer_choice2 with (q:=(HECBList mqls ** P)); can_change_aop_solver.
    eapply absinfer_trans.
    eapply absinfer_choice1 with (q:=(HECBList mqls ** P)); can_change_aop_solver.

    eapply absinfer_prim; can_change_aop_solver.
    unfolds; intros.
    destruct s as [[[[]]]].
    eexists O, (END Some Vnull).
    split.
    simpl in H1; mytac.
    eapply hmstep_merge_emp.
    constructors.
    unfolds.
    exists x.
    split; auto.
    exists mqls.
    repeat (split;auto).
      Ltac join_get_solver :=
    match goal with 
      | H: OSAbstMod.join (OSAbstMod.sig ?x ?y) _ ?O |- OSAbstMod.get ?O ?x = Some ?y =>
        eapply OSAbstMod.join_get_get_l; eauto
      | H: OSAbstMod.join ?O1 ?O2 ?O |- OSAbstMod.get ?O ?x = Some ?y =>
        eapply OSAbstMod.join_get_get_r; [eauto | join_get_solver]
    end. 
    join_get_solver.
    apply eqdomO_same.
    apply eqtid_same.
    unfolds; intros; rewrite OSAbstMod.emp_sem.
    destruct(OSAbstMod.get O a); auto.

    sep auto.
  Qed.
*)
