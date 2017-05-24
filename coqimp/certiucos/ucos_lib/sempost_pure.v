Require Export sem_common.
Require Export OSQPostPure.

Open Scope code_scope.

Lemma sempost_ltu_trans:
  forall n,
    Int.ltu n ($ 65535) = true ->
    Int.ltu (n+ᵢ$ 1) ($ 65536) = true.
Proof.
  int auto.
  int auto.
Qed.  

Lemma sempost_inc_cnt_prop:
  forall s P a msgq mq a' msgq' mq' n i x2 x3 x4 qid b tcbls,
    s |= AEventData a msgq ** P ->
    RLH_ECBData_P msgq mq ->
    R_ECB_ETbl_P qid (a,b) tcbls ->
    a = (V$OS_EVENT_TYPE_SEM :: Vint32 i :: Vint32 n :: x2 :: x3 :: x4 :: nil) ->
    msgq = DSem n ->
    mq = (abssem n, nil) ->
    a' = (V$OS_EVENT_TYPE_SEM :: Vint32 i :: Vint32 (n+ᵢ$ 1)  :: x2 :: x3 :: x4 :: nil) ->
    msgq' = DSem (n+ᵢ$ 1) ->
    mq' = (abssem (n+ᵢ$ 1), nil) ->
    Int.ltu n ($ 65535) = true ->
    s |= AEventData a' msgq' **
         [| RLH_ECBData_P msgq' mq' |] ** 
         [| R_ECB_ETbl_P qid (a',b) tcbls |] ** P. 
Proof.
  intros.
  sep pauto.
  unfold AEventData in *.
  sep pauto.


  apply sempost_ltu_trans; auto.
  unfold RLH_ECBData_P in *.
  destruct H0.
  split.
  auto.  
  unfold RH_ECB_P in *.
  destruct H2.
  split.
  intros.
  auto.
  intros.
  tryfalse.
Qed.

Lemma something_in_not_nil : forall (T:Type) (y: @list T), y<>nil -> exists x, In x y.
Proof.
  intros T y.
  elim y.
  intro; tryfalse.
  intros.
  exists a.
  simpl.
  left; auto.
Qed.

Lemma rg1 :  forall x2 x6 ,  0 <= Int.unsigned x2 < 64->
                             x6 = $ Int.unsigned x2&ᵢ$ 7 ->
                             0<= Int.unsigned x6 < 8.
Proof.
  intros.
  subst x6.

  mauto.
Qed.

Lemma rg2 :  forall x2 x7 ,  0 <= Int.unsigned x2 < 64->
                             x7 = Int.shru ($ Int.unsigned x2) ($ 3) ->
                             0<= Int.unsigned x7 < 8.
Proof.
  intros.
  subst x7.
  mauto.
Qed.

Lemma sempost_grp_wls_nil:
  forall (v'36 v'13 : vallist) (v'12 : int32) 
         (v'32 : block) (v'15 : int32) (v'24 : val) 
         (v'35 v'0 : val) (v'8 : tid) (v'9 v'11 : EcbMod.map)
         x  (x1 : waitset)
         (v'6 v'10 : EcbMod.map) (v'38 v'69 v'39 : int32) 
         (v'58 : block) (a : priority)
         (c : msg) (v'62 v'7 : TcbMod.map) 
         (vhold : addrval),
    v'12 = Int.zero ->
    R_PrioTbl_P v'36 v'7 vhold ->
    RL_Tbl_Grp_P v'13 (Vint32 v'12) ->
    R_ECB_ETbl_P (v'32, Int.zero)
                 (V$OS_EVENT_TYPE_SEM
                   :: Vint32 v'12
                   :: Vint32 x :: v'24 :: v'35 :: v'0 :: nil,
                  v'13) v'7 ->
    RH_TCBList_ECBList_P v'11 v'7 v'8 ->
    EcbMod.join v'9 v'10 v'11 ->
    EcbMod.joinsig (v'32, Int.zero) (abssem x , x1) v'6 v'10 ->
    x1 = nil.
Proof.
  intros.
  unfolds in H2.
  destruct H2 as (H2 & H2' & _).
  destruct H2 as (_ & H2 & _ & _).
  destruct H2' as (_ & H2' & _ & _).
  unfolds in H2.
  unfolds in H2'.
  

  unfolds in H3.
  unfolds in H1.
  unfolds in H0.
  destruct H3 as (_ & H3 & _ & _).
  unfolds in H3.
  destruct H3 as (H3 & H3').

  lets Hg : EcbMod.join_joinsig_get H4 H5.
  clear H4 H5.
  assert ( x1 = nil \/ x1 <> nil) by tauto.
  destruct H4; intros; auto.

  idtac.
  apply something_in_not_nil in H4.
  inversion H4.
  assert (EcbMod.get v'11 (v'32, Int.zero) = Some (abssem x, x1) /\ In x0 x1) by tauto.
  lets aadf : H3 H6.
  mytac.
  lets bbdf : H2' H10.
  destruct bbdf.
  unfolds in H.
  do 3 destruct H.
  destruct H as (Ha & Hb & Hc & Hd& He).
  cut ( 0<=(∘(Int.unsigned x7)) <8)%nat.
  intro.
  assert (V$0 = V$0) by auto.
  lets adfafd : H1 H Hd H12.
  destruct adfafd.
  destruct H13.
  destruct H14.
  cut ( $ 0&ᵢ($ 1<<ᵢ$ Z.of_nat ∘(Int.unsigned x7)) = $ 0).
  intro.
  apply H13 in H17.
  subst x8.

  lets rg : rg1 Ha Hb.
  clear -He rg.
  false.
  gen He.
  mauto.

  lets rg : rg2 Ha Hc.
  clear -rg.
  mauto.

  lets rg : rg2 Ha Hc.
  clear -rg.
  mauto.
Qed.

Lemma post_exwt_succ_pre_sem
     : forall (v'36 v'13 : vallist) (v'12 : int32) 
         (v'32 : block) (v'24 : block) 
         (v'35 v'0 : val) (v'8 : tid) (v'9 v'11 : EcbMod.map)
         x (x1 : waitset)
         (v'6 v'10 : EcbMod.map) (v'38 v'69 v'39 : int32) 
         (v'58 : block) (a : priority) (b : taskstatus) 
         (c :msg) (v'62 v'7 : TcbMod.map) 
         (vhold : addrval),
       v'12 <> Int.zero ->
       R_PrioTbl_P v'36 v'7 vhold ->
       RL_Tbl_Grp_P v'13 (Vint32 v'12) ->
       R_ECB_ETbl_P (v'32, Int.zero)
         (V$OS_EVENT_TYPE_SEM
          :: Vint32 v'12
             :: Vint32 x :: Vptr (v'24, Int.zero) :: v'35 :: v'0 :: nil,
         v'13) v'7 ->
       RH_TCBList_ECBList_P v'11 v'7 v'8 ->
       EcbMod.join v'9 v'10 v'11 ->
       EcbMod.joinsig (v'32, Int.zero) (abssem x , x1) v'6 v'10 ->
       Int.unsigned v'12 <= 255 ->
       array_type_vallist_match Int8u v'13 ->
       length v'13 = ∘OS_EVENT_TBL_SIZE ->
       nth_val' (Z.to_nat (Int.unsigned v'12)) OSUnMapVallist = Vint32 v'38 ->
       Int.unsigned v'38 <= 7 ->
       nth_val' (Z.to_nat (Int.unsigned v'38)) v'13 = Vint32 v'69 ->
       Int.unsigned v'69 <= 255 ->
       nth_val' (Z.to_nat (Int.unsigned v'69)) OSUnMapVallist = Vint32 v'39 ->
       Int.unsigned v'39 <= 7 ->
       nth_val' (Z.to_nat (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39))) v'36 =
       Vptr (v'58, Int.zero) ->
       TcbJoin (v'58, Int.zero) (a, b, c) v'62 v'7 ->
       x1 <> nil /\
       GetHWait v'7 x1 (v'58, Int.zero) /\
       TcbMod.get v'7 (v'58, Int.zero) = Some (a, b, c) /\ a = ((v'38<<ᵢ$ 3)+ᵢv'39).
Proof.
  intros.
  lets Hs :  tcbjoin_get_a  H16.
  unfolds in H3.
  unfolds in H1.
  unfolds in H0.
  unfolds in H2.
  destruct H2.
  destruct H17 as (H17&Htype).
  unfolds in H2.
  unfolds in H17.
  lets Hg : EcbMod.join_joinsig_get H4 H5.
  clear H4 H5.
  clear H16.
  assert ( Int.unsigned v'38 < 8) as Hx by omega.
  assert (Int.unsigned v'39 < 8) as Hy by omega.
  clear H10 H12.
  lets Hrs : math_xy_prio_cons Hx Hy.
  unfold nat_of_Z in H0.
  destruct H0 as (Hpr1 & Hpr2).
  assert ((v'58, Int.zero) <> vhold) as Hnvhold.
  destruct Hpr2.
  apply H0 in Hs.
  destruct Hs;auto.
  lets Hnth : nth_val'_imp_nth_val_vptr H15.
  lets Hsd : Hpr1 Hrs Hnth.
  destruct Hsd as (st & m & Hst);auto.
  unfold get in Hst; simpl in Hst.
  rewrite Hs in Hst.
  inverts Hst.
  assert (Int.shru ((v'38<<ᵢ$ 3)+ᵢv'39) ($ 3)= v'38).
  eapply math_shrl_3_eq; eauto.
  eapply nat_8_range_conver; eauto.
  assert ( (Z.to_nat (Int.unsigned v'38))  < length v'13)%nat.
  rewrite H8.
  simpl.
  unfold Pos.to_nat; simpl.
  clear - Hx.
  mauto.
  lets Has : array_int8u_nth_lt_len H7 H4.
  destruct Has as (i & Hnthz & Hinsa).
  rewrite H11 in Hnthz.
  inverts Hnthz.
  assert ((((v'38<<ᵢ$ 3)+ᵢv'39)&ᵢ$ 7) = v'39).
  eapply math_8range_eqy; eauto.
  eapply  nat_8_range_conver; eauto.
  apply nth_val'_imp_nth_val_int in H11.
  assert ( Vint32 v'12 = Vint32 v'12) by auto.
  lets Hzs : H1 H11 H10.
  eapply  nat_8_range_conver; eauto.
  destruct Hzs.
  lets Has : math_8_255_eq H6 H9 H.
  assert (i <> $ 0).
  assert ($ 1<<ᵢ$ Z.of_nat ∘(Int.unsigned v'38) = $ 1<<ᵢv'38).
  clear -Hx.
  mauto.
  rewrite H18 in H16.
  apply H16 in Has.
  apply ltu_eq_false in Has.
  pose (Int.eq_spec i ($0)).
  rewrite Has in y.
  auto.
  assert (PrioWaitInQ (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39)) v'13).
  unfolds.
  rewrite Int.repr_unsigned in *.
  exists ( ((v'38<<ᵢ$ 3)+ᵢv'39)&ᵢ$ 7 ).
  exists (Int.shru ((v'38<<ᵢ$ 3)+ᵢv'39) ($ 3) ).
  rewrite H0 in *.
  exists i.
  splits; eauto.
  rewrite H5.
  eapply math_8_255_eq; eauto.
  destruct H2 as (H2'&H2&H2''&Hres).
  lets Hes : H2 H19.
  unfold V_OSEventType in Hes.
  simpl nth_val in Hes.
  assert (Some (V$OS_EVENT_TYPE_SEM) = Some (V$OS_EVENT_TYPE_SEM)) by auto.
  apply Hes in H20.
  clear Hes.
  rename H20 into Hes.
  destruct Hes as (td & nn &mm & Hge).
  destruct Hpr2 as (Hpr2 & Hpr3).
  unfolds in Hpr3.
  assert (td = (v'58, Int.zero)  \/ td <> (v'58, Int.zero) ) by tauto.
  destruct H20.
  Focus 2.
  lets Hass : Hpr3 H20 Hge Hs.
  rewrite Int.repr_unsigned in *.
  tryfalse.
  rewrite Int.repr_unsigned in *.
  subst td.
  unfold get in Hge; simpl in Hge.
  rewrite Hs in Hge.
  inverts Hge.
  destruct H3 as (H3'&H3&H3''&Hres').
  destruct H3 as (Heg1 & Heg2).
  lets Hrgs : Heg2 Hs.
  destruct Hrgs as (xz &  qw & Hem & Hin).
  unfold get in Hem; simpl in Hem.
  rewrite Hg in Hem.
  inverts Hem.


  assert (qw = nil \/ qw <> nil) by tauto.
  destruct H3.
  subst qw.
  simpl in Hin; tryfalse.
  splits; auto.
  unfolds.
  splits; auto.
  do 3 eexists; splits; eauto.
  intros.
  assert (EcbMod.get v'11 (v'32, Int.zero) = Some (abssem xz, qw) /\ In t' qw) .
  splits; auto.
  lets Habs : Heg1 H22.
  destruct Habs as (prio' & m' & n' & Hbs).
  do 3 eexists; splits; eauto.
  destruct H17 as (H17'&H17&H17''&Hres'').
  lets Hpro : H17 Hbs.
  destruct Hpro as (Hpro&Hss).
  clear Hss.
  unfolds in Hpro.
  destruct Hpro as (xa & xb & zz & Hran & Hxx & Hyy & Hnths & Hzz).
  subst xa xb.
  rewrite Int.repr_unsigned in *.
  lets Hat : math_highest_prio_select H13 H9 H11 Hnths  Hzz;
    try eapply int_usigned_tcb_range; try omega;
    eauto.
  assert (Vint32 v'12 = Vint32 v'12) by auto.
  lets Hzs : H1 Hnths H23.
  eapply nat_8_range_conver; eauto.
  try eapply int_usigned_tcb_range; eauto.  
  destruct Hzs.
  assert (zz = $ 0 \/ zz <> $ 0) by tauto.
  destruct H26.
  subst zz.
  rewrite Int.and_commut in Hzz.
  rewrite Int.and_zero in Hzz.
  unfold Int.one in *.
  unfold Int.zero in *.
  assert ($ 1<<ᵢ(prio'&ᵢ$ 7) <> $ 0 ).
  eapply math_prop_neq_zero2; eauto.
  tryfalse.
  assert (Int.ltu ($ 0) zz = true).
  clear - H26.
  int auto.
  assert (0<=Int.unsigned zz ).
  int auto.
  assert (Int.unsigned zz = 0).
  omega.
  rewrite <- H0 in H26.
  rewrite Int.repr_unsigned in *.
  tryfalse.
  apply H25 in H27.
  assert ($ Z.of_nat ∘(Int.unsigned (Int.shru prio' ($ 3))) = (Int.shru prio' ($ 3))).
  clear -Hran.
  mauto.
  rewrite H28 in *.
  auto.
  lets Hasss : Hpr3 H20 Hs Hbs; eauto.
  unfolds.
  rewrite zlt_true; auto.
  assert (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39) < Int.unsigned prio' \/
          Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39) = Int.unsigned prio').
  omega.
  destruct H23; auto; tryfalse.
  false.
  apply Hasss.
  apply unsigned_inj; eauto.
Qed.


Lemma sem_post_get_tcb_stat
: forall (p : int32) (etbl : vallist) (ptbl : list val) 
         (tid : addrval) (tcbls : TcbMod.map) (abstcb : abstcb.B)
         (tcbls' : TcbMod.map) (vl rtbl : vallist) 
         (qid : addrval) (vle : list val) (vhold : addrval),
    0 <= Int.unsigned p < 64 ->
    array_type_vallist_match Int8u etbl ->
    length etbl = ∘OS_EVENT_TBL_SIZE ->
    prio_in_tbl p etbl ->
    nth_val' (Z.to_nat (Int.unsigned p)) ptbl = Vptr tid ->
    R_PrioTbl_P ptbl tcbls vhold ->
    TcbJoin tid abstcb tcbls' tcbls ->
    TCBNode_P vl rtbl abstcb ->
    R_ECB_ETbl_P qid (V$OS_EVENT_TYPE_SEM :: vle, etbl) tcbls ->
    V_OSTCBStat vl = Some (V$OS_STAT_SEM).
Proof.
  introv Hran Harr Hlen Hpri Hnth Hr Htj Htn Hre.
  unfolds in Hre.
  destruct Hre as (Hre1 & Hre2 & Hre3).
  unfolds in Hre2.
  destruct Hre1 as (Hre1'&Hre1&Hre1''& _).
  unfolds in Hre1.
  unfolds in Htn.
  destruct abstcb.
  destruct p0.
  destruct Htn as (Hv1 & Hv2 &  Hrl & Hrc).
  funfold Hrl.
  rewrite H8 in H4.
  inverts H4.
  unfolds in Hrc.
  destruct Hrc as (_&_&_&Hrc).
  unfolds in Hrc.
  destruct Hrc as (_&Hrc&_&_&_).
  unfolds in Hrc.
  unfolds in Hpri.
  lets Hges : tcbjoin_get_a Htj.
  unfolds in Hr.
  destruct Hr.
  apply nth_val'_imp_nth_val_vptr in Hnth.
  lets Hs : H Hnth; eauto.
  assert (tid <> vhold) as Hnvhold.
  apply H4 in Hges;destruct Hges;auto.
  destruct Hs as (st & mm & Hgs);auto.
  unfold get in Hgs; simpl in Hgs.
  rewrite Hges in Hgs.
  inverts Hgs.
  assert (PrioWaitInQ (Int.unsigned p) etbl).
  unfolds.
  rewrite Int.repr_unsigned.
  remember (Int.shru p ($3)) as py.
  remember ( p&ᵢ$ 7) as px.
  lets Hrs : n07_arr_len_ex ∘(Int.unsigned py)  Harr Hlen.
  subst py.
  clear - H17.
  mauto.
  destruct Hrs as (vx & Hntht & Hin).
  do 3 eexists; splits; eauto.
  assert ( V_OSEventType (V$OS_EVENT_TYPE_SEM :: vle) = Some (V$OS_EVENT_TYPE_SEM)).
  unfolds.
  simpl; auto.
  lets Hsd : Hre1 H15 H20.
  mytac.
  rewrite Int.repr_unsigned in H22.
  assert (x = tid \/ x <> tid) by tauto.
  destruct H23.
  subst x.
  unfold get in H22; simpl in H22.
  rewrite Hges in H22.
  inverts H22.
  eapply Hrc; eauto.
  unfolds in H21.
  lets Hfs : H21 H23 H22 Hges.
  tryfalse.
Qed. 


Lemma le7_le7_range64:  forall v'57 v'59, Int.unsigned v'57 <= 7 -> Int.unsigned v'59 <= 7 ->  0 <= Int.unsigned ((v'57<<ᵢ$ 3)+ᵢv'59) < 64.
  intros.
  mauto.
Qed.

Lemma TCBList_P_post_sem: (*tcblist_P_post_mbox *)
 forall (v'42 : val) (v'48 : list vallist) (v'47 : TcbMod.map)
         (v'60 : val) (v'50 : list vallist) (v'37 : vallist)
         (v'59 v'49 v'44 : TcbMod.map) (v'63 v'64 v'65 : val)
         (v'51 v'52 v'53 v'54 v'55 v'56 : int32) (x00 : addrval)
         (v'58 : block) (v'40 v'38 : int32) (prio : priority)
         (st : taskstatus) (msg0 msg1:msg)
         (v'7 v'62 v'43 : TcbMod.map) (v'36 : vallist) 
         (v'39 : int32) (v'13 : vallist) (vhold : addrval),
    Int.unsigned v'38 <= 7 ->
    Int.unsigned v'39 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned v'39)) OSMapVallist = Vint32 v'40 ->
    prio_in_tbl ((v'38<<ᵢ$ 3)+ᵢv'39) v'13 ->
    RL_RTbl_PrioTbl_P v'13 v'36 vhold ->
    nth_val' (Z.to_nat (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39))) v'36 =
    Vptr (v'58, Int.zero) ->
    R_PrioTbl_P v'36 v'7 vhold ->
    array_type_vallist_match Int8u v'37 ->
    length v'37 = ∘OS_RDY_TBL_SIZE ->
    TcbMod.join v'44 v'43 v'7 ->
    TcbJoin (v'58, Int.zero) (prio, st, msg0) v'62 v'7 ->
    get_last_tcb_ptr v'48 v'42 = Some (Vptr (v'58, Int.zero)) ->
    TCBList_P v'42 v'48 v'37 v'47 ->
    TCBList_P v'60 v'50 v'37 v'59 ->
    TcbJoin (v'58, Int.zero) (prio, st, msg0) v'59 v'49 ->
    TcbMod.join v'47 v'49 v'44 ->
    TCBNode_P
      (v'60
         :: v'63
         :: v'64
         :: v'65
         :: Vint32 v'51
         :: V$OS_STAT_SEM
         :: Vint32 v'52
         :: Vint32 v'53
         :: Vint32 v'54
         :: Vint32 v'55 :: Vint32 v'56 :: nil) v'37
      (prio, st, msg0) ->
    TCBList_P v'42
              (v'48 ++
                    (v'60
                       :: v'63
                       :: Vnull
                       :: msg1
                       :: V$0
                       :: V$0
                       :: Vint32 v'52
                       :: Vint32 v'53
                       :: Vint32 v'54
                       :: Vint32 v'55 :: Vint32 v'56 :: nil)
                    :: v'50)
              (update_nth_val (Z.to_nat (Int.unsigned v'38)) v'37
                              (val_inj
                                 (or (nth_val' (Z.to_nat (Int.unsigned v'38)) v'37)
                                     (Vint32 v'40))))
              (TcbMod.set v'44 (v'58, Int.zero) (prio, rdy, msg1)).
Proof.
  intros.
  unfolds in H5.
  destruct H5 as (Ha1 & Ha2 & Ha3).
  assert ( 0 <= Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39) < 64).
  clear -H H0.
  mauto.
  unfold nat_of_Z in Ha1.
  eapply nth_val'_imp_nth_val_vptr in H4.
  lets Hps : Ha1 H5 H4.
  
  lets Hgs : tcbjoin_get_a H9.
  assert ((v'58, Int.zero) <> vhold) as Hnvhold.
  apply Ha2 in Hgs.
  destruct Hgs;auto.
  apply Hps in Hnvhold.
  clear Hps.
  mytac.
  unfold get in H17; simpl in H17.
  rewrite H17 in Hgs.
  inverts Hgs.
  remember ((v'38<<ᵢ$ 3)) as px.
  remember (v'39) as py.
  clear Heqpy.
  remember (px+ᵢpy) as prio.
  remember ( (v'58, Int.zero)) as tid.
  lets Hps : tcbjoin_set_ex (prio,st,msg0) (prio,rdy,msg1)  H14;eauto.
  destruct Hps as (b&Htx & Hty).
  remember (val_inj
              (or (nth_val' (Z.to_nat (Int.unsigned v'38)) v'37) (Vint32 v'40))) as Hv.
  assert (0<= Z.to_nat (Int.unsigned v'38) <8)%nat.
  clear -H.
  mauto.
  lets Hsx : n07_arr_len_ex H6 H7; eauto.
  destruct Hsx as (vx & Hnth & Hi).
  lets Hns :  nth_val_nth_val'_some_eq  Hnth.
  rewrite Hns in HeqHv.
  simpl in HeqHv.
  subst Hv.
  assert (v'38 = Int.shru prio ($ 3)).
  subst.
  clear - H H0.
  mauto.
  rewrite H19.
  assert (v'40 = ($ 1<<ᵢ(prio &ᵢ$ 7))).  
  rewrite Heqprio.
  rewrite Heqpx.
  assert ((((v'38<<ᵢ$ 3)+ᵢpy)&ᵢ$ 7) = py).
  clear -H H0.
  mauto.
  rewrite H20.
  clear -H0 H1.
  unfold OSMapVallist in H1.
  (* ** ac: SearchAbout OSMapVallist. *)
  eapply math_mapval_core_prop; eauto.
  mauto.
  
  rewrite H20.
  eapply TCBList_P_Combine; eauto.
  eapply TCBList_P_rtbl_add_simpl_version; eauto.
  rewrite <-H19.
  auto.
  intros.
  unfolds in Ha3.
  lets Hsx : tcbjoin_join_get_neq H13 H14 H21.
  destruct Hsx.
  eapply Ha3; eauto.
  lets Hacb  :  TcbMod.join_get_l H8 H23; eauto.
  simpl.
  do 4 eexists; splits; eauto.
  unfolds; simpl; eauto.
  unfold TcbJoin in *.
  unfold join in *; simpl in *.
  eauto.
  unfolds in H15.
  unfolds.
  fsimpl.
  usimpl H15.
  usimpl H22.
  splits.
  unfolds; simpl; auto.
  unfolds; simpl; auto.
  funfold H23.
  unfolds.
  do 6 eexists; splits; try solve [unfolds; simpl;auto].
  omega.
  splits; eauto.
  eexists.
  split.
  unfolds;simpl; eauto.
  auto.
  unfolds.
  splits.
  unfolds.
  intros.
  unfolds in H15.
  fsimpl.
  usimpl H15.
  splits; try solve [unfolds; simpl;auto].
  eexists; eauto.
  unfolds.
  intros.
  inverts H15.
  splits; try solve [unfolds; simpl;auto].
  unfolds.
  splits; try solve [unfolds; simpl;auto].
  apply prio_in_tbl_orself ; auto.
  unfolds.
  splits.
  unfolds.
  intros.
  usimpl H22.
  unfolds in H15.
  fsimpl.
  usimpl H15.
  usimpl H25.
  false.
  rewrite H26 in H19.
  rewrite H19 in Hnth.
  rewrite H26 in *.
  (* ** ac: Check prio_notin_tbl_orself. *)
  lets Hfs :  prio_notin_tbl_orself  H16 Hnth.
  tryfalse.

  unfolds.
  intros.
  usimpl H22.
  unfolds.
  intros.
  unfolds in H15.
  fsimpl.
  usimpl H15.
  usimpl H25.

  unfolds.
  intros.
  usimpl H22.
  unfolds.
  intros.
  unfolds in H15.
  fsimpl.
  usimpl H15.
  usimpl H25.
  
  unfolds.
  splits; try solve [
                unfolds;
                introv Hf; inverts Hf].
  eapply TCBList_P_rtbl_add_simpl_version; eauto.
  rewrite <-H19.
  auto.
  intros.
  lets Hnas : tcbjoin_tid_neq H13 H21.
  unfolds in Ha3.
  eapply Ha3; eauto.
  lets Haxc  : TcbMod.join_get_r H13 H21.
  lets Haa : TcbMod.join_get_r H14 Haxc.
  lets Ad :  TcbMod.join_get_l H8 Haa; eauto.
Qed.


Lemma tcb_inrtbl_not_vhold: forall v'42 v'62 v'93 v'57 v'81, RL_RTbl_PrioTbl_P v'42 v'62 v'93 ->  prio_in_tbl ((v'57)) v'42 -> nth_val' (Z.to_nat (Int.unsigned ((v'57)))) v'62 =  Vptr (v'81, Int.zero) ->   0 <= Int.unsigned v'57 < 64 -> (v'81, Int.zero) <> v'93.
Proof.
  introv H H0 H1 asdfasfd.
  unfolds in H.
  lets adaf: H H0.
  auto.
  mytac.
  (* ** ac: Check nth_val_nth_val'_some_eq. *)
  apply nth_val_nth_val'_some_eq in H4.
  rewrite H1 in H4.
  inverts H4.
  auto.
Qed.

Lemma ECBList_P_Set_Rdy_hold_sem
: forall (a : list EventCtr) (tcbls : TcbMod.map) 
         (tid : tidspec.A) (prio : priority) (msg0 msg' : msg) 
         (x y : val) (b : list EventData) (c : EcbMod.map) 
         (eid : ecbid) (nl : int32),
    TcbMod.get tcbls tid = Some (prio, wait (os_stat_sem eid) nl, msg0) ->
    EcbMod.get c eid = None ->
    ECBList_P x y a b c tcbls ->
    ECBList_P x y a b c (TcbMod.set tcbls tid (prio, rdy, msg')).
Proof.
  inductions a; intros.
  simpl in *; auto.
  simpl in H1.
  mytac.
  destruct b; tryfalse.
  destruct a.
  mytac.
  simpl.
  eexists.
  splits; eauto.
  unfolds.
  unfolds in H2.

  splits.
  
  destructs H2.
  unfolds in H2.
  mytac.
  unfolds.
  splits; unfolds;intros.

  apply H2 in H11.
  apply H11 in H12.
  mytac.
  assert (tid = x3 \/ tid <> x3) by tauto.
  destruct H13.
  subst tid.
  unfold get in *; simpl in *.
  rewrite H12 in H.
  inverts H.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  exists x3 x4 x5.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.
  
  
  apply H8 in H11.
  apply H11 in H12.
  mytac.
  assert (tid = x3 \/ tid <> x3) by tauto.
  destruct H13.
  subst tid.
  unfold get in *; simpl in *.
  rewrite H12 in H.
  inverts H.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  exists x3 x4 x5.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.

  
  apply H9 in H11.
  apply H11 in H12.
  mytac.
  assert (tid = x3 \/ tid <> x3) by tauto.
  destruct H13.
  subst tid.
  unfold get in *; simpl in *.
  rewrite H12 in H.
  inverts H.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  exists x3 x4 x5.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.

  
  apply H10 in H11.
  apply H11 in H12.
  mytac.
  assert (tid = x3 \/ tid <> x3) by tauto.
  destruct H13.
  subst tid.
  unfold get in *; simpl in *.
  rewrite H12 in H.
  inverts H.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  exists x3 x4 x5.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.



  
  unfolds.
  destructs H2;unfolds in H6;destructs H6.
  splits;intros prio' mg ng x3 Hti;
  assert (tid = x3
          \/ tid <> x3) by tauto.
  destruct H11.
  subst tid.
  unfold get in *; simpl in *.
  unfold get in *; simpl in *.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.eq_beq_true in Hti; auto.
  inverts Hti.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  eapply H6; eauto.

  destruct H11.
  subst tid.
  unfold get in *; simpl in *.
  unfold get in *; simpl in *.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.eq_beq_true in Hti; auto.
  inverts Hti.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  eapply H8; eauto.
  
  destruct H11.
  subst tid.
  unfold get in *; simpl in *.
  unfold get in *; simpl in *.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.eq_beq_true in Hti; auto.
  inverts Hti.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  eapply H9; eauto.

  destruct H11.
  subst tid.
  unfold get in *; simpl in *.
  unfold get in *; simpl in *.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.eq_beq_true in Hti; auto.
  inverts Hti.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  eapply H10; eauto.

  mytac;auto.

  do 3 eexists; splits; eauto.
  eapply IHa; eauto.
  eapply ecbmod_joinsig_get_none; eauto.
Qed.

Lemma ecblist_p_post_exwt_hold_sem (* ecblist_p_post_exwt_hold_mbox *)
: forall (v'36 : vallist) (v'12 : int32) (v'13 : vallist)
         (v'38 v'69 v'39 : int32) (v'58 : block) (v'40 : int32)
         (v'32 : block) (v'15 : int32) (v'24 : val)
         (v'35 : val) (x1 : waitset) 
         (v'0 : val) (v'1 : list EventCtr) (v'5 : list EventData)
         (v'6 : EcbMod.map) (v'7 : TcbMod.map) 
         (v'11 : EcbMod.map) (v'31 : list EventData) 
         (v'30 : list EventCtr) (v'29 : val) (v'10 v'9 : EcbMod.map)
         (prio : priority) (v'62 : TcbMod.map) (st : taskstatus)
         (msg0 msg1: msg) (y : int32) (vhold : addrval),
    Int.unsigned v'15 <= 65535 ->
    RL_RTbl_PrioTbl_P v'13 v'36 vhold ->
    v'12 <> Int.zero ->
    Int.unsigned v'12 <= 255 ->
    array_type_vallist_match Int8u v'13 ->
    length v'13 = ∘OS_EVENT_TBL_SIZE ->
    nth_val' (Z.to_nat (Int.unsigned v'12)) OSUnMapVallist = Vint32 v'38 ->
    Int.unsigned v'38 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned v'38)) v'13 = Vint32 v'69 ->
    Int.unsigned v'69 <= 255 ->
    nth_val' (Z.to_nat (Int.unsigned v'69)) OSUnMapVallist = Vint32 v'39 ->
    Int.unsigned v'39 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39))) v'36 =
    Vptr (v'58, Int.zero) ->
    nth_val' (Z.to_nat (Int.unsigned v'39)) OSMapVallist = Vint32 v'40 ->
    Int.unsigned v'40 <= 128 ->
    RL_Tbl_Grp_P v'13 (Vint32 v'12) ->
    R_ECB_ETbl_P (v'32, Int.zero)
                 (V$OS_EVENT_TYPE_SEM
                   :: Vint32 v'12
                   :: Vint32 v'15 :: v'24 :: v'35 :: v'0 :: nil,
                  v'13) v'7 ->
    RLH_ECBData_P
      (DSem v'15) (abssem v'15, x1) ->
    ECBList_P v'0 Vnull v'1 v'5 v'6 v'7 ->
    ECBList_P v'29 (Vptr (v'32, Int.zero)) v'30 v'31 v'9 v'7 ->
    EcbMod.joinsig (v'32, Int.zero) (abssem v'15, x1) v'6 v'10 ->
    EcbMod.join v'9 v'10 v'11 ->
    TcbJoin (v'58, Int.zero) (prio, st, msg0) v'62 v'7 ->
    R_PrioTbl_P v'36 v'7 vhold ->
    x1 <> nil ->
    ECBList_P v'29 Vnull
              (v'30 ++
                    ((V$OS_EVENT_TYPE_SEM
                       :: Vint32 y
                       :: Vint32 v'15 :: v'24 :: v'35 :: v'0 :: nil,
                      update_nth_val (Z.to_nat (Int.unsigned v'38)) v'13
                                     (Vint32 (v'69&ᵢInt.not v'40))) :: nil) ++ v'1)
              (v'31 ++
                    (DSem v'15 ::nil)
                    ++ v'5)
              (EcbMod.set v'11 (v'32, Int.zero)
                          (abssem v'15, remove_tid (v'58, Int.zero) x1))
              (TcbMod.set v'7 (v'58, Int.zero) (prio, rdy, msg1))
.
Proof.
  introv Hcnt.
  intros.
  unfolds in H21.
  destruct H21 as (Ha1 & Ha2 & Ha3).
  assert ( 0 <= Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39) < 64).
  clear -H5 H9.
  mauto.
  unfold nat_of_Z in Ha1.
  eapply nth_val'_imp_nth_val_vptr in H10.
  lets Hps : Ha1 H21 H10.
  apply tcbjoin_get_a in H20.
  assert ((v'58, Int.zero) <> vhold) as Hnvhold.
  apply Ha2 in H20.
  destruct H20;auto.
  destruct Hps as (sts & mg & Hget);auto.
  unfold get in *; simpl in *.
  rewrite Hget in H20.
  inverts H20.
  remember ((v'38<<ᵢ$ 3)) as px.
  remember (v'39) as py.
  clear Heqpy.
  remember (px+ᵢpy) as prio.
  remember ( (v'58, Int.zero)) as tid.
  unfolds in H14.
  destruct H14 as (Ha & Hb & Hc).
  destruct Ha as (Ha''&Ha&Ha'&Ha''').
  destruct Hb as (Hb''&Hb&Hb'&Hb''').
  lets Hz : math_unmap_get_y H1 H4.
  lets Heq1 :  math_mapval_core_prop H11; eauto.
  omega.
  subst v'40.
  assert (v'38 = Int.shru prio ($3)).
  subst.
  clear -Hz H9.
  mauto.
  assert (py = prio &ᵢ $ 7).
  subst prio. 
  rewrite Heqpx.
  clear -Hz H9.
  mauto.
  rewrite H14 in H6.
  assert (PrioWaitInQ (Int.unsigned prio) v'13) as Hcp.
  unfolds.
  do 3 eexists; splits; eauto.
  rewrite Int.repr_unsigned.
  eapply nth_val'_imp_nth_val_int; eauto.
  rewrite Int.repr_unsigned.
  rewrite <- H20.
  unfold Int.one.
  eapply math_8_255_eq; eauto.
  
  unfold Int.zero in H0.
  rewrite <-H14 in *.
  lets Hneq :  rl_tbl_grp_neq_zero H1 H0  H4 H6 H13.
  omega.
  auto.
  lets Hecp : Ha Hcp.
  unfold V_OSEventType in Hecp.
  simpl nth_val in Hecp.
  assert (Some (V$OS_EVENT_TYPE_SEM) = Some (V$OS_EVENT_TYPE_SEM)) by auto.
  apply Hecp in H23.
  clear Hecp.
  rename H23 into Hecp.
  destruct Hecp as (ct & nl & mg & Hcg).
  assert (ct = tid) as Hed.
  assert (ct = tid \/ ct <> tid)  by tauto.
  destruct H23; auto.
  lets Heqs : Ha3 H23 Hcg Hget.
  rewrite Int.repr_unsigned in Heqs.
  tryfalse.
  subst ct.
  unfold get in Hcg; simpl in Hcg.
  rewrite Hget in Hcg.
  inversion Hcg.
  subst mg st .
  clear Hcg.
  
  lets Hsds : ecb_set_join_join  (abssem v'15, remove_tid tid x1)  H18  H19.
  destruct Hsds as ( vv & Hsj1 & Hsj2).

  eapply semacc_compose_EcbList_P.
  instantiate (1:= (v'32, Int.zero)).
  unfolds.
  splits.
  unfolds.
  splits;unfolds.
  Focus 2.
  
  introv Hprs Hxx.
  clear Hxx.
  apply prio_wt_inq_convert in Hprs.
  destruct Hprs as (Hprs1 & Hprs2).
  rewrite H14 in Hprs1.
  rewrite H20 in Hprs1.
  lets Hrs : prio_wt_inq_tid_neq  H6 H21 .
  destruct Hrs as (Hrs & _).
  apply Hrs in Hprs1.
  destruct Hprs1 as (Hpq & Hneq).
  unfolds in Ha.
  lets Hxs : Ha Hpq.
  rewrite Int.repr_unsigned in Hxs.
  destruct Hxs as (tid' & nn & mm & Htg).
  unfolds;simpl;auto.
  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H23.
  subst tid'.
  unfold get in Htg; simpl in Htg.
  rewrite Hget in Htg.
  inversion Htg.
  tryfalse.
  exists tid' nn mm.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false;eauto.

  intros.
  unfolds in H25;simpl in H25;tryfalse.
  intros.
  unfolds in H25;simpl in H25;tryfalse.
  intros.
  unfolds in H25;simpl in H25;tryfalse.
  
  3:eauto.

  unfolds.
  splits;
    intros prio' mm nn tid'.
  Focus 2.
  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H23.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  unfolds in Hb.
  lets Hga : Hb Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in Ha3.
  lets Hneqp: Ha3 H23 Hget Hgs.
  assert ( PrioWaitInQ (Int.unsigned prio') v'13 /\ prio' <> prio) .
  splits; auto.

  lets Hrs : prio_wt_inq_tid_neq  H6 H21 .
  destruct Hrs as (_ & Hrs).
  apply Hrs in H25.
  rewrite H20.
  rewrite H14.
  auto.

  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H23.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  unfolds in Hb''.
  lets Hga : Hb'' Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in Ha3.
  lets Hneqp: Ha3 H23 Hget Hgs.
  assert ( PrioWaitInQ (Int.unsigned prio') v'13 /\ prio' <> prio) .
  splits; auto.
  unfolds in Hx;simpl in Hx;tryfalse.

  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H23.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  unfolds in Hb'.
  lets Hga : Hb' Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in Ha3.
  lets Hneqp: Ha3 H23 Hget Hgs.
  assert ( PrioWaitInQ (Int.unsigned prio') v'13 /\ prio' <> prio) .
  splits; auto.
  unfolds in Hx;simpl in Hx;tryfalse.

  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H23.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  unfolds in Hb'''.
  lets Hga : Hb''' Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in Ha3.
  lets Hneqp: Ha3 H23 Hget Hgs.
  assert ( PrioWaitInQ (Int.unsigned prio') v'13 /\ prio' <> prio) .
  splits; auto.
  unfolds in Hx;simpl in Hx;tryfalse.

  simpl fst in Hc;simpl;auto.

  5:eauto.
  4:eauto.
  unfolds.
  splits; auto.
  unfolds.
  split.
  intros.
  destruct H15 as (Ht1 & Ht2 & Ht3).
  apply Ht2 in H23.
  subst x1.
  tryfalse.
  intros.
  destruct H15 as (Ht1 & Ht2 & Ht3).
  apply Ht3 in H22.
  auto.
  
  eapply ECBList_P_Set_Rdy_hold_sem;eauto.
  rewrite Int.repr_unsigned.  
  eauto.
  eapply joinsig_join_getnone; eauto.
  eapply ECBList_P_Set_Rdy_hold_sem;eauto.
  rewrite Int.repr_unsigned.  
  eauto.
  eapply  joinsig_get_none; eauto.
Qed.


Lemma rh_tcblist_ecblist_p_post_exwt_aux_sem 
: forall (v'8 tid0 : tid) (v'11 : EcbMod.map) 
         (v'7 : TcbMod.map) (v'9 v'10 : EcbMod.map) 
         (eid : tidspec.A) x 
         (x0 : maxlen) (x1 : waitset) (v'6 : EcbMod.map) 
         (prio : priority) (msg0 : msg) 
         (st : taskstatus),
    RH_TCBList_ECBList_P v'11 v'7 v'8 ->
    EcbMod.join v'9 v'10 v'11 ->
    EcbMod.joinsig eid (abssem x, x1) v'6 v'10 ->
    In tid0 x1 ->
    TcbMod.get v'7 tid0 = Some (prio, st, msg0) ->
    exists xl, st = wait (os_stat_sem eid) xl
.
Proof.
  intros.
  unfolds in H.
  destruct H as (Hexaa & Hex & Hexa & Hexaaa).
  lets Hget : EcbMod.join_joinsig_get H0 H1.
  assert (EcbMod.get v'11 eid = Some (abssem x, x1) /\ In tid0 x1).
  split; auto.
  apply Hex in H.
  mytac.
  unfold get in H; simpl in H.
  rewrite H3 in H.
  inverts H.
  eauto.
Qed.


Lemma rh_tcblist_ecblist_p_post_exwt_sem
: forall (v'8 tid : tid) (v'11 : EcbMod.map) 
         (v'7 : TcbMod.map) (v'9 v'10 : EcbMod.map) 
         (eid : tidspec.A) x 
         (x0 : maxlen) (x1 : waitset) (v'6 : EcbMod.map) 
         (prio : priority) (msg0 msg1: msg) 
         (x00 : addrval) (xl : int32),
    RH_TCBList_ECBList_P v'11 v'7 v'8 ->
    EcbMod.join v'9 v'10 v'11 ->
    EcbMod.joinsig eid (abssem x , x1) v'6 v'10 ->
    In tid x1 ->
    TcbMod.get v'7 tid = Some (prio, wait (os_stat_sem eid) xl, msg0) ->
    RH_TCBList_ECBList_P
      (EcbMod.set v'11 eid (abssem x, remove_tid tid x1))
      (TcbMod.set v'7 tid (prio, rdy, msg1)) v'8
.
Proof.
  intros.
  unfolds.
  splits.
  Focus 2.
  splits; intros.
  destruct H4.
  unfolds in H.
  destruct H as (Hy&H&Hx&Hz).
  destruct H.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H7.
  subst.
  apply ecbmod_joinsig_get in H1.
  lets Hget : EcbMod.join_get_get_r H0 H1.
  assert (EcbMod.get v'11 eid = Some (abssem x, x1)/\ In tid0 x1 ).
  splits; auto.
  lets Hsa : H H7.
  mytac.
  unfold get in H9; simpl in H9.
  rewrite H3 in H9.
  inverts H9.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H9.
  subst.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  inverts H4.
  (* ** ac: Check in_wtset_rm_notin. *)
  apply in_wtset_rm_notin in H8.
  tryfalse.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  assert (EcbMod.get v'11 eid0 = Some (abssem n, wls) /\ In tid0 wls ).

  splits; auto.
  lets Hsc : H H10.
  mytac.
  unfold get in *; simpl in *.
  rewrite H3 in H12.
  inverts H12.
  tryfalse.
  rewrite TcbMod.set_sem .
  rewrite tidspec.neq_beq_false; auto.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H8.
  subst.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  inverts H4.
  (* ** ac: Check tidneq_inwt_in. *)
  lets Hbss :tidneq_inwt_in x1 H7.
  destruct Hbss as (Hbss & _).
  lets Hbssc : Hbss H5.
  apply ecbmod_joinsig_get in H1.
  lets Hget : EcbMod.join_get_get_r H0 H1.
  assert ( EcbMod.get v'11 eid0 = Some (abssem n, x1) /\ In tid0 x1 ).
  splits; auto.
  apply H in H4.
  mytac.
  do 3 eexists; eauto.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  assert ( EcbMod.get v'11 eid0 = Some (abssem n, wls)/\ In tid0 wls ).
  splits; auto.
  apply H in H9.
  mytac.
  do 3 eexists; eauto .
  apply ecbmod_joinsig_get in H1.
  lets Hget : EcbMod.join_get_get_r H0 H1.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H5.
  subst.
  rewrite TcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  inverts H4.
  rewrite TcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  
  unfolds in H.
  destruct H as (H6 & H & H7 & H8).
  destruct H.
  apply H9 in H4.
  mytac.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H11.
  subst.
  unfold get in *; simpl in *.
  rewrite H4 in Hget.
  inverts Hget.
  lets Hbss :tidneq_inwt_in  x1 H5.
  destruct Hbss as (_ & Hbss).
  lets Hbssc : Hbss H10.
  rewrite EcbMod.set_sem.
  rewrite tidspec.eq_beq_true; auto.
  do 2 eexists; splits; eauto.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 2 eexists; splits; eauto.


  splits; intros.
  destruct H4.
  unfolds in H.
  destruct H as (H&_).
  destruct H.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H7;subst.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  tryfalse.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  assert (EcbMod.get v'11 eid0 = Some (absmsgq x2 y, qwaitset) /\ In tid0 qwaitset).
  split;auto.
  apply H in H8.
  mytac.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H9;subst.
  unfold get in *; simpl in *.
  rewrite H3 in H8;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  eauto.

  unfolds in H.
  destruct H as (H&_).
  destruct H.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H6;subst.
  rewrite TcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  inverts H4.

  rewrite TcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  apply H5 in H4.
  mytac.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H8;subst.
  apply ecbmod_joinsig_get in H1.
  lets Hget : EcbMod.join_get_get_r H0 H1.
  unfold get in *; simpl in *.
  rewrite H4 in Hget;tryfalse.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 3 eexists;split;eauto.

  
  splits; intros.
  destruct H4.
  unfolds in H.
  destruct H as (Hh&Hr&H&_).
  destruct H.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H7;subst.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  tryfalse.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  assert (EcbMod.get v'11 eid0 = Some (absmbox n, wls) /\ In tid0 wls).
  split;auto.
  apply H in H8.
  mytac.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H9;subst.
  unfold get in *; simpl in *.
  rewrite H3 in H8;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  eauto.

  unfolds in H.
  destruct H as (Hh&Hr&H&_).
  destruct H.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H6;subst.
  rewrite TcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  inverts H4.

  rewrite TcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  apply H5 in H4.
  mytac.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H8;subst.
  apply ecbmod_joinsig_get in H1.
  lets Hget : EcbMod.join_get_get_r H0 H1.
  unfold get in *; simpl in *.
  rewrite H4 in Hget;tryfalse.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 2 eexists;split;eauto.

  
  splits; intros.
  destruct H4.
  unfolds in H.
  destruct H as (Hh&Hhh&Hx&H).
  destruct H.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H7;subst.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  tryfalse.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  assert (EcbMod.get v'11 eid0 = Some (absmutexsem n1 n2, wls) /\ In tid0 wls).
  split;auto.
  apply H in H8.
  mytac.
  assert (Htmp:tid = tid0 \/ tid <> tid0) by tauto.
  destruct Htmp;subst.
  unfold get in *; simpl in *.
  rewrite H3 in H8;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  eauto.

  unfolds in H.
  destruct H as (Hh&Hx&Hhh&H).
  destruct H.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H6;subst.
  rewrite TcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  inverts H4.

  rewrite TcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  apply H5 in H4.
  mytac.
  assert (Htmp:eid = eid0 \/ eid <> eid0) by tauto.
  destruct Htmp;subst.
  apply ecbmod_joinsig_get in H1.
  lets Hget : EcbMod.join_get_get_r H0 H1.
  unfold get in *; simpl in *.
  rewrite H4 in Hget;tryfalse.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 3 eexists;split;eauto.


  apply Mutex_owner_hold_for_set_tcb.
  eapply Mutex_owner_set; eauto.
  intro; mytac.
  inverts H4.
  unfolds in H.
  mytac.
  unfolds in H6; mytac.
Qed.


Lemma sempost_grp_wls_nil':
  forall v'36 v'6 vhold v'7 v'13 v'12 v'32 x v'24 v'35 v'0 v'11 v'8 v'9 v'10 x1,
    v'12 = Int.zero ->
    R_PrioTbl_P v'36 v'7 vhold ->
    RL_Tbl_Grp_P v'13 (Vint32 v'12) ->
    R_ECB_ETbl_P (v'32, Int.zero)
                 (V$OS_EVENT_TYPE_SEM
                   :: Vint32 v'12
                   :: Vint32 x :: v'24 :: v'35 :: v'0 :: nil,
                  v'13) v'7 ->
    RH_TCBList_ECBList_P v'11 v'7 v'8 ->
    EcbMod.join v'9 v'10 v'11 ->
    EcbMod.joinsig (v'32, Int.zero) (abssem x , x1) v'6 v'10 ->
    x1 = nil.
Proof.
  intros.
  unfolds in H2.
  destruct H2 as (H2 & H2' & _).
  destruct H2 as (_ & H2 & _ & _).
  destruct H2' as (_ & H2' & _ & _).
  unfolds in H2.
  unfolds in H2'.
  

  unfolds in H3.
  unfolds in H1.
  unfolds in H0.
  destruct H3 as (_ & H3 & _ & _).
  unfolds in H3.
  destruct H3 as (H3 & H3').

  lets Hg : EcbMod.join_joinsig_get H4 H5.
  clear H4 H5.
  assert ( x1 = nil \/ x1 <> nil) by tauto.
  destruct H4; intros; auto.

  idtac.
  apply something_in_not_nil in H4.
  inversion H4.
  assert (EcbMod.get v'11 (v'32, Int.zero) = Some (abssem x, x1) /\ In x0 x1) by tauto.
  lets aadf : H3 H6.
  mytac.
  lets bbdf : H2' H10.
  destruct bbdf.
  unfolds in H.
  do 3 destruct H.
  destruct H as (Ha & Hb & Hc & Hd& He).
  cut ( 0<=(∘(Int.unsigned x7)) <8)%nat.
  intro.
  assert (V$0 = V$0) by auto.
  lets adfafd : H1 H Hd H12.
  destruct adfafd.
  destruct H13.
  destruct H14.
  cut ( $ 0&ᵢ($ 1<<ᵢ$ Z.of_nat ∘(Int.unsigned x7)) = $ 0).
  intro.
  apply H13 in H17.
  subst x8.

  lets rg : rg1 Ha Hb.
  clear -He rg.
  false.
  gen He.
  mauto.

  lets rg : rg2 Ha Hc.
  clear -rg.
  mauto.

  lets rg : rg2 Ha Hc.
  clear -rg.
  mauto.
Qed.

Lemma sempost_inc_RH_TCBList_ECBList_P_hold:
  forall mqls tcbls ct a n wl,
    RH_TCBList_ECBList_P mqls tcbls ct ->
    EcbMod.get mqls a = Some (abssem n, wl) ->
    Int.ltu n ($ 65535) = true ->
    RH_TCBList_ECBList_P 
      (EcbMod.set mqls a (abssem (Int.add n Int.one), wl)) tcbls ct.
Proof.
  intros.
  unfold RH_TCBList_ECBList_P in *.
  destruct H as [Hq [Hsem [Hmbox Hmutex]]] .
  intuition.


(***************** Q begin ************)

  unfold RH_TCBList_ECBList_Q_P in *.
  destruct Hq as [F1 F2].
  intuition.
  destruct (tidspec.beq a eid) eqn:Feq.
  (* ** ac: Check tidspec.beq_true_eq. *)
  apply tidspec.beq_true_eq in Feq; substs.
  unfold get in *; simpl in *.
  match goal with
    | H: EcbMod.get (EcbMod.set _ _ _) _ = _ |- _ =>
        rewrite EcbMod.set_a_get_a in H; tryfalse; auto
  end.

  apply CltEnvMod.beq_refl.
  eapply F1.
  split; 
    [ rewrite EcbMod.set_a_get_a' in H2; eauto
    | eauto].

  destruct (tidspec.beq a eid) eqn:Feq.
  apply tidspec.beq_true_eq in Feq; substs.
  unfold get in *; simpl in *.
  match goal with
    | H: TcbMod.get _ _ = _ |- _ =>
        apply F2 in H; mytac; tryfalse
  end.
      
  rewrite EcbMod.set_a_get_a'; 
    [ eapply F2; eauto
    | auto].
(**************** Q end ************)  

  unfold RH_TCBList_ECBList_SEM_P in *.
  destruct Hsem as [F1 F2].
  intuition.
  destruct (tidspec.beq a eid) eqn:Feq.
  apply tidspec.beq_true_eq in Feq; substs.
  unfold get in *; simpl in *.
  rewrite EcbMod.set_a_get_a in H2; eauto.
  inverts H2.
  eapply F1.
  split; eauto.

  apply CltEnvMod.beq_refl.
  
  eapply F1.
  split;
    [ rewrite EcbMod.set_a_get_a' in H2; eauto
    | eauto].

  destruct (tidspec.beq a eid) eqn:Feq.
  apply tidspec.beq_true_eq in Feq; substs.
  unfold get in *; simpl in *.
  apply F2 in H; mytac.
  rewrite H in H0.
  inverts H0.
  exists (Int.add n Int.one) wl.
  rewrite EcbMod.set_a_get_a; eauto.

  apply CltEnvMod.beq_refl.

  rewrite EcbMod.set_a_get_a'; 
    [ eapply F2; eauto
    | auto].

  unfold RH_TCBList_ECBList_MBOX_P in *.
  destruct Hmbox as [F1 F2].
  intuition.
  destruct (tidspec.beq a eid) eqn:Feq.

  apply tidspec.beq_true_eq in Feq; substs.
  unfold get in *; simpl in *.
  match goal with
    | H: EcbMod.get (EcbMod.set _ _ _) _ = _ |- _ =>
        rewrite EcbMod.set_a_get_a in H; tryfalse; auto
  end.

  apply CltEnvMod.beq_refl.
  
  eapply F1.
  split; 
    [ rewrite EcbMod.set_a_get_a' in H2; eauto
    | eauto].

  destruct (tidspec.beq a eid) eqn:Feq.
  apply tidspec.beq_true_eq in Feq; substs.
  unfold get in *; simpl in *.
  match goal with
    | H: TcbMod.get _ _ = _ |- _ =>
        apply F2 in H; mytac; tryfalse
  end.
      
  rewrite EcbMod.set_a_get_a'; 
    [ eapply F2; eauto
    | auto].


  unfold RH_TCBList_ECBList_MUTEX_P in *.
  destruct Hmutex as [F1 F2].
  intuition.
  destruct (tidspec.beq a eid) eqn:Feq.
  apply tidspec.beq_true_eq in Feq; substs.
  unfold get in *; simpl in *.

  match goal with
    | H: EcbMod.get (EcbMod.set _ _ _) _ = _ |- _ =>
        rewrite EcbMod.set_a_get_a in H; tryfalse; auto
  end.

  apply CltEnvMod.beq_refl.

  eapply F1.
  split; 
    [ rewrite EcbMod.set_a_get_a' in H4; eauto
    | eauto].

  destruct (tidspec.beq a eid) eqn:Feq.
  apply tidspec.beq_true_eq in Feq; substs.
  unfold get in *; simpl in *.

  match goal with
    | Hget: TcbMod.get _ _ = _ |- _ =>
        apply H in Hget; mytac; tryfalse
  end.
      
  rewrite EcbMod.set_a_get_a'; 
    [ eapply H; eauto
    | auto].

  eapply Mutex_owner_set.
  unfolds.
  intros.
  mytac.
  inverts H3.
  auto.
Qed.

Lemma node_fold':
  forall s P vl t b,
    s |= Astruct (b, Int.zero) t vl ** P ->
    struct_type_vallist_match t vl ->
    s |= node (Vptr (b, Int.zero)) vl t ** P.
  intros.
  unfold node.
  sep pauto.
Qed.

Lemma sempost_vallist_match_assert1:
  forall x,
    Int.ltu x ($ 65535) = true ->
    Int.unsigned (Int.add x Int.one) <= 65535.
Proof.
  intros.
  int auto.
  destruct (zlt (Int.unsigned x) 65535).
  int auto.
  tryfalse.
Qed.  

Lemma sempost_struct_type_vallist_match_sem:
  forall i1 x2 x3 v'44,
    isptr v'44 ->
    isptr x2 ->
    Int.ltu i1 ($ 65535) = true ->
    struct_type_vallist_match OS_EVENT
                              (V$OS_EVENT_TYPE_SEM
                                :: V$0 :: Vint32 (i1+ᵢ$ 1) :: x2 :: x3 :: v'44 :: nil).
Proof.
  intros.
  apply sempost_vallist_match_assert1 in H1.
  pauto.
Qed.

Lemma rl_etbl_ptbl_p:
  forall l egrp v'33 i4 x6 v'22 etbl tcbls ptbl etype av,
    array_type_vallist_match Int8u etbl ->
    length etbl = ∘OS_RDY_TBL_SIZE ->
    R_ECB_ETbl_P l
                 (etype
                   :: Vint32 egrp
                   :: Vint32 i4 :: v'33 
                   :: x6 :: v'22 :: nil,
                  etbl) tcbls ->
    RL_Tbl_Grp_P etbl (Vint32 egrp) ->
    R_PrioTbl_P ptbl tcbls av->
    RL_RTbl_PrioTbl_P etbl ptbl av.
Proof.
  introv Ha Hl.
  intros.
  unfolds in H.
  unfolds in H0.
  unfolds in H1.
  unfolds.
  intros.
  unfolds in H3.
  destruct H1.
  destruct H4.
  destruct H.
  destruct H6 as (H6&Htype).
  unfolds in H6.
  unfolds in H.
  assert ( PrioWaitInQ (Int.unsigned p) etbl).
  unfolds.
  remember (Int.shru p ($3)) as px.
  remember (p &ᵢ $ 7) as py.
  lets Hxx : n07_arr_len_ex   ∘(Int.unsigned px ) Ha Hl.
  clear - Heqpx H2.
  subst px.
  mauto.
  destruct Hxx as (vx & Hth & Hvr).
  lets Has : H3 Hth; eauto.
  do 3 eexists; eauto; splits; eauto.
  rewrite Int.repr_unsigned.
  rewrite <- Heqpx.
  eauto.
  rewrite Int.repr_unsigned.
  unfold Int.one.
  subst py.
  eauto.
  destructs H.
  unfolds in Htype.
  destruct Htype.
  apply H in H7.
  unfold V_OSEventType in H7.
  simpl in H7.
  unfolds in H11;simpl in H11;inverts H11.
  assert (Some (V$OS_EVENT_TYPE_Q) = Some (V$OS_EVENT_TYPE_Q)) by auto.
  apply H7 in H11.
  
  mytac.
  rewrite Int.repr_unsigned in *.
  apply H4 in H11.
  eexists; eauto.
 
  destruct H11.
  unfolds in H11;simpl in H11;inverts H11.
  apply H8 in H7.
  assert (Some (V$OS_EVENT_TYPE_SEM) = Some (V$OS_EVENT_TYPE_SEM)) by auto.
  apply H7 in H11.
  mytac.
  rewrite Int.repr_unsigned in *.
  apply H4 in H11.
  eexists; eauto.
  
  destruct H11.
  unfolds in H11;simpl in H11;inverts H11.
  apply H9 in H7.
  assert (Some (V$OS_EVENT_TYPE_MBOX) = Some (V$OS_EVENT_TYPE_MBOX)) by auto.
  apply H7 in H11.
  mytac.
  rewrite Int.repr_unsigned in *.
  apply H4 in H11.
  eexists; eauto.

  unfolds in H11;simpl in H11;inverts H11.
  apply H10 in H7.
  assert (Some (V$OS_EVENT_TYPE_MUTEX) = Some (V$OS_EVENT_TYPE_MUTEX)) by auto.
  apply H7 in H11.
  mytac.
  rewrite Int.repr_unsigned in *.
  apply H4 in H11.
  eexists; eauto.
Qed.   
