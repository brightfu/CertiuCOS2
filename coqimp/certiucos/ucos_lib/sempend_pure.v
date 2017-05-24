Require Export sem_common.

Open Scope code_scope.
Hint Resolve CltEnvMod.beq_refl: brel .


Lemma TCBListP_head_in_tcb:
  forall v'51 v'52 v'22 x9 x8 i9 i8 i6 i5 i4 i3 v'33 v'34 v'50 xx,
    TCBList_P (Vptr v'52)
          ((v'51
            :: v'22
               :: x9
                  :: x8
                     :: Vint32 i9
                        :: Vint32 i8
                           :: Vint32 xx
                              :: Vint32 i6
                                 :: Vint32 i5
                                    :: Vint32 i4 :: Vint32 i3 :: nil) :: v'33)
          v'34 v'50 ->
        exists st, TcbMod.get v'50 v'52 = Some ( xx, st, x8).
Proof.
  intros.
  unfolds in H.
  fold TCBList_P in H.
  mytac.
  unfolds in H2.
  destruct x2; destruct p.
  mytac.
  unfolds in H2.
  unfolds in H4.
  simpl in H2.
  simpl in H4.
  inverts H2.
  inverts H4.
  inverts H.
  unfolds in H0; simpl in H0.
  inverts H0.
  unfold TcbJoin in H1.
  unfold join in H1; simpl in H1.
  unfolds in H6.
  eexists.
  eapply TcbMod.join_get_l.
  eauto.
  eapply TcbMod.get_a_sig_a.
  apply CltEnvMod.beq_refl.
Qed.

Lemma low_stat_rdy_imp_high:
  forall a b c d e f g h i j st rtbl p t m,
    array_type_vallist_match Int8u rtbl ->
    length rtbl = ∘OS_RDY_TBL_SIZE ->
    RL_TCBblk_P  (a
                    :: b
                    :: c
                    :: d
                    :: Vint32 e
                    :: Vint32 st
                    :: Vint32 f
                    :: g
                    :: h :: i :: j :: nil)
    ->
    R_TCB_Status_P
      (a
         :: b
         :: c
         :: d
         :: Vint32 e
         :: Vint32 st
         :: Vint32 f
         :: g
         :: h :: i :: j :: nil)
      rtbl (p, t, m) -> Int.eq st ($ OS_STAT_RDY) = true ->
    Int.eq e ($ 0) = true ->
    t = rdy .
 Proof.
  introv Hz Hlen  Ht  Hr Heq Heqq.
  funfold Ht.
  unfolds in Hr.
  mytac.
  clear H0 H2.
  unfolds in H.
  unfolds in H1.
  mytac.
  unfolds in H0.
  unfolds in H1.
  unfolds in H2.
  unfolds in H3.
  unfolds in H4.
  unfold RdyTCBblk in *.
  unfold V_OSTCBStat in *; simpl in *.
  unfold WaitTCBblk in *; simpl in *.
  unfold V_OSTCBPrio,  V_OSTCBDly , V_OSTCBEventPtr in *; simpl in *.
  assert (Some (Vint32 x) = Some (Vint32 x)).
  auto.
  unfold Pos.to_nat in Hlen.
  simpl in Hlen.
  assert ( 0 <= Int.unsigned x < 64 ) by omega.
  lets Hdis : prio_rtbl_dec  Hz Hlen; eauto.
  assert (if Int.eq x4 ($ OS_STAT_RDY) then  x4  =($ OS_STAT_RDY)
          else x4 <> ($ OS_STAT_RDY)).
  apply Int.eq_spec.
  rewrite Heq in H8.
  subst.
  destruct Hdis as [Hd1 | Hd2].
  assert (Some (Vint32 x) = Some (Vint32 x) /\
          prio_in_tbl x rtbl). 
  split; auto.
  apply H in H8.
  destruct H8 as ( _ & Had & Hzd).
  destruct Hzd. inverts H8.
  auto.
  assert (Some (Vint32 e) = Some (Vint32 e)).
  auto.
  assert (Some (Vint32 x) = Some (Vint32 x) /\
          prio_not_in_tbl x  rtbl/\Some (Vint32 e) = Some (Vint32 e)).   
  splits; auto.
  apply H0 in H9; auto.
  mytac.
  apply ltu_eq_false in H9.
  unfold Int.zero in H9.
  rewrite Heqq in H9.
  tryfalse.
Qed.
 
Lemma sempend_TCBListP_head_in_tcb_rdy:
  forall v'51 v'52 v'22 x9 x8 i9 i8 i6 i5 i4 i3 v'33 v'50 xx rtbl,
    array_type_vallist_match Int8u rtbl ->
    length rtbl = ∘OS_RDY_TBL_SIZE ->
    TCBList_P (Vptr v'52)
              ((v'51
                  :: v'22
                  :: x9
                  :: x8
                  :: Vint32 i9
                  :: Vint32 i8
                  :: Vint32 xx
                  :: Vint32 i6
                  :: Vint32 i5
                  :: Vint32 i4 :: Vint32 i3 :: nil) :: v'33)
              rtbl v'50 ->
    i9 = $ 0 ->
    i8 = $ OS_STAT_RDY ->
    TcbMod.get v'50 v'52 = Some ( xx, rdy, x8).
Proof.
  intros.
  unfolds in H1.
  fold TCBList_P in H1.
  mytac_H.
  unfolds in H6.
  destruct x2; destruct p.
  mytac_H.
  unfolds in H4; unfolds in H2; unfolds in H3.
  simpl in H2; simpl in H4; simpl in H3.
  inverts H2; inverts H4; inverts H3.
  assert (t = rdy).
    eapply low_stat_rdy_imp_high; eauto.
  inverts H2.
  inverts H1.
  unfold TcbJoin in H5.
  eapply TcbMod.join_get_l.
  eauto.
  eapply TcbMod.get_a_sig_a.
  apply CltEnvMod.beq_refl.
Qed.

Lemma tcblist_p_node_rl_sem:
  forall v'33 v'49 v'42 v'47 v'21 x10 x9 i i8 i7 i6 i5 i4 i3 i1 v'32 ,
    TCBList_P (Vptr (v'49, Int.zero))
          ((v'47
            :: v'21
               :: x10
                  :: x9
                     :: Vint32 i8
                        :: Vint32 i7
                           :: Vint32 i6
                              :: Vint32 i5
                                 :: Vint32 i4
                                    :: Vint32 i3 :: Vint32 i1 :: nil) :: v'32)
          v'33 v'42 ->
    RL_TCBblk_P
     (v'47
      :: v'21
         :: x10
            :: x9
               :: Vint32 i
                  :: V$OS_STAT_SEM
                     :: Vint32 i6
                        :: Vint32 i5
                           :: Vint32 i4 :: Vint32 i3 :: Vint32 i1 :: nil).
Proof.
  introv Ht.
  simpl in Ht.
  mytac;simpl_hyp.
  inverts H.
  unfolds in H2.
  destruct x2.
  destruct p.
  mytac; simpl_hyp.
  funfold H2.
  unfolds.
  do 6 eexists;splits; try unfolds; simpl;  eauto.
  splits; auto.
  eexists.
  splits.
  unfolds.
  simpl; eauto.
  introv Hf.
  inverts Hf.
Qed.

  
  
Lemma ECBList_P_high_tcb_block_hold_sem:
  forall  ectrl head tail msgql ecbls tcbls ptcb prio  m qid time,
    ECBList_P head tail ectrl msgql ecbls tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, rdy, m) ->
    EcbMod.get ecbls qid = None ->
    ECBList_P head tail ectrl msgql ecbls 
              (TcbMod.set tcbls ptcb (prio, wait (os_stat_sem qid) time, m)).
Proof.
  inductions ectrl.
  intros.
  simpl.
  simpl in H.
  auto.
  intros.
  simpl in H.
  mytac.
  destruct msgql; tryfalse.
  destruct a.
  mytac.
  simpl.
  exists x.
  splits; auto.
  unfolds.
  destruct H2 as (Hr1 & Hr2 & Hr3).
  destruct Hr1 as (Hra3 & Hra1 & Hra2 & Hra4).
  destruct Hr2 as (Hrb3 & Hrb1 & Hrb2 & Hrb4).
  simpl in Hr3.
  splits.
  unfolds.
  splits.
  Focus 2.
  {
    unfolds.
    intros.
    eapply Hra1 in H6;eauto.
    mytac.
    assert (x3 = ptcb \/ x3 <> ptcb) by tauto.
    destruct H7.
    subst.
    unfold get in H6; simpl in H6.
    rewrite H0 in H6.
    inverts H6.
    exists x3 x4 x5.
    rewrite TcbMod.set_sem.
    rewrite tidspec.neq_beq_false; eauto.
  }
  Unfocus.
  Focus 2.
  {
    unfolds.
    intros.
    eapply Hra2 in H6;eauto.
    mytac.
    assert (x3 = ptcb \/ x3 <> ptcb) by tauto.
    destruct H7.
    subst.
    unfold get in H6; simpl in H6.
    rewrite H0 in H6.
    inverts H6.
    exists x3 x4 x5.
    rewrite TcbMod.set_sem.
    rewrite tidspec.neq_beq_false; eauto.
  }
  Unfocus.
  {
    unfolds.
    intros.
    eapply Hra3 in H6;eauto.
    mytac.
    assert (x3 = ptcb \/ x3 <> ptcb) by tauto.
    destruct H7.
    subst.
    unfold get in H6; simpl in H6.
    rewrite H0 in H6.
    inverts H6.
    exists x3 x4 x5.
    rewrite TcbMod.set_sem.
    rewrite tidspec.neq_beq_false; eauto.
  }
  {
    unfolds.
    intros.
    eapply Hra4 in H6;eauto.
    mytac.
    assert (x3 = ptcb \/ x3 <> ptcb) by tauto.
    destruct H7.
    subst.
    unfold get in H6; simpl in H6.
    rewrite H0 in H6.
    inverts H6.
    exists x3 x4 x5.
    rewrite TcbMod.set_sem.
    rewrite tidspec.neq_beq_false; eauto.
  }
  unfolds.
  splits.
  Focus 2.
  {
    unfolds.
    intros.
    assert (tid = ptcb \/ tid <> ptcb) by tauto.
    destruct H6.
    subst.
    rewrite TcbMod.set_sem in H2.
    rewrite tidspec.eq_beq_true in H2; eauto.
    inverts H2.
    apply ecbmod_joinsig_get in H3.
    rewrite H3 in H1.
    tryfalse.
    rewrite TcbMod.set_sem in H2.
    rewrite tidspec.neq_beq_false in H2; eauto.
  }
  Unfocus.

  unfolds.
  intros.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.
  destruct H6.
  subst.
  rewrite TcbMod.set_sem in H2.
  rewrite tidspec.eq_beq_true in H2; eauto.
  inverts H2.
  rewrite TcbMod.set_sem in H2.
  rewrite tidspec.neq_beq_false in H2; eauto.
  unfolds.
  intros.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.
  destruct H6.
  subst.
  rewrite TcbMod.set_sem in H2.
  rewrite tidspec.eq_beq_true in H2; eauto.
  inverts H2.
  rewrite TcbMod.set_sem in H2.
  rewrite tidspec.neq_beq_false in H2; eauto.
  unfolds.
  intros.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.
  destruct H6.
  subst.
  rewrite TcbMod.set_sem in H2.
  rewrite tidspec.eq_beq_true in H2; eauto.
  inverts H2.
  rewrite TcbMod.set_sem in H2.
  rewrite tidspec.neq_beq_false in H2; eauto.
  simpl; auto.
  do 3 eexists; splits; eauto.
  eapply IHectrl; eauto.
  eapply  ecbmod_joinsig_get_none; eauto.
Qed.

Lemma ejoin_get_none_r : forall ma mb mc x a, EcbMod.get ma x = Some a -> EcbMod.join ma mb mc -> EcbMod.get mb x = None.
Proof.
  intros.
  unfolds in H0.
  lets adf : H0 x.
  destruct (EcbMod.get ma x).
  destruct (EcbMod.get mb x).
  tryfalse.
  auto.
  destruct (EcbMod.get mb x).
  tryfalse.
  auto.
Qed.

Lemma ejoin_get_none_l : forall ma mb mc x a, EcbMod.get mb x = Some a -> EcbMod.join ma mb mc -> EcbMod.get ma x = None.
Proof.
  intros.
  apply EcbMod.join_comm in H0.
  eapply ejoin_get_none_r; eauto.
Qed.

Lemma R_ECB_ETbl_P_high_tcb_block_hold:
  forall (l : addrval) (vl : vallist) (egrp : int32) 
    (v2 v3 v4 v5 : val) (etbl : vallist) (tcbls : TcbMod.map)
    (ptcb : tidspec.A) (prio : int32) (st : taskstatus) 
    (m : msg) (y bity bitx ey time : int32) (av : addrval),
  Int.unsigned prio < 64 ->
  R_PrioTbl_P vl tcbls av ->
  R_ECB_ETbl_P l
    (V$OS_EVENT_TYPE_SEM :: Vint32 egrp :: v2 :: v3 :: v4 :: v5 :: nil, etbl)
    tcbls ->
  TcbMod.get tcbls ptcb = Some (prio, st, m) ->
  y = Int.shru prio ($ 3) ->
  bity = Int.shl ($ 1) y ->
  bitx = Int.shl ($ 1) (prio &ᵢ $ 7) ->
  nth_val ∘(Int.unsigned y) etbl = Some (Vint32 ey) ->
  R_ECB_ETbl_P l
    (V$OS_EVENT_TYPE_SEM
     :: Vint32 (Int.or egrp bity) :: v2 :: v3 :: v4 :: v5 :: nil,
    update_nth_val ∘(Int.unsigned y) etbl (Vint32 (Int.or ey bitx)))
    (TcbMod.set tcbls ptcb (prio, wait (os_stat_sem l) time, m))
.
Proof.
  introv Hran Hrs  Hre Htc Hy Hb1 Hb2 Hnth.
  subst.
  unfolds in Hre.
  destruct Hre as (Hre1 & Hre2 & Het).
  unfolds.
  splits.
  unfolds.
  splits.
  Focus 2.
  {
    unfolds.
    intros.
    destruct Hre1 as (_ & Hre1 & _ & _).
    destruct Hre2 as (_ & Hre2 & _ & _).
    unfolds in Hre1.
    unfolds in Hre2.
    assert (prio = $ prio0 \/ prio <> $ prio0) by tauto.
    destruct H1.
    subst.
    exists ptcb time m.
    rewrite TcbMod.set_sem.
    erewrite tidspec.eq_beq_true; eauto.
    lets Hres : prio_wt_inq_keep Hran H1 Hnth .
    destruct Hres.
    apply H2 in H.
    apply Hre1 in H.
    mytac.
    exists x x0 x1.
    assert (x = ptcb \/ x <> ptcb) by tauto.
    destruct H4.
    subst.
    unfold get in H; simpl in H.
    rewrite Htc in H.
    inverts H.
    tryfalse.
    rewrite TcbMod.set_sem.
    erewrite tidspec.neq_beq_false; eauto.
    unfolds. 
    simpl; auto.
  }
  Unfocus.
  Focus 2.
  {
    unfolds.
    intros.
    usimpl H0.
  }
  Unfocus.
  {
    unfolds.
    intros.
    usimpl H0.
  }
  {
    unfolds.
    intros.
    usimpl H0.
  }
  unfolds.
  splits.
  Focus 2.
  {
    unfolds.
    intros.
    assert (tid = ptcb \/ tid <> ptcb) by tauto.  
    destruct H0.
    subst.
    splits.
    rewrite TcbMod.set_sem in H.
    erewrite tidspec.eq_beq_true in H; eauto.
    inverts H.
    unfolds.
    rewrite Int.repr_unsigned.
    exists ( prio0 &ᵢ $ 7).
    exists (Int.shru prio0 ($3)).
    exists ((Int.or ey ($ 1<<ᵢ(prio0 &ᵢ $ 7)))).
    splits; eauto.
    clear - Hran.
    int auto.
    eapply pure_lib.update_nth; eauto.
    rewrite Int.and_commut.
    rewrite Int.or_commut.
    unfold Int.one.
    rewrite Int.and_or_absorb.
    auto.
    unfolds; simpl; auto.
    rewrite TcbMod.set_sem in H.
    erewrite tidspec.neq_beq_false in H; eauto.
    unfolds in Hre2.
    destruct Hre2 as (_ & Hre2 & _ & _).
    lets Hasd : Hre2  H.
    destruct Hasd as (Has1 & Has2).
    splits.
    eapply prio_wt_inq_keep; eauto.
    rewrite Int.repr_unsigned.
    unfolds  in Hrs.
    destruct Hrs.
    destruct H2.
    unfolds in H3.
    lets Hdd : H3 H0 H Htc.
    eauto.
    unfolds; simpl; auto.
  }
  Unfocus.
  Focus 2.
  {
    unfolds.

    intros.
    assert (tid = ptcb \/ tid <> ptcb) by tauto.  
    destruct H0.
    subst.
    rewrite TcbMod.set_sem in H.
    erewrite tidspec.eq_beq_true in H; eauto.
    inverts H.
    rewrite TcbMod.set_sem in H.
    erewrite tidspec.neq_beq_false in H; eauto.
    destruct Hre2 as (_&_&Hre2&_).
    apply Hre2 in H.
    destruct H.
    usimpl H1.
  }
  Unfocus.
  {
    unfolds.
    intros.
    assert (tid = ptcb \/ tid <> ptcb) by tauto.  
    destruct H0.
    subst.
    rewrite TcbMod.set_sem in H.
    erewrite tidspec.eq_beq_true in H; eauto.
    inverts H.
    rewrite TcbMod.set_sem in H.
    erewrite tidspec.neq_beq_false in H; eauto.
    destruct Hre2 as (Hre2&_).
    apply Hre2 in H.
    destruct H.
    usimpl H1.
  }
  unfolds.
  intros.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.  
  destruct H0.
  subst.
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.neq_beq_false in H; eauto.
  destruct Hre2 as (_&_& _ &Hre2).
  apply Hre2 in H.
  destruct H.
  usimpl H1.
  simpl.
  unfolds.
  branch 2.
  unfolds; simpl; auto.
Qed.

Lemma TCBList_P_tcb_block_hold :
  forall ptcb v1 v2 v3 v5 v6 v8 v9 v10 v11 rtbl vl
    tcbls prio st m qid time ry,
    TCBList_P (Vptr ptcb) ((v1::v2::v3::m::v5::(Vint32 v6)::(Vint32 prio)::v8::(Vint32 v9)::(Vint32 v10)::v11::nil)::vl) rtbl tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, st, m) ->
    prio_neq_cur tcbls ptcb ( prio) ->
    st = rdy \/ (exists n, st = wait os_stat_time n) -> 
    nth_val (nat_of_Z (Int.unsigned v9)) rtbl = Some (Vint32 ry) ->
    TCBList_P (Vptr ptcb)
              ((v1::v2::(Vptr qid)::m::(Vint32 time)::(Vint32 ($ OS_STAT_SEM))::(Vint32 prio)::v8::(Vint32 v9)::(Vint32 v10)::v11::nil)
                 ::vl) 
              (update_nth_val ∘(Int.unsigned v9) rtbl (Vint32 (Int.and ry (Int.not v10)))) 
              (TcbMod.set tcbls ptcb ( prio, wait (os_stat_sem qid) ( time), m)).
Proof.
  introv  Htcb Htm Hst Hprio Hnth.
  unfolds in Htcb;fold TCBList_P in Htcb.
  mytac.
  inverts H.
  unfolds in H0.
  simpl in H0; inverts H0.
  unfolds.
  fold TCBList_P.
  exists x x0.
  exists x1.
  exists (prio,wait (os_stat_sem qid) time,m).
  splits; eauto.
  eapply tcbjoin_set; eauto.
  {
    unfolds in H2.
    destruct x2.
    destruct p.
    mytac.
    unfolds in H0.
    simpl in H0; inverts H0.
    unfolds in H;simpl in H; inverts H.
    unfolds.
    split.  
    unfolds.
    simpl.
    auto.
    funfold H2.
    split.
    auto.
    split.
    unfolds.
    do 6 eexists; splits; try unfolds; simpl; eauto.
    splits; eauto.
    eexists.
    splits.
    unfolds;simpl; eauto.
    introv Hf.
    inverts Hf.
    lets Hexa : tcbjoin_get H1 Htm.
    inverts Hexa.
    unfolds in H4.
    split.
    unfolds.
    intros.
    simpl_hyp.
    unfolds in H.
    destruct H.
    simpl_hyp.
    unfolds in H0.
    assert (prio&ᵢ$ 7 = prio&ᵢ$ 7) by auto.
    assert (Int.shru ( prio) ($ 3) =Int.shru (prio) ($ 3)) by auto.
    assert ( nth_val ∘(Int.unsigned (Int.shru (prio) ($ 3)))
                     (update_nth_val ∘(Int.unsigned (Int.shru (prio) ($ 3))) rtbl
                                     (Vint32 (ry&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))))) = 
             Some (Vint32  (ry&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))))).
    eapply pure_lib.update_nth; eauto.
    lets Hr: H0 H H2 H5.
    rewrite Int.and_assoc in Hr.
    assert (Int.not ($ 1<<ᵢ(prio&ᵢ$ 7))&ᵢ($ 1<<ᵢ(prio&ᵢ$ 7)) = $ 0).
    rewrite Int.and_commut.
    rewrite Int.and_not_self.
    auto.
    rewrite H6  in Hr.
    rewrite Int.and_zero in Hr.
    assert ( $ 1<<ᵢ(prio&ᵢ$ 7) <> $ 0) by (apply  math_prop_neq_zero2; try omega).
    unfold Int.zero in Hr.
    tryfalse.
    split.
    unfolds.
    intros.
    inverts H.
    split.
    unfolds.
    split.
    unfolds.
    intros.
    inverts H0.
    split.
    unfolds.
    intros.
    inverts H0.
    inverts H2.
    unfolds in H.
    mytac.
    inverts H.
    inverts H2.
    exists m0. auto.
    
    split.
    unfolds.
    intros.
    inverts H0.
    split.
    unfolds.
    intros.
    inverts H0.
    

    unfolds.
    intros.
    inverts H0.
    

    unfolds.
    split.
    unfolds.
    intros.
    inverts H.
    split.
    unfolds.
    intros.
    inverts H.
    split.
    unfolds.
    splits; try unfolds ; simpl ; auto.

    intros.
    subst.
    apply nth_upd_eq in H2.
    inverts H2.
    rewrite Int.and_assoc.
    assert (Int.not ($ 1<<ᵢ(prio&ᵢ$ 7))&ᵢ($ 1<<ᵢ(prio&ᵢ$ 7)) = $ 0).
    rewrite Int.and_commut.
    rewrite Int.and_not_self.
    auto.
    rewrite H.
    rewrite  Int.and_zero.
    auto.
    split.
    unfolds; simpl; auto.
    unfolds; simpl; auto.
    split.
    unfolds.
    intros.
    inverts H.
    splits; unfolds; intros; inverts H.
  }
  unfolds in H2.
  destruct x2.
  destruct p.
  mytac; simpl_hyp.
  funfold H2.
  
  Require Import OSTimeDlyPure.
  
  eapply update_rtbl_tcblist_hold; eauto.
  unfolds in Hst.
  intros.
  lets Has : tcbjoin_get_getneq H1 H.
  destruct Has.
  eapply Hst; eauto.
Qed.

Lemma RH_CurTCB_high_block_hold_sem :
  forall ptcb tcbls prio st qid time m,
    RH_CurTCB ptcb tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, st, m) ->
    RH_CurTCB ptcb (TcbMod.set tcbls ptcb
        (prio, wait (os_stat_sem qid) time, m)).
Proof.
  introv Hr Ht.
  unfolds in Hr.
  mytac.
  unfold get in H; simpl in H.
  rewrite H in Ht.
  inverts Ht.
  unfolds.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.eq_beq_true; eauto.
Qed.

Lemma RH_TCBList_ECBList_P_high_block_hold_sem :
  forall ecbls tcbls pcur qid m cnt wl prio  time,
    RH_TCBList_ECBList_P ecbls tcbls pcur ->
    EcbMod.get ecbls qid = Some (abssem cnt, wl) ->
    TcbMod.get tcbls pcur = Some (prio, rdy, m) ->
    RH_TCBList_ECBList_P (EcbMod.set ecbls qid (abssem cnt, pcur::wl)) (TcbMod.set tcbls pcur (prio, wait (os_stat_sem qid) time, m)) pcur. 
Proof.
  introv Hr Ht He.
  unfolds in Hr.
  destruct Hr as (Hr3 & Hr1 & Hr2 & Hr4).
  unfolds.
  splits.
  Focus 2.
  {
    unfolds.
    splits.
    intros.
    mytac.
    assert (qid  = eid \/ qid <> eid) by tauto.
    destruct H1.
    subst.
    rewrite EcbMod.set_sem in H.
    rewrite tidspec.eq_beq_true in H; auto.
    inverts H.
    simpl in H0.
    destruct H0.
    do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.eq_beq_true; auto.
    assert (EcbMod.get ecbls eid = Some (abssem n, wl) /\ In tid wl) by eauto.
    apply Hr1 in H0.
    mytac.
    assert (pcur = tid \/ pcur <> tid) by tauto.
    destruct  H1.
    do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.eq_beq_true; auto.
    do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.
    rewrite EcbMod.set_sem in H.
    rewrite tidspec.neq_beq_false in H; auto.
    assert (EcbMod.get ecbls eid = Some (abssem n, wls) /\ In tid wls) by eauto.
    apply Hr1 in H2.
    mytac.
    assert (pcur = tid \/ pcur <> tid) by tauto.
    destruct  H3.
    subst.
    unfold get in H2; simpl in H2.
    rewrite H2 in He.
    inverts He. 
    do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.
    intros.
    assert (pcur = tid \/ pcur <> tid) by tauto.
    destruct  H0.
    subst.
    rewrite TcbMod.set_sem in H.
    rewrite tidspec.eq_beq_true in H; eauto.
    inverts H.
    exists cnt.
    exists (tid::wl).
    splits; eauto.
    rewrite EcbMod.set_sem.
    rewrite tidspec.eq_beq_true; eauto.
    simpl; left; auto.
    rewrite TcbMod.set_sem in H.
    rewrite tidspec.neq_beq_false in H; eauto.
    apply Hr1 in H.
    mytac.
    assert (qid  = eid \/ qid <> eid) by tauto.
    destruct H2.
    subst.
    rewrite EcbMod.set_sem.
    rewrite tidspec.eq_beq_true; auto.
    do 2 eexists; splits; eauto.
    unfold get in H; simpl in H.
    rewrite H in Ht.
    inverts Ht.
    simpl.
    right; auto.
    rewrite EcbMod.set_sem.
    rewrite tidspec.neq_beq_false; auto.
    do 2 eexists; splits; eauto.
  }
  Unfocus.
  Focus 2.
  {
    splits.
    intros.
    mytac.
    assert (qid  = eid \/ qid <> eid) by tauto.
    destruct H1.
    subst.
    rewrite EcbMod.set_sem in H.
    rewrite tidspec.eq_beq_true in H; auto.
    inverts H.
    rewrite EcbMod.set_sem in H.
    rewrite tidspec.neq_beq_false in H; auto.
    assert (EcbMod.get ecbls eid =Some (absmbox n, wls) /\ In tid wls) by eauto.
    apply Hr2 in H2.
    mytac.
    assert (pcur = tid \/ pcur <> tid) by tauto.
    destruct  H3.
    subst.
    unfold get in H2; simpl in H2.
    rewrite H2 in He.
    inverts He. 
    do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.
    intros.
    assert (pcur = tid \/ pcur <> tid) by tauto.
    destruct  H0.
    subst.
    rewrite TcbMod.set_sem in H.
    rewrite tidspec.eq_beq_true in H; eauto.
    inverts H.
    rewrite TcbMod.set_sem in H.
    rewrite tidspec.neq_beq_false in H; eauto.
    apply Hr2 in H.
    mytac.
    assert (qid  = eid \/ qid <> eid) by tauto.
    destruct H2.
    subst.
    unfold get in H; simpl in H.
    rewrite H in Ht.
    inverts Ht.
    rewrite EcbMod.set_sem.
    rewrite tidspec.neq_beq_false; auto.
    do 2 eexists; splits; eauto.
  }
  Unfocus.
  {
    splits.
    intros.
    mytac.
    assert (qid  = eid \/ qid <> eid) by tauto.
    destruct H1.
    subst.
    rewrite EcbMod.set_sem in H.
    rewrite tidspec.eq_beq_true in H; auto.
    inverts H.
    rewrite EcbMod.set_sem in H.
    rewrite tidspec.neq_beq_false in H; auto.
    assert (EcbMod.get ecbls eid = Some (absmsgq x y, qwaitset) /\ In tid qwaitset) by eauto.
    apply Hr3 in H2.
    mytac.
    assert (pcur = tid \/ pcur <> tid) by tauto.
    destruct  H3.
    subst.
    unfold get in H2; simpl in H2.
    rewrite H2 in He.
    inverts He. 
    do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.
    intros.
    assert (pcur = tid \/ pcur <> tid) by tauto.
    destruct  H0.
    subst.
    rewrite TcbMod.set_sem in H.
    rewrite tidspec.eq_beq_true in H; eauto.
    inverts H.
    rewrite TcbMod.set_sem in H.
    rewrite tidspec.neq_beq_false in H; eauto.
    apply Hr3 in H.
    mytac.
    assert (qid  = eid \/ qid <> eid) by tauto.
    destruct H2.
    subst.
    unfold get in H; simpl in H.
    rewrite H in Ht.
    inverts Ht.
    rewrite EcbMod.set_sem.
    rewrite tidspec.neq_beq_false; auto.
    do 3 eexists; splits; eauto.
  }
  {
    splits.
    intros.
    mytac.
    assert (qid  = eid \/ qid <> eid) by tauto.
    destruct H1.
    subst.
    rewrite EcbMod.set_sem in H.
    rewrite tidspec.eq_beq_true in H; auto.
    inverts H.
    rewrite EcbMod.set_sem in H.
    rewrite tidspec.neq_beq_false in H; auto.
    assert (EcbMod.get ecbls eid = Some (absmutexsem n1 n2, wls) /\ In tid wls) by eauto.
    apply Hr4 in H2.
    mytac.
    assert (pcur = tid \/ pcur <> tid) by tauto.
    destruct  H3.
    subst.
    unfold get in H2; simpl in H2.
    rewrite H2 in He.
    inverts He. 
    do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.
    intros.
    assert (pcur = tid \/ pcur <> tid) by tauto.
    destruct  H0.
    subst.
    rewrite TcbMod.set_sem in H.
    rewrite tidspec.eq_beq_true in H; eauto.
    inverts H.
    rewrite TcbMod.set_sem in H.
    rewrite tidspec.neq_beq_false in H; eauto.
    apply Hr4 in H.
    mytac.
    assert (qid  = eid \/ qid <> eid) by tauto.
    destruct H2.
    subst.
    unfold get in H; simpl in H.
    rewrite H in Ht.
    inverts Ht.
    rewrite EcbMod.set_sem.
    rewrite tidspec.neq_beq_false; auto.
    do 3 eexists; splits; eauto.

    apply Mutex_owner_hold_for_set_tcb.
    eapply Mutex_owner_set; eauto.
    intro; mytac.
    tryfalse.

    inverts Hr4.
    apply H0.
  }
Qed.


