Require Export ucos_include.
Require Import OSTimeDlyPure.
Require Import OSQAcceptPure.
Require Import oscore_common.
Require Import new_inv.

Local Open Scope int_scope.
Local Open Scope Z_scope.
Local Open Scope code_scope.


Ltac simpljoin1 := simpljoin.

(**** lzh-begin ****)

Lemma ecbmod_absmsgq:
  forall a x y z b,
    RLH_ECBData_P
      (DMsgQ a x y z) b -> exists vl n wl, b = (absmsgq vl n, wl).
Proof.
  intros.
  unfold RLH_ECBData_P in H.
  destruct b.
  destruct e;tryfalse.
  do 3 eexists;auto.
Qed.
(**** lzh-end ****)

Lemma post_exwt_succ_pre:
  forall v'36 v'13 v'12 v'32 v'15 v'24 v'35 v'0 v'8 v'9 v'11 x x0 x1 v'6 v'10 v'38 v'69 v'39 v'58 a b c v'62 v'7 vhold,
    v'12 <> Int.zero ->
    R_PrioTbl_P v'36 v'7 vhold ->
    RL_Tbl_Grp_P v'13 (Vint32 v'12) ->
    R_ECB_ETbl_P (v'32, Int.zero)
                 (V$OS_EVENT_TYPE_Q
                   :: Vint32 v'12
                   :: Vint32 v'15 :: Vptr (v'24, Int.zero) :: v'35 :: v'0 :: nil,
                  v'13) v'7 ->
    RH_TCBList_ECBList_P v'11 v'7 v'8 ->
    EcbMod.join v'9 v'10 v'11 ->
    EcbMod.joinsig (v'32, Int.zero) (absmsgq x x0, x1) v'6 v'10 ->
    Int.unsigned v'12 <= 255 ->
    array_type_vallist_match Int8u v'13 ->
    length v'13 = ∘OS_EVENT_TBL_SIZE ->
    nth_val' (Z.to_nat (Int.unsigned v'12)) OSUnMapVallist = Vint32 v'38 ->
    Int.unsigned v'38 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned v'38)) v'13 = Vint32 v'69 ->
    Int.unsigned v'69 <= 255 ->
    nth_val' (Z.to_nat (Int.unsigned v'69)) OSUnMapVallist = Vint32 v'39 ->
    Int.unsigned v'39 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39))) v'36 = Vptr (v'58, Int.zero)->
    TcbJoin (v'58, Int.zero) (a,b,c) v'62 v'7 ->
    x1<>nil /\ GetHWait v'7 x1 (v'58,Int.zero) /\ TcbMod.get v'7 (v'58,Int.zero) = Some (a,b,c).
Proof.
  intros.
  lets Hs : tcbjoin_get_a H16.
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
  destruct Hsd as (st & m & Hst).
  intro; tryfalse.

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
  destruct H2 as (H2&Hres).
  lets Hes : H2 H19.
  unfold V_OSEventType in Hes.
  simpl nth_val in Hes.
  assert (Some (V$OS_EVENT_TYPE_Q) = Some (V$OS_EVENT_TYPE_Q)) by auto.
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
  destruct H3 as (H3&Hres').
  destruct H3 as (Heg1 & Heg2).
  lets Hrgs : Heg2 Hs.
  destruct Hrgs as (xz & y & qw & Hem & Hin).
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
  assert (EcbMod.get v'11 (v'32, Int.zero) = Some (absmsgq xz y, qw) /\ In t' qw) .
  splits; auto.
  lets Habs : Heg1 H22.
  destruct Habs as (prio' & m' & n' & Hbs).
  do 3 eexists; splits; eauto.
  destruct H17 as (H17&Hres'').
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


Lemma prio_set_rdy_in_tbl:
  forall prio0 prio rtbl grp,
    0 <= Int.unsigned prio0 < 64 ->
    0 <= Int.unsigned prio < 64 ->
    prio0 <> prio ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    prio_in_tbl prio0 rtbl ->
    prio_in_tbl prio0
                (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                                (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7))))).
Proof.
  introv Fd1 Fd2 Fneq Fnth Fpit.
  unfold prio_in_tbl in *.
  introv Fx Fy Fnth'.
  assert ( ∘(Int.unsigned (Int.shru prio ($ 3))) =  ∘(Int.unsigned (Int.shru prio0 ($ 3))) \/
           ∘(Int.unsigned (Int.shru prio ($ 3))) <>  ∘(Int.unsigned (Int.shru prio0 ($ 3)))) by tauto.
  destruct H.
  assert (nth_val ∘(Int.unsigned  (Int.shru prio ($ 3)))
                  (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                                  (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7))))) = 
          Some (Vint32  (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7))))).
  eapply update_nth.
  eauto.
  subst.
  rewrite <- H in Fnth'.
  rewrite H0 in Fnth'.
  inverts Fnth'.
  eapply or_and_combine; eauto.
  eapply Fpit; trivial.
  rewrite <- H; trivial.
  unfolds in H.
  eapply prio_bit_and_zero; eauto.
  subst.

  assert (nth_val ∘(Int.unsigned  (Int.shru prio0 ($ 3))) rtbl = Some (Vint32 z)).
  eapply nth_upd_neq.
  eapply neq_comm.
  eapply H.
  eapply Fnth'.
  eapply Fpit; auto.
Qed.


Lemma prio_set_rdy_in_tbl_rev:
  forall prio0 prio rtbl grp,
    0 <= Int.unsigned prio0 < 64 ->
    0 <= Int.unsigned prio < 64 ->
    prio0 <> prio ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    prio_in_tbl prio0
                (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                                (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7))))) ->
    prio_in_tbl prio0 rtbl.
Proof.
  introv Fd1 Fd2 Fneq Fnth Fpit.
  unfold prio_in_tbl in *.
  introv Fx Fy Fnth'.
  assert ( ∘(Int.unsigned (Int.shru prio ($ 3))) =  ∘(Int.unsigned (Int.shru prio0 ($ 3))) \/
           ∘(Int.unsigned (Int.shru prio ($ 3))) <>  ∘(Int.unsigned (Int.shru prio0 ($ 3)))) by tauto.
  destruct H.
  assert (nth_val ∘(Int.unsigned  (Int.shru prio ($ 3)))
                  (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                                  (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7))))) = 
          Some (Vint32  (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7))))).
  eapply update_nth.
  eauto.
  subst.
  rewrite <- H in Fnth'.
  inverts Fnth'.
  rewrite H in H0.
  rewrite H in Fpit.
  lets Hzz: Fpit H0; eauto.
  rewrite -> Fnth in H2.
  inverts H2.
  eapply or_and_distrib; eauto.
  eapply prio_bit_and_zero; eauto.
  assert (nth_val ∘(Int.unsigned  (Int.shru prio0 ($ 3))) 
                  (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                                  (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7))))) = Some (Vint32 z)). 
  eapply nth_upd_neqrev; eauto.
  rewrite Fy in Fnth'. trivial.
  eapply Fpit; auto.
Qed.

Lemma prio_set_rdy_not_in_tbl:
  forall prio0 prio rtbl grp,
    0 <= Int.unsigned prio0 < 64 ->
    0 <= Int.unsigned prio < 64 ->
    prio0 <> prio ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    prio_not_in_tbl prio0 rtbl ->
    prio_not_in_tbl prio0
                    (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                                    (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7))))).
Proof.
  introv Fd1 Fd2 Fneq Fnth Fpit.
  unfold prio_not_in_tbl in *.
  introv Fx Fy Fnth'.
  assert ( ∘(Int.unsigned (Int.shru prio ($ 3))) =  ∘(Int.unsigned (Int.shru prio0 ($ 3))) \/
           ∘(Int.unsigned (Int.shru prio ($ 3))) <>  ∘(Int.unsigned (Int.shru prio0 ($ 3)))) by tauto.
  destruct H.
  assert (nth_val ∘(Int.unsigned  (Int.shru prio ($ 3)))
                  (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                                  (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7))))) = 
          Some (Vint32  (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7))))).
  eapply update_nth.
  eauto.
  subst.
  rewrite <- H in Fnth'.
  rewrite H0 in Fnth'.
  inverts Fnth'.
  eapply or_and_combine_zero; eauto.
  eapply Fpit; trivial.
  rewrite <- H; trivial.
  unfolds in H.
  eapply prio_bit_and_zero; eauto.
  subst.
  assert (nth_val ∘(Int.unsigned  (Int.shru prio0 ($ 3))) rtbl = Some (Vint32 z)).
  eapply nth_upd_neq.
  eapply neq_comm.
  eapply H.
  eapply Fnth'.
  eapply Fpit; auto.
Qed.


Lemma prio_set_rdy_not_in_tbl_rev:
  forall prio0 prio rtbl grp,
    0 <= Int.unsigned prio0 < 64 ->
    0 <= Int.unsigned prio < 64 ->
    prio0 <> prio ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    prio_not_in_tbl prio0
                    (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                                    (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7))))) ->
    prio_not_in_tbl prio0 rtbl.
Proof.
  introv Fd1 Fd2 Fneq Fnth Fpit.
  unfold prio_in_tbl in *.
  introv Fx Fy Fnth'.
  assert ( ∘(Int.unsigned (Int.shru prio ($ 3))) =  ∘(Int.unsigned (Int.shru prio0 ($ 3))) \/
           ∘(Int.unsigned (Int.shru prio ($ 3))) <>  ∘(Int.unsigned (Int.shru prio0 ($ 3)))) by tauto.
  destruct H.
  assert (nth_val ∘(Int.unsigned  (Int.shru prio ($ 3)))
                  (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                                  (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7))))) = 
          Some (Vint32  (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7))))).
  eapply update_nth.
  eauto.
  subst.
  rewrite <- H in Fnth'.
  inverts Fnth'.
  rewrite H in H0.
  rewrite H in Fpit.
  lets Hzz: Fpit H0; eauto.
  rewrite -> Fnth in H2.
  inverts H2.
  eapply or_and_distrib_zero; eauto.
  eapply prio_bit_and_zero; eauto.
  
  assert (nth_val ∘(Int.unsigned  (Int.shru prio0 ($ 3))) 
                  (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                                  (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7))))) = Some (Vint32 z)). 
  eapply nth_upd_neqrev; eauto.
  rewrite Fy in Fnth'. trivial.
  eapply Fpit; auto.
Qed.



Module new_rtbl.
  (* I want rtbl has more abstractions which make the operations on it more clean *)
  Definition set_rdy p rtbl :=
    update_nth_val ∘(Int.unsigned (Int.shru p ($ 3))) rtbl
                   (val_inj (or (nth_val' (Z.to_nat (Int.unsigned (Int.shru p ($ 3)))) rtbl)
                                (Vint32 ($ 1<<ᵢ(p&ᵢ$ 7))))).

  Lemma trans_lemma_1:
    forall p grp rtbl,
      nth_val (Z.to_nat (Int.unsigned (Int.shru p ($ 3)))) rtbl = Some (Vint32 grp) ->
      (val_inj
         (or (nth_val' (Z.to_nat (Int.unsigned (Int.shru p ($ 3)))) rtbl)
             (Vint32 ($ 1<<ᵢ(p&ᵢ$ 7))))) =
      (Vint32 (Int.or grp ($ 1<<ᵢ(p&ᵢ$ 7)))).
    Proof.
      intros.
      unfold val_inj.
      eapply nth_val_nth_val'_some_eq in H.
      rewrite H.
      unfold or.
      trivial.
    Qed.

  Lemma prio_set_rdy_in_tbl_lemma_1:
    forall rtbl p,
      0<= Int.unsigned p < 64 ->
      array_type_vallist_match Int8u rtbl ->
      length rtbl = ∘OS_RDY_TBL_SIZE ->
      (exists v, nth_val (Z.to_nat (Int.unsigned (Int.shru p ($ 3)))) rtbl = Some (Vint32 v)). 
  Proof.
    intros.
    eapply array_type_match_get_value; eauto.
    clear -H.
    mauto.
  Qed.

  Lemma prio_set_rdy_in_tbl:
    forall p0 p rtbl,
      0 <= Int.unsigned p0 < 64 ->
      0 <= Int.unsigned p < 64 ->
      array_type_vallist_match Int8u rtbl ->
      length rtbl = ∘OS_RDY_TBL_SIZE ->
      p0 <> p ->
      prio_in_tbl p0 rtbl ->
      prio_in_tbl p0 (set_rdy p rtbl).
  Proof.
    intros.
    unfold set_rdy.
    assert (Fnth: 
              (exists v, nth_val (Z.to_nat (Int.unsigned (Int.shru p ($ 3)))) rtbl = Some (Vint32 v))). 
      eapply prio_set_rdy_in_tbl_lemma_1; eauto.
    inversion Fnth.
    lets Feq: trans_lemma_1 H5.
    rewrite Feq.
    eapply prio_set_rdy_in_tbl; eauto.
  Qed.

  Lemma prio_set_rdy_in_tbl_rev:
    forall p0 p rtbl,
      0 <= Int.unsigned p0 < 64 ->
      0 <= Int.unsigned p < 64 ->
      array_type_vallist_match Int8u rtbl ->
      length rtbl = ∘OS_RDY_TBL_SIZE ->
      p0 <> p ->
      prio_in_tbl p0 (set_rdy p rtbl) ->
      prio_in_tbl p0 rtbl.
  Proof.
    intros.
    unfold set_rdy in *.
    assert (Fnth: 
              (exists v, nth_val (Z.to_nat (Int.unsigned (Int.shru p ($ 3)))) rtbl = Some (Vint32 v))). 
      eapply prio_set_rdy_in_tbl_lemma_1; eauto.
    inversion Fnth.
    lets Feq: trans_lemma_1 H5.
    rewrite Feq in H4.
    eapply prio_set_rdy_in_tbl_rev; eauto.
  Qed.

  
  Lemma prio_set_rdy_not_in_tbl:
    forall p0 p rtbl,
      0 <= Int.unsigned p0 < 64 ->
      0 <= Int.unsigned p < 64 ->
      array_type_vallist_match Int8u rtbl ->
      length rtbl = ∘OS_RDY_TBL_SIZE ->
      p0 <> p ->
      prio_not_in_tbl p0 rtbl ->
      prio_not_in_tbl p0 (set_rdy p rtbl).
  Proof.
    intros.
    unfold set_rdy.
    assert (Fnth: 
              (exists v, nth_val (Z.to_nat (Int.unsigned (Int.shru p ($ 3)))) rtbl = Some (Vint32 v))). 
      eapply prio_set_rdy_in_tbl_lemma_1; eauto.
    inversion Fnth.
    lets Feq: trans_lemma_1 H5.
    rewrite Feq.
    eapply prio_set_rdy_not_in_tbl; eauto.
  Qed.


  Lemma prio_set_rdy_not_in_tbl_rev:
    forall p0 p rtbl,
      0 <= Int.unsigned p0 < 64 ->
      0 <= Int.unsigned p < 64 ->
      array_type_vallist_match Int8u rtbl ->
      length rtbl = ∘OS_RDY_TBL_SIZE ->
      p0 <> p ->
      prio_not_in_tbl p0 (set_rdy p rtbl) ->
      prio_not_in_tbl p0 rtbl.
  Proof.
    intros.
    unfold set_rdy in *.
    assert (Fnth: 
              (exists v, nth_val (Z.to_nat (Int.unsigned (Int.shru p ($ 3)))) rtbl = Some (Vint32 v))). 
      eapply prio_set_rdy_in_tbl_lemma_1; eauto.
    inversion Fnth.
    lets Feq: trans_lemma_1 H5.
    rewrite Feq in H4.
    eapply prio_set_rdy_not_in_tbl_rev; eauto.
  Qed.
End new_rtbl.    


Lemma RdyTCBblk_rtbl_add:
  forall prio0 prio rtbl grp vl,
    0 <= Int.unsigned prio0 < 64 ->
    0 <= Int.unsigned prio < 64 ->
    prio0 <> prio ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    RdyTCBblk vl rtbl prio0 ->
    RdyTCBblk vl 
              (update_nth_val (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) rtbl
                              (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7)))))
              prio0.
Proof.
  introv Fp0 Fp Fneq Fnth.
  unfold RdyTCBblk.
  intuition; trivial.
  eapply prio_set_rdy_in_tbl; eauto.
Qed.

Lemma RLH_RdyI_P_rtbl_add:
  forall prio0 prio rtbl grp stat msg vl,
    0 <= Int.unsigned prio0 < 64 ->
    0 <= Int.unsigned prio < 64 ->
    prio0 <> prio ->
    V_OSTCBPrio vl = Some (Vint32 prio0) ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    RLH_RdyI_P vl rtbl (prio0, stat, msg) ->
    RLH_RdyI_P vl 
               (update_nth_val (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) rtbl
                               (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7)))))
               (prio0, stat, msg).
Proof.
  introv Fp0 Fp Fneq Fvp Fnth Frdy.
  unfolds in Frdy.
  unfolds.
  introv Frdy_tcb.
  eapply Frdy; eauto.
  unfolds.
  unfolds in Frdy_tcb.
  simpljoin1;split; auto.
  rewrite Fvp in H.
  inversion H.
  rewrite <- H6 in *.
  eapply prio_set_rdy_in_tbl_rev; eauto.
Qed.  

Lemma RHL_RdyI_P_rtbl_add:
  forall prio0 prio rtbl grp stat msg vl,
    0 <= Int.unsigned prio0 < 64 ->
    0 <= Int.unsigned prio < 64 ->
    prio0 <> prio ->
    V_OSTCBPrio vl = Some (Vint32 prio0) ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    RHL_RdyI_P vl rtbl (prio0, stat, msg) ->
    RHL_RdyI_P vl 
               (update_nth_val (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) rtbl
                               (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7)))))
               (prio0, stat, msg).
Proof.
  introv Fp0 Fp Fneq Fvp Fnth Frdy.
  unfolds in Frdy.
  unfolds.
  intros.
  inversion H.
  rewrite <- H1 in *.
  clear H1; subst.
  splits.
  eapply RdyTCBblk_rtbl_add; eauto.
  eapply Frdy; eauto.
  eapply Frdy; eauto.
  eapply Frdy; eauto.
Qed.

Lemma WaitTCBblk_rtbl_add:
  forall prio0 prio rtbl grp vl t,
    0 <= Int.unsigned prio0 < 64 ->
    0 <= Int.unsigned prio < 64 ->
    prio0 <> prio ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    WaitTCBblk vl rtbl prio0 t->
    WaitTCBblk vl 
               (update_nth_val (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) rtbl
                               (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7)))))
               prio0 t.
Proof.
  introv Fp0 Fp Fneq Fnth.
  unfold WaitTCBblk.
  intuition; trivial.
  eapply prio_set_rdy_not_in_tbl; eauto.
Qed.

Lemma WaitTCBblk_rtbl_add_rev:
  forall prio0 prio rtbl grp vl t,
    0 <= Int.unsigned prio0 < 64 ->
    0 <= Int.unsigned prio < 64 ->
    prio0 <> prio ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    WaitTCBblk vl 
               (update_nth_val (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) rtbl
                               (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7)))))
               prio0 t ->
    WaitTCBblk vl rtbl prio0 t.
Proof.
  introv Fp0 Fp Fneq Fnth.
  unfold WaitTCBblk.
  intuition; trivial.
  eapply prio_set_rdy_not_in_tbl_rev; eauto.
Qed.

Lemma RLH_Wait_P_rtbl_add:
  forall prio0 prio rtbl grp stat msg vl,
    0 <= Int.unsigned prio0 < 64 ->
    0 <= Int.unsigned prio < 64 ->
    prio0 <> prio ->
    V_OSTCBPrio vl = Some (Vint32 prio0) ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    RLH_Wait_P vl rtbl (prio0, stat, msg) ->
    RLH_Wait_P vl 
               (update_nth_val (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) rtbl
                               (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7)))))
               (prio0, stat, msg).
Proof.
  introv Fp0 Fp Fneq Fvp Fnth Fwait.
  unfolds in Fwait.
  unfolds.
  introv Fwait_tcb Fst.
  eapply Fwait; eauto.
  unfolds.
  unfolds in Fwait_tcb.
  simpljoin1;splits; auto.
  rewrite Fvp in H.
  inversion H.
  rewrite <- H7 in *.
  eapply prio_set_rdy_not_in_tbl_rev; eauto.
Qed.  


Lemma RLH_WaitS_P_rtbl_add:
  forall prio0 prio rtbl grp stat msg vl,
    0 <= Int.unsigned prio0 < 64 ->
    0 <= Int.unsigned prio < 64 ->
    prio0 <> prio ->
    V_OSTCBPrio vl = Some (Vint32 prio0) ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    RLH_WaitS_P vl rtbl (prio0, stat, msg) ->
    RLH_WaitS_P vl 
                (update_nth_val (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) rtbl
                                (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7)))))
                (prio0, stat, msg).
Proof.
  introv Fp0 Fp Fneq Fvp Fnth Fwait.
  unfolds in Fwait.
  unfolds.
  introv Fwait_tcb Fst.
  eapply Fwait; eauto.
  unfolds.
  unfolds in Fwait_tcb.
  simpljoin1;splits; auto.
  rewrite Fvp in H.
  inversion H.
  rewrite <- H7 in *.
  eapply prio_set_rdy_not_in_tbl_rev; eauto.
Qed.  

Lemma RLH_WaitQ_P_rtbl_add:
  forall prio0 prio rtbl grp stat msg vl,
    0 <= Int.unsigned prio0 < 64 ->
    0 <= Int.unsigned prio < 64 ->
    prio0 <> prio ->
    V_OSTCBPrio vl = Some (Vint32 prio0) ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    RLH_WaitQ_P vl rtbl (prio0, stat, msg) ->
    RLH_WaitQ_P vl 
                (update_nth_val (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) rtbl
                                (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7)))))
                (prio0, stat, msg).
Proof.
  introv Fp0 Fp Fneq Fvp Fnth Fwait.
  unfolds in Fwait.
  unfolds.
  introv Fwait_tcb Fst.
  eapply Fwait; eauto.
  unfolds.
  unfolds in Fwait_tcb.
  simpljoin1; splits; auto.
  rewrite Fvp in H.
  inversion H.
  rewrite <- H7 in *.
  eapply prio_set_rdy_not_in_tbl_rev; eauto.
Qed.



Lemma RLH_WaitMB_P_rtbl_add:
  forall prio0 prio rtbl grp stat msg vl,
    0 <= Int.unsigned prio0 < 64 ->
    0 <= Int.unsigned prio < 64 ->
    prio0 <> prio ->
    V_OSTCBPrio vl = Some (Vint32 prio0) ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    RLH_WaitMB_P vl rtbl (prio0, stat, msg) ->
    RLH_WaitMB_P vl 
                (update_nth_val (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) rtbl
                                (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7)))))
                (prio0, stat, msg).
Proof.
  introv Fp0 Fp Fneq Fvp Fnth Fwait.
  unfolds in Fwait.
  unfolds.
  introv Fwait_tcb Fst.
  eapply Fwait; eauto.
  unfolds.
  unfolds in Fwait_tcb.
  simpljoin1;splits; auto.
  rewrite Fvp in H.
  inversion H.
  rewrite <- H7 in *.
  eapply prio_set_rdy_not_in_tbl_rev; eauto.
Qed.


Lemma RLH_WaitMS_P_rtbl_add:
  forall prio0 prio rtbl grp stat msg vl,
    0 <= Int.unsigned prio0 < 64 ->
    0 <= Int.unsigned prio < 64 ->
    prio0 <> prio ->
    V_OSTCBPrio vl = Some (Vint32 prio0) ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    RLH_WaitMS_P vl rtbl (prio0, stat, msg) ->
    RLH_WaitMS_P vl 
                (update_nth_val (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) rtbl
                                (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7)))))
                (prio0, stat, msg).
Proof.
  introv Fp0 Fp Fneq Fvp Fnth Fwait.
  unfolds in Fwait.
  unfolds.
  introv Fwait_tcb Fst.
  eapply Fwait; eauto.
  unfolds.
  unfolds in Fwait_tcb.
  simpljoin1; splits; auto.
  rewrite Fvp in H.
  inversion H.
  rewrite <- H7 in *.
  eapply prio_set_rdy_not_in_tbl_rev; eauto.
Qed.


Lemma RLH_Wait_all_rtbl_add:
  forall prio0 prio rtbl grp stat msg vl,
    0 <= Int.unsigned prio0 < 64 ->
    0 <= Int.unsigned prio < 64 ->
    prio0 <> prio ->
    V_OSTCBPrio vl = Some (Vint32 prio0) ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    RLH_TCB_Status_Wait_P vl rtbl (prio0, stat, msg) ->
    RLH_TCB_Status_Wait_P vl 
                          (update_nth_val (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) rtbl
                                          (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7)))))
                          (prio0, stat, msg).
Proof.
  introv Fp0 Fp Fneq Fvp Fnth Fwait.
  unfolds in Fwait.
  unfolds.
  intuition; trivial.
  eapply RLH_Wait_P_rtbl_add; eauto.
  eapply RLH_WaitS_P_rtbl_add; eauto.
  eapply RLH_WaitQ_P_rtbl_add; eauto.
  eapply RLH_WaitMB_P_rtbl_add; eauto.
  eapply RLH_WaitMS_P_rtbl_add; eauto.
Qed.

Lemma RHL_Wait_P_rtbl_add:
  forall prio0 prio rtbl grp stat msg vl,
    0 <= Int.unsigned prio0 < 64 ->
    0 <= Int.unsigned prio < 64 ->
    prio0 <> prio ->
    V_OSTCBPrio vl = Some (Vint32 prio0) ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    RHL_Wait_P vl rtbl (prio0, stat, msg) ->
    RHL_Wait_P vl 
               (update_nth_val (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) rtbl
                               (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7)))))
               (prio0, stat, msg).
Proof.
  introv Fp0 Fp Fneq Fvp Fnth Fwait.
  unfolds in Fwait.
  unfolds.
  intros.
  inversion H.
  rewrite <- H1 in *.
  clear H1; subst.
  splits.
  eapply WaitTCBblk_rtbl_add; eauto.
  eapply Fwait; eauto.
  eapply Fwait; eauto.
  eapply Fwait; eauto.
Qed.
  

Lemma RHL_WaitS_P_rtbl_add:
  forall prio0 prio rtbl grp stat msg vl,
    0 <= Int.unsigned prio0 < 64 ->
    0 <= Int.unsigned prio < 64 ->
    prio0 <> prio ->
    V_OSTCBPrio vl = Some (Vint32 prio0) ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    RHL_WaitS_P vl rtbl (prio0, stat, msg) ->
    RHL_WaitS_P vl 
                (update_nth_val (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) rtbl
                                (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7)))))
                (prio0, stat, msg).
Proof.
  introv Fp0 Fp Fneq Fvp Fnth Fwait.
  unfolds in Fwait.
  unfolds.
  intros.
  inversion H.
  rewrite <- H1 in *.
  clear H1; subst.
  splits.
  eapply WaitTCBblk_rtbl_add; eauto.
  eapply Fwait; eauto.
  eapply Fwait; eauto.
  eapply Fwait; eauto.
Qed.

Lemma RHL_WaitQ_P_rtbl_add:
  forall prio0 prio rtbl grp stat msg vl,
    0 <= Int.unsigned prio0 < 64 ->
    0 <= Int.unsigned prio < 64 ->
    prio0 <> prio ->
    V_OSTCBPrio vl = Some (Vint32 prio0) ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    RHL_WaitQ_P vl rtbl (prio0, stat, msg) ->
    RHL_WaitQ_P vl 
                (update_nth_val (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) rtbl
                                (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7)))))
                (prio0, stat, msg).
Proof.
  introv Fp0 Fp Fneq Fvp Fnth Fwait.
  unfolds in Fwait.
  unfolds.
  intros.
  inversion H.
  rewrite <- H1 in *.
  clear H1; subst.
  splits.
  eapply WaitTCBblk_rtbl_add; eauto.
  eapply Fwait; eauto.
  eapply Fwait; eauto.
  eapply Fwait; eauto.
Qed.

Lemma RHL_WaitMB_P_rtbl_add:
  forall prio0 prio rtbl grp stat msg vl,
    0 <= Int.unsigned prio0 < 64 ->
    0 <= Int.unsigned prio < 64 ->
    prio0 <> prio ->
    V_OSTCBPrio vl = Some (Vint32 prio0) ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    RHL_WaitMB_P vl rtbl (prio0, stat, msg) ->
    RHL_WaitMB_P vl 
                (update_nth_val (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) rtbl
                                (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7)))))
                (prio0, stat, msg).
Proof.
  introv Fp0 Fp Fneq Fvp Fnth Fwait.
  unfolds in Fwait.
  unfolds.
  intros.
  inversion H.
  rewrite <- H1 in *.
  clear H1; subst.
  splits.
  eapply WaitTCBblk_rtbl_add; eauto.
  eapply Fwait; eauto.
  eapply Fwait; eauto.
  eapply Fwait; eauto.
Qed.

Lemma RHL_WaitMS_P_rtbl_add:
  forall prio0 prio rtbl grp stat msg vl,
    0 <= Int.unsigned prio0 < 64 ->
    0 <= Int.unsigned prio < 64 ->
    prio0 <> prio ->
    V_OSTCBPrio vl = Some (Vint32 prio0) ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    RHL_WaitMS_P vl rtbl (prio0, stat, msg) ->
    RHL_WaitMS_P vl 
                (update_nth_val (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) rtbl
                                (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7)))))
                (prio0, stat, msg).
Proof.
  introv Fp0 Fp Fneq Fvp Fnth Fwait.
  unfolds in Fwait.
  unfolds.
  intros.
  inversion H.
  rewrite <- H1 in *.
  clear H1; subst.
  splits.
  eapply WaitTCBblk_rtbl_add; eauto.
  eapply Fwait; eauto.
  eapply Fwait; eauto.
  eapply Fwait; eauto.
Qed.

Lemma RHL_Wait_all_rtbl_add:
  forall prio0 prio rtbl grp stat msg vl,
    0 <= Int.unsigned prio0 < 64 ->
    0 <= Int.unsigned prio < 64 ->
    prio0 <> prio ->
    V_OSTCBPrio vl = Some (Vint32 prio0) ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    RHL_TCB_Status_Wait_P vl rtbl (prio0, stat, msg) ->
    RHL_TCB_Status_Wait_P vl 
                          (update_nth_val (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) rtbl
                                          (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7)))))
                          (prio0, stat, msg).
Proof.
  introv Fp0 Fp Fneq Fvp Fnth Fwait.
  unfolds in Fwait.
  unfolds.
  intros.
  intuition.
  eapply RHL_Wait_P_rtbl_add; eauto.
  eapply RHL_WaitS_P_rtbl_add; eauto.
  eapply RHL_WaitQ_P_rtbl_add; eauto.
  eapply RHL_WaitMB_P_rtbl_add; eauto.
  eapply RHL_WaitMS_P_rtbl_add; eauto.
Qed.

Lemma R_TCB_Status_P_rtbl_add:
  forall prio0 prio rtbl grp stat msg vl,
    0 <= Int.unsigned prio0 < 64 ->
    0 <= Int.unsigned prio < 64 ->
    prio0 <> prio ->
    V_OSTCBPrio vl = Some (Vint32 prio0) ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    R_TCB_Status_P vl rtbl (prio0, stat, msg) ->
    R_TCB_Status_P vl 
                   (update_nth_val (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) rtbl
                                   (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7)))))
                   (prio0, stat, msg).
Proof.
  introv Fp0 Fp Fneq Fvp Fnth Fwait.
  unfolds in Fwait.
  unfolds.
  intros.
  intuition.
  eapply RLH_RdyI_P_rtbl_add; eauto.
  eapply RHL_RdyI_P_rtbl_add; eauto.
  eapply RLH_Wait_all_rtbl_add; eauto.
  eapply RHL_Wait_all_rtbl_add; eauto.
Qed.

Lemma TCBNode_P_rtbl_add:
  forall prio0 prio rtbl grp stat msg vl,
    0 <= Int.unsigned prio0 < 64 ->
    0 <= Int.unsigned prio < 64 ->
    prio0 <> prio ->
    V_OSTCBPrio vl = Some (Vint32 prio0) ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    TCBNode_P vl rtbl (prio0, stat, msg) ->
    TCBNode_P vl 
              (update_nth_val (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) rtbl
                              (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7)))))
              (prio0, stat, msg).
Proof.
  introv Fp0 Fp Fneq Fvp Fnth Ftcb.
  unfolds in Ftcb.
  unfolds.
  intros.
  intuition.
  eapply R_TCB_Status_P_rtbl_add; eauto.
Qed.

Lemma TCBNode_P_prio:
  forall vl rtbl p t m,
    TCBNode_P vl rtbl (p, t, m) ->
    0 <= Int.unsigned p < 64 /\ V_OSTCBPrio vl = Some (Vint32 p).
Proof.
  intros.
  unfolds in H.
  destruct H as (Hv1 & Hv2 & Hv3 & Hvs).
  unfolds in Hv3.
  fsimpl.
  rewrite Hv2 in H.
  inverts H.
  split; try omega; auto.
Qed.

          

Lemma TCBList_P_rtbl_add_simpl_version:
  forall vl vptr rtbl tcbls prio grp,
    0<= Int.unsigned prio < 64 ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    (forall tid p s m , TcbMod.get tcbls tid  = Some (p,s,m) -> p <> prio
    ) ->
    TCBList_P vptr vl rtbl tcbls ->
    TCBList_P vptr vl
              (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                              (Vint32 (Int.or grp ($ 1<<ᵢ(prio &ᵢ$ 7))))) 
              tcbls.
Proof.
  inductions vl.
  intros; simpl in *; auto.
  intros.
  unfold TCBList_P in *; fold TCBList_P in *.
  simpljoin1.
  exists x x0 x1 x2.
  splits; auto.
  destruct x2; destruct p.
  eapply TCBNode_P_rtbl_add; eauto.
  eapply TCBNode_P_prio; eauto.
  eapply H1; eauto.
  unfolds in H4.
  eapply TcbMod.join_sig_get; eauto.
  eapply TCBNode_P_prio; eauto.
  
  eapply IHvl; eauto.
  intros; eapply H1.
  eapply tcbjoin_get_get; eauto.
Qed.

Lemma TCBList_P_rtbl_add_lemma_1a:
  forall ma mb mab mc ma' ma'' p s m tid,
    TcbMod.join ma mb mab ->
    TcbMod.join mc ma' ma ->
    TcbJoin tid (p, s, m) ma'' ma' ->
    TcbMod.get mb tid = None.
Proof.
  introv Fj1 Fj2 Fs1.
  assert (Hl0: TcbMod.indom ma' tid).
    eapply TcbMod.get_indom.
    apply TcbMod.join_sig_get in Fs1.
    eauto.
  assert (Hl1: TcbMod.indom ma tid).
    eapply TcbMod.indom_sub_indom; eauto.
    TcbMod.solve_map.
  assert (Hl2: TcbMod.disj ma mb).
    TcbMod.solve_map.
  assert (Hl3: ~ TcbMod.indom mb tid).
    eapply TcbMod.disj_indom; eauto.
    TcbMod.solve_map.
  eapply TcbMod.nindom_get; trivial.
Qed.  

Lemma get_get_neq:
  forall m tid v1 v2 tid',
    TcbMod.get m tid = v1 ->
    TcbMod.get m tid' = v2 ->
    v1 <> v2 ->
    tid <> tid'.
Proof.
  introv Fg1 Fg2 Fneq.
  assert (Fdes: tid = tid' \/ tid <> tid').
    tauto.
  destruct Fdes eqn: Fdes'.
  subst.
  tryfalse.
  trivial.
Qed.

Lemma TCBList_P_rtbl_add_lemma_1:
  forall ma mb mab' mab mc ma' ma'' prio st msg tid,
    TcbMod.join ma mb mab ->
    TcbMod.join mc ma' ma ->
    TcbJoin tid (prio, st, msg) ma'' ma' ->
    TcbJoin tid (prio, st, msg) mab' mab ->
    R_Prio_No_Dup mab ->
    (forall tid' p s m,
       TcbMod.get mb tid' = Some (p, s, m) -> p <> prio).
Proof.
  introv Fj1 Fj2 Fs1 Fs2 Fnodup.
  introv Fget.
  assert (Hl1: TcbMod.get mab tid = Some (prio, st, msg)).
  eapply TcbMod.join_sig_get.
  unfolds in Fs2.
  unfold join, sig in Fs2; simpl in Fs2; eauto.

  assert (Hl2: TcbMod.get mb tid = None).
    eapply TCBList_P_rtbl_add_lemma_1a; eauto.
  assert (Hl3: tid <> tid').
    eapply get_get_neq; eauto.
    intro; tryfalse.
  assert (Hl4: TcbMod.sub mb mab).
    TcbMod.solve_map.
  unfold R_Prio_No_Dup in Fnodup.
  lets HF1': Fnodup Hl3.
  unfold get in HF1'; simpl in HF1'.
  lets HF1: HF1' Hl1.
  lets Hl5: TcbMod.get_sub_get Fget Hl4. 
  eapply neq_comm.
  eapply HF1; eauto.
  auto.
Qed.


Lemma TCBList_P_rtbl_add_lemma_2a:
  forall ertbl ptbl tcbl tcbl' tid px py prio  bitx st msg mab' mab vhold,
     Int.unsigned py <= 7 ->
     Int.unsigned px <= 7 ->
    RL_RTbl_PrioTbl_P ertbl ptbl vhold->
    nth_val' (Z.to_nat (Int.unsigned ((py<<ᵢ$ 3)+ᵢpx))) ptbl = Vptr tid ->
    TcbJoin tid (prio, st, msg) tcbl' tcbl ->
    R_PrioTbl_P ptbl mab vhold->
    TcbJoin tid (prio, st, msg) mab' mab -> 
    nth_val' (Z.to_nat (Int.unsigned px)) OSMapVallist = Vint32 bitx ->
    prio = ((py<<ᵢ$ 3)+ᵢpx) /\ 
    0 <= Int.unsigned prio < 64 /\ 
    px = prio &ᵢ$ 7 /\
    py = Int.shru prio ($ 3) /\
    bitx = $ 1<<ᵢpx. 
Proof.
  intros.
  unfolds in H4.
  apply tcbjoin_get_a in H5.
  assert ( 0 <= Int.unsigned ((py<<ᵢ$ 3)+ᵢpx) < 64).
  clear - H H0.
  mauto.
  apply nth_val'_imp_nth_val_vptr in H2.
  destruct H4.
  lets Ha : H4 H7 H2.
  destruct Ha as (st0 & m & Hg).
  apply H8 in H5.
  destruct H5; auto.
  unfold get in Hg; simpl in Hg.
  rewrite H5 in Hg.
  inverts Hg.
  splits; eauto.
  clear - H H0.
  mauto.
  clear - H H0.
  mauto.
  clear - H0 H6.
  mautoext.
Qed.
  
Lemma TCBList_P_rtbl_add_lemma_2:
  forall prio px py bitx grp rtbl vl vptr tcbls,
    0 <= Int.unsigned prio < 64 ->
    py = Int.shru prio ($ 3) ->
    px = prio &ᵢ$ 7 ->
    bitx = $ 1<<ᵢpx  ->
    Int.unsigned py <= 7 ->
    Int.unsigned px <= 7 ->
    
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    TCBList_P vptr vl
              (update_nth_val (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) rtbl
                              (Vint32 (Int.or grp ($ 1<<ᵢ(prio &ᵢ$ 7)))))
              tcbls
    ->
    TCBList_P vptr vl
              (update_nth_val (Z.to_nat (Int.unsigned py)) rtbl
                              (val_inj
                                 (or (nth_val' (Z.to_nat (Int.unsigned py)) rtbl) (Vint32 bitx))))
              tcbls.
Proof.
  intros.
  remember (val_inj
           (or (nth_val' (Z.to_nat (Int.unsigned py)) rtbl) (Vint32 bitx))) as Hv.
  subst py.
  apply nth_val_nth_val'_some_eq in H5.
  unfold nat_of_Z in H5.
  rewrite H5 in HeqHv.
  unfold or in HeqHv.
  simpl in HeqHv.
  subst.
  auto.
Qed.

Lemma nth_val'2nth_val:
  forall n rtbl x,
    nth_val' n rtbl = Vint32 x ->
    nth_val n rtbl = Some (Vint32 x).
Proof.
  intros.
  inductions n;
  simpl in *;  destruct rtbl; simpl in *;tryfalse; try subst; auto.
Qed.

Lemma TCBList_P_rtbl_add_lemma_main:
  forall px py bitx ertbl (ma mb mab mc ma' ma'' mab':TcbMod.map) ptbl prio st msg tid vptr vl rtbl vhold,
    Int.unsigned py <= 7 ->
    Int.unsigned px <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned px)) OSMapVallist = Vint32 bitx ->
    RL_RTbl_PrioTbl_P ertbl ptbl vhold->
    nth_val' (Z.to_nat (Int.unsigned ((py<<ᵢ$ 3)+ᵢpx))) ptbl = Vptr tid ->
    R_PrioTbl_P ptbl mab vhold->
    array_type_vallist_match Int8u rtbl ->
    length rtbl = ∘OS_RDY_TBL_SIZE ->
    (* *)
    TcbMod.join ma mb mab ->
    TcbMod.join mc ma' ma ->
    TcbJoin tid (prio, st, msg) ma'' ma' ->
    TcbJoin tid (prio, st, msg) mab' mab ->
    (* *)
    TCBList_P vptr vl rtbl mb ->
    TCBList_P vptr vl
              (update_nth_val (Z.to_nat (Int.unsigned py)) rtbl
                              (val_inj
                                 (or (nth_val' (Z.to_nat (Int.unsigned py)) rtbl) (Vint32 bitx))))
              mb.
Proof.
  intros.
  lets Hl0: H4.
  unfold R_PrioTbl_P in Hl0; destructs Hl0.
  assert (Hl1: (forall tid' p s m,
                  TcbMod.get mb tid' = Some (p, s, m) -> p <> prio)).
  eapply TCBList_P_rtbl_add_lemma_1; eauto.
  assert (Hl2: prio = ((py<<ᵢ$ 3)+ᵢpx) /\ 
               0 <= Int.unsigned prio < 64 /\ 
               px = prio &ᵢ$ 7 /\
               py = Int.shru prio ($ 3) /\
               bitx = $ 1<<ᵢpx).
  eapply TCBList_P_rtbl_add_lemma_2a; eauto.
  destructs Hl2.
  assert (Hl3: (exists v, nth_val (Z.to_nat (Int.unsigned py)) rtbl = Some (Vint32 v))).
  eapply array_type_match_get_value; eauto.
  clear -H.
  int auto.
  inversion Hl3.
  rewrite -> H18 in H20; eauto.
  eapply TCBList_P_rtbl_add_lemma_2; eauto.
  eapply TCBList_P_rtbl_add_simpl_version; eauto.
Qed.

Lemma TCBList_P_rtbl_add:
  forall v'47 v'36 v'38 v'39 v'40 v'13 v'44 v'43 v'7 v'8  v'45 v'58 v'59 v'49 v'62 v'37 prio st msg vhold,
    Int.unsigned v'38 <= 7 ->
    Int.unsigned v'39 <= 7 -> 
    nth_val' (Z.to_nat (Int.unsigned v'39)) OSMapVallist = Vint32 v'40 ->
    prio_in_tbl ((v'38<<ᵢ$ 3)+ᵢv'39) v'13 ->
    RL_RTbl_PrioTbl_P v'13 v'36 vhold->
    nth_val' (Z.to_nat (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39))) v'36 = Vptr (v'58, Int.zero) ->
    R_PrioTbl_P v'36 v'7 vhold->
    array_type_vallist_match Int8u v'37 ->
    length v'37 = ∘OS_RDY_TBL_SIZE ->
    (* *)
    TcbMod.join v'44 v'43 v'7 ->
    TcbMod.join v'47 v'49 v'44 ->
    TcbJoin (v'58, Int.zero) (prio, st, msg) v'59 v'49 ->
    TcbJoin (v'58, Int.zero) (prio, st, msg) v'62 v'7 ->
    (* *)
    TCBList_P v'8 v'45 v'37 v'43 ->
    TCBList_P v'8 v'45
              (update_nth_val (Z.to_nat (Int.unsigned v'38)) v'37
                              (val_inj
                                 (or (nth_val' (Z.to_nat (Int.unsigned v'38)) v'37) (Vint32 v'40))))
              v'43.
Proof.
  intros.
  eapply TCBList_P_rtbl_add_lemma_main; eauto.
Qed.
(*lzh-end ****)



    
Lemma rl_tbl_grp_p_set_hold:
  forall v'12 v'38 v'13 v'69 v'39 v'36 v'58 v'40 v'41,
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
    nth_val' (Z.to_nat (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39))) v'36 = Vptr (v'58, Int.zero)->
    nth_val' (Z.to_nat (Int.unsigned v'39)) OSMapVallist = Vint32 v'40 ->
    Int.unsigned v'40 <= 128 ->
    nth_val' (Z.to_nat (Int.unsigned v'38)) OSMapVallist = Vint32 v'41 ->
    Int.unsigned v'41 <= 128 ->
    Int.eq (v'69&ᵢInt.not v'40) Int.zero = true ->
    RL_Tbl_Grp_P v'13 (Vint32 v'12) ->
    RL_Tbl_Grp_P
      (update_nth_val (Z.to_nat (Int.unsigned v'38)) v'13
                      (Vint32 (v'69&ᵢInt.not v'40))) (Vint32 (v'12&ᵢInt.not v'41)).
Proof.
  intros.
  unfold Int.zero in *.
  pose (Int.eq_spec (v'69&ᵢInt.not v'40) ($ 0)) as Hps.
  rewrite H14 in Hps.
  unfolds in H15.
  unfolds.
  intros.
  assert (n =  (Z.to_nat (Int.unsigned v'38)) \/  n <>(Z.to_nat (Int.unsigned v'38))) as Hdisj.
  tauto.
  destruct Hdisj.
  subst n.
  apply nth_upd_eq in H17.
  inverts H17.
  assert (Int.unsigned v'38 < 8) as Ha by omega.
  assert ($ Z.of_nat (Z.to_nat (Int.unsigned v'38)) = v'38).
  clear - Ha.
  mauto.
  rewrite H17 in *.
  inverts H18.
  assert (   ($ 1<<ᵢv'38)&ᵢInt.not v'41 = $ 0).
  clear - Ha H12.
  mautoext.
  splits.
  split.
  intros.
  auto.
  intros.
  lets Hzs : math_8_255_eq H0 H3 H.
  rewrite Int.and_commut.
  rewrite <-Int.and_assoc.
  assert ( v'12&ᵢ($ 1<<ᵢv'38) = ($ 1<<ᵢv'38)&ᵢv'12) .
  rewrite Int.and_commut; auto.
  rewrite H20 in Hzs.
  rewrite Hzs.
  auto.
  splits.
  rewrite Int.and_assoc.
  intros.
  assert (Int.not v'41&ᵢ($ 1<<ᵢv'38) = ($ 1<<ᵢv'38)&ᵢInt.not v'41).
  apply Int.and_commut.
  rewrite H20 in H19.
  rewrite H18 in H19.
  rewrite Int.and_zero in H19.
  unfold Int.zero in H19.
  false.
  clear -Ha H19.
  gen H19.
  mauto.
  intros.
  rewrite Hps in H19.
  false.
  eapply nth_upd_neq in H17; eauto.
  inverts H18.
  assert (Vint32 v'12 = Vint32 v'12) by auto.
  lets Hsa : H15 H16 H17 H18.
  destruct Hsa.
  lets Hasd : math_nth_8_neq_not  H12 H19; try omega; eauto.
  split.
  split;
    intros.
  apply H20.
  rewrite Int.and_assoc in H22.
  rewrite Hasd in H22.
  auto.
  intros.
  apply H20 in H22.
  assert (v'12&ᵢInt.not v'41 = Int.not v'41 &ᵢ v'12).
  apply Int.and_commut.
  rewrite H23.
  rewrite Int.and_assoc.
  rewrite H22.
  rewrite Int.and_zero; auto.
  split.
  intros.
  apply H21.
  rewrite Int.and_assoc in H22.
  rewrite Hasd in H22.
  auto.
  intros.
  apply H21 in H22.
  rewrite Int.and_assoc.
  rewrite Hasd.
  auto.
Qed.

Definition get_last_tcb_ptr (l: list vallist) (x : val) :=
  match l with
    | nil => Some x
    |  _ => V_OSTCBNext (last l nil)
  end.

Lemma get_last_tcb_ptr_prop:
  forall l1 a x1 x z,
    V_OSTCBNext a = Some x1 ->
    get_last_tcb_ptr l1 x1 = Some x ->
    get_last_tcb_ptr (a :: l1) z = Some x.
Proof.
  inductions l1; intros; simpl in *; auto.
  inverts H0.
  auto.
Qed.


Lemma TCBList_P_Split:
  forall l1 x l2 rtbl tcbls,
    TCBList_P x (l1 ++ l2) rtbl tcbls ->
    exists y tls1 tls2,
      get_last_tcb_ptr l1 x  = Some y /\
      TcbMod.join tls1 tls2 tcbls /\
      TCBList_P x l1 rtbl tls1 /\
      TCBList_P y l2 rtbl tls2.
Proof.
  inductions l1.
  intros.
  simpl in H.
  exists x TcbMod.emp tcbls.
  simpl.
  splits; simpljoin1; auto.
  apply TcbMod.join_emp; auto.
  intros.
  simpl in H.
  simpljoin1.
  lets Hx : IHl1 H3.
  simpljoin1.
  lets Has : get_last_tcb_ptr_prop (Vptr x0)  H0 H.
  exists x.
  lets Hab : tcbjoin_join_ex  H1 H4.
  simpljoin1.
  exists x6 x5.
  splits; eauto.
  simpl.
  unfold TcbJoin in H7.
  do 4 eexists; splits; eauto.
Qed.


Lemma get_last_tcb_ptr_prop':
  forall l1 a x1 x z,
    l1 <> nil ->
    V_OSTCBNext a = Some x1 ->
    get_last_tcb_ptr (a :: l1) z = Some x->
    get_last_tcb_ptr l1 x1 = Some x.
Proof.
  inductions l1; intros; simpl in *; auto; tryfalse.
Qed.


Lemma TCBList_P_Combine:
  forall l1 x l2 rtbl y tls1 tls2 tcbls,
    get_last_tcb_ptr l1 x  = Some y ->
    TcbMod.join tls1 tls2 tcbls ->
    TCBList_P x l1 rtbl tls1 ->
    TCBList_P y l2 rtbl tls2 ->
    TCBList_P x (l1 ++ l2) rtbl tcbls.
Proof.
  inductions l1.
  intros.
  simpl in *.
  inverts H.
  subst.
  apply TcbMod.join_meq in H0.
  apply TcbMod.meq_eq in H0.
  subst.
  auto.
  intros.
  simpl.
  simpl in H1.
  simpljoin1.
  assert (l1 = nil \/ l1 <> nil) by tauto.
  destruct H1.
  subst.
  assert ( get_last_tcb_ptr nil x1 = Some x1).
  simpl; auto.
  simpl in H6.
  subst.
  do 4 eexists; splits; eauto.
  unfolds in H4.
  apply TcbMod.join_comm in H4.
  apply TcbMod.join_meq in H4.
  apply TcbMod.meq_eq in H4.
  subst.
  auto.
  lets Hbcd : get_last_tcb_ptr_prop' H1 H3 H.
  lets Hds : tcbjoin_join_ex2 H4 H0.
  destruct Hds as (z & Hxa & Hxb).
  unfold TcbJoin in Hxb.
  do 4 eexists;  splits; eauto.
Qed.




Lemma prio_in_tbl_orself :
  forall prio v'37 vx,
    prio_in_tbl prio
                (update_nth_val (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) v'37
                                (Vint32 (Int.or vx ($ 1<<ᵢ(prio&ᵢ$ 7))))).
Proof.
  intros.
  unfolds.
  intros.
  subst.
  apply nth_upd_eq in H1.
  inverts H1.
  rewrite Int.and_commut.
  rewrite Int.or_commut.
  rewrite Int.and_or_absorb.
  auto.
Qed.


Lemma prio_notin_tbl_orself :
  forall prio v'37 vx,
    Int.unsigned prio < 64 ->
    nth_val (Z.to_nat(Int.unsigned (Int.shru prio ($ 3)))) v'37 = Some (Vint32 vx) ->
    ~ prio_not_in_tbl prio
      (update_nth_val (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) v'37
                      (Vint32 (Int.or vx ($ 1<<ᵢ(prio&ᵢ$ 7))))).
Proof.
  introv Hr Hx  Hf.
  unfolds in Hf.
  assert (nth_val ∘(Int.unsigned (Int.shru prio ($ 3)))
                  (update_nth_val (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) v'37
                                  (Vint32 (Int.or vx ($ 1<<ᵢ(prio&ᵢ$ 7))))) = 
          Some (Vint32  (Int.or vx ($ 1<<ᵢ(prio&ᵢ$ 7))))).
  eapply update_nth; eauto.
  lets Hzds : Hf H; eauto.
  rewrite Int.and_commut in Hzds.
  rewrite Int.or_commut in Hzds.
  rewrite Int.and_or_absorb in Hzds.
  gen Hzds.
  clear - Hr.
  mauto.
Qed.
   
    
Lemma TCBList_P_post_msg:
  forall v'42 v'48 v'47 v'60 v'50 v'37 v'59 v'49 v'44 v'63 v'64 v'65 v'51 v'52 v'53 v'54 v'55 v'56 x00 v'58 v'40 v'38 prio st msg v'7 v'62 v'43 v'36 v'39 v'13 vhold,
    Int.unsigned v'38 <= 7 ->
    Int.unsigned v'39 <= 7 -> 
    nth_val' (Z.to_nat (Int.unsigned v'39)) OSMapVallist = Vint32 v'40 ->
    prio_in_tbl ((v'38<<ᵢ$ 3)+ᵢv'39) v'13 ->
    RL_RTbl_PrioTbl_P v'13 v'36 vhold->
    nth_val' (Z.to_nat (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39))) v'36 = Vptr (v'58, Int.zero) ->
    R_PrioTbl_P v'36 v'7  vhold->
    array_type_vallist_match Int8u v'37 ->
    length v'37 = ∘OS_RDY_TBL_SIZE ->
    (* *)
    TcbMod.join v'44 v'43 v'7 ->
    TcbJoin (v'58, Int.zero) (prio, st, msg) v'62 v'7 ->
    get_last_tcb_ptr v'48 v'42 = Some (Vptr (v'58, Int.zero)) ->
    TCBList_P v'42 v'48 v'37 v'47 ->
    TCBList_P v'60 v'50 v'37 v'59 ->
    TcbJoin (v'58, Int.zero) (prio, st, msg) v'59 v'49 ->
    TcbMod.join v'47 v'49 v'44 ->
    TCBNode_P
      (v'60
         :: v'63
         :: v'64
         :: v'65
         :: Vint32 v'51
         :: V$OS_STAT_Q
         :: Vint32 v'52
         :: Vint32 v'53
         :: Vint32 v'54
         :: Vint32 v'55 :: Vint32 v'56 :: nil) v'37
      (prio, st, msg) ->
    TCBList_P v'42
              (v'48 ++
                    (v'60
                       :: v'63
                       :: Vnull
                       :: Vptr x00
                       :: V$0
                       :: Vint32 ($ OS_STAT_Q&ᵢInt.not ($ OS_STAT_Q))
                       :: Vint32 v'52
                       :: Vint32 v'53
                       :: Vint32 v'54
                       :: Vint32 v'55 :: Vint32 v'56 :: nil) :: v'50)
              (update_nth_val (Z.to_nat (Int.unsigned v'38)) v'37
                              (val_inj
                                 (or (nth_val' (Z.to_nat (Int.unsigned v'38)) v'37) (Vint32 v'40))))           
              (TcbMod.set v'44 (v'58, Int.zero)
                          (prio, rdy , Vptr x00)).
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
  simpljoin1.
  unfold get in H16; simpl in H16.
  rewrite H16 in Hgs.
  inverts Hgs.
  remember ((v'38<<ᵢ$ 3)) as px.
  remember (v'39) as py.
  clear Heqpy.
  remember (px+ᵢpy) as prio.
  remember ( (v'58, Int.zero)) as tid.
  lets Hps : tcbjoin_set_ex (prio,st,msg) (prio,rdy,Vptr x00)  H14;eauto.
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
  mautoext.
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
  unfold TcbJoin in Htx.
  do 4 eexists; splits; eauto.
  unfolds; simpl; eauto.
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
  rewrite H26 in H17.
  rewrite H26 in H22.
  lets Hfs :  prio_notin_tbl_orself  H17 Hnth.
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


Lemma rl_tbl_grp_p_set_hold':
  forall v'12 v'38 v'37 v'57 v'69 v'39 v'36 v'13 v'58 v'40 v'41,
    v'12 <> Int.zero ->
    Int.unsigned v'12 <= 255 ->
    array_type_vallist_match Int8u v'13 ->
    length v'13 = ∘OS_EVENT_TBL_SIZE ->
    array_type_vallist_match Int8u v'37 ->
    length v'37 =  ∘OS_RDY_TBL_SIZE ->
    nth_val' (Z.to_nat (Int.unsigned v'12)) OSUnMapVallist = Vint32 v'38 ->
    Int.unsigned v'38 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned v'38)) v'13 = Vint32 v'69 ->
    Int.unsigned v'69 <= 255 ->
    nth_val' (Z.to_nat (Int.unsigned v'69)) OSUnMapVallist = Vint32 v'39 ->
    Int.unsigned v'39 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39))) v'36 = Vptr (v'58, Int.zero)->
    nth_val' (Z.to_nat (Int.unsigned v'39)) OSMapVallist = Vint32 v'40 ->
    Int.unsigned v'40 <= 128 ->
    nth_val' (Z.to_nat (Int.unsigned v'38)) OSMapVallist = Vint32 v'41 ->
    Int.unsigned v'41 <= 128 ->
    RL_Tbl_Grp_P v'13 (Vint32 v'12) ->
    RL_Tbl_Grp_P v'37 (Vint32 v'57) ->
    RL_Tbl_Grp_P  (update_nth_val (Z.to_nat (Int.unsigned v'38)) v'37
                                  (val_inj
                                     (or (nth_val' (Z.to_nat (Int.unsigned v'38)) v'37) (Vint32 v'40))))
                  (Vint32 (Int.or v'57 v'41)).
Proof.
  intros.
  unfold Int.zero in *.
  unfolds in H16.
  unfolds in H17.
  unfolds.
  intros.
  inverts H20.
  assert (n =  (Z.to_nat (Int.unsigned v'38)) \/  n <>(Z.to_nat (Int.unsigned v'38))) as Hdisj.
  tauto.
  destruct Hdisj.
  subst n.
  apply nth_upd_eq in H19.
  unfolds in H19.
  remember (or (nth_val' (Z.to_nat (Int.unsigned v'38)) v'37) (Vint32 v'40)) as vo.
  destruct vo; tryfalse.
  subst v0.
  assert ((Z.to_nat (Int.unsigned v'38)) < length v'37)%nat.
  rewrite H4.
  simpl.
  clear -H6.
  mauto.
  lets Hrs : array_int8u_nth_lt_len H19 ; eauto.
  destruct Hrs as (i & Hnth & Hr).
  rewrite Hnth in Heqvo.
  simpl in Heqvo.
  inverts Heqvo.
  assert (Int.unsigned v'38 < 8) as Ha by omega.
  assert ($ Z.of_nat (Z.to_nat (Int.unsigned v'38)) = v'38).
  clear - Ha.
  mauto.
  rewrite H20 in *.
  clear H20.
  split.
  split.
  intros.
  rewrite Int.and_commut in H20.
  rewrite  Int.and_or_distrib in H20.
  apply int_or_zero_split in H20.
  lets Hneq : math_nth_8_neq_zero  Ha H14.
  destruct H20.
  tryfalse.
  intros.
  apply int_or_zero_split in H20.
  destruct H20. subst.
  lets Hnz : math_nth_8_neq_zero' H12.
  omega.
  tryfalse.
  splits.
  assert (Int.unsigned v'40 <= Int.unsigned (Int.or i v'40)) .
  rewrite Int.or_commut.
  apply Int.or_le.
  lets Hgs : math_nth_8_gt_zero  H10 H12.
  assert (0 < Int.unsigned (Int.or i v'40)) by omega.
  intros.
  unfolds.
  rewrite zlt_true; auto.
  intros.
  rewrite Int.and_commut.
  rewrite Int.and_or_distrib.
  lets Has :   math_nth_8_eq_shl Ha H14.
  rewrite Has.
  rewrite Int.or_commut.
  rewrite Int.or_and_absorb.
  auto.
  apply nth_upd_neq in H19.
  assert ( Vint32 v'57 = Vint32 v'57) by auto.
  lets Hrs : H17 H18 H19 H21.
  destruct Hrs.
  splits.
  split;intros.
  apply H22.
  rewrite Int.and_commut in H24.
  rewrite Int.and_or_distrib in H24.
  apply int_or_zero_split in H24.
  destruct H24.
  rewrite Int.and_commut; auto.
  apply H22 in H24.
  rewrite Int.and_commut.
  rewrite Int.and_or_distrib .
  rewrite Int.and_commut in H24.
  rewrite H24.
  rewrite Int.and_commut.
  assert ($ 0 = Int.zero) by auto.
  rewrite H25.
  rewrite Int.or_commut.
  rewrite Int.or_zero.
  lets Hbc : math_nth_8_eq_zero H6 H14 H20; eauto.
  intros.
  split; intros.
  apply H23.
  lets Hbc : math_nth_8_eq_zero H6 H14 H20; eauto.
  rewrite Int.and_commut in H24.
  rewrite Int.and_or_distrib in H24.
  rewrite Int.and_commut in Hbc.
  rewrite Hbc in H24.
  rewrite Int.or_zero in H24.
  rewrite Int.and_commut.
  auto.
  apply H23 in H24.
  lets Hbc : math_nth_8_eq_zero H6 H14 H20; eauto.
  rewrite Int.and_commut .
  rewrite Int.and_or_distrib.
  rewrite Int.and_commut in Hbc.
  rewrite Hbc .
  rewrite Int.or_zero.
  rewrite Int.and_commut.
  auto.
  auto.
Qed.



Lemma r_priotbl_p_set_hold:
  forall v'7 prio st msg v'36 tid x y vhold,
    R_PrioTbl_P v'36 v'7 vhold->
    TcbMod.get v'7 tid = Some (prio, st, msg) ->
    R_PrioTbl_P v'36
                (TcbMod.set v'7 tid
                            (prio, x, y)) vhold.
Proof.
  intros.
  unfolds in H.
  unfolds.
  splits.
  intros.
  destruct H.
  lets Hs : H H1 H2.
  simpljoin1.
  assert (tcbid = tid \/ tcbid <> tid) by tauto.
  destruct H7.
  subst.
  unfold get; simpl.
  rewrite TcbMod.set_sem.
  rewrite tidspec.eq_beq_true; auto.
  apply Hs in H3; auto.
  unfold get in H3; simpl in H3.
  rewrite H0 in H3.
  simpljoin1.
  inverts H3.
  do 2 eexists; eauto.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  intros.
  assert (tcbid = tid \/ tcbid <> tid) by tauto.
  destruct H2.
  subst.
  rewrite  TcbMod.set_sem in H1.
  rewrite tidspec.eq_beq_true in H1.
  inverts H1.
  eapply H; eauto.
  auto.
   rewrite  TcbMod.set_sem in H1.
  rewrite tidspec.neq_beq_false in H1; auto.
  eapply H; eauto.
  destruct H.
  destruct H1.
  eapply R_Prio_NoChange_Prio_hold; eauto.
Qed.   

Lemma rl_tbl_grp_p_set_hold''
: forall (v'12 v'38 : int32) (v'13 : vallist) 
         (v'69 v'39 : int32) (v'36 : list val) (v'58 : block)
         (v'40 v'41 : int32),
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
    nth_val' (Z.to_nat (Int.unsigned v'38)) OSMapVallist = Vint32 v'41 ->
    Int.unsigned v'41 <= 128 ->
    Int.eq (v'69&ᵢInt.not v'40) Int.zero = false->
    RL_Tbl_Grp_P v'13 (Vint32 v'12) ->
    RL_Tbl_Grp_P
      (update_nth_val (Z.to_nat (Int.unsigned v'38)) v'13
                      (Vint32 (v'69&ᵢInt.not v'40))) (Vint32 v'12).
Proof.
  intros.
  unfold Int.zero in *.
  pose (Int.eq_spec (v'69&ᵢInt.not v'40) ($ 0)) as Hps.
  rewrite H14 in Hps.
  unfolds in H15.
  unfolds.
  intros.
  assert (n =  (Z.to_nat (Int.unsigned v'38)) \/  n <>(Z.to_nat (Int.unsigned v'38))) as Hdisj.
  tauto.
  destruct Hdisj.
  subst n.
  apply nth_upd_eq in H17.
  inverts H17.
  assert (Int.unsigned v'38 < 8) as Ha by omega.
  assert ($ Z.of_nat (Z.to_nat (Int.unsigned v'38)) = v'38).
  clear - Ha.
  mauto.
  rewrite H17 in *.
  inverts H18.
  splits.
  splits.
  intros.
  lets Hsa : math_8_255_eq H0 H3 H.
  rewrite Hsa in H18.
  false.
  gen H18.
  clear - Ha.
  mauto.
  intros.
  tryfalse.
  split.
  intros.
  unfolds.
  rewrite zlt_true; auto.
  remember (v'69&ᵢInt.not v'40) as x.
  clear - Hps.
  assert (0<=Int.unsigned x) by (int auto).
  assert (0 = Int.unsigned x \/ 0 < Int.unsigned x) by omega.
  destruct H0; auto.
  false.
  apply Hps.
  rewrite H0.
  int auto.
  intros.
  lets Hzs : math_8_255_eq H0 H3 H.
  auto.
  inverts H18.
  eapply nth_upd_neq in H17;  eauto.
Qed.

  
Lemma rl_rtbl_priotbl_p_hold:
  forall v'36 v'12 v'13 v'38 v'69 v'39 v'58 v'40 v'41 v'57 v'37 vhold,
    (v'58, Int.zero) <> vhold ->
    RL_RTbl_PrioTbl_P v'37 v'36 vhold->
    v'12 <> Int.zero ->
    Int.unsigned v'12 <= 255 ->
    array_type_vallist_match Int8u v'13 ->
    length v'13 = ∘OS_EVENT_TBL_SIZE ->
    array_type_vallist_match Int8u v'37 ->
    length v'37 = ∘OS_EVENT_TBL_SIZE ->
    nth_val' (Z.to_nat (Int.unsigned v'12)) OSUnMapVallist = Vint32 v'38 ->
    Int.unsigned v'38 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned v'38)) v'13 = Vint32 v'69 ->
    Int.unsigned v'69 <= 255 ->
    nth_val' (Z.to_nat (Int.unsigned v'69)) OSUnMapVallist = Vint32 v'39 ->
    Int.unsigned v'39 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39))) v'36 = Vptr (v'58, Int.zero)->
    nth_val' (Z.to_nat (Int.unsigned v'39)) OSMapVallist = Vint32 v'40 ->
    Int.unsigned v'40 <= 128 ->
    nth_val' (Z.to_nat (Int.unsigned v'38)) OSMapVallist = Vint32 v'41 ->
    Int.unsigned v'41 <= 128 ->
    RL_Tbl_Grp_P v'13 (Vint32 v'12) ->
    RL_Tbl_Grp_P v'37 (Vint32 v'57) ->
    Int.unsigned v'57 <= 255 ->
    array_type_vallist_match Tint8 v'37 ->
    length v'37 = nat_of_Z OS_RDY_TBL_SIZE ->
    RL_RTbl_PrioTbl_P
      (update_nth_val (Z.to_nat (Int.unsigned v'38)) v'37
                      (val_inj
                         (or (nth_val' (Z.to_nat (Int.unsigned v'38)) v'37) (Vint32 v'40))))
      v'36 vhold.
Proof.
  introv Hnvhold.
  intros.
  unfold  RL_RTbl_PrioTbl_P  in *.
  unfolds in H17.
  unfolds in H18.
  intros.
  unfolds in H23.
  assert (  p&ᵢ$ 7  = p&ᵢ$ 7 ) by auto.
  assert (Int.shru p ($ 3) = Int.shru p ($ 3)) by auto.
  assert ( ∘(Int.unsigned (Int.shru p ($ 3))) <> Z.to_nat (Int.unsigned v'38) \/
           ∘(Int.unsigned (Int.shru p ($ 3))) = (Z.to_nat (Int.unsigned v'38)))%nat.
  tauto.

  lets Hy : math_unmap_get_y H1 H6.
  assert ( ∘(Int.unsigned (Int.shru p ($ 3))) <∘OS_EVENT_TBL_SIZE)%nat.
  clear -H22.
  mauto.
  lets Ha : nthval'_has_value H4  H27; eauto.
  destruct Ha as (x&Hnth & Htru).
  lets Hnt : nth_val'_imp_nth_val_int Hnth.
  destruct H26.
  assert ( nth_val ∘(Int.unsigned (Int.shru p ($ 3)))
                   (update_nth_val (Z.to_nat (Int.unsigned v'38)) v'37
                                   (val_inj
                                      (or (nth_val' (Z.to_nat (Int.unsigned v'38)) v'37)
                                          (Vint32 v'40)))) = Some (Vint32 x)).
  eapply nth_upd_neqrev; eauto.
  lets Hb : H23 H24 H25 H28 .
  assert (Int.unsigned (Int.shru p ($ 3))<8). 
  clear - H22.
  mauto.
  remember (Int.shru p ($3)) as px. 
  assert ($ Z.of_nat ∘(Int.unsigned px) = px).
  clear - H29.
  mauto.
  assert (prio_in_tbl p v'37 ).
  unfolds.
  intros.
  subst.
  rewrite H33 in Hnt.
  inverts Hnt.
  auto.
  eapply H; eauto.
  assert (  p&ᵢ$ 7 = v'39 \/  p&ᵢ$ 7 <> v'39).
  tauto.
  destruct H28.
  subst v'39.

  lets Hzzp : int_usigned_tcb_range H22.
  destruct Hzzp.
  remember (Int.shru p ($3)) as px.
  assert (px = v'38).
  clear - Hy  H29 H26.
  gen H26.
  mauto.
  subst v'38.
  subst px.
  assert ( (((Int.shru p ($ 3))<<ᵢ$ 3)+ᵢ(p&ᵢ$ 7)) = p).
  clear -H22.
  mauto.
  rewrite H30 in H12.
  apply nth_val'_imp_nth_val_vptr in H12.
  eexists; eauto.
  assert ( prio_in_tbl p v'37).
  unfolds.
  intros.
  subst.
  lets Hzzp : int_usigned_tcb_range H22.
  destruct Hzzp.
  remember (Int.shru p ($3)) as px.
  remember (p&ᵢ$ 7) as py.
  assert ( px = v'38).
  clear -Hy H30 H26.
  gen H26.
  mauto.
  subst v'38.
  rewrite Hnt in H31.
  inverts H31.
  remember ((val_inj
               (or (nth_val' (Z.to_nat (Int.unsigned px)) v'37)
                   (Vint32 v'40)))) as v.
  unfold val_inj in Heqv.
  rewrite H26 in Hnth.
  rewrite Hnth in Heqv.
  unfold or in Heqv.
  subst v.
  assert ( nth_val ∘(Int.unsigned (px))
                   (update_nth_val (Z.to_nat (Int.unsigned px)) v'37
                                   (Vint32 (Int.or z v'40))) =Some (Vint32 (Int.or z v'40))).
  rewrite <- H26.
  eapply update_nth; eauto.
  lets Hd : H23 H31; eauto.
  rewrite Int.and_commut in Hd.
  rewrite Int.and_or_distrib in Hd.
  lets Hzzps :  math_nth_8_eq_zero'  H13 H29 H28; eauto; try omega.
  rewrite Int.and_commut in Hzzps.
  rewrite Hzzps in Hd.
  rewrite Int.or_zero in Hd.
  rewrite Int.and_commut in Hd.
  auto.
  eapply H; eauto.
Qed.

(*modified by zhanghui*)
Lemma rl_rtbl_priotbl_p_hold1:
  forall v'36 v'38 v'39 v'58 v'40 v'37 vhold,
    RL_RTbl_PrioTbl_P v'37 v'36 vhold->
    Int.unsigned v'38 <= 7 ->
    Int.unsigned v'39 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39))) v'36 = Vptr (v'58, Int.zero)->
    (v'58, Int.zero) <> vhold ->
    array_type_vallist_match Tint8 v'37 ->
    length v'37 = nat_of_Z OS_RDY_TBL_SIZE ->
    nth_val' (Z.to_nat (Int.unsigned v'39)) OSMapVallist = Vint32 v'40 ->
    Int.unsigned v'40 <= 128 ->
    RL_RTbl_PrioTbl_P
      (update_nth_val (Z.to_nat (Int.unsigned v'38)) v'37
                      (val_inj
                         (or (nth_val' (Z.to_nat (Int.unsigned v'38)) v'37) (Vint32 v'40))))
      v'36 vhold.
Proof.
  intros.
  unfold  RL_RTbl_PrioTbl_P  in *.
  intros.
  assert(0 <= Int.unsigned ((v'38<<ᵢ$ 3) +ᵢ v'39) < 64).
  clear - H0 H1.
  mauto.

  assert(p <> ((v'38<<ᵢ$ 3) +ᵢ  v'39) \/ p = (v'38<<ᵢ$ 3) +ᵢ  v'39).
  tauto.
  destruct H11.
 
  lets Hx: new_rtbl.prio_set_rdy_in_tbl_rev H8 H10 H4 H5 H11.
  unfold new_rtbl.set_rdy in Hx.
  assert(((v'38<<ᵢ$ 3) +ᵢ  v'39) >>ᵢ $ 3 = v'38).
  clear - H0 H1.
  mauto.
  rewrite H12 in Hx.
  assert(((v'38<<ᵢ$ 3) +ᵢ  v'39)&ᵢ$ 7 = v'39).
  clear - H0 H1.
  mauto.
  rewrite H13 in Hx.
  assert(($ 1<<ᵢv'39) = v'40).
  symmetry.
  apply math_mapval_core_prop; auto.
  mauto.
  rewrite H14 in Hx.
  eapply Hx in H9.
  apply H; auto.

  substs.
  exists (v'58, Int.zero).
  split; auto.
  apply nth_val'_imp_nth_val_vptr; auto.
Qed.


Lemma prio_wt_inq_convert:
  forall pri vx,
    PrioWaitInQ pri vx <->
    PrioWaitInQ (Int.unsigned ($ pri)) vx /\ 0 <= pri < 64.
Proof.
  split; intros.
  unfolds in H.
  simpljoin1.
  split.
  unfolds.
  do 3 eexists;splits; eauto.
  clear -H H4.
  int auto.
  rewrite Int.repr_unsigned.
  eauto.
  rewrite Int.repr_unsigned.
  eauto.
  auto.
  auto.
  destruct H.
  unfolds in H.
  simpljoin1.
  unfolds.
  do 3 eexists;splits;eauto.
  clear H H6.
  rewrite Int.repr_unsigned in *.
  eauto.
  rewrite Int.repr_unsigned in *.
  eauto.
Qed.




Lemma prio_wt_inq_tid_neq:
  forall prio'  v'13  v'69 prio,
    nth_val' (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) v'13 = Vint32 v'69 ->
    Int.unsigned prio < 64 ->
    (PrioWaitInQ (Int.unsigned prio')
                 (update_nth_val (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) v'13
                                 (Vint32 (v'69&ᵢInt.not ($ 1<<ᵢ (prio &ᵢ $7))))) <->
     PrioWaitInQ  (Int.unsigned prio') v'13 /\  prio' <> prio).
Proof.
  intros.
  splits.
  intros.
  unfolds in H1.
  destruct H1 as (x & y & z & Hx & Hy & Hz & Hn & Heq).
  subst.
  rewrite Int.repr_unsigned in *.
  
  assert (Int.shru prio ($ 3) = Int.shru prio' ($ 3) \/
          Int.shru prio ($ 3) <> Int.shru prio' ($ 3)) by tauto.
  destruct H1.
  rewrite H1 in Hn.
  lets Hzs : nth_upd_eq  Hn.
  inverts Hzs.
  assert (prio&ᵢ$ 7 = prio'&ᵢ$ 7 \/ prio&ᵢ$ 7 <> prio'&ᵢ$ 7) by tauto.
  destruct H2.
  rewrite H2 in Heq.
  rewrite Int.and_assoc in Heq.
  assert (Int.not ($ 1<<ᵢ(prio'&ᵢ$ 7))&ᵢ(Int.one<<ᵢ(prio'&ᵢ$ 7)) = Int.zero).
  rewrite Int.and_commut.
  rewrite  Int.and_not_self; auto.
  rewrite H3 in Heq.
  rewrite Int.and_zero in Heq.
  false.
  gen Heq.
  clear -Hx.
  mauto.
  splits.
  unfolds.
  do 3 eexists.
  splits; eauto.
  rewrite Int.repr_unsigned.
  unfold nat_of_Z.
  rewrite H1 in H.
  apply nth_val'_imp_nth_val_int in H.
  eauto.
  rewrite Int.repr_unsigned.
  rewrite Int.and_assoc in Heq.
  
  assert (Int.unsigned (prio'&ᵢ$ 7) < 8).
  clear -Hx.
  mauto.
  assert (Int.unsigned (prio&ᵢ$ 7) < 8).
  clear -H0.
  mauto.
  lets Hxa : int_not_shrl_and H4 H3 H2.
  unfold Int.one in *.
  rewrite Hxa in Heq.
  auto.
  introv Hf.
  subst prio.
  apply H2.
  auto.
  apply nth_upd_neq in Hn.
  splits.
  unfolds.
  do 3 eexists.
  splits; eauto.
  rewrite Int.repr_unsigned.
  apply nth_val'_imp_nth_val_int in H.
  eauto.
  rewrite Int.repr_unsigned.
  eauto.
  introv hf.
  subst prio.
  apply H1.
  auto.
  unfold nat_of_Z.
  introv Hf.
  apply H1.
  rewrite Z2Nat.inj_iff in Hf.
  apply unsigned_inj.
  auto.
  apply Int.unsigned_range.
  apply Int.unsigned_range.
  intros.
  destruct H1 as (Hpro & Hneq).
  unfolds in Hpro.
  destruct Hpro as (px & py & pz & Hx& Hy& Hz &Hnt & Hez).
  unfolds.
  rewrite Int.repr_unsigned.
  apply nth_val'_imp_nth_val_int in H.
  assert (Int.shru prio ($ 3) = Int.shru prio' ($ 3) \/
          Int.shru prio ($ 3) <> Int.shru prio' ($ 3)) by tauto.
  destruct H1.
  unfold nat_of_Z in *.
  do 3 eexists.
  splits; eauto.
  rewrite H1 in *.
  eapply update_nth; eauto.
  subst py px.
  rewrite Int.repr_unsigned in *.
  rewrite H1 in *.
  rewrite H in Hnt.
  inverts Hnt.
  assert (pz &ᵢ Int.not ($ 1<<ᵢ(prio&ᵢ$ 7)) = Int.not ($ 1<<ᵢ(prio&ᵢ$ 7)) &ᵢ pz).
  apply Int.and_commut.
  rewrite H2.
  rewrite Int.and_assoc.
  rewrite Hez.
  lets Hsd : int_usigned_tcb_range Hx.
  destruct Hsd.
  assert (0<=Int.unsigned prio < 64).
  split; try omega.
  clear -prio'.
  int auto.
  lets Hss : int_usigned_tcb_range H5.
  destruct Hss.
  apply  int_not_shrl_and ; try omega.
  introv Hf.
  apply Hneq.

  rewrite math_prio_eq.
  rewrite math_prio_eq at 1.
  rewrite H1.
  rewrite Hf.
  auto.
  omega.
  omega.
  do 3 eexists.
  splits; eauto.
  subst px py.
  rewrite Int.repr_unsigned in *.
  unfold nat_of_Z in *.
  eapply nth_upd_neqrev; eauto.
  introv Hf.
  apply H1.
  rewrite Z2Nat.inj_iff in Hf.
  apply unsigned_inj.
  auto.
  apply Int.unsigned_range.
  apply Int.unsigned_range.
  subst px.
  rewrite Int.repr_unsigned in *.
  auto.
Qed.


Lemma wtset_notnil_msgls_nil:
  forall x1 x0 x ,
  x1 <> nil ->
  RH_ECB_P (absmsgq x x0, x1) -> x = nil.
Proof.
  intros.
  unfolds in H0.
  eapply H0; eauto.
Qed.


Lemma  rl_tbl_grp_neq_zero:
  forall  v'12  px v'13 v'69,
    Int.unsigned px < 8 ->
    Int.unsigned v'12 <= 255 ->
    v'12 <> $ 0 ->
    nth_val' (Z.to_nat (Int.unsigned v'12)) OSUnMapVallist = Vint32  px -> 
    nth_val' (Z.to_nat (Int.unsigned px)) v'13 = Vint32 v'69 ->
    RL_Tbl_Grp_P v'13 (Vint32 v'12) ->
    v'69 <> $ 0.
Proof.
  introv Hran Hras Hneq Hnth Hth2 Hr.
  unfolds in Hr.
  assert (0 <=Z.to_nat (Int.unsigned px) < 8 )%nat.
  clear - Hran.
  mauto.
  apply nth_val'_imp_nth_val_int in Hth2.
  assert (Vint32 v'12 = Vint32 v'12) by auto.
  lets Hsr : Hr H Hth2 H0.
  simpljoin1.
  lets Hneqz : math_8_255_eq Hras Hneq; eauto.
  assert ($ Z.of_nat (Z.to_nat (Int.unsigned px)) = px).
  clear -Hran.
  mauto.
  rewrite H0 in *.
  rewrite Hneqz in *.
  assert (v'69 = $ 0 \/ v'69 <> $ 0) by tauto.
  destruct H4; auto.
  apply H1 in H4.
  false.
  gen H4.
  clear - Hran.
  mauto.
Qed.


Lemma ECBList_P_Set_Rdy_hold:
  forall a tcbls tid prio  msg msg'  x y  b c eid nl,
    TcbMod.get tcbls tid =  Some (prio, wait (os_stat_q eid) nl, msg) ->
    EcbMod.get c eid = None ->
    ECBList_P x y a b c tcbls ->
    ECBList_P x y a b c (TcbMod.set tcbls tid (prio,rdy,msg')).
Proof.
  inductions a; intros.
  simpl in *; auto.
  simpl in H1.
  simpljoin1.
  destruct b; tryfalse.
  destruct a.
  simpljoin1.
  simpl.
  eexists.
  splits; eauto.
  unfolds.
  unfolds in H2.

  splits.
  
  destructs H2.
  unfolds in H2.
  simpljoin1.
  unfolds.
  splits; unfolds;intros.

  apply H2 in H11.
  apply H11 in H12.
  simpljoin1.
  assert (tid = x3 \/ tid <> x3) by tauto.
  destruct H13.
  subst tid.
  unfold get in H12; simpl in H12.
  rewrite H12 in H.
  inverts H.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  exists x3 x4 x5.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.
  
  
  apply H8 in H11.
  apply H11 in H12.
  simpljoin1.
  assert (tid = x3 \/ tid <> x3) by tauto.
  destruct H13.
  subst tid.
  unfold get in H12; simpl in H12.
  rewrite H12 in H.
  inverts H.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  exists x3 x4 x5.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.

  
  apply H9 in H11.
  apply H11 in H12.
  simpljoin1.
  assert (tid = x3 \/ tid <> x3) by tauto.
  destruct H13.
  subst tid.
  unfold get in H12; simpl in H12.
  rewrite H12 in H.
  inverts H.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  exists x3 x4 x5.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.

  
  apply H10 in H11.
  apply H11 in H12.
  simpljoin1.
  assert (tid = x3 \/ tid <> x3) by tauto.
  destruct H13.
  subst tid.
  unfold get in H12; simpl in H12.
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
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  rewrite H in Hti.
  inverts Hti.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  rewrite tidspec.eq_beq_true in Hti; tryfalse; auto.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  eapply H6; eauto.

  destruct H11.
  subst tid.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  rewrite H in Hti.
  inverts Hti.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  rewrite tidspec.eq_beq_true in Hti; tryfalse; auto.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  eapply H8; eauto.

  destruct H11.
  subst tid.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  rewrite H in Hti.
  inverts Hti.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  rewrite tidspec.eq_beq_true in Hti; tryfalse; auto.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  eapply H9; eauto.

  destruct H11.
  subst tid.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  rewrite H in Hti.
  inverts Hti.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  rewrite tidspec.eq_beq_true in Hti; tryfalse; auto.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  eapply H10; eauto.

  simpljoin1;auto.


  do 3 eexists; splits; eauto.
  eapply IHa; eauto.
  eapply ecbmod_joinsig_get_none; eauto.
Qed.



Lemma ecblist_p_post_exwt_hold:
  forall  v'36 v'12 v'13 v'38 v'69 v'39 v'58 v'40  v'32 v'15 v'24 v'35 v'16
          v'18 v'19 v'20 v'34 v'21 v'22 v'23 v'25 v'26 v'27 x x0 x1 v'0 v'1
          v'5 v'6 v'7 x00 v'11 v'31 v'30 v'29 v'10 v'9 prio v'62 st msg y vhold,
    RL_RTbl_PrioTbl_P v'13 v'36 vhold->
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
    nth_val' (Z.to_nat (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39))) v'36 = Vptr (v'58, Int.zero)->
    nth_val' (Z.to_nat (Int.unsigned v'39)) OSMapVallist = Vint32 v'40 ->
    Int.unsigned v'40 <= 128 ->
    RL_Tbl_Grp_P v'13 (Vint32 v'12) ->
    R_ECB_ETbl_P (v'32, Int.zero)
                 (V$OS_EVENT_TYPE_Q
                   :: Vint32 v'12
                   :: Vint32 v'15 :: Vptr (v'24, Int.zero) :: v'35 :: v'0 :: nil,
                  v'13) v'7 ->
    RLH_ECBData_P
      (DMsgQ (Vptr (v'24, Int.zero))
             (v'16
                :: v'18
                :: v'19
                :: v'20
                :: v'34
                :: Vint32 v'21
                :: Vint32 v'22 :: Vptr (v'23, Int.zero) :: nil)
             (v'26 :: v'25 :: nil) v'27) (absmsgq x x0, x1)->
    ECBList_P v'0 Vnull v'1 v'5 v'6 v'7 ->
    ECBList_P v'29 (Vptr (v'32, Int.zero)) v'30 v'31 v'9 v'7 ->
    EcbMod.joinsig (v'32, Int.zero) (absmsgq x x0, x1) v'6 v'10 ->
    EcbMod.join v'9 v'10 v'11 ->
    TcbJoin (v'58, Int.zero) (prio, st, msg) v'62 v'7 ->
    R_PrioTbl_P v'36 v'7 vhold ->
    x1 <> nil ->
    ECBList_P v'29 Vnull
              (v'30 ++
                    ((V$OS_EVENT_TYPE_Q
                       :: Vint32 y
                       :: Vint32 v'15 :: Vptr (v'24, Int.zero) :: v'35 :: v'0 :: nil,
                      update_nth_val (Z.to_nat (Int.unsigned v'38)) v'13
                                     (Vint32 (v'69&ᵢInt.not v'40))) :: nil) ++ v'1)
              (v'31 ++
                    (DMsgQ (Vptr (v'24, Int.zero))
                           (v'16
                              :: v'18
                              :: v'19
                              :: v'20
                              :: v'34
                              :: Vint32 v'21
                              :: Vint32 v'22 :: Vptr (v'23, Int.zero) :: nil)
                           (v'26 :: v'25 :: nil) v'27 :: nil) ++ v'5)
              (EcbMod.set v'11 (v'32, Int.zero)
                          (absmsgq nil x0, remove_tid (v'58, Int.zero) x1))
              (TcbMod.set v'7 (v'58, Int.zero)
                          (prio, rdy , Vptr x00))
.
Proof.
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
  unfold get in Hget; simpl in Hget.
  rewrite Hget in H20.
  inverts H20.
  remember ((v'38<<ᵢ$ 3)) as px.
  remember (v'39) as py.
  clear Heqpy.
  remember (px+ᵢpy) as prio.
  remember ( (v'58, Int.zero)) as tid.
  unfolds in H14.
  destruct H14 as (Ha & Hb & Hc).
  destruct Ha as (Ha&Ha'&Ha''&Ha''').
  destruct Hb as (Hb&Hb'&Hb''&Hb''').
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
  assert (Some (V$OS_EVENT_TYPE_Q) = Some (V$OS_EVENT_TYPE_Q)) by auto.
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
  
  lets Hsds : ecb_set_join_join  (absmsgq nil x0, remove_tid tid x1)  H18  H19.
  destruct Hsds as ( vv & Hsj1 & Hsj2).
  eapply msgqlist_p_compose.
  instantiate (1:= (v'32, Int.zero)).
  unfolds.
  splits.
  unfolds.
  splits;unfolds.
  
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
 


  unfolds.
  splits;
  intros prio' mm nn tid'.
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
  unfolds in Hb'''.
  lets Hga : Hb''' Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in Ha3.
  lets Hneqp: Ha3 H23 Hget Hgs.
  assert ( PrioWaitInQ (Int.unsigned prio') v'13 /\ prio' <> prio) .
  splits; auto.
  unfolds in Hx;simpl in Hx;tryfalse.

  simpl fst in Hc;simpl;auto.
  
  instantiate (1:=v'9).
  eapply ECBList_P_Set_Rdy_hold;eauto.
  rewrite Int.repr_unsigned.  
  eauto.
  eapply joinsig_join_getnone; eauto.
  instantiate (1:=v'6).
  eapply ECBList_P_Set_Rdy_hold;eauto.
  rewrite Int.repr_unsigned.  
  eauto.
  eapply  joinsig_get_none; eauto.
  unfolds in H15.
  simpljoin1.
  unfolds in r.
  apply r in H22.
  subst x.
  instantiate (1:=(absmsgq nil x0, remove_tid tid x1)).
  splits; auto.
  unfolds.
  splits; intros; auto; tryfalse.
  eapply Hsj1.
  eapply Hsj2.
Qed.

Lemma ecblist_p_post_exwt_hold':
  forall (v'36 : vallist) (v'12 : int32) (v'13 : vallist)
         (v'38 v'69 v'39 : int32) (v'58 : block) (v'40 v'41 : int32)
         (v'32 : block) (v'15 : int32) (v'24 : block)
         (v'35 v'16 v'18 v'19 v'20 v'34 : val) (v'21 v'22 : int32)
         (v'23 : block) (v'25 v'26 : val) (v'27 : vallist)
         (x : list msg) (x0 : maxlen) (x1 : waitset) 
         (v'0 : val) (v'1 : list EventCtr) (v'5 : list EventData)
         (v'6 : EcbMod.map) (v'7 : TcbMod.map) (x00 : addrval)
         (v'11 : EcbMod.map) (v'31 : list EventData) 
         (v'30 : list EventCtr) (v'29 : val) (v'10 v'9 : EcbMod.map)
         (prio : priority) v'62 st msg vhold,
    RL_RTbl_PrioTbl_P v'13 v'36 vhold->
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
    nth_val' (Z.to_nat (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39))) v'36 = Vptr (v'58, Int.zero)->
    nth_val' (Z.to_nat (Int.unsigned v'39)) OSMapVallist = Vint32 v'40 ->
    Int.unsigned v'40 <= 128 ->
    nth_val' (Z.to_nat (Int.unsigned v'38)) OSMapVallist = Vint32 v'41 ->
    Int.unsigned v'41 <= 128 ->
    RL_Tbl_Grp_P v'13 (Vint32 v'12) ->
    R_ECB_ETbl_P (v'32, Int.zero)
                 (V$OS_EVENT_TYPE_Q
                   :: Vint32 v'12
                   :: Vint32 v'15 :: Vptr (v'24, Int.zero) :: v'35 :: v'0 :: nil,
                  v'13) v'7 ->
    RLH_ECBData_P
      (DMsgQ (Vptr (v'24, Int.zero))
             (v'16
                :: v'18
                :: v'19
                :: v'20
                :: v'34
                :: Vint32 v'21
                :: Vint32 v'22 :: Vptr (v'23, Int.zero) :: nil)
             (v'26 :: v'25 :: nil) v'27) (absmsgq x x0, x1)->
    ECBList_P v'0 Vnull v'1 v'5 v'6 v'7 ->
    ECBList_P v'29 (Vptr (v'32, Int.zero)) v'30 v'31 v'9 v'7 ->
    EcbMod.joinsig (v'32, Int.zero) (absmsgq x x0, x1) v'6 v'10 ->
    EcbMod.join v'9 v'10 v'11 ->
    TcbJoin (v'58, Int.zero) (prio, st, msg) v'62 v'7 ->
    R_PrioTbl_P v'36 v'7 vhold->
    x1 <> nil -> 
    ECBList_P v'29 Vnull
              (v'30 ++
                    ((V$OS_EVENT_TYPE_Q
                       :: Vint32 v'12
                       :: Vint32 v'15 :: Vptr (v'24, Int.zero) :: v'35 :: v'0 :: nil,
                      update_nth_val (Z.to_nat (Int.unsigned v'38)) v'13
                                     (Vint32 (v'69&ᵢInt.not v'40))) :: nil) ++ v'1)
              (v'31 ++
                    (DMsgQ (Vptr (v'24, Int.zero))
                           (v'16
                              :: v'18
                              :: v'19
                              :: v'20
                              :: v'34
                              :: Vint32 v'21
                              :: Vint32 v'22 :: Vptr (v'23, Int.zero) :: nil)
                           (v'26 :: v'25 :: nil) v'27 :: nil) ++ v'5)
              (EcbMod.set v'11 (v'32, Int.zero)
                          (absmsgq nil x0, remove_tid (v'58, Int.zero) x1))
              (TcbMod.set v'7 (v'58, Int.zero)
                          (prio, rdy , Vptr x00)).
  Proof.
    intros.
    eapply ecblist_p_post_exwt_hold; eauto.
  Qed.


Lemma rh_curtcb_set_nct:
  forall v'8 v'7 x tid ,
    RH_CurTCB v'8 v'7 ->
    v'8 <> tid ->
    RH_CurTCB v'8
              (TcbMod.set v'7 tid
                          x).
Proof.
 intros.
 unfolds in H.
 simpljoin1.
 unfolds.
 exists x0 x1 x2.
 rewrite TcbMod.set_sem.
 rewrite tidspec.neq_beq_false; eauto.
Qed.

Lemma tidneq_inwt_in:
  forall  x1 tid tid0,
    tid <> tid0 ->
    (In tid0 (remove_tid tid x1) <->
    In tid0 x1).
Proof.
  inductions x1.
  simpl.
  intros; splits; auto.
  intros.
  simpl.
  splits.
  intros.
  simpl in H0.
  remember (beq_tid tid a) as Hb.
  destruct Hb.
  apply eq_sym in HeqHb.
  apply tidspec.beq_true_eq in HeqHb.
  subst.
  right.
  eapply IHx1; eauto.
  simpl in H0.
  destruct H0; auto.
  right.
  apply eq_sym in HeqHb.
  apply tidspec.beq_false_neq in HeqHb.
  eapply IHx1; eauto.
  intros.
  destruct H0.
  subst.
  rewrite tidspec.neq_beq_false; auto.
  simpl.
  left; auto.
  remember (beq_tid tid a) as Hb.
  destruct Hb.
  apply eq_sym in HeqHb.
  apply tidspec.beq_true_eq in HeqHb.
  subst.
  eapply IHx1; eauto.
  simpl.
  right.
  eapply IHx1; eauto.
Qed.


Lemma  tid_in_rmwt_in :
  forall x1 tid,
    In tid (remove_tid tid x1) ->
    In tid x1.
Proof.
  inductions x1.
  simpl.
  intros; auto.
  simpl.
  intros.
  remember (beq_tid tid a) as Hb.
  destruct Hb.
  apply eq_sym in HeqHb.
  apply tidspec.beq_true_eq in HeqHb.
  left; auto.
  simpl in H.
  destruct H.
  left; auto.
  right; apply IHx1; auto.
Qed.



Lemma in_wtset_rm_notin:
  forall x1 tid,
    In tid x1 ->
    ~ In tid (remove_tid tid x1).
Proof.
  inductions x1.
  simpl.
  intros; tryfalse.
  simpl.
  intros.
  destruct H.
  subst.
  intro Hf.
  rewrite tidspec.eq_beq_true in Hf; auto.
  eapply IHx1; eauto.
  apply tid_in_rmwt_in; auto.
  apply IHx1 in H.
  introv Hf.
  apply H.
  remember (beq_tid tid a) as Hb.
  destruct Hb.
  auto.
  apply eq_sym in HeqHb.
  simpl in Hf.
  apply tidspec.beq_false_neq in HeqHb.
  destruct Hf.
  tryfalse.
  auto.
Qed.



Lemma rh_tcblist_ecblist_p_post_exwt:
  forall v'8 tid v'11 v'7 v'9 v'10 eid x x0 x1 v'6 prio  msg x00 xl,
    RH_TCBList_ECBList_P v'11 v'7 v'8 ->
    EcbMod.join v'9 v'10 v'11 ->
    EcbMod.joinsig eid (absmsgq x x0, x1) v'6 v'10 ->
    In tid x1 ->
    TcbMod.get v'7 tid = Some (prio,  wait (os_stat_q eid) xl, msg) ->
    RH_TCBList_ECBList_P
      (EcbMod.set v'11 eid
                  (absmsgq nil x0, remove_tid tid x1))
      (TcbMod.set v'7 tid
                  (prio, rdy , Vptr x00)) v'8.
Proof.
  intros.
  unfolds.
  splits.
  splits; intros.
  destruct H4.
  unfolds in H.
  destruct H as (H&Hx).
  destruct H.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H7.
  subst.
  apply ecbmod_joinsig_get in H1.
  lets Hget : EcbMod.join_get_get_r H0 H1.
  assert (EcbMod.get v'11 eid = Some (absmsgq x x0, x1)/\ In tid0 x1 ).
  splits; auto.
  lets Hsa : H H7.
  simpljoin1.
  unfold get in H8; simpl in H8.
  rewrite H3 in H8.
  inverts H8.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H8.
  subst.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  inverts H4.
  apply  in_wtset_rm_notin in H9.
  tryfalse.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  assert (EcbMod.get v'11 eid0 = Some (absmsgq x2 y, qwaitset) /\ In tid0 qwaitset ).
  splits; auto.
  lets Hsc : H H13.
  simpljoin1.
  unfold get in H14; simpl in H14.
  rewrite H3 in H14.
  inverts H14.
  tryfalse.
  rewrite TcbMod.set_sem .
  rewrite tidspec.neq_beq_false; auto.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H8.
  subst.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  inverts H4.
  lets Hbss :tidneq_inwt_in  x1 H7.
  destruct Hbss as (Hbss & _).
  lets Hbssc : Hbss H5.
  apply ecbmod_joinsig_get in H1.
  lets Hget : EcbMod.join_get_get_r H0 H1.
  assert ( EcbMod.get v'11 eid0 = Some (absmsgq x y, x1) /\ In tid0 x1 ).
  splits; auto.
  apply H in H4.
  simpljoin1.
  do 3 eexists; eauto.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  assert ( EcbMod.get v'11 eid0 = Some (absmsgq x2 y, qwaitset)/\ In tid0 qwaitset ).
  splits; auto.
  apply H in H9.
  simpljoin1.
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
  destructs H.
  destruct H.
  apply H9 in H4.
  simpljoin1.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H11.
  subst.
  unfold get in H4; simpl in H4.
  rewrite H4 in Hget.
  inverts Hget.
  lets Hbss :tidneq_inwt_in  x1 H5.
  destruct Hbss as (_ & Hbss).
  lets Hbssc : Hbss H10.
  rewrite EcbMod.set_sem.
  rewrite tidspec.eq_beq_true; auto.
  do 3 eexists; splits; eauto.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 3 eexists; splits; eauto.


  splits; intros.
  destruct H4.
  unfolds in H.
  destruct H as (Hh&H&Hx).
  destruct H.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H7;subst.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  tryfalse.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  assert (EcbMod.get v'11 eid0 = Some (abssem n, wls) /\ In tid0 wls).
  split;auto.
  apply H in H8.
  simpljoin1.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H11;subst.
  unfold get in H8; simpl in H8.
  rewrite H3 in H8;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  eauto.

  unfolds in H.
  destruct H as (Hh&H&Hx).
  destruct H.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H6;subst.
  rewrite TcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  inverts H4.

  rewrite TcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  apply H5 in H4.
  simpljoin1.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H10;subst.
  apply ecbmod_joinsig_get in H1.
  lets Hget : EcbMod.join_get_get_r H0 H1.
  unfold get in H4; simpl in H4.
  rewrite H4 in Hget;tryfalse.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 2 eexists;split;eauto.

  
  splits; intros.
  destruct H4.
  unfolds in H.
  destruct H as (Hh&Hhh&H&Hx).
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
  simpljoin1.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H9;subst.
  unfold get in H8; simpl in H8.
  rewrite H3 in H8;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  eauto.

  unfolds in H.
  destruct H as (Hh&Hhh&H&Hx).
  destruct H.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H6;subst.
  rewrite TcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  inverts H4.

  rewrite TcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  apply H5 in H4.
  simpljoin1.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H8;subst.
  apply ecbmod_joinsig_get in H1.
  lets Hget : EcbMod.join_get_get_r H0 H1.
  unfold get in H4; simpl in H4.
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
  simpljoin1.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H10;subst.
  unfold get in H8; simpl in H8.
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
  simpljoin1.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H9;subst.
  apply ecbmod_joinsig_get in H1.
  lets Hget : EcbMod.join_get_get_r H0 H1.
  unfold get in H4; simpl in H4.
  rewrite H4 in Hget;tryfalse.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 3 eexists;split;eauto.

  unfolds in H.
  destructs H.
  clear H H4 H5.
  elim H6; intros.
  unfold RH_TCBList_ECBList_MUTEX_OWNER in *.
  destruct H4 as (Hx&H4).
  intros.

  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H7; intros.
  subst eid.
  rewrite EcbMod.set_a_get_a in H5.
  inversion H5.
  apply CltEnvMod.beq_refl.
  rewrite EcbMod.set_a_get_a' in H5.
  2:apply tidspec.neq_beq_false; auto.

  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H8.
  subst.
  rewrite TcbMod.set_a_get_a.
  do 3 eexists;eauto.
  apply CltEnvMod.beq_refl.
  rewrite TcbMod.set_a_get_a'.
  2:apply tidspec.neq_beq_false; auto.
  eapply H4;eauto.
Qed.


Lemma qpost_ovf_prop:
  forall i2 i1 x13 x12 x6 x7 x8 v'49 v'47 x14 x15 x x1 x2 v2,
    true = Int.ltu i2 i1 ->
    WellformedOSQ
      (x13
         :: x12
         :: x6
         :: x7
         :: x8
         :: Vint32 i2
         :: Vint32 i1 :: Vptr (v'49, Int.zero) :: nil) -> 
    RLH_ECBData_P
      (DMsgQ (Vptr (v'47, Int.zero))
             (x13
                :: x12
                :: x6
                :: x7
                :: x8
                :: Vint32 i2
                :: Vint32 i1 :: Vptr (v'49, Int.zero) :: nil)
             (x14 :: x15 :: nil) v2)  (absmsgq x x1, x2) ->
    Z.ge (Z_of_nat (length x)) (Int.unsigned x1).
Proof.
  introv Hlt Hwl Hr.
  funfold Hwl.
  funfold Hr.
  funfold H0.
  assert (  Z.of_nat (length x) = Int.unsigned x0) by auto.
  rewrite H0.
  unfold qend_right, arrayelem_addr_right in *.
  simpljoin1.
  unfold ptr_offset_right, ptr_minus in *.
  destruct x3.
  destruct x10.
  destruct x5.
  fsimpl.
  funfold H.
  funfold H1.
  clear - Hlt.
  int auto.
Qed.

Lemma qpost_ovf_prop':
  forall i2 i1 x13 x12 x6 x7 x8 v'49 v'47 x14 x15 x x1 x2 v2,
    true = Int.eq i1 i2 ->
    WellformedOSQ
      (x13
         :: x12
         :: x6
         :: x7
         :: x8
         :: Vint32 i2
         :: Vint32 i1 :: Vptr (v'49, Int.zero) :: nil) -> 
    RLH_ECBData_P
      (DMsgQ (Vptr (v'47, Int.zero))
             (x13
                :: x12
                :: x6
                :: x7
                :: x8
                :: Vint32 i2
                :: Vint32 i1 :: Vptr (v'49, Int.zero) :: nil)
             (x14 :: x15 :: nil) v2)  (absmsgq x x1, x2) ->
    Z.ge (Z_of_nat (length x)) (Int.unsigned x1).
Proof.
  introv Hlt Hwl Hr.
  funfold Hwl.
  funfold Hr.
  funfold H0.
  assert (  Z.of_nat (length x) = Int.unsigned x0) by auto.
  rewrite H0.
  unfold qend_right, arrayelem_addr_right in *.
  simpljoin1.
  unfold ptr_offset_right, ptr_minus in *.
  destruct x3.
  destruct x10.
  destruct x5.
  fsimpl.
  funfold H.
  funfold H1.
  clear - Hlt.
  int auto.
Qed.

Lemma osq_same_blk_st_in':
  forall (qptr qst qend qin qout qsz qen : val) (b : block) (i : int32),
    WellformedOSQ
      (qptr :: qst :: qend :: qin :: qout :: qsz :: qen :: Vptr (b, i) :: nil) ->
    exists i', qin = Vptr (b, i').
Proof.
  intros.
  funfold H.
  funfold H9.
  funfold H8.
  funfold H3.
   unfolds in H10.
  simpljoin1.
  unfold ptr_minus in *.
  unfold ptr_offset_right in *.
  fsimpl.
  simpl in H5.
  inverts H5.
  eexists; eauto.
Qed.


Lemma wellq_in_props:
  forall (x12 x11 x5 x6 : val) (v'49 : block) (x i2 i1 : int32)
         (v'47 : block) (x13 x14 : val) (v2 : list val) 
         (v'46 : absecb.B),
    length v2 = ∘OS_MAX_Q_SIZE ->
    RLH_ECBData_P
      (DMsgQ (Vptr (v'47, Int.zero))
             (x12
                :: x11
                :: x5
                :: Vptr (v'49, x)
                :: x6
                :: Vint32 i2 :: Vint32 i1 :: Vptr (v'49, Int.zero) :: nil)
             (x13 :: x14 :: nil) v2) v'46 ->
    WellformedOSQ
      (x12
         :: x11
         :: x5
         :: Vptr (v'49, x)
         :: x6
         :: Vint32 i2 :: Vint32 i1 :: Vptr (v'49, Int.zero) :: nil) ->
    Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero)) <= Int.unsigned x /\
    4 * ((Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4) =
    Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero)) /\
    (Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4 < 20 /\
    (Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4 <
    Z.of_nat (length v2).
Proof.
  introv Hlen Hrl  Hwf.  
  assert (auxand (Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero)) <= Int.unsigned x)
                 (4 * ((Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4) =
                  Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero)) /\
                  (Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4 < 20 /\
                  (Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4 <
                  Z.of_nat (length v2)
                 )).
  funfold Hwf.
  unfold arrayelem_addr_right, qend_right  in *.
  unfold  ptr_offset_right, ptr_minus in *.
  simpljoin1.
  fsimpl.
  simpl in H7.
  subst i.
  simpl in H13, H12,H10.
  clear H5.
  assert (Int.zero+ᵢ($ 4+ᵢInt.zero) = $4) as Heq.
  clear -x.
  mauto.
  rewrite Heq in *.
  clear Heq.
  unfolds in Hrl.
  destruct v'46. 
  destruct e; tryfalse.
  splits.
  clear - H.
  int auto.
  apply eq_sym.
  eapply Z_div_exact_2; try omega.
  eapply math_prop_int_modu; eauto.
  eapply math_prop_ltu_20; eauto.
  rewrite Hlen.
  unfold OS_MAX_Q_SIZE.
  simpl.
  eapply math_prop_ltu_20; eauto.
  auto.
Qed.


Lemma wellformedosq_size_add_1:
  forall x13 x12 x6 v'49 x x8 i2 i1,
    WellformedOSQ
      (x13
         :: x12
         :: x6
         :: Vptr (v'49, x)
         :: x8
         :: Vint32 i2
         :: Vint32 i1 :: Vptr (v'49, Int.zero) :: nil) -> Int.unsigned (i2+ᵢ$ 1) <= Int16.max_unsigned.
Proof.
  introv Hwl.
  funfold Hwl.
  unfold qend_right, arrayelem_addr_right in *.
  simpljoin1.
  unfold ptr_offset_right, ptr_minus in *.
  destruct x1.
  destruct x3.
  destruct x5.
  fsimpl.
  clear - H11.
  unfold OS_MAX_Q_SIZE in *.
  unfold Int16.max_unsigned.
  unfold Int16.modulus.
  simpl.
  int auto.
  int auto.
Qed.


Lemma wellformedosq_ens_add_1:
  forall x13 x12 x6 v'49 x x8 i2 i1 x10 x11 v'46 v2 v'36,
    length v2 = ∘OS_MAX_Q_SIZE ->
    RLH_ECBData_P
         (DMsgQ (Vptr (v'36, Int.zero))
                (x13
                   :: x12
                   :: x6
                   :: Vptr (v'49, x)
                   :: x8
                   :: Vint32 i2
                   :: Vint32 i1 :: Vptr (v'49, Int.zero) :: nil)
            (x10 :: x11 :: nil) v2) v'46 ->
    WellformedOSQ
      (x13
         :: x12
         :: x6
         :: Vptr (v'49, x)
         :: x8
         :: Vint32 i2
         :: Vint32 i1 :: Vptr (v'49, Int.zero) :: nil) -> Int.unsigned (i1+ᵢ$ 1) <= Int16.max_unsigned.
Proof.
  introv Ha Hlh Hwf.
  funfold Hwf.
  unfolds in Hlh.
  destruct v'46.
  destruct e;tryfalse.
  simpljoin1.
  unfold qend_right, arrayelem_addr_right in *.
  simpljoin1.
  unfold ptr_offset_right,  ptr_minus in *.
  fsimpl.
  funfold H.
  simpl in H17, H16 , H15 , H5.
  inverts H5.
  assert ( (Int.zero+ᵢ($ 4+ᵢInt.zero))  = $4).
  clear -x.
  mauto.
  rewrite H in *.
  funfold H0.
  funfold H1.
  unfold distance in *.
  simpl in H22, H24, H25.
  rewrite Int.repr_unsigned in *.
  clear H.
  remember ( ((Int.unsigned (Int.divu (x-ᵢ$ 4) ($ 4))) )) as M.
  remember ( Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4))) as N.
  assert (M = N \/ M > N \/ M < N).
  clear -x.
  omega.
  destruct H as [Ha1 | [Ha2 | Ha3]].
  apply H25 in Ha1.
  destruct Ha1.
  simpljoin1.
  pose (Int.eq_spec x0 Int.zero) as Hps.
  rewrite H in Hps.
  subst.
  clear -x.
  mauto.
  simpljoin1.
  pose (Int.eq_spec x0 m) as Hps.
  rewrite H in Hps.
  subst x0.
  clear - H11.
  unfold OS_MAX_Q_SIZE in H11.
  unfold  Int16.max_unsigned.
  simpl.
  mauto.
  lets Hzs : H22 Ha2.
  eapply vallist_seg_length_prop in Hzs.
  rewrite Hzs in H5.
  eapply math_MN_le_int16; eauto.
  eapply math_MN_le_max; eauto.
  rewrite Ha.
  eapply math_MN_le_max; eauto.
  lets Hasb : H24 Ha3.
  remember (vallist_seg ∘N ∘(Int.unsigned m) v2) as l1.
  eapply eq_sym in Heql1.
  eapply vallist_seg_length_prop in Heql1.
  remember (vallist_seg 0 ∘M v2) as l2.
  eapply eq_sym in Heql2.
  eapply vallist_seg_length_prop in Heql2.
  assert (length (l1 ++ l2) = length l )%nat.
  rewrite Hasb.
  auto.
  rewrite app_length in H.
  rewrite Heql1 in H; rewrite Heql2 in H.
  assert (length l < ∘(Int.unsigned m))%nat.
  assert (∘M < ∘N)%nat.
  unfold nat_of_Z.
  eapply Z2Nat.inj_lt.
  subst M.
  apply Int.unsigned_range.
  subst N.
  apply Int.unsigned_range.
  auto.
  clear - H9 H12 H H0.
  omega.
  eapply math_le_int16; eauto.
  clear -x.
  omega.
  rewrite Ha.
  eapply math_MN_max_prop; eauto.
  eapply math_MN_max_prop; eauto.
  rewrite Ha.
  eapply math_MN_max_prop; eauto.
Qed.



Lemma rlh_ecb_nowait_prop:
  forall v'25 i i3 v'47 x4 v'42 v'40 v'35 v'34 x1 x2 x3 v'37,
    RL_Tbl_Grp_P v'40 (Vint32 i)->
    R_ECB_ETbl_P (v'25, Int.zero)
                 (V$OS_EVENT_TYPE_Q
                   :: Vint32 i
                   :: Vint32 i3 :: Vptr (v'47, Int.zero) :: x4 :: v'42 :: nil,
                  v'40) v'35 ->
    EcbMod.get v'34 (v'25, Int.zero) = Some (absmsgq x1 x2, x3) ->
    RH_TCBList_ECBList_P v'34 v'35 v'37 ->
    Int.eq i ($ 0) = true ->
    x3 = nil.
Proof.
  introv Hrl Hre Hecb Hrh Heq.
  pose (Int.eq_spec i ($0)) as Hps.
  rewrite Heq in Hps.
  subst i.
  clear Heq.
  simpljoin1.
  unfolds in Hrh.
  destruct Hrh as (Hrh&_).
  unfolds in Hre.
  destruct Hre as (Hre1 & Hre2 &_).
  unfolds in Hre1.
  destruct Hre1 as (Hre1 & _).
  destruct Hre2 as (Hre2 & _).
  unfolds in Hre1.
  unfolds in Hre2.
  assert (x3 = nil \/ x3 <> nil) by tauto.
  destruct H; auto.
  destruct x3.
  tryfalse.
  unfolds in Hrh.
  destruct Hrh as (Hrh &_).
  assert (In t (t::x3)).
  simpl.
  left; auto.

  assert ( EcbMod.get v'34 (v'25, Int.zero) = Some (absmsgq x1 x2, t :: x3)/\ In t (t :: x3)).
  split; auto.
  apply Hrh in H1.
  simpljoin1.
  apply Hre2 in H1.
  simpljoin1.

  unfolds in H1.
  simpljoin1.
  unfolds in Hrl.
  rewrite Int.repr_unsigned in H5.
  assert (0<=∘(Int.unsigned (Int.shru x ($ 3)))<8)%nat.
  clear - H7.
  mauto.
  assert (V$0 = V$0) by auto.
  lets Habb : Hrl H3 H5 H4.
  simpljoin1.
  rewrite Int.and_commut in H8.
  rewrite Int.and_zero in H8.
  assert (x8 = $0).
  apply H8; auto.
  subst x8.
  rewrite Int.and_commut in H6.
  rewrite Int.and_zero in H6.
  rewrite Int.repr_unsigned in H6.
  assert ( $1<<ᵢ(x&ᵢ$ 7) <> $ 0).
  eapply   math_prop_neq_zero2;omega.
  unfold Int.zero in H6.
  unfold Int.one in H6.
  tryfalse.
Qed.




Lemma qpost_no_wait_prop':
  forall i2 i1 x13 x12 x6 x7 x8 v'49 v'47 x14 x15 x x1 x2 v2,
    Int.ltu i1 i2 = true ->
    WellformedOSQ
      (x13
         :: x12
         :: x6
         :: x7
         :: x8
         :: Vint32 i2
         :: Vint32 i1 :: Vptr (v'49, Int.zero) :: nil) -> 
    RLH_ECBData_P
      (DMsgQ (Vptr (v'47, Int.zero))
             (x13
                :: x12
                :: x6
                :: x7
                :: x8
                :: Vint32 i2
                :: Vint32 i1 :: Vptr (v'49, Int.zero) :: nil)
             (x14 :: x15 :: nil) v2)  (absmsgq x x1, x2) ->
    Z.of_nat (length x) < (Int.unsigned x1) .
Proof.
introv Hlt Hwl Hr.
  funfold Hwl.
  funfold Hr.
  funfold H0.
  assert (  Z.of_nat (length x) = Int.unsigned x0) by auto.
  rewrite H0.
  unfold qend_right, arrayelem_addr_right in *.
  simpljoin1.
  unfold ptr_offset_right, ptr_minus in *.
  destruct x3.
  destruct x10.
  destruct x5.
  fsimpl.
  funfold H.
  funfold H1.
  clear - Hlt.
  int auto.
Qed.


Lemma get_wellformedosq_in_setst:
  forall i1 i2 x13 x12 x6 v'49 x x8,
    Int.ltu i1 i2 = true ->
    WellformedOSQ
      (x13
         :: x12
         :: x6
         :: Vptr (v'49, x)
         :: x8
         :: Vint32 i2
         :: Vint32 i1 :: Vptr (v'49, Int.zero) :: nil) ->
    val_inj
      match x6 with
        | Vundef => None
        | Vnull => Some (Vint32 Int.zero)
        | Vint32 _ => None
        | Vptr (b2, ofs2) =>
          if peq v'49 b2
          then
            if Int.eq (x+ᵢInt.mul ($ 1) ($ 4)) ofs2
            then Some (Vint32 Int.one)
            else Some (Vint32 Int.zero)
          else Some (Vint32 Int.zero) 
      end <> Vint32 Int.zero ->
    WellformedOSQ
      (x13
         :: x12
         :: x6
         :: x12
         :: x8
         :: Vint32 i2
         :: Vint32 (i1+ᵢ$ 1) :: Vptr (v'49, Int.zero) :: nil).
Proof.
  introv Hlt Hvl Hj.
  funfold Hvl.
  unfold qend_right, arrayelem_addr_right in *.
  simpljoin1.
  unfold ptr_offset_right, ptr_minus in *.
  destruct x1.
  destruct x3.
  destruct x5.
  fsimpl.
  rewrite peq_true in Hj.
  remember (Int.eq (x+ᵢInt.mul ($ 1) ($ 4)) i) as Hb.
  destruct Hb; simpl in Hj; tryfalse.
  apply eq_sym in HeqHb.
  pose ( Int.eq_spec (x+ᵢInt.mul ($ 1) ($ 4)) i ) as Hpx. 
  rewrite HeqHb in Hpx.
  subst i.
  simpl in H7.
  subst.
  simpl in H5.
  assert ( Int.zero+ᵢ($ 4+ᵢInt.zero) = $ 4) as Hx. 
  clear -x.
  int auto.
  int auto.
  rewrite Hx in *.
  assert (Int.mul ($ 1) ($ 4) = $ 4) as Hy.
  clear -x.
  int auto.
  rewrite Hy in *.
  simpl in *.
  do 7 eexists; splits; try solve [unfolds; simpl; eauto].
  splits; eauto.
  unfolds.
  splits; simpl; eauto.
  rewrite Pos2Z.inj_eqb .
  rewrite Z.eqb_refl.
  splits; auto.
  rewrite Pos2Z.inj_eqb .
  rewrite Z.eqb_refl.
  auto.
  unfolds.
  eexists.
  unfold ptr_offset_right, ptr_minus in *.
  rewrite Pos2Z.inj_eqb .
  rewrite Z.eqb_refl.
  splits; eauto.
  simpl.
  assert (Int.divu ($ 4-ᵢ$ 4) ($ 4) = $0).
  clear -x.
  mauto.
  rewrite H1.
  rewrite Int.unsigned_repr.
  eapply Z2Nat.inj_lt;omega.
  clear -x.
  int auto.
  unfolds.
  unfold ptr_offset_right, ptr_minus in *.
  rewrite Pos2Z.inj_eqb .
  rewrite Z.eqb_refl.
  eexists;  splits; eauto.
Qed.


Lemma msgqlist_p_compose'
: forall (p : val) (qid : addrval) (mqls : EcbMod.map)
         (qptrl1 qptrl2 : list EventCtr) (i i1 : int32) 
         (a : addrval) (x3 p' : val) (v'41 : vallist)
         (msgqls1 msgqls2 : list EventData) (msgq : EventData)
         (mqls1 mqls2 : EcbMod.map) (mq : absecb.B) 
         (mqls' : EcbMod.map) (tcbls : TcbMod.map),
    R_ECB_ETbl_P qid
                 (V$OS_EVENT_TYPE_Q
                   :: Vint32 i :: Vint32 i1 :: Vptr a :: x3 :: p' :: nil, v'41) tcbls ->
    ECBList_P p (Vptr qid) qptrl1 msgqls1 mqls1 tcbls ->
    ECBList_P p' Vnull qptrl2 msgqls2 mqls2 tcbls ->
    RLH_ECBData_P msgq mq ->
    EcbMod.joinsig qid mq mqls2 mqls' ->
    EcbMod.join mqls1 mqls' (EcbMod.set mqls qid mq) ->
    ECBList_P p Vnull
              (qptrl1 ++
                      ((V$OS_EVENT_TYPE_Q
                         :: Vint32 i :: Vint32 i1 :: Vptr a :: x3 :: p' :: nil, v'41)
                         :: nil) ++ qptrl2) (msgqls1 ++ (msgq :: nil) ++ msgqls2) (EcbMod.set mqls qid mq)
              tcbls.
Proof.
  intros.
  eapply msgqlist_p_compose;eauto.
Qed.






Lemma rlh_ecbdata_in_end:
  forall i1 i2 x13 x12 v'49 x x8 v'47 x14 x15 v2 x1 x2 x0,
    Int.ltu i1 i2 = true ->
    length v2 = ∘OS_MAX_Q_SIZE ->
    WellformedOSQ
      (x13
         :: x12
         :: Vptr (v'49, (x+ᵢInt.mul ($ 1) ($ 4)) )
         :: Vptr (v'49, x)
         :: x8
         :: Vint32 i2
         :: Vint32 i1 :: Vptr (v'49, Int.zero) :: nil) ->
    RLH_ECBData_P
      (DMsgQ (Vptr (v'47, Int.zero))
             (x13
                :: x12
                :: Vptr (v'49, (x+ᵢInt.mul ($ 1) ($ 4)) )
                :: Vptr (v'49, x)
                :: x8
                :: Vint32 i2
                :: Vint32 i1 :: Vptr (v'49, Int.zero) :: nil)
             (x14 :: x15 :: nil) v2) (absmsgq x1 x2, nil) ->
    RLH_ECBData_P
      (DMsgQ (Vptr (v'47, Int.zero))
             (x13
                :: x12
                :: Vptr (v'49, x+ᵢInt.mul ($ 1) ($ 4))
                :: x12
                :: x8
                :: Vint32 i2
                :: Vint32 (i1+ᵢ$ 1) :: Vptr (v'49, Int.zero) :: nil)
             (x14 :: x15 :: nil)
             (update_nth_val
                (Z.to_nat
                   ((Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) /
                                                                                4)) v2 (Vptr x0))) (absmsgq (x1 ++ (Vptr x0::nil)) x2, nil).
Proof.
  introv Hi Hlen Hw Hr.
  funfold Hw.
  unfold qend_right, arrayelem_addr_right in *.
  unfold ptr_offset_right,   ptr_minus  in *.
  fsimpl.
  simpl in H1.
  subst i.
  simpl in H5.
  inverts H5.
  assert (Int.mul ($ 1) ($ 4) = $ 4).
  clear -b.
  mauto.
  rewrite H1 in *.
  simpl in H13, H12, H10.
  unfolds in Hr.
  destruct Hr as (Hm1 & Hm2 & Hm3 & Hm4).
  funfold Hm1.
  funfold Hm2.
  funfold Hm3.
  unfold distance in *.
  rewrite Int.repr_unsigned in *.
  simpl in H18 , H20 ,  H21.
  unfolds.
  splits.
  unfolds.
  assert (Int.unsigned (Int.divu ($ 4-ᵢ$ 4) ($ 4)) = 0).
  clear -x.
  repeat progress (int auto);simpl;
  try    rewrite Zdiv_0_l;omega.
  assert ((Int.zero+ᵢ($ 4+ᵢInt.zero)) = $ 4).
  clear -x.
  mauto.
  assert (Int.unsigned ($ 4) = 4).
  clear -x.
  int auto.
  do 7 eexists; splits; try solve [unfolds; simpl; eauto].
  rewrite H3 in *.
  clear H3.
  rewrite H5 in *.
  rewrite H16 in *.
  lets Heq : math_le_xyz  H11 H H12 H0 H15; eauto.
  rewrite Int.repr_unsigned; auto.
  rewrite H16 in *.
  destruct Heq as (Hle & Hse & He).    
  assert ( Int.unsigned (Int.divu (x-ᵢ$ 4) ($ 4)) >  Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4)) \/
           Int.unsigned (Int.divu (x-ᵢ$ 4) ($ 4)) =  Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4))) by omega.
  destruct H3 as [Ha1 | Ha2].
  lets Hres : H18 Ha1.
  remember ( ∘(Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4)))) as M.
  remember (∘(Int.unsigned (Int.divu (x-ᵢ$ 4) ($ 4)))) as N.
  rewrite  <- He.
  splits.
  splits.
  intros.
  assert (0<=Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4))).
  apply Int.unsigned_range.
  omega.
  intros.
  rewrite <- Hse.
  lets Heqs : math_le_max_q H11 H9 Hse.
  destruct Heqs as (Hs1 & Hs2).
  lets Has : vallist_seg_upd_prop (Vptr x0) Hres. 
  rewrite Hlen.
  auto.
  auto.
  rewrite Has.
  unfold vallist_seg.
  simpl.
  rewrite app_nil_r.
  auto.
  intros.
  right.
  lets Heqs : math_le_max_q H11 H9 Hse.
  destruct Heqs as (Hs1 & Hs2).
  lets Has : vallist_seg_upd_prop (Vptr x0) Hres. 
  rewrite Hlen.
  auto.
  auto.
  rewrite <- Hse.
  rewrite Has.
  lets Hcs : math_len_le_and (Vptr x0) Hlen H11 H9 Hse.
  destruct Hcs as (Hcs1 & Hcs2).
  split.
  lets Hsss : vallist_seg_length_prop Has.
  auto.
  auto.
  rewrite <- H3 in *.
  subst M.
  rewrite app_length in Hsss.
  simpl in Hsss.
  eapply math_length_int_eq; eauto.
  unfold vallist_seg.
  simpl.
  rewrite app_nil_r.
  auto.
  eapply isptr_list_tail_add;eauto.
  lets Heqs : H21 Ha2.
  rewrite <- He.
  rewrite Ha2.
  remember ( ∘(Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4)))) as M.
  splits.
  splits.
  assert (0<=Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4))).
  apply Int.unsigned_range.
  intros.
  clear - H3 H17.
  omega.
  intros.  
  rewrite <- Hse.
  rewrite Ha2.
  rewrite <-HeqM.
  destruct Heqs.
  destruct H17.
  subst x1.
  simpl.
  rewrite  vallist_seg_upd_SM.
  unfold vallist_seg;simpl.
  auto.
  rewrite Hlen.
  eapply math_max_le_q; eauto.
  destruct H17.
  eapply ltu_eq_false in Hi.
  rewrite  Int.eq_sym in Hi.
  rewrite Hi in H17.
  inverts H17.
  introv Hz.
  rewrite <- Hz in *.
  right. 
  rewrite <- Hse.
  rewrite Ha2.
  rewrite HeqM.
  destruct Heqs.
  destruct H3.
  subst x1.
  rewrite  vallist_seg_upd_SM.
  unfold vallist_seg;simpl.
  splits.
  eapply math_length_int_eq; eauto.
  simpl.
  rewrite Ha2 in Hse.
  simpl in Hse.
  rewrite <- Hse.
  auto.
  auto.
  rewrite Hlen.
  simpl.
  unfold Pos.to_nat;simpl; omega.
  destruct H3 as (Hfs &_).
  eapply ltu_eq_false in Hi.
  rewrite Int.eq_sym in Hi.
  rewrite Hi in Hfs.
  inverts Hfs.
  eapply isptr_list_tail_add;eauto.
  unfolds.
  eexists.
  splits.
  unfolds; simpl; eauto.
  rewrite app_length.
  simpl.
  eapply  math_inc_eq_ltu; eauto.
  unfolds.
  eexists.
  splits; auto.
  unfolds; simpl; eauto.
  rewrite Int.repr_unsigned; auto.
  unfolds.
  splits; auto.
  intros.
  tryfalse.
Qed.
       

Lemma rh_tcbls_mqls_p_setmsg_hold:
  forall (mqls : EcbMod.map) (tcbls : TcbMod.map) (ct : tid) 
         (a : tidspec.A) (v : msg) (vl : list msg) (qmax : maxlen) 
         (wl : waitset),
    RH_TCBList_ECBList_P mqls tcbls ct ->
    EcbMod.get mqls a = Some (absmsgq vl qmax, wl) ->
    RH_TCBList_ECBList_P (EcbMod.set mqls a (absmsgq (vl++v::nil) qmax, wl)) tcbls ct.
Proof.
  intros.
  unfold RH_TCBList_ECBList_P in *; simpljoin1; splits.
  clear H1 H2 H3.
  unfold RH_TCBList_ECBList_Q_P in *; simpljoin1; splits.
  clear H1; intros.
  destruct (tidspec.beq a eid) eqn : eq1.
  lets Hx: tidspec.beq_true_eq eq1; substs.
  rewrite EcbMod.set_a_get_a in H1; auto.
  destruct H1; inverts H1; eauto.
  rewrite EcbMod.set_a_get_a' in H1; auto.
  eapply H; eauto.
  clear H; intros.
  destruct (tidspec.beq a eid) eqn : eq1.
  lets Hx: tidspec.beq_true_eq eq1; substs.
  rewrite EcbMod.set_a_get_a; auto.
  apply H1 in H; auto.
  do 4 destruct H.
  unfold get in H; simpl in H.
  rewrite H in H0; inverts H0.
  eauto.
  rewrite EcbMod.set_a_get_a'; auto.
  eapply H1; eauto.

  clear H H2 H3.
  unfold RH_TCBList_ECBList_SEM_P in *; simpljoin1; splits.
  clear H1; intros.
  destruct (tidspec.beq a eid) eqn : eq1.
  lets Hx: tidspec.beq_true_eq eq1; substs.
  rewrite EcbMod.set_a_get_a in H1; auto.
  destruct H1; inverts H1; eauto.
  rewrite EcbMod.set_a_get_a' in H1; auto.
  eapply H; eauto.
  clear H; intros.
  destruct (tidspec.beq a eid) eqn : eq1.
  lets Hx: tidspec.beq_true_eq eq1; substs.
  rewrite EcbMod.set_a_get_a; auto.
  apply H1 in H; auto.
  do 3 destruct H.
  unfold get in H; simpl in H.
  rewrite H in H0; inverts H0.
  eauto.
  rewrite EcbMod.set_a_get_a'; auto.
  eapply H1; eauto.
  
  clear H H1 H3.
  unfold RH_TCBList_ECBList_MBOX_P in *; simpljoin1; splits.
  clear H1; intros.
  destruct (tidspec.beq a eid) eqn : eq1.
  lets Hx: tidspec.beq_true_eq eq1; substs.
  rewrite EcbMod.set_a_get_a in H1; auto.
  destruct H1; inverts H1; eauto.
  rewrite EcbMod.set_a_get_a' in H1; auto.
  eapply H; eauto.
  clear H; intros.
  destruct (tidspec.beq a eid) eqn : eq1.
  lets Hx: tidspec.beq_true_eq eq1; substs.
  rewrite EcbMod.set_a_get_a; auto.
  apply H1 in H; auto.
  do 3 destruct H.
  unfold get in H; simpl in H.
  rewrite H in H0; inverts H0.
  eauto.
  rewrite EcbMod.set_a_get_a'; auto.
  eapply H1; eauto.

  clear H H1 H2.
  unfold RH_TCBList_ECBList_MUTEX_P in *; simpljoin1; splits.
  clear H1; intros.
  destruct (tidspec.beq a eid) eqn : eq1.
  lets Hx: tidspec.beq_true_eq eq1; substs.
  rewrite EcbMod.set_a_get_a in H1; auto.
  destruct H1; inverts H1; eauto.
  rewrite EcbMod.set_a_get_a' in H1; auto.
  eapply H; eauto.
  clear H; intros.
  destruct (tidspec.beq a eid) eqn : eq1.
  lets Hx: tidspec.beq_true_eq eq1; substs.
  rewrite EcbMod.set_a_get_a; auto.
  apply H1 in H; auto.
  do 4 destruct H.
  unfold get in H; simpl in H.
  rewrite H in H0; inverts H0.
  eauto.
  rewrite EcbMod.set_a_get_a'; auto.
  eapply H1; eauto.

 
  unfold RH_TCBList_ECBList_MUTEX_OWNER in *.
  intros.

  assert (eid = a \/ eid <> a) by tauto.
  destruct H4; intros.
  subst eid.
  rewrite EcbMod.set_a_get_a in H3.
  inversion H3.
  apply CltEnvMod.beq_refl.
  rewrite EcbMod.set_a_get_a' in H3.
  2:apply tidspec.neq_beq_false; auto.
  eapply H2;eauto.
Qed.



Lemma get_wellformedosq_in_setst':
  forall i1 i2 x13 x12 x6 v'49 x x8,
    x6 <> Vptr (v'49,  (x+ᵢInt.mul ($ 1) ($ 4))) ->
    WellformedOSQ
      (x13
         :: x12
         :: x6
         :: Vptr (v'49, x)
         :: x8
         :: Vint32 i2
         :: Vint32 i1 :: Vptr (v'49, Int.zero) :: nil) ->
    WellformedOSQ
      (x13
         :: x12
         :: x6
         :: Vptr (v'49, x+ᵢInt.mul ($ 1) ($ 4))
         :: x8
         :: Vint32 i2
         :: Vint32 (i1+ᵢ$ 1) :: Vptr (v'49, Int.zero) :: nil).
Proof.
  intros.
  assert (Int.mul ($ 1) ($ 4) = $ 4) by mauto.
  rewrite H1 in *.
  funfold H0.
  unfold qend_right, arrayelem_addr_right in *.
  simpljoin1.
  unfold ptr_offset_right, ptr_minus in *.
  fsimpl.
  simpl in *.
  assert ( Int.zero+ᵢ($ 4+ᵢInt.zero) = $ 4).
  clear -x.
  mauto.
  rewrite H3 in *.
  inverts H7.
  unfolds.
  do 7 eexists; splits; try solve [unfolds; simpl; eauto].
  rewrite H3 in *.
  splits; eauto.
  unfolds.
  splits; simpl; auto.
  rewrite Pos2Z.inj_eqb .
  rewrite Z.eqb_refl.
  splits; eauto.
  rewrite Pos2Z.inj_eqb .
  rewrite Z.eqb_refl.
  auto.
  unfolds.
  unfold ptr_offset_right, ptr_minus in *.
  eexists.
  rewrite Pos2Z.inj_eqb .
  rewrite Z.eqb_refl.
  splits; eauto.
  simpl.
  eapply  math_ltu_false_false; eauto.
  simpl.
  eapply math_lt_mod_lt with i2 ;eauto.
  intro Hf.
  subst i2.
  tryfalse.
  unfolds.
  unfold ptr_offset_right, ptr_minus in *.
  eexists.
  rewrite Pos2Z.inj_eqb .
  rewrite Z.eqb_refl.
  splits; eauto.
Qed.


Lemma rlh_ecbdata_in_noend:
  forall i1 i2 x13 x12 v'49 x x8 v'47 x14 x15 v2 x1 x2 x0 x6,
    x6 <> Vptr (v'49, x+ᵢInt.mul ($ 1) ($ 4)) ->
    Int.ltu i1 i2 = true ->
    length v2 = ∘OS_MAX_Q_SIZE ->
    WellformedOSQ
      (x13
         :: x12
         :: x6
         :: Vptr (v'49, x)
         :: x8
         :: Vint32 i2
         :: Vint32 i1 :: Vptr (v'49, Int.zero) :: nil) ->
    RLH_ECBData_P
      (DMsgQ (Vptr (v'47, Int.zero))
             (x13
                :: x12
                :: x6
                :: Vptr (v'49, x)
                :: x8
                :: Vint32 i2
                :: Vint32 i1 :: Vptr (v'49, Int.zero) :: nil)
             (x14 :: x15 :: nil) v2) (absmsgq x1 x2, nil) ->
    RLH_ECBData_P
      (DMsgQ (Vptr (v'47, Int.zero))
             (x13
                :: x12
                :: x6
                :: Vptr (v'49, x+ᵢInt.mul ($ 1) ($ 4))
                :: x8
                :: Vint32 i2
                :: Vint32 (i1+ᵢ$ 1) :: Vptr (v'49, Int.zero) :: nil)
             (x14 :: x15 :: nil)
             (update_nth_val
                (Z.to_nat
                   ((Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) /
                                                                                4)) v2 (Vptr x0))) (absmsgq (x1++ (Vptr x0 :: nil)) x2, nil).
Proof.
  introv Hneq Hi Hlen Hw Hr.
  funfold Hw.
  unfold qend_right, arrayelem_addr_right in *.
  unfold ptr_offset_right,   ptr_minus  in *.
  fsimpl.
  simpl in H7,H13,H12, H10, H5.
  inverts H5.
  assert (Int.mul ($ 1) ($ 4) = $ 4).
  clear -b.
  mauto.
  rewrite H5 in *.
  assert (i2 <> x+ᵢ$ 4) as Hni.
  introv Hf.
  apply Hneq.
  subst i2.
  auto.
  clear Hneq.
  unfolds in Hr.
  destruct Hr as (Hm1 & Hm2 & Hm3 & Hm4).
  funfold Hm1.
  funfold Hm2.
  funfold Hm3.
  unfold distance in *.
  rewrite Int.repr_unsigned in *.
  simpl in H19 , H21 ,  H22.
  remember (Int.unsigned (Int.divu (x-ᵢ$ 4) ($ 4))) as M.
  remember (Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4))) as N.
  assert (Int.unsigned ($ 4) = 4).
  clear -x.
  int auto.
  rewrite H1 in *.
  rewrite H7 in *.
  unfolds.
  splits.
  unfolds.
  do 7 eexists; splits; try solve [unfolds; simpl; eauto].
  splits.
  splits.
  introv Hc1.
  lets Heq :math_int_lt_eq_split H H0 HeqM HeqN  Hc1; eauto.
  destruct Heq as (He1 & He2 & He3 & He4).
  rewrite He3.
  rewrite He1.
  destruct He2 as [Hea1 | Hea2].
  lets Hca1 : H19 Hea1.
  lets Has : vallist_seg_upd_prop (Vptr x0) Hca1.
  rewrite Hlen.
  apply He4.
  apply He4.
  rewrite Has.
  auto.
  lets Hrs : H22 Hea2.
  destruct Hrs as [Hrs1 | Hrs2].
  destruct Hrs1 as (Heq1 & Heq2).
  subst x1.
  rewrite Hea2.
  rewrite  vallist_seg_upd_SM.
  simpl; auto.
  rewrite Hlen.
  rewrite <-Hea2.
  destruct He4.
  clear - H14.
  omega.
  destruct Hrs2 as (Hie & _).
  eapply ltu_eq_false in Hi.
  rewrite Int.eq_sym in Hi.
  rewrite Hi in Hie.
  tryfalse.
  introv Hc2.
  lets Heq :math_int_lt_eq_split' H H0 HeqM HeqN  Hc2; eauto.
  destruct Heq as (He1 & He2 & He3 & He4).
  rewrite He3.
  rewrite He1.
  lets Hres : H21 He2.
  rewrite vallist_seg_upd_irr with (y:= (Vptr x0)) (M:=∘M)in Hres;auto.
  remember ( vallist_seg 0 ∘M v2) as xy.
  apply eq_sym in Heqxy.
  lets Has : vallist_seg_upd_prop (Vptr x0) Heqxy.
  rewrite Hlen.
  clear - He4.
  destruct He4.
  omega.
  clear -x.
  omega.
  rewrite Has.
  rewrite app_assoc.
  rewrite Hres.
  auto.
  apply He4.
  rewrite Hlen.
  apply He4.
  introv Hc3.
  lets Heq :math_int_lt_eq_split'' H H0 HeqM HeqN  Hc3; eauto.
  right.
  destruct Heq as (He1 & He2 & He3 & He4).
  destruct He2 as (Hes & Hek).
  rewrite He3.
  rewrite He1.
  lets Hrs : H21 Hek.
  rewrite vallist_seg_upd_irr with (y:= (Vptr x0)) (M:=∘M)in Hrs;auto.
  remember ( vallist_seg 0 ∘M v2) as xy.
  apply eq_sym in Heqxy.
  lets Has : vallist_seg_upd_prop (Vptr x0) Heqxy.
  rewrite Hlen.
  clear - He4.
  simpljoin1.
  omega.
  clear -x.
  omega.
  rewrite Has.
  rewrite app_assoc.
  rewrite Hrs.
  remember ( vallist_seg ∘N ∘(Int.unsigned x2) (update_nth_val ∘M v2 (Vptr x0))) as l1.
  remember (vallist_seg 0 (S ∘M) (update_nth_val ∘M v2 (Vptr x0))) as l2.
  apply eq_sym in Heql1.
  apply eq_sym in Heql2.
  lets Hl1 : vallist_seg_length_prop Heql1.
  clear - H4.
  omega.
  rewrite update_nth_val_len_eq.
  rewrite Hlen.
  clear -He4.
  simpljoin1.
  omega.
  lets Hl2 : vallist_seg_length_prop Heql2.
  clear -x.
  omega.
  rewrite update_nth_val_len_eq.
  rewrite Hlen.
  clear -He4.
  simpljoin1.
  rewrite H0.
  omega.
  assert (length (l1 ++ xy) = length x1).
  rewrite Hrs; auto.
  assert (length l2 = length ( xy ++ Vptr x0 :: nil)) .
  rewrite Has.
  auto.
  rewrite app_length in H14.
  rewrite app_length in H17.
  rewrite Hl1 in H14.
  rewrite Hl2 in H17.
  simpl in H17.
  assert (length xy = ∘M)% nat.
  clear - H17.
  omega.
  rewrite H18 in H14.
  assert (length x1 =(∘(Int.unsigned x2)-1))%nat.
  clear - H14 He4 H2 H4.
  simpljoin1.
  rewrite <- H0 in H14.
  omega.
  split; auto.
  eapply math_int_eq_len; eauto.
  clear - He4.
  simpljoin1.
  omega.
  rewrite Hlen.
  eapply He4.
  eapply isptr_list_tail_add;eauto.
  unfolds.
  eexists.
  splits.
  unfolds; simpl; eauto.
  rewrite app_length.
  simpl.
  eapply  math_inc_eq_ltu; eauto.
  unfolds.
  eexists.
  splits; auto.
  unfolds; simpl; eauto.
  rewrite Int.repr_unsigned; auto.
  unfolds.
  splits; auto.
  intros.
  tryfalse.
Qed.


Lemma prio_in_rtbl_hold:
  forall rtbl x y prio,
    Int.unsigned prio < 64 ->
    Int.unsigned x <= 7 ->
    length rtbl = ∘OS_RDY_TBL_SIZE ->
    array_type_vallist_match Int8u rtbl ->
    prio_in_tbl prio rtbl ->
    prio_in_tbl prio
                (update_nth_val (Z.to_nat (Int.unsigned x)) rtbl
                                (val_inj
                                   (or (nth_val' (Z.to_nat (Int.unsigned x)) rtbl) (Vint32 y)))).
Proof.
  introv Hr1 Hr2 Hlen Har Hpro.
  unfolds.
  intros.
  subst.
  unfolds in Hpro.
  remember (val_inj
               (or (nth_val' (Z.to_nat (Int.unsigned x)) rtbl) (Vint32 y))) as Hx.
  assert ((Z.to_nat (Int.unsigned x)) < length rtbl)%nat.
  rewrite Hlen.
  clear - Hr2.
  mauto.
  lets Hsx : array_int8u_nth_lt_len Har H.
  simpljoin1.
  rewrite H0 in H1.
  simpl in H1.
  remember (Int.shru prio ($3)) as py.
  assert (py = x \/ py <> x) by tauto.
  destruct H3.
  subst x.
  unfold nat_of_Z in H1.
  apply nth_upd_eq in H1.
  inverts H1.
  apply nth_val'_imp_nth_val_int in H0.
  lets Hsd : Hpro H0; eauto.
  rewrite Int.and_commut.
  rewrite Int.and_or_distrib.
  rewrite Int.and_commut in Hsd.
  rewrite Hsd.
  rewrite Int.or_and_absorb.
  auto.
  apply nth_upd_neq in H1.
  lets Hsd : Hpro H1; eauto.
  introv Hf.
  apply H3.
  unfold nat_of_Z in Hf.
  apply Z2Nat.inj_iff in Hf;  try apply Int.unsigned_range.
  apply unsigned_inj ; auto.
Qed.


Lemma idle_in_rtbl_hold':
  forall rtbl x y,
    Int.unsigned x <= 7 ->
    length rtbl = ∘OS_RDY_TBL_SIZE ->
    array_type_vallist_match Int8u rtbl ->
    prio_in_tbl ($ OS_IDLE_PRIO) rtbl ->
    prio_in_tbl ($ OS_IDLE_PRIO)
                (update_nth_val (Z.to_nat (Int.unsigned x)) rtbl
                                (val_inj
                                   (or (nth_val' (Z.to_nat (Int.unsigned x)) rtbl) (Vint32 y)))).
Proof.
  intros.
  eapply prio_in_rtbl_hold; eauto.
  unfold OS_IDLE_PRIO.
  unfold OS_LOWEST_PRIO.
  clear-x.
  int auto.
Qed.






Lemma get_tcb_stat:
  forall p etbl ptbl tid tcbls abstcb tcbls' vl rtbl qid vle vhold,
    0 <= Int.unsigned p < 64 ->
    array_type_vallist_match Int8u etbl ->
    length etbl = ∘OS_EVENT_TBL_SIZE ->
    prio_in_tbl p etbl ->
    nth_val' (Z.to_nat (Int.unsigned p)) ptbl = Vptr tid ->
    R_PrioTbl_P ptbl tcbls vhold -> 
    TcbJoin tid abstcb tcbls' tcbls ->
    TCBNode_P vl rtbl abstcb -> 
    R_ECB_ETbl_P qid
                 (V$OS_EVENT_TYPE_Q
                   ::vle,
                  etbl) tcbls ->
    V_OSTCBStat vl = Some (Vint32 (Int.repr OS_STAT_Q)).
Proof.
  introv Hran Harr Hlen Hpri Hnth Hr Htj Htn Hre.
  unfolds in Hre.
  destruct Hre as (Hre1 & Hre2 & Hre3).
  unfolds in Hre2.
  destruct Hre1 as (Hre1& _).
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
  destruct Hrc as (_&_&Hrc&_).
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
  assert ( V_OSEventType (V$OS_EVENT_TYPE_Q :: vle) = Some (V$OS_EVENT_TYPE_Q)).
  unfolds.
  simpl; auto.
  lets Hsd : Hre1 H15 H20.
  simpljoin1.
  rewrite Int.repr_unsigned in H21.
  assert (x = tid \/ x <> tid) by tauto.
  destruct H23.
  subst x.
  unfold get in H21; simpl in H21.
  rewrite Hges in H21.
  inverts H21.
  eapply Hrc; eauto.
  unfolds in H22.
  lets Hfs : H22 H23 H21 Hges.
  tryfalse.
 Qed.



Lemma rh_tcblist_ecblist_p_post_exwt_aux:
  forall (v'8 tid0 : tid) (v'11 : EcbMod.map) 
         (v'7 : TcbMod.map) (v'9 v'10 : EcbMod.map) 
         (eid : tidspec.A) (x : list msg) 
         (x0 : maxlen) (x1 : waitset) (v'6 : EcbMod.map) 
         (prio : priority) (msg0 : msg) 
         st,
    RH_TCBList_ECBList_P v'11 v'7 v'8 ->
    EcbMod.join v'9 v'10 v'11 ->
    EcbMod.joinsig eid (absmsgq x x0, x1) v'6 v'10 ->
    In tid0 x1 ->
    TcbMod.get v'7 tid0 = Some (prio, st, msg0) ->
    exists xl, st =  wait (os_stat_q eid) xl.
Proof.
  intros.
  unfolds in H.
  destruct H as (Hex & Hexa).
  lets Hget : EcbMod.join_joinsig_get H0 H1.
  assert (EcbMod.get v'11 eid = Some (absmsgq x x0, x1) /\ In tid0 x1).
  split; auto.
  apply Hex in H.
  simpljoin1.
  unfold get in H; simpl in H.
  rewrite H3 in H.
  inverts H.
  eauto.
Qed.
  

Lemma statq_and_not_statq_eq_rdy:
  Int.eq ($ OS_STAT_Q&ᵢInt.not ($ OS_STAT_Q)) ($ OS_STAT_RDY) = true.
Proof.
  rewrite Int.and_not_self.
  auto.
Qed.

Lemma isptr_zh :
  forall x, isptr x ->
            match x with
              | Vundef => false
              | Vnull => true
              | Vint32 _ => false
              | Vptr _ => true
            end = true.
Proof.
  intros.
  unfolds in H; destruct H.
  substs; auto.
  destruct H; substs; auto.
Qed.


(***lemmas***)
Lemma tcbdllseg_get_last_tcb_ptr :
  forall vl head headprev tail tailnext P s,
    s |= tcbdllseg head headprev tail tailnext vl ** P ->
    get_last_tcb_ptr vl head = Some tailnext.
Proof.
  induction vl; intros.
  destruct_s s; simpl in H; simpljoin.
  simpl; auto.

  unfold tcbdllseg in H; unfold dllseg in H; fold dllseg in H.
  sep normal in H; destruct H; sep split in H.
  sep remember (1::nil)%nat in H.
  destruct_s s.
  unfold sat in H; fold sat in H.
  Ltac simpl_state := simpl substmo in *; simpl getmem in *; simpl getabst in *.
  simpl_state; simpljoin1.
  unfold tcbdllseg in IHvl.
  lets Hx: IHvl H8.
  simpl.
  destruct vl; auto.
  simpl in Hx; inverts Hx; auto.
Qed.

Lemma tcbdllseg_combine_ptr_in_tcblist :
  forall vl1 vl2 head1 headprev1 tail1 tailnext1 tail2 tailnext2 s P,
    s |= tcbdllseg head1 headprev1 tail1 tailnext1 vl1 ** tcbdllseg tailnext1 tail1 tail2 tailnext2 vl2 ** P ->
    vl2 <> nil ->
    ptr_in_tcblist tailnext1 head1 (vl1 ++ vl2).
Proof.
  inductions vl1; intros.
  unfold tcbdllseg in H at 1.
  simpl dllseg in H.
  sep split in H; substs.
  rewrite app_nil_l.

  Lemma tcbdllseg_ptr_in_tcblist_head :
    forall vl head headprev tail tailnext s P,
      s |= tcbdllseg head headprev tail tailnext vl ** P ->
      vl <> nil ->
      ptr_in_tcblist head head vl.
  Proof.
    destruct vl; intros; tryfalse.
    destruct_s s; unfold tcbdllseg in H; unfold dllseg in H; fold dllseg in H.
    sep normal in H; destruct H; sep split in H.
    simpl.
    Lemma beq_addrval_true : forall a, beq_addrval a a = true.
    Proof.
      intro.
      destruct a; simpl.
      rewrite Int.eq_true.
      rewrite beq_pos_Pos_eqb_eq.
      rewrite Pos.eqb_refl.
      simpl; auto.
    Qed.

    Lemma beq_val_true : forall v, beq_val v v = true.
    Proof.
      intro.
      destruct v; simpl; auto.
      rewrite Int.eq_true; auto.
      rewrite beq_addrval_true; auto.
    Qed.
    rewrite beq_val_true.
    auto.
  Qed.

  apply tcbdllseg_ptr_in_tcblist_head in H; auto.
  unfold tcbdllseg in H at 1.
  unfold dllseg in H; fold dllseg in H.
  sep normal in H; destruct H; sep split in H.
  sep remember (1::nil)%nat in H.
  destruct_s s.
  unfold sat in H; fold sat in H.
  simpl_state; simpljoin1.
  unfold tcbdllseg in IHvl1 at 1.
  lets Hx: IHvl1 H9 H0.
  rewrite <- app_comm_cons.
  simpl.
  destruct (beq_val tailnext1 head1); auto.
  rewrite H1; auto.
Qed.

Lemma sep_disj_dist :
  forall P Q R s,
    s |= (P \\// Q) ** R ->
    s |= (P ** R) \\// (Q ** R).
Proof.
  intros.
  destruct_s s.
  simpl in H; simpljoin1.
  destruct H3.
  left.
  simpl.
  do 6 eexists; splits; eauto.
  right.
  simpl.
  do 6 eexists; splits; eauto.
Qed.

Lemma tcbdllseg_split_hoare :
  forall spec sd linv inv r ri tid tcbls rtbl vltcb P s q head tail,
    ptr_in_tcbdllseg (Vptr tid) head vltcb ->
    TCBList_P head vltcb rtbl tcbls ->
    {|spec, sd, linv, inv, r, ri|} |- tid
      {{
          EX (l1 l2 : list vallist) tcb_cur (tail1 : val) (tcbls1 tcbls2 : TcbMod.map),
          tcbdllseg head Vnull tail1 (Vptr tid) l1 **
                    tcbdllseg (Vptr tid) tail1 tail Vnull (tcb_cur :: l2) **
                    [|vltcb = l1 ++ (tcb_cur :: l2)|] **
                    [|TcbMod.join tcbls1 tcbls2 tcbls|] **
                    [|TCBList_P head l1 rtbl tcbls1|] **
                    [|TCBList_P (Vptr tid) (tcb_cur :: l2) rtbl tcbls2|] ** P
        }} s {{q}} ->
    {|spec, sd, linv, inv, r, ri|} |- tid {{tcbdllseg head Vnull tail Vnull vltcb ** P }} s {{q}}.
Proof.
  intros.
  eapply backward_rule1.
  eapply tcbdllseg_split'; eauto.
  eapply backward_rule1.
  instantiate(1:=(EX (l1 l2 : list vallist) (tcb_cur : vallist) 
                     (tail1 : val) (tcbls1 tcbls2 : TcbMod.map),
                  tcbdllseg head Vnull tail1 (Vptr tid) l1 **
                            tcbdllseg (Vptr tid) tail1 tail Vnull (tcb_cur :: l2) **
                            [|vltcb = l1 ++ tcb_cur :: l2|] **
                            [|TcbMod.join tcbls1 tcbls2 tcbls|] **
                            [|TCBList_P head l1 rtbl tcbls1|] **
                            [|TCBList_P (Vptr tid) (tcb_cur :: l2) rtbl tcbls2|] ** P)).
  intros; clear H1.
  destruct H2.
  do 4 destruct H1.
  destruct x0.
  unfold tcbdllseg in H1 at 2.
  simpl dllseg in H1.
  sep split in H1; tryfalse.
  sep auto; eauto.
  auto.
Qed.


Lemma tcbdllseg_split_hoare' :
  forall spec sd linv inv r ri tid P s q head tail vltcb1 vl vltcb2,
    {|spec, sd, linv, inv, r, ri|} |- tid
      {{EX tail1 tailnext1,
          tcbdllseg head Vnull tail1 tailnext1 vltcb1 **
          tcbdllseg tailnext1 tail1 tail Vnull (vl :: vltcb2) **
          [|get_last_tcb_ptr vltcb1 head = Some tailnext1|] ** P
        }} s {{q}} ->
      {|spec, sd, linv, inv, r, ri|} |- tid
        {{tcbdllseg head Vnull tail Vnull (vltcb1++vl::vltcb2) ** P }} s {{q}}.
Proof.
  intros.
  Lemma tcbdllseg_head_vptr :
    forall vltcb1 vl vltcb2 head tail s,
      s |= tcbdllseg head Vnull tail Vnull (vltcb1++vl::vltcb2) ->
      exists a, head = Vptr a.
  Proof.
    intros.
    destruct vltcb1.
    rewrite app_nil_l in H.
    unfold tcbdllseg in H.
    unfold dllseg in H; fold dllseg in H.
    sep normal in H.
    destruct H.
    sep split in H.
    unfold node in H; sep normal in H; destruct H.
    sep split in H.
    simpljoin.
    eauto.
    rewrite <- app_comm_cons in H.
    unfold tcbdllseg in H.
    unfold dllseg in H; fold dllseg in H.
    sep normal in H.
    destruct H.
    sep split in H.
    unfold node in H; sep normal in H; destruct H.
    sep split in H.
    simpljoin.
    eauto.
  Qed.

  eapply hoare_pure_gen with (p:=(exists a, head = Vptr a)).
  intros.
  eapply tcbdllseg_head_vptr in H0; auto.
  pure intro.
  eapply backward_rule1.
  intros.
  eapply ucos_common.tcbdllseg_split; eauto.
  pure intro.
  eapply backward_rule1
  with (p:=(EX tail1 tailnext1 : val,
        tcbdllseg (Vptr x) Vnull tail1 tailnext1 vltcb1 **
        tcbdllseg tailnext1 tail1 tail Vnull (vl :: vltcb2) **
        [|get_last_tcb_ptr vltcb1 (Vptr x) = Some tailnext1|] ** P)).
  intros.
  sep auto.
  destruct H0; simpljoin.
  unfolds.
  destruct vltcb1; tryfalse.
  unfolds; auto.
  inverts H2.
  simpl; auto.
  auto.
Qed.


Lemma ecblist_p_post_exwt_hold1:
  forall  v'36 v'12 v'13 v'38 v'69 v'39 v'58 v'40  v'32 v'15 v'24 v'35 v'16
          v'18 v'19 v'20 v'34 v'21 v'22 v'23 v'25 v'26 v'27 x x0 x1 v'0 v'1
          v'5 v'6 v'7 x00 v'11 v'31 v'30 v'29 v'10 v'9 prio v'62 st msg y vhold,
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
    nth_val' (Z.to_nat (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39))) v'36 = Vptr (v'58, Int.zero)->
    nth_val' (Z.to_nat (Int.unsigned v'39)) OSMapVallist = Vint32 v'40 ->
    Int.unsigned v'40 <= 128 ->
    RL_Tbl_Grp_P v'13 (Vint32 v'12) ->
(**)    
    R_ECB_ETbl_P (v'32, Int.zero)
                 (V$OS_EVENT_TYPE_Q
                   :: Vint32 v'12
                   :: Vint32 v'15 :: Vptr (v'24, Int.zero) :: v'35 :: v'0 :: nil,
                  v'13) v'7 ->
    RLH_ECBData_P
      (DMsgQ (Vptr (v'24, Int.zero))
             (v'16
                :: v'18
                :: v'19
                :: v'20
                :: v'34
                :: Vint32 v'21
                :: Vint32 v'22 :: Vptr (v'23, Int.zero) :: nil)
             (v'26 :: v'25 :: nil) v'27) (absmsgq x x0, x1) ->
    ECBList_P v'0 Vnull v'1 v'5 v'6 v'7 ->
    ECBList_P v'29 (Vptr (v'32, Int.zero)) v'30 v'31 v'9 v'7 ->
    EcbMod.joinsig (v'32, Int.zero) (absmsgq x x0, x1) v'6 v'10 ->
    EcbMod.join v'9 v'10 v'11 ->
    TcbJoin (v'58, Int.zero) (prio, st, msg) v'62 v'7 ->
    R_PrioTbl_P v'36 v'7 vhold ->
    x1 <> nil ->
    ECBList_P v'29 Vnull
              (v'30 ++
                    ((V$OS_EVENT_TYPE_Q
                       :: Vint32 y
                       :: Vint32 v'15 :: Vptr (v'24, Int.zero) :: v'35 :: v'0 :: nil,
                      update_nth_val (Z.to_nat (Int.unsigned v'38)) v'13
                                     (Vint32 (v'69&ᵢInt.not v'40))) :: nil) ++ v'1)
              (v'31 ++
                    (DMsgQ (Vptr (v'24, Int.zero))
                           (v'16
                              :: v'18
                              :: v'19
                              :: v'20
                              :: v'34
                              :: Vint32 v'21
                              :: Vint32 v'22 :: Vptr (v'23, Int.zero) :: nil)
                           (v'26 :: v'25 :: nil) v'27 :: nil) ++ v'5)
              (EcbMod.set v'11 (v'32, Int.zero)
                          (absmsgq nil x0, remove_tid (v'58, Int.zero) x1))
              (TcbMod.set v'7 (v'58, Int.zero)
                          (prio, rdy , Vptr x00))
.
Proof.
  intros.
  unfolds in H20.
  destruct H20 as (Ha1 & Ha2 & Ha3).
  assert ( 0 <= Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39) < 64).
  clear -H4 H8.
  mauto.
  unfold nat_of_Z in Ha1.
  eapply nth_val'_imp_nth_val_vptr in H9.
  lets Hps : Ha1 H20 H9.
  apply tcbjoin_get_a in H19.
  assert ((v'58, Int.zero) <> vhold) as Hnvhold.
  apply Ha2 in H19.
  destruct H19;auto.
  destruct Hps as (sts & mg & Hget);auto.
  unfold get in Hget; simpl in Hget.
  rewrite Hget in H19.
  inverts H19.
  remember ((v'38<<ᵢ$ 3)) as px.
  remember (v'39) as py.
  clear Heqpy.
  remember (px+ᵢpy) as prio.
  remember ( (v'58, Int.zero)) as tid.
  unfolds in H13.
  destruct H13 as (Ha & Hb & Hc).
  destruct Ha as (Ha&Ha'&Ha''&Ha''').
  destruct Hb as (Hb&Hb'&Hb''&Hb''').
  lets Hz : math_unmap_get_y H0 H3.
  lets Heq1 :  math_mapval_core_prop H10; eauto.
  omega.
  subst v'40.
  assert (v'38 = Int.shru prio ($3)).
  subst.
  clear -Hz H8.
  mauto.
  assert (py = prio &ᵢ $ 7).
  subst prio. 
  rewrite Heqpx.
  clear -Hz H8.
  mauto.
  rewrite H13 in H5.
  assert (PrioWaitInQ (Int.unsigned prio) v'13) as Hcp.
  unfolds.
  do 3 eexists; splits; eauto.
  rewrite Int.repr_unsigned.
  eapply nth_val'_imp_nth_val_int; eauto.
  rewrite Int.repr_unsigned.
  rewrite <- H19.
  unfold Int.one.
  eapply math_8_255_eq; eauto.
  
  unfold Int.zero in H.
  rewrite <-H13 in *.
  lets Hneq :  rl_tbl_grp_neq_zero H0 H  H3 H5 H12.
  omega.
  auto.
  lets Hecp : Ha Hcp.
  unfold V_OSEventType in Hecp.
  simpl nth_val in Hecp.
  assert (Some (V$OS_EVENT_TYPE_Q) = Some (V$OS_EVENT_TYPE_Q)) by auto.
  apply Hecp in H22.
  clear Hecp.
  rename H22 into Hecp.
  destruct Hecp as (ct & nl & mg & Hcg).
  assert (ct = tid) as Hed.
  assert (ct = tid \/ ct <> tid)  by tauto.
  destruct H22; auto.
  lets Heqs : Ha3 H22 Hcg Hget.
  rewrite Int.repr_unsigned in Heqs.
  tryfalse.
  subst ct.
  unfold get in Hcg; simpl in Hcg.
  rewrite Hget in Hcg.
  inversion Hcg.
  subst mg st .
  clear Hcg.
  
  lets Hsds : ecb_set_join_join  (absmsgq nil x0, remove_tid tid x1)  H17  H18.
  destruct Hsds as ( vv & Hsj1 & Hsj2).
  eapply msgqlist_p_compose.
  instantiate (1:= (v'32, Int.zero)).
  unfolds.
  splits.
  unfolds.
  splits;unfolds.
  
  introv Hprs Hxx.
  clear Hxx.
  apply prio_wt_inq_convert in Hprs.
  destruct Hprs as (Hprs1 & Hprs2).
  rewrite H13 in Hprs1.
  rewrite H19 in Hprs1.
  lets Hrs : prio_wt_inq_tid_neq  H5 H20 .
  destruct Hrs as (Hrs & _).
  apply Hrs in Hprs1.
  destruct Hprs1 as (Hpq & Hneq).
  unfolds in Ha.
  lets Hxs : Ha Hpq.
  rewrite Int.repr_unsigned in Hxs.
  destruct Hxs as (tid' & nn & mm & Htg).
  unfolds;simpl;auto.
  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H22.
  subst tid'.
  unfold get in Htg; simpl in Htg.
  rewrite Hget in Htg.
  inversion Htg.
  tryfalse.
  exists tid' nn mm.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false;eauto.

  intros.
  unfolds in H24;simpl in H24;tryfalse.
  intros.
  unfolds in H24;simpl in H24;tryfalse.
  intros.
  unfolds in H24;simpl in H24;tryfalse.

  unfolds.
  splits;
  intros prio' mm nn tid'.
  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H22.
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
  lets Hneqp: Ha3 H22 Hget Hgs.
  assert ( PrioWaitInQ (Int.unsigned prio') v'13 /\ prio' <> prio) .
  splits; auto.

  lets Hrs : prio_wt_inq_tid_neq  H5 H20 .
  destruct Hrs as (_ & Hrs).
  apply Hrs in H24.
  rewrite H19.
  rewrite H13.
  auto.

  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H22.
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
  lets Hneqp: Ha3 H22 Hget Hgs.
  assert ( PrioWaitInQ (Int.unsigned prio') v'13 /\ prio' <> prio) .
  splits; auto.
  unfolds in Hx;simpl in Hx;tryfalse.

  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H22.
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
  lets Hneqp: Ha3 H22 Hget Hgs.
  assert ( PrioWaitInQ (Int.unsigned prio') v'13 /\ prio' <> prio) .
  splits; auto.
  unfolds in Hx;simpl in Hx;tryfalse.

  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H22.
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
  lets Hneqp: Ha3 H22 Hget Hgs.
  assert ( PrioWaitInQ (Int.unsigned prio') v'13 /\ prio' <> prio) .
  splits; auto.
  unfolds in Hx;simpl in Hx;tryfalse.

  simpl fst in Hc;simpl;auto.
  
  instantiate (1:=v'9).
  eapply ECBList_P_Set_Rdy_hold;eauto.
  rewrite Int.repr_unsigned.  
  eauto.
  eapply joinsig_join_getnone; eauto.
  instantiate (1:=v'6).
  eapply ECBList_P_Set_Rdy_hold;eauto.
  rewrite Int.repr_unsigned.  
  eauto.
  eapply  joinsig_get_none; eauto.
  unfolds in H14.
  simpljoin1.
  unfolds in r.
  apply r in H21.
  subst x.
  instantiate (1:=(absmsgq nil x0, remove_tid tid x1)).
  splits; auto.
  unfolds.
  splits; intros; auto; tryfalse.
  eapply Hsj1.
  eapply Hsj2.
Qed.

Lemma qpost_ovf_prop1 :
  forall (i2 i1 : int32) (x13 x12 x6 x7 x8 : val) 
         (v'49 v'47 : block) (x14 x15 : val) (x : list msg) 
         (x1 : maxlen) (x2 : waitset) (v2 : vallist),
    (true = Int.ltu i2 i1 \/ true = Int.eq i1 i2) ->
    WellformedOSQ
      (x13
         :: x12
         :: x6
         :: x7
         :: x8
         :: Vint32 i2
         :: Vint32 i1 :: Vptr (v'49, Int.zero) :: nil) ->
    RLH_ECBData_P
      (DMsgQ (Vptr (v'47, Int.zero))
             (x13
                :: x12
                :: x6
                :: x7
                :: x8
                :: Vint32 i2
                :: Vint32 i1 :: Vptr (v'49, Int.zero) :: nil)
             (x14 :: x15 :: nil) v2) (absmsgq x x1, x2) ->
    Z.of_nat (length x) >= Int.unsigned x1.
Proof.
  intros.
  destruct H.
  eapply qpost_ovf_prop; eauto.
  eapply qpost_ovf_prop'; eauto.
Qed.

Fixpoint vptr_next (head:val) (vltcb:list vallist) :=
  match vltcb with
    | nil => True
    | vl::vltcb' =>
      exists a, head = Vptr a /\
                match V_OSTCBNext vl with
                  | Some vn => vptr_next vn vltcb'
                  | None => False
                end
  end.


Definition distinct_tcbdllseg_next_ptr_vnull (head : val) (l : list vallist) :=
  distinct_tcbdllseg_next_ptr head l /\ get_last_tcb_ptr l head = Some Vnull /\
  vptr_next head l.

Lemma tcbdllseg_vptr_next :
  forall vltcb head headprev tail tailnext s P,
    s |= tcbdllseg head headprev tail tailnext vltcb ** P ->
    vptr_next head vltcb.
Proof.
  inductions vltcb; intros.
  simpl; auto.

  unfold tcbdllseg in H.
  unfold dllseg in H; fold dllseg in H.
  sep normal in H; destruct H; sep split in H.
  sep remember (1::nil)%nat in H.
  destruct_s s.
  unfold sat in H; fold sat in H.
  simpl getmem in H; simpl getabst in H; simpl substmo in H.
  simpljoin.
  eapply IHvltcb in H8.
  unfold vptr_next; fold vptr_next.
  rewrite H0.
  unfold node in H7; sep normal in H7.
  destruct H7.
  sep split in H.
  simpljoin.
  eauto.
Qed.

  
Lemma tcbdllseg_distinct_tcbdllseg_next_ptr_vnull :
  forall vltcb head headprev tail s P,
    s |= tcbdllseg head headprev tail Vnull vltcb ** P ->
    distinct_tcbdllseg_next_ptr_vnull head vltcb.
Proof.
  intros.
  unfolds.
  split.
  inductions vltcb; intros.
  unfolds.
  simpl.
  unfold tcbdllseg in H.
  unfold dllseg in H.
  sep split in H.
  substs.
  auto.

  unfold tcbdllseg in H.
  unfold dllseg in H; fold dllseg in H.
  sep normal in H.
  destruct H.
  sep split in H.
  destruct_s s.
  assert
    (
      (e, e0, m, i, (i0, i1, c), o, a0)
        |= node head a OS_TCB_flag **
        dllseg x head tail Vnull vltcb OS_TCB_flag V_OSTCBPrev V_OSTCBNext **
        P
    ) as H_bak by auto.
  sep remember (1::nil)%nat in H.
  simpl_sat H; simpljoin.
  unfold tcbdllseg in IHvltcb.
  lets Hx: IHvltcb H8.

  unfold distinct_tcbdllseg_next_ptr; fold distinct_tcbdllseg_next_ptr.
  rewrite H0.
  destruct vltcb; auto.
  split; auto.
  eapply not_ptr_in_tcbdllseg1; eauto.
  split.
  eapply tcbdllseg_get_last_tcb_ptr; eauto.
  eapply tcbdllseg_vptr_next; eauto.
Qed.

Lemma app_cons_not_nil :
  forall {A} (vl1:list A) v vl2,
  exists a vl', vl1++v::vl2 = a::vl'.
Proof.
  inductions vl1; intros.
  rewrite app_nil_l; eauto.
  rewrite <- app_comm_cons.
  pose proof IHvl1 v vl2.
  simpljoin.
  rewrite H.
  exists a (x::x0).
  auto.
Qed.

Lemma get_last_tcb_ptr_last :
  forall vltcb vl head,
    get_last_tcb_ptr (vltcb++vl::nil) head = Some Vnull ->
    V_OSTCBNext vl = Some Vnull.
Proof.
  inductions vltcb; intros.
  rewrite app_nil_l in H.
  simpl in H; auto.
  rewrite <- app_comm_cons in H.
  eapply IHvltcb with (head:=head).
  unfold get_last_tcb_ptr in *.

  pose proof app_cons_not_nil (A:=vallist) vltcb vl nil.
  do 2 destruct H0.
  rewrite H0.
  rewrite H0 in H.
  unfold last in *; auto.
Qed.


Lemma tcblist_get_split :
  forall vltcb p head vl,
    tcblist_get p head vltcb = Some vl ->
    exists vltcb1 vltcb2, vltcb = vltcb1++vl::vltcb2.
Proof.
  inductions vltcb; intros.
  simpl in H; tryfalse.

  unfold tcblist_get in H; fold tcblist_get in H.
  destruct (beq_val p head) eqn : eq1.
  inverts H.
  exists (nil (A:=vallist)) vltcb.
  rewrite app_nil_l; auto.

  destruct(V_OSTCBNext a) eqn: eq2; tryfalse.

  lets Hx: IHvltcb H; simpljoin.
  rewrite app_comm_cons.
  eauto.
Qed.

Lemma ptr_in_tcbdllseg1_true :
  forall vltcb1 vltcb2 vl vl' head p,
    V_OSTCBNext vl = Some p ->
    vptr_next head (vltcb1 ++ vl :: vl' :: vltcb2) ->
    ptr_in_tcbdllseg1 p head (vltcb1 ++ vl :: vl' :: vltcb2).
Proof.
  inductions vltcb1; intros.
  rewrite app_nil_l.
  unfold ptr_in_tcbdllseg1; fold ptr_in_tcbdllseg1.
  rewrite H.
  rewrite beq_val_true.
  destruct (beq_val p head); auto.

  rewrite <- app_comm_cons in *. 
  unfold ptr_in_tcbdllseg1; fold ptr_in_tcbdllseg1.
  unfold vptr_next in H0; fold vptr_next in H0; simpljoin.
  destruct (beq_val p (Vptr x)); auto.
  destruct (V_OSTCBNext a); tryfalse.
  eapply IHvltcb1; eauto.
Qed.

Lemma distinct_tcbdllseg_next_ptr_vnull_dup_node_false :
  forall vltcb1 vltcb2 head vl,
    distinct_tcbdllseg_next_ptr_vnull head (vl :: vltcb1 ++ vl :: vltcb2) ->
    False.
Proof.
  intros.
  destruct vltcb2.
  unfolds in H; simpljoin.
  rewrite app_comm_cons in H0.

  apply get_last_tcb_ptr_last in H0.
  unfold vptr_next in H1; fold vptr_next in H1.
  simpljoin.
  destruct (V_OSTCBNext vl) eqn : eq1; tryfalse.
  inverts H0.
  destruct vltcb1.
  rewrite app_nil_l in H2.
  unfold vptr_next in H2; simpljoin; tryfalse.
  rewrite <- app_comm_cons in H2.
  unfold vptr_next in H2; simpljoin; tryfalse.

  unfolds in H; simpljoin.
  unfold distinct_tcbdllseg_next_ptr in H; fold distinct_tcbdllseg_next_ptr in H.
  pose proof app_cons_not_nil (A:=vallist) vltcb1 vl (v::vltcb2).
  simpljoin.
  rewrite H2 in H.
  destruct (V_OSTCBNext vl) eqn : eq1; tryfalse.
  simpljoin.
  rewrite <- H2 in H3.

  destruct vltcb1.
  rewrite app_nil_l in H3.
  unfold distinct_tcbdllseg_next_ptr in H3; fold distinct_tcbdllseg_next_ptr in H3.
  rewrite eq1 in H3.
  destruct H3.
  unfold ptr_in_tcbdllseg1 in H3; fold ptr_in_tcbdllseg1 in H3.
  rewrite beq_val_true in H3.
  apply H3; auto.

  rewrite <- app_comm_cons in H3.
  unfold distinct_tcbdllseg_next_ptr in H3; fold distinct_tcbdllseg_next_ptr in H3.
  pose proof app_cons_not_nil (A:=vallist) vltcb1 vl (v::vltcb2); simpljoin.
  rewrite H4 in H3.
  destruct (V_OSTCBNext v1) eqn : eq2; tryfalse.
  destruct H3.
  rewrite <- H4 in H3.
  unfold vptr_next in H1; fold vptr_next in H1; simpljoin.
  rewrite eq1 in H6.
  rewrite <- app_comm_cons in H6.
  unfold vptr_next in H6; fold vptr_next in H6; simpljoin.
  destruct (V_OSTCBNext v1) eqn : eq3; tryfalse.
  inverts eq2.

  apply H3.
  eapply ptr_in_tcbdllseg1_true; auto.
Qed.

Lemma tcblist_get_distinct_tcbdllseg_next_ptr_vnull_false :
  forall vltcb head vl v p,
    distinct_tcbdllseg_next_ptr_vnull head (vl :: vltcb) ->
    V_OSTCBNext vl = Some v ->
    tcblist_get p v vltcb = Some vl ->
    False.
Proof.
  intros.
  eapply tcblist_get_split in H1; simpljoin.
  eapply distinct_tcbdllseg_next_ptr_vnull_dup_node_false; eauto.
Qed.

Lemma distinct_tcbdllseg_next_ptr_vnull_tail :
  forall vltcb vl head v,
    distinct_tcbdllseg_next_ptr_vnull head (vl :: vltcb) ->
    V_OSTCBNext vl = Some v ->
    distinct_tcbdllseg_next_ptr_vnull v vltcb.
Proof.
  inductions vltcb; intros.
  unfold distinct_tcbdllseg_next_ptr_vnull in *; simpljoin.
  split.
  unfold distinct_tcbdllseg_next_ptr in *; auto.
  split.
  simpl in *.
  rewrite H1 in H0; auto.
  simpl; auto.

  assert(distinct_tcbdllseg_next_ptr_vnull head (vl :: a :: vltcb)) as H_bak.
  auto.
  unfolds in H.
  simpljoin.
  unfold distinct_tcbdllseg_next_ptr in H; fold distinct_tcbdllseg_next_ptr in H.
  rewrite H0 in H.
  destruct H.
  destruct vltcb.
  unfolds.
  simpl.
  split; auto.
  split.
  simpl in H1; auto.
  simpl in H2.
  destruct H2.
  destruct H2.
  rewrite H0 in H4.
  eauto.
  destruct(V_OSTCBNext a) eqn : eq2; tryfalse.
  assert(distinct_tcbdllseg_next_ptr_vnull head (a :: v0 :: vltcb)).
  unfolds.
  destruct H3.
  splits; auto.
  unfold distinct_tcbdllseg_next_ptr; fold distinct_tcbdllseg_next_ptr.
  rewrite eq2.
  split; auto.
  intro.
  apply H.
  clear - eq2 H5.
  unfold ptr_in_tcbdllseg1 in *; fold ptr_in_tcbdllseg1 in *.
  destruct (beq_val head v) eqn : eq1; auto.
  rewrite eq2.
  auto.

  unfold vptr_next in *; fold vptr_next in *.
  rewrite  eq2 in *.
  destruct H2.
  destruct H2.
  rewrite H0 in H5.
  simpljoin.
  destruct (V_OSTCBNext v0); tryfalse.
  eauto.

  eapply IHvltcb in H4; eauto.
  unfold distinct_tcbdllseg_next_ptr_vnull in *.
  simpljoin.
  splits; auto.
  unfold distinct_tcbdllseg_next_ptr; fold distinct_tcbdllseg_next_ptr.
  rewrite eq2.
  split; auto.

  unfold vptr_next in H9; fold vptr_next in H9.
  rewrite eq2 in H9; rewrite H0 in H9.
  simpljoin.
  unfold vptr_next; fold vptr_next.
  rewrite eq2.
  eexists.
  splits; eauto.
Qed.

Lemma distinct_tcbdllseg_next_ptr_vnull_tcblist_get_get_last_tcb_ptr :
  forall vltcb1 vltcb2 vl head tid p,
    tcblist_get (Vptr tid) head (vltcb1++vl::vltcb2) = Some vl ->
    get_last_tcb_ptr vltcb1 head = Some p ->
    distinct_tcbdllseg_next_ptr_vnull head (vltcb1++vl::vltcb2) ->
    p = (Vptr tid).
Proof.
  induction vltcb1; intros.
  simpl in H0; inverts H0.
  rewrite app_nil_l in H.
  unfold tcblist_get in H; fold tcblist_get in H.
  destruct (beq_val (Vptr tid) p) eqn : eq1.
  apply beq_val_true_eq in eq1; auto.
  destruct(V_OSTCBNext vl) eqn : eq2; tryfalse.
  rewrite app_nil_l in H1.
  false.
  eapply tcblist_get_distinct_tcbdllseg_next_ptr_vnull_false; eauto.

  rewrite <- app_comm_cons in H.
  unfold tcblist_get in H; fold tcblist_get in H.
  destruct (beq_val (Vptr tid) head) eqn : eq1.
  inverts H.
  rewrite <- app_comm_cons in H1. 

  false.
  eapply distinct_tcbdllseg_next_ptr_vnull_dup_node_false; eauto.
  destruct (V_OSTCBNext a) eqn : eq2; tryfalse.
  eapply IHvltcb1; eauto.
  unfold get_last_tcb_ptr in *; fold get_last_tcb_ptr in *.
  destruct vltcb1.
  simpl in H0.
  rewrite eq2 in H0; inverts H0; auto.
  auto.
  eapply distinct_tcbdllseg_next_ptr_vnull_tail; eauto.
Qed.

Lemma ptr_in_tcbdllseg1_preserv :
  forall vltcb1 vl vl' vltcb2 head p,
    ptr_in_tcbdllseg1 p head (vltcb1 ++ vl :: vltcb2) ->
    same_prev_next vl vl' ->
    ptr_in_tcbdllseg1 p head (vltcb1 ++ vl' :: vltcb2).
Proof.
  inductions vltcb1; intros.
  rewrite app_nil_l in *.
  unfold ptr_in_tcbdllseg1 in *; fold ptr_in_tcbdllseg1 in *.
  destruct (beq_val p head) eqn : eq1; auto.
  unfolds in H0.
  destruct (V_OSTCBNext vl); tryfalse.
  destruct (V_OSTCBNext vl'); tryfalse.
  simpljoin; auto.
  rewrite <- app_comm_cons in *.
  unfold ptr_in_tcbdllseg1 in *; fold ptr_in_tcbdllseg1 in *.
  destruct (beq_val p head) eqn : eq1; auto.
  destruct (V_OSTCBNext a); tryfalse.
  eapply IHvltcb1; eauto.
Qed.

Lemma tcbls_rtbl_timetci_update_not_nil :
  forall a a0 a' rtbl b c d rtbl' b' c',
    tcbls_rtbl_timetci_update (a::a0) rtbl (Vint32 b) c d =
    Some (a', rtbl', b', c') ->
    a' <> nil.
Proof.
  intros.
  simpl in H.
  xunfold H.
  auto.
  auto.
  auto.
  auto.
Qed.

Lemma distinct_tcbdllseg_next_ptr_preserve :
  forall vltcb1 vltcb2 vl vl' head,
    distinct_tcbdllseg_next_ptr_vnull head (vltcb1++vl::vltcb2) ->
    same_prev_next vl vl' ->
    distinct_tcbdllseg_next_ptr_vnull head (vltcb1++vl'::vltcb2).
Proof.
  inductions vltcb1; intros.
  rewrite app_nil_l in *.
  unfold distinct_tcbdllseg_next_ptr_vnull in *; fold distinct_tcbdllseg_next_ptr_vnull in *.
  destruct H.
  destruct H1.
  unfold distinct_tcbdllseg_next_ptr in *; fold distinct_tcbdllseg_next_ptr in *.
  unfold get_last_tcb_ptr in *; fold get_last_tcb_ptr in *.
  split.
  destruct vltcb2; auto.
  unfolds in H0.
  destruct (V_OSTCBNext vl) eqn : eq1; tryfalse.
  destruct (V_OSTCBNext vl'); tryfalse.
  destruct H0; substs.
  auto.
  split.
  destruct vltcb2.
  simpl in *.
  unfolds in H0.
  rewrite H1 in H0.
  destruct (V_OSTCBNext vl'); tryfalse.
  destruct H0; substs; auto.
  unfold last in *; fold last in *.
  auto.
  unfold vptr_next in *; fold vptr_next in *.
  destruct H2.
  exists x.
  destruct H2.
  split; auto.
  unfolds in H0.
  destruct (V_OSTCBNext vl); tryfalse.
  destruct (V_OSTCBNext vl'); tryfalse.
  destruct H0; substs; auto.

  rewrite <- app_comm_cons in H.
  rewrite <- app_comm_cons.
  unfold distinct_tcbdllseg_next_ptr_vnull in *.
  destruct H.
  unfold distinct_tcbdllseg_next_ptr in *; fold distinct_tcbdllseg_next_ptr in *.
  pose proof app_cons_not_nil vltcb1 vl vltcb2.
  pose proof app_cons_not_nil vltcb1 vl' vltcb2.
  simpljoin.
  rewrite H3.
  rewrite H2 in H.
  destruct (V_OSTCBNext a) eqn: eq1; tryfalse.
  rewrite H2 in H1.
  unfold get_last_tcb_ptr in H1.
  pose proof IHvltcb1 vltcb2 vl vl' v.
  assert(
      distinct_tcbdllseg_next_ptr v (vltcb1 ++ vl :: vltcb2) /\
      get_last_tcb_ptr (vltcb1 ++ vl :: vltcb2) v = Some Vnull /\
      vptr_next v (vltcb1 ++ vl :: vltcb2)
    ).
  rewrite H2.
  destruct H.
  split; auto.
  split; auto.
  rewrite H2 in H4. 
  unfold vptr_next in H4; fold vptr_next in H4.
  destruct H4.
  destruct H4.
  destruct(V_OSTCBNext a); tryfalse.
  unfold vptr_next; fold vptr_next.
  inverts eq1.
  destruct H7.
  eauto.
  
  apply H5 in H6; auto; clear H5.
  rewrite H3 in H6.
  destruct H6.
  destruct H6.
  split.
  split; auto.
  rewrite <- H3 in *.
  rewrite <- H2 in *.
  destruct H.
  clear - H H0.
  intro.
  apply H.

  eapply ptr_in_tcbdllseg1_preserv; eauto.
  eapply same_prev_next_sym; auto.
  split; auto.
  unfold vptr_next in *; fold vptr_next in *.
  rewrite eq1.
  destruct H4.
  destruct H4.
  exists x3.
  split; auto.
Qed.

Lemma get_lasr_tcb_ptr_tick_hold:
  forall a b c d a' b' c' rtbl rtbl' head x,
    tcbls_rtbl_timetci_update a rtbl 
                              (Vint32 b) c d =
    Some (a', rtbl',  b', c') ->
    get_last_tcb_ptr a (Vptr head) = Some (Vptr x) ->
    get_last_tcb_ptr a' (Vptr head) = Some (Vptr x).
Proof.
  induction a;intros.
  simpl in H.
  inverts H.
  simpl in H0;simpl;inverts H0;auto.

  simpl in H.
  xunfold H.

  symmetry in Htick.
  destruct a0.
  simpl.
  simpl in Htick; inverts Htick.
  auto.
  assert (get_last_tcb_ptr (v3 :: a0) (Vptr head) = Some (Vptr x)).
  clear - H0.
  simpl in *; auto.
  lets Hx: IHa Htick H.
  assert (exists h t, l = h::t).
  eapply tcbls_rtbl_timetci_update_not_nil in Htick.
  destruct l; tryfalse.
  do 2 eexists; eauto.
  simpljoin1.
  simpl in Hx.
  simpl; auto.

  symmetry in Htick.
  destruct a0.
  simpl.
  simpl in Htick; inverts Htick.
  unfolds in H0; simpl in H0; inverts H0.
  unfolds; simpl; auto.
  assert (get_last_tcb_ptr (v1 :: a0) (Vptr head) = Some (Vptr x)).
  clear - H0.
  simpl in *; auto.
  lets Hx: IHa Htick H.
  assert (exists h t, l0 = h::t).
  eapply tcbls_rtbl_timetci_update_not_nil in Htick.
  destruct l0; tryfalse.
  do 2 eexists; eauto.
  simpljoin1.
  simpl in Hx.
  simpl; auto.

  symmetry in Htick.
  destruct a0.
  simpl.
  simpl in Htick; inverts Htick.
  unfolds in H0; simpl in H0; inverts H0.
  unfolds; simpl; auto.
  assert (get_last_tcb_ptr (v1 :: a0) (Vptr head) = Some (Vptr x)).
  clear - H0.
  simpl in *; auto.
  lets Hx: IHa Htick H.
  assert (exists h t, l1 = h::t).
  eapply tcbls_rtbl_timetci_update_not_nil in Htick.
  destruct l1; tryfalse.
  do 2 eexists; eauto.
  simpljoin1.
  simpl in Hx.
  simpl; auto.

  symmetry in Htick.
  destruct a0.
  simpl.
  simpl in Htick; inverts Htick.
  unfolds in H0; simpl in H0; inverts H0.
  unfolds; simpl; auto.
  assert (get_last_tcb_ptr (v3 :: a0) (Vptr head) = Some (Vptr x)).
  clear - H0.
  simpl in *; auto.
  lets Hx: IHa Htick H.
  assert (exists h t, l = h::t).
  eapply tcbls_rtbl_timetci_update_not_nil in Htick.
  destruct l; tryfalse.
  do 2 eexists; eauto.
  simpljoin1.
  simpl in Hx.
  simpl; auto.
Qed.
