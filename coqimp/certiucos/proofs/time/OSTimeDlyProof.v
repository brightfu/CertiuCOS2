(**************************  uc/OS-II  ******************************)
(*************************** OS_TIME.C ******************************)
(******Proofs for API Fucntion:  void* OSTimeDly(INT16U ticks)*******)
(************************C Source Code:******************************)
(* 
void  OSTimeDly (INT16U ticks)
{
1  if (ticks > 0)
   {
2    OS_ENTER_CRITICAL();
3    if(OSTCBCur -> OSTCBPrio == OS_PRIO_IDLE)
     {
4      OS_EXIT_CRITICAL;
5      reutrn;
     }
6    if (OSTCBCur->OSTCBStat == OS_STAT_RDY && OSTCBCur -> OSTCBDly == 0)
     {
7      if ((OSRdyTbl[OSTCBCur->OSTCBY] &= ~OSTCBCur->OSTCBBitX) == 0)
       {
8        OSRdyGrp &= ~OSTCBCur->OSTCBBitY;
       }
9      OSTCBCur->OSTCBDly = ticks;
10       OS_EXIT_CRITICAL();
11      OS_Sched();
     }
12   else 
13     OS_EXIT_CRITICAL();
   }
14 return;
}
*)
(*********************************************************************)

Require Import ucos_include.
Require Import OSTimeDlyPure.
Require Import time_absop_rules.

Open Scope code_scope.
(* OSTimeDelay Proof *)
Open Scope int_scope.

Lemma val_inj_ltu_true:
forall i,
val_inj
         (if Int.ltu ($ 0) i
          then Some (Vint32 Int.one)
          else Some (Vint32 Int.zero)) <> Vint32 Int.zero ->
Int.ltu ($ 0) i = true.
Proof.
  intros.
  remember (Int.ltu ($ 0) i) as Hi.
  destruct Hi; auto.
Qed.


Lemma val_inj_ltu_false:
  forall i,val_inj
             (if Int.ltu ($ 0) i
              then Some (Vint32 Int.one)
              else Some (Vint32 Int.zero)) = Vint32 Int.zero \/
           val_inj
             (if Int.ltu ($ 0) i
              then Some (Vint32 Int.one)
              else Some (Vint32 Int.zero)) = Vnull ->
           i = Int.zero.
Proof.
  intros.
  destruct H;
    match goal with
      | H : context [if ?x then _ else _ ] |- _ =>
        let y := fresh in  remember x as y ; destruct y; simpl in H; tryfalse
    end.
  apply ltu_zero_eq_zero;eauto.
  int auto.
Qed.
(*
Ltac solve_if_neq :=
  match goal with
  |  |- context[if ?c then _ else _] =>   
     try solve 
         [ let x := fresh in
           (destruct c; simpl; introv x; tryfalse) |
           apply true_if_else_true;
             apply Zle_is_le_bool;
             try rewrite byte_max_unsigned_val; 
             try rewrite max_unsigned_val; 
             try omega; auto
         ]

  end.

Ltac pure_auto := first [ do 2 solve_if_neq | go | pauto'].
*)

Lemma OSTimeDlyProof :
  forall vl p r tid ,
    Some p = BuildPreA' os_api OSTimeDly dlyapi vl OSLInv tid init_lg ->
    Some r = BuildRetA' os_api OSTimeDly dlyapi vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api OSTimeDly = Some (t, d1, d2, s) /\
      {| OS_spec, GetHPrio, OSLInv, I, r, Afalse |} |-tid {{ p }} s {{ Afalse }}.
Proof.
  init_spec.
  
(* if----------------------L1*)
  hoare forward; pure_auto.
  Focus 2.
  instantiate (1 := <||END None||>  **
                           LV ticks @ Int16u |-> Vint32 i **
                           Aie true **
                           Ais nil **
                           Acs nil ** Aisr empisr ** A_dom_lenv ((ticks, Int16u) :: nil) ** p_local OSLInv tid init_lg).

  hoare forward.
  hoare forward.
  
  hoare unfold pre.
  hoare abscsq.
  apply noabs_oslinv.
  eapply  OSTimeDly_high_level_step_1.
  eapply val_inj_ltu_false; auto.
  pure_auto.
  hoare forward.
  (* en_crit---------------L2*)
  pure intro.
  assert (Int.ltu ($ 0) i = true).
  remember (Int.ltu ($ 0) i) as X.
  destruct X;unfolds in H;simpl in H;tryfalse;auto.
  clear H H0 H2.
  hoare forward prim.
  hoare unfold.
  (* if idle ---------------L3*)
  hoare forward.
  pure_auto.
  pure_auto.
  pure intro.
  instantiate (1:=Afalse).
  (*------------------------L4*)
  assert (Int.eq i4 ($ OS_IDLE_PRIO) =true).
  destruct (Int.eq i4 ($ OS_IDLE_PRIO));unfolds in H4;simpl in H4;tryfalse;auto.
  clear H4 H5 H12.
  unfold1 TCBList_P in H10;simpljoin.
  unfold TCBNode_P in *.
  destruct x2.
  destruct p.
  simpljoin.
  unfold V_OSTCBNext, V_OSTCBMsg, V_OSTCBPrio in *.
  unfold TcbJoin in *.
  assert (TcbMod.get v'21 x = Some (p, t, m)).
  lets H100 : TcbMod.get_sig_some x (p, t, m).
  eapply TcbMod.join_get_get_l; eauto.
  assert (TcbMod.get v'13 x = Some (p, t, m)).
  eapply TcbMod.join_get_get_r; eauto.
  unfolds in H25.
  inverts H25.
  lets Hx: Int.eq_spec p ($ OS_IDLE_PRIO).
  rewrite H23 in Hx.
  subst p.
  inverts H4.
  hoare abscsq.
  apply noabs_oslinv.
  eapply OSTimeDly_high_level_step_4;eauto.
  pure_auto.

  hoare forward prim.
  unfold AOSTCBList.
  sep pauto;eauto.
  sep cancel tcbdllflag.
  unfold tcbdllseg.
  unfold dllseg at 2;fold dllseg.
  sep pauto.
  unfold node.
  sep pauto.
  splits; pauto.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  simpl;auto.
  do 4 eexists;splits;eauto.
  unfolds.
  splits;eauto.
  simpl;auto.
  (* return----------------------L5*)
  hoare forward.
  
  (* if rdy ---------------L6*)
  hoare forward.
  pure intro.
  assert (Int.eq i4 ($ OS_IDLE_PRIO) = false) as Hnidle.
  clear -H4.
  destruct (Int.eq i4 ($ OS_IDLE_PRIO));auto;destruct H4;simpl in H;tryfalse.
  clear H4.
  hoare forward;pure_auto.
  pure intro.
  (*-----------------------L4*)
  assert (Int.eq i5 ($ OS_STAT_RDY) =true).
  destruct (Int.eq i5 ($ OS_STAT_RDY));destruct (Int.eq i6 ($ 0));unfolds in H4;simpl in H4;tryfalse;auto.
  assert (Int.eq i6  ($ 0) = true) as Hdly0.
  destruct (Int.eq i5 ($ OS_STAT_RDY));destruct (Int.eq i6 ($ 0));unfolds in H4;simpl in H4;tryfalse;auto.
  clear H4 H5 H12.
  hoare unfold.
  assert (TCBList_P (Vptr (v'23, Int.zero))
                    ((v'22
                        :: v'18
                        :: x7
                        :: x6
                        :: Vint32 i6
                        :: Vint32 i5
                        :: Vint32 i4
                        :: Vint32 i3
                        :: Vint32 i2
                        :: Vint32 i1 :: Vint32 i0 :: nil) :: v'9)
                    v'10 v'21) as Htcblistp.
  auto.
  unfold1 TCBList_P in H10; simpljoin.
  unfold TCBNode_P in *.
  rename e into H10.
  rename e0 into H25.
  rename j into  H26.
  rename t into H27.
  rename t0 into H28.
  destruct x2.
  destruct p.
  simpljoin.
  unfold V_OSTCBNext, V_OSTCBMsg, V_OSTCBPrio in *.
  unfold TcbJoin in *.
  assert (TcbMod.get v'21 x = Some (p, t, m)).
  lets H100 : TcbMod.get_sig_some x (p, t, m).
  eapply TcbMod.join_get_get_l; eauto.
  assert (TcbMod.get v'13 x = Some (p, t, m)).
  eapply TcbMod.join_get_get_r; eauto.
  assert ((Int.unsigned i2 < 8)%Z).
  unfold RL_TCBblk_P in r; simpljoin.
  unfold V_OSTCBY in H34; simpl in H34; inverts H34.
  pauto.
  assert (length v'10 = 8%nat).
  pauto.
  assert (exists i4,
            nth_val' (Z.to_nat (Int.unsigned i2)) v'10 = Vint32 i4 /\
            Int.unsigned i4 <= 255)%Z.
  apply array_int8u_nth_lt_len; auto.
  rewrite H31.
  clear - H30.
  apply Nat2Z.inj_lt.
  rewrite Z2Nat.id; int auto.
  simpljoin.
  hoare forward.
  pure_auto.
  rewrite H32; simpl; pure_auto.
  pure_auto.
(*  pure_auto. *)
  rewrite H32; simpl; pure_auto.
  pure_auto.

  (* if -----------------------L5*)
  
  hoare unfold.
  hoare forward.
  pure_auto.
  rewrite H32; simpl val_inj.
  rewrite update_nth_val_len_eq.
  rewrite H31.
  simpl; auto.
  
  rewrite H32; simpl val_inj.
  rewrite len_lt_update_get_eq.
  simpl.
  cut (Int.unsigned (Int.and x2 (Int.not i1)) <=? Byte.max_unsigned = true)%Z.
  intros H100; rewrite H100; auto.
  apply leb_bytemax_true_intro.
  apply int_lemma1; auto.
  rewrite H31; simpl; auto.

  rewrite H32; simpl val_inj.
  rewrite len_lt_update_get_eq.
  simpl.
  pure_auto.
  rewrite H31; simpl; auto.
  unfold AOSRdyGrp.
  hoare_assign.
  pure_auto.
  pure_auto.
  rule_type_val_match_elim; simpl; auto.
  pure_auto.

  hoare forward.
  lets Hst: low_stat_rdy_imp_high r H23 Hdly0;eauto.
  subst.
  hoare forward.
  pure_auto.
  hoare abscsq.
  apply noabs_oslinv.
  eapply OSTimeDly_high_level_step_2; eauto.
  pure_auto.
  unfold AECBList in *.
  instantiate (1 := <||END None||> ** Aie true **
                       Ais nil **
                       Acs nil **
                       Aisr empisr ** p_local OSLInv (v'23, Int.zero) init_lg ** LV ticks @ Int16u |-> Vint32 i ** A_dom_lenv ((ticks, Int16u) :: nil)).
  hoare forward prim.
  unfold AECBList in *.
  instantiate (1 := LV ticks @ Int16u |-> Vint32 i ** A_dom_lenv ((ticks, Int16u) :: nil)).
  sep semiauto.
  sep cancel evsllseg.
  sep cancel Astruct.
  sep cancel dllseg.
  sep cancel dllseg.
  sep lift 3%nat in H10.
  sep lift 3%nat.
  eapply tcbdllflag_hold;eauto.
  apply tcbdllflag_hold_middle.
  simpl;auto.
  rule_type_val_match_elim; simpl val_inj.
  rewrite H32; simpl val_inj.
  split.
  eapply event_wait_rl_tbl_grp';eauto.
  rewrite len_lt_update_get_eq in H36.
  rewrite H32 in H36.
  simpl in H36.
  destruct (Int.eq (x2&ᵢInt.not i1) ($ 0));simpl in H36;tryfalse;auto.
  rewrite H31.
  unfolds OS_RDY_TBL_SIZE.
  simpl Z.of_nat.
  auto.
  eapply idle_in_rtbl_hold;eauto.
  
  rule_type_val_match_elim; simpl; auto.
  cut (Int.unsigned (i4&ᵢInt.not i0) <=? Byte.max_unsigned = true)%Z.
  intros H100;rewrite H100; auto.
  apply leb_bytemax_true_intro.
  apply int_lemma1; auto.

  split.
  apply array_type_vallist_match_hold; auto.
  rewrite H31; simpl; auto.
  apply Nat2Z.inj_lt.
  clear - H30.
  rewrite Z2Nat.id; int auto.

  rewrite H32; simpl.
  cut (Int.unsigned (x2&ᵢInt.not i1) <=? Byte.max_unsigned = true)%Z.
  intros H100; rewrite H100; auto.
  apply leb_bytemax_true_intro.
  apply int_lemma1; auto.

  rewrite update_nth_val_len_eq.
  simpl; auto.

  eapply R_PrioTbl_P_hold1; eauto.

  rewrite H32.
  simpl.
  
  eapply rtbl_remove_RL_RTbl_PrioTbl_P_hold with (prio:= p) ;eauto;
  (funfold r; try rewrite Int.repr_unsigned; auto).

  apply nth_val'_imp_nth_val_int;auto.
  
  eapply ECBList_P_hold1;eauto.
  instantiate (1 := (TcbMod.set v'21 (v'23, Int.zero)
                                (p, wait os_stat_time  i, m))).
  rewrite H32; simpl val_inj.
  
  3:apply TcbMod.join_set_r; eauto;unfold TcbMod.indom;eauto.

  eapply TCBList_P_tcb_dly_hold;eauto.
  
  eapply TcbMod_join_impl_prio_neq_cur_r;eauto.

  eapply R_PrioTbl_P_impl_prio_neq_cur; eauto.
  funfold r; auto.
  apply nth_val'_imp_nth_val_int;auto.
  rewrite H32; simpl val_inj.
  eapply TCBList_P_tcb_dly_hold';eauto; (funfold r; try rewrite Int.repr_unsigned; auto).
  eapply TcbMod_join_impl_prio_neq_cur_l;eauto.
  eapply R_PrioTbl_P_impl_prio_neq_cur; eauto.
  apply nth_val'_imp_nth_val_int;auto.
  unfolds; simpl; auto.
  unfolds; simpl; auto.
  split; auto.
  pure_auto.
  eapply RH_CurTCB_hold1; eauto.
  eapply RH_TCBList_ECBList_P_hold1; eauto.
  simpl; auto.


  (**hoare forward**)

  hoare forward.
  instantiate (1:=  LV ticks @ Int16u |-> Vint32 i **
                       A_dom_lenv ((ticks, Int16u) :: nil)).
  sep auto.
  eauto.
  unfolds;simpl;auto.
  simpl;auto.
  sep auto.
  sep cancel p_local.
  simpl; auto.
  sep auto.
  sep cancel p_local.
  simpl; auto.
  unfold getasrt in H10.
  unfold OS_SchedPost  in H10.
  unfold OS_SchedPost' in H10.
  sep auto.
  inverts H25; auto.

  (* if false  *)
  lets Hst: low_stat_rdy_imp_high r r0 Hdly0;eauto.
  subst.
  hoare forward.
  pauto.
  hoare abscsq.
  apply noabs_oslinv.
  eapply OSTimeDly_high_level_step_2;eauto.
  can_change_aop_solver.
  unfold AECBList in *.
  hoare forward prim.
  unfold AECBList in *.
  instantiate (1 := LV ticks @ Int16u |-> Vint32 i ** A_dom_lenv ((ticks, Int16u) :: nil)).
  sep semiauto.
  sep cancel evsllseg.
  sep cancel Astruct.
  sep cancel dllseg.
  sep cancel dllseg.
  sep lift 3%nat in H10.
  sep lift 3%nat.
  
  eapply tcbdllflag_hold;eauto.
  apply tcbdllflag_hold_middle.
  simpl;auto.
  rule_type_val_match_elim; simpl val_inj.
  rewrite H32; simpl val_inj.
  split.
  eapply event_wait_rl_tbl_grp'';eauto.
  rewrite H32 in H34.
  rewrite len_lt_update_get_eq in H34.
  clear -H34.
  unfold val_inj in H34.
  simpl in H34.
  destruct ( Int.eq (x2&ᵢInt.not i1) ($ 0));tryfalse;auto.
  destruct H34;tryfalse.
  rewrite H31.
  simpl Z.of_nat.
  auto.
  eapply idle_in_rtbl_hold;eauto.
  
  split.
  apply array_type_vallist_match_hold; auto.
  rewrite H31; simpl; auto.
  apply Nat2Z.inj_lt.
  clear -H30.
  rewrite Z2Nat.id; int auto.

  rewrite H32; simpl.
  cut (Int.unsigned (x2&ᵢInt.not i1) <=? Byte.max_unsigned = true)%Z.
  intros H100; rewrite H100; auto.
  apply leb_bytemax_true_intro.
  apply int_lemma1; auto.

  rewrite update_nth_val_len_eq.
  simpl; auto.
  
  eapply R_PrioTbl_P_hold1; eauto.

  rewrite H32.
  simpl.
  eapply rtbl_remove_RL_RTbl_PrioTbl_P_hold with (prio:= p) ;eauto;
  (funfold r; try rewrite Int.repr_unsigned; auto).
  apply nth_val'_imp_nth_val_int;auto.
  eapply ECBList_P_hold1;eauto.
  instantiate (1 := (TcbMod.set v'21 (v'23, Int.zero)
                                (p, wait os_stat_time i, m))).
  rewrite H32; simpl val_inj.
  
  3:apply TcbMod.join_set_r; eauto;unfold TcbMod.indom;eauto.
  eapply TCBList_P_tcb_dly_hold;eauto.
  eapply TcbMod_join_impl_prio_neq_cur_r;eauto.

  eapply R_PrioTbl_P_impl_prio_neq_cur; eauto.
  funfold r; auto.
  apply nth_val'_imp_nth_val_int;auto.
  rewrite H32; simpl val_inj.
  eapply TCBList_P_tcb_dly_hold';eauto;   
  (funfold r; try rewrite Int.repr_unsigned; auto).
  eapply TcbMod_join_impl_prio_neq_cur_l;eauto.
  eapply R_PrioTbl_P_impl_prio_neq_cur; eauto.
  apply nth_val'_imp_nth_val_int;auto.
  unfolds; simpl; auto.

  unfolds; simpl; auto.

  split; auto.
  pauto.
  eapply RH_CurTCB_hold1; eauto.
  eapply RH_TCBList_ECBList_P_hold1; eauto.
  simpl; auto.

  (*hoare forward*)
  hoare forward.

  instantiate (1:=  LV ticks @ Int16u |-> Vint32 i **
           A_dom_lenv ((ticks, Int16u) :: nil)).
  sep auto.
  eauto.
  unfolds;simpl;auto.
  simpl;auto.
  sep auto.
  inverts H25.
  sep cancel 1%nat 1%nat.
  simpl ; auto.
  unfold getasrt.
  unfold OS_SchedPre.
  unfold OS_SchedPre'.
  sep auto.
  sep cancel 1%nat 1%nat.
  simpl; auto.
   unfold getasrt in H10.
  unfold OS_SchedPost in H10.
  unfold OS_SchedPost' in H10.
  sep auto.
  inverts H25; auto.

  pure intro.
  assert (Int.eq i5 ($ OS_STAT_RDY)=false \/ Int.eq i6 ($ 0) = false).
  clear -H4.
  unfold val_inj in H4;destruct (Int.eq i5 ($ OS_STAT_RDY));destruct (Int.eq i6 ($ 0));simpl in H4;tryfalse;auto.
  assert (Int.ltu Int.zero Int.one && Int.ltu Int.zero Int.one = true).
  unfolds.
  
  assert ( Int.ltu Int.zero Int.one = true).
  clear;int auto.
  rewrite H.
  auto.
  rewrite H in H4.
  destruct H4;tryfalse.

  assert (TCBList_P (Vptr (v'23, Int.zero))
                    ((v'22
                        :: v'18
                        :: x7
                        :: x6
                        :: Vint32 i6
                        :: Vint32 i5
                        :: Vint32 i4
                        :: Vint32 i3
                        :: Vint32 i2
                        :: Vint32 i1 :: Vint32 i0 :: nil) :: v'9)
                    v'10 v'21) as X.
  auto.
  unfold1 TCBList_P in H10.
  simpljoin.
  unfold TCBNode_P in *.
  destruct x2.
  destruct p.
  simpljoin.
  lets Hx: low_stat_nordy_imp_high r0 H5.
  
  unfolds in j.
  assert (TcbMod.get v'21 x = Some (p, t1, m)).
  lets H100 : TcbMod.get_sig_some x (p, t1, m).
  eapply TcbMod.join_get_get_l; eauto.
  assert (TcbMod.get v'13 x = Some (p, t1, m)).
  eapply TcbMod.join_get_get_r; eauto.

  hoare abscsq.
  apply noabs_oslinv.
  eapply OSTimeDly_high_level_step_3;eauto.
  inverts e.
  eauto.
  can_change_aop_solver.
  instantiate (1:= <|| END None ||>  ** p_local OSLInv (v'23, Int.zero) init_lg **
                           Aisr empisr **
                           Aie true **
                           Ais nil **
                           Acs nil **
                           LV ticks @ Int16u |-> Vint32 i ** A_dom_lenv ((ticks, Int16u) :: nil)).
  hoare forward prim.

  unfold AOSTCBList.
  sep pauto;eauto.
  unfold tcbdllseg.
  unfold dllseg at 2;fold dllseg.
  sep pauto.
  unfold node.
  sep pauto.
  splits; pure_auto.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  simpl;auto.
  destruct H4.
  sep auto.
  sep auto.
Qed.


































































