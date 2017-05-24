(**************************  uc/OS-II  ****************************)
(*************************** OS_CORE.C *******************************)
(*********Proof of Internal Fucntion:  void OS_Sched (void)***********)
(************************ Code:****************************)
(*** 
void  OS_Sched (void)
{
    INT8U      y;
1   OS_ENTER_CRITICAL();
2   y = OSUnMapTbl[OSRdyGrp];
3   OSPrioHighRdy = (INT8U)((y << 3) + OSUnMapTbl[OSRdyTbl[y]]);
4    OSPrioCur ′ =ₑ OSTCBCur ′ → OSTCBPrio;ₛ
5   if (OSPrioHighRdy != OSPrioCur)
    {                                              
6      OSTCBHighRdy = OSTCBPrioTbl[OSPrioHighRdy];
7      OSCtxSwCtr++;                               
8      OSCtxSw();                                  
    }
9      OS_EXIT_CRITICAL();
}
***)

Require Import ucos_include.
Require Import absop_rules.
Require Import symbolic_lemmas.
Require Import os_ucos_h.
Require Import oscore_common.
Open Scope code_scope.


Import DeprecatedTactic.

Lemma OSSched_proof:
    forall vl p r logicl ct, 
      Some p =
      BuildPreI os_internal OS_Sched
                  vl logicl OS_SchedPre ct->
      Some r =
      BuildRetI os_internal OS_Sched vl logicl OS_SchedPost ct->
      exists t d1 d2 s,
        os_internal OS_Sched = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init spec.
  hoare_split_pure_all.
  subst.
  (*----------------en_crit---------------------*)
  unfolds in  H0.
  destruct H0;subst.
  hoare forward prim.
  (*---------------get y------------------------*)

  hoare unfold.
  unfold AOSUnMapTbl.
  hoare forward;pauto.
  lets Hx:osunmapvallist_prop H1.
  mytac.
  rewrite H5.
  simpl.
  rtmatch_solve.
  apply Zle_bool_imp_le in H6;omega.
  
  (*--------------get highest prio--------------*)
  unfold AGVars.
  unfold AOSRdyTbl.

  lets Hiprop: osunmapvallist_prop H1.
  mytac.
  rewrite H4.
  assert (Int.unsigned x <=? Byte.max_unsigned  =true).
  rewrite byte_max_unsigned_val.
  assert (Int.unsigned x <=? 255 =true).
  apply Zle_bool_imp_le in H5.
  apply Zle_is_le_bool.
  omega.
  auto.
  pure intro.
  
  lets Hxprop: array_type_vallist_match_imp_rule_type_val_match H9.
  rewrite H10.
  apply Zle_bool_imp_le in H5.
  instantiate (1:= Z.to_nat (Int.unsigned x)).
  unfold OS_RDY_TBL_SIZE.
  apply  Z2Nat.inj_lt.
  apply Int.unsigned_range.
  omega.
  omega.
  unfolds in Hxprop.
  remember (nth_val' (Z.to_nat (Int.unsigned x)) v'12) as X.
  destruct X;tryfalse.

  hoare forward.
  rewrite H6.
  auto.
  rewrite H6.
  auto.

  assert (Int.unsigned x <= 7).
  apply Zle_bool_imp_le;auto.
  omega.

 
  sep lift 2%nat in H11.
  unfold OS_RDY_TBL_SIZE in H10.
  eapply GAarray_imp_length_P in H11.
  rewrite H11.
  simpl.
  apply Zle_bool_imp_le in H5.
  omega.
  rewrite <- HeqX.
  simpl;auto.
  eauto.
  remember (Int.unsigned i0 <=? Byte.max_unsigned) as Y.
  destruct Y;tryfalse.
  symmetry in HeqY.
  rewrite  byte_max_unsigned_val in HeqY.
  apply Zle_bool_imp_le in HeqY.
  omega.
  remember (Int.unsigned i0 <=? Byte.max_unsigned) as Y.
  destruct Y;tryfalse.
  symmetry in HeqY.
  rewrite  byte_max_unsigned_val in HeqY.
  apply Zle_bool_imp_le in HeqY.
  omega.
  assert ((Int.unsigned i0 <=? 255) = true) as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255));tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H12.
  simpl;auto.
  rtmatch_solve.
  apply Zle_bool_imp_le in H13;omega.

  rewrite int_iwordsize_gt_3.
  simpl.
  assert ((Int.unsigned i0 <=? 255) = true) as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255));tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H12.
  simpl;auto.
  (* get current task prio *)

  hoare unfold.
  hoare forward.
  go.
  
  (*----check if current task is highest ready----*)
  rewrite int_iwordsize_gt_3.
  simpl add.
  assert ((Int.unsigned i0 <=? 255) = true) as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255));tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H12.
  unfold AOSTCBPrioTbl.
  lets Hran:shl3_add_range H5 H13.
  apply Zle_bool_imp_le in Hran.
  hoare forward.
  assert ( Int.unsigned ((x<<ᵢ$ 3)+ᵢ x0) <= Byte.max_unsigned ).
  rewrite byte_max_unsigned_val.
  omega.
  apply Zle_is_le_bool in H34.  
  rewrite H34;auto.
  assert ( Int.unsigned i5 <=? Byte.max_unsigned =true).
  rewrite byte_max_unsigned_val.
  apply Zle_is_le_bool.
  omega.
  rewrite H34;auto.
  destruct (Int.eq ((x<<ᵢ$ 3) +ᵢ x0) i5);auto.
  destruct (Int.eq ((x<<ᵢ$ 3) +ᵢ x0) i5);simpl;auto.
  hoare forward.
  assert ( Int.unsigned ((x<<ᵢ$ 3) +ᵢ x0) <= Byte.max_unsigned ).
  rewrite byte_max_unsigned_val.
  omega.
  apply Zle_is_le_bool in H35.  
  rewrite H35;auto.
  destruct H31;auto.

  eapply array_type_vallist_match_imp_rule_type_val_match;eauto.
  rewrite H35.

  assert (64%nat = Z.to_nat (63+1)).
  simpl;auto.
  rewrite H36.
  eapply int_unsigned_le_z2nat_lt.
  auto.
  
  hoare forward;eauto.
  pure intro.

  lets Hinrtbl:unmap_inrtbl H2 H1 H4 H12;auto.
  lets Hhastid:prio_in_rtbl_has_tid H31 Hinrtbl.
  rewrite Int.repr_unsigned.
  lets Hx:Int.unsigned_range ((x<<ᵢ$ 3)+ᵢx0).
  split;omega.
  destruct Hhastid.
  Require Import List.
  hoare lifts (1::14::2::nil)%nat pre.
  hoare remember (1::2::3::nil) pre.

 
  eapply abscsq_rule'.
  apply noabs_oslinv.
  unfold isched.
  
  instantiate (1:= <|| (ASSUME sc;; sched);; v'0 ||>  **
                       LV y @ Int8u |-> Vint32 x ** A_dom_lenv ((y, Int8u) :: nil) ** H38).
  apply absinfer_seq;auto.
  subst H38.
  go.
  subst H38.
  can_change_aop_solver.
  apply absinfer_choice1;auto.
  subst H38.
  can_change_aop_solver.
  subst H38.
  can_change_aop_solver.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  instantiate (1:= <|| (spec_done None;;sched);; v'0 ||>  **
                       LV y @ Int8u |-> Vint32 x ** A_dom_lenv ((y, Int8u) :: nil) ** H38).
  
  eapply sc_isched_step with (t:=x1) (ct:=(v'29, Int.zero));eauto.
  subst H38.
  can_change_aop_solver.
  split.

  eapply highest_rdy_eq;eauto.
  rewrite Int.repr_unsigned in H37;auto.

  instantiate (2:=  (v'29, Int.zero)).
  instantiate (2:= (v'28
              :: v'24
                 :: x8
                    :: x7
                       :: Vint32 i7
                          :: Vint32 i6
                             :: Vint32 i5
                                :: Vint32 i4
                                   :: Vint32 i3
                                      :: Vint32 i2 :: Vint32 i1 :: nil):: v'11).
  instantiate (2:=v'9).
  instantiate (2:=v'7).
  subst H38.
  unfold p_local in H39.
  unfold CurTid in H39.
  unfold LINV in H39.
  Set Printing Depth 99.
  unfold AOSTCBList.
  sep normal in H39.
  sep destruct H39.
  sep split in H39.
  sep lift 11%nat in H39.
  apply read_only_merge_vptr in H39.
  destruct H39.
  clear H45.
  sep normal.
  sep eexists.
  sep split.
  unfold tcbdllseg.
  sep cancel 10%nat 3%nat.
  sep cancel 9%nat 2%nat.
  apply read_only_split_vptr.
  sep cancel 1%nat 1%nat.
  sep cancel 24%nat 2%nat.
  unfold1 dllseg.
  unfold node.
  sep normal.
  sep eexists.
  sep split;eauto.
  sep cancel Astruct.
  sep cancel dllseg.
  exact H39.
  unfolds;simpl;auto.
  split;auto.
  go.
  eauto.
  eauto.
  auto.
  split;auto.
  subst H38.
  sep auto.

  eapply prio_neq_tid_neq with (s:=s) (p_ct:=i5);eauto.
  rewrite Int.repr_unsigned in H37;eauto.
  clear -H33.
  destruct (Int.eq ((x<<ᵢ$ 3)+ᵢx0) i5);simpl in H33;auto.
  unfold Int.notbool in H33.
  int auto.
  instantiate (2:=(v'29, Int.zero)).
  sep auto.
  eauto.
  eauto.
  eauto.
  split;auto.
  go.

  eapply abscsq_rule'.
   apply noabs_oslinv.
  instantiate (1:= <|| sched;; v'0 ||>  **
                       LV y @ Int8u |-> Vint32 x ** A_dom_lenv ((y, Int8u) :: nil) ** H38).
  apply absinfer_seq;auto.
  subst H38.
  can_change_aop_solver.
  subst H38.
  can_change_aop_solver.
  apply absinfer_seq_end;auto.
  subst H38.
  can_change_aop_solver.
  subst H38.
  can_change_aop_solver.
  
  apply backward_rule1 with ( <|| sched;; v'0 ||>  **
                                  (LV y @ Int8u |-> Vint32 x ** A_dom_lenv ((y, Int8u) :: nil)) ** H38).
  intros.
  sep normal.
  auto.
  subst H38.

  eapply frame_rule' with (frm:=  LV y @ Int8u |-> Vint32 x **  
                                     A_dom_lenv ((y, Int8u) :: nil) ).

  apply GoodI_I. (* GoodI *)
  simpl;auto.
  simpl;auto.
  intros;sep auto.
  eapply switch_rule'.
  instantiate (1:= LINV OSLInv (v'29, Int.zero) init_lg).
  intros.
  unfold p_local in H38.
  sep cancel OSLInv.
  exact H38.
  intros.
  unfold SWINVt.
  unfold CurTid in H38.
  sep normal in H38.
  sep destruct H38.
  
  sep normal.
  exists x2.
  sep cancel 1%nat 1%nat.
  unfold SWINV.
  sep normal.
  exists INUM.
  sep lifts (3::2::nil)%nat.
  eapply imp_isrclr.
  apply simpl_inv_excrit.

  unfold OSInv.
  unfold AGVars.
  unfold AOSTCBPrioTbl.
  sep semiauto;eauto.
  sep cancel 1%nat 1%nat.
  sep cancel AOSEventFreeList.
  sep cancel AOSQFreeList.
  sep cancel AOSQFreeBlk.
  sep cancel AECBList.
  sep cancel 6%nat 1%nat.
  unfold AOSTCBList'.
  apply disj_split.
  left.
  sep normal.
  sep eexists.
  unfold AOSTCBFreeList'.
  sep lift 12%nat.
  apply disj_split.
  left.
  unfold TCBFree_Not_Eq.
  unfold AOSTCBFreeList in H38.
  sep normal.
  sep cancel tcbdllflag.
  sep auto;eauto.
  unfold tcbdllseg.
  sep cancel sll.
  sep cancel sllfreeflag.
  unfold1 dllseg.
  unfold node.
  sep auto;eauto.
  split;auto.
  go.
  intro.
  subst.

  sep lifts (1::7::nil)%nat in H38.
  eapply Astruct_sll_OS_TCB_dup_false;eauto.
  intro;subst.
  sep lifts (1::7::nil)%nat in H38.
  eapply Astruct_sll_OS_TCB_dup_false;eauto.
  simpl;auto.
  rewrite Int.repr_unsigned in H37.
  eauto.
  destruct_s s.
  simpl in H42;subst i10.
  simpl.
  auto.
  simpl;auto.
  rewrite byte_max_unsigned_val.
  apply Zle_is_le_bool in H1.
  rewrite H1;auto.

  simpl in H18.
  clear -H18;mytac.
  unfolds in H2.
  destruct x2.
  destruct p.
  mytac.
  unfolds in H5.
  mytac.
  unfolds in H5;simpl in H5;inverts H5.
  clear -H20.
  int auto.
  
  intros.
  unfold SWPRE_NDEAD.
  split.
  unfold SWPRE.
  rewrite Int.repr_unsigned in H37.
  rewrite H37 in *.

  exists x1.

  sep lift 2%nat.
  apply imp_isrclr.

  sep remember (6::7::8::9::10::nil)%nat in H38.
  assert(s|=AOSTCBList v'7 (Vptr (v'29, Int.zero)) v'9 (  (v'28
              :: v'24
                 :: x8
                    :: x7
                       :: Vint32 i7
                          :: Vint32 i6
                             :: Vint32 i5
                                :: Vint32 i4
                                   :: Vint32 i3
                                      :: Vint32 i2 :: Vint32 i1 :: nil) :: v'11) v'12 (v'29, Int.zero) v'15 ** H39).
  unfold AOSTCBList.
  sep normal.
  clear HeqH39.
  sep semiauto;eauto.
  unfold tcbdllseg.
  simpl dllseg at 2.
  unfold node.
  sep auto.

  split;auto.
  go.
  clear H38.
  subst H39.
  
  sep cancel Aisr.
  sep normal.
  exists OS_TCB.
  exists OS_TCB.
  sep cancel 4%nat 2%nat.

  sep lifts (1::22::28::nil)%nat in H40.
  unfold CurTid in H40.
  eapply highest_rdy_eq in H40;eauto.
  unfold LINV.
  exists v'15.
  sep auto.
  unfolds in H0.
  unfold indom.
  mytac;eauto.
  
  simpl;auto.
  intros.
  sep cancel 1%nat 1%nat.
  simpl;auto.
  
  apply disj_rule.
  pure intro.
  
  apply backward_rule1 with (<|| v'0 ||>  ** OSInv ** atoy_inv' ** Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr ** LV y @ Int8u |-> Vint32 x  ** A_dom_lenv ((y, Int8u) :: nil) ** GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (v'29, Int.zero) **  LINV OSLInv (v'29, Int.zero) init_lg).
  intros.
  unfold SWINVt in H33.
  unfold SWINV in H33.
  sep normal in H33.
  sep destruct H33.

  sep lifts (2::9::nil)%nat in H33.  
  lets Hi:topis_nil H33.
  subst x1.
  sep lifts (8::4::nil)%nat in H33.
  apply isrclr_imp  in H33.
  apply simpl_inv_encrit in H33.

  clear -H33.

  sep lifts (4::7::2::3::10::5::11::1::nil)%nat in H33.  

  apply atopis_pure in H33.

  sep lifts (2::8::nil)%nat in H33.
  
  apply ostcbcur_tp_os_tcb in H33.
  sep lifts (2::10::nil)%nat.
  auto.
  hoare lifts (1::7::4::5::6::2::3::nil)%nat pre.
  eapply seq_rule.

  eapply excrit1_rule'_ISnil_ISRemp;eauto.
  go.
  unfold LINV.
  unfold OSLInv.
  go.
  intros.
  unfold p_local.
  unfold CurTid.
  sep auto.
  hoare forward.
  unfold p_local.
  unfold CurTid.
  sep auto.

  lets Hinrtbl:unmap_inrtbl H2 H1 H4 H12;auto.
  pure intro.
  lets Hhastid:prio_in_rtbl_has_tid H31 Hinrtbl.
  rewrite Int.repr_unsigned.
  lets Hx:Int.unsigned_range ((x<<ᵢ$ 3)+ᵢx0).
  split;omega.
  destruct Hhastid.
  hoare lifts (2::14::3::nil)%nat pre.
  hoare remember (1::2::3::nil) pre.

  eapply abscsq_rule'.
   apply noabs_oslinv.
  unfold isched.
  
  instantiate (1:= <|| ASSUME nsc;;v'0 ||>  **
                       LV y @ Int8u |-> Vint32 x ** A_dom_lenv ((y, Int8u) :: nil) ** H36).
  apply absinfer_seq;auto.
  subst H36;can_change_aop_solver.
  subst H36;can_change_aop_solver.
  
  apply absinfer_choice2;auto.
  subst H36;can_change_aop_solver.
  subst H36;can_change_aop_solver.

  eapply abscsq_rule'.
   apply noabs_oslinv.
  instantiate (1:= <|| spec_done None;;v'0 ||>  **
                       LV y @ Int8u |-> Vint32 x ** A_dom_lenv ((y, Int8u) :: nil) ** H36).

  eapply nsc_isched_step with (t:=x1) (ct:=(v'29, Int.zero));eauto.
  subst H36.
  can_change_aop_solver.
  split.
  eapply highest_rdy_eq;eauto.
  rewrite Int.repr_unsigned in H35;auto.

  instantiate (2:=  (v'29, Int.zero)).
  instantiate (2:= (v'28
              :: v'24
                 :: x8
                    :: x7
                       :: Vint32 i7
                          :: Vint32 i6
                             :: Vint32 i5
                                :: Vint32 i4
                                   :: Vint32 i3
                                      :: Vint32 i2 :: Vint32 i1 :: nil):: v'11).
  instantiate (2:=v'9).
  instantiate (2:=v'7).
  subst H36.
  unfold p_local in H37.

  unfold CurTid in H37.
  sep normal in H37.
  sep normal.
  sep destruct H37.
  exists x2.
  sep cancel 1%nat 1%nat.
  sep cancel 28%nat 2%nat.
  unfold AOSTCBList.
  unfold tcbdllseg.
  unfold1 dllseg.
  unfold node.
  sep auto.
  eauto.
  eauto.
  auto.
  split;auto.
  go.

  subst H36.
  sep auto.
  eapply prio_eq_tid_eq with (s:=s) (p_ct:=i5);eauto.
  rewrite Int.repr_unsigned in H35;eauto.
  clear -H33.
  destruct (Int.eq ((x<<ᵢ$ 3)+ᵢx0) i5);simpl in H33;destruct H33;auto;tryfalse.
  instantiate (2:=(v'29, Int.zero)).
  sep auto.
  eauto.
  eauto.
  auto.
  split;auto.
  go.

  eapply abscsq_rule'.
   apply noabs_oslinv.
  instantiate (1:= <||v'0 ||>  **
                       LV y @ Int8u |-> Vint32 x ** A_dom_lenv ((y, Int8u) :: nil) ** H36).
  apply absinfer_seq_end;auto.
  subst H36;can_change_aop_solver.
  subst H36;can_change_aop_solver.
  
  apply backward_rule1 with ( <|| v'0 ||>  ** OSInv ** atoy_inv' ** Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr ** LV y @ Int8u |-> Vint32 x  ** A_dom_lenv ((y, Int8u) :: nil) ** p_local OSLInv (v'29, Int.zero) init_lg ).
  intros.
  subst H36.
  sep remember (6::7::8::9::10::nil)%nat in H37.
  assert(s |= AOSTCBList v'7 (Vptr (v'29, Int.zero)) v'9 (  (v'28
              :: v'24
                 :: x8
                    :: x7
                       :: Vint32 i7
                          :: Vint32 i6
                             :: Vint32 i5
                                :: Vint32 i4
                                   :: Vint32 i3
                                      :: Vint32 i2 :: Vint32 i1 :: nil)  :: v'11) v'12 (v'29, Int.zero) v'15 ** H36).
  unfold AOSTCBList.
  sep normal.
  clear HeqH36.
  sep semiauto;eauto.
  unfold tcbdllseg.
  simpl dllseg at 2.
  unfold node.
  sep auto.
  split;auto.
  go.
  clear H37.
  subst H36.
  sep lifts (2::10::nil)%nat.
  apply inv_change.
  unfold OldOSInvWL.
  sep semiauto;eauto.
  sep cancel 2%nat 1 %nat.
  sep cancel AOSEventFreeList.
  sep cancel AOSQFreeList.
  sep cancel AOSQFreeBlk.
  sep cancel AOSTCBList.
  exact H38.  
  simpl;auto.
  simpl;auto.
  rewrite byte_max_unsigned_val.
  apply Zle_is_le_bool in H1.
  rewrite H1;auto.
  auto.

  simpl in H18.
  clear -H18;mytac.
  unfolds in H2.
  destruct x2.
  destruct p.
  mytac.
  unfolds in H5.
  mytac.
  unfolds in H5;simpl in H5;inverts H5.
  clear -H20.
  int auto.
  hoare lifts (1::7::4::5::6::2::3::nil)%nat pre.
  eapply seq_rule.
  eapply excrit1_rule'_ISnil_ISRemp;eauto.
  unfold p_local.
  unfold CurTid.
  unfold LINV.
  unfold OSLInv.
  go.
  intros;sep auto.
  hoare forward.

  (***************************** self deleted case *****************************)
  hoare forward prim.
  hoare unfold.
  unfold AOSTCBList'.
  hoare lift 9%nat pre.
  eapply backward_rule1.
  intros.
  apply disj_split in H3.
  eauto.
  apply disj_rule.
  unfold p_local.
  unfold CurTid.
  pure intro.
  eapply backward_rule1.
  intros.
  sep lifts (4::1::nil)%nat in H8.
  apply read_only_merge_vptr in H8.
  instantiate (1:= GV OSTCBCur @ OS_TCB ∗ |-> Vptr v'17 **
          GV OSTCBList @ OS_TCB ∗ |-> v'7 **
          tcbdllseg v'7 Vnull v'13 (Vptr v'17) v'9 **
          tcbdllseg (Vptr v'17) v'13 v'21 Vnull (v'10 :: v'11) **
          tcbdllflag v'7 (v'9 ++ v'10 :: v'11) **
          AOSEventFreeList v'1 **
          AOSQFreeList v'2 **
          AOSQFreeBlk v'3 **
          AECBList v'5 v'4 v'14 v'15 **
          AOSMapTbl **
          AOSUnMapTbl **
          AOSTCBPrioTbl v'6 v'12 v'15 v'18 **
          AOSIntNesting **
          AOSTCBFreeList' v'19 v'20 v'17 v'15**
          AOSRdyTbl v'12 **
          GV OSRdyGrp @ Int8u |-> Vint32 i **
          AOSTime (Vint32 v'16) **
          HECBList v'14 **
          HTCBList v'15 **
          HTime v'16 **
          HCurTCB v'17 **
          AGVars **
          A_isr_is_prop **
           <|| isched;; v'0 ||>  **
          Aisr empisr **
          Aie false **
          Ais nil **
          Acs (true :: nil) **
          atoy_inv' **
          LINV OSLInv ct (logic_val (V$ 0) :: nil) **
          LV y @ Int8u |-> v' ** A_dom_lenv ((y, Int8u) :: nil) ** [|v'17 = ct|]).
  destruct H8.
  subst v'17.
  sep auto.
  hoare_split_pure_all.
  subst v'17.
  unfold tcbdllseg.
  unfold tcbdllflag.

  hoare lifts (3::4::5::30::nil)%nat pre.
  eapply backward_rule1.
  intros.
  eapply task_del_noexists in H8.
  exact H8.
  apply pfalse_rule.
  (*************)
  hoare unfold.
  unfold AOSUnMapTbl.
  hoare forward.
  pauto.
  lets Hx:osunmapvallist_prop H0.
  mytac.
  rewrite H5.
  simpl.
  rtmatch_solve.
  apply Zle_bool_imp_le in H6;omega.
  
  (*--------------get highest prio--------------*)
  unfold AGVars.
  unfold AOSRdyTbl.

  lets Hiprop: osunmapvallist_prop H0.
  mytac.
  rewrite H4.
  assert (Int.unsigned x <=? Byte.max_unsigned  =true).
  rewrite byte_max_unsigned_val.
  assert (Int.unsigned x <=? 255 =true).
  apply Zle_bool_imp_le in H5.
  apply Zle_is_le_bool.
  omega.
  auto.
  pure intro.
  
  lets Hxprop: array_type_vallist_match_imp_rule_type_val_match H9.
  rewrite H10.
  apply Zle_bool_imp_le in H5.
  instantiate (1:= Z.to_nat (Int.unsigned x)).
  unfold OS_RDY_TBL_SIZE.
  apply  Z2Nat.inj_lt.
  apply Int.unsigned_range.
  omega.
  omega.
  unfolds in Hxprop.
  remember (nth_val' (Z.to_nat (Int.unsigned x)) v'12) as X.
  destruct X;tryfalse.

  hoare forward.
  rewrite H6.
  auto.
  
  rewrite H6.
  auto.
  assert (Int.unsigned x <= 7).
  apply Zle_bool_imp_le;auto.
  omega.

  sep lift 2%nat in H11.
  unfold OS_RDY_TBL_SIZE in H10.
  eapply GAarray_imp_length_P in H11.
  rewrite H11.
  simpl.
  apply Zle_bool_imp_le in H5.
  omega.
  rewrite <- HeqX.
  simpl;auto.
  eauto.
  remember (Int.unsigned i0 <=? Byte.max_unsigned) as Y.
  destruct Y;tryfalse.
  symmetry in HeqY.
  rewrite  byte_max_unsigned_val in HeqY.
  apply Zle_bool_imp_le in HeqY.
  omega.
  remember (Int.unsigned i0 <=? Byte.max_unsigned) as Y.
  destruct Y;tryfalse.
  symmetry in HeqY.
  rewrite  byte_max_unsigned_val in HeqY.
  apply Zle_bool_imp_le in HeqY.
  omega.
  assert ((Int.unsigned i0 <=? 255) = true) as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255));tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H12.
  simpl;auto.
  rtmatch_solve.
  apply Zle_bool_imp_le in H13;omega.

  rewrite int_iwordsize_gt_3.
  simpl.
  assert ((Int.unsigned i0 <=? 255) = true) as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255));tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H12.
  simpl;auto.
  (* get current task prio *)
  unfold AOSTCBFreeList'.
  hoare normal pre.
  hoare lift 23%nat pre.
  eapply backward_rule1.
  intros.
  apply disj_split in H11.
  destruct H11.
  unfold TCBFree_Not_Eq in H11.
  sep split in H11;tryfalse.
  eauto.
  unfold TCBFree_Eq.
  unfold p_local.
  unfold CurTid.
  hoare unfold.
  eapply backward_rule1.
  intros.
  sep lifts (15::1::nil)%nat in H14.

  Set Printing Depth 999.
  apply read_only_merge_vptr in H14.
  instantiate (1:=  GV OSTCBCur @ OS_TCB ∗ |-> Vptr v'17 **
           Astruct v'17 OS_TCB_flag
             (v'26
              :: x10
                 :: x9
                    :: x8
                       :: Vint32 i7
                          :: Vint32 i6
                             :: Vint32 x0
                                :: Vint32 i4
                                   :: Vint32 i3
                                      :: Vint32 i2 :: Vint32 i1 :: nil) **
           PV get_off_addr v'17 ($ 24) @ Int8u |-r-> (V$ 0) **
           sll v'26 v'24 OS_TCB_flag (fun vl : vallist => nth_val 0 vl) **
           sllfreeflag v'26 v'24 **
            <|| isched;; v'0 ||>  **
           A_dom_lenv ((y, Int8u) :: nil) **
           GV OSPrioHighRdy @ Int8u
           |-> val_inj
                 (add
                    (val_inj
                       (if Int.ltu ($ 3) Int.iwordsize
                        then Some (Vint32 (x<<ᵢ$ 3))
                        else None))
                    (nth_val' (Z.to_nat (Int.unsigned i0)) OSUnMapVallist)
                    Int32u Int8u) **
           GV OSIntExitY @ Int8u |-> Vint32 v'23 **
           GV OSPrioCur @ Int8u |-> Vint32 v'22 **
           GV OSTCBHighRdy @ OS_TCB ∗ |-> Vptr v'21 **
           GV OSCtxSwCtr @ Int32u |-> Vint32 v'19 **
           LV y @ Int8u |-> Vint32 x **
           GV OSTCBList @ OS_TCB ∗ |-> v'7 **
           tcblist v'7 Vnull v'13 Vnull (v'9 ++ v'10 :: v'11) v'12 v'15 **
           TCB_Not_In (Vptr v'17) v'7 (v'9 ++ v'10 :: v'11) **
           tcbdllflag v'7 (v'9 ++ v'10 :: v'11) **
           AOSEventFreeList v'1 **
           AOSQFreeList v'2 **
           AOSQFreeBlk v'3 **
           AECBList v'5 v'4 v'14 v'15 **
           AOSMapTbl **
           GAarray OSUnMapTbl (Tarray Int8u 256) OSUnMapVallist **
           AOSTCBPrioTbl v'6 v'12 v'15 v'18 **
           AOSIntNesting **
           GV OSTCBFreeList @ OS_TCB ∗ |-> Vptr v'17 **
           GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE) v'12 **
           GV OSRdyGrp @ Int8u |-> Vint32 i **
           AOSTime (Vint32 v'16) **
           HECBList v'14 **
           HTCBList v'15 **
           HTime v'16 **
           HCurTCB v'17 **
           GV OSRunning @ Int8u |-> (V$ 1) **
           A_isr_is_prop **
           Aisr empisr **
           Aie false **
           Ais nil **
           Acs (true :: nil) **
           atoy_inv' ** LINV OSLInv ct (logic_val (V$ 0) :: nil)  ** [|v'17 = ct|]).
  destruct H14.
  subst v'17.
  sep auto.
  hoare_split_pure_all.
  subst v'17.
  
  hoare forward.
  go.
  unfold p_local.
  unfold CurTid.
  sep normal.
  sep eexists.
  sep cancel LINV.
  sep lift 2%nat in H14.
  apply read_only_split_vptr in H14.
  sep cancel 1%nat 1%nat.
  simpl;auto.

  (*----check if current task is highest ready----*)
  rewrite int_iwordsize_gt_3.
  simpl add.
  assert ((Int.unsigned i0 <=? 255) = true) as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255));tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H14.
  unfold AOSTCBPrioTbl.
  lets Hran:shl3_add_range H5 H17.
  apply Zle_bool_imp_le in Hran.
  hoare forward.
  assert ( Int.unsigned ((x<<ᵢ$ 3)+ᵢ x1) <= Byte.max_unsigned ).
  rewrite byte_max_unsigned_val.
  omega.
  apply Zle_is_le_bool in H30.  
  rewrite H30;auto.
  assert ( Int.unsigned x0 <=? Byte.max_unsigned =true).
  rewrite byte_max_unsigned_val.
  apply Zle_is_le_bool.
  omega.
  rewrite H30;auto.
  destruct (Int.eq ((x<<ᵢ$ 3) +ᵢ x1) x0);auto.
  destruct (Int.eq ((x<<ᵢ$ 3) +ᵢ x1) x0);simpl;auto.
  hoare forward.
  assert ( Int.unsigned ((x<<ᵢ$ 3) +ᵢ x1) <= Byte.max_unsigned ).
  rewrite byte_max_unsigned_val.
  omega.
  apply Zle_is_le_bool in H31.  
  rewrite H31;auto.
  destruct H27.
  eapply array_type_vallist_match_imp_rule_type_val_match;eauto.
  rewrite H31.

  assert (64%nat = Z.to_nat (63+1)).
  simpl;auto.
  rewrite H32.
  eapply int_unsigned_le_z2nat_lt.
  auto.
  unfold p_local.
  unfold CurTid.
  sep normal.
  exists OS_TCB.
  sep cancel LINV.
  sep cancel 4%nat 1%nat.
  simpl;auto.
  hoare forward;eauto.
  unfold p_local.
  unfold CurTid.
  sep normal.
  exists OS_TCB.
  sep cancel LINV.
  sep cancel 5%nat 1%nat.
  simpl;auto.
  instantiate (1:=Afalse).
  pure intro.
  lets Hinrtbl:unmap_inrtbl H2 H1 H4 H14;auto.
  lets Hhastid:prio_in_rtbl_has_tid H27 Hinrtbl.
  rewrite Int.repr_unsigned.
  lets Hx:Int.unsigned_range ((x<<ᵢ$ 3)+ᵢx1).
  split;omega.
  destruct Hhastid.
  hoare lifts (1::14::2::nil)%nat pre.
  hoare remember (1::2::3::nil) pre.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  unfold isched.
  instantiate (1:= <|| (ASSUME sc;; sched);; v'0 ||>  **
                       LV y @ Int8u |-> Vint32 x ** A_dom_lenv ((y, Int8u) :: nil) ** H34).
  apply absinfer_seq;auto.
  subst H34.
  unfold tcblist.
  unfold LINV.
  unfold OSLInv.
  go.
  subst H34.
  unfold tcblist.
  unfold LINV.
  unfold OSLInv.
  can_change_aop_solver.
  apply absinfer_choice1;auto.
  subst H34.
  unfold tcblist.
  unfold LINV.
  unfold OSLInv.
  can_change_aop_solver.
  subst H34.
  unfold tcblist.
  unfold LINV.
  unfold OSLInv.
  can_change_aop_solver.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  instantiate (1:= <|| (spec_done None;;sched);; v'0 ||>  **
                       LV y @ Int8u |-> Vint32 x ** A_dom_lenv ((y, Int8u) :: nil) ** H34).
  
  eapply sc_isched_step with (t:=x2) (ct:=ct);eauto.
  subst H34.
  unfold tcblist.
  unfold LINV.
  unfold OSLInv.
  can_change_aop_solver.
  split.

  eapply highest_rdy_eq_dead;eauto.
  rewrite Int.repr_unsigned in H33;auto.

  subst H34.
  sep cancel tcblist.
  sep cancel 31%nat 1%nat.
  sep cancel  7%nat 1%nat.
  exact H35.
  subst H34.
  sep auto.

  sep lifts (15::16::31::7::nil)%nat in H35.
  eapply  highest_ct_dead_neq in H35;eauto.
  rewrite Int.repr_unsigned in H33;auto.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  instantiate (1:= <|| sched;; v'0 ||>  **
                       LV y @ Int8u |-> Vint32 x ** A_dom_lenv ((y, Int8u) :: nil) ** H34).
  apply absinfer_seq;auto.
  subst H34.
  unfold tcblist.
  unfold LINV.
  unfold OSLInv.
  can_change_aop_solver.
  subst H34.
  unfold tcblist.
  unfold LINV.
  unfold OSLInv.
  can_change_aop_solver.
  apply absinfer_seq_end;auto.
  subst H34.
  unfold tcblist.
  unfold LINV.
  unfold OSLInv.
  can_change_aop_solver.
  subst H34.
  unfold tcblist.
  unfold LINV.
  unfold OSLInv.
  can_change_aop_solver.
  
  apply backward_rule1 with ( <|| sched;; v'0 ||>  **
                                  (LV y @ Int8u |-> Vint32 x ** A_dom_lenv ((y, Int8u) :: nil)) ** H34).
  intros.
  sep normal.
  auto.
  subst H34.

  eapply switchdead_rule with (Px:=LINV OSLInv ct  (logic_val (V$ 0) :: nil) ** LV y @ Int8u |-> Vint32 x ** A_dom_lenv ((y, Int8u) :: nil) ).
  unfold LINV,OSLInv.
  simpl;auto.
  intros.
  sep cancel LINV.
  sep cancel 2%nat 2%nat.
  sep cancel 2%nat 2%nat.
  exact H34.
  
  intros.
  unfold SWINVt.
  
  sep normal.
  exists OS_TCB.
  sep cancel 6%nat 1%nat.
  unfold SWINV.
  sep normal.
  exists INUM.
  sep lifts (4::2::nil)%nat.
  eapply imp_isrclr.
  apply simpl_inv_excrit.

  unfold OSInv.
  unfold AGVars.
  unfold AOSTCBPrioTbl.
  
  sep semiauto;eauto.
  sep cancel 2%nat 1%nat.
  sep cancel AOSEventFreeList.
  sep cancel AOSQFreeList.
  sep cancel AOSQFreeBlk.
  sep cancel AECBList.
  sep cancel 10%nat 1%nat.
  unfold AOSTCBList'.
  apply disj_split.
  right.
  sep normal.
  exists v'13.
  sep cancel TCB_Not_In.
  unfold AOSTCBFreeList'.
  sep lift 8%nat.
  apply disj_split.
  right.
  unfold TCBFree_Eq.
  sep auto.
  go.
  eexists;split.
  unfolds;simpl;auto.
  auto.
  simpl;auto.
  rewrite Int.repr_unsigned in H33;eauto.
  destruct_s s.
  simpl;simpl in H38;subst;auto.
  simpl;auto.
  rewrite byte_max_unsigned_val.
  apply Zle_is_le_bool in H0.
  rewrite H0;auto.

  clear -H13.
  unfolds in H13.
  mytac.
  unfolds in H.
  simpl in H.
  inverts H;auto.
  clear -H13.
  int auto.
  intros.
  unfold SWPRE_DEAD.
  split.
  unfold SWPRE.
  rewrite Int.repr_unsigned in H33.
  rewrite H33 in *.

  exists x2.
  sep lift 2%nat.
  apply imp_isrclr.
  sep cancel Aisr.
  sep normal.
  exists OS_TCB.
  exists OS_TCB.
  sep cancel 3%nat 2%nat.
  assert ( s |= GV OSTCBCur @ OS_TCB ∗ |-> Vptr ct **  AHprio GetHPrio x2 ** Atrue).
  eapply highest_rdy_eq_dead;eauto.
  sep cancel tcblist.
  sep auto.
  auto.

  exists v'15.

  eapply dead_not_in;eauto.
  sep cancel tcblist.
  sep cancel 14%nat 1%nat.
  sep auto.
  intros.
  sep cancel LINV.
  simpl;auto.

  apply disj_rule.
  eapply backward_rule1 with Afalse.
  intros.
  simpl in H26;mytac.
  false.
  apply pfalse_rule.
  pure intro.
  destruct H29.
  remember (Int.eq ((x<<ᵢ$ 3) +ᵢ x1) x0) as X.
  destruct X.
  simpl in H29.

  assert (Int.eq ((x<<ᵢ$ 3) +ᵢ  x1) x0 =false).
  eapply dead_not_ready;eauto.
  eapply prio_not_in_tcbls_nready;eauto.
  clear -H13.
  unfolds in H13.
  mytac.
  unfolds in H;inverts H.
  auto.
  rewrite H31 in HeqX0;tryfalse.
  simpl in H30.
  clear -H29;int auto.
  destruct (Int.eq ((x<<ᵢ$ 3) +ᵢ  x1) x0);simpl in H29;tryfalse.
Qed.
