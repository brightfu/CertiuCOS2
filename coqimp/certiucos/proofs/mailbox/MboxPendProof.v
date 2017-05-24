(**************************  uc/OS-II  ******************************)
(*************************** OS_MBOX.C ******************************)
(*Proof of API Fucntion:  Int8u OSMboxPend(OS_EVENT* pevent, Int16u timeout)*)
(***************************** Code: ********************************)
(***
   Int8u ·OSMboxPend·(⌞ pevent @ OS_EVENT ∗; timeout @ Int16u ⌟)··{
         ⌞ 
         message @ Void∗;
         legal @ Int8u
        ⌟; 

1        If (pevent′ ==ₑ  NULL)
         {
2           RETURN  ′MBOX_PEND_NULL_ERR
         };ₛ
3        ENTER_CRITICAL;ₛ
4        legal′ =ᶠ OS_EventSearch(·pevent′·);ₛ
5        If (legal′ ==ₑ ′0)
         {
6           EXIT_CRITICAL;ₛ
7           RETURN  ′MBOX_PEND_P_NOT_LEGAL_ERR
         };ₛ 
8        If (pevent′→OSEventType !=ₑ ′OS_EVENT_TYPE_MBOX){
9           EXIT_CRITICAL;ₛ
10          RETURN  ′MBOX_PEND_WRONG_TYPE_ERR
         };ₛ
11       If (OSTCBCur′→OSTCBPrio ==ₑ ′OS_IDLE_PRIO)
         {
12          EXIT_CRITICAL;ₛ
13          RETURN  ′MBOX_PEND_FROM_IDLE_ERR
         };ₛ
14       If ( (OSTCBCur′→OSTCBStat  !=ₑ ′OS_STAT_RDY) ||ₑ (OSTCBCur′→OSTCBDly  !=ₑ ′0))
         {
15          EXIT_CRITICAL;ₛ
16          RETURN  ′MBOX_PEND_NOT_READY_ERR
         };ₛ     
17       message′ =ₑ pevent′→OSEventPtr;ₛ
18       If (message′ !=ₑ NULL)
         {
19          pevent′→OSEventPtr =ₑ NULL;ₛ
20          OSTCBCur′→OSTCBMsg =ₑ message′;ₛ
21          EXIT_CRITICAL;ₛ
22          RETURN  ′MBOX_PEND_SUCC 
         };ₛ
23       OSTCBCur′→OSTCBMsg =ₑ NULL;ₛ
24       OSTCBCur′→OSTCBStat =ₑ ′OS_STAT_MBOX;ₛ
25       OSTCBCur′→OSTCBDly =ₑ timeout′;ₛ
26       OS_EventTaskWait(­pevent′­);ₛ
27       EXIT_CRITICAL;ₛ
28       OS_Sched(­);ₛ
29       ENTER_CRITICAL;ₛ
30       message′ =ₑ OSTCBCur′→OSTCBMsg;ₛ                                 
31       If (message′ !=ₑ NULL)
         {
32          EXIT_CRITICAL;ₛ
33          RETURN  ′MBOX_PEND_SUCC
         };ₛ
34       EXIT_CRITICAL;ₛ
35       RETURN  ′MBOX_PEND_TIMEOUT_ERR
  }· . 
*)
Require Import ucos_include.
Require Import Mbox_common.
Require Import os_ucos_h.
Require Import mbox_absop_rules.
Require Import sep_lemmas_ext.
Local Open Scope code_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.

Ltac can_change_aop_solver :=  clear; try unfold OSInv;
  try unfold AOSEventFreeList, AOSQFreeList, AOSQFreeBlk, AECBList;
  try unfold AOSMapTbl, AOSUnMapTbl, AOSTCBPrioTbl, AOSIntNesting, AOSTCBList, AOSTCBFreeList;
  try unfold AOSRdyTblGrp, AOSRdyTbl, AOSRdyGrp, AOSTime, AGVars;
  try unfold AOSEvent, AOSEventTbl, AMsgData, AOSQCtr, AOSQBlk, node;
  unfold can_change_aop; fold can_change_aop; intuition auto 1 with can_change_aop;simpl;intros; intuition auto 1 with can_change_aop.

Lemma MboxPendProof:
    forall  vl p r tid, 
      Some p =
      BuildPreA' os_api OSMboxPend mbox_pendapi vl OSLInv tid init_lg ->
      Some r =
      BuildRetA' os_api OSMboxPend mbox_pendapi vl OSLInv tid init_lg ->
      exists t d1 d2 s,
        os_api OSMboxPend = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|- tid {{p}}s {{Afalse}}.
Proof.
  intros.
  init_spec.
  hoare unfold.
  destruct x0; unfolds in H2; elim  H2;intros; simpljoin; tryfalse.
  hoare forward.
  (* intro; tryfalse. *)
  hoare unfold.
  hoare abscsq.
  apply noabs_oslinv.
  eapply absinfer_mbox_pend_null_return.
  can_change_aop_solver.
  unfolds.
  unfold type_val_match.
  pauto.
  hoare forward.
  hoare forward.
  hoare unfold.
  false.
  destruct H; intros;  tryfalse.
  hoare unfold.

  
  hoare unfold.
  hoare forward.
  destruct x.
  simpl.
  intro; tryfalse.
  hoare unfold.
  destruct x.
  false; simpl in *.
  auto.

  (* pevent(x) is not null *)
  instantiate (1:=Afalse).
  hoare forward.
  hoare unfold.
  hoare forward prim.
  hoare forward.
  sep cancel tcbdllflag.
  sep cancel Aop.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aisr.
  sep cancel AECBList.
  sep cancel AOSTCBList.
  sep cancel AOSRdyTblGrp.
  sep cancel AOSTCBPrioTbl.
  eauto.
  go.
  go.
  eapply retpost_osev .
  Require Import linv_solver.
  linv_solver.
  linv_solver.
  hoare unfold.
  eapply backward_rule1.
  intros;eapply disj_star_elim.
  eauto.
  hoare forward.
  
  Focus 2.
  (* legal = 0 *)
  hoare unfold.
  hoare forward.
  change (Int.eq ($ 0) ($ 0)) with true.
  (* simpl; intro; tryfalse. *)
  hoare unfold.
  hoare abscsq.
  apply noabs_oslinv.
  inverts H6.


  eapply absinfer_mbox_pend_p_not_legal_return.
  can_change_aop_solver.
  auto.
  auto.
  hoare forward prim.
  eauto.
  go.
  hoare forward.
  hoare forward.
  hoare unfold.
  false.
  destruct H4; intros.
  int auto.
  int auto.

  hoare unfold.  
  hoare forward.
  Local Ltac bfsolver :=
    match goal with
      | |- context[if ?e then _ else _] => destruct e; simpl; try solve[ intro; tryfalse | auto]
    end.
  (* bfsolver. *)

  hoare unfold.
  false.
  int auto.
  instantiate (1:=Afalse).
  hoare forward.
  hoare unfold.


  hoare forward.
  (* intro; tryfalse. *)
  go.
  bfsolver.
  bfsolver.
  hoare unfold.
  eapply backward_rule1.
  intros.
  sep lift 8%nat in H27.
  remember (Int.eq i1 ($ OS_EVENT_TYPE_MBOX)) as X.
  destruct X;simpl in H11;auto;tryfalse.
  unfold Int.notbool in H11;simpl in H11.
  rewrite eq_one_zero in H11.
  tryfalse.

  eapply eventtype_neq_mbox' in H27;eauto.
  hoare_split_pure_all.
  hoare abscsq.
  apply noabs_oslinv.
  inverts H16.
  eapply absinfer_mbox_pend_wrong_type_return; auto.
  can_change_aop_solver.
  hoare forward prim.
  unfold AECBList.
  sep pauto.
  eapply evsllseg_compose.
  instantiate (2:= (Vint32 i1 :: Vint32 i0 :: Vint32 i2 :: x2 :: x3 :: v'42 :: nil) ).
  unfolds; simpl; eauto.
  auto.
  auto.
  sep cancel 4%nat 2%nat.
  sep cancel 4%nat 2%nat.
  unfold AEventNode.
  unfold AOSEvent.
  unfold node.
  sep pauto.
  unfold AOSEventTbl.
  sep pauto.
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel AEventData.
  eauto.
  auto.
  eauto.
  unfolds ; simpl; auto.
  
  pauto.
  splits; [auto| struct_type_match_solver].
  auto.
  go.
  
  hoare forward.
  hoare forward.

  hoare unfold.
  (* legal && type = Mbox *)
  apply val_inj_eq in H11.
  subst i1.

  hoare forward.
  struct_type_match_solver.
  bfsolver.
  hoare unfold.
  (* idle pend *)
  remember (Int.eq i7 ($ OS_IDLE_PRIO)).
  destruct b.
  Focus 2.
  false.
  simpl in H11.
  tryfalse.

  assert ( i7 = $ OS_IDLE_PRIO).
  clear -Heqb.
  int auto.
  destruct (zeq (Int.unsigned i7) OS_IDLE_PRIO).
  apply unsigned_inj.
  int auto.
  unfold OS_IDLE_PRIO. 
  unfold OS_LOWEST_PRIO.
  omega.
  inversion Heqb.
  unfold OS_IDLE_PRIO. 
  unfold OS_LOWEST_PRIO.


  omega.
  subst i7.



  hoare abscsq.
  apply noabs_oslinv.
  inverts H16.

  eapply absinfer_mbox_pend_from_idle_return.
  can_change_aop_solver.
  auto.


  lets tmp: TCBListP_head_in_tcb H32.
  simpljoin.
  do 2 eexists.
  eauto.
  eapply TcbMod.join_get_r.
  eauto.
  eauto.

  hoare forward prim.
  unfold AECBList.
  unfold AOSTCBList.
  unfold tcbdllseg.
  sep pauto.
  sep cancel 3%nat 1%nat.
  unfold dllseg.
  fold dllseg.
  unfold node.
  sep pauto.
  sep cancel Astruct.
  sep cancel dllseg.
  eapply evsllseg_compose.
  instantiate (2:=V$OS_EVENT_TYPE_MBOX :: Vint32 i0 :: Vint32 i2 :: x2 :: x3 :: v'42 :: nil).
  unfold V_OSEventListPtr; simpl;  auto. 
  auto.  
  auto.
  repeat (sep cancel evsllseg).
  (* AEventNode *)  

  unfold AEventNode.
  unfold AOSEvent.
  unfold AOSEventTbl.
  unfold node.
  sep pauto.
  eauto.
  unfolds; auto.
  split;[auto| struct_type_match_solver].
  unfolds; auto.
  unfolds; auto.
  split;auto.
  struct_type_match_solver. (* pauto *)
  auto.
  eauto.
  eauto.
  auto.
  pauto.

  hoare forward.
  hoare forward.
  hoare unfold.

  (* not idle pend *)
  hoare forward.
  struct_type_match_solver.
  bfsolver.
  bfsolver.
  go.
  bfsolver.
  bfsolver.
  bfsolver.
  bfsolver.
  bfsolver.
  (* pauto.
   * pauto.
   * destruct (Int.eq i8 ($ OS_STAT_RDY));auto.
   * destruct (Int.eq i9 ($ OS_STAT_RDY));simpl;auto.
   * destruct (Int.eq i9 ($ 0));simpl;auto.
   * destruct (Int.eq i9 ($ 0));simpl;auto.
   * destruct (Int.eq i9 ($ 0));simpl;auto. *)
  hoare unfold.
  assert (Int.eq i8 ($ OS_STAT_RDY) = false \/ Int.eq i9 ($ 0) =false).
  clear -H19.
  destruct (Int.eq i8 ($ OS_STAT_RDY));destruct (Int.eq i9 ($ 0));simpl in H19;auto;tryfalse.
  assert (Int.ltu Int.zero (Int.notbool Int.one)
                  || Int.ltu Int.zero (Int.notbool Int.one) = false).
  unfold Int.notbool.
  clear;int auto.
  rewrite H in H19.
  simpl in H19; tryfalse.
  unfold1 TCBList_P in H32.
  simpljoin.
  unfolds in e0; inverts e0; inverts e.
  unfold TCBNode_P in *.
  destruct x4.
  destruct p.
  simpljoin.
  unfold V_OSTCBNext, V_OSTCBMsg, V_OSTCBPrio, V_OSTCBDly, V_OSTCBStat in *.
  unfold TcbJoin in *.
  assert (TcbMod.get v'49 (v'51, Int.zero) = Some (p, t1, m)).
  lets H100 : TcbMod.get_sig_some (v'51, Int.zero) (p, t1, m).
  eapply TcbMod.join_get_get_l; eauto.
  assert (TcbMod.get v'36 (v'51, Int.zero) = Some (p, t1, m)).
  eapply TcbMod.join_get_get_r; eauto.

  idtac.
(* ** ac:   Check r_tcb_status_p_nrdy. *)
(* ** ac:   Check r_tcb_status_p_nrdy. *)

  lets Hnrdy: r_tcb_status_p_nrdy H47 H44.
  hoare abscsq.
  apply noabs_oslinv.

  inverts H16.
  eapply absinfer_mbox_pend_not_ready_return;eauto.
  can_change_aop_solver.
  hoare forward prim.

  unfold AECBList.
  unfold AOSTCBList.
  unfold tcbdllseg.
  sep pauto.
  sep cancel 3%nat 1%nat.
  unfold dllseg.
  fold dllseg.
  unfold node.
  sep pauto.
  sep cancel Astruct.
  sep cancel dllseg.
  eapply evsllseg_compose.
  instantiate (2:=V$OS_EVENT_TYPE_MBOX :: Vint32 i0 :: Vint32 i2 :: x2 :: x3 :: v'42 :: nil).
  unfold V_OSEventListPtr; simpl;  auto. 
  auto.  
  auto.
  repeat (sep cancel evsllseg).
  (* AEventNode *)  

  unfold AEventNode.
  unfold AOSEvent.
  unfold AOSEventTbl.
  unfold node.
  sep pauto.
  eauto.
  unfolds; auto.
  split;[auto| struct_type_match_solver]. 
  unfolds; auto.
  unfolds; auto.
  split;auto.
  struct_type_match_solver.
  auto.
  eauto.
  eauto.
  auto.
  pauto.
  eauto.
  unfolds.
  do 4 eexists.
  fold TCBList_P.
  splits; eauto.
  unfolds; auto.
  unfolds; auto.
  eauto.
  auto.
  pauto.

  hoare forward.
  hoare forward.
  hoare_split_pure_all.
  assert (Int.eq i8 ($ OS_STAT_RDY) = true /\ Int.eq i9 ($ 0) = true) as Hstrdy.
  clear -H19.

  assert (Int.ltu Int.zero (Int.notbool Int.one)
                  || Int.ltu Int.zero (Int.notbool Int.zero) = true).
  
  unfold Int.notbool.
  clear;int auto.
  destruct (Int.eq i8 ($ OS_STAT_RDY));destruct (Int.eq i9 ($ 0));simpl in H19;auto;tryfalse.
  rewrite H in H19;unfold val_inj in H19;simpl in H19;destruct H19;tryfalse.

  assert (Int.ltu Int.zero (Int.notbool Int.zero)
                  || Int.ltu Int.zero (Int.notbool Int.one) = true).
  
  unfold Int.notbool.
  clear;int auto.
  rewrite H0 in H19;
  unfold val_inj in H19;simpl in H19;destruct H19;tryfalse.

  assert (Int.ltu Int.zero (Int.notbool Int.zero)
              || Int.ltu Int.zero (Int.notbool Int.zero) = true).
  
  unfold Int.notbool.
  clear;int auto.
  rewrite H0 in H19;
  unfold val_inj in H19;simpl in H19;destruct H19;tryfalse.

  clear H19.


  (* Cur is ready *)

  unfold AEventData.

  destruct v'41; hoare_split_pure_all; tryfalse.
  inverts H27.
  unfolds in H5.
  destruct v'46; destruct e; tryfalse.
  inversion H5.
  subst m0.

  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  unfold AOSRdyGrp.
  hoare_split_pure_all.
  simpljoin.


  lets tmp:  TCBListP_head_in_tcb H32.
  destruct tmp as (tmp2 & tmp).



  lets aaa: TCBList_P_impl_high_tcbcur_rdy  H32; eauto.
  simpljoin.
  rewrite H5 in tmp.
  inverts tmp.



  hoare unfold.
  hoare forward.
  (* intro; tryfalse. *)
  struct_type_match_solver.
  hoare unfold.
  hoare forward.
  clear -H25.
  pauto.
  clear -H25; pauto.
  clear -H25; pauto.
  hoare unfold.
  assert ( exists xx, m= Vptr xx).
  clear -H19 H51 H52.
  destruct m; simpl in H19, H51, H52; tryfalse.
  unfold Int.notbool in H19, H51, H52.
  int auto.
  eauto.
  simpljoin.

  (* message not null *)
  hoare unfold.
  hoare forward.
  hoare unfold.
  hoare forward.
  assert ( w = nil).
  clear -H33.
  unfolds in H33.
  simpljoin.
  apply H.
  intro.
  tryfalse.
  subst w.


  hoare abscsq.
  apply noabs_oslinv.
  inverts H16.
  eapply absinfer_mbox_pend_inst_get_return; eauto.
  can_change_aop_solver.
  eapply EcbMod.join_get_r; eauto.
  eapply EcbMod.join_get_l; eauto.
  eapply EcbMod.get_a_sig_a.
  apply CltEnvMod.beq_refl.


  eapply TcbMod.join_get_r; eauto.
  

  hoare forward prim.
  unfold AECBList.
  unfold AOSTCBList.
  unfold tcbdllseg.
  sep pauto.
  sep cancel 7%nat 1%nat.
  unfold dllseg.
  fold dllseg.
  unfold node.
  sep pauto.
  sep cancel Astruct.
  sep cancel dllseg.
  eapply evsllseg_compose.
  instantiate (2:=V$OS_EVENT_TYPE_MBOX :: Vint32 i0 :: Vint32 i2 :: Vnull :: x3 :: v'42 :: nil).
  unfold V_OSEventListPtr; simpl;  auto.   Focus 3.
  repeat (sep cancel evsllseg).
  (* AEventNode *)  

  unfold AEventNode.
  unfold AOSEvent.
  unfold AOSEventTbl.
  unfold node.
  sep pauto.
  eauto.
  unfold AEventData.
  sep cancel Astruct.
  sep cancel Aarray.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  unfold AOSRdyGrp.
  sep pauto.
  sep lift 2%nat.



  eapply AOSTCBPrioTbl_high_tcblist_get_msg.
  lets tmp:  TCBListP_head_in_tcb H32.
  destruct tmp as (tmp2 & tmp).

  lets aaa: TCBList_P_impl_high_tcbcur_rdy H32; eauto.
  simpljoin.
  rewrite H54 in tmp.
  inverts tmp.
  eapply TcbMod.join_get_r.
  eauto.
  exact H54.

  sep cancel AOSTCBPrioTbl.
  instantiate (2:= (DMbox (Vnull))).
  sep pauto.
(* ** ac:   SearchAbout tcbdllflag. *)
  Require Import tcblist_setnode_lemmas.
(* ** ac:   SearchAbout tcbdllflag. *)
  eapply tcbdllflag_hold.
  2: sep cancel tcbdllflag.
(* ** ac:   SearchAbout eq_dllflag. *)
  apply tcbdllflag_hold_middle.
  unfolds ;auto.
  eauto.
  pauto.
  eauto.
  unfolds; simpl; auto.
  auto.
  pauto.
  split; auto.
  struct_type_match_solver.
  eauto.
  eauto.
  unfolds; simpl; auto.
  unfolds; simpl; auto.
  split; auto.
  struct_type_match_solver.
  rewrite list_prop1.
  rewrite list_prop1.

  eapply ecblist_p_compose.
  Focus 2.



  eapply ECBList_P_high_tcb_get_msg_hold.
  eauto.
  lets tmp:  TCBListP_head_in_tcb H32.
  destruct tmp as (tmp2 & tmp).

  lets aaa: TCBList_P_impl_high_tcbcur_rdy H32; eauto.
  simpljoin.
  rewrite H55 in tmp.
  inverts tmp.
  eapply TcbMod.join_get_r; eauto.
  eapply EcbMod.join_set_r; eauto.
  unfolds.
  eexists.
  eapply EcbMod.join_get_l; eauto.
  eapply EcbMod.get_a_sig_a.
  apply CltEnvMod.beq_refl.
  Hint Resolve CltEnvMod.beq_refl.
  3:eauto.

  eapply ECBList_P_high_tcb_get_msg_hold.
  unfold ECBList_P; fold ECBList_P.
  unfold ECBList_P in H0; fold ECBList_P in H0.
  simpljoin.
  eexists; splits; eauto.
  do 3 eexists; splits.
  unfolds; simpl; eauto.
  unfolds.
  erewrite <- EcbMod.set_sig.

  eapply EcbMod.join_set_l.
  eauto.
  unfolds; eexists.
  eapply EcbMod.get_a_sig_a.
  auto.
  unfolds; splits; auto.
  unfolds; splits; auto.
  auto.
  lets tmp:  TCBListP_head_in_tcb H32.
  destruct tmp as (tmp2 & tmp).

  lets aaa: TCBList_P_impl_high_tcbcur_rdy  H32; eauto.
  simpljoin.
  rewrite H55 in tmp.
  inverts tmp.

  eapply TcbMod.join_get_r.
  eauto.
  exact H55.



  eapply TCBList_P_tcb_get_msg_hold;  eauto.
  eapply TcbMod.join_set_r.
  auto.
  unfolds; eexists; eauto.


  eapply  RH_CurTCB_high_get_msg_hold .
  auto.
  lets tmp:  TCBListP_head_in_tcb H32.
  destruct tmp as (tmp2 & tmp).



  lets aaa: TCBList_P_impl_high_tcbcur_rdy  H32; eauto.
  simpljoin.
  rewrite H59 in tmp.
  inverts tmp.
  eapply TcbMod.join_get_r.
  eauto.  
  exact H59.


  eapply RH_TCBList_ECBList_P_high_get_msg_hold_mbox.
  auto.
  eapply EcbMod.join_get_r.
  eauto.
  eapply EcbMod.join_get_l.
  eauto.
  eapply EcbMod.get_a_sig_a.
  auto.
  eapply TcbMod.join_get_r; eauto.
  pauto.
  hoare forward.

  hoare forward.
  remember (Int.eq i7 ($ OS_IDLE_PRIO)).
  destruct b.
  false.
  clear -H11.
  destruct H11; intros; tryfalse.

  hoare unfold.
  (* doesn't have message now, wait *)
  hoare unfold.
  hoare forward.
  hoare unfold.
  hoare forward.
  hoare unfold.
  hoare forward.
  clear -H1; pauto.

  hoare lifts (14 ::12::18::nil)%nat pre.
  eapply backward_rule1.
  intros.
  apply a_isr_is_prop_split in H51.
  exact H51.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  unfold AOSRdyGrp.
  hoare_split_pure_all.

  hoare unfold.
  inverts H16.
  hoare forward.

  unfold node.
  sep pauto.
  sep cancel Astruct.
  instantiate  (2:=DMbox m).
  unfold AEventNode.
  unfold AOSEvent.
  unfold AEventData.
  unfold node.
  unfold AEventData.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  unfold AOSRdyGrp.
  unfold AOSEventTbl.
  sep pauto.
  sep cancel Aarray.

  sep cancel Astruct.
  sep cancel Aop.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Aisr.
  sep cancel Acs.
  eauto.
  12:pauto.
  unfolds; simpl; auto.
  unfolds; simpl; auto.
  pauto.
  eauto.
  unfolds; simpl; auto.
  eauto.
  pauto.
  split; auto.
  struct_type_match_solver.
  split.
  reflexivity.
  struct_type_match_solver.
  split.
  simpl; reflexivity.
  eexists; split; eauto.
  unfolds; simpl; eauto.

   eapply tcblist_p_node_rl_mbox; eauto.

   linv_solver.
   linv_solver.


  hoare_ex_intro.
  unfold OS_EventTaskWaitPost.

  unfold OS_EventTaskWaitPost'.
  unfold getasrt.

  hoare normal pre.
  hoare_ex_intro.  
  hoare_split_pure_all.
  inverts H52.
  inverts H16.
  unfold V_OSTCBY,V_OSTCBBitX,V_OSTCBBitY,V_OSEventGrp in H53.
  simpl in H53.
  simpljoin.
  inverts H53.
  inverts H52.
  inverts H54.
  inverts H59.

  assert ( m = Vnull).
  clear -H19.

  destruct m; destruct H19; simpl; intros; tryfalse.
  auto.
  simpl in H.
  destruct a.
  int auto.
  simpl in H.
  destruct a.
  int auto.

  subst m.


  hoare abscsq.
  apply noabs_oslinv.
  eapply absinfer_mbox_pend_block; eauto.
  can_change_aop_solver.


  eapply EcbMod.join_get_r; eauto.
  eapply EcbMod.join_get_l; eauto.
  apply EcbMod.get_a_sig_a.
  auto.
  eapply TcbMod.join_get_r; eauto.

(* ** ac:   Show. *)
(* ** ac:   Show. *)

  unfold AOSTCBPrioTbl.
  hoare_split_pure_all.
  lets cp : H32.
  destruct cp as (td & vv & tcblss & asbs & Hveq & Hnes & Htcj & Htp & Htlis).
  destruct asbs.
  destruct p.
  destruct Htp as (_ & _ & Hrsl & _).
  funfold Hrsl.
  assert (0<= Int.unsigned x < 64).
  clear -H62 H70.
  omega.
  assert (prio_neq_cur v'36 (v'51, Int.zero) ( x)).
  eapply R_PrioTbl_P_impl_prio_neq_cur; eauto.  
  eapply TcbMod.join_get_r.
  eauto.
  eauto.


(* ** ac:   SearchAbout OSInv. *)

(* ** ac:   Check excrit1_rule'_ISnil_ISRemp'. *)
(* ** ac:   SearchAbout A_isr_is_prop. *)
  eapply backward_rule1.
  intro.
  intros.
  eapply add_a_isr_is_prop.
  sep cancel Aisr.
  sep cancel Ais.
  eauto.
  hoare forward prim.
  (* eapply seq_rule.
   * hoare lift 2%nat pre.
   * eapply excrit1_rule'_ISnil_ISRemp'.
   * intros;unfold OSInv; unfold A_isr_is_prop; sep pauto. *)

  unfold AOSTCBList.
  sep pauto.
  unfold tcbdllseg.
  unfold dllseg at 2.
  fold dllseg.
  sep pauto.
  repeat (sep cancel dllseg).
  sep cancel node.
  (* AOSPrioTbl *)

  sep pauto.
  (* AECBList *)
  unfold AECBList.
  (* instantiate (1:=   A_dom_lenv
   *                      ((timeout, Int16u)
   *                         :: (pevent, OS_EVENT ∗)
   *                         :: (message, (Void) ∗)
   *                         :: (legal, Int8u) :: nil) **
   *                      LV message @ (Void) ∗ |-> Vnull **
   *                      LV legal @ Int8u |-> (V$1) **  LV timeout @ Int16u |-> Vint32 i **
   *                      LV pevent @ OS_EVENT ∗ |-> Vptr (v'27, Int.zero)). *)
  sep pauto.
  eapply evsllseg_compose.
  
  instantiate  (2:=(V$OS_EVENT_TYPE_MBOX
              :: Vint32 (Int.or v'64 (Int.shl (Int.repr 1) (Int.shru x ($ 3))))
                 :: Vint32 i2 :: Vnull :: x3 :: v'42 :: nil)).
  unfold V_OSEventListPtr; simpl;  auto. 
  auto.  
  auto.
  repeat (sep cancel evsllseg).

  (* sep cancel AOSEventFreeList.
   * sep cancel AOSQFreeList.
   * sep cancel AOSQFreeBlk.
   * sep cancel AOSRdyTblGrp.
   * idtac. *)
  sep cancel AEventNode.
  unfold AOSTCBPrioTbl.
  sep pauto.
  sep cancel 1%nat 1%nat.
  sep cancel 4%nat 1%nat.
(* ** ac:   SearchAbout tcbdllflag. *)
  eapply tcbdllflag_hold.
  2: sep lift 3%nat in H58; exact H58.
(* ** ac:   SearchAbout eq_dllflag. *)
  eapply tcbdllflag_hold_middle.
  unfolds; simpl.
  splits; compute; auto.
  
  (* sep cancel A_dom_lenv. *)
  (* sep cancel AOSTCBFreeList. *)
  (* sep semiauto;eauto. *)


  eapply  TcbMod_set_R_PrioTbl_P_hold ; eauto.
  eapply TcbMod.join_get_r; eauto.
  Require Import OSTimeDlyPure.
  eapply  rtbl_remove_RL_RTbl_PrioTbl_P_hold ; eauto.
(*  clear -H54 H59.
  assert (0 <= Int.unsigned x < 64) by omega.
  clear -H.
  mauto.
  clear -H54 H59.
  assert (0 <= Int.unsigned x < 64) by omega.
  clear -H.
  mauto.

  idtac.
*)
  rewrite list_prop1.
  rewrite list_prop1.
  eapply ecblist_p_compose.

  eapply EcbMod.join_set_r.
  eauto.
  eexists.
  eapply EcbMod.join_get_l.
  eauto.
  apply EcbMod.get_a_sig_a.
  go.
  eapply  ECBList_P_high_tcb_block_hold_mbox; eauto.
  eapply TcbMod.join_get_r; eauto.

    eapply ejoin_get_none_l.
    2:eauto.
    eapply EcbMod.join_get_l; eauto.
    apply EcbMod.get_a_sig_a.
    go.
  {
    unfold ECBList_P; fold ECBList_P.
    eexists; split.
    eauto.
    split.
    Focus 2.

    do 3 eexists; splits.
    unfolds; simpl; auto.
    3:eauto.
    unfolds.
    erewrite <- EcbMod.set_sig.
    eapply EcbMod.join_set_l.
    eauto.
    unfolds; eexists.
    apply EcbMod.get_a_sig_a.
    go.
    unfolds.
    splits; auto.
    unfolds; split; intros; auto.
    clear -H59; tryfalse.
    eapply  ECBList_P_high_tcb_block_hold_mbox; eauto.
    eapply TcbMod.join_get_r; eauto.

    eapply ejoin_get_none_r.
    2:eauto.
    apply EcbMod.get_a_sig_a.
    go.


    eapply R_ECB_ETbl_P_high_tcb_block_hold; eauto.
    eapply TcbMod.join_get_r; eauto.
  }

  unfold V_OSTCBPrev; simpl nth_val; auto.
  unfold V_OSTCBNext; simpl nth_val; auto.

  eapply TCBList_P_tcb_block_hold; eauto.


  eapply TcbMod_join_impl_prio_neq_cur_r; eauto.



  eapply TCBList_P_tcb_block_hold' with (prio := x); eauto.

  eapply TcbMod_join_impl_prio_neq_cur_r; eauto.
  eapply TcbMod.join_comm; eauto.
  eapply TcbMod.join_set_r; eauto.
  unfolds; eexists; eauto.

  eapply  RH_CurTCB_high_block_hold_mbox ; eauto.
  eapply TcbMod.join_get_r; eauto.

  eapply RH_TCBList_ECBList_P_high_block_hold_mbox; eauto.
  eapply EcbMod.join_get_r; eauto.
  eapply EcbMod.join_get_l; eauto.
  eapply EcbMod.get_a_sig_a.

  go.
  eapply TcbMod.join_get_r; eauto.

  unfold isr_is_prop.
  intros;unfold empisr;auto.
  pauto.


(* schedule *)

  hoare forward. 
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Aisr.
  sep cancel Acs.
  eauto.
  unfolds; auto.
  pauto.
  linv_solver.
  linv_solver.
  unfold OS_SchedPost.  
  unfold OS_SchedPost'.
  unfold getasrt.
  hoare_ex_intro. 

(* enter critical *)  
  hoare forward prim.
  (* pauto. *)
  
  hoare unfold.
  hoare forward.
  struct_type_match_solver.
  hoare unfold.
  hoare forward.
  clear -H79; pauto.
  clear -H79; pauto.
  clear -H79; pauto.

  hoare unfold.


  assert ( exists xxx, x11= Vptr xxx).
  clear -H63 H64 H75.
  destruct x11; simpl in H63; simpl in H64; simpl in H75; int auto.
  unfold Int.notbool in H63; int auto.
  exists a; auto.
  simpljoin. 
  lets backup : H73.

  unfold TCBList_P in H73; fold TCBList_P in H73.
  simpljoin.
  unfold TCBNode_P in H89.
  destruct x7; destruct p0.
  simpljoin.
  unfolds in H89; simpl in H89.
  inverts H89.
  inverts H73.

  hoare abscsq.
  apply noabs_oslinv.

  inverts H60.

  Local Open Scope Z_scope.

Lemma absinfer_mbox_pend_block_get_return
     : forall (P : asrt) (mqls : EcbMod.map) (qid : addrval) 
         (v : int32) (p : priority) (t : ostime) (ct : tidspec.A)
         (tls : TcbMod.map) (m : msg) (st : taskstatus) T_T,
       Int.unsigned v <= 65535 ->
       can_change_aop P ->
       TcbMod.get tls ct = Some (p, st, m) ->
       m <> Vnull ->
       T_T ⊢  <|| mbox_pend_timeout_err (|Vptr qid :: Vint32 v :: nil|)
    ?? mbox_pend_block_get_succ (|Vptr qid :: Vint32 v :: nil|)
    ||>
  **
        HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P
        ⇒  <|| END (Some (Vint32 (Int.repr  MBOX_PEND_SUCC))) ||>  **
         HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P
.
Proof.
  infer_part1 1%nat.
  infer_part2.
Qed.


  eapply absinfer_mbox_pend_block_get_return.
  auto.


  can_change_aop_solver.
  unfold TcbJoin in *.
  unfold join in *; unfold get in *; unfold sig in *; simpl in *; go.

  (* eapply TcbMod.join_get_r; eauto.
   * eapply TcbMod.join_get_l; eauto.
   * eapply TcbMod.get_a_sig_a; eauto.
   * go. *)

  (* auto. *)
  try intro; tryfalse.

  hoare forward prim.
  unfold AOSTCBList.
  sep pauto.
  unfold tcbdllseg.
  sep pauto.
  sep cancel 4%nat 1%nat.
  unfold dllseg; fold dllseg.
  unfold node.
  sep pauto.

  sep cancel Astruct.
  sep cancel dllseg.
  sep cancel tcbdllflag.
  eauto.
  unfolds; simpl; auto.
  unfolds; simpl; auto.
  split; auto.
  struct_type_match_solver.
  eauto.
  eauto.
  eauto.
  pauto.

  hoare forward.

  (* time out *)
  hoare forward.
  hoare unfold.

  assert (x11= Vnull).
  clear -H63.
  destruct x11; destruct H63; intros; int auto.
  simpl in H.
  destruct a.
  int auto.
  simpl in H; destruct a; int auto.

  lets backup : H73.

  unfold TCBList_P in H73; fold TCBList_P in H73.
  simpljoin.
  unfold TCBNode_P in H88.
  destruct x4; destruct p0.
  simpljoin.
  unfolds in H64; simpl in H64.
  inverts H64.
  inverts H88.
  inverts H73.

  hoare abscsq.
  apply noabs_oslinv.
  inverts H60.

Lemma absinfer_mbox_pend_to_return :
   forall P mqls qid v t ct tls st prio TuT,
    Int.unsigned v <= 65535 ->
    TcbMod.get tls ct = Some (prio, st, Vnull) ->
    can_change_aop P ->
    absinfer TuT
      ( <||
    mbox_pend_timeout_err (|Vptr qid :: Vint32 v :: nil|)
    ?? mbox_pend_block_get_succ (|Vptr qid :: Vint32 v :: nil|)
    ||>  ** 
           HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P) 
      (<||  END (Some (Vint32 (Int.repr MBOX_PEND_TIMEOUT_ERR)))||>  ** HECBList mqls  ** HTCBList tls ** HTime t ** HCurTCB ct ** P).
Proof.
  infer_part1 0%nat.
  infer_part2.
Qed.


  eapply absinfer_mbox_pend_to_return.
  auto.

  unfold TcbJoin in *.
  unfold join in *; unfold get in *; unfold sig in *; simpl in *; go.

  (* eapply TcbMod.join_get_r; eauto.
   * eapply TcbMod.join_get_l; eauto.
   * eapply TcbMod.get_a_sig_a; eauto.
   * auto with brel. *)
  can_change_aop_solver.

  hoare forward prim.
  unfold AOSTCBList.
  sep pauto.
  unfold tcbdllseg.
  sep pauto.
  sep cancel 4%nat 1%nat.
  unfold dllseg; fold dllseg.
  unfold node.
  sep pauto.

  sep cancel Astruct.
  sep cancel dllseg.
  sep cancel tcbdllflag.
  eauto.
  unfolds; simpl; auto.
  unfolds; simpl; auto.
  split; auto.
  struct_type_match_solver.
  eauto.
  eauto.
  eauto.
  pauto.

  hoare forward.


  
  (* Require Import MboxPendPart2.
   * eapply (mbox_pend_part0 i
   *                         H1
   *                         v'
   *                         v'0
   *                         v'1
   *                         v'2
   *                         v'3
   *                         v'4
   *                         v'5
   *                         v'6
   *                         v'7
   *                         v'8
   *                         v'9
   *                         v'10
   *                         v'11
   *                         v'12
   *                         v'13
   *                         v'14
   *                         v'15
   *                         v'16
   *                         v'17
   *                         v'18
   *                         v'19
   *                         v'20
   *                         v'23
   *                         v'24
   *                         v'25
   *                         v'26
   *                         v'28
   *                         v'29
   *                         v'31
   *                         v'33
   *                         v'36
   *                         v'37
   *                         v'40
   *                         v'44
   *                         v'45
   *                         v'46
   *                         v'47
   *                         w
   *                         v'49
   *                         H4
   *                         H18
   *                         H13
   *                         H17
   *                         H10
   *                         v'21
   *                         v'27
   *                         x3
   *                         i2
   *                         H24
   *                         H26
   *                         H3
   *                         H2
   *                         H
   *                         H15
   *                         v'22
   *                         v'38
   *                         v'41
   *                         v'51
   *                         v'52
   *                         v'53
   *                         H29
   *                         H30
   *                         H28
   *                         x8
   *                         x9
   *                         H35
   *                         H36
   *                         i9
   *                         H37
   *                         i8
   *                         H38
   *                         i7
   *                         H39
   *                         i6
   *                         H40
   *                         H34
   *                         H14
   *                         H8
   *                         H9
   *                         H22
   *                         Heqb
   *                         H11
   *                         H49
   *                         H50
   *                         H5
   *                         H51
   *                         v'30
   *                         v'39
   *                         v'43
   *                         v'54
   *                         v'58
   *                         v'61
   *                         v'62
   *                         v'63
   *                         v'64
   *                         v'65
   *                         v'66
   *                         H31
   *                         H27
   *                         H47
   *                         H46
   *                         H44
   *                         H45
   *                         H55
   *                         H57
   *                         H12
   *                         H21
   *                         H42
   *                         H41
   *                         H43
   *                         H32
   *                         H23
   *                         H20
   *                         H25
   *                         H48
   *                         H7
   *                         H33
   *                         H19
   *                         H0
   *                         H6)
   * . *)
Qed.
