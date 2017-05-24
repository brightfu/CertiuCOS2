Require Import include_frm.
Require Import os_program.
Require Import os_spec.
Require Import Classical.
Require Import abs_op.
Require Import inv_prop.
Require Import os_code_defs.
Require Import ifun_spec.
Require Import base_tac.
Require Import oscorrectness.
Require Import auxdef.
Require Import List.
Require Import OSTimeDlyProof.
Require Import OSTimeGetProof.
Require Import OSSemCreateProof.
Require Import OSSemDeleteProof.
Require Import OSSemAcceptProof.
Require Import MboxAcceptProof.
Require Import MboxCreateProof.
Require Import MboxDelProof.
Require Import MboxPendProof.
Require Import MboxPostProof.
Require Import OSSemPendProof.
Require Import OSSemPostProof.
Require Import OSQAcceptProof.
Require Import OSQCreateProof.
Require Import OSQDelProof.
Require Import OSQPendProof.
Require Import OSQPostProof.
Require Import OSQGetMsgProof.
Require Import IntExitProof.
Require Import OSEventRemoveProof.
Require Import OSEventSearchProof.
Require Import OSEventTaskRdy.
Require Import OSEventTaskWait.
Require Import OSEventWaitListInitProof.
Require Import OSSchedProof.
Require Import OSTimeTickProof.
Require Import TimeIntProof.
Require Import ToyIntProof.
Require Import OSMutexAcceptProof.
Require Import OSMutexCreateProof.
Require Import OSMutexDelProof.
Require Import OSMutexPendProof.
Require Import OSMutexPostProof.
Require Import taskdelete.
Require Import taskcreate.
Require Import OSIsOwnerProof.
Require Import OSTCBInitProof.
Require Import toptheorem.

Definition Spec:= OS_spec.
(*
Lemma api_internal_fun_nsame:
  no_fun_same os_api os_internal.
Proof.
  unfolds.
  split.
  intros.
  unfold os_api in *.
  unfold os_internal.
  simpl in *;auto.
  remember (Zeq_bool OSQAccept f) as X.
  destruct X.
  apply eq_sym in HeqX.
  apply Zeq_bool_eq in HeqX.
  subst.
  auto.

  remember (Zeq_bool OSQCreate f) as X1.
  destruct X1.
  apply eq_sym in HeqX1.
  apply Zeq_bool_eq in HeqX1.
  subst.
  auto.

  remember (Zeq_bool OSQDel f) as X2.
  destruct X2.
  apply eq_sym in HeqX2.
  apply Zeq_bool_eq in HeqX2.
  subst.
  auto.
  
  remember (Zeq_bool OSQPend f) as X3.
  destruct X3.
  apply eq_sym in HeqX3.
  apply Zeq_bool_eq in HeqX3.
  subst.
  auto.
  
  remember (Zeq_bool OSQPost f) as X4.
  destruct X4.
  apply eq_sym in HeqX4.
  apply Zeq_bool_eq in HeqX4.
  subst.
  auto.
  
  remember (Zeq_bool OSQGetMsg f) as X5.
  destruct X5.
  apply eq_sym in HeqX5.
  apply Zeq_bool_eq in HeqX5.
  subst.
  auto.

  remember (Zeq_bool OSSemAccept f) as X6.
  destruct X6.
  apply eq_sym in HeqX6.
  apply Zeq_bool_eq in HeqX6.
  subst.
  auto.

  remember (Zeq_bool OSSemCreate f) as X7.
  destruct X7.
  apply eq_sym in HeqX7.
  apply Zeq_bool_eq in HeqX7.
  subst.
  auto.

  remember (Zeq_bool OSSemDel f) as X8.
  destruct X8.
  apply eq_sym in HeqX8.
  apply Zeq_bool_eq in HeqX8.
  subst.
  auto.

  remember (Zeq_bool OSSemPend f) as X9.
  destruct X9.
  apply eq_sym in HeqX9.
  apply Zeq_bool_eq in HeqX9.
  subst.
  auto.

  remember (Zeq_bool OSSemPost f) as X10.
  destruct X10.
  apply eq_sym in HeqX10.
  apply Zeq_bool_eq in HeqX10.
  subst.
  auto.

  remember (Zeq_bool OSTimeDly f) as X11.
  destruct X11.
  apply eq_sym in HeqX11.
  apply Zeq_bool_eq in HeqX11.
  subst.
  auto.

  remember (Zeq_bool OSTimeGet f) as X12.
  destruct X12.
  apply eq_sym in HeqX12.
  apply Zeq_bool_eq in HeqX12.
  subst.
  auto.

  remember (Zeq_bool OSMboxCreate f) as X13.
  destruct X13.
  apply eq_sym in HeqX13.
  apply Zeq_bool_eq in HeqX13.
  subst.
  auto.

  remember (Zeq_bool OSMboxDel f) as X14.
  destruct X14.
  apply eq_sym in HeqX14.
  apply Zeq_bool_eq in HeqX14.
  subst.
  auto.

  remember (Zeq_bool OSMboxAccept f) as X15.
  destruct X15.
  apply eq_sym in HeqX15.
  apply Zeq_bool_eq in HeqX15.
  subst.
  auto.

  remember (Zeq_bool OSMboxPend f) as X16.
  destruct X16.
  apply eq_sym in HeqX16.
  apply Zeq_bool_eq in HeqX16.
  subst.
  auto.

  remember (Zeq_bool OSMboxPost f) as X17.
  destruct X17.
  apply eq_sym in HeqX17.
  apply Zeq_bool_eq in HeqX17.
  subst.
  auto.

  remember (Zeq_bool OSMutexAccept f) as X18.
  destruct X18.
  apply eq_sym in HeqX18.
  apply Zeq_bool_eq in HeqX18.
  subst.
  auto.

  remember (Zeq_bool OSMutexCreate f) as X19.
  destruct X19.
  apply eq_sym in HeqX19.
  apply Zeq_bool_eq in HeqX19.
  subst.
  auto.

  remember (Zeq_bool OSMutexDel f) as X20.
  destruct X20.
  apply eq_sym in HeqX20.
  apply Zeq_bool_eq in HeqX20.
  subst.
  auto.

  remember (Zeq_bool OSMutexPend f) as X21.
  destruct X21.
  apply eq_sym in HeqX21.
  apply Zeq_bool_eq in HeqX21.
  subst.
  auto.

  remember (Zeq_bool OSMutexPost f) as X22.
  destruct X22.
  apply eq_sym in HeqX22.
  apply Zeq_bool_eq in HeqX22.
  subst.
  auto.

  tryfalse.

  intros.
  unfold os_api in *.
  unfold os_internal in *.
  simpl in *;auto.
  remember (Zeq_bool OSInit f) as X.
  destruct X.
  apply eq_sym in HeqX.
  apply Zeq_bool_eq in HeqX.
  subst.
  auto.

  remember (Zeq_bool OSStart f) as X1.
  destruct X1.
  apply eq_sym in HeqX1.
  apply Zeq_bool_eq in HeqX1.
  subst.
  auto.

  remember (Zeq_bool OSIntEnter f) as X2.
  destruct X2.
  apply eq_sym in HeqX2.
  apply Zeq_bool_eq in HeqX2.
  subst.
  auto.
  
  remember (Zeq_bool OSVersion f) as X3.
  destruct X3.
  apply eq_sym in HeqX3.
  apply Zeq_bool_eq in HeqX3.
  subst.
  auto.
  
  remember (Zeq_bool OSIntExit f) as X4.
  destruct X4.
  apply eq_sym in HeqX4.
  apply Zeq_bool_eq in HeqX4.
  subst.
  auto.
  
  remember (Zeq_bool OSTimeTick f) as X5.
  destruct X5.
  apply eq_sym in HeqX5.
  apply Zeq_bool_eq in HeqX5.
  subst.
  auto.

  remember (Zeq_bool OS_EventTaskRdy f) as X6.
  destruct X6.
  apply eq_sym in HeqX6.
  apply Zeq_bool_eq in HeqX6.
  subst.
  auto.

  remember (Zeq_bool OS_EventTaskWait f) as X7.
  destruct X7.
  apply eq_sym in HeqX7.
  apply Zeq_bool_eq in HeqX7.
  subst.
  auto.

  remember (Zeq_bool OS_EventTO f) as X8.
  destruct X8.
  apply eq_sym in HeqX8.
  apply Zeq_bool_eq in HeqX8.
  subst.
  auto.

  remember (Zeq_bool OS_Sched f) as X9.
  destruct X9.
  apply eq_sym in HeqX9.
  apply Zeq_bool_eq in HeqX9.
  subst.
  auto.

  remember (Zeq_bool OS_TaskIdle f) as X10.
  destruct X10.
  apply eq_sym in HeqX10.
  apply Zeq_bool_eq in HeqX10.
  subst.
  auto.

  remember (Zeq_bool  OS_EventWaitListInit f) as X11.
  destruct X11.
  apply eq_sym in HeqX11.
  apply Zeq_bool_eq in HeqX11.
  subst.
  auto.

  remember (Zeq_bool OS_InitEventList f) as X12.
  destruct X12.
  apply eq_sym in HeqX12.
  apply Zeq_bool_eq in HeqX12.
  subst.
  auto.

  remember (Zeq_bool OS_InitMisc f) as X13.
  destruct X13.
  apply eq_sym in HeqX13.
  apply Zeq_bool_eq in HeqX13.
  subst.
  auto.

  remember (Zeq_bool OS_InitRdyList f) as X14.
  destruct X14.
  apply eq_sym in HeqX14.
  apply Zeq_bool_eq in HeqX14.
  subst.
  auto.

  remember (Zeq_bool OS_InitTaskIdle f) as X15.
  destruct X15.
  apply eq_sym in HeqX15.
  apply Zeq_bool_eq in HeqX15.
  subst.
  auto.

  remember (Zeq_bool OS_InitSTKList f) as X16.
  destruct X16.
  apply eq_sym in HeqX16.
  apply Zeq_bool_eq in HeqX16.
  subst.
  auto.

  remember (Zeq_bool OS_InitTCBList f) as X17.
  destruct X17.
  apply eq_sym in HeqX17.
  apply Zeq_bool_eq in HeqX17.
  subst.
  auto.

  remember (Zeq_bool OS_TCBInit f) as X18.
  destruct X18.
  apply eq_sym in HeqX18.
  apply Zeq_bool_eq in HeqX18.
  subst.
  auto.

  remember (Zeq_bool OS_EventRemove f) as X19.
  destruct X19.
  apply eq_sym in HeqX19.
  apply Zeq_bool_eq in HeqX19.
  subst.
  auto.

  remember (Zeq_bool OS_EventSearch f) as X20.
  destruct X20.
  apply eq_sym in HeqX20.
  apply Zeq_bool_eq in HeqX20.
  subst.
  auto.
  tryfalse.
Qed.


Lemma os_no_call_api:
  no_call_api_os os_api os_internal os_interrupt.
Proof.
  unfolds.
  splits.
  unfolds.
  intros.
  unfolds in H.
  destruct f;simpl in H;tryfalse.
  remember ( Zeq_bool OSQAccept (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  unfolds;splits;auto.

  remember ( Zeq_bool OSQCreate(Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  unfolds;intuition auto.
  
  remember ( Zeq_bool OSQDel(Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  unfolds;intuition auto.

  remember ( Zeq_bool OSQPend(Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  unfolds;intuition auto.

  remember ( Zeq_bool OSQGetMsg(Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  unfolds;intuition auto.

  remember ( Zeq_bool OSQPost(Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  unfolds;intuition auto.

  remember ( Zeq_bool OSSemAccept (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  unfolds;intuition auto.

  remember ( Zeq_bool OSSemCreate (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  unfolds;intuition auto.

  remember ( Zeq_bool OSSemDel (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  unfolds;intuition auto.

  remember ( Zeq_bool OSSemPend (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  unfolds;intuition auto.

  remember ( Zeq_bool OSSemPost (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  unfolds;intuition auto.

  remember ( Zeq_bool OSTimeDly (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  unfolds;intuition auto.

  remember ( Zeq_bool OSTimeGet (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  unfolds;intuition auto.

  remember ( Zeq_bool OSMboxCreate (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  unfolds;intuition auto.

  remember ( Zeq_bool OSMboxDel (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  unfolds;intuition auto.

  remember ( Zeq_bool OSMboxAccept (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  unfolds;intuition auto.

  remember ( Zeq_bool OSMboxPost (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  unfolds;intuition auto.

  remember ( Zeq_bool OSMboxPend (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  unfolds;intuition auto.

  remember ( Zeq_bool OSMutexAccept (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  unfolds;intuition auto.

  remember ( Zeq_bool OSMutexCreate (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  unfolds;intuition auto.

  remember ( Zeq_bool OSMutexDel (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  unfolds;intuition auto.

  remember ( Zeq_bool OSMutexPend (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  unfolds;intuition auto.

  remember ( Zeq_bool OSMutexPost (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  unfolds;intuition auto.
  
  tryfalse.

  unfolds.
  intros.
  unfolds in H.
  destruct f;simpl in H;tryfalse.
 
  remember ( Zeq_bool OSIntExit (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  unfolds;intuition;auto.

  remember ( Zeq_bool OSTimeTick (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  unfolds;intuition auto.
  
  remember ( Zeq_bool OS_EventTaskRdy (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  unfolds;intuition auto.

  remember ( Zeq_bool OS_EventTaskWait (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  unfolds;intuition auto.

  remember ( Zeq_bool OS_Sched (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  unfolds;intuition auto.
 
  remember ( Zeq_bool OS_EventWaitListInit (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  unfolds;intuition auto.

  remember ( Zeq_bool OS_EventRemove (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  unfolds;intuition auto.

  remember ( Zeq_bool OS_EventSearch (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  unfolds;intuition auto.
  tryfalse.
  unfolds.
  intros.
  unfolds in H.
  destruct f;simpl in H;tryfalse.
  inverts H.
  simpl;auto.
  destruct f.
  inverts H.
  simpl;intuition auto.
  tryfalse.
Qed.
*)
Lemma good_fun_api:
  forall (f : fid) (t : type) (d1 d2 : decllist) (s : stmts),
    os_api f = Some (t, d1, d2, s) ->
    good_decllist (revlcons d1 d2) = true /\ GoodStmt' s.
Proof.
  intros.
  unfolds in H.
  destruct f;simpl in H;tryfalse.
  remember ( Zeq_bool OSQAccept (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  splits;simpl;intuition auto.

  remember ( Zeq_bool OSQCreate(Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  splits;simpl;intuition auto.
  
  remember ( Zeq_bool OSQDel(Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  splits;simpl;intuition auto.

  remember ( Zeq_bool OSQPend(Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  splits;simpl;intuition auto.

  remember ( Zeq_bool OSQGetMsg(Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  splits;simpl;intuition auto.

  remember ( Zeq_bool OSQPost(Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  splits;simpl;intuition auto.

  remember ( Zeq_bool OSSemAccept (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  splits;simpl;intuition auto.
  
  remember ( Zeq_bool OSSemCreate (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  splits;simpl;intuition auto.

  remember ( Zeq_bool OSSemDel (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  splits;simpl;intuition auto.

  remember ( Zeq_bool OSSemPend (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  splits;simpl;intuition auto.

  remember ( Zeq_bool OSSemPost (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  splits;simpl;intuition auto.

  remember ( Zeq_bool OSTimeDly (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  splits;simpl;intuition auto.

  remember ( Zeq_bool OSTimeGet (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  splits;simpl;intuition auto.

  remember ( Zeq_bool OSMboxCreate (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  splits;simpl;intuition auto.

  remember ( Zeq_bool OSMboxDel (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  splits;simpl;intuition auto.

  remember ( Zeq_bool OSMboxAccept (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  splits;simpl;intuition auto.

  remember ( Zeq_bool OSMboxPost (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  splits;simpl;intuition auto.

  remember ( Zeq_bool OSMboxPend (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  splits;simpl;intuition auto.

  remember ( Zeq_bool OSMutexAccept (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  splits;simpl;intuition auto.

  remember ( Zeq_bool OSMutexCreate (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  splits;simpl;intuition auto.

  remember ( Zeq_bool OSMutexDel (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  splits;simpl;intuition auto.

  
  remember ( Zeq_bool OSMutexPend (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  splits;simpl;intuition auto.

  remember ( Zeq_bool OSMutexPost (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  splits;simpl;intuition auto.

  
  remember ( Zeq_bool OSTaskCreate (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  splits;simpl;intuition auto.

  
  remember ( Zeq_bool OSTaskDel (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  splits;simpl;intuition auto.
  
  tryfalse.
Qed.

Lemma good_fun_internal:
  forall (f : fid) (t : type) (d1 d2 : decllist) (s : stmts),
    os_internal f = Some (t, d1, d2, s) ->
    good_decllist (revlcons d1 d2) = true /\ GoodStmt' s.
Proof.
  intros.
  unfolds in H.
  destruct f;simpl in H;tryfalse.

  remember ( Zeq_bool OSIntExit (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  splits;simpl;intuition auto.

  remember ( Zeq_bool OSTimeTick (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  
  splits;simpl;intuition auto.
  
  remember ( Zeq_bool OS_EventTaskRdy (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  
  splits;simpl;intuition auto.

  remember ( Zeq_bool OS_EventTaskWait (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  
  splits;simpl;intuition auto.

  remember ( Zeq_bool OS_Sched (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  
  splits;simpl;intuition auto.

  remember ( Zeq_bool OS_EventWaitListInit (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  
  splits;simpl;intuition auto.

  remember ( Zeq_bool OS_EventRemove (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  
  splits;simpl;intuition auto.

  remember ( Zeq_bool OS_EventSearch (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  
  splits;simpl;intuition auto.

  remember ( Zeq_bool OS_TCBInit (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  
  splits;simpl;intuition auto.

  remember ( Zeq_bool OS_IsSomeMutexOwner (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  
  splits;simpl;intuition auto.
  
  tryfalse.
Qed.
  

Lemma eqdomos_p: eqdomOS (os_api, os_internal, os_interrupt) (api_spec, int_spec, GetHPrio).
Proof.
  unfolds.
  splits;intros.
  split;intros.
  simpljoin.
  unfolds in H.

  simpl in *;auto.
  remember (Zeq_bool OSQAccept f) as X.
  destruct X.
  apply eq_sym in HeqX.
  apply Zeq_bool_eq in HeqX.
  subst.
  eexists;unfolds;simpl;eauto.

  remember (Zeq_bool OSQCreate f) as X1.
  destruct X1.
  apply eq_sym in HeqX1.
  apply Zeq_bool_eq in HeqX1.
  subst.
  eexists;unfolds;simpl;eauto.

  remember (Zeq_bool OSQDel f) as X2.
  destruct X2.
  apply eq_sym in HeqX2.
  apply Zeq_bool_eq in HeqX2.
  subst.
  eexists;unfolds;simpl;eauto.
  
  remember (Zeq_bool OSQPend f) as X3.
  destruct X3.
  apply eq_sym in HeqX3.
  apply Zeq_bool_eq in HeqX3.
  subst.
  eexists;unfolds;simpl;eauto.
  
  remember (Zeq_bool OSQPost f) as X4.
  destruct X4.
  apply eq_sym in HeqX4.
  apply Zeq_bool_eq in HeqX4.
  subst.
  eexists;unfolds;simpl;eauto.
  
  remember (Zeq_bool OSQGetMsg f) as X5.
  destruct X5.
  apply eq_sym in HeqX5.
  apply Zeq_bool_eq in HeqX5.
  subst.
  eexists;unfolds;simpl;eauto.

  remember (Zeq_bool OSSemAccept f) as X6.
  destruct X6.
  apply eq_sym in HeqX6.
  apply Zeq_bool_eq in HeqX6.
  subst.
  eexists;unfolds;simpl;eauto.

  remember (Zeq_bool OSSemCreate f) as X7.
  destruct X7.
  apply eq_sym in HeqX7.
  apply Zeq_bool_eq in HeqX7.
  subst.
  eexists;unfolds;simpl;eauto.

  remember (Zeq_bool OSSemDel f) as X8.
  destruct X8.
  apply eq_sym in HeqX8.
  apply Zeq_bool_eq in HeqX8.
  subst.
  eexists;unfolds;simpl;eauto.

  remember (Zeq_bool OSSemPend f) as X9.
  destruct X9.
  apply eq_sym in HeqX9.
  apply Zeq_bool_eq in HeqX9.
  subst.
  eexists;unfolds;simpl;eauto.

  remember (Zeq_bool OSSemPost f) as X10.
  destruct X10.
  apply eq_sym in HeqX10.
  apply Zeq_bool_eq in HeqX10.
  subst.
  eexists;unfolds;simpl;eauto.

  remember (Zeq_bool OSTimeDly f) as X11.
  destruct X11.
  apply eq_sym in HeqX11.
  apply Zeq_bool_eq in HeqX11.
  subst.
  eexists;unfolds;simpl;eauto.

  remember (Zeq_bool OSTimeGet f) as X12.
  destruct X12.
  apply eq_sym in HeqX12.
  apply Zeq_bool_eq in HeqX12.
  subst.
  eexists;unfolds;simpl;eauto.

  remember (Zeq_bool OSMboxCreate f) as X13.
  destruct X13.
  apply eq_sym in HeqX13.
  apply Zeq_bool_eq in HeqX13.
  subst.
  eexists;unfolds;simpl;eauto.

  remember (Zeq_bool OSMboxDel f) as X14.
  destruct X14.
  apply eq_sym in HeqX14.
  apply Zeq_bool_eq in HeqX14.
  subst.
  eexists;unfolds;simpl;eauto.

  remember (Zeq_bool OSMboxAccept f) as X15.
  destruct X15.
  apply eq_sym in HeqX15.
  apply Zeq_bool_eq in HeqX15.
  subst.
  eexists;unfolds;simpl;eauto.

  remember (Zeq_bool OSMboxPend f) as X16.
  destruct X16.
  apply eq_sym in HeqX16.
  apply Zeq_bool_eq in HeqX16.
  subst.
  eexists;unfolds;simpl;eauto.

  remember (Zeq_bool OSMboxPost f) as X17.
  destruct X17.
  apply eq_sym in HeqX17.
  apply Zeq_bool_eq in HeqX17.
  subst.
  eexists;unfolds;simpl;eauto.

  remember (Zeq_bool OSMutexAccept f) as X18.
  destruct X18.
  apply eq_sym in HeqX18.
  apply Zeq_bool_eq in HeqX18.
  subst.
  eexists;unfolds;simpl;eauto.
  
  remember (Zeq_bool OSMutexCreate f) as X19.
  destruct X19.
  apply eq_sym in HeqX19.
  apply Zeq_bool_eq in HeqX19.
  subst.
  eexists;unfolds;simpl;eauto.

  remember (Zeq_bool OSMutexDel f) as X20.
  destruct X20.
  apply eq_sym in HeqX20.
  apply Zeq_bool_eq in HeqX20.
  subst.
  eexists;unfolds;simpl;eauto.

  remember (Zeq_bool OSMutexPend f) as X21.
  destruct X21.
  apply eq_sym in HeqX21.
  apply Zeq_bool_eq in HeqX21.
  subst.
  eexists;unfolds;simpl;eauto.

  remember (Zeq_bool OSMutexPost f) as X22.
  destruct X22.
  apply eq_sym in HeqX22.
  apply Zeq_bool_eq in HeqX22.
  subst.
  eexists;unfolds;simpl;eauto.

  remember (Zeq_bool OSTaskCreate f) as X23.
  destruct X23.
  apply eq_sym in HeqX23.
  apply Zeq_bool_eq in HeqX23.
  subst.
  eexists;unfolds;simpl;eauto.

  remember (Zeq_bool OSTaskDel f) as X24.
  destruct X24.
  apply eq_sym in HeqX24.
  apply Zeq_bool_eq in HeqX24.
  subst.
  eexists;unfolds;simpl;eauto.
  
  tryfalse.
  
  simpljoin.
  unfolds in H.

  simpl in *;auto.
  remember (Zeq_bool OSQAccept f) as X.
  destruct X.
  apply eq_sym in HeqX.
  apply Zeq_bool_eq in HeqX.
  subst.
  eexists;unfolds;simpl;eauto.

  remember (Zeq_bool OSQCreate f) as X1.
  destruct X1.
  apply eq_sym in HeqX1.
  apply Zeq_bool_eq in HeqX1.
  subst.
  eexists;unfolds;simpl;eauto.

  remember (Zeq_bool OSQDel f) as X2.
  destruct X2.
  apply eq_sym in HeqX2.
  apply Zeq_bool_eq in HeqX2.
  subst.
  eexists;unfolds;simpl;eauto.
  
  remember (Zeq_bool OSQPend f) as X3.
  destruct X3.
  apply eq_sym in HeqX3.
  apply Zeq_bool_eq in HeqX3.
  subst.
  eexists;unfolds;simpl;eauto.
  
  remember (Zeq_bool OSQPost f) as X4.
  destruct X4.
  apply eq_sym in HeqX4.
  apply Zeq_bool_eq in HeqX4.
  subst.
  eexists;unfolds;simpl;eauto.
  
  remember (Zeq_bool OSQGetMsg f) as X5.
  destruct X5.
  apply eq_sym in HeqX5.
  apply Zeq_bool_eq in HeqX5.
  subst.
  eexists;unfolds;simpl;eauto.

  remember (Zeq_bool OSSemAccept f) as X6.
  destruct X6.
  apply eq_sym in HeqX6.
  apply Zeq_bool_eq in HeqX6.
  subst.
  eexists;unfolds;simpl;eauto.

  remember (Zeq_bool OSSemCreate f) as X7.
  destruct X7.
  apply eq_sym in HeqX7.
  apply Zeq_bool_eq in HeqX7.
  subst.
  eexists;unfolds;simpl;eauto.

  remember (Zeq_bool OSSemDel f) as X8.
  destruct X8.
  apply eq_sym in HeqX8.
  apply Zeq_bool_eq in HeqX8.
  subst.
  eexists;unfolds;simpl;eauto.

  remember (Zeq_bool OSSemPend f) as X9.
  destruct X9.
  apply eq_sym in HeqX9.
  apply Zeq_bool_eq in HeqX9.
  subst.
  eexists;unfolds;simpl;eauto.

  remember (Zeq_bool OSSemPost f) as X10.
  destruct X10.
  apply eq_sym in HeqX10.
  apply Zeq_bool_eq in HeqX10.
  subst.
  eexists;unfolds;simpl;eauto.

  remember (Zeq_bool OSTimeDly f) as X11.
  destruct X11.
  apply eq_sym in HeqX11.
  apply Zeq_bool_eq in HeqX11.
  subst.
  eexists;unfolds;simpl;eauto.

  remember (Zeq_bool OSTimeGet f) as X12.
  destruct X12.
  apply eq_sym in HeqX12.
  apply Zeq_bool_eq in HeqX12.
  subst.
  eexists;unfolds;simpl;eauto.

  remember (Zeq_bool OSMboxCreate f) as X13.
  destruct X13.
  apply eq_sym in HeqX13.
  apply Zeq_bool_eq in HeqX13.
  subst.
  eexists;unfolds;simpl;eauto.

  remember (Zeq_bool OSMboxDel f) as X14.
  destruct X14.
  apply eq_sym in HeqX14.
  apply Zeq_bool_eq in HeqX14.
  subst.
  eexists;unfolds;simpl;eauto.

  remember (Zeq_bool OSMboxAccept f) as X15.
  destruct X15.
  apply eq_sym in HeqX15.
  apply Zeq_bool_eq in HeqX15.
  subst.
  eexists;unfolds;simpl;eauto.

  remember (Zeq_bool OSMboxPend f) as X16.
  destruct X16.
  apply eq_sym in HeqX16.
  apply Zeq_bool_eq in HeqX16.
  subst.
  eexists;unfolds;simpl;eauto.

  remember (Zeq_bool OSMboxPost f) as X17.
  destruct X17.
  apply eq_sym in HeqX17.
  apply Zeq_bool_eq in HeqX17.
  subst.
  eexists;unfolds;simpl;eauto.

  remember (Zeq_bool OSMutexAccept f) as X18.
  destruct X18.
  apply eq_sym in HeqX18.
  apply Zeq_bool_eq in HeqX18.
  subst.
  eexists;unfolds;simpl;eauto.
  
  remember (Zeq_bool OSMutexCreate f) as X19.
  destruct X19.
  apply eq_sym in HeqX19.
  apply Zeq_bool_eq in HeqX19.
  subst.
  eexists;unfolds;simpl;eauto.

  remember (Zeq_bool OSMutexDel f) as X20.
  destruct X20.
  apply eq_sym in HeqX20.
  apply Zeq_bool_eq in HeqX20.
  subst.
  eexists;unfolds;simpl;eauto.

  remember (Zeq_bool OSMutexPend f) as X21.
  destruct X21.
  apply eq_sym in HeqX21.
  apply Zeq_bool_eq in HeqX21.
  subst.
  eexists;unfolds;simpl;eauto.

  remember (Zeq_bool OSMutexPost f) as X22.
  destruct X22.
  apply eq_sym in HeqX22.
  apply Zeq_bool_eq in HeqX22.
  subst.
  eexists;unfolds;simpl;eauto.

  
  remember (Zeq_bool OSTaskCreate f) as X23.
  destruct X23.
  apply eq_sym in HeqX23.
  apply Zeq_bool_eq in HeqX23.
  subst.
  eexists;unfolds;simpl;eauto.

  
  remember (Zeq_bool OSTaskDel f) as X24.
  destruct X24.
  apply eq_sym in HeqX24.
  apply Zeq_bool_eq in HeqX24.
  subst.
  eexists;unfolds;simpl;eauto.
  
  tryfalse.

  unfolds in H.
  unfolds in H0.
  
  simpl in *;auto.
  remember (Zeq_bool OSQAccept f) as X.
  destruct X.
  apply eq_sym in HeqX.
  apply Zeq_bool_eq in HeqX.
  subst.
  inverts H;inverts H0;simpl;intuition auto.

  remember (Zeq_bool OSQCreate f) as X1.
  destruct X1.
  apply eq_sym in HeqX1.
  apply Zeq_bool_eq in HeqX1.
  subst.
  inverts H;inverts H0;simpl;intuition auto.

  remember (Zeq_bool OSQDel f) as X2.
  destruct X2.
  apply eq_sym in HeqX2.
  apply Zeq_bool_eq in HeqX2.
  subst.
  inverts H;inverts H0;simpl;intuition auto.
  
  remember (Zeq_bool OSQPend f) as X3.
  destruct X3.
  apply eq_sym in HeqX3.
  apply Zeq_bool_eq in HeqX3.
  subst.
  inverts H;inverts H0;simpl;intuition auto.
  
  remember (Zeq_bool OSQPost f) as X4.
  destruct X4.
  apply eq_sym in HeqX4.
  apply Zeq_bool_eq in HeqX4.
  subst.
  inverts H;inverts H0;simpl;intuition auto.
  
  remember (Zeq_bool OSQGetMsg f) as X5.
  destruct X5.
  apply eq_sym in HeqX5.
  apply Zeq_bool_eq in HeqX5.
  subst.
  inverts H;inverts H0;simpl;intuition auto.

  remember (Zeq_bool OSSemAccept f) as X6.
  destruct X6.
  apply eq_sym in HeqX6.
  apply Zeq_bool_eq in HeqX6.
  subst.
  inverts H;inverts H0;simpl;intuition auto.

  remember (Zeq_bool OSSemCreate f) as X7.
  destruct X7.
  apply eq_sym in HeqX7.
  apply Zeq_bool_eq in HeqX7.
  subst.
  inverts H;inverts H0;simpl;intuition auto.

  remember (Zeq_bool OSSemDel f) as X8.
  destruct X8.
  apply eq_sym in HeqX8.
  apply Zeq_bool_eq in HeqX8.
  subst.
  inverts H;inverts H0;simpl;intuition auto.

  remember (Zeq_bool OSSemPend f) as X9.
  destruct X9.
  apply eq_sym in HeqX9.
  apply Zeq_bool_eq in HeqX9.
  subst.
  inverts H;inverts H0;simpl;intuition auto.

  remember (Zeq_bool OSSemPost f) as X10.
  destruct X10.
  apply eq_sym in HeqX10.
  apply Zeq_bool_eq in HeqX10.
  subst.
  inverts H;inverts H0;simpl;intuition auto.

  remember (Zeq_bool OSTimeDly f) as X11.
  destruct X11.
  apply eq_sym in HeqX11.
  apply Zeq_bool_eq in HeqX11.
  subst.
  inverts H;inverts H0;simpl;intuition auto.
  
  remember (Zeq_bool OSTimeGet f) as X12.
  destruct X12.
  apply eq_sym in HeqX12.
  apply Zeq_bool_eq in HeqX12.
  subst.
  inverts H;inverts H0;simpl;intuition auto.

  remember (Zeq_bool OSMboxCreate f) as X13.
  destruct X13.
  apply eq_sym in HeqX13.
  apply Zeq_bool_eq in HeqX13.
  subst.
  inverts H;inverts H0;simpl;intuition auto.

  remember (Zeq_bool OSMboxDel f) as X14.
  destruct X14.
  apply eq_sym in HeqX14.
  apply Zeq_bool_eq in HeqX14.
  subst.
  inverts H;inverts H0;simpl;intuition auto.

  remember (Zeq_bool OSMboxAccept f) as X15.
  destruct X15.
  apply eq_sym in HeqX15.
  apply Zeq_bool_eq in HeqX15.
  subst.
  inverts H;inverts H0;simpl;intuition auto.

  remember (Zeq_bool OSMboxPend f) as X16.
  destruct X16.
  apply eq_sym in HeqX16.
  apply Zeq_bool_eq in HeqX16.
  subst.
  inverts H;inverts H0;simpl;intuition auto.

  remember (Zeq_bool OSMboxPost f) as X17.
  destruct X17.
  apply eq_sym in HeqX17.
  apply Zeq_bool_eq in HeqX17.
  subst.
  inverts H;inverts H0;simpl;intuition auto.

  remember (Zeq_bool OSMutexAccept f) as X18.
  destruct X18.
  apply eq_sym in HeqX18.
  apply Zeq_bool_eq in HeqX18.
  subst.
  inverts H;inverts H0;simpl;intuition auto.
  
  remember (Zeq_bool OSMutexCreate f) as X19.
  destruct X19.
  apply eq_sym in HeqX19.
  apply Zeq_bool_eq in HeqX19.
  subst.
  inverts H;inverts H0;simpl;intuition auto.

  remember (Zeq_bool OSMutexDel f) as X20.
  destruct X20.
  apply eq_sym in HeqX20.
  apply Zeq_bool_eq in HeqX20.
  subst.
  inverts H;inverts H0;simpl;intuition auto.

  remember (Zeq_bool OSMutexPend f) as X21.
  destruct X21.
  apply eq_sym in HeqX21.
  apply Zeq_bool_eq in HeqX21.
  subst.
  inverts H;inverts H0;simpl;intuition auto.

  remember (Zeq_bool OSMutexPost f) as X22.
  destruct X22.
  apply eq_sym in HeqX22.
  apply Zeq_bool_eq in HeqX22.
  subst.
  inverts H;inverts H0;simpl;intuition auto.


  remember (Zeq_bool OSTaskCreate f) as X23.
  destruct X23.
  apply eq_sym in HeqX23.
  apply Zeq_bool_eq in HeqX23.
  subst.
  inverts H;inverts H0;simpl;intuition auto.

  remember (Zeq_bool OSTaskDel f) as X24.
  destruct X24.
  apply eq_sym in HeqX24.
  apply Zeq_bool_eq in HeqX24.
  subst.
  inverts H;inverts H0;simpl;intuition auto.
  
  tryfalse.

  split;intros.
  simpljoin.
  destruct i.
  unfold int_spec.
  simpl;eauto.
  unfold os_interrupt in H.
  simpl in H.
  destruct i;tryfalse.
  unfold int_spec;simpl;eauto.
  simpljoin.
  unfolds in H.
  destruct i.
  simpl in H.
  unfold os_interrupt;simpl;eauto.
  simpl in H.
  destruct i.
  unfold os_interrupt.
  simpl;eauto.
  tryfalse.
Qed.


Lemma eqdom_internal_lh: EqDom os_internal Spec.
Proof.
  unfolds.
  intros.
  split;intros;simpljoin.
  unfold os_internal in H.
  unfold Spec.
  unfold OS_spec.
  destruct f;simpl in H;tryfalse.
  
  remember ( Zeq_bool OSIntExit (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  apply eq_sym in HeqHs.
  apply Zeq_bool_eq in HeqHs.
  subst.
  rewrite <- HeqHs.
  eexists;simpl;eauto.
  clear HeqHs.
  
  remember ( Zeq_bool OSTimeTick (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  apply eq_sym in HeqHs.
  apply Zeq_bool_eq in HeqHs.
  subst.
  rewrite <- HeqHs.
  eexists;simpl;eauto.
  clear HeqHs.
  
  remember ( Zeq_bool OS_EventTaskRdy (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  apply eq_sym in HeqHs.
  apply Zeq_bool_eq in HeqHs.
  subst.
  rewrite <- HeqHs.
  eexists;simpl;eauto.
  clear HeqHs.


  remember ( Zeq_bool OS_EventTaskWait (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  apply eq_sym in HeqHs.
  apply Zeq_bool_eq in HeqHs.
  subst.
  rewrite <- HeqHs.
  eexists;simpl;eauto.
  clear HeqHs.

  remember ( Zeq_bool OS_Sched (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  apply eq_sym in HeqHs.
  apply Zeq_bool_eq in HeqHs.
  subst.
  rewrite <- HeqHs.
  eexists;simpl;eauto.
  clear HeqHs.

  remember ( Zeq_bool OS_EventWaitListInit (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  apply eq_sym in HeqHs.
  apply Zeq_bool_eq in HeqHs.
  subst.
  rewrite <- HeqHs.
  eexists;simpl;eauto.
  clear HeqHs.

  remember ( Zeq_bool OS_EventRemove (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  apply eq_sym in HeqHs.
  apply Zeq_bool_eq in HeqHs.
  subst.
  rewrite <- HeqHs.
  eexists;simpl;eauto.
  clear HeqHs.

  remember ( Zeq_bool OS_EventSearch (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  apply eq_sym in HeqHs.
  apply Zeq_bool_eq in HeqHs.
  subst.
  rewrite <- HeqHs.
  eexists;simpl;eauto.
  clear HeqHs.

  
  remember ( Zeq_bool OS_TCBInit (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  apply eq_sym in HeqHs.
  apply Zeq_bool_eq in HeqHs.
  subst.
  rewrite <- HeqHs.
  eexists;simpl;eauto.
  clear HeqHs.

  remember ( Zeq_bool OS_IsSomeMutexOwner (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  apply eq_sym in HeqHs.
  apply Zeq_bool_eq in HeqHs.
  subst.
  rewrite <- HeqHs.
  eexists;simpl;eauto.
  clear HeqHs.
  
  tryfalse.
  
  unfold os_internal.
  unfold Spec in H.
  unfold OS_spec in H.
  destruct f;simpl in H;tryfalse.
  
  remember ( Zeq_bool OS_EventSearch (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  apply eq_sym in HeqHs.
  apply Zeq_bool_eq in HeqHs.
  subst.
  rewrite <- HeqHs.
  eexists;simpl;eauto.
  clear HeqHs.
  
  remember ( Zeq_bool  OS_EventRemove (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  apply eq_sym in HeqHs.
  apply Zeq_bool_eq in HeqHs.
  subst.
  rewrite <- HeqHs.
  eexists;simpl;eauto.
  clear HeqHs.
  
  remember ( Zeq_bool OS_EventTaskRdy (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  apply eq_sym in HeqHs.
  apply Zeq_bool_eq in HeqHs.
  subst.
  rewrite <- HeqHs.
  eexists;simpl;eauto.
  clear HeqHs.


  remember ( Zeq_bool OS_EventTaskWait (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  apply eq_sym in HeqHs.
  apply Zeq_bool_eq in HeqHs.
  subst.
  rewrite <- HeqHs.
  eexists;simpl;eauto.
  clear HeqHs.

  remember ( Zeq_bool OS_Sched (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  apply eq_sym in HeqHs.
  apply Zeq_bool_eq in HeqHs.
  subst.
  rewrite <- HeqHs.
  eexists;simpl;eauto.
  clear HeqHs.

  remember ( Zeq_bool OSIntExit (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  apply eq_sym in HeqHs.
  apply Zeq_bool_eq in HeqHs.
  subst.
  rewrite <- HeqHs.
  eexists;simpl;eauto.
  clear HeqHs.

  remember ( Zeq_bool OSTimeTick (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  apply eq_sym in HeqHs.
  apply Zeq_bool_eq in HeqHs.
  subst.
  rewrite <- HeqHs.
  eexists;simpl;eauto.
  clear HeqHs.

  remember ( Zeq_bool OS_EventWaitListInit (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  apply eq_sym in HeqHs.
  apply Zeq_bool_eq in HeqHs.
  subst.
  rewrite <- HeqHs.
  eexists;simpl;eauto.
  clear HeqHs.

  remember ( Zeq_bool OS_TCBInit (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  apply eq_sym in HeqHs.
  apply Zeq_bool_eq in HeqHs.
  subst.
  rewrite <- HeqHs.
  eexists;simpl;eauto.
  clear HeqHs.

  remember ( Zeq_bool OS_IsSomeMutexOwner (Z.pos p)) as Hs.
  destruct Hs.
  inverts H.
  apply eq_sym in HeqHs.
  apply Zeq_bool_eq in HeqHs.
  subst.
  rewrite <- HeqHs.
  eexists;simpl;eauto.
  clear HeqHs.
  
  tryfalse.
Qed.


Definition ucos_init S O:= 
  initst S O I OSLInv init_lg/\ eqdomSO S O.

Theorem ucos_toprule: TopRule low_level_os_code os_spec ucos_init.
Proof.
  unfold low_level_os_code.
  unfold os_spec.
  lets Hos:eqdomos_p.
  eapply top_rule with (I:=I) (Spec:=OS_spec) (lasrt:=OSLInv);eauto.
  constructors;eauto.
  unfolds.
  unfolds in Hos.
  simpljoin;auto.
  Focus 2.
  constructors;eauto.
  unfolds in Hos.
  unfolds.
  simpljoin;auto.
  intros.
  simpl in H, H0.
  destruct i; tryfalse.
  eapply timetickisr_proof;eauto.  (*TimeTick*)
  destruct i;tryfalse.
  eapply toyisr_proof;eauto.  (*Toy*)

  intros.
  simpl in H.
  unfold api_spec in *.
  destruct f;simpl in H;tryfalse.
  remember ( Zeq_bool OSQAccept (Z.pos p0)) as Hs.
  destruct Hs.
  unfold qaccapi in H.
  inverts H.
  apply eq_sym in HeqHs.
  apply Zeq_bool_eq in HeqHs.
  simpl in *.
  rewrite <- HeqHs in *.

  eapply OSQAccProof;eauto.
  remember ( Zeq_bool OSQCreate (Z.pos p0)) as Hs.
  destruct Hs.
  apply eq_sym in HeqHs0.
  apply Zeq_bool_eq in HeqHs0.
  simpl in *.
  rewrite <- HeqHs0 in *.
  inverts H.
  eapply OSQCreateProof;eauto.
  remember ( Zeq_bool OSQDel (Z.pos p0)) as Hs.
  destruct Hs.
  apply eq_sym in HeqHs1.
  apply Zeq_bool_eq in HeqHs1.
  unfolds get_afun.
  simpl in *.
  rewrite <- HeqHs1 in *.
  inverts H.

  eapply OSQDelProof;eauto.
  remember ( Zeq_bool OSQPend (Z.pos p0)) as Hs.
  destruct Hs.
  apply eq_sym in HeqHs2.
  apply Zeq_bool_eq in HeqHs2.
  unfolds get_afun.
  simpl in *.
  rewrite <- HeqHs2 in *.
  inverts H.
  
  eapply OSQPendRight;eauto.
  remember ( Zeq_bool OSQGetMsg (Z.pos p0)) as Hs.
  destruct Hs.
  apply eq_sym in HeqHs3.
  apply Zeq_bool_eq in HeqHs3.
  unfolds get_afun.
  simpl in *.
  rewrite <- HeqHs3 in *.
  inverts H.

  eapply OSQGetMsgProof;eauto.
  remember ( Zeq_bool OSQPost (Z.pos p0)) as Hs.
  destruct Hs.
  apply eq_sym in HeqHs4.
  apply Zeq_bool_eq in HeqHs4.
  unfolds get_afun.
  simpl in *.
  rewrite <- HeqHs4 in *.
  inverts H.

  eapply OSQPostProof;eauto.

  remember ( Zeq_bool OSTimeDly (Z.pos p0)) as Hs.
  destruct Hs.
  apply eq_sym in HeqHs5.
  apply Zeq_bool_eq in HeqHs5.
  unfolds get_afun.
  simpl in *.
  rewrite <- HeqHs5 in *.
  inverts H.

  eapply OSTimeDlyProof;eauto.

  remember ( Zeq_bool OSTimeGet (Z.pos p0)) as Hs.
  destruct Hs.
  apply eq_sym in HeqHs6.
  apply Zeq_bool_eq in HeqHs6.
  unfolds get_afun.
  simpl in *.
  rewrite <- HeqHs6 in *.
  inverts H.
  eapply OSTimeGetRight;eauto. 
  assert (vl = nil).
  unfold BuildPreA' in H0.
  unfold os_api in H0.
  simpl in H0.
  remember (rev vl) as Z.
  destruct Z;tryfalse.
  destruct vl;tryfalse.
  auto.
  simpl in HeqZ.
  destruct vl;simpl in HeqZ;tryfalse.
  subst vl;auto.
  
  unfold tmgetapi;auto.
  remember ( Zeq_bool OSSemAccept (Z.pos p0)) as Hs.
  destruct Hs.
  apply eq_sym in HeqHs7.
  apply Zeq_bool_eq in HeqHs7.
  unfolds get_afun.
  simpl in *.
  rewrite <- HeqHs7 in *.
  inverts H.

  eapply OSSemAccProof;eauto.
  
  remember ( Zeq_bool OSSemCreate (Z.pos p0)) as Hs.
  destruct Hs.
  apply eq_sym in HeqHs8.
  apply Zeq_bool_eq in HeqHs8.
  unfolds get_afun.
  simpl in *.
  rewrite <- HeqHs8 in *.
  inverts H.

  eapply OSSemCreProof;eauto.


  remember ( Zeq_bool OSSemDel (Z.pos p0)) as Hs.
  destruct Hs.
  apply eq_sym in HeqHs9.
  apply Zeq_bool_eq in HeqHs9.
  unfolds get_afun.
  simpl in *.
  rewrite <- HeqHs9 in *.
  inverts H.

  eapply OSSemDeleteProof;eauto.

  remember ( Zeq_bool OSSemPend (Z.pos p0)) as Hs.
  destruct Hs.
  apply eq_sym in HeqHs10.
  apply Zeq_bool_eq in HeqHs10.
  unfolds get_afun.
  simpl in *.
  rewrite <- HeqHs10 in *.
  inverts H.

  eapply OSSemPendProof;eauto.

  remember ( Zeq_bool OSSemPost (Z.pos p0)) as Hs.
  destruct Hs.
  apply eq_sym in HeqHs11.
  apply Zeq_bool_eq in HeqHs11.
  unfolds get_afun.
  simpl in *.
  rewrite <- HeqHs11 in *.
  inverts H.

  eapply OSSemPostProof;eauto.

  remember ( Zeq_bool  OSMboxCreate (Z.pos p0)) as Hs.
  destruct Hs.
  apply eq_sym in HeqHs12.
  apply Zeq_bool_eq in HeqHs12.
  unfolds get_afun.
  simpl in *.
  rewrite <- HeqHs12 in *.
  inverts H.

  eapply MboxCreateProof;eauto.

  
  remember ( Zeq_bool  OSMboxDel (Z.pos p0)) as Hs.
  destruct Hs.
  apply eq_sym in HeqHs13.
  apply Zeq_bool_eq in HeqHs13.
  unfolds get_afun.
  simpl in *.
  rewrite <- HeqHs13 in *.
  inverts H.

  eapply MboxDelProof;eauto.
  
   
  remember ( Zeq_bool  OSMboxAccept (Z.pos p0)) as Hs.
  destruct Hs.
  apply eq_sym in HeqHs14.
  apply Zeq_bool_eq in HeqHs14.
  unfolds get_afun.
  simpl in *.
  rewrite <- HeqHs14 in *.
  inverts H.

  eapply MboxAcceptProof;eauto.

  remember ( Zeq_bool  OSMboxPend (Z.pos p0)) as Hs.
  destruct Hs.
  apply eq_sym in HeqHs15.
  apply Zeq_bool_eq in HeqHs15.
  unfolds get_afun.
  simpl in *.
  rewrite <- HeqHs15 in *.
  inverts H.

  eapply MboxPendProof;eauto.

  remember ( Zeq_bool OSMboxPost (Z.pos p0)) as Hs.
  destruct Hs.
  apply eq_sym in HeqHs16.
  apply Zeq_bool_eq in HeqHs16.
  unfolds get_afun.
  simpl in *.
  rewrite <- HeqHs16 in *.
  inverts H.

  eapply MboxPostProof;eauto.
  
   
  remember ( Zeq_bool OSMutexCreate (Z.pos p0)) as Hs.
  destruct Hs.
  apply eq_sym in HeqHs17.
  apply Zeq_bool_eq in HeqHs17.
  unfolds get_afun.
  simpl in *.
  rewrite <- HeqHs17 in *.
  inverts H.

  eapply OSMutexCreateRight;eauto.
  
   
  remember ( Zeq_bool OSMutexDel (Z.pos p0)) as Hs.
  destruct Hs.
  apply eq_sym in HeqHs18.
  apply Zeq_bool_eq in HeqHs18.
  unfolds get_afun.
  simpl in *.
  rewrite <- HeqHs18 in *.
  inverts H.
  
 
  eapply OSMutexDelRight;eauto.
  

     
  remember ( Zeq_bool OSMutexAccept (Z.pos p0)) as Hs.
  destruct Hs.
  apply eq_sym in HeqHs19.
  apply Zeq_bool_eq in HeqHs19.
  unfolds get_afun.
  simpl in *.
  rewrite <- HeqHs19 in *.
  inverts H.
 
  eapply OSMutexAccepteRight;eauto.

       
  remember ( Zeq_bool OSMutexPend (Z.pos p0)) as Hs.
  destruct Hs.
  apply eq_sym in HeqHs20.
  apply Zeq_bool_eq in HeqHs20.
  unfolds get_afun.
  simpl in *.
  rewrite <- HeqHs20 in *.
  inverts H.
 
  eapply OSMutexPendProof;eauto.

  remember ( Zeq_bool OSMutexPost (Z.pos p0)) as Hs.
  destruct Hs.
  apply eq_sym in HeqHs21.
  apply Zeq_bool_eq in HeqHs21.
  unfolds get_afun.
  simpl in *.
  rewrite <- HeqHs21 in *.
  inverts H.
 
  eapply OSMutexPostRight;eauto.

  
  remember ( Zeq_bool OSTaskCreate (Z.pos p0)) as Hs.
  destruct Hs.
  apply eq_sym in HeqHs22.
  apply Zeq_bool_eq in HeqHs22.
  unfolds get_afun.
  simpl in *.
  rewrite <- HeqHs22 in *.
  inverts H.

  eapply TaskCreateProof;eauto.

  remember ( Zeq_bool OSTaskDel (Z.pos p0)) as Hs.
  destruct Hs.
  apply eq_sym in HeqHs23.
  apply Zeq_bool_eq in HeqHs23.
  unfolds get_afun.
  simpl in *.
  rewrite <- HeqHs23 in *.
  inverts H.

  eapply TaskDeleteProof;eauto.

  
  inverts H.



  (*internel funs*)
  constructors.
  apply eqdom_internal_lh.
  intros.

  unfold OS_spec in H.
  simpl in H.  
  remember (Zeq_bool OS_EventSearch f) as Hx.
  destruct Hx;tryfalse.
  inverts H.
  apply eq_sym in HeqHx.
  apply Zeq_bool_eq in HeqHx.
  subst.
  do 3 eexists.
  splits.
  
  unfold os_internal.
  simpl.
  auto.
  simpl;auto.
  simpl;auto.

  intros.
  lets Hx:OSEventSearch_proof H H0.
  simpljoin.
  unfold os_internal in H1.
  simpl in H1.
  inverts H1.
  auto.

  remember (Zeq_bool OS_EventRemove f) as Hx.
  destruct Hx;tryfalse.
  inverts H.
  apply eq_sym in HeqHx0.
  apply Zeq_bool_eq in HeqHx0.
  subst.
  do 3 eexists.
  splits.
  
  unfold os_internal.
  simpl.
  auto.
  simpl;auto.
  simpl;auto.

  intros.
  lets Hx:OSEventRemove_proof H H0.
  simpljoin.
  unfold os_internal in H1.
  simpl in H1.
  inverts H1.
  auto.

  remember (Zeq_bool OS_EventTaskRdy f) as Hx.
  destruct Hx;tryfalse.
  inverts H.
  apply eq_sym in HeqHx1.
  apply Zeq_bool_eq in HeqHx1.
  subst.
  do 3 eexists.
  splits.
  
  unfold os_internal.
  simpl.
  auto.
  simpl;auto.
  simpl;auto.

  intros.
  lets Hx:OSEventTaskRdy_proof H H0.
  simpljoin.
  unfold os_internal in H1.
  simpl in H1.
  inverts H1.
  auto.

  remember (Zeq_bool OS_EventTaskWait f) as Hx.
  destruct Hx;tryfalse.
  inverts H.
  apply eq_sym in HeqHx2.
  apply Zeq_bool_eq in HeqHx2.
  subst.
  do 3 eexists.
  splits.
  
  unfold os_internal.
  simpl.
  auto.
  simpl;auto.
  simpl;auto.
 
  intros.
  lets Hx:OSEventTaskWait_proof H H0.
  simpljoin.
  unfold os_internal in H1.
  simpl in H1.
  inverts H1.
  auto.


  remember (Zeq_bool OS_Sched f) as Hx.
  destruct Hx;tryfalse.
  inverts H.
  apply eq_sym in HeqHx3.
  apply Zeq_bool_eq in HeqHx3.
  subst.
  do 3 eexists.
  splits.
  
  unfold os_internal.
  simpl.
  auto.
  simpl;auto.
  simpl;auto.

  intros.
  lets Hx:OSSched_proof H H0.
  simpljoin.
  unfold os_internal in H1.
  simpl in H1.
  inverts H1.
  auto.

  remember (Zeq_bool OSIntExit f) as Hx.
  destruct Hx;tryfalse.
  inverts H.
  apply eq_sym in HeqHx4.
  apply Zeq_bool_eq in HeqHx4.
  subst.
  do 3 eexists.
  splits.
  unfold os_internal.
  simpl.
  auto.
  simpl;auto.
  simpl;auto.

  intros.
  lets Hx:OSIntExit_proof H H0.
  simpljoin.
  unfold os_internal in H1.
  simpl in H1.
  inverts H1.
  auto.

  remember (Zeq_bool OSTimeTick f) as Hx.
  destruct Hx;tryfalse.
  inverts H.
  apply eq_sym in HeqHx5.
  apply Zeq_bool_eq in HeqHx5.
  subst.
  do 3 eexists.
  splits.
  
  unfold os_internal.
  simpl.
  auto.
  simpl;auto.
  simpl;auto.

  intros.
  lets Hx:OSTimeTick_proof H H0.
  simpljoin.
  unfold os_internal in H1.
  simpl in H1.
  inverts H1.
  auto.

  remember (Zeq_bool OS_EventWaitListInit f) as Hx.
  destruct Hx;tryfalse.
  inverts H.
  apply eq_sym in HeqHx6.
  apply Zeq_bool_eq in HeqHx6.
  subst.
  do 3 eexists.
  splits.
  
  unfold os_internal.
  simpl.
  auto.
  simpl;auto.
  simpl;auto.

  intros.
  lets Hx:OSEventWaitListInit_proof H H0.
  simpljoin.
  unfold os_internal in H1.
  simpl in H1.
  inverts H1.
  auto.


  remember (Zeq_bool OS_TCBInit f) as Hx.
  destruct Hx;tryfalse.
  inverts H.
  apply eq_sym in HeqHx7.
  apply Zeq_bool_eq in HeqHx7.
  subst.
  do 3 eexists.
  splits.
  
  unfold os_internal.
  simpl.
  auto.
  simpl;auto.
  simpl;auto.

  intros.
  lets Hx:OSTCBInit_proof H H0.
  simpljoin.
  unfold os_internal in H1.
  simpl in H1.
  inverts H1.
  auto.

  
  remember (Zeq_bool OS_IsSomeMutexOwner f) as Hx.
  destruct Hx;tryfalse.
  inverts H.
  apply eq_sym in HeqHx8.
  apply Zeq_bool_eq in HeqHx8.
  subst.
  do 3 eexists.
  splits.
  
  unfold os_internal.
  simpl.
  auto.
  simpl;auto.
  simpl;auto.

  intros.
  lets Hx:OSIsOwner_proof H H0.
  simpljoin.
  unfold os_internal in H1.
  simpl in H1.
  inverts H1.
  auto.
  
  unfolds.
  split;auto.
  apply GoodI_I.
Qed.

Theorem ucos_correct: GOOD_OS low_level_os_code os_spec ucos_init.
Proof.
  apply Soundness.
  apply ucos_toprule.
Qed.
