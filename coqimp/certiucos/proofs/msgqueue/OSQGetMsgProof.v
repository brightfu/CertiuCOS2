(**************************  uc/OS-II  ******************************)
(**************************** OS_Q.C ********************************)
(****************Proofs for API Fucntion:  void* OSQGetMsg()*********)
(**************************** Code:**********************************)
(*
void *OSQGetMsg()
{
         void * msg;
1        OS_ENTER_CRITICAL();
2        msg=  OSTCBCur->OSTCBMsg;
3        OSTCBCur->OSTCBMsg = (void * )0;
4        OS_EXIT_CRITICAL();
5        return msg;
}
*)
(*********************************************************************)
(*Modified by Ming 2015-3-30*)

Require Import ucos_include.
Require Import OSQGetMsgPure.
Require Import msgq_absop_rules.
Open Scope code_scope.

Lemma OSQGetMsgProof: 
  forall tid vl p r, 
    Some p = BuildPreA' os_api OSQGetMsg (getmsg, (Tptr Tvoid, nil)) vl OSLInv tid init_lg ->
    Some r = BuildRetA' os_api OSQGetMsg (getmsg, (Tptr Tvoid, nil)) vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api OSQGetMsg = Some (t, d1, d2, s) /\
      {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|}|-tid {{p}}s {{Afalse}}.
Proof.
  (*Initialize Specification*)
  init_spec.

  (*L1-L3: OS_ENTER_CRITICAL(); msg = OSTCBCur->OSTCBMsg; OSTCBCur->OSTCBMsg = (void * )0*)
  hoare forward prim; pauto.
  hoare unfold pre.
  hoare forward; pauto.
  hoare forward.

  (*L4: OS_EXIT_CRITICAL*)
  hoare unfold pre. 
  simpl in H8; simpljoin1; pure_intro.
  destruct x2; destruct p.
  assert (TcbMod.get v'14 (v'24, Int.zero) = Some (p, t, m)).
  eapply TcbMod.join_joinsig_get; eauto.
 
  hoare abscsq.
  apply noabs_oslinv.
  eapply OSQGetMsg_high_level_step; pauto.
(*  can_change_aop_solver. *)

(*prove the new inv hold*)
  assert (x6 = m).
  unfolds in H10; destruct H10.
  unfolds in H3; simpl in H3; inverts H3; auto.
  substs.

  hoare forward prim.
  sep_unfold.
  unfold AECBList in *.
  sep pauto.
  sep cancel Astruct.
  sep cancel dllseg.
  sep cancel dllseg.
  sep cancel evsllseg.
  sep cancel 1%nat 1%nat.
  sep cancel 3%nat 1%nat.
  sep lift 3%nat in H3.
  eapply tcbdllflag_hold.
  2: sep cancel 1%nat 1%nat.
  eapply tcbdllflag_hold_middle.
  simpl; splits;
    try solve [unfolds; simpl; auto].
  auto.
  eauto.
  
  eapply R_PrioTbl_P_msg; eauto.
  auto.
  eapply ECBList_P_msg; eauto.
  unfold TCBList_P; fold TCBList_P.
  exists (v'24, Int.zero) x0 x1 (p, t, Vnull).
  splits; pauto.
  eapply TcbMod.joinsig_set; eauto.
  eapply   TCBNode_P_msg.
  apply H10.
  eauto.
  eapply TcbMod.joinsig_set_set; eauto.
  pauto.
  pauto.
  splits; pauto.
  eapply RH_CurTCB_Prop; eauto.
  eapply RH_TCBList_ECBList_P_msg; eauto.
  pauto.

  (*L5: return msg;*) 
  hoare forward; pauto.
Qed.

Close Scope code_scope.
