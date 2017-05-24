
(**************************  uc/OS-II  ******************************)
(*************************** OS_SEM.C *********************************)
(****Proofs for API Fucntion:  void* OSSemAccept(OS_EVENT* pevent)*****)
(************************C Source Code:******************************)
(** 
/*
*********************************************************************************************************
*                                           ACCEPT SEMAPHORE
*
* Description: This function checks the semaphore to see if a resource is available or, if an event
*              occurred.  Unlike OSSemPend(), OSSemAccept() does not suspend the calling task if the
*              resource is not available or the event did not occur.
*
* Arguments  : pevent     is a pointer to the event control block
*
* Returns    : >  0       if the resource is available or the event did not occur the semaphore is
*                         decremented to obtain the resource.
*              == 0       if the resource is not available or the event did not occur or,
*                         if 'pevent' is a NULL pointer or,
*                         if you didn't pass a pointer to a semaphore
*********************************************************************************************************
*/

#if OS_SEM_ACCEPT_EN > 0
INT16U  OSSemAccept (OS_EVENT *pevent)
{
    INT16U     cnt;
    BOOLEAN    legal;

1    if (pevent == (OS_EVENT * )0) {                 
2        return (0);
    }
3    OS_ENTER_CRITICAL();
4    legal = OS_EventSearch(pevent);
5    if (!legal)
    {
6        OS_EXIT_CRITICAL();
7        return (0);
    }
8    if (pevent->OSEventType != OS_EVENT_TYPE_SEM) {
9         OS_EXIT_CRITICAL();
10        return (0);
    }
11    cnt = pevent->OSEventCnt;
12    if (cnt > 0) {                                
13        --pevent->OSEventCnt;                    
    }
14    OS_EXIT_CRITICAL();
15    return (cnt);                               
}
***)
(* ** Ac: Print LoadPath. *)

Require Import sem_common.
Require Import semacc_pure.

(*
Lemma semacc_ecblist_P_compose_no_change: already exist ! 
*)

(* Hint Resolve gooda_qcc retpost_osev. *)
Open Scope code_scope.

Lemma OSSemAccProof: 
  forall tid vl p r, 
    Some p =
    BuildPreA' os_api OSSemAccept
               (semacc, (Tint16, Tptr os_ucos_h.OS_EVENT :: nil)) vl OSLInv tid init_lg ->
    Some r =
    BuildRetA' os_api OSSemAccept
               (semacc, (Tint16, Tptr os_ucos_h.OS_EVENT :: nil)) vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api OSSemAccept = Some (t, d1, d2, s) /\
      {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|} |- tid {{p}}s {{Afalse}}.
Proof.
  init_spec.
  (* L1 - L2 *)
  lzh_hoare_if; pure_auto.
  subst.
  hoare abscsq.
  Hint Resolve noabs_oslinv.
  auto.
  eapply semacc_absimp_null.
  auto. can_change_aop_solver.
  hoare forward.

  (* L3 *)
  hoare forward prim; pure_auto.

  (* L4 *)
  hoare unfold.
  hoare forward.
  instantiate (2:= semacc (Vptr x0 :: nil)).
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Aisr.
  sep cancel Acs.
  sep cancel tcbdllflag.
  sep cancel AECBList.
  sep cancel AOSRdyTblGrp.
  sep cancel AOSTCBList.
  sep cancel AOSTCBPrioTbl.
  sep cancel 1%nat 1%nat.
  exact_s.
  pure_auto.
  pure_auto.
  apply retpost_osev.
  intros.
  sep pauto.
  (* ** ac: Check disj_star_elim. *)
  sep destruct H2.
  apply adisj_elim in H2.
  destruct H2.
  sep auto.
  sep auto.

  intros.
  sep auto.
  
  hoare_split_pure_all.
  unfold OS_EventSearchPost.
  unfold OS_EventSearchPost'.
  unfold getasrt. (* getasrt is meaning of notation PRE *)
  eapply backward_rule1.
  intros.
  eapply disj_star_elim; eauto.


  (* 由于os_eventsearch(pevent)可能找到，也可能找不到，所以，这里就天然的要分成两种情况 *)
  hoare forward.
  
(************************************  legal == 0 **********************************)
  Focus 2. (* proof legal == 0 branch first *)
  hoare_split_pure_all.
  mytac.
  inverts H4; inverts H5; inverts H6.
  lzh_hoare_if.
  pure_auto.
  hoare abscsq.
  auto.
  eapply semacc_absimp_no_sem.
  can_change_aop_solver.
  eapply sem_H_get_none; auto.
  hoare forward; pauto.
  hoare forward prim.
  sep pauto.
  pure_auto.
  hoare forward.
  
(**********************************************************************************)
(***********************************  legal == 1 **********************************)
  lzh_simpl_int_eq; tryfalse.
  hoare_split_pure_all.
  inverts H10; inverts H15; inverts H16. 
  mytac.
  lzh_hoare_if.
  pure_auto.
  lzh_simpl_int_eq; tryfalse.

  hoare unfold.
  lzh_hoare_if.
  pure_auto.
  pure_auto.
  pure_auto.
  transform_pre semacc_eventtype_neq_sem ltac:(sep cancel AEventData).

  hoare_split_pure_all.
  hoare abscsq.
  auto.
  eapply semacc_absimp_no_sem; pauto.
  
(*********  exit critical ***********)
  fold_AEventNode_r.
  compose_evsllseg.
  fold_AECBList.

  hoare forward prim.
  sep pauto.
  pure_auto.
  hoare forward.
(*******************************  type != sem finished **********************)
(*******************************  type = sem ********************************)
  hoare unfold.
  lzh_simpl_int_eq; subst.
  clear Hif_false.
  hoare forward.
  (* pure_auto. *)
  struct_type_match_solver.
  lzh_hoare_if.
  pure_auto.
  pure_auto.
  hoare forward.
  (* pure_auto. *)
  struct_type_match_solver.
  pure_auto.
  
(***************************** cnt = 0 ****************************)
  Focus 2.
  apply semacc_ltu_zero_false in Hif_false.
  subst.

  transform_pre semacc_triangle_sem ltac:(sep cancel AEventData).
  hoare_split_pure_all.
  (* ** ac: Check eventsearch_after_get_H. *)
  
  assert (Hget:EcbMod.get v'35 (v'26, Int.zero) = Some v'46).
    eapply eventsearch_after_get_H; eauto.
  destruct H11 as [? [? ?]].
  subst.

  hoare abscsq.
  auto.
  eapply semacc_absimp_no_source; pauto.
  fold_AEventNode_r.
  compose_evsllseg.
  fold_AECBList.

  hoare forward prim.
  sep pauto.
  pure_auto.
  hoare forward.

(*************************************** cnt = 0 finished *****************************)
(*************************************** cnt > 0 **************************************)
  transform_pre semacc_triangle_sem ltac:(sep cancel AEventData).
  hoare_split_pure_all.
  mytac_H.

  assert (Hget: EcbMod.get v'35 (v'26, Int.zero) = Some (abssem i1, x)).
    eapply EcbMod.join_joinsig_get; eauto.

  hoare abscsq. auto.
  eapply semacc_absimp_succ; pauto. 

  transform_pre semacc_new_fundation ltac:(sep cancel AEventData).
  clear H5 H6.
  hoare_split_pure_all.
  fold_AEventNode_r.
  compose_evsllseg.
  lets Hnewjoin: ecb_get_set_join_join Hget H7 H10.
  destruct Hnewjoin as (ml1n & F1 & F2).
  assert (
      ECBList_P v'38 Vnull
                (v'22 ++
                      ((V$OS_EVENT_TYPE_SEM
                         :: Vint32 i :: Vint32 (i1-ᵢ$ 1):: x2 :: x3 :: v'42 :: nil, v'40) :: nil) ++
                      v'23) (v'24 ++ (DSem (i1-ᵢ$ 1) :: nil) ++ v'25) 
                (EcbMod.set v'35 (v'26, Int.zero) (abssem (i1-ᵢ$ 1), x)) v'36).
  eapply semacc_compose_EcbList_P; eauto.
  
  fold_AECBList.
  hoare forward prim.
  sep pauto.

  eapply semacc_RH_TCBList_ECBList_P_hold; eauto.
  pauto.
  
  hoare forward.
  pure_auto.
Qed.







  



