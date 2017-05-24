(**************************  uc/OS-II  ******************************)
(*************************** OS_Q.C *********************************)
(*******Proofs for API Fucntion:  void* OSQDel(OS_EVENT *pevent)*****)
(**************************** Code: *********************************)
(* 
INT8U OSQDel(OS_EVENT *pevent)
{

    BOOLEAN    tasks_waiting;
    OS_Q      *pq;
    int8u      x;
    BOOLEAN    legal;
1   if (pevent == (OS_EVENT * )0)
    {
2        return(OS_ERR_PEVENT_NULL);
    }
3   OS_ENTER_CRITICAL();
4   legal = OS_EventSearch(pevent);
5   if (!legal)
    {
6       OS_EXIT_CRITICAL();
7       return (OS_ERR_EVENT_TYPE);
    }

8   if (pevent->OSEventType != OS_EVENT_TYPE_Q)
    {
9       OS_EXIT_CRITICAL();
10      return (OS_ERR_EVENT_TYPE);
    }

11  if (pevent->OSEventGrp != 0x00)
    {
12     tasks_waiting = TRUE;
    }
    else
    {
13    tasks_waiting = FALSE;
    }
14  if (tasks_waiting == FALSE)
    {	
        OS_EventRemove(pevent);	 
15      pq = (OS_Q * ) pevent->OSEventPtr;
16      (pq-> qfreeblk) ->nextblk = OSQFreeBlk;
17      OSQFreeBlk = (OS_Q_FREEBLK * )pq -> qfreeblk;
18      pq->OSQPtr = OSQFreeList;
19      OSQFreeList = pq;
20      pevent->OSEventType = OS_EVENT_TYPE_UNUSED;
21      pevent->OSEventPtr  = OSEventFreeList;
22      OSEventFreeList  = pevent;
23      OS_EXIT_CRITICAL();
24      return (OS_NO_ERR);
    }
    else
    {
25      OS_EXIT_CRITICAL();
26      return( OS_ERR_TASK_WAITING);
    }
}
*)
(*********************************************************)
Require Import  ucos_include.
Require Import OSQDelPure.

Open Scope code_scope.
Require Import absop_rules.
Open Scope int_scope.


Lemma OSQDelProof: 
  forall  tid vl p r, 
    Some p =
    BuildPreA' os_api OSQDel
               (qdel, (Tint8, Tptr os_ucos_h.OS_EVENT :: nil)) vl  OSLInv tid init_lg ->
    Some r =
    BuildRetA' os_api OSQDel
               (qdel, (Tint8, Tptr os_ucos_h.OS_EVENT :: nil)) vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api OSQDel = Some (t, d1, d2, s) /\
      {|OS_spec , GetHPrio,OSLInv,  I, r, Afalse|}|-tid {{p}}s {{Afalse}}.
Proof.
  init_spec.
  (*L1-L2*)
  hoare forward; pure_auto.
  hoare unfold pre.
  assert (x=Vnull) by pure_auto.
  subst x.
  hoare_abscsq.
  apply noabs_oslinv.
  eapply absinfer_qdel_err1_return.
  pure_auto.
  hoare forward.

  hoare forward.
  hoare unfold pre.
  assert (exists v, x= Vptr v) by pure_auto.
  simp join.

  (* encrit -----------------------L3 *)
  hoare forward prim.
  hoare unfold pre.
  hoare forward.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aisr.
  sep cancel AECBList.
  sep cancel AOSTCBList.
  sep cancel AOSRdyTblGrp.
  sep cancel  AOSTCBPrioTbl.  
  sep cancel tcbdllflag.
  sep cancel 1%nat 1%nat.
  eauto.
  pure_auto.
  pure_auto.
  apply retpost_osev.
  intros.
  sep destruct H3.
  destruct H3; sep auto.
  intros.
  sep auto.

  hoare unfold pre.
  (* hoare lift 2%nat pre. *)
  eapply backward_rule1.
  intros;eapply disj_star_elim.
  eauto.
  hoare forward.
  hoare unfold pre.
  inverts H17.
  hoare forward.
  pure_auto.
  hoare unfold pre.
  
  assert ( Int.eq ($ 1) ($ 0) = false ).
  int auto.
  instantiate (1:= Afalse).
  rewrite H16 in H11.
  simpl in H11.
  false.
  hoare forward.
  hoare unfold pre.
  hoare forward;pure_auto.
  hoare unfold pre.
  remember (Int.eq i0 ($ OS_EVENT_TYPE_Q)) as Heq.
  destruct Heq.
  apply eq_sym in HeqHeq.
  simpl in H12.
  assert (Int.notbool Int.one = Int.zero) as Hv.
  clear -x2.
  simpl; auto.
  rewrite Hv in H12.
  tryfalse.
  instantiate (1:=Afalse).
  hoare unfold pre.
  eapply backward_rule1.
  intros.
 
  sep lift 8%nat in H27.
  eapply eventtype_neq_q in H27; eauto.
  pure intro.
  hoare abscsq.
  apply noabs_oslinv.
  eapply absinfer_qdel_err3_return.
  can_change_aop_solver.
  lets Hge : EcbMod.join_joinsig_get H19 H8.
  eexists.
  splits; eauto.
  introv Hf.
  apply H27.
  simp join.
  do 3 eexists; eauto.
  hoare forward prim.
  unfold AECBList.
  sep pauto.
  2 : apply H3.
  rewrite list_prop1.
  rewrite list_prop1.
  eapply evsllseg_merge; eauto.
  lets Heq : ecblistp_length_eq H3 H14.
  simpl. 
  auto.
  unfold evsllseg; fold evsllseg.
  sep pauto.
  unfold AEventNode.
  unfold AOSEvent.
  unfold node.
  unfold AOSEventTbl.
  sep pauto.
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel 1%nat 2%nat.
  sep cancel 1%nat 1%nat.
  eauto.
  eauto.
  unfolds; simpl; auto.
  auto.
  splits;[reflexivity | pure_auto].
  unfolds; simpl; auto.
  pure_auto. 
  hoare forward.

  hoare forward.
  hoare unfold pre.
  hoare forward;pure_auto. 
  hoare unfold pre.
  hoare forward.
  hoare forward.
  hoare unfold pre.
  hoare forward.
  hoare unfold pre.
  hoare forward.
  pure_auto.
  instantiate (1:=Afalse).  
  2:instantiate (1:=Afalse).
  Focus 2.
  hoare unfold pre.
  hoare abscsq.
  apply noabs_oslinv.
  eapply  absinfer_qdel_err4_return.
  pure_auto.
  unfold ECBList_P in H3.
  fold ECBList_P in H3.
 
  apply val_inj_eq_q in H12.
  subst i0.
  
  eapply ecb_wt_ex_prop ;
    [eapply l4; eauto | eauto..].
  hoare forward prim.
  unfold AECBList.
  sep pauto.
  2 : apply H3.
  rewrite list_prop1.
  rewrite list_prop1.
  eapply evsllseg_merge; eauto.
  lets Heq : ecblistp_length_eq H3 H14.
  simpl. 
  auto.
  unfold evsllseg; fold evsllseg.
  sep pauto.
  unfold AEventNode.
  unfold AOSEvent.
  unfold node.
  unfold AOSEventTbl.
  sep pauto.
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel 2%nat 2%nat.
  sep cancel 2%nat 1%nat.      
  eauto.
  eauto.
  unfolds; simpl; auto.
  auto.
  splits;[reflexivity | pure_auto].
  unfolds; simpl; auto.
  pure_auto. 
  hoare forward.
  hoare unfold pre.
  rewrite Int.eq_false in H28.
  simpl in H28; tryfalse.
  auto.
  destruct H28;simpl in H28; simp join; tryfalse.
  hoare unfold pre.
  hoare forward.
  pure_auto.
  Focus 2.
  hoare unfold pre.
  rewrite Int.eq_true in H27.
  simpl in H27; destruct H27; tryfalse.
  instantiate (1:=Afalse).  
  Focus 2.
  rewrite Int.eq_true in H27.
  destruct H27.
  simpl in H27; simp join; tryfalse.
  sep split in H27.
  simpl in H28; destruct H28; tryfalse.
  hoare unfold pre.
  Focus 2.
  hoare unfold pre.
  inverts H7.
  hoare forward.
  pure_auto.
  hoare unfold pre.
  hoare abscsq.
  apply noabs_oslinv.
  eapply absinfer_qdel_err2_return.
  pure_auto.
  introv Hf.
  simp join.
  rewrite H8 in H9; tryfalse.
  hoare unfold pre.
  hoare forward prim.
  eauto.
  pure_auto.
  hoare forward.
  hoare forward.
  hoare unfold pre.
  rewrite Int.eq_true in H5.
  simpl in H5; destruct H5; tryfalse.
  apply val_inj_eq_q in H12.
  subst i0.
  apply l5 in H17.
  subst i.
  clear H27 H28 H29 H15.
  hoare unfold pre.
  hoare forward.
  instantiate (6:=v'24).
  instantiate (5:=  (
                    ((V$OS_EVENT_TYPE_Q :: V$0 :: Vint32 i1 :: x2 :: x3 :: v'44 :: nil,
                      v'42) :: v'25))).
  instantiate (4:=v'26).
  instantiate (3:=  (
                    (v'43 :: nil) ++ v'27)).
  instantiate (2:=qdel (Vptr (v'28, Int.zero) :: nil) ).
  rewrite list_prop1.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aisr.
  eapply evsllseg_merge; eauto.
  simpl.
  lets Heq : ecblistp_length_eq H3 H14.
  omega.
  sep cancel evsllseg.
  unfold evsllseg; fold evsllseg.
  unfold_msg.
  sep pauto.
  sep cancel evsllseg.
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel 1%nat 1%nat.
  eauto.
  simpl; auto.
  2:unfolds; simpl; eauto.
  auto.
  simpl; auto.
  split;[auto | pure_auto].
  (******)
  split.
  instantiate (1:= (v'28, Int.zero)).
  intros.
  subst.
  simpl evsllseg in H12.
  sep split in H12.
  simp join.
  intros.
  sep destroy H12.
  apply evsllseg_get_last_eq in H36; auto.
  auto.
  simpl; eauto.
  pure_auto.
  sep auto.
  sep auto.

  hoare unfold pre.
  clear H11.
  inverts H12.
  hoare forward.
  pure_auto.
  pure_auto.

  unfold AEventData.
  destruct v'57.
  hoare unfold pre.
  hoare forward.
  pure_auto.
  pure_auto.
  hoare unfold pre.
  hoare forward.
  pure_auto.
  hoare unfold pre.
  hoare forward.
  pure_auto.
  pure_auto.
  hoare unfold pre.
  hoare forward.
  pure_auto.
  hoare forward.
  hoare forward.
  hoare unfold pre.
  hoare forward.
  pure_auto.
  hoare forward.
  assert (v'50 = nil \/ v'50 <> nil) as Hasrt by tauto.
  destruct Hasrt.
  subst v'50.
  simpl in H27.
  apply eq_sym in H27.
  simp join.
  destruct H29; auto.
  simp join.
  lets Hres : ecblist_ecbmod_get H3 ; eauto.
  simp join.
  hoare_abscsq.
  apply noabs_oslinv.
  eapply absinfer_qdel_succ_return.
  pure_auto.
  eauto.
  eauto.
  hoare forward prim.
  unfold AOSEventFreeList.
  unfold AOSQFreeList.
  unfold AOSQFreeBlk.
  unfold AECBList.
  sep pauto.
  rewrite nil_simp in H53.
  sep cancel evsllseg.
  unfold qblkf_sll.
  instantiate (4:=   (v'24 :: x11 :: nil) :: v'5).
  unfold qblkf_sllseg; fold qblkf_sllseg.
  unfold node.
  sep pauto.
  sep cancel qblkf_sllseg.
  unfold os_inv.sll.
  instantiate (3:= ((v'28
                       :: x8
                       :: x
                       :: x0
                       :: x1
                       :: Vint32 i0
                       :: Vint32 i :: Vptr (v'27, Int.zero) :: nil)) :: v'4).
  unfold_sll.
  sep pauto.
  sep cancel sllseg.
  sep cancel 6%nat 1%nat.
  sep cancel 7%nat 1%nat.
  sep cancel 7%nat 1%nat.
  unfold ecbf_sll.
  instantiate (2:=( (V$OS_EVENT_TYPE_UNUSED
                      :: V$0
                      :: Vint32 i2 :: Vptr (v'25, Int.zero) :: x5 :: v'40 :: nil)) :: v'3).
  unfold_ecbfsll.
  sep pauto.
  sep cancel Astruct.
  sep cancel ecbf_sllseg.
  sep cancel Aarray.
  eauto.
  simpl; auto.
  unfolds; simpl; auto.
  split; [auto | pure_auto].
(*  pure_auto. *)
  unfolds; simpl; auto.
  split; [auto | pure_auto].
  simpl;auto.
  simpl; auto.
  split; [auto|pure_auto].
  auto.
  assert (v'39 = nil).
  destruct v'39; auto.
  simpl in H27; tryfalse.
  subst v'39.
  auto.
  eapply ecb_del_prop_RHhold; eauto.
  pure_auto.
  hoare forward.
  lets Hp : H38 H51.
  simp join.
  lets Hres : ecblist_ecbmod_get' H3; eauto.
  simp join.
  lets Hress : ecbjoin_sig_join H55 H56. 
  simp join.
  hoare_abscsq.
  apply noabs_oslinv.
  eapply absinfer_qdel_succ_return.
  pure_auto.
  eauto.
  eauto.
  hoare forward prim.
  unfold AOSEventFreeList.
  unfold AOSQFreeList.
  unfold AOSQFreeBlk.
  unfold AECBList.
  sep pauto.
  sep cancel evsllseg.
  unfold qblkf_sll.
  instantiate (4:=   (v'24 :: x11 :: nil) :: v'5).
  unfold qblkf_sllseg; fold qblkf_sllseg.
  unfold node.
  sep pauto.
  sep cancel qblkf_sllseg.
  unfold os_inv.sll.
  instantiate (3:= ( (v'28
                        :: x8
                        :: x
                        :: x0
                        :: x1
                        :: Vint32 i0
                        :: Vint32 i :: Vptr (v'27, Int.zero) :: nil) ) :: v'4).
  unfold_sll.
  sep pauto.
  sep cancel sllseg.
  sep cancel 6%nat 1%nat.
  sep cancel 7%nat 1%nat.
  sep cancel 7%nat 1%nat.
  unfold ecbf_sll.
  instantiate (2:=((V$OS_EVENT_TYPE_UNUSED
                     :: V$0
                     :: Vint32 i2 :: Vptr (v'25, Int.zero) :: x5 :: v'40 :: nil) ) :: v'3).
  unfold_ecbfsll.
  sep pauto.
  sep cancel Astruct.
  sep cancel ecbf_sllseg.
  sep cancel Aarray.
  eauto.
  simpl; auto.
  unfolds; simpl; auto.
  split; [auto | pure_auto].
  (* pure_auto. *)
  unfolds; simpl; auto.
  split; [auto | pure_auto].
  simpl;auto.
  simpl; auto.
  split; [auto|pure_auto].
  auto.
  eapply ecb_list_join_join ; eauto.
  eapply ecb_del_prop_RHhold; eauto.
  pure_auto.
  hoare forward.
  hoare unfold pre.
  hoare unfold pre.
  hoare unfold pre.
  Grab Existential Variables.
  exact Afalse.
Qed.
  
Close Scope code_scope.
Close Scope int_scope.
