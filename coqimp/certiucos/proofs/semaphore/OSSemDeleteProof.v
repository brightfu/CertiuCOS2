(**************************  uc/OS-II  ****************************)
(*************************** OS_SEM.C *****************************)
(*****Proof of API Fucntion:  int8u OSSemDel(OS_EVENT* pevent) ****)
(***************************** Code: ******************************)
(*
Definition OSSemDel_impl :=
Int8u ·OSSemDel·(⌞pevent @ OS_EVENT∗⌟)··{
           ⌞
             tasks_waiting @ Int8u ;
             legal @ Int8u
           ⌟;

1            If (pevent′ ==ₑ NULL){
2                RETURN (OSSemDel) ′OS_ERR_PEVENT_NULL
            };ₛ
3            ENTER_CRITICAL;ₛ
4            legal′ =ᶠ OS_EventSearch(·pevent′·);ₛ
5            If (legal′ ==ₑ ′0){
6                EXIT_CRITICAL;ₛ
7                RETURN (OSSemDel) ′OS_ERR_PEVENT_NULL
            };ₛ
8            If (pevent′→OSEventType !=ₑ ′OS_EVENT_TYPE_SEM){
9                EXIT_CRITICAL;ₛ
10                RETURN (OSSemDel) ′OS_ERR_EVENT_TYPE 
            };ₛ
11            IF (pevent′→OSEventGrp !=ₑ ′0){
12                tasks_waiting′ =ₑ ′1
            }ELSE{
13                tasks_waiting′ =ₑ ′0
            };ₛ
14            IF (tasks_waiting′ ==ₑ ′0){
15                OS_EventRemove(­pevent′­);ₛ
16                pevent′→OSEventType =ₑ ′OS_EVENT_TYPE_UNUSED;ₛ
17                pevent′→OSEventListPtr =ₑ OSEventFreeList′;ₛ
18                OSEventFreeList′ =ₑ pevent′;ₛ
19                EXIT_CRITICAL;ₛ
20                RETURN (OSSemDel) ′OS_NO_ERR 
            }ELSE{
21                EXIT_CRITICAL;ₛ
22                RETURN (OSSemDel) ′OS_ERR_TASK_WAITING
            }
}·.
*)


Require Import sem_common.
Require Import semdel_pure.

Open Scope code_scope.

Lemma OSSemDeleteProof: 
  forall tid vl p r, 
    Some p =
    BuildPreA' os_api OSSemDel
              (semdel,(Tint8,Tptr os_ucos_h.OS_EVENT::nil)) vl OSLInv tid init_lg ->
    Some r =
    BuildRetA' os_api OSSemDel
              (semdel,(Tint8,Tptr os_ucos_h.OS_EVENT::nil)) vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api OSSemDel = Some (t, d1, d2, s) /\
      {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|} |- tid {{p}}s {{Afalse}}.
Proof.
  init_spec.

  (* L1 - L2 *)
  lzh_hoare_if.
  pure_auto.
  pure_auto.
  Hint Resolve noabs_oslinv.
  hoare abscsq; auto.
  eapply semdel_absimp_null; pauto.
  hoare forward.

  (* L3 *)
  hoare forward prim; pure_auto.

  (* L4 *)
  hoare_unfold.
  hoare forward.
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
  sep pauto.
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
  clear LHift_true.
  hoare abscsq; auto.
  eapply semdel_absimp_no_sem; pure_auto.
  eapply sem_H_get_none.
  eauto.
  eauto.
  hoare forward prim.
  sep pauto.
  pure_auto.
  
  hoare forward.
(**********************************************************************************)
(***********************************  legal == 1 **********************************)
  lzh_simpl_int_eq. tryfalse.

  hoare_split_pure_all.
  inverts H10; inverts H15; inverts H16.
  mytac.

  lzh_hoare_if.
  pure_auto.
  lzh_simpl_int_eq; tryfalse.

  clear Hif_false.
  hoare_unfold.
  lzh_hoare_if.
  pure_auto.
  pure_auto.
  pure_auto.
  transform_pre semacc_eventtype_neq_sem ltac:(sep cancel AEventData).

  hoare_split_pure_all.
  hoare abscsq; auto.
  eapply semdel_absimp_type_err; pure_auto.
  
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
  hoare_unfold.
  lzh_hoare_if.
  pure_auto. pure_auto.
  pure_auto.
  
  lzh_simpl_int_eq. subst.
  hoare forward.

  lzh_simpl_int_eq; subst.
  hoare forward.

(***********************  tasks_waiting = 1 *****************************)
  lzh_simpl_int_eq; subst.
  lzh_hoare_if;
  lzh_val_inj_simpl.
  pure_auto.
  lzh_simpl_int_eq; tryfalse.

  clear LHif_false.
  instantiate (1:=Afalse).
  
  transform_pre semacc_triangle_sem ltac:(sep cancel AEventData).
  hoare_split_pure_all.
  (* ** ac: Check sem_ecb_wt_ex_prop. *)
  assert (exists cnt' w wls', EcbMod.get v'35 (v'26, Int.zero) = Some (abssem cnt', w::wls')).
  {
    eapply sem_ecb_wt_ex_prop with (grp:=i); eauto.
    rewrite Int.eq_false; auto.
  }
  mytac.
  hoare abscsq; auto.
  eapply semdel_absimp_task_waiting; pure_auto.
  
  fold_AEventNode_r.
  compose_evsllseg.
  fold_AECBList.

  hoare forward prim.
  sep pauto.
  pure_auto.
  hoare forward.
  pure_auto.
  apply adisj_elim in H11.
  destruct H11; apply astar_comm in H11; apply astar_l_afalse_elim in H11; exact H11.

  apply adisj_elim in H11.
  destruct H11; apply astar_comm in H11; apply astar_l_afalse_elim in H11; exact H11.
  
(********************************  tasks_waiting == 0 **************************)
  lzh_simpl_int_eq; subst.
  transform_pre semacc_triangle_sem ltac:(sep cancel AEventData).
  hoare_split_pure_all.
  mytac.

  lzh_hoare_if;
  pure_auto;
  lzh_val_inj_simpl;
  lzh_simpl_int_eq; tryfalse.

  clear LHif_true.
  instantiate (1:=Afalse).
  hoare_unfold.
  hoare forward.
  
  sep cancel Aie; sep cancel Ais; sep cancel Acs; sep cancel Aisr.
  match goal with
    | H : ECBList_P ?p Vnull (?ectrl1 ++ ?ectrl2) (?msgqls1 ++ ?msgqls2) ?mqls ?tcbls |- _ =>
       instantiate (6:=ectrl1);
        instantiate (5:=ectrl2);
        instantiate (4:=msgqls1);
        instantiate (3:=msgqls2)
  end.
  do 2 rewrite list_prop1.
  
  eapply evsllseg_merge; eauto.
  simpl.
  lets Heq : ecblistp_length_eq H2 H13.
  omega.
  sep cancel evsllseg.
  unfold evsllseg; fold evsllseg.
  unfold_msg.
  sep pauto.
  sep cancel evsllseg.
  sep cancel Astruct.
  sep cancel Aarray.
  sep pauto.
  eauto.
  eauto.
  pure_auto.
  pure_auto.
  split.
  auto.
  struct_type_match_solver.
  (*****)
  split.
  instantiate (1:= (v'26, Int.zero)).
  intros.
  subst.
  simpl evsllseg in H11.
  sep split in H11.
  mytac.
  intros.
  sep destroy H11.
  apply evsllseg_get_last_eq in H34; auto.
  auto.
  simpl; eauto.
  pure_auto.

  intros.
  sep auto.
  intros.
  sep auto.
  (*****)
  hoare_unfold.
  hoare forward.
  hoare_unfold.
  hoare_assert_pure (isptr v'26).
  seg_isptr.
  hoare forward.
  pure_auto.
  hoare forward.

  (****  ex critical ****)
  hoare_split_pure_all.
  inverts H11.

  assert (v'41 = nil \/ v'41 <> nil) as Hasrt by tauto.
  (*************** list head: v'41 == nil *********************)
  destruct Hasrt.
  lets Hf:H27 H11.
  mytac.
  simpl in H25.
  apply eq_sym in H25.
  apply length_zero_nil in H25.
  subst v'37.
  lets Hres : semdel_ecblist_ecbmod_get H2 ; eauto.
  mytac.
  unfold AEventData.
  hoare_split_pure_all.
  hoare_abscsq; auto.
  eapply semdel_absimp_succ.
  can_change_aop_solver.
  eauto.
  eauto.
  hoare forward prim.
  unfold AOSEventFreeList.
  unfold AOSQFreeList.
  unfold AOSQFreeBlk.
  unfold AECBList.
  sep pauto.
  rewrite nil_simp in H41.
  sep cancel evsllseg.
  unfold ecbf_sll.
  instantiate (2:=
                 ((V$OS_EVENT_TYPE_UNUSED
                    :: V$0 :: Vint32 i2 :: x5 :: x6 :: v'26 :: nil) :: v'1)).
  unfold_ecbfsll.
  sep pauto.
  sep cancel Astruct.
  sep cancel ecbf_sllseg.
  sep cancel Aarray.
  exact_s.
  simpl; auto.
  pure_auto.
  split; [auto | struct_type_match_solver].
  rewrite nil_simp.
  auto.

  eapply semdel_ecb_del_prop_RHhold; eauto.
  pure_auto.
  hoare forward.

(************************** v'41 <> nil *******************************)
  lets Hp : H36 H11.
  mytac.

  lets Hres : semdel_ecblist_ecbmod_get' H2; eauto.
  mytac.
  
  lets Hress : semdel_ecbjoin_sig_join H40 H41. 
  mytac.
  unfold AEventData.
  hoare_split_pure_all.
  hoare_abscsq; auto.
  eapply semdel_absimp_succ.
  can_change_aop_solver.
  eauto.  
  eauto.
  hoare forward prim.
  unfold AOSEventFreeList.
  unfold AOSQFreeList.
  unfold AOSQFreeBlk.
  unfold AECBList.
  sep pauto.
  sep cancel evsllseg.
  unfold ecbf_sll.
  instantiate (2:=
                 ((V$OS_EVENT_TYPE_UNUSED
                    :: V$0 :: Vint32 i2 :: x5 :: x6 :: v'26 :: nil) :: v'1)).
  unfold_ecbfsll.
  sep pauto.
  sep cancel Astruct.
  sep cancel ecbf_sllseg.
  sep cancel Aarray.
  exact_s.
  simpl; auto.
  unfolds; simpl; auto.
  split; [auto | struct_type_match_solver].
  eapply semdel_ecb_list_join_join ; eauto.
  eapply semdel_ecb_del_prop_RHhold; eauto.
  pure_auto.
  hoare forward.
  (***** succ case end ******)
  intros.
  
  apply adisj_elim in H11.
  destruct H11; apply astar_comm in H11; apply astar_l_afalse_elim in H11; exact H11.
Qed.
