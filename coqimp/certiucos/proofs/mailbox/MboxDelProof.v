(**************************  uc/OS-II  ******************************)
(*************************** OS_MBOX.C ******************************)
(******Proof of API Fucntion:  Int8u OSMboxDel(OS_EVENT* pevent) ****)
(***************************** Code: ********************************)
(***
 Int8u ·OSMboxDel·(⌞ pevent @ OS_EVENT ∗⌟)··{
        ⌞ 
         tasks_waiting @ Int8u;
         legal @ Int8u
        ⌟; 
         
1        If (pevent′ ==ₑ  NULL)
         {
             RETURN  ′MBOX_DEL_NULL_ERR
2        };ₛ
3            ENTER_CRITICAL;ₛ
4        legal′ =ᶠ OS_EventSearch(·pevent′·);ₛ
5        If (legal′ ==ₑ ′0)
         {
6            EXIT_CRITICAL;ₛ
7            RETURN  ′MBOX_DEL_P_NOT_LEGAL_ERR
         };ₛ 
8        If (pevent′→OSEventType !=ₑ ′OS_EVENT_TYPE_MBOX)
         {
9            EXIT_CRITICAL;ₛ
10           RETURN  ′MBOX_DEL_WRONG_TYPE_ERR
         };ₛ  
11       IF (pevent′→OSEventGrp !=ₑ ′0)
         {
12           tasks_waiting′ =ₑ ′1
         }
         ELSE
         {
13           tasks_waiting′ =ₑ ′0
         };ₛ
14       IF (tasks_waiting′ ==ₑ ′0)
         {
15           OS_EventRemove(­pevent′­);ₛ
16           pevent′→OSEventType =ₑ ′OS_EVENT_TYPE_UNUSED;ₛ
17           pevent′→OSEventListPtr =ₑ OSEventFreeList′;ₛ
18           OSEventFreeList′ =ₑ pevent′;ₛ
19           EXIT_CRITICAL;ₛ
20           RETURN  ′MBOX_DEL_SUCC
         }
         ELSE
         {
21          EXIT_CRITICAL;ₛ
22          RETURN  ′MBOX_DEL_TASK_WAITING_ERR
         }   
}·.
}
 ***)
Require Import ucos_include.
Require Import Mbox_common.
Require Import os_ucos_h.
Require Import mbox_absop_rules.
Require Import sep_lemmas_ext.
(* Require Import OSQCreatePure. *)
Local Open Scope code_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.


Lemma MboxDelProof:
    forall  vl p r tid, 
      Some p =
      BuildPreA' os_api OSMboxDel mbox_delapi vl OSLInv tid init_lg->
      Some r =
      BuildRetA' os_api OSMboxDel mbox_delapi vl OSLInv tid init_lg->
      exists t d1 d2 s,
        os_api OSMboxDel = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|- tid {{p}}s {{Afalse}}.
Proof.
  intros.
  init_spec.

  hoare forward.
  pauto.
  pauto.

  hoare unfold.
  assert (x = Vnull).
  destruct x; simpl in *; tryfalse.
  auto.
  destruct a.
  simpl in *.
  tryfalse.
  subst.
  hoare abscsq.
  apply noabs_oslinv.

  apply absinfer_mbox_del_null_return.
  can_change_aop_solver.
  hoare forward.
  hoare forward.
  hoare unfold.
  assert (exists v, x= Vptr v) by pauto.
  simpljoin.

  hoare forward prim.
  (* pauto. *)
  hoare unfold.
  hoare forward.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Aisr.
  sep cancel Acs.
  sep cancel Aop.
  sep cancel tcbdllflag.
  sep cancel AECBList.
  sep cancel AOSTCBList.
  sep cancel AOSRdyTblGrp.
  sep cancel AOSTCBPrioTbl.
  eauto.
  go.
  go.

  exact retpost_osev.
  hoare unfold.
  Require Import linv_solver.
  linv_solver.
  linv_solver.
(* ** ac:   Locate "POST". *)
  unfold getasrt.
  unfold OS_EventSearchPost.
  unfold OS_EventSearchPost'.
  hoare_split_pure_all.
  eapply backward_rule1.
  intros;eapply disj_star_elim.
  eauto.
  hoare forward.

(* legal == 0 *)
  Focus 2.
  hoare unfold.
  hoare forward.
  (* destruct (Int.eq ($ 0) ($ 0)); intro; tryfalse. *)
  hoare_split_pure_all.
  inverts H7.
  hoare abscsq.
  apply noabs_oslinv.

  apply absinfer_mbox_del_p_not_legal_return.
  can_change_aop_solver.
  intro.
  simpljoin.
  rewrite H8 in H6.
  inversion H6.
  hoare unfold.
  hoare forward prim.
  eauto.
  pauto.
  hoare unfold.
  hoare forward.
  hoare forward.
  hoare unfold.
  assert (Int.eq ($ 0) ($ 0) = true).
  int auto.

  rewrite H6 in H5.
  false; destruct H5; intros.
  inversion H5.
  inversion H5.

  (* legal==1*)
  hoare unfold.
  hoare forward.
  (* destruct (Int.eq ($ 1) ($ 0)); intro; tryfalse. *)
  hoare unfold.
  false.
  int auto.
  hoare forward.
  instantiate (1 := Afalse).
  hoare unfold.
  false.
  int auto.

  hoare unfold.
  hoare forward.
  (* intro; tryfalse. *)
  struct_type_match_solver.

(* eapply struct_type_vallist_match_os_event; eauto.*)
  destruct (Int.eq i0 ($ OS_EVENT_TYPE_MBOX)); intro; tryfalse.
  destruct (Int.eq i0 ($ OS_EVENT_TYPE_MBOX)); intro; tryfalse.
  (* Type != MBOX *)
  hoare unfold.

  remember (Int.eq i0 ($ OS_EVENT_TYPE_MBOX)).
  destruct b;
  simpl in H12, H15, H19.
  clear -H12.
  assert (Int.notbool Int.one = Int.zero).
  int auto.
  rewrite H15 in H12.
  tryfalse.
  eapply backward_rule1.
  intros.
  sep lift 8%nat in H28.
  eapply eventtype_neq_mbox;
  eauto.
  hoare unfold.

  hoare_split_pure_all.
  inverts H17.

  hoare abscsq.
  apply noabs_oslinv.
  apply absinfer_mbox_del_wrong_type_return.
  can_change_aop_solver.
  lets Hge : EcbMod.join_joinsig_get H19 H8.
  eexists.
  splits.
  eauto.
  clear -H28 Hge.
  intro.
  simpljoin.
  rewrite Hge in H28.
  apply H28.
  eexists; eauto.

  hoare unfold; hoare forward prim.
  unfold AECBList.
  sep pauto.
  2: apply H3.

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
  go.
  unfolds; simpl; auto.
  pauto. 
  hoare forward.

  hoare forward.
   (* Type == MBOX *)
  hoare unfold.
  hoare forward.
  (* intro; tryfalse. *)
  go.
  destruct (Int.eq i ($ 0)); intro; tryfalse.
  destruct (Int.eq i ($ 0)); intro; tryfalse.
  hoare unfold.
  hoare forward.
  hoare forward.
  hoare unfold.
  hoare forward.
  (* tasks_wt = 1 *)


  hoare unfold.
  hoare forward.
  (* destruct (Int.eq ($ 1) ($ 0)); intro; tryfalse. *)


  hoare unfold.

  clear -H29.
  unfold Int.eq in H29.  
  repeat ur_rewriter_in H29.
  simpl in H29.
  tryfalse.

  inverts H17.
  hoare abscsq.
  apply noabs_oslinv.
  eapply absinfer_mbox_del_task_wt_return.
  can_change_aop_solver.
  
  eapply ecb_wt_ex_prop_mbox;
  [eapply l4;  eauto| eauto..].

  apply val_inj_eq in H12.
  subst i0.
  auto.

  hoare unfold.
  hoare forward prim.
  unfold AECBList.
  sep pauto.
  2:apply H3.
  rewrite list_prop1.
  rewrite list_prop1.
  eapply evsllseg_merge; eauto.
  lets Heq : ecblistp_length_eq H3 H14.
  simpl; auto.

  sep cancel 5%nat 1%nat.  
  unfold evsllseg; fold evsllseg.
  sep pauto.
  unfold AEventNode.
  unfold AOSEvent.
  unfold node.
  unfold AOSEventTbl.
  sep pauto.
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel 2%nat 1%nat.
  eauto.
  eauto.
  unfolds; simpl.
  auto.
  unfolds.
  auto.
  splits; auto.
  struct_type_match_solver.


  unfolds; simpl; auto.
  pauto.

  hoare forward.
  instantiate (1:=Afalse) in H29.
  simpl in H29.
  simpljoin.
  destruct H29; intros;
  simpljoin; tryfalse.


  (* task_wt == 0 *)
  hoare forward.
  (* destruct (Int.eq ($ 0) ($ 0)); intro; tryfalse. *)
  Focus 2.
  hoare unfold.
  false.
  assert (Int.eq ($ 0) ($ 0) = true).
  clear; int auto.
  rewrite H29 in H28.
  clear -H28.
  elim H28; intros.
  simpl in H.
  inversion H.
  simpl in H.
  inversion H.

  (* task_wt == 0 *)
  hoare unfold.
  apply val_inj_eq in H12.
  subst i0.
  apply l5 in H20.
  subst i.
  clear H30 H28 H29 H15.
  hoare unfold.
  inverts H17.
  hoare forward.
  instantiate (6:=v'22).
  instantiate (5:=  (
                    ((V$OS_EVENT_TYPE_MBOX :: V$0 :: Vint32 i1 :: x2 :: x3 :: v'42 :: nil,
                      v'40) :: v'23))).
  instantiate (4:=v'24).
  instantiate (3:=  (
                    (v'41 :: nil) ++ v'25)).


  rewrite list_prop1.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aisr.
  eapply evsllseg_merge.
  auto.
  simpl.
  lets Heq : ecblistp_length_eq H3 H14.
  auto.
  unfold evsllseg; fold evsllseg.
  sep pauto.
  unfold AEventNode.
  sep pauto.
  unfold AOSEvent.
  unfold node.
  unfold AOSEventTbl.
  sep pauto.
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel 3%nat 2%nat.
  sep cancel 3%nat 1%nat.
  eauto.


  eauto.
  unfolds; simpl; auto.
  auto.
  split; [ auto |struct_type_match_solver].
  unfolds; simpl; auto.
 
  2:auto.
  2: simpl; eauto.
  split; intros.

  sep destroy H12.
  subst v'22.
  simpl in H36.
  clear -H36.
  simpljoin.

  sep destroy H12.
  apply evsllseg_get_last_eq in H36; auto.

  pauto.
  linv_solver.
  linv_solver.

  hoare unfold.
  hoare forward.
  hoare unfold.
  hoare_assert_pure (isptr v'26).
  seg_isptr.
  hoare forward.
  clear -H28; pauto.
  hoare forward.
  inverts H12.

  destruct v'55.
  unfold AEventData.
  pure intro.
  unfold AEventData;  pure intro.
  2:   unfold AEventData;  pure intro.

  assert (v'48 = nil \/ v'48 <> nil) as Hasrt by tauto.
  destruct Hasrt.
  subst v'48.
  simpl in H20.
  apply eq_sym in H20.
  simpl in H4.
  simpljoin.

  lets Hres : ecblist_ecbmod_get_mbox H3 ; eauto.
  simpljoin.

  (* succ high level step*)
  hoare abscsq.
  apply noabs_oslinv.
  
  eapply  absinfer_mbox_del_succ_return .
  clear;can_change_aop_solver.

  exact H4.
  exact H12.
  hoare forward prim.
  unfold AOSEventFreeList.

  unfold AECBList.
  sep pauto.
  rewrite nil_simp in H28.
  sep cancel evsllseg.

  unfold ecbf_sll.
  instantiate (2:=( (V$OS_EVENT_TYPE_UNUSED
                      :: V$0
                      :: Vint32 i2 :: x4 :: x5 :: v'26 :: nil)) :: v'1).
  unfold_ecbfsll.
  sep pauto.
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel ecbf_sllseg.

  eauto.
  simpl; auto.
  unfolds; simpl; auto.
  split; [auto |   struct_type_match_solver].
  assert (v'52 = x6 /\ v'50 = nil).
  apply H29; auto.
  destruct H42; subst v'52.
  subst v'50.
  simpl; auto.

  eapply ecb_del_prop_RHhold; eauto.

  unfold AEventData.
  pauto.
  hoare forward.
  clear -H28; unfold AEventData in H28; sep auto.

  lets Hp : H38 H12.
  simpljoin.

  lets Hres : ecblist_ecbmod_get_mbox' H3; eauto.
  simpljoin.
  idtac.
  
  lets Hress : ecbjoin_sig_join' H33 H42. 
  simpljoin.
  hoare_abscsq.
  apply noabs_oslinv.

  eapply absinfer_mbox_del_succ_return.
  clear; can_change_aop_solver.
  eauto.  
  eauto.
  hoare forward prim.
  unfold AOSEventFreeList.
  unfold AECBList.
  sep pauto.
  sep cancel evsllseg.
  instantiate (2:=((V$OS_EVENT_TYPE_UNUSED
                     :: V$0
                     :: Vint32 i2 :: x4 :: x5 :: v'26 :: nil) ) :: v'1).
  unfold_ecbfsll.
  sep pauto.
  sep cancel Astruct.
  sep cancel ecbf_sllseg.
  sep cancel Aarray.
  eauto.
  simpl; auto.
  unfolds; simpl; auto.
  split; [auto |   struct_type_match_solver].
     
  eapply ecb_list_join_join ; eauto.
  eapply ecb_del_prop_RHhold; eauto.
  unfold AEventData.
  pauto.
  hoare forward.

  clear -H46; unfold AEventData in H46.
  sep auto.

  clear -H15.
  destruct H15.
  sep auto.
  sep auto.
  Grab Existential Variables.
  exact (V$ 0).
  exact Vundef.
  exact Vundef.
  exact ($ 0).
Qed.
