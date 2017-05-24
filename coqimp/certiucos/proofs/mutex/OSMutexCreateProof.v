(**************************  uc/OS-II  ******************************) 
(*************************** OS_MUTEX.C *****************************) 
(****Proofs for API Fucntion:  OS_EVENT* OSMutexCreate(int8u prio)***) 
(***************************** Code: ********************************) 
(**
OS_EVENT∗ ·OSMutexCreate·(⌞prio @ Int8u⌟)··{
           ⌞pevent @ OS_EVENT∗⌟;

1          If (prio′ ≥ ′OS_LOWEST_PRIO)
           {                         
12              RETURN 〈OS_EVENT ∗〉 NULL
           };ₛ
13         ENTER_CRITICAL;ₛ
14         If (OSTCBPrioTbl′[prio′] !=ₑ NULL)
           {
15              EXIT_CRITICAL;ₛ
16              RETURN 〈OS_EVENT ∗〉 NULL               
           };ₛ                   
17         pevent′ =ₑ OSEventFreeList′;ₛ
18         If (OSEventFreeList′ !=ₑ NULL)
           {
19              OSEventFreeList′ =ₑ  〈OS_EVENT∗〉 OSEventFreeList′→OSEventListPtr
           };ₛ
20         IF (pevent′ !=ₑ NULL)
           {
21              OS_EventWaitListInit(­pevent′­);ₛ  
22              pevent′→OSEventType =ₑ ′OS_EVENT_TYPE_MUTEX;ₛ
23              pevent′→OSEventCnt  =ₑ ((〈Int16u〉prio′) ≪ ′8) |ₑ ′OS_MUTEX_AVAILABLE;ₛ  
24              pevent′→OSEventPtr  =ₑ NULL;ₛ
25              pevent ′ → OSEventListPtr =ₑ OSEventList ′;ₛ
26              OSTCBPrioTbl′[prio′] =ₑ 〈OS_TCB ∗〉 PlaceHolder;ₛ
27              OSEventList′ =ₑ pevent′;ₛ
28              EXIT_CRITICAL;ₛ
29              RETURN pevent′          
            }
            ELSE
            {
30              EXIT_CRITICAL;ₛ
31              RETURN 〈OS_EVENT ∗〉 NULL
            }
 }·.
*) 
Require Import ucos_include.
Require Import os_ucos_h.
Require Import OSMutex_common.
Require Import mutex_absop_rules.
(*Require Import OSQPendPure.*)  
Local Open Scope code_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.


(*------------------- OS MUTEX Create -------------------------*)  


Theorem OSMutexCreateRight: 
  forall vl p r tid,
    Some p = BuildPreA' os_api OSMutexCreate mutexcreapi vl OSLInv tid init_lg->
    Some r = BuildRetA' os_api OSMutexCreate mutexcreapi vl OSLInv tid init_lg->
    exists t d1 d2 s,
      os_api OSMutexCreate = Some (t, d1, d2, s) /\ {| OS_spec, GetHPrio, OSLInv, I, r, Afalse |} |- tid {{ p }} s {{ Afalse }}.
Proof.
  init_spec.
  hoare unfold.
  hoare forward;  pauto.
  (* destruct (Int.ltu (Int.repr OS_LOWEST_PRIO) i).
   * intro; tryfalse.
   * intro; tryfalse.
   * destruct (Int.eq i (Int.repr OS_LOWEST_PRIO) ).
   * intro; tryfalse.
   * intro; tryfalse.
   * destruct (Int.ltu (Int.repr OS_LOWEST_PRIO) i); 
   * destruct (Int.eq i (Int.repr OS_LOWEST_PRIO) ).
   * intro; tryfalse.
   * intro; tryfalse.
   * intro; tryfalse.
   * intro; tryfalse. *)
  hoare unfold.
  hoare abscsq.
  apply noabs_oslinv.


  eapply mutexcre_error_absinfer.
  can_change_aop_solver.
  pauto.
  hoare forward.
  hoare forward .
  hoare unfold.
  assert  (Int.unsigned i < OS_LOWEST_PRIO).
  pauto.
  int auto.
  elim H; intros.
  int auto.
  int auto.
  elim H; intros.
  int auto.
  int auto.
  unfold OS_LOWEST_PRIO; omega.
  unfold OS_LOWEST_PRIO; omega.
  clear H.
  hoare forward prim.
  hoare unfold.
  unfold OS_LOWEST_PRIO in *.
  assert (rule_type_val_match OS_TCB ∗ (nth_val' (Z.to_nat (Int.unsigned i)) v'5) = true).
  Require Import symbolic_lemmas.
  apply array_type_vallist_match_imp_rule_type_val_match.
  rewrite H6.
  clear -H0.
  mauto.
  auto.
  hoare forward.

  math simpls.
  
  auto.
  
  unfolds in H7.
  clear -H7.
  remember ( nth_val' (Z.to_nat (Int.unsigned i)) v'5 ).
  destruct v; simpl; intro; tryfalse.
  destruct a; simpl in H; tryfalse.

  clear -H7.
  unfolds in H7.
  remember ( nth_val' (Z.to_nat (Int.unsigned i)) v'5 ).
  destruct v; simpl; intro; tryfalse.
  destruct a; simpl in H; tryfalse.

  hoare unfold.
  hoare forward prim.
  unfold AOSTCBPrioTbl.
  sep pauto.
  go.
  hoare abscsq.
  apply noabs_oslinv.
  apply  mutexcre_error_absinfer.
  go.
  math simpl.
  auto.
  hoare forward.
  hoare forward.
  hoare unfold.
  hoare forward.
  pauto.

  destruct v'0; hoare unfold.
  

  hoare unfold.
  hoare forward.
  (* intro; tryfalse.
   * intro; tryfalse. *)
  hoare unfold.
  false.
  int auto.
  hoare unfold.
  instantiate (1:=Afalse).
  hoare forward.
  hoare unfold.

  hoare forward.
  (* intro; tryfalse.
   * intro; tryfalse. *)
  hoare unfold; false.
  int auto.
  hoare unfold.
  hoare forward prim.
  sep_unfold.
  sep pauto.
  instantiate (3:=nil).
  unfold ecbf_sll.
  simpl ecbf_sllseg.
  

  sep pauto.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  eauto.

  auto.
  auto.
  go.

  hoare abscsq.
  apply noabs_oslinv.

  eapply  mutexcre_error_absinfer.
  can_change_aop_solver.
  math simpl.
  auto.
  hoare forward.
  instantiate (1:=Afalse) in H11.
  apply adisj_elim in H11.
  elim H11; intros; sep auto.

  (* succ *)  
  hoare unfold.
  hoare forward.
  (* intro; tryfalse.
   * intro; tryfalse. *)
  hoare forward.
  go.
  pauto.
  hoare forward.
  Focus 2.
  hoare_split_pure_all.
  clear -H11.
  false.
  elim H11; intros.
  int auto.
  int auto.


  hoare unfold.
  hoare forward.
  (* intro; tryfalse. *)

  Focus 2.
  hoare unfold.
  false.
  clear -H24.
  elim H24; intros; int auto.


  instantiate (1:=Afalse).

  hoare unfold.
  hoare forward.
  sep cancel Astruct.
  rewrite (@intlemma1 v'22 v'24); auto.
  sep cancel Aarray.
  sep cancel Aisr.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel 1%nat 1%nat.
  eauto.
  splits; eauto.
  go.
  intro.
  intros.
  sep pauto.
  sep cancel p_local.
  simpl ; auto.

  intro.
  intros.
  sep pauto.
  sep cancel p_local.
  simpl ; auto.
  hoare unfold.
  hoare forward.
  hoare forward.
  math simpls.
  change ( Int.ltu ($ 8) Int.iwordsize ) with true.
  (* simpl; intro; tryfalse. *)
  (* change ( Int.ltu ($ 8) Int.iwordsize ) with true. *)
  (* simpl; intro; tryfalse. *)
  hoare forward.
  hoare unfold.
  hoare forward.
  pauto.
  hoare unfold.
  unfold os_mutex.PlaceHolder.
  hoare forward.
  eapply forward_rule2.
  Local Open Scope list_scope.
  match goal with
  | |- {|_ ,_, _, _, _, _|}|- _ {{?P}}?x ′ [_] =ₑ _ {{_}} =>
   match find_dom_lenv P with
     | (none _, _) => fail
     | (some ?m, Some ?ls) =>
       let ret1 := constr:(var_notin_dom x ls) in
       let ret2 := eval compute in ret1 in
                                    match ret2 with
                                      | true =>
                                        match find_aop P with
                                          | none _ => assert (3=12)
                                          | some ?n =>
                                            match find_gvararray P x with
                                              | none _ => assert (1=11)
                                              | some ?o => 
                                                hoare lifts (n :: m :: o :: nil) pre;
                                                  eapply assign_rule_array_g_aop;
                                                  idtac(*
                                                  [ intro s; split; intro H; exact H
                                                  | simpl; auto
                                                  | symbolic
                                                      execution
                                                  | symbolic
                                                      execution
                                                  | intuition auto
                                                  | try omega
                                                  | apply
                                                      aux_for_hoare_lemmas.assign_type_match_true;
                                                    simpl; auto
                                                  | try omega ]*)  
                                            end
                                        end
                                      | false => assert (2=2)
                                    end
   end
  end.

  intro s.
  split.
  intro HHH.
  exact HHH.
  intro HHH; exact HHH.
  simpl; auto.

  2:symbolic execution.
  intros.
  sep normal; sep eexists.  eapply cast_rv_tptr.
  eapply addrof_gvar_rv.
  apply  astar_l_anotinlenv_intro.
  sep cancel 21%nat 1%nat.
  eauto.
  intro.
  apply astar_l_adomlenv_elim in H34.
  elim H34; intros.
  unfolds in H36.
  clear -H35 H36.
  unfolds in H35.
  simpljoin.
  destruct x.
  lets adfsadf: H36 OSPlaceHolder t.
  elim adfsadf; intros.
  assert (   ListSet.set_In (OSPlaceHolder, t)
                            ((prio, Int8u) :: (pevent, OS_EVENT ∗) :: nil)).
  apply H1.
  eexists; eauto.
  unfolds in H2.
  simpl in H2.
  elim H2; intros; tryfalse.
  elim H3; intros; tryfalse.
  auto.
  math simpls.
  tauto.
  clear -H0.
  bsimplr.
  omega.
  apply eq_vptr.
  do 2 eexists.
  splits; eauto.
  rewrite H6.
  clear -H0.
  bsimplr.
  omega.
  intro; intros.
  sep eexists.
  sep cancel p_local.
  simpl; auto.
  intro.
  intros.
  eauto.
  
  hoare_assert_pure ( EcbMod.get v'13 (v'25, Int.zero) = None).
  sep lifts (5::7::nil)%nat in H34.
  
  (* in OSQ *)  
  Require Import OSQCreatePure.
  lets Hs : ecblist_star_not_inh H27 H34.
  auto.


  hoare unfold.
  hoare forward.

  inverts H33.
  hoare abscsq.
  apply noabs_oslinv.
  eapply mutexcre_succ_absinfer.
  go.
  math simpl.
  auto.
  apply create_val_inj_lemma0 in H8.

  eapply mutex_createpure; eauto.

  unfold OS_LOWEST_PRIO.
  int auto.
  eauto.
  hoare forward prim.
  unfold AOSEventFreeList.
  unfold AECBList.
  unfold AOSTCBPrioTbl.
  unfold AECBList in H27.
  sep pauto.
  unfold ecbf_sll.
  sep cancel ecbf_sllseg.
  Local Open Scope int_scope.
  instantiate (4:=( (V$OS_EVENT_TYPE_MUTEX
                      :: Vint32 Int.zero ::  val_inj
                      (or
                         (val_inj
                            (if Int.ltu ($ 8) Int.iwordsize
                             then Some (Vint32 (i<<ᵢ$ 8))
                             else None)) (V$OS_MUTEX_AVAILABLE))
                      :: Vnull :: v'29 :: v'20 :: nil), INIT_EVENT_TBL) :: v'4).


  instantiate (3:= ( (DMutex (val_inj
                                (or
                                   (val_inj
                                      (if Int.ltu ($ 8) Int.iwordsize
                                       then Some (Vint32 (i<<ᵢ$ 8))
                                       else None)) (V$OS_MUTEX_AVAILABLE)))  Vnull) :: v'3)).
  unfold evsllseg; fold evsllseg.



  unfold AEventNode.
  unfold AEventData.
  unfold AMsgData.
  unfold AOSQCtr.
  unfold_msg.
  sep pauto.
  sep cancel evsllseg.
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel 3%nat 1%nat.
  sep cancel 3%nat 1%nat.
  eauto.
  unfolds; simpl; auto.
  apply RL_Tbl_init_prop.
  unfolds; simpl; auto.
  simpl.
  auto.
  unfolds.
  splits; try unfolds;
  math simpl; auto.
  go.
  clear -H0.
  unfold OS_MUTEX_AVAILABLE.
  mauto.


  eapply val_inj_eq' in H8.
  destruct H8.
  simpljoin.
  lets tmp:val_eq_some_not_zero H8 H36.
  apply R_PrioTbl_P_update_vhold; auto.
  apply RL_RTbl_PrioTbl_P_update_vhold;auto.

  eapply val_inj_eq' in H8.
  destruct H8.
  simpljoin.

  lets tmp:val_eq_some_not_zero H8 H36.
  auto.

  splits.
  rewrite array_type_vallist_match_is_all_elem_p.
  apply all_elem_hold_for_upd.
  rewrite <-  array_type_vallist_match_is_all_elem_p.
  auto.
  pauto.
  rewrite update_nth_val_len_eq.
  auto.

  eapply  ECBList_Mutex_Create_prop; eauto.
  apply create_val_inj_lemma0 in H8.
  lets aaa: nth_val'_imply_nth_val H8.
  rewrite H6.
  clear -H0.
  mauto.

  lets bbb: priotbl_null_no_tcb H5 aaa.

  eapply Mutex_Create_TCB_prop; eauto.
  pauto.
  
  hoare forward.
  instantiate (1:=Afalse) in H24.
  apply adisj_elim in H24.
  elim H24; intros; sep auto.
Qed.

