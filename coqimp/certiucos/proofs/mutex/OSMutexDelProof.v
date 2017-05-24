(**************************  uc/OS-II  ******************************) 
(*************************** OS_MUTEX.C *****************************) 
(****Proof of API Fucntion:  OS_EVENT* OSMutexDel(OS_EVENT* pevent)**) 
(***************************** Code: ********************************) 
(**
 Int8u ·OSMutexDel·(⌞ pevent @ OS_EVENT ∗⌟)··{
        ⌞ 
         tasks_waiting @ Int8u;
         pip @ Int8u;
         legal @ Int8u
        ⌟; 
         
1       If (pevent′ ==ₑ  NULL)
        {
2            RETURN ′OS_ERR_PEVENT_NULL
        };ₛ
3       ENTER_CRITICAL;ₛ
4       legal′ =ᶠ OS_EventSearch(·pevent′·);ₛ
5       If (legal′ ==ₑ ′0)
        {
6           EXIT_CRITICAL;ₛ
7           RETURN ′OS_ERR_PEVENT_NO_EX
        };ₛ 
8       If (pevent′→OSEventType !=ₑ ′OS_EVENT_TYPE_MUTEX)
        {
9           EXIT_CRITICAL;ₛ
10          RETURN ′OS_ERR_EVENT_TYPE
        };ₛ  
11      IF (pevent′→OSEventGrp !=ₑ ′0   ||ₑ ( ( pevent′→OSEventCnt &ₑ ′OS_MUTEX_KEEP_LOWER_8  )!=ₑ  ′OS_MUTEX_AVAILABLE))
        {
12          tasks_waiting′ =ₑ ′1
        }ELSE{
13          tasks_waiting′ =ₑ ′0
        };ₛ
14      IF (tasks_waiting′ ==ₑ ′0)
        {
15          pip′ =ₑ 〈Int8u〉 (pevent′→OSEventCnt ≫ ′8);ₛ
16          If ( OSTCBPrioTbl′[pip′]  !=ₑ 〈OS_TCB ∗〉 PlaceHolder)
            {
17              EXIT_CRITICAL;ₛ
18              RETURN ′OS_ERR_MUTEXPR_NOT_HOLDER
            };ₛ
19          OS_EventRemove(­pevent′­);ₛ
20          OSTCBPrioTbl′[pip′] =ₑ NULL;ₛ
21          pevent′→OSEventType =ₑ ′OS_EVENT_TYPE_UNUSED;ₛ
22          pevent′→OSEventListPtr =ₑ OSEventFreeList′;ₛ
23          pevent′→OSEventCnt =ₑ ′0;ₛ                 
24          OSEventFreeList′ =ₑ pevent′;ₛ
25          EXIT_CRITICAL;ₛ
26          RETURN ′OS_NO_ERR
        }ELSE{
27          EXIT_CRITICAL;ₛ
28          RETURN ′OS_ERR_TASK_WAITING
        }    
 }· .
*) 
Require Import include_frm.
Require Import ucos_include.
Require Import OSMutex_common.
Require Import mutex_absop_rules.

Local Open Scope code_scope.


  
Theorem OSMutexDelRight: 
  forall vl p r tid,
    Some p = BuildPreA' os_api OSMutexDel mutexdelapi vl OSLInv tid init_lg ->
    Some r = BuildRetA' os_api OSMutexDel mutexdelapi vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api OSMutexDel = Some (t, d1, d2, s) /\ {| OS_spec, GetHPrio, OSLInv, I, r, Afalse |} |- tid {{ p }} s {{ Afalse }}.
Proof.
  init_spec.
  destruct x; unfolds in H1; elim H1; intros;simpljoin ; tryfalse.
  hoare unfold.
  hoare forward.
  (* intro; tryfalse. *)
  hoare abscsq.
  apply noabs_oslinv.

  apply mutexdel_null_absinfer.
  go.
  hoare forward.

  hoare forward.
  hoare unfold.

  false.
  clear -H.
  elim H; intros; tryfalse.
  
  hoare unfold.

  hoare forward.
  
  destruct x.
  simpl; intro; tryfalse.
  hoare unfold.
  destruct x.
  false.
  int auto.
  instantiate (1:=Afalse).
  hoare forward.


  hoare forward prim.
  hoare unfold.
  hoare forward.
  sep cancel Ais.
  sep cancel Aie.
  sep cancel Acs.
  sep cancel Aisr.
  sep cancel AECBList.
  sep cancel AOSTCBList.
  sep cancel tcbdllflag.
  sep cancel AOSRdyTblGrp.
  sep cancel AOSTCBPrioTbl.
  sep cancel 1%nat 1%nat.
  eauto.
  go.
  go.

  exact retpost_osev.
  Require Import linv_solver.
  linv_solver.
  linv_solver.
  (* intro; intros.
   * 
   * Require Import sep_lemmas_ext.
   * sep destruct H3.
   * rewrite disj_split in H3.
   * apply DisjPropE in H3.
   * destruct H3; intros.
   * sep normal in H3.
   * sep destruct H3.
   * sep eexists.
   * sep cancel p_local.
   * simpl; auto.
   * 
   * sep normal in H3.
   * sep destruct H3.
   * sep eexists.
   * sep cancel p_local.
   * simpl; auto. *)
  hoare unfold.
  eapply backward_rule1.
  intros;eapply disj_star_elim.
  eauto.
  hoare forward. 
  Focus 2.
  hoare unfold.
  hoare forward.
  (* intro. *)
  (* tryfalse. *)
  hoare_split_pure_all.
  inverts H7.
  hoare abscsq.
  apply noabs_oslinv.

  apply  mutexdel_no_mutex_err_absinfer; auto.
  go.
  hoare unfold.
  hoare forward prim.
  eauto.
  pauto.
  hoare unfold.
  hoare forward.
  hoare forward.
  hoare unfold.
  Local Open Scope int_scope.
  assert (Int.eq ($ 0) ($ 0) = true).
  int auto.

  rewrite H6 in H5.
  false; destruct H5; intros.
  inversion H5.
  inversion H5.

  (* legal==1*)  
  hoare unfold.
  hoare forward.
  (* intro. *)
  (* tryfalse. *)
  hoare unfold.
  false.
  int auto.
  hoare forward.
  hoare_split_pure_all.
  false.
  int auto.

  hoare unfold.
  hoare forward.
  (* intro; tryfalse. *)
  go.
  destruct (Int.eq i0 ($ OS_EVENT_TYPE_MUTEX)); simpl;intro;tryfalse.
  destruct (Int.eq i0 ($ OS_EVENT_TYPE_MUTEX)); simpl;intro;tryfalse.
  hoare unfold.

  remember (Int.eq i0 ($ OS_EVENT_TYPE_MUTEX)).
  destruct b;
  simpl in H12, H15, H20.
  clear -H12.
  assert (Int.notbool Int.one = Int.zero).
  int auto.
  rewrite H15 in H12.
  tryfalse.
  eapply backward_rule1.
  intros.
  sep lift 8%nat in H28.

  
  eapply eventtype_neq_mutex;
  eauto.
  hoare unfold.

  hoare_split_pure_all.
  inverts H17.

  hoare abscsq.
  apply noabs_oslinv.

  eapply mutexdel_type_err_absinfer.
  can_change_aop_solver.
  lets Hge : EcbMod.join_joinsig_get H19 H8.
  eauto.
  intro.
  apply H28.
  simpljoin.
  erewrite EcbMod.join_get_r; eauto.
  erewrite EcbMod.join_get_l; eauto.
  apply EcbMod.get_a_sig_a.
  go.


  hoare forward prim.
  unfold AECBList.
  sep pauto.
  2:eauto.
    rewrite list_prop1.
  rewrite list_prop1.
  eapply evsllseg_merge; eauto.
  lets Heq : ecblistp_length_eq H3 H14.
  simpl; auto.

  sep cancel 4%nat 1%nat.  
  unfold evsllseg; fold evsllseg.
  unfold AEventNode.
  unfold AOSEvent.
  unfold node.
  unfold AOSEventTbl.
  sep pauto.

  eauto.
  go.
  go.
  go.
  hoare forward.
  hoare forward.
  hoare unfold.

  hoare unfold.
  hoare forward.
  (* intro; tryfalse. *)
  go.
  destruct (Int.eq i ($ 0)); intro; tryfalse.
  destruct (Int.eq i ($ 0)); intro; tryfalse.
  (* intro; tryfalse. *)
  go.
  (* intro; tryfalse. *)
  destruct (Int.eq (i1&ᵢ$ OS_MUTEX_KEEP_LOWER_8) ($ OS_MUTEX_AVAILABLE)); intro; tryfalse.
  destruct (Int.eq (i1&ᵢ$ OS_MUTEX_KEEP_LOWER_8) ($ OS_MUTEX_AVAILABLE)); intro; tryfalse.
  destruct (Int.eq (i1&ᵢ$ OS_MUTEX_KEEP_LOWER_8) ($ OS_MUTEX_AVAILABLE)); destruct (Int.eq i ($ 0)); intro; tryfalse.
  hoare unfold.

  hoare forward.
  hoare forward.
  apply val_inj_eq in H12.
  subst i0.

  hoare forward.
  hoare unfold.
  (* task waiting = 1 *)  

  hoare forward.
  change (Int.eq ($ 1) ($ 0) ) with false.
  (* simpl; intro; tryfalse. *)

  hoare unfold.
  false.
  clear -H28.
  int auto.

  hoare unfold.
  inverts H17.

  unfold AEventData.
  destruct v'42; hoare_split_pure_all.
  unfolds in H29; inversion H29.
  unfolds in H17; inversion H17.  
  unfolds in H17; inversion H17.
  inverts H29.
  inverts H30.
  unfolds in H6.
  destruct v'47; tryfalse.
  destruct e; tryfalse.

  lets aaa: @inteq_has_value i ($ 0).
  lets bbb: @inteq_has_value  (i1&ᵢ$ OS_MUTEX_KEEP_LOWER_8)  ($ OS_MUTEX_AVAILABLE).
  simpljoin.
  rewrite H29 in H12.
  rewrite H30 in H12.

  apply  or_true_ltrue_rtrue in H12.
  destruct H12; intros.
  clear H15 H20 H28 H17.
  (* ex wt *)  

  Local Open Scope list_scope.


  assert (exists z zz t' tl,
            EcbMod.get v'36 (v'27, Int.zero) = Some (absmutexsem z zz, t' :: tl)).
  eapply ecb_wt_ex_prop_mutex.

  5:eauto.
  6:eauto.
  5:eauto.
  5:eauto.

  apply l4; eauto.
  rewrite H30.
  simpl; auto.

  auto.
  auto.
  auto.

  simpljoin.
  assert (EcbMod.get v'36 (v'27, Int.zero) = Some (absmutexsem i0 o, w)).
  eapply EcbMod.join_get_r; eauto.
  eapply EcbMod.join_get_l; eauto.
  apply EcbMod.get_a_sig_a.
  go.
  rewrite H15 in H12.
  inverts H12.
  lets ttt: mutex_ex_wt_ex_owner r.
  simpljoin.
  

  hoare abscsq.
  apply noabs_oslinv.

  eapply mutexdel_ex_wt_err_absinfer.


  go.
  exact H15.
  hoare forward prim.

  unfold AECBList.
  sep pauto.
  2:eauto.
  rewrite list_prop1.
  rewrite list_prop1.
  eapply evsllseg_merge; eauto.
  lets Heq : ecblistp_length_eq H3 H14.
  simpl; auto.

  sep cancel 4%nat 1%nat.  
  unfold evsllseg; fold evsllseg.
  unfold AEventNode.
  unfold AOSEvent.
  unfold node.
  unfold AOSEventTbl.
  sep pauto.
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel evsllseg.
  eauto.
  unfold AEventData.
  sep pauto.
  
  go.
  eauto.
  go.
  auto.
  go.
  go.
  hoare forward.
  clear H15 H20 H28 H17.
  (* ex owner but no wt *)  
  unfolds in m.
  simpljoin.
  inverts H12.
  assert ( x1&ᵢ$ OS_MUTEX_KEEP_LOWER_8 <> $ OS_MUTEX_AVAILABLE).
  intro.
  assert (  Int.eq (x1&ᵢ$ OS_MUTEX_KEEP_LOWER_8) ($ OS_MUTEX_AVAILABLE) = true).
  rewrite H12.
  apply Int.eq_true.
  rewrite H17 in H29.
  simpl in H29.
  unfold Int.notbool in H29; simpl in H29.
  unfold Int.eq in H29.
  unfold Int.one in H29.
  unfold Int.zero in H29.
  ur_rewriter_in H29.
  ur_rewriter_in H29.
  simpl in H29.
  inverts H29.
  unfold Int.zero in H6.
  apply H6; auto.
  apply H31 in H12.
  simpljoin.
  hoare abscsq.
  apply noabs_oslinv.

  eapply mutexdel_ex_wt_err_absinfer.
  go.
  eapply EcbMod.join_get_r; eauto.
  eapply EcbMod.join_get_l; eauto.
  apply EcbMod.get_a_sig_a.
  go.

  hoare forward prim.
  unfold AECBList.
  sep pauto.
  2:eauto.
  rewrite list_prop1.
  rewrite list_prop1.
  eapply evsllseg_merge; eauto.
  lets Heq : ecblistp_length_eq H3 H14.
  simpl; auto.

  sep cancel 4%nat 1%nat.  
  unfold evsllseg; fold evsllseg.
  unfold AEventNode.
  unfold AOSEvent.
  unfold node.
  unfold AOSEventTbl.
  sep pauto.
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel evsllseg.
  unfold AEventData.
  sep pauto.
  go.
  eauto.
  go.
  auto.
  go.
  go.
  hoare forward.

  instantiate (1:=Afalse) in H28.
  destruct H28; intros.
  sep auto.
  sep auto.

  hoare forward.
  change (Int.eq ($ 0) ($ 0)) with true.
  (* simpl; intro;tryfalse. *)
  Focus 2.
  hoare unfold.
  false.
  clear -H20.
  int auto.
  elim H20; intros; int auto.

  hoare unfold.

  hoare forward.
  (* intro; tryfalse. *)
  go.

  apply intlemma0.
  (* intro; tryfalse. *)
  inverts H17.
  unfold AEventData.
  destruct v'42; hoare_split_pure_all.
  false; clear -H30; unfolds in H30; tryfalse.
  false; clear -H17; unfolds in H17; tryfalse.
  false; clear -H17; unfolds in H17; tryfalse.
  inverts H30.
  inverts H31.

  unfolds in H6.
  destruct v'47;destruct e; try solve [clear -H6; tryfalse].
  simpljoin.
  unfolds in m.
  simpljoin.
  unfolds in r.
  simpljoin.
  inverts e.
  unfold AOSTCBPrioTbl.
  hoare_split_pure_all.
  destruct H33.

  assert ( exists t, nth_val (Z.to_nat (Int.unsigned (Int.shru x ($ 8)))) v'28 = Some t).
  apply ls_has_nth_val.
  rewrite H36.
  clear -H32.
  remember (Int.shru x ($ 8)).
  mauto.
  destruct H37.

  assert (isptr x0).

  assert ( (Z.to_nat (Int.unsigned (Int.shru x ($ 8)))) < 64)%nat.
  clear -H32.
  remember (Int.shru x ($ 8)).
  mauto.
  rewrite <- H36 in H38.
  Require Import symbolic_lemmas.
  lets bbb: array_type_vallist_match_imp_rule_type_val_match H38 H33.
  unfolds in bbb.
  lets bbbb: nth_val_nth_val'_some_eq H37.
  rewrite bbbb in bbb.
  clear -bbb.
  unfolds; auto.
  destruct x0.
  inversion bbb.
  left; auto.
  inversion bbb.
  right; eauto.


  hoare forward.

  hoare_split_pure_all.
  eapply ift_rule''.
  unfold os_mutex.PlaceHolder.
  intro.
  intros.
  eapply uop_rv; [ idtac | simpl; auto | auto | simpl; auto ].

  eapply bop_rv; [ sep_get_rv | idtac | simpl; auto | auto | simpl; auto ].

  Focus 5.
  eapply cast_rv_tptr.
  eapply addrof_gvar_rv.
  eapply dom_lenv_imp_notin_lenv.
  Local Open Scope list_scope.
  instantiate (1:=  ((pevent, os_ucos_h.OS_EVENT ∗)
                       :: (tasks_waiting, Int8u)
                       :: (pip, Int8u) :: (legal, Int8u) :: nil)).
  simpl.
  auto.
  sep auto.
  auto.

  apply del_intlemma1.
  auto.
  apply del_intlemma2.
  auto.
  rewrite H36.
  apply del_intlemma2.
  auto.

  rewrite mutexdel_intlemma1.
  apply array_type_vallist_match_imp_rule_type_val_match.
  rewrite H36.
  clear -H32.
  remember (Int.shru x ($ 8)).
  mauto.
  auto.
  auto.

  rewrite mutexdel_intlemma1.
  rewrite (nth_val_nth_val'_some_eq _ _ H37).
  clear -H38.
  unfolds in H38.
  elim H38; intros; simpljoin; subst ; pauto.
  simpl.
  destruct v'48; simpl; auto.
  (* intro; tryfalse. *)
  simpl.
  destruct x; destruct v'48.
  destruct ( peq b b0) ; destruct ( Int.eq i i0); intro; tryfalse.
  auto.
  auto.


  rewrite mutexdel_intlemma1.
  rewrite (nth_val_nth_val'_some_eq _ _ H37).

  clear -H38.
  unfolds in H38.
  elim H38; intros; simpljoin; subst ; pauto.
  simpl.
  destruct v'48; simpl; intro; tryfalse.
  simpl.
  destruct x; destruct v'48.
  destruct ( peq b b0) ; destruct ( Int.eq i i0); intro; tryfalse.
  auto.
  simpl.
  eauto.

  (* new return *) 
  hoare unfold.
  hoare abscsq.
  apply noabs_oslinv.
  eapply mutexdel_pr_not_holder_err_absinfer.
  go.
  hoare unfold.
  hoare forward prim.

  unfold AECBList.
  unfold AOSTCBPrioTbl.
  sep pauto.
  4:eauto.
  rewrite list_prop1.
  rewrite list_prop1.
  sep cancel 1%nat 1%nat.
  eapply evsllseg_merge; eauto.
  lets Heq : ecblistp_length_eq H3 H14.
  simpl; auto.

  sep cancel 5%nat 1%nat.  
  unfold evsllseg; fold evsllseg.
  unfold AEventNode.
  unfold AOSEvent.
  unfold node.
  unfold AOSEventTbl.
  sep pauto.
  sep cancel Astruct.
  sep cancel Aarray.
  unfold AEventData.
  sep pauto.
  sep cancel evsllseg.

  eauto.

  go.
  go.
  go.
  go.
  go.
  go.
  go.
  go.
  hoare forward.



  hoare unfold.
  hoare forward.
  hoare unfold.
  hoare forward.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aisr.
  (* after function call *) 


  4: simpl; eauto.
  sep cancel 1%nat 2%nat.
  instantiate (5:=v'23).
  instantiate (4:=  (
                    ((V$OS_EVENT_TYPE_MUTEX :: Vint32 i :: Vint32 x :: v0 :: x3 :: v'43 :: nil,
                      v'41) :: v'24))).
  instantiate (3:=v'25).
  instantiate (2:=  (
                    (DMutex (Vint32 x) v0  :: nil) ++ v'26)).

  rewrite list_prop1.
  eapply evsllseg_merge.
  auto.
  simpl.
  lets Heq : ecblistp_length_eq H3 H14.
  auto.
  unfold AEventData.
  unfold evsllseg; fold evsllseg.
  unfold AEventNode.
  unfold AOSEvent.
  unfold node.
  unfold AOSEventTbl.
  sep pauto.
  unfold AEventData.
  sep pauto.
  sep cancel Astruct.
  sep cancel Aarray.

  sep cancel 5%nat 1%nat.
  sep cancel 4%nat 1%nat.
  eauto.
  go.
  eauto.
  go.
  auto.
  go.
  eauto.
  2:auto.
  2:go.
  split; intros; sep destroy H39.
  subst v'23.
  simpl in H52.
  clear -H52; simpljoin.


  apply evsllseg_get_last_eq in H52; auto.
  {
    intro; intros.
    sep normal in H39.
    sep destruct H39.
    sep eexists.
    sep cancel p_local.
    simpl; auto.
  }

  linv_solver.
  (* right way *)  
  instantiate(1:=Afalse).
  hoare unfold.
  eapply seq_rule;[idtac|idtac].
  eapply forward_rule2;   [ idtac | first [ intros s H; exact H | sep pauto ] ].
  let s := fresh in
  let H := fresh in
  match goal with
    | |- {|_ ,_, _, _, _, _|}|- _ {{?P}}?x ′ [_] =ₑ _ {{_}} =>
      match find_lvararray P x with
        | some ?m => idtac 
        | none _ =>match find_dom_lenv P with
                     | (none _, _) => fail 2
                     | (some ?m, Some ?ls) =>
                       let ret1 := constr:(var_notin_dom x ls) in
                       let ret2 := eval compute in ret1 in
                           match ret2 with
                             | true =>
                               match find_aop P with
                                 | none _ => fail 1
                                 | some ?n =>
                                   match find_gvararray P x with
                                     | none _ => fail 3
                                     | some ?o =>
                                       hoare lifts (n :: m :: o :: nil) pre;
                                         eapply assign_rule_array_g_aop
                                   end
                               end
                             | false => fail
                           end
                   end
      end
  end.
  intros sss; split; intro HHH; exact HHH.
  simpl; auto.
  symbolic execution.
  symbolic execution.
  Focus 2.
  branch 1.
  auto.
  Focus 3.
  clear; pauto.
  apply assign_type_match_true.
  simpl; auto.

  apply del_intlemma1.
  auto.
  apply del_intlemma2.
  auto.

  rewrite H36.
  apply del_intlemma2; auto.
  {
    intro; intros.
    sep normal in H40.
    sep destruct H40.
    sep eexists.
    sep cancel p_local.
    simpl; auto.
  }


  hoare unfold.
  hoare forward.
  hoare unfold.
  hoare_assert_pure (isptr v'27).
  seg_isptr.
  hoare forward.
  pauto.
  hoare forward.
  hoare unfold.
  hoare forward.
  apply val_inj_bool_or_lemma0 in H12.
  elim H12; intros.
  apply val_inj_not_eq in H48.
  apply a in H48.
  simpljoin.
  assert (w=nil).
  apply H6; auto.
  subst w.
  assert (exists eee, EcbMod.join eee (EcbMod.sig (v'60, Int.zero) (absmutexsem (Int.shru x ($ 8)) None, nil)) v'36).
  assert (EcbMod.sub  (EcbMod.sig (v'60, Int.zero) (absmutexsem (Int.shru x ($ 8)) None, nil)) v'36).
  unfolds.
  intros.
  unfolds.
  unfolds in H48.
  eapply EcbMod.join_get_r; eauto.
  eapply EcbMod.join_get_l; eauto.


  lets aaa: EcbMod.sub_exists_join H48.
  simpljoin.
  apply EcbMod.join_comm in H56.
  eauto.
  destruct H48.

  hoare abscsq.
  apply noabs_oslinv.
  inverts H39.
  eapply mutexdel_succ_absinfer.
  go.
  eapply EcbMod.join_get_r; eauto.
  apply EcbMod.get_a_sig_a.
  go.
  eauto.


  inverts H39.
  hoare forward prim.
  instantiate (6:=( (V$OS_EVENT_TYPE_UNUSED
                      :: Vint32 i0
                      :: V$0 ::  Vnull ::x6:: v'27 :: nil)) :: v'2).
  unfold AOSEventFreeList.

  unfold AECBList.
  unfold AOSTCBPrioTbl.
  sep pauto.
  sep cancel 8%nat 1%nat.
  sep cancel 6%nat 1%nat.
  sep cancel 9%nat 2%nat.
  unfold ecbf_sll.
  unfold ecbf_sllseg; fold ecbf_sllseg.
  unfold node.
  unfold AOSEventTbl.
  sep pauto.
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel ecbf_sllseg.
  eauto.
  go.
  go.
  go.
  rewrite mutexdel_intlemma1 in H17.
  rewrite (nth_val_nth_val'_some_eq _ _ H37) in H17.



  eapply  R_Prio_Tbl_P_hold_for_del; eauto.
  rewrite mutexdel_intlemma1.
  eauto.
  auto.

  apply val_eq_lemma001 in H17.
  subst x0.
  auto.
  auto.


  rewrite mutexdel_intlemma1.
  eauto.
  auto.

  rewrite mutexdel_intlemma1.  

  clear -H32.
  remember (Int.shru i2 ($ 8)).
  int auto.
  auto.
  auto.
  rewrite mutexdel_intlemma1.
  eapply RL_RTbl_PrioTbl_P_hold_for_del.
  apply val_eq_lemma001 in H17.
  rewrite mutexdel_intlemma1 in H17.
  rewrite (nth_val_nth_val'_some_eq _ _ H37) in H17.
  subst x0.
  auto.
  auto.
  eauto.
  clear -H32.
  remember (Int.shru i2 ($ 8)).
  int auto.
  auto.
  eauto 1.
  eauto 1.
  eauto 1.
  auto.
  rewrite mutexdel_intlemma1.
  split.

  rewrite array_type_vallist_match_is_all_elem_p.
  apply all_elem_hold_for_upd.
  rewrite <- array_type_vallist_match_is_all_elem_p.
  auto 1.
  simpl.
  auto 1.
  rewrite update_nth_val_len_eq.
  auto.
  auto.
  (* Require Import mathlib. *)
  rewrite list_prop1 in H3.
  rewrite list_prop1 in H3.
  lets fff : ecblist_p_decompose H3.
  auto.
  assert (v'47 = nil \/ v'47 <> nil) as Hasrt by tauto.
  destruct Hasrt; intros.
  lets aff: H44  H58.
  simpljoin.
  simpl.
  apply eq_sym in H42.
  simpl in H4.
  simpljoin.
  lets Hres : ecblist_ecbmod_get_mutex H3 ; eauto.
  apply del_val_inj_lemma0 in H12.
  subst i0.
  auto.
  simpljoin.
  lets aaa:ecb_join_sig_eq H58 H48.
  subst x1; simpl; auto.

  lets tmp : H46 H58.
  simpljoin.
  lets Hres : ecblist_ecbmod_get_mutex' H3; eauto.
  apply del_val_inj_lemma0 in H12.
  subst i0.
  auto.
  simpljoin.
  eapply ecb_list_join_join; eauto.

  eapply del_ecbmod_join_lemma0; eauto.
  apply EcbMod.join_comm; auto.
  

  eapply ecb_del_prop_RHhold.
  eauto.
  go.
  unfold AEventData.
  go.
  
  hoare forward.
  unfold AEventData in H39.
  sep pauto.
  instantiate (1:=Afalse) in H12.
  (* apply DisjPropE in H12. *)
  destruct H12; intros; sep auto.
  Grab Existential Variables.
  exact (V$0).
  exact (V$0).
  exact ($0).
  exact Afalse.
Qed.

(*0*) 
(*0*)
