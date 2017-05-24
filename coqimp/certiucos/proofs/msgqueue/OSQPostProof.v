(*****************************  uc/OS-II  *******************************)
(******************************* OS_Q.C *********************************)
(*Proofs for API Fucntion:  INT8U OSQPost (OS_EVENT* pevent, void *msg) *)
(******************************** Code:**********************************)
(*** 
INT8U  OSQPost (void *msg, OS_EVENT *pevent)
{
    OS_Q      *pq;
    BOOLEAN    legal;
    int8u      x;

1   if (pevent == (OS_EVENT * )0) 
    {                                            
2        return (OS_ERR_PEVENT_NULL);
    }
3   if (msg == (void * )0) 
    {                                               
4       return (OS_ERR_POST_NULL_PTR);
    }
5   OS_ENTER_CRITICAL();
6   legal = OS_EventPtrSearch(pevent);
7   if (!legal)
    {
8       OS_EXIT_CRITICAL();
9       return (OS_ERR_PEVENT_NULL);
    }
10  if (pevent->OSEventType != OS_EVENT_TYPE_Q)
    {
11      OS_EXIT_CRITICAL();
12      return (OS_ERR_PEVENT_NULL)
    }
13  if (pevent->OSEventGrp != 0x00)
    {                              
        x = OS_STAT_Q;
14      OS_EventTaskRdy(pevent, msg, OS_STAT_Q); 
15      OS_EXIT_CRITICAL();
16      OS_Sched();                                 
17      return (OS_NO_ERR);
    }
18  pq = (OS_Q * )pevent->OSEventPtr;               
19  if (pq->OSQEntries >= pq->OSQSize)
    {                                               
20      OS_EXIT_CRITICAL();
21      return (OS_Q_FULL);
    }
22  *pq->OSQIn++ = msg;                              
23  pq->OSQEntries++;                                
24  if (pq->OSQIn == pq->OSQEnd)
    {                                                
25      pq->OSQIn = pq->OSQStart;
    }
26  OS_EXIT_CRITICAL();
27  return (OS_NO_ERR);
}
}
***)
Require Import ucos_include.
Require Import OSQPostPure.
Require Import OSQAcceptPure.
Require Import msgq_absop_rules.
Require Import oscore_common.
Require Import go.
Require Import OSEventTaskRdyPure.
Require Import new_inv.
Require Import tcblist_setnode_lemmas.
(*
Require Import gen_lemmas.
Require Import lab.
*)
Open Scope code_scope.
Open Scope int_scope.
Open Scope Z_scope.

(*-----------OS Q Post-------------------*)

(*Hint Resolve gooda_qpost retpost_osev . *)
(*-------------------------------------------------------------*)

Lemma OSQPostProof: 
  forall vl p r tid, 
    Some p =
    BuildPreA' os_api OSQPost
               (qpost, (Tint8, Tptr os_ucos_h.OS_EVENT :: Tptr Tvoid :: nil)) vl OSLInv tid init_lg->
    Some r =
    BuildRetA' os_api OSQPost
               (qpost, (Tint8, Tptr os_ucos_h.OS_EVENT :: Tptr Tvoid :: nil)) vl OSLInv tid init_lg->
    exists t d1 d2 s,
      os_api OSQPost = Some (t, d1, d2, s) /\
      {|OS_spec , GetHPrio, OSLInv, I, r, Afalse |}|-tid {{p}}s {{Afalse}}.
Proof.
  init_spec.
  hoare forward.
  apply isptr_zh; auto.
  pauto.

  (*pevent is Null pointer------------------------L1 ~ L2*)
  pure intro.
  assert (x0 =Vnull).
  pauto.
  subst x0.

  hoare_abscsq.
  apply noabs_oslinv.
  eapply qpost_absinfer_null.
  go.
  
  (*hoare_forward_abscsq qpost_absinfer_null. *)
  hoare forward.
  hoare forward.
  pure intro.

  clean_ptr H H2 x0.
  (*msg is Null pointer -------------------------L3 ~ L4*)

  hoare forward.
  apply isptr_zh; auto.
  pauto.
  
  pure intro.
  assert (x=Vnull) by pauto.
  subst x.
  hoare abscsq.
  apply noabs_oslinv.
  eapply qpost_absinfer_msg_null;eauto.
  go. 
  hoare forward.
  hoare forward.
  pure intro.
  clean_ptr H H1 x.

  (* encrit --------------------------------- L5*)
  hoare forward prim.
  
  (* call search to check if queue exists -------------------L6 *)
  hoare unfold.
  hoare forward.
  do 3 sep cancel 18%nat 1%nat.
  sep cancel 17%nat 1%nat.
  sep cancel 5%nat 1%nat.
  sep cancel 9%nat 1%nat.
  sep cancel 14%nat 1%nat.
  sep cancel 10%nat 1%nat.
  sep cancel 7%nat 1%nat.
  sep cancel 1%nat 1%nat.
  eauto.
  simpl; eauto.
  pure_auto.
  apply retpost_osev.
  intros.

  destruct H1.
  destruct H1.
  sep auto.
  sep auto.

  intros.
  sep auto.
  
  (* check if does not exists ---------------------- L7 ~ L9 *)
  hoare unfold.
(*  hoare lift 2%nat pre. *)
  eapply backward_rule1.
  eapply disj_star_elim.
  apply disj_rule.
  pure intro.

  inverts H15.
  rename H16 into H15.
  rename H17 into H16.

  (*---- ok ----*)
  hoare forward.
  pure_auto.
  instantiate (1:=Afalse).
  pure intro.
  destruct H9.
  go.
  hoare forward.
  pure intro.
  clear H9.
  
  (*---does not exist---*)
  Focus 2.
  pure intro.
  inverts H5.
  rename H6 into H5.
  hoare forward.
  pure_auto.
  pure intro.
  hoare abscsq.
  apply noabs_oslinv.
  eapply qpost_absinfer_no_q;eauto.
  go.
  intro;simpljoin1;tryfalse.
  hoare forward prim.
  exact H7.
  go.
  hoare forward.
  hoare forward.
  pure intro.
  assert (Int.eq ($ 0) ($ 0) =true ) by pauto.
  rewrite H4 in H3.
  destruct H3;simpl in H3;tryfalse.

  (* check event type --------------- L10 ~ L12 *)
  unfold AEventNode.
  unfold AOSEvent.
  unfold node.
  unfold AOSEventTbl.
  unfold AMsgData.
  unfold AOSQCtr.
  unfold AOSQBlk.
  unfold node.
  
  hoare unfold.
  hoare forward; pure_auto.
  
  instantiate (1:=Afalse).
  pure intro.

  apply notint_neq_zero_eq in H9.
  unfold OS_EVENT_TYPE_Q in H9.
  
  
  eapply backward_rule1.
  intros.
  sep lift 8%nat in H24.

  eapply eventtype_neq_q in H24;eauto.
  hoare_split_pure_all.
  hoare abscsq.
  apply noabs_oslinv.
  eapply qpost_absinfer_no_q;auto.
  go.
  hoare forward prim.
  
  unfold AECBList.
  sep pauto.
  eapply evsllseg_compose.
  
  instantiate (2:=Vint32 i0 :: Vint32 i :: Vint32 i1 :: x3 :: x4 :: v'43 :: nil).
  unfold V_OSEventListPtr; simpl; auto.
  auto.  
  auto.
  repeat (sep cancel evsllseg).
  (* AEventNode *)  

  unfold AEventNode.
  unfold AOSEvent.
  unfold AOSEventTbl.
  unfold node.
  sep pauto.
  sep cancel 1%nat 3%nat.
  sep cancel 1%nat 1%nat.
  eauto.
  eauto.
  unfolds;simpl;auto.
  auto.
  auto.
  go.
  auto.
  go.
  hoare forward.

  hoare forward.  
  pure intro.

  remember (Int.eq i0 ($ OS_EVENT_TYPE_Q)) as X.
  destruct X;simpl in H9;destruct H9;tryfalse.
  
  (*prove the event data is DMsgQ*)
  hoare lift 8%nat pre.
  apply hoare_pure_gen with (p:=(exists v1 v2 v3 v4, v'42 = DMsgQ v1 v2 v3 v4)).
  intros.
  unfold AEventData in H13.
  destruct v'42;
  try solve [
    sep split in H13;
  unfolds in H14; simpl in H14;
  inverts H14;
  rewrite Int.eq_false in HeqX; tryfalse].
  eauto.
  pure intro.
  (*finish, no false cases left here*)

  
  (* exists task waiting -------L13 ~ L17 ----------- *)
  apply hoare_pure_gen with (p := (exists a, x=x3 /\ x3 = Vptr (a, Int.zero))).
  clear - H1; clear H1; clears.
  intros.
  simpljoin.
  unfold AEventData in H.
  sep split in H.
  unfolds in H0; simpl in H0; inverts H0.
  unfold AMsgData in H; unfold AOSQCtr in H; unfold node in H.
  sep normal in H.
  do 2 destruct H; sep split in H.
  destruct H0; substs.
  eauto.
  pure intro.
  
  hoare forward; pure_auto.
  instantiate (1:=Afalse).
  
  pure intro.
  apply notint_neq_zero_eq in H9.
  clear H13 H14.
  hoare forward.

  (*call OS_EventTaskRdy*)
  unfold AOSTCBList.
  unfold AOSTCBPrioTbl.
  hoare normal pre.
  pure_intro.
  hoare forward.

(* pre conditions of OS_EventTaskRdy*)
  do 4 sep cancel 11%nat 1%nat.
  sep cancel 1%nat 2%nat.
  unfold AEventNode.
  unfold AOSEvent.
  unfold node.
  unfold AOSEventTbl.
  sep normal.
  sep eexists.
  sep split; eauto.
  do 2 sep cancel 8%nat 1%nat.
  sep cancel 7%nat 1%nat.
  sep cancel 11%nat 1%nat.
  sep lifts (3::5::nil)%nat in H30.
  apply tcbdllseg_compose in H30.
  sep cancel 1%nat 1%nat.
  exact H30.
  pure_auto.
  split; pure_auto.
  split.
  pure_auto.
  intro; substs.
  clear - H9; rewrite Int.eq_true in H9; tryfalse.
  simpl; eauto.
  simpl; eauto.
  simpl; auto.
  lets Hx: TCBList_P_Combine H24 H25; eauto.

  sep lift 3%nat in H30.
  eapply tcbdllseg_get_last_tcb_ptr; eauto.
  auto.
  eauto.
  auto.

  sep lifts (3::5::nil)%nat in H30.

  eapply tcbdllseg_combine_ptr_in_tcblist; eauto.
(*  intro; tryfalse. *)

  pure_auto.
  intros.
  sep auto.
  intros.
  sep auto.
(*finished side conditions*)
  
  hoare normal pre.
  hoare unfold.
  rename H46 into Hxx1; rename H47 into Hxx2; rename H48 into Hxx3; rename H49 into Hxx4; rename H50 into Hxx5; rename H62 into Hxx6; rename H63 into Hxx7.
  rename H54 into H49;
  rename H55 into H50; rename H56 into H51; rename H57 into H52; rename H58 into H53;
  rename H59 into H54; rename H60 into H55; rename H61 into H56; rename H65 into H57.
  rename H64 into vl_stv_match.
  inverts H55.
  
  (*after OS_EventTaskRdy*)

  (*prove some properties used by the following reasoning*)
  
  (*1: get the range info of the event table elements*)
  assert (Int.unsigned v'75 <= 7) as y_le7.
  clear - H38 H20.
  lets Hx: osunmapvallist_prop H20; simpljoin.
  rewrite H in H38; inverts H38.
  apply Z.leb_le in H0; auto.

  assert (Int.unsigned v'76 <= 255) as erow_le255.
  clear - H39 H10 H18 y_le7.
  assert (Z.to_nat (Int.unsigned v'75) < length v'61)%nat.
  rewrite H18; unfold OS_EVENT_TBL_SIZE.
  mauto.
  lets Hx: array_int8u_nth_lt_len H10 H; simpljoin.
  rewrite H39 in H0; invert H0; auto.

  assert(Int.unsigned v'74 <= 7) as x_le7.
  clear - H40 erow_le255.
  lets Hx: osunmapvallist_prop erow_le255; simpljoin.
  rewrite H in H40; inverts H40.
  apply Z.leb_le in H0; auto.

(*L15: EXIT_CRITICAL;ₛ*)
  unfold AEventNode.
  unfold AOSEvent, AEventData.
  unfold AOSEventTbl, AMsgData.
  unfold AOSQCtr; unfold AOSQBlk; unfold node.
  
  (*abs step*)
  lets Hx : ecbmod_absmsgq H4; simpljoin.
  symmetry in HeqX.
  lets Hx: Int.eq_spec i0 ($ OS_EVENT_TYPE_Q).
  rewrite HeqX in Hx; substs.

  pure intro. (*x1 is destructed here*)
  pose proof Int.eq_spec v'59 ($ 0).
  rewrite H9 in H35.

  assert(exists n m tcbls, TcbJoin (v'92, Int.zero) (((v'75<<ᵢ$ 3) +ᵢ  v'74), wait (os_stat_q (v'30, Int.zero)) n, m) tcbls v'51) as tcbls_tcbjoin.
  unfolds in H5; simpljoin.
  unfolds in H5; simpljoin.
  unfolds in H5.
  unfold V_OSEventType in H5; simpl in H5.
  pose proof H5 (Int.unsigned ((v'75<<ᵢ$ 3) +ᵢ  v'74)).
  assert(PrioWaitInQ (Int.unsigned ((v'75<<ᵢ$ 3) +ᵢ  v'74)) v'61).
  unfolds.
  assert(($ Int.unsigned ((v'75<<ᵢ$ 3) +ᵢ  v'74) >>ᵢ $ 3) = v'75) as xx1.
  clear - y_le7 x_le7.
  mauto.
  rewrite xx1.
  assert(($ Int.unsigned ((v'75<<ᵢ$ 3) +ᵢ  v'74)&ᵢ$ 7) = v'74) as xx2.
  clear - y_le7 x_le7.
  mauto.
  rewrite xx2.
  exists v'74 v'75 v'76.
  splits; eauto.
  clear - y_le7 x_le7.
  mauto.
  apply nth_val'2nth_val; eauto.
  eapply math_8_255_eq; eauto.
  pose proof rl_tbl_grp_neq_zero.
  lets Hx: rl_tbl_grp_neq_zero Hxx4; eauto.
  clear - y_le7.
  mauto.
  assert (Some (V$ OS_EVENT_TYPE_Q) = Some (V$ OS_EVENT_TYPE_Q)) by auto.
  apply H70 in H72; auto.
  simpljoin.

  unfolds in H52; simpljoin.
  apply nth_val'2nth_val' in H32.
  lets Hx: H52 H32 H57.
  clear - y_le7 x_le7.
  mauto.
  simpljoin.

  clear - H74 H72 H75.
  unfold get in H72, H75; simpl in H72, H75.
  rewrite Int.repr_unsigned in H72.
  lets Hx: R_Prio_No_Dup_tid_eq H74 H72 H75.
  simpljoin.
  unfold TcbJoin.
  exists x6 x13.
  unfold join, sig; simpl.
  exists (TcbMod.minus v'51 (TcbMod.sig (v'92, Int.zero)
        ((v'75<<ᵢ$ 3) +ᵢ  v'74, wait (os_stat_q (v'30, Int.zero)) x6, x13))).
  unfold TcbMod.join.
  intros.
  destruct (tidspec.beq  (v'92, Int.zero) a) eqn : eq1.
  lets Hx: tidspec.beq_true_eq eq1.
  substs.
  rewrite TcbMod.minus_sem.
  rewrite TcbMod.get_sig_some.
  rewrite H75; auto.
  lets Hx: tidspec.beq_false_neq eq1.
  rewrite TcbMod.minus_sem.
  rewrite TcbMod.get_sig_none; auto.
  destruct (TcbMod.get v'51 a); auto.
  
  simpljoin.
  
  lets Hx: post_exwt_succ_pre H35 H52 H17 H5 H7.
  lets Hx1: Hx H16 H6 H20 H10 H18; clear Hx.
  lets Hx2: Hx1 H38 y_le7 H39 erow_le255 H40.
  lets Hx3: Hx2 x_le7 H32 H43.
  simpljoin.
  
  hoare abscsq.
  apply noabs_oslinv.
  eapply qpost_absinfer_exwt_succ; eauto.
  pure_auto.
  clear - H16 H6.
  eapply join_joinsig_get; eauto.

  (*prove TCBList_P hold for the new vltcb and tcbls*)
  clear Hx1 Hx2.

  assert (R_Prio_No_Dup v'51).
  clear - H52.
  unfolds in H52; simpljoin; auto.
  
  (*split the new vltcb in hoare pre*)
  hoare lift 21%nat pre.
  lets old_tcbnode_p : TCBList_P_tcblist_get_TCBNode_P H54 H33 H55.
  eapply set_node_elim_hoare
  with (st':=rdy) (m':=(Vptr x0))
       (rtbl':=update_nth_val (Z.to_nat (Int.unsigned v'75)) v'55
                              (Vint32 (Int.or v'93 v'77))); eauto.
  (*TCBNode_P*)
  eapply TCBNode_P_set_rdy; eauto.
  clear - y_le7 x_le7.
  mauto.
  assert((((v'75<<ᵢ$ 3) +ᵢ  v'74) >>ᵢ $ 3) = v'75).
  clear - y_le7 x_le7.
  mauto.
  rewrite H70.
  apply nth_val'2nth_val; auto.
  clear - H30 Hxx2 Hxx6 y_le7.
  assert (Z.to_nat (Int.unsigned v'75) < length v'55)%nat.
  rewrite Hxx6.
  eapply z_le_n_lt'; auto.
  lets Hx: array_int8u_nth_lt_len Hxx2 H.
  simpljoin.
  rewrite H30 in H0.
  inverts H0; auto.

  clear - H37.
  simpl in H37; substs.
  apply Int.and_not_self.

  clear - y_le7 x_le7.
  mauto.
  
  assert((((v'75<<ᵢ$ 3) +ᵢ  v'74)&ᵢ$ 7) = v'74).
  clear - y_le7 x_le7. 
  mauto.
  rewrite H70.
  eapply math_mapval_core_prop; auto.
  clear - x_le7.
  mauto.

(*rtbl_set_one_bit*)
{  
  unfolds.
  assert((((v'75<<ᵢ$ 3) +ᵢ  v'74) >>ᵢ $ 3) = v'75).
  clear - y_le7 x_le7.
  mauto.
  rewrite H70.
  assert((((v'75<<ᵢ$ 3) +ᵢ  v'74)&ᵢ$ 7) = v'74).
  clear - y_le7 x_le7.
  mauto.
  rewrite H71.
  do 2 eexists.
  splits; eauto.
  clear - y_le7 x_le7.
  mauto.
}  
  unfolds; simpl; auto.
  hoare forward prim.
  
(*combine ecb list*)
  unfold AECBList.
  sep normal.
  eexists.
  sep cancel 13%nat 1%nat.
  simpl update_nth_val in H71.
  sep split.
  eapply evsllseg_compose; eauto.
  instantiate (2:=(V$ OS_EVENT_TYPE_Q
              :: Vint32 v'60
              :: Vint32 i1 :: Vptr (v'35, Int.zero) :: x4 :: v'43 :: nil)).
  unfolds; simpl; eauto.

  instantiate (18:=DMsgQ (Vptr (v'35, Int.zero))
             (x15
              :: x14
                 :: x8
                    :: x9
                       :: x10
                          :: Vint32 i0
                             :: Vint32 i :: Vptr (v'38, Int.zero) :: nil)
             (x1 :: x16 :: nil) x5).
  
  unfold AEventNode.
  unfold AOSEvent, AEventData.
  unfold AOSEventTbl, AMsgData. 
  unfold AOSQCtr, AOSQBlk; unfold node.
  sep normal; sep eexists; sep split; eauto.
  do 2 sep cancel 13%nat 6%nat.

  do 5 sep cancel 3%nat 1%nat.
  
(*AOSTCBPrioTbl*)
  unfold AOSTCBPrioTbl.
  sep normal.
  eexists.
  sep cancel 4%nat 1%nat.
  sep cancel 3%nat 1%nat.
  sep cancel 7%nat 1%nat.
  sep split; eauto.
  
  unfold AOSTCBList.
  sep normal; do 4 eexists.
  sep cancel 3%nat 1%nat.
  sep cancel 1%nat 1%nat.
  sep cancel 1%nat 2%nat.
  sep cancel 1%nat 1%nat.
  sep split; eauto.

  sep lift 2%nat in H70.
  eapply tcbdllflag_set_node in H70; eauto.
  unfolds; simpl; auto.  
  
  eapply r_priotbl_p_set_hold; auto; eauto.
  unfolds; simpl; auto.
  split; auto.
  go.
  split; auto.
  go.

  eapply ecblist_p_post_exwt_hold1; eauto.
  clear - H42 x_le7.
  lets Hx: osmapvallist_prop x_le7; simpljoin.
  rewrite H42 in H; inverts H.
  auto.
  
  assert(tid = (v'92, Int.zero) \/ tid <> (v'92, Int.zero)).
  tauto.
  destruct H80.
  substs.
  unfolds.
  unfold get; simpl.
  rewrite TcbMod.set_a_get_a.
  eauto.
  apply tidspec.eq_beq_true; auto.
  eapply rh_curtcb_set_nct; auto.

  eapply rh_tcblist_ecblist_p_post_exwt; eauto.
  clear - H47.
  unfolds in H47; simpljoin; auto.

  pure_auto.

  (*L16: OS_Sched (­);ₛ*)
  hoare forward.
  do 3 sep cancel 3%nat 1%nat.
  sep cancel 1%nat 2%nat.
  sep cancel 1%nat 1%nat.
  sep cancel 1%nat 1%nat.
  eauto.
  unfolds.
  left; auto.
  pure_auto.
  intros.
  sep auto.
  sep cancel 1%nat 1%nat.
  simpl; auto.
  intros.
  sep auto.
  sep cancel 1%nat 1%nat.
  simpl; auto.
  
  (*L17: RETURN ′ OS_NO_ERR*)
  hoare unfold.
  hoare forward.
  inverts H70; auto.
  hoare forward.  

  (*L18: pq ′ =ₑ pevent ′ → OSEventPtr;ₛ*)
  hoare forward.
  pure_auto.
  pure_auto.

  (*L19: If(pq ′ → OSQEntries ≥ pq ′ → OSQSize)*)
  unfold AEventData.
  hoare unfold.
  hoare forward; pure_auto.
  instantiate (1 := Afalse).
  pure intro.
  
  (*high level step*)
  remember (Int.ltu i3 i2) as Y.
  remember (Int.eq i2 i3 ) as Z.
  assert (Int.ltu Int.zero Int.one || Int.ltu Int.zero Int.one = true).
  simpl.
  go.
  assert (Int.ltu Int.zero Int.one || Int.ltu Int.zero Int.zero = true).
  simpl.
  go.
  assert (Int.ltu Int.zero Int.zero || Int.ltu Int.zero Int.one = true).
  simpl.
  go.
  assert (Int.ltu Int.zero Int.zero || Int.ltu Int.zero Int.zero = false).
  simpl.
  go.
  clear H13 H28.

  assert (true = Int.ltu i3 i2 \/ true = Int.eq i2 i3).
  destruct Y;destruct Z;simpl in H9; try rewrite H37 in H9;tryfalse;try rewrite H38 in H9;tryfalse;try rewrite H39 in H9;tryfalse;try rewrite H40 in H9;tryfalse; auto.
  simpl in H9; tryfalse.
  lets Hy:ecbmod_absmsgq H4; simpljoin.
  
  hoare_abscsq.
  apply noabs_oslinv.
  eapply qpost_absinfer_ovf.
  go.
  eapply EcbMod.join_joinsig_get; eauto.
  eapply qpost_ovf_prop1; eauto.
  
  (*L20: EXIT_CRITICAL;ₛ*)
  hoare forward prim.
  sep cancel 10%nat 2%nat.
  unfold AECBList.
  sep normal.
  eexists.
  sep cancel 7%nat 1%nat.
  sep split; eauto.
 
  eapply evsllseg_compose; eauto.
  unfolds; simpl; eauto.
  sep cancel 7%nat 2%nat.
  sep cancel 7%nat 2%nat.
  unfold AEventNode.
  unfold AOSEvent, AEventData.
  unfold node, AOSEventTbl, AMsgData.
  unfold AOSQCtr; unfold AOSQBlk; unfold node.
  sep normal; sep eexists.
  sep split; eauto.
  do 3 sep cancel 1%nat 1%nat.
  do 2 sep cancel 2%nat 1%nat.
  exact H28.

  split; auto.
  go.
  split; auto.
  go.
  split; auto.
  go.
  pure_auto.

(*L21: RETURN ′ OS_Q_FULL*)
  hoare forward.
  (*elim afalse*)
  hoare forward.
  
  (*L22: ∗ pq ′ → OSQIn =ₑ message ′;ₛ*)
  lets Hx: osq_same_blk_st_in' H27; simpljoin.
  simpl in H25; inverts H25.
  lets Hy: wellq_in_props H29 H4 H27;eauto.
  simpljoin.

  hoare forward; eauto.
  pure_auto.
  go.

  (*L23: pq ′ → OSQEntries =ₑ pq ′ → OSQEntries +ₑ ′ 1;ₛ*)
  hoare forward.
  pure_auto.
  go.
  pure_auto.

  (*L24: pq ′ → OSQEntries =ₑ pq ′ → OSQEntries +ₑ ′ 1;ₛ*)
  hoare forward.
  pure_auto.
  go.
  pure_auto.
  
  (*L25: If(pq ′ → OSQIn ==ₑ pq ′ → OSQEnd)*)
  pure intro.
  lets Hx: wellformedosq_ens_add_1 H29 H4 H27.
  hoare forward.
  pure_auto.
  go.
(*
  pure_auto.
  go. *)
  clear - H32.
  destruct x; unfolds in H32;
    destruct H32; tryfalse; destruct H; tryfalse.
  simpl; intro; tryfalse.
  destruct a.
  inverts H.
  destruct (peq v'42 b);
    destruct (Int.eq (x2 +ᵢ  Int.mul ($ 1) ($ 4)) i); simpl; intro; tryfalse.
  
  (*L26: pq ′ → OSQIn =ₑ pq ′ → OSQStart*)
  hoare forward.
  pure_auto.
  go.
  pure_auto.

  assert (exists a, x = Vptr a).
  clear - H27.
  unfolds in H27; simpl in H27; simpljoin.
  unfolds in H0; simpl in H0; inverts H0.
  eauto.
  simpljoin.
  (*combine the 2 cases after if*)
  eapply backward_rule1 with
  (p:= (EX new_qin,
        [| ((v'42, x2 +ᵢ  Int.mul ($ 1) ($ 4)) = x3 /\ new_qin = x11) \/
         ((v'42, x2 +ᵢ  Int.mul ($ 1) ($ 4)) <> x3 /\ new_qin = (Vptr (v'42, x2 +ᵢ  Int.mul ($ 1) ($ 4)))) |] **
        <|| qpost (Vptr (v'27, Int.zero) :: Vptr x0 :: nil) ||>  **
        LV pq @ os_ucos_h.OS_Q ∗ |-> Vptr (v'38, Int.zero) **
        Astruct (v'38, Int.zero) os_ucos_h.OS_Q
        (x12
           :: x11
           :: Vptr x3
           :: new_qin
           :: x7
           :: Vint32 i3
           :: Vint32 (i2 +ᵢ  $ 1) :: Vptr (v'42, Int.zero) :: nil) **
        Aarray (v'42, Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))
        (Tarray (Void) ∗ ∘ OS_MAX_Q_SIZE)
        (update_nth_val
           (Z.to_nat
             ((Int.unsigned x2 -
               Int.unsigned (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))) / 4)) x5
           (Vptr x0)) **
        Astruct (v'42, Int.zero) os_ucos_h.OS_Q_FREEBLK (x1 :: x13 :: nil) **
        Astruct (v'27, Int.zero) os_ucos_h.OS_EVENT
        (V$ OS_EVENT_TYPE_Q
        :: Vint32 i
        :: Vint32 i1 :: Vptr (v'38, Int.zero) :: x4 :: v'43 :: nil) **
        Aarray v'21 (Tarray Int8u ∘ OS_EVENT_TBL_SIZE) v'41 ** Aie false **
        Ais nil **
        Acs (true :: nil) **
        Aisr empisr **
        GV OSEventList @ os_ucos_h.OS_EVENT ∗ |-> v'39 **
        evsllseg v'39 (Vptr (v'27, Int.zero)) v'23 v'25 **
        evsllseg v'43 Vnull v'24 v'26 **
        A_isr_is_prop **
        AOSTCBList v'29 v'30 v'31 (v'32 :: v'33) v'34 tid v'37 **
        tcbdllflag v'29 (v'31 ++ v'32 :: v'33) **
        AOSRdyTblGrp v'34 v'35 **
        AOSTCBPrioTbl v'28 v'34 v'37 v'48 **
        HECBList v'36 **
        HTCBList v'37 **
        HCurTCB tid **
        p_local OSLInv tid init_lg **
        LV legal @ Int8u |-> (V$ 1) **
        AOSEventFreeList v'2 **
        AOSQFreeList v'3 **
        AOSQFreeBlk v'4 **
        AOSMapTbl **
        AOSUnMapTbl **
        AOSIntNesting **
        AOSTCBFreeList v'19 v'20 **
        AOSTime (Vint32 v'17) **
        HTime v'17 **
        AGVars **
        atoy_inv' **
        LV os_code_defs.x @ Int8u |-> v'1 **
        LV message @ (Void) ∗ |-> Vptr x0 **
        LV pevent @ os_ucos_h.OS_EVENT ∗ |-> Vptr (v'27, Int.zero) **
        A_dom_lenv
        ((message, (Void) ∗)
           :: (pevent, os_ucos_h.OS_EVENT ∗)
           :: (pq, os_ucos_h.OS_Q ∗)
           :: (legal, Int8u) :: (os_code_defs.x, Int8u) :: nil)
    )).

  intros.
  destruct H39.
  
  (*if true*)
  sep auto.
  left.
  split; auto.
  simpljoin.
  clear - H48.
  destruct x3.
  destruct (peq v'42 b) eqn : eq1;
    destruct (Int.eq (x2 +ᵢ  Int.mul ($ 1) ($ 4)) i) eqn : eq2;
    simpl in H48; tryfalse.
  substs.
  pose proof Int.eq_spec (x2 +ᵢ  Int.mul ($ 1) ($ 4)) i.
  rewrite eq2 in H.
  substs; auto.

  (*if false*)
  sep auto.
  right.
  split; auto.
  simpljoin.
  clear - H48.
  destruct x3.
  destruct (peq v'42 b) eqn : eq1;
    destruct (Int.eq (x2 +ᵢ  Int.mul ($ 1) ($ 4)) i) eqn : eq2;
    simpl in H48; destruct H48; tryfalse.
  substs.
  intro.
  inverts H0.
  pose proof Int.eq_spec (x2 +ᵢ  Int.mul ($ 1) ($ 4)) (x2 +ᵢ  Int.mul ($ 1) ($ 4)).
  rewrite eq2 in H0.
  tryfalse.

  intro; inverts H0.
  tryfalse.

  intro; inverts H0.
  tryfalse.
  
  pure intro.

  (*high level step*)
  lets Hx1: ecbmod_absmsgq H4.
  lets Hx2: EcbMod.join_joinsig_get H16 H6.
  simpljoin.
  
  assert(Int.eq i ($ 0) = true).
  clear - H14.
  destruct (Int.eq i ($ 0)) eqn : eq1; simpl in H14; auto.
  unfold Int.notbool in H14.
  rewrite Int.eq_true in H14.
  destruct H14; tryfalse.
  
  lets Hx3: rlh_ecb_nowait_prop H17 H5 Hx2 H7 H40; substs.

  hoare abscsq.
  apply noabs_oslinv.
  eapply qpost_absinfer_nowt_succ.
  pure_auto.
  eauto.

  assert(Int.ltu i2 i3 = true).
  clear - H28.
  apply val_inj_i1_i2_lt in H28; auto.

  eapply qpost_no_wait_prop'; eauto.

  (*L26: EXIT_CRITICAL;ₛ*)
  hoare forward prim.
  sep cancel 10%nat 2%nat.
  unfold AECBList.
  sep normal.
  eexists.
  sep cancel 7%nat 1%nat.
  sep split.
  
  eapply evsllseg_compose with
  (l:= (V$ OS_EVENT_TYPE_Q
         :: Vint32 i
         :: Vint32 i1 :: Vptr (v'38, Int.zero) :: x4 :: v'43 :: nil)
  ).
  unfolds; simpl; eauto.
  eauto.
  eauto.
  do 2 sep cancel 7%nat 2%nat.
  instantiate (2:=
                 (DMsgQ (Vptr (v'38, Int.zero))
                        (x12
                           :: x11
                           :: Vptr x3
                           :: v'22
                           :: x7
                           :: Vint32 i3
                           :: Vint32 (i2 +ᵢ  $ 1)
                           :: Vptr (v'42, Int.zero) :: nil)
                        (x1 :: x13 :: nil)
                        (update_nth_val
                           (Z.to_nat
                              ((Int.unsigned x2 -
                                Int.unsigned (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))) / 4)) x5
                (Vptr x0))
                 )).
  unfold AEventNode;
  unfold AOSEvent, AEventData; unfold AOSEventTbl;
  unfold AMsgData; unfold AOSQBlk, AOSQCtr; unfold node.
  sep normal; sep eexists.
  sep split; eauto.
  sep cancel 4%nat 1%nat.
  sep cancel 3%nat 1%nat.
  do 3 sep cancel 2%nat 1%nat.
  exact H41.

  split; auto.
  go.
  unfolds; simpl; eauto.
  {
    destruct H39; simpljoin.
    eapply get_wellformedosq_in_setst; eauto.
    apply val_inj_i1_i2_lt; auto.
    rewrite peq_true.
    rewrite Int.eq_true.
    simpl; intro; tryfalse.
    
    eapply get_wellformedosq_in_setst'; eauto.
    intro; inverts H42; tryfalse.
  }

  split; auto.
  go.
  {
    clear - H30 H39.
    destruct H39; simpljoin; auto.
    unfolds in H30; destruct H30; simpljoin; auto.
  }
  pure_auto.
  lets Hx1: get_wellformedosq_in_setst H27.
  apply val_inj_i1_i2_lt; auto.
  split; auto.
  go.

  eapply msgqlist_p_compose'; eauto.
  {  (*destruct the if condition here*)
    destruct H39; simpljoin.
    eapply rlh_ecbdata_in_end;eauto.
    eapply val_inj_i1_i2_lt; auto.

    eapply rlh_ecbdata_in_noend; eauto.
    clear - H39.
    intro; inversion H; apply H39; auto.
    eapply val_inj_i1_i2_lt; auto.
  }    
    
  eapply EcbMod.joinsig_set;eauto.
  eapply EcbMod.joinsig_set_set;eauto.
  eapply rh_tcbls_mqls_p_setmsg_hold;eauto.
  pure_auto.

  (*L27: RETURN ′ OS_NO_ERR*)
  hoare forward.
Qed.

Close Scope code_scope.
