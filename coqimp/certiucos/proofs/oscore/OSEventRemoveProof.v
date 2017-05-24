(**************************  uc/OS-II  *******************************)
(*************************** OS_CORE.C *******************************)
(*Proof of Internal Fucntion:  void OS_EventRemove (OS_EVENT* pevent)*)
(***************************  Code: **********************************)
(***
void OS_EventRemove (OS_EVENT *pevent)
{
     OS_EVENT *p,*p1, x;

1:   p = OSEventList;
2:   p1 = OSEventList;
3:   x = 0;
4:   if (p == pevent)
     {
5:       OSEventList = OSEventList->OSEventListPtr;
6:       return
     };
7:   while (p != (OS_EVENT * )0 && x == 0)
     {
8:       p1 = p -> OSEventListPtr;   
9:       if(p1 != pevent)
         {
10:        p = p1;
         }
         else
         {
11:        x = 1;
         }
     };
12:  if (x == 1)
     {
13:      p->OSEventListPtr = p1->OSEventListPtr;
     };
14:  return;
}
***)
Require Import ucos_include.
Require Import OSEventRemovePure.
Require Import oscore_common.
Require Import symbolic_lemmas.

Open Scope code_scope.
Open Scope Z_scope.
Open Scope int_scope.
Open Scope list_scope.

(*
Require Import ucert. 
Open Scope code_scope.
Require Import mathlib.
Require Import OSEventRemovePure.
*)

Lemma backward_1 :
  forall P P' Q S spec sd linv I r ri s tid,
         P ==> P' ->
         {|spec , sd, linv, I, r, ri|}|-tid {{P'**Q}}s {{S}} ->
         {|spec , sd, linv, I, r, ri|}|-tid {{P**Q}}s {{S}}.      
Proof.
  intros.
  eapply backward_rule1 with (p:=P'**Q).
  intros.
  sep auto.
  auto.
Qed.


Ltac hoare_change pos asrt :=
  hoare lift pos%nat pre; apply backward_1 with (P':=asrt); sep pauto.

  
Lemma OSEventRemove_proof:
    forall vl p r logicl tid,  
      Some p =
      BuildPreI os_internal OS_EventRemove
                  vl logicl OS_EventRemovePre tid ->
      Some r =
      BuildRetI os_internal OS_EventRemove vl logicl OS_EventRemovePost tid ->
      exists t d1 d2 s,
        os_internal OS_EventRemove = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-tid {{p}} s {{Afalse}}. 
Proof.
  init_spec.
  rename v'8 into aop.

  hoare_split_pure_all.
  hoare lift 6%nat pre.
  apply hoare_pure_gen with (p:=(ecbls_ptr_distinct (v'4 ++ v'5))).
  intros; eapply evsllseg_distinct'; eauto.
  hoare_split_pure_all.
  rename H4 into Hx.
  hoare lifts (2::3::4::5::6::nil)%nat pre.
  
  simpl in H; inverts H.
  destruct H2.

(*L1: p = OSEventList*)
  hoare forward.
  sep lift 7%nat in H4; pose proof evsllseg_isptr H4; pauto.

(*L2: p1 = OSEventLsit*)
  hoare forward.
  sep lift 8%nat in H4; pose proof evsllseg_isptr H4; pauto.

(*L3: x = 0*)
  hoare forward.

(*L4: if(p == pevent)*)
  hoare remember (1::2::3::4::10::13::nil)%nat pre.
  hoare forward.
  sep lift 5%nat in H5; pose proof evsllseg_isptr H5; pauto.
  sep lift 5%nat in H5; pose proof evsllseg_isptr H5; pauto.
  instantiate (1:=Afalse).

(*L5: OSEventList = OSEventList->OSEventListPtr*)
  (*get the if condition into the context*)
  hoare_split_pure_all.
  simpljoin1.
  (*in the true branch of if, we first prove v'6 = (Vptr v'7),
    according to the if condition*)
  assert (val_eq v'6 (Vptr v'7) = Some (Vint32 Int.one)).
  unfold val_eq in *.
  destruct v'6; try solve [simpl in H7; tryfalse].
  destruct v'7; simpl in H5; tryfalse.
  destruct a, v'7.
  destruct (peq b b0); destruct (Int.eq i i0); auto; try solve [simpl in H5; tryfalse].

  apply val_eq_true_eq in H3.
  substs.
  (*finished the proof of v'6 = Vptr v'7*)

  (*then we should prove in this case v'4 is nil,
    if it were not, Vptr v'7 points to a node in v'4,
    the last ptr of v'4 is also Vptr v'7, which points to a node in v'5,
    v'5 is not nill because the whole sll ends with Vnull
   *)
  destruct v'4.
  (*v'4 is nil*)
  (*then v'2 is nil accordingly*)
  destruct v'2.
  simpl app.
  (*v'5 and v'3 are not nil*)
  destruct v'5.
  simpl evsllseg.
  hoare_split_pure_all.
  destruct H3; inversion H3.
  destruct v'3.
  simpl evsllseg.
  solve_Afalse_in_pre.

  (*take off the node*)
  unfold evsllseg at 2; fold evsllseg.
  destruct e.
  unfold AEventNode at 2.
(*  destruct e0. *)
  unfold AOSEvent.
  unfold node.
  hoare_split_pure_all.
  simpljoin1.
assert(exists v1 v2 v3 v4 v5 v6 tail, v = v1::v2::v3::v4::v5::v6::tail).
clear - H11.
  apply struct_type_vallist_match_os_event; auto.
  simpljoin1.
  inverts H3.
  hoare forward.
  auto.

(*L6: return*)
  hoare forward.
  unfold AEventNode.
  unfold AOSEvent.
  unfold node.
  sep pauto; pauto.
  instantiate (1:=nil).
  simpl app.
  eauto.
  split; intros.
  eauto.
  tryfalse.
  unfolds; simpl; auto.
  auto.
  simpl; auto.
  hoare_split_pure_all.
  solve_Afalse_in_pre.
 
  (*v'2 is not nil, false*)
  simpl in H0.
  inversion H0.
  (*v'4 is not nil, false*)
  assert (e::v'4 <> nil).
  intro; tryfalse.
  
  apply H2 in H3.
  destruct v'5.
  (*v'5 is nil ->  false*)
  replace ((e :: v'4) ++ nil) with (e :: v'4).

  hoare lift 5%nat pre.
  apply hoare_pure_gen with (p:=(get_last_ptr (e::v'4) = Some Vnull)).
  intros.
  apply evsllseg_get_last_eq in H8; auto.
(*  intro; tryfalse. *)
  hoare_split_pure_all.
  assert (e :: v'4 <> nil).
  intros; tryfalse.
  
  apply H2 in H9.
  rewrite <- H9 in H8.
  inversion H8.
  rewrite app_nil_r; auto.
 
  hoare lift 5%nat pre.
  apply hoare_pure_gen with (p:=False).
  intros.
  eapply evsllseg_ptr_dup_false; eauto.
  
  (*apply H4.
  symmetry; auto.*)
  hoare_split_pure_all; tryfalse.
  apply disj_rule.
  solve_Afalse_in_pre.
  
(*prove: v'4 is not nil, v'5 is not nil,
         the last ptr of v'4 points to the head of v'5,
         so the head of v'5 is the node we will remove.
 *)
  hoare_split_pure_all.
  destruct v'4.
(*v'4 is nil, false*)
  assert (Vptr v'7 = v'6) by (apply H; auto).
  substs.
  simpl in H5.
  destruct v'7.
  rewrite peq_true in H5.
  rewrite Int.eq_true in H5.
  destruct H5; tryfalse.

(*v'4 is not nil, prove v'5 is not nil*)
  destruct v'5.
(*v'5 is nil, false*)  
  assert (Some (Vptr v'7) = get_last_ptr (e :: v'4)).
  apply H2; auto.
  (*intro; tryfalse.*)

  replace ((e :: v'4) ++ nil) with (e:: v'4).
  hoare lift 5%nat pre.
  apply hoare_pure_gen with (p:=(get_last_ptr(e::v'4) = Some Vnull)).
  intros.
  apply evsllseg_get_last_eq in H7; auto.
  (*intro; tryfalse.*)
  
  hoare_split_pure_all.
  rewrite H7 in H6.
  inversion H6.
  rewrite app_nil_r; auto.
(*v'4, v'5 are not nil*)
(*v'2 is not nil*)
  destruct v'2; simpl in H0; inverts H0.
(*v'3 is not nil*)
  destruct v'3.
  hoare lift 5%nat pre.
  apply hoare_pure_gen with (p:=False).

  intros.
  apply evsllseg_list_len_eq' in H0.
  simpl in H0.
  inverts H0.
  rewrite app_length in H8.
  rewrite app_length in H8.
  rewrite H7 in H8.
  apply plus_reg_l in H8.
  simpl in H8; tryfalse.
  hoare_split_pure_all; tryfalse.

(*generate a more explicit pre condition*)
  assert (v'6 <> (Vptr v'7)).  
  intro; substs.
  simpl in H5; destruct v'7.
  rewrite peq_true in H5; rewrite Int.eq_true in H5.
  simpl in H5; destruct H5; tryfalse.
   
(*L7: while (p != (OS_EVENT * )0 && x == 0) *)
  eapply seq_rule.
(*LOOP INV*)
  apply backward_rule1 with (p:= (
    (EX v ectrl1 ectrl2 msgql1 msgql2,
     <|| aop ||> **
         LV x @ Int8u |-> (V$0) **
         LV p1 @ os_ucos_h.OS_EVENT ∗ |-> v **
         LV p @ os_ucos_h.OS_EVENT ∗ |-> v **
         evsllseg v'6 v ectrl1 msgql1 **
         evsllseg v Vnull ectrl2 msgql2 **
         [| ectrl1 ++ ectrl2 = (e::v'4) ++ e0 :: v'5 /\
            msgql1 ++ msgql2 = (e1::v'2) ++ e2 :: v'3 |] **
         [|ptr_in_ectrls v'6 ectrl1 (Vptr v'7) = false|] **
         [|v <> (Vptr v'7) /\ v <> Vnull|](*the segment pointed by v is not nil, if pevent is not found*) **
         LV pevent @ os_ucos_h.OS_EVENT ∗ |-> Vptr v'7
         ** H4
    )
     \\//
    (EX a ectrl1 ectrl2 msgqls1 msgqls2 osevent etbl msgq,
     <|| aop ||> **
         LV x @ Int8u |-> (V$1) **
         LV p1 @ os_ucos_h.OS_EVENT ∗ |-> Vptr v'7 **
         LV p @ os_ucos_h.OS_EVENT ∗ |-> Vptr a **
         LV pevent @ os_ucos_h.OS_EVENT ∗ |-> Vptr v'7 **
         evsllseg v'6 (Vptr a) ectrl1 msgqls1 **
         AEventNode (Vptr a) osevent etbl msgq **
         [|V_OSEventListPtr osevent = Some (Vptr v'7)|] **
         evsllseg (Vptr v'7) Vnull ectrl2 msgqls2 **
         [|ectrl1 ++ (osevent, etbl)::ectrl2 = ((e::v'4) ++ e0 :: v'5) /\
           msgqls1 ++ msgq::msgqls2 = ((e1::v'2) ++ e2 :: v'3) |] **
         [|Vptr a <> Vptr v'7|] ** [|ptr_in_ectrls v'6 ectrl1 (Vptr v'7) = false|] **
         H4)
   )).
 
(*before the while loop, prove PRE implies the LOOP INV*)
  intros.
  left.
  exists v'6 (nil:list EventCtr) ((e :: v'4) ++ e0 :: v'5) (nil:list EventData) (((e1 :: v'2) ++ e2 :: v'3)).
  do 4 (sep cancel 1%nat 1%nat).
  unfold evsllseg at 1.
  sep pauto.
  split.
  pauto.
  intro; substs.
  rewrite <- app_comm_cons in H6.
  eapply evsllseg_vnull_false_p.
  eauto.  
  
  apply ptr_in_ectrls_nil_false.
  intro.
  substs.
  simpl in H5; destruct v'7; rewrite peq_true in H5; rewrite Int.eq_true in H5.
  simpl in H5; destruct H5; tryfalse.
(*loop inv of while in pre condition*)

  eapply while_rule.
  intros.
  destruct H6.
  do 5 destruct H6.
  sep lift 6%nat in H6; pose proof evsllseg_isptr H6; pauto.
  symbolic execution; pauto.
  rewrite Int.eq_true.
  (*simpl; intro; tryfalse.*)

  apply isptr_vundef1; auto.
  do 8 destruct H6.
  symbolic execution.
  destruct x.
  simpl; intro; tryfalse.
  destruct x.
  simpl; intro; tryfalse.
  (*simpl; intro; tryfalse.*)
  destruct x.
  rewrite Int.eq_false; simpl; intro; tryfalse.
  
  apply disj_conj_distrib_pre.
  apply disj_rule.
  eapply backward_rule1.
  eapply sep_aconj_r_aistrue_to_astar.
  intros.
  do 5 destruct H6.
  sep lift 6%nat in H6; pose proof evsllseg_isptr H6; pauto.
  instantiate (2:=Int32u).
  instantiate (1:=Vint32 Int.one).
  symbolic execution; pauto.
  (*rewrite Int.eq_true.
  simpl; intro; tryfalse.*)
  destruct H11.
  unfolds in H8.
  rewrite Int.eq_true.
  simpl val_inj.
  destruct x; destruct H8; try solve [tryfalse | destruct H8; tryfalse].
  simpl; destruct a; simpl.
  auto.
  (*intro; tryfalse.*)
  
(*L8: p1 = p -> OSEventListPtr;*)
  hoare_split_pure_all.
  hoare lift 6%nat pre.
  apply hoare_pure_gen with (p:=(isptr v'8)).
  intros.

  eapply evsllseg_head_isptr'.
  eauto.
  hoare_split_pure_all.
(*prove v'10 and v'12 are not nill, so we can unfold the mqsllseg for one node*)
  assert (exists x, v'8 = Vptr x).
  unfolds in H11.
  destruct H9.
  destruct H11; substs; tryfalse.
  eauto.
  destruct H12; substs.
  eapply hoare_pure_gen; intros.
  eapply evsllseg_has_node; eauto.
  hoare_split_pure_all.
  simpljoin1.
  unfold evsllseg at 2; fold evsllseg.
  unfold AEventNode at 2.
  unfold AOSEvent.
  unfold node.
  destruct x0.
  hoare_split_pure_all.
  destruct H3.
  assert(exists v1 v2 v3 v4 v5 v6 tail, v = v1::v2::v3::v4::v5::v6::tail).
  apply struct_type_vallist_match_os_event; auto.

  simpljoin1.
  hoare lift 5%nat pre.
  inverts H3.
  hoare forward.
  pure_auto.
 
(*L9: if(p1 != pevent) *)
  unfolds in H18; simpl in H18; inverts H18.
  hoare lift 6%nat pre.
  eapply hoare_pure_gen.
  intros; eapply evsllseg_head_isptr'; eauto.
  hoare forward; pauto.
  apply isptr_val_inj_vundef; auto.

(*L10: p = p1;*)
  hoare forward.
  pauto.

(*L11: x = 1; *)
  hoare forward.

(*proof the loop inv hold after the loop body*)
destruct H3.
(*1: the case of x=0*)  
  left.
  exists v'8 (v'9 ++ (x0 :: v'12 :: x5 :: x6 :: x7 :: v'8 :: x9, v0)::nil) x1.
  exists (v'11 ++ x2 :: nil) x3.
  sep pauto.
  sep cancel 1%nat 1%nat.
  do 5 sep cancel 5%nat 2%nat.
  sep lift 4%nat in H3.
  eapply evsllseg_append1; eauto.
  split.
  intro.
  substs.
  simpl in H18; destruct v'7.
  rewrite peq_true in H18; rewrite Int.eq_true in H18; simpl in H18.
  rewrite notbool_one_zero in H18.
  tryfalse.
  intro; substs.
  sep lift 2%nat in H3.
  pose proof evsllseg_vnull_nil_p H3.
  destruct H25; substs.
  assert (e::v'4 <> nil).
  intro; tryfalse.

  apply H2 in H25; symmetry in  H25.

  apply (get_last_ptr_ptr_in_ectrls_true (e::v'4) v'7 v'6 e0 v'5) in H25.
  rewrite <- H6 in H25.
  
  sep lift 8%nat in H3.
  apply evsllseg_get_last_eq_p in H3.

  intros.
  erewrite ptr_in_ectrls_false_append in H25; eauto.
  inversion H25.
  intro; substs.
  rewrite app_nil_l in H6.
  inversion H6.
  destruct v'4.
  rewrite app_nil_l in H33; tryfalse.
  rewrite <- app_comm_cons in H33; tryfalse.

  destruct v'9.
  rewrite app_nil_l.
  unfolds.
  destruct (val_beq v'6 (Vptr v'7)) eqn : eq1.
  apply val_beq_true_eq in eq1; substs.
  unfold val_inj in H5.
  simpl in H5; destruct v'7.
  rewrite peq_true in H5; rewrite Int.eq_true in H5.
  destruct H5; tryfalse.
  simpl; auto.
  
  eapply ptr_in_ectrls_false_append; eauto.
  sep lift 8%nat in H3.
  apply evsllseg_get_last_eq_p in H3; auto.
  (*intro; tryfalse.*)
  
  rewrite <- list_cons_assoc.
  rewrite <- H6.
  rewrite <- list_cons_assoc.
  rewrite <- H15.
  auto.
  
(*2: the case of x=1*) 
  right.
  exists (v'13, Int.zero) v'9 x1 v'11 x3 (x0 :: v'12 :: x5 :: x6 :: x7 :: v'8 :: x9).
  exists v0 x2.
  assert (v'8 = (Vptr v'7)).
  sep split in H3.
  destruct H18.

  apply val_inj_notint_zero_eq in H18.
  auto.

  apply val_inj_notint_vnull_false in H18; tryfalse.
  substs.
  sep pauto.
  unfold AEventNode.
  unfold AOSEvent.
  unfold node.
  sep pauto; eauto.
  sep cancel 1%nat 3%nat.
  do 7 sep cancel 1%nat 1%nat.
  auto.
  
(*a false case: x = 0 and x = 1 in pre*)
  apply backward_rule1 with (p:=Afalse).
  intros.
  do 9 destruct H6.
  sep split in H6.
  sep remember (1::nil)%nat in H6.
  
  apply aistrue_oand in H8.
  destruct H8.
  clear - H6 H15.
  destruct_s s.
  simpl sat in H6; simpljoin1.
  simpl sat in H15.
  rewrite H8 in H15.
  destruct H15.
  destruct H.
  simpl cmp_int_type in H.
  destruct (load Int8u m (x12, 0)) eqn : eq1; tryfalse.
  apply mapstoval_load in H9.
  erewrite load_mono in eq1; eauto.
  rewrite Int.unsigned_zero in H9.
  rewrite H9 in eq1; inverts eq1.
  simpl in H.
  rewrite Int.eq_false in H.
  inverts H.
  simpl in H1.
  rewrite Int.eq_true in H1; tryfalse.
  intro.
  inversion H2.
  auto.
  solve_Afalse_in_pre.

(*now after the while loop, we have the while inv and the falsehood of the while condition *)
  apply disj_conj_distrib_pre.
  apply disj_rule.
(*the case of x=0*)
  eapply backward_rule1.
  eapply sep_aconj_r_aisfalse_to_astar.
  intros.
  do 5 destruct H6.
  sep lift 6%nat in H6; pose proof evsllseg_isptr H6; pauto.
  instantiate (2:=Int32u).
  instantiate (1:=Vint32 Int.one).
  symbolic execution; pauto.
(*  rewrite Int.eq_true.
  simpl.
  unfolds in H8.
  simpljoin1.
  intro; tryfalse. *)
  rewrite Int.eq_true.
  simpl.
  destruct H11.
  destruct x;
  try solve [destruct H8; [tryfalse | destruct H8; tryfalse]].
  destruct H8.
  simpl; destruct a; simpl.
  rewrite notbool_zero_one.
  unfold Int.ltu.
  rewrite Int.unsigned_zero.
  rewrite Int.unsigned_one.
  simpl; auto.

  simpl; destruct a; simpl.
  rewrite notbool_zero_one.
  unfold Int.ltu.
  rewrite Int.unsigned_zero.
  rewrite Int.unsigned_one.
  simpl; auto.

  (*intro; tryfalse.*)
  
  hoare_split_pure_all.
  destruct H10; tryfalse.

(*the case of x=1*)
  eapply backward_rule1.
  eapply sep_aconj_r_aisfalse_to_astar.
  instantiate (2:=Int32u).
  instantiate (1:=Vint32 Int.zero).
  intros. 
  symbolic execution;destruct x; pauto.
  (*simpl; intro; tryfalse.
  simpl; intro; tryfalse.
  pure_auto.
  intro; tryfalse.*)
  
(*L12: if (x == 1)*)  
  hoare_split_pure_all.
(*prove v'10 and v'12 are not nil*)
  destruct v'10.
  unfold evsllseg at 3.
  hoare_split_pure_all; simpljoin1; tryfalse.
  destruct v'12.
  unfold evsllseg at 3.
  solve_Afalse_in_pre.
(*proved*)
  hoare_split_pure_all.
  unfold evsllseg at 3; fold evsllseg.
  unfold AEventNode at 2 3.
  destruct e3.
  unfold AOSEvent.
  unfold node.
  hoare_split_pure_all.
  assert(exists v1 v2 v3 v4 v5 v6 tail, v'13 = v1::v2::v3::v4::v5::v6::tail).
  destruct H19.
  apply struct_type_vallist_match_os_event; auto.  
  simpljoin1; auto.
  
(*  assert(exists v1 v2 v3 v4 v5 v6 tail, v7 = v1::v2::v3::v4::v5::v6::tail).
  destruct H12.
  apply struct_type_vallist_match_os_event; auto.
 *)
  
  simpljoin1.
  eapply seq_rule.
  eapply ift_rule''.
  instantiate (2:=Int32u).
  instantiate (1:=Vint32 Int.one).
  intros.
  symbolic execution.
  (*intro; tryfalse.*)
  
(*L13: p->OSEventListPtr = p1->OSEventListPtr;*)
  inverts H17.
  inverts H12.
  hoare forward.
  (*pure_auto.*)
  assert(exists v1 v2 v3 v4 v5 v6 tail, v = v1::v2::v3::v4::v5::v6::tail).
  apply struct_type_vallist_match_os_event; auto.
  simpljoin1; simpl.
  omega.
  assert(exists v1 v2 v3 v4 v5 v6 tail, v = v1::v2::v3::v4::v5::v6::tail).
  apply struct_type_vallist_match_os_event; auto.
  simpljoin1.
  
  (*L14: return*) 
  apply disj_rule.
  hoare_split_pure_all.

  hoare_change 13%nat (AEventData (x :: x0 :: x1 :: x2 :: x3 :: x11 :: x5) v'15).
  
  apply ret_rule'.
 
  intros.
  
  sep normal.
  unfolds in H16; simpl in H16; inverts H16.  
  inverts H12; inverts H17.
  unfolds in H6; simpl in H6; inverts H6.

(*prove a property on the list*)
  rewrite list_cons_assoc in H8.
 
assert ((v'9 ++ (x :: x0 :: x1 :: x2 :: x3 :: Vptr (v'22, Int.zero) :: x5, v'14) :: nil) = (e :: v'4)).
  pose proof ecbls_ptr_distinct_get_last_eq (v'9 ++ (x :: x0 :: x1 :: x2 :: x3 :: Vptr(v'22, Int.zero) :: x5, v'14) :: nil) ((x6 :: x7 :: x8 :: x9 :: x10 :: v'19 :: x12, v0) :: v'10) (e::v'4) (e0::v'5) (Vptr (v'22, Int.zero)).
  rewrite <- H8 in Hx.
  apply H6; auto.

  erewrite get_last_app; eauto.
  rewrite <- get_last_get_last_ptr_eq; symmetry.
  apply H2.
  intro; tryfalse.

  rewrite <- H6 in H8.
  apply app_inv_head in H8.
  inversion H8; substs.

  assert (e1 :: v'2  = v'11 ++ v'15 :: nil).
(*length v'11 = length v'9, by H6: length v'9 + 1 = length v'4 + 1,
  length v'4 = length v'2, length v'2 + 1 = length v'4 + 1 = length v'9 + 1 = length v'11 + 1, then by H29*)
  assert (length v'11 = length v'9).
  sep lift 13%nat in H21.
  apply evsllseg_list_len_eq in H21; auto.
  
  assert (length (v'9 ++
       (x :: x0 :: x1 :: x2 :: x3 :: Vptr (v'22, Int.zero) :: x5, v'14)
       :: nil) = length (e::v'4)) by (rewrite H6; auto).
  
  rewrite app_length_tail in H16.
  simpl in H16.
  rewrite list_cons_assoc in H24.
  assert(length ((v'11 ++ v'15 :: nil)) = length (e1 :: v'2)).
  rewrite app_length_tail.
  simpl; rewrite <- H7; rewrite H12; auto.
  clear - H17 H24.
  eapply app_length_eq_eq; eauto.
  
  rewrite H12 in H24.
  rewrite list_cons_assoc in H24.
  apply app_inv_head in H24.
  inversion H24.
  substs.
 
  exists (Vptr (v'22, Int.zero)) (Vptr (v'18, Int.zero)) (V$1) (Vptr (v'22, Int.zero)) (e1 :: v'2) v'3.
  exists (e :: v'4) v'5.
  exists (upd_last_ectrls (e :: v'4) v'19) v'6 v'6 v'19.
  exists (x6 :: x7 :: x8 :: x9 :: x10 :: v'19 :: x12, v0) e2.
  exists (x6 :: x7 :: x8 :: x9 :: x10 :: v'19 :: x12) v0.
  exists (v'22, Int.zero).
  unfold AEventNode.
  unfold AOSEvent.
  unfold node.
  sep pauto; eauto.
  do 4 sep cancel 9%nat 3%nat.
  sep cancel 2%nat 4%nat.
  sep cancel 8%nat 4%nat.
  sep cancel 3%nat 1%nat.
  sep cancel 3%nat 1%nat.
 
  rewrite <- H6.
  rewrite H12.

  rewrite upd_last_ectrls_last.
  unfolds in H14; simpl in H14; inverts H14.
  unfolds in H19; simpl in H19; inverts H19.
  sep lift 3%nat in H21; pose proof evsllseg_isptr H21; pauto.
  
  assert (s |= evsllseg v'6 v'19 (v'9++(x :: v'17 :: x1 :: x2 :: x3 :: v'19 :: x5, v'14) :: nil) (v'11 ++ v'15 :: nil) ** evsllseg v'19 Vnull v'5 v'3).
  sep cancel 1%nat 2%nat.
  sep lifts (4::2::3::1::nil)%nat in H21.
  eapply evsllseg_append1; eauto.
 
  clear - H22 H14.
  unfold struct_type_vallist_match in *.
  unfold os_ucos_h.OS_EVENT in *.
  unfold struct_type_vallist_match' in *.
  simpljoin1; auto.
  unfold rule_type_val_match.
  pauto.

  sep auto.

  eapply evsllseg_merge'; eauto.

  split.
  intros; tryfalse.
  intros.
  split; auto.
  simpl; rewrite H7; auto.
  sep auto.
  
(*false cases*)
  hoare_split_pure_all.
  destruct H3; tryfalse.
Qed.
