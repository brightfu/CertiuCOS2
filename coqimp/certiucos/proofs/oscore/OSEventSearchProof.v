(**************************  uc/OS-II  *******************************)
(*************************** OS_CORE.C *******************************)
(*Proof of Internal Fucntion:  BOOLEAN OS_EventSearch (OS_EVETN* pevent)*)
(****************************  Code:   *******************************)
(***
int OS_EventSearch (OS_EVENT *pevent)
{
     OS_EVENT *p, *p1;
     int x;

1    p = OSEventList;
2    x = 0;
3    while (p != (OS_EVENT* )0 && x == 0)
     {
4        p1 = p -> OSEventListPtr;
5        if(p != pevent)
         {
6          p = p1
         }
         else
         {
7          x = 1
         }
     };
8    return x;
}
 ***)
Require Import ucos_include.
Require Import symbolic_lemmas.
Require Import OSESearchPure.

Open Scope code_scope.
Open Scope Z_scope.
Open Scope int_scope.
Open Scope list_scope.


Lemma OSEventSearch_proof:
  forall vl p r logicl tid, 
    Some p =
    BuildPreI os_internal OS_EventSearch vl logicl OS_EventSearchPre tid ->
    Some r =
    BuildRetI os_internal OS_EventSearch vl logicl OS_EventSearchPost tid ->
    exists t d1 d2 s,
      os_internal OS_EventSearch = Some (t, d1, d2, s) /\
      {| OS_spec, GetHPrio, OSLInv, I, r, Afalse |} |-tid {{p}} s {{Afalse}}. 
Proof.
  init_spec.

  (*L1: p = OSEventList *)
  hoare unfold.
  hoare forward.
  pauto.

  (*L2: x = 0 *)
  hoare forward.
  
  (*L3: while (p != (OS_EVENT* )0 && x == 0 *)
  (*1: remember irrelevant sep-conjunctions*)
  hoare remember (1::2::3::5::19::20::nil)%nat pre.

  (*2: get the while loop inv into the pre-condition,
    so the pre-condition after the while statement
    can be correctly instantiated
   *)

  apply backward_rule1 with (p := (*below is the loop inv*)
   (
     (EX v v1 ectrl1 ectrl2 msgqls1 msgqls2 mqls1 mqls2,
      <|| v'16 ||> **
          LV x @ Int8u |-> (V$0) **
          LV p @ os_ucos_h.OS_EVENT ∗ |-> v **
          LV p1 @ os_ucos_h.OS_EVENT ∗ |-> v1 **
          LV pevent @ os_ucos_h.OS_EVENT ∗ |-> Vptr v'14 **
          evsllseg v'17 v ectrl1 msgqls1 ** evsllseg v Vnull ectrl2 msgqls2 **
          [|v'3 = ectrl1 ++ ectrl2|] **
          [|v'2 = msgqls1 ++ msgqls2|] **
          [|ECBList_P v'17 v ectrl1 msgqls1 mqls1 v'13|] ** 
          [|ECBList_P v Vnull ectrl2 msgqls2 mqls2 v'13|] **   
          [|EcbMod.join mqls1 mqls2 v'12|] **
          [|EcbMod.get mqls1 v'14 = None |] ** H0)
       \\//
       (EX vn v1 ectrl1 ectrl2 msgqls1 msgqls2 osevent etbl mqls1 mqls' mqls2 mq msgq,
        <|| v'16 ||> **
            LV x @ Int8u |-> (V$1) **
            LV p @ os_ucos_h.OS_EVENT ∗ |-> (Vptr v'14) **
            LV p1 @ os_ucos_h.OS_EVENT ∗ |-> v1 **
            LV pevent @ os_ucos_h.OS_EVENT ∗ |-> Vptr v'14 **
            evsllseg v'17 (Vptr v'14) ectrl1 msgqls1 **
            evsllseg vn Vnull ectrl2 msgqls2 **
            [|V_OSEventListPtr osevent = Some vn|] **
            AEventNode (Vptr v'14) osevent etbl msgq **
            [|ECBList_P v'17 (Vptr v'14) ectrl1 msgqls1 mqls1 v'13|] **
            [|ECBList_P vn Vnull ectrl2 msgqls2 mqls2 v'13|] **
            [|RLH_ECBData_P msgq mq|] **
            [|v'3 = ectrl1 ++ ((osevent, etbl) :: nil) ++ ectrl2|] **
            [|v'2 = msgqls1 ++ (msgq :: nil) ++ msgqls2|] **
            [|length ectrl1 = length msgqls1|] **
            [|R_ECB_ETbl_P v'14 (osevent, etbl) v'13|] **
            [|EcbMod.joinsig v'14 mq mqls2 mqls' /\ EcbMod.join mqls1 mqls' v'12|] **
            H0)
   )
                            ).
  intros.
  left.
  exists v'17 v'1 (nil : (list EventCtr)) v'3 (nil : (list EventData)) v'2.
  exists EcbMod.emp v'12.
  unfold evsllseg at 1.
  unfold ECBList_P at 1.
  sep pauto.
  apply EcbMod.join_emp; auto.
  (*end 2*)

  (*3: apply the 'seq_rule' to get the while statement
    off the remaining statements, then apply the 'while_rule'
   *)
  eapply seq_rule.
  eapply while_rule with (tp := Int32u).

  (*4: prove the condition expression of while is legal *)
  intros.
  destruct H3. (*2 cases*)
  (*case 1*)
  do 8 destruct H3.
  sep lift 7%nat in H3.
  pose proof evsllseg_isptr H3.
  symbolic_execution.
  pauto.
  destruct x; simpl; intro; tryfalse;
  try (unfolds in H6; destruct H6; [tryfalse | destruct H6; tryfalse]).
  destruct a; simpl in H0; tryfalse.

  destruct x;
    try solve [simpl; unfolds in H6; destruct H6; [tryfalse | destruct H0; tryfalse]].
  simpl; intro; tryfalse.
  simpl; destruct a; simpl; intro; tryfalse.

  rewrite Int.eq_true.
(*  simpl; intro; tryfalse.

  
  rewrite Int.eq_true. *)
  destruct x;
    try solve [simpl; unfolds in H6; destruct H6; [tryfalse | destruct H0; tryfalse]].
  simpl.
  destruct (Int.ltu Int.zero (Int.notbool Int.one) && Int.ltu Int.zero Int.one); simpl; intro; tryfalse.
  simpl; destruct a; simpl.
  destruct (Int.ltu Int.zero (Int.notbool Int.zero) && Int.ltu Int.zero Int.one); simpl; intro; tryfalse.

  (*case 2*)
  do 13 destruct H3.
  sep lift 7%nat in H3.
  pose proof evsllseg_isptr H3.
  destruct v'14.
  symbolic_execution; pure_auto.  
  
  (*5: the cond-expr of while hold implies the left part
    of the loop-inv*)
  apply backward_rule1 with ( p:= (
    (EX v v1 (ectrl1 ectrl2 : list EventCtr)
        (msgqls1 msgqls2 : list EventData) (mqls1 mqls2 : EcbMod.map),
     <|| v'16 ||> **
         LV x @ Int8u |-> (V$0) **
         LV p @ os_ucos_h.OS_EVENT ∗ |-> (Vptr v) **
         LV p1 @ os_ucos_h.OS_EVENT ∗ |-> v1 **
         LV pevent @ os_ucos_h.OS_EVENT ∗ |-> Vptr v'14 **
         evsllseg v'17 (Vptr v) ectrl1 msgqls1 **
         evsllseg (Vptr v) Vnull ectrl2 msgqls2 **
         [|v'3 = ectrl1 ++ ectrl2|] **
         [|v'2 = msgqls1 ++ msgqls2|] **
         [|ECBList_P v'17 (Vptr v) ectrl1 msgqls1 mqls1 v'13|] **
         [|ECBList_P (Vptr v) Vnull ectrl2 msgqls2 mqls2 v'13|] **
         [|EcbMod.join mqls1 mqls2 v'12|] ** [|EcbMod.get mqls1 v'14 = None|]
         ** H0)
                                 )).
  intros.
  destruct H3.
  destruct H3. (*2 cases*)
  (*case 1*)
  do 8 destruct H3.
  assert (exists v, x = Vptr v).
  sep lift 7%nat in H3.
  pose proof evsllseg_isptr H3.
  sep remember (3::4::nil)%nat in H3.
  clear - H3 H6 H7.
  destruct_s s.
  simpl in H3; simpljoin1.
  simpl in H6.
  rewrite H25 in H6.
  rewrite H16 in H6.
  unfold uop_type in H6.
  unfold cmp_int_type in H6.
  unfold bop_int_type in H6.
  destruct x; try solve [simpl; unfolds in H7; destruct H7; [tryfalse | destruct H; tryfalse]].
  simp join.
  destruct (load os_ucos_h.OS_EVENT ∗ m (x26, 0)) eqn : eq1; tryfalse.
  destruct (val_eq v Vnull) eqn : eq2; tryfalse.
  destruct (notint v0) eqn : eq3; tryfalse.
  destruct (load Int8u m (x27, 0)); tryfalse.
  destruct (val_eq v2 (V$0)); tryfalse.

  intros.
  pose proof bool_and_true_1 H1 H.
  simp join.
  unfolds in eq3.
  destruct v0; tryfalse.
  inverts eq3.

  pose proof ltu_zero_notbool_true H3.

  pose proof val_eq_zero_neq eq2 H2.
  replace (Int.unsigned Int.zero) with 0 in H17.
  assert (load os_ucos_h.OS_EVENT ∗ x6 (x26, 0) = Some Vnull).
  eapply mapstoval_load; eauto.

(* ** ac:   Print addr. *)
  pose proof load_mono (os_ucos_h.OS_EVENT ∗) (x26,0)%Z H5 H6.
  apply join_comm in H0.
  rewrite H6 in H9.
  pose proof load_mono (os_ucos_h.OS_EVENT ∗) (x26,0)%Z H0 H9.
  rewrite eq1 in H10.
  rewrite H9 in H10.
  inverts H10.
  tryfalse.
  rewrite Int.unsigned_zero; auto.
  eauto.
  destruct H7.
  substs.
  do 8 eexists.
  sep auto.

  (*case 2*)
  do 13 destruct H3.
  sep remember (2::3::nil)%nat in H3.
  destruct_s s.
  simpl in H3; simpljoin1.
  simpl in H6.
  rewrite H21, H30 in H6.
  unfold uop_type in H6.
  unfold cmp_int_type in H6.
  unfold bop_int_type in H6.
  destruct (load os_ucos_h.OS_EVENT ∗ m (x38, 0)).
  destruct (load Int8u m (x39, 0)) eqn : eq1.
  destruct (val_eq v0 (V$0)) eqn : eq2.
  destruct (val_eq v Vnull).
  destruct (notint v2).
  simpljoin1.

  pose proof bool_and_true_gt H0 H3.
  simpljoin1.
  clear H9 H0.

  apply mapstoval_load in H31; auto.
  pose proof (load_mono Int8u (x39, Int.unsigned Int.zero) H8 H31).
  rewrite H31 in H0.
  rewrite Int.unsigned_zero in H0.
  rewrite eq1 in H0.
  inverts H0.
  simpl in eq2.
  rewrite Int.eq_false in eq2.
  inverts eq2.
  apply Int.ltu_inv in H10; omega.
  intro; tryfalse.
 
  simpljoin1; tryfalse.
  simpljoin1; tryfalse.
  destruct (val_eq v Vnull); simpljoin1; tryfalse.
  destruct (notint v1); simpljoin1; tryfalse.
  destruct (val_eq v Vnull); simpljoin1; tryfalse.
  destruct (notint v0); simpljoin1; tryfalse.
  simpljoin1; tryfalse.

  (*L4: p1 = p -> OSEventListPtr *)
  (* extract the node which p points to*)  
  hoare_ex_intro.
  destruct v'21.
  simpl evsllseg at 5.
  hoare_split_pure_all; simpljoin1.
  inversion H3.
  destruct v'23.
  simpl evsllseg at 5.

  Ltac solve_Afalse_in_pre :=
    eapply backward_rule1 with (p:=Afalse);
    [intros s_1 H_1; destruct_s s_1; simpl in H_1; simpljoin1; tryfalse |
     apply pfalse_rule].
  solve_Afalse_in_pre.

  unfold evsllseg at 5; fold evsllseg.

  destruct e.
  unfold AEventNode at 1.
(*  destruct e0. *)
  pure intro.
  unfold AOSEvent at 2; unfold node.
  pure intro.
  hoare forward; pure_auto.

  (*L5: if(p != pevent)*)
  hoare normal pre; hoare_ex_intro.
  eapply forward_rule2.
  eapply if_rule2'.
  symbolic_execution.
  destruct v'14.
  destruct (peq v'27 b).
  destruct (Int.eq Int.zero i2); simpl; intro; tryfalse.
  simpl; intro; tryfalse.
  destruct v'14.
  destruct (peq v'27 b).
  destruct (Int.eq Int.zero i2); simpl; auto.
  simpl; intro; tryfalse.
(*  simpl; intro; tryfalse.
  simpl; intro; tryfalse.*)
  
  (*L6: p=p1*)
  hoare_split_pure_all.
  hoare forward.
  pauto.
  
  (*L7: x=1*)
  hoare_split_pure_all.
  hoare forward.

  (*prove the loop inv hold after the if statement*)
  intros.
  destruct H0.
  left.
(*  simpl AEventData in H0. *)
  sep split in H0.
(*
  unfolds in H5; simpl in H5; inverts H5.
  unfolds in H7; simpl in H7; inverts H7.
*)
  
  (*if true, p=p1*)
  exists v'26 v'26
         (v'20 ++ (Vint32 i0 :: Vint32 i :: Vint32 i1 :: x2 :: x3 :: v'26 :: nil, v0)::nil) v'21 (v'22 ++ e0::nil).
  exists v'23.
  unfold ECBList_P in H9; fold ECBList_P in H9; simpljoin1.
  unfolds in H27; simpl in H27; inverts H27; inverts H9.
  exists (EcbMod.merge v'24 (EcbMod.sig (v'27, Int.zero) x0)) x1.
(*   sep split in H0.
  mytac. *)

  (*prove (v'28, Int.zero) <> (b, i2)*)
  destruct v'14.
  assert ((v'27, Int.zero) <> (b, i2)).
  destruct (peq v'27 b) eqn : eq1.
  destruct (Int.eq Int.zero i2) eqn : eq2.
  simpl in H3.
  unfold Int.notbool in H3.
  rewrite Int.eq_false in H3.
  tryfalse.
  auto.
  intro.
  inversion H7.
  rewrite H31 in eq2.
  rewrite Int.eq_true in eq2; tryfalse.
  pose proof peq v'27 b.
  destruct H7; tryfalse.
  intro.
  inversion H7.
  rewrite H27 in n0.
  tryfalse.
  clear H3 H24 H25.
  sep split; auto.
  (*end*)

  sep pauto.
  sep lift 4%nat in H0.
  eapply evsllseg_append; eauto.
  pauto.

  rewrite EcbMod.merge_sem.
  rewrite H11.

  rewrite EcbMod.get_sig_none; auto.

  clear - H10 H28.
  eapply EcbMod.join_shift_l; eauto.

  sep remember (3::9::nil)%nat in H0.
  clear - H8 H29 H0 H28 H26.
  eapply ECBList_P_append; eauto.
  unfold TcbJoin in H28.
  unfold join, sig in H28; simpl in H28.
  eauto.
  
  apply list_cons_assoc.
  apply list_cons_assoc.

  (*if false, x=1*)
  right.

  (*prove (v'28, Int.zero) = (b, i0)*)
  (*line: a*)sep split in H0.  (*problem here: all the pure assertions are split out*)
  destruct v'14.
  assert ((v'27, Int.zero) = (b, i2)).
  clear - H3.
  destruct (peq v'27 b) eqn : eq1.
  destruct (Int.eq Int.zero i2) eqn : eq2.
  simpl in H3.
  unfold Int.notbool in H3.
  rewrite Int.eq_false in H3.
  pose proof Int.eq_spec Int.zero i2.
  rewrite eq2 in H.
  destruct H3; tryfalse.
  substs; auto.
  intro; tryfalse.
  simpl in H3.
  unfold Int.notbool in H3.
  rewrite Int.eq_true in H3.
  destruct H3; tryfalse.
  simpl in H3.
  unfold Int.notbool in H3.
  rewrite Int.eq_true in H3.
  destruct H3; tryfalse.
  clear H3.
  inversion H24; substs; clear H24.
  (*end*)


  unfold ECBList_P in H9; fold ECBList_P in H9.
  simpljoin1.
  (*have to manually instantiate the EX variables.
  can not use 'sep pauto' first because some of the register assertions split into the context at line:a are not easy to apply when 'sep auto' has changed 's'*)
  unfold V_OSEventListPtr in H9; simpl in H9; inverts H9.
  destruct x; inverts H3.
  exists x4 x4 v'20 v'21 v'22 v'23.
  exists (Vint32 i0 :: Vint32 i :: Vint32 i1 :: x2 :: x3 :: x4 :: nil)
         v0 v'24 v'25 x1 x0.
  exists e0.
  sep split; auto.
  sep pauto.
  unfold AEventNode.
  unfold AOSEvent.
  unfold node.
  sep pauto; eauto.
  split; pauto.

  sep remember (9::nil)%nat in H0.
  eapply evsllseg_list_len_eq; eauto.

  (*L8:  return x*)
  apply disj_conj_distrib_pre.
  apply disj_rule.

  (*the right case, return 1*)
  eapply rete_rule' with (t := Int8u); intros.
  (*s|= LV x @ Int8u |-> (V$0) ** P -> s |= Rv x' @ Int8u == (V$0)*)
  instantiate (1:=(V$0)).

  destruct H3.
  symbolic_execution.

  pauto.
  substs.
  destruct H3.
  do 8 destruct H0.
  assert (x = Vnull).
  sep lift 7%nat in H0.
  pose proof evsllseg_isptr H0.
  sep remember (3::4::nil)%nat in H0.
  clear - H0 H3 H6.
  destruct_s s; simpl in H0; simpljoin1.
  simpl in H3.
  rewrite H25 in H3.
  rewrite H16 in H3.
  unfold uop_type in H3.
  unfold cmp_int_type in H3.
  unfold bop_int_type in H3.
  destruct (load Int8u m (x27, 0)) eqn : eq1.
  replace (Int.unsigned Int.zero) with 0 in *.
  apply mapstoval_load in H26.
  pose proof load_mono Int8u (x27, 0) H0 H26.
  rewrite eq1 in H.
  rewrite H26 in H.
  inverts H.
  unfold val_eq at 2 in H3.
  rewrite Int.eq_true in H3.
  simpljoin1.
  destruct (load os_ucos_h.OS_EVENT ∗ m (x26, 0)) eqn : eq2; tryfalse.
  destruct (val_eq v Vnull) eqn : eq3; tryfalse.
  destruct (notint v0) eqn: eq4; tryfalse.
  unfolds in H.
  destruct v1; tryfalse.
  destruct (Int.ltu Int.zero i2 && Int.ltu Int.zero Int.one) eqn : eq5.
  inverts H.
  simpl in H1.
  rewrite Int.eq_false in H1.
  tryfalse.
  intro; tryfalse.
  inverts H.
  assert(Int.ltu Int.zero Int.one = true).
  unfolds.
  apply zlt_true.
  rewrite Int.unsigned_zero; rewrite Int.unsigned_one.
  omega.
  rewrite H in eq5.
  rewrite andb_false_iff in eq5.
  destruct eq5; tryfalse.
  unfolds in eq3.
  destruct v; tryfalse.
  apply mapstoval_load in H17.
  pose proof load_mono (os_ucos_h.OS_EVENT ∗) (x26, 0) H8 H17.
  rewrite H17 in H3.
  apply join_comm in H0.
  pose proof load_mono (os_ucos_h.OS_EVENT ∗) (x26, 0) H0 H3.
  rewrite H3 in H4.
  rewrite eq2 in H4.
  inverts H4; auto.
  simpl.
  pauto.
  destruct a0.
  inverts eq3.
  unfolds in eq4.
  unfold Int.notbool in eq4.
  rewrite Int.eq_true in eq4.
  inverts eq4.
  rewrite H in H2; tryfalse.
  auto.
  rewrite Int.unsigned_zero; auto.
  simpljoin1.
  destruct (load os_ucos_h.OS_EVENT ∗ m (x26, 0) ); tryfalse.
  destruct (val_eq v Vnull); tryfalse.
  destruct (notint v0); tryfalse.
  substs.
  
  sep lift 7%nat.
  (*  sep lift 8%nat.*)
  sep cancel 28%nat 1%nat.
(*  sep lift 25%nat in H0. (*can not cancel A_dom_env assertion, ?*)*)
  sep normal.
  exists (Vptr v'14) Vnull (V$0) x0.
  sep pauto.
(*  rename s' into s1. *)
(*  sep cancel 1%nat 1%nat.*)
  right.
  sep pauto.
  sep cancel 1%nat 10%nat.
  do 4 sep cancel 3%nat 2%nat. 
  do 3 sep cancel 3%nat 2%nat.
  
  instantiate (4 := (x1 ++ x2)).
  instantiate (3 := (x3 ++ x4)).
  instantiate (2 := v'4).
  instantiate (1 := v'15).  
  apply ECBList_P_nil in H10; simpljoin1.
  unfold evsllseg at 2 in H0.
  sep split in H0.
  do 2 rewrite app_nil_r.
  auto.
  auto.
  split; auto.

  apply ECBList_P_nil in H10; simpljoin1.
  apply EcbMod.join_comm in H11.
  apply EcbMod.join_emp_eq in H11.
  substs; auto.
  auto.

  (*the left case, return 0*)
  eapply rete_rule' with (t := Int8u); intros.
  instantiate (1 := (V$1)).

  destruct H3.
  symbolic_execution.

  destruct H3.
  do 13 destruct H3.
  unfold AEventNode in H3.
  sep pauto.
  clear H6.
  sep pauto.
  
  sep cancel 20%nat 2%nat.
(*  sep cancel 1%nat 2%nat. *)
  left.
  
  do 27 eexists.
  sep auto; pauto.
Qed.
