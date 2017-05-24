(**************************  uc/OS-II  *******************************)
(*************************** OS_CORE.C *******************************)
(**Proof of Internal Fucntion: void OS_EventTaskWait(OS_EVENT* pevent) **)
(**************************** Code:***********************************)
(*
Void ·OS_EventTaskWait·(⌞pevent @ OS_EVENT∗⌟)··{
       ⌞ ⌟;

1       OSTCBCur′→OSTCBEventPtr =ₑ pevent′;ₛ
2       OSRdyTbl′[OSTCBCur′→OSTCBY] =ₑ 
                 OSRdyTbl′[OSTCBCur′→OSTCBY] &ₑ (∼OSTCBCur′→OSTCBBitX);ₛ
3       If (OSRdyTbl′[OSTCBCur′→OSTCBY] ==ₑ ′0)
        {
4           OSRdyGrp′ =ₑ OSRdyGrp′ &ₑ (∼OSTCBCur′→OSTCBBitY)
        };ₛ
5       pevent′→OSEventTbl[OSTCBCur′→OSTCBY] =ₑ 
               pevent′→OSEventTbl[OSTCBCur′→OSTCBY] |ₑ OSTCBCur′→OSTCBBitX;ₛ
6       pevent′→OSEventGrp =ₑ pevent′→OSEventGrp |ₑ OSTCBCur′→OSTCBBitY;ₛ
7       RETURN
}·. 
*)

(* Require Import ucert. *)
Require Import ucos_include.
Require Import OSETWaitPure.
Open Scope code_scope.


Lemma OSEventTaskWait_proof:
    forall tid vl p r ll, 
      Some p =
      BuildPreI os_internal OS_EventTaskWait
                  vl ll OS_EventTaskWaitPre tid ->
      Some r =
      BuildRetI os_internal OS_EventTaskWait vl ll OS_EventTaskWaitPost tid ->
      exists t d1 d2 s,
        os_internal OS_EventTaskWait = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|- tid {{p}} s {{Afalse}}. 
Proof. 
  init_spec.
  hoare unfold.

  hoare forward.
  hoare unfold.


  lets Hi3: range_ostcby H.
  destruct Hi3 as [Hi3 Hi2].
  assert (Z.to_nat (Int.unsigned i3) < length v'0)%nat.
  {
    rewrite H8.
    unfold OS_RDY_TBL_SIZE.
    
    apply z_le_7_imp_n;auto.
    omega.
  }
  
  lets Hx: array_int8u_nth_lt_len H2 H12.
  Import DeprecatedTactic.
  mytac.
  hoare forward.
  go.
  (* simpl;splits;pauto. *)

  rewrite H8.
  unfold OS_RDY_TBL_SIZE.
  simpl Z.of_nat.
  auto.

(* ** ac:   Locate array_type_vallist_match_imp_rule_type_val_match. *)
  Import symbolic_lemmas.
  
  eapply array_type_vallist_match_imp_rule_type_val_match.
  rewrite H8.
  unfold OS_RDY_TBL_SIZE.
  
  apply z_le_7_imp_n;auto.
  omega.
  auto.

  go.
  (* simpl;splits;pauto. *)
  unfold val_inj.
  unfold and.
  rewrite H27.
  auto.

  go.
  (* simpl;splits;pauto. *)
  unfold OS_RDY_TBL_SIZE.
  simpl Z.of_nat.
  auto.
  rewrite H8.
  unfold OS_RDY_TBL_SIZE.
  simpl Z.of_nat.
  auto.
  (*
  Focus 2.
  hoare lift 8%nat pre.
  apply backward_rule1 with Afalse.
  intros.

  sep remember (1::nil)%nat in H2.
  simpl in H2.
  mytac;auto.
  apply pfalse_rule.
   *)
  unfold AOSRdyGrp.
  hoare forward.
  (* simpl;splits;pauto. *)
  go.
  rewrite H27.

  rewrite <- update_nth_val_length_eq.
  rewrite H8.
  unfold OS_RDY_TBL_SIZE.
  simpl Z.of_nat.
  auto.
  rewrite len_lt_update_get_eq.
  rewrite H27.
  simpl.
  rtmatch_solve.
  apply int_lemma1;auto.
  rewrite H8.
  unfold OS_RDY_TBL_SIZE.
  simpl Z.of_nat.
  auto.
  rewrite H27.
  rewrite len_lt_update_get_eq.
  simpl.
(* ** ac:   Locate "$". *)
  Local Open Scope int_scope.
  destruct (Int.eq (x&ᵢInt.not i2) ($ 0));auto.
  rewrite H8.
  unfold OS_RDY_TBL_SIZE.
  simpl Z.of_nat.
  auto.
  
  eapply forward_rule2.
  hoare forward.

  go.
  (* simpl;splits;pauto. *)
  unfold val_inj.
  unfold and.

  destruct v'1;tryfalse.
  auto.
  intros.
  apply H29.
  apply disj_rule;pure intro.
  clear  H35 H33 H34.
  
  assert (Z.to_nat (Int.unsigned i3) < length v'4)%nat.
  rewrite H9.
  unfold OS_EVENT_TBL_SIZE.
  apply z_le_7_imp_n;auto.
  omega.
  lets Hx:array_int8u_nth_lt_len H4 H33.
  mytac.
  hoare forward.
  go.
  (* simpl;splits;pauto. *)
  rewrite H9.
  unfold OS_EVENT_TBL_SIZE.
  simpl Z.of_nat.
  auto.
  rewrite H34.
  simpl.
  rtmatch_solve.
  go.
  (* simpl;splits;pauto. *)
  rewrite H34.
  simpl.
  auto.
  go.
  (* simpl;splits;pauto. *)

  eapply eq_int;auto.
  rewrite H9.
  unfold OS_EVENT_TBL_SIZE.
  simpl Z.of_nat.
  auto.

  hoare forward.
  go.
  go.
  
  hoare forward.
  simpl;auto.
  simpl;auto.
  2:simpl;auto.
  2:auto.
  4:simpl;auto.
  5:auto.
  6:simpl;auto.
  splits;auto.
  eapply nth_val'_imp_nth_val_int;eauto.
  simpl.
 
  rewrite <- unsigned_to_z_eq.
  rewrite unsigned_to_z_eq.
  rewrite H27.

  simpl.
  auto.
  rewrite unsigned_to_z_eq.
  eapply nth_val'_imp_nth_val_int;eauto.
  splits;auto.
  rewrite <- unsigned_to_z_eq.
  rewrite unsigned_to_z_eq.
  rewrite H34.
  simpl.
  auto.
  split;auto.
  rewrite H27.
  simpl.
  rewrite H27 in H30.
  rewrite len_lt_update_get_eq in H30.
  assert (Int.eq (x &ᵢInt.not i2) ($ 0) =true).
  clear -H30.
  simpl in H30.
  simpl.
  destruct (Int.eq (x &ᵢInt.not i2) ($ 0));tryfalse;auto.

  eapply event_wait_rl_tbl_grp';eauto.
  rewrite H8.
  simpl;auto.
  unfold and.
  unfold val_inj.
  rewrite H27.
  eapply idle_in_rtbl_hold;eauto.

  rtmatch_solve.
  apply int_lemma1;auto.
  split.
  rewrite H27.

  eapply array_type_vallist_match_int8u_update_hold;eauto.
  omega.
  rewrite H27.

  rewrite <- update_nth_val_length_eq.
  auto.
  go.

  rewrite H34.
  eapply event_wait_rl_tbl_grp;eauto.
  simpl;auto.
  apply array_type_vallist_match_hold;auto.
  rewrite H34.
  rtmatch_solve.
  apply int_unsigned_or_prop;auto.
  simpl;splits;auto.
  rtmatch_solve.
  rtmatch_solve.
  apply int_unsigned_or_prop';auto.
  pauto.
  pauto.
  pauto.

  (*------------------------------*)
   
  assert (Z.to_nat (Int.unsigned i3) < length v'4)%nat.
  rewrite H9.
  unfold OS_EVENT_TBL_SIZE.
  apply z_le_7_imp_n;auto.
  omega.
  lets Hx:array_int8u_nth_lt_len H4 H31.
  mytac.
  hoare forward.
  go.
  rewrite H9.
  unfold OS_EVENT_TBL_SIZE.
  simpl Z.of_nat.
  auto.
  rewrite H32.
  simpl.
  rtmatch_solve.
  go.
  rewrite H32.
  simpl.
  auto.
  go.

  eapply eq_int;auto.
  rewrite H9.
  unfold OS_EVENT_TBL_SIZE.
  simpl Z.of_nat.
  auto.

  hoare forward.
  go.
  go.
  
  hoare forward.
   simpl;auto.
  simpl;auto.
  2:simpl;auto.
  2:auto.
  4:simpl;auto.
  5:auto.
  6:simpl;auto.
  splits;auto.
  eapply nth_val'_imp_nth_val_int;eauto.
  simpl.
 
  rewrite <- unsigned_to_z_eq.
  rewrite unsigned_to_z_eq.
  rewrite H27.

  simpl.
  auto.
  rewrite unsigned_to_z_eq.
  eapply nth_val'_imp_nth_val_int;eauto.
  splits;auto.
  rewrite <- unsigned_to_z_eq.
  rewrite unsigned_to_z_eq.
  rewrite H32.
  simpl.
  auto.
  split;auto.
  rewrite H27.
  simpl.
  rewrite H27 in H30.
  rewrite len_lt_update_get_eq in H30.
  assert (Int.eq (x &ᵢInt.not i2) ($ 0) = false).
  clear -H30.
  simpl in H30.
  destruct H30.
  simpl in H.
  destruct (Int.eq (x &ᵢInt.not i2) ($ 0));tryfalse;auto.
  simpl in H.
  destruct (Int.eq (x &ᵢInt.not i2) ($ 0));tryfalse;auto.
  

  eapply event_wait_rl_tbl_grp'';eauto.
  rewrite H8.
  simpl;auto.
  unfold and.
  unfold val_inj.
  rewrite H27.
  eapply idle_in_rtbl_hold;eauto.

  rtmatch_solve.
  split.
  rewrite H27.

  eapply array_type_vallist_match_int8u_update_hold;eauto.
  omega.
  rewrite H27.

  rewrite <- update_nth_val_length_eq.
  auto.
  go.
  simpl.
  rewrite H32.
  eapply event_wait_rl_tbl_grp;eauto.
  simpl;auto.
  apply array_type_vallist_match_hold;auto.
  rewrite H32.
  rtmatch_solve.
  apply int_unsigned_or_prop;auto.
  simpl;splits;auto.
  rtmatch_solve.
  rtmatch_solve.
  apply int_unsigned_or_prop';auto.
  pauto.
  pauto.
  pauto.

Qed.
