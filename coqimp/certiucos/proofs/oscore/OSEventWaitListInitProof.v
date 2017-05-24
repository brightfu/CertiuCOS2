(**************************  uc/OS-II  *******************************)
(*************************** OS_CORE.C *******************************)
(*Proof of Internal Fucntion:
  void OS_EventWaitListInit(OS_EVENT* pevent) *)
(**************************** Code:***********************************)
(*
Void · OS_EventWaitListInit·(⌞pevent @ OS_EVENT∗ ⌟)··{
       ⌞ptbl @ Int8u∗⌟;

1       pevent′→OSEventGrp =ₑ ′0;ₛ
2       ptbl′ =ₑ &ₐ pevent′→OSEventTbl[′0];ₛ
3       ∗ptbl′ =ₑ ′0;ₛ
4       ++ ptbl′;ₛ
5       ∗ptbl′ =ₑ ′0;ₛ
6       ++ ptbl′;ₛ
7       ∗ptbl′ =ₑ ′0;ₛ
8       ++ ptbl′;ₛ
9       ∗ptbl′ =ₑ ′0;ₛ
10      ++ ptbl′;ₛ
11      ∗ptbl′ =ₑ ′0;ₛ
12      ++ ptbl′;ₛ
13      ∗ptbl′ =ₑ ′0;ₛ
14      ++ ptbl′;ₛ
15      ∗ptbl′ =ₑ ′0;ₛ
16      ++ ptbl′;ₛ
17      ∗ptbl′ =ₑ ′0;ₛ
18      RETURN
}·. 
*)

Require Import ucos_include.

Open Scope code_scope.


Lemma OSEventWaitListInit_proof:
    forall  vl p r ll tid, 
      Some p =
      BuildPreI os_internal OS_EventWaitListInit vl ll  OS_EventWaitListInitPre  tid->
      Some r =
      BuildRetI os_internal OS_EventWaitListInit vl ll OS_EventWaitListInitPost tid ->
      exists t d1 d2 s,
        os_internal OS_EventWaitListInit = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio, OSLInv,  I, r, Afalse|}|- tid {{p}} s {{Afalse}}. 
Proof.
  init_spec.
  hoare unfold pre.
  apply vallist_destru in H0; simp join.
  hoare forward.
  hoare forward.
  simpl; auto.
  right. eexists. eauto.
  simpl typelen.
  simpl Int.mul.
  erewrite Int.mul_zero.
  rewrite Int.add_zero.
  rewrite Int.add_zero.
  rewrite eq_1 in *.
  hoare forward;simpl; 
  try rewrite Zdiv_1_r in *;
  try rewrite <-Zminus_diag_reverse; eauto; try omega.
  hoare forward;simpl; 
  try rewrite Zdiv_1_r in *;
  try rewrite <-Zminus_diag_reverse; eauto; try omega.
  pure_auto.
  rewrite  Int.mul_one in *; unfold Int.one; rewrite eq_2 in *.
  hoare forward.
  hoare forward; pure_auto.
  rewrite  Int.mul_one in *; unfold Int.one; rewrite eq_3 in *.
  hoare forward.
  hoare forward; pure_auto.
  rewrite  Int.mul_one in *; unfold Int.one; rewrite eq_4 in *.
  hoare forward.
  hoare forward; pure_auto.
  
  rewrite  Int.mul_one in *; unfold Int.one; rewrite eq_5 in *.
  hoare forward.
  hoare forward; pure_auto.
  
  rewrite  Int.mul_one in *; unfold Int.one; rewrite eq_6 in *.
  hoare forward.
  hoare forward; pure_auto.
  
  rewrite  Int.mul_one in *; unfold Int.one; rewrite eq_7 in *.
  hoare forward.
  hoare forward; pure_auto.

  rewrite  Int.mul_one in *; unfold Int.one; rewrite eq_8 in *.
  hoare forward.
  hoare forward.
  sep auto.
  splits; simpl; auto.
Qed.  
