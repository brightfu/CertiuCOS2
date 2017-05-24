(**************************  uc/OS-II  ******************************)
(*************************** OS_MBOX.C ******************************)
(****Proofs for API Fucntion:  void* OSMboxAccept(OS_EVENT* pevent***)
(***************************** Code: ********************************)
(***
 Void ∗ ·OSMboxAccept·(⌞pevent @ OS_EVENT∗⌟)··{
        ⌞ 
          message @ Void ∗;
          legal @ Int8u
        ⌟; 
               
1          If(pevent′ ==ₑ NULL)
           {
2              RETURN  〈Void ∗〉 NULL 
           };ₛ
3          ENTER_CRITICAL;ₛ
4          legal′ =ᶠ OS_EventSearch(·pevent′·);ₛ
5          If (legal′ ==ₑ ′0)
           {
6             EXIT_CRITICAL;ₛ
7             RETURN 〈Void ∗〉 NULL 
           };ₛ
8          If (pevent′→OSEventType !=ₑ ′OS_EVENT_TYPE_MBOX)
           {
9             EXIT_CRITICAL;ₛ
10            RETURN 〈Void ∗〉 NULL 
           };ₛ
11          message′ =ₑ pevent′→OSEventPtr;ₛ
12          pevent′→OSEventPtr =ₑ NULL;ₛ
13          EXIT_CRITICAL;ₛ
14          RETURN  message′ 
 }· .
}
***)
Require Import ucos_include.
Require Import Mbox_common.
Require Import os_ucos_h.
Require Import mbox_absop_rules.
Require Import sep_lemmas_ext.
Local Open Scope code_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.


Lemma MboxAcceptProof:
    forall  vl p r tid, 
      Some p =
      BuildPreA' os_api OSMboxAccept mbox_accapi vl  OSLInv tid init_lg ->
      Some r =
      BuildRetA' os_api OSMboxAccept mbox_accapi vl  OSLInv tid init_lg ->
      exists t d1 d2 s,
        os_api OSMboxAccept = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-tid {{p}}s {{Afalse}}.
Proof.
  intros.
  init_spec.
  hoare unfold.
  hoare forward.
  pauto.
  pauto.
  hoare unfold.
  hoare abscsq.
  apply noabs_oslinv.
  eapply absinfer_mbox_acc_err_return.
  can_change_aop_solver.
  auto.
  hoare forward.
  hoare forward.
  hoare unfold.
  assert ( exists xx, x = Vptr xx) by pauto.
  simpljoin.

  hoare unfold.
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
  eauto.
  go.
  go.
  exact retpost_osev.
  Require Import linv_solver.
  linv_solver.
  linv_solver.
  hoare unfold.
(*
  hoare lift 3%nat pre.
*)
  eapply backward_rule1.
  intros;eapply disj_star_elim.
  eauto.

  hoare forward.
  hoare unfold.
  hoare forward.
  change (Int.eq ($ 1 ) ( $ 0)) with false.
  (* simpl; intro; tryfalse. *)
  hoare unfold.
  false.
  int auto.

  (* legal == 0 *)
  Focus 2.
  hoare unfold.
  hoare forward.
  change (Int.eq ($ 0 ) ( $ 0)) with true.
  (* simpl; intro; tryfalse. *)
  hoare unfold.
  hoare forward prim.
  eauto.
  pauto.
  inverts H7.
  hoare abscsq.
  apply noabs_oslinv.
  eapply absinfer_mbox_acc_err_return.
  can_change_aop_solver.
  pauto.
  hoare forward.
  hoare forward.
  hoare unfold.
  false.
  destruct H5; intros.
  int auto.
  int auto.

  (* succ path *)
  hoare forward.
  hoare_split_pure_all.
  false.
  int auto.
  (* succ path *)
  hoare unfold.
  hoare forward.
  (* intro; tryfalse. *)
  struct_type_match_solver.
  int auto.
  (* intro; tryfalse.
   * intro; tryfalse. *)
  unfold OS_EVENT_TYPE_MBOX; omega.
  int auto.
  (* intro; tryfalse.
   * intro; tryfalse. *)
  unfold OS_EVENT_TYPE_MBOX; omega.
  hoare unfold.
  hoare forward prim.
  unfold AECBList.
  sep pauto.
  2: exact H3.
  rewrite list_prop1.
  rewrite list_prop1.
  eapply evsllseg_merge; eauto.
  simpl.
  lets Heq : ecblistp_length_eq H3 H14.
  auto.
  sep cancel 4%nat 1%nat.
  unfold evsllseg; fold evsllseg.
  sep pauto.
  unfold AEventNode.
  sep pauto.
  sep cancel 3%nat 2%nat.
  unfold AOSEvent.
  sep pauto.
  unfold node.
  sep pauto.
  unfold AOSEventTbl.
  sep cancel Astruct.
  sep cancel Aarray.
  sep pauto.
  splits; [ auto| pauto].
  eauto.

  unfolds; simpl.
  eauto.
  pauto.
  unfolds.
  simpl; auto.
  pauto.
  hoare abscsq.
  apply noabs_oslinv.
  inverts H17.
  
  eapply absinfer_mbox_acc_err_return.
  can_change_aop_solver.
  pauto.
  hoare forward.

  hoare forward.

  (*succ path*)
  unfold AEventData.
  hoare unfold.
  apply val_inj_eq in H12.
  subst i0.
  destruct v'41; hoare_split_pure_all; tryfalse.
  inversion H15.
  subst m.
  destruct x2;  try solve [clear -H26;false; clear -H26; unfolds in H26; elim H26; intros; simpljoin; tryfalse].
  hoare forward.
  (* intro; tryfalse. *)
  struct_type_match_solver.
  hoare forward.
  hoare abscsq.
  apply noabs_oslinv.
  inverts H17.
  eapply absinfer_mbox_acc_err_return.
  can_change_aop_solver.
  unfolds; simpl; auto.
  hoare forward prim.
  unfold AECBList.
  sep pauto.
  2: apply H3.
  repeat rewrite list_prop1.
  eapply evsllseg_merge; eauto.
  simpl; auto.

  lets aaa :  ecblistp_length_eq H3 H14.
  auto.
  sep cancel 5%nat 1%nat.
  unfold evsllseg; fold evsllseg.
  unfold AEventNode.
  unfold AEventData.
  unfold AOSEvent.
  unfold node.
  unfold AOSEventTbl.
  sep pauto.
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel evsllseg.
  eauto.
  unfolds; simpl; auto.
  eauto.
  unfolds; simpl; auto.
  pauto.
  splits;[auto | struct_type_match_solver].
  pauto.
  hoare forward.

  (* really succ path *)
  hoare unfold.
  hoare forward.
  (* intro; tryfalse. *)
  struct_type_match_solver.
  hoare forward.
  unfolds in H6.
  destruct v'46.
  destruct e; tryfalse.
  elim H6; intros.

  hoare abscsq.
  apply noabs_oslinv.
  inverts H17.
  eapply absinfer_mbox_acc_succ_return.
  can_change_aop_solver.
  eauto.
  eapply EcbMod.join_get_r.
  eauto.
  eapply EcbMod.join_get_l.
  eauto.
  rewrite <- H12.
  eapply EcbMod.get_a_sig_a.
  apply CltEnvMod.beq_refl.

  hoare forward prim.
  unfold AECBList.
  sep pauto.
  rewrite list_prop1 in H3.
  rewrite list_prop1 in H3.
  instantiate (3:= (v'22 ++
          (V$OS_EVENT_TYPE_MBOX
           :: Vint32 i :: Vint32 i1 :: Vnull :: x3 :: v'42 :: nil, v'40)
          :: v'23) ).
  instantiate (2:=(v'24 ++ DMbox ( Vnull) :: v'25)).
  eapply evsllseg_merge; eauto.
  simpl; auto.

  lets aaa :  ecblistp_length_eq H3 H14.
  auto.
  sep cancel 5%nat 1%nat.
  unfold evsllseg; fold evsllseg.
  unfold AEventNode.
  unfold AEventData.
  unfold AOSEvent.
  unfold node.
  unfold AOSEventTbl.
  sep pauto.
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel evsllseg.
  eauto.
  unfolds; simpl; auto.

  2: unfolds; simpl; auto.
  auto.
  pauto.

  split;[auto|struct_type_match_solver].

  3:pauto.

  Focus 3.
  hoare forward.

  rewrite list_prop1 in H3.
  rewrite list_prop1 in H3.
  apply ecblist_p_decompose in H3.
  simpljoin.
  2:auto.
  unfold ECBList_P in H12; fold ECBList_P in H12.
  simpljoin.

  destruct x4. 


  eapply ecblist_p_compose.
  2:apply H3.
  Focus 2.
  unfold ECBList_P; fold ECBList_P.

  eexists.
  split.
  eauto.
  split.

  eapply R_ECB_ETbl_P_high_ecb_mbox_acpt_hold.
  eauto.


  do 3 eexists.
  splits.
  eauto.
  instantiate (3:= (absmbox Vnull, w0)).
  3: eauto.
  instantiate (1:= (EcbMod.set x1 x2 (absmbox Vnull, w0))).


  eapply ecb_sig_join_sig'_set.
  eauto.
 
  eapply RLH_ECBData_p_high_mbox_acpt_hold.
  eauto.

  lets aaa : ecblist_p_eqh H3 H4.
  instantiate (1:=v'35).

  eapply EcbMod.join_sub_l; eauto.
  eapply EcbMod.join_sub_l; eauto.
  elim aaa; intros.
  inverts H12.
  subst x0.
  Focus 2.
  eapply mbox_acpt_rh_tcblist_ecblist_p_hold; auto.
  Unfocus.
  apply absmbox_ptr_wt_nil in r.
  unfolds in H31.
  destruct e; tryfalse.
  elim H33; intros.
  subst.
  eapply absmbox_ptr_wt_nil in H35.
  subst w0.

  eapply EcbMod.join_set_r.
  eauto.
  unfolds.
  eexists.
  eapply EcbMod.join_get_l.
  eauto.
  exact H32.

  apply EcbMod.get_a_sig_a.
  apply CltEnvMod.beq_refl.

  eapply EcbMod.join_get_r.
  eauto.
  eapply EcbMod.join_get_l.
  eauto.

  apply absmbox_ptr_wt_nil in r.
  subst w.
  apply EcbMod.get_a_sig_a.
  apply CltEnvMod.beq_refl.
  Grab Existential Variables.
  exact Afalse.
Qed.
