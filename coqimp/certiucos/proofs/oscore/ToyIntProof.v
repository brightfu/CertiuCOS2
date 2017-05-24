(**************************  uc/OS-II  *******************************)
(*************************** OS_CORE.C *******************************)
(*************** Proof of Interupt Handler OSToyISR ******************)
(**************************** Code:***********************************)
(*
OSToyISR ↝ 
{
1     ++OSIntToyCount′;ₛ
2     STI;ₛ 
3     EOI(1);ₛ     
4     OSIntExit(­);ₛ
5     IRET
 }.
*)
Require Import ucos_include.
Require Import ToyIntPure.
Require Import oscore_common.
Open Scope code_scope.

Lemma toyisr_proof:
  forall ir si p r ct lg,
    Some p = BuildintPre OSToyISR int_spec ir si I OSLInv ct lg->
    Some r = BuildintRet OSToyISR int_spec ir si I OSLInv ct lg->
    exists s,
      os_interrupt OSToyISR = Some s /\
      {| OS_spec , GetHPrio, OSLInv, I, retfalse, r|}|-ct {{p}}s {{Afalse}}.
Proof.
  intros.
  unfold BuildintPre in H.
  simpl in H.
  unfold ipreasrt' in H.
  inverts H.
  unfold  BuildintRet in H0.
  simpl in H0.
  unfold iretasrt' in H0.
  inverts H0.
  unfold os_interrupt.
  simpl.
  eexists.
  split.
  auto.

  unfold invlth_noisr.
  unfold starinv_noisr.
  simpl.

  eapply backward_rule1.
  instantiate (1:= ( <|| toyint ||>  **
    Aisr (isrupd ir OSToyISR true) **
    Ais (OSToyISR :: si) **
    Acs nil ** Aie false ** 
    [|exists k,
      gettopis (OSToyISR :: si) = k /\
      (forall j : nat, (0 <= j < k)%nat ->  (isrupd ir OSToyISR true) j = false)|] ** OSInv ** atoy_inv ** A_dom_lenv nil) **
    p_local OSLInv ct lg).
  intros.
  sep cancel p_local.
  eapply ih_no_lvar'.
  sep normal.
  sep cancel OSInv.
  sep auto.
  pure intro.
  rename H0 into Hisrinv.

  unfold atoy_inv.
  unfold atoy_inv'.
  hoare forward.
  (* intro;tryfalse. *)
  hoare unfold.
  hoare_abscsq.
  apply noabs_oslinv.
  unfold toyint.
  Require Import int_absop_rules.
  eapply absimp_toy.
  can_change_aop_solver.
  eapply seq_rule.
  hoare lifts (1::22::25::23::24::nil)%nat pre.
  eapply sti1_rule'.

  intros.
  instantiate (1:= atoy_inv'** [|isr_is_prop (isrupd ir 1%nat true) (1%nat::si)|]  ** A_dom_lenv nil ** p_local OSLInv ct lg).
  sep lifts (1::3::5::6::7::8::nil)%nat.
 
  eapply toyint_sti_inv_elim;eauto.
  unfold OSInv.
  unfold atoy_inv;unfold atoy_inv'.
  sep auto.
  apply GoodI_I.
  unfold p_local.
  unfold CurTid,LINV,OSLInv.
  go.
  intros.
  sep auto.
  eapply seq_rule.
  eapply eoi_ieon_rule'.
  simpl.
  rewrite Int.unsigned_repr.
  omega.
  rewrite max_unsigned_val.
  omega.
  instantiate (1:=1%nat).
  rewrite Int.unsigned_repr.
  
  simpl.
  auto.
  rewrite max_unsigned_val.
  omega.
  intros.
  unfold getinv.
  unfold I.
  unfold atoy_inv.
  instantiate (1:=  [|isr_is_prop (isrupd ir 1%nat true) (1%nat :: si)|] **A_dom_lenv nil ** p_local OSLInv ct lg).
  unfold A_isr_is_prop.
  sep auto;eauto.
  destruct_s s.
  simpl in H2,H4.
  subst;simpl;auto.
  apply GoodI_I.
  unfold p_local.
  unfold CurTid,LINV,OSLInv.
  go.
  sep auto.
  sep cancel p_local.
  simpl;auto.
  simpl;auto.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  eapply absinfer_seq_end;eauto.
  go.
  go.
  unfold p_local.
  unfold LINV.
  unfold OSLInv.
  hoare unfold.
  hoare forward.
  instantiate (1:=  [|isr_is_prop (isrupd ir 1%nat true) (1%nat :: si)|] **A_dom_lenv nil).
  sep cancel Aisr.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel 1%nat 1%nat.
  sep cancel 2%nat 4%nat.
  apply disj_split.
  right.
  unfold p_local.
  unfold OSLInv,LINV.
  sep auto.
  auto.
  
  Import DeprecatedTactic.
  split.
  unfold INUM;auto.
  clear -Hisrinv.
  intros.
  apply Hisrinv in H.
  unfold OSToyISR in *.
  unfold isrupd in *.
  destruct (beq_nat 1 j);auto.
  clear -H1.
  unfold isr_is_prop in *.
  intros.
  
  apply H1 in H.
  unfold isrupd in *.
  destruct (beq_nat 1 x );tryfalse;auto.
  simpl;auto.
  intros.
  sep normal in H0.
  sep destruct H0.
  sep split in H0.
  destruct H0.
  sep auto.
  sep split in H0.
  simpl in H0;tryfalse.
  intros.
  sep normal in H0.
  sep destruct H0.
  sep split in H0.
  sep auto.
  hoare unfold.
  inverts H0.
  hoare forward.
  destruct H0.
  unfold p_local in H0.
  sep normal in H0.
  unfold LINV in H0.
  unfold OSLInv in H0.
  sep split in H0.
  sep normal in H0.
  sep destruct H0.
  sep split in H0.
  inverts H15.
  inverts H16.
  sep lift 2%nat in H0.
  apply disj_split in H0.
  destruct H0.
  sep normal in H0.
  sep destruct H0.
  sep split in H0;tryfalse.
  unfold IRINV.
  sep lift 2%nat.
  apply disj_split.
  left.
  unfold iret_ieon.
  unfold isr_inv.
  sep normal.
  exists (isrupd (isrupd ir 1%nat true) 1%nat false) (1%nat).
  assert (s|=Aisr (isrupd (isrupd ir 1%nat true) 1%nat false) ** Aie true ** Ais (1%nat :: v'24)** [| forall j : nat,
            (0 <= j < gettopis (OSToyISR :: v'24))%nat ->
            isrupd ir OSToyISR true j = false |] ** 
           PV get_off_addr ct ($ 24) @ Int8u |-r-> x ** CurTid ct).
  sep split;auto.
  sep auto.
  clear H0.
  sep cancel 5%nat 2%nat.
  sep cancel 5%nat 2%nat.
  clear -H15.
  split.
  split.
  sep auto.
  split.
  simpl.
  sep split in H15.
  split.
  rewrite H3;simpl;auto.
  simpl in H15;auto.
  sep split in H15.
  simpl.
  split.
  intros.
  simpl in H.
  unfold OSToyISR in *.
  simpl in H.
  apply H in H4.
  clear -H4.
  unfold isrupd in *.
  destruct (beq_nat 1 j);auto.
  unfolds in H15;auto.
  sep auto.
  sep split in H0.
  unfolds in H0;tryfalse.
  destruct H0.
  sep auto.
  sep split in H0;unfolds in H0;tryfalse.
  destruct H0.
  sep auto.
  sep split in H0;unfolds in H0;tryfalse.
  
  destruct H0.
  unfold OSToyISR.
  Require Import OSTimeTickPure.
  rewrite isrupd_true_false in H0.
  sep auto.
  sep split in H0;unfolds in H0;tryfalse.
  destruct H0.
  sep auto.
  sep split in H0;unfolds in H0;tryfalse.
Qed.

