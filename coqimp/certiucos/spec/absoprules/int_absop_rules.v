Require Import include_frm.
Require Import os_inv.
Require Import abs_op.
Require Import sep_auto.
Require Import ucos_frmaop.
Require Import abs_step.
Require Import os_code_defs.

Local Open Scope int_scope.

Lemma absimp_toy:
  forall P tls qls curtid tm s sch,
    can_change_aop P ->
    absinfer sch
             ( <||toyint_spec (|nil|) ;; s||> ** HECBList qls **  HTCBList tls ** HTime tm **  HCurTCB curtid ** P)
             ( <||END None;;s ||> ** HECBList qls** HTCBList tls **  HTime tm ** HCurTCB curtid **P).
Proof.
  intros.
  apply absinfer_seq.
  can_change_aop_solver.
  can_change_aop_solver.
  infer_solver 0%nat.
Qed.


Lemma  tcbjoinsig_set_sub_sub:
  forall t x tcbls tcbls' tls y tls',
    TcbMod.joinsig t x tcbls tcbls' ->
    TcbMod.set tls t y = tls' ->
    TcbMod.sub tcbls' tls ->
    TcbMod.sub tcbls tls'.
Proof.
  intros.
  unfolds; intros.
  unfold TcbMod.joinsig in H.
  unfold TcbMod.sub in H1.
  unfold TcbMod.lookup in *.
  pose proof H a.
  substs.
  rewrite H2 in H3.
  destruct (tidspec.beq t a) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite TcbMod.set_a_get_a; auto.
  rewrite TcbMod.get_sig_some in H3; tryfalse.
  pose proof tidspec.beq_false_neq _ _ eq1.
  rewrite TcbMod.get_sig_none in H3; auto.
  destruct (TcbMod.get tcbls' a) eqn : eq2; tryfalse.
  apply H1 in eq2; substs.
  rewrite TcbMod.set_a_get_a'; auto.
Qed.



Lemma tickstep_eqdomtls:
  forall (tls tls_sub:TcbMod.map) qls tls' qls' ,
    TcbMod.sub tls_sub tls ->
    tickstep' tls qls tls' qls' tls_sub->
    eqdomtls tls tls'.
Proof.
  intros.
  inductions H0.
  unfolds.
  intros.
  split;intros.
  unfolds;unfolds in H0.
  simpljoin.
  eexists;eauto.
  unfolds in H0.
  unfolds;simpljoin;eauto.
  assert (eqdomtls tls tls').
  subst tls'.
  eapply tls_get_set_indom;eauto.
  instantiate (1:=(p, st, msg0)).
  eapply TcbMod.get_sub_get;eauto.
  eapply TcbMod.join_get_l.
  eauto.
  eapply TcbMod.get_a_sig_a.
  apply CltEnvMod.beq_refl.
  lets Hx: tcbjoinsig_set_sub_sub H0 H2 H.
  apply IHtickstep' in Hx.
  clear -H4 Hx.
  unfold eqdomtls in *.
  intros.
  lets Ha: H4 tid.
  lets Hb: Hx tid.
  clear H4 Hx.
  split;
    destruct Ha,Hb.
  intros.

  apply H in H3.
  apply H1 in H3;auto.
  intros.
  apply H2 in H3.
  apply H0 in H3.
  auto.
Qed.




Lemma absimp_timetick:
  forall P tls qls tls' qls' curtid tm s sch,
    can_change_aop P ->
    tickstep tls qls tls' qls' ->
    absinfer sch ( <|| timetick_spec (|nil|);;s ||>
                 ** HECBList qls **  HTCBList tls ** HTime tm **  HCurTCB curtid ** P)
           ( <|| END None;;s ||> **                                                                                                                 
                 HECBList qls'** HTCBList tls' **  HTime (Int.add tm Int.one) **
                 HCurTCB curtid **P).
Proof.
  intros.
  apply absinfer_seq.
  can_change_aop_solver.
  can_change_aop_solver.

  idtac.
  (* ** ac: Print absinfer. *)
  eapply absinfer_prim.
  can_change_aop_solver.
  can_change_aop_solver.
  (* ** ac: Print absimp. *)
  unfold absimp.
  intros.
  eexists; exgamma.
  (* infer_part1 0%nat. *)
  (* eexists; exgamma. *)
  splits.
  hmstep_solver.
  assert (eqdomO  
        (set (set O absecblsid (absecblist qls'))
                       abtcblsid (abstcblist tls'))
                  (set
        (set (set O absecblsid (absecblist qls'))
                       abtcblsid (abstcblist tls')) ostmid (ostm (tm+ᵢInt.one)))).
  {
    eapply abst_get_set_eqdom.
    absdata_solver.
    simpl;auto.
  }
  
  assert (eqdomO  (set O absecblsid (absecblist qls')) (set (set O absecblsid (absecblist qls'))
                                                                                abtcblsid (abstcblist tls'))).
  {
    eapply abst_get_set_eqdom.
    absdata_solver.
    simpl.
  
    eapply tickstep_eqdomtls;eauto.
    apply TcbMod.sub_refl.
  }
  
  assert (eqdomO O (set O absecblsid (absecblist qls'))).
  {
    eapply abst_get_set_eqdom.
    absdata_solver.
    simpl;auto.
  }

  (* ** ac: Check tickstep_eqdomtls. *)
  eapply tickstep_eqdomtls;eauto.
  apply TcbMod.sub_refl.
  
  (* eapply eqdomO_trans;eauto. *)
  assert (tidsame (set (set O absecblsid (absecblist qls'))
                                 abtcblsid (abstcblist tls'))
                  (set
                     (set (set O absecblsid (absecblist qls'))
                                    abtcblsid (abstcblist tls')) ostmid (ostm (tm+ᵢInt.one)))).
  {
    tidsame_solver.
  }
  assert (tidsame O
                  (set (set O absecblsid (absecblist qls'))
                       abtcblsid (abstcblist tls'))).
  {
    tidsame_solver.
  }
  
  eapply tidsame_trans; eauto.
  repeat simpl_absdata_sep; sep auto.
Qed.

