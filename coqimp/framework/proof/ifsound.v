Require Import  sound_include.

Lemma if_rule_sound :
  forall Spec sd I r ri  p q e tp s1 s2 li t,
    (p ==> EX v , Rv e @ tp ==  v) ->
    RuleSem Spec sd li I r ri  (p//\\ Aistrue e) s1 q t -> 
    RuleSem Spec sd li I r ri  (p //\\ Aisfalse e) s2 q t ->
    RuleSem Spec sd li I r ri  p (sif e s1 s2) q t.
Proof.
  introv Hpre Hsim1 Hsim2.
  introv .
  unfold RuleSem in *.
  introv Hsat.
  lets (Hsat1&Hsat2) : Hsat.
  unfold nilcont.
  eapply identity_step_msim_hold; eauto.
  apply  notabortm_if.
  introv.
  destruct o  as [[m isr]aux].
  eapply ostc_step; eauto.
  eapply stmt_step; eauto.
  constructors.
  lets Hev : Hpre Hsat.
  simpl in Hev.
  destruct Hev as (v & Hee & Het &Hvn).
  simpl in Hee.
  destruct o  as [[m isr]aux].
  simpl get_smem in *.
  eapply skip_expr_eval_msim_hold; eauto.
  assert (istrue v = Some true \/ istrue v  = Some false) as Hasrt.
  destruct v; simpl; try tauto; tryfalse.
  destruct (Int.eq i Int.zero); try tauto.
  destruct Hasrt.
  eapply identity_step_msim_hold; eauto.
  apply notabortm_if_v.
  introv.
  eapply ostc_step;eauto.
  eapply stmt_step; eauto.
  eapply svift_step; eauto.
  assert ((m, isr, aux, O, aop) |= p //\\ Aistrue e) as Hpree.
  split; auto.
  simpl.
  exists v; splits; auto.
  eapply Hsim1;eauto.
  eapply identity_step_msim_hold; eauto.
  apply notabortm_if_v.
  introv.
  eapply ostc_step;eauto.
  eapply stmt_step; eauto.
  eapply sviff_step; eauto.
  assert ((m, isr, aux, O, aop) |= p //\\ Aisfalse e) as Hpree.
  split; auto.
  simpl.
  exists v; splits; auto.
  eapply Hsim2; eauto.
Qed.

Lemma notabortm_ifthen :  
  forall e s,   notabortm (curs (sifthen e s), (kenil, kstop)).
Proof.
  intros.
  unfold notabortm.
  split.
  introv Hf; 
    match goal with
      | H : ?P _ |- _ => unfold P in H; simp join; tryfalse
    end.
  unfold notabort.
  splits;
    introv Hf; 
    match goal with
      | H : ?P _ |- _ => unfold P in H; simp join; tryfalse
    end.
Qed.


Lemma ift_rule_sound : 
  forall Spec sd I r ri  p q e tp s li t,
    (p ==> EX v , Rv e @ tp ==  v) ->
    (p//\\ Aisfalse e ==> q) ->
    RuleSem Spec sd  li I r ri  (p//\\ Aistrue e) s q t  -> 
    RuleSem Spec sd  li I r ri  p (sifthen e s) q t.
Proof.
  introv Hpre Hsim1 Hsim2.
  introv.
  unfold RuleSem in *.
  introv Hsat.
  lets (Hsat1&Hsat2) : Hsat.
  unfold nilcont.
  eapply identity_step_msim_hold; eauto.
  apply notabortm_ifthen.
  introv.
  destruct o  as [[m isr]aux].
  eapply ostc_step; eauto.
  eapply stmt_step; eauto.
  constructors.
  lets Hev : Hpre Hsat.
  simpl in Hev.
  destruct Hev as (v & Hee & Het &Hvn).
  simpl in Hee.
  destruct o  as [[m isr]aux].
  simpl get_smem in *.
  eapply skip_expr_eval_msim_hold; eauto.
  assert (istrue v = Some true \/ istrue v  = Some false) as Hasrt.
  destruct v; simpl; try tauto; tryfalse.
  destruct (Int.eq i Int.zero); try tauto.
  destruct Hasrt.
  eapply identity_step_msim_hold; eauto.
  apply notabortm_if_v.
  introv.
  eapply ostc_step;eauto.
  eapply stmt_step; eauto.
  eapply svift_step; eauto.
  assert ((m, isr, aux, O, aop) |= p //\\ Aistrue e) as Hpree.
  split; auto.
  simpl.
  exists v; splits; auto.
  eapply Hsim2;eauto.
  eapply identity_step_msim_hold; eauto.
  apply notabortm_if_v.
  introv.
  eapply ostc_step;eauto.
  eapply stmt_step; eauto.
  eapply sviff_step; eauto.
  assert ((m, isr, aux, O, aop) |= p //\\ Aisfalse e) as Hpree.
  split; auto.
  simpl.
  exists v; splits; auto.
  lets Hsatq : Hsim1 Hpree.
  constructors; intros; tryfalse.
  false.
  invertstep idtac.
  exists aop OO  O Os.
  splits; eauto.
  constructors.
  destruct H0 as (_&_&Hf&_).
  false.
  apply Hf. eexists.   eauto.
Qed.
