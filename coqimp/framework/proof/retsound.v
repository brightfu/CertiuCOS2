Require Import  sound_include.

Lemma ret_rule_sound :
  forall (Spec:funspec) sd  (I:Inv) (r:retasrt) (p: asrt) li t,
    (p ==> r None )  ->    RuleSem Spec sd  li I r Afalse p sret Afalse t.
Proof.
  introv Hc Hsat.
  constructors; introv Hfalse; tryfalse.
  introv _ _ _ Hstep.
  unfold nilcont in Hstep.
  invertstep tryfalse.
  unfolds in Hfalse.
  inverts Hfalse.
  introv _ _ Htsj Hinv Habsj. 
  lets Hres : Hc Hsat.
  exists aop OO O Os.
  splits; eauto.
  constructors.
  destruct Hsat.
  auto.
  destruct Hfalse as (_&_&_&Hf&_).
  false.
  unfold nilcont in Hf.
  apply Hf.
  eexists;splits;  eauto.
Qed.

(*IReturn Rule Sound*)
Lemma exitint_rule_sound :  
  forall (Spec:funspec) sd (I:Inv) (ri:asrt)  (p: asrt) li t,
    (p ==>  ri )  ->   
    RuleSem Spec sd  li I arfalse ri p  (sprim exint) Afalse t.
Proof.
  introv Hc Hsat.
  constructors; introv Hfalse; tryfalse.
  introv _ _ _ Hstep.
  unfold nilcont in Hstep.
  invertstep tryfalse.
  unfolds in Hfalse.
  inverts Hfalse.
  introv _ _ Htsj Hinv Habsj. 
  lets Hres : Hc Hsat.
  exists aop OO O Os.
  splits; eauto.
  constructors.
  destruct Hsat.
  auto.
  destruct Hfalse as (_&_&_&_&_&Hf&_).
  false.
  unfold nilcont in Hf.
  apply Hf.
  eexists;splits;  eauto.
Qed.

Lemma rete_rule_sound :  
  forall (Spec:funspec) sd (I:Inv) (r:retasrt) (p: asrt) (e : expr) (v: val) 
         (t:type) li tid, 
    (p ==>  r (Some v) //\\  Rv e@t == v ) ->
    RuleSem Spec sd li I r Afalse p (srete e) Afalse tid.
Proof.
  introv Hspec  Hsat.
  lets (Hsat1&Hsat2&Hsat3) : Hspec Hsat.
  simpl in Hsat2.
  destruct o as [[[[]]]].
  eapply identity_step_msim_hold;eauto.
  eapply  notabort_rete.
  introv.
  eapply ostc_step.
  eapply stmt_step;   eauto.
  unfold nilcont.
  eauto.
  constructors.
  destruct Hsat; auto.
  eapply  skip_expr_eval_msim_hold; eauto.
  destruct Hsat; auto.
  constructors;introv Hfalse; tryfalse.
  introv  _ _ _ Hstep.
  invertstep tryfalse.
  simpl in H4;tryfalse.
  inverts Hfalse.
  introv  Hcall Hint Hdss  Hsat11 Habsd.
  exists aop OO O Os.
  simpl in Hsat3.
  splits; eauto.
  constructors.
  destruct Hsat; auto.
  destruct Hfalse as  (_&_&_&_&Hf&_).
  false.
  apply Hf.
  exists v kstop.
  splits; eauto.
Qed.

