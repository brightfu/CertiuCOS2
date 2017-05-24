Require Import sound_include.

Lemma assign_rule_sound : 
  forall (Spec : funspec) (sd : ossched) 
         (I : Inv) (r : retasrt) (ri p : asrt) 
         (e1 e2 : expr) (l : addrval) (v1 v2 : val)
         (tp1 tp2 : type) (aop : absop) 
         (li : LocalInv) (t : tid),
    assign_type_match tp1 tp2 ->
    p ** PV l @ tp1 |-> v1 ==>
      Lv e1 @ tp1 == l //\\ Rv e2 @ tp2 == v2 ->
    p ** PV l @ tp1 |-> v2 ==> CurLINV li t ->
                             RuleSem Spec sd li I r ri 
                                     (
                                       <|| aop ||>  ** p ** PV l @ tp1 |-> v1
                                     )
                                     (sassign e1 e2)
                                     (
                                       <|| aop ||>  ** p ** PV l @ tp1 |-> v2
                                     ) t.
Proof.
  introv Htma Hc Hlin.
  introv Hsat.
  destruct Hsat as (Hsat1 & Hsat2).
  sep split in Hsat1.
  lets Hs : Hc Hsat1.
  simpl in H.
  subst aop0.
  destruct Hs as (Havl & Heval).
  simpl in Havl.
  simpl in Heval.
  destruct Havl as (Ha & Ht).
  destruct Heval as (He & Htt & Hvn).
  destruct  o as [[[[ge le] m] ir ]aux].
  simpl in Ha, Ht, He, Htt.
  constructors; introv Hfalse; tryfalse.  
  introv Hinv Hts1 Hts2 Hlos.
  exists aop OO   (ge,le,m,ir,aux) Ms O Os.
  unfold nilcont in Hlos.
  invertstep idtac.
  splits; eauto.
  constructors.
  eapply skip_expr_eval_msim_hold ; eauto.
  constructors; introv Hff; tryfalse.
  introv Hinvv Htsjm Htsjm' Hloststep.
  invertstep idtac.

  exists  aop OO0  (ge,le,m,ir,aux) Ms0 O Os0. 
  splits; eauto.
  constructors.
  lets Head :  evaladdr_val_eq Ht Ha.
  simpl get_smem in *.
  eapply  skip_expr_eval_msim_hold; eauto.
  constructors; introv Hfff; tryfalse.
  introv Hsinv Htsj1 Htsj2 Hlostep.
  destruct m' as [[G E]  MM].
  assert (tp1 = t1) as H100.
  unfold joinm2 in Hts1.  
  unfold joinmem in Hts1.  
  simp join.
  eapply evaltype_GE_eq; eauto.
  subst.


  lets Hass:assign_loststep_exists' Hlostep   Htsj1 Hsat1.
  destruct Hass as (oo& Hltep).
  destruct Hltep as (Hstep & Httsj1).
  invertstep idtac.
  exists aop OO1.  
  exists(ge0, le0, M', ir, aux) Ms1 O  Os1.
  splits; eauto.
  constructors.


  assert ((ge0, le0, M', ir, aux, O, aop) |= p ** PV l @ t1 |-> v2) as Hpq.
  eapply store_asrt_hold' ; eauto. 
  eapply Hc; eauto.
  lets Hbs : Hlin Hpq.  
  eapply absinfer_sound.local_inv_aop_irev with (aop := aop).
  auto.
  constructors; introv Hf1 ; tryfalse.
  introv _ _ _ Hstep .
  invertstep tryfalse.

  inverts Hf1.
  introv  Hvts Hvinv Hvabs.
  assert ((ge0, le0, M', ir, aux, O, aop) |= p ** PV l @ t1 |-> v2) as Hpq.
  eapply store_asrt_hold' ; eauto. 
  eapply Hc; eauto.
  lets Hbs : Hlin Hpq.  
  exists aop  OO2 O Os2.
  splits; eauto.
  constructors.
  eapply absinfer_sound.local_inv_aop_irev with (aop := aop).
  auto.
  unfold lift.
  sep split; auto.
  destruct Hf1 as (_&_&Hf2&_).
  false.
  apply Hf2. unfolds;  eauto.
  introv Hinnv  Hjmm2  Hddisj Hstep.
  apply Hstep.
  destruct o2 as [[[[G E] M] isr] auxx ].
  unfold joinm2 in *.
  unfold joinmem in *.
  simp join.
  
  lets Heqt : evaltype_GE_eq H2 Ht.
  lets Heqt' : evaltype_GE_eq H4 Htt.
  subst.


  simpl in Hsat1.
  simp join.
  unfolds in H9.
  subst x3.
  assert (x2 = O) by join auto.
  subst x2.
  clear H3.
  assert (join x0 x x34) by join auto.
  assert (join Ms1 x34 x4) by join auto.
  lets Hes :  store_exist_join  H7  H H1 H6.  
  destruct Hes.
  do 2 eexists.
  eapply ostc_step.
  eapply stmt_step.
  eauto.
  constructors; eauto.
  introv _ _ _ Habrt.
  apply Habrt.
  exists ((cure (eaddrof e1)) , (kenil ,(kassignl v2 t1 kstop))) 
         o2.
  destruct o2 as [[mm isr ] ax].
  eapply ostc_step.
  eapply stmt_step; eauto.
  constructors.

  introv Hj1  Hinv Hdisj.
  introv Helo.
  apply Helo.
  exists ((cure e2), (kenil, (kassignr e1 tp1 kstop))) o2.
  destruct o2 as [[[[ge2 le2] m2] ir2] aux2].
  eapply ostc_step.
  eapply stmt_step; eauto.
  unfolds; eauto.
  unfold joinm2 in Hinv.
  unfold joinmem in Hinv.
  simp join.
  constructors;eauto.
  simpl in Ht.
  simpl in Htt.

  eapply evaltype_eq_prop;eauto.
  eapply evaltype_eq_prop;eauto.
Qed.

