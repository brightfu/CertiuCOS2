Require Import sound_include.

Lemma seq_rule_sound_aux : 
  forall  I r ri p' q FSpec sd s2 li t,  
    (
      forall o O op, 
        ((o, O, op) |= p' /\ satp o O (CurLINV li  t)) ->
        MethSimMod FSpec sd  (nilcont s2) o  op O li I r ri (lift q) t
    )->
    forall c ke ks aop o O, 
      MethSimMod FSpec sd (c, (ke, ks)) o  aop O li I r ri (lift p') t ->
      MethSimMod FSpec sd (c, (ke, (AddStmtToKs s2 ks))) o  aop O li I r ri (lift q) t.
Proof.
  introv Hs2.
  cofix Hcofix.
  introv Hmp.
  inverts Hmp.
  assert (notabortm (c, (ke,ks)) \/ ~notabortm (c, (ke,ks))) as Hasrt.
  tauto.
  destruct Hasrt as [Htrue | Hfalse].
  constructors.
  introv Hfcal Hinv Htj1 Htj2 Hstep.
  destruct C' as [c' [ke' ks']].
  assert (disjoint O Os) as Hdd.
  eexists; eauto.
  lets Hnotabt : H6 p Htrue Hinv Htj1 Hdd.
  rewrite   addstmts_eq_addcont in *.
  lets Hre : cont_frame_mono  Hnotabt Hstep.
  destruct Hre as (cc'&kec'&ks1 & Hlstep & Heqks).
  apply eq_sym in Heqks.
  inverts Heqks.
  lets Hres : H Hinv Htj1 Htj2 Hlstep.  
  eapply fcall_not; eauto.
  simp join.
  do 6 eexists;splits ; eauto.
  rewrite <- addstmts_eq_addcont in *.
  eapply Hcofix;eauto.

  introv Hc.
  inverts Hc.
  unfolds in Htrue.
  destruct Htrue as (Hf & _ ).
  false. apply Hf.
  unfolds.
  do 4 eexists; eauto.

  introv Hc.
  inverts Hc.
  unfolds in Htrue.
  destruct Htrue as  ( _ &Hf&_).
  false. apply Hf.
  do 2 eexists; eauto.


  introv Hc.
  inverts Hc.
  false. 


  eapply addstmts_not_eqkstop; eauto.
  destruct Htrue as  ( _ &_&_&Hf&_).
  introv Hc Hcal Hint.
  false. apply Hf.
  inverts Hc.
  eexists; splits; eauto.
  eapply callcont_none_addstmts; eauto.
  eapply intcont_none_addstmts; eauto.

  introv Hc Hsf Hcall Hint.
  inverts Hc.
  false.
  destruct Htrue as  ( _ &_&_&_&Hf&_).
  false. apply Hf.
  lets Hh : addstmt_kret_exist H12.
  destruct Hh as (ks''& Hks) .
  subst ks.
  inverts H12.
  do 2 eexists; splits; eauto.
  eapply callcont_none_addstmts; eauto.
  eapply intcont_none_addstmts; eauto.
  (*
introv Hc Hsf Hcall Hint.
inverts Hc.
false.

destruct Htrue as  (_&_ & _ &_&_&_&Hf&_).
false. apply Hf.
lets Hh : addstmt_kret_exist H12.
destruct Hh as (ks''& Hks) .
subst ks.
inverts H13.
do 3  eexists; splits; eauto.
eapply callcont_none_addstmts; eauto.
eapply intcont_none_addstmts; eauto.
   *)
  introv Hc Hcall Hint.
  inverts Hc.
  false.
  destruct Htrue as  ( _ &_&_&_&_&Hf&_).
  false. apply Hf.
  eexists; splits; eauto.
  eapply intcont_none_addstmts; eauto.
  eapply callcont_none_addstmts; eauto.

  introv Hnot  Hjm1 Hjm2 Hinv  Hdisj.
  lets Hnotb : H6 p Htrue Hjm1 Hjm2 Hinv.  
  rewrite  addstmts_eq_addcont  in *.
  eapply  loststepabt_cont_loststepabt'; eauto.

  introv Hc.
  inverts Hc.
  destruct Htrue as  ( _ &_&_&_&_&_&Hf&_).
  false.
  apply Hf.
  do 4 eexists; eauto.

  introv Hc.
  inverts Hc.
  destruct Htrue as  ( _ &_&_&_&_&_&_&Hf).
  false.
  apply Hf.
  do 2 eexists; eauto.

  casenot Hfalse. 
  unfolds in Cs.
  destruct Cs as (f0 & vl' & tl & ks0 & Hceq).
  inverts Hceq.
  constructors; introv Hfalse; tryfalse.
  false.  apply Hfalse. 
  unfolds; do 4 eexists; eauto.

  inverts Hfalse.
  introv Hmdisj Hinv Hdisj.
  lets Hres : H0 Hmdisj Hinv Hdisj. eauto.
  simp join.
  do 12 eexists; splits; eauto.
  splits; eauto.
  introv Hk.
  splits; eauto.
  eapply H18; eauto.
  intros.
  eapply Hcofix; eauto.
  eapply H18; eauto.
  destruct Hfalse as ( Hff & Hfalse); tryfalse.
  false. 
  apply Hff.
  unfolds. 
  do 4 eexists; eauto. 

  casenot Hfalse.
  destruct Cs as (x & ks0 & Hceq).
  inverts Hceq.
  constructors; introv Hfalse; tryfalse.
  introv _ _ _ Hlss.
  invertstep tryfalse.
  inverts Hfalse.
  introv Hc' Hmdisj Hinv.
  lets Hres : H1 Hmdisj Hinv ; eauto.
  simp join.
  do 9 eexists; splits; eauto. 
  splits; eauto.
  destruct H17 ;[left; simp join; eauto | right; eauto].


  unfolds in Hfalse. 
  destruct Hfalse as(_& Hf &_).
  false. apply Hf.
  do 2 eexists; eauto.

  casenot Hfalse. 
  destruct Cs as (vv & Hceq).
  inverts Hceq.
  constructors; introv Hfalse; tryfalse.
  introv Hinv Hjm1 Hjm2 Hstep .
  invertstep  tryfalse.
  lets Hres : H2 Hinv Hjm2 ; eauto.
  clear -Hjm1.
  unfolds.
  unfolds in Hjm1.
  unfold joinmem in Hjm1.
  join auto.
  simp join.
  do 6 eexists; splits; eauto.
  lets Hres : H2 Hinv Hjm2 ; eauto.
  clear -Hjm1.
  unfolds.
  unfolds in Hjm1.
  unfold joinmem in Hjm1.
  join auto.
  simp join.
  do 6 eexists; splits; eauto.

  introv _ _ _  Hf.
  apply Hf.
  rewrite  addstmts_eq_addcont in *.
  simpl.
  eexists. exists o2.
  destruct o2 as [[[[]]]].
  eapply ostc_step; eauto.
  eapply stmt_step; eauto.
  destruct vv; constructors.

  casenot Hfalse. 
  destruct Cs as (ks0 & Heqc & Hcal &Hint).
  inverts Heqc.
  constructors; introv Hfalse; tryfalse.
  introv Hinv Hjm1 Hjm2 Hstep.
  invertstep  tryfalse.
  lets Hff :callcont_none_addstmts_rev s2 Hcal. 
  tryfalse.
  inverts Hfalse.
  introv Hcall Hintt Hmdisj Hinv Hdisj.
  rewrite  addstmts_eq_addcont  in *. 
  lets Hres : H3 Hcal Hint Hmdisj Hinv Hdisj.
  eauto. 
  simp join.
  do 4 eexists; splits; eauto. 

  destruct Hfalse as (_&_&_&Hf&_).  
  false.
  apply Hf.
  eexists; splits; eauto.
  eapply callcont_none_addstmts_rev; eauto.
  eapply intcont_none_addstmsts_rev; eauto.

  casenot Hfalse.
  destruct Cs as (v&ks0 & Heqc & Hcal&Hint).
  inverts Heqc.
  constructors; introv Hfalse; tryfalse.
  introv Hinv Hjm1 Hjm2 Hstep.
  invertstep tryfalse.
  lets Hff :callcont_none_addstmts_rev  s2 Hcal. 
  tryfalse.
  inverts Hfalse.
  introv   Hcall Hintt Hmdisj Hinv Hdisj.
  rewrite  addstmts_eq_addcont  in *.
  lets Hres : H4 Hcal Hint Hmdisj Hinv Hdisj; eauto.

  (*
introv  Hfs Hcall Hintt .
rewrite  addstmts_eq_addcont  in *.
lets Hres : H7 Hcal Hint ; eauto.
   *)
  destruct Hfalse as (_&_&_&_&Hf&_).  
  false.
  apply Hf.
  simpl.
  do 2 eexists; splits; eauto.
  eapply callcont_none_addstmts_rev; eauto.
  eapply intcont_none_addstmsts_rev; eauto.


  (*apply Classical_Prop.NNPP in Hfalse.*)

  casenot Hfalse.
  destruct Cs as (ks0 & Heqc &Hint& Hcal).
  inverts Heqc.
  constructors; introv Hfalse; tryfalse.
  introv Hinv Hjm1 Hjm2 Hstep.
  invertstep  tryfalse.
  rewrite  addstmts_eq_addcont  in *.
  lets Hff : intcont_none_addstmsts_rev s2 Hint.
  rewrite  addstmts_eq_addcont  in *.
  tryfalse.
  inverts Hfalse.
  introv Hcall Hintt Hmdisj Hinv Hdisj.
  rewrite   addstmts_eq_addcont  in *.
  lets Hres : H5 Hcal Hint Hmdisj Hinv Hdisj.
  eauto. 
  simp join.
  do 4 eexists; splits; eauto. 
  destruct Hfalse as (_&_&_&_&_&Hf&_).  
  false.
  apply Hf.
  eexists; splits; eauto.
  eapply intcont_none_addstmsts_rev; eauto.
  eapply callcont_none_addstmts_rev; eauto.

  casenot Hfalse.
  destruct Cs as (e1&e2&e3 & ks0 & Hceq).
  inverts Hceq.
  constructors; introv Hfalse; tryfalse.
  introv _ _ _ Hlss.
  invertstep tryfalse.
  unfolds in Hfalse.
  destruct Hfalse as (_&_&_&_&_&_&Hf&_).  
  false.
  apply Hf.
  unfolds.
  exists e1 e2 e3 (AddStmtToKs s2 ks0).
  auto.

  inverts Hfalse.
  introv Hc' Hmdisj Hinv.
  lets Hres : H7 Hmdisj Hinv.  
  eauto.
  auto.
  simp join.
  do 14 eexists; splits; eauto. 
  splits; eauto.

  apply Classical_Prop.NNPP in Hfalse.
  destruct Hfalse as (e & ks0 & Hceq).
  inverts Hceq.
  constructors; introv Hfalse; tryfalse.
  introv _ _ _ Hlss.
  invertstep tryfalse.
  unfolds in Hfalse.
  destruct Hfalse as (_&_&_&_&_&_&_&Hf).  
  false.
  apply Hf.
  unfolds.
  do 2 eexists; eauto.
  inverts Hfalse.
  introv Hc' Hmdisj Hinv.
  lets Hres : H8 Hmdisj Hinv ; eauto.
  simp join.
  do 5 eexists; splits; eauto. 
  destruct H12; simp join.
  left; do 3 eexists; splits; eauto.
  right; do 3 eexists; splits; eauto.
Qed.





Lemma seq_rule_sound :
  forall  Spec sd  I r ri p p' q  s1 s2 li t, 
    RuleSem Spec sd  li I r ri p s1 p' t  -> 
    RuleSem Spec sd  li I r ri p' s2 q  t->
    RuleSem Spec sd li I r ri p (sseq s1 s2) q t.
Proof.
  introv Hs1 Hs2.
  introv Hsat.
  unfold RuleSem  in Hs1.
  unfold RuleSem  in Hs2.
  lets Hms1 : Hs1 Hsat.
  unfold nilcont.
  eapply  identity_step_msim_hold; auto.
  apply  notabort_sseq.
  introv.
  destruct o as [[[[]]]].
  eapply ostc_step; eauto.
  eapply stmt_step; eauto.
  constructors; eauto.
  destruct Hsat; auto.
  assert (kseq s2 kstop = AddStmtToKs s2 kstop).
  simpl.
  auto.
  rewrite H.
  eapply seq_rule_sound_aux ; eauto.
Qed.
