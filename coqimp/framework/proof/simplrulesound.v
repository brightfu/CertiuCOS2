Require Import sound_include.

Lemma pure_split_rule_sound: 
  forall P (p:Prop) Spec sd I r ri Q s li t, 
    (
      p -> 
      RuleSem Spec sd li I r ri P s Q t
    ) -> 
    RuleSem Spec sd li I r ri (P ** [| p |]) s Q t. 
Proof.
  intros.
  unfold RuleSem in *.
  intros.
  unfold sat in H0.
  fold sat in H0.
 destruct o as [[[[]]]].
 simpl in *.
  simp join.
  unfolds in H8.
  subst.
  join auto.
Qed.


Lemma  ex_intro_rule_sound: 
  forall Spec sd I r ri {tp:Type} q s p li t,
    (forall v', RuleSem Spec sd li I r ri (p v') s q t) ->
    RuleSem Spec sd li I r ri (EX v : tp, p v) s q t.
Proof.
  intros.
  unfold RuleSem in *.
  simpl.
  intros.
  simp join.
  eapply H;split;eauto.
Qed.

Lemma  disj_rule_sound: 
  forall Spec sd I r ri p1 p2 q s li t,
    RuleSem Spec sd li I r ri p1 s q t ->
    RuleSem Spec sd li I r ri p2 s q t->
    RuleSem Spec sd li I r ri (p1\\//p2) s q t.
Proof.
  intros.
  unfold RuleSem in *.
  simpl.
  intros.
  simp join.
  destruct H1.
  eapply H; split; eauto.
  eapply H0; split; eauto.
Qed. 

Lemma pfalse_rule_sound: 
  forall  Spec sd  I li r ri q s t, 
    RuleSem Spec sd li  I r ri  Afalse s q t.
Proof.
  intros.
  unfold RuleSem.
  intros.
  simp join.
  false.
Qed.


Definition AuxEq G o :=  G = get_genv (get_smem o) .

Lemma  genv_introret_rule_sound_aux :   
  forall (Spec : funspec) sd  (I : Inv) (r : retasrt) 
         (ri : asrt) (q : asrt) (G : env) (C : code) 
         (o : taskst) (aop : absop) (O : osabst) li t,
    AuxEq G o ->
    MethSimMod Spec sd C o aop O li I r ri (lift q) t ->
    MethSimMod Spec sd C o aop O li I  (fun v => (Agenv G//\\ r v))  ri (lift q) t.
Proof.
  introv.
  gen C o aop O.
  cofix Hcofix.
  introv Hg Hsim.
  inverts Hsim.
  constructors; try auto.
  introv Hfcall Hinv Hjm1 Hjm2 Hstep.
  lets Hres : H Hfcall Hinv Hjm1 Hjm2 Hstep.
  simp join.
  do 6 eexists; splits; eauto.
  eapply Hcofix.
  lets Heq : loststep_keepG Hstep.
  eapply get_env_eq; eauto.
  auto.

  introv Hc Hmdisj Hinv Hdisj.
  lets Hres : H0 Hc Hmdisj Hinv Hdisj.
  simp join.
  do 12 eexists; splits; eauto.
  splits;auto.
  introv Hsa.
  splits; eauto.
  eapply H18; eauto.
  introv Hc1 Hc2 Hc3.
  eapply Hcofix.
  destruct o as [[[[]]]].
  destruct o' as [[[[]]]].
  simpl.
  simpl in Hc3.
 destruct Hc3; auto.
 unfolds.
 simpl.
 unfolds in Hg.
 simpl in Hg.  
 subst e.
 auto.

 eapply H18; eauto.
 introv Hc Hc' Hmdisj Hinv .
  lets Hres : H1 Hc Hc' Hmdisj Hinv.
  simp join.
  do 9 eexists ; splits; eauto.
  splits; eauto.
  destruct H17;[left; simp join; eauto | right; eauto].  
  splits; eauto.
  introv Hj Hinn Hjj.
  eapply Hcofix.
  clear - H11 Hinn Hg.
  unfold joinmem in *.
  unfolds.
  join auto.
  eapply H17; eauto.

  introv Hc Hcal Hint Hmdj Hinv Hdisj.
  lets Hres : H3 Hc Hmdj Hinv Hdisj; eauto.
  simp join.
  do 4 eexists; splits; eauto.
  unfold lift in *.
  split;auto.
  simpl; auto.


  introv Hc  Hcal Hint Hmdj Hinv Hdisj.
  lets Hres : H4 Hc Hmdj Hinv Hdisj; eauto.
  simp join.
  do 4 eexists; splits; eauto.
  unfold lift in *.

  introv Hc Hsat Hdisj Hjon.
  lets Hres : H7 Hc Hsat Hdisj Hjon.
  simp join.
  do 14 eexists; splits; eauto.
  splits; eauto.
  eapply Hcofix; eauto.
  clear  -H15 Hg.
  unfold joinmem in  H15.
  join auto.

  introv Hc Hsat Hdisj Hjon.
  lets Hres : H8 Hc Hsat Hdisj Hjon.
  simp join.
  do 5 eexists; splits; eauto.
  destruct H12.
  left.
  simp join.
  do 3 eexists; splits; eauto.
  right.
  simp join.
  do 3 eexists; splits; eauto.
  intros.
  eapply Hcofix; eauto.
  clear -H17 Hg.
  unfolds in H17.
  join auto.
Qed.


Lemma  genv_introret_rule_sound :   
  forall   Spec  sd I r ri p q  s G li t, 
    RuleSem Spec sd li  I r ri p s q t ->
    RuleSem Spec  sd li I (fun v => (Agenv G //\\ r v)) ri
            (Agenv G //\\ p) s q t .
Proof.
  introv Hrus.
  introv Hsat.
  destruct Hsat.
  destruct H.
  simpl in H.
  assert ((o, O, aop) |= p /\ satp o O (CurLINV li t)) by (split; auto).
  lets Hsim : Hrus H2.
  eapply genv_introret_rule_sound_aux; eauto.
Qed.


Lemma   genv_introexint_rule_sound_aux :
  forall (Spec : funspec) sd  (I : Inv) (r : retasrt) 
         (ri : asrt) (q : asrt) (G : env) (C : code) 
         (o : taskst) (aop : absop) (O : osabst) li t,
    AuxEq G o ->
    MethSimMod Spec sd C o aop O li I r ri (lift q) t ->
    MethSimMod Spec sd C o aop O li I  r (Agenv G//\\ ri)  (lift q) t.
Proof.
  introv.
  gen C o aop O.
  cofix Hcofix.
  introv Hg Hsim.
  inverts Hsim.
  constructors; try auto.
  introv Hfcall Hinv Hjm1 Hjm2 Hstep.
  lets Hres : H Hfcall Hinv Hjm1 Hjm2 Hstep.
  simp join.
  do 6 eexists; splits; eauto.
  eapply Hcofix.
  lets Heq : loststep_keepG Hstep.
  eapply get_env_eq; eauto.
  auto.

  introv Hc Hmdisj Hinv Hdisj.
  lets Hres : H0 Hc Hmdisj Hinv Hdisj.
  simp join.
  do 12 eexists; splits; eauto.
  splits;auto.
  introv Hsa.
  splits; eauto.
  eapply H18; eauto.
  introv Hc1 Hc2 Hc3.
  eapply Hcofix.
  destruct o as [[[[]]]].
  destruct o' as [[[[]]]].
  simpl.
  simpl in Hc3.
 destruct Hc3; auto.
 unfolds.
 simpl.
 unfolds in Hg.
 simpl in Hg.  
 subst e.
 auto.

 eapply H18; eauto.
 introv Hc Hc' Hmdisj Hinv .
  lets Hres : H1 Hc Hc' Hmdisj Hinv.
  simp join.
  do 9 eexists ; splits; eauto.
  splits; eauto.
  destruct H17;[left; simp join; eauto | right; eauto].  
  splits; eauto.
  introv Hj Hinn Hjj.
  eapply Hcofix.
  clear - H11 Hinn Hg.
  unfold joinmem in *.
  unfolds.
  join auto.
  eapply H17; eauto.

  introv Hc Hcal Hint Hmdj Hinv Hdisj.
  lets Hres : H5 Hc Hmdj Hinv Hdisj; eauto.
  simp join.
  do 4 eexists; splits; eauto.
  unfold lift in *.
  split;auto.


  introv Hc Hsat Hdisj Hjon.
  lets Hres : H7 Hc Hsat Hdisj Hjon.
  simp join.
  do 14 eexists; splits; eauto.
  splits; eauto.
  eapply Hcofix; eauto.
  clear  -H15 Hg.
  unfold joinmem in  H15.
  join auto.

  introv Hc Hsat Hdisj Hjon.
  lets Hres : H8 Hc Hsat Hdisj Hjon.
  simp join.
  do 5 eexists; splits; eauto.
  destruct H12.
  left.
  simp join.
  do 3 eexists; splits; eauto.
  right.
  simp join.
  do 3 eexists; splits; eauto.
  intros.
  eapply Hcofix; eauto.
  clear -H17 Hg.
  unfolds in H17.
  join auto.
Qed.



Lemma  genv_introexint_rule_sound :   
  forall   Spec sd li I r ri  p q  s G t, 
    RuleSem Spec sd li  I r ri p s q t  ->
    RuleSem Spec sd  li I r (Agenv G //\\ ri)
            (Agenv G //\\ p) s q t .
Proof.
  introv Hrus.
  introv Hsat.
  destruct Hsat.
  destruct H.
  simpl in H.
  assert ((o, O, aop) |= p /\ satp o O (CurLINV li t)) by (split; auto).
  lets Hsim : Hrus H2.
  eapply genv_introexint_rule_sound_aux; eauto.
Qed.


Lemma   sim_retspec_intro :
  forall p sd C gamma o  O I  q li t,
    MethSimMod p sd C o gamma O li I arfalse Afalse q t ->
    forall r ri, MethSimMod p sd C o gamma O li I r  ri q t .
Proof.
  cofix Hcofix.
  introv Hsim.
  introv.
  inverts Hsim.
  constructors; introv Hfalse; tryfalse; try eauto.
  introv Hinv Hj1 Hj2 Hlos.
  lets Hre : H Hinv Hj1 Hj2 Hlos ; eauto.
  simp join.
  do 6 eexists; splits; eauto.
  introv Hmdisj Hinv Hdisj.
  lets Hre : H0 Hfalse Hmdisj Hinv Hdisj.
  simp join.
  do 12 eexists; splits; eauto.
  splits; eauto.
  introv Hevn.
  splits; eauto.
  eapply H18; eauto.
  introv  Hf1 Hf2 Hdsj . 
  eapply Hcofix.  
  eapply H18;eauto.

  introv  Hmdisj Hinc Hdisj .
  lets Hres : H1 Hfalse  Hmdisj Hinc Hdisj; eauto.
  simp join.
  do 9 eexists; splits; eauto.
  splits; eauto.
  destruct H17. 
  left.
  destruct H9.
  split; auto.
  intros.
  eapply Hcofix.
  eapply H17; eauto.
  right.
  auto.
  
  introv Hcall Hint Hmdisj Hinv Hdisj.
  lets Hre : H3 Hfalse Hcall Hint Hmdisj  Hdisj; eauto.
  simp join.
  simpl in H13.
  tryfalse.

  introv  Hcall Hint Hmdisj Hinv Hdisj.
  lets Hre : H4 Hfalse Hcall Hint Hmdisj Hdisj; eauto.
  simp join.
  simpl in H13.
  tryfalse.

  introv Hcall Hint Hmdisj Hinv Hdisj.
  lets Hre : H5 Hfalse Hcall Hint Hmdisj Hdisj; eauto.
  simp join.
  simpl in H13; tryfalse.
  
  introv Hsat Hdisj Hj.
  lets Hks : H7 Hsat Hdisj Hj; eauto.
  simp join.
  do 14 eexists; splits; eauto.
  splits; eauto.


  introv Hsat Hdisj Hj.
  lets Hks : H8 Hsat Hdisj Hj; eauto.
  simp join.
  do 5 eexists; splits; eauto.
  destruct H12; simp join.
  left.
  do 3 eexists; splits; eauto.
  right.
  do 3 eexists; splits.  
  eauto.
  eauto.
  eauto.
  eauto.
  intros.
  eapply Hcofix.
  eapply H15; eauto.
Qed.


Lemma retspec_intro_rule_sound : 
  forall Spec sd I ri r p q s li t, 
    RuleSem Spec sd  li I arfalse Afalse p s q t  -> 
    RuleSem Spec sd  li I r ri p  s q  t.
Proof.
  introv Hsim.
  unfold RuleSem in *.
  introv Hwf.
  lets Hsem : Hsim Hwf.
  eapply Hsim in Hwf.
  eapply sim_retspec_intro ; eauto.
Qed.
