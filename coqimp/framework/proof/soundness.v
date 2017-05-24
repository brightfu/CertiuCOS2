Require Import sound_include.
Require Import rulesound.


Theorem RuleSound: 
  forall (Spec:funspec) (sd : ossched) (I:Inv) (r:retasrt) (ri:asrt)
         (pre:asrt) (s:stmts) (post:asrt) lasrt tid,
    InfRules Spec sd lasrt I r ri pre s post tid ->  
    RuleSem Spec sd lasrt I r ri pre s post tid.
Proof.
  introv Hspe.
  inductions Hspe.
  eapply pfalse_rule_sound;eauto.
  eapply pure_split_rule_sound;eauto.
  eapply genv_introret_rule_sound ;eauto.
  eapply genv_introexint_rule_sound ;eauto.
  eapply ret_rule_sound; eauto. 
  eapply exitint_rule_sound; eauto.
  eapply rete_rule_sound;eauto.
  eapply call_rule_sound;eauto. 
  eapply calle_rule_sound; eauto.
  eapply calle_rule_lvar_sound; eauto.
  eapply conseq_rule_sound;eauto.
  eapply conseq_rule_r_sound;eauto.
  eapply abscsq_rule_sound;eauto.
  eapply seq_rule_sound;eauto.
  eapply if_rule_sound;eauto.
  eapply ift_rule_sound; eauto.
  eapply while_rule_sound; eauto.
  eapply frame_rule_sound;eauto.
  eapply frame_rule_all_sound;eauto.
  eapply retspec_intro_rule_sound;eauto.
  eapply assign_rule_sound;eauto.
  eapply encrit1_rule_sound ;eauto.
  eapply encrit2_rule_sound;eauto.
  eapply excrit1_rule_sound ;eauto.
  eapply excrit2_rule_sound;eauto.
  eapply cli1_rule_sound;eauto.
  eapply cli2_rule_sound;eauto.
  eapply sti1_rule_sound;eauto.
  eapply sti2_rule_sound;eauto.
  eapply switch_rule_sound;eauto.
  eapply switch_dead_rule_sound; eauto.
  eapply checkis_rule_sound;eauto.
  eapply eoi_ieon_rule_sound;eauto.
  eapply eoi_ieoff_rule_sound;eauto.
  eapply ex_intro_rule_sound;eauto.
  eapply disj_rule_sound;eauto.
  eapply task_crt_rule_sound; eauto.
  eapply task_delself_rule_sound; eauto.
  eapply task_delother_rule_sound;eauto.
Qed.

Hint Resolve RuleSound.

Lemma WFFunEnv_imply_WFFuncsSim :
  forall P FSpec sd I lasrt, 
    WFFunEnv P FSpec sd lasrt I ->
    WFFuncsSim P FSpec sd lasrt I .
Proof.
  introv Hwfenv.
  unfolds in Hwfenv.
  destruct Hwfenv as [Heqd Hwfenv].
  unfolds.
  split; auto.
  introv Hf.
  lets Hre :  Hwfenv Hf. 
  destruct Hre as (d1&d2&s & Hpf & Htm & Hgood & Hforal).
  do 3 eexists; splits; eauto.
Qed.


Lemma  MethSim_to_Methsim' :  
  forall P FSpec sd  I s r p ri q lasrt tid, 
    GoodI I sd lasrt->
    WFFuncsSim  P FSpec sd lasrt I ->
    RuleSem FSpec sd lasrt I r ri p s q tid->
    (forall o O aop, (o, O, aop) |= p /\ satp o O (CurLINV lasrt tid) -> 
                     MethSim P sd (nilcont s) o  aop O lasrt I r ri (lift q) tid). 
Proof.
  introv goodi.
  introv Hwf Hrsem Hsat.
  lets Hsim : Hrsem Hsat.
  eapply MethSim_to_Methsim'_aux ; eauto.
Qed.

Lemma WFFunEnv_imply_Methsim' :  
  forall P FSpec  sd I lasrt, 
    GoodI I sd lasrt->
    WFFunEnv P FSpec sd lasrt I -> 
    WFFuncsSim' P FSpec sd lasrt I.
Proof.
  introv GoodI.
  introv Hwf. 
  unfolds.
  split.
  destruct Hwf.
  auto.
  introv Hsf.
  lets Hre :  WFFunEnv_imply_WFFuncsSim  Hwf. 
  unfolds in Hre.
  destruct Hre as [Heqd Hre].
  lets Hree : Hre Hsf.
  destruct Hree as (d1 & d2 & s & Hpf & Htm & Hgood & Hforall).
  do 3 eexists; splits; eauto.
  introv Hp Hr.
  lets Hof : Hforall Hp Hr.
  eapply MethSim_to_Methsim'; eauto.
  split; auto.
Qed.

