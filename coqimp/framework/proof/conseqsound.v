Require Import sound_include.

Lemma conseq_rule_sound_aux : 
  forall p  sd  I r ri q q' li t,
    (q ==> q') ->
    forall  C o aop O, 
      MethSimMod p sd C o aop O li I  r ri (lift q) t ->
      MethSimMod p sd C o aop O li I  r ri (lift q') t .
Proof.
  introv Himp.
  cofix Hcofix.
  introv Hsim.                               
  inverts Hsim.
  constructors;try auto.
  introv Hfcall Hinv Hjm1 Hjm2 Hlstop.
  lets Hex : H Hfcall Hinv Hjm1.  
  lets Hex' : Hex Hjm2 Hlstop.
  simp join.
  do 6 eexists; splits; eauto.
  introv Hc Hmdisj Hinv Hdisj.
  lets Hex : H0 Hc Hmdisj Hinv Hdisj.
  simp join.
  do 12 eexists; splits; eauto.
  splits; eauto.
  introv Hsa.
  splits; eauto.
  eapply H18; eauto.
  introv Hj1 Hj2 Heq.
  eapply Hcofix.
  eapply H18; eauto.
  introv Hc  Hinv Hjm1 Hjm2.
  lets Hex : H1 Hc   Hinv Hjm1 Hjm2  . 
  simp join.
  do 9 eexists; splits; eauto.
  splits; eauto.
  destruct H17; [simp join; left;split; eauto | right; eauto]. 
 
  introv Hc Hdis Hinv Hdd.
  lets Hsk : H2 Hc Hdis Hinv Hdd.
  simp join.
  do 4 eexists; splits; eauto.
  
  introv Hc  Hinv Hjm1 Hjm2.
  lets Hex : H7 Hc   Hinv Hjm1 Hjm2  . 
  simp join.
  do 14 eexists; splits; eauto.
  splits; eauto.
  introv Hc  Hinv Hjm1 Hjm2.
  lets Hex : H8 Hc   Hinv Hjm1 Hjm2  . 
  simp join.
  do 5 eexists; splits; eauto.
  destruct H12; simp join.
  left; do 3 eexists; splits; eauto.
  right; do 3 eexists;splits; eauto.
Qed.

Lemma conseq_rule_sound :
  forall Spec sd I r ri p' p q q' s li t, 
    (p' ==>  p) ->  (q ==> q') ->
    RuleSem Spec sd li I r ri p s q  t ->
    RuleSem  Spec sd li  I r ri p' s q' t.
Proof.
  introv Himp1 Himp2 Hsim.
  introv .
  unfold RuleSem in *.
  introv Hsat.
  lets (Hsat1 & Hsat2) : Hsat.
  lets Hsatp : Himp1 Hsat1.
  assert ((o, O, aop) |= p /\ satp o O (CurLINV li t)) by (split; auto).
  lets Hsim1 : Hsim  H. 
  eapply  conseq_rule_sound_aux; eauto.
Qed.


Lemma conseq_rule_r_sound_aux :
  forall p sd I r ri ri' q r' li t, 
    (
      forall v,  r v==> r' v
    ) ->
    ri ==> ri' ->
    forall  C o aop O, 
      MethSimMod p sd C o aop O li I  r ri q t ->
      MethSimMod p sd C o aop O li I  r' ri' q t .
Proof.
  introv Himp1 Himp2.
  cofix Hcofix.
  introv Hsim.                               
  inverts Hsim.
  constructors;try auto.
  introv Hfcall Hinv Hjm1 Hjm2 Hlstop.
  lets Hex : H Hfcall Hinv Hjm1.  
  lets Hex' : Hex Hjm2 Hlstop.
  simp join.
  do 6 eexists; splits; eauto.
  introv Hc Hmdisj Hinv Hdisj.
  lets Hex : H0 Hc Hmdisj Hinv Hdisj.
  simp join.
  do 12 eexists; splits; eauto.
  splits; eauto.
  introv Hsa.
  splits; eauto.
  eapply H18; eauto.
  introv Hj1 Hj2 Heq.
  eapply Hcofix.
  eapply H18; eauto.
  introv Hc  Hinv Hjm1 Hjm2.
  lets Hex : H1 Hc   Hinv Hjm1 Hjm2  . 
  simp join.
  do 9 eexists; splits; eauto.
  splits; eauto.
  destruct H17; [simp join; left;split; eauto | right; eauto]. 

  introv Hc Hcal Hint Hdis Hinv Hdd.
  lets Hsk : H3 Hc Hdis Hinv Hdd; eauto.
  simp join.
  do 4 eexists; splits; eauto.
  
   introv Hc Hcal Hint Hdis Hinv Hdd.
  lets Hsk : H4 Hc Hdis Hinv Hdd; eauto.
  simp join.
  do 4 eexists; splits; eauto.

   introv Hc Hcal Hint Hdis Hinv Hdd.
  lets Hsk : H5 Hc Hdis Hinv Hdd; eauto.
  simp join.
  do 4 eexists; splits; eauto.

  introv Hc  Hinv Hjm1 Hjm2.
  lets Hex : H7 Hc   Hinv Hjm1 Hjm2  . 
  simp join.
  do 14 eexists; splits; eauto.
  splits; eauto.
  introv Hc  Hinv Hjm1 Hjm2.
  lets Hex : H8 Hc   Hinv Hjm1 Hjm2  . 
  simp join.
  do 5 eexists; splits; eauto.
  destruct H12; simp join.
  left; do 3 eexists; splits; eauto.
  right; do 3 eexists;splits; eauto.
Qed.

Lemma conseq_rule_r_sound : 
  forall  Spec sd I r r' ri ri' p q s li t, 
    (forall v,r v ==> r' v) ->
    ri ==> ri' ->
    RuleSem Spec sd  li I  r ri p s q  t->
    RuleSem  Spec sd li I  r' ri' p s q t.
Proof.
  introv Himp Himp' Hsim.
  introv .
  unfold RuleSem in *.
  introv Hsat.
  lets Hsim1 : Hsim  Hsat. 
  eapply  conseq_rule_r_sound_aux; eauto.
Qed.


Lemma absconseq_rule_sound_aux : 
  forall p  sd I r ri q q' li t,
    (absimp' sd li q q' t) ->
    forall  C o aop O, 
      MethSimMod p sd C o aop O li I  r ri (lift q) t ->
      MethSimMod p sd C o aop O li I  r ri (lift q') t .
Proof.
  introv Himp.
  cofix Hcofix.
  introv Hsim.                               
  inverts Hsim.
  constructors;try auto.
  introv Hfcall Hinv Hjm1 Hjm2 Hlstop.
  lets Hex : H Hfcall Hinv Hjm1.  
  lets Hex' : Hex Hjm2 Hlstop.
  simp join.
  do 6 eexists; splits; eauto.

  introv Hc Hmdisj Hinv Hdisj.
  lets Hex : H0 Hc Hmdisj Hinv Hdisj.
  simp join.
  do 12 eexists; splits; eauto.
  splits; eauto.
  introv Hsa.
  splits; eauto.
  eapply H18; eauto.
  introv Hj1 Hj2 Heq.
  eapply Hcofix.
  eapply H18; eauto.

  introv Hc  Hinv Hjm1 Hjm2.
  lets Hex : H1 Hc  Hinv Hjm1 Hjm2  . 
  simp join.
  do 9 eexists; splits; eauto.
  splits; eauto.
  destruct H17; [simp join; left;split; eauto | right; eauto]. 

  introv Hc Hdis Hinv Hdd.
  lets Hsk : H2 Hc Hdis Hinv Hdd.
  simp join.
  assert ((o, x1, x) |= lift q v/\  satp o x1 (CurLINV li t)) by (split;auto).
  lets Hss : Himp H14.
  lets Htt : Hss H10.
  simp join.
  lets Hspp : hmstepstar_trans H9 H16.  
  exists x4 x5 x3 x2.
  splits; eauto.
  
  introv Hc  Hinv Hjm1 Hjm2.
  lets Hex : H7 Hc   Hinv Hjm1 Hjm2  . 
  simp join.
  do 14 eexists; splits; eauto.
  splits; eauto.
  introv Hc  Hinv Hjm1 Hjm2.
  lets Hex : H8 Hc   Hinv Hjm1 Hjm2  . 
  simp join.
  do 5 eexists; splits; eauto.
  destruct H12; simp join.
  left; do 3 eexists; splits; eauto.
  right; do 3 eexists;splits; eauto.
Qed.

Lemma abscsq_rule_sound :  
  forall   Spec sd I r ri p' p q q' s li t , 
    absinferfull sd li p' p t -> 
    absinferfull sd li q q' t ->
    RuleSem Spec sd  li I r ri p s q t  ->
    RuleSem  Spec sd  li I r ri p' s q' t.
Proof.
  introv  Himp1 Himp2 Hsim.
  apply absinfersound in Himp1.
  apply absinfersound in Himp2.
  apply absimp_eq_absimp' in Himp1.
  apply absimp_eq_absimp'  in Himp2.
  introv .
  unfold RuleSem in *.
  introv  Hsat.
  unfold absimp' in Himp1.
  lets Hsatt :  Himp1  Hsat.
  constructors; try auto.
  introv Hfcall Hinv Hjm1 Hjm2 Hstep.
  lets Hres : Hsatt  Hjm2.
  destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
  lets Hsm : Hsim  Hsp.
  inverts Hsm.
  lets Hsm : H Hfcall Hinv Hjm1 Hdsjj  Hstep. 
  simp join.
  lets Hks : hmstepstar_trans Hstar H9.
  exists x x0 x1 x2 x3 x4.  
  splits; eauto.
  eapply absconseq_rule_sound_aux ; eauto.

  introv Hc Hmdisj Hinv Hdisj.
  lets Hres : Hsatt  Hdisj.
  destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
  lets Hsm : Hsim  Hsp.
  inverts Hsm.
  lets Hress : H0 Hc Hmdisj Hinv Hdsjj.
  simp join.
  lets Hstt : hmstepstar_trans  Hstar H9.
  do 12 eexists; 
    splits; eauto.
  splits; auto.
  introv Henv.  
  splits.
  eapply H18; eauto.
  introv Hvv Hvvv Hdss.
  eapply absconseq_rule_sound_aux ; eauto.
  eapply H18; eauto.

  introv Hc Hmdisj Hinv Hdisj.
  lets Hres : Hsatt  Hdisj.
  destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
  lets Hsm : Hsim  Hsp.
  inverts Hsm.
  lets Hress : H1 Hc Hmdisj Hinv Hdsjj.
  simp join.
  lets Hstt : hmstepstar_trans  Hstar H10.  
  clear Hstar H10.
  do 9 eexists; splits; eauto.
  splits; eauto.
  destruct H17; [simp join; left;split; eauto | right; eauto]. 
 
  introv  Hs Hjmm Hswin.
  eapply absconseq_rule_sound_aux ; eauto.

  introv Hc Hmdisj Hinv Hdisj.
  lets Hres : Hsatt  Hdisj.
  destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
  lets Hsm : Hsim  Hsp.
  inverts Hsm.
  lets Hsk : H2 Hc Hmdisj Hinv Hdsjj.
  simp join.
  lets Hstt : hmstepstar_trans  Hstar H9.  
  assert ((o, x1, x) |= lift q v /\ satp o x1 (CurLINV li t)) by (split; auto).
  lets Hds : Himp2 H18 H10.
  simp join.
  lets Hsbt : hmstepstar_trans  Hstt  H20.  
  do 4 eexists; splits; eauto.

   introv Hc Hcal Hint Hmdisj Hinv Hdisj.
   lets Hres : Hsatt  Hdisj.
  destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
  lets Hsm : Hsim  Hsp.
  inverts Hsm.
  lets Hsk : H3 Hc Hmdisj Hinv Hdsjj; eauto.
  simp join.
  lets Hsbt : hmstepstar_trans  Hstar  H9.  
  do 4 eexists; splits; eauto.

   introv Hc Hcal Hint Hmdisj Hinv Hdisj.
   lets Hres : Hsatt  Hdisj.
  destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
  lets Hsm : Hsim  Hsp.
  inverts Hsm.
  lets Hsk : H4 Hc Hmdisj Hinv Hdsjj; eauto.
  simp join.
  lets Hsbt : hmstepstar_trans  Hstar  H9.  
  do 4 eexists; splits; eauto.

  introv Hc Hcal Hint Hmdisj Hinv Hdisj.
  lets Hres : Hsatt  Hdisj.
  destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
  lets Hsm : Hsim  Hsp.
  inverts Hsm.
  lets Hsk : H5 Hc Hmdisj Hinv Hdsjj; eauto.
  simp join.
  lets Hsbt : hmstepstar_trans  Hstar  H9.  
  do 4 eexists; splits; eauto.

  introv Hnot  Hinv Hjon Hdisj.
  unfolds in Hdisj.
  destruct Hdisj as (OO & Hdisj).
  lets Hres : Hsatt  Hdisj.
  destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
  lets Hsm : Hsim  Hsp.
  inverts Hsm.
  assert (disjoint O' Os) as Hds.
  unfolds.
  eauto.
  lets Hree : H6 Hnot Hinv Hjon Hds; eauto.

  introv Hc Hmdisj Hinv Hdisj.
  lets Hres : Hsatt  Hdisj.
  destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
  lets Hsm : Hsim  Hsp.
  inverts Hsm.
  lets Hress : H7 Hc Hmdisj Hinv Hdsjj.
  simp join.
  lets Hstt : hmstepstar_trans  Hstar H13.  
  eexists.
  exists x0 x1 x2.
  do 10 eexists; splits; eauto.
  splits; eauto.
  eapply absconseq_rule_sound_aux ; eauto.

  introv Hc Hmdisj Hinv Hdisj.
  lets Hres : Hsatt  Hdisj.
  destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
  lets Hsm : Hsim  Hsp.
  inverts Hsm.
  lets Hress : H8 Hc Hmdisj Hinv Hdsjj.
  simp join.
  lets Hstt : hmstepstar_trans  Hstar H11.
  clear Hstar H11.
  eexists.
  exists x0 x1 x2.
  exists x3.
  splits; eauto.
  destruct H12; simp join.
  left.
  exists x x4 x5.
  splits; eauto.
  eapply absconseq_rule_sound_aux ; eauto.
  right.
  exists x x4 x5.
  splits; eauto.
  introv Hs1 Hj1 Hj2.
  eapply absconseq_rule_sound_aux ; eauto.
Qed.
