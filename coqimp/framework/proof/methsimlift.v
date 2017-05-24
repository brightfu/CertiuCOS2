Require Import sound_include.
Require Import funsim.

Lemma  MethSim_to_Methsim'_aux :
  forall P FSpec sd I r ri q li t,
    GoodI I sd li->
    WFFuncsSim P FSpec sd li  I ->  
    forall C o aop O, 
      MethSimMod FSpec sd C o aop O li I r ri q t ->
      MethSim P sd C o  aop O li I  r ri q t.
Proof.
  introv Hgi Hwf.
  cofix Hcofix.
  introv  Hsim.
  inverts Hsim.
  assert (notabortm C \/ ~  notabortm C) as Hasrt.
  tauto.
  destruct Hasrt as [Htrue | Hfalse].
  assert ( notabortm C) as Hasrt; auto.
  unfolds in Htrue.
  destruct Htrue as (Hcall & Hsw & Hend& 
                           Hret & Hrete & Hex & Hstkcrt & Hstkfr).  
  constructors; try auto.

  (*notabort C*)
  introv Hinv Hjm1 Hjm2 Hstep.
  lets Hre0 : H P Hcall  Hinv Hjm1  Hstep; eauto.
  simp join.
  do 6 eexists; splits; eauto.

  introv Hc. subst.
  false. apply Hsw.  do 2 eexists.   eauto.

  introv _ Hinv Hjm1   Hdisj.
  lets Hre0 : H6 P Hasrt  Hinv Hjm1 ; eauto.

  introv Hc. subst.
  false. apply Hstkcrt.  do 4 eexists.   eauto.
  
  introv Hc. subst.
  false. apply Hstkfr.  do 2 eexists.   eauto.

  (*~notabort C*)
  casenot Hfalse.
  unfold IsFcall in Cs.
  destruct Cs as (f & vl & tl & ks & Hc).
  subst.
  constructors; introv Hfalse; tryfalse.
  introv Hjm1 Hdisj Hstep.
  invertstep idtac.
  destruct o as [[[[G E]MM ]isr] aux].
  unfold joinm2 in Hjm1.
  unfold joinmem in Hjm1.
  simp join.
  lets Hre0 : H0   Hdisj; eauto.
  unfold disjoint, getmem; simpl; eauto.
  destruct Hre0 as ( gamma' & OO' & om &  M0 & O'&Os'& Ot& Of  & pre& post& tp & logicl &
                            Hstar& Hjm2 & Hjon1 & Hjon2 & Hleq & Hsf &  Hpre  &Hsat &Hinv'  &Hforal).
  assert (post_imp_linv post li vl logicl t) as Himpp.
  unfolds.
  intros.
  eapply Hforal; eauto.
  exists  gamma' OO'.
  eexists.
  exists Ms  O' Os'.
  splits; auto.
  unfolds; eexists.
  unfold joinmem;
    split; do 6 eexists; splits; eauto.
  simpl substaskst in *.
  unfold satp.
  intros.
  eapply  INV_irrev_prop; eauto.
  eapply local_inv_E_irev.
  eapply  join_satp_local_inv ; eauto.
  eapply Hcofix.
  destruct Hwf as [Hdeq Hwf].
  lets Hff : Hwf Hsf.
  destruct Hff as (d3 & d4 & s' & Hpff & Hmat &Hgood & Hsimm).
  rewrite H16 in Hpff.
  apply sym_eq in Hpff. 
  inverts Hpff.
  assert (length vl <= length_dl (revlcons d1 d2)) as Hasrt.
  eapply length_prop; eauto.
  eapply tl_vl_match_leneq;eauto.
  lets Hex : alloc_star_exist P  (kcall f s x1 ks0) x0 x8 .
  lets Hexx : Hex   x4 x5 Hasrt Hgood.
  destruct Hexx as (le'&M'&Hastp).  
  lets Hestp : losidstepstar_imply_losallocstepn  Hastp.
  destruct Hestp as (n &  Hstarr).
  eapply alloc_stepn_msim_hold with (p := P).
  eapply local_inv_E_irev.
  eapply  join_satp_local_inv ; eauto.
  do 2 eexists; eauto.
  introv Hsap.
  lets Heqc : alloc_stepn_code_eq Hstarr Hsap.
  rewrite <- Heqc. 
  lets Hsdk : absinfer_sound.join_satp_local_inv Hjm2  Hjon2  Hsat.
  assert (satp (x0, empenv, x8, x4, x5) O' (CurLINV li t)) as Hsat'.
  eapply local_inv_E_irev; eauto.
  lets Hbs :  losalloc_local_inv_hold Hsat'  Hsap.

  (**continue**)
  eapply  identity_step_msim_hold ; eauto.
  eapply alloc_notabortm ; eauto.
  introv. 
  destruct o' as [[]].
  constructors.
  eapply stmt_step; eauto.
  constructors; eauto.
  (*assert (length (rev tl) = length tl) by apply rev_length.
  rewrite <- H9 in H23.*)

  assert (rev (rev tl) = tl).
  apply rev_involutive.
  rewrite <- H9 in H23.
  clear H9.
  lets Hre' :  build_pre_ret_exist logicl t H23  H22 Hgood. 
  lets Hre : Hre' H16 Hsf;  eauto. 
  clear Hre'.
  destruct Hre as (Hpr & Hps).
  destruct Hpr as (pe & Hpr).
  destruct Hps as (pr & Hps).
  lets Hsiim : Hsimm Hpr Hps.
  unfolds in Hsiim.
  unfolds in Hjm2.
  simp join.
  rewrite rev_involutive in H23.
  lets Hf: tl_vl_dl'' H23 H22.
  lets Hreq : alloc_lemma Hpr  Hf   Hpre  Hsap; eauto.
  destruct Hreq as (EE' & MM' & Hjmm & Hspe ).
  lets HHsim : Hsiim Hspe.
  assert ( kcall f s x6 ks0 = kstop ##  kcall f s x6 ks0) as Heqc ; simpl; auto.
  rewrite Heqc.
  eapply fun_seq_comp with (q := fun v =>  getasrt (post (rev vl) v logicl t)) (M := M0)   (Of := Of) ; eauto.
  introv.
  eapply (getprop (post  (rev vl) v logicl t)).
  introv Hgv Hev Ho Hj Hjd.
  eapply Hforal with (o1 := o) (O'' := O'0); eauto.
  simpl in Hgv.
  destruct o'0 as [[[[]]]].
  simpl in Hgv.
  simpl in Hev.
  simpl.
  split; auto.
  lets Hms : Hsiim Hspe.
  eapply  fun_free_comp; eauto.
  introv Hcal Hint.
  eapply fun_free_ignore; eauto.

  introv Hinv Hjm1 Hdisj Hstep.
  destruct o as [[[[G E]MM ]isr] aux].
  unfold joinm2 in Hjm1.
  unfold joinmem in Hjm1.
  simp join.
  unfold getmem in H0.
  simpl in H0.
  unfolds in Hdisj.
  destruct Hdisj as (OO & Hdisj).
  lets Hresk : H0   Hinv Hdisj; eauto.  
  unfolds; eauto.
  destruct Hresk as ( gamma' & OO' & om &  M0 & O'&Os'& Ot& Of  & pre& post& tp & logicl &
                             Hstar& Hjm2 & Hjon1 & Hjon2 & Hleq & Hsf &  Hpre  &Hsat &Hinv'  &Hforal).
  destruct Hwf as [Hdeq Hwf].
  lets Hff : Hwf Hsf.
  destruct Hff as (d3 & d4 & s' & Hpff & Hmat &Hgood & Hsimm).
  apply Hstep.
  exists (curs (salloc vl (revlcons d3 d4)), (kenil, kcall f s' x1 ks)).
  eexists.
  eapply ostc_step; eauto.
  eapply stmt_step; eauto.
  constructors; eauto.

  casenot Hfalse.  
  destruct Cs as ( x & ks & Hc).
  subst.
  constructors;introv Hfalse; tryfalse.
  introv _ _ Hf.
  invertstep idtac.

  inverts Hfalse.
  introv  Hmdisj Hinv Hdisj.
  lets Hre0 : H1  Hmdisj Hinv Hdisj; eauto.
  simp join.
  do 9 eexists; splits; eauto.
  splits; auto.
  destruct H17.
  destruct H9.  
  left; split; eauto.
  right; eauto.

  unfolds in Hfalse. 
  destruct Hfalse as ( Hf  & _ ).
  false.
  apply Hf.
  do 2 eexists; eauto.

  casenot Hfalse.
  unfolds in Cs.
  destruct Cs as (v & Hc).
  subst.
  constructors; auto; introv Hfalse; tryfalse.
  introv _ _ Hf.
  invertstep tryfalse.

  unfolds in Hfalse. 
  destruct Hfalse as ( _  & Hf &_ ).
  false.
  apply Hf.
  eexists; eauto.

  casenot Hfalse.  
  destruct Cs as (ks & Hc & Hcal & Hint ). 
  subst.
  constructors;try auto;  try (introv Hfalse; tryfalse).

  introv _ _  Hf.
  false.
  invertstep tryfalse.

  unfolds in Hfalse. 
  destruct Hfalse as ( _  & _ &Hf &_ ).
  false.
  apply Hf.
  exists ks; splits; eauto.

  casenot Hfalse.
  destruct Hwf as [Heqd _].
  unfolds in Heqd.
  destruct Cs as ( v & ks & Hc & Hcal & Hint). 
  subst.
  constructors;try auto;  try (introv Hfalse; tryfalse).

  introv _ _  Hf.
  invertstep tryfalse.

  unfolds in Hfalse. 
  destruct Hfalse as( _  & _ &_ &Hf &_).
  false.
  apply Hf.
  unfolds.
  exists v ks; splits; intuition eauto.
  
  casenot Hfalse.
  destruct Cs as (ks & Heqc &Hint &Hcal).
  subst C.
  constructors;try auto;  try (introv Hfalse; tryfalse).

  introv _ _  Hf.
  false.
  invertstep tryfalse.
  unfolds in Hfalse.
  destruct Hfalse as( _  & _ &_ &_ &Hf&_).
  false.  apply Hf.
  eexists; split; eauto.

  casenot Hfalse.
  destruct Cs as (e1&e2&e3&ks & Heqc).
  subst C.
  constructors;try auto;  try (introv Hfalse; tryfalse).

  introv _ _  Hf.
  false.
  invertstep tryfalse.
  unfolds in Hfalse.
  destruct Hfalse as( _  & _ &_ &_ &_&Hf&_).
  false.  apply Hf.
  do 4  eexists; split; eauto.
  
  inverts Hfalse.
  introv Hsat1 Hdisjj Hijo.
  lets Hks : H7 Hsat1 Hdisjj Hijo; eauto.
  simp join.
  do 14 eexists; splits; eauto.
  splits; eauto.
  
  apply Classical_Prop.NNPP in Hfalse.
  destruct Hfalse as (e1&ks & Heqc).
  subst C.
  constructors;try auto;  try (introv Hfalse; tryfalse).
  
  introv _ _  Hf.
  false.
  invertstep tryfalse.
  unfolds in Hfalse.
  destruct Hfalse as( _  & _ &_ &_ &_&_&Hf).
  false.  apply Hf.
  do 2  eexists; split; eauto.

  inverts Hfalse.
  introv Hsat1 Hdisjj Hijo.
  lets Hks : H8 Hsat1 Hdisjj Hijo; eauto.
  simp join.
  destruct H12.
  simp join.
  do 8 eexists; splits; eauto.
  left.
  splits; eauto.
  simp join.
  do 8 eexists; splits; eauto.
  right.
  splits; eauto.
  Grab Existential Variables.
  auto.
Qed.
