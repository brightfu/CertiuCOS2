Require Import sound_include.

Lemma switch_rule_sound:
  forall  Spec sd lg  I r ri x li   t aop P P'  Px is cs,
    GoodFrm Px ->
    P ==> P' ** Px ->
    P' ==> <|| sched;; aop ||>  ** SWINVt I t ** Ais is ** Acs cs  ->
    P' ==> SWPRE_NDEAD sd x t ->
    Px ==> LINV li t lg ** Atrue ->
    RuleSem Spec sd li  I r ri  P  
            (sprim (switch x))  (<|| aop ||>  ** SWINVt I t ** Ais is ** Acs cs ** Px) t.
Proof.
  introv Hgood Himp Hp1 Hp2 Hpx.
  unfolds.
  introv Hsat.
  destruct Hsat as ( Hsat1 & Hsat2).
  lets Hsa : Himp  Hsat1.
  unfold sat in Hsa; fold sat in Hsa.
  simp join.
  destruct o as [[[[]]]].
  simpl substmo in *.
  simpl getabst in *.
  simpl assertion.getmem in *.
  lets Hsab : Hp1 H3.
  lets Hsabb : Hp2 H3.
  constructors; introv Hf; tryfalse.
  introv _ _ _ Hstep.

  invertstep tryfalse.
  unfold nilcont in Hf.
  inverts Hf.
  introv Hs1 Hdisj Hjoin.
  sep split in Hsab.
  simpl getabsop in *.
  simpl gettaskst in *.
  exists aop0 aop.
  exists OO.
  exists (e, e0, x1, i, l).
  exists  x0 O Os x4 x3.
  splits; eauto.
  constructors.
  unfolds.
  clear-H0.
  join auto.
  clear -H2; join auto.
  simpl.  
  eapply swinv_aop_irev; eauto.
  split.  
  exists lg.

  eapply linv_aop_irev; eauto.
  left.
  split.
  Lemma swprendead_aop_irev:
    forall o O aop t  sd  x,
      (o, O, aop) |= SWPRE_NDEAD sd x t  ->
      satp o O ( SWPRE_NDEAD sd x t ).
  Proof.
    intros.
    unfold SWPRE_DEAD in *.
    destruct H.
    split.
    eapply swpre_aop_irev; eauto.
    destruct o as [[[[]]]].
    destruct H0.
    exists x0.
    auto.
  Qed.

  eapply swprendead_aop_irev; eauto.


  introv Hsap1 Hj1 Hj2 .
  constructors; introv Hf; tryfalse.
  introv _ _ _  Hstep.
  invertstep idtac.
  inverts Hf.
  introv Hst1 Hdisj1 Hjj1.
  simpl substaskst in *.
  exists aop OO0  O'' Os0.
  splits; auto.
  constructors.
  lets Hxx : Hpx H4.

  eapply  joinmem_swinv_linv; eauto.
  unfold lift.
  sep split.
  unfold joinmem in Hj1.
  simp join.
  unfold sat.
  fold sat.
  simpl assertion.getmem.
  simpl getabst.
  simpl substmo.
  exists  Mc' x6  x7. 
  exists Oc' x4 O''.
  splits; auto.
  clear -H8.
  join auto.
  clear -Hj2.
  join auto.
  eapply goodfrm_prop; eauto.
  apply Hp1 in H3.
  sep split in H3.
  unfolds in Hj1.
  simp join.
  simpl; auto.
  apply Hp1 in H3.
  sep split in H3.
  unfolds in Hj1.
  simp join.
  simpl; auto.
  simpl; auto.
  unfolds in Hf.
  destruct Hf.
  destruct H7 as (_&Hf&_).
  false.
  apply Hf.
  unfolds.
  eexists; eauto.
  destruct Hf as (_&Hf&_).
  false.
  apply Hf.
  unfolds.
  unfold nilcont.
  do 2 eexists; eauto.
Qed.




Lemma switch_dead_rule_sound : 
  forall  Spec sd lg  I r ri x li   t aop P P'  Px is cs,
    GoodFrm Px ->
    P ==> P' ** Px ->
    P' ==> <|| sched;; aop ||>  ** SWINVt I t ** Ais is ** Acs cs  ->
    P' ==> SWPRE_DEAD sd x t  ->
    Px ==> LINV li t lg ** Atrue ->
    RuleSem Spec sd li  I r ri  P  
            (sprim (switch x))  Afalse t.
Proof.
  introv Hgood Himp Hp1 Hp2 Hpx.
  unfolds.
  introv Hsat.
  destruct Hsat as ( Hsat1 & Hsat2).
  lets Hsa : Himp  Hsat1.
  unfold sat in Hsa; fold sat in Hsa.
  simp join.
  destruct o as [[[[]]]].
  simpl substmo in *.
  simpl getabst in *.
  simpl assertion.getmem in *.
  lets Hsab : Hp1 H3.
  lets Hsabb : Hp2 H3.
  constructors; introv Hf; tryfalse.
  introv _ _ _ Hstep.

  invertstep tryfalse.
  unfold nilcont in Hf.
  inverts Hf.
  introv Hs1 Hdisj Hjoin.
  sep split in Hsab.
  simpl getabsop in *.
  simpl gettaskst in *.
  exists aop0 aop.
  exists OO.
  exists (e, e0, x1, i, l).
  exists  x0 O Os x4 x3.
  splits; eauto.
  constructors.
  unfolds.
  clear-H0.
  join auto.
  clear -H2; join auto.
  simpl.  
  eapply swinv_aop_irev; eauto.
  split.  
  exists lg.

  eapply linv_aop_irev; eauto.
  right.
  simpl substaskst.
  eapply swdead_aop_irev; eauto.
  destruct Hf as (_&Hf&_).
  false.
  apply Hf.
  unfolds.
  unfold nilcont.
  do 2 eexists; eauto.
Qed.
