Require Import sound_include.


Lemma encrit1_rule_sound :
  forall Spec sd  li I r ri isr is cs i aop t  P,  
    GoodFrm P ->
    RuleSem Spec sd li I r ri 
            ( <||aop||> ** OS[isr, true, is, cs] ** (ATopis i) ** [| i <= INUM|] ** P) 
            (sprim encrit)
            ( <||aop||> ** OS[isr, false, is, true::cs] ** (invlth_isr I O i) ** P) t.
Proof.
  introv  Hgood  Hsat.
  destruct Hsat as (Hsat1 & Hsat2).
  destruct o as [[[[G E] M] irr] aux].
  destruct aux as [[ie iss]css].
  sep split in Hsat1.
  simpl in H0,H1,H2,H3,H4,H5.
  subst.
  unfold nilcont.
  constructors; introv Hfalse; tryfalse.
  introv Hinv Hjm1 Hjm2 Hstep.

  invertstep idtac.
  unfolds in Hjm1.
  unfold joinmem in Hjm1.
  simp join.
  simpl substaskst in *.
  assert (gettopis si < INUM \/ gettopis si = INUM).
  destruct H.
  right; auto.
  left; omega.
  destruct H0 as [Hi1 | Hi2].
  lets Hivv : Hinv aop.
  unfold INV in Hivv.
  unfold sat in Hivv; fold sat in Hivv.
  simp join.
  simpl substmo in *.
  destruct H7 as [Hon | Hoff].
  unfold inv_ieon in Hon.
  sep split in Hon.
  clear H0.
  lets Hsr :  inv_destr Hi1 Hon.
  simpl in H4, H1.
  unfold sat in Hsr; fold sat in Hsr.
  simp join.
  trysimplsall.
  simpl assertion.getmem in H2.
  assert (exists k j, join x6 x8 k /\ join x x10 j /\ join  j x6 Ms /\ join k j x2).
  clear -H5 H2 H1.
  join auto.
  destruct H0 as (Ml & Mss & Hj1& Hj2 & Hj3 & Hj4).
  exists aop OO (x0, x1, Ml, x4, (false, si, true :: ci)). 
  assert (exists k j, join x12 O k /\  join x7 x13 j /\ join j x12 Os /\ join k j OO).
  clear -H4 Hjm2 H8.
  join auto.
  destruct H0 as (Ol & Oss & Hjj1& Hjj2 & Hjj3 & Hjj4).
  exists Mss.
  exists Ol Oss.
  splits; eauto.
  constructors.
  unfolds.
  unfold joinmem; join auto.
  unfold INV.
  simpl substaskst.
  exists x x10 Mss.
  trysimplsall.
  exists x7 x13 Oss.
  simpl assertion.getmem.
  splits; eauto.
  eapply good_inv_prop; eauto.
  apply (invp (I (S INUM))).
  right.
  unfold inv_ieoff.
  sep split; auto.
  exists ( gettopis si).
  sep split; auto.
  left.
  sep split; auto.
  assert ((gettopis si + 1) = S (gettopis si) ) by omega.
  rewrite H0 .
  eapply inv_isr_prop ; eauto.
  assert (joinmem (x0, x1, x8, x4, (false, si, true :: ci)) x6 (x0, x1, Ml, x4, (false, si, true :: ci))).
  unfolds; join auto.
  assert (join O x12 Ol) by join auto.
  lets Hkxs : absinfer_sound.join_satp_local_inv li  H0 H7. 
  eapply Hkxs.
  eapply Linv_igore; eauto.
  constructors;  trysimplsall; introv Hf ;tryfalse.
  intros;invertstep idtac.
  inverts Hf.
  introv Hmdisj Hinvv Hdisjj.
  unfold getmem in Hinvv.
  simpl in Hinvv.
  exists aop OO0 Ol Os0.
  splits; eauto.
  constructors.
  assert (joinmem (x0, x1, x8, x4, (false, si, true :: ci)) x6 (x0, x1, Ml, x4, (false, si, true :: ci))).
  unfolds; join auto.
  assert (join O x12 Ol) by join auto.
  lets Hkxs : absinfer_sound.join_satp_local_inv li  H0 H7. 
  eapply Hkxs.
  eapply Linv_igore; eauto.
  unfold lift.
  sep split; auto.
  exists x6 x8 Ml x12 O Ol.
  simpl.
  splits; auto.
  eapply inv_isr_prop ; eauto.

  eapply goodfrm_prop; eauto.
  destruct Hf as (_&_&Hff&_).
  false. apply Hff.
  eexists; eauto.
  unfold inv_ieoff in Hoff.
  sep split in Hoff; tryfalse.

  lets Hivvv: Hinv aop.
  rewrite Hi2 in *.
  exists aop OO .
  unfold INV in Hivvv.
  unfold sat in Hivvv; fold sat in Hivvv.
  simp join.
  simpl substmo in *.
  destruct H7 as [Hon | Hoff].
  trysimplall.
  assert (exists k, join x5 x8 k /\ join k x x2).
  clear - H5 H1.
  join auto.
  assert (exists k, join x9 O k /\ join k x7 OO).
  clear -H4 Hjm2.
  join auto.
  simp join.
  exists (x0, x1, x10, x4, (false, si, true :: ci)).
  exists x.
  exists x6 x7.
  splits; eauto.
  constructors.
  unfolds.
  unfold joinmem; join auto.
  simpl.
  unfold INV.
  exists x empmem x x7 empabst x7.
  trysimplall.
  splits; eauto.
  join auto.
  join auto.
  eapply good_inv_prop; eauto.
  apply (invp (I (S INUM))).
  right.
  unfold inv_ieoff.
  sep split; auto.
  exists ( gettopis si).
  sep split; auto.
  right.
  sep split; auto.
  simpl ;split; auto.
  unfolds; auto.
  assert (joinmem (x0, x1, x8, x4, (false, si, true :: ci)) x5 (x0, x1, x10, x4, (false, si, true :: ci))).
  unfolds; join auto.
  assert (join O x9 x6) by join auto.
  lets Hkxs : absinfer_sound.join_satp_local_inv li  H9 H10. 
  eapply Hkxs.
  eapply Linv_igore; eauto.
  constructors;  trysimplsall; introv Hhf ;tryfalse.
  intros;invertstep idtac.
  inverts Hhf.
  introv Hmdisj Hinvv Hdisjj.
  exists aop OO0 x6 Os0. 
  splits; eauto.
  constructors.
  assert (joinmem (x0, x1, x8, x4, (false, si, true :: ci)) x5 (x0, x1, x10, x4, (false, si, true :: ci))).
  unfolds; join auto.
  assert (join O x9 x6) by join auto.
  lets Hkxs : absinfer_sound.join_satp_local_inv li  H9 H10. 
  eapply Hkxs.
  eapply Linv_igore; eauto.
  unfold lift.
  sep split; auto.
  exists x5 x8 x10 x9 O x6.
  trysimplall.
  splits; auto.
  unfold inv_ieon in Hon.
  sep split in Hon.
  eapply inv_isr_prop ; eauto.
  eapply goodfrm_prop; eauto.
  destruct Hhf as (_&_&Hff&_).
  false. apply Hff.
  eexists; eauto.
  unfold inv_ieoff in Hoff.
  sep split in Hoff; tryfalse.
  introv _ _ _  Hstep.
  apply Hstep.
  destruct o2 as [[[[]]]].
  destruct l as [[]].
  do 2 eexists.
  eapply  encrit_step ; eauto.
Qed.

Lemma  encrit2_rule_sound : 
  forall Spec sd  I r ri isr is cs  aop li t P ,  
    GoodFrm P ->
    RuleSem Spec sd li I r ri 
            ( <||aop||> ** OS[isr, false, is, cs]  ** P) 
            (sprim encrit)
            ( <||aop||> ** OS[isr, false, is, false::cs]  ** P)  t.
Proof.
  introv  Hgood  Hsat.
  destruct Hsat as (Hsat1 & Hsat2).
  destruct o as [[[[G E] M] irr] aux].
  destruct aux as [[ie iss]css].
  sep split in Hsat1.
  simpl in H0,H1,H2,H3.
  subst.
  unfold nilcont.
  constructors; introv Hfalse; tryfalse.
  introv Hinv Hjm1 Hjm2 Hstep.

  invertstep idtac.
  unfolds in Hjm1.
  unfold joinmem in Hjm1.
  simp join.
  simpl substaskst in *.
  unfold INV in *.
  lets Hinvv : Hinv aop0.
  unfold sat in Hinvv; fold sat in Hinvv.
  simp join.
  trysimplall.
  destruct H6 as [Hon | Hoff].
  unfold inv_ieon in Hon.
  sep split in Hon; tryfalse.
  unfold inv_ieoff in Hoff.
  sep split in Hoff.
  exists aop0 OO  (x0, x1, x8, x4, (false, si, false :: ci)).
  exists Ms O Os.
  splits; eauto.
  
  constructors.
  unfolds.
  unfold joinmem; join auto.
  simpl substaskst.
  unfolds.
  intros.
  exists x x5 Ms x7 x9 Os.
  trysimplall.
  splits; auto.
  eapply good_inv_prop; eauto.
  apply (invp (I (S INUM))).
  right.
  unfold inv_ieoff.  
  sep split; auto.
  sep destruct Hoff.
  sep split in Hoff.
  exists x6.
  sep split; auto.
  destruct Hoff.
  sep split in H6.
  left;sep split;  auto.
  eapply inv_isr_prop; eauto.
  right.
  sep auto.
  eapply Linv_igore; eauto.
  constructors;  trysimplsall; introv Hhf ;tryfalse.
  intros;invertstep idtac.
  inverts Hhf.
  introv Hmdisj Hinvv Hdisjj.
  exists aop0 OO0 O Os0.
  splits; eauto.
  constructors.
  eapply Linv_igore; eauto.
  unfold lift.
  sep split; auto.
  eapply goodfrm_prop; eauto.
  destruct Hhf as (_&_&Hff&_).
  false. apply Hff.
  eexists; eauto.
  introv _ _ _  Hstep.
  apply Hstep.
  destruct o2 as [[[[]]]].
  destruct l as [[]].
  do 2 eexists.
  eapply  encrit_step ; eauto.
Qed. 



Lemma  excrit1_rule_sound : 
  forall Spec sd  I r ri isr is cs  i aop t li P ,  
    GoodFrm P ->
    P ==> CurLINV li t->
    RuleSem Spec sd  li I r ri 
            (<|| aop ||>  **
                 OS [isr, false, is, true :: cs] **
                 ATopis i ** invlth_isr I 0 i ** P)
            (sprim excrit)
            (<|| aop ||>  ** OS [isr, true, is, cs] ** P ) t.
Proof.
  introv  Hgood Himp Hsat.
  destruct Hsat as (Hsat1 & Hsat2).
  destruct o as [[[[G E] M] irr] aux].
  destruct aux as [[ie iss]css].
  sep split in Hsat1.
  simpl in H0,H1,H2,H3,H4.
  subst.
  simpl in Hsat1.
  simp join.
  lets Hks : Himp H4.
  unfold nilcont.
  constructors; introv Hfalse; tryfalse.
  introv Hinv Hjm1 Hjm2 Hstep.
  invertstep idtac.
  unfolds in Hjm1.
  unfold joinmem in Hjm1.
  simp join.
  simpl substaskst in *.
  unfold INV in *.
  lets Hinvv : Hinv aop0.
  unfold sat in Hinvv; fold sat in Hinvv.
  simp join.
  trysimplall.
  destruct H10 as [Hon | Hoff].
  unfold inv_ieon in Hon.
  sep split in Hon; tryfalse.
  assert (exists Mss, join x0 Mss x6/\ join x Ms Mss ).
  clear -H8 H0.
  join auto.
  assert (exists Oss, join x3 Oss OO /\ join x2 Os Oss).
  clear -H2 Hjm2.
  join auto.
  simp join.
  exists aop0 OO. 
  exists (x4, x5, x0, x8, (true, si, ci)).
  exists x14 x3 x10.
  splits; eauto.
  constructors.
  unfolds.
  unfold joinmem; join auto.
  simpl substaskst.
  assert (exists k, join x1 k x14 /\ join x x9 k ).
  clear - H1 H11.
  join auto.
  assert  (exists k, join x11 k x10 /\ join x2 x13 k). 
  clear -H7 H10.
  join auto.
  simp join.
  unfolds.
  intros.
  exists x1 x16 x14 x11 x15 x10.
  trysimplall.
  splits; eauto.
  eapply good_inv_prop; eauto.
  apply (invp (I (S INUM))).
  left.
  unfold inv_ieon.
  sep split; auto.
  unfold invlth_isr in *.
  replace (INUM-0) with INUM by omega.
  unfold inv_ieoff in Hoff.
  sep split in Hoff.
  sep destruct Hoff.
  sep split in Hoff.
  simpl in H16,H17.
  destruct Hoff.
  sep split in H18.
  lets Hrs : nat_exists H19.
  simp join.
  rewrite H20 in *.
  replace (S x18) with (S (( gettopis si) +(S x18 - (gettopis si + 1)))) by omega.
  apply starinv_isr_elim1 with (i := gettopis si)(j := (S x18 - (gettopis si + 1))).
  replace (S (gettopis si)) with ((gettopis si) +1) by omega.
  unfold invlth_isr in H18.
  exists x x9 x16 x2 x13 x15.
  simpl assertion.getmem.
  simpl getabst.
  simpl substmo.

  splits; eauto.
  replace (gettopis si) with (gettopis si-0) by omega.
  eapply inv_isr_prop ; eauto.
  eapply inv_isr_prop ; eauto.
  sep split in H18.
  rewrite H17 in *.
  subst x17.
  simpl in H18.
  simp join.
  rewrite H19 in *.
  assert (x=x16) by join auto.
  unfolds in H18.
  subst x13.
  assert (x2 = x15) by join auto.
  subst.
  replace (INUM) with (INUM-0) by omega.
  eapply inv_isr_prop ; eauto.
  eapply  Linv_igore; eauto.
  unfolds.
  intros.
  eapply absinfer_sound.local_inv_aop_irev; eauto.
  constructors; introv Hff; tryfalse.
  introv _ _ _ Hstep.
  intros; invertstep idtac.
  inverts Hff.
  trysimplsall.
  introv  Hsatp Hdisj Hjj.
  unfold getmem in Hdisj.
  simpl in Hdisj.
  exists aop0 OO0  x3 Os0.
  splits; eauto.
  constructors.
  eapply  Linv_igore; eauto.
  unfolds.
  intros.
  eapply absinfer_sound.local_inv_aop_irev; eauto.
  unfold lift.
  sep split; auto.
  eapply goodfrm_prop; eauto.
  destruct Hff as (_&_&Hff&_).
  false. apply Hff.
  eexists; eauto.
  introv Hs1 Hs2 Hs3 Hss.
  apply Hss.
  unfolds in Hs2.
  unfold joinmem in Hs2.
  simp join.
  do 2 eexists.
  eapply excrit_step; eauto.
Qed.


Lemma  excrit2_rule_sound : 
  forall Spec sd  I r ri isr is cs  aop t li P ,  
    GoodFrm P ->
    RuleSem Spec sd  li I r ri 
            (<|| aop ||>  **
                 OS [isr, false, is, false :: cs]  ** P)
            (sprim excrit)
            (<|| aop ||>  ** OS [isr, false, is, cs] ** P ) t.
Proof.
  introv  Hgood  Hsat.
  destruct Hsat as (Hsat1 & Hsat2).
  destruct o as [[[[G E] M] irr] aux].
  destruct aux as [[ie iss]css].
  sep split in Hsat1.
  simpl in H0,H1,H2,H3.
  subst.
  unfold nilcont.
  constructors; introv Hfalse; tryfalse.
  introv Hinv Hjm1 Hjm2 Hstep.

  invertstep idtac.
  unfolds in Hjm1.
  unfold joinmem in Hjm1.
  simp join.
  simpl substaskst in *.
  unfold INV in *.
  lets Hinvv : Hinv aop0.
  unfold sat in Hinvv; fold sat in Hinvv.
  simp join.
  trysimplall.
  destruct H6 as [Hon | Hoff].
  unfold inv_ieon in Hon.
  sep split in Hon; tryfalse.
  unfold inv_ieoff in Hoff.
  sep split in Hoff.
  exists aop0 OO  (x0, x1, x8, x4, (false, si, ci)).
  exists Ms O Os.
  splits; eauto.
  constructors.
  unfolds.
  unfold joinmem; join auto.
  simpl substaskst.
  unfolds.
  intros.
  exists x x5 Ms x7 x9 Os.
  trysimplall.
  splits; auto.
  eapply good_inv_prop; eauto.
  apply (invp (I (S INUM))).
  right.
  unfold inv_ieoff.  
  sep split; auto.
  sep destruct Hoff.
  sep split in Hoff.
  exists x6.
  sep split; auto.
  destruct Hoff.
  sep split in H6.
  left;sep split;  auto.
  eapply inv_isr_prop; eauto.
  right.
  sep auto.
  eapply Linv_igore; eauto.
  constructors;  trysimplsall; introv Hhf ;tryfalse.
  intros;invertstep idtac.
  inverts Hhf.
  introv Hmdisj Hinvv Hdisjj.
  exists aop0 OO0 O Os0.
  splits; eauto.
  constructors.
  eapply Linv_igore; eauto.
  unfold lift.
  sep split; auto.
  eapply goodfrm_prop; eauto.
  destruct Hhf as (_&_&Hff&_).
  false. apply Hff.
  eexists; eauto.
  introv Hs1 Hs2 Hs3 Hstep.
  unfold joinm2 in Hs2.
  unfold joinmem in Hs2.
  simp join.
  apply Hstep.
  do 2 eexists.
  eapply  excrit_step  ; eauto.
Qed. 
