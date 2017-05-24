Require Import sound_include.


Import DeprecatedTactic.
Open Scope Z_scope.


Lemma eoi_ieon_rule_sound:
  forall Spec  sd  I r ri isr is id cs  i aop li t P,  
    0 <= Int.unsigned id  <  Z_of_nat INUM ->
    i = Z.to_nat (Int.intval id) ->  
    GoodFrm P -> 
    P ==> CurLINV li t ->
    isr i = true ->
    RuleSem Spec sd  li I r ri 
            (<|| aop ||>  **
                 OS [isr, true, i :: is, cs] ** getinv (I i) ** P)
            (sprim (eoi id))
            (<|| aop ||>  **
                 OS [isrupd isr i false, true, i :: is, cs] ** P) t.
Proof.
  introv Hp1 Hp2  Hgood Himp Hisr  Hsat.
  unfold Int.unsigned in *.
  destruct Hsat as (Hsat1 & Hsat2).
  destruct o as [[[[G E] M]iis]ax].
  destruct ax  as [[ie iss] css].
  sep split in Hsat1.
  simpl in H,H0,H1,H2,H3.
  subst.
  simpl in Hsat1.
  simp join.
  constructors; introv Hff; tryfalse.
  unfold nilcont.
  introv Hinv Hjm1 Hjm2 Hstep.
  invertstep idtac.
  unfolds in Hjm1.
  unfold joinmem in Hjm1.
  simp join.
  lets Hks : Hinv aop.
  simpl substaskst in *.
  remember (  Z.to_nat (Int.intval i)) as m.
  unfold INV in Hks.
  unfold sat in Hks; fold sat in Hks.
  trysimplall.
  simp join.
  lets Hle:    Zle_imply_natle H7 H6.  
  remember (  Z.to_nat (Int.intval i)) as m.
  destruct H14 as [Hon | Hoff].
  unfold inv_ieon in Hon.
  sep split in Hon.
  unfold invlth_isr  in Hon.
  replace (INUM -0)%nat  with (INUM) in * by omega.
  clear H.
  exists aop OO.
  assert (exists Mss, join x0 Mss x13 /\ join x Ms Mss).
  clear -H0 H11.
  join auto.
  assert (exists Oss, join x3 Oss OO /\ join x2 Os Oss).
  clear -H2 Hjm2.
  join auto.
  destruct H as (Mss & Hj1 & Hj2).
  destruct H8 as (Oss & Hjj1 & Hjj2).

  exists (x10, x11, x0,  isrupd x14 (Z.to_nat (Int.intval i)) false,
          (true, m :: is, cs) ).
  exists Mss x3 Oss.
  unfold INV in *.
  assert (exists j, INUM = S j).
  destruct INUM.
  omega.
  eauto.
  destruct H as (j & Hinum).
  rewrite Hinum in *.
  splits; eauto.
  constructors.
  unfolds.
  unfold joinmem; join auto.
  simpl substaskst.
  unfolds.
  intros.
  assert (exists k, join x1 k  Mss/\ join x x4 k).
  clear -H1 Hj2.
  join auto.
  assert (exists k, join x6 k  Oss/\ join x2 x8 k).
  clear -H10 Hjj2.
  join auto.
  simp join.
  exists x1 x9  Mss x6 x5 Oss.
  splits;eauto.
  simpl substmo.
  destruct (prec  (I (S (S j)))) as [Hp1 Hp2].
  destruct Hp2 as [Hp2 _ _ ].
  lets Hsd : Hp2 H13.
  simpl in Hsd.
  lets Hks : Hsd  (Z.to_nat (Int.intval i)).
  eapply good_inv_prop; eauto.
  apply (invp (I (S (S j)))).
  simpl substmo.
  left.
  unfold inv_ieon.
  sep split; auto.
  unfold invlth_isr.
  rewrite Hinum in *.
  replace (S j - 0)%nat  with (S j) by omega.
  remember (Z.to_nat (Int.intval i))  as m.
  destruct m.
  unfold starinv_isr  in Hon; fold  starinv_isr  in Hon.
  simpl in Hon.
  mytac.
  destruct H20.
  mytac.
  exists x x4 x9 x2 x8 x5.
  splits; eauto.
  simpl substmo.
  exists (isrupd x21 0%nat false).
  right.
  exists empmem x x empabst x2 x2.
  trysimplsall.
  splits; mytac;eauto.
  splits;simpl;mytac;eauto.
  eapply good_inv_prop; eauto.
  apply (invp (I 0%nat)).
  destruct (prec (I 0%nat)) as [Hp1 Hp2].
  destruct Hp2 as [Hp2 _ _ ].
  lets Hsd : Hp2 H3.
  eapply Hsd; eauto.
  simpl substmo.
  eapply  starinv_isr_prop4.
  eapply inv_isr_prop ; eauto.

  simp join.
  tryfalse.
  lets Hisnum : sm_nat_exist Hle.
  destruct Hisnum as (k & Heqk).
  rewrite Heqk in *.
  assert (S (S k) = ((S m%nat) + (S (k-m)))%nat) by omega.
  rewrite H16 in *.
  lets Hres :  starinv_isr_prop_intro3  Hon.
  eapply starinv_isr_prop_elim.
  simpl in Hres.
  simp join.
  destruct H26.
  mytac.
  assert (exists k, join x15 k x9/\ join x x16 k).
  clear -H15 H18.
  join auto.
  assert (exists k, join x18 k x5/\ join x2 x19 k).
  clear -H14 H20.
  join auto.
  simp join.
  exists x15 x17 x9 x18 x14 x5.
  splits; eauto.
  simpl substmo.
  replace (S m) with (S( m + 0))%nat  in * by omega.
  eapply  starinv_isr_prop5; eauto.
  eapply inv_isr_prop; eauto.
  simpl substmo.
  exists x x16 x17 x2 x19 x14.
  splits; eauto.
  simpl .
  exists  (isrupd x27 (S m) false).
  right.
  exists empmem x x empabst x2 x2.
  splits; eauto.
  join auto.
  join auto.
  splits; eauto.
  splits; auto.
  unfolds.
  rewrite <- beq_nat_refl;auto.
  unfolds; auto.
  unfolds; auto.

  eapply good_inv_prop; eauto.
  apply (invp (I (S m))).
  destruct (prec(I (S m))) as [Hp1 Hp2].
  destruct Hp2 as [Hp2 _ _ ].
  lets Hsd : Hp2 H3.
  eapply Hsd; eauto.
  simpl substmo.
  eapply starinv_isr_prop4; eauto.
  eapply inv_isr_prop; eauto.
  simp join; tryfalse.
  lets Hks : Himp H4.
  eapply Linv_igore; eauto.
  unfolds.
  intros.
  eapply absinfer_sound.local_inv_aop_irev; eauto.

  constructors; introv Hfalse; tryfalse.
  intros; invertstep idtac.
  inverts Hfalse.
  trysimplsall.
  introv Hds Hdss Hddss.
  exists aop OO0 x3 Os0. 
  splits; eauto.
  constructors.
  lets Hks : Himp H4.
  eapply Linv_igore; eauto.
  unfolds.
  intros.
  eapply absinfer_sound.local_inv_aop_irev; eauto.
  unfold lift.
  sep split; simpl; auto.
  eapply goodfrm_prop; eauto.
  subst m.
  auto.
  destruct Hfalse as ( _ & _&Hfff&_).
  false.
  apply Hfff.
  eexists; eauto.
  unfold inv_ieoff in Hoff.
  sep split in Hoff.
  simpl in H; tryfalse.
  introv Hjj1 Hjj2 Hinv.
  introv Hstep.
  apply Hstep.
  destruct o2 as  [[[[]]]].
  do 2 eexists.
  unfold nilcont.
  eapply eoi_step; eauto.
Qed.

Lemma  eoi_ieoff_rule_sound  : 
  forall Spec sd  I r ri isr is id  i cs aop t P li,  
    0 <= Int.unsigned id  <  Z_of_nat INUM ->
    i = Z.to_nat (Int.unsigned id) ->  
    GoodFrm P -> 
    RuleSem Spec sd  li I r ri 
            (<|| aop ||>  ** OS [isr, false, i :: is, cs] ** P)
            (sprim (eoi id))
            ( <|| aop ||>  **
                  OS [isrupd isr i false, false, i :: is, cs] ** P) t.
Proof.
  introv Hp1 Hp2  Hgood   Hsat.
  unfold Int.unsigned in *.
  destruct Hsat as (Hsat1 & Hsat2).
  destruct o as [[[[G E] M]iis]ax].
  destruct ax  as [[ie iss] css].
  sep split in Hsat1.
  simpl in H,H0,H1,H2,H3.
  subst.
  constructors; introv Hff; tryfalse.
  unfold nilcont.
  introv Hinv Hjm1 Hjm2 Hstep.
  invertstep idtac.
  unfolds in Hjm1.
  unfold joinmem in Hjm1.
  simp join.
  lets Hks : Hinv aop.
  simpl substaskst in *.
  remember (  Z.to_nat (Int.intval i)) as m.
  unfold INV in Hks.
  unfold sat in Hks; fold sat in Hks.
  trysimplall.
  simp join.
  exists aop OO (x6, x7, x8, isrupd x10 (Z.to_nat (Int.unsigned i))false,
                 (false, Z.to_nat (Int.intval i) :: is, cs)).
  exists Ms O Os.
  splits; eauto.
  constructors.
  unfolds.
  unfold joinmem; join auto.
  simpl substaskst.
  unfolds.
  intros.
  unfold INV.
  exists x x0 Ms x2 x4 Os.
  splits; eauto.
  simpl substmo.
  eapply good_inv_prop; eauto.
  apply (invp (I (S INUM))).
  destruct (prec(I (S INUM))) as [Hp1 Hp2].
  destruct Hp2 as [Hp2 _ _ ].
  lets Hsd : Hp2 H9.
  eapply Hsd; eauto. 
  simpl substmo.
  right.
  destruct H10.
  unfold inv_ieon in H.
  sep split in H.
  simpl in H2; tryfalse.
  unfold inv_ieoff in *.
  sep split in H.
  sep destruct H.
  sep split in H.
  sep split; auto.
  simpl in H10.
  subst x1.
  exists (Z.to_nat (Int.intval i) ).
  destruct H.
  sep split; auto.
  left.
  sep split in H.
  sep split; auto.
  unfold invlth_isr in *.
  unfold Int.unsigned in *.
  remember (Z.to_nat (Int.intval i)) as m.
  replace (m +1)%nat with (S m) in * by omega.
  eapply  starinv_isr_prop4; eauto.
  eapply inv_isr_prop; eauto.
  sep split; auto.
  right.
  sep split in H.
  simpl in H.
  simp join.
  simpl.
  splits; eauto.
  eapply Linv_igore; eauto.
  constructors; introv Hfalse; tryfalse.
  intros; invertstep idtac.
  inverts Hfalse.
  trysimplsall.
  introv Hds Hdss Hddss.
  exists aop OO0 O Os0. 
  splits; eauto.
  constructors.
  eapply Linv_igore; eauto.
  unfold lift.
  sep split; auto.
  eapply goodfrm_prop; eauto.
  destruct Hfalse as ( _ & _&Hfff&_).
  false.
  apply Hfff.
  eexists; eauto.
  introv Hjj1 Hjj2 Hinv.
  introv Hstep.
  apply Hstep.
  destruct o2 as  [[[[]]]].
  do 2 eexists.
  unfold nilcont.
  eapply eoi_step; eauto.
Qed.
