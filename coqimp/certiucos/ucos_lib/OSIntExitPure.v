Require Import ucos_include.
Import DeprecatedTactic.
Lemma simpl_inv_excrit'
: forall P i,
    Aisr empisr ** OSInv ** invlth_isr' I 1 i ** P ==>
         Aisr empisr ** invlth_isr I 0%nat i ** P.
Proof.
  intros.
  sep cancel 4%nat 3%nat.
  destruct i.

  unfold invlth_isr.
  unfold starinv_isr.
  rewrite NPeano.Nat.sub_0_r in *.
  unfold I in *.
  unfold getinv in *.

  sep normal in H; sep destruct H; sep split in H.
  sep split; auto.
  
  unfold sat in *; fold sat in *;
  destruct_s s; trysimplall; mytac.
  exists empisr.
  right.
  do 6 eexists; mytac; eauto.
  unfold invlth_isr' in H5.
  simpl leb in H5.
  simpl in H5.
  destruct H5;subst.
  apply join_comm in H1.
  apply join_emp_eq in H1.
  subst.
  unfolds in H0.
  subst.
  apply join_comm in H3.
  apply join_emp_eq in H3.
  subst.
  auto.
  unfolds invlth_isr'.
  simpl leb in H.
  unfold invlth_isr.
  unfold starinv_isr.
  rewrite NPeano.Nat.sub_0_r in *.
  fold starinv_isr.
  unfold I in *.
  unfold getinv in *.
  sep normal in H; sep destruct H; sep split in H.
  sep split; auto.
  unfold sat in *; fold sat in *;
  destruct_s s; trysimplall; mytac.
  do 6 eexists;mytac;eauto.
  exists empisr.
  right.
  do 6 eexists;splits;eauto;mytac.
  unfolds.
  auto.
  fold starinv_isr.
  clear -H5.
  induction i.
  unfold starinv_isr.
  unfold getinv.
  unfold atoy_inv.
  exists empisr.
  right.
  unfold A_isr_is_prop.
  simpl in H5.
  mytac.

  do 6 eexists;splits;simpl;eauto;mytac.
  mytac.
  eauto.
  mytac.
  eauto.
  do 6 eexists;splits;eauto;mytac.
  instantiate (1:=empmem).
  mytac.
  eauto.
  instantiate (1:=empabst).
  mytac.
  do 8 eexists;splits;eauto.
  mytac.
  instantiate (1:=empabst).
  mytac.
  exists x9.
  splits;auto.
  unfolds;auto.
  unfolds;auto.
  do 8 eexists;splits;mytac.
  mytac.
  mytac.
  do 6 eexists;splits;mytac.
  mytac.
  mytac.
  eauto.
  unfolds.
  unfold empisr.
  intros;auto.

  eapply starinv_prop1_rev.
  fold I in *.
  unfold starinv_isr at 2.
  simpl.
  do 6 eexists;splits;eauto;mytac.
  exists empisr.
  right.
  do 6 eexists;splits;eauto;mytac.
  mytac.
  mytac.
  unfold empisr;eauto.
  do 6 eexists;splits;eauto;mytac.
  mytac.
  mytac.
  do 8 eexists;splits;eauto;mytac.
  mytac.
  mytac.
  do 6 eexists;splits;eauto;mytac.
  mytac.
  eauto.
  unfolds.
  unfold empisr.
  intros;auto.
Qed.

Lemma simpl_inv_excrit'':
  forall P i v'0,
    (
      forall j : nat,
        (0 <= j < i)%nat -> (isrupd v'0 i false) j = false) ->
    Aisr (isrupd v'0 i false)  **  invlth_isr I 0%nat i  ** P ==>
         Aisr (isrupd v'0 i false) ** OSInv ** invlth_isr' I 1 i ** P.
Proof.
  intros.
  sep cancel 3%nat 4%nat.
  unfold invlth_isr in *.
  unfold invlth_isr' in *.
  destruct_s s.
  destruct i.
  simpl leb.
  simpl (0-0)%nat in H0.
  unfold starinv_isr in H0.
  unfold I in H0.
  unfold getinv in H0.
  sep normal in H0.
  sep destruct H0.
  trysimplall.
  sep split in H0.
  simpl in H1.
  subst i0.
  destruct H0.
  simpl in H0.
  mytac.
  unfolds in H0.
  simpl in H0.
  tryfalse.
  Lemma xx:forall e e0 m ir a b c P, (e, e0, m, ir,a,b,c) |= P -> (e, e0, m, ir,a,b,c) |= Aisr ir ** P.
  Proof.
    intros.
    simpl in *.
    do 6 eexists;splits;eauto;mytac.
  Qed.
  apply xx.
  sep cancel 2%nat 1%nat.
  simpl in *.
  mytac;auto.
  simpl leb.
  simpl (S i -0)%nat in H0.

  Lemma temp: forall s i P,
                (forall j : nat, (0 <= j < S (S i))%nat -> (getisr (gettaskst s)) j = false) ->
                s|= P ** starinv_isr I 0%nat (S i) ->
                s |= P ** OSInv ** (if true then atoy_inv' else Aemp).
  Proof.
    induction i;intros.
    simpl starinv_isr in H0.
    sep normal in H0.
    sep destruct H0.
    Lemma  xxx: forall m s P X x0,
                  (forall j : nat, (0 <= j < 2)%nat -> getisr (gettaskst s) j = false) ->
                  (m<2)%nat ->
                  s |= (([|x0 m%nat = true|] //\\
                                             Aisr x0) \\//
                                                      ([|x0 m%nat = false|] //\\
                                                                            Aisr x0) ** X) ** P ->
                  s |= X ** P.
    Proof.
      intros.
      destruct_s s.
      simpl in *;mytac.
      destruct H5;mytac.
      assert (0 <= m < 2)%nat by omega.
      apply H in H2.
      tryfalse.
      do 6 eexists;splits;eauto;mytac.
    Qed.
    apply xxx in H0;auto.
    sep lift 2%nat in H0.
    apply xxx in H0;auto.
    unfold atoy_inv in H0.
    unfold A_isr_is_prop in H0.
    sep cancel OSInv.
    sep auto.
    apply IHi.
    intros.
    apply H;auto.
    omega.
    sep cancel 1%nat 1%nat.
    apply starinv_prop1 in H0.
    sep pauto.
    simpl (S (0 + S i)) in H0.
    unfold I in H0.
    unfold starinv_isr in H0.
    unfold getinv in H0.
    unfold aemp_isr_is in H0.
    unfold A_isr_is_prop in H0.
    sep destruct H0.
    destruct H0;
      sep auto.
    destruct H0;sep auto.
    destruct H0;sep auto.
  Qed.
  
  eapply temp;eauto.
  simpl.
  intros.
  remember (starinv_isr I 0%nat (S i)) as X.
  clear HeqX.
  simpl in H0.
  mytac.
  assert (j = S i \/ j<> S i) by tauto.
  destruct H0.
  subst j.
  unfolds.
  simpl.
  assert (beq_nat i i=true).
  symmetry.
  apply beq_nat_refl.
  rewrite H0.
  auto.
  apply H.
  omega.
Qed.


Lemma simpl_inv_excrit''':
  forall P i v'0,
    (
      forall j : nat,
        (0 <= j < i)%nat -> (isrupd v'0 i false) j = false) ->
    Aisr (isrupd v'0 i false) ** OSInv ** invlth_isr' I 1 i ** P ==>
         Aisr (isrupd v'0 i false)  **  invlth_isr I 0%nat i  ** P.
Proof.
  intros.
  sep cancel 4%nat 3%nat.
  unfold invlth_isr in *.
  unfold invlth_isr' in *.
  destruct_s s.
  destruct i.
  simpl leb in H0.
  simpl (0-0)%nat.
  unfold starinv_isr.
  unfold I.
  unfold getinv.
  sep normal.
  exists (isrupd v'0 0%nat false).
  sep split in H0.
  sep split.
  simpl in H1.
  2:simpl;auto.
  subst i0.
  right.
  remember OSInv as X.
  clear HeqX.
  simpl in H0.
  mytac.
  simpl.
  do 6 eexists;splits;eauto;mytac.
  unfolds.
  simpl.
  auto.
  simpl leb in H0.
  Lemma temp': forall s i P,
                (forall j : nat, (0 <= j < S (S i))%nat -> (getisr (gettaskst s)) j = false) ->
                s |= P ** OSInv ** (if true then atoy_inv' else Aemp) ->
                s |= P ** starinv_isr I 0%nat (S i).
  Proof.
    induction i;intros.
    simpl starinv_isr.
    destruct_s s.
    sep normal.
    exists i i.
    simpl in H.
    Lemma xxx': forall m s P X,
                  (forall j : nat, (0 <= j < 2)%nat -> getisr (gettaskst s) j = false) ->
                  (m<2)%nat ->
                  s |= X ** P ->
                  s |= (([|getisr (gettaskst s) m%nat = true|] //\\
                                             Aisr (getisr (gettaskst s))) \\//
                                                      ([|getisr (gettaskst s) m%nat = false|] //\\
                                                                            Aisr (getisr (gettaskst s))) ** X) ** P .
    Proof.
      intros.
      destruct_s s.
      simpl in *;mytac.
      do 6 eexists;splits;eauto;mytac.
      right.
      do 6 eexists;splits;eauto;mytac.
      apply H.
      omega.
    Qed.
    apply xxx';auto.
    sep lift 2%nat.
    apply xxx';auto.
    unfold atoy_inv.
    Lemma sss:forall s P, s|=OSInv ** P -> s |= OSInv ** A_isr_is_prop ** P.
    Proof.
      intros.
      sep cancel 2%nat 3%nat.
      unfold OSInv in *.
      sep normal in H.
      sep destruct H.
      sep normal.
      sep eexists.
      sep lifts (19::20::nil)%nat.
      Lemma sss':forall s P, s|=  A_isr_is_prop ** P -> s|=A_isr_is_prop ** A_isr_is_prop ** P.
      Proof.
        intros.
        sep cancel 2%nat 3%nat.
        unfold A_isr_is_prop in *.
        sep auto.
      Qed.
      eapply sss'.
      sep auto.
    Qed.
    sep lift 2%nat in H0.
    apply sss in H0.
    sep normal.
    sep cancel OSInv.
    sep auto.
    
    Lemma starinv_prop1_rev'
     : forall (j i : hid) (I : Inv) P,
       P ** starinv_isr I i j ** starinv_isr I (S (i + j)) 0%nat ==>
                  P ** starinv_isr I i (S j).
    Proof.
      intros.
      sep cancel 1%nat 1%nat.
      eapply starinv_prop1_rev;eauto.
    Qed.
    apply starinv_prop1_rev'.
    simpl (S (0 + S i)).
    unfold I at 2.
    unfold starinv_isr at 2.
    unfold getinv.
    sep normal.
    destruct_s s.
    exists i0.
    assert ((e, e0, m, i0, (i1, i2, c), o, a)
   |= ((([|i0 (S (S i)) = true|] //\\ Aisr i0) \\//
       ([|i0 (S (S i)) = false|] //\\ Aisr i0) ** aemp_isr_is) **
      P) ** starinv_isr I 0%nat (S i)).
    apply IHi.
    intros.
    simpl in H.
    simpl;apply H.
    omega.
    sep normal.
    simpl in H.
    unfold aemp_isr_is.
    sep lift 2%nat in H0.
    apply sss in H0.
    clear -H H0.

    sep lift 2%nat in H0.
    sep lifts (1::3::nil)%nat.
    remember (OSInv ** P ** atoy_inv') as X.
    clear HeqX.
    simpl in *;mytac.
    do 6 eexists;splits;eauto;mytac.
    right.
    do 6 eexists;splits;eauto;mytac.
    mytac.
    mytac.
    apply H;omega.
    do 6 eexists;splits;eauto;mytac.
    mytac.
    mytac.
    do 8 eexists;splits;eauto;mytac.
    mytac.
    mytac.
    eauto.
    do 6 eexists;splits;eauto;mytac.
    mytac.
    sep normal in H1.
    auto.
  Qed.
  eapply temp';eauto.
  intros.
  simpl.
  remember (OSInv ** (if true then atoy_inv' else Aemp)) as X.
  clear HeqX.
  simpl in H0;mytac.
  assert (j = S i \/ j<> S i) by tauto.
  destruct H0.
  subst j.
  unfolds.
  simpl.
  assert (beq_nat i i=true).
  symmetry.
  apply beq_nat_refl.
  rewrite H0.
  auto.
  apply H.
  omega.
Qed.

Lemma invlth_isr_invlth_isr'_imp:
  forall s x si P i,
    s|=ATopis x ** invlth_isr I 0%nat x ** Ais (i::si) ** isrclr ** P ->
    s|=OSInv **  invlth_isr' I 1 i **  Ais (i::si) ** Aisr empisr ** P.
Proof.
  intros.
  sep lift 4%nat in H.
  apply isrclr_imp in H.
  Lemma atopis_eq:
    forall s i x si P,
      s |= ATopis x ** Ais (i :: si) ** P -> x= i.
  Proof.
    intros.
    destruct_s s.
    simpl in H.
    mytac.
    simpl;auto.
  Qed.
  
  sep lifts (2::4::nil)%nat in H.
  lets Hx:atopis_eq H.
  subst x.
  apply astar_l_atopis_elim in H.
  destruct H.
  sep cancel 4%nat 5%nat.
  destruct i.
  unfold invlth_isr'.
  unfold invlth_isr in *.
  unfold starinv_isr in *.
  rewrite NPeano.Nat.sub_0_r in *.
  unfold I in *.
  unfold getinv in *.
  simpl leb.

  sep normal in H0; sep destruct H0; sep split in H0.
  sep split; auto.
  destruct H0.
  simpl in H0.
  mytac.
  rewrite H3 in H0.
  unfold empisr ;tryfalse.
  sep normal in H0.
  remember OSInv as X.
  clear HeqX.
  destruct_s H1.
  unfold sat in *; fold sat in *;
  destruct_s s; trysimplall; mytac.
  do 6 eexists; mytac; eauto.
 
  unfolds invlth_isr'.
  simpl leb.
  unfold invlth_isr in H0.
  unfold starinv_isr in H0.
  rewrite NPeano.Nat.sub_0_r in *.
  fold starinv_isr in H0.
  unfold I in *.
  unfold getinv in *.
  sep lift 3%nat in H0.
  sep normal in H0.
  sep destruct H0.
  apply xxx in H0;auto.
  Focus 2.
  sep split in H0.
  intros.
  rewrite H3.
  unfolds;auto.
  eapply astar_mono.
  intros;eauto.
  2:exact H0.
  intros.
  clear -H2.
  sep cancel 1%nat 2%nat.
  destruct_s s0.
  sep split in H2.
  simpl in H.
  subst.
  sep split.
  2:simpl;auto.
  induction i.
  unfold starinv_isr in *.
  unfold getinv in *.
  unfold atoy_inv.
  simpl in H2.
  mytac.
  destruct H.
  mytac.
  unfolds in H;tryfalse.
  mytac.
  simpl.
  do 8 eexists;splits;eauto;mytac.
  mytac.
  eexists;splits;eauto.
  unfolds;auto.
  apply IHi.
  clear IHi.
  
  apply starinv_prop1 in H2.
  sep cancel 1%nat 1%nat.
  simpl in H2.
  mytac.
  destruct H0.
  mytac.
  simpl;auto.
  destruct_s H.
  mytac;simpl in *.
  mytac.
Qed.

Lemma elim_a_isr_is_prop': forall isr is s P , isr_is_prop isr is -> s |= Aisr isr **
                                                                      Ais is **
                                                                      A_isr_is_prop ** P -> s|= Aisr isr ** Ais is ** P .
Proof.
  intros.
  unfold A_isr_is_prop in H0.
  sep auto.
Qed.
