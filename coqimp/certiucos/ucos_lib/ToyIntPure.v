Require Import ucos_include.
Import DeprecatedTactic.
Lemma ih_no_lvar'
: forall (aop : absop) (isrreg : isr) (si : is) (cs : cs) (ie : ie),
    <|| aop ||>  ** Aisr isrreg ** Ais si ** Acs cs ** Aie ie ** isr_inv ** (OSInv ** atoy_inv) ** A_dom_lenv nil==>
        <|| aop ||>  **
        Aisr isrreg ** Ais si ** Acs cs ** Aie ie ** [|exists k,gettopis si = k /\ forall j, (0 <= j < k)%nat -> isrreg j = false|] ** OSInv ** atoy_inv ** A_dom_lenv nil .
Proof.
  intros.
  sep cancel 7%nat 7%nat.
  sep cancel 7%nat 7%nat.
  sep cancel 1%nat 1%nat.
  sep cancel 3%nat 3%nat.
  sep cancel 3%nat 3%nat.
  sep cancel 4%nat 4%nat.
  unfold isr_inv in H.
  sep semiauto.
  destruct H.
  simpl in H.
  simpl.
  destruct H;auto.
  destruct H.
  destruct H0.
  exists x0.
  simpl in H0.
  destruct H0;split;auto.
  simpl in H1.
  simpl in H.
  destruct H.
  rewrite <- H in H1.
  destruct H1;auto.
Qed.
 
Lemma toyint_sti_inv_elim:
  forall ir si P,
    (forall j : nat,
       (0 <= j < gettopis (1%nat :: si))%nat ->
       isrupd ir 1%nat true j = false) ->
    Aisr (isrupd ir 1%nat true)  ** Ais (1%nat::si) ** OSInv ** atoy_inv ** P ==>
         Aisr (isrupd ir 1%nat true)  ** Ais (1%nat::si) ** ATopis 1%nat ** invlth_isr I 0%nat 1%nat ** atoy_inv' ** [|isr_is_prop (isrupd ir 1%nat true) (1%nat::si)|] ** P.
Proof.
  intros.
  sep cancel 5%nat 7%nat.
  unfold invlth_isr.
  simpl (1-0)%nat.
  unfold I.
  unfold starinv_isr.
  simpl getinv.
  unfold atoy_inv in H0.
  unfold A_isr_is_prop in H0.
  sep normal.
  exists (isrupd ir 1%nat true).
  exists (isrupd ir 1%nat true).
  Lemma xx: forall ir si s P, s|= Aisr ir ** Ais si ** (EX (isr : isr) (is : is),
                                                        Aisr isr ** Ais is ** [|isr_is_prop isr is|]) ** P -> s |= Aisr ir ** Ais si **  [|isr_is_prop ir si|] ** P.
  Proof.
    intros.
    sep cancel 4%nat 4%nat.
    destruct_s s.
    simpl in *.
    mytac.
    do 6 eexists;splits;mytac.
    mytac.
    mytac.
    do 6 eexists;splits;mytac.
    mytac.
    mytac.
    auto.
  Qed.
  sep lifts (1::2::5::nil)%nat in H0.
  apply xx in H0.
  Lemma  xxx: forall ir s P,
    s |=  Aisr (isrupd ir 1%nat true) ** P ->
    s |= (([|isrupd ir 1%nat true 1%nat = true|] //\\
        Aisr (isrupd ir 1%nat true)) \\//
       ([|isrupd ir 1%nat true 1%nat = false|] //\\
                                               Aisr (isrupd ir 1%nat true)) ** atoy_inv) ** P.
  Proof.
    intros.
    sep cancel 2%nat 2%nat.
    left.
    simpl in *.
    mytac;auto.
  Qed.
  apply xxx.
  sep lift 2%nat.
  assert ( isrupd ir 1%nat true 0%nat = false).
  apply H;auto.
  Lemma xxxx: forall ir s P,
                isrupd ir 1%nat true 0%nat = false ->
                s |=  OSInv ** Aisr (isrupd ir 1%nat true) ** P ->
    s |= (([|isrupd ir 1%nat true 0%nat = true|] //\\
        Aisr (isrupd ir 1%nat true)) \\//
       ([|isrupd ir 1%nat true 0%nat = false|] //\\
        Aisr (isrupd ir 1%nat true)) ** OSInv) ** P.
  Proof.
    intros.
    sep cancel 3%nat 2%nat.
    right.
    sep cancel 1%nat 2%nat.
    split;auto.
    simpl in *;mytac;auto.
  Qed.
  apply xxxx;auto.
  sep lift 2%nat in H0.
  Lemma xx': forall si s P, s |= Ais (1%nat :: si) ** P -> s|=  Ais (1%nat :: si) ** ATopis 1%nat ** P.
  Proof.
    intros.
    sep cancel 2%nat 3%nat.
    destruct_s s.
    simpl in *;mytac.
    do 6 eexists;splits;mytac.
    mytac.
    mytac.
    simpl.
    auto.
  Qed.
  apply xx' in H0.
  sep cancel 5%nat 1%nat.
  sep auto.
Qed.
 
