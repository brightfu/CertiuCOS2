Require Import include_frm.
Require Import base_tac.
Require Import sep_auto.
Require Import mem_join_lemmas.



Lemma  hmstepstar_seq :
  forall sc s1 O  x s2 s1',
    hmstepstar sc s1 O s1' x ->
    hmstepstar sc  (s1;; s2) O (s1';; s2) x.
Proof.
  introv Hl.
  inductions Hl.
  constructors; eauto.
  constructors; eauto.
  constructors; eauto.
Qed.

Definition absimp' sc (li : LocalInv)  (p p' : asrt) (t: tid) := 
  forall (s : taskst) (O : osabst) (gamma : absop),
    (s, O, gamma) |= p /\ satp s O (CurLINV li t)->
    forall Of OO,
      join O Of OO ->
      exists O' gamma' OO',
        join O' Of OO' /\
        hmstepstar sc gamma OO gamma'
                   OO' /\ (s, O', gamma') |= p' /\ satp s O' (CurLINV li t).

Lemma  hmstepstar_trans : 
  forall aop O aop' O' aop'' O'' sd ,  
    hmstepstar sd aop O aop' O' ->  
    hmstepstar sd  aop' O'  aop'' O'' ->
    hmstepstar sd aop  O  aop'' O''. 
Proof.
  introv Hse.
  inductions Hse.
  auto.
  introv Hss.
  apply IHHse in Hss.
  constructors; eauto.
Qed.


Lemma join_eqdom_eqdom :
  forall O O' O1 O2' O2 , 
    join O O1 O2 ->
    join O' O1 O2'->
    eqdomO O O' -> 
    eqdomO O2 O2'.
Proof.
  unfold eqdomO in *; intros.
  simpljoin.
  split.

  unfold indom in *; intros.
  pose proof H x.
  pose proof H0 x.
  pose proof H1 x.
  destruct H5.
  unfold get in *; simpl in *.
  split; intros; destruct H7.
  rewrite H7 in H3.
  destruct (OSAbstMod.get O x) eqn: eq1.
  destruct (OSAbstMod.get O1 x); tryfalse.
  elim H5; eauto.
  intros.
  rewrite H8 in H4.
  destruct (OSAbstMod.get O2' x); tryfalse.
  eauto.

  destruct (OSAbstMod.get O1 x); tryfalse.
  destruct(OSAbstMod.get O' x);
    destruct(OSAbstMod.get O2' x); tryfalse; eauto.

  rewrite H7 in H4.
  destruct (OSAbstMod.get O' x) eqn: eq1.
  destruct (OSAbstMod.get O1 x); tryfalse.
  elim H6; eauto.
  intros.
  rewrite H8 in H3.
  destruct (OSAbstMod.get O2 x); tryfalse.
  eauto.

  destruct (OSAbstMod.get O1 x); tryfalse.
  destruct(OSAbstMod.get O x);
    destruct(OSAbstMod.get O2 x); tryfalse; eauto.

  intros.
  pose proof H abstcblsid.
  pose proof H0 abstcblsid.
  unfold indom in H1.
  pose proof H1 abstcblsid; destruct H6.
  unfold get in *; simpl in *.
  rewrite H3 in H4.
  destruct(OSAbstMod.get O abstcblsid) eqn : eq1.
  destruct(OSAbstMod.get O1 abstcblsid); tryfalse.
  elim H6; eauto; intros.
  rewrite H8 in H5.
  destruct (OSAbstMod.get O2' abstcblsid); tryfalse.
  substs.
  pose proof H2 tls.
  elim H4; auto.
  intros.
  destruct H5.
  rewrite H8 in H5; inverts H5.
  eauto.

  destruct (OSAbstMod.get O1 abstcblsid); tryfalse.
  destruct (OSAbstMod.get O' abstcblsid);
    destruct (OSAbstMod.get O2' abstcblsid); tryfalse.
  substs.
  exists tls.
  split; auto.
  unfolds.
  intro; split; intro; auto.
Qed.

  
Lemma join_eqdom_ex :
  forall O1 O2 O2' O3,
    join O1 O2 O3 ->
    eqdomO O2 O2' ->
    exists z, join O1 O2' z.
Proof.
  unfold join, eqdomO, indom; unfold get; simpl.
  intros.
  exists (OSAbstMod.merge O1 O2').
  unfold OSAbstMod.join; intros.
  pose proof H a.
  destruct H0.
  pose proof H0 a.
  destruct H3.
  rewrite OSAbstMod.merge_sem.
  destruct (OSAbstMod.get O1 a) eqn : eq1;
  destruct (OSAbstMod.get O2 a) eqn : eq2;
  destruct (OSAbstMod.get O3 a) eqn : eq3;
  destruct (OSAbstMod.get O2' a) eqn : eq4; tryfalse; substs; auto.
  elim H4; eauto.
  intros; tryfalse.
Qed.


Lemma join_eqdom_ex3 :
  forall O'' OO O1 O O' Of OO',  
    join O'' OO O1->
    join O Of OO ->
    join O' Of OO'->
    eqdomO O O' ->
    exists z z1,  join O'' OO' z /\ join O z1 O1 /\ join O' z1 z.
Proof.   
  intros.
  lets Hax :  join_eqdom_eqdom  H0 H1 H2.
  lets Hxx : join_eqdom_ex H Hax.
  simp join.
  eexists x.
  eexists.
  splits; join auto.
Qed.

Lemma specstep_locality :
  forall  sc r O r' O' O'' O1,
    join O'' O O1 ->
    spec_step sc  r O r' O' ->
    exists O2,  spec_step  sc r O1 r' O2 /\  join O'' O' O2 .
Proof.
  induction 2.
  
  lets Has : join_eqdom_ex3 H H3 H4 H1.
  simp join.
  exists x.
  splits; auto.
  constructors; eauto.

  exists O1.
  constructors; auto.
  constructors.

  apply IHspec_step in H.
  simp join.
  exists x.
  splits; auto.
  constructors; eauto.

  exists O1.
  split; auto.
  constructors; eauto.
  
  exists O1.
  split; auto.
  constructors; eauto.

  exists O1.
  split; auto.
  constructors; eauto.
  join auto.
  
  exists O1.
  split; auto.
  constructors; eauto.
  join auto.
Qed.

Lemma spec_stepstar_locality :
  forall  sc r O r' O' O'',
    spec_stepstar  sc  r O r' O' ->
    forall O1,
      join O'' O O1 -> exists O2,  spec_stepstar  sc r O1 r' O2 /\  join O'' O' O2 .
Proof.
  induction 1.
  intros.
  exists O1.
  splits; eauto.
  constructors.
  intros.
  lets Hx :  specstep_locality  H1 H.
  simp join.
  apply IHspec_stepstar in  H3.
  simp join.
  eexists.
  split.
  constructors; eauto.
  auto.
Qed.

Lemma  absimp_eq_absimp':
  forall sc p q li t,
    absimplication sc li p  q t <->
    absimp' sc li p q t.
Proof.
  intros; split.
  intros.
  unfolds.
  unfolds in H.
  intros.
  lets Ha : H H0.
  simp join.
  assert (join Of O OO) by join auto.
  lets Hxx :  spec_stepstar_locality  H2  H6.
  simp join.
  assert (join x Of x1) by join auto.
  do 3  eexists; splits; eauto.
  
  intros.
  unfolds in H.
  unfolds.
  intros.
  assert (join O empabst O) by join auto.
  lets Hxx : H H0 H1.
  simp join.
  exists x1 x0.
  splits; eauto.
  assert (x =x1) by join auto.
  subst.
  auto.
  assert (x=x1) .
  join auto.
  subst x.
  auto.
Qed.

Lemma join_satp_local_inv:
  forall o M o' O Of O' t li,
    joinmem o M o' ->
    join O Of O' ->
    satp o O (CurLINV li t) ->
    satp o' O' (CurLINV li t).
Proof.
  intros.
  unfold satp in *.
  intros.
  pose proof H1 aop.
  unfold CurLINV in *.
  destruct H2.
  exists x.
  destruct o; destruct p; destruct s; destruct p.
  destruct o'; destruct p; destruct s; destruct p.
  unfold joinmem in H; simpljoin.
  unfold sat in H2; fold sat in H2.
  unfold sat; fold sat.
  simpl getmem in *.
  simpl getabst in *.
  simpl substmo in *.
  simpljoin.
  exists x6 (merge x7 M) x3.
  exists x9 (merge x10 Of) O'.
  splits; auto.
  eapply mem_join_join_merge23_join; eauto.
  eapply join_merge23_join; eauto.
  exists x12 (merge x13 M) (merge x7 M).
  exists x15 (merge x16 Of) (merge x10 Of).
  splits; eauto.

  apply join_comm in H2.
  eapply mem_join3_merge_merge_join; eauto.


  apply join_comm in H5.
  eapply osabst_join3_merge_merge_join; eauto.
Qed.

Lemma  local_inv_aop_irev:
  forall o O aop li t,
    (o, O,aop) |=  CurLINV li t ->
    satp o O  (CurLINV li t ) .            
Proof.
  intros.
  unfold satp; intros.
  unfold CurLINV in *.
  destruct H.
  destruct o; destruct p.
  destruct s; destruct p.
  unfold sat in *; fold sat in *.
  simpl getmem in *.
  simpl getabst in *.
  simpl substmo in *.
  simpljoin.
  do 7 eexists.
  splits; eauto.
  do 6 eexists; splits; eauto.
  unfold LINV in *.
  clear - H8.
  simpl in H8; simpljoin.
  simpl.
  do 6 eexists; splits; eauto.
  instantiate (1:=x).
  pose proof g t x.

  Lemma GoodLocalInvAsrt_aop_irev :
    forall p e e0 m i l o aop aop',
      GoodLocalInvAsrt p ->
      (e, e0, m, i, l, o, aop) |= p ->
      (e, e0, m, i, l, o, aop') |= p.
  Proof.
    inductions p; intros; simpl in H; tryfalse;
    try solve [simpl in H0; simpl; simpljoin; eauto].
    destruct H.
    destruct H0.
    left.
    eapply IHp1; eauto.
    right.
    eapply IHp2; eauto.
    destruct H.
    simpl in H0; simpljoin.
    simpl.
    do 6 eexists; splits; eauto.
    destruct H1.
    exists x.
    eapply H; eauto.
  Qed.
  eapply GoodLocalInvAsrt_aop_irev; eauto.
  destruct H;auto.
Qed.


Lemma absinfersound :
  forall sc p q li  t, 
    absinferfull sc li p q t ->  
    absimplication sc li p q t.
Proof.  
  introv Hs.
  inductions Hs; auto.
  unfolds.
  intros.
  exists O gamma.
  destruct H.
  splits; auto.
  constructors.
  unfolds in IHHs1.
  unfolds in IHHs2.
  unfolds.
  intros.
  apply IHHs1 in H.
  simp join.
  assert ( (s, x, x0) |= q /\ satp s x (CurLINV li t)) as Hast by (split; auto).
  apply IHHs2 in Hast.
  simp join.
  exists x1  x2.
  splits; auto.  
  eapply hmstepstar_trans; eauto.

  unfolds.
  intros.
  destruct H.
  destruct H.
  assert (  (s, O, gamma) |= p1 /\  satp s O (CurLINV li t))  as Hast by (split; auto).
  lets Ha : IHHs1  Hast.
  simp join.
  do 2 eexists; splits; eauto.
  left; auto.
  assert (  (s, O, gamma) |= p2 /\  satp s O (CurLINV li t))  as Hast by (split; auto).
  apply IHHs2 in Hast.
  simp join.
  do 2 eexists; splits; eauto.
  right; auto.

  introv Hsat.
  destruct Hsat as (Hsat & Hast2).
  apply H0 in Hsat.
  assert (  (s, O, gamma) |= p /\  satp s O (CurLINV li t))  as Hast by (split; auto).
  apply IHHs in Hast.
  simp join.
  do 2 eexists.
  splits; eauto.

  unfolds.
  introv Hsat.
  destruct Hsat.
  destruct H1.
  assert (  (s, O, gamma) |= p x /\  satp s O (CurLINV li t))  as Hast by (split; auto).
  apply H0 in Hast.
  simp join.
  do 2 eexists; splits; eauto.

  introv Hsat.
  destruct s as [[[[]]]].
  simpl in Hsat.
  simp join.
  lets Hk : H0 H6.
  assert ( (e, e0, x, i, l, x2, gamma) |= p /\ satp (e, e0, x, i,l) x2 (CurLINV li t)) as Hast.
  split; auto.

  eapply  local_inv_aop_irev; eauto.
  apply IHHs in Hast.
  simp join.
  assert (join x3 x2 O) by join auto.
  lets Hxx : spec_stepstar_locality  H1 H9.
  simp join.
  do 2 eexists; splits; eauto. 
  simpl.
  exists x x0 m.
  exists x1 x3 x5.
  splits; eauto.
  join auto.
  eapply change_aop_rule; eauto.

 assert (join x1 x3 x5) by join auto.
 lets Hks: join_satp_local_inv  H12 H8; eauto.
 unfolds; join auto.
  (*
  unfolds.
  introv Hsat.
  apply Hs in Hsat.
  simp join.
  exists x x0.
  splits; eauto.
  constructors; eauto.
  constructors.
   *)
  introv Hsat.
  destruct s as [[[[]]]].
  unfolds in IHHs.
  assert ( (e, e0, m, i, l, O, s1) |= p **  <|| s1||>).
  destruct Hsat.
  simpl in H1.
  simpl.
  join auto.
  eapply change_aop_rule; eauto.
  destruct Hsat as (Hsat & Hsat2).
  sep lift 2%nat in H1.
  assert ((e, e0, m, i, l, O, s1) |=  <|| s1 ||>  ** p /\ satp (e, e0, m, i, l) O (CurLINV li t)) by (split; auto).
  apply IHHs in H2.
  simp join.
  simpl in Hsat.
  simp join. 
  simpl in H3.
  simp join.
  exists x (s1';;s2).
  splits; eauto.
  eapply  hmstepstar_seq ; eauto.
  simpl.
  do 4 eexists. 
  exists x8.
  join auto.
  eapply change_aop_rule; eauto.

  unfolds.
  introv Hsat.
  exists O s.
  destruct s0 as [[[[]]]].
  simpl in Hsat.
  simp join.
  constructors.
  constructors.
  constructors; eauto.
  constructors.
  apply H1 in H8.
  split; auto.
  simpl.
  exists empmem.
  do 2 eexists.
  exists  x2.
  do 2 eexists; join auto.
  eapply change_aop_rule; eauto.

  introv Hsat.
  destruct s as [[[[]]]].
  simpl in Hsat.
  simp join.
  exists O s1.
  splits.
  constructors.
  constructors.
  constructors; eauto.
  constructors.
  simpl.
  do 5 eexists; splits;simp join;  eauto.
  eapply change_aop_rule; eauto.
  auto.

  introv Hsat.
  destruct s as [[[[]]]].
  simpl in Hsat.
  simp join.
  exists O s2.
  splits.
  constructors.
  eapply spec_choice_step2; eauto.
  constructors; eauto.
  simpl.
  do 6 eexists; splits;simp join;  eauto.
  eapply change_aop_rule; eauto.
  auto.

  unfolds.
  intros.
  destruct s as [[[[]]]].
  simpl in H3.
  simp join.
  lets Ha1 : H2 H9.
  apply H1 in H9.
  simpl in Ha1.
  exists O.
  exists (END None).
  simpl.
  splits; auto.
  assert (merge  O empabst  = O).
  apply jl_merge_emp.
  rewrite <- H3.
  constructors.
  eapply  spec_assume_step; eauto.
  rewrite jl_merge_emp.
  join auto.
  constructors.
  do 6 eexists; splits; simp join; eauto.
  eapply change_aop_rule; eauto.

  unfolds.
  intros.
  destruct s as [[[[]]]].
  simpl in H3.
  simp join.
  lets Ha1 : H2 H9.
  lets Hsc : H2 H9.
  simpl in Ha1.
  unfold sched_self in Hsc.
  simp join.
  simpl in H3, H5.
  apply H1 in H9.
  simpl in Ha1.
  exists O.
  exists (END None).
  simpl.
  splits; auto.
  assert (merge  O empabst  = O).
  apply jl_merge_emp.
  rewrite <- H8.
  constructors.
  eapply  spec_sched_step; eauto.
  rewrite jl_merge_emp.
  join auto.
  constructors.
  do 6 eexists; splits; simp join; eauto.
  eapply change_aop_rule; eauto.
Qed.
