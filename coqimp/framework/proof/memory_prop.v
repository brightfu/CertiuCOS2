Require Import include_frm.
Require Import base_tac.
Require Import Coq.Logic.Classical_Pred_Type.

Require Import mem_join_lemmas.
Require Import aux_map_lib.

Open Scope Z_scope.
(* Lemmas *)
(* get *)
Lemma allocb_get_some :
    forall m b n i off,
      (off<n)%nat->
        exists v,
          get (allocb m b i n) (b, (i + Z_of_nat off)) = Some (true,v).
Proof.
  intros.
  gen m i off.
  induction n.
  intros.
  omega.
  intros.
  destruct off.
  simpl.
  exists Undef.
  rewrite Z.add_0_r.
  rewrite set_a_get_a; auto.
  
  rewrite Nat2Z.inj_succ.
  assert (Z.succ (Z.of_nat off) = 1 + (Z.of_nat off))%Z.
  omega.
  rewrite H0.
  rewrite Z.add_assoc.
  simpl.
  rewrite set_a_get_a'.
  apply IHn.
  omega.

  intro; inverts H1.
  assert (Z.of_nat off >=0)%Z.
  omega.
  assert (i + 1 + Z.of_nat off >i)%Z.
  omega.
  rewrite<-H3 in H2.
  omega.
Qed.

Lemma allocb_get_none :
  forall m b i off n,
    (off>0)->
    fresh m b ->
    get (allocb m b (BinInt.Z.add i off) n) (b, i) = None.
Proof.
  intros.
  gen m i off.
  induction n.
  intros.
  simpl.
  apply nindom_get.
  unfold fresh in H0.
  eapply H0;eauto.
  intros.
  simpl.
  rewrite set_a_get_a'.
  rewrite<-Z.add_assoc.
  apply IHn;eauto.
  omega.
  intro.
  inversion H1.
  assert (i + off > i).
  omega.
  rewrite H3 in H2.
  omega.
Qed.

Lemma freeb_get_same :
    forall m m' b i off n,
      (off>0)%Z->
      freeb m b (BinInt.Z.add i off) n = Some m' ->
        get m' (b, i) = get m (b, i).
Proof.
  intros.
  gen m m' i off H.
  induction n.
  intros.
  simpl in H0.
  injection H0;intros;subst.
  auto.
  intros.
  simpl in H0.
  remember (get m (b, (i + off))) as v1.
  destruct v1;tryfalse.
  destruct p; destruct b0; tryfalse.
  remember (freeb m b (i + off + 1) n) as m1.
  destruct m1;tryfalse.
  injection H0;intros.
  rewrite<-H1.


  rewrite mem_del_get_neq.
  rewrite<-Z.add_assoc in Heqm1.
  erewrite IHn;eauto.
  omega.
  intro.
  inversion H2.
  assert (i + off > i)%Z.
  omega.
  rewrite <- H4 in H3.
  omega.
Qed.

Lemma storebytes_get_same :
    forall m m' b i off vl,
      (off>0)->
        storebytes m (b, (BinInt.Z.add i off)) vl = Some m' ->
        get m' (b, i) = get m (b, i).
Proof.
  intros.
  gen m m' i off H.
  induction vl.
  intros.
  simpl in H0.
  injection H0;intros;subst.
  auto.
  intros.
  simpl in H0. 
  unfold get in H0; simpl in H0.
  remember (HalfPermMap.get m (b, i + off)) as v1.
  destruct v1; tryfalse.
  destruct b0.
  destruct b0; tryfalse.
  remember (storebytes m (b, (i + off + 1)) vl) as m1.
  destruct m1;tryfalse.
  injection H0;intros.
  rewrite<-H1.

  rewrite set_a_get_a'.
  eapply IHvl.
  erewrite<-BinInt.Z.add_assoc in Heqm1.
  eauto.
  omega.

  intro.
  inversion H2.
  assert (i + off > i).
  omega.
  rewrite H4 in H3.
  omega.
Qed.


(* memory existential *)
Lemma allocb_storebytes_mem_ex :
  forall vl n m b i,
    ((length vl) + i = n)%nat -> 
      (exists m', storebytes (allocb m b 0 n) (b, Z_of_nat i) vl = Some m').
Proof.
  intros.
  gen i.
  induction vl.
  simpl.
  eexists;eauto.
  simpl. 
  intros.
  generalize allocb_get_some.
  intros.
  generalize (H0 m b n 0 i).
  intros.
  assert (i<n)%nat.
  omega.
  apply H1 in H2.
  destruct H2.
  simpl in H2.

  change (
      (fun x =>
         exists m',
           match x with
             | Some (true, _) =>
               match storebytes (allocb m b 0 n) (b, Z.of_nat i + 1) vl with
                 | Some m'0 => Some (set m'0 (b, Z.of_nat i) (true, a))
                 | None => None
               end
             | Some (false, _) => None
             | None => None
           end = Some m') (get (allocb m b 0 n) (b, Z.of_nat i))).
  rewrite H2.

  generalize (IHvl (i+1)%nat).
  intros.
  assert ((length vl + (i + 1))%nat = n).
  omega.
  apply H3 in H4.
  destruct H4.
  rewrite Nat2Z.inj_add in H4.
  simpl in H4.
  rewrite H4.
  eexists;eauto.
Qed.
    
Lemma allocb_store_mem_ex : 
  forall t m b v, 
    (exists m', store t (allocb m b 0 (typelen t)) (b, BinNums.Z0) v = Some m').
Proof.
  intros.
  unfold store.
  generalize encode_val_length.
  intros.
  generalize (H t v).
  intros.
  remember (typelen t) as n.
  remember (encode_val t v) as vl.
  assert (0 = Z_of_nat 0).
  auto.
  rewrite H1.
  eapply allocb_storebytes_mem_ex.
  omega.
Qed.

(* join *)
Lemma join_allocb : 
  forall m1 M m2 m1' m2' b i n, join m1 M m2 ->
    m1' = allocb m1 b i n ->
    m2' = allocb m2 b i n ->
    fresh m2 b ->
    join m1' M m2'.
Proof.
  introv. gen m1 M m2 m1' m2' i.
  induction n. 
  intros.
  simpl in H0,H1.
  subst;auto.
  intros.
  rewrite H0,H1.
  simpl.
  eapply join_set_nindom_l.
  eapply IHn;eauto.
  eauto.
  eauto.
  gen H2.
  clear.
  intro.
  assert (get (allocb m2 b (BinInt.Z.add i 1) n) (b, i) = None).
  apply allocb_get_none.
  omega.
  auto.
  red.
  intros.
  apply indom_get in H0.
  destruct H0.
  unfold get in *; simpl in *.
  rewrite H in H0.
  inversion H0.
Qed.

Lemma join_freeb :
  forall m1 M m2 m1' m2' b i n, join m1 M m2 ->
    freeb m1 b i n = Some m1' ->
    freeb m2 b i n = Some m2' ->
    join m1' M m2'.
Proof.
  introv.
  gen m1 M m2 m1' m2' i.
  induction n.
  simpl.
  intros.
  injection H0;intros;subst.
  injection H1;intros;subst.
  auto.
  simpl.
  intros.
  remember (get m1 (b, i)) as v1.
  remember (get m2 (b, i)) as v2.
  destruct v1,v2;tryfalse.
  destruct p.
  destruct b0; tryfalse.
  destruct p0.
  destruct b0; tryfalse.
  rename m into b0.
  rename m0 into b1.
  remember (freeb m1 b (i + 1) n) as m1''.
  remember (freeb m2 b (i + 1) n) as m2''.
  destruct m1'',m2'';tryfalse.
  injection H0; intros; subst.
  injection H1; intros; subst.

  assert (join m M m0).
  eapply IHn;eauto.
  assert (get m2 (b,i) = Some (true, b0)).
  eapply mem_join_get_get_l_true;eauto.
  assert (b1 = b0).
  rewrite H3 in Heqv2.
  injection Heqv2.
  intros;auto.
  
  subst b1.
  symmetry in Heqv1, Heqm1''.
  assert(get m (b,i) = get m1 (b,i)).
  eapply freeb_get_same; eauto.
  omega.
  rewrite Heqv1 in H4.

  eapply mem_join_del; eauto.
Qed.


Lemma join_free : 
  forall m1 M m2 m1' m2' t b, join m1 M m2 ->
    free t b m1 = Some m1' ->
    free t b m2 = Some m2' ->
    join m1' M m2'.
Proof.
  intros.
  unfold free in H0,H1.
  eapply join_freeb;eauto.
Qed.


Lemma join_storebytes : 
  forall m1 M m2 m1' m2' b o vl,
    join m1 M m2 ->
    storebytes m1 (b, o) vl = Some m1' ->
    storebytes m2 (b, o) vl = Some m2' ->
    join m1' M m2'.
Proof.
  intros.
  gen m1 M m2 m1' m2' o.
  induction vl.
  intros.
  simpl in H0,H1.
  injection H0;intros;subst.
  injection H1;intros;subst.
  auto.
  intros.
  simpl in H0,H1.

  unfold get in *; simpl in *.
  remember (HalfPermMap.get m1 (b, o)) as v1.
  remember (HalfPermMap.get m2 (b, o)) as v2.
  destruct v1,v2;tryfalse.
  destruct b0, b1.
  destruct b0, b1; tryfalse.
  remember (storebytes m1 (b, (o + 1)%Z) vl) as m1''.
  remember (storebytes m2 (b, (o + 1)%Z) vl) as m2''.
  destruct m1'',m2'';tryfalse.
  injection H0;intros;subst.
  injection H1;intros;subst.

  symmetry in Heqv1, Heqm1''.
  assert (get m (b,o) = get m1 (b,o)).
  erewrite storebytes_get_same with (off:=1); eauto.
  omega.

  eapply mem_join_set_true_join; eauto.
  unfold get in *; simpl in *.
  rewrite Heqv1 in H2.
  eauto.
Qed.


Lemma join_store : 
  forall m1 M m2 m1' m2' t a v,
    join m1 M m2 ->
    store t m1 a v = Some m1' ->
    store t m2 a v = Some m2' ->
    join m1' M m2'.
Proof.
  intros.
  unfold store in H0,H1.
  destruct a.
  destruct (encode_val t v);tryfalse.
  eapply join_storebytes;eauto.
  eapply join_storebytes;eauto.
Qed.


Lemma join_allocb_emp :
  forall M b i n,
    fresh M b ->
    join M (allocb emp b i n) (allocb M b i n).
Proof.
  intros.
  gen i.
  induction n. 
  intros.
  simpl.
  apply join_comm.
  eapply join_emp;eauto.
  intros.
  simpl.
  lets IHni : IHn (i+1).
  eapply join_set_nindom_r;eauto.
  red. intros.
  apply indom_get in H0.
  destruct H0.
  rewrite allocb_get_none in H0.
  false.
  omega.
  auto.
Qed.


Lemma join_allocb' :
  forall M1 M2 M b i n,
    join M2 M (allocb M2 b i n)  ->
    fresh M2 b ->
    fresh M1 b ->
    join M1 M (allocb M1 b i n). 
Proof.
  intros.
  eapply join_unique_r in H.
  2:eapply join_allocb_emp;eauto.
  rewrite<-H.
  eapply join_allocb_emp;eauto.
Qed.


Lemma join_store_allocb :
  forall M1 M2 M M'' M1' M2' b t v, 
    join M1 M M2 ->
    join M2 M'' M2' ->
    fresh M2 b ->
    store t (allocb M1 b 0 (typelen t)) (b, 0%Z) v = Some M1' ->
    store t (allocb M2 b 0 (typelen t)) (b, 0%Z) v = Some M2' ->
    join M1 M'' M1'.
Proof.
  intros.
  lets Hs: join_store H2 H3.
  eapply join_allocb;auto.
  apply H.

  assert(join (merge M1 M'') M M2').
  eapply mem_join_join_merge13_join; eauto.
  apply join_comm in Hs; apply join_comm in H4.
  lets Hx: join_unique_r Hs H4; substs.
  eapply mem_join_join_merge; eauto.
Qed.  


(* fresh *)
Lemma fresh_mono :
  forall m1 M m2 b, join m1 M m2 ->
    fresh m2 b -> fresh m1 b.
Proof.
  unfold fresh.
  intros.
  apply H0 in H1.
  intro.
  apply H1.
  unfolds.
  unfold indom in H2; destruct H2.
  destruct x.
  lets Hx: mem_join_get_get_l H2; eauto.
  destruct Hx.
  eauto.
Qed.


Lemma fresh_exist : forall m, (exists b,fresh m b).
Proof.
  intros.
  generalize MemoryNotFull.
  intros.
  generalize (H m).
  intros.
  unfold FullMemory in H0.
  apply not_all_ex_not in H0.
  destruct H0. exists x.
  unfold fresh.
  intros.
  red. intros. apply H0.
  exists i. subst. eauto.
Qed.

(* memory update *)
Lemma alloc_false : forall x t le M M', ~alloc x t le M le M'.
Proof.
  intros.
  red.
  intros.
  unfold alloc in H.
  destruct H.
  destruct H.
  destruct H0.
  destruct H1.
  apply H1.
  apply EnvMod.get_indom.
  rewrite H2.
  rewrite EnvMod.set_a_get_a;eauto.
  eapply identspec.eq_beq_true;eauto.
Qed.

Lemma free_false : forall t b M,(typelen t <> 0)%nat -> ~free t b M = Some M.
Proof.
  intros.
  remember (typelen t) as tlen.
  red.
  intros.
  destruct tlen.
  apply  H.
  auto.
  unfold free in H0.
  rewrite<-Heqtlen in H0.
  simpl in H0.
  remember (get M (b, BinNums.Z0)) as v.
  destruct v;tryfalse.
  remember (freeb M b 1 tlen) as M'.
  destruct p.
  destruct b0; tryfalse.
  destruct M';tryfalse.
  injection H0;intros.
  subst M.

  rewrite mem_del_get in Heqv; tryfalse.
Qed.


Lemma storebytes_mono' :
  forall M1 M1' M M2 M2' a l,
    storebytes M1 a l = Some M1' ->
    join M1 M M2 ->
    join M1' M M2' ->
    storebytes M2 a l = Some M2'.
Proof.
  intros.
  gen H H0 H1.
  gen M1 M1' M M2 M2' a.
  induction l; intros; simpl in *.

  inv H.
  lets H100 : join_unique H1 H0.
  rewrite H100; auto.

  destruct a0.
  unfold get in H; simpl in H.
  remember (HalfPermMap.get M1 (b, o)) as v1; destruct v1.
  2 : tryfalse.
  destruct b0.
  destruct b0; tryfalse.
  symmetry in Heqv1.
  lets H100 : mem_join_get_get_l_true H0 Heqv1.
  rewrite H100; clear H100.
  clear Heqv1.
  remember (storebytes M1 (b, o + 1) l) as v2; destruct v2.
  2 : tryfalse.
  symmetry in Heqv2.
  inversion H; clear H.
  
  cut (exists m', join m M m' /\ set m' (b, o) (true, a) = M2'); intros.
  do 2 destruct H.
  eapply IHl in Heqv2; eauto.
  rewrite Heqv2.
  unfold set in *; simpl in *.
  rewrite H2; auto.
  
  gen H1 H3; clear; intros.
  rewrite <- H3 in H1; clear H3.
  lets H100 : mem_join_set_l_rev H1.
  auto.
  destruct H100; eexists; intuition eauto.
Qed.


Lemma store_mono' :
  forall t M1 M1' M M2 M2' a v,
    store t M1 a v = Some M1' ->
    join M1 M M2 ->
    join M1' M M2' ->
    store t M2 a v = Some M2'.
Proof.
  intros.
  unfold store in *.
  destruct a.
  
  destruct v; simpl in *.

  eapply storebytes_mono'; eauto.
  eapply storebytes_mono'; eauto.
  
  destruct t; eapply storebytes_mono'; eauto.
  destruct a; destruct t; eapply storebytes_mono'; eauto.
Qed.

Lemma store_same_mono :
  forall t M M1 M2 a v,
    join M M1 M2 ->
    store t M a v = Some M ->
    store t M2 a v = Some M2.
Proof.
  intros; eapply store_mono'; eauto.
Qed.


Lemma join_storebytes_storebytes : forall vl b i M1 M1' M2 M,
                                     join M1 M2 M ->
                                     storebytes M1 (b, i) vl = Some M1' ->
                                     exists M', storebytes M (b, i) vl = Some M'.
Proof.
  inductions vl; intros.
  simpl; eauto.
  simpl in H0.
  unfold get in H0; simpl in H0.
  destruct (HalfPermMap.get M1 (b, i)) eqn : eq1; tryfalse.
  destruct b0.
  destruct b0; tryfalse.
  destruct (storebytes M1 (b, (i + 1)%Z) vl) eqn : eq2; tryfalse.
  simpl.
  assert (get M (b, i) = Some (true, c)).
  eapply mem_join_get_get_l_true; eauto.
  unfold get in *; simpl in *.
  rewrite H1.
  pose proof IHvl b (i + 1)%Z M1 m M2 M H eq2; clear IHvl.
  destruct H2.
  change offset with Z in H2.
  rewrite H2.
  eauto.
Qed.


Lemma join_store_general : forall Mc Mc' Ml M tp l v, 
                             join Ml Mc M ->
                             store tp Mc l v = Some Mc' ->
                             exists M', store tp M l v = Some M'.
Proof.
  intros.
  unfold store in H0.
  destruct l.
  unfold store.
  apply join_comm in H.
  eapply join_storebytes_storebytes; eauto.
Qed.

Lemma join_store':forall Mc Mc' Ml M tp b t, 
                   join Ml Mc M ->
                   store tp Mc (b,0%Z) (Vptr t) = Some Mc' ->
                   exists M',
                     store tp M (b,0%Z) (Vptr t) = Some M'.
Proof.
  intros.
  unfold store in H0.
  eapply join_store_general; eauto.
Qed.

Lemma join_store_join:
  forall Ml Mc M t l v Mc' M',
    join Ml Mc M ->
    store t Mc l v = Some Mc' ->
    store t M l v = Some M' ->
    join Ml Mc' M'.
Proof.
  unfold store.
  destruct l.
  intro.
  gen Ml Mc M b o.
  induction (encode_val t v); intros.
  simpl in H0; simpl in H1; inv H0; inv H1; auto.

  simpl in H0.
  unfold get in H0; simpl in H0.
  destruct (HalfPermMap.get Mc (b, o)) eqn : eq1; tryfalse.
  destruct b0.
  destruct b0; tryfalse.
  destruct (storebytes Mc (b, (o + 1)%Z) l) eqn : eq2; tryfalse.
  simpl in H1.
  unfold get in H1; simpl in H1.
  destruct (HalfPermMap.get M (b, o)) eqn : eq3; tryfalse.
  destruct b0.
  destruct b0; tryfalse.
  destruct (storebytes M (b, (o + 1)%Z) l) eqn : eq4; tryfalse.
  pose proof IHl Ml Mc M b (o+1)%Z m m0 H eq2 eq4; clear IHl.

  inv H0.
  inv H1.
  apply join_comm.
  apply join_comm in H2.
  eapply mem_join_set_true_join; auto.
  lets Hx: storebytes_get_same eq2.
  omega.
  unfold get in *; simpl in *.
  change ((fun x => (HalfPermMap.get m (b, o) = x))(HalfPermMap.get Mc (b, o))) in Hx.
  rewrite eq1 in Hx.
  eauto.
Qed.

Lemma disj_storebytes_disj : forall vl M1 M2 M1' b o, disjoint M1 M2 -> storebytes M1 (b, o) vl = Some M1' -> disjoint M1' M2.
Proof.
  inductions vl; intros.
  simpl in H0.
  inv H0; auto.

  simpl in H0.
  unfold get in H0; simpl in H0.
  destruct (HalfPermMap.get M1 (b, o)) eqn : eq1; tryfalse.
  destruct b0.
  destruct b0; tryfalse.
  destruct (storebytes M1 (b, (o + 1)%Z) vl) eqn : eq2; tryfalse.
  pose proof IHvl M1 M2 m b (o+1)%Z H eq2; clear IHvl.
  inv H0.

  assert (get m (b, o) = get M1 (b,o)).
  erewrite storebytes_get_same; eauto.
  omega.
  eapply mem_disjoint_set_l; eauto.
  unfold get in *; simpl in *.
  rewrite eq1 in H0; eauto.
Qed.


Lemma disj_store_disj:forall M1 M2 M1' t l v ,disjoint M1 M2 -> store t M1 l v = Some M1' -> disjoint M1' M2.
Proof.
  intros.
  unfold store in H0.
  destruct l.
  eapply disj_storebytes_disj; eauto.
Qed.  

Lemma merge_store_merge:
  forall M1 M2 m t l v M1' m',
    merge M1 M2 = m ->
    store t M1 l v = Some M1' ->
    store t m l v  = Some m' ->
    merge M1' M2 = m'.
Proof.
  unfold store.
  destruct l.
  intros.
  gen m M1 M2 b o M1' m' H H0 H1.
  induction (encode_val t v); intros.
  simpl in H0.
  simpl in H1.
  inv H0.
  inv H1.
  auto.
  simpl in H0.
  unfold get in H0; simpl in H0.
  destruct (HalfPermMap.get M1 (b, o)) eqn : eq1; tryfalse.
  destruct b0.
  destruct b0; tryfalse.
  destruct (storebytes M1 (b, (o + 1)%Z) l) eqn : eq2; tryfalse.
  simpl in H1.
  unfold get in H1; simpl in H1.
  destruct (HalfPermMap.get m (b, o)) eqn : eq3; tryfalse.
  destruct b0.
  destruct b0; tryfalse.
  destruct (storebytes m (b, (o + 1)%Z) l) eqn : eq4; tryfalse.
  pose proof IHl m M1 M2 b (o+1)%Z m0 m1 H eq2 eq4; clear IHl.
  inv H0.
  inv H1.

  eapply mem_get_set_merge_eq; eauto.
  lets Hx: storebytes_get_same eq2; eauto.
  omega.
  unfold get in *; simpl in *.
  instantiate (1:=c).
  change ((fun x =>(x = Some (true, c)))(HalfPermMap.get m0 (b, o))).
  rewrite Hx.
  auto.
Qed.


Lemma mem_set_a_set_a : forall (M:mem) a val1 val2, set (set M a val1) a val2 = set M a val2.
Proof.
  intros.
  eapply extensionality.
  intro.
  pose proof addr_eq_dec a a0.
  destruct H as [eq1 | eq1].
  substs.
  rewrite set_a_get_a.
  rewrite set_a_get_a.
  auto.
  
  rewrite set_a_get_a'.
  rewrite set_a_get_a'.
  rewrite set_a_get_a'.
  auto.
  auto.
  auto.
  auto.
Qed.


Lemma mem_set_a_set_a' : forall (M:mem) a v a' v', a <> a' ->
                                             set (set M a v) a' v' = set (set M a' v') a v.
Proof.
  intros.
  eapply extensionality.
  intro.
  pose proof addr_eq_dec a a0 as eq1; destruct eq1 as [eq1|eq1];
    pose proof addr_eq_dec a' a0 as eq2; destruct eq2 as [eq2|eq2].
  subst.
  tryfalse.
  
  rewrite set_a_get_a'.
  substs.
  rewrite set_a_get_a.
  rewrite set_a_get_a.
  auto.
  auto.
  auto.
  auto.
  substs.
  rewrite set_a_get_a.
  rewrite set_a_get_a'.
  rewrite set_a_get_a.
  auto.
  auto.
  rewrite set_a_get_a'.
  rewrite set_a_get_a'.
  rewrite set_a_get_a'.
  rewrite set_a_get_a'.
  auto.
  auto.
  auto.
  auto.
  auto.
Qed.


Lemma storebytes_set : forall l M M' b o o' a, storebytes M (b, o) l = Some M' -> (o' < o)%Z -> storebytes (set M (b, o') a) (b, o) l = Some (set M' (b, o') a).
Proof.
  inductions l; intros.
  simpl in H; simpl; inv H; auto.
  simpl in H.
  destruct (get M (b, o)) eqn : eq1; tryfalse.
  destruct (storebytes M (b, (o + 1)%Z) l) eqn : eq2; tryfalse.
  assert (o'<o+1)%Z.
  omega.
  pose proof IHl M m b (o+1)%Z o' a0 eq2 H1; clear IHl.
  simpl.
  rewrite set_a_get_a'.
  unfold get;simpl.
  unfold get in eq1;simpl in eq1.
  rewrite eq1.
  destruct p.
  change offset with Z in H2.
  rewrite H2.
  inv H.
  unfold get in H4;simpl in H4.
  rewrite eq1 in H4.
  destruct b0;auto.
  inverts H4.
  rewrite mem_set_a_set_a'.
  auto.
  intro.
  inversion H.
  assert (o' <> o).
  clear eq1 eq2 H1 H2 H H4; clears.
  omega.
  apply H3 in H4.
  false.
  tryfalse.
  intro.
  inversion H3.
  assert (o' <> o).
  omega.
  apply H4 in H5.
  false.
  unfold get in *;simpl in *.
  rewrite eq1 in H.
  destruct p.
  destruct b0;tryfalse.
  unfold get in *;simpl in *.
  rewrite eq1 in H.
  tryfalse.
Qed.

Lemma mem_disj_merge_minus_disj'
     : forall Ml Mc' Ms Ms' Mc'0 Mcc tp l v ,
       store tp Mc' l v = Some Mcc ->
       disjoint Mc'0 Ms' ->
       merge Mc'0 Ms' = merge Mcc Ms ->
       disjoint Ml Ms ->
       Maps.sub Mc' Ml ->
       disjoint (merge (minus Ml Mc') Mc'0) Ms'.
Proof.
  unfold store.
  destruct l.
  intro.
  gen Ml Mc' Ms Ms' Mc'0 Mcc b o.
  induction (encode_val tp v); intros.
  simpl in H.
  inv H.

  eapply memory_prop_map1; eauto.
  
  (* eapply disj_merge_intro_l. *)
  (* split; auto. *)
  
  (* assert(disjoint (minus Ml Mcc) (merge Mcc Ms)). *)
  (* Check mem_disjoint_disjoint_sub_disjoint_merge. *)
  (* eapply mem_disjoint_disjoint_sub_disjoint_merge; eauto. *)

  (* rewrite <- H1 in H. *)
  (* eapply mem_disjoint_disjoint_merge_disjoint; eauto. *)

  simpl in H.
  unfold get in H; simpl in H.
  destruct (HalfPermMap.get Mc' (b, o)) eqn : e1; tryfalse.
  destruct b0.
  destruct b0; tryfalse.
  destruct (storebytes Mc' (b, (o + 1)%Z) l) eqn : e2; tryfalse.
  assert (storebytes (set Mc' (b, o) (true, a)) (b, (o + 1)%Z) l = Some Mcc).
  clear IHl e1 H0 H1 H2 H3; clears.
  inv H.
  apply storebytes_set; auto.
  omega.

  assert (Maps.sub (set Mc' (b, o) (true, a)) (set Ml (b, o) (true,a))).
  clear IHl e2 H H0 H1 H2 H4; clears.
  eapply mem_sub_get_true_sub_set; eauto.
  assert (disjoint (set Ml (b, o) (true, a)) Ms).
  clear IHl e2 H H1 H4 H5; clears.
  eapply mem_disjoint_get_true_set_disjoint; eauto.


  eapply memory_prop_get_sub_get; eauto.
  
  pose proof IHl (set Ml (b, o) (true, a)) (set Mc' (b, o) (true,a)) Ms Ms' Mc'0 Mcc b (o+1)%Z H4 H0 H1 H6 H5.

  eapply mem_disjoint_merge_minus_get_true_set; eauto.
Qed.


Lemma mem_disj_merge_minus_merge'
     : forall Ml Mc Ms Ms' Mc' m Mcc m' v l tp,
         store tp Mc l v = Some Mcc ->
         store tp m l v= Some m' ->
         disjoint Mc' Ms' ->
         merge Mc' Ms' = merge Mcc Ms ->
         disjoint Ml Ms ->
         Maps.sub Mc Ml ->
         merge Ml Ms =m ->
         merge (merge (minus Ml Mc) Mc') Ms' = m'.
Proof.
  intros.
  unfold store in *.
  destruct l.
  gen Ml Mc Ms Ms' Mc' m Mcc m' b o.
  induction (encode_val tp v); intros.
  simpl in H; simpl in H0.
  inv H; inv H0.

  lets Hx: mem_disjoint_merge_eq_merge_merge H2; eauto.
  eapply mem_sub_disjoint; eauto.
  instantiate (TEMP3:=(minus Ml Mcc)).
  assert(disjoint (minus Ml Mcc) (merge Mcc Ms)).
  eapply mem_disjoint_sub_disjoint_merge; eauto.
  apply Hx in H.
  rewrite H.
  eapply mem_merge_merge_minus_merge; eauto.
     
  simpl in H.
  unfold get in H; simpl in H.
  destruct (HalfPermMap.get Mc (b, o)) eqn : eq1; tryfalse.
  destruct b0.
  destruct b0; tryfalse.
  destruct (storebytes Mc (b, (o + 1)%Z) l) eqn : eq2; tryfalse.
  simpl in H0.
  unfold get in H0; simpl in H0.
  destruct (HalfPermMap.get m (b, o)) eqn : eq3; tryfalse.
  destruct b0.
  destruct b0; tryfalse.
  destruct (storebytes m (b, (o + 1)%Z) l) eqn : eq4; tryfalse.
  pose proof IHl (set Ml (b, o) (true, a)) (set Mc (b, o) (true, a)); clear IHl.
  assert (Maps.sub (set Mc (b, o) (true, a)) (set Ml (b, o) (true, a))).
  clear H6 H3 H1 H5 H2 eq2 H eq3 eq4 H0; clears.
  eapply mem_sub_get_true_sub_set; eauto.
  
  pose proof H6 H7; clear H6 H7.
  assert (disjoint (set Ml (b, o) (true, a)) Ms).
  clear H1 H5 H2 eq2 H eq3 eq4 H0 H8; clears.
  eapply mem_disjoint_get_true_set_disjoint; eauto.
  eapply memory_prop_get_sub_get; eauto.
  
  pose proof H8 Ms H6; clear H6 H8.
  pose proof H7 Ms' Mc' H1; clear H7.
  assert (merge (set Ml (b, o) (true, a)) Ms = (set m (b, o) (true, a))).
  clear H3 H1 H2 eq2 eq3 eq4 H0 H6 H; clears.
  inv H5.
  eapply mem_get_set_merge_eq; eauto.
  eapply memory_prop_get_sub_get; eauto.
  
  pose proof H6 (set m (b, o) (true, a)) H7; clear H6 H7.
  pose proof H8 Mcc H2; clear H8.
  pose proof H6 m' b (o+1)%Z; clear H6.
  assert (storebytes (set Mc (b, o) (true, a)) (b, (o + 1)%Z) l = Some Mcc).
  inversion H.
  apply storebytes_set; auto.
  omega.

  assert (storebytes (set m (b, o) (true, a)) (b, (o + 1)%Z) l = Some m').
  inversion H0.
  apply storebytes_set; auto.
  omega.

  pose proof H7 H6 H8; clear H7 H6 H8.

  eapply mem_merge_merge_minus_get_true_set_eq; eauto.
Qed.  
  

Lemma store_sub_minus_eq:forall Ml M Ml' tp l v, Maps.sub Ml M -> store tp Ml l v = Some Ml' -> minus M Ml = minus M Ml'. 
Proof.
  intros.
  unfold store in H0.
  destruct l.
  gen Ml M Ml' b o.
  induction (encode_val tp v); intros.
  simpl in H0; simpl; inv H0; auto.

  simpl in H0.
  unfold get in H0; simpl in H0.
  destruct (HalfPermMap.get Ml (b, o)) eqn : eq1; tryfalse.
  destruct b0.
  destruct b0; tryfalse.
  destruct (storebytes Ml (b, (o + 1)%Z) l) eqn : eq2; tryfalse.
  
  

  assert (Maps.sub (set Ml (b, o) (true, a)) (set M (b, o) (true, a))).

  
  eapply mem_sub_get_true_set_sub; eauto.
  
  pose proof IHl (set Ml (b, o) (true, a)) (set M (b, o) (true, a)) H1; clear IHl.
  assert (storebytes (set Ml (b, o) (true,a)) (b, (o+1)%Z) l = Some Ml').
  inversion H0.
  apply storebytes_set; auto.
  omega.
  
  pose proof H2 Ml' b (o+1)%Z H3; clear H2.
  clear eq2 H3; clears.
  inverts H0.
  
  Lemma memory_prop_map2:
    forall (A B T : Type) (MC : PermMap A B T) m Ml M a b c,
      usePerm = true ->
      Maps.sub Ml M ->
      isRw c = true ->
      get Ml a = Some c ->
      isRw b = true ->
      minus (set M a b) (set Ml a b) =
      minus (set M a b) (set m a b) ->
      minus M Ml = minus M (set m a b).
    intros.
    Ltac infer ::= infer'.
    hy_eql (pnil, Ml, M, Maps.sub Ml M,
            set M a b, set Ml a b,
            minus (set M a b) (set Ml a b),
            m, set m a b,
            minus (set M a b) (set m a b),
            minus M Ml, minus M (set m a b)) t;
    crush.
    Ltac infer ::= infer_q.
    generalize (@map_flip_eql' _ _ _ _ _ _ H H19); intro.
    subst b0.
    auto.
  Qed.

  eapply memory_prop_map2; ica.
Qed.
  (* assert (forall a0, get ( minus (set M (b, o) (true, a)) (set Ml (b, o) (true, a))) a0 = get (minus (set M (b, o) (true, a)) Ml') a0). *)
  (* rewrite H4; auto. *)
  (* clear H4. *)
  (* eapply extensionality. *)
  (* intro. *)
  (* pose proof H0 a0; clear H0.  *)


  (* eapply memory_prop_map2; eauto. *)
  (* unfold isRw; simpl; auto. *)
  (* unfold isRw; simpl; auto. *)
  (* rewrite minus_sem. *)
  (* rewrite minus_sem. *)
  (* rewrite minus_sem in H1. *)
  (* rewrite minus_sem in H1. *)
  (* assert ((b, o) = a0 \/ (b,o) <> a0) as Hxx by tauto. *)
  (* destruct Hxx. *)
  (* substs. *)
  (* rewrite set_a_get_a in H1. *)
  (* rewrite set_a_get_a in H1. *)
  (* unfold get in *; simpl in *. *)
  (* rewrite eq1. *)
  (* destruct (HalfPermMap.get Ml' (b, o)) eqn : eq2; tryfalse. *)
  (* auto. *)

  (* rewrite set_a_get_a' in H1; auto. *)
  (* rewrite set_a_get_a' in H1; auto. *)

Lemma store_disj_merge:forall M M1 Ms M2 tp l v, disjoint M (merge M1 Ms) -> store tp M1 l v = Some M2 -> disjoint M (merge M2 Ms). 
Proof.
  intros.
  unfold store in H0.
  destruct l.
  gen M M1 Ms M2 b o.
  induction (encode_val tp v); intros.
  simpl in H0; inv H0; auto.

  simpl in H0.
  unfold get in *; simpl in *.
  destruct (HalfPermMap.get M1 (b, o) ) eqn : eq1; tryfalse.
  destruct b0.
  destruct b0; tryfalse.
  destruct (storebytes M1 (b, (o + 1)%Z) l) eqn : eq2; tryfalse.
  pose proof IHl M M1 Ms H m b (o+1)%Z eq2; clear IHl.
  inv H0.

  assert(get m (b, o) = get M1 (b, o)).
  eapply storebytes_get_same; eauto.
  omega.
  unfold get in *; simpl in *.
  rewrite eq1 in H0.
  
  erewrite mem_get_set_merge_eq; eauto.
  apply disjoint_sym.
  apply disjoint_sym in H1.
  eapply mem_disjoint_get_true_set_disjoint; eauto.
  instantiate (1:=c).


  eapply memory_prop_map3; eauto.
Qed.

Lemma store_sub_disj_disj:
  forall M1 M2 Ms Ml M2' tp l v,
    store tp M2 l v = Some M2' ->
    disjoint Ml Ms ->
    Maps.sub M2 Ml ->
    Maps.sub M1 (merge M2' Ms) ->
    disjoint (minus Ml M2') M1.
Proof.
  intros.
  assert (disjoint (minus Ml M2) (merge M2 Ms)).
  eapply mem_disjoint_disjoint_sub_disjoint_merge; auto.
  assert (disjoint (minus Ml M2) (merge M2' Ms)).
  eapply store_disj_merge;  eauto.
  lets Hx: store_sub_minus_eq H1 H.
  rewrite Hx in H4.
  clear - H2 H4.
  apply disjoint_sym.
  apply disjoint_sym in H4.
  eapply mem_sub_disjoint; eauto.
Qed.


Lemma mem_join_merge_minus_join_store'
(*can be derived by lemma " mem_disj_merge_minus_disj' " and  "mem_disj_merge_minus_merge'"*)
: forall Ml Mc Ms Ms' Mc' m Mcc m' v l tp,
    store tp Mc l v = Some Mcc ->
    store tp m l v= Some m' ->
    disjoint Mc' Ms' ->
    merge Mc' Ms' = merge Mcc Ms ->
    Maps.sub Mc Ml ->
    join Ml Ms m ->
    join (merge (minus Ml Mc) Mc') Ms' m'.
Proof.
  intros.
  lets Hx1: mem_disj_merge_minus_disj' H H1 H2 H3.
  eapply my_join_disj; eauto.
  lets Hx2: mem_disj_merge_minus_merge' H H0 H1 H2 H3.
  eapply my_join_disj; eauto.
  assert (merge Ml Ms = m).
  eapply mem_join_disjoint_eq_merge in H4; simpljoin.
  unfold merge in *; simpl in *.
  change ((fun x => (x ->
                     HalfPermMap.merge (HalfPermMap.merge (minus Ml Mc) Mc') Ms' = m'))(HalfPermMap.merge Ml Ms = m)) in Hx2.
  rewrite H5 in Hx2.
  assert (m=m) by auto.
  apply Hx2 in H6.
  rewrite <- H6.

  eapply join_merge_disj; eauto.
Qed.

Close Scope Z_scope.
