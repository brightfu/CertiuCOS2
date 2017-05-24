Require Import include_frm.
Require Import join_lib.

(******************************************************************************)
(** 2016.7.5 added **)
Lemma disj_complex'f_auto :
  forall (A B T : Type) (MC : PermMap A B T)
         O' Ox x0 Oc'0 Os'' OO' Os' OO'' Olc Occ
         a b b' Olx' O1 O2,
    usePerm = false ->
    join Olx' Os'' OO'' ->
    join Oc'0 O2 Olx' ->
    OO'' = set (merge O' Os') a b' ->
    join O1 O2 Olc ->
    join Olc Occ O' ->
    join O' Os' OO' ->
    join OO' Ox x0 ->
    get Occ a = Some b ->
    disjoint (merge Oc'0 O2) Ox.
Proof.          
  intros.
  subst.
  
  assert (merge O' Os' = OO').
  {
    eapply join_sem' in H5.
    heat.
    auto.
  }
  assert (merge Oc'0 O2 = Olx').
  {
    eapply join_sem' in H1.
    heat.
    auto.
  }
  rewrite H2 in *.
  rewrite H8 in *.
  clear H2 H8.
  assert (get OO' a = Some b).
  {
    geat.
  }
  assert (get x0 a = Some b).
  {
    geat.
  }
  
  clear H1 H3 H4 H5 H7 H8.
  hy.
Qed.

Lemma disj_complex'f :
  forall (O' Ox x0 Oc'0 Os'' OO' Os' OO'' Olc Occ : osabst)
         (a : absdataid) (b b' : absdata) Olx' O1 O2,
    join Olx' Os'' OO'' ->
    join Oc'0 O2 Olx' ->
    OO'' = set (merge O' Os') a b' ->
    join O1 O2 Olc ->
    join Olc Occ O' ->
    join O' Os' OO' ->
    join OO' Ox x0 ->
    get Occ a = Some b ->
    disjoint (merge Oc'0 O2) Ox.
Proof.
  intros.
  subst.
  eapply disj_complex'f_auto; auto; ica.
Qed.  

Lemma mem_4join_merge135_disjoint_join_merge24_auto :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 m4 m5 m6 m7 m12 m123 m1234 m12345,
    usePerm = true ->
    join m1 m2 m12 ->
    join m12 m3 m123 ->
    join m123 m4 m1234 ->
    join m1234 m5 m12345 ->
    disjoint m6 m7 ->
    merge m6 m7 = merge (merge m3 m1) m5 ->
    join (merge (merge m4 m2) m6) m7 m12345.
  intros.
  assert (join m6 m7 (merge (merge m3 m1) m5)).
  {
    eapply join_sem.
    auto.
    auto.
  }
  clear H4 H5.
  assert (Hx1: exists m31, join m3 m1 m31).
  {
    geat.
  }
  destruct Hx1 as (m31 & Hx1).
  assert (Hx2: exists m315, join m31 m5 m315).
  {
    geat.
  }
  destruct Hx2 as (m315 & Hx2).
  assert (Hx3: exists m42, join m4 m2 m42).
  {
    geat.
  }
  destruct Hx3 as (m42 & Hx3).
  assert (Hx4: join m315 m42 m12345).
  {
    geat.
  }
  clear H0 H1 H2 H3.
  assert (merge m3 m1 = m31).
  {
    eapply join_sem' in Hx1.
    heat; auto.
  }
  assert (merge m31 m5 = m315).
  {
    eapply join_sem' in Hx2.
    heat; auto.
  }
  rewrite H0 in *.
  rewrite H1 in *.
  clear H0 H1.
  assert (merge m4 m2 = m42).
  {
    eapply join_sem' in Hx3.
    heat; auto.
  }
  rewrite H0.
  clear H0.
  clear Hx2.
  clear Hx1.
  assert (disjoint m42 m6).
  {
    unfold disjoint.
    geat.
  }
  unfold disjoint in H0.
  heat.
  assert (merge m42 m6 = x).
  {
    eapply join_sem' in H0.
    heat; auto.
  }
  rewrite H1.
  clear H1.
  geat.
Qed.

Lemma mem_4join_merge135_disjoint_join_merge24 :
  forall (m1:mem) m2 m3 m4 m5 m6 m7 m12 m123 m1234 m12345,
    join m1 m2 m12 ->
    join m12 m3 m123 ->
    join m123 m4 m1234 ->
    join m1234 m5 m12345 ->
    disjoint m6 m7 ->
    merge m6 m7 = merge (merge m3 m1) m5 ->
    join (merge (merge m4 m2) m6) m7 m12345.
Proof.
  intros; eapply mem_4join_merge135_disjoint_join_merge24_auto; ica.
Qed.

(******************************************************************************)
(** 2016.07.01 added **)

Lemma mem_join_join_disjoint_merge_auto :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 m4 m12 m123,
    usePerm = true ->
    join m1 m2 m12 ->
    join m12 m3 m123 ->
    disjoint m123 m4->
    disjoint (merge m3 m1) m4.
  hy.
Qed.

Lemma mem_join_join_disjoint_merge :
  forall (m1:mem) m2 m3 m4 m12 m123,
    join m1 m2 m12 ->
    join m12 m3 m123 ->
    disjoint m123 m4->
    disjoint (merge m3 m1) m4.
Proof.
  intros; eapply mem_join_join_disjoint_merge_auto; ica.
Qed.

Lemma osabst_disjoint_set_merge_auto :
  forall (A B T : Type) (MC : PermMap A B T) Ol Os OO OOO Olc O1 O2 a b b',
    usePerm = false ->
    join OOO Os OO ->
    join Olc Ol OOO ->
    join O1 O2 Olc ->
    get Ol a = Some b ->
    disjoint (set (merge Ol O1) a b') Os.
  hy.
Qed.

Lemma osabst_disjoint_set_merge :
  forall (Ol:osabst) Os OO OOO Olc O1 O2 a b b',
    join OOO Os OO ->
    join Olc Ol OOO ->
    join O1 O2 Olc ->
    get Ol a = Some b ->
    disjoint (set (merge Ol O1) a b') Os.
Proof.
  intros; eapply osabst_disjoint_set_merge_auto; ica.
Qed.

Lemma osabst_join_minus_merge_merge_set_auto :
  forall (A B T : Type) (MC : PermMap A B T) Ol Os OO OOO Olc O1 O2 x4 x5 a b b',
    usePerm = false ->
    join OOO Os OO ->
    join Olc Ol OOO ->
    join O1 O2 Olc ->
    disjoint x4 x5 ->
    merge x4 x5 = merge (set (merge Ol O1) a b') Os ->
    get Ol a = Some b ->
    join (minus (merge (merge x4 x5) O2) x5) x5 (set OO a b').
Proof.
  intros.
  assert (join x4 x5 (merge (set (merge Ol O1) a b') Os)).
  {
    eapply join_sem; eauto.
  }
  clear H4.
  clear H3.
  Ltac infer ::= infer_v.
  hy.
  Ltac infer ::= infer_q.
Qed.

Lemma osabst_join_minus_merge_merge_set :
  forall (Ol:osabst) Os OO OOO Olc O1 O2 x4 x5 a b b',
    join OOO Os OO ->
    join Olc Ol OOO ->
    join O1 O2 Olc ->
    disjoint x4 x5 ->
    merge x4 x5 = merge (set (merge Ol O1) a b') Os ->
    get Ol a = Some b ->
    join (minus (merge (merge x4 x5) O2) x5) x5 (set OO a b').
Proof.
  intros; eapply osabst_join_minus_merge_merge_set_auto; ica.
Qed.

Lemma osabst_join_minus_merge_merge_auto :
  forall (A B T : Type) (MC : PermMap A B T) Ol Os OO OOO Olc O1 O2 x4 x5 a b b',
    usePerm = false ->
    join OOO Os OO ->
    join Olc Ol OOO ->
    join O1 O2 Olc ->
    disjoint x4 x5 ->
    merge x4 x5 = merge (set (merge Ol O1) a b') Os ->
    get Ol a = Some b ->
    join x4 O2 (minus (merge (merge x4 x5) O2) x5).
  intros.
  assert (join x4 x5 (merge (set (merge Ol O1) a b') Os)).
  {
    eapply join_sem; eauto.
  }
  clear H4.
  clear H3.
  Ltac infer ::= infer_v.
  hy.
  Ltac infer ::= infer_q.
Qed.

Lemma osabst_join_minus_merge_merge :
  forall (Ol:osabst) Os OO OOO Olc O1 O2 x4 x5 a b b',
    join OOO Os OO ->
    join Olc Ol OOO ->
    join O1 O2 Olc ->
    disjoint x4 x5 ->
    merge x4 x5 = merge (set (merge Ol O1) a b') Os ->
    get Ol a = Some b ->
    join x4 O2 (minus (merge (merge x4 x5) O2) x5).
Proof.
  intros; eapply osabst_join_minus_merge_merge_auto; auto.
  3:eauto.
  3:eauto.
  eauto.
  eauto.
  eauto.
Qed. 

(******************************************************************************)
Lemma join_complexf_auto :forall (A B T : Type) (MC : PermMap A B T)
    Ol Oc x0 Os' OO'0 Olc Occ O'0 a b b' Oc'0 OO'' Os'' O1 O2 Olx',
    usePerm = false ->
    join OO'0 (minus Ol Oc) x0 ->
    join O'0 Os' OO'0 ->
    join Olc Occ O'0 ->
    join O1 O2 Olc ->
    get Occ a = Some b ->
    OO'' = set (merge O'0 Os') a b' ->
    join Olx' Os'' OO'' ->
    join Oc'0 O2 Olx' ->
    join (merge (merge Oc'0 O2) (minus Ol Oc)) Os'' (set x0 a b').
  intros.
  subst.
  remember (minus Ol Oc) as Olc'.
  clear HeqOlc'.
  assert (merge Oc'0 O2 = Olx').
  {
    eapply join_sem' in H7.
    heat.
    auto.
  }
  assert (merge O'0 Os' = OO'0).
  {
    eapply join_sem' in H1.
    heat; auto.
  }
  rewrite H5 in *.
  rewrite H8 in *.
  clear H5 H8.
  assert (get OO'0 a = Some b).
  {
    geat.
  }
  assert (get x0 a = Some b).
  {
    geat.
  }
  clear H1 H2 H3 H4.
  Ltac infer ::= infer_v.
  hy.
  Ltac infer ::= infer_q.
Qed.

Lemma join_complexf :
  forall Ol Oc x0 : osabst,
  forall (Os' OO'0 Olc Occ O'0 : osabst) (a : absdataid)
    (b b' : absdata) (Oc'0 OO'' Os'' : osabst) O1 O2 Olx',
    join OO'0 (minus Ol Oc) x0 ->
    join O'0 Os' OO'0 ->
    join Olc Occ O'0 ->
    join O1 O2 Olc ->
    get Occ a = Some b ->
    OO'' = set (merge O'0 Os') a b' ->
    join Olx' Os'' OO'' ->
    join Oc'0 O2 Olx' ->
    join (merge (merge Oc'0 O2) (minus Ol Oc)) Os'' (set x0 a b').
  intros; eapply join_complexf_auto; ica.
Qed.

Lemma mem_4join_merge135_disjoint_disjoint_merge24_auto :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 m4 m5 m6 m7 m12 m123 m1234 m12345,
    usePerm = true ->
    join m1 m2 m12 ->
    join m12 m3 m123 ->
    join m123 m4 m1234 ->
    join m1234 m5 m12345 ->
    disjoint m6 m7 ->
    merge m6 m7 = merge (merge m3 m1) m5 ->
    disjoint (merge m4 m2) m6.
  intros.
  eapply disjoint_semp; auto.
  intro t.
  let i := calc_ins in
  infer i t; infer' (pnil, merge m6 m7, merge m3 m1, merge (merge m3 m1) m5, merge m4 m2) t;
  rewrite H5 in *;
  crush.
Qed.

Lemma mem_4join_merge135_disjoint_disjoint_merge24 :
  forall (m1:mem) m2 m3 m4 m5 m6 m7 m12 m123 m1234 m12345,
    join m1 m2 m12 ->
    join m12 m3 m123 ->
    join m123 m4 m1234 ->
    join m1234 m5 m12345 ->
    disjoint m6 m7 ->
    merge m6 m7 = merge (merge m3 m1) m5 ->
    disjoint (merge m4 m2) m6.
Proof.
  intros; eapply mem_4join_merge135_disjoint_disjoint_merge24_auto; ica.
Qed.


Lemma mem_sub_sub_join_join_merge_minus_auto :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 m4 m5,
    usePerm = true ->
    Maps.sub m1 m2 ->
    Maps.sub m2 m3 ->
    join m4 m3 m5 ->
    join m4 (merge (minus m3 m2) m1) (merge (minus m5 m2) m1).
  hy.
Qed.


Lemma mem_sub_sub_join_join_merge_minus :
  forall (m1:mem) m2 m3 m4 m5,
    Maps.sub m1 m2 ->
    Maps.sub m2 m3 ->
    join m4 m3 m5 ->
    join m4 (merge (minus m3 m2) m1) (merge (minus m5 m2) m1).
Proof.
  intros; eapply mem_sub_sub_join_join_merge_minus_auto; ica.
Qed.

Lemma join_join_merge_disjoint_auto :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 m4 m5 m6 m7 m12 m123,
    usePerm = true ->
    join m1 m2 m12 ->
    join m12 m3 m123 ->
    disjoint m123 m4 ->
    disjoint m4 m5 ->
    disjoint m123 m5 ->
    disjoint (merge m123 m4) m5 ->
    merge m6 m7 = merge (merge m3 m1) m5 ->
    disjoint m6 m4.
  intros.
  eapply disjoint_semp; auto.
  intro t.
  let i := calc_ins in
  infer i t; infer' (pnil, m6, m7, merge m6 m7, merge m3 m1, merge (merge m3 m1) m5) t;
  rewrite H6 in *;
  crush.
Qed.

Lemma join_join_merge_disjoint :
  forall (m1:mem) m2 m3 m4 m5 m6 m7 m12 m123,
    join m1 m2 m12 ->
    join m12 m3 m123 ->
    disjoint m123 m4 ->
    disjoint m4 m5 ->
    disjoint m123 m5 ->
    disjoint (merge m123 m4) m5 ->
    merge m6 m7 = merge (merge m3 m1) m5 ->
    disjoint m6 m4.
Proof.
  intros; eapply join_join_merge_disjoint_auto; auto.
  3: eauto.
  3: eauto.
  5: eauto.
  2: eauto.
  eauto.
  eauto.
  eauto.
Qed.

Lemma osabst_join_join_sub_join_disjoint_auto :
  forall (A B T : Type) (MC : PermMap A B T) o1 o2 o3 o4 o5 o12 o123 o1234,
    usePerm = false ->
    join o1 o2 o12 ->
    join o12 o3 o123 ->
    join o123 o4 o1234 ->
    Maps.sub o5 o4 ->
    disjoint o1 o5.
  hy.
Qed.

Lemma osabst_join_join_sub_join_disjoint :
  forall (o1:osabst) o2 o3 o4 o5 o12 o123 o1234,
    join o1 o2 o12 ->
    join o12 o3 o123 ->
    join o123 o4 o1234 ->
    Maps.sub o5 o4 ->
    disjoint o1 o5.
Proof.
  intros; eapply osabst_join_join_sub_join_disjoint_auto; ica.
Qed.

