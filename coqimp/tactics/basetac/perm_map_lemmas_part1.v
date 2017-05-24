Require Import memory.
Require Import language.
Require Import join_lib.
Require Import join_tactics.

Import veg.

(******************************************************************************)
(** newly added 2016.6.8 **)

Lemma join_eq_minus :
  forall {A B T:Type} {MC:PermMap A B T}
         m1 m2 m3,
    join m1 m2 m3 ->
    m1 = minus m3 m2.
Proof.
  hy.
Qed.

Lemma join_minus_extend :
  forall {A B T:Type} {MC:PermMap A B T}
         m1 m2 m3 m4,
    join m1 m2 (minus m3 m4) ->
    exists m5 m6,
      join m1 m5 m3 /\ join m2 m6 m5.
Proof.
  intros.
  assert (join m1 (minus m3 m1) m3).
  hy.
  exists (minus m3 m1).
  assert (Maps.sub m2 (minus m3 m1)).
  {
    clear H0.
    hy.
  }
  unfold Maps.sub in *.
  destruct H1.
  exists x.
  crush.
Qed.  

(******************************************************************************)
(** newly added 2016.06.06 *)


Ltac crush ::= crush2; invert_flip; crush2.

Lemma mem_join_sig_eq_auto :
  forall (A B T : Type) (MC : PermMap A B T) l a b m m1 m2,
    usePerm = true ->
    isRw a = isRw b ->
    join (sig l a) m1 m ->
    join (sig l b) m2 m ->
    a = b.
  intros.
  let inc := calc_ins_for_context in
  infer inc l; crush.
  destruct (isRw b0); tryfalse.
  rewrite H9 in *.
  assert (isRw (flip b0) = true) by jeauto2.
  tryfalse.
Qed.


Lemma mem_join_sig_eq :
  forall l a b p (m:mem) m1 m2,
    join (sig l (p, a)) m1 m ->
    join (sig l (p, b)) m2 m ->
    a = b.
Proof.
  intros.
  assert ((p,a) = (p,b)).
  {
    eapply mem_join_sig_eq_auto; ica.
  }
  inverts H1.
  auto.
Qed.

Lemma mem_sub_sig_true_get_auto :
  forall (A B T : Type) (MC : PermMap A B T) m a x,
    usePerm = true ->
    isRw x = true ->
    Maps.sub (sig a x) m ->
    get m a = Some x.
  hy.
Qed.

Lemma mem_sub_sig_true_get :
  forall (m:mem) a x,
    Maps.sub (sig a (true, x)) m ->
    get m a = Some (true, x).
Proof.
  intros; eapply mem_sub_sig_true_get_auto; ica.
Qed.

Lemma osabst_disjoint_join_sig_get_none_auto :
  forall (A B T : Type) (MC : PermMap A B T) o1 o2 o3 a x,
    usePerm = false ->
    disjoint o1 o2 ->
    join (sig a x) o3 o1 ->
    get o2 a = None.
  hy.
Qed.

Lemma osabst_disjoint_join_sig_get_none :
  forall (o1:osabst) o2 o3 a x,
    disjoint o1 o2 ->
    join (sig a x) o3 o1 ->
    get o2 a = None.
Proof.
  intros; eapply osabst_disjoint_join_sig_get_none_auto; ica.
Qed.

Lemma osabst_join_join_disjoint_auto :
  forall (A B T : Type) (MC : PermMap A B T) o1 o2 o12 o3 o123,
    usePerm = false ->
    join o1 o2 o12 ->
    join o12 o3 o123 ->
    disjoint o1 o3.
  hy.
Qed.

Lemma osabst_join_join_disjoint :
  forall (o1:osabst) o2 o12 o3 o123,
    join o1 o2 o12 ->
    join o12 o3 o123 ->
    disjoint o1 o3.
Proof.
  intros; eapply osabst_join_join_disjoint_auto; ica.
Qed.

Ltac crush ::= crush2.
Lemma mem_join_join_join_merge_join_merge_auto :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m12 m3 m4 m5 m,
    usePerm = true ->
    join m12 m3 m ->
    join m1 m2 m12 ->
    join m4 m5 (merge m2 m3) ->
    join (merge m1 m4) m5 m.
  hy. (** new crush: 130s, old crush: 118 s **)
Qed.

Lemma mem_join_join_join_merge_join_merge :
  forall (m1:mem) m2 m12 m3 m4 m5 m,
    join m12 m3 m ->
    join m1 m2 m12 ->
    join m4 m5 (merge m2 m3) ->
    join (merge m1 m4) m5 m.
Proof.
  intros; eapply mem_join_join_join_merge_join_merge_auto; ica.
Qed.

Lemma osabst_join_join_join_merge_join_merge_auto :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m12 m3 m4 m5 m,
    usePerm = false ->
    join m12 m3 m ->
    join m1 m2 m12 ->
    join m4 m5 (merge m2 m3) ->
    join (merge m1 m4) m5 m.
  hy.
Qed.


Lemma osabst_join_join_join_merge_join_merge :
  forall (m1:osabst) m2 m12 m3 m4 m5 m,
    join m12 m3 m ->
    join m1 m2 m12 ->
    join m4 m5 (merge m2 m3) ->
    join (merge m1 m4) m5 m.
Proof.
  intros; eapply osabst_join_join_join_merge_join_merge_auto; ica.
Qed.

Lemma mem_join_join_join_merge_disjoint_auto :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m12 m3 m4 m5 m,
    usePerm = true ->
    join m12 m3 m ->
    join m1 m2 m12 ->
    join m4 m5 (merge m2 m3) ->
    disjoint m1 m4.
  hy.
Qed.

Lemma mem_join_join_join_merge_disjoint :
  forall (m1:mem) m2 m12 m3 m4 m5 m,
    join m12 m3 m ->
    join m1 m2 m12 ->
    join m4 m5 (merge m2 m3) ->
    disjoint m1 m4.
Proof.
  intros; eapply mem_join_join_join_merge_disjoint_auto; auto.
  3:eauto.
  eauto.
  eauto.
Qed.

Lemma osabst_join_join_join_merge_disjoint_auto :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m12 m3 m4 m5 m,
    usePerm = false ->
    join m12 m3 m ->
    join m1 m2 m12 ->
    join m4 m5 (merge m2 m3) ->
    disjoint m1 m4.
  hy.
Qed.

Lemma osabst_join_join_join_merge_disjoint :
  forall (m1:osabst) m2 m12 m3 m4 m5 m,
    join m12 m3 m ->
    join m1 m2 m12 ->
    join m4 m5 (merge m2 m3) ->
    disjoint m1 m4.
Proof.
  intros; eapply osabst_join_join_join_merge_disjoint_auto; auto.
  3:eauto.
  eauto.
  eauto.
Qed.

(** end **)

(******************************************************************************)
Lemma mem_join_disjoint_eq_merge :
  forall (m1:mem) m2 m3,
    join m1 m2 m3 ->
    disjoint m1 m2 /\ m3 = merge m1 m2.
Proof.
  intros.
  apply join_disjoint_eq_merge; auto.
Qed.

Lemma mem_join_join_merge23_join :
  forall (m1:mem) m2 m12 m3 m123,
    join m1 m2 m12 ->
    join m12 m3 m123 ->
    join m1 (merge m2 m3) m123.
Proof.
  intros.
  eapply join_join_merge23_join; eauto.
Qed.

Lemma mem_join_get_get_l :
  forall (m1:mem) m2 m3 a b p,
    join m1 m2 m3 ->
    get m1 a = Some (p, b) ->
    exists p', get m3 a = Some (p', b).
Proof.
  intros.
  assert (exists v', get m3 a = Some v' /\ sameV (p,b) v').
  {
    eapply join_get_get_lp; eauto.
  }
  destruct H1.
  destruct H1.
  destruct x.
  exists b0.
  unfold sameV in H2.
  simpl in H2.
  unfold HalfPermMap.sameV in H2.
  simpl in H2.
  subst.
  auto.
Qed.  
  
Lemma mem_join_get_get_l_true :
  forall (m1:mem) m2 m3 a b,
    join m1 m2 m3 ->
    get m1 a = Some (true, b) ->
    get m3 a = Some (true, b).
Proof.
  intros.
  eapply join_get_get_l_true; eauto. 
Qed.

Lemma mem_join_join_disjoint :
  forall (m1:mem) m2 m12 m3 m123,
    join m1 m2 m12 ->
    join m12 m3 m123 ->
    disjoint m1 m3.
Proof.
  intros.
  eapply join_join_disjoint; eauto.
Qed.

Lemma mem_join_merge_rearange :
  forall (m1:mem) m2 m12 m3 m123 m4 m1234,
    join m1 m2 m12 ->
    join m12 m3 m123 ->
    join m123 m4 m1234 ->
    join (merge m1 m3) (merge m2 m4) m1234.
Proof.
  intros.
  eapply join_merge_rearange; eauto.
Qed.  

Lemma mem_join_join_join_merge :
  forall (m1:mem) m2 m12 m3 m123 m4 m1234,
    join m1 m2 m12 ->
    join m12 m3 m123 ->
    join m123 m4 m1234 ->
    join m1 m4 (merge m1 m4).
Proof.
  intros.
  eapply join_join_join_merge'; eauto.
Qed.  

Lemma mem_join_disjoint_disjoint :
  forall (m1:mem) m2 m12 m3,
    join m1 m2 m12 ->
    disjoint m12 m3 ->
    disjoint m1 m3.
Proof.
  intros.
  eapply join_disjoint_disjoint; eauto.
Qed.

Lemma mem_disjoint_merge_disjoint :
  forall (m1:mem) m2 m3 m123,
    join m1 (merge m2 m3) m123 ->
    disjoint m2 m3 ->
    disjoint m1 m2.
Proof.
  intros.
  eapply disjoint_merge_disjoint; eauto.
Qed.

Lemma mem_join_merge_disjoint :
  forall (m1:mem) m2 m3 m4,
    join m1 (merge m2 m3) m4 ->
    disjoint m2 m3 ->
    join (merge m1 m2) m3 m4.
Proof.
  intros.
  eapply join_merge_disjoint; eauto.
Qed.

Lemma mem_get_join_get :
  forall (m1:mem) m2 m3 a x,
    join m1 m2 m3 ->
    get m3 a = Some (true, x) ->
    get m2 a = None ->
    get m1 a = Some (true, x).
Proof.
  intros.
  eapply get_join_getp; eauto.
Qed.

Lemma mem_get_join_sig_del :
  forall (m:mem) a x,
    get m a = Some (true, x) ->
    join (sig a (true, x)) (del m a) m.
Proof.
  intros.
  eapply get_join_sig_del; eauto.
Qed.

(*hard*)
Lemma mem_get_join_join_del_exists :
  forall (m1:mem) m2 m3 a x,
    get m3 a = Some (true, x) ->
    join m1 m2 m3 ->
    exists m2', join (del m1 a) m2' m3.
Proof.
  intros.
  eapply get_join_join_del_exists; eauto.
Qed.

Lemma mem_join_get_get_r_true :
  forall m1 m2 m3 a x,
    join m1 m2 m3 ->
    get m2 a = Some (true, x) ->
    get m3 a = Some (true, x).
Proof.
  intros.
  eapply join_get_get_r_true; eauto.
Qed.

Lemma mem_join_true_del :
  forall m1 m2 a x,
    join m1 (sig a (true, x)) m2 ->
    m1 = del m2 a.
Proof.
  intros.
  eapply join_true_del; eauto 1.
  unfold isRw.
  simpl.
  auto.
Qed.  

Lemma mem_join_set_true_comm :
  forall (m1:mem) m2 m3 a x,
    get m1 a = None ->
    get m2 a = None ->
    join (set m1 a (true, x)) m2 m3 ->
    join m1 (set m2 a (true, x)) m3.
Proof.
  intros.
  eapply join_set_true_comm; eauto.
Qed.

Lemma mem_sig_set :
  forall (m:mem) a x,
    get m a = None ->
    join m (sig a x) (set m a x).
Proof.
  intros.
  eapply sig_set; eauto.
Qed.


(*hard*)
Lemma mem_join_set_l_rev :
  forall (m1:mem) m2 m (m':mem) a b,
    join (set m1 a (true, b)) m2 m ->
    exists m', join m1 m2 m' /\ m = set m' a (true, b).
Proof.
  intros.
  eapply mem_join_set_l_rev'; eauto.
Qed.

Lemma mem_del_get :
  forall (m:mem) a,
    get (del m a) a = None.
Proof.
  intros.
  eapply del_get; eauto.
Qed.

(*hard*)
Lemma mem_join_merge_merge :
  forall (m1:mem) m2 m12 m3 m123 m4 m1234,
    join m1 m2 m12 ->
    join m12 m3 m123 ->
    join m123 m4 m1234 ->
    join (merge (merge m1 m2) m3) m4 m1234.
Proof.
  intros.
  eapply join_merge_merge; eauto.
Qed.

(*very hard*)
(*the following 3 lemmas are complex and duplicated in some sense,
  please start proving after reading them all*)
Lemma mem_merge_assoc2:
  forall (m1:mem) m2 m12 m3 m123 m4 m1234 m5 mx,
    join m1 m2 m12 ->
    join m12 m3 m123 ->
    join m123 m4 m1234 ->
    join m5 (merge (merge m1 m2 ) m4) mx ->
    join m4 (merge (merge m5 m1) m2) mx.
Proof.
  intros.
  eapply merge_assoc2; eauto.
Qed.

(*very hard*)
Lemma mem_merge_join :
  forall (m1:mem) m2 m12 m3 m123 m4 m1234 m5 mx,
    join m1 m2 m12 ->
    join m12 m3 m123 ->
    join m123 m4 m1234 ->
    join m5 (merge (merge m1 m2 ) m4) mx ->
    join (merge m5 m1) m2 (merge (merge m5 m1) m2).
Proof.
  intros.
  eapply merge_join; eauto.
Qed.

(*very hard*)
Lemma join_merge_disjoint :
  forall (m1:mem) m2 m12 m3 m123 m4 m1234 m5 mx,
    join m1 m2 m12 ->
    join m12 m3 m123 ->
    join m123 m4 m1234 ->
    join m5 (merge (merge m1 m2 ) m4) mx ->
    disjoint m1 m5.
Proof.
  intros.
  eapply merge_disjoint; eauto.
Qed.

Lemma join_merge23 :
  forall {A B T:Type} {MC:PermMap A B T} m1 m2 m12 m3 m123,
    join m1 m2 m12 ->
    join m12 m3 m123 ->
    join m1 (merge m2 m3) m123.
Proof.
  intros.
  eapply join_merge23'; eauto.
Qed.

Lemma join_merge_merge1 :
  forall {A B T:Type} {MC:PermMap A B T} m1 m2 m12 m3 m4 m34 m5,
    join m1 m2 m12 ->
    join m3 m4 m34 ->
    join m12 m34 m5 ->
    join m3 (merge m1 m4) (merge m1 m34).
Proof.
  intros.
  eapply join_merge_merge1'; eauto.
Qed.

   
Lemma join_join_merge :
  forall {A B T:Type} {MC:PermMap A B T} m1 m2 m12 m3 m123,
    join m1 m2 m12 ->
    join m12 m3 m123 ->
    join m2 m3 (merge m2 m3).
Proof.
  intros.
  eapply join_join_merge'; eauto.
Qed.

Lemma mem_join3_merge_merge_join :
  forall (m1:mem) m2 m12 m3 m123 m4 m1234,
    join m1 m2 m12 ->
    join m12 m3 m123 ->
    join m123 m4 m1234 ->
    join m1 (merge m2 m4) (merge m12 m4).
Proof.
  intros.
  eapply join3_merge_merge_join; eauto.
Qed.

Lemma osabst_join3_merge_merge_join :
  forall (m1:osabst) m2 m12 m3 m123 m4 m1234,
    join m1 m2 m12 ->
    join m12 m3 m123 ->
    join m123 m4 m1234 ->
    join m1 (merge m2 m4) (merge m12 m4).
Proof.
  intros.
  eapply osabst_join3_merge_merge_join'; eauto.
Qed.

Lemma mem_join_del :
  forall (m1:mem) m2 m3 a x,
    join m1 m2 m3 ->
    get m1 a = Some (true, x) ->
    join (del m1 a) m2 (del m3 a).
Proof.
  intros.
  eapply mem_join_del'; eauto.
Qed.

Lemma mem_get_set_merge_eq :
  forall (m1:mem) m2 a x x',
    get m1 a = Some (true, x) ->
    merge (set m1 a (true, x')) m2 = set (merge m1 m2) a (true, x').
Proof.
  intros.
  eapply mem_get_set_merge_eq'; eauto.
Qed.

Lemma mem_disjoint_get_true_set_disjoint :
  forall m1 m2 a x x',
    disjoint m1 m2 ->
    get m1 a = Some (true, x) ->
    disjoint (set m1 a (true, x')) m2.
Proof.
  intros.
  eapply mem_disjoint_get_true_set_disjoint'; eauto.
  unfold isRw.
  simpl.
  auto.
Qed.

Lemma mem_disjoint_sub_disjoint_merge :
  forall (m1:mem) m2 mx,
    disjoint m1 m2 ->
    Maps.sub mx m1 ->
    disjoint (minus m1 mx) (merge mx m2).
Proof.
  intros.
  eapply mem_disjoint_sub_disjoint_merge'; eauto.
Qed.

Lemma mem_disjoint_disjoint_merge_disjoint :
  forall (m1:mem) m2 m3,
    disjoint m2 m3 ->
    disjoint m1 (merge m2 m3) ->
    disjoint m1 m3.
Proof.
  intros.
  eapply mem_disjoint_disjoint_merge_disjoint'; eauto.
Qed.

Lemma mem_sub_get_true_sub_set :
  forall (m1:mem) m2 a x x',
    Maps.sub m1 m2 ->
    get m1 a = Some (true, x) ->
    Maps.sub (set m1 a (true, x')) (set m2 a (true, x')).
Proof.
  intros.
  eapply mem_sub_get_true_sub_set'; eauto.
  unfold isRw; simpl; auto.
Qed.  



Lemma mem_disjoint_merge_minus_get_true_set :
  forall (m1:mem) m2 m3 m4 a x x',
    get m2 a = Some (true, x) ->
    Maps.sub m2 m1 ->
    disjoint (merge (minus (set m1 a (true, x')) (set m2 a (true, x'))) m3) m4 ->
    disjoint (merge (minus m1 m2) m3) m4.
Proof.
  intros.
  eapply mem_disjoint_merge_minus_get_true_set'; ica.
Qed.

Lemma mem_disjoint_merge_eq_merge_merge :
  forall (m1:mem) m2 m3 m4 mx,
    disjoint m1 m2 ->
    disjoint m3 m4 ->
    merge m1 m2 = merge m3 m4 ->
    disjoint mx (merge m3 m4) ->
    merge (merge mx m1) m2 = merge (merge mx m3) m4.
Proof.
  intros.
  eapply mem_disjoint_merge_eq_merge_merge'; ica.
Qed.  

Lemma mem_sub_disjoint :
  forall (m1:mem) m2 m3,
    Maps.sub m1 m2 ->
    disjoint m2 m3 ->
    disjoint m1 m3.
Proof.
  intros.
  eapply mem_sub_disjoint'; ica.
Qed.  

Lemma mem_merge_merge_minus_get_true_set_eq :
  forall (m1:mem) m2 m3 m4 m5 a x x',
    Maps.sub m2 m1 ->
    get m2 a = Some (true, x) ->
    merge (merge (minus (set m1 a (true, x')) (set m2 a (true, x'))) m3) m4 = m5 ->
    merge (merge (minus m1 m2) m3) m4 = m5.
Proof.
  intros.
  eapply mem_merge_merge_minus_get_true_set_eq'; ica.
Qed.  

Lemma mem_del_get_neq :
  forall (m:mem) a a',
    a <> a' ->
    get (del m a') a = get m a.
Proof.
  intros.
  eapply mem_del_get_neq'; ica.
Qed.  

Lemma mem_join_set_true_join :
  forall (m1:mem) m2 m3 a x x',
    join m1 m2 m3 ->
    get m1 a = Some (true, x) ->
    join (set m1 a (true, x')) m2 (set m3 a (true, x')).
Proof.
  intros.
  eapply mem_join_set_true_join'; ica.
Qed.  

Lemma mem_join_join_merge13_join :
  forall (m1:mem) m2 m12 m3 m123,
    join m1 m2 m12 ->
    join m12 m3 m123 ->
    join (merge m1 m3) m2 m123.
Proof.
  intros.
  eapply mem_join_join_merge13_join'; ica.
Qed.  

Lemma mem_join_join_merge :
  forall (m1:mem) m2 m12 m3 m123,
    join m1 m2 m12 ->
    join m12 m3 m123 ->
    join m1 m3 (merge m1 m3).
Proof.
  intros.
  eapply mem_join_join_merge'; ica.
Qed.  

Lemma mem_disjoint_set_l :
  forall (m1:mem) m2 a x x',
    disjoint m1 m2 ->
    get m1 a = Some (true, x) ->
    disjoint (set m1 a (true, x')) m2.
Proof.
  intros.
  eapply mem_disjoint_set_l'; ica.
Qed.  

Lemma mem_disjoint_disjoint_sub_disjoint_merge :
  forall (m1:mem) m2 mx,
    disjoint m1 m2 ->
    Maps.sub mx m1 ->
    disjoint (minus m1 mx) (merge mx m2).
Proof.
  intros.
  eapply mem_disjoint_disjoint_sub_disjoint_merge'; ica.
Qed.  

Lemma mem_merge_merge_minus_merge :
  forall (m1:mem) m2 m3,
    Maps.sub m1 m2 ->
    disjoint m2 m3 ->
    merge (merge (minus m2 m1) m1) m3 = merge m2 m3.
Proof.
  intros.
  eapply mem_merge_merge_minus_merge'; ica.
Qed.  

Lemma mem_sub_get_true_set_sub :
  forall (m1:mem) m2 a x x',
    Maps.sub m1 m2 ->
    get m1 a = Some (true, x) ->
    Maps.sub (set m1 a (true, x')) (set m2 a (true, x')).
Proof.
  intros.
  eapply mem_sub_get_true_set_sub'; ica.
Qed.  

Lemma mem_sub_disjoint_sub_merge_merge :
  forall (m1:mem) m2 m3,
    Maps.sub m1 m2 ->
    disjoint m2 m3 ->
    Maps.sub (merge m1 m3) (merge m2 m3).
Proof.
  intros.
  eapply mem_sub_disjoint_sub_merge_merge'; ica.
Qed.  

Lemma mem_join_join_disjoint_join_merge :
  forall (m1:mem) m2 m3 m4 mx,
    join m1 mx m2 ->
    join m1 m3 m4 ->
    disjoint m4 mx ->
    join m2 m3 (merge m4 mx).
Proof.
  intros.
  eapply mem_join_join_disjoint_join_merge'; ica.
Qed.

Lemma mem_minus_set_comm :
  forall (M1:mem) M2 l v,
    ~ indom M2 l->
    minus (set M1 l v) M2 = set (minus M1 M2) l v.
Proof.
  intros.
  eapply mem_minus_set_comm'; ica.
Qed.  

Lemma mem_join_minus_get :
  forall (m1:mem) m2 m3 a,
    join m1 m2 m3 ->
    get (minus m3 m2) a = get m1 a.
Proof.
  intros.
  eapply mem_join_minus_get'; ica.
Qed.  

Lemma mem_get_minus_get :
  forall (m1:mem) m2 a x,
    get m1 a = Some x ->
    get m2 a = None ->
    get (minus m1 m2) a = Some x.
Proof.
  intros.
  eapply mem_get_minus_get'; ica.
Qed.  

Lemma mem_join_minus_join_r :
  forall (M:mem) m1 m2 m3 m4,
    Maps.sub m3 M ->
    join m1 m2 (minus M m3) ->
    join m2 m3 m4 ->
    join m1 m4 M.
Proof.
  intros.
  eapply mem_join_minus_join_r'; ica.
Qed.  

Lemma mem_join_minus_r :
  forall (m1:mem) m2 m3 m4,
    join m1 m2 (minus m3 m4) ->
    exists mx, join m2 m4 mx.
Proof.
  intros.
  eapply mem_join_minus_r'; ica.
Qed.  

Lemma mem_sub_del :
  forall (m1:mem) m2 a,
    Maps.sub m1 m2 ->
    Maps.sub (del m1 a) m2.
Proof.
  intros.
  eapply mem_sub_del'; ica.
Qed.  

Lemma mem_get_del_none :
  forall (m:mem) a,
    get (del m a) a = None.
Proof.
  intros.
  eapply mem_get_del_none'; ica.
Qed.  

Lemma mem_get_del_get_eq :
  forall (m:mem) a1 a2,
    a2 <> a1 ->
    get (del m a2) a1 = get m a1.
Proof.
  intros.
  eapply mem_get_del_get_eq'; ica.
Qed.  

Lemma mem_sub_disj:
  forall (M:mem) M1 M2,
    disjoint M1 M2 -> Maps.sub M M1 -> disjoint M M2.
Proof.
  intros.
  eapply mem_sub_disj'; ica.
Qed.  
