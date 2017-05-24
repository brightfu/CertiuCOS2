(** place auxiliary lemmas of MapClass, please add lemmas to the end of file **)
(** please comment your unfinished lemma, because this file will be Export by base_tac.v **)

Require Import join_tactics.
Require Import LibTactics.

Import veg.
Set Implicit Arguments.
Unset Strict Implicit.

(**Lib for  maps added by ming*)
Lemma abst_get_set_disj:
  forall  (A B T : Type) (MC: PermMap A B T)   O id Of x y,
    usePerm = false ->
    get O id = Some x -> 
    disjoint O Of -> 
    disjoint (set O id y) Of.
Proof.
  intros.
  unfold disjoint in *.
  simp join.
  exists (set x0 id y).
  eapply map_join_set_none; eauto.
  eapply map_join_get_no_perm1; eauto.
Qed.


Lemma join_sig_get_disj:
  forall  (A B T : Type) (MC: PermMap A B T)  O O' x y,
    usePerm = false ->
    join (sig x y) O O'-> 
    get O' x = Some y /\ get O x = None/\ Maps.sub O O'.
Proof.
  intros.
  split.
  eapply map_join_get_no_perm2; eauto.
  apply map_get_sig.
  split.
  eapply map_join_get_no_perm1; eauto.
  apply map_get_sig.
  unfold sub.
  eexists.
  apply map_join_comm.
  eauto.
Qed.


Lemma sub_get_get :
  forall  (A B T : Type) (MC: PermMap A B T)  O O' x y,
    usePerm = false ->
    Maps.sub O O' ->
    get O x =  Some y ->
    get O' x = Some y.
Proof.
  intros.
  unfold sub in H0.
  destruct H0.
  eapply  map_join_get_no_perm2; eauto.
Qed.


Lemma sig_set_emp :
  forall  (A B T : Type) (MC: PermMap A B T)  x y ,
    sig x y  = set emp x y.
Proof.
  intros.
  apply eq_sym.
  apply map_set_emp.
Qed.


Lemma sig_set_sig :
  forall  (A B T : Type) (MC: PermMap A B T)  x y y',
    sig x y  = set (sig x y')  x y.
Proof.
  intros.
  apply eq_sym.
  apply map_set_sig.
Qed.

Lemma get_set_neq :
   forall  (A B T : Type) (MC: PermMap A B T)   O x x' y y',
     x <> x' ->
     get O x =  y ->
     get (set O x' y') x =  y.
Proof.
  intros.
  rewrite map_get_set'; auto.
Qed.


Lemma  disj_get_merge_get :
  forall  (A B T : Type) (MC: PermMap A B T)   O O' x y,
    usePerm = false ->
    disjoint O O' ->
    get O x  = Some y ->
    get  (merge O O') x = Some y.
Proof.
  intros.
  unfold disjoint in H0.
  apply map_join_merge in H0.
  eapply map_join_get_no_perm2; eauto.
Qed.

Lemma join_set_set :
forall  (A B T : Type) (MC: PermMap A B T)   O O' O'' id x y,
  usePerm = false ->
  join O O' O'' -> 
  get O id = Some x  ->
  join (set O id y) O'  (set O'' id y).
Proof.
  intros.
  eapply map_join_set_none; eauto.
  eapply map_join_get_no_perm1; eauto.
Qed.

Lemma get_join_sig_set:
forall  (A B T : Type) (MC: PermMap A B T)   qls qid a,  
  get qls qid = None ->
  join (sig qid a) qls (set qls qid a).
Proof.
  intros.
  assert (sig qid a = set emp qid a).
  apply eq_sym.
  apply map_set_emp.
  rewrite H0.
  eapply map_join_set_none; eauto.
  geat.
Qed.


Lemma get_set_eq :
  forall  (A B T : Type) (MC: PermMap A B T)   O x  y,
    get (set O x y)  x = Some y.
Proof.
  intros.
  apply map_get_set.
Qed.

Lemma  join_merge_set_eq:
  forall (A B T : Type) (MC: PermMap A B T)   O Of x id  y O',
    usePerm = false ->
    join  O Of O' ->
    get O id = Some x ->
    merge (set O id y)  Of = set (merge O Of) id y.
Proof.
  intros.
  assert (join (set O id y) Of  (set O' id y)).
  eapply join_set_set; eauto.
  apply map_join_merge' in H2.
  apply map_join_merge' in H0.
  subst O'.
  auto.
Qed.


Lemma disjoint_merge_sym :
  forall  (A B T : Type) (MC: PermMap A B T)  O O',
    disjoint O O' ->
    merge O  O'  = merge O' O.
Proof.
  intros.
  eapply map_merge_comm.
  eauto.
Qed.

Lemma disjoint_sym:
  forall  (A B T : Type) (MC: PermMap A B T)  O O',
    disjoint O O' ->
    disjoint O' O.
Proof.
  intros.
  unfold disjoint in *.
  destruct H.
  exists x.
  apply map_join_comm.
  auto.
Qed.

Lemma join_sig_set: 
  forall  (A B T : Type) (MC: PermMap A B T)   id a O1 O b, 
    usePerm = false ->
    join (sig id a) O1 O -> join (sig id b) O1 (set O id b).
Proof.
  intros.
  assert (set (sig id a)  id b  =  sig id b).
  apply map_set_sig.
  rewrite <- H1.
  eapply join_set_set; eauto.
  jeauto2.
Qed.

Lemma get_join_sig_set_rev:
  forall  (A B T : Type) (MC: PermMap A B T)  x  qls qid qls',  
    usePerm = false ->
    joinsig qid x qls qls' -> 
    qls'= (set qls qid x).
Proof.
  intros.
  unfold joinsig in H0.
  assert (join (sig qid x) qls (set qls qid x)).
  assert (set emp qid x  = sig qid x).
  apply map_set_emp.
  rewrite <- H1.
  eapply map_join_set_none; eauto.
  geat.
  eapply map_join_get_no_perm1; eauto.
  jeauto2.
  eapply map_join_deter; eauto.
Qed.


Lemma disjoint_emp_r:
  forall {A B T:Type} {MC:PermMap A B T} x,
    disjoint emp x .
Proof.
  intros.
  unfold disjoint.
  exists x.
  eapply map_join_comm.
  eapply map_join_emp.
Qed.

Lemma disjoint_emp_l:
  forall {A B T:Type} {MC:PermMap A B T} x,
    disjoint  x emp .
Proof.
  intros.
  unfold join.
  exists x.
  eapply map_join_emp.
Qed.

(*
Lemma minus_disj :
	 forall  (A B T : Type) (MC: PermMap A B T)  M m,
  	 disjoint  (minus M m) m.
Proof. 
  (*
  introv.
  unfolds.t
  rewrite  HalfPermMap.minus_sem.
  remember (MemMod.get M a ) as Hm1.
  remember (MemMod.get m a ) as Hm2.
  destruct Hm1;destruct Hm2; auto.
  Qed.*)
(* Admitted. *)
*)

Lemma get_joinsig_rw:
  forall  (A B T : Type) (MC: PermMap A B T)  v x y,
    usePerm = false ->
    get v x = None -> 
    joinsig x y v (set v x y).
Proof.
  intros.
  unfold joinsig.
  assert (set emp x y  = sig x y).
  apply map_set_emp.
  rewrite <- H1.
  eapply map_join_set_none; eauto.
  geat.
Qed.

(*Lemma join_minus_r : 
  forall  (A B T : Type) (MC: PermMap A B T)  m1 m2 m3 M,
    join m1 m2 (minus M m3) ->
    exists mx, join m2 m3 mx.
Proof.
  (*
  introv Hjm.
  cut (HalfPermMap.disjoint m2 m3).
  introv Hdisj.
  apply join_merge_disj in Hdisj.
  eexists; eauto.
  apply join_disj_meq in Hjm. 
  destruct Hjm.
  apply MemMod.meq_eq in H0.
  assert (HalfPermMap.disjoint (HalfPermMap.minus M m3) m3) by apply Mem_minus_disj.
  rewrite <- H0 in H1.
  apply HalfPermMap.disjoint_merge_elim_l in H1. 
  destruct H1; auto.
  Qed.*)
(* Admitted. *)
*)

Lemma join_in_r : 
  forall  (A B T : Type) (MC: PermMap A B T)  ma mb mab x, 
  join ma mb mab -> indom mb x -> indom mab x.
Proof.
  intros.
  apply map_join_comm in H.
  unfold indom in *.
  simp join.
  assert (exists b, usePerm = b).
  eauto.
  destruct H1.
  destruct x1.
  assert (exists y , get ma x  = y) by eauto.
  destruct H2.
  destruct x1.
  eexists.
  eapply map_join_getp_some;eauto.
  eexists.
  apply map_join_comm in H.
  erewrite <- H0.
  eapply map_join_get_none; eauto.
  eexists.
  eapply map_join_get_no_perm; eauto.
Qed.

Lemma join_in_or :
  forall  (A B T : Type) (MC: PermMap A B T)  ma mb mab x, 
    join ma mb mab ->  indom mab x -> indom ma x \/  indom mb x.
Proof.
  intros.
  unfold indom in H0.
  destruct H0.
  assert (exists b, usePerm = b) by eauto.
  destruct H1.
  destruct x1.
  assert (exists yy, get ma x = yy) by eauto.
  destruct H2.
  destruct x1.
  left; eauto.
  unfold indom.
  eauto.
  right.
  unfold indom.
  eexists.
  rewrite <- H0.
  apply eq_sym.
  eapply map_join_get_none'; jeauto2.
  assert (exists yy, get ma x = yy) by eauto.
  destruct H2.
  destruct x1.
  left; eauto.
  unfold indom.
  eauto.
  right.
  unfold indom.
  eexists.
  rewrite <- H0.
  apply eq_sym.
  eapply map_join_get_none'; jeauto2.
Qed.

Lemma  get_or : 
forall  (A B T : Type) (MC: PermMap A B T)   ma a, 
   get ma a = None \/ exists b,  get ma a = Some b.
Proof.
  intros.
  assert (exists b, get ma a =  b) by eauto.
  destruct H.
  destruct x.
  right; eauto.
  left; eauto.
Qed.

(*
Lemma indom_join_eq:
 forall (A B T : Type) (MC: PermMap A B T)  ma mb ma' mb' mab,
 (forall a,  indom ma a <->  indom ma' a) -> 
  join ma mb mab ->
 join ma' mb' mab -> ma = ma'.
Proof.
  intros.
  unfold indom in *.
  eapply map_join_cancel.
  apply map_join_comm.
  eauto.
  apply map_join_comm.
  
(* ** ac: SearchAbout join. *)
  apply 
  assert (ma = ma' \/ ma <> ma') by tauto.
(* Admitted. *)
*)

Lemma  neq_set_get:
  forall (A B T : Type) (MC: PermMap A B T) x y b tcbls,
    x <> y ->
     get (set tcbls y b) x =  get tcbls x.
Proof.
  intros.
  jeauto2.
Qed.

Lemma  get_join:
  forall (A B T : Type) (MC: PermMap A B T) tcs ptcb m,
    get tcs ptcb = Some m->
    exists tcs',
       join (sig ptcb m) tcs' tcs.
Proof.
  intros.
  jeauto2.
Qed.


Lemma join_merge : 
	forall (A B T : Type) (MC: PermMap A B T) {m1 m2 m3}, 
 	join m1 m2 m3 -> m3 = merge m1 m2.
Proof.
  intros.
  apply map_join_merge'; auto.
Qed.

Lemma disj_join_disj : 
	forall   (A B T : Type) (MC: PermMap A B T)  {m1 m2 m3 m4 m5 m6},
  join m1 m2 m3 ->
  	 join m4 m5 m6 ->
    	 disjoint m3 m6 ->
  		disjoint m1 m4.
Proof.
  intros.
  unfold disjoint in *.
  geat.
Qed.


Lemma join_disj : 
	forall   (A B T : Type) (MC: PermMap A B T)  M1 M2 M,
 	 join M1 M2 M -> 
 	disjoint M1 M2.
Proof.
  intros.
  unfold disjoint.
  geat.
Qed.

Lemma join_sub_sub_sig_neq:
  forall 
  	  (A B T : Type) (MC: PermMap A B T) 	
    x1 x2 m a b m1 m2,
    usePerm = false ->
    join x1 x2 m ->
    sub (sig a m1) x1 ->
    sub (sig b m2) x2 ->
    a <> b.
Proof.
  intros.
  unfold sub in *.
  simp join.
  intro Hf.
  subst.
  assert (get x2 b = Some m2)  by jeauto2.
  assert (get x1 b = Some m1) by jeauto2.
  clear - H0 H3 H4 H.
  eapply map_join_get_some; eauto.
Qed.

Lemma map_join_getp_one:
  forall (A B T : Type) (MC: PermMap A B T)
    t v x y z,
    usePerm = true ->
    join x y z ->
    get x t = Some v ->
    (get y t = None /\ get z t = Some v) \/
    (isRw v = false /\ get y t = Some v /\ get z t = Some (flip v)).
Proof.
  intros.
  destruct (get y t) eqn:Hy.
  rename H1 into Hx.
  assert (v = b /\ isRw v = false /\ get z t = Some (flip v)) by jeauto2.
  right. 
  intuition.
  subst; auto.
  assert (get z t = get x t) by jeauto2.
  rewrite H1 in *.
  left.
  auto.
Qed.

Hint Resolve @map_emp_get @map_eql : jdb1.

Ltac eat_false :=
  match goal with
    | H: ?a = ?b |- _ =>
      try subst; solve [inversion H]
    | H: ?a <> ?b |- _ =>
      try subst; solve [clear -H; tauto]
    | H: False |- _ =>
      inversion H
    | _ => idtac
  end.

Ltac instant H x :=
  generalize (H x); clear H; intro H.

Lemma map_emp_get':
  forall (A B T : Type) (MC: PermMap A B T) x,
    (forall t, get x t = None) ->
    x = emp.
Proof.
  intros.
  generalize (@map_emp_get _ _ _ MC); intro.
  eapply map_eql.
  intros.
  instant H t.
  instant H0 t.
  rewrite H.
  rewrite H0.
  auto.
Qed.  

Hint Resolve @map_emp_get' : jdb1.

Lemma map_join_getp_sig:
  forall (A B T : Type) (MC: PermMap A B T)
    t v1 v2 z,
    usePerm = true ->
    join (sig t v1) (sig t v2) z ->
    v1 = v2 /\ isRw v1 = false /\ get z t = Some (flip v1).
Proof.
  intros.
  assert (Hx: (get (sig t v1) t = Some v1)) by jeauto2.
  assert (Hy: (get (sig t v2) t = Some v2)) by jeauto2.
  jeauto2.
Qed.

Lemma map_join_sig_mergep:
  forall (A B T : Type) (MC: PermMap A B T)
    t v z,
    usePerm = true ->
    isRw v = false ->
    join (sig t v) (sig t v) z ->
    z = sig t (flip v).
Proof.
  intros.
  eapply map_eql.
  intro t'.
  destruct (map_dec_a t t').
  subst.
  generalize (@map_join_getp_sig _ _ _ _ _ _ _ _ H H1); intro.
  heat.
  clear H2 H3.
  rewrite H4.
  rewrite map_get_sig.
  trivial.
  rewrite map_get_sig'.
  assert (get (sig t v) t' = None) by jeauto2.
  assert (get z t' = get (sig t v) t').
    eapply map_join_get_none; eauto.
  rewrite map_get_sig' in H3.
  auto.
  auto.
  auto.
Qed.  

Hint Resolve @map_join_sig_mergep : jdb1.

Lemma map_sig_disjointp:
  forall (A B T : Type) (MC: PermMap A B T)
    t v,
    usePerm = true ->
    isRw v = false ->
    exists z, join (sig t v) (sig t v) z.
Proof.
  intros.
  apply map_disjoint.
  intros.
  destruct (map_dec_a t t0); subst.
  right; right.
  exists v.
  swallow; jeauto2.
  left.
  jeauto2.
Qed.  

Hint Resolve map_sig_disjointp : jdb1.

Lemma map_join_sig_mergep':
  forall (A B T : Type) (MC : PermMap A B T)
    t v,
    usePerm = true ->
    isRw v = false ->
    join (sig t v) (sig t v) (sig t (flip v)).
Proof.
  intros.
  generalize (@map_sig_disjointp _ _ _ _ t v H H0); intro.
  destruct H1.
  assert (x = sig t (flip v)).
    eapply map_join_sig_mergep; auto.
  subst.
  auto.
Qed.  

Hint Resolve map_join_sig_mergep' : jdb1.

Open Scope list_scope.

Lemma jl_perm_sig_merge1:
  forall (A B T : Type) (MC: PermMap A B T)
    t v1 v2 z,
    usePerm = true ->
    join_list ((sig t v1)::(sig t v2)::nil) z ->
    v1 = v2 /\ isRw v1 = false /\ get z t = Some (flip v1).
Proof.
  intros.
  cook.
  assert (join (sig t v1) (sig t v2) z) by jeauto2.
  eapply map_join_getp_sig; eauto.
Qed.  

Lemma jl_perm_sig_merge2:
  forall (A B T : Type) (MC: PermMap A B T)
    t v1 v2 z,
    usePerm = true ->
    join_list ((sig t v1)::(sig t v2)::nil) z ->
    v1 = v2 /\ isRw v1 = false /\ join_list ((sig t (flip v1))::nil) z.
Proof.
  intros.
  generalize (jl_perm_sig_merge1 H H0); intro.
  heat.
  swallow; auto.
  generalize (@map_join_sig_mergep' _ _ _ _ t v2 H H2); intro.
  apply jl_list_to_op in H0.
  assert (sig t (flip v2) = z) by jeauto2.
  subst.
  jeauto2.
Qed.


Lemma jl_perm_merge:
  forall (A B T : Type) (MC: PermMap A B T)
    t a b l' m,
    usePerm = true ->
    join_list ((sig t a)::(sig t b)::l') m ->
    a = b /\ isRw a = false /\ join_list ((sig t (flip a))::l') m.
Proof.
  intros.
  assert (tmp: (sig t a :: sig t b :: l') = (sig t a :: sig t b :: nil) ++ l') by auto.
  rewrite tmp in H0; clear tmp.
  apply jl_split in H0.
  heat.
  generalize (@jl_perm_sig_merge2 _ _ _ _ _ _ _ _ H H0); intro.
  heat.
  swallow; auto.
  assert (join_list ((sig t (flip b) :: nil) ++ l') m) by jeauto2.
  simpl in H3.
  auto.
Qed.  
  
Lemma join_sig_eq_p :
  forall  (A B T : Type) (MC: PermMap A B T) 	
          l a b m1 m2 m3 x1 x2,
    usePerm = true ->
    isRw a = false ->
    isRw b = false ->
    join (sig l a) x1 m1 ->
    join (sig l b) x2 m2 ->
    join m1 m2 m3 ->
    a = b.
Proof.
  intros.
  geat.
  liftH H4 (sig l b).
  generalize (@jl_perm_merge _ _ _ _ _ _ _ _ _ H H4); intro.
  heat.
  auto.
Qed.

Hint Resolve join_sig_eq_p : jdb1.

Lemma map_flip_true:
  forall (A B T : Type) (MC : PermMap A B T) v v',
    usePerm = true ->
    isRw v = true ->
    v' = flip v ->
    isRw v' = false.
Proof.
  intros.
  assert (isRw (flip v) = negb (isRw v)).
    apply map_flip_isRw; auto.  
  rewrite H0 in H2.
  simpl in H2.
  subst.
  auto.
Qed.

Hint Resolve map_flip_true : jdb1.

Lemma map_flip_false:
  forall (A B T : Type) (MC : PermMap A B T) v v',
    usePerm = true ->
    isRw v = false ->
    v' = flip v ->
    isRw (flip v) = true.
Proof.
  intros.
  assert (isRw (flip v) = negb (isRw v)).
    apply map_flip_isRw; auto.  
  rewrite H0 in H2.
  simpl in H2.
  subst.
  auto.
Qed.

Hint Resolve @map_flip_true @map_flip_false : jdb1.

Lemma map_join_sig_mergep'':
  forall (A B T : Type) (MC : PermMap A B T)
    t v a b,
    usePerm = true ->
    isRw v = false ->
    a = sig t v ->
    b = sig t (flip v) ->
    join a a b.
Proof.
  intros.
  generalize (@map_join_sig_mergep' _ _ _ _ t v H H0); intro.
  subst.
  auto.
Qed.

Lemma map_flip_sv':
  forall (A B T : Type) (MC : PermMap A B T) v v',
    usePerm = true ->
    v' = flip v ->
    sameV v v'.
Proof.
  intros.
  assert (sameV v (flip v)).
    apply map_flip_sv; auto.
  subst.
  auto.
Qed.

Hint Resolve @map_flip_sv' : jdb1.
Hint Resolve @map_sv_comm @map_sv_ref @map_sv_assoc: jdb1.
Hint Resolve @map_flip_isRw @map_flip_sv : jdb1.

Lemma map_flip_inv:
  forall (A B T : Type) (MC : PermMap A B T) v,
    usePerm = true ->
    (flip (flip v)) = v.
Proof.
  intros.
  assert (sameV v (flip v)) by jeauto2.
  assert (sameV (flip v) (flip (flip v))) by jeauto2.
  assert (isRw (flip v) = negb (isRw v)) by jeauto2.
  assert (isRw (flip (flip v)) = negb (isRw (flip v))) by jeauto2.
  rewrite H2 in H3.
  rewrite Bool.negb_involutive in H3.
  apply map_perm_eql.
  auto.
  jeauto.
  jeauto.
Qed.

Hint Resolve @map_flip_inv : jdb1.

Lemma join_sig_false_true :
  forall  (A B T : Type) (MC: PermMap A B T)  l a b,
    usePerm = true ->
    isRw b = true ->
    a = flip b -> 
    join (sig l a) (sig l a) (sig l b).
Proof.
  intros.
  assert (isRw a = false) by jeauto2.
  clear H0.
  eapply map_join_sig_mergep''; auto.
  auto.
  rewrite H1.
  rewrite map_flip_inv.
  auto.
  auto.
Qed.  

Lemma join_split :
  forall  (A B T : Type) (MC: PermMap A B T) 
     m1 m2 m m11 m12 m21 m22,
    join m1 m2 m ->
    join m11 m12 m1 ->
    join m21 m22 m2 ->
    exists mx1 mx2, join m11 m21 mx1 /\ join m12 m22 mx2 /\ join mx1 mx2 m.
Proof.
  intros.
  geat.
Qed.  

(** from MapLib **)

Definition dec {A B T: Type} {MC: PermMap A B T} x y :=
  map_dec_a x y.

Lemma get_dec:
  forall (A B T : Type) (MC : PermMap A B T) m a,
    {exists b, get m a = Some b} + {get m a = None}.
Proof.
  intros.
  destruct (get m a).
  left.
  exists b.
  trivial.
  right; trivial.
Qed.  

Lemma emp_sem:
  forall (A B T : Type) (MC : PermMap A B T) a,
    get emp a = None.
Proof.
  intros; geat.
Qed.      

Lemma sig_sem:
  forall (A B T : Type) (MC : PermMap A B T)
    a a' b,
    get (sig a b) a' =
    if (dec a a') then Some b else None.
Proof.
  intros.
  destruct (dec a a').
  subst.
  geat.
  geat.
Qed.

Lemma set_sem_old:
  forall (A B T : Type) (MC : PermMap A B T) m a a' b, 
    if (dec a a')
    then get (set m a b) a = Some b
    else get (set m a b) a' = get m a'.
Proof.
  intros.
  destruct (dec a a').
  geat.
  geat.
Qed.  

Lemma set_sem:
  forall (A B T : Type) (MC : PermMap A B T) m a a' b,
    get (set m a b) a' =
    if (dec a a')
    then Some b
    else get m a'.
Proof.
  intros.
  destruct (dec a a').
  geat.
  geat.
Qed.  

Lemma extensionality:
  forall (A B T : Type) (MC : PermMap A B T) m1 m2, 
    (forall a, get m1 a = get m2 a) -> m1 = m2.
Proof.
  intros.
  geat.
Qed.  

Lemma get_set_same:
  forall (A B T : Type) (MC : PermMap A B T) m a b,
    get m a = Some b ->
    set m a b = m.
Proof.
  intros.
  apply map_eql.
  intros.
  destruct (dec t a).
  subst.
  rewrite H.
  jeauto2.
  jeauto2.
Qed.  

(******************************************************************************)
(** complete tactics **)
(** flip lemma **)

Lemma map_flip_eql:
  forall (A B T : Type) (MC : PermMap A B T) b,
    usePerm = true ->
    b = (flip (flip b)).
  intros.
  eapply map_perm_eql.
  auto.
  assert (sameV (flip b) (flip (flip b))) by jeauto2.
  eapply map_sv_assoc; jeauto2.
  rewrite map_flip_isRw; jeauto2.
  rewrite map_flip_isRw; jeauto2.
  destruct (isRw b); auto.
Qed.  

Hint Resolve @map_flip_eql : jdb1.

Lemma flip_isrw1:
  forall (A B T : Type) (MC : PermMap A B T) v b b',
    usePerm = true ->
    isRw (flip v) = b ->
    b' = negb b ->
    isRw v = b'.
  intros.
  subst.
  assert (v = flip (flip v)) by jeauto2.
  rewrite H0 at 1.
  jeauto2.
Qed.

Hint Resolve @flip_isrw1 : jdb1.

Lemma flip_isrw2:
  forall (A B T : Type) (MC : PermMap A B T) v b b',
    usePerm = true ->
    isRw v = b ->
    b' = negb b ->
    isRw (flip v) = b'.
  intros.
  subst.
  jeauto2.
Qed.

Hint Resolve @flip_isrw2 : jdb1.

Lemma flip_false:
  forall (A B T : Type) (MC : PermMap A B T) b,
    usePerm = true ->
    b = flip b ->
    False.
  intros.
  destruct (isRw b) eqn:F.
  assert (isRw (flip b) = false) by jeauto2.
  tryfalse.
  assert (isRw (flip b) = true) by jeauto2.
  tryfalse.
Qed.

Hint Resolve @flip_false : jdb1.

Ltac simpl_get_set :=
  repeat match goal with
           | H: get (set ?x ?t ?v) ?t = ?b |- _ =>
             rewrite map_get_set in H
           (* | H: get (set ?x ?t ?v) ?t' = ?b |- _ => *)
           (*   rewrite map_get_set' in H; auto 1 *)
         end.

Ltac my_subst :=
  repeat match goal with
           | H: ?a = ?b |- _ =>
             first [subst a | subst b]
         end.

Ltac tryfalse_isRw :=
  repeat match goal with
    | H: isRw (flip ?v) = ?b |- _ =>
      let b' := constr:(negb b) in
      let b'' := (eval simpl in b') in 
      assert (isRw v = b'') by jeauto2;
      clear H;
      tryfalse
    | H: isRw (flip (flip ?v)) = ?b |- _ =>
      rewrite <- (map_flip_eql) in H; auto 1;
      tryfalse
  end.

Ltac destruct_isRw :=
  repeat match goal with
           | |- context [isRw ?b] =>
             let H := fresh in 
             destruct (isRw b) eqn:H; auto 1; tryfalse
         end.

Ltac invert_eql1 :=
  repeat match goal with
           | H: Some _ = Some _ |- _ =>
             inverts H
         end.

Ltac invert_eql := invert_eql1.

Ltac subst_get :=
  repeat match goal with
           | H: get ?m ?t = ?b |- _ =>
             rewrite H in *
         end.

Ltac crush1 :=
  my_subst;
  subst_get;
  simpl_get_set;
  invert_eql;
  tryfalse;
  auto 1;
  try tauto;
  destruct_isRw;
  tryfalse_isRw.

Ltac crush := crush1.

Hint Resolve @map_same @map_same' : jdb1.

(* ** ac: Check @map_same'. *)

Ltac rewrite_same :=
  repeat (match goal with
            | Hn : usePerm = true |- _ =>
              match goal with
                | H: same ?v1 ?v2 = true |- _ =>
                  generalize (@map_same _ _ _ _ _ _ Hn H);
                  clear H;
                  intro H
                | H: same ?v1 ?v2 = false |- _ =>
                  generalize (@map_same' _ _ _ _ _ _ Hn H);
                  clear H;
                  intro H
              end
          end).

Goal forall (A B T : Type) (MC : PermMap A B T) (v1 v2:B),
    usePerm = true ->
    False.
  intros.
  destruct (same v1 v2) eqn:F;
  rewrite_same.
Abort.

(******************************************************************************)
(** merge lemma and tactic **)
Lemma merge_sem :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 a,
    usePerm = false ->
    get (merge m1 m2) a 
    = match (get m1 a, get m2 a) with
        | (Some b1, Some b2) => Some b1
        | (Some b1, None) => Some b1
        | (None, Some b2) => Some b2
        | (None, None) => None
      end.
  intros.
  apply map_merge_sem.
  auto.
Qed.

Lemma merge_semp:
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 a,
    usePerm = true ->
    get (merge m1 m2) a
    = match (get m1 a, get m2 a) with
        | (Some b1, Some b2) => 
          match (same b1 b2) return (option B) with
            | true => match (isRw b1) with
                       | true => Some b1
                       | false => Some (flip b1)
                     end
            | false => Some b1
          end
        | (None, Some b2) => Some b2
        | (Some b1, None) => Some b1
        | (None, None) => None
      end.
  intros.
  apply map_merge_semp; auto.
Qed.

Lemma merge_sem1:
  forall (A B T : Type) (MC : PermMap A B T) m m1 m2 a v1,
    usePerm = false ->
    get m1 a = Some v1 ->
    m = merge m1 m2 ->
    get m a = Some v1.
  intros.
  subst.
  rewrite merge_sem; auto.
  rewrite H0.
  destruct (get m2 a); auto.
Qed.

Hint Resolve @merge_sem1 : jdb1.

Lemma merge_sem1':
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 a v1 b,
    usePerm = false ->
    get m1 a = Some v1 ->
    get m2 a = b ->
    get (merge m1 m2) a = Some v1.
  intros.
  jeauto2.
Qed.
  
Lemma merge_sem2:
  forall (A B T : Type) (MC : PermMap A B T) m m1 m2 a b,
    usePerm = false ->
    get m1 a = None ->
    get m2 a = b ->
    m = merge m1 m2 ->
    get m a = b.
  intros.
  subst.
  rewrite merge_sem; auto.
  rewrite H0.
  destruct (get m2 a); auto.
Qed.  

Lemma merge_sem3:
  forall (A B T : Type) (MC : PermMap A B T) m m1 m2 a b,
    usePerm = false ->
    get m2 a = None ->
    get m1 a = b ->
    m = merge m1 m2 ->
    get m a = b.
  intros.
  subst.
  rewrite merge_sem; auto.
  rewrite H0.
  destruct (get m1 a); auto.
Qed.  

Hint Resolve @merge_sem2 @merge_sem3 : jdb1.

Lemma merge_sem2':
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 a b,
    usePerm = false ->
    get m1 a = None ->
    get m2 a = b ->
    get (merge m1 m2) a = b.
  intros.
  jeauto2.
Qed.  
  
Lemma merge_sem3':
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 a b,
    usePerm = false ->
    get m2 a = None ->
    get m1 a = b ->
    get (merge m1 m2) a = b.
  intros.
  jeauto2.
Qed.
  
Lemma merge_semp3 :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 a b,
    usePerm = true ->
    get m1 a = None ->
    get m2 a = b ->
    get (merge m1 m2) a = b.
  intros.
  destruct (get m2 a) eqn: F1.
  rewrite merge_semp.
  subst.
  rewrite H0; rewrite F1.
  auto.
  auto.
  rewrite merge_semp.
  subst.
  rewrite H0; rewrite F1.
  auto.
  auto.
Qed.

Hint Resolve @merge_semp3 : jdb1.

Lemma merge_semp4 :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 a b,
    usePerm = true ->
    get m2 a = None ->
    get m1 a = b ->
    get (merge m1 m2) a = b.
  intros.
  destruct (get m1 a) eqn: F1.
  rewrite merge_semp.
  subst.
  rewrite H0; rewrite F1.
  auto.
  auto.
  rewrite merge_semp.
  subst.
  rewrite H0; rewrite F1.
  auto.
  auto.
Qed.

Hint Resolve @merge_semp4 : jdb1.

Lemma merge_semp1 :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 a b1 b2,
    usePerm = true ->
    get m1 a = Some b1 ->
    get m2 a = Some b2 ->
    b1 <> b2 ->
    get (merge m1 m2) a = Some b1.
  intros.
  rewrite merge_semp.
  rewrite H0.
  rewrite H1.
  destruct (same b1 b2) eqn:F; rewrite_same.
  tryfalse.
  auto.
  auto.
Qed.

Hint Resolve @merge_semp1 : jdb1.

Lemma merge_semp2 :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 a b b1 b2,
    usePerm = true ->
    get m1 a = Some b1 ->
    get m2 a = Some b2 ->
    b1 = b2 ->
    isRw b1 = false ->
    b = flip b1 ->
    get (merge m1 m2) a = Some b.
  intros.
  subst.
  rewrite merge_semp; auto.
  rewrite H1.
  rewrite H0.
  destruct (same b2 b2) eqn:Ht; rewrite_same; auto.
  rewrite H3.
  auto.
  tryfalse.
Qed.
  
Hint Resolve @merge_semp2 : jdb1.

Lemma merge_sem_none1 :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 a b,
    get m1 a = None ->
    get m2 a = b ->
    get (merge m1 m2) a = b.
  intros.
  destruct (usePerm) eqn:F.
  jeauto2.
  jeauto2.
Qed.

Lemma merge_sem_none2 :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 a b,
    get m2 a = None ->
    get m1 a = b ->
    get (merge m1 m2) a = b.
  intros.
  destruct (usePerm) eqn:F.
  jeauto2.
  jeauto2.
Qed.

Hint Resolve @merge_sem_none1 @merge_sem_none2 : jdb1.

Lemma merge_sem_none_rev :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 a,
    get (merge m1 m2) a = None ->
    (get m1 a = None /\ get m2 a = None).
  intros.
  destruct (get m1 a) eqn: F1.
  destruct (get m2 a) eqn: F2.
  destruct (usePerm) eqn:F.
  generalize H.
  rewrite merge_semp.
  rewrite F1.
  rewrite F2.
  destruct (same b b0) eqn:Ht; rewrite_same.
  destruct (isRw b).
  intros.
  tryfalse.
  intros.
  tryfalse.
  intros; tryfalse.
  auto.
  
  assert (get (merge m1 m2) a = Some b) by jeauto2.
  rewrite H in H0.
  tryfalse.

  assert (get (merge m1 m2) a = Some b) by jeauto2.
  rewrite H in H0; tryfalse.

  destruct (get m2 a) eqn: F2.
  assert (get (merge m1 m2) a = Some b) by jeauto2.
  rewrite H in H0; tryfalse.

  auto.
Qed.

Hint Resolve @merge_sem_none_rev : jdb1.
(* ** ac: SearchAbout "merge_sem". *)

Lemma merge_sem_none3 :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 a,
    get m1 a = None ->
    get m2 a = None ->
    get (merge m1 m2) a = None.
  intros.
  destruct (usePerm) eqn:F.
  jeauto2.
  jeauto2.
Qed.

(* ** ac: Check @merge_sem1'. *)

Ltac infer_merge x y t :=
  (** z = merge x y, then get z t = ? **)
  match goal with
    | F: get x t = ?b1, F1: get y t = ?b2 |- _ =>
      match constr:(b1, b2) with
        | (Some ?v1, Some ?v2) =>
          match goal with
            | Hn: usePerm = false |- _ =>
            (* assert (get (merge x y) t = Some v1) by jeauto2 *)
              generalize (@merge_sem1' _ _ _ _ _ _ _ _ _ Hn F F1); intro
            | Hn: usePerm = true |- _ =>
              let H' := fresh in
              generalize (@merge_semp _ _ _ _ x y t Hn); intro H';
              rewrite F in H';
              rewrite F1 in H';
              let Hs := fresh in 
              destruct (same v1 v2) eqn:Hs;
              rewrite_same;
              [ (** v1 = v2 **)
                (* try (subst v2); *)
                let H1 := fresh in
                destruct (isRw v1) eqn:H1;
                [ (** isRw v1 = true **)
                  idtac
                | (** isRw v1 = false  **)
                  assert (isRw (flip v1) = true) by jeauto2 ]
              | tryfalse]
          end
        | (Some ?v1, None) =>
        (* assert (get (merge x y) t = Some v1) by jeauto2 *)
          generalize (@merge_sem_none2 _ _ _ _ _ _ _ _ F1 F); intro
        | (None, Some ?v2) =>
        (* assert (get (merge x y) t = Some v2) by jeauto2 *)
          generalize (@merge_sem_none1 _ _ _ _ _ _ _ _ F F1); intro
        | (None, None) =>
          (* assert (get (merge x y) t = None) by jeauto2 *)
          generalize (@merge_sem_none3 _ _ _ _ _ _ _ F F1); intro
      end
  end.

Goal forall (A B T : Type) (MC : PermMap A B T) (m1 m2:T) (t:A),
    False.
  intros.
  destruct (usePerm) eqn:F;
  destruct (get m1 t) eqn:F1;
  destruct (get m2 t) eqn:F2;
  infer_merge m1 m2 t.
Abort.

(******************************************************************************)
(** disjoint **)


Lemma disjoint_sem:
  forall (A B T : Type) (MC : PermMap A B T) x y,
    usePerm = false ->
    (forall t, get x t = None \/ get y t = None) ->
    disjoint x y.
  intros.  
  unfold disjoint.
  eapply map_disjoint.
  intros.
  instant H0 t.
  tauto.
Qed.  

Lemma disjoint_sem':
  forall (A B T : Type) (MC : PermMap A B T) x y,
    usePerm = false ->
    disjoint x y ->
    (forall t, get x t = None \/ get y t = None).
  intros.
  unfold disjoint in *.
  heat.
  destruct (get x t) eqn: F1; destruct (get y t) eqn: F2.
  assert (False) by jeauto2.
  tryfalse.
  tauto.
  tauto.
  tauto.
Qed.

Lemma disjoint_semp:
  forall (A B T : Type) (MC : PermMap A B T) m1 m2,
    usePerm = true ->
    (forall t,
        match (get m1 t, get m2 t) with
          | (Some b0, Some b1) => b0 = b1 /\ isRw b0 = false
          | (Some b0, None) => True
          | (None, Some b1) => True
          | (None, None) => True
        end) ->
    (exists m, join m1 m2 m).
  intros.
  apply map_disjoint_semp; auto.
Qed.
  
Lemma disjoint_semp':
  forall (A B T : Type) (MC : PermMap A B T) m1 m2,
    usePerm = true ->
    (exists m, join m1 m2 m) ->
    (forall t,
        match (get m1 t, get m2 t) with
          | (Some b0, Some b1) => b0 = b1 /\ isRw b0 = false
          | (Some b0, None) => True
          | (None, Some b1) => True
          | (None, None) => True
        end).
  intros.
  apply map_disjoint_semp'; auto.
Qed.

Ltac auto_sem H :=
  (** auto apply *_sem lemma for hypo H **)
  match type of H with
    | disjoint _ _ =>
      match goal with
        | Hn : usePerm = false |- _ =>
          generalize (disjoint_sem' Hn H); intro
        | Hn : usePerm = true |- _ =>
          generalize (disjoint_semp' Hn H); intro
      end
    (* | join _ _ _ => *)
    (*   generalize (join_sem' H); intro *)
  end.

Lemma disjoint_sem1:
  forall (A B T : Type) (MC : PermMap A B T) (x y : T) t v,
    usePerm = false ->
    disjoint x y ->
    get x t = Some v ->
    get y t = None.
  intros.
  auto_sem H0.
  instant H2 t.
  destruct H2; tryfalse.
  auto.
Qed.

Hint Resolve @disjoint_sem1 : jdb1.

(* ** ac: SearchAbout disjoint. *)
Hint Resolve @disjoint_sym : jdb1.

Lemma disjoint_sem2:
  forall (A B T : Type) (MC : PermMap A B T) (x y : T) t v,
    usePerm = false ->
    disjoint x y ->
    get y t = Some v ->
    get x t = None.
  intros.
  assert (disjoint y x) by jeauto2.
  jeauto2.
Qed.

Hint Resolve @disjoint_sem2 : jdb1.

Lemma disjoint_semp1:
  forall (A B T : Type) (MC : PermMap A B T) (x y : T) t v,
    usePerm = true ->
    disjoint x y ->
    get x t = Some v ->
    (get y t = None \/
     (get y t = Some v /\ isRw v = false)).
  intros.
  auto_sem H0.
  instant H2 t.
  rewrite H1 in H2.
  destruct (get y t) eqn:F1.
  heat.
  tauto.
  tauto.
Qed.  

Hint Resolve @disjoint_semp1 : jdb1.

Lemma disjoint_semp2:
  forall (A B T : Type) (MC : PermMap A B T) (x y : T) t v,
    usePerm = true ->
    disjoint y x ->
    get x t = Some v ->
    (get y t = None \/
     (get y t = Some v /\ isRw v = false)).
  intros.
  assert (disjoint x y) by jeauto2.
  jeauto2.
Qed.  

Hint Resolve @disjoint_semp2 : jdb1.

(* ** ac: SearchAbout "disjoint_sem". *)

Ltac infer_disjoint x y t :=
  (** [disjoint x y] and [get x t], then [get y t] ? **)
  match goal with
    | H: disjoint x y |- _ =>
      match goal with
        | F1: get x t = ?b |- _ =>
          match constr:(b) with
            | Some ?v =>
              match goal with
                | Hn: usePerm = false |- _ =>
                (* assert (get y t = None) by jeauto2 *)
                  generalize (@disjoint_sem1 _ _ _ _ _ _ _ _ Hn H F1); intro
                | Hn: usePerm = true |- _ =>
                  let H' := fresh in 
                  (* assert (H' : get y t = None \/ (get y t = Some v /\ isRw v = false)) by jeauto2; *)
                  generalize (@disjoint_semp1 _ _ _ _ _ _ _ _ Hn H F1); intro H';
                  destruct H' as [? | [? ?]]
              end
            | None => idtac
          end
      end
  end.

Goal forall (A B T : Type) (MC : PermMap A B T) (x y : T) (t:A),
    disjoint x y ->
    False.
  intros.
  destruct (usePerm) eqn:F;
  destruct (get x t) eqn:F1;
  infer_disjoint x y t.
Abort.

(******************************************************************************)
(** minus **)

Lemma minus_sem :
  forall (A B T : Type) (MC : PermMap A B T) m m1 a,
    usePerm = false ->
    get (minus m m1) a 
    = match (get m a, get m1 a) with
        | (Some b, Some b1) => None
        | (Some b1, None) => Some b1
        | (None, Some b2) => None
        | (None, None) => None
      end.
  intros.
  apply map_minus_sem; auto.
Qed.

Lemma minus_semp :
  forall (A B T : Type) (MC : PermMap A B T) m1 m a,
    usePerm = true ->
    get (minus m m1) a
    = match (get m a, get m1 a) with
        | (Some b, Some b1) =>
          match (same b (flip b1)) return (option B) with
            | true => match (isRw b) with
                       | true => Some b1
                       | false => None
                     end
            | false => None
          end
        | (Some b, None) => Some b
        | (None, Some b1) => None
        | (None, None) => None
      end.
  intros.
  apply map_minus_semp; auto.
Qed.

Lemma minus_semp2 :
  forall (A B T : Type) (MC : PermMap A B T) m m1 a b,
    usePerm = true ->
    get m a = b ->
    get m1 a = None ->
    get (minus m m1) a = b.
  intros.
  rewrite minus_semp.
  destruct b; rewrite H0; rewrite H1.
  auto.
  auto.
  auto.
Qed.  
    
Lemma minus_semp3 :
  forall (A B T : Type) (MC : PermMap A B T) m m1 a,
    usePerm = true ->
    get m a = None ->
    get (minus m m1) a = None.
  intros.
  rewrite minus_semp; auto.
  destruct (get m1 a); rewrite H0; auto.
Qed.

Hint Resolve @minus_semp2 @minus_semp3 : jdb1.

Lemma minus_sem1 :
  forall (A B T : Type) (MC : PermMap A B T) m m1 m2 a b b1,
    usePerm = false ->
    get m a = Some b ->
    get m1 a = Some b1 ->
    m2 = minus m m1 ->
    get m2 a = None.
  intros.
  subst.
  rewrite minus_sem; auto.
  rewrite H0.
  rewrite H1.
  auto.
Qed.  

Lemma minus_sem2 :
  forall (A B T : Type) (MC : PermMap A B T) m m1 m2 a b,
    usePerm = false ->
    get m a = b ->
    get m1 a = None ->
    m2 = minus m m1 ->
    get m2 a = b.
  intros.
  subst.
  rewrite minus_sem; auto.
  destruct (get m a);
  rewrite H1; jeauto2.
Qed.  
  
Lemma minus_sem3 :
  forall (A B T : Type) (MC : PermMap A B T) m m1 m2 a,
    usePerm = false ->
    get m a = None ->
    m2 = minus m m1 ->
    get m2 a = None.
  intros.
  subst.
  rewrite minus_sem; auto.
  rewrite H0.
  destruct (get m1 a); auto.
Qed.  

Hint Resolve @minus_sem1 @minus_sem2 @minus_sem3 : jdb1.

Lemma minus_sem_none1 :
  forall (A B T : Type) (MC : PermMap A B T) m m1 a,
    get m a = None ->
    get (minus m m1) a = None.
  intros.
  destruct (usePerm) eqn: F.
  jeauto2.
  jeauto2.
Qed.

Lemma minus_sem_none2 :
  forall (A B T : Type) (MC : PermMap A B T) m m1 a b,
    get m a = b ->
    get m1 a = None ->
    get (minus m m1) a = b.
  intros.
  destruct (usePerm) eqn: F.
  jeauto2.
  jeauto2.
Qed.

Hint Resolve @minus_sem_none1 @minus_sem_none2 : jdb1.

(* ** ac: SearchAbout "minus_sem". *)

Lemma minus_sem1' :
  forall (A B T : Type) (MC : PermMap A B T) m m1 a b b1,
    usePerm = false ->
    get m a = Some b ->
    get m1 a = Some b1 ->
    get (minus m m1) a = None.
  intros.
  jeauto2.
Qed.  

Lemma minus_sem_none1' :
  forall (A B T : Type) (MC : PermMap A B T) m m1 a b,
    get m a = None ->
    get m1 a = b ->
    get (minus m m1) a = None.
  intros.
  destruct (usePerm) eqn: F.
  jeauto2.
  jeauto2.
Qed.
  
Ltac infer_minus z x t :=
  (** [get x t] and [get z t], then [get (minus z x) t = ?] **)
  match goal with
    | F: get z t = ?b, F1: get x t = ?b1 |- _ =>
      match constr:(b, b1) with
        | (Some ?v, Some ?v1) =>
          match goal with
            | Hn: usePerm = false |- _ =>
            (* assert (get (minus z x) t = None) by jeauto2 *)
              generalize (@minus_sem1' _ _ _ _ _ _ _ _ _ Hn F F1); intro
            | Hn: usePerm = true |- _ =>
              let H' := fresh in 
              generalize (@minus_semp _ _ _ _ x z t Hn); intro H';
              rewrite F in H';
              rewrite F1 in H';
              let Hs := fresh in 
              destruct (same v (flip v1)) eqn:Hs;
              rewrite_same;
              [(** v = flip v1 **)
                match goal with
                  | f : ?v = flip ?v |- _ =>
                    assert (False) by jeauto2;
                    tryfalse
                  | _ => idtac
                end;
                (* (try (subst v)); *)
                let H1 := fresh in
                destruct (isRw v) eqn:H1;
                [ (** isRw (flip v1) = true **)
                  assert ((isRw v1) = false) by (try (rewrite Hs in H1); jeauto2)
                | idtac ] 
              | tryfalse ] 
          end
        | (Some ?v, None) =>
        (* assert (get (minus z x) t = Some v) by jeauto2 *)
          generalize (@minus_sem_none2 _ _ _ _ _ _ _ _ F F1); intro
        | (None, _) =>
          (* assert (get (minus z x) t = None) by jeauto2 *)
          generalize (@minus_sem_none1' _ _ _ _ _ _ _ _ F F1); intro
      end
  end.

Goal forall (A B T : Type) (MC : PermMap A B T) (m m1:T) (t:A),
    False.
  intros.
  destruct (usePerm) eqn:Hn;
  destruct (get m t) eqn:F1;
  destruct (get m1 t) eqn:F2;
  infer_minus m m1 t.
Abort. 

(******************************************************************************)
(** del **)

Lemma del_sem:
  forall (A B T : Type) (MC : PermMap A B T) m a t,
    get (del m a) t
    = match (map_dec_a a t) with
        | left _ => None
        | right _ => get m t
      end.
  intros.
  apply map_del_sem; auto.
Qed.

Lemma del_sem1:
  forall (A B T : Type) (MC : PermMap A B T) m a t,
    a = t ->
    get (del m a) t = None.
  intros.
  subst.
  rewrite del_sem.
  destruct (map_dec_a t t); tryfalse.
  auto.
Qed.

Lemma del_sem2:
  forall (A B T : Type) (MC : PermMap A B T) m a b t,
    a <> t ->
    get m t = b ->
    get (del m a) t = b.
  intros.
  rewrite del_sem.
  destruct (map_dec_a a t); tryfalse.
  auto.
Qed.  

Hint Resolve @del_sem1 @del_sem2 : jdb1.

Ltac infer_del sd t :=
  (** [get m t], then [get (del m a) t = ?]
      sd = (del m a)
   **)
  match sd with
    | del ?m ?a =>
      destruct (map_dec_a a t);
      [ (** a = t **)
        try (solve [subst; tryfalse]);
        assert (get (del m a) t = None) by (apply del_sem1; auto)
      | tryfalse;
        match goal with
          | H: get m t = ?b |- _ =>
            assert (get (del m a) t = b) by (apply del_sem2; auto)
        end ]
  end.

Goal forall (A B T : Type) (MC : PermMap A B T) (m:T) (a t:A),
    False.
  intros.
  destruct (get m t) eqn:F;
  infer_del (del m a) t.
Abort.

(******************************************************************************)
(** join **)


Lemma map_join_getp_some' :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m a b b1 b2,
    usePerm = true ->
    join m1 m2 m ->
    get m1 a = Some b1 ->
    get m2 a = Some b2 ->
    b1 = b2 ->
    isRw b1 = false ->
    b = flip b1 ->
    get m a = Some b. 
  intros.
  (* ** ac: Check map_join_getp_some. *)
  generalize (map_join_getp_some H H0 H1 H2 H5).
  intros.
  tauto.
Qed.  

Hint Resolve @map_join_getp_some' : jdb1.

Lemma map_join_get_none' :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m a b,
    join m1 m2 m ->
    get m1 a = None ->
    get m2 a = b ->
    get m a = b.
  intros.
  rewrite <- H1.
  jeauto2.
Qed.

Hint Resolve @map_join_get_none' : jdb1.

Lemma join_sem:
  forall (A B T : Type) (MC : PermMap A B T) x y z,
    disjoint x y ->
    z = (merge x y) ->
    join x y z.
  intros.
  subst.
  destruct (usePerm) eqn: F.
  Focus 2.
  unfold disjoint in H.
  heat.
  assert ((merge x y) = x0).
  {
    apply map_eql.
    intro.
    rewrite merge_sem.
    destruct (get x t) eqn: F1;
    destruct (get y t) eqn: F2.
    assert (False) by jeauto2.
    tryfalse.
    assert (get x0 t = Some b) by jeauto2.
    rewrite H0.
    auto.
    assert (get x0 t = Some b) by jeauto2.
    rewrite H0.
    auto.
    assert (get x0 t = get x t) by jeauto2.
    rewrite F1 in H0.
    rewrite H0.
    auto.
    auto.
  }
  subst.
  auto.

  (* ** ac: Check @disjoint_semp'. *)
  generalize (@disjoint_semp' _ _ _ _ _ _ F H); intro.
  unfold disjoint in H.
  heat.
  assert (x0 = merge x y).
  {
    apply map_eql.
    intros.
    instant H0 t.
    rewrite merge_semp; auto.
    destruct (get x t) eqn:F1;
    destruct (get y t) eqn:F2.
    destruct (same b b0) eqn:F3; rewrite_same; subst.    
    destruct (isRw b0) eqn:F3.
    heat; tryfalse.
    heat.
    jeauto2.
    heat; tryfalse.
    jeauto2.
    jeauto2.
    jeauto2.
  }
  subst; auto.
Qed.

Hint Resolve @join_sem : jdb1.

Lemma join_sem':
  forall (A B T : Type) (MC : PermMap A B T) x y z,
    join x y z ->
    disjoint x y /\ z = (merge x y).
  intros.
  split.
  geat.
  apply map_eql.
  intros.
  destruct (usePerm) eqn:F.
  rewrite merge_semp; auto.
  destruct (get x t) eqn:F1;
  destruct (get y t) eqn:F2.
  destruct (same b b0) eqn:Ht; rewrite_same; subst.    
  destruct (isRw b0) eqn:F3.
  assert (b0 = b0 /\ isRw b0 = false /\ get z t = Some (flip b0)) by jeauto2.
  heat; tryfalse.
  jeauto2.
  assert (b = b0 /\ isRw b = false /\ get z t = Some (flip b)) by jeauto2.
  heat; tryfalse.
  jeauto2.
  jeauto2.
  jeauto2.

  rewrite merge_sem; auto.
  destruct (get x t) eqn:F1;
  destruct (get y t) eqn:F2.
  destruct (same b b0) eqn:Ht; rewrite_same; subst; jeauto2.
  jeauto2.
  jeauto2.
  jeauto2.
Qed.
  
Lemma join_sem1:
  forall (A B T : Type) (MC : PermMap A B T) x y z t v,
    usePerm = false ->
    join x y z ->
    get x t = Some v ->
    get z t = Some v.
  intros.
  destruct (get x t) eqn: F1;
  destruct (get y t) eqn: F2.
  assert (False) by jeauto2.
  tryfalse.
  assert (get z t = get x t) by jeauto2.
  rewrite F1 in H2.
  rewrite H2.
  inverts H1.
  auto.
  tryfalse.
  tryfalse.
Qed.

Hint Resolve @join_sem1 : jdb1.

Lemma join_semp1:
  forall (A B T : Type) (MC : PermMap A B T) x y z t b1 b2,
    usePerm = true ->
    join x y z ->
    get x t = Some b1 ->
    get y t = Some b2 ->
    b1 <> b2 ->
    False.
  intros.
  apply join_sem' in H0.
  heat.
  generalize (disjoint_semp' H H0 t); intro.
  rewrite H1 in H4; rewrite H2 in H4.
  heat.
  tryfalse.
Qed.  
  
Lemma join_semp2:
  forall (A B T : Type) (MC : PermMap A B T) x y z t b1 b2,
    usePerm = true ->
    join x y z ->
    get x t = Some b1 ->
    get y t = Some b2 ->
    isRw b1 = true ->
    False.
  intros.
  apply join_sem' in H0.
  heat.
  generalize (disjoint_semp' H H0 t); intro.
  generalize H4.
  rewrite H1; rewrite H2.
  intros.
  heat.
  tryfalse.
Qed.

Hint Resolve @join_semp1 @join_semp2 : jdb1.

Lemma join_get_none_rev:
  forall (A B T : Type) (MC : PermMap A B T) x y z t,
    join x y z ->
    get z t = None ->
    get x t = None /\ get y t = None.
  intros.
  apply join_sem' in H.
  heat.
  destruct (usePerm) eqn:Hn;
  destruct (get x t) eqn:F1;
  destruct (get y t) eqn:F2;
  infer_disjoint x y t;
  infer_merge x y t;
  crush.
Qed.

Hint Resolve @join_get_none_rev : jdb1.

Lemma join_get_none_rev1:
  forall (A B T : Type) (MC : PermMap A B T) x y z t,
    join x y z ->
    get z t = None ->
    get x t = None.
  intros.
  assert (get x t = None /\ get y t = None) by jeauto2.
  heat.
  auto.
Qed.

Lemma join_get_none_rev2:
  forall (A B T : Type) (MC : PermMap A B T) x y z t,
    join x y z ->
    get z t = None ->
    get y t = None.
  intros.
  assert (get x t = None /\ get y t = None) by jeauto2.
  heat.
  auto.
Qed.

Hint Resolve @join_get_none_rev1 @join_get_none_rev2 : jdb1.

Lemma map_join_get_none'' :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m a b,
    join m1 m2 m ->
    get m2 a = None ->
    get m1 a = b ->
    get m a = b.
  intros.
  rewrite <- H1.
  jeauto2.
Qed.

(* ** ac: Check @map_join_get_none. *)

Lemma map_join_get_none''' :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m a,
    join m1 m2 m ->
    get m1 a = None ->
    get m2 a = None ->
    get m a = None.
  intros.
  jeauto2.
Qed.  

Lemma map_join_getp_some''
     : forall (A B T : Type) (PermMap : PermMap A B T)
         (x y z : T) (t : A) (v1 v2: B),
    usePerm = true ->
    join x y z ->
    get x t = Some v1 ->
    get y t = Some v2 ->
    v1 = v2 /\ isRw v1 = false /\ get z t = Some (flip v1).
  intros.
  jeauto2.
Qed.


(* ** ac: Check @map_join_get_some. *)
Ltac infer_join x y z t :=
  (** [join x y z] and [get x t] and [get y t], then [get z t = ?] **)
  match goal with
    | H: join x y z |- _ =>
      match goal with
        | F1: get x t = ?b1, F2: get y t = ?b2 |- _ =>
          match constr:(b1, b2) with
            | (Some ?v1, Some ?v2) =>
              match goal with
                | Hn: usePerm = false |- _ =>
                (* assert (False) by jeauto2; tryfalse *)
                  generalize (@map_join_get_some _ _ _ _ _ _ _ _ _ _ Hn H F1 F2); intro; tryfalse 
                | Hn: usePerm = true |- _ =>
                  let H' := fresh in 
                  (* assert (H': v1 = v2 /\ isRw v1 = false /\ get z t = Some (flip v1)) by jeauto2; *)
                  generalize (@map_join_getp_some'' _ _ _ _ _ _ _ _ _ _ Hn H F1 F2); intro H';
                  destruct H' as [ ? [? ?]]
                  (* try (subst v1) *)
              end
            | (Some ?v1, None) =>
            (* assert (get z t = Some v1) by jeauto2 *)
              generalize (@map_join_get_none'' _ _ _ _ _ _ _ _ _ H F2 F1); intro
            | (None, Some ?v2) =>
            (* assert (get z t = Some v2) by jeauto2 *)
              generalize (@map_join_get_none' _ _ _ _ _ _ _ _ _ H F1 F2); intro
            | (None, None) =>
              (* assert (get z t = None) by jeauto2 *)
              generalize (@map_join_get_none''' _ _ _ _ _ _ _ _ H F1 F2); intro
          end
      end
  end.

Goal forall (A B T : Type) (MC : PermMap A B T) (m1 m2 m:T) (t:A),
    join m1 m2 m ->
    False.
  intros.
  destruct (usePerm) eqn:F;
  destruct (get m1 t) eqn:F1;
  destruct (get m2 t) eqn:F2;
  infer_join m1 m2 m t.
Abort.

Goal forall (A B T : Type) (MC : PermMap A B T) (m1 m2 m:T) (t:A) v,
    join m1 m2 m ->
    get m1 t = None ->
    get m2 t = Some v ->
    False.
  intros.
  infer_join m1 m2 m t.
Abort.
(******************************************************************************)
(** sub **)
  
Lemma sub_semp:
  forall (A B T : Type) (MC : PermMap A B T) m m1,
    usePerm = true ->
    (forall t, match (get m t, get m1 t) with
            | (Some b, Some b0) =>
              match (isRw b, isRw b0) with
                | (true, true) => b = b0
                | (true, false) => b = flip b0
                | (false, true) => False
                | (false, false) => b = b0
              end
            | (Some b, None) => True
            | (None, Some b) => False
            | (None, None) => True
          end) ->
    sub m1 m.
  intros.
  unfold sub.
  exists (minus m m1).
  apply join_sem.
  apply disjoint_semp; auto.
  intro.
  instant H0 t.
  rewrite minus_semp.
  destruct (get m t) eqn:F;
  destruct (get m1 t) eqn:F1.
  destruct (same b (flip b0)) eqn:Ht; rewrite_same.
  destruct (isRw b) eqn:F2.
  subst.
  assert (isRw b0 = false) by jeauto2.  
  rewrite H1 in *.
  auto.
  auto.
  auto.
  auto.
  auto.
  auto.
  auto.

  apply map_eql.
  intro.
  instant H0 t.
  rewrite merge_semp.
  rewrite minus_semp.
  destruct (get m t) eqn:F;
  destruct (get m1 t) eqn:F1.
  destruct (same b (flip b0)) eqn:Ht; rewrite_same.
  destruct (isRw b) eqn:F2.
  destruct (same b0 b0) eqn:Ht'; rewrite_same; tryfalse.
  subst.
  assert (isRw b0 = false) by jeauto2.
  rewrite H1 in *.
  auto.

  subst.
  assert (Ht: isRw b0 = true) by jeauto2.
  rewrite Ht in *.
  tryfalse.

  destruct (isRw b) eqn:F2;
  destruct (isRw b0) eqn:F3.
  subst.
  auto.
  subst.
  tryfalse.
  tryfalse.
  subst.
  auto.
  auto.
  tryfalse.
  auto.
  auto.
  auto.
Qed.

(* ** ac: Print Ltac crush. *)

Ltac tryfalse_flip :=
  match goal with
    | H: ?v = flip ?v |- _ =>
      assert (False) by jeauto2;
      tryfalse
    | H: flip ?v = ?v |- _ =>
      assert (v = flip v) by jeauto2;
      assert (False) by jeauto2;
      tryfalse
    | _ => idtac
  end.

Ltac crush2 :=
  crush1; tryfalse_flip.

Ltac crush ::= crush2.

Lemma sub_sem':
  forall (A B T : Type) (MC : PermMap A B T) m m1 m2,
    sub m1 m ->
    m2 = minus m m1 ->
    join m1 m2 m.
  intros.
  unfold sub in *.
  heat.
  assert (x = minus m m1).
  {
    apply map_eql.
    intros.
    destruct usePerm eqn: Hn;
    destruct (get m1 t) eqn:F1;
    destruct (get x t) eqn:F2;
    infer_join m1 x m t;
    infer_minus m m1 t;
    crush.
  }
  subst; auto.
Qed.  

Hint Resolve @sub_sem' : jdb1.
Lemma sub_sem1:
  forall (A B T : Type) (MC : PermMap A B T) m m1 t b,
    usePerm = false ->
    sub m1 m ->
    get m1 t = Some b ->
    get m t = Some b.
  intros.
  geat.
Qed.  

Hint Resolve @sub_sem1 : jdb1.

Lemma sub_semp1 : forall (A B T:Type) (MC:PermMap A B T) x z t b1,
    usePerm = true ->
    sub x z ->
    get x t = Some b1 ->
    (get z t = Some b1 \/
     (get z t = Some (flip b1) /\ isRw b1 = false)).
  intros.
  assert (join x (minus z x) z) by jeauto2.
  destruct (get (minus z x) t) eqn:F1;
  infer_join x (minus z x) z t.
  tauto.
  tauto.
Qed.  

Hint Resolve @sub_semp1 : jdb1.

Lemma sub_sem:
  forall (A B T : Type) (MC : PermMap A B T) m m1,
    usePerm = false ->
    (forall t b, get m1 t = Some b ->
            get m t = Some b) ->
    sub m1 m.
  intros.
  unfold sub.
  exists (minus m m1).
  assert (disjoint m1 (minus m m1)).
  {
    eapply disjoint_sem; auto.
    intros.
    instant H0 t.
    destruct (get m1 t) eqn: F1.
    instant H0 b.
    right.
    assert (Some b = Some b) by jeauto2.
    apply H0 in H1.
    jeauto2.
    auto.
  }
  unfold disjoint in *.
  heat.
  assert (x = m).
  {
    apply map_eql.
    intro.
    instant H0 t.
    destruct (get m1 t) eqn:F1.
    instant H0 b.
    assert (Some b = Some b) by auto.
    apply H0 in H2.
    assert (get x t = Some b) by jeauto2.
    rewrite H3.
    rewrite H2.
    auto.
    assert (get x t = get (minus m m1) t) by jeauto2.
    rewrite H2.
    destruct (get m t) eqn: F2.
    jeauto2.
    jeauto2.
  }
  subst.
  auto.
Qed.

Lemma merge_sub_intro : 
  forall (A B T : Type) (MC : PermMap A B T) m m1 m2,
    usePerm = false ->
    sub m1 m ->
    sub m2 m ->
    sub (merge m1 m2) m.
  intros.
  apply sub_sem; auto.
  intros.
  (* ** ac: SearchAbout merge. *)
  destruct (get m1 t) eqn:F1;
  destruct (get m2 t) eqn:F2.
  (* ** ac: SearchAbout sub. *)
  assert (get m t = Some b0) by jeauto2.
  assert (get m t = Some b1) by jeauto2.
  rewrite H3 in *.
  inverts H4.
  assert (get (merge m1 m2) t = Some b1) by jeauto2.
  rewrite H2 in H4.
  inverts H4.
  auto.

  assert (get m t = Some b0) by jeauto2.
  assert (get (merge m1 m2) t = Some b0) by jeauto2.
  rewrite H3.
  rewrite H2 in H4.
  inverts H4.
  auto.
  
  assert (get m t = Some b0) by jeauto2.
  assert (get (merge m1 m2) t = Some b0) by jeauto2.
  rewrite H3.
  rewrite H2 in H4.
  inverts H4.
  auto.

  assert (get (merge m1 m2) t = None) by jeauto2.
  rewrite H2 in H3.
  tryfalse.
Qed.

Hint Resolve @merge_sub_intro : jdb1.
(* ** ac: SearchAbout "sub_sem". *)

Ltac infer_sub x z t :=
  match goal with
    | H: sub x z |- _ =>
      match goal with
        | F1: get x t = ?b |- _ =>
          match constr:(b) with
            | Some ?v =>
              match goal with
                | Hn: usePerm = false |- _ =>
                (* assert (get z t = Some v) by jeauto2 *)
                  generalize (@sub_sem1 _ _ _ _ _ _ _ _ Hn H F1); intro
                | Hn: usePerm = true |- _ =>
                  let H' := fresh in
                  (* assert (H': get z t = Some v \/ (get z t = Some (flip v) /\ isRw v = false)) by jeauto2; *)
                  generalize (@sub_semp1 _ _ _ _ _ _ _ _ Hn H F1); intro H';
                  destruct H' as [? | [? ?]];
                  [ idtac
                  | assert (isRw (flip v) = true) by jeauto2 ]
              end
            | None => idtac
          end
      end
  end.
  
Goal forall (A B T : Type) (MC : PermMap A B T) m1 m2 (t:A),
    sub m1 m2 ->
    False.
  intros.
  destruct (usePerm) eqn:Hn;
  destruct (get m1 t) eqn:F1;
  destruct (get m2 t) eqn:F2;
  infer_sub m1 m2 t.
Abort.
  
(******************************************************************************)
(** set **)

Lemma map_get_set'':
  forall (A B T : Type) (MC : PermMap A B T) x t t' v b,
    t <> t' ->
    get x t' = b ->
    get (set x t v) t' = b.
  intros.
  rewrite map_get_set'; auto.
Qed.

Hint Resolve @map_get_set'' : jdb1.

Lemma map_get_set''':
  forall (A B T : Type) (MC : PermMap A B T) x t v t',
    t = t' ->
    get (set x t v) t' = Some v.
  intros.
  subst.
  jeauto2.
Qed.  

Hint Resolve @map_get_set''' : jdb1.

Ltac infer_set sm t :=
  (** sm has form [set m t' v] **)
  match sm with
    | set ?m ?t' ?v' =>
      destruct (map_dec_a t t');
      [ (** t = t' **)
        try (solve [subst; tryfalse]);
        assert (get (set m t' v') t = Some v') by (apply map_get_set'''; auto)
      | tryfalse;
        match goal with
          | H: get m t = ?b |- _ =>
            assert (get (set m t' v') t = b) by (apply map_get_set''; auto)
        end ]
  end.

Goal forall (A B T : Type) (MC : PermMap A B T) (m :T) (t t':A) (v v':B),
    get m t = Some v ->
    False.
  intros.
  infer_set (set m t' v') t.
Abort.

(******************************************************************************)
(** sig **)

Lemma map_get_sig'':
  forall (A B T : Type) (MC : PermMap A B T) t t' v,
    t <> t' ->
    get (sig t v) t' = None.
  intros.
  rewrite map_get_sig'; auto.
Qed.

Hint Resolve @map_get_sig'' : jdb1.

Lemma map_get_sig''':
  forall (A B T : Type) (MC : PermMap A B T) t v t',
    t = t' ->
    get (sig t v) t' = Some v.
  intros.
  subst.
  jeauto2.
Qed.  

Hint Resolve @map_get_sig''' : jdb1.

Ltac infer_sig sg t' :=
  (** sg has form [sig t v] **)
  match sg with
    | sig ?t ?v =>
      destruct (map_dec_a t t');
      [ (** t = t' **)
        try (solve [subst; tryfalse]);
        assert (get (sig t v) t' = Some v) by (apply map_get_sig'''; auto)
      | tryfalse;
        assert (get (sig t v) t' = None) by (apply map_get_sig''; auto) ]
  end.

Goal forall (A B T : Type) (MC : PermMap A B T) (t t':A) (v:B),
    False.
  intros.
  infer_sig (sig t v) t'.
Abort.
  
(******************************************************************************)
(** interpret and infer **)

Ltac interpret ins t' :=
  match ins with
    | usePerm =>
      let H := fresh in
      destruct (usePerm) eqn:H
    | (sig ?t ?v) =>
      infer_sig (sig t v) t'
    | (set ?m ?t ?v) =>
      infer_set (set m t v) t'
    | (del ?m ?t) =>
      infer_del (del m t) t'
    | (sub ?m1 ?m) =>
      infer_sub m1 m t'
    | join ?x ?y ?z =>
      infer_join x y z t'
    | merge ?x ?y =>
      infer_merge x y t'
    | disjoint ?x ?y =>
      infer_disjoint x y t'
    | minus ?x ?y =>
      infer_minus x y t'
    | ?m =>
      let H:= fresh in
      destruct (get m t') eqn:H
  end.

Ltac infer ls t :=
     match ls with
       | (?ls', ?ins) =>
         infer ls' t;
         interpret ins t
       | _ =>
         interpret ls t
     end.

(******************************************************************************)
(** hy tactics **)

Ltac hy_disjoint ls t:=
  match goal with
    | Hn : usePerm = true |- disjoint ?x ?y =>
      apply disjoint_semp; auto 1; intro t;
      infer ls t
    | Hn : usePerm = false |- disjoint ?x ?y =>
      apply disjoint_sem; auto 1; intro t;
      infer ls t
  end.

Ltac hy_eql ls t :=
  match goal with
    | |- ?a = ?b =>
      apply map_eql;
      intro t;
      infer ls t
  end.

Ltac hy_join ls t :=
  match goal with
    | |- join ?x ?y ?z =>
      apply join_sem;
      [ hy_disjoint ls t
      | let ls' := constr:(pair ls (merge x y)) in
        hy_eql ls' t]
  end.

Ltac hy_sub ls t:=
  match goal with
    | Hn : usePerm = true |- sub ?x ?y =>
      apply sub_semp; auto 1; intro t;
      infer ls t
    | Hn : usePerm = false |- sub ?x ?y =>
      apply sub_sem; auto 1; intro t;
      infer ls t
  end.

(******************************************************************************)

Lemma get_sig :
  forall (A B T : Type) (MC : PermMap A B T) a a' b,
    get (sig a b) a' =
    if (dec a a') then Some b else None.
Proof.
  intros.
  destruct (dec a a'); geat.
Qed.  


Lemma get_sig_some :
  forall (A B T : Type) (MC : PermMap A B T) (a : A) (b : B),
    get (sig a b) a = Some b.
Proof.
  intros.
  jeauto2.
Qed.  

Lemma get_sig_none :
  forall (A B T : Type) (MC : PermMap A B T) (a a' : A) (b : B),
    a <> a' ->
    get (sig a b) a' = None.
  intros; jeauto2.
Qed.

Lemma get_sig_some_eq :
  forall (A B T : Type) (MC : PermMap A B T) (a a' : A) (b : B),
    get (sig a b) a' = Some b ->
    a = a'.
Proof.
  intros.
  destruct (dec a a').
  auto.
  assert (get (sig a b) a' = None) by jeauto2.
  rewrite H0 in H.
  tryfalse.
Qed.  
  
Lemma get_sig_some_eq' :
  forall (A B T : Type) (MC : PermMap A B T) (a a' : A) (b b' : B),
    get (sig a b) a' = Some b' ->
    a = a' /\ b = b'.
Proof.
  intros.
  destruct (dec a a').
  subst.
  assert (b = b') by jeauto2.
  auto.
  assert (get (sig a b) a' = None) by jeauto2.
  rewrite H0 in H.
  tryfalse.
Qed.  

Lemma set_a_get_a :
  forall (A B T : Type) (MC : PermMap A B T) a b m,
    get (set m a b) a = Some b.
  jeauto2.
Qed.

Lemma set_a_get_a' :
  forall (A B T : Type) (MC : PermMap A B T) a a' b m,
    a <> a' ->
    get (set m a b) a' = get m a'.
  jeauto2.
Qed.  

Lemma set_sig :
  forall (A B T : Type) (MC : PermMap A B T) a b b',
  set (sig a b) a b' = sig a b'.
  jeauto2.
Qed.  

Lemma set_emp_sig :
  forall (A B T : Type) (MC : PermMap A B T) a b,
  set emp a b = sig a b.
  jeauto2.
Qed.

Lemma get_a_sig_a :
  forall (A B T : Type) (MC : PermMap A B T) a b,
    get (sig a b) a = Some b.
  jeauto2.
Qed.

Lemma get_a_sig_a' :
  forall (A B T : Type) (MC : PermMap A B T) a a' b,
    a <> a' -> get (sig a b) a' = None.
  jeauto2.
Qed.

Lemma indom_get :
  forall (A B T : Type) (MC : PermMap A B T) m a,
    indom m a ->
    exists b, get m a = Some b.
  unfold indom.
  intros.
  auto.
Qed.

Lemma get_indom :
  forall (A B T : Type) (MC : PermMap A B T) m (a : A),
  (exists b, get m a = Some b)
  -> indom m a.
  unfold indom.
  jeauto2.
Qed.


Lemma nindom_get :
  forall (A B T : Type) (MC : PermMap A B T) m (a : A),
    ~ indom m a -> get m a = None.
  unfold indom.
  intros.
  unfold not in H.
  destruct (get m a) eqn:F.
  assert (exists v, Some b = Some v) by jeauto2.
  instant H H0.
  tryfalse.
  auto.
Qed.  

Lemma sub_refl :
  forall (A B T : Type) (MC : PermMap A B T) m,
    sub m m.
  unfold sub.
  intros.
  geat.
Qed.

Lemma sub_trans :
  forall (A B T : Type) (MC : PermMap A B T) (m1 m2 m3 : T),
    sub m1 m2 
    -> sub m2 m3
    -> sub m1 m3.
  unfold sub.
  intros.
  geat.
Qed.

Lemma sub_sig :
  forall (A B T : Type) (MC : PermMap A B T) m a b,
    get m a = Some b
    -> sub (sig a b) m.
  unfold sub.
  intros.
  geat.
Qed.

Lemma get_sub_get :
  forall (A B T : Type) (MC : PermMap A B T) (m1 m2 : T) (a : A) (b : B),
    usePerm = false ->
    get m1 a = Some b ->
    sub m1 m2 ->
    get m2 a = Some b.
  intros.
  geat.
Qed.

Lemma indom_sub_indom :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 a, 
    usePerm = false ->
    indom m1 a -> sub m1 m2 -> indom m2 a.
  intros.
  geat.
Qed.

Lemma disj_emp_l :
  forall (A B T : Type) (MC : PermMap A B T) (m : T),
    disjoint (emp) m.
  intros.
  geat.
Qed.  

Lemma disj_emp_r :
  forall (A B T : Type) (MC : PermMap A B T) m,
    disjoint m emp.
  intros.
  geat.
Qed.  

Lemma disj_sym :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2,
    disjoint m1 m2 ->
    disjoint m2 m1.
  intros.
  geat.
Qed.

Lemma disj_sig :
  forall (A B T : Type) (MC : PermMap A B T) a a' b b',
    a <> a' ->
    disjoint (sig a b) (sig a' b').
  intros.
  unfold disjoint.
  eapply map_disjoint.
  intros.
  destruct (dec t a).
  subst.
  right.
  left.
  jeauto2.
  left.
  jeauto2.
Qed.  

(** general **)
Hint Resolve @jl_intro_get_noPerm : jdb1.

Lemma jl_sig_false :
  forall (A B T : Type) (MC : PermMap A B T) t v1 v2 l m,
    usePerm = false ->
    join_list (sig t v1 :: sig t v2 :: l) m ->
    False.
  intros.
  assert ((sig t v1 :: sig t v2 :: l) = ((sig t v1 :: nil) ++ (sig t v2 :: l))) by auto.
  rewrite H1 in H0.
  apply jl_split in H0.
  heat.
  clear H1.
  assert (get x t = Some v1) by jeauto2.
  assert (get x0 t = Some v2) by jeauto2.
  eapply map_join_get_some; eauto 2.
Qed.  

Hint Resolve @jl_sig_false : jdb1.

Lemma disj_indom : 
  forall (A B T : Type) (MC : PermMap A B T) (m1 m2 : T),
    usePerm = false ->
    disjoint m1 m2 -> 
    (forall a : A, 
      (indom m1 a -> ~ indom m2 a)
      /\ (indom m2 a -> ~ indom m1 a)).
  intros.
  geat.
  intros.
  geat.
  unfold not.
  intros.
  geat.
  liftH H0 (sig a x2).
  eapply jl_sig_false; eauto.
  intros.
  geat.
  unfold not.
  intros.
  geat.
  liftH H0 (sig a x0).
  eapply jl_sig_false; eauto.
Qed.  

(** general **)
Lemma nindom_get_rev:
  forall (A B T : Type) (MC : PermMap A B T) (m : T) a,
    get m a = None -> ~ indom m a.
  intros.
  unfold indom.
  unfold not.
  intros.
  destruct H0.
  tryfalse.
Qed.  

Lemma indom_or :
  forall (A B T : Type) (MC : PermMap A B T) (m : T),
    (forall a: A,
        indom m a \/ ~ indom m a).
  intros.
  generalize (@get_or _ _ _ _ m a).
  intros.
  destruct H.
  right.
  apply nindom_get_rev.
  auto.
  left.
  apply get_indom.
  auto.
Qed.  
  
Lemma indom_disj :
  forall (A B T : Type) (MC : PermMap A B T) (m1 m2 : T),
    usePerm = false ->
    (forall a : A, 
        (indom m1 a -> ~ indom m2 a)
        /\ (indom m2 a -> ~ indom m1 a))
    -> disjoint m1 m2.
  intros.
  eapply map_disjoint.
  intros.
  instant H0 t.
  generalize (@indom_or _ _ _ _ m1 t).
  intros.
  destruct H0; destruct H1.
  apply H0 in H1.
  apply nindom_get in H1.
  right; left; auto.
  apply nindom_get in H1.
  left; auto.
Qed.

Lemma merge_sem_none_rev1:
  forall (A B T : Type) (MC : PermMap A B T) (m1 m2 : T) (a : A),
    get (merge m1 m2) a = None -> get m1 a = None.
  intros.
  apply merge_sem_none_rev in H.
  tauto.
Qed.

Lemma merge_sem_none_rev2:
  forall (A B T : Type) (MC : PermMap A B T) (m1 m2 : T) (a : A),
    get (merge m1 m2) a = None -> get m2 a = None.
  intros.
  apply merge_sem_none_rev in H.
  tauto.
Qed.

Hint Resolve @merge_sem_none_rev1 @merge_sem_none_rev2 : jdb1.
  

Lemma indom_merge_intro :
  forall (A B T : Type) (MC : PermMap A B T) (m1 m2 : T) (a : A),
    usePerm = false ->
    indom m1 a \/ indom m2 a ->
    indom (merge m1 m2) a.
  unfold indom.
  intros.
  destruct H0; heat.
  exists x.
  jeauto2.
  destruct (get m1 a) eqn: F1.
  exists b.
  jeauto2.
  exists x.
  jeauto2.
Qed.  
  
Lemma indom_merge_elim: 
  forall (A B T : Type) (MC : PermMap A B T) (m1 m2 : T) (a : A),
    indom (merge m1 m2) a ->
    indom m1 a \/ indom m2 a.
  unfold indom.
  intros.
  heat.
  destruct (get m1 a) eqn:F1;
  destruct (get m2 a) eqn:F2.
  left.
  eauto.
  left.
  eauto.
  right; eauto.
 
  assert (get (merge m1 m2) a = None) by jeauto2.
  rewrite H in H0.
  tryfalse.
Qed.

(** warning **)
Lemma disj_merge_intro_l :
  forall (A B T : Type) (MC : PermMap A B T) (m1 m2 m3 : T),
    usePerm = false -> (** usePerm = true is not valid **)
    disjoint m1 m3 /\ disjoint m2 m3 ->
    disjoint (merge m1 m2) m3.
  intros.
  eapply disjoint_sem; auto.
  destruct H0.
  (* ** ac: Check disjoint_sem'. *)
  intros.
  generalize (disjoint_sem' H H0 t); intro.
  generalize (disjoint_sem' H H1 t); intro.
  destruct H2; destruct H3; try tauto.
  left.
  jeauto2.
Qed.  

(** warning **)
Lemma disj_merge_elim_l :
  forall (A B T : Type) (MC : PermMap A B T) (m1 m2 m3 : T),
    usePerm = false -> (** usePerm = true is not valid **)
    disjoint (merge m1 m2) m3    
    -> disjoint m1 m3 /\ disjoint m2 m3.
  intros.
  rename H into Hn.
  rename H0 into H.
  generalize (disjoint_sem' Hn H); intro.
  split; eapply disjoint_sem; auto.
  intros.
  instant H0 t.
  destruct H0; try tauto.
  left.
  jeauto2.

  intros.
  instant H0 t.
  destruct H0; try tauto.
  eapply merge_sem_none_rev in H0.
  tauto.
Qed.  

Hint Resolve @disjoint_sym : jdb1.

(** warning **)
Lemma disj_merge_intro_r :
  forall (A B T : Type) (MC : PermMap A B T) (m1 m2 m3 : T),
    usePerm = false -> (** usePerm = true is not valid **)
    disjoint m1 m2 /\ disjoint m1 m3
    -> disjoint m1 (merge m2 m3).
  intros.
  (* ** ac: SearchAbout disjoint. *)
  apply disjoint_sym.
  (* ** ac: SearchAbout disjoint. *)
  destruct H0.
  eapply disj_merge_intro_l; auto.
  split; jeauto2.
Qed.  

(** warning **)
Lemma disj_merge_elim_r :
  forall (A B T : Type) (MC : PermMap A B T) (m1 m2 m3 : T),
    usePerm = false -> (** usePerm = true is not valid **)
    disjoint m1 (merge m2 m3)
    -> disjoint m1 m2 /\ disjoint m1 m3.
  intros.
  apply disjoint_sym in H0.
  apply disj_merge_elim_l in H0.
  destruct H0; split; jeauto2.
  auto.
Qed.  

Lemma disj_merge_intro_lr :
  forall (A B T : Type) (MC : PermMap A B T) (m1 m2 m1' m2' : T),
    usePerm = false ->
    disjoint m1 m1'
    -> disjoint m1 m2'
    -> disjoint m2 m1'
    -> disjoint m2 m2'
    -> disjoint (merge m1 m2) (merge m1' m2').
  intros.
  apply disj_merge_intro_l; auto.
  split; apply disj_merge_intro_r; jeauto2.
Qed.  

Lemma disj_merge_elim_lr :
  forall (A B T : Type) (MC : PermMap A B T) (m1 m2 m1' m2' : T),
    usePerm = false ->
    disjoint (merge m1' m2') (merge m1 m2)
    -> (disjoint m1 m1' /\ disjoint m1 m2')
    /\ (disjoint m2 m1' /\ disjoint m2 m2').
  intros.
  apply disj_merge_elim_l in H0; auto.
  destruct H0.
  apply disj_merge_elim_r in H0; auto.
  apply disj_merge_elim_r in H1; auto.
  heat.
  splits; jeauto2.
  split; jeauto2.
Qed.  

Lemma join_comm :
  forall (A B T:Type) (MC:PermMap A B T) ma mb mab,
    join ma mb mab -> join mb ma mab.
  intros; geat.
Qed.
  
Lemma join_assoc_l :
  forall (A B T:Type) (MC:PermMap A B T) ma mb mc mab mabc,
    join ma mb mab->
    join mab mc mabc ->
    exists mbc, join mb mc mbc /\
      join ma mbc mabc.
  intros; geat.
Qed.  
  
Lemma join_assoc_r :
  forall (A B T:Type) (MC:PermMap A B T) ma mb mc mbc mabc,
    join mb mc mbc->
    join ma mbc mabc ->
    exists mab, join ma mb mab /\
           join mab mc mabc.
  intros; geat.
Qed.
  
Lemma join_sub_l :
  forall (A B T:Type) (MC:PermMap A B T) m1 m2 m,
    join m1 m2 m
    -> sub m1 m.
  intros.
  geat.
Qed.  

Lemma join_sub_r :
  forall (A B T:Type) (MC:PermMap A B T) m1 m2 m,
    join m1 m2 m
    -> sub m2 m.
  intros.
  geat.
Qed.  
  
Lemma join_unique :
  forall (A B T:Type) (MC:PermMap A B T) m1 m2 m m',
  join m1 m2 m ->
  join m1 m2 m' ->
  m = m'.
  intros; geat.
Qed.

Lemma join_get_get_l :
  forall (A B T:Type) (MC:PermMap A B T) m1 m2 m a b,
    usePerm = false ->
    join m1 m2 m
    -> get m1 a = Some b
    -> get m a = Some b.
  intros.
  geat.
Qed.

Lemma join_get_get_r :
  forall (A B T:Type) (MC:PermMap A B T) m1 m2 m a b,
    usePerm = false ->
    join m1 m2 m ->
    get m2 a = Some b ->
    get m a = Some b.
  intros; geat.
Qed.  

Lemma ml_eq:
  forall (A B T:Type) (MC:PermMap A B T) m1 m2,
    merge m1 m2 = merge_list (m1 :: m2 :: nil).
  intros.
  unfold merge_list.
  rewrite jl_merge_emp.
  auto.
Qed.

Hint Resolve @ml_eq: jdb1.

Lemma join_merge_disj :
  forall (A B T:Type) (MC:PermMap A B T) m1 m2,
    disjoint m1 m2 ->
    join m1 m2 (merge m1 m2).
  intros.
  geat.
  generalize (@ml_eq _ _ _ _ m1 m2).
  intros.
  rewrite H1.
  geat.
Qed.  
  
Lemma join_get_or :
  forall (A B T:Type) (MC:PermMap A B T) m1 m2 m a b,
    usePerm = false ->
    join m1 m2 m ->
    get m a = Some b ->
    (get m1 a = Some b) \/ (get m2 a = Some b).
  intros.
  destruct (get m1 a) eqn: F1;
  destruct (get m2 a) eqn: F2.
  assert (False).
  {
    eapply map_join_get_some; eauto 2.
  }
  tryfalse.
  assert (get m a = get m1 a) by jeauto.
  rewrite H1 in *.
  rewrite F1 in *.
  inversion H2.
  subst.
  left; auto.
  assert (get m a = get m2 a) by jeauto.
  rewrite H1 in *.
  rewrite F2 in *.
  inversion H2.
  subst.
  right; auto.
  assert (get m a = get m1 a) by jeauto.
  rewrite H1 in *.
  rewrite F1 in *.
  tryfalse.
Qed.  
  
Lemma join_set_l :
  forall (A B T:Type) (MC:PermMap A B T) m1 m2 m a b,
    usePerm = false ->
    join m1 m2 m
    -> indom m1 a
    -> join (set m1 a b) m2 (set m a b).
  intros.
  geat.
Qed.  
  
Lemma join_set_r :
  forall (A B T:Type) (MC:PermMap A B T) m1 m2 m a b,
    usePerm = false ->
    join m1 m2 m
    -> indom m2 a
    -> join m1 (set m2 a b) (set m a b).
  intros.
  geat.
Qed.  

Lemma disjoint_set :
  forall (A B T:Type) (MC:PermMap A B T) m1 m2 a b,
    usePerm = false ->
    disjoint (set m1 a b) m2 ->
    disjoint m1 m2.
  intros.
  apply disjoint_sem; auto.
  intros.
  generalize (disjoint_sem' H H0 t); intro.
  destruct H1; try tauto.
  destruct (map_dec_a a t); subst.
  assert (get (set m1 t b) t = Some b) by jeauto2.
  tryfalse.
  rewrite map_get_set' in H1; auto.  
Qed.

Hint Resolve @disjoint_set : jdb1.

Hint Resolve @join_disj : jdb1.

Lemma join_set_l_rev :
  forall (A B T:Type) (MC:PermMap A B T) m1 m2 m a b,
    usePerm = false ->
    join (set m1 a b) m2 m
    -> exists m', join m1 m2 m'
             /\ m = (set m' a b).
  intros.
  (* ** ac: SearchAbout disjoint. *)
  assert (disjoint (set m1 a b) m2) by jeauto2.
  apply disjoint_set in H1; auto.
  unfold disjoint in H1.
  heat.
  assert (m = (merge (set m1 a b) m2)) by jeauto2.
  assert (x = (merge m1 m2)) by jeauto2.
  subst.
  exists (merge m1 m2).
  split; auto.
  apply map_eql.
  intros.
  destruct (map_dec_a t a).
  subst.
  rewrite map_get_set.
  rewrite merge_sem.
  rewrite map_get_set.
  destruct (get m2 a); auto.
  auto.

  rewrite map_get_set'; auto.
  rewrite merge_sem.
  rewrite merge_sem.
  rewrite map_get_set'; auto.
  auto.
  auto.
Qed.  

(* ** ac: Check join_get_none_rev. *)

(******************************************************************************)
(** plist **)

(** plist has form: (pnil, _, _, _ ,_...) **)
Inductive Plist_nil : Set :=
| pnil : Plist_nil
.

Ltac plist_app l1 l2 :=
  match l2 with
    | (?l2', ?h) =>
      let l := plist_app l1 l2' in
      constr:((l, h))
    | pnil =>
      constr:(l1)
  end.

Goal forall (A B T : Type) (MC : PermMap A B T) (m1 m2 m3 m4:T),
    False.
  intros.
  let l := plist_app (pnil,m1,m2) (pnil,merge m3 m4) in
  pose l.
Abort.

Ltac plist_in l x :=
  match l with
    | (?l', x) => constr:true
    | (?l', _) => plist_in l' x
    | pnil => constr:false
    | x => constr:true
  end.

Goal forall (A B T : Type) (MC : PermMap A B T) (m1 m2 m3 m4:T) (t:A),
    False.
  intros.
  let b := plist_in (pnil, m1, m2, m3) m1 in pose b.
Abort.


Ltac plist_clear_redundant l :=
  match l with
    | (?l', ?h) =>
      let l1 := plist_clear_redundant l' in
      let b := plist_in l1 h in
      match b with
        | true => constr:(l1)
        | false => constr:(l1, h)
      end
    | pnil => constr:(pnil)
  end.

Goal forall (A B T : Type) (MC : PermMap A B T) (m1 m2 m3 m4:T) (t:A),
    False.
  intros.
  let l := plist_clear_redundant (pnil,m1, m1, m1, m1,t ,t,t, m3, merge m1 m3, m1, merge m1 m3) in pose l.
  let l := plist_clear_redundant (pnil, pnil) in pose l.
Abort.

Ltac get_context' l :=
  match goal with
    | H: ?C |- _ =>
      let b := plist_in l C in
      match b with
        | true => fail 1
        | false => get_context' (l, C)
      end
    | _ => constr:(l)
  end.

Ltac get_context :=
  get_context' pnil.

Goal forall (A B T : Type) (MC : PermMap A B T) (m1 m2 m3 m4:T) (t:A),
    join m1 m2 m3 ->
    disjoint m1 m2 ->
    sub m2 m3 ->
    False.
  intros.
  let l := get_context in pose l.
Abort.



Ltac plist_in_join l m :=
  (** find m in l, [join m1 m2 m] also indicate m in l  **)
  match l with
    | (?L, ?h) =>
      match h with
        | m => constr:(true)
        | join ?m1 ?m2 m => constr:(true)
        | _ => plist_in_join L m 
      end
    | pnil => constr:(false)
  end.

Ltac map_is_prim m :=
  match m with
    | merge _ _ => constr:(false)
    | minus _ _ => constr:(false)
    | del _ _ => constr:(false)
    | sig _ _ => constr:(false)
    | set _ _ _ => constr:(false)
    | _ => constr:(true)
  end.

Ltac plist_prim_in_join l m :=
  let b1 := map_is_prim m in
  match b1 with
    | true => plist_in_join l m
    | false => constr:(false)
  end.
  
Goal forall (A B T : Type) (MC : PermMap A B T) (m1 m2 m3 m4:T) (t:A) (v1 v2:B),
    False.
  intros.
  let l := constr:(pnil, m1, m2, join m1 m2 (merge m1 m2)) in
  let b := plist_in_join l (merge m1 m2) in
  pose b.
  let l := constr:(pnil, m1, m2, join m1 m2 (merge m1 m2)) in
  let b := plist_prim_in_join l (merge m1 m2) in
  pose b.
Abort.

Ltac plist_app_nr l1 l2 :=
  (** no redundant version of plist_app **)
  let l := plist_app l1 l2 in
  let l' := plist_clear_redundant l in
  constr:(l').

Goal forall (A B T : Type) (MC : PermMap A B T) (m1 m2 m3 m4:T) (t:A) (v1 v2:B),
    False.
  intros.
  let l1 := constr:(pnil, m1, m2) in
  let l2 := constr:(pnil, m3, m2, m1, merge m1 m2) in
  let l := plist_app_nr l1 l2 in
  pose l.
Abort.

Ltac plist_rev l :=
  match l with
    | (?L, ?h) =>
      let l' := plist_rev L in
      plist_app (pnil, h) l'
    | pnil => constr:(pnil)
  end.

Goal forall (A B T : Type) (MC : PermMap A B T) (m1 m2 m3 m4:T) (t:A) (v1 v2:B),
    False.
  intros.
  let l := constr:(pnil, m1, m2, m3, merge m1 m2, join m1 m2 m3) in
  let l' := plist_rev l in
  pose l'.
Abort.

(* ** ac: Print Ltac plist_clear_redundant. *)
Ltac plist_clear_red_join' l :=
  (** replace plist_in with plist_prim_in_join **)
  match l with
  | (?l', ?h) =>
      let l1 := plist_clear_red_join' l' in
      let b := plist_prim_in_join l1 h in
      match b with
      | true => constr:l1
      | false => constr:(l1, h)
      end
  | pnil => constr:pnil
  end.

Ltac plist_clear_red_join l :=
  let l1 := plist_clear_redundant l in
  plist_clear_red_join' l1.

Goal forall (A B T : Type) (MC : PermMap A B T) (m1 m2 m3 m4:T) (t:A) (v1 v2:B),
    False.
  intros.
  let l := constr:(pnil, m1, m2, join m1 m2 m3, m3, m1) in
  let l' := plist_clear_red_join l in
  pose l'.
  let l := constr:(pnil, m1, m2, m3,join m1 m2 m3) in
  let l' := plist_clear_red_join l in
  pose l'.
  let l := constr:(pnil, m1, m2, merge m1 m2, join m1 m2 (merge m1 m2)) in
  let l' := plist_clear_red_join l in
  pose l'.
Abort.

Ltac plist_subst l x l1 :=
  (** subst x in l with l1 **)
  match l with
    | (?L, x) =>
      plist_app L l1
    | (?L, ?h) =>
      let l' := plist_subst L x l1 in
      constr:((l', h))
    | pnil => constr:(pnil)
  end.
      
Goal forall (A B T : Type) (MC : PermMap A B T) (m1 m2 m3 m4 m11 m12:T) (t:A) (v1 v2:B),
    False.
  intros.
  let l := constr:(pnil, m1, m2, join m1 m2 m3) in
  let l' := plist_subst l m1 (pnil, m11, m12, join m11 m12 m1) in
  pose l'.
Abort.

Ltac plist_filter l f :=
  match l with
    | (?L, ?h) =>
      let b := f h in
      match b with
        | true =>
          let l' := plist_filter L f in
          constr:((l', h))
        | false => plist_filter L f
      end
    | pnil => constr:(pnil)
  end.

Ltac is_map x :=
  match x with
    | join _ _ _ => constr:(true)
    | disjoint _ _ => constr:(true)
    | sub _ _ => constr:(true)
    | _ => constr:(false)
  end.

Ltac is_join x :=
  match x with
    | join _ _ _ => constr:(true)
    | _ => constr:(false)
  end.

Goal forall (A B T : Type) (MC : PermMap A B T) (m1 m2 m3 m4 m11 m12:T) (t:A) (v1 v2:B),
    join m1 m2 m3 ->
    disjoint m1 m2 ->
    sub m1 m3 ->
    False.
  intros.
  let l := get_context in
  let l' := plist_filter l ltac:(is_map) in
  pose l'.
Abort.

Ltac get_context_map :=
  let l := get_context in
  let l' := plist_filter l ltac:(is_map) in
  constr:(l').

Ltac get_context_join :=
  let l := get_context in
  let l' := plist_filter l ltac:(is_join) in
  constr:(l').

Ltac plist_len l :=
  match l with
    | (?L, ?h) =>
      let n := plist_len L in
      constr:(S n)
    | pnil => constr:(O)
  end.

Goal forall (A B T : Type) (MC : PermMap A B T) (m1 m2 m3:T),
    False.
  intros.
  let n := plist_len (pnil, m1, m2, m3) in pose n.
  let n := plist_len (pnil, m1, m2) in
  assert (n <= 2) by auto.
Abort.

Ltac plist_elem' l n :=
  match l with
    | (?L, ?h) =>
      match n with
        | O => constr:(h)
        | S ?n' => plist_elem' L n'
      end
    | pnil => constr:(pnil)
  end.

Ltac plist_elem l n :=
  let l' := plist_rev l in
  plist_elem' l' n.

Goal forall (A B T : Type) (MC : PermMap A B T) (m1 m2 m3:T),
    False.
  intros.
  let n := plist_elem (pnil, m1, m2, m3) 3 in pose n.
Abort.

(******************************************************************************)
(** only deal with context with less then 2 join forms **)

Ltac calc_sub m :=
  match m with
    | merge ?m1 ?m2 =>
      let l1 := calc_sub m1 in
      let l2 := calc_sub m2 in
      let l := plist_app_nr l1 l2 in
      constr:((l, merge m1 m2))
    | minus ?m1 ?m2 =>
      let l1 := calc_sub m1 in
      let l2 := calc_sub m2 in
      let l := plist_app_nr l1 l2 in
      constr:((l, minus m1 m2))
    | set ?m1 ?t1 ?v =>
      let l1 := calc_sub m1 in
      constr:((l1, set m1 t1 v))
    | del ?m1 ?t1 =>
      let l1 := calc_sub m1 in
      constr:((l1, del m1 t1))
    | sig ?t1 ?v =>
      constr:((pnil, sig t1 v))
    | _ =>
      constr:((pnil,m))
  end.         

Goal forall (A B T : Type) (MC : PermMap A B T) (m1 m2 m3 m4:T) (t:A) (v1 v2:B),
    join m1 m2 m3 ->
    disjoint m1 m2 ->
    sub m2 m3 ->
    False.
  intros.
  let l := calc_sub (merge m1 m2) in pose l.
  let l := calc_sub (merge (set m1 t v1) (set m2 t v2)) in pose l.
  let l := calc_sub (minus (merge m1 m2) (merge m1 m3)) in pose l.
Abort.

(* ** ac: Print Ltac plist_subst. *)

Ltac calc_dep m :=
  match m with
    | join ?m1 ?m2 ?m3 =>
      let l1 := calc_sub m1 in
      let l2 := calc_sub m2 in
      let l3 := calc_sub m3 in
      let l := plist_app_nr l1 l2 in
      let l' := plist_app_nr l l3 in
      match l' with
        | (?l'', m3) =>
          let b := map_is_prim m3 in
          match b with
            | true =>
              let l'' := plist_app l'' (pnil, join m1 m2 m3) in
              constr:(l'')
            | false =>
              let l'' := plist_app l'' (pnil, m3, join m1 m2 m3) in
              constr:(l'')
          end
      end
    | disjoint ?m1 ?m2 =>
      let l1 := calc_sub m1 in
      let l2 := calc_sub m2 in
      let l3 := plist_app_nr l1 l2 in
      constr:((l3, disjoint m1 m2))
    | sub ?m1 ?m2 =>
      let l1 := calc_sub m1 in
      let l2 := calc_sub m2 in
      let l3 := plist_app_nr l1 l2 in
      constr:((l3, sub m1 m2))
  end.

Goal forall (A B T : Type) (MC : PermMap A B T) (m1 m2 M m3 m4:T),
    usePerm = true ->
    sub m3 M ->
    join m1 m2 (minus M m3) ->
    join m2 m3 m4 ->
    join m1 m4 M.
  intros.
  let l := calc_dep (join m1 m2 (minus M m3)) in pose l.
  let l := calc_dep (join m1 m2 m3) in pose l.
Abort.

  
Goal forall (A B T : Type) (MC : PermMap A B T) (m1 m2 m3 m4 m5:T) (t:A) (v1 v2:B),
    join m1 m2 m3 ->
    disjoint m1 m2 ->
    sub m2 m3 ->
    False.
  intros.
  let l := calc_dep (join (merge m1 m2) (merge m3 m4) m5) in pose l.
  let l := calc_dep (join m1 m2 m3) in pose l.
  let l := calc_dep (join m4 m5 m1) in pose l.
  let l := calc_dep (sub m1 m2) in pose l.
  let l := calc_dep (disjoint m1 m2) in pose l.
Abort.

(* ** ac: Print Ltac plist_in. *)

Ltac calc_less l1 l2 :=
  match l1 with
    | (?L1, join ?m1 ?m2 ?m3) =>
      let b := plist_in l2 m3 in
      constr:(b)
  end.

Goal forall (A B T : Type) (MC : PermMap A B T) (m1 m2 m3 m4 m5 m6:T) (t:A) (v1 v2:B),
    join m1 m2 m3 ->
    disjoint m1 m2 ->
    sub m2 m3 ->
    False.
  intros.
  let l1 := calc_dep (join (merge m1 m6) m2 m3) in
  let l2 := calc_dep (join m4 m5 m1) in
  let b := calc_less l2 l1 in
  pose b.
Abort.

Ltac plist_mv_to_end l x :=
  let l1 := plist_subst l x pnil in
  let l2 := constr:((l1, x)) in
  constr:(l2).

Goal forall (A B T : Type) (MC : PermMap A B T) (m1 m2 m3 m4 m5 m6:T) (t:A) (v1 v2:B),
    join m1 m2 m3 ->
    disjoint m1 m2 ->
    sub m2 m3 ->
    False.
  intros.
  let l1 := calc_dep (join (merge m1 m6) m2 m3) in 
  let l2 := plist_mv_to_end l1 (merge m1 m6) in
  pose l1; pose l2.
Abort.


Ltac plist_is_biggest l f x :=
  match l with
    | (?L, x) =>
      plist_is_biggest L f x
    | (?L, ?h) =>
      let b := f x h in
      match b with
        | true => constr:(false)
        | false => plist_is_biggest L f x
      end
    | pnil => constr:(true)
  end.

Ltac plist_find_biggest' l f l1 :=
  match l1 with
    | (?L1, ?h1) =>
      let b := plist_is_biggest l f h1 in
      match b with
        | true => constr:(h1)
        | false => plist_find_biggest' l f L1
      end
  end.
          
Ltac plist_find_biggest l f :=
  plist_find_biggest' l f l.

Ltac plist_map l f :=
  match l with
    | (?L, ?h) =>
      let l' := f h in
      let l'' := plist_map L f in
      constr:((l'', l'))
    | pnil => pnil
  end.

Ltac calc_all_dep_of_join :=
  let l := get_context_join in
  let l' := plist_map l ltac:(calc_dep) in
  constr:(l').

Goal forall (A B T : Type) (MC : PermMap A B T) (m1 m2 m3 m4 m5 m6 m41 m42 :T) (t:A) (v1 v2:B),
    join m1 m2 m3 ->
    join m4 m5 m1 ->
    join m41 m42 m4 ->
    disjoint m1 m2 ->
    sub m2 m3 ->
    False.
  intros.
  let l1 := calc_all_dep_of_join in
  let b := plist_is_biggest l1 ltac:(calc_less) (pnil, m1, m2, join m1 m2 m3) in 
  pose l1; pose b.

  let l1 := calc_all_dep_of_join in 
  let l2 := plist_find_biggest l1 ltac:(calc_less) in
  pose l1; pose l2.
Abort.

Ltac calc_sort ll f :=
  match ll with
    | pnil => pnil
    | _ => 
      let l1 := plist_find_biggest ll f in
      let ll1 := plist_mv_to_end ll l1 in
      match ll1 with
        | (?L, ?h) =>
          let ll2 := calc_sort L f in
          constr:((ll2, h))
      end
  end.

Goal forall (A B T : Type) (MC : PermMap A B T) (m1 m2 m3 m4 m5 m6 m41 m42 :T) (t:A) (v1 v2:B),
    join m41 m42 m4 ->
    join m1 m2 m3 ->
    join m4 m5 m1 ->
    disjoint m1 m2 ->
    sub m2 m3 ->
    False.
  intros.
  let l1 := calc_all_dep_of_join in
  let l2 := calc_sort l1 ltac:(calc_less) in
  pose l1; pose l2.
Abort.

Goal forall (A B T : Type) (MC : PermMap A B T) (m1 m2 M m3 m4:T),
    usePerm = true ->
    sub m3 M ->
    join m1 m2 (minus M m3) ->
    join m2 m3 m4 ->
    join m1 m4 M.
  intros.
  let l1 := calc_all_dep_of_join in pose l1.
  
Abort.
  
Ltac plist_foldl l f res :=
  match l with
    | pnil => constr:(res)
    | (?L, ?h) =>
      let x := plist_foldl L f res in
      let y := f x h in
      constr:(y)
  end.

Ltac calc_ins_for_join :=
  let l1 := calc_all_dep_of_join in
  let l2 := calc_sort l1 ltac:(calc_less) in
  let l3 := plist_foldl l2 ltac:(plist_app_nr) pnil in
  let l4 := plist_clear_red_join l3 in 
  constr:(l4).

Goal forall (A B T : Type) (MC : PermMap A B T) (m1 m2 m3 m4 m5 m6 m41 m42 :T) (t:A) (v1 v2:B),
    join m1 m2 m3 ->
    join m4 m5 m1 ->
    join m41 m42 m4 ->
    disjoint m1 m2 ->
    sub m2 m3 ->
    False.
  intros.
  let l1 := calc_all_dep_of_join in
  let l2 := calc_sort l1 ltac:(calc_less) in
  pose l2.
  let l:= calc_ins_for_join in pose l.
Abort.


Ltac is_map_not_join x :=
  match x with
    | disjoint _ _ => constr:(true)
    | sub _ _ => constr:(true)
    | _ => constr:(false)
  end.

Ltac get_context_other :=
  let l := get_context in
  let l' := plist_filter l ltac:(is_map_not_join) in
  constr:(l').

Goal forall (A B T : Type) (MC : PermMap A B T) (m1 m2 m3 m4 m5 m6 m41 m42 :T) (t:A) (v1 v2:B),
    join m1 m2 m3 ->
    join m4 m5 m1 ->
    join m41 m42 m4 ->
    disjoint m1 m2 ->
    sub m2 m3 ->
    False.
  intros.
  let l := get_context_other in
  pose l.
Abort.

Ltac calc_ins_for_other :=
  let l1 := get_context_other in
  let l2 := plist_map l1 ltac:(calc_dep) in
  let l3 := plist_foldl l2 ltac:(plist_app) pnil in
  let l4 := plist_clear_red_join l3 in
  constr:(l4).

Goal forall (A B T : Type) (MC : PermMap A B T) (m1 m2 m3 m4 m5 m6 m41 m42 :T) (t:A) (v1 v2:B),
    join m1 m2 m3 ->
    join m4 m5 m1 ->
    join m41 m42 m4 ->
    disjoint (merge m1 m2) (merge m3 m4) ->
    disjoint m1 m2 ->
    sub m2 m3 ->
    False.
  intros.
  let l := calc_ins_for_other in pose l.
Abort.

Ltac calc_ins_for_context :=
  let l1 := calc_ins_for_join in
  let l2 := calc_ins_for_other in
  let l3 := plist_app l1 l2 in
  let l4 := plist_clear_red_join l3 in
  constr:(l4).

Goal forall (A B T : Type) (MC : PermMap A B T) (m1 m2 m3 m4 m5 m6 m41 m42 :T) (t:A) (v1 v2:B),
    join m1 m2 m3 ->
    join m4 m5 m1 ->
    join m41 m42 m4 ->
    sub (merge m1 m2) m6 ->
    False.
  intros.
  let l := calc_ins_for_context in
  pose l.
Abort.

Ltac get_term_of_goal' t :=
  match t with
    | join ?m1 ?m2 ?m3 =>
      constr:((pnil, m1, m2, m3))
    | disjoint ?m1 ?m2 =>
      constr:((pnil, m1, m2))
    | sub ?m1 ?m2 =>
      constr:((pnil, m1, m2))
    | get ?x ?t = get ?y ?t =>
      constr:((pnil, x, y))
    | get ?x ?t = _ =>
      constr:((pnil, x))
    | _ = get ?x ?t =>
      constr:((pnil, x))
    | ?x = ?y =>
      constr:((pnil, x, y))
    | ?m1 /\ ?m2 =>
      let l1 := get_term_of_goal' m1 in
      let l2 := get_term_of_goal' m2 in
      let l3 := plist_app_nr l1 l2 in
      constr:(l3)
    | _ => constr:(pnil)
  end.

Ltac get_term_of_goal :=
  match goal with
    | |- ?t => get_term_of_goal' t
  end.
          
Goal forall (A B T : Type) (MC : PermMap A B T) (m1 m2 m3 m4 m5 m6 m41 m42 :T) (t:A) (v1 v2:B),
    sub (merge m1 m2) m6 /\ disjoint m1 m2.
  intros.
  let l := get_term_of_goal in pose l.
Abort.

Ltac calc_ins_for_goal :=
  let l1 := get_term_of_goal in
  let l2 := plist_map l1 ltac:(calc_sub) in
  let l3 := plist_foldl l2 ltac:(plist_app) pnil in
  let l4 := plist_clear_redundant l3 in
  constr:(l4).

Goal forall (A B T : Type) (MC : PermMap A B T) (m1 m2 m3 m4 m5 m6 m41 m42 :T) (t:A) (v1 v2:B),
    sub (merge m1 m2) m6 /\ disjoint m1 m2.
  intros.
  let l := calc_ins_for_goal in pose l.
Abort.

Ltac calc_ins :=
  let l1 := calc_ins_for_context in
  let l2 := calc_ins_for_goal in
  let l3 := plist_app l1 l2 in
  let l4 := plist_clear_red_join l3 in
  constr:(l4).

Goal forall (A B T : Type) (MC : PermMap A B T) m1 m2 m12 m3 m123 m4 m1234,
    join m1 m2 m12 ->
    join m12 m3 m123 ->
    join m123 m4 m1234 ->
    join (merge (merge m1 m2) m3) m4 m1234.
  intros.
  let l := calc_ins in
  pose l.
Abort.

Goal forall (A B T : Type) (MC : PermMap A B T) (m1 m2 M m3 m4:T),
    usePerm = true ->
    sub m3 M ->
    join m1 m2 (minus M m3) ->
    join m2 m3 m4 ->
    join m1 m4 M.
  intros.
  let l := calc_ins in pose l.
Abort.

Ltac plist_minus l l1 :=
  match l with
    | (?L, ?h) =>
      let b := plist_in l1 h in
      match b with
        | true => plist_minus L l1
        | false =>
          let l' := plist_minus L l1 in
          constr:((l',h))
      end
    | pnil => constr:(pnil)
  end.

Goal
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 m4 M,
    usePerm = true ->
    Maps.sub m1 M ->
    Maps.sub m2 M ->
    Maps.sub (merge m1 m2) M ->
    join m1 m2 (minus M m4) ->
    disjoint m1 m2 ->
    join m3 m4 m1 ->
    join m3 (minus (minus (minus M m4) m3) m2) (minus (minus M m4) m2).
  intros.
  let l1 := calc_ins in
  let l2 := calc_ins_for_context in
  pose l1;
  pose l2;
  let l3 := plist_minus l1 l2 in
  pose l3.
Abort.

(******************************************************************************)
Ltac interpret ins t' ::=
  match ins with
    (* | usePerm => *)
    (*   let H := fresh in *)
    (*   destruct (usePerm) eqn:H *)
    | (sig ?t ?v) =>
      infer_sig (sig t v) t'
    | (set ?m ?t ?v) =>
      infer_set (set m t v) t'
    | (del ?m ?t) =>
      infer_del (del m t) t'
    | (sub ?m1 ?m) =>
      infer_sub m1 m t'
    | join ?x ?y ?z =>
      infer_join x y z t'
    | merge ?x ?y =>
      infer_merge x y t'
    | disjoint ?x ?y =>
      infer_disjoint x y t'
    | minus ?x ?y =>
      infer_minus x y t'
    | ?m =>
      let H:= fresh in
      destruct (get m t') eqn:H
  end.

Ltac infer' ls t :=
     match ls with
       | (?ls', ?ins) =>
         infer' ls' t;
         interpret ins t
       | pnil => idtac
     end.

Ltac infer ls t ::=
     let ic := calc_ins_for_context in
     let ig := plist_minus ls ic in
     let ic' := plist_minus ls ig in
     infer' ic' t; (** infer context first, and then cut out all false case **)
     try (solve [crush]);
     infer' ig t.

(******************************************************************************)
(** hy tactics **)

Ltac des_usePerm :=
  let Hn := fresh in
  match goal with
    | H: usePerm = _ |- _ => idtac
    | _ => destruct (usePerm) eqn:Hn
  end.

Ltac indom_rewrite :=
  repeat match goal with
           | H: indom ?m ?a |- _ =>
             apply indom_get in H;
             destruct H
           | H: ~ indom ?m ?a |- _ =>
             apply nindom_get in H
         end.

Ltac hy_pre :=
  try intros;
  (* indom_rewrite; *)
  des_usePerm.


Ltac hy_disjoint ls t ::=
  match goal with
    | Hn : usePerm = true |- disjoint ?x ?y =>
      apply disjoint_semp; auto 1; intro t;
      infer ls t
    | Hn : usePerm = false |- disjoint ?x ?y =>
      apply disjoint_sem; auto 1; intro t;
      infer ls t
  end.

Ltac hy_eql ls t ::=
  match goal with
    | |- ?a = ?b =>
      apply map_eql;
      intro t;
      infer ls t
  end.

Ltac hy_join ls t ::=
  match goal with
    | |- join ?x ?y ?z =>
      apply join_sem;
      [ hy_disjoint ls t
      | let ls' := constr:(pair ls (merge x y)) in
        hy_eql ls' t]
  end.

Ltac hy_sub ls t ::=
  match goal with
    | Hn : usePerm = true |- sub ?x ?y =>
      apply sub_semp; auto 1; intro t;
      infer ls t
    | Hn : usePerm = false |- sub ?x ?y =>
      apply sub_sem; auto 1; intro t; intros;
      infer ls t
  end.

Ltac hy :=
  hy_pre;
  (let ins := calc_ins in
   let t := fresh in
   match goal with
     | |- join _ _ _ => hy_join ins t
     | |- disjoint _ _ => hy_disjoint ins t
     | |- sub _ _ => hy_sub ins t
     | |- get ?x ?t1 = _ => infer ins t1
     | |- _ = get ?x ?t1 => infer ins t1
     | |- _ = _ => hy_eql ins t
     | |- _ => infer ins t
   end; crush).

(******************************************************************************)

Lemma join_set_nindom_l :
  forall (A B T:Type) (MC:PermMap A B T) m1 m2 m m1' m' l v,
    join m1 m2 m ->
    m1' = set m1 l v ->
    m' = set m l v ->
    ~indom m l ->
    join m1' m2 m'.
  intros.
  indom_rewrite.
  subst.
  hy.
Qed.

Hint Resolve @join_set_nindom_l : jdb1.

Lemma join_set_nindom_r :
  forall (A B T:Type) (MC:PermMap A B T) m1 m2 m m2' m' l v, join m1 m2 m ->
    m2' = set m2 l v ->
    m' = set m l v ->
    ~indom m l ->
    join m1 m2' m'.
  intros.
  apply join_comm.
  jeauto2.
Qed.  

Hint Resolve @join_set_nindom_r : jdb1.

Lemma join_emp :
  forall (A B T:Type) (MC:PermMap A B T) m m',
    m = m' ->
    join emp m m'.
  intros; geat.
Qed.

Hint Resolve @join_emp : jdb1.

(* ** ac: Check join_sig_set. *)
(* ** ac: Locate join_sig_set. *)

Lemma join_sig_set' : 
  forall (A B T:Type) (MC:PermMap A B T) m a b,
    ~indom m a ->
    join m (sig a b) (set m a b).
  intros.
  assert (join m emp m) by jeauto2.
  assert (sig a b = (set emp a b)) by jeauto2.
  rewrite H1.
  jeauto2.
Qed.  

Hint Resolve @join_sig_set'.

Lemma join_unique_r :
  forall (A B T:Type) (MC:PermMap A B T) m1 m2 m2' m,
  join m1 m2 m ->
  join m1 m2' m ->
  m2 = m2'.
  intros.
  jeauto2.
Qed.

Lemma join_emp_eq :
  forall (A B T:Type) (MC:PermMap A B T) m m',
  join emp m m' -> m = m'.
  intros; geat.
Qed.
  
Lemma sub_exists_join :
  forall (A B T:Type) (MC:PermMap A B T) m1 m,
    sub m1 m ->
    exists m2, join m1 m2 m.
  intros.
  geat.
Qed.
  
Lemma join_sub_minus : forall (A B T:Type) (MC:PermMap A B T) m m1,
    sub m1 m
    -> join m1 (minus m m1) m.
  intros.
  jeauto2.
Qed.

(* ** ac: Check map_join_getp_some. *)

  
Lemma join_sub_sub : forall (A B T:Type) (MC:PermMap A B T) m1 m2 m m',
    usePerm = false ->
    join m1 m2 m 
  -> sub m1 m'
  -> sub m2 m'
  -> sub m m'.
  intros.
  hy.
Qed.

Hint Resolve @join_sub_sub : jdb1.

Lemma join_sig_get : forall (A B T:Type) (MC:PermMap A B T) a x m1 m2,
    usePerm = false ->
    join (sig a x) m1 m2 -> get m2 a = Some x.
  intros.
  geat.
Qed.  

Lemma  join_joinsig_get : forall (A B T:Type) (MC:PermMap A B T) v'24 v'25 v'16 x8 x13 x12 ,
    usePerm = false ->
    join v'24 v'25 v'16 -> joinsig x8 x13 x12 v'25 -> 
    get v'16 x8 = Some x13.
  intros.
  geat.
Qed.  


Lemma joinsig_set : 
  forall (A B T:Type) (MC:PermMap A B T) x8 x13 x12 v'25 v,
      usePerm = false ->
      joinsig x8 x13 x12 v'25 ->  
      joinsig x8 v x12 (set v'25 x8 v).
  intros.
  geat.
Qed.  

Lemma  joinsig_set_set : forall (A B T:Type) (MC:PermMap A B T) x8 x13 x12  v'24 v'25 v'16 v,
    usePerm = false ->
    joinsig x8 x13 x12 v'25 ->
    join v'24 v'25 v'16 -> 
    join v'24 (set v'25 x8 v) (set v'16 x8 v).
  intros.
  geat.
Qed.  

Lemma disj_set_disj_1 : forall (A B T:Type) (MC:PermMap A B T) M1 M2 x v v',
    usePerm = false ->
    disjoint M1 M2 -> get M1 x = Some v -> disjoint (set M1 x v') M2.
  hy.
Qed.

Hint Resolve @disj_set_disj_1 : jdb1.
Hint Resolve @disjoint_sym : jdb1.

Lemma disj_set_disj_2 : forall (A B T:Type) (MC:PermMap A B T) M1 M2 x v v',
    usePerm = false ->
    disjoint M1 M2 -> get M2 x = Some v -> disjoint M1 (set M2 x v').
  intros.
  apply disjoint_sym.
  apply disjoint_sym in H0.
  jeauto2.
Qed.

Hint Resolve @disj_set_disj_2 : jdb1.

Lemma merge_set_eq_1 : forall (A B T:Type) (MC:PermMap A B T) M1 M2 x v,
    usePerm = false ->
    merge (set M1 x v) M2 = set (merge M1 M2) x v.
  hy.
Qed.

Hint Resolve @merge_set_eq_1 : jdb1.
  
Lemma merge_set_eq_2 : forall (A B T:Type) (MC:PermMap A B T) M1 M2 x v v',
    usePerm = false ->
    disjoint M1 M2 -> get M2 x = Some v ->
    merge M1 (set M2 x v') = set (merge M1 M2) x v'.
  intros.
  (* ** ac: SearchAbout disjoint. *)
  assert (disjoint M1 (set M2 x v')) by jeauto2.
  Hint Resolve @map_merge_comm : jdb1.
  assert (merge M1 (set M2 x v') = merge (set M2 x v') M1) by jeauto2.
  rewrite H3.
  assert (merge M1 M2 = merge M2 M1) by jeauto2.
  rewrite H4.
  jeauto2.
Qed.    

Lemma join_shift_l : forall (A B T:Type) (MC:PermMap A B T) m1 m2 m3 mx a v,
    usePerm = false ->
    join m1 m2 m3 -> joinsig a v mx m2 -> join (merge m1 (sig a v)) mx m3.
  intros.
  geat.
  rewrite ml_eq.
  geat.
Qed.

Lemma joinsig_merge_sig : forall (A B T:Type) (MC:PermMap A B T) a1 v1 m1 m2 a2 v2,
    usePerm = false ->
    joinsig a1 v1 m1 m2 -> a1 <> a2 ->
    joinsig a1 v1 (merge m1 (sig a2 v2)) (merge m2 (sig a2 v2)).
  unfold joinsig.
  hy.
Qed.

Lemma eqdom_merge_set : forall (A B T:Type) (MC:PermMap A B T) O Of x v v',
    usePerm = false ->
    get O x = Some v -> eqdom (merge O Of) (merge (set O x v') Of).
  unfold eqdom.
  unfold indom.
  intros.
  split; intros; heat;
  destruct (get (set O x v') x0) eqn: F1;
  destruct (get O x0) eqn: F2;
  destruct (get Of x0) eqn: F3;
  infer_merge O Of x0; tryfalse;
  infer_merge (set O x v') Of x0;
  destruct (map_dec_a x x0);
  subst;
  (try (rewrite map_get_set in F1));
  (try (rewrite map_get_set' in F1; auto 1));
  tryfalse; 
  subst_get; crush ; eauto 2.
Qed.

Lemma disj_trans_sub:
  forall (A B T:Type) (MC:PermMap A B T) m1 m2 m3,
    sub m1 m2 ->
    disjoint m3 m2 ->
    disjoint m3 m1.
  hy.
Qed.

Lemma join_assoc:
  forall (A B T:Type) (MC:PermMap A B T) ma mb mc mab mbc mabc,
    join ma mb mab ->
    join mab mc mabc ->
    join mb mc mbc ->
    join ma mbc mabc.
  intros; geat.
Qed.  
  
Lemma join_assoc_spec_1:
  forall (A B T:Type) (MC:PermMap A B T) ma mb mc mab mabc,
    join ma mb mab ->
    join mc mab mabc ->
    exists mac, join mc ma mac /\
           join mac mb mabc.
  intros; geat.
Qed.
  
Lemma my_joinsig_join_set:
  forall (A B T:Type) (MC:PermMap A B T) x1 v1 v2 ma mb mb' mab,
    usePerm = false ->
    joinsig x1 v1 mb' mb ->
    join ma mb mab ->
    join ma (set mb x1 v2) (set mab x1 v2).
  intros; geat.
Qed.
  
Lemma join_join_disj_r:
  forall (A B T:Type) (MC:PermMap A B T) ma mb mab mc mabc,
    join ma mb mab ->
    join mab mc mabc ->
    disjoint mb mc.
  intros; geat.
Qed.

Lemma join_join_disj_l:
  forall (A B T:Type) (MC:PermMap A B T) ma mb mab mc mabc,
    join ma mb mab ->
    join mab mc mabc ->
    disjoint ma mc.
  intros; geat.
Qed.
  
Lemma join_whole2part:
  forall (A B T:Type) (MC:PermMap A B T) ma mb mab mc mabc,
    join ma mb mab ->
    join mab mc mabc ->
    join mb mc (merge mb mc).
  intros; geat.
  (* ** ac: SearchAbout merge_list. *)
  rewrite (ml_eq).
  geat.
Qed.  

Lemma my_join_sig_abc:
  forall (A B T:Type) (MC:PermMap A B T) ma mb mc mc' x1 v1 v2 mbc mabc,
    usePerm = false -> (** usePerm = true is not valid **)
    join mb mc mbc ->
    join ma mbc mabc ->
    joinsig x1 v1 mc' mc ->
    join ma (set mbc x1 v2)
            (set mabc x1 v2).
  intros; geat.
Qed.  

Lemma my_joinsig_set:
  forall (A B T:Type) (MC:PermMap A B T) x1 v1 v2 m' m,
    usePerm = false ->
    joinsig x1 v1 m' m ->
    joinsig x1 v2 m' (set m x1 v2).
  intros; geat.
Qed.
  
Lemma join_get_r:
  forall (A B T:Type) (MC:PermMap A B T) ma mb mab x1 v1,
    usePerm = false ->
    join ma mb mab ->
    get mb x1 = Some v1 ->
    get mab x1 = Some v1.
  intros; geat.
Qed.  
  
Lemma join_get_l:
  forall (A B T:Type) (MC:PermMap A B T) ma mb mab x1 v1,
    usePerm = false ->
    join ma mb mab ->
    get ma x1 = Some v1 ->
    get mab x1 = Some v1.
  intros; geat.
Qed.
  
Lemma disj_get_neq:
  forall (A B T:Type) (MC:PermMap A B T) ma mb x1 v1 x2 v2,
    usePerm = false ->
    disjoint ma mb ->
    get ma x1 = Some v1 ->
    get mb x2 = Some v2 ->
    x1 <> x2.
  intros.
  assert (disjoint mb ma) by jeauto2.
  destruct (map_dec_a x1 x2); subst; auto.
  infer_disjoint mb ma x2;
  crush.
Qed.  

Hint Resolve @disj_get_neq : jdb1.

Lemma my_join_disj:
  forall (A B T:Type) (MC:PermMap A B T) ma mb mab,
    join ma mb mab ->
    disjoint ma mb.
  intros; geat.
Qed.

Lemma join_get_get_neq:
  forall (A B T:Type) (MC:PermMap A B T) ma mb mab x1 v1 x2 v2,
    usePerm = false ->
    join ma mb mab ->
    get ma x1 = Some v1 ->
    get mb x2 = Some v2 ->
    x1 <> x2.
  intros.
  assert (disjoint ma mb) by jeauto2.
  jeauto2.
Qed.

Hint Resolve @join_get_get_neq : jdb1.

(****************************************************************)
(************************added by xfw****************************)
(****************************************************************)

(* ** ac: Check map_get_set. *)
(* ** ac: Check map_get_set'. *)


 Lemma disj_disj_set_disj:
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m a v v',
    usePerm = true ->
    isRw v = true ->
    disjoint m1 m ->
    disjoint m2 m ->
    get m2 a = Some v ->
    disjoint (set m1 a v') m.
Proof.
  hy.
Qed.

Lemma disj_disj_set_disj':
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m a v v',
    usePerm = true ->
    isRw v = true ->
    disjoint m m1 ->
    disjoint m m2->
    get m2 a = Some v ->
    disjoint m (set m1 a v').
Proof.
  intros.
  apply disjoint_sym.
  eapply disj_disj_set_disj; jeauto2.
Qed.

Lemma sub_set_sub:
  forall (A B T : Type) (MC : PermMap A B T) (m m': T) (a:A) (b:B),
    Maps.sub m m' ->
    Maps.sub (Maps.set m a b) (Maps.set m' a b).
Proof.
  hy.
Qed.

Hint Resolve @sub_set_sub : jdb1.

Lemma get_disj_sub_set:
  forall (A B T : Type) (MC : PermMap A B T) m' m M v v' a,
    usePerm = true ->
    isRw v = true ->
    get m' a = Some v ->
    disjoint m m' ->
    Maps.sub m M ->
    Maps.sub m (set M a v').
Proof.
  hy.
Qed.  

Lemma join_join_join_merge:
  forall (A B T : Type) (MC : PermMap A B T) Ml Ms M Ml' Ms',
    join Ml Ms M -> join Ml' Ms' Ms -> join (merge Ml Ml') Ms' M.
Proof.
  intros.
  rewrite ml_eq.
  geat.
Qed.

Lemma join_join_minus:
  forall  (A B T : Type) (MC : PermMap A B T) M1 M2 M11 M12 M,
    join M1 M2 M ->
    join M11 M12 M1 ->
    join (minus M M12) M12 M.
Proof.
  (* ** ac: SearchAbout minus. *)
  intros.
  assert (sub M12 M) by geat.
  apply join_comm.
  jeauto2.
Qed.

Hint Resolve @join_join_minus : jdb1.

Lemma sub_minus:
  forall  (A B T : Type) (MC : PermMap A B T) x y z,
    join x y z ->
    sub x (minus z y).
  hy.
Qed.

Hint Resolve @sub_minus : jdb1.  


Lemma join_join_sub_minus:
  forall  (A B T : Type) (MC : PermMap A B T) M1 M2 M11 M12 M,
    join M1 M2 M ->
    join M11 M12 M1 ->
    Maps.sub M11 (minus M M12).
Proof.
  hy.
Qed.

Lemma minus_sub
: forall  (A B T : Type) (MC : PermMap A B T) M1 M M2,
    usePerm = false -> (** true is not valid **)
    Maps.sub M1 M ->
    disjoint M1 M2 -> Maps.sub M1 (minus M M2).
Proof.
  hy.
Qed.

Lemma join_join_sub_sub_minus:
  forall (A B T : Type) (MC : PermMap A B T) M1 M2 M11 M12 M m,
    join M1 M2 M ->
    join M11 M12 M1 ->
    Maps.sub m M2 ->
    Maps.sub m (minus M M12).
Proof.
  hy.
Qed.

Lemma join_join_sub_disj:
  forall (A B T : Type) (MC : PermMap A B T) M1 M2 M11 M12 M m,
    join M1 M2 M ->
    join M11 M12 M1 ->
    Maps.sub m M2 ->
    disjoint m M11.
Proof.
  hy.
Qed.  


Lemma join_merge_minus:
  forall (A B T : Type) (MC : PermMap A B T) M1 M2 M m,
    join M1 M2 M ->
    Maps.sub m M1 ->
    join (merge m M2) (minus M1 m) M.
Proof.
  hy.
Qed.

(******************************************************************************)
(** from perm_map_lemmas **)

Hint Resolve @join_sem' : jdb1.
Lemma join_disjoint_eq_merge :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3,
    join m1 m2 m3 ->
    disjoint m1 m2 /\ m3 = merge m1 m2.
Proof.
  intros.
  jeauto2.
Qed.  

Hint Resolve @join_disjoint_eq_merge : jdb1.

Lemma join_merge23_join :
  forall {A B T:Type} {MC:PermMap A B T} m1 m2 m12 m3 m123,
    usePerm = false ->
    join m1 m2 m12 ->
    join m12 m3 m123 ->
    join m1 (merge m2 m3) m123.
Proof.
  intros.
  rewrite ml_eq.
  geat.
Qed.  

Hint Resolve @join_merge23_join : jdb1.

Lemma join_join_merge12_join :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m12 m3 m123,
    join m1 m2 m12 ->
    join m12 m3 m123 ->
    join (merge m1 m2) m3 m123.
Proof.
  intros.
  rewrite ml_eq.
  geat.
Qed.  

Hint Resolve @join_join_merge12_join : jdb1.

Lemma join_join_merge23_join :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m12 m3 m123,
    join m1 m2 m12 ->
    join m12 m3 m123 ->
    join m1 (merge m2 m3) m123.
Proof.
  intros.
  rewrite ml_eq.
  geat.
Qed.  

Hint Resolve @join_join_merge23_join : jdb1.

Lemma join_get_get_lp :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 a v,
    usePerm = true ->
    join m1 m2 m3 ->
    get m1 a = Some v ->
    exists v', get m3 a = Some v' /\ sameV v v'.
Proof.
  intros.
  destruct (get m2 a) eqn:F;
  infer_join m1 m2 m3 a;
  eexists; split; jeauto2.
Qed.  

Hint Resolve @join_get_get_lp : jdb1.

Lemma join_get_get_l_true :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 a b,
    usePerm = true ->
    join m1 m2 m3 ->
    get m1 a = Some b ->
    isRw b = true ->
    get m3 a = Some b.
Proof.
  hy.
Qed.

Hint Resolve @join_get_get_l_true : jdb1.

Lemma join_join_disjoint :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m12 m3 m123,
    join m1 m2 m12 ->
    join m12 m3 m123 ->
    disjoint m1 m3.
Proof.
  intros.
  geat.
Qed.  

Hint Resolve @join_join_disjoint : jdb1.

Lemma join_merge_rearange :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m12 m3 m123 m4 m1234,
    join m1 m2 m12 ->
    join m12 m3 m123 ->
    join m123 m4 m1234 ->
    join (merge m1 m3) (merge m2 m4) m1234.
Proof.
  intros.
  rewrite ml_eq.
  rewrite ml_eq.
  geat.
Qed.

Hint Resolve @join_merge_rearange : jdb1.

Lemma join_join_join_merge' :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m12 m3 m123 m4 m1234,
    join m1 m2 m12 ->
    join m12 m3 m123 ->
    join m123 m4 m1234 ->
    join m1 m4 (merge m1 m4).
Proof.
  intros.
  rewrite ml_eq.
  geat.
Qed.  

Hint Resolve @join_join_join_merge' : jdb1.

Lemma join_disjoint_disjoint :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m12 m3,
    join m1 m2 m12 ->
    disjoint m12 m3 ->
    disjoint m1 m3.
Proof.
  intros.
  geat.
Qed.  

Hint Resolve @join_disjoint_disjoint : jdb1.

Lemma disjoint_merge_disjoint :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 m123,
    join m1 (merge m2 m3) m123 ->
    disjoint m2 m3 ->
    disjoint m1 m2.
Proof.
  hy.
Qed.

Lemma join_merge_disjoint :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 m4,
    join m1 (merge m2 m3) m4 ->
    disjoint m2 m3 ->
    join (merge m1 m2) m3 m4.
Proof.
  intros.
  let l:= calc_ins in pose l.
  hy.
Qed.

Lemma get_join_getp :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 a v,
    usePerm = true ->
    join m1 m2 m3 ->
    get m3 a = Some v ->
    isRw v = true ->
    get m2 a = None ->
    get m1 a = Some v.
Proof.
  hy.
Qed.  

Lemma get_join_sig_del :
  forall (A B T : Type) (MC : PermMap A B T) m a b,
    usePerm = true ->
    get m a = Some b ->
    isRw b = true ->
    join (sig a b) (del m a) m.
Proof.
  hy.
Qed.  
    
(*hard*)
Lemma get_join_join_del_exists :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 a b,
    usePerm = true ->
    get m3 a = Some b ->
    isRw b = true ->
    join m1 m2 m3 ->
    exists m2', join (del m1 a) m2' m3.
Proof.
  intros.
  assert (sub (del m1 a) m3).
  {
    hy.
  }
  auto 1.
Qed.    

Lemma join_get_get_r_true :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 a b,
    usePerm = true ->
    join m1 m2 m3 ->
    get m2 a = Some b ->
    isRw b = true ->
    get m3 a = Some b.
Proof.
  hy.
Qed.

Lemma join_true_del :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 a x,
    usePerm = true ->
    isRw x = true ->
    join m1 (sig a x) m2 ->
    m1 = del m2 a.
Proof.
  hy.
Qed.

Lemma join_set_true_comm :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 a x,
    usePerm = true ->
    get m1 a = None ->
    get m2 a = None ->
    isRw x = true ->
    join (set m1 a x) m2 m3 ->
    join m1 (set m2 a x) m3.
Proof.
  hy.
Qed.


Lemma sig_set :
  forall (A B T : Type) (MC : PermMap A B T) m a x,
    usePerm = true ->
    get m a = None ->
    join m (sig a x) (set m a x).
Proof.
  hy.
Qed.

(*hard*)
Lemma mem_join_set_l_rev' :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m a b,
    usePerm = true ->
    isRw b = true ->
    join (set m1 a b) m2 m ->
    exists m', join m1 m2 m' /\ m = set m' a b.
Proof.
  intros.
  exists (merge m1 m2).
  split; hy.
Qed.

Lemma del_get :
  forall (A B T : Type) (MC : PermMap A B T) m a,
    usePerm = true ->
    get (del m a) a = None.
Proof.
  jeauto2.
Qed.  
  

Hint Resolve @jl_merge_emp @jl_merge_emp' : jdb1.
Hint Resolve @ml_eq : jdb1.

Lemma merge_list_trans :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 m,
    join_list (m1 :: m2 :: m3 :: nil) m ->
    merge (merge m1 m2) m3 = merge_list (m1 :: m2 :: m3 :: nil).
  intros.
  assert (merge m1 m2 = merge_list (m1 :: m2 :: nil)) by jeauto2.
  rewrite H0.
  intro_merge_list (m1::m2::nil).
  assert (disjoint (merge_list (m1::m2::nil)) m3) by geat.
  (* ** ac: SearchAbout disjoint. *)
  apply join_merge_disj in H2.
  geat.
  clear H0.
  (* ** ac: Check @jl_sub. *)
  generalize (@jl_sub _ _ _ _ _ _ _ H1 _ H2); intro.
  assert ((m1::m2::nil) ++ m3 :: nil = m1 :: m2 :: m3 :: nil) by auto.
  rewrite H4 in H0; clear H4.
  intro_merge_list (m1::m2::m3::nil).
  (* ** ac: SearchAbout join_list. *)
  jeauto2.
Qed.  
  
Hint Resolve @merge_list_trans : jdb1.

(*hard*)
Lemma join_merge_merge :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m12 m3 m123 m4 m1234,
    join m1 m2 m12 ->
    join m12 m3 m123 ->
    join m123 m4 m1234 ->
    join (merge (merge m1 m2) m3) m4 m1234.
Proof.
  intros.
  erewrite merge_list_trans; geat.
Qed.
  
(*very hard*)
(*the following 3 lemmas are complex and duplicated in some sense,
  please start proving after reading them all*)
Arguments merge_list : simpl never.

Lemma merge_assoc2:
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m12 m3 m123 m4 m1234 m5 mx,
    join m1 m2 m12 ->
    join m12 m3 m123 ->
    join m123 m4 m1234 ->
    join m5 (merge (merge m1 m2 ) m4) mx ->
    join m4 (merge (merge m5 m1) m2) mx.
Proof.
  intros.
  erewrite merge_list_trans in *; geat;
  intro_merge_list (m1 :: m2 :: m4 :: nil);
  geat;
  intro_merge_list (m5::m1::m2::nil);
  geat.
Qed.  

(*very hard*)
Lemma merge_join :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m12 m3 m123 m4 m1234 m5 mx,
    join m1 m2 m12 ->
    join m12 m3 m123 ->
    join m123 m4 m1234 ->
    join m5 (merge (merge m1 m2 ) m4) mx ->
    join (merge m5 m1) m2 (merge (merge m5 m1) m2).
Proof.
  intros.
  assert (Ht: merge m5 m1 = merge_list (m5::m1::nil)) by jeauto2.
  rewrite Ht at 1.
  erewrite merge_list_trans in *; geat;
  intro_merge_list (m1 :: m2 :: m4 :: nil);
  geat;
  intro_merge_list (m5::m1::m2::nil);
  geat.
Qed.  

(*very hard*)
Lemma merge_disjoint :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m12 m3 m123 m4 m1234 m5 mx,
    join m1 m2 m12 ->
    join m12 m3 m123 ->
    join m123 m4 m1234 ->
    join m5 (merge (merge m1 m2 ) m4) mx ->
    disjoint m1 m5.
Proof.
  intros.
  erewrite merge_list_trans in *; geat;
  intro_merge_list (m1 :: m2 :: m4 :: nil);
  geat.
Qed.

Lemma join_merge23' :
  forall {A B T:Type} {MC:PermMap A B T} m1 m2 m12 m3 m123,
    join m1 m2 m12 ->
    join m12 m3 m123 ->
    join m1 (merge m2 m3) m123.
Proof.
  intros.
  rewrite ml_eq in *.
  geat.
Qed.  


Lemma join_merge_merge1' :
  forall {A B T:Type} {MC:PermMap A B T} m1 m2 m12 m3 m4 m34 m5,
    join m1 m2 m12 ->
    join m3 m4 m34 ->
    join m12 m34 m5 ->
    join m3 (merge m1 m4) (merge m1 m34).
Proof.
  hy.
Qed.

Lemma join_join_merge' :
  forall {A B T:Type} {MC:PermMap A B T} m1 m2 m12 m3 m123,
    join m1 m2 m12 ->
    join m12 m3 m123 ->
    join m2 m3 (merge m2 m3).
Proof.
  hy.
Qed.

Lemma join3_merge_merge_join :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m12 m3 m123 m4 m1234,
    usePerm = true ->
    join m1 m2 m12 ->
    join m12 m3 m123 ->
    join m123 m4 m1234 ->
    join m1 (merge m2 m4) (merge m12 m4).
Proof.
  hy.
Qed.
  
Lemma osabst_join3_merge_merge_join' :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m12 m3 m123 m4 m1234,
    usePerm = false ->
    join m1 m2 m12 ->
    join m12 m3 m123 ->
    join m123 m4 m1234 ->
    join m1 (merge m2 m4) (merge m12 m4).
Proof.
  hy.
Qed.
  
Lemma mem_join_del' :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 a x,
    usePerm = true ->
    join m1 m2 m3 ->
    get m1 a = Some x ->
    isRw x = true ->
    join (del m1 a) m2 (del m3 a).
Proof.
  hy.
Qed.  

Lemma mem_get_set_merge_eq' :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 a x x',
    usePerm = true ->
    get m1 a = Some x ->
    isRw x = true ->
    isRw x' = true ->
    merge (set m1 a x') m2 = set (merge m1 m2) a x'.
Proof.
  hy.
Qed.

Lemma mem_disjoint_get_true_set_disjoint' :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 a x x',
    usePerm = true ->
    disjoint m1 m2 ->
    isRw x = true ->
    get m1 a = Some x ->
    isRw x' = true ->
    disjoint (set m1 a x') m2.
Proof.
  hy.
Qed.      

Lemma mem_disjoint_sub_disjoint_merge' :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 mx,
    usePerm = true ->
    disjoint m1 m2 ->
    Maps.sub mx m1 ->
    disjoint (minus m1 mx) (merge mx m2).
Proof.
  hy.
Qed.  

Lemma mem_disjoint_disjoint_merge_disjoint' :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3,
    usePerm = true ->
    disjoint m2 m3 ->
    disjoint m1 (merge m2 m3) ->
    disjoint m1 m3.
Proof.
  hy.
Qed.  


Lemma mem_sub_get_true_sub_set' :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 a x x',
    usePerm = true ->
    Maps.sub m1 m2 ->
    isRw x = true ->
    get m1 a = Some x ->
    isRw x' = true ->
    Maps.sub (set m1 a x') (set m2 a x').
Proof.
  hy.
Qed.  

Lemma mem_disjoint_merge_minus_get_true_set' :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 m4 a x x',
    usePerm = true ->
    isRw x = true ->
    isRw x' = true ->
    get m2 a = Some x ->
    Maps.sub m2 m1 ->
    disjoint (merge (minus (set m1 a x') (set m2 a x')) m3) m4 ->
    disjoint (merge (minus m1 m2) m3) m4.
Proof.
  hy.
Qed.  

(* ** ac: Print Ltac crush. *)
(* ** ac: Print Ltac crush2. *)
(* ** ac: Print Ltac crush1. *)
(* ** ac: Print Ltac invert_eql. *)

Hint Resolve @map_sv_comm @map_sv_assoc @map_perm_eql : jdb1.

Lemma map_flip_eql' :
  forall (A B T : Type) (MC : PermMap A B T) (v1 v2:B),
    usePerm = true ->
    flip v1 = flip v2 ->
    v1 = v2.
  intros.
  (* ** ac: SearchAbout flip. *)
  (* ** ac: SearchAbout isRw. *)
  assert (isRw (flip v1) = negb (isRw v1)) by jeauto2.
  assert (isRw (flip v2) = negb (isRw v2)) by jeauto2.
  (* ** ac: SearchAbout flip. *)
  assert (sameV v1 (flip v1)) by jeauto2.
  assert (sameV v2 (flip v2)) by jeauto2.
  rewrite H0 in *.
  rewrite H1 in H2.
  (* ** ac: SearchAbout sameV. *)
  assert (sameV (flip v2) v2) by jeauto2.
  assert (sameV v1 v2) by jeauto2.
  destruct (isRw v1) eqn:F1; destruct (isRw v2) eqn:F2;
  crush.
  apply map_perm_eql; jeauto2.  
  apply map_perm_eql; jeauto2.  
Qed.  

Hint Resolve @map_flip_eql' : jdb1.

(* Ltac invert_eql ::= *)
(*      repeat match goal with *)
(*               | H: Some _ = Some _ |- _ => inverts H *)
(*               | H: flip ?v1 = flip ?v2 |- _ => *)
(*                 assert (v1 = v2) by jeauto2 *)
(*             end. *)

(* Print Ltac my_subst. *)

(* Ltac my_subst ::= *)
(*      repeat match goal with *)
(*               | H: get _ _ = _ |- _ => fail  *)
(*               | H: isRw _ = _ |- _ => fail  *)
(*               | H: usePerm = _ |- _ => fail   *)
(*               | H: ?a = ?b |- _ => *)
(*                 first [subst a *)
(*                       | subst b *)
(*                       (* | rewrite H in *; *) *)
(*                       (*   clear H *) *)
(*                       ] *)
(*             end. *)

Lemma mem_disjoint_merge_eq_merge_merge' :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 m4 mx,
    usePerm = true ->
    disjoint m1 m2 ->
    disjoint m3 m4 ->
    merge m1 m2 = merge m3 m4 ->
    disjoint mx (merge m3 m4) ->
    merge (merge mx m1) m2 = merge (merge mx m3) m4.
Proof.
  intros.
  
  apply map_eql.
  intro t.
  infer (pnil, m1, m2, disjoint m1 m2,
         m3, m4, disjoint m3 m4,
         merge m1 m2,
         merge m3 m4) t;
  crush;
  rewrite H2 in *;
  infer (pnil, mx, disjoint mx (merge m3 m4),
         merge mx m1, merge mx m3,
         merge (merge mx m1) m2, merge (merge mx m3) m4) t;
  crush.
Qed.  
  
Lemma mem_sub_disjoint' :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3,
    usePerm = true ->
    Maps.sub m1 m2 ->
    disjoint m2 m3 ->
    disjoint m1 m3.
Proof.
  hy.
Qed.  

Lemma mem_merge_merge_minus_get_true_set_eq' :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 m4 m5 a x x',
    usePerm = true ->
    Maps.sub m2 m1 ->
    isRw x = true ->
    isRw x' = true ->
    get m2 a = Some x ->
    merge (merge (minus (set m1 a x') (set m2 a x')) m3) m4 = m5 ->
    merge (merge (minus m1 m2) m3) m4 = m5.
Proof.
  intros.
  apply map_eql.
  intro t.
  infer (pnil, m1, m2, sub m2 m1,
         set m1 a x', set m2 a x', minus (set m1 a x') (set m2 a x'),
         m3, merge (minus (set m1 a x') (set m2 a x')) m3,
         m4, merge (merge (minus (set m1 a x') (set m2 a x')) m3) m4,
         m5) t;
  try (rewrite H4 in *; solve [crush]);
  infer (pnil, minus m1 m2,
         merge (minus m1 m2) m3,
         merge (merge (minus m1 m2) m3) m4) t;
  crush.
Qed.
  
Lemma mem_del_get_neq' :
  forall (A B T : Type) (MC : PermMap A B T) m a a',
    usePerm = true ->
    a <> a' ->
    get (del m a') a = get m a.
Proof.
  hy.
Qed.  

Lemma mem_join_set_true_join' :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 a x x',
    usePerm = true ->
    join m1 m2 m3 ->
    isRw x = true ->
    isRw x' = true ->
    get m1 a = Some x ->
    join (set m1 a x') m2 (set m3 a x').
Proof.
  hy.
Qed.  

Lemma mem_join_join_merge13_join' :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m12 m3 m123,
    usePerm = true ->
    join m1 m2 m12 ->
    join m12 m3 m123 ->
    join (merge m1 m3) m2 m123.
Proof.
  hy.
Qed.  
  
Lemma mem_join_join_merge' :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m12 m3 m123,
    usePerm = true ->
    join m1 m2 m12 ->
    join m12 m3 m123 ->
    join m1 m3 (merge m1 m3).
Proof.
  hy.
Qed.  

Lemma mem_disjoint_set_l' :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 a x x',
    usePerm = true ->
    disjoint m1 m2 ->
    isRw x = true ->
    get m1 a = Some x ->
    isRw x' = true ->
    disjoint (set m1 a x') m2.
Proof.
  hy.
Qed.  

Lemma mem_disjoint_disjoint_sub_disjoint_merge' :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 mx,
    usePerm = true ->
    disjoint m1 m2 ->
    Maps.sub mx m1 ->
    disjoint (minus m1 mx) (merge mx m2).
Proof.
  hy.
Qed.  
  
Lemma mem_merge_merge_minus_merge' :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3,
    usePerm = true ->
    Maps.sub m1 m2 ->
    disjoint m2 m3 ->
    merge (merge (minus m2 m1) m1) m3 = merge m2 m3.
Proof.
  hy.
Qed.

Lemma mem_sub_get_true_set_sub' :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 a x x',
    usePerm = true ->
    Maps.sub m1 m2 ->
    isRw x = true ->
    isRw x' = true ->
    get m1 a = Some x ->
    Maps.sub (set m1 a x') (set m2 a x').
Proof.
  hy.
Qed.  

Lemma mem_sub_disjoint_sub_merge_merge' :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3,
    usePerm = true ->
    Maps.sub m1 m2 ->
    disjoint m2 m3 ->
    Maps.sub (merge m1 m3) (merge m2 m3).
Proof.
  hy.
Qed.  
  
Lemma mem_sub_disjoint_sub_merge' :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3,
    usePerm = true ->
    Maps.sub m1 m2 ->
    disjoint m2 m3 ->
    Maps.sub m1 (merge m2 m3).
Proof.
  hy.
Qed.  

Lemma mem_join_join_disjoint_join_merge' :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 m4 mx,
    usePerm = true ->
    join m1 mx m2 ->
    join m1 m3 m4 ->
    disjoint m4 mx ->
    join m2 m3 (merge m4 mx).
Proof.
  hy.
Qed.  

(* ** ac: SearchAbout indom. *)

Lemma mem_minus_set_comm' :
  forall (A B T : Type) (MC : PermMap A B T) M1 M2 l v,
    usePerm = true ->
    ~ indom M2 l->
    minus (set M1 l v) M2 = set (minus M1 M2) l v.
Proof.
  intros.
  indom_rewrite.
  hy.
Qed.  

Lemma mem_join_minus_get' :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 a,
    usePerm = true ->
    join m1 m2 m3 ->
    get (minus m3 m2) a = get m1 a.
Proof.
  hy.
Qed.  

Lemma mem_get_minus_get' :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 a x,
    usePerm = true ->
    get m1 a = Some x ->
    get m2 a = None ->
    get (minus m1 m2) a = Some x.
Proof.
  hy.
Qed.  

Lemma mem_join_minus_join_r' :
  forall (A B T : Type) (MC : PermMap A B T) M m1 m2 m3 m4,
    usePerm = true ->
    Maps.sub m3 M ->
    join m1 m2 (minus M m3) ->
    join m2 m3 m4 ->
    join m1 m4 M.
Proof.
  intros.
  let ins := calc_ins in pose ins.
  hy.
Qed.  

Lemma mem_join_minus_r' :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 m4,
    usePerm = true ->
    join m1 m2 (minus m3 m4) ->
    exists mx, join m2 m4 mx.
Proof.
  intros.
  exists (merge m2 m4).
  hy.
Qed.

Lemma mem_sub_del' :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 a,
    usePerm = true ->
    Maps.sub m1 m2 ->
    Maps.sub (del m1 a) m2.
Proof.
  hy.
Qed.
  
Lemma mem_get_del_none' :
  forall (A B T : Type) (MC : PermMap A B T) m a,
    usePerm = true ->
    get (del m a) a = None.
Proof.
  intros.
  jeauto2.
Qed.  

Lemma mem_get_del_get_eq' :
  forall (A B T : Type) (MC : PermMap A B T) m a1 a2,
    usePerm = true ->
    a2 <> a1 ->
    get (del m a2) a1 = get m a1.
Proof.
  intros.
  jeauto2.
Qed.  

Lemma mem_sub_disj':
  forall (A B T : Type) (MC : PermMap A B T) M M1 M2,
    usePerm = true ->
    disjoint M1 M2 -> Maps.sub M M1 -> disjoint M M2.
Proof.
  hy.
Qed.  

(******************************************************************************)
(** tactic update **)
Ltac ica :=
  eauto 2; try (unfold isRw); try (unfold flip); simpl; auto.

Ltac infer_v ls t :=
  (** verbose infer, logical correct by slow **)
  let ic := calc_ins_for_context in
  let ig := plist_minus ls ic in
  let ic' := plist_minus ls ig in
  infer' ic' t; try (solve [ crush ]); infer' ig t.

Ltac infer_q ls t :=
  (** quick infer, may be quick but can not solve **)
  let ic := calc_ins_for_context in
  let ig := plist_minus ls ic in
  let ic' := plist_minus ls ig in
  infer' ic' t; crush; infer' ig t.

Ltac infer ::= infer_q.

Ltac invert_flip :=
  repeat match goal with
           | Hn: usePerm = true, H: flip ?v1 = flip ?v2 |- _ =>
             generalize (@map_flip_eql' _ _ _ _ _ _ Hn H);
             clear H; intro H
         end.

Ltac infer_merge x y t ::=
     match goal with
       | F:get x t = ?b1 |- _ =>
         match goal with 
           | F1:get y t = ?b2 |- _ =>
             match constr:(b1, b2) with
               | (Some ?v1, Some ?v2) =>
                 match goal with
                   | Hn:usePerm = false
                     |- _ => generalize (merge_sem1' Hn F F1); intro
                   | Hn:usePerm = true
                     |- _ =>
                     let H' := fresh in
                     generalize (merge_semp x y t Hn); intro H';
                     try (rewrite F in H'); try (rewrite F1 in H');
                     (let Hs := fresh in
                      destruct (same v1 v2) eqn:Hs; rewrite_same;
                      [ let H1 := fresh in
                        destruct (isRw v1) eqn:H1;
                        [ 
                        | assert (isRw (flip v1) = true) by
                            join_tactics.veg.jeauto2 ]
                      | tryfalse ])
                 end
               | (Some ?v1, None) =>
                 generalize (merge_sem_none2 F1 F); intro
               | (None, Some ?v2) =>
                 generalize (merge_sem_none1 F F1); intro
               | (None, None) =>
                 generalize (merge_sem_none3 F F1); intro
             end
         end
     end.
(******************************************************************************)
