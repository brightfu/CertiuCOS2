Require Import include_frm.
Require Import simulation.
Require Import join_lib.

  
Lemma sub_disj_disj:forall (A B T:Type) (X:PermMap A B T) M1 M2 Ms Ml, disjoint Ml Ms -> Maps.sub M2 Ml -> Maps.sub M1 (merge M2 Ms) -> disjoint (minus Ml M2) M1. 
Proof.
  hy.
Qed.  

Lemma joinm2_merge_minus:
  forall  M1 M2 o m,
    join M1 M2 (get_mem (get_smem o)) ->
    Maps.sub m M1 ->
    joinm2 (substaskst o m) M2 (minus M1 m) o.
Proof.
  intros.
(* ** ac:   Check substaskst. *)
(* ** ac:   Print substaskst. *)
  unfold get_mem in *.
  unfold get_smem in *.
  unfold substaskst.
  destruct o.
  destruct p.
  destruct s.
  destruct p.
  unfold joinm2.
  unfold joinmem.
  eexists.
  split.
  do 6 eexists.
  split; eauto.
  split; eauto.
  instantiate (1:= merge m M2).
  Lemma joinm2_merge_minus_auto1:
    forall (A B T : Type) (MC : PermMap A B T) M1 M2 m0 m,
      usePerm = true ->
      join M1 M2 m0 ->
      Maps.sub m M1 ->
      join m M2 (merge m M2).
    hy.
  Qed.    

  eapply joinm2_merge_minus_auto1; ica.
  do 6 eexists.
  split; eauto.
  split; eauto.

  Lemma joinm2_merge_minus_auto2:
    forall (A B T : Type) (MC : PermMap A B T) M1 M2 m0 m,
      usePerm = true ->
      join M1 M2 m0 ->
      Maps.sub m M1 ->
      join (merge m M2) (minus M1 m) m0.
    hy.
  Qed.    

  eapply joinm2_merge_minus_auto2; ica.
Qed.  

Lemma join_join_merge_merge:
  forall (A B T:Type) (PM:PermMap A B T) M1 M2 M11 M12 M,
    join M1 M2 M ->
    join M11 M12 M1 ->
    M = merge M11 (merge M12 M2).
Proof.
  hy.
Qed.

Lemma sub_join_sub:
  forall (A B T:Type) (PM:PermMap A B T) M1 M2 M m,
    Maps.sub m M1 ->
    join M1 M2 M ->
    Maps.sub m M.
Proof.
  hy.
Qed.

Lemma join_join_join_merge_set:
  forall (A B T:Type) (PM:PermMap A B T) OO' x0 O' Os' O a b,
    usePerm = false ->
    join OO' O x0 ->
    join O' Os' OO' ->
    set O' a b = O' ->
    join (merge (set O' a b) O) Os' (set x0 a b).
Proof.
  intros.
  assert (get O' a = Some b).
  {
    clear - H H2.
    rewrite <- H2.
    hy.
  }
  clear H2.
  hy.
Qed.  
  
Lemma disj_get_set_disj:
  forall (A B T:Type) (PM:PermMap A B T) O O' a b b',
    usePerm = false ->
    disjoint O O' ->
    get O a = Some b ->
    disjoint (set O a b') O'.
Proof.
  hy.
Qed.

Lemma sub_merge_l:
  forall (A B T:Type) (X:PermMap A B T) M1 M2,
    disjoint M1 M2 -> Maps.sub M1 (merge M1 M2).
Proof.
  hy.
Qed.

Lemma join_complex_auto:
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m m21 m22 mx1 mx2 a b b' m2' m21' m22',
    usePerm = false ->
    join m2 m1 m ->
    join m21 m22 m2 ->
    join mx1 mx2 m21 ->
    get mx2 a = Some b ->
    m2' = set (merge mx2 m22) a b' ->
    join m21' m22' m2' ->
    join (merge (merge m21' mx1) m1) m22'
         (set m a b').
  intros.
  subst.
  Ltac infer ::= infer_v.
  hy.
  Ltac infer ::= infer_q. (** restore quick version of tactic **)
Qed.  

Lemma join_complex:
  forall (OO' Ol Oc x0 O' Os' OO' Olc Occ O':osabst) a b b' Oc'0 OO'' Os'',
    join OO' (minus Ol Oc) x0 ->
    join O' Os' OO' ->
    join Olc Occ O' ->
    get Occ a = Some b ->
    OO'' = set (merge Occ Os') a b' ->
    join Oc'0 Os'' OO'' ->
    join (merge (merge Oc'0 Olc) (minus Ol Oc)) Os''
         (set x0 a b').
Proof.
  intros.
  eapply join_complex_auto; ica.
Qed.

Lemma disj_complex_auto:
  forall (A B T : Type) (MC : PermMap A B T) (O' Oc'0 Os'' OO' Os' OO'' Olc Occ:T) a b b',
    usePerm = false ->
    join Oc'0 Os'' OO'' ->
    OO'' = set (merge Occ Os') a b' ->
    join Olc Occ O' ->
    join O' Os' OO' ->
    get Occ a = Some b -> 
    disjoint Oc'0 Olc.
  intros.
  subst.
  hy.
Qed.  
  
Lemma disj_complex:
  forall (O' Oc'0 Os'' OO' Os' OO'' Olc Occ:osabst) a b b',
    join Oc'0 Os'' OO'' ->
    OO'' = set (merge Occ Os') a b' ->
    join Olc Occ O' ->
    join O' Os' OO' ->
    get Occ a = Some b -> 
    disjoint Oc'0 Olc.
Proof.
  intros.
  eapply disj_complex_auto; ica.
Qed.  

Lemma disj_complex'_auto:
  forall (A B T : Type) (MC : PermMap A B T) O' Ox x0 Oc'0 Os'' OO' Os' OO'' Olc Occ a b b',
    usePerm = false ->
    join Oc'0 Os'' OO'' ->
    OO'' = set (merge Occ Os') a b' ->
    join Olc Occ O' ->
    join O' Os' OO' ->
    join OO' Ox x0 ->
    get Occ a = Some b -> 
    disjoint (merge Oc'0 Olc) Ox.
  intros;
  subst.
  hy.
Qed.

Lemma disj_complex':
  forall (O' Ox x0 Oc'0 Os'' OO' Os' OO'' Olc Occ:osabst) a b b',
    join Oc'0 Os'' OO'' ->
    OO'' = set (merge Occ Os') a b' ->
    join Olc Occ O' ->
    join O' Os' OO' ->
    join OO' Ox x0 ->
    get Occ a = Some b -> 
    disjoint (merge Oc'0 Olc) Ox.
Proof.
  intros; eapply disj_complex'_auto; ica.
Qed.

Lemma join_minus:
  forall (A B T:Type) (X:PermMap A B T) a b c,
    join a b c ->
    minus c b = a. 
Proof.
  hy.
Qed.

Lemma joinmem_substaskst_minus:
  forall ol Mc Mc' o,
    joinmem ol Mc' (substaskst o Mc) ->
    substaskst o (minus Mc Mc') = ol.
Proof.
  intros.
  unfold substaskst in *.
  destruct o.
  destruct p.
  destruct s.
  destruct p.
  unfold joinmem in *.
  heat.
  inverts H0.
  apply join_minus in H1.
  subst; auto.
Qed.

Lemma set_set_eq:
  forall (A B T:Type) (X:PermMap A B T) M a b b',
    set M a b = set (set M a b') a b.
Proof.
  hy.
Qed.

Lemma join_crt_auto:
  forall (A B T : Type) (MC : PermMap A B T) OO' O' Os' Ox x0 a b b',
    usePerm = false ->
    get OO' a = Some b ->
    join O' Os' (set OO' a b') ->
    join OO' Ox x0 ->
    join (merge O' Ox) Os' (set x0 a b').
  Ltac infer ::= infer_v.
  hy.
  Ltac infer ::= infer_q.
Qed.

Lemma join_crt:
  forall (OO' O' Os' Ox x0:osabst) a b b',
    get OO' a = Some b ->
    join O' Os' (set OO' a b') ->
    join OO' Ox x0 ->
    join (merge O' Ox) Os' (set x0 a b').
Proof.
    intros; eapply join_crt_auto; ica.
Qed.

Require Import join_lib_aux.

Lemma joinsig_indom_neq:
  forall (A B T:Type) (X:PermMap A B T) a a' b M1 M,
    joinsig a b M1 M ->
    a <> a' ->
    indom M a' ->
    indom M1 a'.
Proof.
  intros.
  eapply joinsig_indom_neq; eauto.
Qed.

Lemma get_set_join_disj_l_auto:
  forall (A B T : Type) (MC : PermMap A B T) OO' O' Os' Ox O x1 x2 a,
    usePerm = false ->
    get OO' a = Some x1 ->
    join O' Os' (set OO' a x2) ->
    join OO' Ox O ->
    disjoint O' Ox.
  Ltac infer ::= infer_v.
  hy.
  Ltac infer ::= infer_q.
Qed.
  
Lemma get_set_join_disj_l:
  forall OO' O' Os' Ox O x1 x2,
    get OO' abstcblsid = Some (abstcblist x1) ->
    join O' Os' (set OO' abstcblsid (abstcblist x2)) ->
    join OO' Ox O ->
    disjoint O' Ox.
Proof.
  intros.
  eapply get_set_join_disj_l_auto; ica.
Qed.  

Lemma join_get_get_l_rev:
  forall (A B T : Type) (MC : PermMap A B T) (m1 m2 m : T) (a : A) (b : B),
    usePerm = false -> join m1 m2 m -> get m a = Some b -> get m2 a = None -> get m1 a = Some b.
Proof.
  hy.
Qed.

Lemma join_get_get_r_rev:
  forall (A B T : Type) (MC : PermMap A B T) (m1 m2 m : T) (a : A) (b : B),
    usePerm = false -> join m1 m2 m -> get m a = Some b -> get m1 a = None -> get m2 a = Some b.
Proof.
  hy.
Qed.

Lemma join_join_merge:
  forall (A B T:Type) (X:PermMap A B T) Ml mi M0 M1 Mlinv' Mx' Ms,
    join mi Ml M0 ->
    join M0 Ms M1 ->
    join Mlinv' Mx' (merge mi Ms) ->
    join (merge Ml Mlinv') Mx' M1.
Proof.
  hy.
Qed.

Lemma join_join_join_merge_disj:
  forall (A B T:Type) (X:PermMap A B T) M0 Ms M1 mi Ml M' Mx',
    join M0 Ms M1 ->
    join mi Ml M0 ->
    join M' Mx' (merge mi Ms) ->
    disjoint Ml M'.
Proof.
  hy.
Qed.

Lemma join_disj_merge_merge:
  forall (A B T:Type) (X:PermMap A B T) O Ox OO Ol,
    join O Ox OO ->
    disjoint Ol OO ->
    join (merge Ol O) Ox (merge Ol OO).
Proof.
  hy.
Qed.

Lemma disj_merge_join_disj_intro:
  forall (A B T :Type) (X:PermMap A B T) M M1 M2 MM,
    join M (merge M1 M2) MM ->
    disjoint M1 M2 ->
    disjoint M M1.
Proof.
  hy.
Qed.

Lemma disj_join_join_merge:
  forall (A B T :Type) (X:PermMap A B T) M1 M2 M3 MM,
    join M1 (merge M2 M3) MM ->
    disjoint M2 M3 ->
    join (merge M2 M1) M3 MM.
Proof.
  hy.
Qed.

Lemma join_merge_merge_recompose:
  forall (A B T:Type) (X:PermMap A B T) mi Ml M0 M1 Mf m0 Ms,
    join mi Ml M0 ->
    join M0 Ms M1 ->
    join M1 Mf m0 ->
    join (merge mi Ms) (merge Ml Mf) m0.
Proof.
  hy.
Qed.

Lemma join_join_join_merge'
: forall (A B T : Type) (MC : PermMap A B T) (Ml Ms M Ml' Ms' : T),
    join Ml Ms M -> join Ml' Ms' Ms -> join (merge Ml' Ml) Ms' M.
Proof.
  hy.
Qed.
