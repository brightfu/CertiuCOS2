Require Import include_frm.
Require Import base_tac.
Require Import simulation.
Require Import sep_auto.
Require Import join_lib.

Import DeprecatedTactic.



Lemma joinm2_minus_join:
  forall o M M' g e m ir l,
    joinm2 o M M' (g,e,m,ir,l) ->
    join (minus m M) M m.
Proof.
  unfold joinm2.
  unfold joinmem.
  intros; mytac.
  Lemma joinm2_minus_join_auto:
    forall (A B T : Type) (MC : PermMap A B T) M' x3 x8 M x2,
      usePerm = true ->
      join x2 M' x3 ->
      join x8 M x2 ->
      join (minus x3 M) M x3.
    hy.
  Qed.

  eapply joinm2_minus_join_auto; ica.
Qed.

Lemma joinm2_sub:
  (*can be derived by lemma join_join_sub_minus*)
  forall o M M' g e m ir l,
    joinm2 o M M' (g,e,m,ir,l) ->
    Maps.sub (get_mem (get_smem o)) (minus m M).
Proof.
  unfold joinm2; unfold get_smem; unfold get_mem; unfold joinmem.
  intros.
  mytac.
  eapply join_join_sub_minus; ica.
Qed.

Lemma sub_join_trans':
  (*can be derived by lemma join_join_sub_sub_minus*)
  forall (o : taskst) (M M' : mem) m g e x i l,
    joinm2 o M M' (g,e,x,i,l) ->
    Maps.sub m M' ->
    Maps.sub m (minus x M).
Proof.
  unfold joinm2; unfold joinmem.
  intros; mytac.
  eapply join_join_sub_sub_minus; ica.
Qed.

Lemma joinm2_sub_disj:
  (*can be derived by lemma join_join_sub_disj*)
  forall o M1 M2 e e0 i l m M,
    joinm2 o M1 M2 (e, e0, M, i, l) ->
    Maps.sub m M2 ->
    disjoint m (get_mem (get_smem o)).
Proof.
  unfold joinm2; unfold get_smem; unfold get_mem; unfold joinmem.
  intros; mytac.

  Lemma joinm2_sub_disj_auto:
    forall (A B T : Type) (MC : PermMap A B T) x2 M2 x3 m x8 M1,
      usePerm = true ->
      join x2 M2 x3 ->
      Maps.sub m M2 ->
      join x8 M1 x2 ->
      disjoint m x8.
    hy.
  Qed.

  eapply joinm2_sub_disj_auto; auto.
  exact H3.
  ica.
  ica.
Qed.

Lemma taskst_join_merge : forall o o1 M1 M2 o', joinmem o M1 o1 ->
     joinmem o1 M2 o' -> exists M3, join M1 M2 M3 /\  joinmem o M3 o'.
Proof.
  unfold joinmem.
  intros.
  mytac.
  exists (merge M1 M2).
  mytac.
  
  Lemma taskst_join_merge_auto:
    forall (A B T : Type) (MC : PermMap A B T) x1 M2 x2 x7 M1,
      join x1 M2 x2 ->
      join x7 M1 x1 ->
      join M1 M2 (merge M1 M2).
    hy.
  Qed.
  
  eapply taskst_join_merge_auto; ica.
  do 6 eexists; mytac.
  eauto.
  eauto.

  Lemma taskst_join_merge_auto1:
    forall (A B T : Type) (MC : PermMap A B T) x1 M2 x2 x7 M1,
      join x1 M2 x2 ->
      join x7 M1 x1 ->
      join x7 (merge M1 M2) x2.
    hy.
  Qed.

  eapply taskst_join_merge_auto1; ica.
Qed.
  
Lemma join_intro_l: forall G E M isr aux M' o, joinmem (G, E , M, isr, aux) M' o -> exists M1, join M M' M1 /\ o = (G,E,M1,isr,aux). 
Proof.
  intros.
  unfold joinmem in *; mytac.
  eexists; mytac; eauto.
Qed.

Lemma join_intro_r : forall G E M isr aux M' o, joinmem o  M' (G, E , M, isr, aux)  -> exists M1, join M1 M'  M  /\ o = (G,E,M1,isr,aux).
Proof.
  intros.
  unfold joinmem in *; mytac.
  eexists; mytac; eauto.
Qed.

Lemma Mem_join_disj : forall M1 M2 M, join M1 M2 M -> HalfPermMap.disjoint M1 M2.
Proof.
  intros.
  unfold join in H.
  simpl in H.
  unfold HalfPermMap.join in H.
  destruct H.
  auto.
Qed.
  
Lemma join_mjoin_intro_intro: forall G E M1 isr aux M2 M3 M o,
                        joinmem (G,E,M1,isr,aux) M o -> 
                        join M2 M3 M ->
                        exists M',  joinmem (G,E,M',isr,aux) M2 o /\ join M1 M3 M'.
Proof.
  unfold joinmem.
  intros.
  mytac.
  exists (merge x1 M3).
  mytac.
  do 6 eexists.
  mytac; eauto.

  Lemma join_mjoin_intro_intro_auto:
    forall (A B T : Type) (MC : PermMap A B T) x1 M x2 M2 M3,
      usePerm = true ->
      join x1 M x2 ->
      join M2 M3 M ->
      join (merge x1 M3) M2 x2.
    hy.
  Qed.

  eapply join_mjoin_intro_intro_auto; ica.

  Lemma join_mjoin_intro_intro_auto1:
    forall (A B T : Type) (MC : PermMap A B T) x1 M x2 M2 M3,
      usePerm = true ->
      join x1 M x2 ->
      join M2 M3 M ->
      join x1 M3 (merge x1 M3).
    hy.
  Qed.

  eapply join_mjoin_intro_intro_auto1; ica.
Qed.

     
Lemma join_frame_dis :   forall o1 M o1' Ms o0 Mf o2, 
                          joinmem o1 M o1' -> 
                          joinmem o1' Ms o0  ->  
                          joinmem o0 Mf o2 ->    
                          exists o M', joinmem o1 Ms o /\ 
                          joinmem o M' o2 /\ joinmem o M o0 /\ join M Mf M'.  
Proof.
  unfold joinmem.
  intros; mytac.
  do 2 eexists.
  mytac.
  do 6 eexists; mytac; eauto.
  instantiate (1:= merge x13 Ms).
  rewrite ml_eq.
  geat.

  do 6 eexists; mytac; eauto.
  instantiate (1:= merge M Mf).
  rewrite ml_eq.
  rewrite ml_eq.
  geat.
  
  do 6 eexists; mytac; eauto.
  rewrite ml_eq.
  geat.
  rewrite ml_eq.
  geat.
Qed.

Lemma join_sub_inv:   forall o1 M o1' Ms Os ab I,
                        joinmem o1 M o1' -> 
                        (substaskst o1' Ms, Os, ab) |= INV I -> 
                        (substaskst o1 Ms, Os, ab) |= INV I. 
Proof.
  intros.
  unfold joinmem in *; mytac.
  unfold substaskst in *; mytac.
  auto.
Qed.

Lemma join_sub_inv_rev:   forall o1 M o1' Ms Os ab I,  joinmem o1 M o1' -> 
                       (substaskst o1 Ms, Os, ab) |= INV I -> 
                     (substaskst o1' Ms, Os, ab) |= INV I. 
Proof.
  intros.
  unfold joinmem in *; mytac.
  unfold substaskst in *; mytac.
  auto.
Qed.

Lemma join_inject: forall o1 M1 o2 M o3 M0 Mf ,
                     joinmem o2 M o3 -> 
                     joinmem o1 M1 o2  -> 
                     join M0 Mf M -> 
                     exists o2' o1' , joinmem o2' Mf o3 /\ joinmem o1' M1 o2' /\ joinmem o1 M0 o1'.
Proof.
  unfold joinmem.
  intros; mytac.

  do 2 eexists.
  mytac.

  geat.
  geat.
  intro_merge_list (x1 :: M1 :: M0 :: nil).
  geat.

  geat.
Qed.
  
Lemma joinmem_get_disj : forall o M o',joinmem o M o' ->  HalfPermMap.disjoint (get_mem (get_smem o)) M.
Proof.
  unfold joinmem;
  unfold get_smem;
  unfold get_mem.
  intros.
  mytac.

  unfold join in H1.
  simpl in H1.
  unfold HalfPermMap.join in H1.
  geat.
Qed.

Lemma join_memj_intro : forall o M o' M1 M2,  joinmem o M o' ->  join M1 M2 M -> 
          exists o1 , joinmem o1 M2 o' /\ joinmem o M1 o1. 
Proof.
  unfold joinmem;
  intros; mytac.
  geat.
Qed.  

(** these two lemma is important **)
Lemma hp_disj_to:
  forall m1 m2,
    disjoint m1 m2 ->
    HalfPermMap.disjoint m1 m2.
  intros.
  unfold disjoint in H.
  mytac.
  unfold join in H; simpl in H.
  unfold HalfPermMap.join in H; mytac.
  auto.
Qed.

Lemma hp_disj_from:
  forall m1 m2,
    HalfPermMap.disjoint m1 m2 ->
    disjoint m1 m2.
  intros.
  unfold HalfPermMap.disjoint in *.
  apply disjoint_semp; auto.
  intro t.
  instant H t.
  unfold get.
  simpl.
  unfold HalfPermMap.get.
  destruct (m1 t) eqn:F1;
  destruct (m2 t) eqn:F2.
  destruct b.
  destruct b.
  tryfalse.
  destruct b0.
  destruct b.
  tryfalse.
  subst.
  ica.
  auto.
  auto.
  auto.
Qed.  

Ltac hp_disj_rr :=
  repeat match goal with
           | H: HalfPermMap.disjoint _ _ |- _ =>
             apply hp_disj_from in H
           | |- HalfPermMap.disjoint _ _ =>
             apply hp_disj_to
         end.

Lemma join_disj_disj : forall o M o' Ms,
                     joinmem o M o' ->  HalfPermMap.disjoint (get_mem (get_smem o')) Ms ->
                             HalfPermMap.disjoint (get_mem (get_smem o)) Ms.
Proof.
  unfold joinmem;
  unfold get_smem;
  unfold get_mem;
  intros;
  mytac.

  hp_disj_rr.
  unfold disjoint in *.
  geat.
Qed.  

Lemma join_join_intro :  forall o M o' M' o'' ,
                           joinmem o M o' -> joinmem o' M' o'' -> 
                           exists M1, joinmem o M1 o''/\ join M M' M1.
Proof.
  unfold joinmem;
  intros;
  mytac.

  geat.
Qed.  

Lemma  join_swinv_prop : forall o M o' Mc aop O I, joinmem o M o' -> 
                                                   (substaskst o Mc, O, aop) |= SWINV I ->
                                                   (substaskst o' Mc, O, aop) |= SWINV I.
Proof.
  intros.
  unfold joinmem in *; mytac.
  simpl in *; mytac.
  destruct x4.
  destruct p.
  mytac.
  do 6 eexists; mytac.
  5 : do 6 eexists; mytac.
  7 : eexists; mytac.
  9 : do 7 eexists; mytac.
  eauto.
  2: eauto.
  3: eauto.
  3: eauto.
  3: eauto.
  3: eauto.
  6: eauto.
  3: eauto.
  3: eauto.
  geat.
  geat.
  geat.
Qed.  

Lemma  join_swinv_prop_rev : forall o M o' Mc aop O I, joinmem o M o' -> 
                                                       (substaskst o' Mc, O, aop) |= SWINV I ->
                                                       (substaskst o Mc, O, aop) |= SWINV I.
Proof.
  intros.
  unfold joinmem in *; mytac.
  simpl in *; mytac.
  destruct x4.
  destruct p.
  mytac.
  do 6 eexists; mytac.
  5 : do 6 eexists; mytac.
  7 : eexists; mytac.
  9 : do 7 eexists; mytac.
  eauto.
  2: eauto.
  3: eauto.
  3: eauto.
  4: eauto.
  3: eauto.
  6: eauto.
  geat.
  geat.
  auto.
  auto.
  auto.
Qed.

Lemma join_join_intro' : forall o M o' M' o'',
                           joinmem o M o' -> joinmem o' M' o''  -> exists o1, joinmem o M' o1/\ joinmem o1 M o''.
Proof.
  unfold joinmem;
  intros;
  mytac.

  geat.
Qed.

Lemma env_join_get:  forall  x l tp E1 E1' E E2,
                    EnvMod.join (EnvMod.sig x (l, tp)) E1 E1' -> 
                    EnvMod.join E E1' E2 -> 
                    EnvMod.get E2 x = Some (l, tp) .
Proof.
  intros.
  eapply EnvMod.join_get_get_r; eauto.
  eapply EnvMod.join_get_get_l; eauto.
  apply EnvMod.get_sig_some.
Qed.

Lemma ListSet_set_In_cons_elim :
  forall {t:Type} (a b:t) x,
    ListSet.set_In a (b::x) -> a = b \/ ListSet.set_In a x.
Proof.
  intros.
  simpl in *; intuition.
Qed.

Lemma ListSet_set_In_cons_intro :
  forall {t:Type} (a b:t) x,
    a = b \/ ListSet.set_In a x -> ListSet.set_In a (b::x).
Proof.
  intros.
  simpl in *; intuition.
Qed.


Lemma  join_eq_dom_env: forall x l tp E1 E1' dd, 
           EnvMod.join (EnvMod.sig x (l, tp)) E1 E1' -> 
           eq_dom_env E1 (getlenvdom dd) -> 
           eq_dom_env E1' ((x,tp)::(getlenvdom dd)).
Proof.
  intros.
  unfold eq_dom_env in *; intros.
  split; intros.
  apply ListSet_set_In_cons_elim in H1; destruct H1; subst.
  inverts H1.
  eexists; eapply EnvMod.join_get_get_l; eauto.
  apply EnvMod.get_sig_some.
  lets H100 : H0 x0 t; destruct H100.
  lets H100 : H2 H1; destruct H100.
  eexists; eapply EnvMod.join_get_get_r; eauto.
  
  apply ListSet_set_In_cons_intro.
  lets H100 : H0 x0 t; destruct H100.
  lets H100 : EnvMod.join_disj_meq H; mytac.
  (* ** ac: SearchAbout EnvMod.meq. *)
  apply EnvMod.meq_eq in H5.
  subst.
  rewrite EnvMod.merge_sem in H1.
  assert (x0 = x \/ x0 <> x) as H100 by repeat decide equality; destruct H100.
  subst.
  rewrite EnvMod.get_sig_some in H1.
  destruct (EnvMod.get E1 x); inverts H1; auto.
  rewrite EnvMod.get_sig_none in H1; auto.
  right.
  apply H3.
  unfold get.
  simpl.
  destruct (EnvMod.get E1 x0); tryfalse || eauto.
Qed.

Lemma join_join_getgenv : forall o o' M1 M2  G E M isr aux,
                    joinmem o M1 o' -> joinmem o' M2 (G,E,M,isr,aux) -> get_genv (get_smem o) = G.
Proof.
  intros.
  unfold joinmem in *; mytac.
  simpl; auto.
Qed.

Lemma join_join_getlenv : forall o o' M1 M2  G E M isr aux,
                    joinmem o M1 o' -> joinmem o' M2 (G,E,M,isr,aux) -> get_lenv (get_smem o) = E.
Proof.
  intros.
  unfold joinmem in *; mytac.
  simpl; auto.
Qed.

Lemma join_eqenv : forall o M o', joinmem o M o' -> eqenv o o'.
Proof.
  intros.
  unfold joinmem in *; mytac.
  unfold eqenv; auto.
Qed.

Lemma eqenv_trans : forall o o' o'', eqenv o o' -> eqenv o' o'' -> eqenv o o''.
Proof.
  intros.
  destruct o as [ [ [ [ ] ] ] ]; simpl.
  destruct o' as [ [ [ [ ] ] ] ]; simpl.
  destruct o'' as [ [ [ [ ] ] ] ]; simpl.
  unfold eqenv in *; mytac.
Qed.

Lemma eqenv_comm: forall o o', eqenv o o' -> eqenv o' o.
  intros.
  destruct o as [ [ [ [ ] ] ] ]; simpl.
  destruct o' as [ [ [ [ ] ] ] ]; simpl.
  unfold eqenv in *; mytac.
Qed.

Lemma joinmem_eqg : forall o M o', joinmem o M o' ->  get_genv (get_smem o) =  get_genv (get_smem o').
Proof.
  intros.
  unfold joinmem in *; mytac.
  simpl in *; auto.
Qed.

