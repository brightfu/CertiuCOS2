Require Import include_frm.
Require Import oscorrectness.
Require Import simulation.
Require Import auxdef.
Require Import Classical.
Require Import sep_auto.
Require Import base_tac.
Require Import soundness.
Require Import absinfer_sound.
Require Import memory_prop.
Require Import joinmemLib.
Require Import lmachLib.
Require Import rulesoundlib.

Import DeprecatedTactic.
Require Import mem_join_lemmas.
Require Import invariant_prop_lemmas.

Ltac simpl_map1 :=
  match goal with
    | H:exists _, _ |- _ => destruct H; simpl_map1
    | H:_ /\ _ |- _ => destruct H; simpl_map1

    | H: emposabst _ |- _ => unfold emposabst in H; subst; simpl_map1
 
    | H:join empenv _ _ |- _ => apply map_join_comm in H; apply map_join_emp' in H; subst; simpl_map1
    | H:join _ empenv _
      |- _ =>
      apply map_join_emp' in H; subst; simpl_map1
    | |- join empenv _ _ => apply map_join_comm; apply map_join_emp; simpl_map1
    | |- join _ empenv _ => apply map_join_emp; simpl_map1
    | H:join ?a ?b ?ab |- join ?b ?a ?ab => apply map_join_comm; auto
    | H:(_, _) = (_, _) |- _ => inversion H; clear H; simpl_map1
    | H:?x = ?x |- _ => clear H; simpl_map1
    | |- ?x = ?x => reflexivity
    | |- join _ ?a ?a => apply map_join_comm; simpl_map1
    | |- join ?a _ ?a => apply map_join_emp; simpl_map1
    | |- empenv = _ => reflexivity; simpl_map1
    | |- _ = empenv => reflexivity; simpl_map1
    | H:True |- _ => clear H; simpl_map1
    | |- True => auto
    | _ => try (progress subst; simpl_map1)
  end.

Ltac simpljoin1 := repeat progress simpl_map1.

Lemma sat_split' :
  forall P Q G E M isr auxs O absop,
    (exists m1 m2 o1 o2,
        join m1 m2 M /\ join o1 o2 O /\
        (G, E, m1, isr, auxs, o1, absop)|= P /\
        (G, E, m2, isr, auxs, o2, absop)|= Q) ->
    (G, E, M, isr, auxs, O, absop)|= P ** Q.
Proof.
  intros.
  mytac.
  simpl; do 6 eexists.
  splits; eauto.
Qed.


Lemma swpre_store
: forall (ge le : env) (Mc : mem) (ir : isr) 
         (au : localst) (O : osabst) (ab : absop) 
         (x : var) (tp : type) (b : block) (t t' : addrval) 
         (sc : ossched) I li,
    GoodI I sc li->
    (ge, le, Mc, ir, au, O, ab) |= SWINVt I t' ->
    (ge, le, Mc, ir, au, O, ab) |= SWPRE sc x t' ->
    EnvMod.get ge OSTCBCur = Some (b, tp) ->
    exists Mc', store tp Mc (b, 0%Z) (Vptr t) = Some Mc'.
Proof.
  intros.
  unfold SWPRE in H1.
  sep normal in H1.
  do 3 destruct H1.
  sep remember (1::nil)%nat in H1.
  simpl in H1; mytac.
  unfold get in H12; simpl in H12.
  rewrite H12 in H2; inverts H2.
  eapply store_exist_join'; eauto.
Qed.


Lemma GoodI_SWINV_indom_curt:
  forall I o O sc t li P,
    GoodI I sc li->
    (forall ab, (o, O, ab) |= SWINVt I t ** P) ->
    indom O curtid.
Proof.
  intros.
  unfold GoodI in *.
  destructs H.
  lets H10: H0 (spec_done None).
  remember (SWINVt I t) as X.
  simpl in H10;mytac.
  eapply H1 in H8.
  mytac.
  eapply get_indom;eauto.
  eexists;eapply join_get_l;eauto.
Qed.


Lemma goodI_swinv_samet: 
  forall ge le M ir au O ab I sc t li Mx Ox MM OO,
    GoodI I sc li->
    join Mx M MM ->
    join Ox O OO ->
    (ge, le, M, ir, au, O, ab) |= SWINVt I t  ->
    (ge, le, Mx, ir, au, Ox, ab) |= (EX lg' : list logicvar, LINV li t lg' ** Atrue)  ->
    (ge, le, M, ir, au, O, ab) |= AHprio sc t ** Atrue -> 
    (exists b tp, get ge OSTCBCur = Some (b,(Tptr tp)) /\
                  load (Tptr tp) M (b,0%Z) = Some (Vptr t) /\ get O curtid = Some (oscurt t)) /\
    ( forall b tp M', get O curtid = Some (oscurt t) -> get ge OSTCBCur = Some (b,(Tptr tp))  -> store (Tptr tp) M (b,0%Z) (Vptr t) = Some M' ->  (ge, le, M', ir, au, O, ab) |= SWINVt I t ).
Proof.
  intros.
  unfold GoodI in *.
  destruct H.
  destruct H5.
  destruct H6.
  unfolds in H7.
  mytac.
  assert (ge= get_genv (get_smem (ge, le, M, ir, au))).
  simpl;auto.
  assert (M= get_mem (get_smem (ge, le, M, ir, au))).
  simpl;auto.
  rewrite H10.
  rewrite H11;auto.
  apply H5 with (ab:=ab).
  auto.
  intros.
  assert ((ge, le, M', ir, au)= substaskst (ge, le, M, ir, au) M').
  simpl;auto.
  rewrite H13.
  assert (set O curtid (oscurt t)=O).
  eapply get_set_same;eauto.
  rewrite <- H14.
  destruct H6 with (o:=(ge, le, M, ir, au)) (O:=O) (ab:=ab) (tid:=t) (b:=b) (tp:=tp) (M':=M') (ct:=t);auto.
  destruct H15.
  destruct H16.
  destruct H16;auto.
  destruct H16.
  clear -H8 H16 H4 H7 H15.
  simpl in H4.
  mytac.
  eapply H7 in H2;eauto.
  apply H8 in H2.
  mytac.
  rewrite H in H15;inverts H15.
  destruct H16;unfolds;eauto.
Qed.

Lemma projs_eqg:forall (o : env * EnvSpec.B * mem * isr * LocalStSpec.B)
                       (Sl : osstate) (t : tid),
                  projS Sl t = Some o -> fst (fst (fst (fst Sl))) = fst (fst (fst (fst o))).
Proof.
  intros.
  destruct Sl as [[[[]]]].
  destruct o as [[[[]]]].
  unfold projS in *;unfold projD in *.
  destruct (get c t );tryfalse.
  destruct (get l t);tryfalse.
  inverts H;simpl;auto.
Qed.


Lemma part_storebytes_part :
  forall vl Tm Tl Ml Mc b o t Mc',
    partM Ml Tl Tm -> TMSpecMod.maps_to Tm t Mc ->
    storebytes Mc (b, o) vl = Some Mc' ->
    exists Ml', storebytes Ml (b, o) vl = Some Ml' /\ partM Ml' Tl (TMSpecMod.put Tm t Mc').
Proof.
  intros.
  induction H; intros.
  unfolds in H0.
  tryfalse.

  destruct (tidspec.beq t0 t) eqn : eq1.
  lets Hx: tidspec.beq_true_eq eq1; substs.
  unfolds in H0.
  rewrite H in H0; inverts H0.
  lets Hx: storebytes_mono H2 H1; simpljoin.
  lets Hx1: join_storebytes H2 H1 H0.
  exists x.
  split; auto.
  assert(TMSpecMod.remove (TMSpecMod.put Tm t Mc') t = TMSpecMod.remove Tm t).
  rewrite TMSpecMod.remove_cancel_put; auto.
  rewrite <- H4 in H3.
  eapply partm_S; eauto.
  rewrite TMSpecMod.put_get_eq; auto.

  apply tidspec.beq_false_neq in eq1.
  lets Hx: TMSpecMod.removeX_presv_Y eq1 H0.
  apply IHpartM in Hx; simpljoin.
  apply join_comm in H2.
  lets Hx: storebytes_mono H2 H4; simpljoin.
  lets Hx1: join_storebytes H2 H4 H6.
  exists x0.
  split; auto.
  rewrite <- TMSpecMod.remove_ext_ext_remove in H5.
  apply join_comm in Hx1.
  eapply partm_S; eauto.
  rewrite TMSpecMod.put_noninterfere; auto.
  auto.
Qed.


Lemma part_store_part:
  forall Tm Tl Ml Mc l v t tp Mc',
    partM Ml Tl Tm ->
    TMSpecMod.maps_to Tm t Mc ->
    store tp Mc l v = Some Mc' ->
    exists Ml',store tp Ml l v = Some Ml' /\ partM Ml' Tl (TMSpecMod.put Tm t Mc').  
Proof.
  intros.
  unfold store in H1.
  destruct l.
  unfold store.
  eapply part_storebytes_part; eauto.
Qed.



Lemma disj_get_eq:forall O Os a x x', OSAbstMod.disj O Os -> OSAbstMod.get O a = Some x -> OSAbstMod.get (OSAbstMod.merge O Os) a = Some x' -> x = x'.
Proof.
  intros.
  rewrite OSAbstMod.merge_sem in H1.
  rewrite H0 in H1.
  unfold OSAbstMod.disj in H; pose proof H a; clear H.
  rewrite H0 in H2.
  destruct (OSAbstMod.get Os a) eqn : eq1; tryfalse.
  inv H1; auto.
Qed.

Lemma projs_eqm: forall o Sl t,  projS Sl t = Some o -> (snd (fst (fst Sl))) = (snd (fst (fst o))).
Proof.
  intros.
  destruct o.
  destruct p.
  destruct p.
  destruct p.
  unfold projS in H.
  destruct Sl.
  destruct p.
  unfold projD in H.
  destruct c.
  destruct p.
  destruct (get c t).
  destruct (get l0 t).
  inversion H.
  subst.
  simpl.
  reflexivity.
  inversion H.
  inversion H.
Qed.

Lemma part_merge_m:
  forall M T Tm M' t C Mc, 
    TMSpecMod.maps_to Tm t Mc -> 
    disjoint M M' ->
    partM M T Tm ->
    partM (merge M M') (TasksMod.set T t C) (TMSpecMod.put Tm t (merge Mc M')).   
Proof.
  intros.
  gen M' t C Mc.
  inductions H1; intros.
  unfolds in H1; tryfalse.

  destruct (tidspec.beq t0 t) eqn : eq1.
  apply tidspec.beq_true_eq in eq1; substs.
  unfolds in H3.
  rewrite H in H3; inverts H3.
  assert ((TMSpecMod.remove Tm t) = (TMSpecMod.remove ((TMSpecMod.put Tm t (merge Mc M'0))) t)).
  rewrite TMSpecMod.remove_cancel_put; auto.
  rewrite H3 in H1.
  assert(join (merge Mc M'0) M' (merge M M'0)).

  eapply mem_join_disjoint_merge; auto.
  eapply partm_S; eauto.
  rewrite TMSpecMod.put_get_eq; auto.

  assert (disjoint M' M'0).
  apply join_comm in H0.
  eapply mem_join_disjoint_disjoint; eauto.
  assert (TMSpecMod.maps_to (TMSpecMod.remove Tm t) t0 Mc).
  eapply TMSpecMod.removeX_presv_Y; auto.
  apply tidspec.beq_false_neq in eq1; auto.
  lets Hx1: IHpartM M'0 H4 H5.
  rewrite <- TMSpecMod.remove_ext_ext_remove in Hx1.
  assert(join (merge M' M'0) m (merge M M'0)).
  apply join_comm in H0.
  eapply mem_join_disjoint_merge; auto.
  assert ((TMSpecMod.put Tm t0 (merge Mc M'0)) t = Some m).
  rewrite TMSpecMod.put_noninterfere; auto.
  apply tidspec.beq_false_neq; auto.
  eapply partm_S; eauto.
  apply join_comm; auto.

  instantiate (TEMP1:=C).
  apply tidspec.beq_false_neq; auto.
Qed.

Lemma part_merge_o:
  forall M T Tm M' t C Mc, 
    TOSpecMod.maps_to Tm t Mc -> 
    disjoint M M' ->
    partO M T Tm ->
    partO (merge M M') (TasksMod.set T t C) (TOSpecMod.put Tm t (merge Mc M')).
Proof.
  intros.
  gen M' t C Mc.
  inductions H1; intros.
  unfolds in H1; tryfalse.

  destruct (tidspec.beq t0 t) eqn : eq1.
  apply tidspec.beq_true_eq in eq1; substs.
  unfolds in H3.
  rewrite H in H3; inverts H3.
  assert ((TOSpecMod.remove Tm t) = (TOSpecMod.remove ((TOSpecMod.put Tm t (merge Mc M'0))) t)).
  rewrite TOSpecMod.remove_cancel_put; auto.
  rewrite H3 in H1.
  assert(join (merge Mc M'0) M' (merge M M'0)).
  
  eapply osabst_join_disjoint_merge; auto.
  eapply parto_S; eauto.
  rewrite TOSpecMod.put_get_eq; auto.

  assert (disjoint M' M'0).
  apply join_comm in H0.
  apply disjoint_sym in H2.
  apply disjoint_sym.
  eapply disj_trans_sub; eauto.
  unfolds.
  eauto.

  assert (TOSpecMod.maps_to (TOSpecMod.remove Tm t) t0 Mc).
  eapply TOSpecMod.removeX_presv_Y; auto.
  apply tidspec.beq_false_neq in eq1; auto.
  lets Hx1: IHpartO M'0 H4 H5.
  rewrite <- TOSpecMod.remove_ext_ext_remove in Hx1.
  assert(join (merge M' M'0) m (merge M M'0)).
  apply join_comm in H0.
  eapply osabst_join_disjoint_merge; auto.
  assert ((TOSpecMod.put Tm t0 (merge Mc M'0)) t = Some m).
  rewrite TOSpecMod.put_noninterfere; auto.
  apply tidspec.beq_false_neq; auto.
  eapply parto_S; eauto.
  apply join_comm; auto.

  instantiate (TEMP1:=C).
  apply tidspec.beq_false_neq; auto.
Qed.


Lemma part_disjm:
  forall M T Tm Ms t Mc, 
    TMSpecMod.maps_to Tm t Mc -> 
    partM M T Tm -> disjoint M Ms -> disjoint Mc Ms.  
Proof.
  intros.
  inductions H0.
  tryfalse.

  destruct (tidspec.beq t0 t) eqn : eq1.
  apply tidspec.beq_true_eq in eq1; substs.
  unfolds in H.
  rewrite H in H0; inverts H0.
  eapply mem_join_disjoint_disjoint; eauto.

  apply IHpartM.
  apply TMSpecMod.removeX_presv_Y; auto.
  apply tidspec.beq_false_neq in eq1; auto.
  apply join_comm in H1.
  eapply mem_join_disjoint_disjoint; eauto.
Qed.

Lemma part_disjo:
  forall M T Tm Ms t Mc, 
    TOSpecMod.maps_to Tm t Mc -> 
    partO M T Tm -> disjoint M Ms -> disjoint Mc Ms.  
Proof.
  intros.
  inductions H0.
  tryfalse.

  destruct (tidspec.beq t0 t) eqn : eq1.
  apply tidspec.beq_true_eq in eq1; substs.
  unfolds in H.
  rewrite H in H0; inverts H0.

  eapply osabst_join_disjoint_disjoint; eauto.

  apply IHpartO.
  apply TOSpecMod.removeX_presv_Y; auto.
  apply tidspec.beq_false_neq in eq1; auto.
  apply join_comm in H1.
  eapply osabst_join_disjoint_disjoint; eauto.
Qed.



Lemma CurLINV_merge_hold:
  forall ge le m isr aux O lasrt m' O' t,
    disjoint m m' ->
    disjoint O O' ->
    satp (ge,le,m,isr,aux) O (CurLINV lasrt t) ->
    satp (ge,le,merge m m',isr,aux) (merge O O') (CurLINV lasrt t).
Proof.
  intros.
  apply join_merge_disj in H.
  apply join_merge_disj in H0.
  eapply join_satp_local_inv; eauto.
  unfolds.
  do 6 eexists; splits; eauto.
Qed.


Lemma LINV_ignore_int:
  forall ge le m isr aux O le' isr' aux' lasrt  t,
    satp (ge,le,m,isr,aux) O (EX lg,LINV lasrt t lg ) ->
    satp (ge,le',m,isr',aux') O (EX lg,LINV lasrt t lg ).
Proof.
  intros.
  unfold satp in H.
  intro.
  pose proof H aop.
  destruct H0.
  exists x.

  unfold LINV in *.
  sep split in H0.
  sep split; auto.

  unfold GoodLInvAsrt in H1.
  pose proof H1 t x.
  remember (lasrt t x) as X.
  eapply GoodLocalInvAsrt_irrel; eauto.
  destruct H2;auto.
Qed.


Lemma LInv_ignore_int:
  forall ge le m isr aux O le' isr' aux' lasrt  t,
    satp (ge,le,m,isr,aux) O (EX lg,LINV lasrt t lg ** Atrue) ->
    satp (ge,le',m,isr',aux') O (EX lg,LINV lasrt t lg ** Atrue).
Proof.
  intros.
  unfold satp in H.
  intro.
  pose proof H aop.
  destruct H0.
  exists x.

  unfold LINV in *.
  sep split in H0.
  sep split; auto.

  unfold GoodLInvAsrt in H1.
  pose proof H1 t x.
  remember (lasrt t x) as X.
  eapply GoodLocalInvAsrt_irrel; eauto.
  simpl; auto.
  destruct H2;auto.
Qed.

Lemma CurLINV_ignore_int:
  forall ge le m isr aux O le' isr' aux' lasrt  t,
    satp (ge,le,m,isr,aux) O (CurLINV lasrt t) ->
    satp (ge,le',m,isr',aux') O (CurLINV lasrt t).
Proof.
  intros.
  unfold satp in H.
  intro.
  pose proof H aop.
  eapply Linv_igore; eauto.
Qed.


Lemma tm_mapsto_put': forall Tm t t' a a', t<>t'-> TMSpecMod.maps_to Tm t' a' -> TMSpecMod.maps_to (TMSpecMod.put Tm t a) t' a'.
Proof.
  unfold TMSpecMod.maps_to.
  unfold TMSpecMod.put.
  intros.
  destruct (TMSpecMod.beq_A t' t).
  subst. tryfalse.
  apply H0.
Qed.

Lemma to_mapsto_put': forall Tm t t' a a', t<>t'-> TOSpecMod.maps_to Tm t' a' -> TOSpecMod.maps_to (TOSpecMod.put Tm t a) t' a'.
Proof.
  unfold TOSpecMod.maps_to.
  unfold TOSpecMod.put.
  intros.
  destruct (TOSpecMod.beq_A t' t).
  subst. tryfalse.
  apply H0.
Qed.

Definition absopx := sched.

Open Scope nat_scope.
Lemma invlth_divide:
  forall i j ge le M ir au O ab I,
    i<j ->
    j<= S INUM ->
    (ge,le,M,ir,au,O,ab) |= invlth_isr I 0 j ->
    exists M1 M2 O1 O2,
      join M1 M2 M /\ OSAbstMod.join O1 O2 O  /\
      (ge,le,M1,ir,au,O1,ab) |= invlth_isr I 0 i /\ (ge,le,M2,ir,au,O2,ab) |= invlth_isr I (i+1)%nat j.  
Proof.
  introv Hij Hj Hinv.
  unfold invlth_isr in *.
  replace (j-0) with j in Hinv by omega.
  destruct j.
  inverts Hij.
  assert (i<= j) by omega.
  lets Hres  : starinv_prop H  Hinv.
  destruct Hres; mytac.
  simpl substmo in *.
  simpl getabst in *.
  simpl getmem in *.
  assert ( (S j - (i + 1) =  (S j - S i) ))%nat by omega.
  rewrite H0.
  replace (i+1) with (S i)  by omega.
  replace (i-0) with i by omega.
  do 4 eexists; splits; eauto.
Qed.

Close Scope nat_scope.

Lemma abst_join_join_merge_eq' :
  forall O1 O2 O3 O4 O,
    OSAbstMod.join O1 O2 O ->
    OSAbstMod.join O3 O4 O2 ->
    O = OSAbstMod.merge (OSAbstMod.merge O1 O4) O3.
Proof.
  intros.
  apply OSAbstMod.extensionality.
  intro.
  unfolds in H0. pose proof H0 a. clear H0.
  unfolds in H. pose proof H a. clear H.
  rewrite OSAbstMod.merge_sem.
  rewrite OSAbstMod.merge_sem.
  destruct (OSAbstMod.get O1 a) eqn : eq1;
    destruct (OSAbstMod.get O2 a) eqn : eq2;
    destruct (OSAbstMod.get O3 a) eqn : eq3;
    destruct (OSAbstMod.get O4 a) eqn : eq4;
    destruct (OSAbstMod.get O a) eqn : eq5;
    tryfalse;
    try (subst; auto).
Qed.

Lemma abst_disj_join_disjmerge :
  forall O O' O1 O2,
    OSAbstMod.disj O O' ->
    OSAbstMod.join O1 O2 O' ->
    OSAbstMod.disj (OSAbstMod.merge O2 O) O1.
Proof.
  intros.
  unfolds.
  intro.
  unfolds in H0.
  pose proof (H0 a). clear H0.
  rewrite OSAbstMod.merge_sem.
  destruct (OSAbstMod.get O1 a) eqn : eq1;
    destruct (OSAbstMod.get O2 a) eqn : eq2;
    destruct (OSAbstMod.get O a) eqn : eq3;
    destruct (OSAbstMod.get O' a) eqn : eq4;
    tryfalse;
    try (subst; auto).
  eapply OSAbstMod.disj_indom in H.
  destruct H.
  apply H.
  unfolds.
  eexists.
  apply eq3.
  unfolds.
  eexists.
  apply eq4.
Qed.

Ltac destruct_get :=
  let a := fresh in
  match goal with
  | H : (match ?X with | Some _ => _ | None => _ end) |- _ => destruct X eqn : a; tryfalse; destruct_get
  | _ => idtac
  end.

Lemma osabst_disj_disjoint :
  forall (o1:osabst) o2,
    OSAbstMod.disj o1 o2 ->
    disjoint o1 o2.
Proof.
  intros.
  unfolds.
  unfold join; simpl.
  exists (OSAbstMod.merge o1 o2).
  unfolds; intro.
  pose proof H a.
  rewrite OSAbstMod.merge_sem.
  destruct_get; auto.
Qed.

Lemma abst_join_disj_disj:
  forall O1 O2 O' O,
    OSAbstMod.join O1 O2 O ->
    OSAbstMod.disj O O' ->
    OSAbstMod.disj O1 O'.
Proof.
  intros.
  unfolds.
  intro.
  unfolds in H.
  pose proof H a. clear H.
  pose proof H0 a. clear H0.
  destruct (OSAbstMod.get O1 a) eqn : eq1;
    destruct (OSAbstMod.get O2 a) eqn : eq2;
    destruct (OSAbstMod.get O a) eqn : eq3;
    destruct (OSAbstMod.get O' a) eqn : eq4;
    tryfalse;
    try (subst; auto).
Qed.

Lemma starinv_isr_prop4' :
  forall j i G E M isr ie is cs ie' cs' O aop  I, 
    (G,E,M,isr,(ie,is,cs),O,aop) |=  starinv_isr I (S i) j -> 
    (G,E,M,(isrupd isr i true),(ie',i::is,cs'),O,aop) |=  starinv_isr I (S i) j.
Proof.
  inductions j.
  simpl   starinv_isr in *.
  introv Hdat.
  destruct Hdat;mytac.  
  destruct H;mytac.
  destruct H;mytac.
  simpl in H;simpl in H0;mytac.
  exists ( isrupd x i true).
  left.  
  splits; simpl;mytac.
  unfolds.
  rewrite   beq_nat_false. 
  auto.
  destruct H;mytac.
  trysimplsall.
  destruct H3;mytac.
  simpl in H; simpl in H1;mytac.
  exists ( isrupd x i true).  
  right.
  exists empmem M M empabst O O.
  trysimplsall.
  splits; mytac;eauto.
  splits;simpl;mytac;eauto.
  unfolds.
  rewrite  beq_nat_false;auto.
  destruct (prec (I (S i))) as [Hi Hj].
  destruct Hj as (Hj1&Hj2&Hj3&Hj4).
  lets Hrs : Hj2 H4.
  simpl set_isisr_s in Hrs.
  eapply good_inv_prop.
  apply invp.
  apply Hrs. 
  introv Hsat.
  eapply starinv_prop1_rev.
  apply starinv_prop1 in Hsat.
  destruct Hsat;mytac.
  trysimplsall.  
  destruct H4;mytac.
  destruct H;mytac.
  exists x x0 M x2 x3 O.
  trysimplsall.
  splits; mytac;eauto.
  destruct H;mytac.
  simpl in H;simpl in H1; mytac.
  exists (isrupd x1 i true).
  left.
  simpl;splits;mytac.  
  unfolds.
  rewrite   beq_nat_false2. 
  auto.
  exists x x0 M x2 x3 O.
  trysimplsall.
  splits; mytac;eauto.
  destruct H;mytac.
  trysimplsall.
  destruct H6;mytac.
  simpl in H;simpl in H4; mytac.
  lets Hs : IHj  H3.
  exists (isrupd x1 i true).
  right.  
  exists empmem x0 x0 empabst x3 x3. 
  trysimplsall; splits; mytac; eauto.
  splits; simpl; mytac; eauto.
  unfolds.
  rewrite   beq_nat_false2. 
  auto.
  destruct (prec (I (S (S (i + j))))) as [Hi Hj].
  destruct Hj as (Hj1&Hj2&Hj3&Hj4).
  lets Hrs : Hj2 H7.
  simpl set_isisr_s in Hrs.
  eapply good_inv_prop.
  apply invp.
  eauto.
  Grab Existential Variables. 
  exact nil.   
  exact false.
Qed.


Lemma good_inv_prop :
  forall p, GoodInvAsrt p ->
            forall ge le M ir ie is cs abst op,
              (ge, le, M ,ir, (ie ,is,cs), abst, op) |= p ->
              forall le' op' ie' cs',
                (ge,le', M, ir, (ie',is,cs') ,abst, op') |= p.
Proof.
  introv.
  inductions p; introv Hgood; introv Hsat; introv; simpl in *;  tryfalse; auto.
  destruct Hsat as [Hsat1 Hsat2].
  destruct Hgood as [Hgp Hgq].
  lets Hgpp : IHp1 Hgp Hsat1.
  lets Hgqq : IHp2 Hgq Hsat2.
  splits.
  eapply Hgpp; eauto.
  eapply Hgqq; eauto.
  destruct Hgood as [Hgp Hgq].
  destruct Hsat as [Hsat1 | Hsat2].
  lets Hgpp : IHp1 Hgp Hsat1.
  left.
  eapply Hgpp; eauto.
  lets Hgqq : IHp2 Hgq Hsat2.
  right.
  eapply Hgqq; eauto.
  simpl in Hgood.
  destruct Hgood as [Hgp Hgq].
  destruct Hsat.
  repeat destruct H.
  destruct H0.
  destruct H0.
  destruct H1.
  destruct H2.
  subst.
  do 6 eexists.
  splits; eauto.
  destruct Hsat as [x Hsatx].
  lets Hp : H (Hgood x) Hsatx.
  exists x.
  eapply Hp; eauto.
Qed.


Lemma  inv_isr_irrev_prop_noempisr :
  forall n low I ge ir le M  ie is cs ie' cs'  abst op, 
    (ge, le, M , ir , (ie,is,cs), abst, op) |= starinv_isr I low n -> 
    forall le' op',
      (ge, le', M ,ir , (ie',is,cs'), abst, op') |= starinv_isr I low n.   
Proof.
  inductions n.
  simpl starinv_isr.
  introv Hsat.
  introv.
  simpl.
  simpl in Hsat.
  destruct Hsat.
  exists x.
  destruct H.
  left; auto.
  right.
  repeat destruct H.
  destruct H0 as (Hm & Hx & Hdj & Hf & Hsa).
  do 6 eexists; splits; eauto.
  eapply good_inv_prop.
  eapply (invp  (I low)).
  eauto.
  
  introv Hsat.
  introv.
  simpl starinv_isr.
  simpl starinv_isr in Hsat.
  unfold sat in Hsat.
  fold sat in Hsat.
  simpl substmo in Hsat.
  unfold sat.
  fold sat.
  simpl substmo.
  simpl getabst in *.
  simpl gettaskst in *.
  simpl empst in *.
  destruct Hsat as (M1 & M2 & M0 & o1 & o2 & o & Hsat).
  destruct Hsat as (HM & Hmm & Ho & Habsj & Hsat).
  simpl assertion.getmem in *.
  exists M1 M2 M0 o1 o2 o; splits; auto.
  destruct Hsat as (Hsat & Hss).
  destruct Hsat.
  exists x.
  destruct H.
  left; auto.
  right.
  repeat destruct H.
  destruct H0 as (Hm & Hx & Hdj & Hf & Hsa).
  do 6 eexists; splits; eauto.
  
  eapply good_inv_prop.
  eapply (invp  (I low)).
  eauto.
  destruct Hsat.
  eapply IHn; eauto.
Qed.

Open Scope nat_scope.
Lemma isr_true_S_i_rev:
  forall I i ge le M ir ie is cs ie' cs' ab ab' O j,
    i<j ->
    (ge,le,M,ir,(ie,is,cs),O,ab) |= invlth_isr I (i+1)%nat j ->
    (ge,le,M,isrupd ir i true,(ie',i::is,cs'),O,ab') |= invlth_isr I (i+1)%nat j.
Proof.
  introv Hij Hinv.
  unfold  invlth_isr in *.
  replace (i+1) with (S i) in * by omega. 
  eapply  starinv_isr_prop4' ; eauto.
  eapply inv_isr_irrev_prop_noempisr; eauto.
  Grab Existential Variables. 
  exact nil.   
  exact false.
Qed.
Close Scope nat_scope.

Lemma int_mem_trans1
: forall sd p C C' o o' Ms I Os Ml li,
    GoodI I sd li->
    lintstep p C o C' o' ->
    disjoint Ml Ms ->
    merge Ml Ms = get_mem (get_smem o) ->
    (forall ab : absop, (substaskst o Ms, Os, ab) |= INV I) ->
    exists Ms' Ml' Os' Ol,
      Ms = merge Ml' Ms' /\
      disjoint Ml' Ms' /\
      Os = merge Os' Ol /\
      disjoint Ol Os' /\
      (forall ab : absop, (substaskst o' Ms', Os', ab) |= INV I).
Proof.
  introv Hgoodi.
  intros.
  destruct o as [[[[]]]].
  destruct o' as [[[[]]]].
  inversion H;subst.
  simpl in H1.
  subst m0.
  
  lets Hinv: H2 absopx.
  unfold INV in *.
  unfold sat in Hinv;fold sat in Hinv;trysimplsall;mytac;tryfalse.
  destruct H7.
  Focus 2.
  unfold inv_ieoff in H1;unfold sat in H1;fold sat in H1;trysimplsall;mytac;tryfalse.
  unfold inv_ieon in *.
  unfold sat in H1;fold sat in H1;trysimplsall;mytac.
  simpl in H11.
  unfold emposabst in *.
  destruct H11.
  subst.
  unfold assertion.getmem in *.
  unfold get_smem in *; unfold get_mem in *.
  
  apply join_emp_eq in H4.
  subst x4.
  apply join_emp_eq in H8.
  subst x7.
  
  apply invlth_divide with (i:=i1) in H10;auto.
  mytac.
  exists (merge x x4) x1 (merge x2 x6) x5.
  mytac.

  eapply mem_join_join_merge_eq;eauto.
  apply disjoint_sym.
  apply mem_join_disjoint_eq_merge in H3.
  destruct H3.
  assert (disjoint (merge x4 x) x1).
  Lemma invariant_prop_map1 :
    forall (A B T : Type) (MC : PermMap A B T) x x0 x1 x4,
      usePerm = true ->
      disjoint x x0 ->
      join x1 x4 x0 ->
      disjoint (merge x4 x) x1.
    hy.
    (** TODO **)
  Qed.
  eapply invariant_prop_map1; eauto.
  
  (* eapply mem_disj_join_disjmerge;eauto. *)
  (* apply disj_merge_intro_l . *)
  (* apply disj_merge_elim_l in H10. *)
  (* destruct H10. *)
  (* auto. *)
  Lemma invariant_prop_map2 :
    forall (A B T : Type) (MC : PermMap A B T) x x0 x1 x4,
      usePerm = true ->
      disjoint x x0 ->
      join x1 x4 x0 ->
      disjoint (merge x x4) x1.
    hy.
    (** TODO **)
  Qed.
  eapply invariant_prop_map2; eauto.
  
  eapply abst_join_join_merge_eq';eauto.
  apply disjoint_sym.
  apply OSAbstMod.join_disj_meq in H5.
  destruct H5.
  assert (OSAbstMod.disj (OSAbstMod.merge x6 x2) x5).

  eapply abst_disj_join_disjmerge;eauto.
  apply disj_merge_intro_l.
  unfold usePerm; simpl; auto.
  apply OSAbstMod.disj_merge_elim_l in H10.
  destruct H10.
  apply osabst_disj_disjoint in H10.
  apply osabst_disj_disjoint in H11.
  split; auto.
  
  intros.
  unfold sat;fold sat;trysimplsall;mytac.
  unfold assertion.getmem.
  unfold get_mem; unfold get_smem.
  exists x x4 (merge x x4) x2 x6 (OSAbstMod.merge x2 x6).
  mytac.
  apply join_merge_disj.
  apply mem_join_disjoint_eq_merge in H3.
  destruct H3.
  apply join_comm in H1.
  apply disjoint_sym in H3.
  apply disjoint_sym.
  eapply mem_join_disjoint_disjoint; eauto.
  unfold merge; simpl; auto.
  
  apply OSAbstMod.join_merge_disj.
  apply OSAbstMod.join_disj_meq in H5.
  destruct H5.
  apply OSAbstMod.join_comm in H4.
  apply OSAbstMod.disj_sym in H5.
  apply OSAbstMod.disj_sym.

  eapply abst_join_disj_disj;eauto.
  eapply good_inv_prop;eauto.
  apply invp.
  assert (inv_prop (getinv (I (S INUM)))).
  apply prec.
  unfolds in H9.
  destruct H9.
  unfolds in H10.
  mytac.
  eapply H11 with (i:=i1) in H6.
  simpl in H6.
  eapply H6.
  right.
  unfold inv_ieoff.
  unfold sat;fold sat;trysimplsall;mytac.
  exists empmem x4 x4 empabst x6 x6;mytac.
  simpl;unfold emposabst;auto.
  simpl; split; auto.
  unfolds; auto.
  exists i1.
  exists empmem x4 x4 empabst x6 x6;mytac.
  simpl;unfold emposabst;auto.
  simpl; unfold emposabst; auto.
  left.
  exists empmem x4 x4 empabst x6 x6;mytac.
  auto.
  simpl;unfold emposabst;auto.
  simpl; unfold emposabst; auto.
  
  eapply isr_true_S_i_rev;eauto.
  unfold invlth_isr in *.
  eapply inv_isr_irrev_prop;eauto.
  Grab  Existential Variables.
  trivial.
Qed.

Lemma int_mem_trans
: forall sd p C C' o o' Ms I Os Ml li,
    GoodI I sd li->
    lintstep p C o C' o' ->
    join Ml Ms (get_mem (get_smem o)) ->
    (forall ab : absop, (substaskst o Ms, Os, ab) |= INV I) ->
    exists Ms' Ml' Os' Ol,
      join Ml' Ms' Ms /\
      join Ol Os' Os /\
      (forall ab : absop, (substaskst o' Ms', Os', ab) |= INV I).
Proof.
  intros.
  assert (disjoint Ml Ms).
  eapply my_join_disj; eauto.
  assert (merge Ml Ms = get_mem (get_smem o)).
  erewrite join_merge; eauto.
  lets Hx: int_mem_trans1 H H0 H3 H4 H2.
  simpljoin.
  do 4 eexists; splits; eauto.
  eapply join_merge_disj; auto.
  apply join_comm.
  apply disjoint_sym in H8.
  eapply join_merge_disj; eauto.
Qed.

(* tactics *)
Require Import symbolic_lemmas.

Lemma mapsto_load_eq:
  forall m m' M a t v v',
    join m m' M -> mapstoval a (Tptr t) true (Vptr v) m ->
    load (Tptr t) M a = Some (Vptr v') -> v =v'.
Proof.
  intros.
  lets Hx: mapstoval_load H0.
  simpl; auto.
  lets Hx1: load_mem_deter Hx H1.
  assert (Maps.sub m M).
  eapply join_sub_l; eauto.
  apply Hx1 in H2; inverts H2; auto.
Qed.

Lemma mapsto_false_load_eq:
  forall m m' M a t v v',
    join m m' M -> mapstoval a (Tptr t) false (Vptr v) m ->
    load (Tptr t) M a = Some (Vptr v') -> v =v'.
Proof.
  intros.
  lets Hx: mapstoval_load H0.
  simpl; auto.
  lets Hx1: load_mem_deter Hx H1.
  assert (Maps.sub m M).
  eapply join_sub_l; eauto.
  apply Hx1 in H2; inverts H2; auto.
Qed.

Lemma tasks_set_eq_set2:
  forall T t x y,
    TasksMod.set T t x = TasksMod.set (TasksMod.set T t y) t x .
Proof.
  intros.
  apply TasksMod.extensionality .
  intros.
  assert (t=a \/ t<>a) by tauto.
  destruct H.
  subst t.
  rewrite TasksMod.set_a_get_a.
  rewrite TasksMod.set_a_get_a.
  auto.
  apply tidspec.eq_beq_true;auto.
  apply tidspec.eq_beq_true;auto.
  rewrite TasksMod.set_a_get_a'.
  rewrite TasksMod.set_a_get_a'.
  rewrite TasksMod.set_a_get_a'.
  auto.
  apply tidspec.neq_beq_false;auto.
  apply tidspec.neq_beq_false;auto.
  apply tidspec.neq_beq_false;auto.
Qed.


Lemma sw_same_t :
  forall (x : var) (tst : taskst) O
         (p : progunit * (osapispec * osintspec * ossched)) 
         (cst : clientst) (T : TasksMod.map) (t' : addrval) 
         (l : block) (tp : type) O' (Cl : CodeSpec.B) 
         (t : tidspec.A) (sleft : spec_code)k,
    GoodSched (snd (snd p)) ->
    TasksMod.get T t = Some Cl ->
    get O curtid = Some (oscurt t) ->
    (forall ab : absop, (tst, O, ab) |= SWPRE (snd (snd p)) x t) ->
    EnvMod.get (get_genv (get_smem tst)) x = Some (l, Tptr tp) ->
    load (Tptr tp) (get_mem (get_smem tst)) (l, 0%Z) = Some (Vptr t') ->
    set O curtid (oscurt t') = O' ->
    hpstep p
           (TasksMod.set T t (curs (hapi_code (sched;; sleft)),k))
           cst O (TasksMod.set T t (curs (hapi_code sleft), k)) cst O' /\
    (forall ab : absop, (tst, O, ab) |= AHprio (snd (snd p)) t' ** Atrue).
Proof.
  introv Hgood Htget Hogetct.
  intros.
  destruct k as (keh & ksh).
  fold get_smem in *.
  destruct tst as [ [ ] ].
  subst O'.
  
  lets H100 : H absopx; clear H; rename H100 into H;  simpl in H.
  destruct s as [ [ ] ]; simpl in H; mytac.
  simpl in H0.
  unfold get in H34; simpl in H34.
  rewrite H34 in H0.
  inversion H0;subst.
  assert (x0=t').
  eapply mapsto_load_eq; eauto.

  subst  x0.
  destruct p.
  destruct p0.
  destruct p0.
  simpl in H5.
  eapply hswi_step;eauto.
  simpl in H5.
  unfolds in Hgood.
  destructs Hgood.
  eapply H; simpl; eauto.
  unfold get; simpl.
  rewrite TasksMod.set_a_get_a; eauto.
  apply tidspec.eq_beq_true;auto.
  apply tasks_set_eq_set2.

  intros.
  simpl;mytac.
  exists empmem m m.
  do 3 eexists;splits;eauto.
  mytac.
  splits;auto.
  unfold get_smem in *.
  unfold get_mem in *.
  unfold get_genv in *.
  unfold get in H34; simpl in H34.
  rewrite H34 in H0;inverts H0.
  rewrite Int.unsigned_zero in H35.
  apply mapstoval_load in H35.
  apply load_mem_mono with (M':=m) in H35.
  rewrite H1 in H35;inverts H35;auto.
  eapply join_sub_l;eauto.
  simpl;auto.
Qed.

Lemma OSAbstMod_join_exists_merge :
  forall O1 O2 O12 O,
    OSAbstMod.join O1 O2 O12 ->
    exists O', OSAbstMod.join O1 O' (OSAbstMod.merge O12 O).
Proof.  
  introv Hj.
  eapply OSAbstMod.sub_exists_join.
  apply OSAbstMod.join_sub_l in Hj.
  unfolds.
  introv Hlook.
  unfold  OSAbstMod.lookup in *.
  rewrite OSAbstMod.merge_sem.
  apply Hj in Hlook.
  unfolds in Hlook.  
  rewrite Hlook.
  destruct ( OSAbstMod.get O a) ; auto.
Qed.

Lemma swpre_prop1 :
  forall o O M O' x sd t,
    (forall ab : absop, (substaskst o M, O', ab) |= SWPRE sd x t) ->
    Maps.sub M (snd (fst (fst o))) ->
    (forall ab : absop, (o, OSAbstMod.merge O' O, ab) |= SWPRE sd x t).
Proof.
  intros.
  destruct o as [ [ [ [ ] ] ] ]; simpl fst in *; simpl snd in *.
  simpl substaskst in *.
  lets H100 : H ab; clear H; rename H100 into H.
  simpl in *; mytac.
  assert (exists x2, join M x2 m).
  eapply sub_exists_join; auto.
  destruct H.
  lets H100 : join_assoc_l H11 H; mytac.
  lets H100 : OSAbstMod_join_exists_merge H3; mytac.
  lets H100: join_assoc_l H16 H1;mytac.
  do 1 eexists.
  exists empmem m m x4 x3.
  eexists;mytac.
  eauto.
  eauto.
  eauto.
  exists empmem m m empabst.
  do 2 eexists;mytac.
  eauto.
  eauto.
  exists x19;mytac.
  eauto.
  exists x13 x2 m empabst x3 x3.
  mytac.
  auto.
  exists x26 x43.
  exists empmem x13 x13.
  exists empabst empabst empabst.
  mytac.
  eexists;mytac.
  eauto.
  eauto.
  auto.

  exists x20 x6 x2 empabst x3 x3.
  mytac;eauto.
  exists x34 x42.
  exists empmem x20 x20 empabst empabst empabst.
  mytac.
  eexists;eauto.
  mytac.
  eauto.
  eauto.
  eauto.
Qed.


Lemma swpre_prop:
  forall (o : taskst) O O' (M : mem) 
         (x : var) (sd : ossched) t,
    (forall ab : absop, (substaskst o M, O', ab) |= SWPRE sd x t) ->
    Maps.sub M (snd (fst (fst o))) ->
    Maps.sub O' O ->
    forall ab : absop, (o, O, ab) |= SWPRE sd x t.
Proof.
  intros.
  lets Hx: swpre_prop1 H H0 absopx.
  instantiate (1:=minus O O') in Hx.

  rewrite osabst_sub_merge_minus_eq in Hx; auto.
Qed.


Lemma part_sub:
  forall M T Tm Mc t,
    partM M T Tm -> TMSpecMod.maps_to Tm t Mc -> Maps.sub Mc M.
Proof.
  intros.
  inductions H.
  tryfalse.

  destruct (tidspec.beq t0 t) eqn : eq1.
  apply tidspec.beq_true_eq in eq1; substs.
  unfolds in H2.
  rewrite H2 in H; inverts H.
  eapply join_sub_l; eauto.

  assert(TMSpecMod.maps_to (TMSpecMod.remove Tm t0) t Mc).
  eapply TMSpecMod.removeX_presv_Y; auto.
  apply tidspec.beq_false_neq in eq1; auto.
  eapply IHpartM in H3.
  clear - H3 H0.
  assert(Maps.sub M' M).
  eapply join_sub_r; eauto.
  eapply sub_trans; eauto.
Qed.


Lemma parto_sub:
  forall M T Tm Mc t,
    partO M T Tm -> TOSpecMod.maps_to Tm t Mc -> Maps.sub Mc M.
Proof.
  intros.
  inductions H.
  tryfalse.

  destruct (tidspec.beq t0 t) eqn : eq1.
  apply tidspec.beq_true_eq in eq1; substs.
  unfolds in H2.
  rewrite H2 in H; inverts H.
  eapply join_sub_l; eauto.

  assert(TOSpecMod.maps_to (TOSpecMod.remove Tm t0) t Mc).
  eapply TOSpecMod.removeX_presv_Y; auto.
  apply tidspec.beq_false_neq in eq1; auto.
  eapply IHpartO in H3.
  clear - H3 H0.
  assert(Maps.sub M' M).
  eapply join_sub_r; eauto.
  eapply sub_trans; eauto.
Qed.


Lemma abst_join_join_merge_ex:
  forall x1 x2 x3 x4,
    OSAbstMod.join x1 x2 x3 ->
    exists y, OSAbstMod.join x1 y (OSAbstMod.merge x3 x4).
Proof.
  intros.
  exists (OSAbstMod.minus (OSAbstMod.merge x2 x4) x1).
  unfolds; intro.
  pose proof H a.
  rewrite OSAbstMod.minus_sem.
  do 2 rewrite OSAbstMod.merge_sem.
  destruct(OSAbstMod.get x1 a);
    destruct(OSAbstMod.get x2 a);
    destruct(OSAbstMod.get x3 a);
    destruct(OSAbstMod.get x4 a);
    tryfalse; auto.
Qed.

Lemma lemma_trans_temp1:
  forall o o' O O' x t' sc t,
    GoodSched sc ->
    (forall ab : absop, (o, O, ab) |= SWPRE sc x t) ->
    (forall ab : absop, (o', merge O O', ab) |= AHprio sc t' ** Atrue) ->
    (forall ab : absop, (o, O, ab) |=  AHprio sc t' ** Atrue).
Proof.
  introv Hh.
  intros.
  lets Hx:H ab.
  lets Hxx: H0 ab.
  clear H H0.
  destruct o as [[[[]]]].
  simpl in *;mytac.
  exists empmem m m.
  do 3 eexists;splits;eauto.
  mytac.
  clear H39 H30 H6 H1 H22 H40 H31 H17.
  split;auto.
  unfolds in Hh.
  destructs Hh.
  assert (sc
            (merge O O') t').
  eapply H;eauto.

  lets Hx:abst_join_join_merge_ex O' H9.
  destruct Hx.
  eapply H1;eauto.
Qed.

Lemma lemma_trans_temp:
  forall o o' O O' x t' sc t,
    GoodSched sc ->
    (forall ab : absop, (o, O, ab) |= SWPRE sc x t) ->
    Maps.sub O O' ->
    (forall ab : absop, (o', O', ab) |= AHprio sc t' ** Atrue) ->
    (forall ab : absop, (o, O, ab) |=  AHprio sc t' ** Atrue).
Proof.
  intros.
  unfolds in H1; simpljoin.
  eapply osabst_join_eq_merge in H1; substs.
  eapply lemma_trans_temp1; eauto.
Qed.


Lemma parto_task_get_set:
  forall O T To C C' t,
    partO O T To ->
    get T t = Some C ->
    partO O (set T t C') To.
Proof.
  intros.
  inversion H.
  eapply parto_O; auto.
  eapply parto_S; eauto.
Qed.

Lemma new_part_o:
  forall O Ol To t Oc Tl,
    disjoint O (minus Ol Oc) ->
    TOSpecMod.maps_to To t Oc ->
    partO Ol Tl To ->
    partO (merge O (minus Ol Oc)) Tl (TOSpecMod.put To t O).
Proof.
  intros.
  inductions H1.
  tryfalse.

  destruct (tidspec.beq t0 t) eqn : eq1.
  apply tidspec.beq_true_eq in eq1; substs.
  unfolds in H0.
  rewrite H0 in H1; inverts H1.
  assert ((TOSpecMod.remove Tm t) = (TOSpecMod.remove (TOSpecMod.put Tm t O) t)).
  erewrite TOSpecMod.remove_cancel_put; auto.
  rewrite H1 in H3.
  assert (minus M m = M').
  eapply osabst_join_minus_eq; auto.
  rewrite H4.
  unfold minus in *; simpl in *.
  rewrite H4 in H.
  assert (join O M' (merge O M')).
  eapply join_merge_disj; auto.
  eapply parto_S; eauto.
  apply TOSpecMod.put_get_eq.

  assert (disjoint O (minus M' Oc)).
  eapply osabst_join_disjoint_minus_disjoint_minus; eauto.

  assert (TOSpecMod.maps_to (TOSpecMod.remove Tm t0) t Oc).
  apply TOSpecMod.removeX_presv_Y; auto.
  apply tidspec.beq_false_neq in eq1; auto.
  lets Hx: IHpartO H4 H5.
  assert (TOSpecMod.put (TOSpecMod.remove Tm t0) t O = TOSpecMod.remove (TOSpecMod.put Tm t O) t0).
  rewrite TOSpecMod.remove_ext_ext_remove; auto.
  apply tidspec.beq_false_neq in eq1; auto.
  rewrite H6 in Hx.
  clear H6.
  assert (join m (merge O (minus M' Oc)) (merge O (minus M Oc))).
  assert (disjoint m M').
  clear - H2.
  eapply my_join_disj; eauto.
  apply disjoint_sym in H6.
  lets Hx1: part_disjo H5 H3 H6.

  assert (join m (minus M' Oc) (minus M Oc)).
  eapply osabst_join_disjoint_minus_join; auto.
  apply disjoint_sym; auto.
  assert (disjoint O m).

  clear - H Hx1 H2.
  apply disjoint_sym in Hx1.
  eapply osabst_disjoint_minus_join_disjoint_disjoint; eauto.
  eapply osabst_join_disjoint_merge1; auto.

  eapply parto_S; eauto.
  rewrite TOSpecMod.put_noninterfere; auto.
  apply tidspec.beq_false_neq in eq1; auto.
Qed.

Lemma sat_split :
  forall P Q G E M isr auxs O absop,
    (G, E, M, isr, auxs, O, absop)|= P ** Q ->
    exists m1 m2 o1 o2,
      join m1 m2 M /\ join o1 o2 O /\
      (G, E, m1, isr, auxs, o1, absop)|= P /\
      (G, E, m2, isr, auxs, o2, absop)|= Q.
Proof.
  intros.
  simpl in H; mytac.
  do 4 eexists; splits; eauto.
Qed.

Lemma ptomvallist_mem_eq :
  forall vl l m1 m2,
    ptomvallist l true vl m1 ->
    ptomvallist l true vl m2 ->
    m1 = m2.
Proof.
  inductions vl; intros.
  simpl in H, H0; substs; auto.

  unfold ptomvallist in *; fold ptomvallist in *.
  destruct l; mytac.
  unfold ptomval in *; substs.
  lets Hx: IHvl H4 H2; substs.
  eapply join_unique; eauto.
Qed.

Lemma curlinv_switch_self:
  forall Olc Occ O' x4 Mc' Mc ge e0 i l0 lasrt t Mcn b tp Oc sd x,
    join Olc Occ O' ->
    join x4 Mc' Mc ->
    satp (ge, e0, Mc', i, l0) Occ (SWPRE sd x t) ->
    satp (ge, e0, Mc, i, l0) Oc (CurLINV lasrt t)->
    satp (ge, e0, x4, i, l0) Olc
         (EX lg' : list logicvar, LINV lasrt t lg' ** Atrue) ->
    get ge OSTCBCur = Some (b, Tptr tp) ->
    store (Tptr tp) Mc (b, 0%Z) (Vptr t) = Some Mcn ->
    satp (ge, e0, Mcn, i, l0) O' (CurLINV lasrt t).
Proof.
  intros.
  assert (satp (ge, e0, Mc, i, l0) O' (CurLINV lasrt t)).
  clear H2.
  unfold satp; intros.
  pose proof H1 aop; clear H1.
  pose proof H3 aop; clear H3.
  destruct H1.
  unfold CurLINV; exists x0.
  unfold SWPRE in H2; sep normal in H2.
  do 3 destruct H2.
  sep remember (1::nil)%list in H2.
  apply sat_split in H2.
  do 5 destruct H2.
  destruct H6.
  destruct H7.
  apply sep_combine_lemmas.GV_separate_rw in H7.
  apply sat_split in H7; mytac.
  simpl in H10; mytac.
  unfold get in H4, H14; simpl in H4, H14; rewrite H4 in H14; inverts H14.
  apply sat_split'.
  exists x9 (merge x4 (merge x10 x6)).
  exists empabst O'.
  splits; eauto.
  clear - H0 H2 H7.
  apply join_comm in H0.
  eapply mem_join_merge3; eauto.
  apply join_emp; auto.
  simpl.
  do 8 eexists; splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  eexists.
  splits; eauto.
  unfolds; auto.
  unfolds; auto.
  clear - H1 H H0 H2 H7.
  apply sat_split in H1; mytac.
  apply sat_split'.
  exists x (merge x1 (merge x10 x6)).
  exists x2 (merge x3 Occ).
  splits; eauto.
  apply join_comm.
  eapply mem_join_disjoint_merge; auto.
  apply join_comm; auto.
  eapply perm_map_lemmas_part4.mem_join_join_disjoint_merge; eauto.
  eapply perm_map_lemmas_part4.join_merge23_join; eauto. 
  
  assert(Mc = Mcn).
  clear - H0 H1 H4 H5.
  pose proof H1 absopx; clear H1.
  unfold SWPRE in H; sep normal in H.
  do 3 destruct H.
  apply sat_split in H; mytac.
  simpl in H2; mytac.
  unfold get in H4, H9; simpl in H4, H9.
  rewrite H4 in H9; inverts H9.
  apply join_comm in H0.
  assert (join x3 (merge x5 x4) Mc).
  eapply mem_join_join_merge23_join; eauto.
  lets Hx: store_mapstoval_frame1 H10 H1 H5; mytac.
  assert (x3 = x6).
  clear - H10 H2.
  unfold mapstoval in *; mytac.
  eapply ptomvallist_mem_eq; eauto.
  substs.
  eapply join_unique; eauto.
  substs; auto.
Qed.

Lemma sw_has_code :
  forall (x : var) (tst : taskst) (O : osabst) 
         (T : tasks) (t' t: addrval) (l : block) (tp : type) 
         (sd : ossched),
    GoodSched sd ->
    (forall ab : absop, (tst, O, ab) |= SWPRE sd x t) ->
    EnvMod.get (get_genv (get_smem tst)) x = Some (l, tp) ->
    load tp (get_mem (get_smem tst)) (l, 0%Z) = Some (Vptr t') ->
    eqdomTO T O -> exists C, TasksMod.get T t' = Some C.
Proof.
  introv Hgood.
  intros.
  lets Hres : H absopx.
  destruct Hres; mytac.
  destruct tst as [[[[]]]].
  destruct H3; trysimplall;mytac.
  destruct H8; trysimplsall; mytac.
  destruct H11; trysimplsall; mytac.
  destruct H14; trysimplsall; mytac.
  clear H.
  simpl in *; mytac.
  unfolds in H2.
  mytac.
  assert (OSAbstMod.sub x4 O) as Hart. 
  eapply OSAbstMod.join_sub_l; eauto.
  destruct Hgood as (Hgood1 & Hgood2 & Hgood3).
  lets Hsd : Hgood1 H6 H7.
  lets Has :  Hgood2  Hsd.
  mytac.
  unfold get in H27; simpl in H27.
  rewrite H0 in H27.
  inverts H27.
  assert (x0=t').
  eapply mapsto_load_eq;eauto.
  subst x0.
  rewrite H in H3.
  inverts H3.
  apply H2.
  eauto.
Qed.

Lemma osabst_merge_set_eq :
  forall (O:osabst) O' x y,
    merge (set O x y) O' = set (merge O O') x y. 
Proof.
  intros.
  eapply extensionality.
  intro.
  rewrite merge_sem.
  destruct (absdataidspec.beq x a) eqn : eq1.
  apply absdataidspec.beq_true_eq in eq1.
  substs.
  rewrite set_a_get_a.
  rewrite set_a_get_a.
  destruct (get O' a); auto.
  apply absdataidspec.beq_false_neq in eq1.
  rewrite set_a_get_a'; auto.
  rewrite set_a_get_a'; auto.
  rewrite merge_sem.
  auto.
  ica.
  ica.  
Qed.

Lemma swinvt_isr_emp:
  forall ge le m isr aux O ab I t,
    ((ge,le,m,isr,aux),O,ab) |= SWINVt I t -> isr = empisr.
Proof.
  unfold SWINVt.
  intros.
  simpl in H.
  mytac.

  eapply Coqlib.extensionality.
  intro.
  pose proof H33 x1.
  unfold empisr; auto.
Qed.

Lemma good_inv_prop':
  forall p : asrt,
    inv_prop p ->
    GoodInvAsrt p ->
    forall (ge le : env) (M : mem) aux aux' (op : absop) abst,
      (ge, le, M, empisr, aux, abst, op) |= p ->
      forall (le' : env) (op' : absop) ,
        (ge, le', M, empisr, aux', abst, op') |= p.
Proof.
  intros.
  destruct aux as [[]].
  destruct aux' as [[]].
  remember ((ge, le', M, empisr, (i1, i2, c0), abst, op')) as X.
  assert ((ge, le', M, empisr, (i1, i0, c0), abst, op') |= p).
  eapply good_inv_prop;eauto.
  unfold  inv_prop in H.
  destruct H.
  unfold assertion.inv_isr_prop in H3.
  mytac. 
  assert ((set_is_s (ge, le', M, empisr, (i1, i0, c0), abst, op') i2)|=p).
  apply H6;auto.
  simpl set_is_s in H7.
  auto.
Qed.

Lemma inv_isr_irrev_prop' :
  forall n low I ge le M  aux aux' abst op, 
    (ge, le, M ,empisr, aux, abst, op) |= starinv_isr I low n -> 
    forall le' op',
      (ge, le', M ,empisr, aux', abst, op') |= starinv_isr I low n.   
Proof.
  inductions n.
  simpl starinv_isr.
  introv Hsat.
  introv.
  simpl.
  simpl in Hsat.
  destruct Hsat.
  exists x.
  destruct H.
  left; auto.
  right.
  repeat destruct H.
  destruct H0 as (Hm & Hx & Hdj & Hf & Hsa).
  do 6 eexists; splits; eauto.
  eapply good_inv_prop'.
  apply prec.
  eapply (invp  (I low)).
  eauto.
  introv Hsat.
  introv.
  simpl starinv_isr.
  simpl starinv_isr in Hsat.
  unfold sat in Hsat.
  fold sat in Hsat.
  simpl substmo in Hsat.
  unfold sat.
  fold sat.
  simpl substmo.
  simpl getabst in *.
  simpl gettaskst in *.
  simpl empst in *.
  simpl assertion.getmem in *.
  destruct Hsat as (M1 & M2 & M0 & o1 & o2 & o & Hsat).
  destruct Hsat as (HM & Hmm & Ho & Habsj & Hsat).
  simpl getmem in *.
  exists M1 M2 M0 o1 o2 o; splits; auto.
  destruct Hsat as (Hsat & Hss).
  destruct Hsat.
  exists x.
  destruct H.
  left; auto.
  right.
  repeat destruct H.
  destruct H0 as (Hm & Hx & Hdj & Hf & Hsa).
  do 6 eexists; splits; eauto.
  eapply good_inv_prop'.
  apply prec.
  eapply (invp  (I low)).
  eauto.
  destruct Hsat.
  eapply IHn; eauto.
Qed.

Lemma invlth_isr_add:
  forall i j ge le le' le'' M1 M2  aux aux' O1 O2 ab ab' ab'' I, 
    disjoint M1 M2 ->
    disjoint O1 O2 ->
    i < j -> j <= S INUM ->
    (ge, le, M1, empisr, aux, O1, ab) |= invlth_isr I 0 i -> 
    (ge, le', M2, empisr, aux, O2, ab') |= invlth_isr I ((i+1)%nat) j -> 
    (ge, le'', merge M1 M2, empisr, aux', merge O1 O2, ab'') |= invlth_isr I 0 j.
Proof.
  intros.
  unfold invlth_isr in *.
  remember (j-(i+1)) as r.
  assert (j-0=S(i+r)).
  omega.
  rewrite H5.
  assert((ge, le'', merge M1 M2, empisr, aux', merge O1 O2, ab'')
           |= starinv_isr I 0 (i - 0) ** starinv_isr I (i + 1) r).
  unfold sat;fold sat;trysimplsall.
  simpl assertion.getmem.
  exists M1 M2 (merge M1 M2 ) O1 O2 (merge O1 O2);mytac. 
  eapply join_merge_disj;eauto.
  eapply join_merge_disj;eauto.
  eapply inv_isr_irrev_prop' ;eauto.
  eapply inv_isr_irrev_prop' ;eauto.
  eapply starinv_isr_elim1;eauto.
  assert (i-0=i).
  omega.
  rewrite H7 in H6.
  assert (i+1= S i).
  omega.
  rewrite H8 in H6.
  auto.
Qed.

Lemma invlth_isr_add':
  forall ge le le' le'' M1 M2 aux aux' O1 O2 i j ab ab' ab'' I, 
    disjoint M1 M2 ->
    disjoint O1 O2 ->
    i< j -> j <= S INUM ->
    (ge,le,M1,empisr,aux,O1,ab) |= invlth_isr I 0 i -> 
    (ge,le', M2,empisr,aux,O2,ab') |= invlth_isr I ((i+1)%nat) j -> 
    (ge,le'', merge M2 M1,empisr,aux',merge O2 O1,ab'') |= invlth_isr I 0 j.
Proof.
  intros.
  unfold invlth_isr in *.
  remember (j-(i+1)) as r.
  assert (j-0=S(i+r)).
  omega.
  rewrite H5.
  assert((ge, le'', merge M1 M2, empisr, aux', merge O1 O2, ab'')
           |= starinv_isr I 0 (i - 0) ** starinv_isr I (i + 1) r).
  unfold sat;fold sat;trysimplsall.
  simpl assertion.getmem.
  exists M1 M2 (merge M1 M2 ) O1 O2 (merge O1 O2);mytac.
  eapply join_merge_disj;eauto.
  eapply join_merge_disj;eauto.
  eapply inv_isr_irrev_prop' ;eauto.
  eapply inv_isr_irrev_prop' ;eauto.
  eapply starinv_isr_elim1;eauto.
  assert (i-0=i).
  omega.
  rewrite H7 in H6.
  assert (i+1= S i).
  omega.
  rewrite H8 in H6.
  assert (merge M1 M2 = merge M2 M1).
  eapply disjoint_merge_sym; auto.
  assert (merge O1 O2 = merge O2 O1).
  eapply disjoint_merge_sym; auto.
  rewrite H9 in H6.
  rewrite H10 in H6.
  auto.
Qed.

Lemma starinv_isr_ncare_aux_ab:
  forall j i I ge le le' m aux O ab ab' aux', 
    (ge, le, m , empisr, aux, O, ab)
      |= starinv_isr I i j ->   (ge, le', m , empisr, aux', O, ab')
                                  |= starinv_isr I i j .
Proof.
  induction j.
  intros.
  destruct aux as [[]].
  destruct aux' as [[]].
  unfold starinv_isr in *.
  simpl in *.
  mytac.
  destruct H;mytac.
  unfold empisr in H.
  tryfalse.
  exists empisr.
  right.
  exists empmem m m empabst O O;mytac.
  auto.
  eapply good_inv_prop';eauto.
  apply prec. 
  apply invp.
  intros.
  unfold starinv_isr.
  unfold starinv_isr in H.
  fold starinv_isr in *.
  simpl in H.
  mytac.
  simpl;mytac.
  destruct H3.
  mytac.
  exists empmem m m empabst O O;mytac.
  unfold empisr in H.
  false.
  eapply IHj;eauto.
  mytac.
  exists x x0 m x2 x3 O;mytac;auto.
  exists empisr;right;mytac.
  exists empmem x x empabst x2 x2;mytac;auto.
  destruct aux as [[]].
  destruct aux' as [[]].
  eapply good_inv_prop';eauto.
  apply prec.
  apply invp.
  eapply IHj;eauto.
Qed.

Lemma invariant_prop_map3:
  forall (A B T : Type) (MC : PermMap A B T) x3 x4 Mc Ms,
    disjoint Mc Ms ->
    join x3 x4 Mc ->
    disjoint x4 (merge Ms x3).
Proof.
  hy.
Qed.

Lemma invariant_prop_map5:
  forall (A B T : Type) (MC : PermMap A B T) Ms Mc x x0,
    usePerm = true ->
    disjoint Mc Ms ->
    join x x0 Ms ->
    disjoint x (merge x0 Mc).
Proof.
  hy.
Qed.

Lemma invariant_prop_map4:
  forall (A B T : Type) (MC : PermMap A B T) Mc Ms x3 x4,
    disjoint Mc Ms ->
    join x3 x4 Mc ->
    disjoint x4 (merge x3 Ms).
Proof.
  hy.
Qed.

Lemma swi_rdy_inv' :
  forall o Ol Os Ms Mc I t t' S o', 
    good_is_S S ->
    (disjoint Ol Os) ->
    (disjoint Mc Ms)->
    (forall ab : absop, (substaskst o Ms, Os, ab) |= INV I)->
    (forall ab : absop, (substaskst o Mc, Ol, ab) |= SWINVt I t')->
    projS S t= Some o ->
    projS S t'=Some o' ->
    (
      exists Mc' Ms' Ol' Os',
        disjoint Mc' Ms' /\
        merge Mc' Ms' = merge Mc Ms/\
        disjoint Ol' Os'/\
        merge Ol' Os'= merge Ol Os/\
        (
          ((forall ab : absop, (substaskst o' Ms', Os', ab) |= INV I)/\
           (forall ab : absop, (substaskst o' Mc', Ol', ab) |= RDYINV I t'))
        )
    ).
Proof.
  intros.
  destruct o as [[[[]]]].
  destruct o' as [[[[]]]].
  simpl substaskst in *.
  destruct l as [[]].
  destruct l0 as [[]].
  assert (i = empisr).
  eapply swinvt_isr_emp; eauto.
  subst i.
  destruct S as [[[]]].
  assert (i = empisr).
  clear -H4.
  unfold projS in H4.
  destruct (projD (p, m1) t);destruct (get l t ); tryfalse; auto.
  inverts H4.
  auto.
  subst i.
  assert (i0 = empisr).
  clear -H5.
  unfold projS in H5.
  destruct (projD (p, m1) t'); tryfalse.
  unfold get in H5; simpl in H5.
  destruct (TaskLStMod.get l t' ); tryfalse; auto.
  inverts H5.
  auto.
  subst i0.

  assert (projS (p, m1, empisr, l) t = Some (e, e0, m, empisr, (i1, i2, c))) as Hprojt;auto.
  assert (projS (p, m1, empisr, l) t' = Some (e1, e2, m0, empisr, (i3, i4, c0))) as Hprojt';auto.
  destruct p.
  simpl in H4, H5.
  unfold get in H4, H5; simpl in H4, H5.
  destruct (CltEnvMod.get c1 t');tryfalse.
  destruct (TaskLStMod.get l t');tryfalse.
  destruct (CltEnvMod.get c1 t);tryfalse.
  destruct (TaskLStMod.get l t);tryfalse.
  inverts H5.
  inverts H4.

  pose proof H2 absopx; clear H2.
  pose proof H3 absopx; clear H3.
  unfold INV in H4.
  apply sat_split in H4; mytac.
  destruct H6.
  unfold inv_ieon in H6; apply sat_split in H6; mytac.
  simpl in H8; mytac.
  unfold SWINVt in H2.
  apply sat_split in H2; mytac.
  unfold SWINV in H7.
  apply sat_split in H7; mytac.
  simpl in H11; mytac; tryfalse.

  unfold inv_ieoff in H6.
  apply sat_split in H6; mytac.
  destruct H9.
  apply sat_split in H9; mytac.
  simpl in H8; simpl in H11; mytac.

  unfold SWINVt in H2.
  apply sat_split in H2; mytac.
  unfold SWINV in H7.
  apply sat_split in H7.
  mytac.
  simpl in H10; mytac.
  destruct H11.
  simpl in H7; mytac.

  destruct i3.
  destruct H12.
  sep split in H7.

  exists x4 (merge Ms x3) empabst (merge Os Ol).
  splits; eauto.
  clear - H2 H1.
  eapply invariant_prop_map3; eauto.
  (* eapply disj_merge_intro_r. *)
  (* apply join_comm in H2. *)
  (* split; auto. *)
  (* eapply mem_join_disjoint_disjoint; eauto. *)
  (* eapply my_join_disj; eauto. *)

  clear - H1 H2.
  eapply disjoint_join_merge_merge; auto.
  eapply disj_emp_l.
  assert (merge Os Ol = merge Ol Os).
  eapply disjoint_merge_sym.
  apply disjoint_sym; auto.
  rewrite H10; clear H10.
  apply jl_merge_emp'.

  intro.
  unfold INV.
  apply sat_split'.
  exists x (merge x0 x3) x1 (merge x2 Ol).
  splits.
  eapply mem_join_disjoint_join_merge; auto.
  apply disjoint_sym.
  eapply mem_join_disjoint_disjoint; eauto.
  eapply osabst_join_disjoint_join_merge; auto.  
  apply disjoint_sym; auto.
  clear- H5.
  unfold getinv in *.
  destruct (I (S INUM)) as (INV & prec).
  eapply good_inv_prop'; eauto.

  left.
  unfold inv_ieon.
  apply sat_split'.
  do 4 eexists; splits.
  apply join_emp; auto.
  apply join_emp; auto.
  simpl; unfold emposabst; auto.
  simpl in H8; mytac.
  eapply invlth_isr_add'; eauto.
  clear - H1 H3 H2.
  apply join_comm in H3.
  eapply disjoint_join_join_disjoint; eauto.
  clear - H0 H4.
  apply disjoint_sym.
  apply disjoint_sym in H0.
  apply join_comm in H4.
  eapply osabst_join_disjoint_disjoint; eauto.
  unfold RDYINV.
  left.
  apply sat_split'.
  do 4 eexists.
  splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  split.
  simpl; unfold emposabst; auto.
  simpl.
  eexists.
  splits; auto.
  splits; eauto.
  unfolds; auto.
  unfolds; auto.
  clear - H8.
  destruct H8.
  exists x.
  simpl in H; mytac.
  simpl.
  do 7 eexists.
  splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  eexists; splits; eauto.
  unfolds; auto.
  unfolds; auto.

  simpl in H7; mytac.
  exists x4 (merge x3 Ms) x6 (merge x5 Os).
  splits.
  clear - H1 H2.
  
  eapply invariant_prop_map4; eauto.
  (* eapply disj_merge_intro_r. *)
  (* apply join_comm in H2. *)
  (* split. *)
  (* eapply my_join_disj; eauto. *)
  (* eapply mem_join_disjoint_disjoint; eauto. *)

  clear - H1 H2.
  apply join_comm in H2.
  eapply disjoint_join_merge_merge'; auto.
  
  clear - H0 H6.

  eapply disj_merge_intro_r.
  ica.
  apply join_comm in H6.
  split.
  eapply my_join_disj; eauto.
  eapply osabst_join_disjoint_disjoint; eauto.
  clear - H0 H6.
  apply join_comm in H6.
  eapply disjoint_join_merge_merge'; auto.
  
  clear - H7 H14 H5 H2 H6 H0 H1.
  unfold INV.
  intro.
  eapply sat_split'.
  exists Ms x3 Os x5.
  splits.
  apply join_comm.
  eapply join_merge_disj.
  eapply mem_join_disjoint_disjoint; eauto.
  apply join_comm.
  eapply join_merge_disj.
  eapply osabst_join_disjoint_disjoint; eauto.
  destruct (I (S INUM)) as (INV & goodi).
  unfold getinv in *.
  eapply good_inv_prop'; eauto.

  left.
  unfold inv_ieon.
  apply sat_split'.
  do 4 eexists.
  splits.
  apply join_emp; auto.
  apply join_emp; auto.
  simpl; unfold emposabst; auto.
  rewrite H7 in H14.
  assert (exists h, h < INUM).
  exists 1.
  unfold INUM; omega.
  destruct H.
  assert (INUM <= S INUM).
  unfold INUM; omega. 
  lets Hx: invlth_divide H H3 H14; mytac.
  assert (x3 = merge x0 x1).
  eapply join_merge; auto.
  assert (x5 = merge x2 x7).
  eapply join_merge; auto.
  rewrite H11, H12.
  eapply invlth_isr_add; eauto.
  eapply my_join_disj; eauto.
  eapply my_join_disj; eauto.
 
  unfold RDYINV.
  left.
  apply sat_split'.
  do 4 eexists; splits.
  apply join_emp; auto.
  apply join_emp; auto.
  simpl; unfold emposabst; splits; auto.
  eexists.
  splits; eauto.
  clear - H8.
  sep auto.

  (**)
  destruct i4.
  exists (merge x0 Mc) x (merge x2 Ol) x1.
  splits; auto.
  apply disjoint_sym.
  clear - H3 H1.    
  eapply invariant_prop_map5; ica.
  (* eapply disj_merge_intro_r. *)
  (* split. *)
  (* eapply my_join_disj; eauto. *)
  (* apply disjoint_sym in H1. *)
  (* eapply mem_join_disjoint_disjoint; eauto. *)
  clear - H3 H1.
  eapply disjoint_join_merge_merge''; auto.
  
  clear - H4 H0.
  apply disjoint_sym.
  eapply disj_merge_intro_r.
  ica.
  split.
  eapply my_join_disj; eauto.
  apply disjoint_sym in H0.
  eapply osabst_join_disjoint_disjoint; eauto.
  clear - H4 H0.
  eapply disjoint_join_merge_merge''; auto.

  intro.
  unfold INV.
  apply sat_split'.
  exists x empmem x1 empabst.
  splits.
  apply join_comm; apply join_emp; auto.
  apply join_comm; apply join_emp; auto.
  clear - H5.
  unfold getinv in *.
  destruct (I (S INUM)) as (inv & goodi).
  eapply good_inv_prop'; eauto.

  right.
  unfold inv_ieoff.
  apply sat_split'.
  do 4 eexists; splits; eauto.
  apply join_emp; eauto.
  apply join_emp; eauto.
  simpl; unfold emposabst; auto.
  exists INUM.
  apply sat_split'.
  do 4 eexists.
  splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  simpl; unfold emposabst; auto.
  right.
  simpl; unfold emposabst; auto.

  unfold RDYINV.
  right.
  unfold SWINVt.
  apply sat_split'.
  exists (merge x3 x0) x4 (merge x5 x2) x6.
  splits.
  apply join_comm.
  apply join_comm in H2.
  assert (merge x0 Mc = merge Mc x0).
  eapply disjoint_merge_sym; auto.
  apply join_comm in H3.
  apply disjoint_sym in H1.
  eapply mem_join_disjoint_disjoint; eauto.
  rewrite H7.
  eapply mem_join_disjoint_join_merge; auto.
  apply disjoint_sym.
  apply disjoint_sym in H1.
  apply join_comm in H3.
  eapply mem_join_disjoint_disjoint; eauto.

  apply join_comm.
  clear - H0 H6 H4.
  apply join_comm in H4.
  assert (merge x2 Ol = merge Ol x2).
  eapply disjoint_merge_sym; auto.
  eapply osabst_join_disjoint_disjoint; eauto.
  apply disjoint_sym; auto.
  rewrite H.
  eapply osabst_join_disjoint_join_merge; auto.
  apply join_comm; auto.
  apply disjoint_sym.
  apply disjoint_sym in H0.
  eapply osabst_join_disjoint_disjoint; eauto.

  unfold SWINV.
  apply sat_split'.
  do 4 eexists; splits.
  apply join_emp; auto.
  apply join_emp; auto.
  simpl.
  do 6 eexists; splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  eexists.
  unfold emposabst.
  splits; eauto.
  unfolds; auto.
  exists INUM.
  apply sat_split'.
  do 4 eexists.
  splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  simpl; unfold emposabst; auto.

  assert (disjoint x3 x0).
  clear - H1 H3 H2.
  apply join_comm in H3.
  eapply disjoint_join_join_disjoint; eauto.
  assert (disjoint x5 x2).
  clear - H0 H4 H6.
  apply join_comm in H4.
  eapply disjoint_join_join_disjoint; eauto.
  clear - H7 H9 H12 H14.
  destruct H12.
  sep split in H.
  eapply invlth_isr_add; eauto.

  simpl in H; mytac.
  rewrite H in H14.
  lets Hx: invlth_divide 1 H14.
  unfold INUM; omega.
  unfold INUM; omega.
  mytac.
  lets Hx: invlth_isr_add H2 H3.
  eapply my_join_disj; eauto.
  eapply my_join_disj; eauto.
  unfold INUM; omega.
  unfold INUM; omega.
  assert (x3 = merge x x0).
  eapply join_merge; auto.
  assert (x5 = merge x1 x2).
  eapply join_merge; auto.
  substs.
  rewrite jl_merge_emp.
  rewrite jl_merge_emp.
  eauto.

  clear - H8.
  destruct H8.
  exists x.
  simpl in H; mytac.
  simpl.
  do 7 eexists.
  splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  eexists.
  unfold emposabst.
  splits; eauto.
  unfolds; auto.

(*case 2 for the destruction of is:  h::is'*)
  unfolds in H.
  apply H in Hprojt'.
  unfolds in Hprojt'.
  mytac.
  assert (
      (e, e0, merge x3 x0, empisr, (false, i2, c), merge x5 x2, absopx)
        |= invlth_isr I 0 INUM
    ).
  clear - H12 H14 H3 H4 H0 H1 H2 H6.
  destruct H12.
  sep split in H.
  eapply invlth_isr_add; eauto.
  apply join_comm in H3.
  eapply disjoint_join_join_disjoint; eauto.
  apply join_comm in H4.
  eapply disjoint_join_join_disjoint; eauto.

  simpl in H; mytac.
  rewrite H in H14.
  unfold invlth_isr in *.
  rewrite jl_merge_emp.
  rewrite jl_merge_emp.
  eapply starinv_isr_ncare_aux_ab; eauto.

  lets Hx: invlth_divide H7 H10.
  omega.
  mytac.
  exists (merge x4 x7) (merge x x8) (merge x6 x9) (merge x1 x10).
  splits.
  apply join_comm in H3.
  eapply disjoint_join_join_merge_join_disjoint_merge_merge; eauto.
  apply join_comm in H3.
  eapply disjoint_join_join_merge4; eauto.
  apply join_comm in H4.
  eapply disjoint_join_join_merge_join_disjoint_merge_merge; eauto.
  apply join_comm in H4.
  eapply disjoint_join_join_merge4; eauto.

  intro.
  unfold INV.
  apply sat_split'.
  exists x x8 x1 x10.
  splits.
  apply join_merge_disj.
  clear - H11 H3 H2 H1.
  apply join_comm in H3.
  apply disjoint_sym.
  eapply disjoint_join_merge_disjoint; eauto.

  clear - H13 H0 H4 H6.
  apply join_merge_disj.
  apply join_comm in H4.
  apply disjoint_sym.
  eapply disjoint_join_merge_disjoint; eauto.

  clear - H5.
  unfold getinv in *.
  destruct (I (S INUM)) as (INV & goodi).
  eapply good_inv_prop'; eauto.

  right.
  unfold inv_ieoff.
  apply sat_split'.
  do 4 eexists.
  splits; auto.
  eapply join_emp; auto.
  eapply join_emp; auto.
  simpl; unfold emposabst; auto.
  exists h.
  apply sat_split'.
  do 4 eexists.
  splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  simpl; unfold emposabst; auto.
  left.
  sep split; auto.
  clear - H16.
  unfold invlth_isr in *.
  eapply starinv_isr_ncare_aux_ab; eauto.

  intro.
  unfold RDYINV.
  right.
  unfold SWINVt.
  apply sat_split'.
  exists x7 x4 x9 x6.
  splits.
  apply join_comm; apply join_merge_disj; auto.
  clear - H1 H3 H2 H11.
  apply disjoint_sym.
  apply join_comm in H3.
  eapply disjoint_join_merge_disjoint'; eauto.
  apply join_comm.
  apply join_merge_disj.
  clear - H13 H4 H6 H0.
  apply join_comm in H4.
  apply disjoint_sym.
  eapply disjoint_join_merge_disjoint'; eauto.

  unfold SWINV.
  apply sat_split'.
  do 4 eexists; splits.
  apply join_emp; auto.
  apply join_emp; auto.
  simpl.
  do 6 eexists; splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  eexists.
  unfold emposabst.
  splits; eauto.
  unfolds; auto.
  exists h.
  apply sat_split'.
  do 4 eexists.
  splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  simpl; unfold emposabst; auto.
  clear - H15.
  unfold invlth_isr in *.
  eapply starinv_isr_ncare_aux_ab; eauto.

  clear - H8.
  destruct H8.
  exists x.
  simpl in H; mytac.
  simpl.
  do 7 eexists; splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  eexists; unfold emposabst; splits; eauto.
  unfolds; auto.
  Grab Existential Variables.
  apply absopx.
Qed.

Lemma osabst_disj_indom_set_disj:
  forall (O:osabst) O' x y,
    indom O x -> disjoint O O' ->
    disjoint (set O x y) O'.
Proof.
  intros.
  unfolds in H; destruct H.
  eapply disj_set_disj_1; eauto.
Qed.

Lemma swi_rdy_inv'''1 :
  forall (o : taskst) Ol Os  Ms Mc 
         (I : Inv) (t t' : tid) (S : osstate)
         (o' : env * EnvSpec.B * mem * isr * LocalStSpec.B) 
         (b : block) (tp : type) (Mcc : mem) (sc : ossched) li x,
    (forall ab : absop, (substaskst o Mc, Ol, ab) |= SWPRE_NDEAD sc x t) ->
    good_is_S S ->
    GoodI I sc li->
    disjoint Ol Os ->
    disjoint Mc Ms ->
    (forall ab : absop, (substaskst o Ms, Os, ab) |= INV I) ->
    (forall ab : absop, (substaskst o Mc, Ol, ab) |= SWINVt I t) ->
    (forall ab : absop, (substaskst o Mc, Ol, ab) |= AHprio sc t' ** Atrue) ->
    projS S t = Some o ->
    projS S t' = Some o' ->
    EnvMod.get (get_genv (get_smem o)) OSTCBCur = Some (b, Tptr tp) ->
    store (Tptr tp) Mc (b, 0%Z) (Vptr t') = Some Mcc ->
    exists Mc' Ms' Ol' Os',
      disjoint Mc' Ms' /\
      merge Mc' Ms' = merge Mcc Ms /\
      disjoint Ol' Os' /\
      merge Ol' Os'  = set (merge Ol Os) curtid (oscurt t') /\
      (forall ab : absop, (substaskst o' Ms', Os', ab) |= INV I) /\
      (forall ab : absop, (substaskst o' Mc', Ol', ab) |= RDYINV I t').
Proof.
  introv Hswprendead.
  intros.
  assert (forall ab : absop, (substaskst o Mcc,set Ol curtid (oscurt t'), ab) |= SWINVt I t').
  unfold GoodI in *.
  destructs H0.
  intros.
  assert (substaskst o Mcc= substaskst (substaskst o Mc) Mcc).
  destruct o as [[[[]]]];simpl;auto.
  rewrite H13.
  lets Hx:H4 ab.
  lets Hy:H5 ab.
  eapply H11 in Hx;eauto.
  3:destruct o as [[[[]]]];simpl;eauto.
  mytac.
  destruct H15;mytac;eauto.   
  unfold SWPRE_NDEAD in Hswprendead.
  destruct Hswprendead with (ab:=ab).
  clear - H15 H14 H18.
  simpl in H18;mytac.
  assert (get (sig abtcblsid (abstcblist x)) abtcblsid = Some (abstcblist x)).
  apply map_get_sig.
  eapply join_get_l in H2;eauto.
  rewrite H14 in H2;inverts H2.
  destruct H15;auto.
  destruct o as [[[[]]]];simpl.
  simpl in H8.
  eauto.
  rewrite <- osabst_merge_set_eq.
  eapply swi_rdy_inv';eauto.
  eapply osabst_disj_indom_set_disj;auto.
  assert (forall ab : absop, (substaskst o Mc, Ol, ab) |= SWINVt I t ** Aemp).
  intros.
  lets Hx:H4 ab.
  sep auto.
  eapply GoodI_SWINV_indom_curt with (sc:=sc) in H11;eauto.
  eapply disj_store_disj;eauto.
Qed.

(*
Lemma swi_rdy_inv''' :
  forall (o : taskst) Ol Os  Ms Mc 
         (I : Inv) (t t' : tid) (S : osstate)
         (o' : env * EnvSpec.B * mem * isr * LocalStSpec.B) 
         (b : block) (tp : type) (Mcc : mem) (sc : ossched) OO li lg,
    good_is_S S ->
    GoodI I sc li->
    join Ol Os OO->
    disjoint Mc Ms ->
    (forall ab : absop, (substaskst o Ms, Os, ab) |= INV I) ->
    (forall ab : absop, (substaskst o Mc, Ol, ab) |= SWINVt I t ** li t lg) ->
    (forall ab : absop, (substaskst o Mc, Ol, ab) |= AHprio sc t' ** Atrue) ->
    projS S t = Some o ->
    projS S t' = Some o' ->
    EnvMod.get (get_genv (get_smem o)) OSTCBCur = Some (b, Tptr tp) ->
    store (Tptr tp) Mc (b, 0%Z) (Vptr t') = Some Mcc ->
    exists Mc' Ms' Ol' Os' OO',
      disjoint Mc' Ms' /\
      merge Mc' Ms' = merge Mcc Ms /\
      join Ol' Os' OO' /\
      OO' = set OO curtid (oscurt t') /\
      (forall ab : absop, (substaskst o' Ms', Os', ab) |= INV I) /\
      (forall ab : absop, (substaskst o' Mc', Ol', ab) |= RDYINV I t' ** li t' init_lg).
Proof.
  intros.
  assert (disjoint Ol Os).
  eapply my_join_disj; eauto.
  lets Hx: swi_rdy_inv'''1 H H0 H10 H2 H3.
  lets Hx1: Hx H4 H5 H6 H7 H8; clear Hx.
  lets Hx2: Hx1 H9; clear Hx1.
  assert (OO = merge Ol Os).
  eapply join_merge; auto.
  substs.
  clear - Hx2; mytac.
  do 5 eexists.
  splits; eauto.
  eapply join_merge_disj; auto.
Qed.
*)

Lemma partm_task_get_set:
  forall O T To t C C',
    partM O T To -> get T t = Some C -> partM O (set T t C') To.
Proof.
  intros.
  inverts H.
  eapply partm_O; eauto.
  eapply partm_S; eauto.
Qed.


Lemma partm_merge_disj :
  forall M (T : tasks) (Tm : TMSpecMod.Map)
         (t : TMSpecMod.A) Mn Mc,
    disjoint M Mn ->
    TMSpecMod.maps_to Tm t Mc ->
    partM M T Tm ->
    partM (merge M Mn) T (TMSpecMod.put Tm t (merge Mc Mn)).
Proof.
  intros.
  gen H1.
  gen H.
  gen H0.
  rename Mn into M'.
  gen M'.
  intro M' after t.

  intros.
  gen M' t Mc.
  inductions H1; intros.
  unfolds in H1; tryfalse.

  destruct (tidspec.beq t0 t) eqn : eq1.
  apply tidspec.beq_true_eq in eq1; substs.
  unfolds in H3.
  rewrite H in H3; inverts H3.
  assert ((TMSpecMod.remove Tm t) = (TMSpecMod.remove ((TMSpecMod.put Tm t (merge Mc M'0))) t)).
  rewrite TMSpecMod.remove_cancel_put; auto.
  rewrite H3 in H1.
  assert(join (merge Mc M'0) M' (merge M M'0)).

  eapply mem_join_disjoint_merge; auto.
  eapply partm_S; eauto.
  rewrite TMSpecMod.put_get_eq; auto.

  assert (disjoint M' M'0).
  apply join_comm in H0.
  eapply mem_join_disjoint_disjoint; eauto.
  assert (TMSpecMod.maps_to (TMSpecMod.remove Tm t) t0 Mc).
  eapply TMSpecMod.removeX_presv_Y; auto.
  apply tidspec.beq_false_neq in eq1; auto.
  lets Hx1: IHpartM M'0 H4 H5.
  rewrite <- TMSpecMod.remove_ext_ext_remove in Hx1.
  assert(join (merge M' M'0) m (merge M M'0)).
  apply join_comm in H0.
  eapply mem_join_disjoint_merge; auto.
  assert ((TMSpecMod.put Tm t0 (merge Mc M'0)) t = Some m).
  rewrite TMSpecMod.put_noninterfere; auto.
  apply tidspec.beq_false_neq; auto.
  eapply partm_S; eauto.
  apply join_comm; auto.

  apply tidspec.beq_false_neq; auto.
Qed.


Lemma mem_join_sub_join_minus_minus'_auto :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 m4,
    usePerm = true ->
    join m1 m2 m3 ->
    Maps.sub m4 m2 ->
    join m1 (minus m2 m4) (minus m3 m4).
  hy.
Qed.

Lemma mem_join_sub_join_minus_minus' :
  forall (m1:mem) m2 m3 m4,
    join m1 m2 m3 ->
    Maps.sub m4 m2 ->
    join m1 (minus m2 m4) (minus m3 m4).
Proof.
  intros; eapply mem_join_sub_join_minus_minus'_auto; ica.
Qed.

Lemma partm_minus_sub :
  forall (M Mc Mm: mem) (T : tasks) (Tm : TMSpecMod.Map) 
         (t : TMSpecMod.A),
    Maps.sub Mm Mc ->
    TMSpecMod.maps_to Tm t Mc ->
    partM M T Tm ->
    partM (minus M Mm) T (TMSpecMod.put Tm t (minus Mc Mm)).
Proof.
  intros.
  inductions H1.
  tryfalse.

  destruct (tidspec.beq t0 t) eqn : eq1.
  apply tidspec.beq_true_eq in eq1; substs.
  unfolds in H0.
  rewrite H0 in H1; inverts H1.
  assert (TMSpecMod.remove Tm t = TMSpecMod.remove (TMSpecMod.put Tm t (minus m Mm)) t).
  rewrite TMSpecMod.remove_cancel_put; auto.
  rewrite H1 in H3; clear H1.

  assert (join (minus m Mm) M' (minus M Mm)).
  eapply mem_sub_join_minus_join; eauto.
  eapply partm_S; eauto.
  rewrite TMSpecMod.put_get_eq; auto.

  assert (TMSpecMod.maps_to (TMSpecMod.remove Tm t0) t Mc).
  eapply TMSpecMod.removeX_presv_Y; auto.
  apply tidspec.beq_false_neq in eq1; auto.
  apply IHpartM in H4.

  assert(TMSpecMod.put (TMSpecMod.remove Tm t0) t (minus Mc Mm) =
         TMSpecMod.remove (TMSpecMod.put Tm t (minus Mc Mm)) t0).
  rewrite TMSpecMod.remove_ext_ext_remove; auto.
  apply tidspec.beq_false_neq in eq1; auto.
  rewrite H5 in H4; clear H5.

  assert (join m (minus M' Mm) (minus M Mm)).
  assert (TMSpecMod.maps_to (TMSpecMod.remove Tm t0) t Mc).
  apply TMSpecMod.removeX_presv_Y; auto.
  apply tidspec.beq_false_neq in eq1; auto.
  assert (disjoint M' m).
  apply disjoint_sym.
  eapply my_join_disj; eauto.
  lets Hx: part_disjm H5 H3 H6.
  assert (disjoint m Mm).
  apply disjoint_sym in Hx.

  clear - H Hx.
  apply disjoint_sym in Hx.
  apply disjoint_sym.
  eapply mem_disjoint_sub_disjoint; eauto.
  assert (Maps.sub Mm M').
  lets Hx1: part_sub H3 H5.
  eapply sub_trans; eauto.

  eapply mem_join_sub_join_minus_minus'; eauto.

  eapply partm_S; eauto.
  rewrite TMSpecMod.put_noninterfere; auto.
  apply tidspec.beq_false_neq in eq1; auto.
Qed.

Lemma parto_disjoint :
  forall O T To t t' Oc Oc',
    partO O T To ->
    TOSpecMod.maps_to To t Oc ->
    TOSpecMod.maps_to To t' Oc' ->
    t <> t' ->
    disjoint Oc Oc'.
Proof.
  intros.
  inductions H; intros.
  tryfalse.

  destruct (tidspec.beq t0 t) eqn :eq1;
    destruct (tidspec.beq t0 t') eqn : eq2.
  
  apply tidspec.beq_true_eq in eq1;
    apply tidspec.beq_true_eq in eq2; substs; tryfalse.

  apply tidspec.beq_true_eq in eq1; substs.
  unfolds in H2; rewrite H2 in H; inverts H.
  assert (TOSpecMod.maps_to (TOSpecMod.remove Tm t) t' Oc').
  apply TOSpecMod.removeX_presv_Y; auto.
  lets Hx: parto_sub H1 H.

  eapply osabst_join_sub_disjoint; eauto.

  apply tidspec.beq_true_eq in eq2; substs.
  unfolds in H3; rewrite H3 in H; inverts H.
  assert (TOSpecMod.maps_to (TOSpecMod.remove Tm t') t Oc).
  apply TOSpecMod.removeX_presv_Y; auto.
  lets Hx: parto_sub H1 H.
  apply disjoint_sym.
  eapply osabst_join_sub_disjoint; eauto.

  assert(TOSpecMod.maps_to (TOSpecMod.remove Tm t0) t Oc).
  apply TOSpecMod.removeX_presv_Y; auto.
  apply tidspec.beq_false_neq in eq1; auto.
  assert (TOSpecMod.maps_to (TOSpecMod.remove Tm t0) t' Oc').
  apply TOSpecMod.removeX_presv_Y; auto.
  apply tidspec.beq_false_neq in eq2; auto.
  apply IHpartO; auto.
Qed.

Lemma parto_tl_irrel :
  forall Ol Tl Tl' To,
    partO Ol Tl To ->
    partO Ol Tl' To.
Proof.
  intros.
  inductions H.
  constructors; auto.
  eapply parto_S; eauto.
Qed.

Lemma tospecmod_remove_comm :
  forall t t0 Tm,
    t <> t0 ->
    (TOSpecMod.remove (TOSpecMod.remove Tm t) t0) =
    (TOSpecMod.remove (TOSpecMod.remove Tm t0) t).
Proof.
  intros.
  apply TOSpecMod.extensionality; intros.

  destruct (tidspec.beq t0 x) eqn : eq1;
    destruct (tidspec.beq t x) eqn : eq2.

  apply tidspec.beq_true_eq in eq1;
    apply tidspec.beq_true_eq in eq2;
    substs; tryfalse.

  apply tidspec.beq_true_eq in eq1; substs.
  lets Hx: TOSpecMod.nid_remove (TOSpecMod.remove Tm t) x.
  unfolds in Hx.
  rewrite Hx.
  assert (TOSpecMod.not_in_dom x (TOSpecMod.remove Tm x)).
  apply TOSpecMod.nid_remove.
  lets Hx1: TOSpecMod.remove_shrinks_dom t H0.
  rewrite Hx1; auto.

  apply tidspec.beq_true_eq in eq2; substs.
  lets Hx: TOSpecMod.nid_remove (TOSpecMod.remove Tm t0) x.
  unfolds in Hx.
  rewrite Hx.
  assert (TOSpecMod.not_in_dom x (TOSpecMod.remove Tm x)).
  apply TOSpecMod.nid_remove.
  lets Hx1: TOSpecMod.remove_shrinks_dom t0 H0.
  rewrite Hx1; auto.

  apply tidspec.beq_false_neq in eq1;
    apply tidspec.beq_false_neq in eq2.

  destruct (Tm x) eqn : eq3.
  lets Hx: TOSpecMod.removeX_presv_Y eq1 eq3.
  lets Hx1: TOSpecMod.removeX_presv_Y eq2 Hx.
  rewrite Hx1.
  lets Hx3: TOSpecMod.removeX_presv_Y eq2 eq3.
  lets Hx2: TOSpecMod.removeX_presv_Y eq1 Hx3.
  rewrite Hx2; auto.

  lets Hx: TOSpecMod.remove_shrinks_dom t eq3.
  lets Hx1: TOSpecMod.remove_shrinks_dom t0 Hx.
  rewrite Hx1.
  lets Hx2: TOSpecMod.remove_shrinks_dom t0 eq3.
  lets Hx3: TOSpecMod.remove_shrinks_dom t Hx2.
  rewrite Hx3; auto.
Qed.


Lemma parto_minus_remove :
  forall Ol Tl Tl' To t Oc,
    partO Ol Tl To ->
    TOSpecMod.maps_to To t Oc ->
    partO (minus Ol Oc) Tl' (TOSpecMod.remove To t).
Proof.
  intros.
  inductions H.
  tryfalse.

  destruct (tidspec.beq t0 t) eqn : eq1.
  apply tidspec.beq_true_eq in eq1; substs.
  unfolds in H2.
  rewrite H in H2; inverts H2.
  assert (minus M Oc = M').

  apply osabst_join_minus1; auto.
  substs.
  eapply parto_tl_irrel; eauto.

  apply tidspec.beq_false_neq in eq1.
  assert (TOSpecMod.maps_to (TOSpecMod.remove Tm t0) t Oc).
  eapply TOSpecMod.removeX_presv_Y; auto.
  apply IHpartO in H3.

  rewrite tospecmod_remove_comm in H3; auto.
  eapply parto_S; eauto.
  eapply TOSpecMod.removeX_presv_Y; eauto.
  assert (TOSpecMod.maps_to (TOSpecMod.remove Tm t0) t Oc).
  eapply TOSpecMod.removeX_presv_Y; eauto.
  lets Hx: parto_sub H1 H4.
  clear - H0 Hx.

  eapply osabst_join_sub_join_minus; auto.
Qed.


Lemma tmspecmod_remove_comm :
  forall t t0 Tm,
    t <> t0 ->
    (TMSpecMod.remove (TMSpecMod.remove Tm t) t0) =
    (TMSpecMod.remove (TMSpecMod.remove Tm t0) t).
Proof.
  intros.
  apply TMSpecMod.extensionality; intros.

  destruct (tidspec.beq t0 x) eqn : eq1;
    destruct (tidspec.beq t x) eqn : eq2.

  apply tidspec.beq_true_eq in eq1;
    apply tidspec.beq_true_eq in eq2;
    substs; tryfalse.

  apply tidspec.beq_true_eq in eq1; substs.
  lets Hx: TMSpecMod.nid_remove (TMSpecMod.remove Tm t) x.
  unfolds in Hx.
  rewrite Hx.
  assert (TMSpecMod.not_in_dom x (TMSpecMod.remove Tm x)).
  apply TMSpecMod.nid_remove.
  lets Hx1: TMSpecMod.remove_shrinks_dom t H0.
  rewrite Hx1; auto.

  apply tidspec.beq_true_eq in eq2; substs.
  lets Hx: TMSpecMod.nid_remove (TMSpecMod.remove Tm t0) x.
  unfolds in Hx.
  rewrite Hx.
  assert (TMSpecMod.not_in_dom x (TMSpecMod.remove Tm x)).
  apply TMSpecMod.nid_remove.
  lets Hx1: TMSpecMod.remove_shrinks_dom t0 H0.
  rewrite Hx1; auto.

  apply tidspec.beq_false_neq in eq1;
    apply tidspec.beq_false_neq in eq2.

  destruct (Tm x) eqn : eq3.
  lets Hx: TMSpecMod.removeX_presv_Y eq1 eq3.
  lets Hx1: TMSpecMod.removeX_presv_Y eq2 Hx.
  rewrite Hx1.
  lets Hx3: TMSpecMod.removeX_presv_Y eq2 eq3.
  lets Hx2: TMSpecMod.removeX_presv_Y eq1 Hx3.
  rewrite Hx2; auto.

  lets Hx: TMSpecMod.remove_shrinks_dom t eq3.
  lets Hx1: TMSpecMod.remove_shrinks_dom t0 Hx.
  rewrite Hx1.
  lets Hx2: TMSpecMod.remove_shrinks_dom t0 eq3.
  lets Hx3: TMSpecMod.remove_shrinks_dom t Hx2.
  rewrite Hx3; auto.
Qed.

Lemma partm_tl_irrel :
  forall Ml Tl Tl' Tm,
    partM Ml Tl Tm ->
    partM Ml Tl' Tm.
Proof.
  intros.
  inductions H.
  constructors; auto.
  eapply partm_S; eauto.
Qed.

Lemma partm_minus_remove :
  forall Ml Tl Tl' Tm t Mc,
    partM Ml Tl Tm ->
    TMSpecMod.maps_to Tm t Mc ->
    partM (minus Ml Mc) Tl' (TMSpecMod.remove Tm t).
Proof.
  intros.
  inductions H.
  tryfalse.

  destruct (tidspec.beq t0 t) eqn : eq1.
  apply tidspec.beq_true_eq in eq1; substs.
  unfolds in H2.
  rewrite H in H2; inverts H2.
  assert (minus M Mc = M').

  apply mem_join_minus1; auto.
  substs.

  eapply partm_tl_irrel; eauto.

  apply tidspec.beq_false_neq in eq1.
  assert (TMSpecMod.maps_to (TMSpecMod.remove Tm t0) t Mc).
  eapply TMSpecMod.removeX_presv_Y; auto.
  apply IHpartM in H3.

  rewrite tmspecmod_remove_comm in H3; auto.
  eapply partm_S; eauto.
  eapply TMSpecMod.removeX_presv_Y; eauto.
  assert (TMSpecMod.maps_to (TMSpecMod.remove Tm t0) t Mc).
  eapply TMSpecMod.removeX_presv_Y; eauto.
  lets Hx: part_sub H1 H4.
  clear - H0 Hx.

  eapply mem_join_sub_join_minus; auto.
Qed.
  
Lemma parto_complex :
  forall Ol Tl To t' On Oc Os O Olc Oc'0 t,
    partO Ol Tl To ->
    TOSpecMod.maps_to To t' On ->
    TOSpecMod.maps_to To t Oc ->
    t <> t' ->
    join Ol Os O ->
    disjoint Oc'0 Olc ->
    disjoint (merge Oc'0 Olc) (minus Ol Oc) ->
    partO (merge (merge Oc'0 Olc) (minus Ol Oc)) Tl
          (TOSpecMod.put (TOSpecMod.put To t Olc) t' (merge On Oc'0)).
Proof.
  intros.
  clear H3; clears.
  
  lets Hx: parto_minus_remove H H0.
  instantiate (1:=Tl) in Hx.

  assert (TOSpecMod.maps_to (TOSpecMod.remove To t') t Oc).
  apply TOSpecMod.removeX_presv_Y; auto.
  lets Hx1: parto_minus_remove Hx H3.
  instantiate (1:=Tl) in Hx1.

  assert (disjoint Olc (minus (minus Ol On) Oc)).
  lets Hx2: parto_sub H H0.

  eapply osabst_disjoint_minus_minus_disjoint; auto.
  

  eapply osabst_disjoint_merge_disjoint2; eauto.

  assert (partO (merge Olc (minus (minus Ol On) Oc)) Tl (TOSpecMod.put (TOSpecMod.remove To t') t Olc)).
  assert (TOSpecMod.remove (TOSpecMod.remove To t') t = TOSpecMod.remove (TOSpecMod.put (TOSpecMod.remove To t') t Olc) t).
  rewrite TOSpecMod.remove_cancel_put; auto.
  rewrite H7 in Hx1; clear H7.
  eapply parto_S; eauto.
  eapply TOSpecMod.put_get_eq.
  apply join_merge_disj; auto.

  assert (TOSpecMod.remove (TOSpecMod.put (TOSpecMod.put To t Olc) t' (merge On Oc'0)) t' =
          TOSpecMod.put (TOSpecMod.remove To t') t Olc).  
  rewrite TOSpecMod.remove_cancel_put; auto.
  rewrite TOSpecMod.remove_ext_ext_remove; auto.
  rewrite <- H8 in H7.
  eapply parto_S; eauto.
  rewrite TOSpecMod.put_get_eq; eauto.
  lets Hx2: parto_disjoint H H1 H0 H2.
  lets Hx3: parto_sub H H0.
  clear - H4 H5 H6 Hx2 Hx3.

  assert (minus (minus Ol On) Oc = minus (minus Ol Oc) On).

  apply disjoint_sym in Hx2.
  apply osabst_disjoint_minus_comm; auto.
  rewrite H; clear H.

  remember (minus Ol Oc) as X.


  eapply osabst_disjoint_disjoint_merge_distribute; eauto.
  substs.

  eapply osabst_sub_disjoint_sub_minus; auto.
  apply disjoint_sym; auto.
Qed.

Lemma switch_linv:
  forall Mn Mc'0 On Oc'0 on I lasrt t',
    disjoint Mc'0 Mn->
    disjoint Oc'0 On->
    (forall ab : absop, (substaskst on Mc'0, Oc'0, ab) |= RDYINV I t') ->
    satp (substaskst on Mn) On
         (EX lg : list logicvar, LINV lasrt t' lg ** Atrue) ->
    satp (substaskst on (merge Mn Mc'0)) (merge On Oc'0) (CurLINV lasrt t').
Proof.
  intros.
  unfold satp in *.
  intros.
  pose proof H1 aop; clear H1.
  pose proof H2 aop; clear H2.
  destruct on as [[[[]]]].
  simpl substaskst in *.
  unfold RDYINV in H3.
  destruct H3. 
  apply sat_split in H2; mytac.
  simpl in H4; destruct l, p; mytac.
  unfold CurLINV.
  destruct H1.
  exists x.
  unfold CurTid.
  remember (LINV lasrt t' x ** Atrue).
  remember (EX tp : type, GV OSTCBCur @ Tptr tp |-r-> Vptr t').
  simpl.
  exists Mc'0 Mn.
  eexists.
  exists Oc'0 On.
  eexists.
  splits; eauto.
  apply join_comm.
  eapply join_merge_disj.
  apply disjoint_sym; auto.
  apply join_comm.
  eapply join_merge_disj.
  apply disjoint_sym; auto.

  unfold SWINVt in H2.
  unfold CurLINV.
  unfold CurTid.
  destruct H1.
  exists x.
  remember ((EX tp : type, GV OSTCBCur @ Tptr tp |-r-> Vptr t')).
  remember (LINV lasrt t' x ** Atrue).
  sep lift 2%nat in H2.
  apply sat_split in H2.
  mytac.
  remember ((EX tp : type, GV OSTCBCur @ Tptr tp |-r-> Vptr t')).
  remember (LINV lasrt t' x ** Atrue).
  simpl.
  exists x0 (merge x1 Mn); eexists.
  exists x2 (merge x3 On); eexists.
  splits; eauto.
  assert (merge Mn Mc'0 = merge Mc'0 Mn).
  eapply disjoint_merge_sym.
  apply disjoint_sym; auto.
  rewrite H6.
  eapply mem_join_disjoint_join_merge; auto.
  assert (merge On Oc'0 = merge Oc'0 On).
  eapply disjoint_merge_sym.
  apply disjoint_sym; auto.
  rewrite H6.
  eapply osabst_join_disjoint_join_merge; auto.
  substs.
  remember (LINV lasrt t' x).
  simpl in H1.
  simpl.
  mytac.
  exists x4 (merge x5 x1); eexists.
  exists x7 (merge x8 x3); eexists.
  splits; eauto. 
  assert (merge x1 Mn = merge Mn x1).
  eapply disjoint_merge_sym.
  apply join_comm in H2.
  eapply mem_join_disjoint_disjoint; eauto.
  rewrite H1.
  eapply mem_join_disjoint_join_merge; auto.
  apply join_comm in H2.
  apply disjoint_sym.
  eapply mem_join_disjoint_disjoint; eauto.

  assert (merge x3 On = merge On x3).
  eapply disjoint_merge_sym.
  apply join_comm in H3.
  eapply osabst_join_disjoint_disjoint; eauto.
  rewrite H1.
  eapply osabst_join_disjoint_join_merge; auto.
  apply join_comm in H3.
  apply disjoint_sym.
  eapply osabst_join_disjoint_disjoint; eauto.
Qed.


Lemma partm_disjoint :
  forall M T Tm t t' Mc Mc',
    partM M T Tm ->
    TMSpecMod.maps_to Tm t Mc ->
    TMSpecMod.maps_to Tm t' Mc' ->
    t <> t' ->
    disjoint Mc Mc'.
Proof.
  intros.
  inductions H; intros.
  tryfalse.

  destruct (tidspec.beq t0 t) eqn :eq1;
    destruct (tidspec.beq t0 t') eqn : eq2.
  
  apply tidspec.beq_true_eq in eq1;
    apply tidspec.beq_true_eq in eq2; substs; tryfalse.

  apply tidspec.beq_true_eq in eq1; substs.
  unfolds in H2; rewrite H2 in H; inverts H.
  assert (TMSpecMod.maps_to (TMSpecMod.remove Tm t) t' Mc').
  apply TMSpecMod.removeX_presv_Y; auto.
  lets Hx: part_sub H1 H.
  eapply mem_join_sub_disjoint; eauto.

  apply tidspec.beq_true_eq in eq2; substs.
  unfolds in H3; rewrite H3 in H; inverts H.
  assert (TMSpecMod.maps_to (TMSpecMod.remove Tm t') t Mc).
  apply TMSpecMod.removeX_presv_Y; auto.
  lets Hx: part_sub H1 H.
  apply disjoint_sym.
  eapply mem_join_sub_disjoint; eauto.

  assert(TMSpecMod.maps_to (TMSpecMod.remove Tm t0) t Mc).
  apply TMSpecMod.removeX_presv_Y; auto.
  apply tidspec.beq_false_neq in eq1; auto.
  assert (TMSpecMod.maps_to (TMSpecMod.remove Tm t0) t' Mc').
  apply TMSpecMod.removeX_presv_Y; auto.
  apply tidspec.beq_false_neq in eq2; auto.
  apply IHpartM; auto.
Qed.


Lemma partm_merge_sub :
  forall M T Tm t t' Mc Mc',
    partM M T Tm ->
    TMSpecMod.maps_to Tm t Mc ->
    TMSpecMod.maps_to Tm t' Mc' ->
    t <> t' ->
    Maps.sub (merge Mc Mc') M.
Proof.
  intros.
  inductions H; intros.
  tryfalse.

  destruct (tidspec.beq t0 t) eqn :eq1;
    destruct (tidspec.beq t0 t') eqn : eq2.
  
  apply tidspec.beq_true_eq in eq1;
    apply tidspec.beq_true_eq in eq2; substs; tryfalse.

  apply tidspec.beq_true_eq in eq1; substs.
  unfolds in H2; rewrite H2 in H; inverts H.
  assert (TMSpecMod.maps_to (TMSpecMod.remove Tm t) t' Mc').
  apply TMSpecMod.removeX_presv_Y; auto.
  lets Hx: part_sub H1 H.


  eapply mem_join_sub_sub_merge; eauto.

  apply tidspec.beq_true_eq in eq2; substs.
  unfolds in H3; rewrite H3 in H; inverts H.
  assert (TMSpecMod.maps_to (TMSpecMod.remove Tm t') t Mc).
  apply TMSpecMod.removeX_presv_Y; auto.
  lets Hx: part_sub H1 H.

  eapply mem_join_sub_sub_merge'; eauto.

  assert(TMSpecMod.maps_to (TMSpecMod.remove Tm t0) t Mc).
  apply TMSpecMod.removeX_presv_Y; auto.
  apply tidspec.beq_false_neq in eq1; auto.
  assert (TMSpecMod.maps_to (TMSpecMod.remove Tm t0) t' Mc').
  apply TMSpecMod.removeX_presv_Y; auto.
  apply tidspec.beq_false_neq in eq2; auto.
  eapply sub_join_sub; eauto.
Qed.


Lemma parto_merge_sub :
  forall O T To t t' Oc Oc',
    partO O T To ->
    TOSpecMod.maps_to To t Oc ->
    TOSpecMod.maps_to To t' Oc' ->
    t <> t' ->
    Maps.sub (merge Oc Oc') O.
Proof.
  intros.
  inductions H; intros.
  tryfalse.

  destruct (tidspec.beq t0 t) eqn :eq1;
    destruct (tidspec.beq t0 t') eqn : eq2.
  
  apply tidspec.beq_true_eq in eq1;
    apply tidspec.beq_true_eq in eq2; substs; tryfalse.

  apply tidspec.beq_true_eq in eq1; substs.
  unfolds in H2; rewrite H2 in H; inverts H.
  assert (TOSpecMod.maps_to (TOSpecMod.remove Tm t) t' Oc').
  apply TOSpecMod.removeX_presv_Y; auto.
  lets Hx: parto_sub H1 H.
  
  eapply join_sub_sub_merge; eauto.

  apply tidspec.beq_true_eq in eq2; substs.
  unfolds in H3; rewrite H3 in H; inverts H.
  assert (TOSpecMod.maps_to (TOSpecMod.remove Tm t') t Oc).
  apply TOSpecMod.removeX_presv_Y; auto.
  lets Hx: parto_sub H1 H.

  eapply join_sub_sub_merge'; eauto.

  assert(TOSpecMod.maps_to (TOSpecMod.remove Tm t0) t Oc).
  apply TOSpecMod.removeX_presv_Y; auto.
  apply tidspec.beq_false_neq in eq1; auto.
  assert (TOSpecMod.maps_to (TOSpecMod.remove Tm t0) t' Oc').
  apply TOSpecMod.removeX_presv_Y; auto.
  apply tidspec.beq_false_neq in eq2; auto.
  eapply sub_join_sub; eauto.
Qed.

Lemma mem_set_get_neq :
  forall m a a' x,
    a <> a' ->
    set m a x a' = m a'.
Proof.
  intros.
  assert (get (set m a x) a' = get m a').
  rewrite set_a_get_a'; auto.
  eauto.
Qed.

Lemma storebytes_mem_eq_dom_true :
  forall vl a M M',
    storebytes M a vl = Some M' ->
    mem_eq_dom_true M M'.
Proof.
  inductions vl; intros.
  simpl in H; inverts H.
  unfolds; intros.
  split; intros; 
    split; intros; simpljoin1; eauto.
  
  unfold storebytes in H; fold storebytes in H.
  destruct a0.
  unfold get in *; simpl in *.
  destruct (HalfPermMap.get M (b, o)) eqn : eq1; tryfalse.
  destruct b0.
  destruct b0; tryfalse.
  destruct (storebytes M (b, (o + 1)%Z) vl) eqn : eq2; tryfalse.
  inverts H.
  eapply IHvl in eq2; clear IHvl.
  unfolds; intros.
  assert ((b, o) = a0 \/ (b, o) <> a0) by tauto.
  destruct H.
  substs.
  split.
  unfolds in eq2.
  split; intros.
  destruct H.
  assert (HalfPermMap.get M (b, o) = Some (true, x)).
  eauto.
  rewrite eq1 in H0; inverts H0.
  exists a.
  assert (get (set m (b, o) (true, a)) (b, o) = Some (true, a)).
  eapply set_a_get_a.
  eauto.
  eapply eq2.
  destruct H.
  assert (get (set m (b, o) (true, a)) (b, o) = Some (true, x)).
  eauto.
  rewrite set_a_get_a in H0; inverts H0.
  eapply eq2.
  exists c; eauto.
  intro; split; intros.
  unfold HalfPermMap.get in eq1.
  rewrite eq1 in H; inverts H.
  assert (get (set m (b, o) (true, a)) (b, o) = Some (false, x)).
  eauto.
  rewrite set_a_get_a in H0; inverts H0.
  rewrite mem_set_get_neq; auto.
Qed.

Lemma store_mem_eq_dom_true :
  forall t M a v M',
    store t M a v = Some M' ->
    mem_eq_dom_true M M'.
Proof.
  intros.
  unfold store in H; destruct a.
  eapply storebytes_mem_eq_dom_true; eauto.
Qed.


Lemma disj_complex'':
  forall Mc'0 Ms' Ms tp Mc' b t' Mcc Ml Tl Tm Mn m ml Mc t,
    merge Mc'0 Ms' = merge Mcc Ms->
    store (Tptr tp) Mc' (b, 0%Z) (Vptr t') = Some Mcc ->
    Maps.sub Mc' Ml ->
    partM Ml Tl Tm ->
    TMSpecMod.maps_to Tm t' Mn ->
    TMSpecMod.maps_to Tm t Mc ->
    t <> t' ->
    join Ml Ms m ->
    join ml Mc' Mc ->
    disjoint Mc'0 Mn.
Proof.
    intros.
  lets Hx: partm_disjoint H2 H4 H3 H5.
  lets Hx1: partm_merge_sub H2 H4 H3 H5.

  assert (Maps.sub (merge Mc' Mn) Ml).
  eapply mem_disjoint_sub_merge_part; eauto.   
  lets Hx2: store_mem_eq_dom_true H0.
  lets Hx3: mem_sub_merge_mem_eq_dom_true H8 Hx2.
  unfolds in Hx; simpljoin1.
  eapply join_comm in H7.
  eapply mem_join_join_disjoint; eauto.
  simpljoin1.
  assert (disjoint Ml Ms).
  unfolds; eauto.
  lets Hx3: disjoint_mem_eq_dom_true_disjoint H11 H10.
  assert (disjoint Mc' Mn).
  apply join_comm in H7.
  eapply mem_join_disjoint_disjoint; eauto.
  assert (disjoint Mcc Mn).
  eapply disj_store_disj; eauto.
  apply disjoint_sym in Hx3.
  lets Hx4: mem_sub_merge_disjoint_merge_disjont H9 H13 Hx3.
  rewrite <- H in Hx4.
  eapply mem_disjoint_merge_disjoint1; eauto.
Qed.


Lemma disj_complex''':
  forall (Olc Occ Oc' Os'' OO'' O' Os' OO' Ol Oc:osabst)
         x0 Oc'0 On t t' a b b' To Tl,
    get Occ a = Some b ->
    join Oc'0 Os'' OO'' ->
    OO'' = set (merge Occ Os') a b' ->
    join Olc Occ O' ->
    join O' Os' OO' ->
    join OO' (minus Ol Oc) x0 ->
    partO Ol Tl To ->
    TOSpecMod.maps_to To t Oc ->
    TOSpecMod.maps_to To t' On ->
    t <> t' ->
    disjoint Oc'0 On.
Proof.
  intros.
  
  assert (disjoint OO' On).
  lets Hx: parto_disjoint H5 H6 H7 H8.

  assert (disjoint OO' (minus Ol Oc)).
  eapply my_join_disj; eauto.

  assert (Maps.sub On Ol).
  lets Hx1: parto_sub H5 H7; auto.


  apply disjoint_sym in Hx.
  eapply osabst_disjoint_minus_sub_disjoint; eauto.

  assert (disjoint (merge Occ Os') On).

  eapply osabst_join_join_disjoint_merge_disjoint; eauto.
    
  assert (get (merge Occ Os') a = Some b).

  eapply osabst_get_merge; auto.

  assert (disjoint OO'' On).

  substs.
  eapply osabst_get_set_disjoint; eauto.

  eapply osabst_disjoint_join_disjoint; eauto.
Qed.


Lemma rdyinv_isremp :
  forall (o : taskst) (O : osabst) (I : Inv) (M : mem) t,
    (forall ab : absop, (substaskst o M, O, ab) |= RDYINV I t) ->
    forall M' : mem, RdyChange (substaskst o M') = substaskst o M'.
Proof.
  intros.
  lets H100 : H absopx; clear H; rename H100 into H.
  destruct o as [ [ [ [ ] ] ] ]; simpl in *.
  destruct l.
  destruct p.
  destruct H; mytac.
  cut (x14 = empisr).
  intros; subst; auto.
  unfold empisr.
  apply Coqlib.extensionality; auto.
  unfold invlth_isr in *.
  cut (x33 = empisr).
  intros; subst; auto.
  unfold empisr.
  apply Coqlib.extensionality; auto.
Qed.


Lemma swi_rdy_eq_swi :
  forall (o : taskst) (M Mr : mem) (O Or : osabst) (I : Inv) t,
    (forall ab : absop, (substaskst o M, O, ab) |= SWINVt I t) ->
    (forall ab : absop, (substaskst o Mr, Or, ab) |= RDYINV I t) ->
    forall ab : absop, (RdyChange (substaskst o Mr), Or, ab) |= SWINVt I t.
Proof.
  intros.
  lets H100 : H ab; clear H; rename H100 into H.
  lets H100 : H0 ab; clear H0; rename H100 into H0.
  destruct o as [ [ [ [ ] ] ] ]; simpl in *; mytac.
  destruct l.
  destruct p.
  destruct H0; mytac.
  tryfalse.

  exists x1 x2 Mr Or empabst Or.
  splits; eauto.
  apply join_comm; apply join_emp; auto.
  exists empmem x1 x1 empabst Or Or.
  splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  
  do 6 eexists; splits; eauto.
  eapply join_comm; eapply join_emp; auto.
  eapply join_emp; eauto.
  eexists.
  unfold emposabst.
  splits; eauto.
  unfolds; auto.

  do 7 eexists; splits; eauto.
  eapply join_emp; eauto.
  eapply join_emp; eauto.
  unfold emposabst; splits; eauto.
  rewrite plus_0_r.
  cut (x38 = empisr).
  intros; subst; auto.
  unfold empisr.
  apply Coqlib.extensionality; auto.

  do 8 eexists; splits; eauto.
  eapply join_emp; auto.
  eapply join_emp; auto.
  eexists.
  unfold emposabst.
  splits; eauto.
  unfolds; auto.
Qed.


Lemma swinv_isremp :
  forall (o : taskst) (O : osabst) (I : Inv) t,
    (forall ab : absop, (o, O, ab) |= SWINVt I t) ->
    RdyChange o = o.
Proof.
  intros.
  lets Hres : H absopx.
  destruct o as [[[[]]]].
  destruct Hres; trysimplsall; mytac.
  unfolds. 
  destruct H4;trysimplsall; mytac.
  destruct H5; trysimplsall; mytac.
  destruct H0; trysimplsall; mytac.
  simpl in H7; mytac.
  unfold assertion.getmem in *.
  unfold get_smem in *; unfold get_mem in *.
  assert (empisr = x15).
  eapply Coqlib.extensionality.
  unfold empisr.
  eauto.
  subst x15.
  auto.
Qed.


Lemma swdead_ahprio_false:
  forall o O ab sd t x,
    GoodSched sd ->
    (o,O,ab) |= SWPRE_DEAD sd x t ->
    (o,O,ab) |= AHprio sd t ** Atrue ->
    False.
Proof.
  intros.
  destruct o as [[[[]]]].
  unfolds in H.
  simpl in H1; mytac.
  apply H8 in H5.
  mytac.
  
  unfold SWPRE_DEAD in H0.
  destruct H0.
  destruct H3.
  sep split in H3.
  assert (get O abtcblsid = Some (abstcblist x0)).
  clear - H1 H4.
  jeat.
  simpl in H3; mytac.
  assert (get O abtcblsid = Some (abstcblist x2)).
  clear - H11.
  jeat.
  rewrite H6 in H3; inverts H3.
  apply H5.
  unfolds; eauto.
Qed.


Lemma partm_minus_partm :
  forall Ml M Tl Tl' Tm,
    partM (minus Ml M) Tl Tm ->
    partM Ml Tl' Tm.
Proof.
  intros.
  inductions H.
  eapply partm_O; auto.

  assert (exists m5 m6,
             join m m5 Ml /\ join M' m6 m5).
  eapply join_minus_extend; eauto.
  mytac.
  assert (M' = minus x x0).
  eapply join_eq_minus; auto.
  eapply IHpartM in H4.
  eapply partm_S; eauto.
Qed.



Lemma parto_minus_parto :
  forall Ol O Tl Tl' To,
    partO (minus Ol O) Tl To ->
    partO Ol Tl' To.
Proof.
  intros.
  inductions H.
  eapply parto_O; auto.

  assert (exists m5 m6,
             join m m5 Ol /\ join M' m6 m5).
  eapply join_minus_extend; eauto.
  mytac.
  assert (M' = minus x x0).
  eapply join_eq_minus; auto.
  eapply IHpartO in H4.
  eapply parto_S; eauto.
Qed.


Lemma crt_partm:
  forall t Mlc Mcre Mc t' x x' y Tm Tl Ml,
    t <> t' ->
    get Tl t = x ->
    TMSpecMod.maps_to Tm t Mc ->
    join Mlc Mcre Mc ->
    partM Ml Tl Tm ->
    partM Ml (set (set Tl t x') t' y)
          (TMSpecMod.put (TMSpecMod.put Tm t Mlc) t' Mcre).
Proof.
  intros.
  clear H0.
  
  assert (partM (minus Ml Mcre) Tl (TMSpecMod.put Tm t Mlc)).
  lets Hx: partm_minus_remove H3 H1.
  instantiate (1:=Tl) in Hx.
  assert (TMSpecMod.remove Tm t = TMSpecMod.remove (TMSpecMod.put Tm t Mlc) t).
  rewrite TMSpecMod.remove_cancel_put; auto.
  rewrite H0 in Hx; clear H0.
  eapply partm_S; eauto.
  rewrite TMSpecMod.put_get_eq; eauto.

  lets Hx1: part_sub H3 H1.

  eapply mem_join_sub_join_minus_minus; auto.
  lets Hx: TMSpecMod.in_or_notin t' (TMSpecMod.put Tm t Mlc).
  destruct Hx.

  unfolds in H4; destruct H4.
  assert (TMSpecMod.maps_to (TMSpecMod.put Tm t Mlc) t Mlc).
  unfolds.
  rewrite TMSpecMod.put_get_eq; auto.
  lets Hx: partm_minus_remove H0 H5.
  instantiate (1:=Tl) in Hx.
  rewrite TMSpecMod.remove_cancel_put in Hx.
  rewrite TMSpecMod.put_noninterfere in H4; auto.
  assert (TMSpecMod.maps_to (TMSpecMod.remove Tm t) t' x0).
  apply TMSpecMod.removeX_presv_Y; auto.
  lets Hx1: partm_minus_remove Hx H6.
  instantiate (1:=Tl) in Hx1.

  assert (partM (minus (minus Ml Mcre) x0) Tl (TMSpecMod.remove (TMSpecMod.put Tm t Mlc) t')).
  assert (TMSpecMod.remove (TMSpecMod.remove Tm t) t' =
          TMSpecMod.remove (TMSpecMod.remove (TMSpecMod.put Tm t Mlc) t') t).
  symmetry.
  rewrite tmspecmod_remove_comm; auto.
  rewrite TMSpecMod.remove_cancel_put; auto.
  rewrite H7 in Hx1; clear H7.
  eapply partm_S; eauto.
  rewrite TMSpecMod.remove_ext_ext_remove; auto.
  rewrite TMSpecMod.put_get_eq; eauto.

  lets Hx2: part_sub H3 H1.
  lets Hx3: part_sub H3 H4.
  lets Hx4: partm_disjoint H3 H1 H4 H.
  lets Hx5: partm_merge_sub H3 H1 H4 H.
  
  lets Hx6: mem_sub_sub_disjoint_join_minus Hx2 Hx3 Hx5 Hx4 H2; auto.

  assert (TMSpecMod.remove (TMSpecMod.put Tm t Mlc) t' =
          TMSpecMod.remove (TMSpecMod.put (TMSpecMod.put Tm t Mlc) t' Mcre) t').
  rewrite TMSpecMod.remove_cancel_put; auto.
  rewrite H8 in H7; clear H8.
  clear Hx Hx1.

  assert (partM (minus Ml x0) (set (set Tl t x') t' y)
                (TMSpecMod.put (TMSpecMod.put Tm t Mlc) t' Mcre)).
  eapply partm_S; eauto.
  rewrite TMSpecMod.put_get_eq; eauto.

  lets Hx2: part_sub H3 H1.
  lets Hx3: part_sub H3 H4.
  lets Hx4: partm_disjoint H3 H1 H4 H.
  lets Hx5: partm_merge_sub H3 H1 H4 H.

  lets Hx6: mem_sub_sub_disjoint_join_minus1 Hx2 Hx3 Hx5 Hx4 H2; auto.

  eapply partm_minus_partm; eauto.
  assert (TMSpecMod.put Tm t Mlc =
          TMSpecMod.remove (TMSpecMod.put (TMSpecMod.put Tm t Mlc) t' Mcre) t').
  rewrite TMSpecMod.remove_cancel_put.
  rewrite <- TMSpecMod.remove_nothing; auto.
  rewrite H5 in H0; clear H5.
  eapply partm_S; eauto.
  rewrite TMSpecMod.put_get_eq; eauto.
  assert (Maps.sub Mcre Ml).
  lets Hx: part_sub H3 H1.
  assert (Maps.sub Mcre Mc).
  eapply join_sub_r; eauto.
  eapply sub_trans; eauto.

  
  eapply mem_sub_join_minus; eauto.
Qed.


Lemma crt_parto:
  forall Ol Tl To t Oc O' Os' OO' x0 Olc Ocre x x' y t' a b b',
    get Tl t = Some x -> 
    partO Ol Tl To ->
    TOSpecMod.maps_to To t Oc ->
    t <> t' ->
    get OO' a = Some b ->
    join O' Os' (set OO' a b') ->
    join OO' (minus Ol Oc) x0 ->
    join Olc Ocre O' ->
    partO (merge O' (minus Ol Oc)) (set (set Tl t x') t' y)
          (TOSpecMod.put (TOSpecMod.put To t Olc) t' Ocre).
Proof.
  intros.
  clear H.
  lets Hx: TOSpecMod.in_or_notin t' To.
  destruct Hx.

  (*indom t' To*)
  unfolds in H; destruct H.
  lets Hx: parto_minus_remove H0 H.
  instantiate (1:=Tl) in Hx.
  assert (TOSpecMod.maps_to (TOSpecMod.remove To t') t Oc).
  apply TOSpecMod.removeX_presv_Y; auto.
  lets Hx1: parto_minus_remove Hx H7.
  instantiate (1:=Tl) in Hx1.

  assert (partO (merge Olc (minus (minus Ol x1) Oc)) Tl (TOSpecMod.put (TOSpecMod.remove To t') t Olc)).
  assert ( TOSpecMod.remove (TOSpecMod.remove To t') t =
           TOSpecMod.remove (TOSpecMod.put (TOSpecMod.remove To t') t Olc) t).
  rewrite TOSpecMod.remove_cancel_put; auto.
  rewrite H8 in Hx1; clear H8.
  eapply parto_S; eauto.
  rewrite TOSpecMod.put_get_eq; eauto.
  lets Hx2: parto_sub H0 H.
  lets Hx3: parto_sub H0 H1.
  lets Hx4: parto_disjoint H0 H1 H H2.
  assert (disjoint Olc (minus (minus Ol x1) Oc)).
  assert (disjoint OO' (minus (minus Ol x1) Oc)).
  assert (disjoint OO' (minus Ol Oc)).
  eapply my_join_disj; eauto.
  eapply osabst_disjoint_minus_minus_disjoint; auto.
  assert (disjoint (set OO' a b') (minus (minus Ol x1) Oc)).
  eapply osabst_get_set_disjoint; eauto.
  assert (disjoint O' (minus (minus Ol x1) Oc)).
  eapply osabst_disjoint_join_disjoint; eauto.
  eapply osabst_disjoint_join_disjoint; eauto.
  eapply join_merge_disj; auto.

  assert (
      partO (merge O' (minus (minus Ol x1) Oc)) (set (set Tl t x') t' y)
            (TOSpecMod.put (TOSpecMod.put To t Olc) t' Ocre)
    ).
  assert (TOSpecMod.put (TOSpecMod.remove To t') t Olc =
          TOSpecMod.remove (TOSpecMod.put (TOSpecMod.put To t Olc) t' Ocre) t').
  rewrite TOSpecMod.remove_cancel_put.
  rewrite TOSpecMod.remove_ext_ext_remove; auto.
  rewrite H9 in H8; clear H9.
  eapply parto_S; eauto.
  rewrite TOSpecMod.put_get_eq; eauto.

  remember (minus (minus Ol x1) Oc) as X.
  assert (disjoint O' X).
  lets Hx2: parto_sub H0 H.
  lets Hx3: parto_sub H0 H1.
  lets Hx4: parto_disjoint H0 H1 H H2.
  assert (disjoint OO' (minus (minus Ol x1) Oc)).
  assert (disjoint OO' (minus Ol Oc)).
  eapply my_join_disj; eauto.
  eapply osabst_disjoint_minus_minus_disjoint; auto.
  assert (disjoint (set OO' a b') (minus (minus Ol x1) Oc)).
  eapply osabst_get_set_disjoint; eauto.
  assert (disjoint O' (minus (minus Ol x1) Oc)).
  eapply osabst_disjoint_join_disjoint; eauto.
  substs; auto.

  eapply osabst_disjoint_join_join_merge_merge; auto.
  apply join_comm; auto.

  assert (
      merge O' (minus (minus Ol x1) Oc) =
      minus (merge O' (minus Ol Oc)) x1
    ).

  assert (disjoint O' x1).
  assert (disjoint OO' (minus Ol Oc)).
  eapply my_join_disj; eauto.
  assert (Maps.sub x1 Ol).
  lets Hx2: parto_sub H0 H; auto.
  assert (disjoint OO' x1).
  eapply osabst_disjoint_minus_sub_disjoint; eauto.
  lets Hx2: parto_disjoint H0 H1 H H2.
  apply disjoint_sym; auto.
  assert (disjoint (set OO' a b') x1).
  eapply disj_set_disj_1; eauto.
  eapply osabst_disjoint_join_disjoint; eauto.

  lets Hx2: osabst_disjoint_minus_merge_comm H10.
  instantiate (1:=(minus Ol Oc)) in Hx2.
  rewrite <- Hx2.
  assert (minus (minus Ol x1) Oc = minus (minus Ol Oc) x1).
  lets Hx3: parto_disjoint H0 H1 H H2.
  rewrite osabst_disjoint_minus_comm; auto.
  apply disjoint_sym; auto.
  rewrite H11; auto.
  rewrite H10 in H9; clear H10.
  eapply parto_minus_parto; eauto.

  (*not indom t' To*)
  lets Hx: parto_minus_remove H0 H1.
  instantiate (1:=Tl) in Hx.
  assert (partO (merge Olc (minus Ol Oc)) Tl (TOSpecMod.put To t Olc)).
  assert (
      TOSpecMod.remove To t =
      TOSpecMod.remove (TOSpecMod.put To t Olc) t
    ).
  rewrite TOSpecMod.remove_cancel_put; auto.
  rewrite H7 in Hx; clear H7.
  eapply parto_S; eauto.
  rewrite TOSpecMod.put_get_eq; eauto.
  assert (disjoint Olc (minus Ol Oc)).
  assert (disjoint OO' (minus Ol Oc)).
  eapply my_join_disj; eauto.
  assert (disjoint (set OO' a b') (minus Ol Oc)).
  eapply disj_set_disj_1; eauto.
  assert (disjoint O' (minus Ol Oc)).
  eapply osabst_disjoint_join_disjoint; eauto.
  eapply osabst_disjoint_join_disjoint; eauto.
  eapply join_merge_disj; auto.

  assert (
      TOSpecMod.put To t Olc =
      TOSpecMod.remove (TOSpecMod.put (TOSpecMod.put To t Olc) t' Ocre) t'
    ).
  rewrite TOSpecMod.remove_cancel_put.
  rewrite <- TOSpecMod.remove_nothing; auto.
  apply TOSpecMod.putA_presv_nidB; auto.
  rewrite H8 in H7; clear H8.

  eapply parto_S; eauto.
  rewrite TOSpecMod.put_get_eq; eauto.
  eapply osabst_disjoint_join_join_merge_merge; auto.
  assert (disjoint OO' (minus Ol Oc)).
  eapply my_join_disj; eauto.
  assert (disjoint (set OO' a b') (minus Ol Oc)).
  eapply disj_set_disj_1; eauto.
  assert (disjoint O' (minus Ol Oc)).
  eapply osabst_disjoint_join_disjoint; eauto.
  auto.
  apply join_comm; auto.
Qed.

Require Import rulesoundlib.
Lemma linv_change_linv_aux:
  forall g e m ir ir' aux e' aux' O t lasrt lg,
    satp (g, e, m, ir, aux) O  ( lasrt t lg ** [|GoodLInvAsrt lasrt|]) ->
    satp (g, e', m, ir', aux') O  ( lasrt t lg ** [|GoodLInvAsrt lasrt|]).
Proof.
  intros.
  unfold GoodLInvAsrt in *.
  unfold satp in *.
  intro.
  pose proof H aop; clear H.
  sep split in H0.
  sep split; auto. 
  eapply GoodLocalInvAsrt_irrel; eauto.
  eapply H.
Qed.

Lemma crt_init:
  forall Mr Mcre Or Ocre e t' lasrt I,
    disjoint Mr Mcre ->
    disjoint Or Ocre ->
    (forall ab : absop,
       (e, empenv, Mr, empisr, (true, nil, nil), Or, ab) |= RDYINV I t') ->
    satp (e, empenv, Mcre, empisr, (true, nil, nil) ) Ocre
         (lasrt t' init_lg ** [|GoodLInvAsrt lasrt|]) ->
    satp (e, empenv, merge Mr Mcre, empisr, (true, nil, nil)) 
         (merge Or Ocre)
         (CurTid t' ** LINV lasrt t' init_lg ** OS [empisr, true, nil, nil]).
Proof.
  intros.
  unfold satp in *.
  intro.
  pose proof H2 aop; clear H2.
  pose proof H1 aop; clear H1.
  unfold RDYINV in H2; destruct H2.
  apply sat_split in H1; mytac.
  simpl in H4; mytac.
  unfold CurTid.
  remember (EX tp : type, GV OSTCBCur @ Tptr tp |-r-> Vptr t').
  apply sat_split'.
  exists Mr Mcre Or Ocre.
  splits; eauto.
  apply join_merge_disj; auto.
  apply join_merge_disj; auto.
  unfold LINV.
  sep auto.

  unfold SWINVt in H1.
  unfold CurTid.
  sep lift 2%nat in H1.
  apply sat_split in H1; mytac.
  apply sat_split'.
  exists x (merge x0 Mcre).
  exists x1 (merge x2 Ocre).
  splits; eauto.
  eapply mem_join_disjoint_join_merge; auto.
  eapply osabst_join_disjoint_join_merge; auto.

  unfold SWINV in H5.
  simpl in H5; mytac; tryfalse.
Qed.

Lemma linv_split:
  forall ge le Md i aux Od lasrt t,
    satp (ge, le, Md, i, aux) Od
         (EX lg : list logicvar, LINV lasrt t lg ** Atrue) ->
    exists Mdc Mdl Odc Odl,
      join Mdc Mdl Md /\
      join Odc Odl Od /\
      satp (ge, le, Mdc, i, aux) Odc
           (EX lg : list logicvar, LINV lasrt t lg).
Proof.
  intros.
  pose proof H absopx; clear H.
  destruct H0.
  apply sat_split in H; mytac.
  exists x0 x1 x2 x3.
  splits; auto.
  unfold satp; intro.
  exists x.
  unfold LINV in *.
  sep split in H1.
  sep split; auto.
  eapply good_linvasrt_aop_irev; eauto.
Qed.



Lemma delother_partm:
  forall Ml Tl Tm t t' Mc Md Mdc Mdl,
    partM Ml Tl Tm ->
    TMSpecMod.maps_to Tm t Mc ->
    TMSpecMod.maps_to Tm t' Md ->
    t <> t' ->
    join Mdc Mdl Md ->
    partM Ml Tl (TMSpecMod.put (TMSpecMod.put Tm t (merge Mc Mdc)) t' Mdl).
Proof.
  intros.
  lets Hx: partm_minus_remove H H0.
  instantiate (1:=Tl) in Hx.

  assert (TMSpecMod.maps_to (TMSpecMod.remove Tm t) t' Md).
  apply TMSpecMod.removeX_presv_Y; auto.

  lets Hx1: partm_minus_remove Hx H4.
  instantiate (1:=Tl) in Hx1.

  assert (partM (merge (merge Mc Mdc) (minus (minus Ml Mc) Md)) Tl
                (TMSpecMod.remove (TMSpecMod.put Tm t (merge Mc Mdc)) t')).
  assert (TMSpecMod.remove (TMSpecMod.remove Tm t) t' =
          TMSpecMod.remove (TMSpecMod.remove (TMSpecMod.put Tm t (merge Mc Mdc)) t') t
         ).
  rewrite TMSpecMod.remove_ext_ext_remove; auto.
  rewrite TMSpecMod.remove_cancel_put.
  rewrite tmspecmod_remove_comm; auto.
  rewrite H5 in Hx1; clear H5.
  eapply partm_S; eauto.
  rewrite TMSpecMod.remove_ext_ext_remove; auto.
  rewrite TMSpecMod.put_get_eq; eauto.

  lets Hx2: partm_disjoint H H0 H1 H2.

  assert (disjoint (merge Mc Mdc) (minus (minus Ml Mc) Md)).
  lets Hx3: partm_merge_sub H H0 H1 H2.
  clear - H3 Hx2 Hx3.

  eapply mem_join_disjoint_sub_disjoint_merge_minus; eauto.
  eapply join_merge_disj; auto.

  assert (TMSpecMod.remove (TMSpecMod.put Tm t (merge Mc Mdc)) t' =
          TMSpecMod.remove (TMSpecMod.put (TMSpecMod.put Tm t (merge Mc Mdc)) t' Mdl) t'
         ).
  rewrite TMSpecMod.remove_cancel_put; auto.
  rewrite H6 in H5; clear H6.
  eapply partm_S; eauto.
  rewrite TMSpecMod.put_get_eq; eauto.

  lets Hx2: partm_disjoint H H0 H1 H2.
  lets Hx3: partm_merge_sub H H0 H1 H2.
  clear - Hx3 Hx2 H3.
  eapply mem_join_disjoint_sub_merge_join; eauto.
Qed.

Lemma delother_parto:
  forall Ml Tl Tm t t' Mc Md Mdc Mdl,
    partO Ml Tl Tm ->
    TOSpecMod.maps_to Tm t Mc ->
    TOSpecMod.maps_to Tm t' Md ->
    t <> t' ->
    join Mdc Mdl Md ->
    partO Ml Tl (TOSpecMod.put (TOSpecMod.put Tm t (merge Mc Mdc)) t' Mdl).
Proof.
  intros.
  lets Hx: parto_minus_remove H H0.
  instantiate (1:=Tl) in Hx.

  assert (TOSpecMod.maps_to (TOSpecMod.remove Tm t) t' Md).
  apply TOSpecMod.removeX_presv_Y; auto.

  lets Hx1: parto_minus_remove Hx H4.
  instantiate (1:=Tl) in Hx1.

  assert (partO (merge (merge Mc Mdc) (minus (minus Ml Mc) Md)) Tl
                (TOSpecMod.remove (TOSpecMod.put Tm t (merge Mc Mdc)) t')).
  assert (TOSpecMod.remove (TOSpecMod.remove Tm t) t' =
          TOSpecMod.remove (TOSpecMod.remove (TOSpecMod.put Tm t (merge Mc Mdc)) t') t
         ).
  rewrite TOSpecMod.remove_ext_ext_remove; auto.
  rewrite TOSpecMod.remove_cancel_put.
  rewrite tospecmod_remove_comm; auto.
  rewrite H5 in Hx1; clear H5.
  eapply parto_S; eauto.
  rewrite TOSpecMod.remove_ext_ext_remove; auto.
  rewrite TOSpecMod.put_get_eq; eauto.

  lets Hx2: parto_disjoint H H0 H1 H2.

  assert (disjoint (merge Mc Mdc) (minus (minus Ml Mc) Md)).
  lets Hx3: parto_merge_sub H H0 H1 H2.
  clear - H3 Hx2 Hx3.

  eapply osabst_join_disjoint_sub_disjoint_merge_minus; eauto.
  eapply join_merge_disj; auto.

  assert (TOSpecMod.remove (TOSpecMod.put Tm t (merge Mc Mdc)) t' =
          TOSpecMod.remove (TOSpecMod.put (TOSpecMod.put Tm t (merge Mc Mdc)) t' Mdl) t'
         ).
  rewrite TOSpecMod.remove_cancel_put; auto.
  rewrite H6 in H5; clear H6.
  eapply parto_S; eauto.
  rewrite TOSpecMod.put_get_eq; eauto.

  lets Hx2: parto_disjoint H H0 H1 H2.
  lets Hx3: parto_merge_sub H H0 H1 H2.
  clear - Hx3 Hx2 H3.
  eapply osabst_join_disjoint_sub_merge_join; eauto.
Qed.


Lemma disj_complex'''':
  forall OO' a b b' O' Os' x0 Ol Oc Tl To Od t t',
    get OO' a = Some b ->
    join O' Os' (set OO' a b') ->
    join OO' (minus Ol Oc) x0 ->
    partO Ol Tl To ->
    TOSpecMod.maps_to To t Oc ->
    TOSpecMod.maps_to To t' Od -> t <> t' -> disjoint O' Od.
Proof.
  intros.
  lets Hx: parto_disjoint H2 H3 H4 H5.
  assert (disjoint OO' (minus Ol Oc)).
  eapply my_join_disj; eauto.

  lets Hx1: parto_sub H2 H4.

  assert (Maps.sub Od (minus Ol Oc)).
  eapply osabst_sub_disjoint_sub_minus; eauto.
  apply disjoint_sym; auto.

  assert (disjoint OO' Od).
  eapply disj_trans_sub; eauto.

  assert (disjoint (set OO' a b') Od).
  eapply disj_set_disj_1; eauto.
  eapply osabst_join_disjoint_disjoint; eauto.
Qed.

Lemma swpre_hpswitch_nabt:
  forall ge le m i l O A x t,
    satp (ge, le, m, i, l) O (SWPRE A x t) ->
    exists l0 tp t',
      get ge x = Some (l0, Tptr tp) /\
      load (Tptr tp) m (l0, 0%Z) = Some (Vptr t').
Proof.
  intros.
  pose proof H absopx; clear H.
  unfold SWPRE in H0.
  destruct H0.
  simpl in H; simpljoin1.
  do 3 eexists.
  split; eauto.
  lets Hx: mapstoval_load H33.
  simpl; auto.
  eapply load_mem_mono; eauto.
  eapply join_sub_l; eauto.
Qed.

Lemma ahprio_nodead:
  forall o O ab sd I t li,
    GoodI I sd li->
    (o,O,ab) |= AHprio sd t ** Atrue ->
    task_no_dead O t. 
Proof.
  intros.
  unfolds.
  intros.
  destruct o as [[[[]]]].
  simpl in H0; mytac.
  unfolds in H; mytac.
  unfolds in H3; mytac.
  lets Hx: H6 H5; mytac.
  assert (get O abtcblsid = Some (abstcblist x)).
  eapply join_get_get_l; eauto.
  rewrite H1 in H10; inverts H10.
  unfolds; eauto.
Qed.


Lemma AHprio_local:
  forall o Occ O x t ab,
    (o, Occ, ab) |= AHprio x t ** Atrue ->
    Maps.sub Occ O ->
    (o, O, ab) |= AHprio x t ** Atrue.
Proof.
  intros.
  destruct o as [[[[]]]].
  simpl in H; mytac.
  unfolds in H0; destruct H0.
  simpl.
  do 3 eexists.
  exists x3 (merge x4 x0); eexists.
  splits; eauto.
  apply join_emp; auto.
  eapply join_merge23_join; eauto.
Qed.

Lemma nodead_swpredead_false:
  forall o O O' ab sd x t I li,
    GoodI I sd li->
    (o,O,ab) |= SWPRE_DEAD sd x t ->
    Maps.sub O O' ->
    task_no_dead O' t ->
    False.
Proof.
  intros.
  destruct o as [[[[]]]].
  unfold SWPRE_DEAD in H0.
  destruct H0.
  simpl in H3; mytac.
  unfolds in H2.
  pose proof H2 x0; clear H2.
  assert (get (sig abtcblsid (abstcblist x0)) abtcblsid = Some (abstcblist x0)).
  eapply map_get_sig.
  assert (get O abtcblsid = Some (abstcblist x0)).
  eapply join_get_get_l; eauto.
  assert (get O' abtcblsid = Some (abstcblist x0)).
  unfolds in H1; destruct H1.
  eapply join_get_get_l; eauto.
  apply H3 in H5.
  apply H12.
  unfold indom in *; mytac.
  eauto.
Qed.

Lemma ret_st : forall (ge le : env) (M : mem) (ir : isr) (ei : ie) 
         (i0 : hid) (si0 : list hid) (ci : cs) (O : osabst) 
         (isrreg : isr) (i : hid) (si : list hid) (I : Inv)
         (Ch gamma : absop) (G : env) lasrt t lg,
    (ge, le, M, ir, (ei, i0 :: si0, ci), O, gamma)%list
      |= Agenv G //\\
      ( <|| Ch ||>  **
            Aisr (isrupd isrreg i false) **
            Ais (i :: si)%list ** Acs nil ** IRINV I ** A_dom_lenv nil) **
      p_local lasrt t lg->
    ir = isrupd isrreg i false /\ i0 = i /\ si0 = si /\ ci = nil /\ ge = G.
Proof.
  intros.
  destruct H.
  simpl in H; substs.
  remember ( <|| Ch ||>  **
           Aisr (isrupd isrreg i false) **
           Ais (i :: si)%list ** Acs nil ** IRINV I ** A_dom_lenv nil) as X.
  unfold sat in H0; fold sat in H0.
  simpljoin.
  Ltac unfold_sat := unfold getabst in *; unfold substmo in *; unfold substaskst in *; unfold assertion.getmem in *; unfold get_mem in *; unfold get_smem in *.
  unfold_sat.

  simpl in H3; mytac;
  inverts H16; auto.
Qed.


Lemma good_inv_prop_iret
: forall p ir (i:hid) ge le M op abst le' op'    ie cs is ie' cs',
    inv_prop p ->
    GoodInvAsrt p ->
    ir i = false ->
    (ge, le, M, ir, (ie, i::is, cs)%list, abst, op) |= p ->
    (ge, le', M, ir, (ie',is,cs'), abst, op') |= p.
Proof.
  intros.
  assert ((ge, le', M, ir, (ie', i::is, cs'), abst, op') |= p)%list.
  eapply good_inv_prop;eauto.
  unfold  inv_prop in H.
  destruct H.
  unfold assertion.inv_isr_prop in H4.
  mytac. 
  assert ((set_is_s (ge, le', M, ir, (ie', i::is, cs'), abst, op') is)|=p)%list.
  eapply H6;eauto.
  simpl set_is_s in H8.
  auto.
Qed.


Lemma starinv_isr_ncare_aux_ab_iret
: forall (j i : hid) (I : Inv) (ge le le' : env) 
         (m : mem) (O : osabst) (ab ab' : absop)
         ie is cs ie' cs' ir f,
    ir f =false -> 
    (ge, le, m, ir, (ie,f::is,cs), O, ab)%list |= starinv_isr I i j ->
    (ge, le', m, ir, (ie',is,cs'), O, ab') |= starinv_isr I i j.
Proof.
  induction j.
  intros.
  unfold starinv_isr in *.
  simpl in *.
  mytac.
  destruct H0;mytac.
  exists x.
  left;mytac.
  auto.
  exists x.
  right.
  exists empmem m m empabst O O;mytac.
  auto.
  assert ((ge, le', m, x, (ie', f::is, cs'), O, ab')%list |= getinv (I i)).
  eapply good_inv_prop;eauto.
  apply invp.
  lets Hx:prec ((I i)).
  unfold inv_prop in Hx.
  destruct Hx.
  unfold assertion.inv_isr_prop in H2.
  mytac.
  apply H6 with (i0:=f) (is0:=is)in H0;auto.  

  intros.
  unfold starinv_isr.
  unfold starinv_isr in H0.
  fold starinv_isr in *.
  simpl in H0.
  mytac.
  simpl;mytac.
  destruct H4.
  mytac.
  exists empmem m m empabst O O;mytac.
  exists x5;left;mytac.
  auto.
  eapply IHj;eauto.
  mytac.
  exists x x0 m x2 x3 O;mytac;auto.
  exists x5;right;mytac.
  exists empmem x x empabst x2 x2;mytac;auto.
  assert ((ge, le', x, x5, (ie', f::is, cs'), x2, ab')%list |= getinv (I i)).
  eapply good_inv_prop;eauto.
  apply invp.
  lets Hx:prec ((I i)).
  unfold inv_prop in Hx.
  destruct Hx.
  unfold assertion.inv_isr_prop in H4.
  mytac.
  apply H9 with (i0:=f) (is0:=is)in H0;auto.   
  eapply IHj;eauto.
Qed.


Lemma invlth_isr_add_iret:
  forall ge le le' le'' M1 M2 ir ie f is cs ie' cs' O1 O2 i j ab ab' ab'' I,
    ir f = false ->
    disjoint M1 M2 /\ disjoint O1 O2 ->
    i< j -> j<= S INUM->
    (ge,le,M1,ir,(ie, f:: is, cs),O1,ab)%list |= invlth_isr I 0 i -> 
    (ge,le', M2, ir,(ie, f :: is, cs),O2,ab')%list |= invlth_isr I ((i+1)%nat) j -> 
    (ge,le'',merge M2 M1, ir, (ie',is,cs'),merge O2 O1,ab'') |= invlth_isr I 0 j.
Proof.
  introv Hirf.
  intros.
  unfold invlth_isr in *.
  remember (j-(i+1)) as r.
  assert (j-0=S(i+r)).
  omega.
  rewrite H4.
  assert((ge, le'', merge M1 M2, ir, (ie',is,cs'), merge O1 O2, ab'')
           |= starinv_isr I 0 (i - 0) ** starinv_isr I (i + 1) r).
  unfold sat;fold sat;trysimplsall.
  simpl assertion.getmem.
  exists M1 M2 (merge M1 M2 ) O1 O2 (merge O1 O2);mytac.
  eapply join_merge_disj;eauto.
  eapply join_merge_disj;eauto.
  
  eapply starinv_isr_ncare_aux_ab_iret ;eauto.
  eapply starinv_isr_ncare_aux_ab_iret;eauto.
  eapply starinv_isr_elim1;eauto.
  assert (i-0=i).
  omega.
  rewrite H6 in H5.
  assert (i+1= S i).
  omega.
  rewrite H7 in H5.
  auto.
  destruct H.
  assert (merge M2 M1 = merge M1 M2).
  rewrite disjoint_merge_comm; auto.
  apply disjoint_sym; auto.
  rewrite H9.
  assert (merge O2 O1 = merge O1 O2).
  rewrite disjoint_merge_comm; auto.
  apply disjoint_sym; auto.
  rewrite H10.
  auto.
Qed.


Lemma iret_spec :
  forall (genv lenv : env) (m : mem) (isrreg : isr) 
         (ie0 : ie) (is0 : is) (cs0 : cs) (O Os : osabst) 
         (is' : list hid) (i : hid) (ab : absop) (Ms : mem) 
         (I : Inv) (ab' : absop) (G : env) MM OO lasrt t lg,
    join m Ms MM ->
    join O Os OO ->
    satp (genv, lenv, Ms, isrupd isrreg i false, (ie0, is0, cs0))
         Os (INV I) ->
    (genv, lenv, m, isrupd isrreg i false, (ie0, is0, cs0), O, ab)
      |= Agenv G //\\
      ( <|| ab' ||>  **
            Aisr (isrupd isrreg i false) **
            Ais (i :: is')%list ** Acs nil ** IRINV I ** A_dom_lenv nil) **
      p_local lasrt t lg ->
    exists Ml Mi Ol Oi,
      join Ml Mi MM /\
      join Ol Oi OO /\
      satp (genv, lenv, Mi, isrupd isrreg i false, (true, is', cs0)) Oi (INV I)  /\
      satp (genv, lenv, Ml, isrupd isrreg i false, 
            (true, is', cs0)) Ol (p_local lasrt t lg).
Proof.
  intros.
  pose proof H1 absopx; clear H1.
  destruct H2.
  simpl in H1; substs.
  sep normal in H2.
  apply sat_split in H2; mytac.
  simpl in H4; mytac.
  unfold INV in *.
  remember (p_local lasrt t lg).
  simpl in H5; mytac.
  destruct H21; mytac.
  exists m Ms O Os.
  splits; auto.
  unfold satp; intro.
  apply sat_split in H3; mytac.
  apply sat_split'.
  do 4 eexists.
  splits; eauto.
  eapply good_inv_prop_iret; eauto.
  apply prec.
  apply invp.
  unfold isrupd;simpl;auto.
  rewrite Nat.eqb_refl; auto.

  left.
  destruct H4.
  clear - H4.
  unfold inv_ieon in *.
  apply sat_split in H4; mytac.
  apply sat_split'.
  do 4 eexists.
  splits; eauto.
  unfold invlth_isr in *.
  eapply starinv_isr_ncare_aux_ab_iret; eauto.
  unfold isrupd.
  rewrite Nat.eqb_refl; auto.

  clear - H4.
  unfold inv_ieoff in H4; simpl in H4; mytac; tryfalse.

  clear - H27.
  unfold p_local in *.
  unfold satp; intro.
  apply sat_split in H27; mytac.
  apply sat_split'.
  do 4 eexists.
  splits; eauto.
  unfold LINV in *.
  sep split in H2.
  sep split; auto.
  unfolds in H3.
  pose proof H3 t lg; mytac.
  eapply GoodLocalInvAsrt_irrel; eauto.

  (*ie false*)
  apply sat_split in H3; mytac.
  exists x18 (merge Ms x17).
  exists x21 (merge Os x20).
  splits; eauto.
  clear - H18 H.
  apply join_comm in H.
  apply join_comm.
  eapply join_join_join_merge; eauto.
  clear - H20 H0.
  apply join_comm in H0.
  apply join_comm.
  eapply join_join_join_merge; eauto.
  simpl in H11; inverts H11.
  destruct H4.
  clear - H4.
  simpl in H4; mytac; tryfalse.
  
  unfold satp; intro.
  apply sat_split'.
  exists x (merge x0 x17).
  exists x1 (merge x2 x20).
  splits.
  eapply mem_join_disjoint_join_merge; auto.
  clear - H H18.
  apply disjoint_sym.
  eapply mem_join_join_disjoint; eauto.
  eapply osabst_join_disjoint_join_merge; auto.
  clear - H0 H20.
  apply disjoint_sym.
  eapply join_join_disj_l; eauto.

  lets Hx:prec (I (S INUM)).
  unfold inv_prop in Hx.
  destruct Hx.
  unfold assertion.inv_isr_prop in H6.
  mytac.
  eapply good_inv_prop in H3;eauto.
  apply H8 with (i:=x6) (is0:=is') in H3.
  unfold set_is_s in H3.
  eauto.
  simpl;auto.
  unfold isrupd.
  rewrite Nat.eqb_refl; auto.
  simpl; auto.
  apply invp.
  left.

  unfold inv_ieoff in *.
  unfold inv_ieon.
  simpl in H4; mytac.
  destruct H14; mytac.
  apply sat_split'.
  do 4 eexists; splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  simpl; unfold emposabst; auto.
  eapply invlth_isr_add_iret;eauto.
  unfold isrupd.
  rewrite Nat.eqb_refl; auto.
  split.
  clear - H H18 H1.
  apply join_comm in H1.

  eapply join_join_join_disjoint13; eauto.
  clear - H0 H20 H2.
  apply join_comm in H2.
  eapply join_join_join_disjoint13; eauto.

  apply sat_split'.
  do 4 eexists.
  splits; eauto.
  eapply join_emp; eauto.
  eapply join_emp; eauto.
  simpl; unfold emposabst; auto.
  unfold invlth_isr in H17.
  do 2 rewrite jl_merge_emp'.
  eapply starinv_isr_ncare_aux_ab_iret with (f:=INUM);eauto.

  clear - H27.
  unfold p_local in *.
  unfold satp; intros.
  apply sat_split in H27; mytac.
  apply sat_split'.
  do 4 eexists; splits; eauto.
  unfold LINV in *.
  sep split in H2.
  sep split; auto.
  unfolds in H3.
  pose proof H3 t lg.
  destruct H4.
  eapply GoodLocalInvAsrt_irrel; eauto.
Qed.


Lemma mapstoval_false_vptr_eq :
  forall l a x m m',
    mapstoval l (Tptr a) false (Vptr x) m -> mapstoval l (Tptr a) false (Vptr x) m' ->
    m = m'.
Proof.
  intros.
  unfold mapstoval in H, H0; simpljoin1.
  simpl in H1, H2; destruct x; simpl in H1, H2; destruct l; simpljoin1.
  unfold ptomval in *; substs.
  assert (x4 = x10).
  eapply join_unique; eauto.
  substs.
  assert (x2 = x0).
  eapply join_unique; eauto.
  substs.
  eapply join_unique; eauto.
Qed.

Lemma curtid_exact :
  forall ge le le' M M' ir ir' aux aux' O O' absop absop' t,
    (ge, le, M, ir, aux, O, absop) |= CurTid t ->
    (ge, le', M', ir', aux', O', absop') |= CurTid t ->
    M = M' /\ O = O'.
Proof.
  intros.
  simpl in H, H0; mytac.
  rewrite H13 in H4; inverts H4.
  lets Hx: mapstoval_false_vptr_eq H14 H5; auto.
Qed.

Lemma linv_exact :
  forall lasrt t lg ge le le' M M' ir ir' aux aux' O O' absop absop',
    (ge, le, M, ir, aux, O, absop) |= LINV lasrt t lg ->
    (ge, le', M', ir', aux', O', absop') |= LINV lasrt t lg ->
    M = M' /\ O = O'.
Proof.
  intros.
  unfold LINV in *.
  sep split in H; sep split in  H0.
  clear H2.
  unfolds in H1.
  pose proof H1 t lg; clear H1.
  destruct H2.
  unfolds in H2.
  assert (satp (ge, le, M, ir, aux) O (lasrt t lg)).
  unfolds; intro.
  eapply GoodLocalInvAsrt_aop_irev; eauto.
  assert (satp (ge, le', M', ir', aux') O' (lasrt t lg)).
  unfolds; intro.
  eapply GoodLocalInvAsrt_aop_irev; eauto.
  eapply H2; eauto.
Qed.

Lemma p_local_exact:
  forall ge le M ir aux O le' M' aux' ir' O' lasrt t lg,
    satp (ge,le,M,ir,aux) O (p_local lasrt t lg) ->
    satp (ge,le',M',ir',aux') O' (p_local lasrt t lg) ->
    M' = M /\ O' = O.
Proof.
  intros.
  lets Hx: H absopx; clear H.
  lets Hx1: H0 absopx; clear H0.
  unfold p_local in *.
  apply sat_split in Hx; apply sat_split in Hx1.
  simpljoin1.
  lets Hx: curtid_exact H5 H2; simpljoin1.
  lets Hx: linv_exact H6 H3; mytac.
  eapply join_unique; eauto.
  eapply join_unique; eauto.
Qed.


Lemma INV_irrev_prop :
  forall  I ge le M ir aux abst op, 
    (ge, le, M ,ir, aux, abst, op) |= INV I -> 
    forall le' op',
      (ge, le', M ,ir, aux, abst, op') |= INV I.
Proof.
  introv Hsat.
  introv.
  unfold INV in *.
  unfold inv_ieon in *.
  unfold inv_ieoff in *.
  unfold invlth_isr in *.
  unfold sat in *.
  fold sat in *.
  simpl getabst in *.
  simpl substmo in *.
  simpl empst in *.
  simpl getmem in *.
  simpl gettaskst in *.
  destruct aux as [[ie is] cs].
  simpl getis in *.
  destruct Hsat as (M1 & M2 & M0 & o1 & o2 & o & Hsat).
  destruct Hsat as (Hm0 & Hmj & Hoa & Hjoin & Hst & Hsat).
  exists M1 M2 M0 o1 o2 o; splits; eauto.
  eapply   good_inv_prop.
  eapply (invp  (I (S INUM))).
  eauto.
  simpl getie in *.
  destruct Hsat as [Hsat1 | Hsat2].
  left.
  destruct Hsat1 as (M1' & M3' & M' & o1' & O3' & o' & Heq & Hmjj & Hoo & Habs & Hie & Hsat).
  do 6 eexists; splits; eauto.
  eapply inv_isr_irrev_prop ; eauto.
  right.
  destruct Hsat2 as (M1' & M3' & M' & o1' & O3' & o' & Heq & Hmjj & Hoo & Habs & Hie & Hsat).
  do 6  eexists; splits; eauto.
  do 7 eexists; splits; mytac; eauto.
  mytac;eauto.
  mytac; eauto.
  destruct H4.
  left.
  destruct H;mytac.
  do 6 eexists; splits; mytac; eauto.
  mytac.
  eauto.
  mytac.
  eauto.
  omega.
  assert (gettopis is + 0 + 1 =gettopis is + 1)%nat by omega.
  rewrite H.
  eapply inv_isr_irrev_prop ; eauto.
  right.
  splits;mytac; eauto.
  replace ((gettopis is)) with (gettopis is + 0)%nat in H  by omega.
  auto.
Qed.


Lemma inv_ncare_le
: forall (ge le le' : env) (m : mem) (ir : isr) 
         (ls : localst) (O : osabst)  (I : Inv),
    satp (ge, le, m, ir, ls) O (INV I) ->
    satp (ge, le', m, ir, ls) O (INV I).
Proof.
  intros.
  unfold satp in *; intro.
  pose proof H aop.
  eapply INV_irrev_prop; eauto.
Qed.


Lemma p_local_ignore_int :
  forall (ge le : env) (m : mem) (isr0 : isr) 
         (aux : localst) (O : osabst) (le' : env) 
         (isr' : isr) (aux' : localst) (lasrt : tid -> list logicvar -> asrt)
         (t : addrval) lg,
    satp (ge, le, m, isr0, aux) O (p_local lasrt t lg) ->
    satp (ge, le', m, isr', aux') O (p_local lasrt t lg).
Proof.
  intros.
  unfold satp in *.
  intro.
  pose proof H aop; clear H.
  unfold p_local in *.
  unfold sat in *; fold sat in *.
  unfold_sat.
  simpljoin.
  exists x x0 m x2 x3 O.
  splits; auto.
  clear - H4.
  unfold LINV in *.
  sep split in H4; sep split; auto.
  eapply GoodLocalInvAsrt_irrel; eauto.
  eapply H.
Qed.


Lemma linvtrue_merge_hold:
  forall e e0 Mll i0 l Oll lasrt t Ml Ol,
    disjoint Ml Mll ->
    disjoint Ol Oll ->
    satp (e, e0, Mll, i0, l) Oll
         (EX lg' : list logicvar, LINV lasrt t lg' ** Atrue) ->
    satp (e, e0, merge Ml Mll, i0, l) (merge Ol Oll)
         (EX lg' : list logicvar, LINV lasrt t lg' ** Atrue).
Proof.
  intros.
  unfold satp in *.
  intro.
  pose proof H1 aop; clear H1.
  destruct H2.
  exists x.
  simpl in H1; mytac.
  simpl.
  exists x0 (merge Ml x1); eexists.
  exists x3 (merge Ol x4); eexists.
  splits; eauto.
  rewrite disjoint_merge_comm.
  remember (merge x1 Ml).
  rewrite disjoint_merge_comm.
  substs.
  eapply mem_join_disjoint_join_merge; auto.
  apply disjoint_sym; auto.
  auto.
  apply disjoint_sym.
  apply disjoint_sym in H.
  apply join_comm in H2.
  eapply mem_join_disjoint_disjoint; eauto.

  rewrite disjoint_merge_comm.
  remember (merge x4 Ol).
  rewrite disjoint_merge_comm.
  substs.
  eapply osabst_join_disjoint_join_merge; auto.
  apply disjoint_sym; auto.
  auto.
  apply disjoint_sym.
  apply disjoint_sym in H0.
  apply join_comm in H4.
  eapply osabst_join_disjoint_disjoint; eauto.

  do 6 eexists; splits; eauto.
  apply join_comm; apply join_emp; auto.
  apply join_comm; apply join_emp; auto.
  unfolds; auto.
Qed.


Lemma curlinv_p_local_trans:
  forall ge le M ir aux O lasrt t,
    satp (ge, le, M, ir, aux) O (CurLINV lasrt t) ->
    exists Ml Mlinv Ol Olinv lg,
      join Ml Mlinv M /\
      join Ol Olinv O /\
      satp (ge, le, Mlinv, ir, aux) Olinv (p_local lasrt t lg).
Proof.
  intros.
  unfold satp in H.
  pose proof H absopx; clear H.
  unfold p_local.
  unfold CurLINV in H0.
  destruct H0.
  sep lift 3%nat in H.
  remember (CurTid t ** LINV lasrt t x).
  simpl in H; mytac.
  do 5 eexists.
  splits; eauto.
  unfold satp; intro.
  simpl in H4; mytac.
  instantiate (1 := x).
  simpl.
  exists x2 x5 x1.
  exists empabst x4 x4.
  splits; eauto.
  apply join_emp; auto.
  do 8 eexists; splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  eexists.
  unfold emposabst.
  splits; eauto.
  unfolds; auto.
  do 6 eexists; splits; eauto.
  apply join_comm; eapply join_emp; auto.
  apply join_comm.
  apply join_emp; auto.
  eapply GoodLocalInvAsrt_aop_irev; eauto.
  eapply g.
  unfolds; auto.
Qed.

Lemma  inv_noisr_irrev_prop_enint :
  forall n low I ge le M ir i ie is cs abst op, 
    (ge, le, M ,ir, (ie,is,cs), abst, op) |= starinv_noisr I low n -> 
    forall le' op' ie' cs',
      (ge, le', M ,isrupd ir i true, (ie',i::is,cs') , abst, op')%list |= starinv_noisr I low n.
Proof.
  inductions n.
  simpl starinv_isr.
  introv Hsat.
  introv.
  simpl.
  simpl in Hsat.
  assert ( (ge, le', M, ir, (ie', is, cs'), abst, op') |= getinv (I low)).
  eapply  good_inv_prop.
  eapply (invp  (I low)).
  eauto.
  lets Hx: prec ( (I low)).
  destruct Hx.
  unfold assertion .inv_isr_prop in H1.
  mytac.
  apply H2 with (i:=i) in H.
  unfold set_isisr_s in H.
  unfold get_isr_s, get_is_s in H.
  auto.

  
  introv Hsat.
  introv.
  simpl starinv_isr.
  simpl starinv_noisr in *.
  unfold sat in *.
  fold sat in *.
  simpl substmo in *.
  simpl getmem in *.
  simpl getabst in *.
  destruct Hsat as (M1 & M2 & M0 & o1 & o2 & o & Hsat).
  destruct Hsat as (HM & Hmm & Ho & Habsj & Hsat).
  exists M1 M2 M0 o1 o2 o; splits; auto.
  destruct Hsat.

  assert ( (ge, le', M1, ir, (ie', is, cs'), o1, op') |= getinv (I low)).
  eapply  good_inv_prop.
  eapply (invp  (I low)).
  eauto.
  lets Hx: prec ( (I low)).
  destruct Hx.
  unfold assertion .inv_isr_prop in H3.
  mytac.
  apply H4 with (i:=i) in H1.
  unfold set_isisr_s in H1.
  unfold get_isr_s, get_is_s in H1.
  auto.

  destruct Hsat.
  eapply IHn; eauto.
Qed.

Require Import step_prop.

Lemma starinvnoisr_prop1_rev:
  forall  j i I,
    (starinv_noisr I i j) ** (starinv_noisr I (S (i+j)) 0)%nat ==> 
                          (starinv_noisr I i (S j)). 
Proof.
  inductions j.
  introv Hsat.
  trysimplsall.
  assert (S i = S (i+0)) by omega.
  rewrite <- H in Hsat.
  auto.
  introv Hsat.
  simpl starinv_noisr in *.
  sauto.
  assert (S (i + S j) = S (S i + j)) by omega.
  rewrite H in *.
  lets Hrs : IHj Hsat.
  sauto.
Qed.

Lemma invisr_imply_noisr' :
  forall j ge le M ir aux O ab I ,
    ( forall i : hid, i <= j -> ir i = false) -> 
    (ge, le, M, ir, aux, O, ab) |= starinv_isr I 0 j -> 
    (ge, le, M, ir, aux, O, ab) |= starinv_noisr I 0 j.
Proof.
  inductions j.   
  intros.
  unfold starinv_noisr.
  unfold starinv_isr in H0.
  destruct H0; mytac.
  destruct H0; mytac.
  destruct H0;mytac; tryfalse.
  simpl in H0; simpl in H1; mytac.
  lets Hs :  H 0; tryfalse.    
  assert (0<=0) by omega.
  apply Hs in H1; tryfalse.
  destruct H0; mytac.
  trysimplsall.
  destruct H4; mytac.
  simpl in H0; simpl in H2; mytac.
  auto.
  introv Hsat Hss.
  apply starinv_prop1 in Hss.
  destruct Hss;mytac.
  trysimplsall.
  destruct H4; mytac.
  destruct H; mytac.
  destruct H; mytac.
  simpl in H; simpl in  H1; mytac.
  lets Hs : Hsat (S j); tryfalse.
  assert (S j <= S j) by omega.
  apply Hs in H0; tryfalse.
  destruct H; mytac.
  destruct H6; mytac.
  trysimplsall.
  simpl in H; simpl in  H4; mytac.
  assert (forall i : hid, i <= j -> x1 i = false).
  introv Hij.
  eapply Hsat; omega.
  lets Hres : IHj H1 H3.               
  eapply starinvnoisr_prop1_rev.
  replace (S (0 + j)) with (S j) by omega.
  do 6 eexists; mytac;eauto. 
Qed.

Lemma isr_false_inv_eq: 
  forall i ge le M ir ie ie' is cs cs' O ab I,
    i<INUM ->
    higherint ir i -> 
    (ge,le,M,ir,(ie,is,cs),O,ab) |= invlth_isr I 0 i -> 
    (ge,le,M, isrupd ir i true, (ie',i::is,cs'),O,ab)%list |= invlth_noisr I 0 i.
Proof.    
  introv Hfor Hh Hinv.
  unfolds in Hh.
  unfold invlth_noisr in *.
  unfold invlth_isr in *.
  replace (i-0) with i in * by omega.  
  eapply inv_noisr_irrev_prop_enint;
  eapply invisr_imply_noisr' ; eauto.
Qed.

Lemma invlth_add_sinum':
  forall i ge le M M' M'' ir aux O O' O'' ab I,
    i<= INUM ->
    join M M' M'' ->
    join O O' O'' ->
    (ge,le,M',ir,aux,O',ab) |= invlth_isr I (i%nat) INUM -> 
    (ge,le,M,ir,aux,O,ab) |= getinv (I (S INUM)) ->
    (ge,le,M'',ir,aux,O'',ab) |= invlth_isr I (i%nat) INUM** getinv (I (S INUM)). 
Proof. 
  introv Hinu Hmj Hdj Hsat1 Hsat2.                                           
  unfold invlth_isr in *.
  exists M' M  M''.
  exists  O' O  O''.
  splits;simpl substmo in *;  mytac; eauto.
Qed.

Lemma isr_false_eq :
  forall ir i , ir i = false  -> ir = isrupd (isrupd ir i true) i false.
Proof.
  intros.
  eapply Coqlib.extensionality.
  intros.
  unfold isrupd.
  remember (beq_nat i x) as Hr.
  destruct Hr.
  apply eq_sym in HeqHr.
  apply beq_nat_true in HeqHr.
  subst. auto.
  auto.
Qed.

Lemma isr_false_sat1 :
  forall ir i  ge le M ie is cs O ab ie' (j : nat)  cs' I,
    ir i = false ->
    (ge,le,M,isrupd ir i true,(ie,i::is,cs),O,ab)%list |= getinv (I j) ->
    (ge,le,M,ir,(ie',is,cs'),O,ab) |=  getinv (I j).
Proof.
  introv Hir Hsat.
  lets Heq : isr_false_eq  Hir.
  eapply good_inv_prop.
  apply invp.   
  destruct (prec (I j)) as [Hja Hjb].
  destruct Hjb as (Ht1 & Ht2 & Ht3 & Ht4).
  lets Hres : Ht1 Hsat.
  simpl in Hres.
  lets Hd : Hres i.
  lets Haa : Ht3 Hd.
  simpl in Haa.
  rewrite <- isr_false_eq in  Haa .
  eapply Haa;eauto.
  eauto.   
Qed.

Lemma le_beq_nat_false :
  forall i j, i < j -> beq_nat i j = false.
Proof.
  inductions i;inductions j;intros; tryfalse.  
  inverts H.
  simpl;auto.
  inverts H.
  simpl.
  apply IHi.
  omega.
Qed.

Lemma isr_true_aux :  
  forall  n i j ir I ge le M   ie is cs ie' cs' abst op,
    ir i = false ->
    i < j -> 
    (ge, le, M ,  isrupd ir i true , (ie,i::is,cs), abst, op)%list |= starinv_isr I j n -> 
    (ge, le, M ,ir , (ie',is,cs'), abst, op) |= starinv_isr I j n.   
Proof.
  inductions n.
  introv Hir Hij Hsat.
  simpl starinv_isr.
  simpl in Hsat.
  mytac.
  destruct H.
  mytac.
  exists ir.
  left.
  simpl;
    splits; mytac; auto.
  unfolds in H.
  erewrite le_beq_nat_false in H; eauto.
  exists ir.
  right.
  simpl.
  do 6 eexists; trysimplsall; splits; mytac; eauto.
  mytac.
  auto.
  mytac.
  auto.
  unfolds in H3.
  erewrite  le_beq_nat_false in H3; eauto.
  eapply good_inv_prop.
  apply invp.
  eapply isr_false_sat1;eauto.
  intros.
  simpl in H1.
  mytac.
  destruct H5.
  mytac.
  simpl.
  do 6 eexists; splits; mytac; eauto.
  mytac.
  mytac.
  exists ir.
  left.
  splits;mytac;  auto.
  unfolds in H1.
  erewrite  le_beq_nat_false in H1; eauto.
  mytac.
  simpl.
  exists  x x0  M  x2 x3 abst.
  splits; mytac; auto.
  exists ir.
  right.
  exists empmem x x empabst x2 x2.
  splits; mytac; auto.    
  unfolds in H8.
  erewrite  le_beq_nat_false in H8; eauto.
  eapply isr_false_sat1; eauto.
  eapply IHn; eauto.
  Grab Existential Variables.
  exact nil.
  exact false.
Qed.

Lemma isr_true_S_i':
  forall I i ge le M ir ie is cs ie' cs' ab O j,
    i<j->
    j<=INUM ->
    ir i = false ->
    (ge,le,M,isrupd ir i true,(ie,i::is,cs),O,ab)%list |= invlth_isr I (i+1)%nat j ** getinv (I (S INUM))->
    (ge,le,M,ir,(ie',is,cs'),O,ab) |= invlth_isr I (i+1)%nat j ** getinv (I (S INUM)).
Proof.
  introv Hij Hjnum Hir Hsat.
  simpl in Hsat.
  mytac.
  do 6 eexists.
  splits; trysimplsall;eauto.
  2: eapply isr_false_sat1 ; eauto.
  unfold invlth_isr in *.
  eapply isr_true_aux; eauto. omega.
Qed.

Lemma starinv_isr_ncare_ab:
  forall j i I ge isr le le' m aux O ab ab', 
    (ge, le, m , isr, aux, O, ab)
      |= starinv_isr I i j ->
    (ge, le', m ,isr, aux, O, ab')
      |= starinv_isr I i j .
Proof.
  induction j.
  intros.
  unfold starinv_isr in *.
  simpl in *.
  mytac.
  destruct H;mytac.
  exists x.
  left.
  mytac.
  auto.
  exists x.
  right.
  exists empmem m m empabst O O;mytac.
  auto.
  destruct aux as [[]].
  eapply good_inv_prop;eauto.
  apply invp.
  intros.
  unfold starinv_isr.
  unfold starinv_isr in H.
  fold starinv_isr in *.
  simpl in H.
  mytac.
  simpl;mytac.
  destruct H3.
  mytac.
  exists empmem m m empabst O O;mytac.
  exists x5;left;mytac.
  auto.
  eapply IHj;eauto.
  mytac.
  exists x x0 m x2 x3 O;mytac;auto.
  exists x5;right;mytac.
  exists empmem x x empabst x2 x2;mytac;auto.
  destruct aux as [[]].
  eapply good_inv_prop;eauto.
  apply invp.
  eapply IHj;eauto.
Qed.

Definition cjy_and1 := Coq.Init.Logic.and.
Lemma precise_starinv_isr :
  forall I low n,
    precise (starinv_isr I low n).
Proof.
  intros.
  gen I low.
  induction n; intros; simpl in *.
  unfold precise; intros.
  unfold sat in H, H0; fold sat in H, H0; fold cjy_and1; mytac.
  destruct s as [ [ [ [ [ [ ] ] ] ] ] ]; simpl in *.
  destruct H, H0; mytac; unfold cjy_and1.
  split; intros; auto.
  tryfalse.
  tryfalse.
  change (e, e0, M1, x, l, o1, a) with (substmo (e, e0, M1, x, l, o1, a) M1 o1) in H15.
  change (e, e0, M2, x, l, o2, a) with (substmo (e, e0, M1, x, l, o1, a) M2 o2) in H5.
  assert (precise (getinv (I low))) by apply prec.
  lets H100 : H H15 H5.
  auto.

  unfold precise in *; intros.
  unfold sat in H, H0; fold sat in H, H0; fold cjy_and1; mytac.
  destruct s as [ [ [ [ [ [ ] ] ] ] ] ]; simpl in *.
  destruct H9, H4; mytac; unfold cjy_and1.
  change (e, e0, M1, x11, l, o1, a) with (substmo (e, e0, M1, x11, l, o1, a) M1 o1) in H10.
  change (e, e0, M2, x11, l, o2, a) with (substmo (e, e0, M1, x11, l, o1, a) M2 o2) in H5.
  lets H100 : IHn H10 H5; auto.
  tryfalse.
  tryfalse.
  change (e, e0, x6, x11, l, x9, a) with (substmo (e, e0, x6, x11, l, x9, a) x6 x9) in H10.
  change (e, e0, x0, x11, l, x3, a) with (substmo (e, e0, x6, x11, l, x9, a) x0 x3) in H5.
  lets H100 : IHn H10 H5.
  change (e, e0, x5, x11, l, x8, a) with (substmo (e, e0, x5, x11, l, x8, a) x5 x8) in H21.
  change (e, e0, x, x11, l, x2, a) with (substmo (e, e0, x5, x11, l, x8, a) x x2) in H11.
  assert (precise (getinv (I low))) as H200 by apply prec.
  lets H300 : H200 H21 H11; clear H200.
  destruct H100, H300; split; intros.
  
  lets Hx1: mem_join_sub_r H6.
  lets Hx2: mem_join_sub_r H1. 
  lets H100: H (sub_trans Hx1 H7)
                (sub_trans Hx2 H12).
  lets Hx3: mem_join_sub_l H6.
  lets Hx4: mem_join_sub_l H1. 
  lets H200 : H2 (sub_trans Hx3 H7)
                 (sub_trans Hx4 H12).
  subst.
  eapply join_unique; eauto.

  lets Hx1: osabst_join_sub_r H8.
  lets Hx2: osabst_join_sub_r H3. 
  lets H100: H0 (sub_trans Hx1 H7)
                (sub_trans Hx2 H12).
  lets Hx3: osabst_join_sub_l H8.
  lets Hx4: osabst_join_sub_l H3. 
  lets H200 : H4 (sub_trans Hx3 H7)
                 (sub_trans Hx4 H12).
  subst.
  eapply join_unique; eauto.
Qed.

Lemma invlth_isr_minus:
  forall ge le M1 M2 ir aux O1 O2 i j ab ab' ab'' I, 
    i< j -> j<= S INUM ->
    disjoint M1 M2 -> disjoint O1 O2 ->    
    (ge,le, M2,ir,aux,O2,ab') |= invlth_isr I ((i+1)%nat) j -> 
    (ge,le, merge M1 M2,ir,aux, merge O1 O2,ab'') |= invlth_isr I 0 j ->
    (ge,le,M1,ir,aux,O1,ab) |= invlth_isr I 0 i .
Proof.
  intros.
  unfold invlth_isr in *.
  destruct j.
  inverts H.
  assert (i<= j) by omega.
  lets Hres : starinv_prop H5 H4.
  destruct Hres;mytac.
  simpl substmo in *.
  simpl getabst in *.
  simpl getmem in *.
  assert ( (S j - (i + 1) =  (S j - S i) ))%nat by omega.
  rewrite H6 in H3.
  replace (i+1) with (S i) in H3 by omega.
  assert (substmo (ge, le,  merge M1 M2 , ir, aux, merge O1 O2, ab') M2 O2 |= starinv_isr I (S i) (S j - S i)) by (simpl substmo; auto).
  assert (substmo (ge, le,  merge M1 M2 , ir, aux, merge O1 O2, ab') x0 x3 |= starinv_isr I (S i) (S j - S i)) by (simpl substmo ; eapply starinv_isr_ncare_ab; eauto).
  lets Hres : precise_starinv_isr H8 H12.
  assert (Maps.sub M2 (merge M1 M2)).  
  eapply disjoint_sub_merge_r; auto.
  assert (Maps.sub x0  (merge M1 M2)). 
  eapply join_sub_r;eauto.
  assert (Maps.sub O2 (merge O1 O2)).  
  eapply disjoint_sub_merge_r; auto.
  assert (Maps.sub x3 (merge O1 O2)). 
  eapply join_sub_r;eauto.
  destruct Hres.
  lets Heq1 : H18 H15 H16.
  lets Heq2 : H17 H13 H14.
  subst.
  apply join_merge_disj in H1.
  apply join_comm in H1.
  apply join_comm in H7.
  lets Heqq : join_unique_r H1 H7.
  subst.
  apply join_merge_disj in H2.
  apply join_comm in H2.
  apply join_comm in H9.
  lets Heqq : join_unique_r H2 H9.
  subst.
  replace (i-0) with i by omega.
  eapply starinv_isr_ncare_ab; eauto.
Qed.



Lemma invlth_isr_minus':
  forall ge le M1 M2 ir aux O1 O2 i j ab ab' ab'' I, 
    i< j -> j<= S INUM ->
    disjoint M1 M2 -> disjoint O1 O2 ->    
    (ge,le, M2,ir,aux,O2,ab') |= invlth_isr I ((i+1)%nat) j**getinv (I (S INUM)) -> 
    (ge,le,merge M1 M2,ir,aux, merge O1 O2,ab'') |= invlth_isr I 0 j ** getinv (I (S INUM))->
    (ge,le,M1,ir,aux,O1,ab) |= invlth_isr I 0 i .
Proof.
  intros.
  destruct j.
  inverts H.
  destruct H3;mytac.
  destruct H4;mytac.
  simpl substmo in *.
  simpl getabst in *.
  simpl getmem in *.
  assert
    (substmo (ge, le,  merge M1 M2 , ir, aux, merge O1 O2, ab') x0 x3 |= 
             getinv (I (S INUM))) by (simpl substmo; auto).
  assert (substmo (ge, le,  merge M1 M2 , ir, aux, merge O1 O2, ab') x4 x7 |= getinv (I (S INUM))).  
  simpl.
  destruct aux as [[]].
  eapply good_inv_prop; eauto.
  eapply invp.
  destruct (prec  (I (S INUM))) as [Hpre Hcc].

  lets Hres : Hpre H3 H6.
  destruct Hres.
  assert (Maps.sub x4 (merge M1 M2)).
  eapply join_sub_r; eauto.
  assert (Maps.sub x0 (merge M1 M2)).
  assert (Maps.sub x0 M2).
  eapply join_sub_r; eauto.
  assert (Maps.sub M2 (merge M1 M2) ).
  eapply disjoint_sub_merge_r; eauto.
  eapply sub_trans; eauto.
  assert (Maps.sub x7 (merge O1 O2)).
  eapply join_sub_r; eauto.

  assert (Maps.sub x3 (merge O1 O2)).
  assert (Maps.sub x3 O2).
  eapply join_sub_r; eauto.
  assert (Maps.sub O2 (merge O1 O2)).
  eapply disjoint_sub_merge_r; auto.
  eapply sub_trans; eauto.
  lets Heq1 : H13 H16 H15.
  lets Heq2 : H14 H18 H17.
  subst x4; subst x7.
  lets Hres : Mem_disjoint_join_disjoint H1 H4 H5.
  destruct Hres.
  lets Hres : OSAbst_disjoint_join_disjoint H2 H10 H7.
  destruct Hres.
  subst x1.
  subst x6.
  eapply invlth_isr_minus with (M1:=M1)(M2:=x)(O1:=O1)(O2:=x2);eauto.
Qed.

Lemma eq_dom_env_emp :
  eq_dom_env empenv nil.
Proof.
  unfolds.
  split; intros.
  simpl in H; tryfalse.
  destruct H.
  unfold empenv in H; simpl in H.
  unfold get in H; simpl in H.
  rewrite EnvMod.emp_sem in H; tryfalse.
Qed.


Lemma en_int_inv :
  forall Mi Ms'  (ir : isr) (is0 : language.is)
         Os' Oi (x : absop) (I : Inv) i 
         (G : env) lasrt t Ms Os Mlinv Olinv lg,
    disjoint Mlinv Ms ->
    disjoint Olinv Os ->
    join Mi Ms' Ms->
    join Oi Os' Os->
    higherint ir i ->
    (i < INUM)%nat ->
    (forall ab : absop,
       (G, empenv, Ms, ir, (true, is0, nil), 
        Os, ab) |= INV I) ->
    (forall ab : absop,
        (G, empenv, Ms', isrupd ir i true, (false, i :: is0, nil)%list, Os', ab)
          |= INV I) ->
    satp (G, empenv, Mlinv, isrupd ir i true, (false, i :: is0, nil)%list) Olinv (p_local lasrt t lg) ->
    (G, empenv, (merge Mi Mlinv), isrupd ir i true, (false, i :: is0, nil)%list, (merge Oi Olinv), x)
      |= ipreasrt i ir is0 x I G lasrt t lg /\ satp (G, empenv, merge Mi Mlinv, isrupd ir i true, (false, i :: is0, nil)%list) (merge Oi Olinv) (CurLINV lasrt t).
Proof.
  intros.
  split.
  unfold ipreasrt.
  split.
  simpl; auto.
  sep normal.
  apply sat_split'.
  do 4 eexists.
  splits; eauto.
  eapply join_emp; auto.
  eapply join_emp; auto.
  simpl; unfold emposabst; auto.

  apply sat_split'.
  do 4 eexists.
  splits; eauto.
  eapply join_emp; auto.
  eapply join_emp; auto.
  simpl; unfold emposabst; auto.
  
  apply sat_split'.
  do 4 eexists.
  splits; eauto.
  eapply join_emp; auto.
  eapply join_emp; auto.
  simpl; unfold emposabst; auto.

  apply sat_split'.
  do 4 eexists.
  splits; eauto.
  eapply join_emp; auto.
  eapply join_emp; auto.
  simpl; unfold emposabst; auto.

  apply sat_split'.
  do 4 eexists.
  splits; eauto.
  eapply join_emp; auto.
  eapply join_emp; auto.
  simpl; unfold emposabst; auto.

  apply sat_split'.
  do 4 eexists.
  splits; eauto.
  eapply join_emp; auto.
  eapply join_emp; auto.
  unfold isr_inv.
  exists (isrupd ir i true).
  split.
  simpl; unfold emposabst; auto.
  exists i.
  split.
  simpl; unfold emposabst; auto.
  simpl; unfold emposabst; splits; auto.
  intros.
  clear - H3 H8.
  unfolds in H3.
  pose proof H3 j.
  assert (j <= i).
  clear- H8.
  omega.
  apply H in H0.
  unfold isrupd.
  assert (Nat.eqb i j = false).
  assert (i <> j).
  omega.
  apply Nat.eqb_neq in H1; auto.
  rewrite H1; auto.
  apply sat_split'.
  exists Mi Mlinv Oi Olinv.
  splits.
  apply join_merge_disj.
  apply disjoint_sym in H.
  eapply mem_join_disjoint_disjoint; eauto.
  apply join_merge_disj.
  apply disjoint_sym in H0.
  eapply osabst_join_disjoint_disjoint; eauto.
  eapply isr_false_inv_eq with true nil; eauto.
  lets Hx_false: H6 absopx; clear H6.
  lets Hx_true: H5 absopx; clear H5.
  unfold INV in *.
  apply sat_split in Hx_false; mytac.
  destruct H9.
  unfold inv_ieon in H9.
  simpl in H9; mytac; tryfalse.
  unfold inv_ieoff in H9.
  apply sat_split in H9; mytac.
  destruct H12.
  apply sat_split in H12; mytac.
  destruct H15.
  simpl in H11; simpl in H14; mytac.
  sep split in H15.
  lets Hs: invlth_add_sinum' H15 H8; eauto.
  omega.
  apply sat_split in Hx_true; mytac.
  destruct H13.
  unfold inv_ieon in H13.
  apply sat_split in H13; mytac.
  simpl in H16; mytac.
  lets Hss: invlth_add_sinum' H17 H12; eauto.
  omega.
  unfold higherint in H3.
  apply isr_true_S_i' with (ie':=true) (cs':=nil)in Hs; auto.
  lets Hx: invlth_isr_minus'.
  assert (Ms = merge Mi Ms').
  eapply map_join_merge'; auto.
  assert (Os = merge Oi Os').
  eapply map_join_merge'; auto.
  substs.
  eapply invlth_isr_minus';eauto.
  eapply my_join_disj; eauto.
  eapply my_join_disj; eauto.

  unfold inv_ieoff in H13.
  simpl in H13; mytac; tryfalse.
  simpl in H15; mytac.
  simpl in H14; mytac.
  clear - H4.
  false.
  omega.

  pose proof H7 x; clear H7.
  apply sat_split'.
  do 4 eexists.
  splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  simpl.
  unfold emposabst; splits; auto.
  apply eq_dom_env_emp.
  unfold CurLINV.
  unfold p_local in H7.
  unfold satp in *.
  
  intro.
  clear - H7 H H0 H1 H2.
  pose proof H7 aop; clear H7.
  exists lg.
  apply sat_split in H3; mytac.
  apply sat_split'.
  exists x (merge x0 Mi).
  exists x1 (merge x2 Oi).
  splits; auto.
  assert (disjoint Mi Mlinv).
  eapply mem_join_disjoint_disjoint; eauto.
  apply disjoint_sym; auto.
  assert (merge Mi Mlinv = merge Mlinv Mi).
  eapply disjoint_merge_sym; auto.
  rewrite H8; clear H8.
  eapply mem_join_disjoint_join_merge; auto.
  apply disjoint_sym; auto.
  assert (disjoint Oi Olinv).
  eapply osabst_join_disjoint_disjoint; eauto.
  apply disjoint_sym; auto.
  assert (merge Oi Olinv = merge Olinv Oi).
  eapply disjoint_merge_sym; auto.
  rewrite H8; clear H8.
  eapply osabst_join_disjoint_join_merge; auto.
  apply disjoint_sym; auto.

  apply sat_split'.
  exists x0 Mi x2 Oi.
  splits; auto.
  eapply join_merge_disj.
  apply join_comm in H3.
  assert (disjoint x0 Ms).
  eapply mem_join_disjoint_disjoint; eauto.
  apply disjoint_sym in H7.
  apply disjoint_sym.
  eapply mem_join_disjoint_disjoint; eauto.
  eapply join_merge_disj.
  apply join_comm in H4.
  assert (disjoint x2 Os).
  eapply osabst_join_disjoint_disjoint; eauto.
  apply disjoint_sym in H7.
  apply disjoint_sym.
  eapply osabst_join_disjoint_disjoint; eauto.

  simpl; auto.
Qed.

Lemma inv_substask_emple
: forall (genv lenv : env) (M1 : mem) (ir : isr) 
         (aux : localst) (Ms : mem) (Os : osabst) (I : Inv),
    satp (substaskst (genv, lenv, M1, ir, aux) Ms) Os(INV I) ->
    satp (substaskst (genv, (emp:env), M1, ir, aux) Ms) Os (INV I).
Proof.
  intros.
  unfold satp in *.
  unfold substaskst in *.
  intro.
  lets H100 : H aop.
  eapply INV_irrev_prop; eauto.
Qed.

Lemma bp_bpa
: forall (po pi : progunit) (ip : intunit) (A : osspec) 
         (o : taskst) (O : osabst) (d1 d2 : decllist) 
         (s : stmts) (vl : vallist) (pf : asrt) (t : type) 
         (tl : list type) (f : fid) (p' : asrt) (ab : api_code) 
         (G : env) lasrt tid,
    eqdomOS (po, pi, ip) A ->
    po f = Some (t, d1, d2, s) ->
    fst (fst A) f = Some (ab, (t, rev tl)) ->
    Some pf = BuildPreA po f (ab, (t, rev tl)) vl G lasrt tid init_lg ->
    buildp (revlcons d1 d2) vl = Some p' ->
    (forall ab0 : absop,
       (o, O, ab0)
         |= (p' ** p_local lasrt tid init_lg ** Aie true ** Ais nil ** Acs nil ** Aisr empisr) **
         A_dom_lenv (getlenvdom (revlcons d1 d2))) ->
    get_genv (get_smem o) = G -> (o, O, ab (rev vl)) |= pf /\ satp o O (CurLINV lasrt tid).
Proof.
  intros.              
  unfold BuildPreA in H2.
  rewrite H0 in H2.
  rewrite H3 in H2.
  destruct (dl_vl_match d1 (rev vl));tryfalse.
  inverts H2.
  split.
  split.
  simpl.
  auto.
  pose proof H4 (ab (rev vl)); clear H4.
  sep auto.

  unfold satp; intro.
  pose proof H4 aop; clear H4.
  unfold CurLINV.
  unfold p_local in H2.
  exists init_lg.
  sep normal in H2.
  sep auto.
Qed.


Lemma build_api_asrt :
  forall (po pi : progunit) (ip : intunit) (A : osspec)
         (d1 d2 : decllist) (vl : list val) (p' : asrt) 
         (t : type) (s : stmts) (f : fid) (G : env) lasrt tid,
    dl_vl_match d1 (rev vl) = true ->
    eqdomOS (po, pi, ip) A ->
    po f = Some (t, d1, d2, s) ->
    buildp (revlcons d1 d2) vl = Some p' ->
    exists p r ab ft,
      fst (fst A) f = Some (ab, ft) /\
      Some p = BuildPreA po f (ab, ft) vl G lasrt tid init_lg /\
      Some r = BuildRetA po f (ab, ft) vl G lasrt tid init_lg.
Proof.
  introv Hdv.
  intros.
  unfold eqdomOS in *.
  destruct A ;destruct p; fold cjy_and; mytac.  
  lets H100 : H f.
  destruct H100.
  assert (exists fdef, po f = Some fdef) as H100 by eauto.
  apply H4 in H100; destruct H100.
  lets H100 : H2 H0 H6; mytac.
  destruct x; simpl fst in *; simpl snd in *.
  unfold BuildPreA, BuildRetA. 
  rewrite H0.
  rewrite H6.
  rewrite H1.
  assert (exists x, buildq (revlcons d1 d2) = Some x) as H100.
  gen H1; clear. 
  gen vl p'.
  induction (revlcons d1 d2); intros; simpl in *.
  eauto.
  destruct (negb (in_decllist i d) && good_decllist d); tryfalse.
  destruct vl; tryfalse.
  remember (buildp d nil) as p100; destruct p100; tryfalse.
  symmetry in Heqp100.
  apply IHd in Heqp100; mytac. 
  rewrite H; eauto.
  remember (buildp d vl) as p100; destruct p100; tryfalse.
  symmetry in Heqp100.
  apply IHd in Heqp100; mytac. 
  rewrite H; eauto.
  mytac.
  rewrite H9.
  unfold cjy_and.
  rewrite Hdv in *.
  do 4 eexists; mytac; auto.
Qed.

Lemma retv_spec1 :
  forall (o : taskst) (O : osabst) (ab : osapi) 
         (abs : absop) (R : retasrt) (vl : vallist) 
         (po : progunit) (v : val) (f : fid) (G : env) lasrt t,
    Some R = BuildRetA po f ab vl G lasrt t init_lg ->
    (o, O, abs) |= R (Some v) ->
    exists M,
      freels (getaddr (snd (fst (get_smem o)))) (get_mem (get_smem o))
             M .
Proof.
  intros.
  unfolds in H.
  destruct (po f); tryfalse.
  destruct f0, p, p.
  destruct (buildq (revlcons d0 d)) eqn : eq1; tryfalse.
  inverts H.
  destruct o as [[[[]]]].
  destruct H0.
  simpl in H; substs.
  simpl.
  sep normal in H0.
  sep lift 8%nat in H0.

  sep remember (1::nil)%list in H0.
  simpl in H0; mytac.
  sep lift 3%nat in H5.
  sep remember (1::nil)%list in H5.
  simpl in H5; mytac.
  symmetry in eq1.
  lets Hx: free_intro eq1 H5 H4 H1.
  mytac.
  exists x0.
  auto.
Qed.

Lemma os_env_aop_irrev :
  forall e e0 e0' m i l O aop aop' ie is cs isr,
    (e, e0, m, i, l, O, aop)
      |= Aie ie ** Ais is ** Acs cs ** Aisr isr ->
    (e, e0', m, i, l, O, aop')
      |= Aie ie ** Ais is ** Acs cs ** Aisr isr.
Proof.
  intros.
  simpl in H; mytac.
  simpl.
  destruct l, p.
  do 6 eexists.
  splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  unfold emposabst.
  split; auto.
  do 6 eexists; splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  unfold emposabst.
  split; auto.
  do 6 eexists.
  splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  unfold emposabst.
  split; auto.
  unfolds; auto.
Qed.

Lemma retv_spec :
  forall (o : taskst) (O : osabst) (ab : osapi) 
         (abs : absop) (R : retasrt) (vl : vallist) 
         (po : progunit) (v : val) (f : fid) (G : env) lasrt t,
    Some R = BuildRetA po f ab vl G lasrt t init_lg ->
    (o, O, abs) |= R (Some v) ->
    exists M,
      freels (getaddr (snd (fst (get_smem o)))) (get_mem (get_smem o))
             M /\ InitTaskSt lasrt t (emple_tst (substaskst o M), O).
Proof.
  intros.
  unfolds in H.
  destruct (po f); tryfalse.
  destruct f0, p, p.
  destruct (buildq (revlcons d0 d)) eqn : eq1; tryfalse.
  inverts H.
  destruct o as [[[[]]]].
  destruct H0.
  simpl in H; substs.
  simpl.
  sep normal in H0.
  sep lift 8%nat in H0.

  sep remember (1::nil)%list in H0.
  simpl in H0; mytac.
  sep lift 3%nat in H5.
  sep remember (1::nil)%list in H5.
  simpl in H5; mytac.
  symmetry in eq1.
  lets Hx: free_intro eq1 H5 H4 H1.
  mytac.
  exists x0.
  split; auto.
  
  unfolds; simpl.
  split; auto.
  unfold satp; intro.
  unfold p_local in H6.
  sep normal in H6.
  sep remember (1::nil)%list in H6.
  simpl in H6; mytac.
  sep remember (1::nil)%list in H9.
  sep remember (1::nil)%list.
  unfold sat; fold sat.
  unfold_sat.
  simpl in H9.
  mytac.
  do 6 eexists.
  splits; eauto.
  apply join_emp; auto.
  simpl.
  do 8 eexists.
  splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  eexists.
  splits; eauto.
  unfolds; auto.
  unfolds; auto.

  sep lifts (2::3::4::5::nil)%list in H10.
  sep lifts (3::4::5::2::nil)%list.
  clear - H10.

  sep lift 5%nat in H10.
  sep lift 5%nat.
  remember (Aie true ** Ais nil ** Acs nil ** Aisr empisr).
  simpl in H10.
  simpl.
  mytac.
  do 6 eexists; splits; eauto.
  do 6 eexists; splits; eauto.
  apply join_comm.
  apply join_emp; auto.
  apply join_comm.
  apply join_emp; auto.
  eapply GoodLocalInvAsrt_irrel; eauto.
  eapply H9.
  unfolds; auto.
Qed.


Lemma ret_spec :
  forall (o : taskst) (O : osabst) (ab : osapi) 
         (abs : absop) (R : retasrt) (vl : vallist) 
         (po : progunit) (f : fid) (G : env) lasrt t,
    Some R = BuildRetA po f ab vl G lasrt t init_lg->
    (o, O, abs) |= R None ->
    exists M,
      freels (getaddr (snd (fst (get_smem o)))) (get_mem (get_smem o))
             M /\ InitTaskSt lasrt t (emple_tst (substaskst o M), O).
Proof.
  intros.
  unfolds in H.
  destruct (po f); tryfalse.
  destruct f0, p, p.
  destruct (buildq (revlcons d0 d)) eqn : eq1; tryfalse.
  inverts H.
  destruct o as [[[[]]]].
  destruct H0.
  simpl in H; substs.
  simpl.
  sep normal in H0.
  sep lift 8%nat in H0.

  sep remember (1::nil)%list in H0.
  simpl in H0; mytac.
  sep lift 3%nat in H5.
  sep remember (1::nil)%list in H5.
  simpl in H5; mytac.
  symmetry in eq1.
  lets Hx: free_intro eq1 H5 H4 H1.
  mytac.
  exists x0.
  split; auto.
  
  unfolds; simpl.
  split; auto.
  unfold satp; intro.
  unfold p_local in H6.
  sep normal in H6.
  sep remember (1::nil)%list in H6.
  simpl in H6; mytac.
  sep remember (1::nil)%list in H9.
  sep remember (1::nil)%list.
  unfold sat; fold sat.
  unfold_sat.
  simpl in H9.
  mytac.
  do 6 eexists.
  splits; eauto.
  apply join_emp; auto.
  simpl.
  do 8 eexists.
  splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  eexists.
  splits; eauto.
  unfolds; auto.
  unfolds; auto.

  sep lifts (2::3::4::5::nil)%list in H10.
  sep lifts (3::4::5::2::nil)%list.
  clear - H10.

  sep lift 5%nat in H10.
  sep lift 5%nat.
  remember (Aie true ** Ais nil ** Acs nil ** Aisr empisr).
  simpl in H10.
  simpl.
  mytac.
  do 6 eexists; splits; eauto.
  do 6 eexists; splits; eauto.
  apply join_comm.
  apply join_emp; auto.
  apply join_comm.
  apply join_emp; auto.
  eapply GoodLocalInvAsrt_irrel; eauto.
  eapply H9.
  unfolds; auto.
Qed.

Lemma curtid_irrel :
  forall e e0 e0' M i l O aop aop' tid,
    (e, e0, M, i, l, O, aop) |= CurTid tid ->
    (e, e0', M, i, l, O, aop') |= CurTid tid.
Proof.
  intros.
  simpl in H; mytac.
  simpl.
  do 8 eexists; splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  eexists.
  splits; eauto.
  unfolds; auto.
  unfolds; auto.
Qed.


Lemma free_curlinv_still:
  forall al' o' M O lasrt tid,
    freels al' (get_mem (get_smem o')) M ->
    InitTaskSt lasrt tid (emple_tst (substaskst o' M), O) ->
    satp o' O (CurLINV lasrt tid).
Proof.
  intros.
  destruct o' as [[[[]]]].
  simpl in *.
  unfolds in H0.
  simpl in H0.
  unfold satp in *.
  intro.
  mytac.
  pose proof H0 aop.
  clear H0.
  unfold CurLINV.
  exists init_lg.
  apply freels_join in H; destruct H.
  assert (
      (e, e0, M, i, l, O, aop)
        |= CurTid tid ** LINV lasrt tid init_lg ** OS [empisr, true, nil, nil]).
  clear - H1.
  remember (OS [empisr, true, nil, nil]).

  sep remember (1::nil)%list in H1.
  sep remember (1::nil)%list.
  simpl in H1.
  simpl; mytac.
  exists x x0 M.
  do 3 eexists.
  splits; eauto.
  apply join_emp; auto.
  do 8 eexists; splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  eexists.
  splits; eauto.
  unfolds; auto.
  unfolds; auto.
  remember (OS [empisr, true, nil, nil]).
  simpl in H6.
  simpl; mytac.
  do 6 eexists.
  splits; eauto.
  do 6 eexists; splits; eauto.
  apply join_comm; apply join_emp; auto.
  apply join_comm; apply join_emp; auto.
  eapply GoodLocalInvAsrt_irrel; eauto.
  eapply H12.
  unfolds; auto.
  sep auto.
  sep remember (1::nil)%list in H1.
  simpl in H1.
  sep remember (1::nil)%list.
  simpl.
  mytac.
  exists x0 (merge x1 x).
  do 4 eexists.
  splits; eauto.
  eapply mem_join_join_merge23_join; eauto.
  eapply join_emp; auto.
  do 8 eexists; splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  eexists.
  splits; eauto.
  unfolds; auto.
  unfolds; auto.
  remember (OS [empisr, true, nil, nil]).
  simpl in H8.
  simpl.
  mytac.
  exists x2.
  exists (merge x3 x).
  do 4 eexists; splits; eauto.
  eapply mem_join_disjoint_join_merge; auto.
  eapply mem_join_join_disjoint; eauto.
  apply join_comm; eauto.
  do 6 eexists; splits; eauto.
  apply join_comm; apply join_emp; auto.
  apply join_comm; apply join_emp; auto.
  eapply GoodLocalInvAsrt_irrel; eauto.
  eapply H14.
  unfolds; auto.
Qed.

Lemma tmspecmod_remove_emp_eq_emp :
  forall t,
    TMSpecMod.remove TMSpecMod.emp t = TMSpecMod.emp.
Proof.
  intros.
  apply TMSpecMod.extensionality; intros.
  unfold TMSpecMod.emp.
  unfold TMSpecMod.remove.
  destruct (TMSpecMod.beq_A x t); auto.
Qed.

Lemma tospecmod_remove_emp_eq_emp :
  forall t,
    TOSpecMod.remove TOSpecMod.emp t = TOSpecMod.emp.
Proof.
  intros.
  apply TOSpecMod.extensionality; intros.
  unfold TOSpecMod.emp.
  unfold TOSpecMod.remove.
  destruct (TOSpecMod.beq_A x t); auto.
Qed.


Definition absop_irrel (P:asrt) :=
  forall G E m isr aux o absop absop',
    (G, E, m, isr, aux, o, absop) |= P ->
    (G, E, m, isr, aux, o, absop') |= P.

Lemma absop_irrel_sat :
  forall P Q,
    absop_irrel P ->
    absop_irrel Q ->
    absop_irrel (P ** Q).
Proof.
  intros.
  unfold absop_irrel in *.
  intros.
  simpl in H1; mytac.
  simpl.
  do 6 eexists; splits; eauto.
Qed.

Lemma ostcbcur_absop_irrel :
  forall t,
    absop_irrel (EX tp : type, GV OSTCBCur @ Tptr tp |-r-> Vptr t).
Proof.
  unfold absop_irrel.
  intros.
  destruct H.
  exists x.
  simpl in H; mytac.
  simpl.
  do 7 eexists; splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  eexists.
  splits; eauto.
  unfolds; auto.
  unfolds; auto.
Qed.


Definition subevntls := 
  fun (env0 : CltEnvMod.map) (tls : TcbMod.map) =>
    forall t : tid, indom env0 t -> indom tls t.

Definition subisttls := 
  fun (lst : ltaskstset) (tls : TcbMod.map) =>
    forall t : tid, indom lst t -> indom tls t.

Definition subdomSO := 
  fun (S : osstate) (O : osabst) =>
    let (p, lst) := S in
    let (c, _) := p in
    let (p0, _) := c in
    let (_, pi) := p0 in
    match get O abtcblsid with
      | Some (abstcblist tls) => subevntls pi tls /\ subisttls lst tls
      | Some (absecblist _) => False
      | Some (ostm _) => False
      | Some (oscurt _) => False
      | None => False
    end.

Lemma eqdomSO_impl_subdomSO:
  forall S O,eqdomSO S O -> subdomSO S O.
Proof.
  intros.
  unfolds.
  destruct S; destruct p; destruct c.
  destruct p.
  unfolds in H.
  destruct (get O abtcblsid) eqn : eq1; tryfalse.
  destruct a; tryfalse.
  destruct H.
  split; unfolds; intros.
  unfolds in H.
  eapply H in H1; auto.
  unfolds in H0.
  eapply H0 in H1.
  auto.
Qed.

Definition side_condition' := 
fun (I : Inv) (pa : LocalInv) (schedmethod : ossched)
    (init : osstate -> osabst -> Type) (lg : list logicvar) =>
  GoodI I schedmethod pa /\
  (forall (S : osstate) (O : osabst),
     init S O -> initst S O I pa lg /\ subdomSO S O).


Definition indomSt :=
  fun (S : osstate) t =>
    let (p, lst) := S in
    let (c, _) := p in
    let (p0, _) := c in
    let (_, pi) := p0 in
    indom pi t.

Lemma absop_irrel_init_rdy :
  forall pa t vl,
    absop_irrel (init_rdy pa t vl).
Proof.
  intros.
  unfold absop_irrel; intros.
  unfold init_rdy in *.
  sep split in H.
  sep split; auto.
  eapply good_linvasrt_aop_irev; eauto.
Qed.

Lemma subdomSO_joinsig:
  forall t E envs envs' lst lst' auxs G M M' isr O,
    join (sig t E) envs' envs ->
    join (sig t auxs) lst' lst ->
    subdomSO (G, envs, M, isr, lst) O ->
    subdomSO (G, envs', M', isr, lst') O.
Proof.
  intros.
  unfold subdomSO in *.
  destruct (get O abtcblsid); tryfalse.
  destruct a; tryfalse.
  destruct H1.
  split.
  clear H2.
  unfold subevntls in *; intros.
  eapply H1.
  unfolds.
  unfolds in H2; destruct H2.
  exists x.
  eapply join_get_r; eauto.
  clear H1.
  unfold subisttls in *.
  intros.
  eapply H2.
  unfold indom in *.
  destruct H1.
  exists x.
  eapply join_get_r;eauto.
Qed.

Lemma partm_disjoint_put :
  forall (M : mem) (T : tasks) (Tm : TMSpecMod.Map) (t : TMSpecMod.A) 
         (Mn : mem),
    disjoint M Mn ->
    partM M T Tm -> partM (merge M Mn) T (TMSpecMod.put Tm t Mn).
Proof.
  intros.
  gen Mn t.
  inductions H0; intros.
  eapply partm_S.
  eapply TMSpecMod.put_get_eq; eauto.
  apply join_comm.
  apply join_merge_disj; auto.
  eapply partm_O.
  intros.
  rewrite TMSpecMod.remove_cancel_put. 
  pose proof H t0.
  apply TMSpecMod.remove_shrinks_dom; auto.
  
  assert (t0 = t \/ t0 <> t) by tauto.
  destruct H3.
  substs.
  assert (TMSpecMod.remove Tm t = TMSpecMod.remove (TMSpecMod.put Tm t Mn) t).
  rewrite TMSpecMod.remove_cancel_put; auto.
  assert (partM (merge M' Mn) Tl' (TMSpecMod.put Tm t Mn)).
  rewrite H3 in H1.
  eapply partm_S; eauto. 
  eapply TMSpecMod.put_get_eq.
  apply join_comm.
  eapply join_merge_disj.
  eapply mem_join_disjoint_disjoint; eauto.
  apply join_comm; eauto.

  assert (merge M' Mn = minus (merge M Mn) m).
  
  eapply mem_join_disjoint_merge_minus_merge_eq; eauto.
  rewrite H5 in H4.
  eapply partm_minus_partm; eauto.

  assert (disjoint M' Mn).
  eapply mem_join_disjoint_disjoint; eauto.
  apply join_comm; eauto.
  eapply IHpartM with (t0 := t0) in H4.
  assert (TMSpecMod.remove (TMSpecMod.put Tm t0 Mn) t = TMSpecMod.put (TMSpecMod.remove Tm t) t0 Mn).
  rewrite TMSpecMod.remove_ext_ext_remove; auto.
  rewrite <- H5 in H4; clear H5.
  eapply partm_S; eauto.
  rewrite TMSpecMod.put_noninterfere; eauto.
  eapply mem_join_disjoint_join_merge; auto.
  Grab Existential Variables.
  auto.
Qed.

Lemma parto_put_emp :
  forall Ol T T' To t,
    partO Ol T To ->
    partO Ol T' (TOSpecMod.put To t empenv).
Proof.
  intros.
  gen T' t.
  inductions H; intros.
  eapply parto_S.
  eapply TOSpecMod.put_get_eq.
  apply join_emp; eauto.
  eapply parto_O; intros.
  rewrite TOSpecMod.remove_cancel_put.
  pose proof H t0.
  eapply TOSpecMod.remove_shrinks_dom; auto.
  
  assert (t0 = t \/ t0 <> t) by tauto.
  destruct H2; substs.
  assert (TOSpecMod.remove Tm t = TOSpecMod.remove (TOSpecMod.put Tm t empenv) t).
  rewrite TOSpecMod.remove_cancel_put; auto.
  rewrite H2 in H1.
  assert (partO M' T' (TOSpecMod.put Tm t empenv)).
  eapply parto_S; intros.
  eapply TOSpecMod.put_get_eq.
  eapply join_emp; auto.
  eauto.
  assert (M' = minus M m).
  symmetry.
  eapply osabst_join_minus_eq; auto.
  rewrite H4 in H3.
  eapply parto_minus_parto; eauto.

  pose proof IHpartO T' t0.
  assert (TOSpecMod.put (TOSpecMod.remove Tm t) t0 empenv =
          TOSpecMod.remove (TOSpecMod.put Tm t0 empenv) t).
  rewrite TOSpecMod.remove_ext_ext_remove; auto.
  rewrite H4 in H3.
  eapply parto_S; eauto.
  rewrite TOSpecMod.put_noninterfere; auto.
  Grab Existential Variables.
  auto.
Qed.

Lemma indomSt_preserve :
  forall G G' envs envs' M M' isr isr' lst lst' t0 t E,
    indomSt (G, envs, M, isr, lst) t0 ->
    t0 <> t ->
    join (sig t E) envs' envs ->
    indomSt (G', envs', M', isr', lst') t0.
Proof.
  intros.
  unfold indomSt in *.
  unfold indom in *.
  destruct H.
  exists x.
  eapply join_sig_get_r; eauto.
Qed.

Lemma init_partmo':
  forall S O I lasrt sd init T tc,
    get O curtid = Some (oscurt tc) ->
    eqdomto T O ->
    init S O ->
    side_condition' I lasrt sd init init_lg ->
    exists Tm To Ml Ms Ol Os,
      join Ml Ms (snd (fst (fst S))) /\
      join Ol Os O /\
      partM Ml T Tm /\ partO Ol T To /\
      (
        exists Mc Oc oc,
          Tm tc = Some Mc /\ To tc = Some Oc /\
          projS S tc = Some oc /\
          satp (substaskst oc Ms) Os (INV I) /\
          satp (substaskst oc Mc) Oc (CurTid tc ** LINV lasrt tc init_lg ** OS [empisr,true,nil,nil]) /\
          get_lenv (get_smem oc) = empenv
      ) /\
      (
        forall t,
          indomSt S t ->
          t <> tc ->
          exists Mr Or or,
            Tm t = Some Mr /\ To t = Some Or /\
            projS S t = Some or /\
            satp (substaskst or Mr) Or ( LINV lasrt t init_lg ** OS [empisr,true,nil,nil]) /\
            get_lenv (get_smem or) = empenv
      ).
Proof.
  intros.
  unfolds in H1; mytac.
  apply H2 in X; clear H2; mytac.
  
  destruct S as [[[[]]]].
  simpl snd.

  gen sd init T H.
  gen tc H3.

  inductions H2; intros.
  
  unfold init_cur in H3.
  pose proof H3 absopx; clear H3.

  apply sat_split in H5; mytac.
  exists (TMSpecMod.put TMSpecMod.emp tc x0) (TOSpecMod.put TOSpecMod.emp tc x2).
  exists x0 x x2 x1.
  splits; auto.
  apply join_comm; auto.
  apply join_comm; auto.

  eapply partm_S.
  rewrite TMSpecMod.put_get_eq; eauto.
  apply join_comm; apply join_emp; auto.
  rewrite TMSpecMod.remove_cancel_put.

  eapply partm_O.
  intros; rewrite tmspecmod_remove_emp_eq_emp.
  unfolds; auto.

  eapply parto_S.
  rewrite TOSpecMod.put_get_eq; eauto.
  apply join_comm; apply join_emp; auto.
  rewrite TOSpecMod.remove_cancel_put.
  eapply parto_O.
  intros; rewrite tospecmod_remove_emp_eq_emp.
  unfolds; auto.

  do 3 eexists.
  splits.
  rewrite TMSpecMod.put_get_eq; eauto.
  rewrite TOSpecMod.put_get_eq; eauto.
  simpl.
  rewrite H2 in H; inverts H.
  rewrite get_sig_some.
  rewrite get_sig_some.
  eauto.

  simpl.
  intro.
  eapply rulesoundlib.INV_irrev_prop; eauto.

  simpl; intro.
  unfold CurTid.

  assert (
      (G, E, x0, isr, auxs, x2, aop)
        |= (EX tp : type, GV OSTCBCur @ Tptr tp |-r-> Vptr t) **
        init_rdy pa t (logic_val (Vint32 (Int.repr 1)) :: nil)).
  gen H7.
  eapply absop_irrel_sat.
  eapply ostcbcur_absop_irrel; eauto.
  
  eapply absop_irrel_init_rdy; eauto.
  rewrite H2 in H; inverts H.
  clear - H8.
  unfold init_rdy in H8.
  unfold LINV.
  sep auto.
  unfold init_rdy in H7.
  sep normal in H7; destruct H7.
  sep remember (8::nil)%list in H7.
  simpl in H7; mytac.
  simpl.
  eapply eqdomenv_nil_enil; eauto.

(*--*)
  intros.
  rewrite H2 in H; inverts H.
  clear - H8 H4 H9 H0.
  unfolds in H8.
  unfold indom in H8.
  destruct H8.
  assert (tc = t0 \/ tc <> t0) by tauto.
  destruct H1.
  tryfalse.
  rewrite get_sig_none in H; tryfalse.
  auto.

  
  assert (JMeq.JMeq (G, envs', M', isr, lst') (G, envs', M', isr, lst')).
  auto.
  assert ((logic_val (Vint32 (Int.repr 1)) :: nil)%list = init_lg).
  unfold init_lg; auto.
  lets Hx: IHinitst H10 H11; clear IHinitst.


  assert (subdomSO (G, envs', M', isr, lst') O ).
  eapply subdomSO_joinsig;eauto.
  eapply Hx in H12;eauto.
  clear Hx.
  clear H10 H11.
  rewrite H in H3;inverts H3.
  mytac.

  (*2 cases*) 
  assert ((exists Mt, x t = Some Mt) \/ x t = None).
  destruct (x t).
  left.
  eauto.
  right; auto.
  destruct H20.

 (*case1: x t = Some Mt*)
  mytac.

  (*  exists (TMSpecMod.put x t (merge x8 m0)) (to_inj x0 t). *)
  exists (TMSpecMod.put x t m0) (TOSpecMod.put x0 t empabst).
  exists (merge x1 m0) x2 x3 x4.
  splits;auto.

  eapply join_join_merge1; eauto.
  eapply partm_tl_irrel.

  eapply partm_disjoint_put; eauto.
  clear -H3 H2.
  unfolds;join auto.

  eapply parto_put_emp; eauto.
 
  (*1st sub part of goal*)
  exists x5 x6 (substaskst x7 M).
  splits;auto.
  rewrite TMSpecMod.put_noninterfere;auto.
  rewrite TOSpecMod.put_noninterfere;auto.

  clear -H16 H0 H1 H4.
  unfold projS in *.
  unfold projD in *.
  unfolddef.
  remember (get envs' tc) as X.
  destruct X.
  symmetry in HeqX.
  eapply join_get_r in HeqX;eauto.
  rewrite HeqX.
  remember (get lst' tc) as Y.
  destruct Y.
  symmetry in HeqY.
  eapply join_get_r in HeqY;eauto.
  rewrite HeqY.
  inverts H16;simpl;auto. 
  tryfalse.
  tryfalse.
  destruct x7 as [[[[]]]].
  simpl substaskst in *;auto.
  destruct x7 as [[[[]]]].
  simpl substaskst in *;auto.
  destruct x7 as [[[[]]]].
  simpl substaskst in *;auto.

  (*2nd sub part of goal*)
  intros.
  assert (t0 = t \/ t0 <> t) by tauto.
  destruct H23.
  (*case: t0 = t*)
  subst.
  (*  exists (merge x8 m0) x9 (G, E, M, isr, auxs). *)
  exists m0 empabst (G, E, M, isr, auxs).
  splits; auto.
  rewrite TMSpecMod.put_get_eq; eauto.
  rewrite TOSpecMod.put_get_eq; eauto.
  unfolds.
  clear -H0 H1.
  unfold projD.
  assert (get (sig t E) t = Some E).
  apply map_get_sig.
  eapply join_get_l in H0;eauto.
  rewrite H0.
  assert (get (sig t auxs) t = Some auxs).
  apply map_get_sig.
  eapply join_get_l in H1;eauto.
  rewrite H1.
  auto.
  simpl.
  clear -H11 H3 H5 H2 H20.
  unfold init_rdy in *.
  unfold LINV.
  unfold satp.
  intro.
  pose proof H5 aop.
  sep auto.
  clear - H5.
  pose proof H5 absopx; clear H5.
  sep remember (2::nil)%list in H.
  simpl in H; mytac.
  simpl.
  eapply eqdomenv_nil_enil; auto.

  (*case t0 <> t*)
  pose proof H14 t0; clear H14.
  assert (indomSt (G, envs', M', isr, lst') t0).
  clear - H21 H23 H0 H1.
  eapply indomSt_preserve; eauto.
  apply H24 in H14; auto.
  clear H24.
  mytac.
  exists x9 x10 (substaskst x11 M).
  splits; auto.
  rewrite TMSpecMod.put_noninterfere; auto.
  rewrite TOSpecMod.put_noninterfere; auto.

  clear - H25 H0 H1 H23.
  unfold projS in *.
  unfold projD in *.
  destruct (get envs' t0) eqn : eq1; tryfalse.
  destruct (get lst' t0) eqn : eq2; tryfalse.
  erewrite join_get_r; eauto.
  erewrite join_get_r; eauto.
  destruct x11 as [[[[]]]].
  inverts H25.
  simpl; auto.

  destruct x11 as [[[[]]]].
  simpl substaskst in *.
  auto.
  destruct x11 as [[[[]]]].
  simpl; simpl in H27; auto.


  exists (TMSpecMod.put x t m0) (TOSpecMod.put x0 t empenv).
  exists (merge x1 m0) x2 x3 x4.
  splits; auto.
  clear - H3 H2.
  eapply mem_join_join_merge13_join; eauto.
  apply join_comm; auto.
  clear - H20 H11 H2 H3.
  eapply partm_disjoint_put; eauto.
  eapply mem_join_join_disjoint; eauto.
  apply join_comm; eauto.
  eapply parto_put_emp; eauto.

  exists x5 x6 (substaskst x7 M).
  splits; auto.
  rewrite TMSpecMod.put_noninterfere; auto.
  rewrite TOSpecMod.put_noninterfere; auto.
  clear - H16 H0 H1 H4.
  unfold projS in *.
  unfold projD in *.
  destruct x7 as [[[[]]]].
  unfold get in H16; simpl in H16.
  destruct (CltEnvMod.get envs' tc) eqn : eq1; tryfalse.
  destruct (TaskLStMod.get lst' tc) eqn : eq2; tryfalse.
  inverts H16.
  erewrite join_get_r; eauto.
  erewrite join_get_r; eauto.
  simpl; auto.
  
  destruct x7 as [[[[]]]]; simpl substaskst in *; auto.
  destruct x7 as [[[[]]]]; simpl substaskst in *; auto.
  destruct x7 as [[[[]]]]; simpl; auto.

  (*2nd sub part of goal*)
  intros.
  assert (t0 = t \/ t0 <> t) by tauto.
  destruct H23.
  (*case: t0 = t*)
  subst.
  (*  exists (merge x8 m0) x9 (G, E, M, isr, auxs). *)
  exists m0 empabst (G, E, M, isr, auxs).
  splits; auto.
  rewrite TMSpecMod.put_get_eq; eauto.
  rewrite TOSpecMod.put_get_eq; eauto.
  unfolds.
  clear -H0 H1.
  unfold projD.
  assert (get (sig t E) t = Some E).
  apply map_get_sig.
  eapply join_get_l in H0;eauto.
  rewrite H0.
  assert (get (sig t auxs) t = Some auxs).
  apply map_get_sig.
  eapply join_get_l in H1;eauto.
  rewrite H1.
  auto.
  simpl.
  clear -H11 H3 H5 H2 H20.
  unfold init_rdy in *.
  unfold LINV.
  unfold satp.
  intro.
  pose proof H5 aop.
  sep auto.
  clear - H5.
  pose proof H5 absopx; clear H5.
  sep remember (2::nil)%list in H.
  simpl in H; mytac.
  simpl.
  eapply eqdomenv_nil_enil; auto.

  (*case t0 <> t*)
  pose proof H14 t0; clear H14.
  assert (indomSt (G, envs', M', isr, lst') t0).
  clear - H21 H23 H0 H1.
  eapply indomSt_preserve; eauto.
  apply H24 in H14; auto.
  clear H24.
  mytac.
  exists x8 x9 (substaskst x10 M).
  splits; auto.
  rewrite TMSpecMod.put_noninterfere; auto.
  rewrite TOSpecMod.put_noninterfere; auto.

  clear - H25 H0 H1 H23.
  unfold projS in *.
  unfold projD in *.
  destruct (get envs' t0) eqn : eq1; tryfalse.
  destruct (get lst' t0) eqn : eq2; tryfalse.
  erewrite join_get_r; eauto.
  erewrite join_get_r; eauto.
  destruct x10 as [[[[]]]].
  inverts H25.
  simpl; auto.

  destruct x10 as [[[[]]]].
  simpl substaskst in *.
  auto.
  destruct x10 as [[[[]]]].
  simpl; simpl in H27; auto.
  Grab Existential Variables.
  auto.
  auto.
Qed.


Lemma init_partmo :
  forall S O I lasrt sd init T tc,
    get O curtid = Some (oscurt tc) ->
    eqdomto T O ->
    init S O ->
    side_condition I lasrt sd init init_lg ->
    exists Tm To Ml Ms Ol Os,
      join Ml Ms (snd (fst (fst S))) /\
      join Ol Os O /\
      partM Ml T Tm /\ partO Ol T To /\
      (
        exists Mc Oc oc,
          Tm tc = Some Mc /\ To tc = Some Oc /\
          projS S tc = Some oc /\
          satp (substaskst oc Ms) Os (INV I) /\
          satp (substaskst oc Mc) Oc (CurTid tc ** LINV lasrt tc init_lg ** OS [empisr,true,nil,nil]) /\
          get_lenv (get_smem oc) = empenv
      ) /\
      (
        forall t,
          indom T t ->
          t <> tc ->
          exists Mr Or or,
            Tm t = Some Mr /\ To t = Some Or /\
            projS S t = Some or /\
            satp (substaskst or Mr) Or ( LINV lasrt t init_lg ** OS [empisr,true,nil,nil]) /\
            get_lenv (get_smem or) = empenv
      ).
Proof.
  intros.
  assert (side_condition' I lasrt sd init init_lg).
  unfold side_condition in H1; mytac.
  unfold side_condition'.
  split; auto.
  intros.
  eapply H2 in X0; mytac.
  auto.
  clear - H4.
  apply eqdomSO_impl_subdomSO; auto.

  lets Hx: init_partmo' H H0 X H2.
  mytac.
  do 6 eexists;splits;eauto.
  do 3 eexists;splits;eauto.
  intros.
  assert (indomSt S t).
  unfold side_condition in H1.
  mytac.
  eapply H16 in X; mytac.
  clear - H18 H14 H0.
  destruct S as [[[[]]]].
  unfolds.
  unfolds in H18.
  unfolds in H0; mytac.
  rewrite H in H18; mytac.
  eapply H0 in H14; mytac.
  unfolds in H1.
  eapply H1.
  unfolds; eauto.

  eapply H8 in H16.
  eauto.
  auto.
Qed.

Lemma joinm2_eq :
  forall m1 m1' Ms Mf m,
    joinm2 m1 Ms Mf m ->
    joinm2 m1' Ms Mf m ->
    m1 = m1'.
Proof.
  intros.
  unfold joinm2 in *; mytac.
  unfold joinmem in *; mytac.
  assert (x21 = x9).
  assert (x3 = x15).
  apply join_comm in H4.
  apply join_comm in H8.
  lets Hx: join_unique_r H4 H8; auto.
  substs.
  apply join_comm in H10.
  apply join_comm in H6.
  lets Hx: join_unique_r H10 H6; auto.
  substs; auto.
Qed.

Lemma alloc_curlinv_hold:
  forall lasrt o Ms Mf o2 o' o'' p tid vl dl f s ks cst Cl' cst' O,
    joinm2 o Ms Mf o2 ->
    joinm2 o' Ms Mf o'' ->
    ltstep p tid
           (curs (salloc vl dl), (kenil, kcall f s empenv ks)) cst o2 Cl' cst'
           o'' ->
    satp o O (CurLINV lasrt tid) ->
    satp o' O (CurLINV lasrt tid).
Proof.
  intros.
  inverts H1.

  inverts H4.
  inverts H3; tryfalse.
  inverts H3; tryfalse.
  inverts H4; inverts H1; inverts H6.


  assert (o = o').
  eapply joinm2_eq; eauto.
  substs; auto.

  inverts H4; inverts H6; inverts H1.
  assert (o = o').
  eapply joinm2_eq; eauto.
  substs; auto.

  inverts H1.
  assert (o = o').
  eapply joinm2_eq; eauto.
  substs; auto.  

  inverts H4; tryfalse.
  inverts H1; tryfalse.
  inverts H3.
  inverts H4.

  inverts H4; tryfalse.
  inverts H3.
  lets Hx: alloc_store_exist_mem_env H7 H8 H9.
  mytac.
  eapply joinm2_ex_join in H.
  eapply joinm2_ex_join in H0.
  unfold joinmem in *; mytac.
  lets Hx: join_unique H H0; substs.
  assert (satp (x9, x4, x11, x13, x14) O (CurLINV lasrt tid)).
  eapply local_inv_E_irev; eauto.
  clear H2.

  eapply join_satp_local_inv; eauto.
  unfolds; do 6 eexists; splits; eauto.
  instantiate (1:=x0).
  
  clear - H14 H11 H4.
  eapply mem_join_eq_trans; eauto.
  apply join_comm; apply join_emp; auto.

  inverts H3.
  lets Hx: alloc_exist_mem_env H7.
  mytac.
  eapply joinm2_ex_join in H.
  eapply joinm2_ex_join in H0.
  unfold joinmem in *; mytac.
  lets Hx: join_unique H H0; substs.
  assert (satp (x11, x6, x13, x15, x16) O (CurLINV lasrt tid)).
  eapply local_inv_E_irev; eauto.
  clear H2.

  eapply join_satp_local_inv; eauto.
  unfolds; do 6 eexists; splits; eauto.
  instantiate (1:=x0).
  clear - H9 H12 H4.
  eapply mem_join_eq_trans; eauto.
  apply join_comm; apply join_emp; auto.

  inverts H3.
  lets Hx: joinm2_eq H H0; substs.
  auto.
Qed.

Lemma partm_neq_disj:
  forall Ml Tl Tm t t' Mc Md,
    t' <> t ->
    partM Ml Tl Tm ->
    TMSpecMod.maps_to Tm t Mc ->
    TMSpecMod.maps_to Tm t' Md ->
    disjoint Mc Md.
Proof.
  intros.
  eapply partm_disjoint; eauto.
Qed.

Lemma partM_normal:
  forall o' Ms' Ml Mc e e0 m i l Ms M Tl Tm t',
    joinm2 o' Ms' (minus Ml Mc) (e, e0, m, i, l) ->
    join Ml Ms M ->
    partM Ml Tl Tm ->
    TMSpecMod.maps_to Tm t' Mc ->
    partM (minus m Ms') Tl (TMSpecMod.put Tm t' (get_mem (get_smem o'))).
Proof.
  intros.
  unfold joinm2 in H; mytac.
  unfold joinmem in *; mytac.
  simpl.

  assert (partM x3 Tl (TMSpecMod.put Tm t' x2)).
  lets Hx: partm_minus_remove H1 H2.
  instantiate (1:=Tl) in Hx.
  assert (TMSpecMod.remove (TMSpecMod.put Tm t' x2) t' = TMSpecMod.remove Tm t').
  rewrite TMSpecMod.remove_cancel_put; auto.
  rewrite <- H in Hx.
  eapply partm_S; eauto.
  rewrite TMSpecMod.put_get_eq; auto.

  assert (TMSpecMod.maps_to (TMSpecMod.put Tm t' x2) t' x2).
  unfolds.
  rewrite TMSpecMod.put_get_eq; auto.
  assert (partM (minus x3 x2) Tl (TMSpecMod.remove Tm t')).
  lets Hx: partm_minus_remove H H3.
  instantiate (1:=Tl) in Hx.
  rewrite TMSpecMod.remove_cancel_put in Hx; auto.
  assert (TMSpecMod.remove Tm t' = TMSpecMod.remove (TMSpecMod.put Tm t' x8) t').
  rewrite TMSpecMod.remove_cancel_put; auto.
  rewrite H6 in H4; clear H6.
  eapply partm_S; eauto.
  rewrite TMSpecMod.put_get_eq; eauto.
  eapply mem_join_sub_join_minus_minus; auto.
  eapply join_sub_l; eauto.
Qed.


Lemma partO_normal:
  forall (O':osabst) Os Os' x OO' O Ol Oc Tl t' To,
    join O' Os' OO' ->
    join OO' (minus Ol Oc) x->
    join Ol Os O ->
    partO Ol Tl To ->
    TOSpecMod.maps_to To t' Oc ->
    partO (minus x Os') Tl (TOSpecMod.put To t' O').
Proof.
  intros.
  assert (partO x Tl (TOSpecMod.put To t' OO')).
  lets Hx: parto_minus_remove H2 H3.
  instantiate (1:=Tl) in Hx.
  assert (TOSpecMod.remove (TOSpecMod.put To t' OO') t' = TOSpecMod.remove To t').
  rewrite TOSpecMod.remove_cancel_put; auto.
  rewrite <- H4 in Hx.
  eapply parto_S; eauto.
  rewrite TOSpecMod.put_get_eq; auto.

  assert (TOSpecMod.maps_to (TOSpecMod.put To t' OO') t' OO').
  unfolds.
  rewrite TOSpecMod.put_get_eq; auto.
  assert (partO (minus x OO') Tl (TOSpecMod.remove To t')).
  lets Hx: parto_minus_remove H4 H5.
  instantiate (1:=Tl) in Hx.
  rewrite TOSpecMod.remove_cancel_put in Hx; auto.
  assert (TOSpecMod.remove To t' = TOSpecMod.remove (TOSpecMod.put To t' O') t').
  rewrite TOSpecMod.remove_cancel_put; auto.
  rewrite H7 in H6; clear H7.
  eapply parto_S; eauto.
  rewrite TOSpecMod.put_get_eq; eauto.

  eapply osabst_join_sub_join_minus_minus; auto.
  eapply join_sub_l; eauto.
Qed.


Lemma swi_rdy_inv'''':
  forall (o : taskst) (Ol Os : osabst) (Ms Mc : mem) 
         (I : Inv) (t t' : tid) (S : osstate)
         (o' : env * EnvSpec.B * mem * isr * LocalStSpec.B) 
         (b : block) (tp : type) (Mcc : mem) (sc : ossched) 
         (OO : osabst) (li : LocalInv) x,
    good_is_S S ->
    GoodI I sc li ->
    join Ol Os OO ->
    disjoint Mc Ms ->
    (forall ab : absop, (substaskst o Ms, Os, ab) |= INV I) ->
    (forall ab : absop, (substaskst o Mc, Ol, ab) |= SWINVt I t) ->
    (forall ab : absop, (substaskst o Mc, Ol, ab) |= AHprio sc t' ** Atrue) ->
    (forall ab : absop, (substaskst o Mc, Ol, ab) |= SWPRE_NDEAD sc x t) ->
    projS S t = Some o ->
    projS S t' = Some o' ->
    EnvMod.get (get_genv (get_smem o)) OSTCBCur = Some (b, Tptr tp) ->
    store (Tptr tp) Mc (b, 0%Z) (Vptr t') = Some Mcc ->
    exists Mc' Ms' Ol' Os' OO',
      disjoint Mc' Ms' /\
      merge Mc' Ms' = merge Mcc Ms /\
      join Ol' Os' OO' /\
      OO' = set OO curtid (oscurt t') /\
      (forall ab : absop, (substaskst o' Ms', Os', ab) |= INV I) /\
      (forall ab : absop,
         (substaskst o' Mc', Ol', ab) |= RDYINV I t').
Proof.
  intros.
  assert (disjoint Ol Os).
  eapply my_join_disj; eauto.
  lets Hx: swi_rdy_inv'''1 H6 H H0 H11 H2.
  lets Hx1: Hx H3 H4 H5 H7 H8; clear Hx.
  lets Hx2: Hx1 H9 H10; clear Hx1.
  assert (OO = merge Ol Os).
  eapply join_merge; auto.
  substs.
  clear - Hx2; mytac.
  do 5 eexists.
  splits; eauto.
  eapply join_merge_disj; auto.
Qed.

Local Open Scope Z_scope.
(*Definition GoodI1 :=
  fun (I : Inv) (sd : ossched) (pa : LocalInv) =>
    (forall (o : taskst) (O0 O' : osabst) (ab : absop) (OO : osabst),
        (o, O0, ab) |= starinv_noisr I 0%nat (S INUM) -> join O0 O' OO -> O' = empabst) /\
    (forall (o : taskst) (O : osabst) (ab : absop) (tid : addrval),
        (o, O, ab) |= SWINVt I tid ->
        exists b tp,
          get (get_genv (get_smem o)) OSTCBCur = Some (b, Tptr tp) /\
          load (Tptr tp) (get_mem (get_smem o)) (b, 0) = Some (Vptr tid) /\
          get O curtid = Some (oscurt tid)) /\
    (forall (o : taskst) (O : osabst) (ab : absop) (tid : tid) 
            (b : block) (tp : type) (M' : mem) (ct : addrval),
        (o, O, ab) |= SWINVt I ct ->
        (o, O, ab) |= AHprio sd tid ** Atrue ->
        get (get_genv (get_smem o)) OSTCBCur = Some (b, Tptr tp) ->
        store (Tptr tp) (get_mem (get_smem o)) (b, 0) (Vptr tid) = Some M' ->
        exists tls,
          get O abtcblsid = Some (abstcblist tls) /\
          (indom tls ct /\ (substaskst o M', set O curtid (oscurt tid), ab) |= SWINVt I tid \/
                           ~ indom tls ct /\
           (forall (Mx : mem) (Ox : osabst) (MM : mem) (OO : osabst),
               satp (substaskst o Mx) Ox (EX lg : list logicvar, pa ct lg) ->
               join M' Mx MM ->
               join O Ox OO -> (substaskst o MM, set OO curtid (oscurt tid), ab) |= SWINVt I tid))) /\
    GoodSched sd.
 *)

Lemma swi_rdy_inv_dead :
  forall (o : taskst) (Ol Os : osabst) (Ms Mc : mem) 
         (I : Inv) (t t' : tid) (S : osstate)
         (o' : env * EnvSpec.B * mem * isr * LocalStSpec.B) 
         (b : block) (tp : type) (Mcc : mem) (sc : ossched) 
         (OO : osabst) (li : LocalInv) (x : var) ol OOO Olc o1 O1 M2 O2 MMM,
    good_is_S S ->
    GoodI I sc li ->
    join OOO Os OO ->
    disjoint Mc Ms ->
    disjoint Ms MMM ->
    joinmem ol Mc (substaskst o MMM) ->
    join Olc Ol OOO ->
    join O1 O2 Olc ->
    joinmem o1 M2 ol ->
    (forall ab : absop, (substaskst o Ms, Os, ab) |= INV I) ->
    (forall ab : absop, (substaskst o Mc, Ol, ab) |= SWINVt I t) ->
    (forall ab : absop, (substaskst o Mc, Ol, ab) |= AHprio sc t' ** Atrue) ->
    (forall ab : absop, (substaskst o Mc, Ol, ab) |= SWPRE_DEAD sc x t) ->
    satp o1 O1 (EX lg' : list logicvar, LINV li t lg') ->
    projS S t = Some o ->
    projS S t' = Some o' ->
    EnvMod.get (get_genv (get_smem o)) OSTCBCur = Some (b, Tptr tp) ->
    store (Tptr tp) Mc (b, 0%Z) (Vptr t') = Some Mcc ->
    exists Mc' Ms' Ol' Os' OO' Olx',
      disjoint Mc' Ms' /\
      merge Mc' Ms' = merge (merge Mcc (getmem o1)) Ms /\
      join Olx' Os' OO' /\
      join Ol' O2 Olx' /\ 
      OO' = set OO curtid (oscurt t') /\
      (forall ab : absop, (substaskst o' Ms', Os', ab) |= INV I) /\
      (forall ab : absop, (substaskst o' Mc', Ol', ab) |= RDYINV I t').
Proof.
  intros.
  destruct o as [[[[]]]].
  destruct o' as [[[[]]]].
  destruct o1 as [[[[]]]].
  destruct ol as [[[[]]]].
  simpl substaskst in *.
  unfold joinmem in *; simpljoin1.
  simpl in H14.
  unfold getmem; simpl get_mem.

  unfold GoodI in H0; mytac.
  clear H0.
  rename H4 into get_curtid.
  pose proof H9 absopx.
  pose proof H10 absopx.
  lets Hx: H7 H0 H4 H15 H16. clear H7.
  mytac.
  destruct H19; mytac.
  (*2 cases by H19*)

  (*case 1 is false*)
  simpl substaskst in H21.
  pose proof H11 absopx.
  unfold SWPRE_DEAD in H22.
  destruct H22.
  destruct H23.
  simpl in H23; mytac.
  assert (get Ol abtcblsid = Some (abstcblist x1)).
  clear - H26.
  eapply join_get_l; eauto.
  rewrite H7 in H23; inverts H23.
  clear - H19 H32.
  false; apply H32.

  (*case 2*)
  simpl substaskst in *.
  assert (satp (x6, x7, x2, x10, x11) O1 (EX lg : list logicvar, li t lg)).
  unfold satp; intro.
  pose proof H12 aop.
  destruct H22; unfold LINV in H22.
  sep split in H22.
  eexists; eauto.
  
  assert (join Mcc x2 (merge Mcc x2)).
  clear - H18 H20 H16.
  assert (disjoint Mc x2).
  apply disjoint_sym.
  eapply join_join_disjoint; eauto.
  lets Hx: disj_store_disj H H16.
  eapply join_merge_disj; auto.
  
  assert (join Ol O1 (merge Ol O1)).
  clear - H5 H6.
  assert (disjoint Ol O1).
  apply disjoint_sym.
  eapply osabst_join_join_disjoint_auto; eauto.
  eapply join_merge_disj; auto.

  lets Hx: H21 H22 H23 H24.
  assert (disjoint (set (merge Ol O1) curtid (oscurt t')) Os).
  pose proof H9 absopx.
  lets Hx1: get_curtid H25; simpljoin1.
  clear - H28 H1 H5 H6.
  remember (oscurt t) as b.
  remember (oscurt t') as b'.
  remember curtid as a.
  clear Heqb Heqb' Heqa.
  clears.
  eapply osabst_disjoint_set_merge; eauto.
   
  assert (disjoint (merge Mcc x2) Ms).
  clear - H20 H18 H16 H3.
  assert (exists x9', join x8 Mcc x9' /\ store (Tptr tp) x9 (b, 0) (Vptr t') = Some x9').
  apply join_comm in H20.
  lets Hx: lmachLib.store_mono H20 H16; destruct Hx.
  lets Hx: join_store H20 H16 H.
  apply join_comm in Hx.
  eauto.
  simpljoin1.
  apply disjoint_sym in H3.
  lets Hx: disj_store_disj H3 H0.
  clear - H18 H Hx.
  eapply mem_join_join_disjoint_merge; eauto.
  lets Hx1: swi_rdy_inv' H H25 H26 H13 H14.
  simpl substaskst.
  intros.
  pose proof H8 ab.
  eauto.
  simpl substaskst.
  intro.
  lets Hx1: swinv_aop_irev Hx.
  pose proof Hx1 ab.
  auto.

  simpl substaskst in Hx1.
  simpljoin1.
  exists x1 x3 x4 x5.
  eexists.
  exists (minus (merge (merge x4 x5) O2) x5).
  splits; eauto.
  pose proof H9 absopx.
  lets Hx1: get_curtid H33; simpljoin1.
  clear - H30 H29 H5 H6 H36 H1.
  remember curtid as a.
  remember (oscurt t) as b.
  remember (oscurt t') as b'.
  clear Heqa Heqb Heqb'.
  eapply osabst_join_minus_merge_merge_set; eauto.

  pose proof H9 absopx.
  lets Hx1: get_curtid H33; simpljoin1.
  clear - H30 H29 H5 H6 H36 H1.
  remember curtid as a.
  remember (oscurt t) as b.
  remember (oscurt t') as b'.
  clear Heqa Heqb Heqb'.
  
  lets Hx: osabst_join_minus_merge_merge H1 H5 H6 H29 H30.
  lets Hx1: Hx H36.
  auto.  
Qed.

Lemma linv_aop_irev':
  forall o O aop aop' li t lg,
    (o,O,aop) |= LINV li t lg ->
    (o,O,aop') |= LINV li t lg.
Proof.
  intros.
  destruct o as [[[[]]]].
  simpl in H; simpljoin.
  simpl.
  do 6 eexists; splits; eauto.
  eapply GoodLocalInvAsrt_aop_irev; eauto.
  unfolds in H4.
  lets Hx:H4 t lg.
  mytac;auto.
Qed.

Lemma aux_atrue:
  forall ol Olc t lasrt,
    satp ol Olc (EX lg' : list logicvar, LINV lasrt t lg' ** Atrue) ->
    exists o1 M2 O1 O2,
      joinmem o1 M2 ol /\ join O1 O2 Olc /\
      satp o1 O1 (EX lg' : list logicvar, LINV lasrt t lg').
Proof.
  intros.
  assert (forall aop, exists o1 M2 O1 O2,
            joinmem o1 M2 ol /\ join O1 O2 Olc /\
            ( o1, O1, aop) |= (EX lg' : list logicvar, LINV lasrt t lg')).
  intros.
  lets Hx:H aop.
  destruct Hx.
  remember (LINV lasrt t x) as X.
  simpl in H0.
  mytac.
  do 4 eexists;splits;eauto.
  instantiate (2:=substaskst ol x0).
  instantiate (1:=x1).
  clear -H1;destruct ol as [[[[]]]].
  simpl.
  simpl in H1.
  unfolds.
  do 6 eexists;splits;eauto.
  eexists;eauto.
  lets Hx:H0 (spec_done None).
  mytac.
  do 4 eexists;splits;eauto.
  unfolds;intros.
  destruct H3.
  eexists.
  eapply linv_aop_irev';eauto.
Qed.


Lemma mem_join_merge_minus_join_store'f :
  forall (Ml Mc Mc' Mcc m m' M2 Mc'0 Ms' Ms: mem) o1 ol o (v : val) 
         (l : addr) (tp : type),
    store tp Mc' l v = Some Mcc ->
    store tp m l v = Some m' ->
    joinmem o1 M2 ol ->
    joinmem ol Mc' (substaskst o Mc) ->
    disjoint Mc'0 Ms' ->
    merge Mc'0 Ms' = merge (merge Mcc (getmem o1)) Ms ->
    Maps.sub Mc Ml ->
    join Ml Ms m ->
    join (merge (merge (minus Ml Mc) M2) Mc'0) Ms' m'.
Proof.
  intros.
  destruct o1 as [[[[]]]].
  destruct o as [[[[]]]].
  unfold getmem in H4; unfold joinmem in *;  simpl in *.
  mytac.
  rename x2 into Mc.
  clears.
  rename x7 into x0.

  assert (join Mc (minus Ml Mc) Ml).
  eapply join_sub_minus; auto.

  assert (exists Mc1, join x1 Mcc Mc1 /\ store tp Mc l v = Some Mc1).
  apply join_comm in H8.
  lets Hx: lmachLib.store_mono H8 H; destruct Hx.
  lets Hx: join_store H8 H H2.
  apply join_comm in Hx.
  eauto.
  destruct H2.
  destruct H2.
  rename x into Mc1.
  assert (exists Ml1, join Mc1 (minus Ml Mc) Ml1 /\ store tp Ml l v = Some Ml1).
  lets Hx: lmachLib.store_mono H1 H7; destruct Hx.
  lets Hx: join_store H1 H7 H9.
  eauto.
  do 2 destruct H9.
  rename x into Ml1.

  assert (exists m1, join Ml1 Ms m1 /\ store tp m l v = Some m1).
  lets Hx: lmachLib.store_mono H6 H11; destruct Hx.
  lets Hx: join_store H6 H11 H12.
  eauto.
  do 2 destruct H12.
  rename x into m1.

  rewrite H0 in H13; inverts H13.

  clear H H8 H6 H5 H1 H7 H11 H0.
  remember (minus Ml Mc) as M3.
  clear HeqM3.
  eapply mem_4join_merge135_disjoint_join_merge24; eauto.
Qed.



Lemma disj'f :
  forall (Ml Mc Mc' Mcc m M2 Mc'0 Ms' Ms: mem) o1 ol o (v : val) 
         (l : addr) (tp : type),
    store tp Mc' l v = Some Mcc ->
    joinmem o1 M2 ol ->
    joinmem ol Mc' (substaskst o Mc) ->
    disjoint Mc'0 Ms' ->
    merge Mc'0 Ms' = merge (merge Mcc (getmem o1)) Ms ->
    Maps.sub Mc Ml ->
    join Ml Ms m ->
    disjoint (merge (minus Ml Mc) M2) Mc'0.
Proof.
  intros.
  destruct o as [[[[]]]].
  destruct o1 as [[[[]]]].
  unfold getmem in *.
  unfold joinmem in *; simpljoin1.
  simpl in *.
  inverts H6.

  assert (join x2 (minus Ml x2) Ml).
  eapply join_sub_minus; auto.
  clears.
  rename x7 into x0.
  rename x2 into Mc.
  
  assert (exists Mc1, join x1 Mcc Mc1 /\ store tp Mc l v = Some Mc1).
  apply join_comm in H7.
  lets Hx: lmachLib.store_mono H7 H; destruct Hx.
  lets Hx: join_store H7 H H1.
  apply join_comm in Hx.
  eauto.
  do 2 destruct H1.
  rename x into Mc1.
  assert (exists Ml1, join Mc1 (minus Ml Mc) Ml1 /\ store tp Ml l v = Some Ml1).
  lets Hx: lmachLib.store_mono H0 H6; destruct Hx.
  lets Hx: join_store H0 H6 H8.
  eauto.
  do 2 destruct H8.
  rename x into Ml1.

  assert (exists m1, join Ml1 Ms m1 /\ store tp m l v = Some m1).
  lets Hx: lmachLib.store_mono H5 H10; destruct Hx.
  lets Hx: join_store H5 H10 H11.
  eauto.
  do 2 destruct H11.
  rename x into m1.

  clear H H7 H5 H4 H0 H6 H10 H12.
  remember (minus Ml Mc) as M3.
  clear HeqM3.
  eapply mem_4join_merge135_disjoint_disjoint_merge24; eauto.
Qed.



Lemma partm_minus_subf :
  forall (M Mc Mm : mem) (T : tasks) (Tm : TMSpecMod.Map)
         (t : TMSpecMod.A),
    Maps.sub Mm Mc ->
    TMSpecMod.maps_to Tm t Mc ->
    partM M T Tm ->
    partM (merge (minus M Mc) Mm) T (TMSpecMod.put Tm t Mm).
Proof.
  intros.
  inductions H1.
  unfolds in H0; tryfalse.

  assert (t = t0 \/ t <> t0) by tauto.
  destruct H4.
  substs.
  unfolds in H0.
  rewrite H1 in H0; inverts H0.
  assert (TMSpecMod.remove Tm t0 = TMSpecMod.remove (TMSpecMod.put Tm t0 Mm) t0).
  rewrite TMSpecMod.remove_cancel_put; auto.
  rewrite H0 in H3.
  eapply partm_S; eauto.
  rewrite TMSpecMod.put_get_eq; eauto.
  assert (M' = minus M Mc).
  apply join_comm in H2; apply join_eq_minus; auto.
  rewrite <- H4.
  assert (disjoint Mm M').
  apply join_comm in H2.
  apply disjoint_sym.
  eapply mem_join_sub_disjoint; eauto.
  apply join_comm.
  apply disjoint_sym in H5.
  eapply join_merge_disj; auto.

  assert (TMSpecMod.maps_to (TMSpecMod.remove Tm t0) t Mc).
  eapply TMSpecMod.removeX_presv_Y; auto.
  apply IHpartM in H5.
  assert (TMSpecMod.put (TMSpecMod.remove Tm t0) t Mm =
          TMSpecMod.remove (TMSpecMod.put Tm t Mm) t0).
  rewrite TMSpecMod.remove_ext_ext_remove; auto.
  rewrite H6 in H5.
  eapply partm_S; eauto.
  rewrite TMSpecMod.put_noninterfere; eauto.
  assert (Maps.sub Mc M').
  assert (TMSpecMod.maps_to (TMSpecMod.remove Tm t0) t Mc).
  eapply TMSpecMod.removeX_presv_Y; auto.
  lets Hx: part_sub H3 H7; auto.
  clear - H H7 H2.
  eapply mem_sub_sub_join_join_merge_minus; eauto.
Qed.


(*sent to lzh*)
Lemma join_complexf:
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
Proof.
  eapply join_complexf.
Qed.

(*sent to lzh*)
Lemma disj_complex'f
: forall (O' Ox x0 Oc'0 Os'' OO' Os' OO'' Olc Occ : osabst)
         (a : absdataid) (b b' : absdata) Olx' O1 O2,
    join Olx' Os'' OO'' ->
    join Oc'0 O2 Olx' ->
    OO'' = set (merge O' Os') a b' ->
    join O1 O2 Olc ->
    join Olc Occ O' ->
    join O' Os' OO' ->
    join OO' Ox x0 -> get Occ a = Some b -> disjoint (merge Oc'0 O2) Ox.
Proof.
  eapply disj_complex'f.
Qed.


Lemma disj_complex''f :
  forall (Mc'0 Ms' Ms : mem) (tp : type) (Mc' : mem) 
         (b : block) (t' : addrval) (Mcc Ml : mem) 
         (Tl : tasks) (Tm : TMMap) (Mn : TMSpecMod.B) 
         (m ml : mem) (Mc : TMSpecMod.B) (t : TMSpecMod.A) Mx,
    merge Mc'0 Ms' = merge (merge Mcc Mx) Ms ->
    store (Tptr tp) Mc' (b, 0%Z) (Vptr t') = Some Mcc ->
    Maps.sub Mc' Ml ->
    partM Ml Tl Tm ->
    TMSpecMod.maps_to Tm t' Mn ->
    TMSpecMod.maps_to Tm t Mc ->
    Maps.sub Mx ml ->
    t <> t' -> join Ml Ms m -> join ml Mc' Mc -> disjoint Mc'0 Mn.
Proof.
  intros.

  assert (exists mx, join Mx mx ml).
  exists (minus ml Mx).
  eapply join_sub_minus; auto.
  destruct H9.
  rename x into x0.

  assert (exists Mc1, join ml Mcc Mc1 /\ store (Tptr tp) Mc (b, 0%Z) (Vptr t') = Some Mc1).
  apply join_comm in H8.
  lets Hx: lmachLib.store_mono H8 H0; destruct Hx.
  lets Hx: join_store H8 H0 H10.
  apply join_comm in Hx.
  eauto.
  do 2 destruct H10.
  rename x into Mc1.

  lets Hx: partm_neq_disj H6 H2 H3 H4.
  lets Hx1: partm_merge_sub H2 H4 H3 H6.
  assert (disjoint (merge Mc Mn) Ms).
  apply disjoint_sym.
  apply join_comm in H7.
  eapply mem_join_sub_disjoint; eauto.
  apply disjoint_sym in H12.
  lets Hx2: store_disj_merge H12 H11.

  assert (disjoint Mc1 Mn).
  apply disjoint_sym in Hx.
  lets Hx3: disj_store_disj Hx H11; auto.

  assert (disjoint Mn Ms).
  lets Hx4: part_sub H2 H3.
  apply disjoint_sym.
  apply join_comm in H7.
  eapply mem_join_sub_disjoint; eauto.

  assert (disjoint Mc1 Ms).
  assert (disjoint Mc Ms).
  lets Hx3: part_sub H2 H4.
  apply disjoint_sym.
  apply join_comm in H7.
  eapply mem_join_sub_disjoint; eauto.
  eapply disj_store_disj; eauto.
  apply disjoint_sym in Hx2.

  clear - H9 H10 H13 H15 H14 Hx2 H.
  lets Hx: join_join_merge_disjoint H9 H10 H13 H14 H15.
  eapply Hx; eauto.
Qed.


Lemma disj_complex'''f :
  forall Olc Occ : osabst,
  forall (Os'' OO'' O' Os' OO' Ol Oc x0 Oc'0 : osabst)
         (On : TOSpecMod.B) (t t' : TOSpecMod.A) (a : absdataid)
         (b b' : absdata) (To : TOMap) (Tl : tasks) Olx' O1 O2,
    get Occ a = Some b ->
    join Oc'0 O2 Olx' ->
    join Olx' Os'' OO'' ->
    OO'' = set (merge O' Os') a b' ->
    join Olc Occ O' ->
    join O1 O2 Olc ->
    join O' Os' OO' ->
    join OO' (minus Ol Oc) x0 ->
    partO Ol Tl To ->
    TOSpecMod.maps_to To t Oc ->
    TOSpecMod.maps_to To t' On -> t <> t' -> disjoint Oc'0 On.
Proof.
  intros.
  assert (exists x0', join OO'' (minus Ol Oc) x0').
  assert (get O' a = Some b). Check join_get_r.
  eapply join_get_r; eauto.
  assert (get (merge O' Os') a = Some b).
  rewrite map_merge_sem.
  rewrite H11.
  destruct (get Os' a); auto.
  auto.
  assert (OO' = merge O' Os').
  eapply map_join_merge'; auto.
  substs.
  exists (set x0 a b').
  eapply join_set_set; eauto.
  destruct H11.
  
  eapply osabst_join_join_sub_join_disjoint;eauto.
  remember (minus Ol Oc) as Ox.
  assert (disjoint On Oc).
  eapply parto_disjoint.
  Focus 2. eapply H9.
  Focus 2. eapply H8.
  eapply H7.
  assert (forall a b:TOSpecMod.A, a <> b -> b <> a).
  intros;intro;false.
  apply H12;apply H10.
  assert (Maps.sub On Ol).
  eapply parto_sub;eauto.
  rewrite HeqOx.
  apply minus_sub.
  Focus 2. apply H13.
  Focus 2. apply H12. auto.
Qed.
