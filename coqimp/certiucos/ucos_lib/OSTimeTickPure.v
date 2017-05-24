Require Import ucos_include.
Require Import OSQPostPure.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevanceFacts.

(*--------Time Int---------*)

Import TcbMod.

(*part1*)
Import DeprecatedTactic.
Ltac hoare_ex_intro' :=
  repeat
    match goal with
      | |- {|_ , _, _, _, _ , _|}|-_ {{EX _, _}}_ {{_}} => apply ex_intro_rule; intros
    end.
Ltac hoare_split_pure_all'' :=
  hoare normal pre; hoare_ex_intro'; hoare_split_pure_all'.

Ltac pure_intro' :=
  hoare_split_pure_all''; isptr_intro; array_leneq_intro; hoare_split_pure_all;
  mytac; struct_type_vallist_match_elim; simpl_field_eq.


Ltac xunfold' H:=
  let M:= fresh in  
  match type of H with
    | match ?X with
        | _ => _
      end = Some _ => remember X as M;destruct M;tryfalse;auto
    | _ => idtac
  end.

Ltac xunfold'' H:=
  let M:= fresh in  
  match type of H with
    | Some _  = match ?X with
        | _ => _
      end => remember X as M;destruct M;tryfalse;auto
    | _ => idtac
  end.



Ltac xunfold'''' H:=
  match type of H with
    |  (Some ?p) = _
       => destruct p as [[[]]]
    | _ => idtac
  end.

Ltac xunfold''' H:=
  let M:= fresh in  
  match type of H with
    | match ?X with
        | _ => _
      end = Some _ => remember X as M eqn:Htick;destruct M;tryfalse;auto;xunfold'''' Htick;inverts H
    | _ => idtac
  end.

Ltac xunfold H :=
  repeat (xunfold' H);
  subst;
  simpl in *;unfold add_option_first in H;(xunfold''' H).

Ltac xxunfold':=
  match goal with
    | |- match ?X with
        | _ => _
      end = Some _ => remember X as M;destruct M;tryfalse;auto
    | _ => idtac
  end.

Ltac xxunfold'' :=
  match goal with
    | |- Some _  = match ?X with
        | _ => _
      end => remember X as M;destruct M;tryfalse;auto
    | _ => idtac
  end.



Ltac xxunfold''' :=
  match goal with
    | |- match ?X with
           | _ => _
         end = Some _ => remember X as M eqn:Htick;destruct M;tryfalse;auto;xunfold'''' Htick
    | _ => idtac
  end.

Ltac xxunfold :=
  repeat (xxunfold');
  subst;
  simpl in *;unfold add_option_first;(xxunfold''').

Ltac inverts_all' :=
    match goal with
      | H: Some _ = Some _ |- _ => inverts H
    end.
Ltac inverts_all:= repeat inverts_all'.


Ltac mytac_1' :=
  match goal with
    | H:exists _, _ |- _ => destruct H; mytac_1'
    | H:_ /\ _ |- _ => destruct H; mytac_1'
    |  _ => try (progress subst; mytac_1')
  end.

Ltac mytac' := repeat progress mytac_1'.

Fixpoint get_ectr (eid:val) (head:val) (ectrl:list EventCtr) :=
  match eid,head,ectrl with
    | (Vptr e),(Vptr e'),(osevent, etbl)::vll =>
      match beq_addrval e e' with
        | true => Some (osevent,etbl)
        | false => match V_OSEventListPtr osevent with
                     | Some vn => get_ectr eid vn vll
                     | _ => None
                   end
      end
    | _,_,_ => None
  end.


Lemma tcbdllseg_compose'
: forall (s : RstateOP) (P : asrt) (h hp t1 tn1 t2 tn2 : val)
         (l1 l2 : list vallist),
    s |= tcbdllseg h hp t1 tn1 l1 ** tcbdllseg tn1 t1 t2 tn2 l2 ** P ->
    s |= tcbdllseg h hp t2 tn2 (l1 ++ l2) **  [| (l1=nil/\tn1=h)\/( exists vl,l1<>nil /\ List.last l1 nil = vl /\ nth_val 0 vl = Some tn1)|] ** P.
Proof.
  intros.
  sep split.
  eapply tcbdllseg_compose;eauto.
  destruct l1.
  left.
  split;auto.
  unfold tcbdllseg in H.
  unfold dllseg in H.
  sep split in H.
  auto.
  right.

  Lemma list_split_last: forall l v, exists (x:vallist) (l':list vallist), (v::l) = (l'++(x::nil)).
  Proof.
    intros.
    exists (last (v::l) nil) (removelast (v::l)).
    apply app_removelast_last.
    intro;tryfalse.
  Qed.
   
  Lemma last_get: forall  (l':list vallist) (x:vallist), last (l'++(x::nil)) nil = x.
  Proof.
    induction l'.
    intros.
    simpl;auto.
    intros.
    simpl.
    rewrite IHl'.
    destruct l'.
    simpl;auto.
    simpl;auto.
  Qed.

  lets Hx:list_split_last l1 v.
  mytac.
  exists x.
  splits;auto.
  (* intro;tryfalse. *)
  rewrite H0.
  apply last_get.
  rewrite H0 in H.
  remember (tcbdllseg tn1 t1 t2 tn2 l2 ** P) as X.
  clear HeqX.
  clear H0.
  gen x0 s h hp X x t1 tn1 H.
  clear.
  induction x0.
  intros.
  simpl ((nil ++ x :: nil)) in H.
  unfold tcbdllseg in *.
  unfold dllseg in H.
  sep normal in H.
  sep destruct H.
  sep split in H.
  subst.
  unfolds in H0.
  auto.
  intros.
  simpl ((a :: x0) ++ x :: nil) in H.
  unfold tcbdllseg in H.
  unfold1 dllseg in H.
  sep split in H.
  sep normal in H.
  sep destruct H.
  sep split in H.
  eapply IHx0 with (s:=s).
  unfold tcbdllseg.
  sep cancel 2%nat 1%nat.
  exact H.
Qed.
Require Import os_ucos_h.
Open Scope code_scope.
Open Scope Z_scope.
Lemma neq_null_false_elim:forall x v s P, s |= LV x @ OS_TCB ∗ |-> v ** P -> s |= Aisfalse (x ′ !=ₑ NULL) -> v = Vnull.
Proof.
  intros.
  destruct_s s.
  simpl in H; mytac.
  simpl in H0.
  destruct H0.
  rewrite H9 in H.
  destruct H.
  simpl uop_type in H.
  destruct (load OS_TCB ∗ m (x13, 0%Z)) eqn : eq1; tryfalse.
  destruct (val_eq v0 Vnull) eqn : eq2; tryfalse.
  unfolds in H10; mytac.
  replace (Int.unsigned Int.zero) with 0 in H3; auto.
  unfold load in eq1.
  unfold loadm in eq1.
  destruct (loadbytes m (x13, 0) (typelen OS_TCB ∗)) eqn : eq3; tryfalse.
  pose proof symbolic_lemmas.ptomvallist_loadbytes (x13, 0) (encode_val OS_TCB ∗ v) x0 true H3.
  simpl typelen in eq3.
  assert (length (encode_val OS_TCB ∗ v) = 4%nat).
  destruct v; simpl; auto.
  destruct a0; simpl; auto.
  rewrite H4 in H2.
  pose proof lmachLib.loadbytes_mono x0 x1 m.
  pose proof H6 (x13, 0) 4%nat (encode_val OS_TCB ∗ v) H1 H2; clear H6.
  rewrite eq3 in H7.
  rewrite H2 in H7.
  inverts H7.
  inverts eq1.
  clear H4.
  clear H1 H5 H3 H2 eq3.
  destruct v; auto.
  simpl in eq2; tryfalse.
  simpl in eq2; tryfalse.
  simpl in eq2; destruct a0; simpl in eq2.
  unfold decode_val in eq2.
  simpl in eq2.
  destruct (peq b b && Int.eq_dec i2 i2 && true &&
              (peq b b && Int.eq_dec i2 i2 && true &&
               (peq b b && Int.eq_dec i2 i2 && true &&
                    (peq b b && Int.eq_dec i2 i2 && true && true)))).
  simpl in eq2.
  inverts eq2.
  simpl in H.
  inverts H.
  simpl in H0.
  unfold Int.notbool in H0.
  rewrite Int.eq_true in H0.
  rewrite Int.eq_false in H0; tryfalse.
  simpl in eq2; tryfalse.
Qed.
  

Lemma neq_null_true_elim:forall x v s P, s |= LV x @ OS_TCB ∗ |-> v ** P -> s |= Aistrue (x ′ !=ₑ NULL) -> v <> Vnull.
Proof.
  intros.
  intro.
  substs.
  destruct_s s.
  simpl in H; mytac.
  clear H5.
  replace (Int.unsigned Int.zero) with 0 in H10; auto.
  simpl in H0.
  rewrite H9 in H0.
  destruct H0.
  destruct H.
  simpl uop_type in H.
  destruct (load OS_TCB ∗ m (x13, 0)) eqn : eq1; tryfalse.
  destruct (val_eq v Vnull) eqn : eq2; tryfalse.
  unfolds in H10; mytac.
  simpl encode_val in H3.
  unfold load in eq1; unfold loadm in eq1.
  destruct(loadbytes m (x13, 0) (typelen OS_TCB ∗)) eqn : eq3; tryfalse.
  simpl typelen in eq3.
  pose proof symbolic_lemmas.ptomvallist_loadbytes (x13, 0) (MNull :: MNull :: MNull :: MNull :: nil) x0 true H3.
  simpl length in H2.
  pose proof lmachLib.loadbytes_mono x0 x1 m (x13, 0) 4  (MNull :: MNull :: MNull :: MNull :: nil) H1 H2.
  rewrite eq3 in H4.
  rewrite H2 in H4.
  inverts H4.
  inverts eq1.
  simpl in eq2.
  inverts eq2.
  simpl in H.
  inverts H.
  simpl in H0.
  unfold Int.notbool in H0.
  rewrite Int.eq_true in H0; tryfalse.
Qed.

Open Scope int_scope.
Lemma ne_0_minus_1_in_range:
  forall i2 : int32,
    Int.unsigned i2 <= 65535 ->
    Int.eq i2  ($ 0)  = false ->
    Int.unsigned (i2-ᵢ$ 1) <= Int16.max_unsigned.
Proof.
  intros.
  pose (Int.eq_spec i2 ($0)) as Hp.
  rewrite H0 in Hp.
  unfold Int16.max_unsigned.
  unfold Int16.modulus.
  simpl.
  clear - H Hp.
  int auto.
  int auto.
  assert ( 1 <= Int.unsigned i2 \/ Int.unsigned i2 = 0).
  assert ( 0 <= Int.unsigned i2 ) by (apply Int.unsigned_range).
  omega.
  destruct H1.
  omega.
  rewrite <- H1 in Hp.
  rewrite Int.repr_unsigned in Hp.
  tryfalse.
Qed.

Lemma z_to_nat_shr3:
  forall x,0 <= Int.unsigned x -> Int.unsigned x < 64 -> (0 <= Z.to_nat (Int.unsigned (Int.shru x ($ 3))) < 8)%nat.
Proof.
  intros.
  eapply int8_range_nat.
  splits.
  remember (Int.shru x ($3)) as xx.
  clear -x.
  int auto.
  eapply shru_3_lt_8; auto.
Qed.


Lemma TCBList_P_RL_TCBblk_P :
  forall l l' a x x1 x2,
    TCBList_P x (l++a::l') x1 x2 -> RL_TCBblk_P a.
Proof.
  inductions l; intros.
  simpl in H; mytac.
  unfold TCBNode_P in H2; destruct x5; destruct p; mytac; auto.

  rewrite <- app_comm_cons in H.
  simpl in H; mytac.
  eapply IHl; eauto.
Qed.

Import TcbMod.
Lemma join_join_minus : forall m1 m2 m3 ma mb,
  join m1 m2 m3 -> join ma mb m1 -> join mb m2 (minus m3 ma).
Proof.
  intros.
  unfolds.
  intros.
  rewrite minus_sem.
  pose proof H a.
  pose proof H0 a.
  destruct(get m1 a);
  destruct(get m2 a);
  destruct(get m3 a);
  destruct(get ma a);
  destruct(get mb a);
  tryfalse;
  substs; auto.
Qed.


Lemma tcbnode_rl_prop':
  forall v'13 v'14 v'12 v v'4 v'7 v'3 v'5 v'6 v'15 v'16 v'21 v'8 x7 x6 i6 i5 i4 i3 i2 i1 i0,
    TcbMod.join v'13 v'14 v'12 ->
    TCBList_P v v'4 v'7 v'13 ->
    TCBList_P v'3 (v'5 :: v'6) v'7 v'14 ->
    v'4 ++ v'5 :: v'6 =
    v'15 ++
         (v'21
            :: v'8
            :: x7
            :: x6
            :: Vint32 i6
            :: Vint32 i5
            :: Vint32 i4
            :: Vint32 i3
            :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil)
         :: v'16 ->
    RL_TCBblk_P (v'21
                   :: v'8
                   :: x7
                   :: x6
                   :: Vint32 i6
                   :: Vint32 i5
                   :: Vint32 i4
                   :: Vint32 i3
                   :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil).
Proof.
 (*length v'4 = length v'15*)
  intros.
  gen v'13 v'14 v'12 v v'4 v'7 v'3 v'5 v'6 v'16.
  inductions v'15; intros.

  destruct v'4.
  inversion H2; clear H2; substs.
  unfolds in H1; mytac.
  unfolds in H4; mytac.
  destruct x2; destruct p; mytac.
  auto.

  rewrite app_nil_l in H2.
  rewrite <- app_comm_cons in H2.
  inversion H2; clear H2.
  substs.
  unfolds in H0; mytac.
  unfolds in H4; mytac.
  destruct x2; destruct p; mytac.
  auto.

  destruct v'4.
  rewrite app_nil_l in H2.
  rewrite <- app_comm_cons in H2.
  inversion H2; clear H2.
  substs.
  simpl in H1; mytac.


  eapply TCBList_P_RL_TCBblk_P; eauto.

  do 2 rewrite <- app_comm_cons in H2.
  inverts H2.
  simpl in H0; mytac.
  pose proof IHv'15 v'21 v'8 x7 x6 i6 i5 i4 i3 i2 i1 i0 x1 v'14 (TcbMod.minus v'12 (TcbMod.sig x x2)); clear IHv'15.
  assert(TcbMod.join x1 v'14 (TcbMod.minus v'12 (TcbMod.sig x x2))).
  clear - H H3.
(*candidate for MapLib*)
  unfolds in H3.

  eapply join_join_minus; eauto.
  pose proof H0 H7; clear H0.
  pose proof H8 x0 v'4 v'7 H6; clear H8.
  pose proof H0 v'3 v'5 v'6 H1 v'16; clear H0.
  apply H8; auto.
Qed.

(*a candidate lemma for MapLib*)
Lemma join_join_disj :
  forall m1 m2 m3 m4 m5,
    join m1 m2 m3 -> join m4 m5 m2 -> disj m1 m4.
Proof.
  intros.
  intro.
  pose proof H a.
  pose proof H0 a.

  destruct (get m1 a);
    destruct (get m2 a);
    destruct (get m3 a);
    destruct (get m4 a);
    destruct (get m5 a);
    tryfalse; auto.
Qed.


Lemma tcbnode_rl_prop:
  forall v'13 v'14 v'12 v'2 v'4 v'7 v'3 v'5 v'6 v'15 v'16 v'21 v'8 x7 x6 i6 i5 i4 i3 i2 i1 i0,
    TcbMod.join v'13 v'14 v'12 ->
    TCBList_P (Vptr v'2) v'4 v'7 v'13 ->
    TCBList_P v'3 (v'5 :: v'6) v'7 v'14 ->
    v'4 ++ v'5 :: v'6 =
    v'15 ++
         (v'21
            :: v'8
            :: x7
            :: x6
            :: Vint32 i6
            :: Vint32 i5
            :: Vint32 i4
            :: Vint32 i3
            :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil)
         :: v'16 ->
    RL_TCBblk_P (v'21
                   :: v'8
                   :: x7
                   :: x6
                   :: Vint32 i6
                   :: Vint32 i5
                   :: Vint32 i4
                   :: Vint32 i3
                   :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil).
Proof.
  intros.
  eapply tcbnode_rl_prop'; eauto.
Qed.

Lemma TCBList_P_split :
  forall {l1 l2 rtbl tcbls v},
    TCBList_P v (l1++l2) rtbl tcbls ->
    exists tcbls' tcbls'',
      (TCBList_P v l1 rtbl tcbls' /\ TcbMod.join tcbls' tcbls'' tcbls).
Proof.
  inductions l1; intros.
  simpl.
  do 2 eexists; split; eauto.
  apply TcbMod.join_emp; eauto.
  rewrite <- app_comm_cons in H.
  simpl in H; mytac.
  apply IHl1 in H3; mytac.
  exists (TcbMod.merge (TcbMod.sig x x2) x3) x4.
  split.
  simpl.
  do 4 eexists; repeat split; eauto.
  unfolds.
  clear - H1 H3.
  unfolds in H1.
  apply TcbMod.join_merge_disj.
  eapply join_join_disj; eauto.
  clear - H1 H3.
  intro.
  unfolds in H1.
  pose proof H1 a; clear H1.
  pose proof H3 a; clear H3.
  rewrite merge_sem.
  unfold Maps.sig in *.
  simpl in H.
  destruct (get (sig x x2) a);
  destruct (get x1 a);
  destruct (get tcbls a);
  destruct (get x3 a);
  destruct (get x4 a); tryfalse; substs;auto.
Qed.

Lemma TCBList_P_combine :
  forall {l1 l2 v1 v2 rtbl tcbls1 tcbls2 tcbls},
    TcbMod.join tcbls1 tcbls2 tcbls ->
    TCBList_P v1 l1 rtbl tcbls1 ->
    TCBList_P v2 l2 rtbl tcbls2 ->
    l1 <> nil ->
    V_OSTCBNext (last l1 nil) = Some v2 ->
    TCBList_P v1 (l1++l2) rtbl tcbls.
Proof.
  intros.
  destruct l1; tryfalse.

  clear H2.
  gen v.
  inductions l1; intros.
  simpl in H3.
  simpl.
  simpl in H0; mytac.
  do 4 eexists; repeat split; eauto.

  clear - H H4.
  unfold TcbJoin in *.
  intro.
  pose proof H a; clear H.
  pose proof H4 a; clear H4.
  rewrite TcbMod.emp_sem in H.
  unfold Maps.sig in *.
  simpl in *.
  destruct (get tcbls1 a);
  destruct (get tcbls2 a);
  destruct (get tcbls a);
  destruct (get (sig x x2) a);
  tryfalse; substs; auto.
  
  rewrite <- app_comm_cons.
  unfold TCBList_P; fold TCBList_P.
  remember (a::l1) as lx.
  unfold TCBList_P in H0; fold TCBList_P in H0.
  substs.
  mytac. 
  do 4 eexists; repeat split; eauto.
  instantiate (1:=TcbMod.merge x1 tcbls2).
  clear - H H4.
  unfold TcbJoin in *.
  intro.
  pose proof H a; clear H.
  pose proof H4 a; clear H4.
  rewrite TcbMod.merge_sem.
  unfold Maps.sig in *.
  simpl in *.
  destruct (get x1 a);
  destruct (get tcbls a);
  destruct (get tcbls1 a);
  destruct (get tcbls2 a);
  destruct (get (sig x x2) a);
  tryfalse; substs; auto.

  eapply IHl1; eauto.

  clear - H H4.
  apply TcbMod.join_merge_disj.
  unfold TcbJoin in H4.
  apply TcbMod.join_comm in H.
  apply TcbMod.join_comm in H4.
  apply TcbMod.disj_sym.
  eapply join_join_disj; eauto.
Qed.


Lemma tcblist_p_recombine:
  forall v'14 v'12 v'2 v'7 v'13 l1 l2 v'3 l1' l2',
    l1 = nil /\ v'3 = Vptr v'2 \/
       (exists vl, l1 <> nil /\ last l1 nil = vl /\ nth_val 0 vl = Some v'3) ->
    TcbMod.join v'13 v'14 v'12 ->
    TCBList_P (Vptr v'2) l1 v'7 v'13 ->
    TCBList_P v'3 l2 v'7 v'14 ->
    l1 ++ l2 =
    l1' ++ l2' ->
    exists rtbl' tcbls', TCBList_P (Vptr v'2) l1' rtbl' tcbls'.
Proof.
  intros. 
  destruct H.
  mytac; substs.
  rewrite app_nil_l in H3.
  substs.
  pose proof TCBList_P_split H2; mytac.
  do 2 eexists; eauto.
  mytac.
  pose proof TCBList_P_combine H0 H1 H2 H.
  unfold V_OSTCBNext in H4.
  apply H4 in H5; clear H4.
  unfold vallist in H5.
  rewrite H3 in H5.
  pose proof TCBList_P_split H5.
  mytac.
  eauto.
Qed.


Lemma rl_tcbblk_tcby_range:
  forall  v'21 v'8 x7 x6 i6 i5 i4 i3 i2 i1 i0,
    RL_TCBblk_P
      (v'21
         :: v'8
         :: x7
         :: x6
         :: Vint32 i6
         :: Vint32 i5
         :: Vint32 i4
         :: Vint32 i3
         :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil) ->
    Int.unsigned i2 < 8.
Proof.
  intros.
  funfold H.
  clear H10.
  mauto.
Qed.


Lemma tcbdllseg_compose_tail:
  forall s v'22 v'21 v'8 x7 x6 i6 i5 i4 i3 i2 i1 i0 v'2 v'18,
    struct_type_vallist_match OS_TCB_flag  (v'21
                                         :: v'8
                                         :: x7
                                         :: x6
                                         :: Vint32 i6
                                         :: Vint32 i5
                                         :: Vint32 i4
                                         :: Vint32 i3
                                         :: Vint32 i2
                                         :: Vint32 i1 :: Vint32 i0 :: nil) ->
    s|=
     Astruct (v'22, Int.zero) OS_TCB_flag
     (v'21
        :: v'8
        :: x7
        :: x6
        :: Vint32 i6
        :: Vint32 i5
        :: Vint32 i4
        :: Vint32 i3
        :: Vint32 i2
        :: Vint32 i1 :: Vint32 i0 :: nil) **
     tcbdllseg (Vptr v'2) Vnull v'8 (Vptr (v'22, Int.zero)) v'18 -> 
    s |= tcbdllseg (Vptr v'2) Vnull (Vptr (v'22, Int.zero)) v'21
      (v'18 ++
            (v'21
               :: v'8
               :: x7
               :: x6
               :: Vint32 i6
               :: Vint32 i5
               :: Vint32 i4
               :: Vint32 i3
               :: Vint32 i2 :: Vint32 i1 :: Vint32 i0  :: nil)
            :: nil).
Proof.
  intros.
  assert ( s
   |= tcbdllseg (Vptr v'2) Vnull (Vptr (v'22, Int.zero)) v'21
        (v'18 ++
         (v'21
          :: v'8
             :: x7
                :: x6
                   :: Vint32 i6
                      :: Vint32 i5
                         :: Vint32 i4
                            :: Vint32 i3
                               :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil)
         :: nil) ** Aemp).
  
  eapply tcbdllseg_compose.
  sep cancel tcbdllseg.
  unfold tcbdllseg.
  unfold dllseg.
  unfold node.
  sep normal.
  sep eexists.
  sep split;auto.
  sep auto.
  (* intro;tryfalse. *)
  sep auto.
Qed.


Lemma nth_val_length : forall l i v, nth_val i l = Some v -> (i < length l)%nat.
Proof.
  inductions l; intros.
  simpl in H; tryfalse.

  simpl in H.
  destruct i.
  simpl; omega.

  apply IHl in H.
  simpl; omega.
Qed.

Lemma array_type_vallist_match_rule_type_val_match :
  forall l n t x,
    array_type_vallist_match t l -> nth_val n l = Some x ->
    rule_type_val_match t x = true.
Proof.
  inductions l; intros.
  simpl in H0; tryfalse.

  destruct n.
  simpl in H0.
  inverts H0.
  unfolds in H; mytac; auto.

  simpl in H; mytac.
  simpl in H0.
  eapply IHl; eauto.
Qed.


Lemma set_rdy_tbl_grp_hold:
  forall v'7 i x1 m i0 i2 p l i3 i4 i5  v0 v4 x,
    RL_Tbl_Grp_P v'7 (Vint32 i) ->
    array_type_vallist_match Int8u v'7 ->
    length v'7 = Pos.to_nat 8 ->
    (Int.unsigned i <= 255)%Z ->
    RL_TCBblk_P
      (x1
         :: v0
         :: x
         :: m
         :: Vint32 i0
         :: v4
         :: Vint32 p
         :: Vint32 i2
         :: Vint32 i3 :: Vint32 i4 :: Vint32 i5 :: nil) ->
    set_rdy_tbl (Vint32 i4) (Vint32 i3) v'7 = Some l ->
    array_type_vallist_match Int8u l /\
    length l = Pos.to_nat 8 /\
    (Int.unsigned (Int.or i i5) <= 255)%Z /\
    RL_Tbl_Grp_P l (Vint32 (Int.or i i5)).
Proof.
  intros.
  simpl in H4.
  destruct (nth_val (Z.to_nat (Int.unsigned i3)) v'7) eqn : eq1; tryfalse.
  destruct (or v (Vint32 i4)) eqn : eq2; tryfalse.  
  unfolds in H3; simpl in H3; mytac.
  unfolds in H7; simpl in H7.
  unfolds in H3; simpl in H3.
  inverts H7.
  inverts H4.
  apply array_type_vallist_match_hold; auto.
  eapply nth_val_length; eauto.
  unfolds in eq2.
  destruct v; tryfalse.
  inverts eq2.
  eapply array_type_vallist_match_rule_type_val_match in eq1; eauto.
  simpl in eq1.
  destruct (Int.unsigned i1 <=? Byte.max_unsigned) eqn : eq2; tryfalse.
  simpl.
  unfold Byte.max_unsigned in *.
  simpl in eq2.
  apply Zle_bool_imp_le in eq2.
  assert (Int.unsigned ($ 1<<ᵢ(x0&ᵢ$ 7)) <=128).
  clear -H18.
  mauto.
  lets Hx : int_unsigned_or_prop eq2 H4.
  simpl.
  apply Zle_imp_le_bool in Hx.
  rewrite Hx.
  auto.
  inverts H4.
  rewrite update_nth_val_len_eq; auto.
  unfolds in H8; simpl in H8.
  inverts H8.
  assert (Int.unsigned ($ 1<<ᵢ(Int.shru x0 ($ 3))) <=128).
  clear -H18.
  mauto.
  eapply int_unsigned_or_prop; eauto.
  unfolds in H8; simpl in H8; inverts H8.
  unfolds.
  unfolds in H.
  usimpl H3.
  usimpl H6.
  usimpl H16.
  usimpl H5.
  usimpl H9.
  usimpl H7.
  assert ( 0<=(Z.to_nat (Int.unsigned (Int.shru x0 ($ 3))))  <8)%nat.
  clear - H18.
  mauto.
  assert (Vint32 i = Vint32 i) by auto.
  unfolds in eq2.
  destruct v; tryfalse.
  lets Habb : H H3  H5; eauto.
  intros.
  inverts H8.
  inverts eq2.
  inverts H4.
  assert (n = Z.to_nat (Int.unsigned (Int.shru x0 ($ 3))) \/
          n <> Z.to_nat (Int.unsigned (Int.shru x0 ($ 3))))%nat .
  tauto.
  destruct H4.
  rewrite <- H4 in H7.
  apply nth_upd_eq in H7.
  inverts H7.
  destruct Habb.
  assert (Int.unsigned (Int.shru x0 ($ 3)) <8).
  clear - H18.
  mauto.
  remember (Int.shru x0 ($ 3)) as M.
  split.
  split.
  intros.
  rewrite Int.and_commut in H11.
  rewrite Int.and_or_distrib in H11.
  apply int_or_zero_split in H11.
  destruct H11.
  subst n.
  clear - H12 H9.
  false.
  gen H12.
  mauto.
  intros.
  apply int_or_zero_split in H11.
  destruct H11.
  assert ($ 1<<ᵢ(x0&ᵢ$ 7) <> $ 0).
  eapply math_prop_neq_zero2; try omega.
  tryfalse.
  split.
  intros.
  eapply int_eq_false_ltu.
  apply Int.eq_false.
  introv Hf.
  apply int_or_zero_split in Hf.
  destruct Hf.
  assert ($ 1<<ᵢ(x0&ᵢ$ 7) <> $ 0).
  eapply math_prop_neq_zero2; try omega.
  tryfalse.
  introv Hf.
  rewrite Int.and_commut.
  rewrite Int.and_or_distrib.

  subst n.
  assert ((($ 1<<ᵢ$ Z.of_nat (Z.to_nat (Int.unsigned M)))&ᵢ($ 1<<ᵢM)) =
          $ 1<<ᵢ$ Z.of_nat (Z.to_nat (Int.unsigned M))).
  clear - H9.
  mauto.
  rewrite H4.
  rewrite Int.or_commut.
  rewrite Int.or_and_absorb.
  auto.
  apply nth_upd_neq in H7; auto.
  assert (Vint32 i = Vint32 i) by auto.
  lets Hsa : H H6 H7 H8.
  destruct Hsa.
  assert (Int.unsigned (Int.shru x0 ($ 3)) <8).
  clear - H18.
  mauto.
  remember (Int.shru x0 ($ 3)) as M.
  split.
  split.
  intros.
  eapply H9.
  rewrite Int.and_commut in H13.
  rewrite Int.and_or_distrib in H13.
  apply int_or_zero_split in H13.
  mytac.
  rewrite Int.and_commut.
  auto.
  intros.
  apply H9 in H13.
  rewrite Int.and_commut.
  rewrite Int.and_or_distrib .
  rewrite Int.and_commut in H13.
  rewrite H13.
  assert (($ 1<<ᵢ$ Z.of_nat n)&ᵢ($ 1<<ᵢM) =$ 0).
  clear - H12 H4 H6.
  gen H4.
  mauto.
  rewrite H14.
  auto.
  split.
  intros.
  eapply int_eq_false_ltu.
  apply Int.eq_false.
  assert (v= $0 \/ v<>$0) by tauto . 
  destruct H14; auto.
  subst v.
  assert ($ 0 = $ 0) by auto.
  apply H9 in H14.
  false.
  rewrite Int.and_commut in H13.
  rewrite Int.and_or_distrib in H13.
  rewrite Int.and_commut in H14.
  rewrite H14 in H13.
  assert (($ 1<<ᵢ$ Z.of_nat n)&ᵢ($ 1<<ᵢM) = $ 0).
  clear - H12 H6 H4.
  gen H4.
  mauto.
  rewrite H16 in H13.
  rewrite Int.or_zero in H13.
  clear -H13 H6.
  gen H13.
  mauto.
  intros.
  apply H11 in H13.
  rewrite Int.and_commut .
  rewrite Int.and_or_distrib .
  rewrite Int.and_commut in H13.
  rewrite H13.
  rewrite Int.or_and_absorb.
  auto.
Qed.

Lemma timetick_update_prop:
  forall v'12 v'7 i v'15 v'16 v'17 x y y' head rtbl tcbls,
    TCBList_P head v'12 rtbl tcbls ->
    array_type_vallist_match Int8u v'7 ->
    length v'7 = ∘OS_RDY_TBL_SIZE ->
    (Int.unsigned i <= 255)%Z ->
    RL_Tbl_Grp_P v'7 (Vint32 i) ->
    tcbls_rtbl_timetci_update v'12 v'7 (Vint32 i) x y =
    Some (v'15, v'16, Vint32 v'17, y') ->
    array_type_vallist_match Int8u v'16 /\
    length v'16 = ∘OS_RDY_TBL_SIZE /\
    (Int.unsigned v'17 <= 255)%Z /\
    RL_Tbl_Grp_P v'16 (Vint32 v'17).
Proof.
  induction v'12;intros.
  unfold tcbls_rtbl_timetci_update in *.
  inverts H4;auto.
  simpl in H4.
  xunfold H4.
  mytac'.
  eapply IHv'12;eauto.
  mytac'.
  unfold TCBNode_P in *.
  destruct x3.
  destruct p.
  mytac'.
  unfold V_OSTCBMsg in *.
  simpl in H;inverts H.
  unfold V_OSTCBNext in *.
  simpl in H4;inverts H4.
  unfold V_OSTCBPrio in *;simpl in H6;inverts H6.
  clear H9.
  eapply IHv'12 with (i:=(Int.or i i5)) (v'7:=l);eauto;eapply set_rdy_tbl_grp_hold;eauto.
  mytac'.
  unfold TCBNode_P in *.
  destruct x3.
  destruct p.
  mytac'.
  unfolds in H;simpl in H;inverts H.
  unfolds in H4;simpl in H4;inverts H4.
  unfolds in H6;simpl in H6;inverts H6.
  clear H9.
  eapply IHv'12 with (i:=(Int.or i i5)) (v'7:=l);eauto;eapply set_rdy_tbl_grp_hold;eauto.
  mytac'.
  eapply IHv'12;eauto.
Qed.
  
Lemma tick_rdy_ectr_get_ectr_eq:
  forall els vl head l eid, tick_rdy_ectr vl head els = Some l -> (exists et etbl,get_ectr (Vptr eid) head els = Some (et, etbl)) -> (exists et etbl,get_ectr (Vptr eid) head l = Some (et, etbl)).
Proof.
  induction els.
  intros.
  unfolds in H.
  remember ( nth_val 2 vl) as Y;destruct Y;tryfalse.
  destruct v;tryfalse.
  inverts H;auto.
  simpl in H.
  destruct head;tryfalse;auto.
  inverts H;auto.
  inverts H;auto.
  intros.
  unfolds in H.
  mytac.
  remember ( nth_val 2 vl) as Y;destruct Y;tryfalse.
  destruct v;tryfalse;inverts H;auto.
  do 2 eexists;eauto.

  xunfold H2.
  
  remember (beq_addrval eid a1) as X;destruct X;tryfalse.
  
  symmetry in HeqH2.
  xunfold HeqH2;inverts_all;
  simpl;
  rewrite <- HeqX;
  do 2 eexists;eauto.

  symmetry in HeqH2;
    xunfold HeqH2;inverts_all;
    simpl;rewrite <- HeqX;
    do 2 eexists;eauto.

  inverts H2.
  remember (beq_addrval eid a1) as X;destruct X;tryfalse.
  symmetry in HeqH2;
    xunfold HeqH2;inverts_all;
    simpl;rewrite <- HeqX;
    do 2 eexists;eauto.
  simpl.
  
  rewrite <- HeqX.
  rewrite <- HeqH2 in *.
  symmetry in HeqH3.
  eapply IHels;eauto.
  unfolds.
  instantiate (1:= vl).
  rewrite <- HeqY.
  auto.
Qed.


Lemma tcbls_rtbl_timetci_update_get_ectr_eq:
  forall tls els els' tls' rtbl rtbl' rgrp rgrp' head eid,
      tcbls_rtbl_timetci_update tls rtbl (Vint32 rgrp) head els =
             Some (tls', rtbl', Vint32 rgrp', els') ->
      (exists et etbl,get_ectr (Vptr eid) head els = Some (et,etbl)) ->
      exists et etbl,get_ectr (Vptr eid) head els' = Some (et,etbl).
Proof.
  induction tls;intros.
  simpl in H.
  inverts H;auto.
  simpl in H.
  xunfold H;eapply IHtls;eauto.
  symmetry in HeqH22.
  eapply tick_rdy_ectr_get_ectr_eq;eauto.
Qed.


Lemma TCBList_P_in_list_get_some_q :
  forall l v rtbl tcbls i0 i1 i3 i4 i6 i7 i8 i9 i10 a,
    TCBList_P v l rtbl tcbls ->
    In (i0::i1::Vptr a::i3::Vint32 i4::V$OS_STAT_Q::Vint32 i6::i7::i8::i9::i10::nil) l ->
    0 <= Int.unsigned i6 < 64 ->
    array_type_vallist_match Int8u rtbl ->
    length rtbl = ∘OS_RDY_TBL_SIZE ->
    exists tid p n m, TcbMod.get tcbls tid = Some(p, wait(os_stat_q a) n, m).
Proof.
  inductions l; intros.
  simpl in H0; tryfalse.

  simpl in H0.
  destruct H0.
  substs.
  simpl in H; mytac.
  unfold TCBNode_P in H5; destruct x2; destruct p; mytac.
  unfolds in H9; mytac.
  unfolds in H11; mytac.
  unfolds in H14.
  unfold WaitTCBblk in H14.
  assert (0 <= Int.unsigned i6 < 64) by auto.
  pose proof prio_rtbl_dec i6 rtbl H17 H2 H3.
  destruct H18.
  unfolds in H9.
  pose proof H9 i6; clear H9.
  unfold RdyTCBblk in H19.
  unfold V_OSTCBPrio in H19.
  simpl in H19.
  assert (Some (Vint32 i6) = Some (Vint32 i6) /\ prio_in_tbl i6 rtbl) by auto.
  apply H19 in H9.
  destruct H9.
  unfolds in H9; simpl in H9; tryfalse.

  
  exists x.
  pose proof H4 x.
  rewrite TcbMod.get_sig_some in H19.
  destruct (get x1 x); tryfalse.
  destruct (get tcbls x); tryfalse.
  substs.
  unfold V_OSTCBPrio in H14.
  unfold V_OSTCBDly in H14.
  unfold V_OSTCBStat in H14.
  unfold V_OSTCBEventPtr in H14.
  simpl in H14.
  assert (exists m0, (p, t, m) = (i6, wait (os_stat_q a0) i4, m0)).
  apply H14; auto.
  destruct H19; inverts H19.
  eauto.

  simpl in H; mytac.
  pose proof IHl x0 rtbl x1; clear IHl.
  apply H in H0; auto; clear H.
  mytac.
  exists x3.
  pose proof H6 x3.
  rewrite H in H0.
  destruct (get (Maps.sig x x2) x3); tryfalse.
  destruct (get tcbls x3); tryfalse.
  substs.
  eauto.
Qed.

Lemma TCBList_P_in_list_get_some_mbox :
  forall l v rtbl tcbls i0 i1 i3 i4 i6 i7 i8 i9 i10 a,
    TCBList_P v l rtbl tcbls ->
    In (i0::i1::Vptr a::i3::Vint32 i4::V$OS_STAT_MBOX::Vint32 i6::i7::i8::i9::i10::nil) l ->
    0 <= Int.unsigned i6 < 64 ->
    array_type_vallist_match Int8u rtbl ->
    length rtbl = ∘OS_RDY_TBL_SIZE ->
    exists tid p n m, TcbMod.get tcbls tid = Some(p, wait(os_stat_mbox a) n, m).
Proof.
  inductions l; intros.
  simpl in H0; tryfalse.

  simpl in H0.
  destruct H0.
  substs.
  simpl in H; mytac.
  unfold TCBNode_P in H5; destruct x2; destruct p; mytac.
  unfolds in H9; mytac.
  unfolds in H11; mytac.
  unfolds in H15.
  unfold WaitTCBblk in H15.
  assert (0 <= Int.unsigned i6 < 64) by auto.
  pose proof prio_rtbl_dec i6 rtbl H17 H2 H3.
  destruct H18.
  unfolds in H9.
  pose proof H9 i6; clear H9.
  unfold RdyTCBblk in H19.
  unfold V_OSTCBPrio in H19.
  simpl in H19.
  assert (Some (Vint32 i6) = Some (Vint32 i6) /\ prio_in_tbl i6 rtbl) by auto.
  apply H19 in H9.
  destruct H9.
  unfolds in H9; simpl in H9; tryfalse.
  
  exists x.
  pose proof H4 x.
  rewrite TcbMod.get_sig_some in H19.
  destruct (get x1 x); tryfalse.
  destruct (get tcbls x); tryfalse.
  substs.
  unfold V_OSTCBPrio in H14.
  unfold V_OSTCBDly in H14.
  unfold V_OSTCBStat in H14.
  unfold V_OSTCBEventPtr in H14.
  simpl in H14.
  assert (exists m0, (p, t, m) = (i6, wait (os_stat_mbox a0) i4, m0)).
  apply H15; auto.
  destruct H19; inverts H19.
  eauto.

  simpl in H; mytac.
  pose proof IHl x0 rtbl x1; clear IHl.
  apply H in H0; auto; clear H.
  mytac.
  exists x3.
  pose proof H6 x3.
  rewrite H in H0.
  destruct (get (Maps.sig x x2) x3); tryfalse.
  destruct (get tcbls x3); tryfalse.
  substs.
  eauto.
Qed.

Lemma TCBList_P_in_list_get_some_sem :
  forall l v rtbl tcbls i0 i1 i3 i4 i6 i7 i8 i9 i10 a,
    TCBList_P v l rtbl tcbls ->
    In (i0::i1::Vptr a::i3::Vint32 i4::V$OS_STAT_SEM::Vint32 i6::i7::i8::i9::i10::nil) l ->
    0 <= Int.unsigned i6 < 64 ->
    array_type_vallist_match Int8u rtbl ->
    length rtbl = ∘OS_RDY_TBL_SIZE ->
    exists tid p n m, TcbMod.get tcbls tid = Some(p, wait(os_stat_sem a) n, m).
Proof.
  inductions l; intros.
  simpl in H0; tryfalse.

  simpl in H0.
  destruct H0.
  substs.
  simpl in H; mytac.
  unfold TCBNode_P in H5; destruct x2; destruct p; mytac.
  unfolds in H9; mytac.
  unfolds in H11; mytac.
  unfolds in H13.
  unfold WaitTCBblk in H13.
  assert (0 <= Int.unsigned i6 < 64) by auto.
  pose proof prio_rtbl_dec i6 rtbl H17 H2 H3.
  destruct H18.
  unfolds in H9.
  pose proof H9 i6; clear H9.
  unfold RdyTCBblk in H19.
  unfold V_OSTCBPrio in H19.
  simpl in H19.
  assert (Some (Vint32 i6) = Some (Vint32 i6) /\ prio_in_tbl i6 rtbl) by auto.
  apply H19 in H9.
  destruct H9.
  unfolds in H9; simpl in H9; tryfalse.
  
  exists x.
  pose proof H4 x.
  rewrite TcbMod.get_sig_some in H19.
  destruct (get x1 x); tryfalse.
  destruct (get tcbls x); tryfalse.
  substs.
  unfold V_OSTCBPrio in H14.
  unfold V_OSTCBDly in H14.
  unfold V_OSTCBStat in H14.
  unfold V_OSTCBEventPtr in H14.
  simpl in H14.
  assert (exists m0, (p, t, m) = (i6, wait (os_stat_sem a0) i4, m0)).
  apply H13; auto.
  destruct H19; inverts H19.
  eauto.

  simpl in H; mytac.
  pose proof IHl x0 rtbl x1; clear IHl.
  apply H in H0; auto; clear H.
  mytac.
  exists x3.
  pose proof H6 x3.
  rewrite H in H0.
  destruct (get (Maps.sig x x2) x3); tryfalse.
  destruct (get tcbls x3); tryfalse.
  substs.
  eauto.
Qed.

Lemma TCBList_P_in_list_get_some_mutex :
  forall l v rtbl tcbls i0 i1 i3 i4 i6 i7 i8 i9 i10 a,
    TCBList_P v l rtbl tcbls ->
    In (i0::i1::Vptr a::i3::Vint32 i4::V$OS_STAT_MUTEX::Vint32 i6::i7::i8::i9::i10::nil) l ->
    0 <= Int.unsigned i6 < 64 ->
    array_type_vallist_match Int8u rtbl ->
    length rtbl = ∘OS_RDY_TBL_SIZE ->
    exists tid p n m, TcbMod.get tcbls tid = Some(p, wait(os_stat_mutexsem a) n, m).
Proof.
  inductions l; intros.
  simpl in H0; tryfalse.

  simpl in H0.
  destruct H0.
  substs.
  simpl in H; mytac.
  unfold TCBNode_P in H5; destruct x2; destruct p; mytac.
  unfolds in H9; mytac.
  unfolds in H11; mytac.
  unfolds in H16. 
  unfold WaitTCBblk in H16.
  assert (0 <= Int.unsigned i6 < 64) by auto.
  pose proof prio_rtbl_dec i6 rtbl H17 H2 H3.
  destruct H18.
  unfolds in H9.
  pose proof H9 i6; clear H9.
  unfold RdyTCBblk in H19.
  unfold V_OSTCBPrio in H19.
  simpl in H19.
  assert (Some (Vint32 i6) = Some (Vint32 i6) /\ prio_in_tbl i6 rtbl) by auto.
  apply H19 in H9.
  destruct H9.
  unfolds in H9; simpl in H9; tryfalse.
  
  exists x.
  pose proof H4 x.
  rewrite TcbMod.get_sig_some in H19.
  destruct (get x1 x); tryfalse.
  destruct (get tcbls x); tryfalse.
  substs.
  unfold V_OSTCBPrio in H14.
  unfold V_OSTCBDly in H14.
  unfold V_OSTCBStat in H14.
  unfold V_OSTCBEventPtr in H14.
  simpl in H14.
  assert (exists m0, (p, t, m) = (i6, wait (os_stat_mutexsem a0) i4, m0)).
  apply H16; auto.
  destruct H19; inverts H19.
  eauto.

  simpl in H; mytac.
  pose proof IHl x0 rtbl x1; clear IHl.
  apply H in H0; auto; clear H.
  mytac.
  exists x3.
  pose proof H6 x3.
  rewrite H in H0.
  destruct (get (Maps.sig x x2) x3); tryfalse.
  destruct (get tcbls x3); tryfalse.
  substs.
  eauto.
Qed.


Lemma list_app_in :
  forall (A:Type) (l1:list A) l2 l3 l4 x,
    l1 ++ l2 = l3 ++ x :: l4 -> In x l1 \/ In x l2.
Proof.
  intros.
  gen l1 l2 l4 x.
  inductions l3; intros.
  destruct l1.
  do 2 rewrite app_nil_l in H.
  substs.
  right.
  simpl; auto.

  rewrite app_nil_l in H.
  rewrite <- app_comm_cons in H.
  inverts H.
  left.
  simpl; auto.

  destruct l1.
  destruct l2.
  rewrite app_nil_l in H.
  tryfalse.
  rewrite app_nil_l in H.
  rewrite <- app_comm_cons in H.
  inversion H.
  pose proof IHl3 nil l2 l4 x.
  rewrite app_nil_l in H0.
  pose proof H0 H2; clear H0.
  substs.
  right.
  destruct H3.
  simpl in H0; tryfalse.
  simpl; right.
  auto.

  do 2 rewrite <- app_comm_cons in H.
  inverts H.
  apply IHl3 in H2.
  destruct H2.
  left.
  simpl; right; auto.
  right; auto.
Qed.

Import EcbMod.
(*candidate lemma for MapLib*)
Lemma joinsig_beq_addrval_false_get : forall a a1 x x1 m1 m2,
  joinsig a x m1 m2 -> get m2 a1 = Some x1 -> a <> a1 -> get m1 a1 = Some x1. 
Proof.
  intros.
  unfold joinsig in H.
  pose proof H a1.
  rewrite get_sig_none in H2; auto.
  rewrite H0 in H2.
  destruct (get m1 a1); tryfalse.
  substs; auto.
Qed.


Lemma beq_pos_true : forall p, beq_pos p p = true.
Proof.
  inductions p.
  unfolds.
  fold beq_pos.
  rewrite IHp; auto.
  unfolds.
  fold beq_pos.
  rewrite IHp; auto.
  simpl; auto.
Qed.


Lemma beq_addrval_false_neq : forall a1 a2, beq_addrval a1 a2 = false -> a1 <> a2.
Proof.
  intros.
  unfolds in H.
  destruct a1, a2.
  intro.
  inverts H0.
  rewrite beq_pos_true in H.
  rewrite Int.eq_true in H.
  simpl in H; tryfalse.
Qed.

Lemma ECBList_P_get_ectr_some : forall (l:list EventCtr) tl ecbls mqls tcbls a x v,
  EcbMod.get mqls a = Some x -> ECBList_P v tl l ecbls mqls tcbls ->
  exists et etbl, get_ectr (Vptr a) v l = Some (et, etbl).
Proof.
  inductions l; intros.
  simpl in H0; mytac.
  unfolds in H; simpl in H; tryfalse.
  simpl in H0.
  destruct ecbls; mytac; tryfalse.
  destruct a; mytac.
  simpl.
  destruct (beq_addrval a0 x0) eqn : eq1.
  eauto.
  rewrite H0.
  assert (EcbMod.get x2 a0 = Some x).
  apply beq_addrval_false_neq in eq1.
  eapply joinsig_beq_addrval_false_get; eauto.
  clear H.
  eapply IHl; eauto.
Qed.


Lemma in_TCBList_P_TCBNode_P :
  forall l a h r m, In a l -> TCBList_P h l r m-> exists rtbl abstcb, TCBNode_P a rtbl abstcb.
Proof.
  inductions l; intros.
  simpl in H; tryfalse.
  simpl in H.
  destruct H; substs.
  simpl in H0; mytac; eauto.
  simpl in H0; mytac.
  eapply IHl; eauto.
Qed.
  
Lemma tcb_eptr_get_ectr':
  forall v'14 v'15 v'3 v'4 v'5 v'6 v'7 v'21 v'28 v'9
         b i7 x6 i6 i5 i4 i3 i2 i1 i0 v'17 v'18 v'13 v'8 v'20 v'16 v'22 v'19,
    TcbMod.join v'14 v'15 v'13 ->
    TCBList_P (Vptr v'3) v'5 v'8 v'14 ->
    TCBList_P v'4 (v'6 :: v'7) v'8 v'15 ->
    v'5 ++ v'6 :: v'7 =
    v'21 ++
         (v'28
            :: v'9
            :: Vptr (b, i7)
            :: x6
            :: Vint32 i6
            :: Vint32 i5 (*V$OS_STAT_Q*)
            :: Vint32 i4
            :: Vint32 i3
            :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil)
         :: v'22 ->
    ECBList_P v'20 Vnull v'16 v'17 v'18 v'13 ->
    RH_TCBList_ECBList_P v'18 v'13 v'19 ->
    (*added by zhanghui *) 0 <= Int.unsigned i4 < 64 -> array_type_vallist_match Int8u v'8 -> length v'8 = ∘OS_RDY_TBL_SIZE ->
    exists et etbl, get_ectr (Vptr (b, i7)) v'20 v'16 = Some (et,etbl) .
Proof.
  intros.
  assert
    (i5 = $ OS_STAT_RDY \/
     i5 = $ OS_STAT_SEM \/
     i5 = $ OS_STAT_Q \/ i5 = $ OS_STAT_MBOX \/ i5 = $ OS_STAT_MUTEX).
  apply list_app_in in H2.
  destruct H2.


  eapply in_TCBList_P_TCBNode_P in H2; eauto.
  mytac; unfolds in H2; destruct x0; destruct p; mytac.
  unfolds in H11; mytac.
  unfolds in H10; mytac.
  unfolds in H19; simpl in H19; inverts H19.
  auto.

  eapply in_TCBList_P_TCBNode_P in H2; eauto.
  mytac; unfolds in H2; destruct x0; destruct p; mytac.
  unfolds in H11; mytac.
  unfolds in H10; mytac.
  unfolds in H19; simpl in H19; inverts H19.
  auto.

  destruct H8; substs.
(*$OS_STAT_RDY*)
  apply list_app_in in H2.
  destruct H2.
  
  eapply in_TCBList_P_TCBNode_P in H2; eauto.
  mytac; unfolds in H2; destruct x0; destruct p; mytac.
  unfolds in H11; mytac.
  unfolds in H10; mytac.
  unfolds in H9; simpl in H19; inverts H19.
  unfolds in H26; simpl in H26; inverts H26.
  assert( $ OS_STAT_RDY = $ OS_STAT_RDY) by auto.
  apply H27 in H19; tryfalse.
  auto.

  eapply in_TCBList_P_TCBNode_P in H2; eauto.
  mytac; unfolds in H2; destruct x0; destruct p; mytac.
  unfolds in H11; mytac.
  unfolds in H10; mytac.
  unfolds in H9; simpl in H19; inverts H19.
  unfolds in H26; simpl in H26; inverts H26.
  assert( $ OS_STAT_RDY = $ OS_STAT_RDY) by auto.
  apply H27 in H19; tryfalse.
  auto.

  destruct H8; substs.
(*$OS_STAT_SEM*)
  assert (exists tid p n m, TcbMod.get v'13 tid = Some (p, wait (os_stat_sem (b, i7)) n, m)).
  apply list_app_in in H2.
  destruct H2.
  assert(exists tid p n m, TcbMod.get v'14 tid = Some (p, wait (os_stat_sem (b, i7)) n, m)).
  eapply TCBList_P_in_list_get_some_sem; eauto.
  mytac.
  pose proof H x.
  rewrite H8 in H10.
  exists x.
  destruct (TcbMod.get v'15 x); tryfalse.
  destruct (TcbMod.get v'13 x); tryfalse.
  substs; eauto.
  
  assert(exists tid p n m, TcbMod.get v'15 tid = Some (p, wait (os_stat_sem (b, i7)) n, m)).
  eapply TCBList_P_in_list_get_some_sem; eauto.
  mytac.
  pose proof H x.
  rewrite H8 in H10.
  exists x.
  destruct (TcbMod.get v'14 x); tryfalse.
  destruct (TcbMod.get v'13 x); tryfalse.
  substs; eauto.

  mytac.
  unfolds in H4; destruct H4; mytac.
  clear H4 H11 H12.
  unfolds in H10; destruct H10; mytac.
  
  apply H10 in H8; mytac; clear H10.
  eapply ECBList_P_get_ectr_some; eauto.

  destruct H8; substs.
(*$ OS_STAT_Q*)
  assert (exists tid p n m, TcbMod.get v'13 tid = Some (p, wait (os_stat_q (b, i7)) n, m)).
  apply list_app_in in H2.
  destruct H2.
  assert(exists tid p n m, TcbMod.get v'14 tid = Some (p, wait (os_stat_q (b, i7)) n, m)).
  eapply TCBList_P_in_list_get_some_q; eauto.
  mytac.
  pose proof H x.
  rewrite H8 in H10.
  exists x.
  destruct (TcbMod.get v'15 x); tryfalse.
  destruct (TcbMod.get v'13 x); tryfalse.
  substs; eauto.
  
  assert(exists tid p n m, TcbMod.get v'15 tid = Some (p, wait (os_stat_q (b, i7)) n, m)).
  eapply TCBList_P_in_list_get_some_q; eauto.
  mytac.
  pose proof H x.
  rewrite H8 in H10.
  exists x.
  destruct (TcbMod.get v'14 x); tryfalse.
  destruct (TcbMod.get v'13 x); tryfalse.
  substs; eauto.

  mytac.
  unfolds in H4; destruct H4; mytac.
  clear H10 H11 H12.
  unfolds in H4; destruct H4; mytac.
  
  apply H10 in H8; mytac; clear H10.
  
  eapply ECBList_P_get_ectr_some; eauto.

  destruct H8; substs.
(*$OS_STAT_MBOX*)
  assert (exists tid p n m, TcbMod.get v'13 tid = Some (p, wait (os_stat_mbox (b, i7)) n, m)).
  apply list_app_in in H2.
  destruct H2.
  assert(exists tid p n m, TcbMod.get v'14 tid = Some (p, wait (os_stat_mbox (b, i7)) n, m)).
  eapply TCBList_P_in_list_get_some_mbox; eauto.
  mytac.
  pose proof H x.
  rewrite H8 in H10.
  exists x.
  destruct (TcbMod.get v'15 x); tryfalse.
  destruct (TcbMod.get v'13 x); tryfalse.
  substs; eauto.
  
  assert(exists tid p n m, TcbMod.get v'15 tid = Some (p, wait (os_stat_mbox (b, i7)) n, m)).
  eapply TCBList_P_in_list_get_some_mbox; eauto.
  mytac.
  pose proof H x.
  rewrite H8 in H10.
  exists x.
  destruct (TcbMod.get v'14 x); tryfalse.
  destruct (TcbMod.get v'13 x); tryfalse.
  substs; eauto.

  mytac.
  unfolds in H4; destruct H4; mytac.
  clear H4 H10 H12.
  unfolds in H11; destruct H11; mytac.
  
  apply H10 in H8; mytac; clear H10.
  
  eapply ECBList_P_get_ectr_some; eauto.

(**$OS_STAT_MUTEX*)
  substs.
  assert (exists tid p n m, TcbMod.get v'13 tid = Some (p, wait (os_stat_mutexsem (b, i7)) n, m)).
  apply list_app_in in H2.
  destruct H2.
  assert(exists tid p n m, TcbMod.get v'14 tid = Some (p, wait (os_stat_mutexsem (b, i7)) n, m)).
  eapply TCBList_P_in_list_get_some_mutex; eauto.
  mytac.
  pose proof H x.
  rewrite H8 in H10.
  exists x.
  destruct (TcbMod.get v'15 x); tryfalse.
  destruct (TcbMod.get v'13 x); tryfalse.
  substs; eauto.
  
  assert(exists tid p n m, TcbMod.get v'15 tid = Some (p, wait (os_stat_mutexsem (b, i7)) n, m)).
  eapply TCBList_P_in_list_get_some_mutex; eauto.
  mytac.
  pose proof H x.
  rewrite H8 in H10.
  exists x.
  destruct (TcbMod.get v'14 x); tryfalse.
  destruct (TcbMod.get v'13 x); tryfalse.
  substs; eauto.
 
  mytac.
  unfolds in H4; destruct H4; mytac.
  clear H4 H10 H11.
  unfolds in H12; destruct H12; mytac.
  
  apply H10 in H8; mytac; clear H10.
  
  eapply ECBList_P_get_ectr_some; eauto.  
Qed.



Lemma tcb_eptr_get_ectr:
  forall v'14 v'15 v'3 v'4 v'5 v'6 v'7 v'21 v'28 v'9
         b i7 x6 i6 i5 i4 i3 i2 i1 i0 v'17 v'18 v'13 v'8 i v'20 v'16 v'24 v'25 v'26 v'27 v'22 v'19,
    TcbMod.join v'14 v'15 v'13 ->
    TCBList_P (Vptr v'3) v'5 v'8 v'14 ->
    TCBList_P v'4 (v'6 :: v'7) v'8 v'15 ->
    v'5 ++ v'6 :: v'7 =
    v'21 ++
         (v'28
            :: v'9
            :: Vptr (b, i7)
            :: x6
            :: Vint32 i6
            :: Vint32 i5
            :: Vint32 i4
            :: Vint32 i3
            :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil)
         :: v'22 ->
    ECBList_P v'20 Vnull v'16 v'17 v'18 v'13 ->
    RH_TCBList_ECBList_P v'18 v'13 v'19 ->
    tcbls_rtbl_timetci_update v'21 v'8 (Vint32 i) v'20 v'16 =
    Some (v'24, v'25, Vint32 v'26, v'27) ->
    (*added by zhanghui *) 0 <= Int.unsigned i4 < 64 -> array_type_vallist_match Int8u v'8 -> length v'8 = ∘OS_RDY_TBL_SIZE ->
    exists et etbl, get_ectr (Vptr (b, i7)) v'20 v'27 = Some (et,etbl) .
Proof.
  intros.
  eapply tcbls_rtbl_timetci_update_get_ectr_eq;eauto.
  clear H5.
  eapply tcb_eptr_get_ectr';eauto.
Qed.


Lemma beq_addrval_eq: forall a b, beq_addrval a b = true -> a = b.
Proof.
  introv HeqX.
  unfold beq_addrval in HeqX.
  destruct b, a.
  rewrite andb_true_iff in HeqX.
  destruct HeqX.
  rewrite beq_pos_Pos_eqb_eq in H.
  apply Peqb_true_eq in H.
  lets Hx: Int.eq_spec i0 i.
  rewrite H0 in Hx.
  subst.
  auto.
Qed.

Lemma eq_beq_addrval: forall a, beq_addrval a a = true.
Proof.
  unfold beq_addrval.
  destruct a.
  rewrite andb_true_iff.
  split.
  rewrite beq_pos_Pos_eqb_eq.
  apply Pos.eqb_refl.
  apply Int.eq_true.
Qed.

Lemma get_ectr_decompose:
  forall qptrl s P msgqls l x p eid,
    s |= evsllseg p Vnull qptrl msgqls ** P ->
    get_ectr (Vptr eid) p qptrl = Some (l,x) ->
    s |= EX vn qptrl1 qptrl2 msgqls1 msgqls2 msgq, 
  [| V_OSEventListPtr l = Some vn /\
     qptrl = qptrl1 ++ ((l, x) :: nil) ++ qptrl2 /\
     msgqls = msgqls1 ++ (msgq :: nil) ++ msgqls2 /\ get_ectr (Vptr eid) p qptrl1 = None /\
   (get_ectr  (Vptr eid) p (qptrl1++ ((l, x) :: nil)) = Some (l,x)) /\ p <> Vnull /\ forall l,In l qptrl1 -> exists x,V_OSEventListPtr (fst l) = Some (Vptr x)|] **
                                                     AEventNode (Vptr eid) l x msgq **
                                                     evsllseg p (Vptr eid) qptrl1 msgqls1 ** evsllseg vn Vnull qptrl2 msgqls2 ** P.
Proof.
  induction qptrl.
  intros.
  simpl evsllseg in *.
  sep split in H.
  destruct H1;subst.
  simpl in H0.
  tryfalse.
  intros.
  simpl evsllseg in *.
  destruct msgqls.
  simpl in H;mytac;tryfalse.
  destruct a as (osevent,etbl).
  sep normal in H.
  sep destruct H.
  sep split in H.
  simpl in H0.
  destruct p;tryfalse.
  remember (beq_addrval eid a) as X.
  destruct X.
  inverts H0.
  sep lift 2%nat in H.
  exists x0 (nil:list EventCtr) qptrl.
  exists (nil:list EventData) msgqls e.
  simpl evsllseg.
  symmetry in HeqX.
  apply beq_addrval_eq in HeqX.
  subst.
  sep auto.
  simpl;splits;auto.
  rewrite eq_beq_addrval.
  auto.
  intro;tryfalse.
  intros.
  tryfalse.
  xunfold' H0.
  inverts H1.
  sep lift 2%nat in H.
  lets Hx: IHqptrl H H0.
  sep normal in Hx.
  clear H.
  sep destruct Hx.
  sep split in Hx.
  mytac.
  clear IHqptrl.
  sep auto.
  Focus 2.
  splits;simpl.
  eauto.
  instantiate (1:=x3).
  instantiate (1:= (osevent, etbl) :: x2).
  simpl.
  auto.
  instantiate (1:= x5).
  instantiate (1:= x6).
  instantiate (1:= e :: x4).
  simpl;auto.
  simpl.
  rewrite <- HeqX.
  rewrite <- HeqH2.
  auto.
  simpl.
  rewrite <- HeqX.
  rewrite <- HeqH2.
  auto.
  intro;tryfalse.
  intros.
  simpl in H1.
  destruct H1;auto.
  subst.
  simpl.
  rewrite <- HeqH2.
  destruct eid;tryfalse.
  destruct x2;destruct x0;simpl in H4;tryfalse;eexists;auto.
  simpl evsllseg at 1.
  sep auto.
Qed.

Lemma vl_elem_neq_dec: forall l x,vl_elem_neq (x::l) -> vl_elem_neq l.
Proof.
  intros.
  unfolds in H.
  unfolds; intros.
  pose proof H (S n) (S m) vn vm.
  apply H3.
  simpl; auto.
  simpl; auto.
  auto.
Qed.


Lemma val_elem_neq_one:
  forall x,vl_elem_neq (x::nil).
Proof.
  unfold vl_elem_neq; intros.
  destruct n; destruct m; tryfalse.
Qed.



Lemma beq_tid_true :
  forall tid, beq_tid tid tid = true.
Proof.
  intros.
  unfolds.
  destruct tid.
  rewrite beq_pos_true.
  rewrite Int.eq_true.
  auto.
Qed.

Lemma in_remove_tid_false :
  forall l tid, In tid (remove_tid tid l) -> False.
Proof.
  inductions l; intros.
  simpl in H; auto.
  simpl in H.
  destruct (beq_tid tid a) eqn : eq1.
  eapply IHl; eauto.
  simpl in H; destruct H.
  substs.
  rewrite beq_tid_true in eq1; tryfalse.
  eapply IHl; eauto.
Qed.


Lemma in_remove_in: forall tid t wl, In tid (remove_tid t wl) -> In tid wl.
Proof.
  intros.
  gen tid t H.
  inductions wl; intros.
  simpl in H; auto.
  simpl in H.
  destruct (beq_tid t a) eqn : eq1.
  simpl.
  apply IHwl in H.
  auto.
  simpl in H.
  destruct H.
  simpl.
  left; auto.
  apply IHwl in H.
  simpl; right; auto.
Qed.


Lemma beq_tid_true_eq :
  forall t1 t2, beq_tid t1 t2 = true -> t1 = t2.
Proof.
  intros.
  unfolds in H.
  destruct t1, t2.
  apply andb_true_iff in H.
  destruct H.
  rewrite beq_pos_Pos_eqb_eq in H.
  apply Peqb_true_eq in H.
  pose proof Int.eq_spec i i0.
  rewrite H0 in H1.
  substs; auto.
Qed.

Lemma in_neq_remove_in: forall tid wl t, t <> tid -> In tid wl -> In tid (remove_tid t wl).
Proof.
  intros.
  gen tid t H H0.
  inductions wl; intros.
  simpl in H0; auto.
  simpl in H0.
  destruct H0.
  substs.
  simpl.
  destruct(beq_tid t tid) eqn : eq1.
  apply beq_tid_true_eq in eq1.
  tryfalse.
  simpl; left; auto.
  simpl.
  destruct(beq_tid t a) eqn: eq1.
  apply beq_tid_true_eq in eq1.
  auto.
  simpl.
  right.
  apply IHwl; auto.
Qed.



Lemma tick_rdy_ectr_imp_x:
  forall (v'33 : list (vallist * vallist)) (v'31 v'10 : val) 
         (v'37 : block) (x6 : val) (i6 i5 i4 i3 i2 i1 i0 i8 i10 : int32)
         (v x5 v'24 : val) (x0 : vallist) (v'34 : list (list val * vallist))
         (x1 : int32) x xx,
   (forall l : vallist * vallist,
    In l v'33 -> exists x2, V_OSEventListPtr (fst l) = Some (Vptr x2)) ->
   RL_TCBblk_P
     (v'31
      :: v'10
         :: Vptr (v'37, Int.zero)
            :: x6
               :: Vint32 i6
                  :: Vint32 i5
                     :: Vint32 i4
                        :: Vint32 i3
                           :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil) ->
   RL_Tbl_Grp_P x0 (Vint32 i8) ->
   Int.eq (x1&ᵢInt.not i1) ($ 0) = true ->
   Int.unsigned x1 <= 255 ->
   nth_val' (Z.to_nat (Int.unsigned i2)) x0 = Vint32 x1 ->
   get_ectr (Vptr (v'37, Int.zero)) (Vptr x) v'33 = None ->
   get_ectr (Vptr (v'37, Int.zero)) (Vptr x)
     (v'33 ++
      (xx :: Vint32 i8 :: Vint32 i10 :: v :: x5 :: v'24 :: nil,
      x0) :: nil) =
   Some
     (xx :: Vint32 i8 :: Vint32 i10 :: v :: x5 :: v'24 :: nil,
     x0) ->
   tick_rdy_ectr
     (v'31
      :: v'10
         :: Vptr (v'37, Int.zero)
            :: x6
               :: Vint32 (i6-ᵢ$ 1)
                  :: V$OS_STAT_RDY
                     :: Vint32 i4
                        :: Vint32 i3
                           :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil)
     (Vptr x)
     (v'33 ++
      (xx :: Vint32 i8 :: Vint32 i10 :: v :: x5 :: v'24 :: nil,
      x0) :: v'34) =
   Some
     (v'33 ++
      (xx
       :: Vint32 (i8&ᵢInt.not i0) :: Vint32 i10 :: v :: x5 :: v'24 :: nil,
      update_nth_val (Z.to_nat (Int.unsigned i2)) x0 (Vint32 (x1&ᵢInt.not i1)))
      :: v'34).
Proof.
  induction v'33;introv Hin;intros.
  simpl.
  unfolds.
  simpl.
  simpl in H5.
  simpl in H4.
  destruct x.
  remember ( beq_pos v'37 b && Int.eq Int.zero i) as X.
  destruct X;simpl in H4;tryfalse.
  rewrite H3.
  rewrite H1.
  auto.
  destruct v'24;tryfalse.

  (*----------------*)
  unfolds.
  simpl in H4,H5.
  simpl.
  destruct a.
  destruct x.
  remember (beq_pos v'37 b && Int.eq Int.zero i) as X;destruct X;tryfalse.
  assert (In (v0,v1) ((v0, v1) :: v'33)) by (simpl;auto).
  apply Hin in H6.
  simpl in H6;mytac.
  rewrite H6 in *.
  assert (tick_rdy_ectr 
       (v'31
        :: v'10
           :: Vptr (v'37, Int.zero)
              :: x6
                 :: Vint32 (i6-ᵢ$ 1)
                    :: V$OS_STAT_RDY
                       :: Vint32 i4
                          :: Vint32 i3
                             :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil)
       (Vptr x)
       (v'33 ++
        (xx
         :: Vint32 i8 :: Vint32 i10 :: v :: x5 :: v'24 :: nil, x0) :: v'34) = Some
     ( v'33 ++
         (xx
          :: Vint32 (i8&ᵢInt.not i0) :: Vint32 i10 :: v :: x5 :: v'24 :: nil,
         update_nth_val (Z.to_nat (Int.unsigned i2)) x0
                        (Vint32 (x1&ᵢInt.not i1))) :: v'34)).

  eapply IHv'33;eauto.
  intros.
  apply Hin;simpl;auto.
  unfolds in H7;simpl in H7;auto.
  rewrite H7.
  auto.
Qed.

Lemma tick_rdy_ectr_imp_x':
  forall (v'33 : list (vallist * vallist)) (v'31 v'10 : val) 
         (v'37 : block) (x6 : val) (i6 i5 i4 i3 i2 i1 i0 i8 i10 : int32)
         (v x5 v'24 : val) (x0 : vallist) (v'34 : list (list val * vallist))
         (x1 : int32) x xx,
   (forall l : vallist * vallist,
    In l v'33 -> exists x2, V_OSEventListPtr (fst l) = Some (Vptr x2)) ->
   RL_TCBblk_P
     (v'31
      :: v'10
         :: Vptr (v'37, Int.zero)
            :: x6
               :: Vint32 i6
                  :: Vint32 i5
                     :: Vint32 i4
                        :: Vint32 i3
                           :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil) ->
  
   RL_Tbl_Grp_P x0 (Vint32 i8) ->
   Int.eq (x1&ᵢInt.not i1) ($ 0) = false ->
   Int.unsigned x1 <= 255 ->
   nth_val' (Z.to_nat (Int.unsigned i2)) x0 = Vint32 x1 ->
   get_ectr (Vptr (v'37, Int.zero)) (Vptr x) v'33 = None ->
   get_ectr (Vptr (v'37, Int.zero)) (Vptr x) (v'33 ++ (xx :: Vint32 i8 :: Vint32 i10 :: v :: x5 :: v'24 :: nil, x0) ::nil) = Some (xx :: Vint32 i8 :: Vint32 i10 :: v :: x5 :: v'24 :: nil, x0) ->
   tick_rdy_ectr
     (v'31
        :: v'10
        :: Vptr (v'37, Int.zero)
        :: x6
        :: Vint32 (i6-ᵢ$ 1)
        :: V$OS_STAT_RDY
        :: Vint32 i4
        :: Vint32 i3
        :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil)
     (Vptr x)
     (v'33 ++
           (xx :: Vint32 i8 :: Vint32 i10 :: v :: x5 :: v'24 :: nil,
            x0) :: v'34) =
   Some
     (v'33 ++
           (xx
             :: Vint32 i8 :: Vint32 i10 :: v :: x5 :: v'24 :: nil,
            update_nth_val (Z.to_nat (Int.unsigned i2)) x0 (Vint32 (x1&ᵢInt.not i1)))
           :: v'34).
Proof.
  induction v'33;introv Hin;intros.
  simpl.
  unfolds.
  simpl.
  simpl in H5.
  simpl in H4.
  destruct x.
  remember ( beq_pos v'37 b && Int.eq Int.zero i) as X.
  destruct X;simpl in H4;tryfalse.
  rewrite H3.
  rewrite H1.
  auto.
  destruct v'24;tryfalse.

  (*----------------*)
  unfolds.
  simpl in H4,H5.
  simpl.
  destruct a.
  destruct x.
  remember (beq_pos v'37 b && Int.eq Int.zero i) as X;destruct X;tryfalse.
  assert (In (v0,v1) ((v0, v1) :: v'33)) by (simpl;auto).
  apply Hin in H6.
  simpl in H6;mytac.
  rewrite H6 in *.
  assert (tick_rdy_ectr 
       (v'31
        :: v'10
           :: Vptr (v'37, Int.zero)
              :: x6
                 :: Vint32 (i6-ᵢ$ 1)
                    :: V$OS_STAT_RDY
                       :: Vint32 i4
                          :: Vint32 i3
                             :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil)
       (Vptr x)
       (v'33 ++
        (xx
         :: Vint32 i8 :: Vint32 i10 :: v :: x5 :: v'24 :: nil, x0) :: v'34) = Some
     ( v'33 ++
         (xx
          :: Vint32 i8 :: Vint32 i10 :: v :: x5 :: v'24 :: nil,
         update_nth_val (Z.to_nat (Int.unsigned i2)) x0
                        (Vint32 (x1&ᵢInt.not i1))) :: v'34)).

  eapply IHv'33;eauto.
  intros.
  apply Hin;simpl;auto.
  unfolds in H7;simpl in H7;auto.
  rewrite H7.
  auto.
Qed.

Lemma tick_rdy_ectr_imp:
  forall v'21,
    isptr v'21 ->
    v'21 <> Vnull ->
    forall v'33 v'31 v'10 v'37 x6 i6 i5 i4 i3 i2 i1 i0 i8 i10 v x5 v'24 x0 v'34 x xx,
    (forall l,In l v'33 -> exists x, V_OSEventListPtr (fst l) = Some (Vptr x)) ->
    RL_TCBblk_P
      (v'31
         :: v'10
         :: Vptr (v'37, Int.zero)
         :: x6
         :: Vint32 i6
         :: Vint32 i5
         :: Vint32 i4
         :: Vint32 i3
         :: Vint32 i2
         :: Vint32 i1 :: Vint32 i0 :: nil) ->
    RL_Tbl_Grp_P x0 (Vint32 i8) ->
    Int.eq (x&ᵢInt.not i1) ($ 0) = true ->
    (Int.unsigned x <= 255)%Z ->
    nth_val' (Z.to_nat (Int.unsigned i2)) x0 = Vint32 x ->
    get_ectr (Vptr (v'37, Int.zero)) v'21 v'33 = None ->
    get_ectr (Vptr (v'37, Int.zero)) v'21 (v'33 ++ (xx:: Vint32 i8 :: Vint32 i10 :: v :: x5 :: v'24 :: nil, x0) ::nil) = Some (xx:: Vint32 i8 :: Vint32 i10 :: v :: x5 :: v'24 :: nil, x0)->
    tick_rdy_ectr
      (v'31
         :: v'10
         :: Vptr (v'37, Int.zero)
         :: x6
         :: Vint32 (i6-ᵢ$ 1)
         :: V$OS_STAT_RDY
         :: Vint32 i4
         :: Vint32 i3
         :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil)
      v'21
      (v'33 ++
            (xx :: Vint32 i8 :: Vint32 i10 :: v :: x5 :: v'24 :: nil,
             x0) :: v'34) =
    Some
      (v'33 ++
            (xx
              :: Vint32 (i8&ᵢInt.not i0) :: Vint32 i10 :: v :: x5 :: v'24 :: nil,
             update_nth_val (Z.to_nat (Int.unsigned i2)) x0 (Vint32 (x&ᵢInt.not i1)))
            :: v'34).
Proof.  
  introv Hv'21 Hv'21'.
  unfolds in Hv'21.
  destruct Hv'21;tryfalse.
  mytac.
  clear Hv'21'.
  intros.
  eapply tick_rdy_ectr_imp_x;eauto.
Qed.

Lemma tick_rdy_ectr_imp':
  forall v'21,
    isptr v'21 ->
    v'21 <> Vnull ->
    forall v'33 v'31 v'10 v'37 x6 i6 i5 i4 i3 i2 i1 i0 i8 i10 v x5 v'24 x0 v'34 x xx,
    (forall l,In l v'33 -> exists x, V_OSEventListPtr (fst l) = Some (Vptr x)) ->
    RL_TCBblk_P
      (v'31
         :: v'10
         :: Vptr (v'37, Int.zero)
         :: x6
         :: Vint32 i6
         :: Vint32 i5
         :: Vint32 i4
         :: Vint32 i3
         :: Vint32 i2
         :: Vint32 i1 :: Vint32 i0 :: nil) ->
    RL_Tbl_Grp_P x0 (Vint32 i8) ->
    Int.eq (x&ᵢInt.not i1) ($ 0) = false ->
    Int.unsigned x <= 255 ->
    nth_val' (Z.to_nat (Int.unsigned i2)) x0 = Vint32 x ->
    get_ectr (Vptr (v'37, Int.zero)) v'21 v'33 = None ->
    get_ectr (Vptr (v'37, Int.zero)) v'21 (v'33 ++ (xx :: Vint32 i8 :: Vint32 i10 :: v :: x5 :: v'24 :: nil, x0) ::nil) = Some (xx :: Vint32 i8 :: Vint32 i10 :: v :: x5 :: v'24 :: nil, x0) ->
    tick_rdy_ectr
      (v'31
         :: v'10
         :: Vptr (v'37, Int.zero)
         :: x6
         :: Vint32 (i6-ᵢ$ 1)
         :: V$OS_STAT_RDY
         :: Vint32 i4
         :: Vint32 i3
         :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil)
      v'21
      (v'33 ++
            (xx:: Vint32 i8 :: Vint32 i10 :: v :: x5 :: v'24 :: nil,
             x0) :: v'34) =
    Some
      (v'33 ++
            (xx
              :: Vint32 i8 :: Vint32 i10 :: v :: x5 :: v'24 :: nil,
             update_nth_val (Z.to_nat (Int.unsigned i2)) x0 (Vint32 (x&ᵢInt.not i1)))
            :: v'34).
Proof.
  introv Hv'21 Hv'21'.
  unfolds in Hv'21.
  destruct Hv'21;tryfalse.
  mytac.
  clear Hv'21'.
  intros.
  eapply tick_rdy_ectr_imp_x';eauto.
Qed.


Lemma tcbls_rtbl_timetci_update_compose:
  forall tls1 rtbl rgrp head els tls1' rtbl' rgrp' els' tls2 tls2' rtbl'' rgrp'' els'',
    tcbls_rtbl_timetci_update tls1 rtbl (Vint32 rgrp) head els =
    Some (tls1',rtbl', Vint32 rgrp', els') ->
    tcbls_rtbl_timetci_update tls2 rtbl' (Vint32 rgrp') head els' = Some (tls2',rtbl'',Vint32 rgrp'',els'') ->
    tcbls_rtbl_timetci_update (tls1++tls2) rtbl (Vint32 rgrp) head els = Some (tls1'++tls2',rtbl'',Vint32 rgrp'',els'').
Proof.
  induction tls1.
  intros.
  simpl in *.
  inverts H.
  auto.

  intros.
  simpl in H.
  xunfold H; rewrite <- HeqH18;  unfold add_option_first.
  symmetry in Htick.
  lets Hx: IHtls1 Htick H0.
  rewrite Hx.
  auto.
  rewrite <- HeqH19.
  xunfold'' HeqH20.
  xunfold'' HeqH20.
  symmetry in Htick.
  lets Hx: IHtls1 Htick H0.
  inverts_all.
  rewrite Hx.
  auto.
  rewrite <- HeqH19.
  
  xunfold'' HeqH20.
  xunfold'' HeqH20.
  rewrite <- HeqH22.
  symmetry in Htick.
  lets Hx: IHtls1 Htick H0.
  inverts_all.
  rewrite Hx.
  auto.
  rewrite <- HeqH19.
  symmetry in Htick.
  lets Hx: IHtls1 Htick H0.
  inverts_all.
  rewrite Hx.
  auto.
Qed.

    
Lemma tcbls_rtbl_timetci_update_decompose:
  forall v'25 v'26 v'27 v'28 v'29 v'33 v'34 v'35 head els  els'',
    tcbls_rtbl_timetci_update (v'25 ++ v'26 :: v'27) v'28 v'29 head els =
    Some (v'35, v'33, v'34, els'') ->
    exists vl1 v vl2 rtbl' rgrp' els',
      v'35 = vl1 ++ v::vl2 /\
      tcbls_rtbl_timetci_update v'25 v'28 v'29 head els =
      Some (vl1, rtbl', rgrp',els') /\
      tcbls_rtbl_timetci_update (v'26 :: v'27) rtbl' rgrp' head els' =
      Some ((v::vl2), v'33, v'34, els'').
Proof.
  induction v'25.
  intros.
  simpl (nil ++ v'26 :: v'27) in H.
  simpl in H.
  xunfold H;eauto.
  do 6 eexists;splits;simpl;eauto.
  simpl.
  eauto.
  rewrite <- HeqH18.
  unfolds.
  rewrite <- Htick.
  auto.
  xunfold'' HeqH22.
  xunfold'' HeqH22.
  do 6 eexists;splits;simpl;eauto.
  simpl.
  eauto.
  rewrite <- HeqH18.
  rewrite <- HeqH19.
  rewrite <- HeqH20.
  inverts_all.
  rewrite <- HeqH.
  rewrite <- HeqH0.
  unfolds;simpl;auto.
  rewrite <- Htick.
  auto.
  do 6 eexists;splits;simpl;eauto.
  simpl.
  eauto.
  xunfold'' HeqH22.
  xunfold'' HeqH22.
  rewrite <- HeqH18.
  rewrite <- HeqH19.
  rewrite <- HeqH20.
  inverts_all.
  rewrite <- HeqH24.
  unfolds;simpl;auto.
  rewrite <- Htick.
  auto.
  do 6 eexists;splits;simpl;eauto.
  simpl.
  eauto.
  rewrite <- HeqH18.
  rewrite <- HeqH19.
  unfolds;simpl;auto.
  rewrite <- Htick.
  auto.
  
  (*---------------------------*)
  intros.
  simpl ((a :: v'25) ++ v'26 :: v'27) in H.
  simpl in H.
  xunfold H.
  symmetry in Htick.
  apply IHv'25 in Htick.
  clear IHv'25.
  mytac.
  do 6 eexists;splits;eauto.
  instantiate (1:=  (v
    :: v0
       :: v1
          :: v2
             :: Vint32 i
                :: v4
                   :: Vint32 i0
                      :: Vint32 i1
                         :: Vint32 i2 :: Vint32 i3 :: Vint32 i4 :: nil)
   :: x ).
  simpl;auto.
  clear H1.
  rewrite <- HeqH18.
  unfolds;simpl;auto.
  rewrite H0;auto.
  
  symmetry in Htick.
  apply IHv'25 in Htick.
  clear IHv'25.
  mytac.
  do 6 eexists;splits;eauto.
  instantiate (1:=  (v
    :: v0
       :: Vnull
          :: v2
             :: Vint32 (i-ᵢInt.one)
                :: V$OS_STAT_RDY
                   :: Vint32 i0
                      :: Vint32 i1
                         :: Vint32 i2 :: Vint32 i3 :: Vint32 i4 :: nil)
   :: x).
  simpl;auto.
  clear H1.
  xunfold'' HeqH22.
  xunfold'' HeqH22.
  rewrite <- HeqH18.
  rewrite <- HeqH19.
  rewrite <- HeqH20.
  inverts_all.
  unfolds;simpl;auto.
  rewrite H0.
  auto.

  symmetry in Htick.
  apply IHv'25 in Htick.
  clear IHv'25.
  mytac.
  do 6 eexists;splits;eauto.
  instantiate (1:=  (v
    :: v0
       :: Vnull
          :: v2
             :: Vint32 (i-ᵢInt.one)
                :: V$OS_STAT_RDY
                   :: Vint32 i0
                      :: Vint32 i1
                         :: Vint32 i2 :: Vint32 i3 :: Vint32 i4 :: nil)
   :: x).
  simpl;auto.
  clear H1.
  xunfold'' HeqH22.
  xunfold'' HeqH22.
  rewrite <- HeqH18.
  rewrite <- HeqH19.
  rewrite <- HeqH20.
  inverts_all.
  rewrite <- HeqH24.
  unfolds;simpl;auto.
  rewrite H0.
  auto.

  symmetry in Htick.
  apply IHv'25 in Htick.
  clear IHv'25.
  mytac.
  do 6 eexists;splits;eauto.
  instantiate (1:=(v
    :: v0
       :: v1
          :: v2
             :: Vint32 (i-ᵢInt.one)
                :: v4
                   :: Vint32 i0
                      :: Vint32 i1
                         :: Vint32 i2 :: Vint32 i3 :: Vint32 i4 :: nil)
   :: x).
  simpl;auto.
  clear H1.
  rewrite <- HeqH18.
  rewrite <- HeqH19.
  unfolds;simpl;auto.
  rewrite H0.
  auto.
Qed.

Lemma tick_rdy_ectr_ignore:
  forall v'28 next pre msg tm stat next' pre' msg' tm' stat' x1 x y z w v v'21,
    (tick_rdy_ectr
       (next
          :: pre
          :: Vptr x1
          :: msg
          :: tm
          :: stat
          :: Vint32 x
          :: Vint32 y
          :: Vint32 z
          :: Vint32 w
          :: Vint32 v :: nil) v'21
       v'28) =
    (tick_rdy_ectr
       (next'
          :: pre'
          :: Vptr x1
          :: msg'
          :: tm'
          :: stat'
          :: Vint32 x
          :: Vint32 y
          :: Vint32 z
          :: Vint32 w
          :: Vint32 v :: nil) v'21
       v'28).
Proof.
  unfold tick_rdy_ectr.
  simpl.
  induction v'28.
  intros.
  simpl.
  auto.
  intros.
  simpl.
  destruct v'21;auto.
  destruct a.
  destruct (beq_addrval x1 a0);auto.
  destruct (V_OSEventListPtr v0);auto.
  assert (tick_rdy_ectr' x1
       (next
        :: pre
           :: Vptr x1
              :: msg
                 :: tm
                    :: stat
                       :: Vint32 x
                          :: Vint32 y
                             :: Vint32 z :: Vint32 w :: Vint32 v :: nil) v2
       v'28 =  tick_rdy_ectr' x1
       (next'
        :: pre'
           :: Vptr x1
              :: msg'
                 :: tm'
                    :: stat'
                       :: Vint32 x
                          :: Vint32 y
                             :: Vint32 z :: Vint32 w :: Vint32 v :: nil) v2
       v'28).
  apply IHv'28.
  rewrite H.
  auto.
Qed.

Lemma tcbls_rtbl_timetci_update_hold:
  forall v'22 v'9 i v'17 v'26 v'27 v'31 v'10 x6 i6 i4 i3 i2 i1 i0 v'21 v'28 v'24 v'25 x7 i5 head rtbl tcbls,
    isptr x7 ->
    TCBList_P head v'22 rtbl tcbls ->
    array_type_vallist_match Int8u v'9 ->
    length v'9 = ∘OS_RDY_TBL_SIZE ->
    Int.unsigned i <= 255 ->
    Int.eq i6 ($ 0) = false ->
    Int.eq (i6-ᵢ$ 1) ($ 0) = true ->
    tcbls_rtbl_timetci_update v'22 v'9 (Vint32 i) v'21 v'17 = Some (v'25, v'26, Vint32 v'27, v'28) ->
    RL_TCBblk_P
      (v'31
         :: v'10
         :: Vnull
         :: x6
         :: Vint32 (i6-ᵢ$ 1)
         :: V$OS_STAT_RDY
         :: Vint32 i4
         :: Vint32 i3
         :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil) ->
    RL_Tbl_Grp_P v'9 (Vint32 i) ->
    tick_rdy_ectr
      (v'31
         :: v'10
         :: x7
         :: x6
         :: Vint32 (i6-ᵢ$ 1)
         :: V$OS_STAT_RDY
         :: Vint32 i4
         :: Vint32 i3
         :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil)
      v'21 v'28 = Some v'24 ->
    tcbls_rtbl_timetci_update
      (v'22 ++
            (v'31
               :: v'10
               :: x7
               :: x6
               :: Vint32 i6
               :: Vint32 i5
               :: Vint32 i4
               :: Vint32 i3
               :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil)
            :: nil) v'9 (Vint32 i) v'21 v'17 =
    Some
      (v'25 ++
            (v'31
               :: v'10
               :: Vnull
               :: x6
               :: Vint32 (i6-ᵢ$ 1)
               :: V$OS_STAT_RDY
               :: Vint32 i4
               :: Vint32 i3
               :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil)
            :: nil,
       update_nth_val (Z.to_nat (Int.unsigned i2)) v'26
                      (val_inj (or (nth_val' (Z.to_nat (Int.unsigned i2)) v'26) (Vint32 i1))),
       Vint32 (Int.or v'27 i0), v'24).
Proof.
  introv Hx7.
  intros.
  eapply tcbls_rtbl_timetci_update_compose;eauto.
  simpl.
  unfolds Int.zero.
  rewrite H3.
  unfold Int.one.
  rewrite H4.
  lets Hx:timetick_update_prop H H0 H1 H2 H7.
  lets Hx': Hx H5.
  clear Hx.
  mytac.
  funfold H6.
  lets Hx:n07_arr_len_ex H9 H10.
  instantiate (1:=Z.to_nat (Int.unsigned (Int.shru x ($ 3)))).

  eapply z_to_nat_shr3;eauto.
  mytac.
  rewrite H6.
  simpl.
  unfolds in Hx7.
  destruct Hx7.
  subst.
  unfold val_inj.
  unfold or.
  rewrite nth_val'_and_nth_val.
  rewrite H6.
  simpl.
  unfolds in H8.
  simpl in H8.
  inverts H8.
  auto.
  destruct H14.
  subst.

  rewrite tick_rdy_ectr_ignore with (next':=v'31) (pre':=v'10) (msg':=x6) (tm':=Vint32 (i6-ᵢ$ 1)) (stat':=V$OS_STAT_RDY).
  rewrite H8.
  unfold val_inj.
  unfold or.
  rewrite nth_val'_and_nth_val.
  rewrite H6.
  simpl.
  unfolds in H8.
  simpl in H8.
  inverts H8.
  auto.
Qed.


Lemma tcbls_rtbl_timetci_update_hold':
  forall v'22 v'9 i v'17 v'26 v'27 v'31 v'10 x6 i6 i4 i3 i2 i1 i0 v'21 v'28 v'25 x7 i5,
    Int.eq i6 ($ 0) = false ->
    Int.eq (i6-ᵢ$ 1) ($ 0) = false ->
    tcbls_rtbl_timetci_update v'22 v'9 (Vint32 i) v'21 v'17 = Some (v'25, v'26, Vint32 v'27, v'28) ->
    tcbls_rtbl_timetci_update
      (v'22 ++
            (v'31
               :: v'10
               :: x7
               :: x6
               :: Vint32 i6
               :: Vint32 i5
               :: Vint32 i4
               :: Vint32 i3
               :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil)
            :: nil) v'9 (Vint32 i) v'21 v'17 =
    Some
      (v'25 ++
            (v'31
               :: v'10
               :: x7
               :: x6
               :: Vint32 (i6-ᵢ$ 1)
               :: Vint32 i5
               :: Vint32 i4
               :: Vint32 i3
               :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil)
            :: nil,
       v'26,
       Vint32 v'27, v'28).
Proof.
  intros.
  eapply tcbls_rtbl_timetci_update_compose;eauto.
  simpl.
  unfolds Int.zero.
  rewrite H.
  unfold Int.one.
  rewrite H0.
  auto.
Qed.


Lemma tcbls_rtbl_timetci_update_hold'':
  forall v'22 v'9 i v'17 v'26 v'27 v'31 v'10 x6 i6 i4 i3 i2 i1 i0 v'21 v'28 v'25 x7 i5,
    Int.eq i6 ($ 0) = true ->
    tcbls_rtbl_timetci_update v'22 v'9 (Vint32 i) v'21 v'17 = Some (v'25, v'26, Vint32 v'27, v'28) ->
    tcbls_rtbl_timetci_update
      (v'22 ++
            (v'31
               :: v'10
               :: x7
               :: x6
               :: Vint32 i6
               :: Vint32 i5
               :: Vint32 i4
               :: Vint32 i3
               :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil)
            :: nil) v'9 (Vint32 i) v'21 v'17 =
    Some
      (v'25 ++
            (v'31
               :: v'10
               :: x7
               :: x6
               :: Vint32 i6
               :: Vint32 i5
               :: Vint32 i4
               :: Vint32 i3
               :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil)
            :: nil,
       v'26,
       Vint32 v'27, v'28).
Proof.
  intros.
  eapply tcbls_rtbl_timetci_update_compose;eauto.
  simpl.
  unfolds Int.zero.
  rewrite H.
  auto.
Qed.
  
(*part2*)

Definition rel_st_els (st : taskstatus) (els : EcbMod.map) :=
  match st with
    | (wait (os_stat_sem eid) one) =>
      match EcbMod.get els eid with
        | Some (m, wl) => true
        | None => false
      end
    | (wait (os_stat_q eid) one) =>
      match EcbMod.get els eid with
        | Some (m, wl) => true
        | None => false
      end
    | (wait (os_stat_mbox eid) one) =>
      match EcbMod.get els eid with
        | Some (m, wl) => true
        | None => false
      end
    | (wait (os_stat_mutexsem eid) one) =>
      match EcbMod.get els eid with
        | Some (m, wl) => true
        | None => false
      end
    | _ => true
  end.



Definition R_Prio_No_Dup_L' (ll:list vallist):=
  forall n  l ,
    nth_vallist n ll = Some l ->
    (
      exists prio, V_OSTCBPrio l = Some (Vint32 prio) /\
      forall n' l',  n <> n' ->
                     nth_vallist n' ll = Some l' ->
                     exists prio',V_OSTCBPrio l' = Some (Vint32 prio') /\
                                  prio <> prio'
    ).
 

Fixpoint Prio_Not_In (prio : int32) (ll : list vallist) {struct ll} :=
  match ll with
    | nil => True
    | l :: ll' => exists prio', V_OSTCBPrio l = Some (Vint32 prio')
                                /\ prio <> prio' /\ Prio_Not_In prio ll'
  end.

Fixpoint R_Prio_No_Dup_L (ll : list vallist) {struct ll} :=
  match ll with
    | nil => True
    | l :: ll' => exists prio,
                  V_OSTCBPrio l = Some (Vint32 prio) /\
                  Prio_Not_In  prio ll'/\ R_Prio_No_Dup_L ll'
  end.


Fixpoint not_in {A B:Type} (e:B) (l:list A) (f:A -> option B) :=
  match l with
    | nil => True
    | h :: t => (forall e', f h = Some e' -> e' <> e) /\ not_in e t f
  end.

Fixpoint set_nth {A:Type} (n:nat) (v:A) (vl: list A) : option (list A) :=
  match vl with
    | nil => None
    | h::t => match n with
                | O => Some (v::t)
                | S x => match set_nth x v t with
                           | Some r => Some (h::r)
                           | None => None
                         end
              end
  end.

Definition set_tcb_next (tcb:vallist) next := set_nth 0%nat next tcb.

Definition get_last_ecb_ptr := 
  fun (l : list  (vallist * vallist)) (x : val) =>
    match l with
      | nil => Some x
      | _ :: _ => V_OSEventListPtr (fst (last l (nil,nil)))
    end.


Fixpoint eq_next l1 l2:=
  match l1,l2 with
    | v1::l1',v2::l2' => nth_val 0%nat v1 = nth_val 0%nat v2 /\ eq_next l1' l2'
    | nil,nil => True
    | _ ,_ => False
  end.



Import TcbMod. 


Lemma join_fst:
  forall a b lstx (l:TcbMod.lb a lstx) (i:TcbMod.is_orderset lstx) (j:TcbMod.is_orderset ((a,b)::lstx)),
    TcbMod.join  (TcbMod.listset_con (lst:=lstx) i) (TcbMod.sig a b) (TcbMod.listset_con (lst:=(a, b) :: lstx)j).
Proof.
  intros.
  intro.
  rewrite TcbMod.sig_sem.
  destruct (tidspec.beq a a0) eqn : eq0.
  apply tidspec.beq_true_eq in eq0; substs.
  destruct(TcbMod.get (TcbMod.listset_con (lst:=lstx) i) a0) eqn : eq1;
  destruct(TcbMod.get (TcbMod.listset_con (lst:=(a0, b) :: lstx) j) a0) eqn: eq2; auto.
  apply TcbMod.lb_notin in l.
  unfold TcbMod.get in eq1.
  simpl in eq1.
  tryfalse.

  unfold TcbMod.get in eq2.
  simpl in eq2.
  rewrite tidspec.eq_beq_true in eq2; auto.
  tryfalse.

  unfold TcbMod.get in eq2.
  simpl in eq2.
  rewrite tidspec.eq_beq_true in eq2; auto.
  inverts eq2; auto.

  unfold TcbMod.get in eq2.
  simpl in eq2.
  rewrite tidspec.eq_beq_true in eq2; auto.
  tryfalse.
  
  apply tidspec.beq_false_neq in eq0.
  destruct(TcbMod.get (TcbMod.listset_con (lst:=lstx) i) a0) eqn : eq1;
  destruct(TcbMod.get (TcbMod.listset_con (lst:=(a, b) :: lstx) j) a0) eqn: eq2; auto.

  unfold TcbMod.get in eq2.
  simpl in eq2.
  rewrite tidspec.neq_beq_false in eq2; auto.
  unfolds in eq1; simpl in eq1.
  rewrite eq1 in eq2; inverts eq2; auto.

  unfolds in eq2; simpl in eq2; rewrite tidspec.neq_beq_false in eq2; auto.
  unfolds in eq1; simpl in eq1.
  rewrite eq1 in eq2; tryfalse.

  unfolds in eq2; simpl in eq2; rewrite tidspec.neq_beq_false in eq2; auto.
  unfolds in eq1; simpl in eq1.
  rewrite eq1 in eq2; tryfalse.
Qed.
 
Lemma disj_eqdom :
  forall m1 m1' m2,
    disj m1 m2 -> eqdom m1 m1' -> disj m1' m2.
Proof.
  intros.
  intro.
  pose proof H a; clear H.
  unfold eqdom in H0.
  unfold indom in H0.
  pose proof H0 a; clear H0.
  destruct H.
  destruct (get m1 a) eqn: eq1.
  assert (exists b0, Some b = Some b0) by eauto.
  apply H in H2.
  destruct H2.
  rewrite H2.
  auto.

  destruct(get m1' a) eqn : eq2.
  assert(exists b0, Some b = Some b0) by eauto.
  apply H0 in H2; destruct H2; tryfalse.

  auto.
Qed.


Lemma tcb_domeq_joinsig_ex:
  forall x1 a b b' x x1',
    TcbMod.join x1 (TcbMod.sig a b) x -> (forall t,TcbMod.indom x1 t <-> TcbMod.indom x1' t) ->exists x', TcbMod.join x1' (TcbMod.sig a b') x'.
Proof.
  intros.
  exists (TcbMod.merge x1' (TcbMod.sig a b')).
  apply TcbMod.join_merge_disj.
(*a candidate lemma for MapLib*)
  apply TcbMod.join_disj_meq in H.
  destruct H; clear H1.
  pose proof disj_eqdom x1 x1' (TcbMod.sig a b) H.
  assert(eqdom x1 x1') by auto.
  apply H1 in H2.
  apply TcbMod.disj_sym.
  apply TcbMod.disj_sym in H2.
  eapply disj_eqdom; eauto.
  unfolds.
  unfold TcbMod.indom.
  intro.
  split; intro.
  destruct H3.
  rewrite TcbMod.sig_sem in H3.
  destruct (tidspec.beq a x0) eqn : eq1.
  inverts H3.
  rewrite sig_sem.
  rewrite eq1; eauto.
  tryfalse.
  destruct H3.
  rewrite TcbMod.sig_sem in H3.
  destruct (tidspec.beq a x0) eqn: eq1; tryfalse.
  inverts H3.
  rewrite TcbMod.sig_sem.
  rewrite eq1; eauto.
Qed.  


Lemma int_dec_zero_one : forall n:int32,
  n = Int.zero \/ n = Int.one \/ (Int.eq Int.one n = false /\ Int.eq Int.zero n = false).
Proof.
  intros.
  destruct n.
  destruct intval.
  left.
  apply Int.unsigned_eq_zero.
  simpl; auto.
  
  destruct p.
  right; right.
  rewrite Int.eq_false; auto; try solve [intro;tryfalse].
  rewrite Int.eq_false; auto; try solve [intro;tryfalse].

  right; left.
  unfold Int.one.
  simpl Int.Z_mod_modulus.
  erewrite Int.eqm_repr_eq.
  reflexivity.
  simpl.
  apply Int.eqm_refl.

  destruct p.
  right; right.
  rewrite Int.eq_false; auto; try solve [intro;tryfalse].
  rewrite Int.eq_false; auto; try solve [intro;tryfalse].
  right; right.
  rewrite Int.eq_false; auto; try solve [intro;tryfalse].
Qed.


Lemma tid_beq_true :
  forall tid, tidspec.beq tid tid = true.
Proof.
  intros.
  unfolds.
  unfolds.
  destruct tid.
  rewrite beq_pos_true.
  rewrite Int.eq_true; auto.
Qed.


Lemma in_remove_tid : forall {l t1 t2}, In t1 (remove_tid t2 l) -> In t1 l.
Proof.
  inductions l; intros.
  simpl in H; tryfalse.
  simpl in H.
  destruct (beq_tid t2 a) eqn : eq1.
  simpl.
  right.
  eapply IHl; eauto.
  simpl in H.
  destruct H.
  substs.
  simpl; auto.
  simpl.
  right.
  eapply IHl; eauto.
Qed.



Lemma in_remove_tid' : forall l t1 t2, In t1 l -> t1 <> t2 -> In t1 (remove_tid t2 l).
Proof.
  inductions l ; intros.
  simpl in H; tryfalse.
  simpl in H.
  destruct H; substs.
  simpl.
  destruct(beq_tid t2 t1) eqn : eq1.
  apply tidspec.beq_true_eq in eq1; tryfalse.
  simpl; auto.
  simpl.
  destruct(beq_tid t2 a) eqn : eq1.
  eapply IHl; eauto.
  simpl.
  right.
  eapply IHl; eauto.
Qed.


Lemma joinsig_listset_con :
  forall l a x i (j:lb a l),
    joinsig a x (listset_con (lst:=l) i) (listset_con (lst:=(a, x):: l) (conj j i)).
Proof.
  intros.
  unfolds.
  unfolds; intros.
  unfold get; simpl.
  destruct (tidspec.beq a0 a) eqn : eq1.
  pose proof tidspec.beq_true_eq a0 a eq1; substs.
  apply lb_notin in j.
  rewrite j; auto.
  destruct(get' l a0); auto.
Qed.


Lemma tid_blt_false : forall tid, tidspec.blt tid tid = false.
Proof.
  intros.
  unfolds.
  unfolds.
  destruct tid.
  rewrite beq_pos_true.
  rewrite blt_pos_Pos_ltb_eq.
  rewrite Pos2Z.inj_ltb.
  rewrite Z.ltb_irrefl.
  unfolds.
  apply zlt_false.
  omega.
Qed.

Lemma lb_get_false :
  forall (l:rlist) a b i, lb a l -> get (listset_con (lst:=l) i) a = Some b -> False.
Proof.
  inductions l; intros.
  unfolds in H0.
  simpl in H0; tryfalse.

  simpl in H; destruct a.
  destruct H.
  unfolds in H0.
  simpl in H0.
  destruct (tidspec.beq a0 a) eqn : eq1.
  apply tidspec.beq_true_eq in eq1; substs.
  rewrite tid_blt_false in H; tryfalse.
  simpl in i; mytac.
  eapply IHl; eauto.
  Grab Existential Variables.
  auto.
Qed.


Lemma isrupd_empisr:(isrupd (isrupd empisr 0%nat true) 0%nat false)  = empisr.
Proof.
  unfold empisr.
  unfolds.
  apply functional_extensionality_dep.
  intros.
  destruct (beq_nat 0 x);auto.
Qed.


Lemma ih_no_lvar
: forall (aop : absop) (isrreg : isr) (si : is) (cs : cs) (ie : ie) ct lg,
    (<|| aop ||>  ** Aisr isrreg ** Ais si ** Acs cs ** Aie ie ** isr_inv ** OSInv ** A_dom_lenv nil) ** p_local OSLInv ct lg ==>
        <|| aop ||>  **
        Aisr isrreg ** Ais si ** Acs cs ** Aie ie ** [|exists k,gettopis si = k /\ forall j, (0 <= j < k)%nat -> isrreg j = false|] ** OSInv ** A_dom_lenv nil ** p_local OSLInv ct lg.
Proof.
  intros.
  sep normal in H.
  sep cancel 8%nat 8%nat.
  sep cancel 7%nat 7%nat.
  sep cancel 7%nat 7%nat.
  sep cancel 1%nat 1%nat.
  sep cancel 3%nat 3%nat.
  sep cancel 3%nat 3%nat.
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

Lemma isrupd_true_false:
  forall ir i,
    isrupd (isrupd ir i true) i false = isrupd ir i false.
Proof.
  intros.
  unfold isrupd.
  apply functional_extensionality_dep.
  intros.
  destruct (beq_nat i x);auto.
Qed.


Lemma a_isr_is_prop_split:
  forall s P isr is, s |= Aisr isr ** Ais is ** A_isr_is_prop ** P -> s |= Aisr isr ** Ais is ** P ** [| isr_is_prop isr is |].
Proof.
  intros.
  unfold A_isr_is_prop in *.
  sep cancel 4%nat 3%nat.
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


Lemma  tcbjoinsig_set_sub_sub:
  forall t x tcbls tcbls' tls y tls',
    TcbMod.joinsig t x tcbls tcbls' ->
    TcbMod.set tls t y = tls' ->
    TcbMod.sub tcbls' tls ->
    TcbMod.sub tcbls tls'.
Proof.
  intros.
  unfolds; intros.
  unfold TcbMod.joinsig in H.
  unfold TcbMod.sub in H1.
  unfold TcbMod.lookup in *.
  pose proof H a.
  substs.
  rewrite H2 in H3.
  destruct (tidspec.beq t a) eqn : eq1.
  pose proof tidspec.beq_true_eq t a eq1; substs.
  rewrite TcbMod.set_a_get_a; auto.
  rewrite TcbMod.get_sig_some in H3; tryfalse.
  pose proof tidspec.beq_false_neq t a eq1.
  rewrite TcbMod.get_sig_none in H3; auto.
  destruct (TcbMod.get tcbls' a) eqn : eq2; tryfalse.
  apply H1 in eq2; substs.
  rewrite TcbMod.set_a_get_a'; auto.
Qed.



Lemma sub_joinsig_set_sud:
  forall tls_used tls t x x' tls_used' tls',
    TcbMod.sub tls_used tls ->
    TcbMod.joinsig t x tls_used' tls_used ->
    TcbMod.set tls t x' = tls' ->TcbMod.sub tls_used' tls'.
Proof.
  intros.
  unfold TcbMod.sub.
  unfold TcbMod.lookup.
  intros.
  pose proof H0 a; clear H0.
  rewrite H2 in H3.
  destruct(tidspec.beq t a) eqn : eq1.
  apply tidspec.beq_true_eq in eq1; substs.
  rewrite TcbMod.get_sig_some in H3; tryfalse.
  rewrite TcbMod.get_sig_none in H3.
  destruct(TcbMod.get tls_used a) eqn : eq2; tryfalse.
  substs.
  rewrite TcbMod.set_a_get_a'; auto.
  unfolds in H.
  unfold TcbMod.lookup in H.
  apply H in eq2.
  auto.
  apply tidspec.beq_false_neq in eq1; auto.
Qed.



Lemma sub_joinsig_get:
  forall tls_used tls t x tls_used',
    TcbMod.sub tls_used tls -> TcbMod.joinsig t x tls_used' tls_used -> TcbMod.get tls t = Some x.
Proof.
  intros.
  pose proof H0 t.
  rewrite TcbMod.get_sig_some in H1.
  destruct (TcbMod.get tls_used' t); tryfalse.
  destruct (TcbMod.get tls_used t) eqn : eq1; tryfalse.
  substs.
  unfolds in H.
  unfold TcbMod.lookup in H.
  apply H in eq1; auto.
Qed.



Lemma ecbmod_set_neq_change:
  forall  eid eid' x a b,
    eid <> eid' ->
    EcbMod.set (EcbMod.set x eid a) eid' b =
    EcbMod.set (EcbMod.set x eid' b) eid a.
Proof.
  intros.
  apply EcbMod.extensionality.
  intro.
  rewrite EcbMod.set_sem.
  rewrite EcbMod.set_sem.
  rewrite EcbMod.set_sem.
  rewrite EcbMod.set_sem.
  
  destruct (tidspec.beq eid' a0) eqn:eq1;
  destruct (tidspec.beq eid a0) eqn:eq2; auto.
  apply tidspec.beq_true_eq in eq1.
  apply tidspec.beq_true_eq in eq2.
  substs; tryfalse.
Qed.


Lemma tcbmod_set_neq_change:
  forall  eid eid' x a b,
    eid <> eid' ->
    TcbMod.set (TcbMod.set x eid a) eid' b =
    TcbMod.set (TcbMod.set x eid' b) eid a.
Proof.
  intros.
  apply TcbMod.extensionality.
  intro.
  rewrite TcbMod.set_sem.
  rewrite TcbMod.set_sem.
  rewrite TcbMod.set_sem.
  rewrite TcbMod.set_sem.
  
  destruct (tidspec.beq eid' a0) eqn:eq1;
  destruct (tidspec.beq eid a0) eqn:eq2; auto.
  apply tidspec.beq_true_eq in eq1.
  apply tidspec.beq_true_eq in eq2.
  substs; tryfalse.
Qed.



Lemma sub_emp:
  forall x,
    TcbMod.sub x emp -> x = emp.
Proof.
  intros.
  apply TcbMod.extensionality.
  intros.
  pose proof H a.
  unfold TcbMod.lookup in H0.
  destruct (TcbMod.get x a).
  pose proof H0 b.
  rewrite H1; auto.
  rewrite TcbMod.emp_sem; auto.  
Qed.


Lemma joinsig_false:
  forall t x y,
    ~ joinsig t x y emp.
Proof.
  intros.
  unfolds.
  intro.
  unfolds in H.
  pose proof H t.
  rewrite TcbMod.get_sig_some in H0.
  destruct (TcbMod.get y t); tryfalse.
Qed.


Lemma tcb_joinsig_get_sub_ex:
  forall t t' st0 st1  tl1' tl1 a tl2 tl2',
    t <> t' ->
    TcbMod.joinsig t st0 tl1' tl1 ->
    TcbMod.get tl1 t' = Some a ->
    TcbMod.sub tl1 tl2 ->
    TcbMod.set tl2 t st1 = tl2' -> 
    TcbMod.get tl1' t' = Some a /\
    TcbMod.sub tl1' tl2' /\ exists x,
                              TcbMod.joinsig t' a x tl1. 
Proof.
  intros.
  split.
  unfolds in H0.
  pose proof H0 t'.
  rewrite H1 in H4.
  rewrite TcbMod.get_sig_none in H4; auto.
  destruct(TcbMod.get tl1' t');
  tryfalse; substs; auto.

  split.
  unfolds; intros.
  pose proof H0 a0.
  pose proof H2 a0.
  unfold TcbMod.lookup in *.
  substs.
  destruct (tidspec.beq t a0) eqn:eq1.
  pose proof tidspec.beq_true_eq t a0 eq1; substs.
  rewrite TcbMod.get_sig_some in H5.
  rewrite TcbMod.set_a_get_a; auto.
  rewrite H4 in H5; tryfalse.

  pose proof tidspec.beq_false_neq t a0 eq1.
  rewrite TcbMod.get_sig_none in H5; auto.
  rewrite TcbMod.set_a_get_a'; auto.
  rewrite H4 in H5.
  destruct(TcbMod.get tl1 a0) eqn:eq2; tryfalse.
  apply H6; substs; auto.
 
  exists (TcbMod.minus tl1 (TcbMod.sig t' a)).
  unfolds; intro.
  rewrite TcbMod.minus_sem.
  destruct(tidspec.beq t' a0) eqn : eq1.
  pose proof tidspec.beq_true_eq t' a0 eq1; substs.
  rewrite TcbMod.get_sig_some.
  rewrite H1; auto.
  pose proof tidspec.beq_false_neq t' a0 eq1.
  rewrite TcbMod.get_sig_none; auto.
  destruct(TcbMod.get tl1 a0); auto.
Qed.

Lemma remove_tid_eq:
  forall wl t t' ,
    remove_tid t' (remove_tid t wl) = remove_tid t (remove_tid t' wl).
Proof.
  inductions wl.
  simpl; auto.
  simpl.
  intros.
  remember (beq_tid t a) as Hx.
  remember ( beq_tid t' a) as Hy.
  destruct Hx; destruct Hy; simpl; auto.
  rewrite <- HeqHx; auto.
  rewrite <- HeqHy; auto.
  rewrite <- HeqHx; auto.
  rewrite <- HeqHy; auto.
  rewrite IHwl.
  auto.
Qed.


Lemma ecbmod_set_eq:
  forall x a b b' c, 
    EcbMod.set (EcbMod.set x a b)  a c =
    EcbMod.set (EcbMod.set x a b')  a c.
Proof.
  intros.
  apply EcbMod.extensionality.
  intro.
  rewrite EcbMod.set_sem.
  rewrite EcbMod.set_sem.
  rewrite EcbMod.set_sem.
  rewrite EcbMod.set_sem.
  destruct(tidspec.beq a a0); auto.
Qed.


Lemma joinsig3_neqtid_joinsig:
  forall t0 t a x3 b x1 c y,
    joinsig t a x3 b ->
    joinsig t a x1 c ->
    joinsig t0 y c b ->
    joinsig t0 y x1 x3.
Proof.
  intros.
  unfold TcbMod.joinsig in *.
  unfolds; intro.
  pose proof H a0; pose proof H0 a0; pose proof H1 a0.
  destruct(tidspec.beq t a0) eqn: eq1;
  destruct(tidspec.beq t0 a0) eqn: eq2.
  pose proof tidspec.beq_true_eq t a0 eq1; substs.
  pose proof tidspec.beq_true_eq t0 a0 eq2; substs.
  rewrite TcbMod.get_sig_some.
  rewrite TcbMod.get_sig_some in H2.
  rewrite TcbMod.get_sig_some in H3.
  rewrite TcbMod.get_sig_some in H4.
  destruct(TcbMod.get x3 a0);
  destruct(TcbMod.get x1 a0);
  destruct(TcbMod.get c a0);  
  destruct(TcbMod.get b a0);
  tryfalse.

  pose proof tidspec.beq_true_eq t a0 eq1; substs.
  pose proof tidspec.beq_false_neq t0 a0 eq2.
  rewrite TcbMod.get_sig_none; auto.
  rewrite TcbMod.get_sig_some in H2; auto.
  rewrite TcbMod.get_sig_some in H3.
  rewrite TcbMod.get_sig_none in H4; auto.
  destruct(TcbMod.get x3 a0);
  destruct(TcbMod.get x1 a0);
  destruct(TcbMod.get c a0);  
  destruct(TcbMod.get b a0);
  tryfalse; auto.

  pose proof tidspec.beq_false_neq t a0 eq1.
  pose proof tidspec.beq_true_eq t0 a0 eq2; substs.
  rewrite TcbMod.get_sig_some; auto.
  rewrite TcbMod.get_sig_none in H2; auto.
  rewrite TcbMod.get_sig_none in H3; auto.
  rewrite TcbMod.get_sig_some in H4.
  destruct(TcbMod.get x3 a0);
  destruct(TcbMod.get x1 a0);
  destruct(TcbMod.get c a0);  
  destruct(TcbMod.get b a0);
  tryfalse; substs; auto.

  pose proof tidspec.beq_false_neq t a0 eq1.
  pose proof tidspec.beq_false_neq t0 a0 eq2.
  rewrite TcbMod.get_sig_none; auto.
  rewrite TcbMod.get_sig_none in H2; auto.
  rewrite TcbMod.get_sig_none in H3; auto.
  rewrite TcbMod.get_sig_none in H4; auto.
  destruct(TcbMod.get x3 a0);
  destruct(TcbMod.get x1 a0);
  destruct(TcbMod.get c a0);  
  destruct(TcbMod.get b a0);
  tryfalse; substs; auto.
Qed.


Lemma tcbjoin_joinsig_eq:
  forall x y x1 z x2,
    TcbJoin x y x1 z ->
    TcbMod.joinsig x y x2 z -> x1 = x2. 
Proof.
  intros.
  apply TcbMod.extensionality.
  intro.
  pose proof H0 a.
  unfolds in H.
  pose proof H a.
  destruct(tidspec.beq x a) eqn : eq1.
  pose proof tidspec.beq_true_eq x a eq1; substs.
  rewrite TcbMod.get_sig_some in H2.
  rewrite TcbMod.get_sig_some in H1.
  destruct(TcbMod.get x2 a);
  destruct(TcbMod.get z a);
  destruct(TcbMod.get x1 a);
  tryfalse; auto.

  pose proof tidspec.beq_false_neq x a eq1; substs.
  rewrite TcbMod.get_sig_none in H2; auto.
  rewrite TcbMod.get_sig_none in H1; auto.
  destruct(TcbMod.get x2 a);
  destruct(TcbMod.get z a);
  destruct(TcbMod.get x1 a);
  tryfalse; substs; auto.
Qed.

Lemma tcbmod_sub_joinsig_sub:
  forall a b x y z y',
    TcbMod.sub a b -> 
    TcbMod.joinsig x y z a ->
    TcbMod.sub z (TcbMod.set b x y').
Proof.
  intros.
  unfolds.
  intro.
  unfolds in H.
  unfolds in H0.
  pose proof H0 a0.
  unfold TcbMod.lookup in *.
  destruct(tidspec.beq x a0) eqn : eq1.
  pose proof tidspec.beq_true_eq x a0 eq1; substs.
  rewrite TcbMod.get_sig_some in H1.
  destruct(TcbMod.get z a0) eqn : eq2;
  destruct(TcbMod.get a a0) eqn : eq3;
  tryfalse; substs; auto.
  rewrite TcbMod.set_a_get_a; auto.
  intros; tryfalse.
  intros.
  rewrite H2 in H1.
  pose proof tidspec.beq_false_neq x a0 eq1.
  rewrite TcbMod.get_sig_none in H1; auto.
  rewrite TcbMod.set_sem.
  rewrite eq1.
  destruct (TcbMod.get a a0) eqn: eq2; tryfalse.
  apply H; auto.
  substs; auto.
Qed.

  
Lemma tcb_minus_self_emp: forall x, TcbMod.minus x x = TcbMod.emp.
Proof.
  intros.
  apply TcbMod.extensionality.
  intros.
  rewrite TcbMod.emp_sem.
  rewrite TcbMod.minus_sem.
  destruct(TcbMod.get x a); auto.
Qed.


Lemma Prio_Not_In_ex :
  forall ll a x, 
    Prio_Not_In x (a::ll) ->
    Prio_Not_In x ll.
Proof.
  inductions ll.
  intros; simpl; auto.
  intros.
  simpl in H.
  simpl.
  mytac.
  eexists; splits;eauto.
Qed.


Lemma nth_vallist_inc_eq:
  forall n' a ll a0 l',
    0%nat <> n' ->
    (nth_vallist n' (a :: ll) = Some l' <->
    nth_vallist (S n') (a :: a0 :: ll) = Some l').
Proof.
  inductions n'.
  intros; tryfalse.
  intros.
  split;intros;
  simpl in H0;
  simpl;
  auto.
Qed.


Lemma tcbjoin_join_ex_join:
  forall x x2 x1 tcbls'' tcbx tcbls,
    TcbJoin x x2 x1 tcbls'' ->
    TcbMod.join tcbls'' tcbx tcbls ->
    exists y, TcbMod.join x1 tcbx y /\ TcbJoin x x2 y tcbls.
Proof.
  intros.
  unfold TcbJoin in *.
  unfold Maps.join in *.
  unfold Maps.sig in *.
  simpl in *.
  exists (TcbMod.minus tcbls (TcbMod.sig x x2)).
  split.
  unfolds; intro.
  pose proof H a.
  pose proof H0 a.
  rewrite TcbMod.minus_sem.
  destruct(tidspec.beq x a) eqn:eq1.
  pose proof tidspec.beq_true_eq x a eq1; substs.
  rewrite TcbMod.get_sig_some.
  rewrite TcbMod.get_sig_some in H1.
  destruct(TcbMod.get tcbls'' a);
  destruct(TcbMod.get tcbx a);
  destruct(TcbMod.get tcbls a);
  destruct(TcbMod.get x1 a);
  tryfalse; auto.

  pose proof tidspec.beq_false_neq x a eq1.
  rewrite TcbMod.get_sig_none; auto.
  rewrite TcbMod.get_sig_none in H1; auto.
  destruct(TcbMod.get tcbls'' a);
  destruct(TcbMod.get tcbx a);
  destruct(TcbMod.get tcbls a);
  destruct(TcbMod.get x1 a);
  tryfalse; substs; auto.

  unfolds; intro.
  pose proof H a.
  pose proof H0 a.
  rewrite TcbMod.minus_sem.
  destruct(tidspec.beq x a) eqn:eq1.
  pose proof tidspec.beq_true_eq x a eq1; substs.
  rewrite TcbMod.get_sig_some.
  rewrite TcbMod.get_sig_some in H1.
  destruct(TcbMod.get tcbls'' a);
  destruct(TcbMod.get tcbx a);
  destruct(TcbMod.get tcbls a);
  destruct(TcbMod.get x1 a);
  tryfalse; substs; auto.

  
  pose proof tidspec.beq_false_neq x a eq1.
  rewrite TcbMod.get_sig_none; auto.
  rewrite TcbMod.get_sig_none in H1; auto.
  destruct(TcbMod.get tcbls'' a);
  destruct(TcbMod.get tcbx a);
  destruct(TcbMod.get tcbls a);
  destruct(TcbMod.get x1 a);
  tryfalse; substs; auto.
Qed.



Lemma TCBList_P_nth_prio:
  forall l n l' (prio:priority) x0 x1 rtbl,
    nth_vallist n l = Some l' ->
    V_OSTCBPrio l' = Some (Vint32 prio) ->
    TCBList_P x0 l rtbl x1 ->
    exists tid st msg, TcbMod.get x1 tid = Some (prio,st,msg) .
Proof.
  inductions l.
  intros.
  simpl in H.
  tryfalse.
  intros.
  destruct n.
  simpl in H.
  inverts H.
  simpl in H1.
  mytac.
  unfolds in H3.
  destruct x4.
  destruct p.
  mytac.
  rewrite H0 in H3.
  inverts H3.
  apply tcbjoin_get_a in H2.
  eauto.
  simpl in H1.
  mytac.
  simpl in H.
  unfolds in H4.
  destruct x4.
  destruct p.
  mytac.
  lets Hsa : IHl H H0 H5.
  mytac.
  exists x0 x4 x5.
  eapply TcbMod.join_get_r;eauto.
Qed.

Ltac trans_back:=
  unfold TcbJoin in *;
  unfold Maps.join in *;
  unfold Maps.sig in *;
  simpl in *.
Lemma tcbjoin_get_none:
  forall x2 a x4 x1 x,
    TcbJoin x2 a x4 x1 ->
    TcbMod.get x1 x = None ->
    TcbMod.get x4 x = None.
Proof.
  intros.
  trans_back.
  pose proof H x.
  rewrite H0 in H1.
  destruct(TcbMod.get (TcbMod.sig x2 a) x); tryfalse;
  destruct(TcbMod.get x4 x); tryfalse.
  auto.
Qed.



Lemma TCBList_P_imp_Prio_Not_In:
  forall l tcbls x p t m x1 x0  rtbl,
    TcbMod.get tcbls x  = Some (p,t,m) ->
    TcbMod.get x1 x = None ->
    sub x1 tcbls ->
    R_Prio_No_Dup tcbls ->
    TCBList_P x0 l rtbl x1 ->
    Prio_Not_In p l.
Proof.  
  inductions l.
  intros; simpl; auto.
  intros.
  simpl.
  simpl in H3.
  mytac.
  lets Ha : tcbjoin_get_a  H5.
  unfolds in H6.
  destruct x5.
  destruct p0.
  mytac.
  lets Hsub : TcbMod.join_sub_r H5.
  
  lets Hs : IHl H H2 H7; auto.
  eapply  tcbjoin_get_none; eauto.
  eapply sub_trans;eauto.
  eexists; splits;eauto.
  assert (x = x2\/ x <>x2) by tauto.
  destruct H10.
  subst x.
  tryfalse.
  lets Hge : TcbMod.get_sub_get Ha H1.
  eapply H2; eauto.
Qed.



Lemma tcbjoin_get_n:
  forall x y x1 tcbls,
    TcbJoin x y x1 tcbls ->
    TcbMod.get x1 x =None.
Proof.
  intros.
  trans_back.
  pose proof H x.
  rewrite TcbMod.get_sig_some in H0.
  destruct(TcbMod.get x1 x); tryfalse.
  auto.
Qed.


Lemma int_eq_false_false:
  forall n,
    Int.eq Int.one n = false ->
    Int.eq n Int.zero = false ->
    Int.eq (n-ᵢInt.one) Int.zero = false.
Proof.
  intros.
  apply ltu_eq_false.
  unfolds.
  remember ( zlt (Int.unsigned Int.zero) (Int.unsigned (n-ᵢInt.one))) as Hx.
  destruct Hx; auto.
  int auto.
  assert (0<=Int.unsigned ($ (Int.unsigned n - 1))).
  apply Int.unsigned_range.
  assert (0=Int.unsigned ($ (Int.unsigned n - 1))) by omega.
  rewrite Int.unsigned_repr in H2.
  false.
  clear -n1 H2.
  omega.
  unfold Int.max_unsigned.
  simpl.
  clear -n1 n0.
  assert ( 0 <= Int.unsigned n <= Int.max_unsigned). 
  apply Int.unsigned_range_2.
  unfold Int.max_unsigned in H.
  simpl in H.
  omega.
Qed.



Lemma R_Prio_No_Dup_Convert :
  forall ll, R_Prio_No_Dup_L' ll -> R_Prio_No_Dup_L ll.
Proof.
  inductions ll; intros.
  unfolds in H; simpl in H.
  unfolds; auto.
  assert (R_Prio_No_Dup_L' ll).
  unfolds.
  intros.
  unfolds in H.
  assert (nth_vallist (S n) (a:: ll) = Some l).
  simpl; auto.
  apply H in H1.
  mytac.
  eexists; splits; eauto.
  simpl.
  unfolds in H.
  assert (nth_vallist O (a:: ll) = Some a).
  simpl; auto.
  apply H in H1.
  mytac.
  eexists; splits; eauto.
  apply IHll in H0.
  clear -H1 H2.
  inductions ll gen a.
  simpl; auto.
  simpl.
  assert (0 <>1)%nat.
  omega.
  assert ( nth_vallist 1 (a :: a0 :: ll) = Some a0)%nat.
  simpl; auto.
  lets Has : H2 H0; eauto.
  mytac.
  eexists; splits; eauto.
  lets Has : IHll H1 .
  eapply Has.
  intros.
  eapply H2 with (S n'); auto.
  apply nth_vallist_inc_eq; eauto.
Qed.


Lemma R_Prio_No_Dup_Convert_rev :
  forall ll, R_Prio_No_Dup_L ll -> R_Prio_No_Dup_L' ll.
Proof.
  inductions ll; intros.
  unfolds; auto.
  intros; simpl in *; tryfalse.
  simpl in H.
  mytac.
  unfolds.
  intros.
  destruct n.
  simpl in H2.
  inverts H2.
  eexists; splits; eauto.
  apply IHll in H1.
  unfolds in H1.
  clear -H0 H.
  inductions ll.
  intros.
  destruct n'; tryfalse.
  simpl in H0.
  intros.
  mytac.
  lets Hzs : IHll H; auto.  
  destruct n'.
  
  tryfalse.
  destruct n'.
  simpl in H2.
  inverts H2.
  eexists; splits; eauto.
  simpl in H2.
  assert ( nth_vallist (S n') (l :: ll) = Some l').
  simpl; auto.
  eapply Hzs with (S n'); eauto.

  simpl in H2.
  apply IHll in H1.
  unfolds in H1.
  lets Hxx  : H1  H2.
  mytac.
  eexists; splits; eauto.
  destruct n'.
  intros.
  simpl in H6.
  inverts H6.  
  clear -H0 H H2 H3.
  inductions ll.
  simpl in H2; tryfalse.
  simpl in H0.
  mytac.
  eexists; splits;eauto.
  destruct n.
  simpl in H2.
  inverts H2.
  rewrite H3 in H0.
  inverts H0.
  auto.
  simpl in H2.
  lets Has : IHll H4 H2 H3 H.
  mytac.
  rewrite H in H5.
  inverts H5.
  auto.
  intros.
  assert ( n<> n') by omega.
  eapply H4; eauto.
Qed.

Lemma  R_Prio_No_Dup_Eq :
  forall ll, R_Prio_No_Dup_L ll <-> R_Prio_No_Dup_L' ll.
Proof.
  intros; split; intros.
  apply R_Prio_No_Dup_Convert_rev; auto.
  apply R_Prio_No_Dup_Convert ; auto.
Qed.

Lemma R_Prio_No_Dup_Sub_hold:
  forall x3 tcbls,
    sub x3 tcbls ->
    R_Prio_No_Dup tcbls ->
    R_Prio_No_Dup x3.
Proof.
  introv Hsub Hr.
  unfolds in Hr.
  unfolds.
  intros.
  lets Hget1 : TcbMod.get_sub_get H0 Hsub.
  lets Hget2 : TcbMod.get_sub_get H1 Hsub.
  eapply Hr; eauto.
Qed.



  
Lemma r_prio_no_dup_join_imp:
  forall l tcbls'' tcbx tcbls v  rtbl,
    join tcbls'' tcbx tcbls ->
    R_Prio_No_Dup tcbls ->
    TCBList_P v l rtbl tcbls'' ->
    R_Prio_No_Dup_L l.
Proof.
  inductions l.
  simpl.
  intros.
  auto.
  intros.
  simpl in H1.
  mytac.
  simpl.
  unfolds in H4.
  destruct x2.
  destruct p.
  lets Hds :  tcbjoin_join_ex_join H3 H.
  mytac.
  lets Hsub : TcbMod.join_sub_r H6.
  lets Hrs : R_Prio_No_Dup_Sub_hold x2 H0; auto.
  lets Hxa : IHl H1 Hrs H5.
  eexists; splits; eauto.
  apply tcbjoin_get_a in H6.
  lets Hn :  tcbjoin_get_n H3.
  eapply  TCBList_P_imp_Prio_Not_In;eauto.
  eapply TcbMod.join_sub_l in H1.
  eapply TcbMod.sub_trans; eauto.
Qed.



Ltac solve_tblk :=
  unfolds; splits;
  try solve [unfolds; simpl; auto];
  try solve [do 6 eexists;splits; try unfolds; simpl;  eauto;  splits; eauto;
             eexists;split; [unfolds; simpl;eauto | auto]].

(*-------------should be fixed by zhanghui----------------*)
Lemma tickchange_eq_ostcbnext:
  forall l x0 rtbl rgrp head ectr l' rtbl' rgrp' ectr',
    V_OSTCBNext l = Some x0 ->
    tickchange_l l rtbl rgrp head ectr l' rtbl' rgrp' ectr' ->
    V_OSTCBNext l' = Some x0.
Proof.
  intros.
  inversion H0; substs; auto.
Qed.

Lemma joinsig_joinsig_neq :
  forall {a1 a2 x1 x2 m2 m2' m3},
    joinsig a1 x1 m2 m3 -> joinsig a2 x2 m2' m2 -> a1 <> a2.
Proof.
  intros.
  intro; substs.
  unfolds in H0.
  unfolds in H.
  pose proof H0 a2; pose proof H a2.
  rewrite get_sig_some in H2.
  rewrite get_sig_some in H1.
  destruct(get m2' a2);
    destruct(get m2 a2);
    destruct(get m3 a2);
    tryfalse.
Qed.

Lemma joinsig_joinsig_neq_ecb :
  forall {a1 a2 x1 x2 m2 m2' m3},
    EcbMod.joinsig a1 x1 m2 m3 -> EcbMod.joinsig a2 x2 m2' m2 -> a1 <> a2.
Proof.
  intros.
  intro; substs.
  unfolds in H0.
  unfolds in H.
  pose proof H0 a2; pose proof H a2.
  rewrite EcbMod.get_sig_some in H2.
  rewrite EcbMod.get_sig_some in H1.
  destruct(EcbMod.get m2' a2);
    destruct(EcbMod.get m2 a2);
    destruct(EcbMod.get m3 a2);
    tryfalse.
Qed.

Lemma neq_set_comm :
  forall a1 a2 x1 x2 m,
    a1 <> a2 -> set (set m a1 x1) a2 x2 = set (set m a2 x2) a1 x1.
Proof.
  intros.
  apply extensionality.
  intros.
  do 4 rewrite set_sem.
  destruct(tidspec.beq a1 a) eqn: eq1;
    destruct(tidspec.beq a2 a) eqn: eq2;
    auto.
  apply tidspec.beq_true_eq in eq1;
    apply tidspec.beq_true_eq in eq2;
    substs; tryfalse.  
Qed.

Lemma tickstep'_other_get_eq:
  forall x y  tcbls'' y' x3 tcbls' els' x1 tcbls,
    TcbJoin x y x1 tcbls'' ->
    tickstep' (set tcbls x y') x3 tcbls' els' x1 ->
    TcbMod.get tcbls' x = Some y'.
Proof.
  intros.
  gen y tcbls'' H.
  inductions H0.
  intros.
  unfolds in H.
  rewrite TcbMod.set_sem.
  rewrite tid_beq_true; auto.
  pose proof IHtickstep' x y' (TcbMod.set tcbls t (p, st', msg0)).
  intros.
  unfold TcbJoin in H3.
  assert(TcbMod.joinsig x y tls_used tcbls'') by auto; clear H3.
(*a candidate lemma for MapLib*)
  pose proof joinsig_joinsig_neq H4 H.  
  assert(set (set tcbls x y') t (p, st', msg0) = set (set tcbls t (p, st', msg0)) x y').
(*a candidate lemma for MapLib*)
  apply neq_set_comm; auto.
  pose proof H1 H5; clear H1.
  pose proof H6 y (TcbMod.minus tcbls'' (TcbMod.sig t (p, st, msg0))).
  apply H1.
  unfold TcbJoin.
  apply TcbMod.join_comm.
  eapply join_join_minus; eauto.
  unfolds in H4.
  apply TcbMod.join_comm; auto.
Qed.


Lemma tcb_joinsig_join_get_minus_eq:
  forall x y x1 tcbls'' tcbx tcbls y' tcbls',
    TcbJoin x y x1 tcbls'' ->
    TcbMod.join tcbls'' tcbx tcbls ->
    TcbMod.get tcbls' x = Some y' ->
    TcbJoin x y' (minus (minus tcbls' tcbx) (sig x y'))
            (minus tcbls' tcbx).
Proof.
  intros.
  trans_back.
  unfolds.
  unfold TcbMod.join; intros.
  unfolds in H.
  pose proof H a; pose proof H0 a.
  rewrite TcbMod.minus_sem.
  rewrite TcbMod.minus_sem.
  destruct(tidspec.beq x a) eqn : eq1.
  pose proof tidspec.beq_true_eq x a eq1; substs.
  rewrite TcbMod.get_sig_some in H2.
  rewrite TcbMod.get_sig_some.
  rewrite H1.
  destruct(TcbMod.get tcbls'' a);
  destruct(TcbMod.get tcbx a);
  destruct(TcbMod.get tcbls a);
  destruct(TcbMod.get x1 a);
  tryfalse; substs; auto.

  pose proof tidspec.beq_false_neq x a eq1.
  rewrite TcbMod.get_sig_none in H2; auto.
  rewrite TcbMod.get_sig_none; auto.
  destruct(TcbMod.get tcbls' a);
  destruct(TcbMod.get tcbls'' a);
  destruct(TcbMod.get tcbx a);
  destruct(TcbMod.get tcbls a);
  destruct(TcbMod.get x1 a);
  tryfalse; substs; auto.
Qed.

Lemma tcb_minus_mergesig_minus_minus_eq:
  forall tcbls' x y tcbx,
    TcbMod.minus tcbls' (TcbMod.merge (TcbMod.sig x y) tcbx) =
    TcbMod.minus (TcbMod.minus tcbls' tcbx) (TcbMod.sig x y).
Proof.
  intros.
  apply TcbMod.extensionality.
  intros.
  do 3 rewrite TcbMod.minus_sem.
  rewrite TcbMod.merge_sem.
  destruct (TcbMod.get tcbls' a);
  destruct (TcbMod.get (sig x y) a);
  destruct (get tcbx a); auto.  
Qed.

Lemma r_prio_no_dup_setst_hold:
  forall x p t m x1 tcbls'' tcbx tcbls x2,
    TcbJoin x (p, t, m) x1 tcbls'' -> 
    TcbMod.join tcbls'' tcbx tcbls ->
    R_Prio_No_Dup tcbls ->
    R_Prio_No_Dup (TcbMod.set tcbls x (p, x2, m)).
Proof.
  intros.
  unfolds; intros.
  destruct(tidspec.beq x tid) eqn: eq1;  
  destruct(tidspec.beq x tid') eqn : eq2.
  pose proof tidspec.beq_true_eq x tid eq1; substs.
  pose proof tidspec.beq_true_eq tid tid' eq2; substs.
  rewrite TcbMod.set_a_get_a in H3; auto; inverts H3.

  pose proof tidspec.beq_true_eq x tid eq1; substs.
  pose proof tidspec.beq_false_neq tid tid' eq2.
  rewrite TcbMod.set_a_get_a in H3; auto; inverts H3.
  rewrite TcbMod.set_a_get_a' in H4; auto.
  unfolds in H1.
  assert(TcbMod.get tcbls tid = Some (prio, t, m0)).
  apply TcbMod.join_comm in H0.
  unfolds in H.
  assert(TcbMod.joinsig tid (prio, t, m0) x1 tcbls'') by auto; clear H.
  eapply TcbMod.join_joinsig_get; eauto.
  eapply H1; eauto.

  pose proof tidspec.beq_true_eq x tid' eq2; substs.
  pose proof tidspec.beq_false_neq tid' tid eq1.
  rewrite TcbMod.set_a_get_a in H4; auto; inverts H4.
  rewrite TcbMod.set_a_get_a' in H3; auto.
  unfolds in H1.
  assert(TcbMod.get tcbls tid' = Some (prio', t, m')).
  apply TcbMod.join_comm in H0.
  unfolds in H.
  assert(TcbMod.joinsig tid' (prio', t, m') x1 tcbls'') by auto; clear H.
  eapply TcbMod.join_joinsig_get; eauto.
  clear H5.
  eapply H1; eauto.

  pose proof tidspec.beq_false_neq x tid' eq2.
  pose proof tidspec.beq_false_neq x tid eq1.
  rewrite TcbMod.set_a_get_a' in H4; auto.
  rewrite TcbMod.set_a_get_a' in H3; auto.
  unfolds in H1.
  clear H5 H6.
  eapply H1; eauto.
Qed.


Lemma joinsig_join_joinmergesig_eq_set:
  forall x y x1 tcbls'' tcbx tcbls y',
    TcbMod.joinsig x y x1 tcbls'' ->
    TcbMod.join tcbls'' tcbx tcbls ->
    TcbMod.join x1 (TcbMod.merge (TcbMod.sig x y') tcbx) (TcbMod.set tcbls x y').
Proof.
  intros.
  unfolds; intros.
  pose proof H a; pose proof H0 a.
  rewrite TcbMod.merge_sem.
  rewrite TcbMod.set_sem.
  destruct(tidspec.beq x a) eqn: eq1.
  pose proof tidspec.beq_true_eq x a eq1; substs.
  rewrite TcbMod.get_sig_some in H1.
  rewrite TcbMod.get_sig_some.
  destruct(TcbMod.get tcbls'' a);
  destruct(TcbMod.get tcbx a);
  destruct(TcbMod.get tcbls a);
  destruct(TcbMod.get x1 a);
  tryfalse; auto.
  
  pose proof tidspec.beq_false_neq x a eq1.
  rewrite TcbMod.get_sig_none; auto.
  rewrite TcbMod.get_sig_none in H1; auto.
  destruct(TcbMod.get tcbls'' a);
  destruct(TcbMod.get tcbx a);
  destruct(TcbMod.get tcbls a);
  destruct(TcbMod.get x1 a);
  tryfalse; substs; auto.
Qed.

Lemma tcb_minus_emp_eq: forall x, TcbMod.minus x TcbMod.emp = x.
Proof.
  intros.
  apply TcbMod.extensionality; intros.
  rewrite TcbMod.minus_sem.
  rewrite TcbMod.emp_sem.
  destruct(TcbMod.get x a); auto. 
Qed.


Lemma tickstep_l_get_last_tcb_ptr_eq':
  forall v'25 v'26 v'27 v'28 v'33 (v'39:int32) head els x1 x2 x3 (x6:int32) xx els' i1 i2,
    tickstep_l (v'25 ++ v'26 :: v'27) v'28 i1 head els
               (x1 ++ x2 :: x3) v'33 i2 els' ->
    length v'25 = length x1 ->
    get_last_tcb_ptr x1 xx = get_last_tcb_ptr v'25 xx.
Proof.
  inductions v'25; intros.
  destruct x1; simpl in H0; tryfalse.
  simpl; auto.
  
  destruct x1; simpl in H0; tryfalse.
  inversion H0.
  rewrite <- app_comm_cons in H.
  rewrite <- app_comm_cons in H.
  inversion H.
  substs.
  inversion H0.
  pose proof IHv'25 v'26 v'27 rtbl' v'33 v'39 head ectr' x1 x2 x3 x6 xx els' rgrp' i2 H14 H3.
  simpl.
  unfolds in H1.
  destruct x1; destruct v'25; simpl in H3; tryfalse.
  clear -H13.
  inversion H13; unfolds; substs; simpl; auto.
  auto.
Qed.

Lemma tickstep_l_get_last_tcb_ptr_eq:
  forall v'25 v'26 v'27 v'28 v'33 v'39 head els x1 x2 x3 x6 xx els',
    tickstep_l (v'25 ++ v'26 :: v'27) v'28 (Vint32 v'39) head els
               (x1 ++ x2 :: x3) v'33 (Vint32 x6) els' ->
    length v'25 = length x1 ->
    get_last_tcb_ptr x1 xx = get_last_tcb_ptr v'25 xx.
Proof.
  intros.
  eapply tickstep_l_get_last_tcb_ptr_eq'; eauto.
Qed.

(* tcbls_rtbl_timetci_update <-> tickstep_l*)

Lemma tcbls_rtbl_timetci_update_tls_eq_next:
  forall v'25 v'28 v'29 x1 x4 x5 head els els',
    tcbls_rtbl_timetci_update v'25 v'28 v'29 head els = Some (x1, x4, x5,els') ->
    eq_next v'25 x1.
Proof.
  induction v'25.
  intros.
  simpl in H;inverts H;auto.
  simpl;auto.
  intros.
  simpl in H.
  xunfold H.
  simpl;symmetry in Htick;apply IHv'25 in Htick;auto.
  simpl;symmetry in Htick;apply IHv'25 in Htick;auto.
  simpl;symmetry in Htick;apply IHv'25 in Htick;auto.
  simpl;symmetry in Htick;apply IHv'25 in Htick;auto.
Qed.

Lemma tcbls_rtbl_timetci_update_tls_link:
  forall v'25 v'15 v'23 v'28 v'29 x1 x4 x5 head els els',
    v'25 = nil /\ Vptr v'15 = Vptr v'23 \/
                  (exists vl,
                     v'25 <> nil /\ last v'25 nil = vl /\ nth_val 0 vl = Some (Vptr v'15)) ->
    tcbls_rtbl_timetci_update v'25 v'28 v'29 head els = Some (x1, x4, x5,els') ->
    x1 = nil /\ Vptr v'15 = Vptr v'23 \/
                (exists vl,
                   x1 <> nil /\ last x1 nil = vl /\ nth_val 0 vl = Some (Vptr v'15)).
Proof.
  intros.
  apply tcbls_rtbl_timetci_update_tls_eq_next in H0.
  destruct H.
  left;mytac;auto.
  simpl in H0.
  destruct x1;tryfalse;auto.
  right.
  mytac.
  eexists;splits;eauto.
  intro.
  destruct H.
  subst.
  clear -H0.
  destruct v'25;simpl in *;auto;tryfalse.
  clear -H0 H2.
  gen v'25 v'15 x1 H0 H2.
  induction v'25.
  intros.
  simpl in H2.
  tryfalse.
  intros.
  simpl in H0.
  destruct x1;tryfalse.
  destruct H0.
  simpl in H2.
  simpl.
  destruct v'25.
  simpl in H0.
  destruct x1;tryfalse.
  rewrite H in H2;auto.
  eapply IHv'25 in H2;eauto.
  destruct x1.
  simpl in H2;tryfalse.
  auto.
Qed.

Lemma tcbls_rtbl_timetci_update_tls_split:
  forall v'25 v'15 v'23 v'28 v'29 x1 x4 x5 v'32 x2 x3 s P head els els',
    v'25 = nil /\ Vptr v'15 = Vptr v'23 \/
                  (exists vl,
                     v'25 <> nil /\ last v'25 nil = vl /\ nth_val 0 vl = Some (Vptr v'15)) ->
    tcbls_rtbl_timetci_update v'25 v'28 v'29 head els = Some (x1, x4, x5,els') ->
    s |= tcbdllseg (Vptr v'23) Vnull v'32 Vnull (x1 ++ x2 :: x3) ** P ->
    s |= EX x, tcbdllseg (Vptr v'23) Vnull x (Vptr v'15) x1 **
                         tcbdllseg (Vptr v'15) x v'32 Vnull (x2::x3) ** P.
Proof.
  intros.
  eapply tcbls_rtbl_timetci_update_tls_link in H0;eauto.
  clear H.
  destruct H0.
  mytac;subst.
  inverts H0.
  simpl List.app in H1.
  unfold tcbdllseg at 1.
  simpl dllseg at 1.
  sep auto.
  mytac.
  apply tcbdllseg_split in H1.
  sep auto.
  destruct H0;mytac;tryfalse.
  rewrite H2 in e;inverts e.
  sep auto.
Qed.
  


Lemma tcbls_rtbl_timetci_update_rgrp_vint:
  forall a b c a' b' c' d e e',
    tcbls_rtbl_timetci_update a b (Vint32 c) d e= Some (a',b',c',e') ->
    exists x, c' = Vint32 x.
Proof.
  inductions a.
  simpl.
  intros.
  inverts H.
  eexists ; eauto.
  intros.
  unfold  tcbls_rtbl_timetci_update in H.
  fold  tcbls_rtbl_timetci_update in H.
  repeat progress  match goal with
                     | H : context [match ?a with | _ => _  end = Some _] |- _ => destruct a; tryfalse
                   end.
  unfold add_option_first in H.
  remember (tcbls_rtbl_timetci_update a0 b (Vint32 c) d e) as y.
  destruct y; tryfalse.
  fsimpl.
  eapply IHa; eauto.
  unfold add_option_first in H.
  remember ( tcbls_rtbl_timetci_update a0 l (Vint32 i5) d e) as y.
  destruct y; tryfalse.
  fsimpl.
  eapply IHa; eauto.
  unfold add_option_first in H.
  remember ( tcbls_rtbl_timetci_update a0 l (Vint32 i5) d l0 ) as y.
  destruct y; tryfalse.
  fsimpl.
  eapply IHa; eauto.
  unfold add_option_first in H.
  remember ( tcbls_rtbl_timetci_update a0 b (Vint32 c) d e  ) as y.
  destruct y; tryfalse.
  fsimpl.
  eapply IHa; eauto.
Qed.



Lemma tick_fixpoint_convert:
  forall vl x y head els vl' x' y' els',
    tcbls_rtbl_timetci_update vl x y head els = Some (vl', x', y', els') ->
    tickstep_l vl x y head els vl' x' y' els'.
Proof.
  inductions vl.
  simpl.
  intros.
  inverts H.
  constructors.
  intros.
  simpl in H.
  do 18  match goal with
           | H : context [match ?a with | _ => _  end = Some _] |- _ => destruct a; tryfalse
         end.
  remember ( Int.eq i Int.zero) as Hi.
  destruct Hi.
  unfolds in H.
  remember ( tcbls_rtbl_timetci_update vl x y head els) as Hx.
  destruct Hx; tryfalse.
  fsimpl.
  apply eq_sym in HeqHx.
  apply eq_sym in HeqHi.
  apply IHvl in HeqHx.
  constructors;eauto.
  eapply     rdy_change_l; eauto.
  remember (Int.eq (i-ᵢInt.one) Int.zero) as Hy.
  remember (set_rdy_grp (Vint32 i4) y ) as Hz.
  destruct Hy.
  destruct Hz; tryfalse.
  destruct v4; tryfalse.
  remember (nth_val (Z.to_nat (Int.unsigned i2)) x ) as Ht.
  destruct Ht; tryfalse.
  remember (or v4 (Vint32 i3) ) as Hk.
  destruct Hk; tryfalse.
  destruct v1; tryfalse.
  unfold add_option_first in H.
  remember ( tcbls_rtbl_timetci_update vl
                                       (update_nth_val (Z.to_nat (Int.unsigned i2)) x v5) 
                                       (Vint32 i5) head els) as Ha.
  destruct Ha; tryfalse.
  fsimpl.
  constructors; eauto.
  eapply wait_rdy_change_l; eauto.
  unfolds.
  rewrite <- HeqHt.
  unfold  bop_eval .
  rewrite <-  HeqHk.
  auto.
  remember ( tick_rdy_ectr
               (v
                  :: v0
                  :: Vptr a
                  :: v2
                  :: Vint32 i
                  :: v3
                  :: Vint32 i0
                  :: Vint32 i1
                  :: Vint32 i2 :: Vint32 i3 :: Vint32 i4 :: nil)
               head els) as Has.
  destruct Has; tryfalse.
  unfold add_option_first in H.
  remember (tcbls_rtbl_timetci_update vl
                                      (update_nth_val (Z.to_nat (Int.unsigned i2)) x v5) 
                                      (Vint32 i5) head l) as Hck.
  destruct Hck; tryfalse.
  fsimpl.
  constructors; eauto.
  eapply waite_rdy_change_l ; eauto.
  unfolds.
  rewrite <- HeqHt.
  unfold  bop_eval .
  rewrite <-  HeqHk.
  auto.
  unfold add_option_first in H.
  remember ( tcbls_rtbl_timetci_update vl x y head els) as Hck.
  destruct Hck; tryfalse.
  fsimpl.
  constructors; eauto.
  eapply wait_change_l; eauto.
Qed.

Lemma tick_fixpoint_convert_rev:
  forall vl x y head els vl' x' y' els',
    tickstep_l vl x y head els vl' x' y' els' ->
    tcbls_rtbl_timetci_update vl x y head els = Some (vl', x', y', els').
Proof.
  intros.
  inductions H.
  simpl.
  auto.
  simpl.
  inverts H.
  rewrite H2.
  unfold    add_option_first.
  remember (tcbls_rtbl_timetci_update ll rtbl' rgrp' head ectr' ) as Hx.
  destruct Hx.
  destruct p.
  destruct p.
  destruct p.
  inverts   IHtickstep_l.
  auto.
  tryfalse.
  rewrite H2.
  rewrite H3.
  unfold    add_option_first.
  remember (tcbls_rtbl_timetci_update ll rtbl' rgrp' head ectr' ) as Hx.
  destruct Hx; tryfalse.
  destruct p.
  destruct p.
  destruct p.
  inverts   IHtickstep_l.
  auto.
  rewrite H2.
  rewrite H3.
  rewrite H6.
  unfolds in H6.
  unfolds in H6.
  unfolds in H7.
  remember (nth_val (Z.to_nat (Int.unsigned vy)) rtbl ) as Hd.
  destruct Hd; tryfalse.
  unfold  bop_eval in H7.
  remember ( or v (Vint32 vbitx) ) as Hds.
  destruct Hds; tryfalse.
  unfold  or in H6.
  destruct rgrp;tryfalse.
  inverts H6.
  inverts H7.
  unfold   add_option_first.
  remember (tcbls_rtbl_timetci_update ll
                                      (update_nth_val (Z.to_nat (Int.unsigned vy)) rtbl v0)
                                      (Vint32 (Int.or i vbity)) head ectr') as Hr.
  destruct Hr; tryfalse.
  destruct p.
  destruct p.
  destruct p.
  inverts   IHtickstep_l; auto.
  rewrite H2.
  rewrite H3.
  rewrite H6.
  unfolds in H6.
  unfolds in H6.
  unfolds in H7.
  unfolds in H6.
  destruct rgrp; tryfalse.
  inverts H6.
  remember (nth_val (Z.to_nat (Int.unsigned vy)) rtbl) as Ht.
  destruct Ht; tryfalse.
  unfold bop_eval in H7.
  remember (or v (Vint32 vbitx)) as Hor.
  destruct Hor; tryfalse.
  inverts H7.
  rewrite H8.
  unfold  add_option_first.
  remember (tcbls_rtbl_timetci_update ll
                                      (update_nth_val (Z.to_nat (Int.unsigned vy)) rtbl v0)
                                      (Vint32 (Int.or i vbity)) head ectr') as Hr.
  destruct Hr; tryfalse.
  do 3 destruct p.
  inverts   IHtickstep_l; auto.
Qed.



Lemma tcbls_rtbl_timetci_update_len_eq':
  forall v'24 v'27 v'39 v'40 x1 x4 x5 x6 i,
    tcbls_rtbl_timetci_update v'24 v'27 i v'39 v'40 =
    Some (x1, x4, x5, x6) ->
    length v'24 = length x1.
Proof.
  intros.
  apply tick_fixpoint_convert in H.
  inductions v'24; intros.
  destruct x1; auto.
  inversion H.

  destruct x1.
  inversion H.
  inversion H; substs.
  simpl.
  apply eq_S.
  eapply IHv'24; eauto.
Qed.

Lemma tcbls_rtbl_timetci_update_len_eq:
  forall v'24 v'27 v'38 v'39 v'40 x1 x4 x5 x6,
    tcbls_rtbl_timetci_update v'24 v'27 (Vint32 v'38) v'39 v'40 =
    Some (x1, x4, x5, x6) ->
    length v'24 = length x1.
Proof.
  intros.
  eapply tcbls_rtbl_timetci_update_len_eq'; eauto.
Qed.





Lemma tickchange_shift :
  forall t t' a els b els' c d els'',
    t <> t' ->
    tickchange t a els b els' ->
    tickchange t' c els' d els'' ->
    exists x,  tickchange t' c els d x /\ tickchange t a x b els''.
Proof.
  intros.
  inductions H0.
  exists els''.
  splits; auto.
  eapply     rdy_change ; eauto.
  exists els''.
  splits; eauto.
  eapply wait_change ; eauto.
  eexists.
  splits; eauto.
  eapply wait_rdy_change ; eauto.
  eexists.
  splits; eauto.
  eapply  waite_change; eauto.
  subst.
  inverts H5.
  exists els.
  splits; auto.
  eapply rdy_change; eauto.
  eapply waite_rdy_change; eauto.
  exists els.
  splits.
  eapply wait_change ; eauto.
  eapply waite_rdy_change; eauto.
  eexists els.
  splits.
  eapply wait_rdy_change; auto.
  eapply waite_rdy_change; eauto.
  exists els.
  splits.
  eapply  waite_change; eauto.
  apply   waite_rdy_change with (eid := eid) (m:=m) (wl := wl) (x:=x); eauto.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H2.
  subst.
  rewrite EcbMod.set_sem in H6.
  rewrite tidspec.eq_beq_true in H6; auto.
  inverts H6.
  exists (EcbMod.set els eid0 (m0,remove_tid t' wl)).
  splits.
  apply   waite_rdy_change with (eid := eid0) (m:=m0) (wl := wl) (x:=x0); eauto.
  rewrite  remove_tid_eq .
  eapply  waite_rdy_change with (wl := remove_tid t' wl); eauto.
  rewrite EcbMod.set_sem.
  rewrite tidspec.eq_beq_true;  auto.
  apply  ecbmod_set_eq.
  rewrite EcbMod.set_sem in H6.
  rewrite tidspec.neq_beq_false in H6; auto.
  exists (EcbMod.set els eid0 (m0,remove_tid t' wl0)).
  splits.
  apply   waite_rdy_change with (eid := eid0) (m:=m0) (wl := wl0) (x:=x0); eauto.
  rewrite   ecbmod_set_neq_change; auto.
  eapply   waite_rdy_change with (x:=x)(m:=m)(wl:=wl); eauto.
  rewrite EcbMod.set_sem.  
  rewrite tidspec.neq_beq_false; auto.
Qed.

(*-----------------------should be proven by zhanghui-------------------------*)
(*a lemma for MapLib*)
Lemma join_join_merge :
  forall m1 m2 m3 m4 m5,
    join m1 m2 m3 -> join m4 m5 m1 -> join m4 (merge m5 m2) m3.
Proof.
  intros.
  unfolds; intros.
  pose proof H a.
  pose proof H0 a.
  rewrite merge_sem.
  destruct(get m1 a);
  destruct(get m2 a);
  destruct(get m3 a);
  destruct(get m4 a);
  destruct(get m5 a);
  tryfalse; substs; auto.
Qed.

Lemma join_join_merge' :
  forall m1 m2 m3 m4 m5,
    join m1 m2 m3 -> join m4 m5 m1 -> join m4 (merge m2 m5) m3.
Proof.
  intros.
  unfolds; intros.
  pose proof H a.
  pose proof H0 a.
  rewrite merge_sem.
  destruct(get m1 a);
  destruct(get m2 a);
  destruct(get m3 a);
  destruct(get m4 a);
  destruct(get m5 a);
  tryfalse; substs; auto.
Qed.

Lemma join_join_merge_ecb :
  forall m1 m2 m3 m4 m5,
    EcbMod.join m1 m2 m3 -> EcbMod.join m4 m5 m1 -> EcbMod.join m4 (EcbMod.merge m5 m2) m3.
Proof.
  intros.
  unfolds; intros.
  pose proof H a.
  pose proof H0 a.
  rewrite EcbMod.merge_sem.
  destruct(EcbMod.get m1 a);
  destruct(EcbMod.get m2 a);
  destruct(EcbMod.get m3 a);
  destruct(EcbMod.get m4 a);
  destruct(EcbMod.get m5 a);
  tryfalse; substs; auto.
Qed.

Lemma join_join_merge'_ecb :
  forall m1 m2 m3 m4 m5,
    EcbMod.join m1 m2 m3 -> EcbMod.join m4 m5 m1 -> EcbMod.join m4 (EcbMod.merge m2 m5) m3.
Proof.
  intros.
  unfolds; intros.
  pose proof H a.
  pose proof H0 a.
  rewrite EcbMod.merge_sem.
  destruct(EcbMod.get m1 a);
  destruct(EcbMod.get m2 a);
  destruct(EcbMod.get m3 a);
  destruct(EcbMod.get m4 a);
  destruct(EcbMod.get m5 a);
  tryfalse; substs; auto.
Qed.


Lemma tcb_join_joinsig_ex_joinsig:
  forall htls'' tcbx htls x y x1,
    join htls'' tcbx htls ->
    joinsig x y x1 htls'' ->
    exists z, joinsig x y z htls.
Proof.
  intros.
  exists (TcbMod.merge x1 tcbx).
  unfolds in H0.
  eapply join_join_merge; eauto.
Qed.
 

Lemma nth_vallist_append : forall l1 l2 n x, nth_vallist n l1 = Some x -> nth_vallist n (l1++l2) = Some x.
Proof.
  inductions l1; intros.
  simpl in H; tryfalse.
  destruct n.
  simpl in H; inverts H.
  simpl; auto.
  simpl in H.
  eapply IHl1 in H.
  simpl; eauto.
Qed.

Lemma Prio_Not_In_app :
  forall l2 l3 x,
    Prio_Not_In x (l2 ++ l3) ->  Prio_Not_In x l2.
Proof.
  inductions l2; intros.
  simpl; auto.
  rewrite <- app_comm_cons in H.
  simpl in H; mytac.
  apply IHl2 in H1.
  simpl.
  exists x0.
  auto.
Qed.

Lemma R_Prio_No_Dup_L_proc : forall a l, R_Prio_No_Dup_L (a::l) -> R_Prio_No_Dup_L (l).
Proof.
  intros.
  unfolds in H.
  unfolds; intros; mytac.
  auto.
Qed.

Lemma r_prio_no_dup_l_mid:
  forall l1 l2 l3,
    R_Prio_No_Dup_L (l1++l2++l3) ->
    R_Prio_No_Dup_L l2.
Proof.
  inductions l1; intros.
  simpl in H.
  gen l3.
  inductions l2; intros.
  unfolds; intros; auto.
  rewrite <- app_comm_cons in H.
  unfolds in H; mytac.
  unfolds; intros.
  exists x; split; auto.
  split; auto.
  eapply Prio_Not_In_app; eauto.
  
  apply IHl2 in H1.
  auto.
  
  rewrite <- app_comm_cons in H.
  apply R_Prio_No_Dup_L_proc in H.
  eapply IHl1; eauto.
Qed. 


Lemma tcbjoin_set:
  forall (x:addrval) y y' htls1 htls,
    TcbJoin x y htls1 htls ->
    TcbJoin x y' htls1 (set htls x y').
Proof.
  intros.
  trans_back.
  unfolds; intros.
  pose proof H a.
  rewrite TcbMod.set_sem.
  destruct (tidspec.beq x a) eqn: eq1.
  pose proof tidspec.beq_true_eq x a eq1; substs.
  rewrite TcbMod.get_sig_some in H0.
  rewrite TcbMod.get_sig_some.
  destruct (TcbMod.get htls1 a);
  destruct (TcbMod.get htls a);
  tryfalse; auto.  
  pose proof tidspec.beq_false_neq x a eq1.
  rewrite TcbMod.get_sig_none; auto.
  rewrite TcbMod.get_sig_none in H0; auto.
Qed.

(*a lemma for MapLib*)
Lemma joinsig_eq : forall x y1 y2 m1 m2 m3, joinsig x y1 m1 m3 -> joinsig x y2 m2 m3 -> y1 = y2.  
Proof.
  intros.
  pose proof H x.
  pose proof H0 x.
  rewrite get_sig_some in H1.
  rewrite get_sig_some in H2.
  destruct (get m1 x);
  destruct (get m2 x);
  tryfalse.
  destruct (get m3 x) eqn : eq1; tryfalse.
  substs; auto.
Qed.


Lemma join_tcbjoin_joinsig_eq'
: forall (x : tidspec.A) (y1 y2 : abstcb.B) (x1 z  x2 : map),
    TcbJoin x y1 x1 z -> joinsig x y2 x2 z-> y1 = y2.
Proof.
  intros.
  unfolds in H.
  assert(TcbMod.joinsig x y1 x1 z) by auto.
  eapply joinsig_eq; eauto.
Qed.



Lemma V_OSTCBNext_set_tcb_next :
  forall v x1 x2, V_OSTCBNext v = Some x1 -> exists x', set_tcb_next v x2 = Some x'.
Proof.
  intros.
  destruct v; tryfalse.
  unfolds in H; simpl in H; inverts H.
  unfold set_tcb_next.
  simpl; eauto.
Qed.

Lemma set_nth_nth_val :
  forall n l x l', set_nth n x l = Some l' -> nth_val n l' = Some x.
Proof.
  inductions n; intros.
  simpl in H.
  destruct l; tryfalse.
  inverts H.
  simpl; auto.
  
  destruct l'.
  destruct l; simpl in H; tryfalse.
  destruct (set_nth n x l) eqn : eq1; tryfalse.
  
  destruct l.
  simpl in H; tryfalse.
  simpl.
  simpl in H.
  destruct(set_nth n x l) eqn : eq1; tryfalse.
  inverts H.
  apply IHn in eq1; auto.
Qed.

Lemma set_nth_nth_val' :
  forall l l' n1 n2 x, n1 <> n2 -> set_nth n1 x l = Some l' -> nth_val n2 l' = nth_val n2 l.
Proof.
  inductions l; intros.
  unfold set_nth in H0.
  destruct n1; tryfalse.
  
  destruct l'.
  destruct n1.
  simpl in H0; tryfalse.
  simpl in H0.
  destruct (set_nth n1 x l); tryfalse.
  destruct n1.
  simpl in H0; inverts H0.
  destruct n2; tryfalse.
  simpl; auto.
  simpl in H0.
  destruct (set_nth n1 x l) eqn : eq1; tryfalse.
  inverts H0.
  destruct n2.
  simpl; auto.
  simpl.
  assert (n1 <> n2).
  omega.
  eapply IHl; eauto.
Qed.

Lemma TCBNode_P_change_next_ptr :
  forall vl vl' rtbl abstcb x,
    TCBNode_P vl rtbl abstcb -> set_tcb_next vl x = Some vl' ->
    TCBNode_P vl' rtbl abstcb.
Proof.
  intros.
  unfolds in H; unfolds.
  destruct abstcb; destruct p. 
  unfolds RL_TCBblk_P.
  unfolds R_TCB_Status_P.
  unfolds RLH_RdyI_P.
  unfolds RHL_RdyI_P.
  unfolds RLH_TCB_Status_Wait_P.
  unfolds RHL_TCB_Status_Wait_P.
  unfolds RLH_Wait_P.
  unfolds RLH_WaitS_P.
  unfolds RLH_WaitQ_P.
  unfolds RLH_WaitMB_P.
  unfolds RLH_WaitMS_P.
  unfolds RHL_Wait_P.
  unfolds RHL_WaitS_P.
  unfolds RHL_WaitQ_P.
  unfolds RHL_WaitMB_P.
  unfolds RHL_WaitMS_P.
  unfolds WaitTCBblk.

  Lemma V_OSTCBMsg_change_next_ptr :
    forall vl vl' a x,
      V_OSTCBMsg vl = Some a -> set_tcb_next vl x = Some vl' ->
      V_OSTCBMsg vl' = Some a.
  Proof.
    intros.
    unfolds in H; unfolds; unfolds in H0.
    pose proof set_nth_nth_val' vl vl' 0%nat 3%nat x.
    rewrite <- H1 in H; auto.
  Qed.
  
  Lemma V_OSTCBPrio_change_next_ptr :
    forall vl vl' a x,
      V_OSTCBPrio vl = Some a -> set_tcb_next vl x = Some vl' ->
      V_OSTCBPrio vl' = Some a.
  Proof.
    intros.
    unfolds in H; unfolds; unfolds in H0.
    pose proof set_nth_nth_val' vl vl' 0%nat 6%nat x.
    rewrite <- H1 in H; auto.
  Qed.
  
  Lemma V_OSTCBX_change_next_ptr :
    forall vl vl' a x,
      V_OSTCBX vl = Some a -> set_tcb_next vl x = Some vl' ->
      V_OSTCBX vl' = Some a.
  Proof.
    intros.
    unfolds in H; unfolds; unfolds in H0.
    pose proof set_nth_nth_val' vl vl' 0%nat 7%nat x.
    rewrite <- H1 in H; auto.
  Qed.
      
  Lemma V_OSTCBY_change_next_ptr :
    forall vl vl' a x,
      V_OSTCBY vl = Some a -> set_tcb_next vl x = Some vl' ->
      V_OSTCBY vl' = Some a.
  Proof.
    intros.
    unfolds in H; unfolds; unfolds in H0.
    pose proof set_nth_nth_val' vl vl' 0%nat 8%nat x.
    rewrite <- H1 in H; auto.
  Qed.

  Lemma V_OSTCBBitX_change_next_ptr :
    forall vl vl' a x,
      V_OSTCBBitX vl = Some a -> set_tcb_next vl x = Some vl' ->
      V_OSTCBBitX vl' = Some a.
  Proof.
    intros.
    unfolds in H; unfolds; unfolds in H0.
    pose proof set_nth_nth_val' vl vl' 0%nat 9%nat x.
    rewrite <- H1 in H; auto.
  Qed.
      
  Lemma V_OSTCBBitY_change_next_ptr :
    forall vl vl' a x,
      V_OSTCBBitY vl = Some a -> set_tcb_next vl x = Some vl' ->
      V_OSTCBBitY vl' = Some a.
  Proof.
    intros.
    unfolds in H; unfolds; unfolds in H0.
    pose proof set_nth_nth_val' vl vl' 0%nat 10%nat x.
    rewrite <- H1 in H; auto.
  Qed.
  
  Lemma V_OSTCBStat_change_next_ptr :
    forall vl vl' a x,
      V_OSTCBStat vl = Some a -> set_tcb_next vl x = Some vl' ->
      V_OSTCBStat vl' = Some a.
  Proof.
    intros.
    unfolds in H; unfolds; unfolds in H0.
    pose proof set_nth_nth_val' vl vl' 0%nat 5%nat x.
    rewrite <- H1 in H; auto.
  Qed.
  
  Lemma V_OSTCBEventPtr_change_next_ptr :
    forall vl vl' a x,
      V_OSTCBEventPtr vl = Some a -> set_tcb_next vl x = Some vl' ->
      V_OSTCBEventPtr vl' = Some a.
  Proof.
    intros.
    unfolds in H; unfolds; unfolds in H0.
    pose proof set_nth_nth_val' vl vl' 0%nat 2%nat x.
    rewrite <- H1 in H; auto.
  Qed.

  Lemma V_OSTCBDly_change_next_ptr :
    forall vl vl' a x,
      V_OSTCBDly vl = Some a -> set_tcb_next vl x = Some vl' ->
      V_OSTCBDly vl' = Some a.
  Proof.
    intros.
    unfolds in H; unfolds; unfolds in H0.
    pose proof set_nth_nth_val' vl vl' 0%nat 4%nat x.
    rewrite <- H1 in H; auto.
  Qed.
  
  Lemma V_OSTCBPrio_change_next_ptr' :
    forall vl vl' prio x,
      V_OSTCBPrio vl' = Some prio -> set_tcb_next vl x = Some vl' ->
      V_OSTCBPrio vl = Some prio.
  Proof.
    intros.
    unfolds in H; unfolds; unfolds in H0.
    pose proof set_nth_nth_val' vl vl' 0%nat 6%nat x.
    rewrite H1 in H; auto.
  Qed.

  Lemma V_OSTCBDly_change_next_ptr' :
    forall vl vl' a x, 
      V_OSTCBDly vl' = Some a -> set_tcb_next vl x = Some vl' ->
      V_OSTCBDly vl = Some a.
  Proof.
    intros.
    unfolds in H; unfolds; unfolds in H0.
    pose proof set_nth_nth_val' vl vl' 0%nat 4%nat x.
    rewrite H1 in H; auto.
  Qed.
  
  Lemma V_OSTCBStat_change_next_ptr' :
    forall vl vl' a x,
      V_OSTCBStat vl' = Some a -> set_tcb_next vl x = Some vl' ->
      V_OSTCBStat vl = Some a.
  Proof.
    intros.
    unfolds in H; unfolds; unfolds in H0.
    pose proof set_nth_nth_val' vl vl' 0%nat 5%nat x.
    rewrite H1 in H; auto.
  Qed.

  Lemma V_OSTCBEventPtr_change_next_ptr' :
    forall vl vl' a x,
      V_OSTCBEventPtr vl' = Some a -> set_tcb_next vl x = Some vl' ->
      V_OSTCBEventPtr vl = Some a.
  Proof.
    intros.
    unfolds in H; unfolds; unfolds in H0.
    pose proof set_nth_nth_val' vl vl' 0%nat 2%nat x.
    rewrite H1 in H; auto.
  Qed.
  
  mytac.
  
  eapply V_OSTCBMsg_change_next_ptr; eauto.
  eapply V_OSTCBPrio_change_next_ptr; eauto.
  do 6 eexists.
  mytac; eauto.
  eapply V_OSTCBPrio_change_next_ptr; eauto.
  eapply V_OSTCBX_change_next_ptr; eauto.
  eapply V_OSTCBY_change_next_ptr; eauto.
  eapply V_OSTCBBitX_change_next_ptr; eauto.
  eapply V_OSTCBBitY_change_next_ptr; eauto.
  eapply V_OSTCBStat_change_next_ptr; eauto.
  eexists; split; eauto.
  eapply V_OSTCBEventPtr_change_next_ptr; eauto.
  
  intros.
  assert(RdyTCBblk vl rtbl prio).
  
  Lemma RdyTCBblk_change_next_ptr :
    forall vl x vl' rtbl prio,
      RdyTCBblk vl rtbl prio -> set_tcb_next vl x = Some vl' -> RdyTCBblk vl' rtbl prio.
  Proof.
    intros.
    unfolds in H; unfolds.
    mytac; auto.
    unfolds in H0; unfolds; unfolds in H.
    pose proof set_nth_nth_val' vl vl' 0%nat 6%nat x.
    rewrite <- H2 in H; auto.
  Qed.
  
  Lemma RdyTCBblk_change_next_ptr' :
    forall vl x vl' rtbl prio,
      RdyTCBblk vl' rtbl prio -> set_tcb_next vl x = Some vl' -> RdyTCBblk vl rtbl prio.
  Proof.
    intros.
    unfolds in H; unfolds.
    mytac; auto.
    unfolds in H0; unfolds; unfolds in H.
    pose proof set_nth_nth_val' vl vl' 0%nat 6%nat x.
    rewrite H2 in H; auto.
  Qed.
  
  eapply RdyTCBblk_change_next_ptr'; eauto.
  apply H3 in H22.
  clear - H0 H22.
  mytac.
  eapply V_OSTCBStat_change_next_ptr; eauto.
  eapply V_OSTCBDly_change_next_ptr; eauto.
  eauto.
      
  intros.
  apply H4 in H21; clear - H0 H21.
  mytac.
  eapply RdyTCBblk_change_next_ptr; eauto.
  eapply V_OSTCBStat_change_next_ptr; eauto.
  eapply V_OSTCBDly_change_next_ptr; eauto.

  intros.
  assert(V_OSTCBPrio vl = Some (Vint32 prio) /\
         prio_not_in_tbl prio rtbl /\ V_OSTCBDly vl = Some (Vint32 t0)).
  clear - H21 H0.
  mytac.
  
  eapply V_OSTCBPrio_change_next_ptr'; eauto.
  auto.
  eapply V_OSTCBDly_change_next_ptr'; eauto.
  assert(V_OSTCBStat vl = Some (V$OS_STAT_RDY)).
  eapply V_OSTCBStat_change_next_ptr'; eauto.
  clear - H23 H24 H0 H5.
  eapply H5 in H24; eauto.
  
  intros.
  assert( V_OSTCBPrio vl = Some (Vint32 prio) /\
          prio_not_in_tbl prio rtbl /\ V_OSTCBDly vl = Some (Vint32 t0)).
  clear - H21 H0.
  mytac; auto.
  eapply V_OSTCBPrio_change_next_ptr'; eauto.
  eapply V_OSTCBDly_change_next_ptr'; eauto.
  assert(V_OSTCBStat vl = Some (V$OS_STAT_SEM)).
  eapply V_OSTCBStat_change_next_ptr'; eauto.
  assert(V_OSTCBEventPtr vl = Some (Vptr eid)).
  eapply V_OSTCBEventPtr_change_next_ptr'; eauto.
  clear - H24 H29 H30 H11 H0.
  eapply H11 in H24; eauto.

  intros.
  assert(V_OSTCBPrio vl = Some (Vint32 prio) /\
         prio_not_in_tbl prio rtbl /\ V_OSTCBDly vl = Some (Vint32 t0)).
  clear - H21 H0.
  mytac; auto.
  eapply V_OSTCBPrio_change_next_ptr'; eauto.
  eapply V_OSTCBDly_change_next_ptr'; eauto.
  assert(V_OSTCBStat vl = Some (V$OS_STAT_Q)).
  eapply V_OSTCBStat_change_next_ptr'; eauto.
  assert(V_OSTCBEventPtr vl = Some (Vptr eid)).
  eapply V_OSTCBEventPtr_change_next_ptr'; eauto.
  clear - H24 H29 H30 H12 H0.
  eapply H12 in H24; eauto.

  intros.
  assert(V_OSTCBPrio vl = Some (Vint32 prio) /\
         prio_not_in_tbl prio rtbl /\ V_OSTCBDly vl = Some (Vint32 t0)).
  clear - H21 H0.
  mytac; auto.
  eapply V_OSTCBPrio_change_next_ptr'; eauto.
  eapply V_OSTCBDly_change_next_ptr'; eauto.
  assert(V_OSTCBStat vl = Some (V$OS_STAT_MBOX)).
  eapply V_OSTCBStat_change_next_ptr'; eauto.
  assert(V_OSTCBEventPtr vl = Some (Vptr eid)).
  eapply V_OSTCBEventPtr_change_next_ptr'; eauto.
  clear - H24 H29 H30 H13 H0.
  eapply H13 in H24; eauto.
  
  intros.
  assert(V_OSTCBPrio vl = Some (Vint32 prio) /\
         prio_not_in_tbl prio rtbl /\ V_OSTCBDly vl = Some (Vint32 t0)).
  clear - H21 H0.
  mytac; auto.
  eapply V_OSTCBPrio_change_next_ptr'; eauto.
  eapply V_OSTCBDly_change_next_ptr'; eauto.
  assert(V_OSTCBStat vl = Some (V$OS_STAT_MUTEX)).
  eapply V_OSTCBStat_change_next_ptr'; eauto.
  assert(V_OSTCBEventPtr vl = Some (Vptr eid)).
  eapply V_OSTCBEventPtr_change_next_ptr'; eauto.
  clear - H24 H29 H30 H14 H0.
  eapply H14 in H24; eauto.
  
  intros.
  apply H6 in H21; clear - H21 H0.
  mytac; auto.
  eapply V_OSTCBPrio_change_next_ptr; eauto.
  eapply V_OSTCBDly_change_next_ptr; eauto.
  eapply V_OSTCBStat_change_next_ptr; eauto.
  
  intros.
  apply H7 in H21; clear - H21 H0.
  mytac; auto.
  eapply V_OSTCBPrio_change_next_ptr; eauto.
  eapply V_OSTCBDly_change_next_ptr; eauto.
  eapply V_OSTCBEventPtr_change_next_ptr; eauto.
  eapply V_OSTCBStat_change_next_ptr; eauto.
  
  intros.
  apply H8 in H21; clear - H21 H0.
  mytac; auto.
  eapply V_OSTCBPrio_change_next_ptr; eauto.
  eapply V_OSTCBDly_change_next_ptr; eauto.
  eapply V_OSTCBEventPtr_change_next_ptr; eauto.
  eapply V_OSTCBStat_change_next_ptr; eauto.

  intros.
  apply H9 in H21; clear - H21 H0.
  mytac; auto.
  eapply V_OSTCBPrio_change_next_ptr; eauto.
  eapply V_OSTCBDly_change_next_ptr; eauto.
  eapply V_OSTCBEventPtr_change_next_ptr; eauto.
  eapply V_OSTCBStat_change_next_ptr; eauto.

  intros.
  apply H10 in H21; clear - H21 H0.
  mytac; auto.
  eapply V_OSTCBPrio_change_next_ptr; eauto.
  eapply V_OSTCBDly_change_next_ptr; eauto.
  eapply V_OSTCBEventPtr_change_next_ptr; eauto.
  eapply V_OSTCBStat_change_next_ptr; eauto.
Qed.


Lemma TCBList_P_not_in_remove_last :
  forall l head rtbl htls,
    TCBList_P head l rtbl htls -> not_in head (removelast l) V_OSTCBNext.
Proof.
  destruct l.
  simpl; auto.

  gen v.
  inductions l; intros.
  simpl; auto.

  simpl in H; mytac.
  
  pose proof V_OSTCBNext_set_tcb_next v (Vptr x3) x4 H0; mytac.
  
  pose proof IHl x0 (Vptr x) rtbl (TcbMod.minus htls (TcbMod.sig x3 x6)).
  change(not_in (Vptr x) (v :: removelast (a :: l)) V_OSTCBNext).
  assert(TCBList_P (Vptr x) (x0 :: l) rtbl (minus htls (sig x3 x6))).
  simpl.
  exists x x4 x5 x2.
  split; auto.
  split.
  
  unfolds in H.
  unfolds.
  eapply set_nth_nth_val; eauto.

  split.
  clear - H1 H5.
  unfolds in H1; unfolds in H5.
  apply TcbMod.join_comm in H1.
  unfolds; apply TcbMod.join_comm.
  eapply join_join_minus; eauto.

  split; auto.
  
  eapply TCBNode_P_change_next_ptr; eauto.
  apply H3 in H8; clear H3.
  simpl; mytac.
  intros.
  intro; substs.
  rewrite H0 in H3; inverts H3.
  unfolds in H1.
  assert(TcbMod.joinsig x x2 x1 htls) by auto.
  unfolds in H5.
  assert(TcbMod.joinsig x x6 x5 x1) by auto.
  pose proof joinsig_joinsig_neq H3 H9; tryfalse.
  simpl in H8.
  destruct l; auto.
  simpl in H8.
  simpl.
  mytac; auto.
  intros.
  clear H8.
  apply H3.
  unfolds.
  eapply set_nth_nth_val.
  rewrite H4 in H9; inverts H9.
  unfolds in H; eauto.
Qed.

Lemma get_last_tcb_ptr_in :
  forall l a head x,
    get_last_tcb_ptr (a::l) head = Some x -> ~ (not_in x (a::l) V_OSTCBNext).
Proof.
  inductions l; intros.
  intro.
  simpl in H.
  simpl in H0; mytac.
  apply H0 in H; tryfalse.

  assert(get_last_tcb_ptr (a :: l) head = Some x).
  simpl in H.
  simpl; auto.
  apply IHl in H0.
  intro.
  apply H0.
  simpl in H1; mytac.
  simpl; mytac; auto.
Qed.

Lemma not_in_remove_last :
  forall {A B:Type} l1 l2 (a:A) (x:B) f,
    not_in x (removelast (l1 ++ a :: l2)) f -> not_in x l1 f.
Proof.
  inductions l1; intros.
  simpl; auto.

  rewrite <- app_comm_cons in H.
  simpl removelast in H.
  destruct(l1 ++ a0 :: l2) eqn : eq1.
  destruct l1; tryfalse. 
  simpl in H; mytac.
  pose proof IHl1 l2 a0 x f.
  assert(not_in x (removelast (l1 ++ a0 :: l2)) f).
  rewrite eq1; auto.
  apply H1 in H2.
  simpl; mytac; auto.
Qed.

Lemma tcblist_p_tid_neq':
  forall ltlsy'' a a1 h x l rtbl htls,
    get_last_tcb_ptr (a :: ltlsy'') h = Some (Vptr x) -> TCBList_P h ((a :: ltlsy'') ++ (a1::l)) rtbl htls ->
    h <> Vptr x.
Proof.
  intros.  
  apply get_last_tcb_ptr_in in H.
  apply TCBList_P_not_in_remove_last in H0.
  intro; substs.
  apply not_in_remove_last in H0.
  tryfalse.
Qed.

      
(*lemma for MapLib*)
Lemma joinsig_emp : forall m a x, joinsig a x emp m -> m = sig a x.
Proof.
  intros.
  apply extensionality; intros.
  pose proof H a0.
  rewrite emp_sem in H0.
  destruct(get (sig a x) a0); destruct(get m a0); tryfalse; substs; auto. 
Qed.

(*lemma for MapLib*)
Lemma join_sig_false : forall a x1 x2 m, join (sig a x1) (sig a x2) m -> False.
Proof.
  intros.
  pose proof H a.
  do 2 rewrite get_sig_some in H0.
  auto.
Qed.


(*lemma for MapLib*)
Lemma join_sig_neq_set : forall a x m1 m2 a1 x1, a <> a1 -> joinsig a x m1 m2 -> joinsig a x (set m1 a1 x1) (set m2 a1 x1).
Proof.
  intros.
  unfolds; intro.
  pose proof H0 a0.
  destruct (tidspec.beq a a0) eqn : eq1.
  pose proof tidspec.beq_true_eq a a0 eq1; substs.
  rewrite get_sig_some.
  rewrite get_sig_some in H1.
  rewrite set_sem.
  assert(a1<>a0) by auto.
  apply tidspec.neq_beq_false in H2.
  rewrite H2.
  rewrite set_sem.
  rewrite H2.
  auto.

  pose proof tidspec.beq_false_neq a a0 eq1.
  rewrite get_sig_none; auto.
  rewrite get_sig_none in H1; auto.
  do 2 rewrite set_sem.
  destruct (tidspec.beq a1 a0) eqn : eq2; auto.
Qed.

Lemma tcbjoin_neq:
  forall x x0 x6 x5 htls y,
    Vptr x <> Vptr x0 ->
    TcbJoin x0 x6 x5 htls ->
    TcbJoin x0 x6 (set x5 x y) (set htls x y).
Proof.
  intros.
  trans_back.
  eapply join_sig_neq_set; auto.
  intro; substs.
  tryfalse.
Qed.


Lemma r_prio_no_dup_two_neq:
  forall a l l1 l2 ll,
    R_Prio_No_Dup_L ((a :: l1) ++ (l :: ll) ++ l2) ->
    V_OSTCBPrio a <> V_OSTCBPrio l.
Proof.
  intros.

  rewrite <- app_comm_cons in H.
  simpl in H; mytac.
  gen a l l2 ll x.
  inductions l1; intros.
  rewrite app_nil_l in H0.
  simpl in H0; mytac.
  intro Hx; inverts Hx.
  rewrite H5 in H.
  rewrite H in H0; inverts H0.
  tryfalse.
  rewrite <- app_comm_cons in H1; simpl in H1; mytac.
  rewrite <- app_comm_cons in H0; simpl in H0; mytac.
  eapply IHl1; eauto.
Qed.

(*two lemmas for MapLib*)
Lemma joinsig_in_other :
  forall m1 m2 m3 a1 x1 a2 x2, a1 <> a2 -> joinsig a1 x1 m1 m3 -> joinsig a2 x2 m2 m3 -> get m2 a1 = Some x1.
Proof.
  intros.
  pose proof H1 a1.
  pose proof H0 a1.
  rewrite get_sig_some in H3.
  rewrite get_sig_none in H2; auto.
  destruct (get m1 a1);
    destruct (get m2 a1);
    destruct (get m3 a1);
    tryfalse; substs; auto.
Qed.

Lemma joinsig_get_minus : forall a x m, get m a = Some x -> joinsig a x (minus m (sig a x)) m.
Proof.
  unfold joinsig.
  unfolds join.
  intros.
  rewrite minus_sem.
  destruct (tidspec.beq a a0) eqn: eq1; tryfalse.
  pose proof tidspec.beq_true_eq a a0 eq1; substs.
  rewrite get_sig_some.
  rewrite H; auto.

  pose proof tidspec.beq_false_neq a a0 eq1; auto.
  rewrite get_sig_none; auto.
  destruct(get m a0); auto.
Qed.

Lemma tcb_neq_joinsig_tcbjoin_joinsig_minus:
  forall x0 x y htls'' htls x5 x4,
    Vptr x0 <> Vptr x ->
    joinsig x y htls'' htls ->
    TcbJoin x0 x5 x4 htls ->
    joinsig x y (minus x4 (sig x y)) x4.
Proof.
  intros.
  trans_back.
  assert (get x4 x = Some y).
  eapply joinsig_in_other; eauto.
  intro; substs.
  tryfalse.
  
  eapply joinsig_get_minus; auto.
Qed.


    
(*-----------------------------------*)

Lemma get_last_ecb_ptr_eq:
  forall head x9 x0 x6 x2 htls eid,
    ECBList_P head (Vptr x9) x0 x6 x2 htls ->
    get_last_ecb_ptr x0 head = Some (Vptr eid) ->
    x9 = eid.
Proof. 
  intros.
  gen head x9 x6 x2 htls eid.
  inductions x0; intros.
  simpl in H0; inverts H0.
  simpl in H; mytac.
  inverts H1; auto.

  destruct x6.
  simpl in H; mytac; tryfalse.
  simpl in H; mytac; destruct a; mytac.
  simpl in H0.
  eapply IHx0; eauto.
  unfolds.
  destruct x0; auto.
  simpl in H0.
  rewrite H in H0; auto.
Qed.

Lemma ECBList_P_get_last_ecb_ptr:
  forall {l1 l2 m1 m2 head x},
  ECBList_P head (Vptr x) l1 l2 m1 m2 ->
    get_last_ecb_ptr l1 head = Some (Vptr x).
Proof.
  inductions l1; intros.
  simpl in H; mytac.
  simpl; auto.
  destruct l2.
  simpl in H; mytac; tryfalse.
  simpl in H; mytac; destruct a; mytac.
  apply IHl1 in H3.
  simpl.
  destruct l1.
  simpl.
  simpl in H3; inverts H3; auto.
  simpl; simpl in H3; auto.
Qed.

Lemma ECBList_P_get_last_ecb_ptr_split_joinsig:
  forall l1 l2 l3 m1 m2 e a head tail,
    ECBList_P head tail (l1 ++ e :: l2) l3 m1 m2  ->
    get_last_ecb_ptr l1 head = Some (Vptr a) ->
    exists m11 m12 mx x, EcbMod.join m11 m12 m1 /\ EcbMod.joinsig a x mx m12.
Proof.
  inductions l1; intros.
  simpl in H0; inverts H0.
  rewrite app_nil_l in H.
  simpl in H; mytac.
  destruct l3; tryfalse; destruct e; mytac.
  exists EcbMod.emp m1 x1 x0.
  split.
  apply EcbMod.join_emp; auto.
  inverts H; auto.
  
  destruct a.
  destruct l1.
  simpl in H0.
  rewrite <- app_comm_cons in H.
  rewrite app_nil_l in H.
  simpl in H; mytac.
  destruct l3; tryfalse; mytac.
  destruct l3; tryfalse; mytac.
  destruct e; mytac.
  rewrite H0 in H; inverts H.
  clear - H2 H6.
  unfolds in H2.
  do 4 eexists; eauto.
  
  rewrite <- app_comm_cons in H.
  unfold ECBList_P in H; fold ECBList_P in H.
  mytac.
  destruct l3; tryfalse.
  mytac.
  assert(get_last_ecb_ptr (e0 :: l1) x2 = Some (Vptr a0)).
  simpl in H0.
  simpl; auto.
  lets _H: IHl1 H4 H5; mytac.
  clear - H2 H6 H7.
  unfolds in H2.
  exists ( (EcbMod.sig x x0)) x1 (EcbMod.merge x3 x5) x6.
  split; auto.
  clear H2; clears.
  unfolds; unfolds; intros.
  rewrite EcbMod.merge_sem.
  pose proof H6 a; pose proof H7 a.
  destruct(tidspec.beq a0 a) eqn : eq1.
  pose proof tidspec.beq_true_eq a0 a eq1; substs.
  rewrite EcbMod.get_sig_some in H0.
  rewrite EcbMod.get_sig_some.
  destruct(EcbMod.get x3 a);
    destruct(EcbMod.get x4 a);
    destruct(EcbMod.get x1 a);
    destruct(EcbMod.get x5 a);
    tryfalse; substs; auto.
  pose proof tidspec.beq_false_neq a0 a eq1.
  rewrite EcbMod.get_sig_none in H0; auto.
  rewrite EcbMod.get_sig_none; auto.
  destruct(EcbMod.get x3 a);
    destruct(EcbMod.get x4 a);
    destruct(EcbMod.get x1 a);
    destruct(EcbMod.get x5 a);
    tryfalse; substs; auto.
Qed.


(*lemma for MapLib*)

Lemma join_join_merge_1_ecb :
  forall m1 m2 m3 m4 m5,
    EcbMod.join m1 m2 m3 -> EcbMod.join m4 m5 m2 ->
    EcbMod.join m1 m4 (EcbMod.merge m1 m4).
Proof.
  intros.
  unfold EcbMod.join; intro.
  rewrite EcbMod.merge_sem.
  pose proof H a; pose proof H0 a.
  destruct(EcbMod.get m1 a);
    destruct(EcbMod.get m2 a);
    destruct(EcbMod.get m3 a);
    destruct(EcbMod.get m4 a);
    destruct(EcbMod.get m5 a);
    tryfalse; auto.
Qed.




Lemma ECBList_P_els_get_split :
  forall {els edata head tail tcbls hels m wl eptr},
    ECBList_P head tail els edata hels tcbls ->
    EcbMod.get hels eptr = Some (m, wl) ->
    exists els1 els2 edata1 edata2 hels1 hels2,
      ECBList_P head (Vptr eptr) els1 edata1 hels1 tcbls /\
      ECBList_P (Vptr eptr) tail els2 edata2 hels2 tcbls /\
      els = els1 ++ els2 /\ edata = edata1 ++ edata2 /\
      EcbMod.join hels1 hels2 hels.
Proof.
  inductions els; intros.
  simpl in H; mytac.
  rewrite EcbMod.emp_sem in H0; tryfalse.
  
  destruct edata.
  simpl in H; mytac; tryfalse.
  assert(ECBList_P head tail (a :: els) (e :: edata) hels tcbls) as Hx by auto.
  simpl in H; mytac; destruct a; mytac.
  destruct(tidspec.beq x eptr) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  exists (nil:(list EventCtr)) ((v, v0) :: els) (nil:(list EventData)) (e :: edata) EcbMod.emp hels.
  simpl; mytac; auto.
  apply EcbMod.join_emp; auto.
  assert(EcbMod.get x1 eptr = Some (m, wl)).
  clear - eq1 H2 H0.
  pose proof tidspec.beq_false_neq _ _ eq1.
  pose proof H2 eptr.
  rewrite EcbMod.get_sig_none in H1; auto.
  rewrite H0 in H1.
  destruct (EcbMod.get x1 eptr); tryfalse.
  substs; auto.
  
  pose proof IHels edata x2 tail tcbls x1 m wl eptr H4 H5; clear IHels.
  mytac.
  exists ((v, v0) :: x3) x4 (e::x5) x6 (EcbMod.merge (EcbMod.sig x x0) x7) x8.
  mytac; auto.
  simpl; exists x.
  mytac; auto.
  exists x0 x7 x2.
  mytac; auto.
  clear - H2 H10.
  unfolds in H2.
  unfolds.
  
  eapply join_join_merge_1_ecb; eauto.
  clear - H2 H10.
  apply EcbMod.join_comm in H2.
  apply EcbMod.join_comm in H10.
  apply EcbMod.join_comm.
  eapply join_join_merge'_ecb; eauto.
Qed.

Lemma ECBList_P_vptr :
  forall l1 l2 m1 m2 head tail a,
    ECBList_P head tail (a::l1) l2 m1 m2 ->
    (exists x, head = Vptr x).
Proof.
  intros.
  destruct l2.
  simpl in H; mytac; tryfalse.
  simpl in H; mytac; destruct a; mytac.
  eauto.
Qed.

Lemma ECBList_P_get_eidls_not_in :
  forall {l1 l2 l3 m1 m2 e x h  head tail},
    ECBList_P head tail (((h::l1)++e::nil)++l2) l3 m1 m2 ->
    get_last_ecb_ptr (h::l1) head = Some x ->
    ~In x (get_eidls head (h::l1)).
Proof.
  inductions l1; intros.
  destruct h.
  simpl in H0; inverts H0.
  destruct l3.
  simpl in H; mytac; tryfalse.
  simpl in H; mytac.
  rewrite H2 in H1; inverts H1.
  destruct l3; tryfalse.
  destruct e; mytac.
  intro.
  simpl in H8; destruct H8; tryfalse.
  inverts H8.
  pose proof joinsig_joinsig_neq_ecb H3 H1; tryfalse.

  unfold get_eidls.
  do 2 rewrite <- app_comm_cons in H.
  destruct l3.
  simpl in H; mytac; tryfalse.
  unfold ECBList_P in H; fold ECBList_P in H; mytac; destruct h; mytac.
  assert(exists x, x3 = Vptr x).
  
  rewrite <- list_cons_assoc in H4.
  eapply ECBList_P_vptr; eauto.
  destruct H5; substs.

  assert(get_last_ecb_ptr (a :: l1) (Vptr x4) = Some x).
  simpl.
  simpl in H0.
  auto.
  pose proof IHl1 l2 l3 x2 m2 e x a (Vptr x4) tail H4 H5.
  intro; apply H6.
  assert(x <> Vptr x0).
  assert(x = Vptr x0).
  clear - H6 H7 H.
  unfold get_eid_ecbls in H7.
  unfolds in H.
  apply nth_val_nth_val'_some_eq in H.
  rewrite H in H7.
  simpl in H7; destruct H7; auto.
  false; apply H6.
  simpl.
  destruct a.
  unfold In in H0.
  auto.
  substs.
  false.

  clear - H4 H5 H2.
  rewrite <- list_cons_assoc in H4.
  
  
  lets _H: ECBList_P_get_last_ecb_ptr_split_joinsig H4 H5; mytac.
  clear - H2 H H0.
  pose proof H2 x0; pose proof H0 x0.
  rewrite EcbMod.get_sig_some in H3.
  rewrite EcbMod.get_sig_some in H1.
  pose proof H x0.
  destruct(EcbMod.get x2 x0);
    destruct(EcbMod.get m1 x0);
    destruct(EcbMod.get x3 x0);
    destruct(EcbMod.get x x0);
    destruct(EcbMod.get x5 x0);
    tryfalse.
  
  remember (a::l1) as xxx.
  
  unfold In in H7; destruct H7.
  substs; tryfalse.
  unfold In.
  unfold get_eidls.
  unfold get_eid_ecbls in H7; fold get_eid_ecbls in H7.
  unfold V_OSEventListPtr in H.
  apply nth_val_nth_val'_some_eq in H.
  rewrite H in H7.
  destruct l1; substs.
  unfold get_eid_ecbls in H7; destruct a.
  unfold removelast in H7.
  destruct H7; tryfalse.
  left; auto.
  unfold get_eid_ecbls in H7; fold get_eid_ecbls in H7.
  destruct e1; destruct a.
  unfold removelast in H7; fold removelast in H7.
  unfold get_eid_ecbls; fold get_eid_ecbls.
  unfold removelast.
  auto.
Qed.


Lemma ecblist_p_compose':
  forall  p qid mqls qptrl1 qptrl2 i i1 a x3 p' v'41 
          msgqls1 msgqls2 msgq mqls1 mqls2 mq mqls' tcbls x,
    R_ECB_ETbl_P qid
                 (x
                    :: Vint32 i ::  i1 ::  a :: x3 :: p' :: nil, v'41) tcbls ->
    ECBList_P p (Vptr qid) qptrl1 msgqls1 mqls1 tcbls->
    ECBList_P p' Vnull qptrl2 msgqls2 mqls2 tcbls->
    RLH_ECBData_P msgq mq ->
    EcbMod.joinsig qid mq mqls2 mqls'->
    EcbMod.join mqls1 mqls' mqls ->
    ECBList_P p Vnull (qptrl1 ++ ((x
                                     :: Vint32 i :: i1 :: a :: x3 :: p' :: nil, v'41)::nil) ++ qptrl2) (msgqls1 ++ (msgq::nil) ++msgqls2) mqls tcbls.
Proof.
  intros.
  simpl.
  eapply ecblist_p_compose; eauto.
  simpl.
  eexists; splits; eauto.
  do 3 eexists; splits; eauto.
  unfolds; simpl; auto.
Qed.

Lemma ecbmod_get_joinsig_join_eq:
  forall eid x1' x1 x2 x3 x4 hels,
    EcbMod.get hels eid = Some x1' ->
    EcbMod.joinsig eid x1 x2 x4 ->
    EcbMod.join x3 x4 hels ->
    x1 = x1'.
Proof.
  intros.
  pose proof H0 eid.
  pose proof H1 eid.
  rewrite H in H3.
  rewrite EcbMod.get_sig_some in H2.
  destruct (EcbMod.get x2 eid); tryfalse.
  destruct (EcbMod.get x3 eid); tryfalse.
  destruct (EcbMod.get x4 eid); tryfalse.
  destruct (EcbMod.get x4 eid); tryfalse.
  substs; auto.
Qed.
(*part3*)

Lemma ECBList_P_Set_Rdy_SEM_hold:
  forall a tcbls tid prio  msg msg'  x y  b c eid nl,
    TcbMod.get tcbls tid =  Some (prio, wait (os_stat_sem eid) nl, msg) ->
    EcbMod.get c eid = None ->
    ECBList_P x y a b c tcbls ->
    ECBList_P x y a b c (TcbMod.set tcbls tid (prio,rdy,msg')).
Proof.
  inductions a; intros.
  simpl in *; auto.
  simpl in H1.
  mytac.
  destruct b; tryfalse.
  destruct a.
  mytac.
  simpl.
  eexists.
  splits; eauto.
  unfolds.
  unfolds in H2.

  splits.
  
  destructs H2.
  unfolds in H2.
  mytac.
  unfolds.
  splits; unfolds;intros.

  apply H2 in H11.
  apply H11 in H12.
  mytac.
  assert (tid = x3 \/ tid <> x3) by tauto.
  destruct H13.
  subst tid.
  unfold Maps.get in *.
  simpl in *.
  rewrite H12 in H.
  inverts H.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  exists x3 x4 x5.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.
  
  
  apply H8 in H11.
  apply H11 in H12.
  mytac.
  assert (tid = x3 \/ tid <> x3) by tauto.
  destruct H13.
  subst tid.
  unfold Maps.get in *;simpl in *.
  rewrite H12 in H.
  inverts H.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  exists x3 x4 x5.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.

  
  apply H9 in H11.
  apply H11 in H12.
  mytac.
  assert (tid = x3 \/ tid <> x3) by tauto.
  destruct H13.
  subst tid.
  unfold Maps.get in *;simpl in *.
  rewrite H12 in H.
  inverts H.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  exists x3 x4 x5.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.

  
  apply H10 in H11.
  apply H11 in H12.
  mytac.
  assert (tid = x3 \/ tid <> x3) by tauto.
  destruct H13.
  subst tid.
  unfold Maps.get in *;simpl in *.
  rewrite H12 in H.
  inverts H.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  exists x3 x4 x5.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.



  
  unfolds.
  destructs H2;unfolds in H6;destructs H6.
  splits;intros prio' mg ng x3 Hti;
  assert (tid = x3
          \/ tid <> x3) by tauto.
  {
    destruct H11.
    subst tid.
    rewrite TcbMod.set_sem in Hti.
    rewrite tidspec.eq_beq_true in Hti; auto.
    inverts Hti.
    rewrite TcbMod.set_sem in Hti.
    rewrite tidspec.neq_beq_false in Hti; auto.
    eapply H6; eauto.
  }
    
  (* rewrite tidspec.neq_beq_false in Hti; auto. *)
  (* rewrite H in Hti. *)
  (* inverts Hti. *)
  (* apply ecbmod_joinsig_get in H3. *)
  (* rewrite tidspec.eq_beq_true in Hti; auto. *)
  (* inverts Hti. *)
  (* rewrite TcbMod.set_sem in Hti. *)
  (* rewrite tidspec.neq_beq_false in Hti; auto. *)
  (* eapply H6; eauto. *)

  destruct H11.
  subst tid.
  rewrite TcbMod.set_sem in Hti.
  (* rewrite tidspec.neq_beq_false in Hti; auto. *)
  (* rewrite H in Hti. *)
  (* inverts Hti. *)
  (* apply ecbmod_joinsig_get in H3. *)
  (* tryfalse. *)
  rewrite tidspec.eq_beq_true in Hti; auto.
  inverts Hti.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  eapply H8; eauto.

  destruct H11.
  subst tid.
  rewrite TcbMod.set_sem in Hti.
  (* rewrite tidspec.neq_beq_false in Hti; auto. *)
  (* rewrite H in Hti. *)
  (* inverts Hti. *)
  (* apply ecbmod_joinsig_get in H3. *)
  (* tryfalse. *)
  rewrite tidspec.eq_beq_true in Hti; auto.
  inverts Hti.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  eapply H9; eauto.

  destruct H11.
  subst tid.
  rewrite TcbMod.set_sem in Hti.
  (* rewrite tidspec.neq_beq_false in Hti; auto. *)
  (* rewrite H in Hti. *)
  (* inverts Hti. *)
  (* apply ecbmod_joinsig_get in H3. *)
  (* tryfalse. *)
  rewrite tidspec.eq_beq_true in Hti; auto.
  inverts Hti.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  eapply H10; eauto.

  mytac;auto.


  do 3 eexists; splits; eauto.
  eapply IHa; eauto.
  eapply ecbmod_joinsig_get_none; eauto.
Qed.



Lemma ECBList_P_Set_Rdy_MBOX_hold:
  forall a tcbls tid prio  msg msg'  x y  b c eid nl,
    TcbMod.get tcbls tid =  Some (prio, wait (os_stat_mbox eid) nl, msg) ->
    EcbMod.get c eid = None ->
    ECBList_P x y a b c tcbls ->
    ECBList_P x y a b c (TcbMod.set tcbls tid (prio,rdy,msg')).
Proof.
  inductions a; intros.
  simpl in *; auto.
  simpl in H1.
  mytac.
  destruct b; tryfalse.
  destruct a.
  mytac.
  simpl.
  eexists.
  splits; eauto.
  unfolds.
  unfolds in H2.

  splits.
  
  destructs H2.
  unfolds in H2.
  mytac.
  unfolds.
  splits; unfolds;intros.

  apply H2 in H11.
  apply H11 in H12.
  mytac.
  assert (tid = x3 \/ tid <> x3) by tauto.
  destruct H13.
  subst tid.
  unfold Maps.get in *;simpl in *.
  rewrite H12 in H.
  inverts H.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  exists x3 x4 x5.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.
  
  
  apply H8 in H11.
  apply H11 in H12.
  mytac.
  assert (tid = x3 \/ tid <> x3) by tauto.
  destruct H13.
  subst tid.
  unfold Maps.get in *;simpl in *.
  rewrite H12 in H.
  inverts H.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  exists x3 x4 x5.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.

  
  apply H9 in H11.
  apply H11 in H12.
  mytac.
  assert (tid = x3 \/ tid <> x3) by tauto.
  destruct H13.
  subst tid.
  unfold Maps.get in *;simpl in *.
  rewrite H12 in H.
  inverts H.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  exists x3 x4 x5.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.

  
  apply H10 in H11.
  apply H11 in H12.
  mytac.
  assert (tid = x3 \/ tid <> x3) by tauto.
  destruct H13.
  subst tid.
  unfold Maps.get in *;simpl in *.
  rewrite H12 in H.
  inverts H.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  exists x3 x4 x5.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.

  unfolds.
  destructs H2;unfolds in H6;destructs H6.
  splits;intros prio' mg ng x3 Hti;
  assert (tid = x3
          \/ tid <> x3) by tauto.
  destruct H11.
  subst tid.
  rewrite TcbMod.set_sem in Hti.
  (* rewrite tidspec.neq_beq_false in Hti; auto. *)
  (* rewrite H in Hti. *)
  (* inverts Hti. *)
  (* apply ecbmod_joinsig_get in H3. *)
  (* tryfalse. *)
  rewrite tidspec.eq_beq_true in Hti; auto.
  inverts Hti.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  eapply H6; eauto.

  destruct H11.
  subst tid.
  rewrite TcbMod.set_sem in Hti.
  (* rewrite tidspec.neq_beq_false in Hti; auto. *)
  (* rewrite H in Hti. *)
  (* inverts Hti. *)
  (* apply ecbmod_joinsig_get in H3. *)
  (* tryfalse. *)
  rewrite tidspec.eq_beq_true in Hti; auto.
  inverts Hti.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  eapply H8; eauto.

  destruct H11.
  subst tid.
  rewrite TcbMod.set_sem in Hti.
  (* rewrite tidspec.neq_beq_false in Hti; auto. *)
  (* rewrite H in Hti. *)
  (* inverts Hti. *)
  (* apply ecbmod_joinsig_get in H3. *)
  (* tryfalse. *)
  rewrite tidspec.eq_beq_true in Hti; auto.
  inverts Hti.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  eapply H9; eauto.

  destruct H11.
  subst tid.
  rewrite TcbMod.set_sem in Hti.
  (* rewrite tidspec.neq_beq_false in Hti; auto. *)
  (* rewrite H in Hti. *)
  (* inverts Hti. *)
  (* apply ecbmod_joinsig_get in H3. *)
  (* tryfalse. *)
  rewrite tidspec.eq_beq_true in Hti; auto.
  inverts Hti.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  eapply H10; eauto.

  mytac;auto.


  do 3 eexists; splits; eauto.
  eapply IHa; eauto.
  eapply ecbmod_joinsig_get_none; eauto.
Qed.




Lemma ECBList_P_Set_Rdy_MUTEX_hold:
  forall a tcbls tid prio  msg msg'  x y  b c eid nl,
    TcbMod.get tcbls tid =  Some (prio, wait (os_stat_mutexsem eid) nl, msg) ->
    EcbMod.get c eid = None ->
    ECBList_P x y a b c tcbls ->
    ECBList_P x y a b c (TcbMod.set tcbls tid (prio,rdy,msg')).
Proof.
  inductions a; intros.
  simpl in *; auto.
  simpl in H1.
  mytac.
  destruct b; tryfalse.
  destruct a.
  mytac.
  simpl.
  eexists.
  splits; eauto.
  unfolds.
  unfolds in H2.

  splits.
  
  destructs H2.
  unfolds in H2.
  mytac.
  unfolds.
  splits; unfolds;intros.

  apply H2 in H11.
  apply H11 in H12.
  mytac.
  assert (tid = x3 \/ tid <> x3) by tauto.
  destruct H13.
  subst tid.
  unfold Maps.get in *;simpl in *.
  rewrite H12 in H.
  inverts H.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  exists x3 x4 x5.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.
  
  
  apply H8 in H11.
  apply H11 in H12.
  mytac.
  assert (tid = x3 \/ tid <> x3) by tauto.
  destruct H13.
  subst tid.
  unfold Maps.get in *;simpl in *.
  rewrite H12 in H.
  inverts H.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  exists x3 x4 x5.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.

  
  apply H9 in H11.
  apply H11 in H12.
  mytac.
  assert (tid = x3 \/ tid <> x3) by tauto.
  destruct H13.
  subst tid.
  unfold Maps.get in *;simpl in *.
  rewrite H12 in H.
  inverts H.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  exists x3 x4 x5.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.

  
  apply H10 in H11.
  apply H11 in H12.
  mytac.
  assert (tid = x3 \/ tid <> x3) by tauto.
  destruct H13.
  subst tid.
  unfold Maps.get in *;simpl in *.
  rewrite H12 in H.
  inverts H.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  exists x3 x4 x5.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.

  
  unfolds.
  destructs H2;unfolds in H6;destructs H6.
  splits;intros prio' mg ng x3 Hti;
  assert (tid = x3
          \/ tid <> x3) by tauto.
  destruct H11.
  subst tid.
  rewrite TcbMod.set_sem in Hti.
  (* rewrite tidspec.neq_beq_false in Hti; auto. *)
  (* rewrite H in Hti. *)
  (* inverts Hti. *)
  (* apply ecbmod_joinsig_get in H3. *)
  (* tryfalse. *)
  rewrite tidspec.eq_beq_true in Hti; auto.
  inverts Hti.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  eapply H6; eauto.

  destruct H11.
  subst tid.
  rewrite TcbMod.set_sem in Hti.
  (* rewrite tidspec.neq_beq_false in Hti; auto. *)
  (* rewrite H in Hti. *)
  (* inverts Hti. *)
  (* apply ecbmod_joinsig_get in H3. *)
  (* tryfalse. *)
  rewrite tidspec.eq_beq_true in Hti; auto.
  inverts Hti.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  eapply H8; eauto.

  destruct H11.
  subst tid.
  rewrite TcbMod.set_sem in Hti.
  (* rewrite tidspec.neq_beq_false in Hti; auto. *)
  (* rewrite H in Hti. *)
  (* inverts Hti. *)
  (* apply ecbmod_joinsig_get in H3. *)
  (* tryfalse. *)
  rewrite tidspec.eq_beq_true in Hti; auto.
  inverts Hti.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  eapply H9; eauto.

  destruct H11.
  subst tid.
  rewrite TcbMod.set_sem in Hti.
  (* rewrite tidspec.neq_beq_false in Hti; auto. *)
  (* rewrite H in Hti. *)
  (* inverts Hti. *)
  (* apply ecbmod_joinsig_get in H3. *)
  (* tryfalse. *)
  rewrite tidspec.eq_beq_true in Hti; auto.
  inverts Hti.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  eapply H10; eauto.

  mytac;auto.


  do 3 eexists; splits; eauto.
  eapply IHa; eauto.
  eapply ecbmod_joinsig_get_none; eauto.
Qed.


Lemma tcblist_p_imp_tcbnode_p:
  forall htls x y l1 h l ll l2 rtbl,
    TcbMod.get htls x = Some y ->
    get_last_tcb_ptr l1 h = Some (Vptr x) ->
    TCBList_P h (l1++(l::ll)++l2) rtbl htls ->
    TCBNode_P l rtbl y.
Proof.
  intros.
  gen htls x y h l ll l2 rtbl.
  inductions l1; intros.
  rewrite app_nil_l in H1.
  rewrite <- app_comm_cons in H1.
  simpl in H1; mytac.
  simpl in H0; inverts H0.
  assert(TcbMod.get htls x = Some x3).
  pose proof H3 x.
  rewrite TcbMod.get_sig_some in H0.
  destruct (TcbMod.get x2 x); tryfalse.
  destruct (TcbMod.get htls x); tryfalse.
  substs; auto.
  rewrite H in H0.
  inverts H0; auto.

  destruct l1.
  simpl in H0.
  rewrite <- app_comm_cons in H1.
  simpl in H1; mytac.
  rewrite H0 in H2; inverts H2.
  assert(TcbMod.get htls x4 = Some x7).
  clear - H3 H7.
  pose proof H3 x4; pose proof H7 x4.
  rewrite TcbMod.get_sig_some in H0.
  trans_back.
  destruct(TcbMod.get (TcbMod.sig x0 x3) x4);
  destruct(TcbMod.get x2 x4);
  destruct(TcbMod.get x6 x4);   
  destruct(TcbMod.get htls x4);
  tryfalse; substs; auto.
  rewrite H in H1; inverts H1; auto.

  assert(TCBList_P h ((a :: v :: l1) ++ l :: (ll ++ l2)) rtbl htls).
  replace( (l :: ll) ++ l2) with (l :: ll ++ l2) in H1; auto.
  pose proof tcblist_p_tid_neq' (v::l1) a l h x (ll++l2) rtbl htls H0 H2.
  clear H2.
  rewrite <- app_comm_cons in H1.
  unfold TCBList_P in H1; fold TCBList_P in H1; mytac.

  assert(x0 <> x).
  intro; substs; tryfalse; clear H3.
  assert(get x2 x = Some y).
  pose proof H4 x.
  rewrite TcbMod.get_sig_none in H7; auto.
  destruct(TcbMod.get x2 x);
  destruct(TcbMod.get htls x);
  tryfalse; substs; auto.  
  eapply IHl1; eauto.
Qed.


Lemma ecblist_p_wait_set_rdy:
  forall ectr' htls x p t m head Vnull edata x3,
    get htls x = Some (p, wait os_stat_time t, m) ->
    ECBList_P head Vnull ectr' edata x3 htls ->
    ECBList_P head Vnull ectr' edata x3 (set htls x (p, rdy, m)).
Proof.
  inductions ectr'.
  intros.
  simpl in *.
  auto.
  intros.
  simpl in H0.
  mytac.
  simpl.
  eexists;splits;eauto.
  Focus 2.
  destruct edata;auto;destruct a;eauto.
  mytac.
  do 3 eexists.
  mytac;eauto.

  Lemma r_ecb_etbl_p_wait_rdy_hold:
    forall x x0 a htls  n m m' p,
      TcbMod.get htls x = Some (p, wait os_stat_time n, m) ->
      R_ECB_ETbl_P x0 a htls ->
      R_ECB_ETbl_P x0 a (set htls x (p, rdy, m')).
  Proof.
    intros.
    unfolds;unfolds in H0.
    destruct a.
    mytac;auto.
    clear -H H0.
    unfold RLH_ECB_ETbl_P in *.
    mytac.
    clear -H H0.
    unfold RLH_ECB_ETbl_Q_P in *.
    intros.
    eapply H0 in H1;eauto.
    mytac.
    assert (x = x1 \/ x<>x1) by tauto.
    destruct H3.
    subst.
    unfold Maps.get in *;simpl in *.
    rewrite H1 in H;inverts H.
    exists x1 x2 x3.
    rewrite tcbmod_neq_set_get;eauto.
    clear -H H1.
    rename H1 into H0.
    unfold RLH_ECB_ETbl_SEM_P in *.
    intros.
    eapply H0 in H1;eauto.
    mytac.
    assert (x = x1 \/ x<>x1) by tauto.
    destruct H3.
    subst.
    unfold Maps.get in *;simpl in *.
    rewrite H1 in H;inverts H.
    do 3 eexists.
    rewrite tcbmod_neq_set_get;eauto.
    clear -H H2.
    rename H2 into H0.
    unfold RLH_ECB_ETbl_MBOX_P in *.
    intros.
    eapply H0 in H1;eauto.
    mytac.
    assert (x = x1 \/ x<>x1) by tauto.
    destruct H3.
    subst.
    unfold Maps.get in *;simpl in *.
    rewrite H1 in H;inverts H.
    do 3 eexists.
    rewrite tcbmod_neq_set_get;eauto.
    clear -H H3.
    rename H3 into H0.
    unfold RLH_ECB_ETbl_MUTEX_P in *.
    intros.
    eapply H0 in H1;eauto.
    mytac.
    assert (x = x1 \/ x<>x1) by tauto.
    destruct H3.
    subst.
    unfold Maps.get in *;simpl in *.
    rewrite H1 in H;inverts H.
    do 3 eexists.
    rewrite tcbmod_neq_set_get;eauto.

    clear -H H1.
    unfold RHL_ECB_ETbl_P in *.
    mytac.
    clear -H H0.
    unfold RHL_ECB_ETbl_Q_P in *.
    intros.
    assert (x = tid \/ x<>tid) by tauto.
    destruct H2;subst.
    rewrite set_a_get_a in H1.
    2:apply TcbMod.beq_refl.
    inverts H1.
    rewrite tcbmod_neq_set_get in H1;eauto.
    clear -H H1.
    rename H1 into H0.
    unfold RHL_ECB_ETbl_SEM_P in *.
    intros.
    assert (x = tid \/ x<>tid) by tauto.
    destruct H2;subst.
    rewrite set_a_get_a in H1.
    2:apply TcbMod.beq_refl.
    inverts H1.
    rewrite tcbmod_neq_set_get in H1;eauto.
    clear -H H2.
    rename H2 into H0.
    unfold RHL_ECB_ETbl_MBOX_P in *.
    intros.
    assert (x = tid \/ x<>tid) by tauto.
    destruct H2;subst.
    rewrite set_a_get_a in H1.
    2:apply TcbMod.beq_refl.
    inverts H1.
    rewrite tcbmod_neq_set_get in H1;eauto.
    clear -H H3.
    rename H3 into H0.
    unfold RHL_ECB_ETbl_MUTEX_P in *.
    intros.
    assert (x = tid \/ x<>tid) by tauto.
    destruct H2;subst.
    rewrite set_a_get_a in H1.
    2:apply TcbMod.beq_refl.
    inverts H1.
    rewrite tcbmod_neq_set_get in H1;eauto.
  Qed.
  eapply r_ecb_etbl_p_wait_rdy_hold;eauto.
Qed.


Lemma ecblist_p_stat_time_minus1_eq:
  forall ectr htls x p n m head edata x3 st,
    get htls x = Some (p, wait st n, m) ->
    ECBList_P head Vnull ectr edata x3 htls ->
    ECBList_P head Vnull ectr edata x3
              (set htls x (p, wait st (n-ᵢInt.one), m)).
Proof.
  inductions ectr.
  intros.
  simpl.
  simpl in H0.
  auto.
  intros.
  simpl in *.
  mytac.
  eexists;splits;eauto.
  
  Lemma r_ecb_etbl_p_tcbstats_eq_hold:
    forall x x0 a htls (st:tcbstats) n m n' m' p,
      TcbMod.get htls x = Some (p, wait st n, m) ->
      R_ECB_ETbl_P x0 a htls ->
      R_ECB_ETbl_P x0 a (set htls x (p, wait st n', m')).
  Proof.
    intros.
    unfolds;unfolds in H0.
    destruct a.
    mytac;auto.
    clear -H H0.
    unfold RLH_ECB_ETbl_P in *.
    mytac.
    clear -H H0.
    unfold RLH_ECB_ETbl_Q_P in *.
    intros.
    eapply H0 in H1;eauto.
    mytac.
    assert (x = x1 \/ x<>x1) by tauto.
    destruct H3.
    subst.
    unfold Maps.get in *;simpl in *.
    rewrite H1 in H;inverts H.
    exists x1 n' m'.
    apply set_a_get_a.
    apply TcbMod.beq_refl.
    do 3 eexists.
    rewrite tcbmod_neq_set_get;eauto.
    clear -H H1.
    rename H1 into H0.
    unfold RLH_ECB_ETbl_SEM_P in *.
    intros.
    eapply H0 in H1;eauto.
    mytac.
    assert (x = x1 \/ x<>x1) by tauto.
    destruct H3.
    subst.
    unfold Maps.get in *;simpl in *.
    rewrite H1 in H;inverts H.
    exists x1 n' m'.
    apply set_a_get_a.
    apply TcbMod.beq_refl.
    do 3 eexists.
    rewrite tcbmod_neq_set_get;eauto.
    clear -H H2.
    rename H2 into H0.
    unfold RLH_ECB_ETbl_MBOX_P in *.
    intros.
    eapply H0 in H1;eauto.
    mytac.
    assert (x = x1 \/ x<>x1) by tauto.
    destruct H3.
    subst.
    unfold Maps.get in *;simpl in *.
    rewrite H1 in H;inverts H.
    exists x1 n' m'.
    apply set_a_get_a.
    apply TcbMod.beq_refl.
    do 3 eexists.
    rewrite tcbmod_neq_set_get;eauto.
    clear -H H3.
    rename H3 into H0.
    unfold RLH_ECB_ETbl_MUTEX_P in *.
    intros.
    eapply H0 in H1;eauto.
    mytac.
    assert (x = x1 \/ x<>x1) by tauto.
    destruct H3.
    subst.
    unfold Maps.get in *;simpl in *.
    rewrite H1 in H;inverts H.
    exists x1 n' m'.
    apply set_a_get_a.
    apply TcbMod.beq_refl.
    do 3 eexists.
    rewrite tcbmod_neq_set_get;eauto.

    clear -H H1.
    unfold RHL_ECB_ETbl_P in *.
    mytac.
    clear -H H0.
    unfold RHL_ECB_ETbl_Q_P in *.
    intros.
    assert (x = tid \/ x<>tid) by tauto.
    destruct H2;subst.
    rewrite set_a_get_a in H1.
    2:apply TcbMod.beq_refl.
    inverts H1.
    eapply H0 in H.
    auto.
    rewrite tcbmod_neq_set_get in H1;eauto.
    clear -H H1.
    rename H1 into H0.
    unfold RHL_ECB_ETbl_SEM_P in *.
    intros.
    assert (x = tid \/ x<>tid) by tauto.
    destruct H2;subst.
    rewrite set_a_get_a in H1.
    2:apply TcbMod.beq_refl.
    inverts H1.
    eapply H0 in H.
    auto.
    rewrite tcbmod_neq_set_get in H1;eauto.
    clear -H H2.
    rename H2 into H0.
    unfold RHL_ECB_ETbl_MBOX_P in *.
    intros.
    assert (x = tid \/ x<>tid) by tauto.
    destruct H2;subst.
    rewrite set_a_get_a in H1.
    2:apply TcbMod.beq_refl.
    inverts H1.
    eapply H0 in H.
    auto.
    rewrite tcbmod_neq_set_get in H1;eauto.
    clear -H H3.
    rename H3 into H0.
    unfold RHL_ECB_ETbl_MUTEX_P in *.
    intros.
    assert (x = tid \/ x<>tid) by tauto.
    destruct H2;subst.
    rewrite set_a_get_a in H1.
    2:apply TcbMod.beq_refl.
    inverts H1.
    eapply H0 in H.
    auto.
    rewrite tcbmod_neq_set_get in H1;eauto.
  Qed.

  eapply r_ecb_etbl_p_tcbstats_eq_hold;eauto.
  destruct edata;tryfalse;auto.
  destruct a.
  mytac.
  do 3 eexists;splits;eauto.
Qed.



(*part4*)
(*--------Time Int---------*)

Import TcbMod.
Lemma tickchange_exists: forall t st els,
  rel_st_els st els = true ->
  exists st' els', tickchange t st els st' els'.
Proof.
  intros.
  destruct st.
  do 2 eexists; eapply rdy_change; auto.
  destruct t0.
  pose proof int_dec_zero_one i.
  destruct H0.
  substs.
  do 2 eexists.
  eapply rdy_change; eauto.
  destruct H0.
  substs.
  simpl in H.
  destruct (EcbMod.get els e) eqn : eq1; tryfalse.
  destruct b.
  do 2 eexists.
  eapply waite_rdy_change with (x:=os_stat_sem e); eauto.
  do 2 eexists.
  eapply waite_change; eauto.
  pose proof int_dec_zero_one i.
  destruct H0.
  substs.  
  do 2 eexists.
  eapply rdy_change; eauto.
  destruct H0.
  substs.
  simpl in H.
  destruct (EcbMod.get els e) eqn : eq1; tryfalse.
  destruct b.
  do 2 eexists.
  eapply waite_rdy_change with (x:= os_stat_q e); eauto.
  do 2 eexists.
  eapply waite_change; eauto.
  pose proof int_dec_zero_one i.
  destruct H0; substs.
  do 2 eexists.
  eapply wait_change; eauto.
  destruct H0.
  substs.
  do 2 eexists.
  eapply wait_rdy_change; eauto.

  destruct H0.
  do 2 eexists.
  eapply wait_change; eauto.
 
  pose proof int_dec_zero_one i.
  destruct H0.
  substs.  
  do 2 eexists.
  eapply rdy_change; eauto.

  destruct H0.
  substs.
  simpl in H.
  destruct (EcbMod.get els e) eqn : eq1; tryfalse.
  destruct b.
  do 2 eexists.
  eapply waite_rdy_change with (x:= os_stat_mbox e); eauto.
 
  do 2 eexists.
  eapply waite_change; eauto.

  pose proof int_dec_zero_one i.
  destruct H0.
  substs.
  do 2 eexists.
  eapply rdy_change; eauto.

  destruct H0.
  substs.
  simpl in H.
  destruct (EcbMod.get els e) eqn : eq1; tryfalse.
  destruct b.
  do 2 eexists.
  eapply waite_rdy_change with (x:= os_stat_mutexsem e); eauto.

  do 2 eexists.
  eapply waite_change; eauto.
  Grab Existential Variables.
  trivial.
Qed.


Lemma RH_TCBList_ECBList_P_rel_st_els :
  forall els tls ct t p st msg,
    TcbMod.get tls t = Some (p, st, msg) ->
    RH_TCBList_ECBList_P els tls ct -> rel_st_els st els = true.
Proof.
  intros.
  unfolds in H0; mytac.
  destruct st.
  simpl; auto.
  destruct t0; simpl; auto.
  unfolds in H1; mytac.
  apply H4 in H; mytac.
  unfold Maps.get in *;simpl in *.
  rewrite H; auto.
  unfolds in H0; mytac.
  apply H4 in H; mytac.
  unfold Maps.get in *;simpl in *.
  rewrite H; auto.
  unfolds in H2; mytac.
  apply H4 in H; mytac.
  unfold Maps.get in *;simpl in *.
  rewrite H; auto.
  unfolds in H3; mytac.
  apply H4 in H; mytac.
  unfold Maps.get in *;simpl in *.
  rewrite H; auto.
Qed.


Lemma RH_TCBList_ECBList_SEM_P_tickchange : forall tls els els' ct t p st st' msg,
  RH_TCBList_ECBList_SEM_P els tls ct ->
  TcbMod.get tls t = Some (p, st, msg) ->
  tickchange t st els st' els' ->
  RH_TCBList_ECBList_SEM_P els' (TcbMod.set tls t (p, st', msg)) ct.
Proof.
  intros.
  inversion H1; substs. (*5 cases*)
(*1*)
  assert ((TcbMod.set tls t (p, st', msg)) = tls).
  apply TcbMod.extensionality.
  intro.
  destruct(tidspec.beq t a) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite TcbMod.set_a_get_a; auto.
  rewrite TcbMod.set_a_get_a'; auto.
  rewrite H3; auto.
(*2*)
  unfolds in H; mytac.
  unfolds; split; intros.
  apply H in H4; mytac.
  destruct (tidspec.beq t tid) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  unfold Maps.get in *;simpl in *.
  rewrite H4 in H0; tryfalse.
  rewrite TcbMod.set_a_get_a'; eauto.

  destruct (tidspec.beq t tid) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite TcbMod.set_a_get_a in H4; auto; tryfalse.
  rewrite TcbMod.set_a_get_a' in H4; auto.
  apply H2 in H4; eauto.
(*3*)
  unfolds in H; mytac.
  unfolds; split; intros.
  apply H in H3; mytac.
  destruct (tidspec.beq t tid) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  unfold Maps.get in *;simpl in *.
  rewrite H3 in H0; tryfalse.
  rewrite TcbMod.set_a_get_a'; eauto.

  destruct (tidspec.beq t tid) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite TcbMod.set_a_get_a in H3; auto; tryfalse.
  rewrite TcbMod.set_a_get_a' in H3; auto.
  apply H2 in H3; eauto.
(*4*)
  assert(x = os_stat_sem eid \/ x = os_stat_q eid \/
         x = os_stat_mbox eid \/ x = os_stat_mutexsem eid).
  tauto.
  clear H3; rename H2 into H3.
  destruct H3; substs.
  unfolds in H; mytac.
  unfolds; split; intros.
  apply H in H5; mytac.
  destruct (tidspec.beq t tid) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite TcbMod.set_a_get_a; auto.
  unfold Maps.get in *;simpl in *.
  rewrite H5 in H0; inverts H0.
  eauto.
  rewrite TcbMod.set_a_get_a'; eauto.

  destruct (tidspec.beq t tid) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite TcbMod.set_a_get_a in H5; auto; inverts H5.
  apply H2 in H0; auto.
  rewrite TcbMod.set_a_get_a' in H5; auto.
  apply H2 in H5; eauto.

  unfolds in H; mytac.
  unfolds; split; intros.
  apply H in H6; mytac.
  destruct (tidspec.beq t tid) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  unfold Maps.get in *;simpl in *.
  rewrite H6 in H0; inverts H0.
  destruct H2; tryfalse; destruct H0; tryfalse.
  rewrite TcbMod.set_a_get_a'; eauto.

  destruct (tidspec.beq t tid) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite TcbMod.set_a_get_a in H6; auto; tryfalse.
  inverts H6.
  destruct H2; tryfalse; destruct H2; tryfalse.
  rewrite TcbMod.set_a_get_a' in H6; auto.
  apply H3 in H6; eauto.
  (*5*)
  assert(x = os_stat_sem eid \/ x = os_stat_q eid \/
         x = os_stat_mbox eid \/ x = os_stat_mutexsem eid).
  tauto.
  clear H2; rename H3 into H2.
  
  unfolds in H; mytac.
  unfolds; split.
  intros.
  destruct (tidspec.beq eid eid0) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H4; mytac.
  inverts H4.
  destruct (tidspec.beq t tid) eqn : eq2.
  pose proof tidspec.beq_true_eq _ _ eq2; substs.
  
  apply in_remove_tid_false in H6; tryfalse.
  rewrite TcbMod.set_a_get_a'; auto.

  pose proof in_remove_tid H6.
  assert(EcbMod.get els eid0 = Some (abssem n, wl)/\In tid wl) by auto.
  apply H in H7; mytac.
  eauto.
  auto.
  rewrite EcbMod.set_a_get_a' in H4; auto.
  apply H in H4; mytac.
  destruct (tidspec.beq t tid) eqn : eq2.
  pose proof tidspec.beq_true_eq _ _ eq2; substs.
  unfold Maps.get in *;simpl in *.
  rewrite H4 in H0.
  destruct H2; substs.
  inverts H0.
  apply tidspec.beq_false_neq in eq1; tryfalse.
  do 3 (destruct H2; substs; inversion H0).
  rewrite TcbMod.set_a_get_a'; auto.
  eauto.

  intros.
  destruct (tidspec.beq t tid) eqn: eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite TcbMod.set_a_get_a in H4; auto.
  inversion H4.

  rewrite TcbMod.set_a_get_a' in H4; auto.
  apply H3 in H4.
  destruct (tidspec.beq eid eid0) eqn: eq2.
  pose proof tidspec.beq_true_eq _ _ eq2; substs; mytac.
  rewrite EcbMod.set_a_get_a; auto.
  rewrite H4 in H5; inverts H5.
  do 3 eexists.
  split; eauto.
 
  apply in_remove_tid'; auto.
  intro; substs.
  apply tidspec.beq_false_neq in eq1; auto.

  rewrite EcbMod.set_a_get_a'; auto.
Qed.


Lemma RH_TCBList_ECBList_MBOX_P_tickchange :
  forall tls els els' ct t p st st' msg,
  RH_TCBList_ECBList_MBOX_P els tls ct ->
  TcbMod.get tls t = Some (p, st, msg) ->
  tickchange t st els st' els' ->
  RH_TCBList_ECBList_MBOX_P els' (TcbMod.set tls t (p, st', msg)) ct.
Proof.
  intros.
  inversion H1; substs. (*5 cases*)
(*1*)
  assert ((TcbMod.set tls t (p, st', msg)) = tls).
  apply TcbMod.extensionality.
  intro.
  destruct(tidspec.beq t a) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite TcbMod.set_a_get_a; auto.
  rewrite TcbMod.set_a_get_a'; auto.
  rewrite H3; auto.
(*2*)
  unfolds in H; mytac.
  unfolds; split; intros.
  apply H in H4; mytac.
  destruct (tidspec.beq t tid) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  unfold Maps.get in *;simpl in *.
  rewrite H4 in H0; tryfalse.
  rewrite TcbMod.set_a_get_a'; eauto.

  destruct (tidspec.beq t tid) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite TcbMod.set_a_get_a in H4; auto; tryfalse.
  rewrite TcbMod.set_a_get_a' in H4; auto.
  apply H2 in H4; eauto.
(*3*)
  unfolds in H; mytac.
  unfolds; split; intros.
  apply H in H3; mytac.
  destruct (tidspec.beq t tid) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  unfold Maps.get in *;simpl in *.
  rewrite H3 in H0; tryfalse.
  rewrite TcbMod.set_a_get_a'; eauto.

  destruct (tidspec.beq t tid) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite TcbMod.set_a_get_a in H3; auto; tryfalse.
  rewrite TcbMod.set_a_get_a' in H3; auto.
  apply H2 in H3; eauto.
(*4*)
  assert(x = os_stat_mbox eid \/ x = os_stat_q eid \/
         x = os_stat_sem eid \/ x = os_stat_mutexsem eid).
  tauto.
  clear H3; rename H2 into H3.
  destruct H3; substs.
  unfolds in H; mytac.
  unfolds; split; intros.
  apply H in H5; mytac.
  destruct (tidspec.beq t tid) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite TcbMod.set_a_get_a; auto.
  unfold Maps.get in *;simpl in *.
  rewrite H5 in H0; inverts H0.
  eauto.
  rewrite TcbMod.set_a_get_a'; eauto.

  destruct (tidspec.beq t tid) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite TcbMod.set_a_get_a in H5; auto; inverts H5.
  apply H2 in H0; auto.
  rewrite TcbMod.set_a_get_a' in H5; auto.
  apply H2 in H5; eauto.

  unfolds in H; mytac.
  unfolds; split; intros.
  apply H in H6; mytac.
  destruct (tidspec.beq t tid) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  unfold Maps.get in *;simpl in *.
  rewrite H6 in H0; inverts H0.
  destruct H2; tryfalse; destruct H0; tryfalse.
  rewrite TcbMod.set_a_get_a'; eauto.

  destruct (tidspec.beq t tid) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite TcbMod.set_a_get_a in H6; auto; tryfalse.
  inverts H6.
  destruct H2; tryfalse; destruct H2; tryfalse.
  rewrite TcbMod.set_a_get_a' in H6; auto.
  apply H3 in H6; eauto.
  (*5*)
  assert(x = os_stat_mbox eid \/ x = os_stat_q eid \/
         x = os_stat_sem eid \/ x = os_stat_mutexsem eid).
  tauto.
  clear H2; rename H3 into H2.
  
  unfolds in H; mytac.
  unfolds; split.
  intros.
  destruct (tidspec.beq eid eid0) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H4; mytac.
  inverts H4.
  destruct (tidspec.beq t tid) eqn : eq2.
  pose proof tidspec.beq_true_eq _ _ eq2; substs.
  
  apply in_remove_tid_false in H6; tryfalse.
  rewrite TcbMod.set_a_get_a'; auto.

  pose proof in_remove_tid H6.
  assert(EcbMod.get els eid0 = Some (absmbox n, wl)/\In tid wl) by auto.
  apply H in H7; mytac.
  eauto.
  auto.
  rewrite EcbMod.set_a_get_a' in H4; auto.
  apply H in H4; mytac.
  destruct (tidspec.beq t tid) eqn : eq2.
  pose proof tidspec.beq_true_eq _ _ eq2; substs.
  unfold Maps.get in *;simpl in *.
  rewrite H4 in H0.
  destruct H2; substs.
  inverts H0.
  apply tidspec.beq_false_neq in eq1; tryfalse.
  do 3 (destruct H2; substs; inversion H0).
  rewrite TcbMod.set_a_get_a'; auto.
  eauto.

  intros.
  destruct (tidspec.beq t tid) eqn: eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite TcbMod.set_a_get_a in H4; auto.
  inversion H4.

  rewrite TcbMod.set_a_get_a' in H4; auto.
  apply H3 in H4.
  destruct (tidspec.beq eid eid0) eqn: eq2.
  pose proof tidspec.beq_true_eq _ _ eq2; substs; mytac.
  rewrite EcbMod.set_a_get_a; auto.
  rewrite H4 in H5; inverts H5.
  do 3 eexists.
  split; eauto.
 
  apply in_remove_tid'; auto.
  intro; substs.
  apply tidspec.beq_false_neq in eq1; auto.

  rewrite EcbMod.set_a_get_a'; auto.
Qed.


Lemma rh_tcblist_ecblist_mutex_owner_set:
  forall els' tls t x y,
    RH_TCBList_ECBList_MUTEX_OWNER els' tls ->
    get tls t = Some x ->
    RH_TCBList_ECBList_MUTEX_OWNER els'
                                   (set tls t y) .
Proof.
  intros.
  unfold RH_TCBList_ECBList_MUTEX_OWNER in *.
  intros.
  assert (t=tid \/ t <> tid ) by tauto.
  destruct H2.
  subst t.
  rewrite TcbMod.set_a_get_a.
  destruct y.
  destruct p.
  do 3 eexists;eauto.
  apply TcbMod.beq_refl.
  rewrite TcbMod.set_a_get_a'.
  eapply H;eauto.
  apply tidspec.neq_beq_false; auto.
Qed.


Lemma rh_tcblist_ecblist_mutex_owner_set':
  forall els tls t m wl eid,
    RH_TCBList_ECBList_MUTEX_OWNER els tls ->
    EcbMod.get els eid = Some (m, wl) ->
    RH_TCBList_ECBList_MUTEX_OWNER (EcbMod.set els eid (m, remove_tid t wl))
                                   tls .
Proof.
  intros.
  unfold RH_TCBList_ECBList_MUTEX_OWNER in *.
  intros.
  assert (eid=eid0 \/ eid <> eid0 ) by tauto.
  destruct H2.
  subst eid0.
  rewrite EcbMod.set_a_get_a in H1.
  inverts H1.
  eapply H;eauto.
  apply TcbMod.beq_refl.
  
  rewrite EcbMod.set_a_get_a' in H1.
  eapply H;eauto.
  apply tidspec.neq_beq_false; auto.
Qed.

Lemma RH_TCBList_ECBList_MUTEX_P_tickchange :
  forall tls els els' ct t p st st' msg,
  RH_TCBList_ECBList_MUTEX_P els tls ct ->
  TcbMod.get tls t = Some (p, st, msg) ->
  tickchange t st els st' els' ->
  RH_TCBList_ECBList_MUTEX_P els' (TcbMod.set tls t (p, st', msg)) ct.
Proof.
    intros.
  inversion H1; substs. (*5 cases*)
(*1*)
  assert ((TcbMod.set tls t (p, st', msg)) = tls).
  apply TcbMod.extensionality.
  intro.
  destruct(tidspec.beq t a) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite TcbMod.set_a_get_a; auto.
  rewrite TcbMod.set_a_get_a'; auto.
  rewrite H3; auto.
(*2*)
  unfolds in H; mytac.
  rename H4 into Hown.
  unfolds; splits; intros.
  apply H in H4; mytac.
  destruct (tidspec.beq t tid) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  unfold Maps.get in *;simpl in *.
  rewrite H4 in H0; tryfalse.
  rewrite TcbMod.set_a_get_a'; eauto.

  destruct (tidspec.beq t tid) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite TcbMod.set_a_get_a in H4; auto; tryfalse.
  rewrite TcbMod.set_a_get_a' in H4; auto.
  apply H2 in H4; eauto.
  eapply rh_tcblist_ecblist_mutex_owner_set;eauto.
(*3*)
  unfolds in H; mytac.
  rename H3 into Hown.
  unfolds; splits; intros.
  apply H in H3; mytac.
  destruct (tidspec.beq t tid) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  unfold Maps.get in *;simpl in *.
  rewrite H3 in H0; tryfalse.
  rewrite TcbMod.set_a_get_a'; eauto.

  destruct (tidspec.beq t tid) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite TcbMod.set_a_get_a in H3; auto; tryfalse.
  rewrite TcbMod.set_a_get_a' in H3; auto.
  apply H2 in H3; eauto.
  eapply rh_tcblist_ecblist_mutex_owner_set;eauto.
(*4*) 
  assert(x = os_stat_mutexsem eid \/ x = os_stat_q eid \/
         x = os_stat_sem eid \/ x = os_stat_mbox eid).
  tauto.
  clear H3; rename H2 into H3.
  destruct H3; substs.
  unfolds in H; mytac.
  rename H3 into Hown.
  unfolds; splits; intros.
  apply H in H3; mytac.
  destruct (tidspec.beq t tid) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite TcbMod.set_a_get_a; auto.
  unfold Maps.get in *;simpl in *.
  rewrite H3 in H0; inverts H0.
  eauto.
  rewrite TcbMod.set_a_get_a'; eauto.

  destruct (tidspec.beq t tid) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite TcbMod.set_a_get_a in H3; auto; inverts H3.
  apply H2 in H0; auto.
  rewrite TcbMod.set_a_get_a' in H3; auto.
  apply H2 in H3; eauto.
  eapply rh_tcblist_ecblist_mutex_owner_set;eauto.
  unfolds in H; mytac.
  unfolds; splits; intros.
  apply H in H7; mytac.
  destruct (tidspec.beq t tid) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  unfold Maps.get in *;simpl in *.
  rewrite H7 in H0; inverts H0.
  destruct H2; tryfalse; destruct H0; tryfalse.
  rewrite TcbMod.set_a_get_a'; eauto.

  destruct (tidspec.beq t tid) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite TcbMod.set_a_get_a in H7; auto; tryfalse.
  inverts H7.
  destruct H2; tryfalse; destruct H2; tryfalse.
  rewrite TcbMod.set_a_get_a' in H7; auto.
  apply H3 in H7; eauto.
  eapply rh_tcblist_ecblist_mutex_owner_set;eauto.
  (*5*)
  assert(x = os_stat_mutexsem eid \/ x = os_stat_q eid \/
         x = os_stat_sem eid \/ x = os_stat_mbox eid).
  tauto.
  clear H2; rename H3 into H2.
  
  unfolds in H; mytac.
  rename H4 into Hown.
  unfolds; splits.
  intros.
  destruct (tidspec.beq eid eid0) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H4; mytac.
  inverts H4.
  destruct (tidspec.beq t tid) eqn : eq2.
  pose proof tidspec.beq_true_eq _ _ eq2; substs.
  
  apply in_remove_tid_false in H6; tryfalse.
  rewrite TcbMod.set_a_get_a'; auto.

  pose proof in_remove_tid H6.
  assert(EcbMod.get els eid0 = Some (absmutexsem n1 n2, wl)/\In tid wl) by auto.
  apply H in H7; mytac.
  eauto.
  auto.
  rewrite EcbMod.set_a_get_a' in H4; auto.
  apply H in H4; mytac.
  destruct (tidspec.beq t tid) eqn : eq2.
  pose proof tidspec.beq_true_eq _ _ eq2; substs.
  unfold Maps.get in *;simpl in *.
  rewrite H4 in H0.
  destruct H2; substs.
  inverts H0.
  apply tidspec.beq_false_neq in eq1; tryfalse.
  do 3 (destruct H2; substs; inversion H0).
  rewrite TcbMod.set_a_get_a'; auto.
  eauto.

  intros.
  destruct (tidspec.beq t tid) eqn: eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite TcbMod.set_a_get_a in H4; auto.
  inversion H4.

  rewrite TcbMod.set_a_get_a' in H4; auto.
  apply H3 in H4.
  destruct (tidspec.beq eid eid0) eqn: eq2.
  pose proof tidspec.beq_true_eq _ _ eq2; substs; mytac.
  rewrite EcbMod.set_a_get_a; auto.
  rewrite H4 in H5; inverts H5.
  do 3 eexists.
  split; eauto.
 
  apply in_remove_tid'; auto.
  intro; substs.
  apply tidspec.beq_false_neq in eq1; auto.

  rewrite EcbMod.set_a_get_a'; auto.
  eapply rh_tcblist_ecblist_mutex_owner_set;eauto.
  

  eapply rh_tcblist_ecblist_mutex_owner_set';eauto.
Qed.
  

Lemma RH_TCBList_ECBList_Q_P_tickchange :
  forall tls els els' ct t p st st' msg,
  RH_TCBList_ECBList_Q_P els tls ct ->
  TcbMod.get tls t = Some (p, st, msg) ->
  tickchange t st els st' els' ->
  RH_TCBList_ECBList_Q_P els' (TcbMod.set tls t (p, st', msg)) ct.
Proof.
  intros.
  inversion H1; substs. (*5 cases*)
(*1*)
  assert ((TcbMod.set tls t (p, st', msg)) = tls).
  apply TcbMod.extensionality.
  intro.
  destruct(tidspec.beq t a) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite TcbMod.set_a_get_a; auto.
  rewrite TcbMod.set_a_get_a'; auto.
  rewrite H3; auto.
(*2*)
  unfolds in H; mytac.
  unfolds; split; intros.
  apply H in H4; mytac.
  destruct (tidspec.beq t tid) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  unfold Maps.get in *;simpl in *.
  rewrite H4 in H0; tryfalse.
  rewrite TcbMod.set_a_get_a'; eauto.

  destruct (tidspec.beq t tid) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite TcbMod.set_a_get_a in H4; auto; tryfalse.
  rewrite TcbMod.set_a_get_a' in H4; auto.
  apply H2 in H4; eauto.
(*3*)
  unfolds in H; mytac.
  unfolds; split; intros.
  apply H in H3; mytac.
  destruct (tidspec.beq t tid) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  unfold Maps.get in *;simpl in *.
  rewrite H3 in H0; tryfalse.
  rewrite TcbMod.set_a_get_a'; eauto.

  destruct (tidspec.beq t tid) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite TcbMod.set_a_get_a in H3; auto; tryfalse.
  rewrite TcbMod.set_a_get_a' in H3; auto.
  apply H2 in H3; eauto.
(*4*)
  destruct H3; substs.
  unfolds in H; mytac.
  unfolds; split; intros.
  apply H in H5; mytac.
  destruct (tidspec.beq t tid) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite TcbMod.set_a_get_a; auto.
  unfold Maps.get in *;simpl in *.
  rewrite H5 in H0; inverts H0.
  eauto.
  rewrite TcbMod.set_a_get_a'; eauto.

  destruct (tidspec.beq t tid) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite TcbMod.set_a_get_a in H5; auto; inverts H5.
  apply H2 in H0; auto.
  rewrite TcbMod.set_a_get_a' in H5; auto.
  apply H2 in H5; eauto.

  unfolds in H; mytac.
  unfolds; split; intros.
  apply H in H6; mytac.
  destruct (tidspec.beq t tid) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  unfold Maps.get in *;simpl in *.
  rewrite H6 in H0; inverts H0.
  destruct H2; tryfalse; destruct H0; tryfalse.
  rewrite TcbMod.set_a_get_a'; eauto.

  destruct (tidspec.beq t tid) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite TcbMod.set_a_get_a in H6; auto; tryfalse.
  inverts H6.
  destruct H2; tryfalse; destruct H2; tryfalse.
  rewrite TcbMod.set_a_get_a' in H6; auto.
  apply H3 in H6; eauto.
  (*5*)
  unfolds in H; mytac.
  unfolds; split.
  intros.
  destruct (tidspec.beq eid eid0) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H4; mytac.
  inverts H4.
  destruct (tidspec.beq t tid) eqn : eq2.
  pose proof tidspec.beq_true_eq _ _ eq2; substs.

  apply in_remove_tid_false in H6; tryfalse.
  rewrite TcbMod.set_a_get_a'; auto.

  pose proof in_remove_tid H6.
  assert(EcbMod.get els eid0 = Some (absmsgq x0 y, wl)/\In tid wl) by auto.
  apply H in H7; mytac.
  eauto.
  auto.
  rewrite EcbMod.set_a_get_a' in H4; auto.
  apply H in H4; mytac.
  destruct (tidspec.beq t tid) eqn : eq2.
  pose proof tidspec.beq_true_eq _ _ eq2; substs.
  unfold Maps.get in *;simpl in *.
  rewrite H4 in H0.
  destruct H2; substs.
  inverts H0.
  apply tidspec.beq_false_neq in eq1; tryfalse.
  do 3 (destruct H2; substs; inversion H0).
  rewrite TcbMod.set_a_get_a'; auto.
  eauto.

  intros.
  destruct (tidspec.beq t tid) eqn: eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite TcbMod.set_a_get_a in H4; auto.
  inversion H4.

  rewrite TcbMod.set_a_get_a' in H4; auto.
  apply H3 in H4.
  destruct (tidspec.beq eid eid0) eqn: eq2.
  pose proof tidspec.beq_true_eq _ _ eq2; substs; mytac.
  rewrite EcbMod.set_a_get_a; auto.
  rewrite H4 in H5; inverts H5.
  do 3 eexists.
  split; eauto.
  
  apply in_remove_tid'; auto.
  intro; substs.
  apply tidspec.beq_false_neq in eq1; auto.

  rewrite EcbMod.set_a_get_a'; auto.
Qed.


Lemma RH_TCBList_ECBList_P_tickchange : forall tls els els' ct t p st st' msg,
  RH_TCBList_ECBList_P els tls ct ->
  TcbMod.get tls t = Some (p, st, msg) ->
  tickchange t st els st' els' ->
  RH_TCBList_ECBList_P els' (TcbMod.set tls t (p, st', msg)) ct.
Proof.
  intros.
  unfolds in H; mytac.
  unfolds.
  split.
  eapply RH_TCBList_ECBList_Q_P_tickchange; eauto.
  split.
  eapply RH_TCBList_ECBList_SEM_P_tickchange; eauto.
  split.
  eapply RH_TCBList_ECBList_MBOX_P_tickchange; eauto.
  eapply RH_TCBList_ECBList_MUTEX_P_tickchange; eauto.
Qed.

Lemma tickstep_exists'':
  forall tls_used tls els ct,
    RH_TCBList_ECBList_P els tls ct ->
    TcbMod.sub tls_used tls ->                   
    exists tls' els', tickstep' tls els tls' els' tls_used.
Proof.
  intro.
  induction tls_used.
  inductions lst0; intros.

  do 2 eexists.
  assert (i = TcbMod.is_orderset_emp').
  apply ProofIrrelevance.proof_irrelevance.  
  subst.
  eapply endtls_step.

  destruct a.
  destruct b as [p msg].
  destruct p as [p st].
  pose proof tickchange_exists a st els.
  assert(rel_st_els st els = true).
  eapply RH_TCBList_ECBList_P_rel_st_els with (t:=a) (p:=p); eauto.
  instantiate (1:=msg).
  pose proof H0 a.
  unfold TcbMod.lookup in H2.
  unfold TcbMod.get in H2.
  simpl in H2.
  rewrite tid_beq_true in H2.
  apply H2; auto.
  apply H1 in H2; mytac.
  simpl in i; mytac.
  pose proof IHlst0 i (TcbMod.set tls a (p, x, msg)) x0 ct.
  assert(RH_TCBList_ECBList_P x0 (set tls a (p, x, msg)) ct).
  eapply RH_TCBList_ECBList_P_tickchange; eauto.
  clear - H0.
  pose proof H0 a; unfold TcbMod.lookup in H.
  unfold TcbMod.get in H.
  simpl in H.
  rewrite tid_beq_true in H.
  unfolds.
  eapply H; eauto.

  assert(TcbMod.sub (listset_con (lst:=lst0) i) (TcbMod.set tls a (p, x, msg))).
  clear - H0.
  unfold TcbMod.sub; unfold TcbMod.lookup; intros.
  pose proof H0 a0; unfold TcbMod.lookup in H1.
  destruct(tidspec.beq a a0) eqn: eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.

  false.
  eapply lb_get_false; eauto.
  rewrite TcbMod.set_a_get_a'; auto.
  eapply H1; eauto.
  unfolds.
  simpl.
  destruct(tidspec.beq a0 a) eqn : eq2.
  apply tidspec.beq_true_eq in eq2; subst.
  rewrite tid_beq_true in eq1; tryfalse.
  unfolds in H; simpl in H; auto.
  apply H3 in H5; auto; mytac.
  do 2 eexists.
  eapply ext_step; eauto.
  clear - l.
  apply joinsig_listset_con.
Qed.



Lemma tickstep_exists':
  forall tls els ct,
    RH_TCBList_ECBList_P els tls ct ->
    exists tls' els', tickstep tls els tls' els'.
Proof.
  intros.
  eapply tickstep_exists''; eauto.
  apply TcbMod.sub_refl.
Qed.

Lemma tickstep_exists:
  forall tls els ct,
  exists tls' els', RH_TCBList_ECBList_P els tls ct ->
                    tickstep tls els tls' els'.
Proof.
  intros.
  lets Hx: tickstep_exists' tls els ct.
  assert ( RH_TCBList_ECBList_P els tls ct \/ ~RH_TCBList_ECBList_P els tls ct) by tauto.
  destruct H.
  apply Hx in H.
  mytac.
  do 2 eexists;intros;eauto.
  exists TcbMod.emp EcbMod.emp.
  intros.
  tryfalse.
Qed.



Lemma tickstep_rh_curtcb':
  forall tls els tls' els' tls'' ct,
    tickstep' tls els tls' els' tls'' ->
    sub tls'' tls ->
    RH_CurTCB ct tls -> RH_CurTCB ct tls'.
Proof.
  induction 1.
  intros.
  auto.
  intros.
  eapply IHtickstep'.
  eapply tcbjoinsig_set_sub_sub; eauto.
  unfolds.
  unfolds in H4.
  mytac.
  assert (ct = t \/ ct <>t) by tauto.
  destruct H1.
  subst.
  rewrite TcbMod.set_sem.
  rewrite tidspec.eq_beq_true; auto.
  do 3 eexists; eauto.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 3 eexists; eauto.
Qed.


Lemma tickstep_rh_curtcb:
  forall ct tls els tls' els',
    tickstep tls els tls' els' ->
    RH_CurTCB ct tls -> RH_CurTCB ct tls'.
Proof.
  introv Htcik Hr.
  eapply  tickstep_rh_curtcb'; eauto.
  apply TcbMod.sub_refl.
Qed.



Lemma tickstep_rh_tcblist_ecblist_p':
  forall ct tls els tls' els' tls'',
    TcbMod.sub tls'' tls ->
    tickstep' tls els tls' els' tls''-> RH_TCBList_ECBList_P els tls ct -> RH_TCBList_ECBList_P els' tls' ct.
Proof.

  introv Heq Htick.
  induction Htick.
  auto.
  intros.
  eapply IHHtick.

  eapply sub_joinsig_set_sud;eauto.

  lets Hget:sub_joinsig_get Heq H.
  clear H Htick IHHtick Heq.
  inverts H0.

  destruct H;subst.
  assert ( (TcbMod.set tls t (p, rdy, msg0)) = tls ).
  apply TcbMod.get_set_same;auto.
  unfold Maps.set in *;simpl in *.
  rewrite H.
  auto.

  rewrite TcbMod.get_set_same;auto.

  unfold RH_TCBList_ECBList_P in *.
  destruct H2 as (H2&Hres).
  
  split.
  split;intros;destruct H2.
  assert (t<>tid).
  intro.
  subst.
  eapply H0 in H.
  mytac.
  unfold Maps.get in *;simpl in *.
  rewrite H in Hget.
  inverts Hget.
  apply H0 in H.
  mytac.
  exists x0 x1 x2.
  rewrite tcbmod_neq_set_get;eauto.
  assert (t<>tid).
  intro.
  subst.
  rewrite TcbMod.set_a_get_a in H.
  inverts H.
  apply TcbMod.beq_refl;auto.
  subst tls'.
  rewrite TcbMod.set_a_get_a' in H.
  apply H2 in H.
  auto.
  apply tidspec.neq_beq_false;auto.

  clear H2.
  destruct Hres as (H2&Hres).
  split.
  split;intros;destruct H2.
  assert (t<>tid).
  intro.
  subst.
  eapply H0 in H.
  mytac.
  unfold Maps.get in *;simpl in *.
  rewrite H in Hget.
  inverts Hget.
  apply H0 in H.
  mytac.
  exists x x0 x1.
  rewrite tcbmod_neq_set_get;eauto.
  assert (t<>tid).
  intro.
  subst.
  rewrite TcbMod.set_a_get_a in H.
  inverts H.
  apply TcbMod.beq_refl;auto.
  subst tls'.
  rewrite TcbMod.set_a_get_a' in H.
  apply H2 in H.
  auto.
  apply tidspec.neq_beq_false;auto.

  clear H2.
  destruct Hres as (H2&Hres).
  split.
  split;intros;destruct H2.
  assert (t<>tid).
  intro.
  subst.
  eapply H0 in H.
  mytac.
  unfold Maps.get in *;simpl in *.
  rewrite H in Hget.
  inverts Hget.
  apply H0 in H.
  mytac.
  exists x x0 x1.
  rewrite tcbmod_neq_set_get;eauto.
  assert (t<>tid).
  intro.
  subst.
  rewrite TcbMod.set_a_get_a in H.
  inverts H.
  apply TcbMod.beq_refl;auto.
  subst tls'.
  rewrite TcbMod.set_a_get_a' in H.
  apply H2 in H.
  auto.
  apply tidspec.neq_beq_false;auto.

  clear H2.
  rename Hres into H2.
  splits;intros;destruct H2.
  assert (t<>tid).
  intro.
  subst.
  eapply H0 in H.
  mytac.
  unfold Maps.get in *;simpl in *.
  rewrite H in Hget.
  inverts Hget.
  apply H0 in H.
  mytac.
  exists x x0 x1.
  rewrite tcbmod_neq_set_get;eauto.
  assert (t<>tid).
  intro.
  subst.
  rewrite TcbMod.set_a_get_a in H.
  inverts H.
  apply TcbMod.beq_refl;auto.
  subst tls'.
  rewrite TcbMod.set_a_get_a' in H.
  apply H2 in H.
  auto.
  apply tidspec.neq_beq_false;auto.

  subst tls'.
  eapply rh_tcblist_ecblist_mutex_owner_set;eauto.
  destruct H0;auto.
  
  unfold RH_TCBList_ECBList_P in *.

  destruct H2 as (H2&Hres).
  split.
  split;intros;destruct H2.
  assert (t<>tid).
  intro.
  subst.
  eapply H0 in H.
  mytac.
  unfold Maps.get in *;simpl in *.
  rewrite H in Hget.
  inverts Hget.
  apply H0 in H.
  mytac.
  exists x0 x1 x2.
  rewrite tcbmod_neq_set_get;eauto.
  assert (t<>tid).
  intro.
  subst.
  rewrite TcbMod.set_a_get_a in H.
  inverts H.
  apply TcbMod.beq_refl;auto.
  subst tls'.
  rewrite TcbMod.set_a_get_a' in H.
  apply H2 in H.
  auto.
  apply tidspec.neq_beq_false;auto.


  clear H2.
  rename Hres into H2.
  destruct H2 as (H2&Hres).
  split.
  split;intros;destruct H2.
  assert (t<>tid).
  intro.
  subst.
  eapply H0 in H.
  mytac.
  unfold Maps.get in *;simpl in *.
  rewrite H in Hget.
  inverts Hget.
  apply H0 in H.
  mytac.
  exists x x0 x1.
  rewrite tcbmod_neq_set_get;eauto.
  assert (t<>tid).
  intro.
  subst.
  rewrite TcbMod.set_a_get_a in H.
  inverts H.
  apply TcbMod.beq_refl;auto.
  subst tls'.
  rewrite TcbMod.set_a_get_a' in H.
  apply H2 in H.
  auto.
  apply tidspec.neq_beq_false;auto.

  clear H2.
  rename Hres into H2.
  destruct H2 as (H2&Hres).
  split.
  split;intros;destruct H2.
  assert (t<>tid).
  intro.
  subst.
  eapply H0 in H.
  mytac.
  unfold Maps.get in *;simpl in *.
  rewrite H in Hget.
  inverts Hget.
  apply H0 in H.
  mytac.
  exists x x0 x1.
  rewrite tcbmod_neq_set_get;eauto.
  assert (t<>tid).
  intro.
  subst.
  rewrite TcbMod.set_a_get_a in H.
  inverts H.
  apply TcbMod.beq_refl;auto.
  subst tls'.
  rewrite TcbMod.set_a_get_a' in H.
  apply H2 in H.
  auto.
  apply tidspec.neq_beq_false;auto.

  clear H2.
  rename Hres into H2.
  splits;intros;destruct H2.
  assert (t<>tid).
  intro.
  subst.
  eapply H0 in H.
  mytac.
  unfold Maps.get in *;simpl in *.
  rewrite H in Hget.
  inverts Hget.
  apply H0 in H.
  mytac.
  exists x x0 x1.
  rewrite tcbmod_neq_set_get;eauto.

  assert (t<>tid).
  intro.
  subst.
  rewrite TcbMod.set_a_get_a in H.
  inverts H.
  apply TcbMod.beq_refl;auto.
  subst tls'.
  rewrite TcbMod.set_a_get_a' in H.
  apply H2 in H.
  auto.
  apply tidspec.neq_beq_false;auto.

  subst tls'.
  eapply rh_tcblist_ecblist_mutex_owner_set;eauto.
  destruct H0;auto.
  (*destruct H3;subst x.*)
  unfold RH_TCBList_ECBList_P in *.
  destruct H2 as (H2&Hres).
  split.
  split;intros;destruct H2.
  apply H0 in H.
  subst tls'.
  assert (t= tid \/ t <>tid) by tauto.
  destruct H1;subst.
  mytac.
  unfold Maps.get in *;simpl in *.
  rewrite H in Hget.
  inverts Hget.
  do 3 eexists.
  rewrite TcbMod.set_a_get_a.
  eauto.
  apply TcbMod.beq_refl;auto.
  mytac.
  do 3 eexists.
  rewrite tcbmod_neq_set_get;eauto.
  subst tls'.
  assert (t= tid \/ t <>tid) by tauto.
  destruct H1;subst.
  rewrite TcbMod.set_a_get_a in H.
  inverts H.
  apply H2 in Hget.
  auto.
  apply TcbMod.beq_refl;auto.
  rewrite tcbmod_neq_set_get in H;eauto.

  clear H2.
  destruct Hres as (H2&Hres).
  split.
  split;intros;destruct H2.
  apply H0 in H.
  subst tls'.
  assert (t= tid \/ t <>tid) by tauto.
  destruct H1;subst.
  mytac.
  unfold Maps.get in *;simpl in *.
  rewrite H in Hget.
  inverts Hget.
  do 3 eexists.
  rewrite TcbMod.set_a_get_a.
  eauto.
  apply TcbMod.beq_refl;auto.
  mytac.
  do 3 eexists.
  rewrite tcbmod_neq_set_get;eauto.
  subst tls'.
  assert (t= tid \/ t <>tid) by tauto.
  destruct H1;subst.
  rewrite TcbMod.set_a_get_a in H.
  inverts H.
  apply H2 in Hget.
  auto.
  apply TcbMod.beq_refl;auto.
  rewrite tcbmod_neq_set_get in H;eauto.

  clear H2.
  destruct Hres as (H2&Hres).
  split.
  split;intros;destruct H2.
  apply H0 in H.
  subst tls'.
  assert (t= tid \/ t <>tid) by tauto.
  destruct H1;subst.
  mytac.
  unfold Maps.get in *;simpl in *.
  rewrite H in Hget.
  inverts Hget.
  do 3 eexists.
  rewrite TcbMod.set_a_get_a.
  eauto.
  apply TcbMod.beq_refl;auto.
  mytac.
  do 3 eexists.
  rewrite tcbmod_neq_set_get;eauto.
  subst tls'.
  assert (t= tid \/ t <>tid) by tauto.
  destruct H1;subst.
  rewrite TcbMod.set_a_get_a in H.
  inverts H.
  apply H2 in Hget.
  auto.
  apply TcbMod.beq_refl;auto.
  rewrite tcbmod_neq_set_get in H;eauto.

  clear H2.
  rename Hres into H2.
  splits;intros;destruct H2.
  apply H0 in H.
  subst tls'.
  assert (t= tid \/ t <>tid) by tauto.
  destruct H1;subst.
  mytac.
  unfold Maps.get in *;simpl in *.
  rewrite H in Hget.
  inverts Hget.
  do 3 eexists.
  rewrite TcbMod.set_a_get_a.
  eauto.
  apply TcbMod.beq_refl;auto.
  mytac.
  do 3 eexists.
  rewrite tcbmod_neq_set_get;eauto.
  subst tls'.

  assert (t= tid \/ t <>tid) by tauto.
  destruct H1;subst.
  rewrite TcbMod.set_a_get_a in H.
  inverts H.
  apply H2 in Hget.
  auto.
  apply TcbMod.beq_refl;auto.
  rewrite tcbmod_neq_set_get in H;eauto.
  destruct H2;eapply H2;eauto.

  subst tls'.
  eapply rh_tcblist_ecblist_mutex_owner_set;eauto.
  destruct H0;auto.


  (********************)
  destruct H.
  subst x.
  subst tls'.
  unfold RH_TCBList_ECBList_P in *.
  destruct H2 as (H2 & Hres).
  split.
  split;intros;destruct H2.
  assert (t= tid \/ t <>tid) by tauto.
  assert  (eid=eid0 \/ eid<>eid0) by tauto.
  destruct H2;subst.
  destruct H3;subst.
  destruct H.
  rewrite EcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  inverts H.
  apply in_remove_tid_false in H2;tryfalse.
  rewrite EcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H0 in H.
  mytac.
  unfold Maps.get in *;simpl in *.
  rewrite H in Hget;inverts H.
  inverts Hget.
  tryfalse.
  destruct H3.
  subst.
  rewrite EcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  destruct H.
  inverts H.
  rewrite tcbmod_neq_set_get;eauto.
  apply in_remove_in in H3.
  assert (EcbMod.get els eid0 = Some (absmsgq x y, wl)/\In tid wl).
  split;auto.
  apply H0 in H.
  auto.
  rewrite tcbmod_neq_set_get;eauto.
  rewrite EcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H0 in H;auto.
  assert (t= tid \/ t <>tid) by tauto.
  assert  (eid=eid0 \/ eid<>eid0) by tauto.
  destruct H2;subst.
  destruct H3;subst.
  rewrite TcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  inverts H.
  rewrite TcbMod.set_a_get_a in H.
  inverts H.
  apply TcbMod.beq_refl;auto.
  destruct H3;subst.
  rewrite TcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H1 in H.
  mytac.
  rewrite H in H5.
  inverts H5.
  rewrite EcbMod.set_a_get_a.
  2: apply TcbMod.beq_refl;auto.
  do 3 eexists;split;eauto.
  eapply in_neq_remove_in;eauto.
  rewrite EcbMod.set_a_get_a'.
  2: apply tidspec.neq_beq_false;auto.
  rewrite TcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H1 in H.
  auto.

  split.
  clear H2.
  destruct Hres as (H2&Hres).
  split;intros;destruct H2.
  assert (t= tid \/ t <>tid) by tauto.
  assert  (eid=eid0 \/ eid<>eid0) by tauto.
  destruct H2;subst.
  destruct H3;subst.
  destruct H.
  rewrite EcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  inverts H.
  apply in_remove_tid_false in H2;tryfalse.
  rewrite EcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H0 in H.
  mytac.
  unfold Maps.get in *;simpl in *.
  rewrite H in Hget;inverts H.
  inverts Hget.
  tryfalse.
  destruct H3.
  subst.
  rewrite EcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  destruct H.
  inverts H.
  rewrite tcbmod_neq_set_get;eauto.
  apply in_remove_in in H3.
  assert (EcbMod.get els eid0 = Some (abssem n, wl)/\In tid wl).
  split;auto.
  apply H0 in H.
  auto.
  rewrite tcbmod_neq_set_get;eauto.
  rewrite EcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H0 in H;auto.
  assert (t= tid \/ t <>tid) by tauto.
  assert  (eid=eid0 \/ eid<>eid0) by tauto.
  destruct H2;subst.
  destruct H3;subst.
  rewrite TcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  inverts H.
  rewrite TcbMod.set_a_get_a in H.
  inverts H.
  apply TcbMod.beq_refl;auto.
  destruct H3;subst.
  rewrite TcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H1 in H.
  mytac.
  rewrite H in H5.
  inverts H5.
  rewrite EcbMod.set_a_get_a.
  2: apply TcbMod.beq_refl;auto.
  do 2 eexists;split;eauto.
  eapply in_neq_remove_in;eauto.
  rewrite EcbMod.set_a_get_a'.
  2: apply tidspec.neq_beq_false;auto.
  rewrite TcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H1 in H.
  auto.

  split.
  clear H2.
  destruct Hres as (Hx&H2&Hres).
  clear Hx.
  split;intros;destruct H2.
  assert (t= tid \/ t <>tid) by tauto.
  assert  (eid=eid0 \/ eid<>eid0) by tauto.
  destruct H2;subst.
  destruct H3;subst.
  destruct H.
  rewrite EcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  inverts H.
  apply in_remove_tid_false in H2;tryfalse.
  rewrite EcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H0 in H.
  mytac.
  unfold Maps.get in *;simpl in *.
  rewrite H in Hget;inverts H.
  inverts Hget.
  tryfalse.
  destruct H3.
  subst.
  rewrite EcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  destruct H.
  inverts H.
  rewrite tcbmod_neq_set_get;eauto.
  apply in_remove_in in H3.
  assert (EcbMod.get els eid0 = Some (absmbox n, wl)/\In tid wl).
  split;auto.
  apply H0 in H.
  auto.
  rewrite tcbmod_neq_set_get;eauto.
  rewrite EcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H0 in H;auto.
  assert (t= tid \/ t <>tid) by tauto.
  assert  (eid=eid0 \/ eid<>eid0) by tauto.
  destruct H2;subst.
  destruct H3;subst.
  rewrite TcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  inverts H.
  rewrite TcbMod.set_a_get_a in H.
  inverts H.
  apply TcbMod.beq_refl;auto.
  destruct H3;subst.
  rewrite TcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H1 in H.
  mytac.
  rewrite H in H5.
  inverts H5.
  rewrite EcbMod.set_a_get_a.
  2: apply TcbMod.beq_refl;auto.
  do 2 eexists;split;eauto.
  eapply in_neq_remove_in;eauto.
  rewrite EcbMod.set_a_get_a'.
  2: apply tidspec.neq_beq_false;auto.
  rewrite TcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H1 in H.
  auto.

  clear H2.
  destruct Hres as (Hx&Hres&H2).
  clear Hx.
  splits;intros;destruct H2.
  assert (t= tid \/ t <>tid) by tauto.
  assert  (eid=eid0 \/ eid<>eid0) by tauto.
  destruct H2;subst.
  destruct H3;subst.
  destruct H.
  rewrite EcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  inverts H.
  apply in_remove_tid_false in H2;tryfalse.
  rewrite EcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H0 in H.
  mytac.
  unfold Maps.get in *;simpl in *.
  rewrite H in Hget;inverts H.
  inverts Hget.
  tryfalse.
  destruct H3.
  subst.
  rewrite EcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  destruct H.
  inverts H.
  rewrite tcbmod_neq_set_get;eauto.
  apply in_remove_in in H3.
  assert (EcbMod.get els eid0 = Some (absmutexsem n1 n2, wl)/\In tid wl).
  split;auto.
  apply H0 in H.
  auto.
  rewrite tcbmod_neq_set_get;eauto.
  rewrite EcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H0 in H;auto.
  assert (t= tid \/ t <>tid) by tauto.
  assert  (eid=eid0 \/ eid<>eid0) by tauto.
  destruct H2;subst.
  destruct H3;subst.
  rewrite TcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  inverts H.
  rewrite TcbMod.set_a_get_a in H.
  inverts H.
  apply TcbMod.beq_refl;auto.
  destruct H3;subst.
  rewrite TcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H1 in H.
  mytac.
  rewrite H in H5.
  inverts H5.
  rewrite EcbMod.set_a_get_a.
  2: apply TcbMod.beq_refl;auto.
  do 3 eexists;split;eauto.
  eapply in_neq_remove_in;eauto.
  rewrite EcbMod.set_a_get_a'.
  2: apply tidspec.neq_beq_false;auto.
  rewrite TcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H1 in H.
  auto.


  eapply rh_tcblist_ecblist_mutex_owner_set;eauto.
  eapply rh_tcblist_ecblist_mutex_owner_set';eauto.
  destruct H0;auto.

  (********************)


  destruct H.
  subst x.
  subst tls'.
  unfold RH_TCBList_ECBList_P in *.
  destruct H2 as (H2 & Hres).
  split.
  split;intros;destruct H2.
  assert (t= tid \/ t <>tid) by tauto.
  assert  (eid=eid0 \/ eid<>eid0) by tauto.
  destruct H2;subst.
  destruct H3;subst.
  destruct H.
  rewrite EcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  inverts H.
  apply in_remove_tid_false in H2;tryfalse.
  rewrite EcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H0 in H.
  mytac.
  unfold Maps.get in *;simpl in *.
  rewrite H in Hget;inverts H.
  inverts Hget.
  tryfalse.
  destruct H3.
  subst.
  rewrite EcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  destruct H.
  inverts H.
  rewrite tcbmod_neq_set_get;eauto.
  apply in_remove_in in H3.
  assert (EcbMod.get els eid0 = Some (absmsgq x y, wl)/\In tid wl).
  split;auto.
  apply H0 in H.
  auto.
  rewrite tcbmod_neq_set_get;eauto.
  rewrite EcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H0 in H;auto.
  assert (t= tid \/ t <>tid) by tauto.
  assert  (eid=eid0 \/ eid<>eid0) by tauto.
  destruct H2;subst.
  destruct H3;subst.
  rewrite TcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  inverts H.
  rewrite TcbMod.set_a_get_a in H.
  inverts H.
  apply TcbMod.beq_refl;auto.
  destruct H3;subst.
  rewrite TcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H1 in H.
  mytac.
  rewrite H in H5.
  inverts H5.
  rewrite EcbMod.set_a_get_a.
  2: apply TcbMod.beq_refl;auto.
  do 3 eexists;split;eauto.
  eapply in_neq_remove_in;eauto.
  rewrite EcbMod.set_a_get_a'.
  2: apply tidspec.neq_beq_false;auto.
  rewrite TcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H1 in H.
  auto.

  split.
  clear H2.
  destruct Hres as (H2&Hres).
  split;intros;destruct H2.
  assert (t= tid \/ t <>tid) by tauto.
  assert  (eid=eid0 \/ eid<>eid0) by tauto.
  destruct H2;subst.
  destruct H3;subst.
  destruct H.
  rewrite EcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  inverts H.
  apply in_remove_tid_false in H2;tryfalse.
  rewrite EcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H0 in H.
  mytac.
  unfold Maps.get in *;simpl in *.
  rewrite H in Hget;inverts H.
  inverts Hget.
  tryfalse.
  destruct H3.
  subst.
  rewrite EcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  destruct H.
  inverts H.
  rewrite tcbmod_neq_set_get;eauto.
  apply in_remove_in in H3.
  assert (EcbMod.get els eid0 = Some (abssem n, wl)/\In tid wl).
  split;auto.
  apply H0 in H.
  auto.
  rewrite tcbmod_neq_set_get;eauto.
  rewrite EcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H0 in H;auto.
  assert (t= tid \/ t <>tid) by tauto.
  assert  (eid=eid0 \/ eid<>eid0) by tauto.
  destruct H2;subst.
  destruct H3;subst.
  rewrite TcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  inverts H.
  rewrite TcbMod.set_a_get_a in H.
  inverts H.
  apply TcbMod.beq_refl;auto.
  destruct H3;subst.
  rewrite TcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H1 in H.
  mytac.
  rewrite H in H5.
  inverts H5.
  rewrite EcbMod.set_a_get_a.
  2: apply TcbMod.beq_refl;auto.
  do 2 eexists;split;eauto.
  eapply in_neq_remove_in;eauto.
  rewrite EcbMod.set_a_get_a'.
  2: apply tidspec.neq_beq_false;auto.
  rewrite TcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H1 in H.
  auto.

  split.
  clear H2.
  destruct Hres as (Hx&H2&Hres).
  clear Hx.
  split;intros;destruct H2.
  assert (t= tid \/ t <>tid) by tauto.
  assert  (eid=eid0 \/ eid<>eid0) by tauto.
  destruct H2;subst.
  destruct H3;subst.
  destruct H.
  rewrite EcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  inverts H.
  apply in_remove_tid_false in H2;tryfalse.
  rewrite EcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H0 in H.
  mytac.
  unfold Maps.get in *;simpl in *.
  rewrite H in Hget;inverts H.
  inverts Hget.
  tryfalse.
  destruct H3.
  subst.
  rewrite EcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  destruct H.
  inverts H.
  rewrite tcbmod_neq_set_get;eauto.
  apply in_remove_in in H3.
  assert (EcbMod.get els eid0 = Some (absmbox n, wl)/\In tid wl).
  split;auto.
  apply H0 in H.
  auto.
  rewrite tcbmod_neq_set_get;eauto.
  rewrite EcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H0 in H;auto.
  assert (t= tid \/ t <>tid) by tauto.
  assert  (eid=eid0 \/ eid<>eid0) by tauto.
  destruct H2;subst.
  destruct H3;subst.
  rewrite TcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  inverts H.
  rewrite TcbMod.set_a_get_a in H.
  inverts H.
  apply TcbMod.beq_refl;auto.
  destruct H3;subst.
  rewrite TcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H1 in H.
  mytac.
  rewrite H in H5.
  inverts H5.
  rewrite EcbMod.set_a_get_a.
  2: apply TcbMod.beq_refl;auto.
  do 2 eexists;split;eauto.
  eapply in_neq_remove_in;eauto.
  rewrite EcbMod.set_a_get_a'.
  2: apply tidspec.neq_beq_false;auto.
  rewrite TcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H1 in H.
  auto.

  clear H2.
  destruct Hres as (Hx&Hres&H2).
  clear Hx.
  splits;intros;destruct H2.
  assert (t= tid \/ t <>tid) by tauto.
  assert  (eid=eid0 \/ eid<>eid0) by tauto.
  destruct H2;subst.
  destruct H3;subst.
  destruct H.
  rewrite EcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  inverts H.
  apply in_remove_tid_false in H2;tryfalse.
  rewrite EcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H0 in H.
  mytac.
  unfold Maps.get in *;simpl in *.
  rewrite H in Hget;inverts H.
  inverts Hget.
  tryfalse.
  destruct H3.
  subst.
  rewrite EcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  destruct H.
  inverts H.
  rewrite tcbmod_neq_set_get;eauto.
  apply in_remove_in in H3.
  assert (EcbMod.get els eid0 = Some (absmutexsem n1 n2, wl)/\In tid wl).
  split;auto.
  apply H0 in H.
  auto.
  rewrite tcbmod_neq_set_get;eauto.
  rewrite EcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H0 in H;auto.
  assert (t= tid \/ t <>tid) by tauto.
  assert  (eid=eid0 \/ eid<>eid0) by tauto.
  destruct H2;subst.
  destruct H3;subst.
  rewrite TcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  inverts H.
  rewrite TcbMod.set_a_get_a in H.
  inverts H.
  apply TcbMod.beq_refl;auto.
  destruct H3;subst.
  rewrite TcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H1 in H.
  mytac.
  rewrite H in H5.
  inverts H5.
  rewrite EcbMod.set_a_get_a.
  2: apply TcbMod.beq_refl;auto.
  do 3 eexists;split;eauto.
  eapply in_neq_remove_in;eauto.
  rewrite EcbMod.set_a_get_a'.
  2: apply tidspec.neq_beq_false;auto.
  rewrite TcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H1 in H.
  auto.
  eapply rh_tcblist_ecblist_mutex_owner_set;eauto.
  eapply rh_tcblist_ecblist_mutex_owner_set';eauto.
  destruct H0;auto.

  (********************)


  destruct H.
  subst x.
  subst tls'.
  unfold RH_TCBList_ECBList_P in *.
  destruct H2 as (H2 & Hres).
  split.
  split;intros;destruct H2.
  assert (t= tid \/ t <>tid) by tauto.
  assert  (eid=eid0 \/ eid<>eid0) by tauto.
  destruct H2;subst.
  destruct H3;subst.
  destruct H.
  rewrite EcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  inverts H.
  apply in_remove_tid_false in H2;tryfalse.
  rewrite EcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H0 in H.
  mytac.
  unfold Maps.get in *;simpl in *.
  rewrite H in Hget;inverts H.
  inverts Hget.
  tryfalse.
  destruct H3.
  subst.
  rewrite EcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  destruct H.
  inverts H.
  rewrite tcbmod_neq_set_get;eauto.
  apply in_remove_in in H3.
  assert (EcbMod.get els eid0 = Some (absmsgq x y, wl)/\In tid wl).
  split;auto.
  apply H0 in H.
  auto.
  rewrite tcbmod_neq_set_get;eauto.
  rewrite EcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H0 in H;auto.
  assert (t= tid \/ t <>tid) by tauto.
  assert  (eid=eid0 \/ eid<>eid0) by tauto.
  destruct H2;subst.
  destruct H3;subst.
  rewrite TcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  inverts H.
  rewrite TcbMod.set_a_get_a in H.
  inverts H.
  apply TcbMod.beq_refl;auto.
  destruct H3;subst.
  rewrite TcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H1 in H.
  mytac.
  rewrite H in H5.
  inverts H5.
  rewrite EcbMod.set_a_get_a.
  2: apply TcbMod.beq_refl;auto.
  do 3 eexists;split;eauto.
  eapply in_neq_remove_in;eauto.
  rewrite EcbMod.set_a_get_a'.
  2: apply tidspec.neq_beq_false;auto.
  rewrite TcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H1 in H.
  auto.

  split.
  clear H2.
  destruct Hres as (H2&Hres).
  split;intros;destruct H2.
  assert (t= tid \/ t <>tid) by tauto.
  assert  (eid=eid0 \/ eid<>eid0) by tauto.
  destruct H2;subst.
  destruct H3;subst.
  destruct H.
  rewrite EcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  inverts H.
  apply in_remove_tid_false in H2;tryfalse.
  rewrite EcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H0 in H.
  mytac.
  unfold Maps.get in *;simpl in *.
  rewrite H in Hget;inverts H.
  inverts Hget.
  tryfalse.
  destruct H3.
  subst.
  rewrite EcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  destruct H.
  inverts H.
  rewrite tcbmod_neq_set_get;eauto.
  apply in_remove_in in H3.
  assert (EcbMod.get els eid0 = Some (abssem n, wl)/\In tid wl).
  split;auto.
  apply H0 in H.
  auto.
  rewrite tcbmod_neq_set_get;eauto.
  rewrite EcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H0 in H;auto.
  assert (t= tid \/ t <>tid) by tauto.
  assert  (eid=eid0 \/ eid<>eid0) by tauto.
  destruct H2;subst.
  destruct H3;subst.
  rewrite TcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  inverts H.
  rewrite TcbMod.set_a_get_a in H.
  inverts H.
  apply TcbMod.beq_refl;auto.
  destruct H3;subst.
  rewrite TcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H1 in H.
  mytac.
  rewrite H in H5.
  inverts H5.
  rewrite EcbMod.set_a_get_a.
  2: apply TcbMod.beq_refl;auto.
  do 2 eexists;split;eauto.
  eapply in_neq_remove_in;eauto.
  rewrite EcbMod.set_a_get_a'.
  2: apply tidspec.neq_beq_false;auto.
  rewrite TcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H1 in H.
  auto.

  split.
  clear H2.
  destruct Hres as (Hx&H2&Hres).
  clear Hx.
  split;intros;destruct H2.
  assert (t= tid \/ t <>tid) by tauto.
  assert  (eid=eid0 \/ eid<>eid0) by tauto.
  destruct H2;subst.
  destruct H3;subst.
  destruct H.
  rewrite EcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  inverts H.
  apply in_remove_tid_false in H2;tryfalse.
  rewrite EcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H0 in H.
  mytac.
  unfold Maps.get in *;simpl in *.
  rewrite H in Hget;inverts H.
  inverts Hget.
  tryfalse.
  destruct H3.
  subst.
  rewrite EcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  destruct H.
  inverts H.
  rewrite tcbmod_neq_set_get;eauto.
  apply in_remove_in in H3.
  assert (EcbMod.get els eid0 = Some (absmbox n, wl)/\In tid wl).
  split;auto.
  apply H0 in H.
  auto.
  rewrite tcbmod_neq_set_get;eauto.
  rewrite EcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H0 in H;auto.
  assert (t= tid \/ t <>tid) by tauto.
  assert  (eid=eid0 \/ eid<>eid0) by tauto.
  destruct H2;subst.
  destruct H3;subst.
  rewrite TcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  inverts H.
  rewrite TcbMod.set_a_get_a in H.
  inverts H.
  apply TcbMod.beq_refl;auto.
  destruct H3;subst.
  rewrite TcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H1 in H.
  mytac.
  rewrite H in H5.
  inverts H5.
  rewrite EcbMod.set_a_get_a.
  2: apply TcbMod.beq_refl;auto.
  do 2 eexists;split;eauto.
  eapply in_neq_remove_in;eauto.
  rewrite EcbMod.set_a_get_a'.
  2: apply tidspec.neq_beq_false;auto.
  rewrite TcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H1 in H.
  auto.

  clear H2.
  destruct Hres as (Hx&Hres&H2).
  clear Hx.
  splits;intros;destruct H2.
  assert (t= tid \/ t <>tid) by tauto.
  assert  (eid=eid0 \/ eid<>eid0) by tauto.
  destruct H2;subst.
  destruct H3;subst.
  destruct H.
  rewrite EcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  inverts H.
  apply in_remove_tid_false in H2;tryfalse.
  rewrite EcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H0 in H.
  mytac.
  unfold Maps.get in *;simpl in *.
  rewrite H in Hget;inverts H.
  inverts Hget.
  tryfalse.
  destruct H3.
  subst.
  rewrite EcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  destruct H.
  inverts H.
  rewrite tcbmod_neq_set_get;eauto.
  apply in_remove_in in H3.
  assert (EcbMod.get els eid0 = Some (absmutexsem n1 n2, wl)/\In tid wl).
  split;auto.
  apply H0 in H.
  auto.
  rewrite tcbmod_neq_set_get;eauto.
  rewrite EcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H0 in H;auto.
  assert (t= tid \/ t <>tid) by tauto.
  assert  (eid=eid0 \/ eid<>eid0) by tauto.
  destruct H2;subst.
  destruct H3;subst.
  rewrite TcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  inverts H.
  rewrite TcbMod.set_a_get_a in H.
  inverts H.
  apply TcbMod.beq_refl;auto.
  destruct H3;subst.
  rewrite TcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H1 in H.
  mytac.
  rewrite H in H5.
  inverts H5.
  rewrite EcbMod.set_a_get_a.
  2: apply TcbMod.beq_refl;auto.
  do 3 eexists;split;eauto.
  eapply in_neq_remove_in;eauto.
  rewrite EcbMod.set_a_get_a'.
  2: apply tidspec.neq_beq_false;auto.
  rewrite TcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H1 in H.
  auto.

  eapply rh_tcblist_ecblist_mutex_owner_set;eauto.
  eapply rh_tcblist_ecblist_mutex_owner_set';eauto.
  destruct H0;auto.
  


  (********************)
  subst x.
  subst tls'.
  unfold RH_TCBList_ECBList_P in *.
  destruct H2 as (H2 & Hres).
  split.
  split;intros;destruct H2.
  assert (t= tid \/ t <>tid) by tauto.
  assert  (eid=eid0 \/ eid<>eid0) by tauto.
  destruct H2;subst.
  destruct H3;subst.
  destruct H.
  rewrite EcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  inverts H.
  apply in_remove_tid_false in H2;tryfalse.
  rewrite EcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H0 in H.
  mytac.
  unfold Maps.get in *;simpl in *.
  rewrite H in Hget;inverts H.
  inverts Hget.
  tryfalse.
  destruct H3.
  subst.
  rewrite EcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  destruct H.
  inverts H.
  rewrite tcbmod_neq_set_get;eauto.
  apply in_remove_in in H3.
  assert (EcbMod.get els eid0 = Some (absmsgq x y, wl)/\In tid wl).
  split;auto.
  apply H0 in H.
  auto.
  rewrite tcbmod_neq_set_get;eauto.
  rewrite EcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H0 in H;auto.
  assert (t= tid \/ t <>tid) by tauto.
  assert  (eid=eid0 \/ eid<>eid0) by tauto.
  destruct H2;subst.
  destruct H3;subst.
  rewrite TcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  inverts H.
  rewrite TcbMod.set_a_get_a in H.
  inverts H.
  apply TcbMod.beq_refl;auto.
  destruct H3;subst.
  rewrite TcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H1 in H.
  mytac.
  rewrite H in H5.
  inverts H5.
  rewrite EcbMod.set_a_get_a.
  2: apply TcbMod.beq_refl;auto.
  do 3 eexists;split;eauto.
  eapply in_neq_remove_in;eauto.
  rewrite EcbMod.set_a_get_a'.
  2: apply tidspec.neq_beq_false;auto.
  rewrite TcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H1 in H.
  auto.

  split.
  clear H2.
  destruct Hres as (H2&Hres).
  split;intros;destruct H2.
  assert (t= tid \/ t <>tid) by tauto.
  assert  (eid=eid0 \/ eid<>eid0) by tauto.
  destruct H2;subst.
  destruct H3;subst.
  destruct H.
  rewrite EcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  inverts H.
  apply in_remove_tid_false in H2;tryfalse.
  rewrite EcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H0 in H.
  mytac.
  unfold Maps.get in *;simpl in *.
  rewrite H in Hget;inverts H.
  inverts Hget.
  tryfalse.
  destruct H3.
  subst.
  rewrite EcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  destruct H.
  inverts H.
  rewrite tcbmod_neq_set_get;eauto.
  apply in_remove_in in H3.
  assert (EcbMod.get els eid0 = Some (abssem n, wl)/\In tid wl).
  split;auto.
  apply H0 in H.
  auto.
  rewrite tcbmod_neq_set_get;eauto.
  rewrite EcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H0 in H;auto.
  assert (t= tid \/ t <>tid) by tauto.
  assert  (eid=eid0 \/ eid<>eid0) by tauto.
  destruct H2;subst.
  destruct H3;subst.
  rewrite TcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  inverts H.
  rewrite TcbMod.set_a_get_a in H.
  inverts H.
  apply TcbMod.beq_refl;auto.
  destruct H3;subst.
  rewrite TcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H1 in H.
  mytac.
  rewrite H in H5.
  inverts H5.
  rewrite EcbMod.set_a_get_a.
  2: apply TcbMod.beq_refl;auto.
  do 2 eexists;split;eauto.
  eapply in_neq_remove_in;eauto.
  rewrite EcbMod.set_a_get_a'.
  2: apply tidspec.neq_beq_false;auto.
  rewrite TcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H1 in H.
  auto.

  split.
  clear H2.
  destruct Hres as (Hx&H2&Hres).
  clear Hx.
  split;intros;destruct H2.
  assert (t= tid \/ t <>tid) by tauto.
  assert  (eid=eid0 \/ eid<>eid0) by tauto.
  destruct H2;subst.
  destruct H3;subst.
  destruct H.
  rewrite EcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  inverts H.
  apply in_remove_tid_false in H2;tryfalse.
  rewrite EcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H0 in H.
  mytac.
  unfold Maps.get in *;simpl in *.
  rewrite H in Hget;inverts H.
  inverts Hget.
  tryfalse.
  destruct H3.
  subst.
  rewrite EcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  destruct H.
  inverts H.
  rewrite tcbmod_neq_set_get;eauto.
  apply in_remove_in in H3.
  assert (EcbMod.get els eid0 = Some (absmbox n, wl)/\In tid wl).
  split;auto.
  apply H0 in H.
  auto.
  rewrite tcbmod_neq_set_get;eauto.
  rewrite EcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H0 in H;auto.
  assert (t= tid \/ t <>tid) by tauto.
  assert  (eid=eid0 \/ eid<>eid0) by tauto.
  destruct H2;subst.
  destruct H3;subst.
  rewrite TcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  inverts H.
  rewrite TcbMod.set_a_get_a in H.
  inverts H.
  apply TcbMod.beq_refl;auto.
  destruct H3;subst.
  rewrite TcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H1 in H.
  mytac.
  rewrite H in H5.
  inverts H5.
  rewrite EcbMod.set_a_get_a.
  2: apply TcbMod.beq_refl;auto.
  do 2 eexists;split;eauto.
  eapply in_neq_remove_in;eauto.
  rewrite EcbMod.set_a_get_a'.
  2: apply tidspec.neq_beq_false;auto.
  rewrite TcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H1 in H.
  auto.

  clear H2.
  destruct Hres as (Hx&Hres&H2).
  clear Hx.
  splits;intros;destruct H2.
  assert (t= tid \/ t <>tid) by tauto.
  assert  (eid=eid0 \/ eid<>eid0) by tauto.
  destruct H2;subst.
  destruct H3;subst.
  destruct H.
  rewrite EcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  inverts H.
  apply in_remove_tid_false in H2;tryfalse.
  rewrite EcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H0 in H.
  mytac.
  unfold Maps.get in *;simpl in *.
  rewrite H in Hget;inverts H.
  inverts Hget.
  tryfalse.
  destruct H3.
  subst.
  rewrite EcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  destruct H.
  inverts H.
  rewrite tcbmod_neq_set_get;eauto.
  apply in_remove_in in H3.
  assert (EcbMod.get els eid0 = Some (absmutexsem n1 n2, wl)/\In tid wl).
  split;auto.
  apply H0 in H.
  auto.
  rewrite tcbmod_neq_set_get;eauto.
  rewrite EcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H0 in H;auto.
  assert (t= tid \/ t <>tid) by tauto.
  assert  (eid=eid0 \/ eid<>eid0) by tauto.
  destruct H2;subst.
  destruct H3;subst.
  rewrite TcbMod.set_a_get_a in H.
  2: apply TcbMod.beq_refl;auto.
  inverts H.
  rewrite TcbMod.set_a_get_a in H.
  inverts H.
  apply TcbMod.beq_refl;auto.
  destruct H3;subst.
  rewrite TcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H1 in H.
  mytac.
  rewrite H in H5.
  inverts H5.
  rewrite EcbMod.set_a_get_a.
  2: apply TcbMod.beq_refl;auto.
  do 3 eexists;split;eauto.
  eapply in_neq_remove_in;eauto.
  rewrite EcbMod.set_a_get_a'.
  2: apply tidspec.neq_beq_false;auto.
  rewrite TcbMod.set_a_get_a' in H.
  2: apply tidspec.neq_beq_false;auto.
  apply H1 in H.
  auto.
  eapply rh_tcblist_ecblist_mutex_owner_set;eauto.
  eapply rh_tcblist_ecblist_mutex_owner_set';eauto.
  destruct H0;auto.
Qed.
 

Lemma tickstep_rh_tcblist_ecblist_p: forall ct tls els tls' els',  tickstep tls els tls' els'-> RH_TCBList_ECBList_P els tls ct -> RH_TCBList_ECBList_P els' tls' ct.
Proof.
  intros.
  unfolds in H.
  eapply tickstep_rh_tcblist_ecblist_p';eauto.
  apply TcbMod.sub_refl.
Qed.


Lemma tickstep_r_priotbl_p':
  forall  v'36 v'12 x x0 v'4 tls vhold,
    TcbMod.sub tls v'36 ->
    tickstep' v'36 v'12 x x0 tls-> R_PrioTbl_P v'4 v'36 vhold-> R_PrioTbl_P v'4 x vhold.
Proof.
  induction 2.
  auto.
  intros.
  apply IHtickstep'.
  eapply sub_joinsig_set_sud;eauto.
  lets Hget:sub_joinsig_get H H0.
  clear IHtickstep' H3 H H0.
  inverts H1.
  destruct H;subst.
  assert ( (TcbMod.set tls t (p, rdy, msg0)) = tls ).
  apply TcbMod.get_set_same;auto.
  unfold Maps.set in *;simpl in *.
  rewrite H.
  auto.
  destruct H.
  rewrite TcbMod.get_set_same;auto.
  rewrite TcbMod.get_set_same;auto.

  unfold R_PrioTbl_P in *.
  split;intros;destructs H4.
  rename tcbid into tid.
  assert (t= tid \/ t <>tid) by tauto.
  destruct H7.
  subst.
  lets Hx: H4 H H1 H3.
  mytac.
  unfold Maps.get in *;simpl in *.
  rewrite H2 in Hget.
  inverts Hget.
  rewrite TcbMod.set_a_get_a.
  2: apply TcbMod.beq_refl;auto.
  do 2 eexists;eauto.
  subst tls'.
  rewrite TcbMod.set_a_get_a'.
  2:apply tidspec.neq_beq_false;auto.
  lets Hx: H4 H H1 H3.
  auto.
  split.
  intros.
  subst tls'.
  rename tcbid into tid.
  assert (t= tid \/ t <>tid) by tauto.
  destruct H2.
  subst.
  rewrite TcbMod.set_a_get_a in H4.
  2: apply TcbMod.beq_refl;auto.
  inverts H4.
  apply H1 in Hget;auto.
  rewrite TcbMod.set_a_get_a' in H4.
  2:apply tidspec.neq_beq_false;auto.
  apply H1 in H4;auto.
  subst tls'.
  eapply R_Prio_NoChange_Prio_hold;eauto.
  
  subst tls'.
  split;intros;destructs H4.
  lets Hx: H2 H H0 H1.
  rename tcbid into tid.
  mytac.
  assert (t= tid \/ t <>tid) by tauto.
  destruct H7.
  subst.
  unfold Maps.get in *;simpl in *.
  rewrite H5 in Hget.
  inverts Hget.
  rewrite TcbMod.set_a_get_a.
  2: apply TcbMod.beq_refl;auto.
  do 2 eexists;eauto.
  rewrite TcbMod.set_a_get_a'.
  2:apply tidspec.neq_beq_false;auto.
  do 2 eexists;eauto.
  split.
  intros.
  rename tcbid into tid.
  assert (t= tid \/ t <>tid) by tauto.
  destruct H3.
  subst.
  rewrite TcbMod.set_a_get_a in H2.
  2: apply TcbMod.beq_refl;auto.
  inverts H2.
  apply H0 in Hget;auto.
  rewrite TcbMod.set_a_get_a' in H2.
  2:apply tidspec.neq_beq_false;auto.
  apply H0 in H2;auto.
  eapply R_Prio_NoChange_Prio_hold;eauto.

  
  clear H0 H3.
  subst tls'.
  split;intros;destructs H4.
  lets Hx: H2 H H0 H1.
  rename tcbid into tid.
  mytac.
  assert (t= tid \/ t <>tid) by tauto.
  destruct H7.
  subst.
  unfold Maps.get in *;simpl in *.
  rewrite H5 in Hget.
  inverts Hget.
  rewrite TcbMod.set_a_get_a.
  2: apply TcbMod.beq_refl;auto.
  do 2 eexists;eauto.
  rewrite TcbMod.set_a_get_a'.
  2:apply tidspec.neq_beq_false;auto.
  do 2 eexists;eauto.
  split.
  intros.
  rename tcbid into tid.
  assert (t= tid \/ t <>tid) by tauto.
  destruct H3.
  subst.
  rewrite TcbMod.set_a_get_a in H2.
  2: apply TcbMod.beq_refl;auto.
  inverts H2.
  apply H0 in Hget;auto.
  rewrite TcbMod.set_a_get_a' in H2.
  2:apply tidspec.neq_beq_false;auto.
  apply H0 in H2;auto.
  eapply R_Prio_NoChange_Prio_hold;eauto.
  
  clear H H5.
  subst tls'.
  split;intros;destructs H4.
  lets Hx: H2 H H0 H1.
  rename tcbid into tid.
  mytac.
  assert (t= tid \/ t <>tid) by tauto.
  destruct H7.
  subst.
  unfold Maps.get in *;simpl in *.
  rewrite H5 in Hget.
  inverts Hget.
  rewrite TcbMod.set_a_get_a.
  2: apply TcbMod.beq_refl;auto.
  do 2 eexists;eauto.
  rewrite TcbMod.set_a_get_a'.
  2:apply tidspec.neq_beq_false;auto.
  do 2 eexists;eauto.
  split.
  intros.
  rename tcbid into tid.
  assert (t= tid \/ t <>tid) by tauto.
  destruct H3.
  subst.
  rewrite TcbMod.set_a_get_a in H2.
  2: apply TcbMod.beq_refl;auto.
  inverts H2.
  apply H0 in Hget;auto.
  rewrite TcbMod.set_a_get_a' in H2.
  2:apply tidspec.neq_beq_false;auto.
  apply H0 in H2;auto.
  eapply R_Prio_NoChange_Prio_hold;eauto.
Qed.

Lemma tickstep_r_priotbl_p:
  forall  v'36 v'12 x x0 v'4 vhold,
    tickstep v'36 v'12 x x0 -> R_PrioTbl_P v'4 v'36 vhold-> R_PrioTbl_P v'4 x vhold.
Proof.
  intros.
  unfold tickstep in *.
  eapply tickstep_r_priotbl_p';eauto.
  apply TcbMod.sub_refl.
Qed.


Lemma rl_rtbl_priotbl_p_set_hold:
  forall next pre eptr msg stat dly i1 i2 i3 i4 i5  v1 v3 ptbl x rtbl vhold,
    x <> vhold ->
    RL_TCBblk_P
      (next
         :: pre
         :: eptr
         :: msg
         :: stat
         :: dly
         :: Vint32 i1
         :: Vint32 i2
         :: Vint32 i3 :: Vint32 i4 :: Vint32 i5 :: nil) ->
    nth_val (Z.to_nat (Int.unsigned i3)) rtbl = Some v1  ->
    or v1 (Vint32 i4) = Some v3 ->
    RL_RTbl_PrioTbl_P rtbl ptbl vhold ->
    nth_val (nat_of_Z (Int.unsigned i1)) ptbl = Some (Vptr x) ->
    RL_RTbl_PrioTbl_P (update_nth_val (Z.to_nat (Int.unsigned i3)) rtbl v3) ptbl vhold.
Proof.
  introv Hnvhold Hrl Hnth Hor Hrb Htn.
  unfolds in Hrl.
  mytac.
  simpl_hyp.
  remember ((Int.shru x0 ($ 3))) as py.
  remember ((x0&ᵢ$ 7)) as px.
  unfolds in Hor.
  destruct v1; tryfalse.
  inverts Hor.
  unfolds in Hrb.
  unfolds.
  introv Hra Hpr.
  assert (p = x0 \/ p <> x0) by tauto.
  destruct H.
  subst.
  eauto.
  eapply Hrb; eauto.
  subst py.
  eapply prio_set_rdy_in_tbl_rev with (prio:= x0); eauto.
  subst px.
  auto.
Qed.

Lemma tcbls_rtbl_timetci_update_rl_rtbl_priotbl_p':
  forall a b c a' b' c' v'4 head els els' vhold,
    RL_TCBListblk_P a ->
    RL_PrioTbl_P v'4 a vhold ->
    tcbls_rtbl_timetci_update a b (Vint32 c) head els=
    Some (a', b', Vint32 c',els') ->
    RL_RTbl_PrioTbl_P b v'4 vhold ->
    RL_RTbl_PrioTbl_P b' v'4 vhold.
Proof.
  induction a.
  intros.
  simpl in H1.
  inverts H1;auto.
  introv Htls;intros.
  simpl in H.
  remember (V_OSTCBPrio a) as X.
  destruct X;tryfalse.
  destruct v;tryfalse.
  simpl in H0.
  xunfold H0.
  mytac.
  eapply IHa;eauto.
  simpl in HeqX;inverts HeqX.
  symmetry in HeqH20.
  do 2 xunfold' HeqH20.
  inverts HeqH20.
  eapply IHa;eauto.
  destruct Htls;auto.
  destruct H;auto.
  mytac.

  eapply rl_rtbl_priotbl_p_set_hold;eauto.
  simpl in HeqX;inverts HeqX.
  symmetry in HeqH20.
  do 2 xunfold' HeqH20.
  inverts HeqH20.
  eapply IHa;eauto.
  destruct Htls;auto.
  destruct H;auto.
  mytac.

  eapply rl_rtbl_priotbl_p_set_hold;eauto.
  simpl in HeqX;inverts HeqX.
  eapply IHa;eauto.
  destruct Htls;auto.
  destruct H;auto.
Qed.

Lemma tcbls_rtbl_timetci_update_rl_rtbl_priotbl_p:
  forall a b c a' b' c' v'4 head els els' tls x vhold,
    TCBList_P x a b tls ->
    RL_PrioTbl_P v'4 a vhold ->
    tcbls_rtbl_timetci_update a b (Vint32 c) head els=
    Some (a', b', Vint32 c',els') ->
    RL_RTbl_PrioTbl_P b v'4 vhold ->
    RL_RTbl_PrioTbl_P b' v'4 vhold.
Proof.
  intros.
  eapply tcbls_rtbl_timetci_update_rl_rtbl_priotbl_p';eauto.
  clear -H.
  gen a b tls x H.
  induction a.
  intros.
  simpl;auto.
  intros.
  simpl.
  split.
  simpl in H.
  unfold TCBNode_P in *;mytac.
  destruct x3.
  destruct p.
  mytac;auto.
  simpl in H.
  unfold TCBNode_P in *;mytac.
  destruct x3.
  destruct p.
  mytac.
  eapply IHa;eauto.
Qed.




Lemma tickstep_decompose :
  forall t  p st msg tcbls tcbls'' els els' tcbls',
    TcbMod.get tcbls'' t = Some (p, st, msg) ->
    TcbMod.sub tcbls'' tcbls ->
    tickstep' tcbls els tcbls' els' tcbls'' ->
    exists st' els'' ts tc,
      joinsig t (p, st, msg) ts tcbls'' /\
      tickchange t st els st' els'' /\
      TcbMod.set tcbls t (p,st',msg) = tc /\ 
      tickstep' tc els'' tcbls' els' ts /\
      TcbMod.sub ts tc.
Proof.                   
  intros.
  inductions H1.
  rewrite emp_sem in H.
  tryfalse.
  assert (t0 = t \/ t0 <> t) by tauto.
  destruct H5.
  subst t0.
  lets Hsx :  tcbjoin_get_a_my  H1.
  rewrite H in Hsx.
  inverts Hsx.
  do 4 eexists; splits; eauto.
  eapply sub_joinsig_set_sud;eauto.
  lets Hres :  tcb_joinsig_get_sub_ex H5 H1 H H0 H3.
  destruct Hres as ( Hge & Hsb & Hex).
  lets Hrsa : IHtickstep' Hge Hsb.
  mytac.
  lets Hcs:  tickchange_shift H5 H2 H8.
  destruct Hcs as (xx2 & Ht1 & Ht2).
  do 4 eexists; splits; eauto.
  eapply ext_step.
  2: eapply Ht2.    
  3: eapply H10.
  2: apply  tcbmod_set_neq_change.
  2: auto.
  eapply joinsig3_neqtid_joinsig; eauto.
  eapply sub_joinsig_set_sud with (tls_used:= tls_used);eauto.
Qed.

Lemma tickchange_nodup:
  forall l rtbl rgrp head ectr l' rtbl' rgrp' ectr' ll,
    tickchange_l l rtbl rgrp head ectr l' rtbl' rgrp' ectr' ->
    R_Prio_No_Dup_L (l :: ll) ->
    R_Prio_No_Dup_L (l' :: ll).
Proof.
  induction 1;
  introv Hr.
  subst l.
  auto.
  simpl in Hr.
  mytac.
  simpl.
  eexists; splits; eauto.
  simpl in Hr.
  mytac.
  simpl.
  eexists; splits; eauto.
  simpl in Hr.
  mytac.
  simpl.
  eexists; splits; eauto.
Qed.
 

Lemma set_rdy_grp_simpl:
  forall x0 rgrp rgrp' rtbl rtbl',
    Int.unsigned x0 < 64 ->
    set_rdy_grp (Vint32 ($ 1<<ᵢ(Int.shru x0 ($ 3)))) rgrp = Some rgrp' ->
    set_rdy_tbl (Vint32 ($ 1<<ᵢ(x0&ᵢ$ 7))) (Vint32 (Int.shru x0 ($ 3))) rtbl = Some rtbl' ->
    exists i g,
      nth_val (Z.to_nat (Int.unsigned (Int.shru x0 ($ 3)))) rtbl = Some (Vint32 i) /\
      rgrp = Vint32 g /\ rgrp' = Vint32 (Int.or g ($ 1<<ᵢ(Int.shru x0 ($ 3)))) /\ 
      rtbl' = update_nth_val (Z.to_nat (Int.unsigned (Int.shru x0 ($ 3)))) rtbl
                             (Vint32 (Int.or i ($ 1<<ᵢ(x0&ᵢ$ 7)))) /\ Int.unsigned (Int.shru x0 ($ 3)) <8 /\ Int.unsigned (x0&ᵢ$ 7) < 8.
Proof.
  intros.
  unfolds in H0.
  unfolds in H0.
  unfold or in H0.
  destruct rgrp; tryfalse.
  unfolds in H1.
  remember ( nth_val (Z.to_nat (Int.unsigned (Int.shru x0 ($ 3)))) rtbl) as X.
  destruct X; tryfalse.
  remember (bop_eval v (Vint32 ($ 1<<ᵢ(x0&ᵢ$ 7))) Int8u Int8u obitor) as Y.
  destruct Y; tryfalse.
  inverts H1.
  apply eq_sym in HeqY.
  unfolds in HeqY.
  unfold or in HeqY.
  destruct v; tryfalse.
  inverts HeqY.
  inverts H0.
  do 2 eexists; splits; eauto.
  clear - H.
  mauto.
  clear - H.
  mauto.
Qed.

(*part5*)
  
Lemma tickchange_tcbnode_p_hold:
  forall l rtbl rgrp head ectr l' rtbl' rgrp' ectr' x t els t' els' p m,
    tickchange_l l rtbl rgrp head ectr l' rtbl' rgrp' ectr' ->
    tickchange x t els t' els' ->
    TCBNode_P l rtbl (p, t, m) ->
    TCBNode_P l' rtbl' (p, t', m).
Proof.
  induction 1.
  subst.
  intros.
  inverts H.
  auto.
  funfold H1.
  unfolds; splits; try solve [unfolds; simpl; auto].
  unfolds.
  splits.
  unfolds.
  intros.
  unfolds in H4.
  destruct H4 as (Hc & _).
  apply Hc in H.
  mytac.
  unfolds.
  intros; tryfalse.
  unfolds.
  splits;
    unfolds;intros. 
  unfolds in H4.
  destruct H4 as (_&_& Hw &_).
  unfolds in Hw.
  destruct Hw as (Hw &_).
  unfolds in Hw.
  lets Hrs : Hw H H1.
  unfolds in H.
  destruct H as (_&_& H).
  usimpl H.
  destruct Hrs.
  destruct H4.
  inverts H4.
  apply int_ltu_eq_false in H.
  tryfalse.
  destruct H4 as (_&_& Hw &_).
  unfolds in Hw.
  destruct Hw as (_& Hw &_).
  unfolds in Hw.
  lets Hrs : Hw H H1 H5.
  mytac.
  destruct H4 as (_&_& Hw &_).
  unfolds in Hw.
  destruct Hw as (_&_& Hw &_).
  unfolds in Hw.
  lets Hrs : Hw H H1 H5.
  mytac.
  destruct H4 as (_&_& Hw &_).
  unfolds in Hw.
  destruct Hw as (_&_&_& Hw &_).
  unfolds in Hw.
  lets Hrs : Hw H H1 H5.
  mytac.
  destruct H4 as (_&_& Hw &_).
  unfolds in Hw.
  destruct Hw as (_&_&_&_& Hw).
  unfolds in Hw.
  lets Hrs : Hw H H1 H5.
  mytac.
  unfolds; splits; try solve [unfolds; intros; tryfalse].
  unfolds.
  intros.
  inverts H.
  destruct H4 as (_&_&_& Hw ).
  unfolds in Hw.
  destruct Hw as (Hw & _).
  unfolds in Hw.
  assert ((prio, wait os_stat_time n, m0) = (prio, wait os_stat_time n, m0)) by auto.
  apply Hw in H.
  destruct H as (Hwt & Hlt & _).
  unfolds in Hwt.
  destruct Hwt as (_ & _ & Hwt).
  usimpl Hwt.
  apply int_ltu_eq_false in Hlt.
  tryfalse.
  funfold H1.
  unfolds; splits; try solve [unfolds; simpl; auto].
  unfolds.
  splits.
  unfolds.
  intros.
  unfolds in H3.
  destruct H3 as (Hc & _).
  apply Hc in H.
  destruct H.
  destruct H1.
  destruct H3; inverts H3.
  unfolds.
  introv Hf.
  inverts Hf.
  pose (Int.eq_spec vdly Int.zero) as Hps.
  rewrite H0 in Hps.
  subst vdly.
  unfolds in H3.
  destruct H3 as (_ &_ &Hc ).
  destruct Hc as (_& Hc).
  unfolds in Hc.
  destruct Hc as (Hc & _).
  unfolds in Hc.
  assert (  (prio, wait os_stat_time Int.one, m0) =
            (prio, wait os_stat_time Int.one, m0)) by auto.
  apply Hc in H.
  destruct H as (Hwt & Hlt & Hv).
  unfolds in Hwt.
  destruct Hwt as (_& _ &Hwt).
  usimpl Hwt.
  pose (Int.eq_spec vdly Int.zero) as Hps.
  rewrite H0 in Hps.
  subst vdly.
  unfolds.
  splits; unfolds; intros.
  destruct H3 as (_&_& Hw &_).
  destruct Hw as (Hw &_).
  lets Hrs : Hw H H1.
  unfolds in H.
  destruct H as (_&_& H).
  usimpl H.
  destruct Hrs as (Hrs & _).
  apply int_ltu_eq_false in Hrs.
  rewrite eq_zero_zero in Hrs; tryfalse.
  unfolds in H3.
  destruct H3 as (_&_& Hw &_).
  destruct Hw as (_& Hw &_).
  unfolds in Hw.
  lets Hrs : Hw H H1 H4.
  destruct Hrs. inverts H3.
  unfolds in H3.
  destruct H3 as (_&_& Hw &_).
  destruct Hw as (_& _& Hw &_).
  unfolds in Hw.
  lets Hrs : Hw H H1 H4.
  destruct Hrs.
  inverts H3.
  unfolds in H3.
  destruct H3 as (_&_& Hw &_).
  destruct Hw as (_&_& _& Hw &_).
  unfolds in Hw.
  lets Hrs : Hw H H1 H4.
  destruct Hrs.
  inverts H3.
  unfolds in H3.
  destruct H3 as (_&_& Hw &_).
  destruct Hw as (_& _&_& _& Hw ).
  unfolds in Hw.
  lets Hrs : Hw H H1 H4.
  destruct Hrs.
  inverts H3.
  unfolds; splits; try solve [unfolds; intros; tryfalse].

  pose (Int.eq_spec vdly Int.zero) as Hps.
  rewrite H0 in Hps.
  subst vdly.
  unfolds.
  funfold H1; try solve [unfolds; simpl; auto].
  splits; try solve [unfolds; simpl; auto].
  unfolds.
  splits; try unfolds; intros.
  destruct H5 as (Hw & _).
  apply Hw in H.
  destruct H as (_&_&H).
  destruct H.  inverts H.
  inverts H.
  splits; try unfolds ; intros.
  destruct H5 as (_&_ &Hw &_).
  destruct Hw as (Hw &_).
  lets Hx : Hw H H1.
  unfolds in H.
  destruct H as (_&_& Hv).
  usimpl Hv.
  destruct Hx.
  apply int_ltu_eq_false in H.
  false.
  destruct H5 as (_&_ &Hw &_).
  destruct Hw as (_&Hw &_).
  lets Hx : Hw H H1 H7.
  unfolds in H.
  destruct H as (_&_& Hv).
  usimpl Hv.
  destruct Hx.
  inverts H.
  false.
  destruct H5 as (_&_ &Hw &_).
  destruct Hw as (_&_&Hw &_).
  lets Hx : Hw H H1 H7.
  unfolds in H.
  destruct H as (_&_& Hv).
  usimpl Hv.
  destruct Hx.
  inverts H.
  false.
  destruct H5 as (_&_ &Hw &_).
  destruct Hw as (_&_&_&Hw &_).
  lets Hx : Hw H H1 H7.
  unfolds in H.
  destruct H as (_&_& Hv).
  usimpl Hv.
  destruct Hx.
  inverts H.
  false.
  destruct H5 as (_&_ &Hw &_).
  destruct Hw as (_&_&_&_&Hw ).
  lets Hx : Hw H H1 H7.
  unfolds in H.
  destruct H as (_&_& Hv).
  usimpl Hv.
  destruct Hx.
  inverts H.
  false.
  destruct H5 as (_&_&_ &Hw).
  splits.
  
  unfolds.
  intros.
  inverts H.
  destruct Hw as (Hw &_).
  unfolds in Hw.
  assert ( (prio, wait os_stat_time n, m0) = (prio, wait os_stat_time n, m0)).
  auto.
  apply Hw in H.
  destruct H as (Ha & Hb &_).
  unfolds in Ha.
  destruct Ha as (_ & _& Ha).
  usimpl Ha.
  false.

  destruct Hw as (_ & Hw &_).
  unfolds.
  intros.
  inverts H.
  unfolds in Hw.
  assert (  (prio,wait (os_stat_sem eid1) n, m0)= (prio,wait (os_stat_sem eid1) n, m0)).
  auto.
  apply Hw in H.
  destruct H as (Ha & Hb &_).
  unfolds in Ha.
  destruct Ha as (_ & _& Ha).
  usimpl Ha.
  false.

  destruct Hw as (_& _ & Hw &_).
  unfolds.
  intros.
  inverts H.
  unfolds in Hw.
  assert (  (prio,wait (os_stat_q eid1) n , m0)= (prio,wait (os_stat_q eid1) n, m0)).
  auto.
  apply Hw in H.
  destruct H as (Ha & Hb &_).
  unfolds in Ha.
  destruct Ha as (_ & _& Ha).
  usimpl Ha.
  false.

  destruct Hw as (_& _& _ & Hw &_).
  unfolds.
  intros.
  inverts H.
  unfolds in Hw.
  assert (  (prio, wait (os_stat_mbox eid1) n , m0)= (prio, wait (os_stat_mbox eid1) n, m0)).
  auto.
  apply Hw in H.
  destruct H as (Ha & Hb &_).
  unfolds in Ha.
  destruct Ha as (_ & _& Ha).
  usimpl Ha.
  false.

  destruct Hw as (_& _& _ & _ & Hw ).
  unfolds.
  intros.
  inverts H.
  unfolds in Hw.
  assert (  (prio,wait (os_stat_mutexsem eid1) n , m0)= (prio, wait (os_stat_mutexsem eid1) n, m0)).
  auto.
  apply Hw in H.
  destruct H as (Ha & Hb &_).
  unfolds in Ha.
  destruct Ha as (_ & _& Ha).
  usimpl Ha.
  false.

  pose (Int.eq_spec vdly Int.zero) as Hps.
  rewrite H0 in Hps.
  subst vdly.
  unfolds.
  funfold H1;  try solve [unfolds; simpl; auto].
  splits;try solve [unfolds; simpl; auto].
  unfolds.
  splits; try unfolds; intros.
  destruct H4 as (Hw & _).
  apply Hw in H.
  destruct H as (_&_&H).
  destruct H.  inverts H.

  inverts H.
  destruct H2.
  subst x0.
  destruct H4 as (_&_ &_& _ & _& Hw &_).
  unfolds in Hw.
  assert ((prio, wait (os_stat_q eid0) Int.one, m1) =
          (prio, wait (os_stat_q eid0) Int.one, m1)).
  auto.
  apply Hw in H.
  destruct H.
  unfolds in H.
  destruct H as (_&_&H).
  usimpl H.
  destruct H.
  subst x0.
  destruct H4 as (_ &_& _ & _& Hw &_).
  unfolds in Hw.
  assert ((prio, wait (os_stat_sem eid0) Int.one, m1) =
          (prio, wait (os_stat_sem eid0) Int.one, m1)).
  auto.
  apply Hw in H.
  destruct H.
  unfolds in H.
  destruct H as (_&_&H).
  usimpl H.
  destruct H.
  subst x0.
  destruct H4 as (_&_& _ &_& _ & _& Hw &_).
  unfolds in Hw.
  assert ((prio, wait (os_stat_mbox eid0) Int.one, m1) =
          (prio, wait (os_stat_mbox eid0) Int.one, m1)).
  auto.
  apply Hw in H.
  destruct H.
  unfolds in H.
  destruct H as (_&_&H).
  usimpl H.
  subst x0.
  destruct H4 as (_&_& _ &_& _ & _& _ & Hw).
  unfolds in Hw.
  assert ((prio, wait (os_stat_mutexsem  eid0) Int.one, m1) =
          (prio, wait (os_stat_mutexsem  eid0) Int.one, m1)).
  auto.
  apply Hw in H.
  destruct H.
  unfolds in H.
  destruct H as (_&_&H).
  usimpl H.

  splits; try unfolds; intros.
  destruct H4 as (_& _& Hw &_).
  destruct Hw as (Hw &_).
  lets Hx : Hw H H1.
  unfolds in H.
  destruct H as (_&_& Hv).
  usimpl Hv.
  destruct Hx.
  false.

  destruct H4 as (_& _& Hw &_).
  destruct Hw as (_& Hw &_).
  lets Hx : Hw H H1 H6.
  unfolds in H.
  destruct H as (_&_& Hv).
  usimpl Hv.
  destruct Hx.
  false.

  destruct H4 as (_& _& Hw &_).
  destruct Hw as (_&_& Hw &_).
  lets Hx : Hw H H1 H6.
  unfolds in H.
  destruct H as (_&_& Hv).
  usimpl Hv.
  destruct Hx.
  false.

  destruct H4 as (_& _& Hw &_).
  destruct Hw as (_&_&_& Hw &_).
  lets Hx : Hw H H1 H6.
  unfolds in H.
  destruct H as (_&_& Hv).
  usimpl Hv.
  destruct Hx.
  false.

  
  destruct H4 as (_& _& Hw &_).
  destruct Hw as (_&_&_& _ & Hw).
  lets Hx : Hw H H1 H6.
  unfolds in H.
  destruct H as (_&_& Hv).
  usimpl Hv.
  destruct Hx.
  false.
  
  splits; try solve [unfolds; intros; tryfalse].

  (*Case 2*)
  subst.
  intros.
  inverts H.
  unfolds.
  funfold H2;   try solve [unfolds; simpl; auto].
  splits;try solve [unfolds; simpl; auto].
  splits.
  destruct H5 as (Hw &_).
  unfolds in Hw.
  unfolds.
  intros.
  lets Hx : Hw H.
  destruct Hx as (_& Hx &_).
  usimpl Hx.
  false.
  unfolds.
  intros.
  inverts H.

  destruct H5 as (_& Hw&_).
  unfolds in Hw.
  assert ((prio, rdy, m0) = (prio, rdy, m0)) by auto.
  apply Hw in H.
  destruct H as (_&_& H).
  usimpl H.
  false.

  destruct H5 as (_&_& Hw&_).
  unfolds.
  splits.
  unfolds.
  intros.
  destruct Hw as (Hw&_).
  unfolds in Hw.
  unfolds in H.
  destruct H as (Ha & Hb & Hc).
  usimpl Ha.
  usimpl Hc.
  usimpl H2.
  assert ( WaitTCBblk
             (vnext
                :: vprev
                :: eid
                :: m
                :: Vint32 vdly
                :: V$OS_STAT_RDY
                :: Vint32 prio
                :: Vint32 vx
                :: Vint32 vy
                :: Vint32 vbitx :: Vint32 vbity :: nil)
             rtbl prio vdly ).
  unfolds.
  splits.
  unfolds; simpl; auto.
  auto.
  unfolds; simpl; auto.
  apply Hw in H.
  destruct H as (_& H).
  destruct H.
  inverts H.
  destruct H3; tryfalse.
  rename H into Hf.
  repeat progress  destruct Hf as [Ha | Hf]; tryfalse.
  unfolds; simpl; auto.
  
  unfolds.
  intros.
  destruct Hw as (_&Hw&_).
  unfolds in Hw.
  intros.
  unfolds in H.
  destruct H as (Ha & Hb & Hc).
  usimpl Ha.
  usimpl Hc.
  usimpl H2.
  usimpl H5.
  assert (  exists m0, (prio, t', m) = (prio, wait (os_stat_sem eid1) vdly, m0)).
  eapply Hw; eauto.
  unfolds; splits; try solve [unfolds; simpl; auto].
  destruct H.
  inverts H.
  rename H3 into Hf.
  repeat progress  destruct Hf as [Ha | Hf]; tryfalse.
  inverts Ha; false.

  
  unfolds.
  intros.
  destruct Hw as (_&_&Hw&_).
  unfolds in Hw.
  intros.
  unfolds in H.
  destruct H as (Ha & Hb & Hc).
  usimpl Ha.
  usimpl Hc.
  usimpl H2.
  usimpl H5.
  assert (  exists m0, (prio, t', m) = (prio, wait (os_stat_q eid1) vdly, m0)).
  eapply Hw; eauto.
  unfolds; splits; try solve [unfolds; simpl; auto].
  destruct H.
  inverts H.
  rename H3 into Hf.
  repeat progress  destruct Hf as [Ha | Hf]; tryfalse.
  inverts Ha; false.

  unfolds.
  intros.
  destruct Hw as (_&_&_&Hw&_).
  unfolds in Hw.
  intros.
  unfolds in H.
  destruct H as (Ha & Hb & Hc).
  usimpl Ha.
  usimpl Hc.
  usimpl H2.
  usimpl H5.
  assert (  exists m0, (prio, t', m) = (prio, wait (os_stat_mbox  eid1) vdly, m0)).
  eapply Hw; eauto.
  unfolds; splits; try solve [unfolds; simpl; auto].
  destruct H.
  inverts H.
  rename H3 into Hf.
  repeat progress  destruct Hf as [Ha | Hf]; tryfalse.
  inverts Ha; false.

  unfolds.
  intros.
  destruct Hw as (_&_&_&_&Hw).
  unfolds in Hw.
  intros.
  unfolds in H.
  destruct H as (Ha & Hb & Hc).
  usimpl Ha.
  usimpl Hc.
  usimpl H2.
  usimpl H5.
  assert (  exists m0, (prio, t', m) = (prio, wait (os_stat_mutexsem  eid1) vdly, m0)).
  eapply Hw; eauto.
  unfolds; splits; try solve [unfolds; simpl; auto].
  destruct H.
  inverts H.
  rename H3 into Hf.
  repeat progress  destruct Hf as [Ha | Hf]; tryfalse.
  inverts Hf; false.
  destruct H5 as (_&_& _&Hw).
  unfolds.
  splits;
    unfolds;introv Hf; inverts Hf.
  rename H3 into Hf.
  repeat progress  destruct Hf as [Ha | Hf]; tryfalse.

  
  destruct Hw as (_& Hw &_).
  unfolds in Hw.
  assert (  (prio,wait (os_stat_sem eid1) t, m0)= (prio,wait (os_stat_sem eid1) t, m0)).
  auto.
  apply Hw in H.
  destruct H as (H&_).
  unfolds in H.
  destruct H as (_&_& H).
  usimpl H.
  rename H3 into Hf;
    repeat progress  destruct Hf as [Ha | Hf]; tryfalse;try solve [inverts Ha; false].

  destruct Hw as (_& _& Hw &_).
  unfolds in Hw.
  assert (  (prio,wait (os_stat_q eid1) t, m0)= (prio,wait (os_stat_q eid1) t, m0)).
  auto.
  apply Hw in H.
  destruct H as (H&_).
  unfolds in H.
  destruct H as (_&_& H).
  usimpl H.
  rename H3 into Hf;
    repeat progress  destruct Hf as [Ha | Hf]; tryfalse;try solve [inverts Ha; false].

  destruct Hw as (_&_ & _& Hw &_).
  unfolds in Hw.
  assert (  (prio,wait (os_stat_mbox eid1) t, m0)= (prio,wait (os_stat_mbox eid1) t, m0)).
  auto.
  apply Hw in H.
  destruct H as (H&_).
  unfolds in H.
  destruct H as (_&_& H).
  usimpl H.
  rename H3 into Hf;
    repeat progress  destruct Hf as [Ha | Hf]; tryfalse;try solve [inverts Ha; false].

  destruct Hw as (_&_ & _& _ &Hw).
  unfolds in Hw.
  assert (  (prio,wait (os_stat_mutexsem eid1) t, m0)= (prio,wait (os_stat_mutexsem eid1) t, m0)).
  auto.
  apply Hw in H.
  destruct H as (H&_).
  unfolds in H.
  destruct H as (_&_& H).
  usimpl H.
  rename H3 into Hf;
    repeat progress  destruct Hf as [Ha | Hf]; tryfalse. 
  inverts Hf; false.

  funfold H2.
  unfolds; splits; try solve [unfolds; simpl; auto].

  unfolds.
  splits.
  destruct H5 as (Hw &_).
  unfolds in Hw.
  unfolds.
  intros.
  unfolds in H.
  destruct H.
  usimpl H.
  assert (RdyTCBblk
            (vnext
               :: vprev
               :: eid
               :: m
               :: Vint32 vdly
               :: stat
               :: Vint32 prio
               :: Vint32 vx
               :: Vint32 vy
               :: Vint32 vbitx :: Vint32 vbity :: nil)
            rtbl prio).
  unfolds; splits.
  unfolds; simpl; auto.
  auto.
  apply Hw in H.
  destruct H as (_&H&_).
  usimpl H.
  false.
  
  unfolds; introv Hf; inverts Hf.
  destruct H5 as (_&_& Hw &_).
  unfolds.
  splits.

  destruct Hw as (Hw &_).
  unfolds in Hw.
  unfolds.
  intros.
  usimpl H2.
  unfolds in H.
  destruct H as (Ha & Hb & Hc).
  simpl_hyp.
  assert (Int.ltu Int.zero vdly = true /\
          (exists m0,
             (prio, wait os_stat_time n, m) = (prio, wait os_stat_time vdly, m0))).
  eapply Hw;
    unfolds; try splits; auto; try unfolds; simpl; auto.
  destruct H.
  destruct H2.
  inverts H2.
  split;eauto.
  eapply int_eq_false_ltu; auto.

  destruct Hw as (_&Hw &_).
  unfolds in Hw.
  unfolds.
  intros.
  usimpl H2.
  unfolds in H.
  destruct H as (Ha & Hb & Hc).
  simpl_hyp.
  assert (
      (exists m0,
         (prio, wait os_stat_time n, m) = (prio, wait (os_stat_sem eid0) vdly, m0))).
  eapply Hw;
    unfolds; try splits; auto; try unfolds; simpl; auto.
  destruct H.
  inverts H.


  destruct Hw as (_&_&Hw &_).
  unfolds in Hw.
  unfolds.
  intros.
  usimpl H2.
  unfolds in H.
  destruct H as (Ha & Hb & Hc).
  simpl_hyp.
  assert (
      (exists m0,
         (prio, wait os_stat_time n, m) = (prio, wait (os_stat_q eid0) vdly, m0))).
  eapply Hw;
    unfolds; try splits; auto; try unfolds; simpl; auto.
  destruct H.
  inverts H.

  destruct Hw as (_&_&_&Hw &_).
  unfolds in Hw.
  unfolds.
  intros.
  usimpl H2.
  unfolds in H.
  destruct H as (Ha & Hb & Hc).
  simpl_hyp.
  assert (
      (exists m0,
         (prio, wait os_stat_time n, m) = (prio, wait (os_stat_mbox eid0) vdly, m0))).
  eapply Hw;
    unfolds; try splits; auto; try unfolds; simpl; auto.
  destruct H.
  inverts H.

  destruct Hw as (_&_&_&_ &Hw).
  unfolds in Hw.
  unfolds.
  intros.
  usimpl H2.
  unfolds in H.
  destruct H as (Ha & Hb & Hc).
  simpl_hyp.
  assert (
      (exists m0,
         (prio, wait os_stat_time n, m) = (prio, wait (os_stat_mutexsem eid0) vdly, m0))).
  eapply Hw;
    unfolds; try splits; auto; try unfolds; simpl; auto.
  destruct H.
  inverts H.

  unfolds; splits; try unfolds; introv Hf; inverts Hf.
  destruct H5 as (_& _& _ & Hw &_).
  unfolds in Hw.
  assert ( (prio, wait os_stat_time n, m0) = (prio, wait os_stat_time n, m0)) by auto.
  apply Hw in H.
  destruct H as (Ha & Hb & Hc).
  unfolds in Ha.
  destruct Ha as (Ht1& Ht2 & Ha).
  usimpl Ha.
  usimpl Hc.
  splits.
  unfolds.
  splits; try solve [unfolds; simpl; auto].
  eapply int_eq_false_ltu; auto.
  auto.

  funfold H2.
  unfolds; splits; try solve [unfolds; simpl; auto].
  unfolds.
  splits;unfolds; intros.
  destruct H4 as (Hw &_).
  unfolds in Hw.
  assert (RdyTCBblk
            (vnext
               :: vprev
               :: eid
               :: m
               :: Vint32 vdly
               :: stat
               :: Vint32 p
               :: Vint32 vx
               :: Vint32 vy
               :: Vint32 vbitx :: Vint32 vbity :: nil)
            rtbl prio).
  destruct H.
  unfolds; splits; auto.
  apply Hw in H2.
  destruct H2 as (_&H2& _).
  usimpl H2.
  false.
  inverts H.
  destruct H4 as (_&_& _&  Hw&_).
  unfolds in Hw.
  assert ((prio, wait os_stat_time Int.one, m0) =
          (prio, wait os_stat_time Int.one, m0)).
  auto.
  apply Hw in H.
  destruct H.
  unfolds in H.
  destruct H as (_&_& H).
  usimpl H.
  false.

  destruct H4 as (_&_& Hw &_).
  splits;
    unfolds;intros.
  destruct Hw as (Hw &_).
  unfolds in Hw.
  assert ( Int.ltu Int.zero vdly = true /\
           (exists m0,
              (p, wait os_stat_time Int.one, m) = (prio, wait os_stat_time vdly, m0))).
  destruct H.
  destruct H4.
  usimpl H.
  usimpl H5.
  usimpl H2.
  eapply Hw ; eauto.
  unfolds; splits; auto.
  destruct H4.
  destruct H5.
  inverts H5.
  false.

  destruct Hw as (_& Hw &_).
  unfolds in Hw.
  assert ( exists m0,
             (p, wait os_stat_time Int.one, m) =
             (p, wait (os_stat_sem eid0) vdly, m0)).
  destruct H.
  destruct H5.
  usimpl H.
  usimpl H6.
  usimpl H2.
  eapply Hw ; eauto.
  unfolds; splits; auto.
  destruct H5.
  inverts H5.

  destruct Hw as (_& _& Hw &_).
  unfolds in Hw.
  assert ( exists m0,
             (p, wait os_stat_time Int.one, m) =
             (p, wait (os_stat_q eid0) vdly, m0)).
  destruct H.
  destruct H5.
  usimpl H.
  usimpl H6.
  usimpl H2.
  eapply Hw ; eauto.
  unfolds; splits; auto.
  destruct H5.
  inverts H5.

  destruct Hw as (_& _ & _ &  Hw &_).
  unfolds in Hw.
  assert ( exists m0,
             (p, wait os_stat_time Int.one, m) =
             (p, wait (os_stat_mbox eid0) vdly, m0)).
  destruct H.
  destruct H5.
  usimpl H.
  usimpl H6.
  usimpl H2.
  eapply Hw ; eauto.
  unfolds; splits; auto.
  destruct H5.
  inverts H5.

  destruct Hw as (_& _ & _ &  _ & Hw).
  unfolds in Hw.
  assert ( exists m0,
             (p, wait os_stat_time Int.one, m) =
             (p, wait (os_stat_mutexsem eid0) vdly, m0)).
  destruct H.
  destruct H5.
  usimpl H.
  usimpl H6.
  usimpl H2.
  eapply Hw ; eauto.
  unfolds; splits; auto.
  destruct H5.
  inverts H5.

  destruct H4 as (_&_&_& Hw&_).
  splits;  unfolds; introv Hf; inverts Hf.

  funfold H2.
  unfolds; splits; auto.
  splits;unfolds; intros.
  destruct H7 as (Hw &_).
  unfolds  in Hw.
  unfolds in H2.
  destruct H2.
  usimpl H2.
  assert (RdyTCBblk
            (vnext
               :: vprev
               :: eid
               :: m
               :: Vint32 vdly
               :: stat
               :: Vint32 prio
               :: Vint32 vx
               :: Vint32 vy
               :: Vint32 vbitx :: Vint32 vbity :: nil)
            rtbl prio) .
  unfolds; splits; auto.
  apply Hw in H2.
  destruct H2.
  destruct H7.
  usimpl H7.
  false.
  inverts H2.


  destruct H7 as (_&_& Hw& _&_).
  splits.
  unfolds.
  intros.
  usimpl H5.
  unfolds in H2.
  destruct H2.
  destruct H5.
  usimpl H2.
  usimpl H7.
  destruct Hw as (Hw &_).
  unfolds in Hw.
  assert ( Int.ltu Int.zero vdly = true /\
           (exists m0, (prio, wait x0 n, m) = (prio, wait os_stat_time vdly, m0))).
  eapply Hw; eauto. 
  unfolds; splits;auto.
  destruct H2.
  destruct H7.
  inverts H7.
  rename H4 into Hf;
    repeat progress  destruct Hf as [Ha | Hf]; tryfalse.

  destruct Hw as (_&Hw &_).
  unfolds in Hw.
  unfolds ;intros.
  usimpl H5.
  usimpl H7.
  unfolds in H2.
  destruct H2.
  usimpl H2.
  destruct H5.
  usimpl H5.
  assert (
      (exists m0, (prio, wait x0 n, m) = (prio, wait (os_stat_sem eid1) vdly, m0))).
  eapply Hw; eauto. 
  unfolds; splits;auto.
  destruct H5.
  inverts H5.
  eauto.

  destruct Hw as (_&_&Hw &_).
  unfolds in Hw.
  unfolds ;intros.
  usimpl H5.
  usimpl H7.
  unfolds in H2.
  destruct H2.
  usimpl H2.
  destruct H5.
  usimpl H5.
  assert (
      (exists m0, (prio, wait x0 n, m) = (prio, wait (os_stat_q eid1) vdly, m0))).
  eapply Hw; eauto. 
  unfolds; splits;auto.
  destruct H5.
  inverts H5.
  eauto.

  destruct Hw as (_&_&_&Hw &_).
  unfolds in Hw.
  unfolds ;intros.
  usimpl H5.
  usimpl H7.
  unfolds in H2.
  destruct H2.
  usimpl H2.
  destruct H5.
  usimpl H5.
  assert (
      (exists m0, (prio, wait x0 n, m) = (prio, wait (os_stat_mbox eid1) vdly, m0))).
  eapply Hw; eauto. 
  unfolds; splits;auto.
  destruct H5.
  inverts H5.
  eauto.

  
  destruct Hw as (_&_&_&_&Hw).
  unfolds in Hw.
  unfolds ;intros.
  usimpl H5.
  usimpl H7.
  unfolds in H2.
  destruct H2.
  usimpl H2.
  destruct H5.
  usimpl H5.
  assert (
      (exists m0, (prio, wait x0 n, m) = (prio, wait (os_stat_mutexsem eid1) vdly, m0))).
  eapply Hw; eauto. 
  unfolds; splits;auto.
  destruct H5.
  inverts H5.
  eauto.

  destruct H7 as (_&_&_&Hw).
  splits; unfolds; introv Hf; inverts Hf;
  rename H4 into Hf;
  repeat progress  destruct Hf as [Ha | Hf]; tryfalse; try inverts Ha.
  destruct Hw as (_&Hw&_).
  unfolds in Hw.
  assert ( (prio, wait (os_stat_sem eid0) n, m0) =
           (prio, wait (os_stat_sem eid0) n, m0)) by auto.
  apply Hw in H2.
  destruct H2.
  destruct H4.
  usimpl H4.
  usimpl H5. 
  destruct H2.
  destruct H4.
  usimpl H2.
  usimpl H5.
  splits; unfolds; auto.

  destruct Hw as (_&_&Hw&_).
  unfolds in Hw.
  assert ( (prio, wait (os_stat_q eid0) n, m0) =
           (prio, wait (os_stat_q eid0) n, m0)) by auto.
  apply Hw in H2.
  destruct H2.
  destruct H4.
  usimpl H4.
  usimpl H5. 
  destruct H2.
  destruct H4.
  usimpl H2.
  usimpl H5.
  splits; unfolds; auto.

  destruct Hw as (_&_&_&Hw&_).
  unfolds in Hw.
  assert ( (prio, wait (os_stat_mbox eid0) n, m0) =
           (prio, wait (os_stat_mbox eid0) n, m0)) by auto.
  apply Hw in H2.
  destruct H2.
  destruct H4.
  usimpl H4.
  usimpl H5. 
  destruct H2.
  destruct H4.
  usimpl H2.
  usimpl H5.
  splits; unfolds; auto.

  destruct Hw as (_&_&_&_&Hw).
  unfolds in Hw.
  assert ( (prio, wait (os_stat_mutexsem eid0) n, m0) =
           (prio, wait (os_stat_mutexsem eid0) n, m0)) by auto.
  inverts Hf.
  apply Hw in H2.
  destruct H2.
  destruct H4.
  usimpl H4.
  usimpl H5. 
  destruct H2.
  destruct H4.
  usimpl H2.
  usimpl H5.
  splits; unfolds; auto.

  funfold H2.
  unfolds; splits; try solve [unfolds; simpl; auto].
  unfolds.
  splits;unfolds; intros.
  destruct H5 as (Hw &_).
  unfolds in Hw.
  assert (RdyTCBblk
            (vnext
               :: vprev
               :: eid
               :: m
               :: Vint32 vdly
               :: stat
               :: Vint32 p
               :: Vint32 vx
               :: Vint32 vy
               :: Vint32 vbitx :: Vint32 vbity :: nil)
            rtbl prio).
  destruct H.
  unfolds; splits; auto.
  apply Hw in H2.
  destruct H2 as (_&H2& _).
  usimpl H2.
  false.
  inverts H.

  destruct H3.
  subst x0.
  destruct H5 as (_&_& _& _& _&Hw&_).
  unfolds in Hw.
  assert ( (prio, wait (os_stat_q eid0) Int.one, m1) =
           (prio, wait (os_stat_q eid0) Int.one, m1)).
  auto.
  apply Hw in H.
  destruct H.
  unfolds in H.
  destruct H as (_&_& H).
  usimpl H.
  false.

  destruct H.
  subst x0.
  destruct H5 as (_&_& _& _& Hw&_).
  unfolds in Hw.
  assert ( (prio, wait (os_stat_sem eid0) Int.one, m1) =
           (prio, wait (os_stat_sem eid0) Int.one, m1)).
  auto.
  apply Hw in H.
  destruct H.
  unfolds in H.
  destruct H as (_&_& H).
  usimpl H.
  false.

  destruct H.
  subst x0.
  destruct H5 as (_&_& _& _& _&_&Hw&_).
  unfolds in Hw.
  assert ( (prio, wait (os_stat_mbox eid0) Int.one, m1) =
           (prio, wait (os_stat_mbox eid0) Int.one, m1)).
  auto.
  apply Hw in H.
  destruct H.
  unfolds in H.
  destruct H as (_&_& H).
  usimpl H.
  false.

  subst x0.
  destruct H5 as (_&_& _& _& _&_&_&Hw).
  unfolds in Hw.
  assert ( (prio, wait (os_stat_mutexsem eid0) Int.one, m1) =
           (prio, wait (os_stat_mutexsem eid0) Int.one, m1)).
  auto.
  apply Hw in H.
  destruct H.
  unfolds in H.
  destruct H as (_&_& H).
  usimpl H.
  false.

  destruct H5 as (_&_& Hw &_).
  splits; unfolds; intros.
  destruct Hw as (Hw &_).
  unfolds in Hw.
  usimpl H2.
  unfolds in H.
  destruct H.
  usimpl H.
  destruct H2.
  usimpl H2.
  assert ( Int.ltu Int.zero vdly  = true /\
           (exists m1,
              (prio, wait x0 Int.one, m) = (prio , wait os_stat_time vdly , m1))).
  eapply Hw; eauto.
  unfolds; splits; auto.
  destruct H2.
  destruct H5.
  inverts H5.
  false.

  destruct Hw as (_&Hw &_).
  unfolds in Hw.
  usimpl H2.
  unfolds in H.
  destruct H.
  usimpl H.
  destruct H2.
  usimpl H2.
  usimpl H5.
  assert (exists m1,
            (prio, wait x0 Int.one, m) = (prio, wait (os_stat_sem eid1) vdly , m1)).
  eapply Hw; eauto.
  unfolds; splits; auto.
  destruct H2.
  inverts H2.
  false.

  destruct Hw as (_&_& Hw &_).
  unfolds in Hw.
  usimpl H2.
  unfolds in H.
  destruct H.
  usimpl H.
  destruct H2.
  usimpl H2.
  usimpl H5.
  assert (exists m1,
            (prio, wait x0 Int.one, m) = (prio, wait (os_stat_q eid1) vdly , m1)).
  eapply Hw; eauto.
  unfolds; splits; auto.
  destruct H2.
  inverts H2.
  false.

  destruct Hw as (_&_ &_&Hw&_).
  unfolds in Hw.
  usimpl H2.
  unfolds in H.
  destruct H.
  usimpl H.
  destruct H2.
  usimpl H2.
  usimpl H5.
  assert (exists m1,
            (prio, wait x0 Int.one, m) = (prio, wait (os_stat_mbox eid1) vdly , m1)).
  eapply Hw; eauto.
  unfolds; splits; auto.
  destruct H2.
  inverts H2.
  false.

  destruct Hw as (_& _&_ &_&Hw).
  unfolds in Hw.
  usimpl H2.
  unfolds in H.
  destruct H.
  usimpl H.
  destruct H2.
  usimpl H2.
  usimpl H5.
  assert (exists m1,
            (prio, wait x0 Int.one, m) = (prio, wait (os_stat_mutexsem eid1) vdly , m1)).
  eapply Hw; eauto.
  unfolds; splits; auto.
  destruct H2.
  inverts H2.
  false.

  splits; unfolds; introv Hf; inverts Hf.

  (*Case 3*)
  subst.
  intros.

  funfold H2.
  funfold H6.
  lets Hc :  set_rdy_grp_simpl H19 H4 H5.
  mytac.
  clear H4 H5.

  inverts H; solve_tblk.
  unfolds.
  splits.
  destruct H3.
  subst t'.
  destruct H7 as (_&Hw&_&_ &_).
  unfolds in Hw.
  assert ( (x0, rdy, m) = (x0, rdy, m) ) by auto.
  apply Hw in H.
  unfolds.
  intros.
  unfolds in H3.
  destruct H3.
  usimpl H3.
  destruct H as (_&_&H).
  usimpl H.
  false.
  destruct H.
  subst t'.
  destruct H7 as (_&_&_&_&Hw &_).
  unfolds in Hw.
  assert ((x0, wait (os_stat_sem eid) Int.zero, m) =
          (x0, wait (os_stat_sem eid) Int.zero, m)) by auto.
  apply Hw in H.
  destruct H as (H&_).
  unfolds in H.
  destruct H as (_&_&H).
  usimpl H .
  false.
  destruct H.
  subst t'.
  destruct H7 as (_&_&_&_&_&Hw&_).
  unfolds in Hw.
  assert ((x0, wait (os_stat_q eid) Int.zero, m) =
          (x0, wait (os_stat_q eid) Int.zero, m)) by auto.
  apply Hw in H.
  destruct H as (H&_).
  unfolds in H.
  destruct H as (_&_&H).
  usimpl H .
  false.
  destruct H.
  subst t'.
  destruct H7 as (_&_&_&_&_&_&Hw&_).
  unfolds in Hw.
  assert ((x0, wait (os_stat_mbox eid) Int.zero, m) =
          (x0, wait (os_stat_mbox eid) Int.zero, m)) by auto.
  apply Hw in H.
  destruct H as (H&_).
  unfolds in H.
  destruct H as (_&_&H).
  usimpl H .
  false.
  subst t'.
  destruct H7 as (_&_&_&_&_&_&_&Hw).
  unfolds in Hw.
  assert ((x0, wait (os_stat_mutexsem eid) Int.zero, m) =
          (x0, wait (os_stat_mutexsem eid) Int.zero, m)) by auto.
  apply Hw in H.
  destruct H as (H&_).
  unfolds in H.
  destruct H as (_&_&H).
  usimpl H .
  false.

  unfolds.
  intros.
  inverts H.
  pose (Int.eq_spec  (vdly-ᵢInt.one) Int.zero ) as Hps.
  rewrite H1 in Hps.
  rewrite Hps.
  splits; auto.
  unfolds.
  splits; auto.
  
  
  apply prio_in_tbl_orself.

  unfolds.
  splits; unfolds; intros;tryfalse.
  unfolds in H.
  destruct H as (Ha & Hb & Hc).
  usimpl Hc.
  usimpl Ha.
  false.
  eapply prio_notin_tbl_orself; eauto.
  destruct H7 as (_&_&_& Hw).
  unfolds.
  splits; unfolds; introv Hf; inverts Hf.
  repeat progress  destruct H3 as [Ha | H3]; tryfalse.

  repeat progress  destruct H3 as [Ha | H3]; tryfalse.
  inverts Ha.
  destruct Hw as (_&Hw&_).
  unfolds in Hw.
  assert ((prio, wait (os_stat_sem eid) Int.zero, m0) =
          (prio, wait (os_stat_sem eid) Int.zero, m0)) by auto.
  apply Hw in H.
  destruct H as (H&_).
  destruct H as (_&_&H).
  usimpl H.
  false.

  repeat progress  destruct H3 as [Ha | H3]; tryfalse.
  inverts Ha.
  destruct Hw as (_&_&Hw&_).
  unfolds in Hw.
  assert ((prio, wait (os_stat_q eid) Int.zero, m0) =
          (prio, wait (os_stat_q eid) Int.zero, m0)) by auto.
  apply Hw in H.
  destruct H as (H&_).
  destruct H as (_&_&H).
  usimpl H.
  false.

  repeat progress  destruct H3 as [Ha | H3]; tryfalse.
  inverts Ha.
  destruct Hw as (_& _&_&Hw&_).
  unfolds in Hw.
  assert ((prio, wait (os_stat_mbox eid) Int.zero, m0) =
          (prio, wait (os_stat_mbox eid) Int.zero, m0)) by auto.
  apply Hw in H.
  destruct H as (H&_).
  destruct H as (_&_&H).
  usimpl H.
  false.

  repeat progress  destruct H3 as [Ha | H3]; tryfalse.
  inverts H3.
  destruct Hw as (_& _& _&_&Hw).
  unfolds in Hw.
  assert ((prio, wait (os_stat_mutexsem eid) Int.zero, m0) =
          (prio, wait (os_stat_mutexsem eid) Int.zero, m0)) by auto.
  apply Hw in H.
  destruct H as (H&_).
  destruct H as (_&_&H).
  usimpl H.
  false.

  unfolds.
  splits.
  unfolds.
  intros.
  unfolds in H.
  destruct H7 as (_&_& _ &Hw &_).
  unfolds in Hw.
  assert ((x0, wait os_stat_time n, m) = (x0, wait os_stat_time n, m) ) by auto.
  apply Hw in H3.
  destruct H3.
  unfolds in H3.
  destruct H3.
  destruct H6.
  usimpl H3.
  usimpl H7.
  destruct H5.
  usimpl H5.
  
  lets Hfs : int_eq_false_false H4 H0.
  tryfalse.

  unfolds; introv Hf; inverts Hf.
  destruct H7 as (_&_&Hw&_).
  unfolds.
  splits; unfolds; intros;usimpl H3.
  unfolds in H.
  destruct H.
  usimpl H.
  destruct H3.
  usimpl H3.
  false.
  eapply prio_notin_tbl_orself; eauto.
  unfolds; splits; introv Hf; inverts Hf.
  destruct H7 as (_&_&_ &Hw &_).
  unfolds in Hw.
  assert ( (prio, wait os_stat_time n, m0) = (prio, wait os_stat_time n, m0)).
  auto.
  apply Hw in H.
  destruct H.
  destruct H3.
  usimpl H5.
  unfolds in H.
  destruct H.
  usimpl H.
  destruct H5.
  usimpl H5.
  lets Hfs : int_eq_false_false H4 H0.
  tryfalse.

  pose (Int.eq_spec (vdly-ᵢInt.one) Int.zero) as Hps. 
  rewrite H1 in Hps.
  rewrite Hps.
  unfolds.
  splits.
  unfolds.
  intros.
  unfolds in H.
  destruct H as (Ha & Hb).
  usimpl Ha.
  splits; eauto.
  unfolds.
  intros.
  inverts H.
  splits; eauto.
  unfolds.
  splits; auto.
  apply prio_in_tbl_orself.
  unfolds;
    splits;unfolds;intros;usimpl H3.
  unfolds in H.
  destruct H as (Ha & Hb & Hc).
  simpl_hyp.
  false.
  eapply prio_notin_tbl_orself; eauto.
  unfolds; splits; introv Hf; inverts Hf.

  unfolds.
  splits.
  unfolds.
  intros.
  unfolds in H.
  destruct H as (Ha & Hb).
  usimpl Ha.
  
  destruct H4.
  subst x3.
  destruct H7 as (_&_& _& Hw).
  destruct Hw as (_&_& Hw&_).
  unfolds in Hw.
  assert ( (prio, wait (os_stat_q eid) n, m) =
           (prio, wait (os_stat_q eid) n, m)).
  auto.
  apply Hw in H.
  destruct H as (Ha & Hc & Hd).
  usimpl Hc.

  destruct H.
  subst x3.
  destruct H7 as (_&_& _& Hw).
  destruct Hw as (_&Hw& _&_).
  unfolds in Hw.
  assert ( (prio, wait (os_stat_sem eid) n, m) =
           (prio, wait (os_stat_sem eid) n, m)).
  auto.
  apply Hw in H.
  destruct H as (Ha & Hc & Hd).
  usimpl Hc.

  destruct H.
  subst x3.
  destruct H7 as (_&_& _& Hw).
  destruct Hw as (_&_& _&Hw&_).
  unfolds in Hw.
  assert ( (prio, wait (os_stat_mbox eid) n, m) =
           (prio, wait (os_stat_mbox eid) n, m)).
  auto.
  apply Hw in H.
  destruct H as (Ha & Hc & Hd).
  usimpl Hc.

  subst x3.
  destruct H7 as (_&_& _& Hw).
  destruct Hw as (_&_& _&_& Hw).
  unfolds in Hw.
  assert ( (prio, wait (os_stat_mutexsem eid) n, m) =
           (prio, wait (os_stat_mutexsem eid) n, m)).
  auto.
  apply Hw in H.
  destruct H as (Ha & Hc & Hd).
  usimpl Hc.

  unfolds; introv Hf; inverts Hf.
  destruct H7 as (_&_& Hw&_).
  unfolds.
  splits;
    unfolds;
    intros;
    usimpl H3.
  unfolds in H.
  destruct H as (Ha & Hb & Hc).
  usimpl Ha.
  usimpl Hc.
  false.
  eapply prio_notin_tbl_orself; eauto.

  destruct H7 as (_&_&_& Hw).
  unfolds.
  splits;
    unfolds;
    intros;
    inverts H;
    repeat progress  destruct H4 as [Ha | H4]; tryfalse.
  inverts Ha.
  destruct Hw as (_&Hw&_&_).
  unfolds in Hw.
  assert ((prio, wait (os_stat_sem eid) n, m0) =
          (prio, wait (os_stat_sem eid) n, m0)) by auto.
  apply Hw in H.
  destruct H as (H&_).
  destruct H as (_&_&H).
  usimpl H.
  destruct H5.
  lets Hsf : int_eq_false_false H0; auto. 
  false.

  inverts Ha.
  destruct Hw as (_& _&Hw&_&_).
  unfolds in Hw.
  assert ((prio, wait (os_stat_q eid) n, m0) =
          (prio, wait (os_stat_q eid) n, m0)) by auto.
  apply Hw in H.
  destruct H as (H&_).
  destruct H as (_&_&H).
  usimpl H.
  destruct H5.
  lets Hsf : int_eq_false_false H0; auto. 
  false.

  inverts Ha.
  destruct Hw as (_& _&_&Hw&_).
  unfolds in Hw.
  assert ((prio, wait (os_stat_mbox eid) n, m0) =
          (prio, wait (os_stat_mbox eid) n, m0)) by auto.
  apply Hw in H.
  destruct H as (H&_).
  destruct H as (_&_&H).
  usimpl H.
  destruct H5.
  lets Hsf : int_eq_false_false H0; auto. 
  false.

  inverts H4.
  destruct Hw as (_& _&_&_&Hw).
  unfolds in Hw.
  assert ((prio, wait (os_stat_mutexsem eid) n, m0) =
          (prio, wait (os_stat_mutexsem eid) n, m0)) by auto.
  apply Hw in H.
  destruct H as (H&_).
  destruct H as (_&_&H).
  usimpl H.
  destruct H5.
  lets Hsf : int_eq_false_false H0; auto. 
  false.

  pose (Int.eq_spec  (vdly-ᵢInt.one) Int.zero) as Hps.
  rewrite H1 in Hps.
  rewrite Hps.
  unfolds.
  splits; unfolds; intros.
  unfolds in H.
  destruct H as (Ha & Hb).
  usimpl Ha.
  splits; eauto.

  inverts H.
  splits; auto.
  unfolds; splits; auto.
  apply prio_in_tbl_orself.

  destruct H7 as (_&_& Hw &_).
  splits;
    unfolds;
    intros;
    usimpl H4.
  unfolds in H.
  destruct H as (Ha & Hb & Hc).
  usimpl Ha.
  usimpl Hc.
  false.
  eapply prio_notin_tbl_orself; eauto.

  destruct H7 as (_&_&_&Hw).
  splits; unfolds; introv Hf; inverts Hf.

  (*Case 4*)
  subst.

  clear H6.
  intros.
  funfold H2.
  funfold H6.
  lets Hc :  set_rdy_grp_simpl H19 H4 H5.
  mytac.
  clear H4 H5.
  inverts H; solve_tblk.
  unfolds.
  splits.
  destruct H3.
  subst t'.
  destruct H7 as (_&Hw&_&_ &_).
  unfolds in Hw.
  assert ( (x0, rdy, m) = (x0, rdy, m) ) by auto.
  apply Hw in H.
  unfolds.
  intros.
  unfolds in H3.
  destruct H3.
  usimpl H3.
  destruct H as (_&_&H).
  usimpl H.
  false.
  destruct H.
  subst t'.
  destruct H7 as (_&_&_&_&Hw &_).
  unfolds in Hw.
  assert ((x0, wait (os_stat_sem eid) Int.zero, m) =
          (x0, wait (os_stat_sem eid) Int.zero, m)) by auto.
  apply Hw in H.
  destruct H as (H&_).
  unfolds in H.
  destruct H as (_&_&H).
  usimpl H .
  false.
  destruct H.
  subst t'.
  destruct H7 as (_&_&_&_&_&Hw&_).
  unfolds in Hw.
  assert ((x0, wait (os_stat_q eid) Int.zero, m) =
          (x0, wait (os_stat_q eid) Int.zero, m)) by auto.
  apply Hw in H.
  destruct H as (H&_).
  unfolds in H.
  destruct H as (_&_&H).
  usimpl H .
  false.
  destruct H.
  subst t'.
  destruct H7 as (_&_&_&_&_&_&Hw&_).
  unfolds in Hw.
  assert ((x0, wait (os_stat_mbox eid) Int.zero, m) =
          (x0, wait (os_stat_mbox eid) Int.zero, m)) by auto.
  apply Hw in H.
  destruct H as (H&_).
  unfolds in H.
  destruct H as (_&_&H).
  usimpl H .
  false.
  subst t'.
  destruct H7 as (_&_&_&_&_&_&_&Hw).
  unfolds in Hw.
  assert ((x0, wait (os_stat_mutexsem eid) Int.zero, m) =
          (x0, wait (os_stat_mutexsem eid) Int.zero, m)) by auto.
  apply Hw in H.
  destruct H as (H&_).
  unfolds in H.
  destruct H as (_&_&H).
  usimpl H .
  false.

  unfolds.
  intros.
  inverts H.
  pose (Int.eq_spec  (vdly-ᵢInt.one) Int.zero ) as Hps.
  rewrite H1 in Hps.
  rewrite Hps.
  splits; auto.
  unfolds.
  splits; auto.
  
  
  apply prio_in_tbl_orself.

  unfolds.
  splits; unfolds; intros;tryfalse.
  unfolds in H.
  destruct H as (Ha & Hb & Hc).
  usimpl Hc.
  usimpl Ha.
  false.
  eapply prio_notin_tbl_orself; eauto.
  destruct H7 as (_&_&_& Hw).
  unfolds.
  splits; unfolds; introv Hf; inverts Hf.
  repeat progress  destruct H3 as [Ha | H3]; tryfalse.

  repeat progress  destruct H3 as [Ha | H3]; tryfalse.
  inverts Ha.
  destruct Hw as (_&Hw&_).
  unfolds in Hw.
  assert ((prio, wait (os_stat_sem eid) Int.zero, m0) =
          (prio, wait (os_stat_sem eid) Int.zero, m0)) by auto.
  apply Hw in H.
  destruct H as (H&_).
  destruct H as (_&_&H).
  usimpl H.
  false.

  repeat progress  destruct H3 as [Ha | H3]; tryfalse.
  inverts Ha.
  destruct Hw as (_&_&Hw&_).
  unfolds in Hw.
  assert ((prio, wait (os_stat_q eid) Int.zero, m0) =
          (prio, wait (os_stat_q eid) Int.zero, m0)) by auto.
  apply Hw in H.
  destruct H as (H&_).
  destruct H as (_&_&H).
  usimpl H.
  false.

  repeat progress  destruct H3 as [Ha | H3]; tryfalse.
  inverts Ha.
  destruct Hw as (_& _&_&Hw&_).
  unfolds in Hw.
  assert ((prio, wait (os_stat_mbox eid) Int.zero, m0) =
          (prio, wait (os_stat_mbox eid) Int.zero, m0)) by auto.
  apply Hw in H.
  destruct H as (H&_).
  destruct H as (_&_&H).
  usimpl H.
  false.

  repeat progress  destruct H3 as [Ha | H3]; tryfalse.
  inverts H3.
  destruct Hw as (_& _& _&_&Hw).
  unfolds in Hw.
  assert ((prio, wait (os_stat_mutexsem eid) Int.zero, m0) =
          (prio, wait (os_stat_mutexsem eid) Int.zero, m0)) by auto.
  apply Hw in H.
  destruct H as (H&_).
  destruct H as (_&_&H).
  usimpl H.
  false.

  unfolds.
  splits.
  unfolds.
  intros.
  unfolds in H.
  destruct H7 as (_&_& _ &Hw &_).
  unfolds in Hw.
  assert ((x0, wait os_stat_time n, m) = (x0, wait os_stat_time n, m) ) by auto.
  apply Hw in H3.
  destruct H3.
  unfolds in H3.
  destruct H3.
  destruct H6.
  usimpl H3.
  usimpl H7.
  destruct H5.
  usimpl H5.
  
  lets Hfs : int_eq_false_false H4 H0.
  tryfalse.

  unfolds; introv Hf; inverts Hf.
  destruct H7 as (_&_&Hw&_).
  unfolds.
  splits; unfolds; intros;usimpl H3.
  unfolds in H.
  destruct H.
  usimpl H.
  destruct H3.
  usimpl H3.
  false.
  eapply prio_notin_tbl_orself; eauto.
  unfolds; splits; introv Hf; inverts Hf.
  destruct H7 as (_&_&_ &Hw &_).
  unfolds in Hw.
  assert ( (prio, wait os_stat_time n, m0) = (prio, wait os_stat_time n, m0)).
  auto.
  apply Hw in H.
  destruct H.
  destruct H3.
  usimpl H5.
  unfolds in H.
  destruct H.
  usimpl H.
  destruct H5.
  usimpl H5.
  lets Hfs : int_eq_false_false H4 H0.
  tryfalse.

  pose (Int.eq_spec (vdly-ᵢInt.one) Int.zero) as Hps. 
  rewrite H1 in Hps.
  rewrite Hps.
  unfolds.
  splits.
  unfolds.
  intros.
  unfolds in H.
  destruct H as (Ha & Hb).
  usimpl Ha.
  splits; eauto.
  unfolds.
  intros.
  inverts H.
  splits; eauto.
  unfolds.
  splits; auto.
  apply prio_in_tbl_orself.
  unfolds;
    splits;unfolds;intros;usimpl H3.
  unfolds in H.
  destruct H as (Ha & Hb & Hc).
  simpl_hyp.
  false.
  eapply prio_notin_tbl_orself; eauto.
  unfolds; splits; introv Hf; inverts Hf.

  unfolds.
  splits.
  unfolds.
  intros.
  unfolds in H.
  destruct H as (Ha & Hb).
  usimpl Ha.
  
  destruct H4.
  subst x3.
  destruct H7 as (_&_& _& Hw).
  destruct Hw as (_&_& Hw&_).
  unfolds in Hw.
  assert ( (prio, wait (os_stat_q eid) n, m) =
           (prio, wait (os_stat_q eid) n, m)).
  auto.
  apply Hw in H.
  destruct H as (Ha & Hc & Hd).
  usimpl Hc.
  usimpl Hd.
  unfolds in Ha.
  destruct Ha.
  destruct H3.
  usimpl H4.
  usimpl H.
  destruct H5.
  lets Hf: int_eq_false_false H H0.
  tryfalse.

  destruct H.
  subst x3.
  destruct H7 as (_&_& _& Hw).
  destruct Hw as (_&Hw& _&_&_).
  unfolds in Hw.
  assert ( (prio, wait (os_stat_sem eid) n, m) =
           (prio, wait (os_stat_sem eid) n, m)).
  auto.
  apply Hw in H.
  destruct H as (Ha & Hc & Hd).
  usimpl Hc.
  usimpl Hd.
  unfolds in Ha.
  destruct Ha.
  destruct H3.
  usimpl H4.
  usimpl H.
  destruct H5.
  lets Hf: int_eq_false_false H H0.
  tryfalse.

  destruct H.
  subst x3.
  destruct H7 as (_&_& _& Hw).
  destruct Hw as (_&_& _&Hw&_).
  unfolds in Hw.
  assert ( (prio, wait (os_stat_mbox eid) n, m) =
           (prio, wait (os_stat_mbox eid) n, m)).
  auto.
  apply Hw in H.
  destruct H as (Ha & Hc & Hd).
  usimpl Hc.
  usimpl Hd.
  unfolds in Ha.
  destruct Ha.
  destruct H3.
  usimpl H4.
  usimpl H.
  destruct H5.
  lets Hf: int_eq_false_false H H0.
  tryfalse.

  subst x3.
  destruct H7 as (_&_& _& Hw).
  destruct Hw as (_&_& _&_& Hw).
  unfolds in Hw.
  assert ( (prio, wait (os_stat_mutexsem eid) n, m) =
           (prio, wait (os_stat_mutexsem eid) n, m)).
  auto.
  apply Hw in H.
  destruct H as (Ha & Hc & Hd).
  usimpl Hc.
  usimpl Hd.
  unfolds in Ha.
  destruct Ha.
  destruct H3.
  usimpl H4.
  usimpl H.
  destruct H5.
  lets Hf: int_eq_false_false H H0.
  tryfalse.
  
  unfolds; introv Hf; inverts Hf.

  destruct H7 as (_&_& Hw&_).
  unfolds.
  splits;
    unfolds;
    intros;
    usimpl H3.
  unfolds in H.
  destruct H as (Ha & Hb & Hc).
  usimpl Ha.
  usimpl Hc.
  false.
  eapply prio_notin_tbl_orself; eauto.

  destruct H7 as (_&_&_& Hw).
  unfolds.
  splits;
    unfolds;
    intros;
    inverts H;
    repeat progress  destruct H4 as [Ha | H4]; tryfalse.
  inverts Ha.
  destruct Hw as (_&Hw&_&_).
  unfolds in Hw.
  assert ((prio, wait (os_stat_sem eid) n, m0) =
          (prio, wait (os_stat_sem eid) n, m0)) by auto.
  apply Hw in H.
  destruct H as (H&_).
  destruct H as (_&_&H).
  usimpl H.
  destruct H5.
  lets Hsf : int_eq_false_false H0; auto. 
  false.

  inverts Ha.
  destruct Hw as (_& _&Hw&_&_).
  unfolds in Hw.
  assert ((prio, wait (os_stat_q eid) n, m0) =
          (prio, wait (os_stat_q eid) n, m0)) by auto.
  apply Hw in H.
  destruct H as (H&_).
  destruct H as (_&_&H).
  usimpl H.
  destruct H5.
  lets Hsf : int_eq_false_false H0; auto. 
  false.

  inverts Ha.
  destruct Hw as (_& _&_&Hw&_).
  unfolds in Hw.
  assert ((prio, wait (os_stat_mbox eid) n, m0) =
          (prio, wait (os_stat_mbox eid) n, m0)) by auto.
  apply Hw in H.
  destruct H as (H&_).
  destruct H as (_&_&H).
  usimpl H.
  destruct H5.
  lets Hsf : int_eq_false_false H0; auto. 
  false.

  inverts H4.
  destruct Hw as (_& _&_&_&Hw).
  unfolds in Hw.
  assert ((prio, wait (os_stat_mutexsem eid) n, m0) =
          (prio, wait (os_stat_mutexsem eid) n, m0)) by auto.
  apply Hw in H.
  destruct H as (H&_).
  destruct H as (_&_&H).
  usimpl H.
  destruct H5.
  lets Hsf : int_eq_false_false H0; auto. 
  false.

  pose (Int.eq_spec  (vdly-ᵢInt.one) Int.zero) as Hps.
  rewrite H1 in Hps.
  rewrite Hps.
  unfolds.
  splits; unfolds; intros.
  unfolds in H.
  destruct H as (Ha & Hb).
  usimpl Ha.
  splits; eauto.

  inverts H.
  splits; auto.
  unfolds; splits; auto.
  apply prio_in_tbl_orself.

  destruct H7 as (_&_& Hw &_).
  splits;
    unfolds;
    intros;
    usimpl H4.
  unfolds in H.
  destruct H as (Ha & Hb & Hc).
  usimpl Ha.
  usimpl Hc.
  false.
  eapply prio_notin_tbl_orself; eauto.
 
  destruct H7 as (_&_&_&Hw).
  splits; unfolds; introv Hf; inverts Hf.
Qed.
 
Lemma tickchange_other_tcbnode_p_hold':
  forall a l rtbl rgrp head ectr l' rtbl' rgrp' ectr' x6,
    V_OSTCBPrio a <> V_OSTCBPrio l ->
    RL_TCBblk_P l ->
    tickchange_l l rtbl rgrp head ectr l' rtbl' rgrp' ectr' ->
    TCBNode_P a rtbl x6 ->  TCBNode_P a rtbl' x6.
Proof.
  introv Hneq Hrl Hc.
  introv Hn.
  funfold Hn.
  destruct x6.
  destruct p.
  mytac.
  rewrite H0 in Hneq.
  funfold H1.
  rewrite H7 in H3.
  inverts H3.
  unfolds.
  splits; auto.
  unfolds.
  do 6 eexists; splits; eauto.
  splits; auto.
  eexists; splits; eauto.
  inverts Hc; auto.
  funfold Hrl.
  lets Hx : set_rdy_grp_simpl H17  H18; auto.
  unfold V_OSTCBPrio in Hneq. 
  simpl in Hneq.
  assert (p<> x).
  introv Hf.
  apply Hneq.
  subst p. 
  auto.
  mytac.
  eapply R_TCB_Status_P_rtbl_add; eauto.
  funfold Hrl.
  lets Hx : set_rdy_grp_simpl H17  H18; auto.
  unfold V_OSTCBPrio in Hneq. 
  simpl in Hneq.
  assert (p<> x).
  introv Hf.
  apply Hneq.
  subst p. 
  auto.
  mytac.
  eapply R_TCB_Status_P_rtbl_add; eauto.
Qed.  

Fixpoint   RL_TCBblk_P_List (ll : list vallist):=
  match ll with
    | nil => True
    | l :: ll' =>  RL_TCBblk_P l /\ RL_TCBblk_P_List ll'
  end.


Lemma tickchange_other_tcbnode_p_hold:
  forall l' ll rtbl' x rgrp' head ectr' ll' rtbl'' rgrp'' ectr'',
    tickstep_l ll rtbl' rgrp' head ectr' ll' rtbl'' rgrp'' ectr'' ->
    R_Prio_No_Dup_L (l' :: ll) ->
    RL_TCBblk_P_List  ll ->
    TCBNode_P l' rtbl' x ->
    TCBNode_P l' rtbl'' x.
Proof.
  induction 1.
  intros.
   auto.
   intros.
   simpl in H1.
   mytac.
   simpl in H2.
   mytac.
   rewrite H4 in H5.
   inverts H5.
   eapply IHtickstep_l; eauto.
   simpl.
   eexists; splits; eauto.
   eapply tickchange_other_tcbnode_p_hold'; eauto.
   rewrite H1.
   rewrite H4.
   introv Hf.
   apply H8.
   inverts Hf.
   auto.
Qed.   

Lemma timetick_idle_in_rtbl:
  forall rtbl tls rgrp head els els' rgrp' rtbl' tls' ,
    prio_in_tbl ($ OS_IDLE_PRIO) rtbl ->
    RL_TCBblk_P_List  tls->
    tcbls_rtbl_timetci_update tls rtbl  
                              (Vint32 rgrp) head els = Some (tls', rtbl', Vint32 rgrp', els') ->
    prio_in_tbl ($ OS_IDLE_PRIO) rtbl'.
Proof.
  introv Hp Ht Htc.
  apply tick_fixpoint_convert in Htc.
  gen Htc.
  induction 1.
  intros; auto.
  intros.
  simpl in Ht.
  mytac.

  inverts H;
    try eapply IHHtc ; eauto.
  funfold H0.
  lets Hx : set_rdy_grp_simpl H7  H8; auto.
  mytac.
  assert (x =$ OS_IDLE_PRIO \/ x <>$ OS_IDLE_PRIO) by tauto.
  destruct H0.
  subst x.
  eapply prio_in_tbl_orself;auto.
  eapply prio_set_rdy_in_tbl; eauto.
  unfold OS_IDLE_PRIO.
  unfold  OS_LOWEST_PRIO.
  clear -x.
  mauto.
  funfold H0.
  lets Hx : set_rdy_grp_simpl H7  H8; auto.
  mytac.
  assert (x =$ OS_IDLE_PRIO \/ x <>$ OS_IDLE_PRIO) by tauto.
  destruct H0.
  subst x.
  eapply prio_in_tbl_orself;auto.
  eapply prio_set_rdy_in_tbl; eauto.
  unfold OS_IDLE_PRIO.
  unfold  OS_LOWEST_PRIO.
  clear -x.
  mauto.
Qed.

Lemma tickchange_other_tcblist_p_hold:
  forall  ll l  rtbl rgrp head ectr l' rtbl' rgrp' ectr' x0 x1,
    R_Prio_No_Dup_L (l :: ll) ->
    RL_TCBblk_P l  ->
    tickchange_l l rtbl rgrp head ectr l' rtbl' rgrp' ectr' -> 
    TCBList_P x0 ll rtbl x1 ->
    TCBList_P x0 ll rtbl' x1 .
Proof.
  inductions ll.
  simpl.
  intros.
  auto.
  intros.
  simpl in H2.
  mytac.
  simpl in H.
  mytac.
  simpl.
  do 4 eexists; splits; eauto.
  rewrite H2 in H7.
  inverts H7.
  lets Hsa : tickchange_other_tcbnode_p_hold' H0  H1 H5.
  rewrite H.
  rewrite H2.
  introv Hf.
  inverts Hf.
  false.
  auto.
  eapply IHll; eauto.
  simpl.
  eexists; splits; eauto.
Qed.  



Lemma TCBList_P_imp_RL:
  forall ll x0 rtbl x1,
    TCBList_P x0 ll rtbl x1 ->
    RL_TCBblk_P_List ll.
Proof.    
  inductions ll.
  intros.
  simpl; auto.
  intros.
  simpl in H.
  mytac.
  simpl.
  unfolds in  H2.
  destruct x4.
  destruct p.
  mytac.
  auto.
  eapply IHll; eauto.
Qed.

  
Lemma timetick_tcblist_prop_hold:
  forall vl x y v head ls vl' x' y' els els' ls' tcbls tcbls' tcbls'' tcbx,
    tickstep_l vl x y head ls vl' x' y' ls' ->
    R_Prio_No_Dup tcbls ->
    TCBList_P v vl x tcbls'' ->
    TcbMod.join tcbls'' tcbx tcbls ->
    tickstep' tcbls els tcbls' els' tcbls'' ->
    TCBList_P v vl' x' (TcbMod.minus tcbls' tcbx).
Proof.  
  intros.
  inductions H gen v  tcbls tcbls'' els els' tcbx.
  simpl.
  simpl in H1.
  subst.
  inverts H3.
  apply TcbMod.join_emp_eq in H2.
  subst.
  rewrite tcb_minus_self_emp.
  auto.
  apply joinsig_false in H.
  tryfalse.
  lets Hnodup: r_prio_no_dup_join_imp H3 H1 H2. 
  simpl in H2.
  mytac.
  lets Hgs : tcbjoin_get_a_my H6.
  destruct x2.
  destruct p.
  lets Hsub:TcbMod.join_sub_l H3.
  lets Hres : tickstep_decompose Hgs Hsub H4 .
  mytac.
  clear Hgs Hsub H4.
  lets Heq : tcbjoin_joinsig_eq H2 H6.
  subst x4.
  simpl.
  exists x x0.
  exists (TcbMod.minus ( TcbMod.minus tcbls' tcbx ) (TcbMod.sig x (p,x2,m))).
  exists (p,x2,m).
  splits;auto.
  eapply tickchange_eq_ostcbnext;eauto.
  lets Hget:tickstep'_other_get_eq H6 H11.
  eapply tcb_joinsig_join_get_minus_eq;eauto.
  eapply tickchange_nodup in Hnodup;eauto.
  eapply tickchange_other_tcbnode_p_hold;eauto.
  eapply TCBList_P_imp_RL; eauto.
  eapply tickchange_tcbnode_p_hold;eauto.
  apply IHtickstep_l with (v:=x0) (tcbx:=TcbMod.merge (TcbMod.sig x (p,x2,m)) tcbx) in H11.
  rewrite <- tcb_minus_mergesig_minus_minus_eq;auto.
  eapply r_prio_no_dup_setst_hold;eauto.
  eapply tickchange_other_tcblist_p_hold;eauto.
  unfolds in H7.
  mytac; auto.
  eapply joinsig_join_joinmergesig_eq_set;eauto.
Qed.



Lemma timetick_tcblist_p:
  forall v'25 v'26 v'27 v'28 v'39 x1 x2 x3 v'33 x6 v'37 v'15 v'38 v'23 v'36 x0 v'12 x head els els',
    length v'25 = length x1 ->
    tcbls_rtbl_timetci_update (v'25 ++ v'26 :: v'27) v'28 (Vint32 v'39) head els=
    Some (x1 ++ x2 :: x3, v'33, Vint32 x6, els') ->
    get_last_tcb_ptr v'25 (Vptr v'23) = Some (Vptr v'15) ->
    TCBList_P (Vptr v'23) v'25 v'28 v'37 ->
    TCBList_P (Vptr v'15) (v'26 :: v'27) v'28 v'38 ->
    tickstep v'36 v'12 x x0 ->
    TcbMod.join v'37 v'38 v'36 ->
    R_Prio_No_Dup v'36 ->
    exists tl1 tl2,  TcbMod.join tl2 tl1 x /\ TCBList_P (Vptr v'15) (x2 :: x3) v'33 tl1 /\ TCBList_P (Vptr v'23) x1 v'33 tl2.
Proof.
  introv Hlen.
  intros.
  apply tick_fixpoint_convert in H.
  lets Hx:TCBList_P_Combine H0 H4 H1 H2.
  unfolds in H3.
  lets Hy:timetick_tcblist_prop_hold H H5 Hx H3.
  instantiate (1:= TcbMod.emp).
  apply TcbMod.join_comm.
  apply TcbMod.join_emp;auto.
  rewrite tcb_minus_emp_eq in Hy.
  apply TCBList_P_Split in Hy.
  mytac.
  do 2 eexists;splits;eauto.
  assert (get_last_tcb_ptr x1 (Vptr v'23) = get_last_tcb_ptr v'25 (Vptr v'23)).
  eapply tickstep_l_get_last_tcb_ptr_eq;eauto.
  rewrite H6 in H10.
  rewrite H0 in H10.
  inverts H10;auto.
Qed.




Lemma tick_rdy_ectr'_decompose :
  forall el1 el2 x eptr e vl ectr' edl hels htls,
    get_last_ecb_ptr el1 (Vptr x) = Some (Vptr eptr) ->
    ~ In (Vptr eptr) (get_eidls (Vptr x) el1) ->
    tick_rdy_ectr' eptr vl (Vptr x) (el1 ++ e :: el2) = Some ectr'->
    ECBList_P (Vptr x) Vnull (el1 ++ e :: el2) edl hels htls ->
    exists x, rdy_ectr vl e = Some x /\ ectr' = (el1 ++ x :: el2).
Proof.
  intros.
  
  inductions el1; intros.
  simpl in H; inverts H.
  simpl in H0.
  false; apply H0.
  auto.
  
  destruct a.
  destruct el1.
  simpl in H.
  simpl in H0.
  rewrite <- app_comm_cons in H1.
  unfold tick_rdy_ectr' in H1; fold tick_rdy_ectr' in H1.
  rewrite H in H1.
  destruct (beq_addrval eptr x) eqn : eq1.
  false; apply H0; left.
  lets _H1: beq_addrval_eq eq1; substs; auto.
  destruct(tick_rdy_ectr' eptr vl (Vptr eptr) (nil ++ e :: el2)) eqn : eq2; tryfalse.
  inverts H1.
  rewrite app_nil_l in eq2.
  unfold tick_rdy_ectr' in eq2; fold tick_rdy_ectr' in eq2.
  destruct e.
  rewrite eq_beq_addrval in eq2.
  destruct (rdy_ectr vl (v1, v2)) eqn : eq3; tryfalse.
  inverts eq2.
  exists e.
  rewrite <- app_comm_cons.
  rewrite app_nil_l.
  auto.
  
  rewrite <- app_comm_cons in H1.
  unfold tick_rdy_ectr' in H1; fold tick_rdy_ectr' in H1.
  destruct(beq_addrval eptr x) eqn : eq1.
  false; apply H0.
  lets _H1: beq_addrval_eq eq1; substs.
  simpl; auto.

  destruct(V_OSEventListPtr v) eqn : eq2; tryfalse.
  destruct(tick_rdy_ectr' eptr vl v1 ((p :: el1) ++ e :: el2)) eqn : eq3; tryfalse.
  inverts H1.
  
  rewrite <- app_comm_cons in H2.
  unfold ECBList_P in H2; fold ECBList_P in H2.
  mytac; destruct edl; tryfalse; mytac.
  rewrite eq2 in H3; inverts H3.
  
  assert(get_last_ecb_ptr (p :: el1) x3 = Some (Vptr eptr)).
  clear -H.
  simpl in H.
  simpl; auto.
  
  assert(~In (Vptr eptr) (get_eidls x3 (p :: el1))).
  clear - H0 eq2.
  intro; apply H0.
  unfold get_eidls in H; unfold In in H.
  unfold get_eidls; unfold In.
  unfold get_eid_ecbls; fold get_eid_ecbls.
  destruct p.
  unfold removelast; fold removelast.
  unfold get_eid_ecbls in H.
  unfolds in eq2.
  apply nth_val_nth_val'_some_eq in eq2.
  rewrite eq2.
  destruct H; auto.
  
  assert(exists x, x3 = Vptr x).
  clear - H6 eq2.
  simpl in H6; mytac.
  destruct edl; tryfalse; mytac.
  eauto.
  
  mytac.
  inverts H1.
  lets _H1: IHel1 H3 H7 eq3 H6.
  mytac.
  eexists; eauto.
Qed.


Lemma tick_rdy_ectr_split:
  forall  ectr head  vnext vprev eptr msg vdly stat prio vx vy vbitx vbity ectr' m wl hels htls edata,
    tick_rdy_ectr' eptr
                   (vnext
                      :: vprev
                      :: Vptr eptr
                      :: msg
                      :: Vint32 vdly
                      :: stat
                      :: Vint32 prio
                      :: Vint32 vx
                      :: Vint32 vy
                      :: Vint32 vbitx :: Vint32 vbity :: nil)
                   head ectr = Some ectr' ->
    EcbMod.get hels eptr = Some (m, wl) ->
    ECBList_P head Vnull ectr edata hels htls ->
    exists l1 l2 a b a' b' c d e,
      rdy_ectr  (vnext
                   :: vprev
                   :: Vptr eptr
                   :: msg
                   :: Vint32 vdly
                   :: stat
                   :: Vint32 prio
                   :: Vint32 vx
                   :: Vint32 vy
                   :: Vint32 vbitx :: Vint32 vbity :: nil) (a,b) = Some (a',b') /\ 
      ectr = l1 ++ ((a,b)::nil) ++ l2 /\
      edata = c ++ (e::nil) ++ d /\
      length c = length l1 /\
      ectr' = l1 ++ ((a',b')::nil) ++ l2 /\
      get_last_ecb_ptr l1 head = Some (Vptr eptr).
Proof.
  intros.
  assert(exists x, head = Vptr x) as Hx.
  destruct head;
  try solve [unfolds in H1; destruct ectr; destruct edata; mytac; tryfalse].
  eauto.
  mytac.

  pose proof ECBList_P_els_get_split H1 H0; mytac.
  destruct x1; destruct x3; simpl in H3; mytac; tryfalse.
  destruct e; mytac.
  destruct x0; destruct x2; try solve [simpl in H2; mytac; tryfalse].
  simpl in H2; mytac.
  rewrite app_nil_l in H.
  inverts H5.
  do 2 rewrite app_nil_l in H1.
  inverts H3; inverts H11.
  unfold tick_rdy_ectr' in H.
  rewrite eq_beq_addrval in H.
  destruct(rdy_ectr
          (vnext
           :: vprev
              :: Vptr x6
                 :: msg
                    :: Vint32 vdly
                       :: stat
                          :: Vint32 prio
                             :: Vint32 vx
                                :: Vint32 vy
                                   :: Vint32 vbitx :: Vint32 vbity :: nil)
          (v, v0)) eqn : eq1; tryfalse.
  invert H.
  destruct e.
  intros; substs.
  exists (nil:(list EventCtr)).
  exists x1 v v0 v1 v2.
  exists (nil:(list EventData)) x3 e0.
  mytac; eauto.
  
  rewrite list_cons_assoc in H1.
  inverts H3.
  
  assert (get_last_ecb_ptr (e :: x0) (Vptr x) = Some (Vptr x6)).
  eapply ECBList_P_get_last_ecb_ptr; eauto.
  
  pose proof ECBList_P_get_eidls_not_in H1 H3.
  
  rewrite <- list_cons_assoc in H1.
  lets _H: tick_rdy_ectr'_decompose H3 H10 H H1; mytac.
  destruct x10.
  destruct e.
  exists ((v3, v4)::x0) x1 v v0 v1 v2; exists (e1::x2) x3 e0.
  mytac; eauto.
  
  symmetry.
  eapply ecblistp_length_eq_1; eauto.
Qed.




Lemma ecblist_p_tick_rdy_ectr_q:
  forall  ectr head  vnext vprev eptr msg vdly stat prio vx vy vbitx vbity ectr' ,
    tick_rdy_ectr' eptr
                   (vnext
                      :: vprev
                      :: Vptr eptr
                      :: msg
                      :: Vint32 vdly
                      :: stat
                      :: Vint32 prio
                      :: Vint32 vx
                      :: Vint32 vy
                      :: Vint32 vbitx :: Vint32 vbity :: nil)
                   head ectr = Some ectr'->
    forall  htls x p m x0 eid edata hels cur m0 wl rtbl,
      get htls x = Some (p, wait x0 Int.one, m) ->
      x0 = os_stat_q eid ->
      ECBList_P head Vnull ectr edata hels htls ->
      RH_TCBList_ECBList_P hels htls cur ->
      EcbMod.get hels eid = Some (m0, wl) ->
      TCBNode_P
        (vnext
           :: vprev
           :: Vptr eptr
           :: msg
           :: Vint32 vdly
           :: stat
           :: Vint32 prio
           :: Vint32 vx
           :: Vint32 vy
           :: Vint32 vbitx :: Vint32 vbity :: nil)
        rtbl (p, wait x0 Int.one, m) ->
      R_Prio_No_Dup htls ->
      ECBList_P head Vnull ectr' edata
                (EcbMod.set hels eid (m0, remove_tid x wl)) (set htls x (p, rdy, m)).
Proof.
  intros.

  unfolds in H5.
  destruct H5 as (Hm & Hp & Hrl & Hrs).
  unfolds in Hm;simpl in Hm;inverts Hm.
  unfolds in Hp;simpl in Hp;inverts Hp.
  unfolds in Hrs.
  mytac.
  unfolds in H9.
  mytac.
  unfolds in H10.
  mytac.

  assert ((p, wait (os_stat_q eid) Int.one, m) =
          (p, wait (os_stat_q eid) Int.one, m)) by auto.
  apply H10 in H13.
  mytac.
  unfolds in H14;simpl in H14;inverts H14.
  unfolds in H15;simpl in H15;inverts H15.
  
  lets Hx:tick_rdy_ectr_split H H4 H2.
  mytac.
  rename H19 into Hlink.
  clear H.
  unfolds in H14.
  xunfold H14; inverts H14.
  
  clear H5 H7 H8 H1 H9 H10 H11 H12.
  symmetry in HeqH7,HeqH8.
  unfolds in HeqH1;simpl in HeqH1;inverts HeqH1.
  unfolds in HeqH3;simpl in HeqH3;inverts HeqH3.
  unfolds in HeqH5;simpl in HeqH5;inverts HeqH5.
  apply ecblist_p_decompose in H2;auto.
  mytac.
  simpl in H1.
  mytac.
  eapply ecblist_p_compose' with (mq:=(m0, remove_tid x wl));eauto.
  lets Hx:get_last_ecb_ptr_eq H Hlink.
  subst x9.
  instantiate (1:=eid).
  unfolds.
  splits.

  unfolds in H5.
  destructs H5.

  unfolds in H1.
  destructs H1.
  
  unfolds.
  splits.

  unfolds in H1.
  unfolds.
  intros.
  funfold Hrl.
  apply prio_wt_inq_convert in H16.
  destruct H16 as (Hprs1 & Hprs2).
  lets Hrs : prio_wt_inq_tid_neq HeqH7 H33.
  destruct Hrs.
  apply H7 in  Hprs1.
  destruct Hprs1.
  lets Hx:H1 H18.
  rewrite Int.repr_unsigned in Hx.
  destruct Hx as (tid' & nn & mm & Htg).
  simpl;auto.
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H20.
  subst tid'.
  unfold Maps.get in *;simpl in *.
  rewrite H0 in Htg.
  inverts Htg;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false;eauto.

  unfolds in H12.
  unfolds.
  intros.
  funfold Hrl.
  apply prio_wt_inq_convert in H16.
  destruct H16 as (Hprs1 & Hprs2).
  lets Hrs : prio_wt_inq_tid_neq HeqH7 H33.
  destruct Hrs.
  apply H7 in  Hprs1.
  destruct Hprs1.
  lets Hx:H12 H18.
  rewrite Int.repr_unsigned in Hx.
  destruct Hx as (tid' & nn & mm & Htg).
  simpl;auto.
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H20.
  subst tid'.
  unfold Maps.get in *;simpl in *.
  rewrite H0 in Htg.
  inverts Htg;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false;eauto.

  unfolds in H14.
  unfolds.
  intros.
  funfold Hrl.
  apply prio_wt_inq_convert in H16.
  destruct H16 as (Hprs1 & Hprs2).
  lets Hrs : prio_wt_inq_tid_neq HeqH7 H33.
  destruct Hrs.
  apply H7 in  Hprs1.
  destruct Hprs1.
  lets Hx:H14 H18.
  rewrite Int.repr_unsigned in Hx.
  destruct Hx as (tid' & nn & mm & Htg).
  simpl;auto.
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H20.
  subst tid'.
  unfold Maps.get in *;simpl in *.
  rewrite H0 in Htg.
  inverts Htg;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false;eauto.

  unfolds in H15.
  unfolds.
  intros.
  funfold Hrl.
  apply prio_wt_inq_convert in H16.
  destruct H16 as (Hprs1 & Hprs2).
  lets Hrs : prio_wt_inq_tid_neq HeqH7 H33.
  destruct Hrs.
  apply H7 in  Hprs1.
  destruct Hprs1.
  lets Hx:H15 H18.
  rewrite Int.repr_unsigned in Hx.
  destruct Hx as (tid' & nn & mm & Htg).
  simpl;auto.
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H20.
  subst tid'.
  unfold Maps.get in *;simpl in *.
  rewrite H0 in Htg.
  inverts Htg;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false;eauto.

  unfolds in H5.
  mytac.
  unfolds in H5.
  destruct H5 as (Hb&Hb'&Hb''&Hb''').
  splits;intros prio' mm nn tid'.
  
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H5.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  unfolds in Hb.
  lets Hga : Hb Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in H6.
  lets Hneqp: H6 H5 H0 Hgs.
  funfold Hrl.
  lets Hrs : prio_wt_inq_tid_neq  HeqH7 H28.
  assert ( PrioWaitInQ (Int.unsigned prio') x3 /\ prio' <> x5) .
  splits; auto.
  destruct Hrs as (_ & Hrs).
  apply Hrs in H7.
  auto.
  simpl;auto.

  assert (x = tid' \/ x <> tid') by tauto.
  destruct H5.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  unfolds in Hb'.
  lets Hga : Hb' Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in H6.
  lets Hneqp: H6 H5 H0 Hgs.
  funfold Hrl.
  lets Hrs : prio_wt_inq_tid_neq  HeqH7 H28.
  assert ( PrioWaitInQ (Int.unsigned prio') x3 /\ prio' <> x5) .
  splits; auto.
  destruct Hrs as (_ & Hrs).
  apply Hrs in H7.
  auto.
  simpl;auto.

  assert (x = tid' \/ x <> tid') by tauto.
  destruct H5.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  unfolds in Hb''.
  lets Hga : Hb'' Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in H6.
  lets Hneqp: H6 H5 H0 Hgs.
  funfold Hrl.
  lets Hrs : prio_wt_inq_tid_neq  HeqH7 H28.
  assert ( PrioWaitInQ (Int.unsigned prio') x3 /\ prio' <> x5) .
  splits; auto.
  destruct Hrs as (_ & Hrs).
  apply Hrs in H7.
  auto.
  simpl;auto.
  
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H5.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  unfolds in Hb'''.
  lets Hga : Hb''' Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in H6.
  lets Hneqp: H6 H5 H0 Hgs.
  funfold Hrl.
  lets Hrs : prio_wt_inq_tid_neq  HeqH7 H28.
  assert ( PrioWaitInQ (Int.unsigned prio') x3 /\ prio' <> x5) .
  splits; auto.
  destruct Hrs as (_ & Hrs).
  apply Hrs in H7.
  auto.
  simpl;auto.
  
  unfolds in H5;destructs H5.
  simpl in H11;simpl;auto.
  
  instantiate (1:=x2).
  eapply ECBList_P_Set_Rdy_hold;eauto.
  eapply joinsig_join_getnone; eauto.
  
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.
  eauto.
  
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.
  auto.
  
  unfolds in H7;simpl in H7;inverts H7.
  eapply ECBList_P_Set_Rdy_hold;eauto.
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.
  eapply  joinsig_get_none; eauto.
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.

  lets Heq:ecbmod_get_joinsig_join_eq H4 H8 H2.
  subst.
  clear -H9.
  unfold RLH_ECBData_P in *.
  destruct x8;destruct m0;mytac;auto;tryfalse.
  unfold RH_ECB_P in *.
  mytac.
  intros.
  apply H2 in H4.
  subst;simpl;auto.
  intros.
  apply H3.
  intro.
  destruct H4.
  subst;simpl;auto.
  unfold RH_ECB_P in *.
  mytac.
  intros.
  apply H in H1.
  subst;simpl;auto.
  intros.
  apply H0.
  intro;destruct H1;subst;simpl;auto.
  unfold RH_ECB_P in *.
  mytac.
  intros.
  apply H in H1.
  subst;simpl;auto.
  intros.
  apply H0.
  intro;destruct H1;subst;simpl;auto.
  
  unfold RH_ECB_P in *.
  mytac;auto.
  intros.
  apply H0 in H4;auto.
  subst;simpl;auto.
  auto.
  intros.
  eapply H2;eauto.
  intro.
  destruct H4.
  subst.
  simpl;auto.
  
  
  instantiate (1:=EcbMod.set x4 eid (m0, remove_tid x wl)).
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.
  eapply EcbMod.joinsig_set;eauto.
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.
  eapply EcbMod.my_joinsig_join_set;eauto.

  
  clear H5 H7 H8 H1 H9 H10 H11 H12.
  symmetry in HeqH7,HeqH8.
  unfolds in HeqH1;simpl in HeqH1;inverts HeqH1.
  unfolds in HeqH3;simpl in HeqH3;inverts HeqH3.
  unfolds in HeqH5;simpl in HeqH5;inverts HeqH5.
  apply ecblist_p_decompose in H2;auto.
  mytac.
  simpl in H1.
  mytac.

  eapply ecblist_p_compose' with (mq:=(m0, remove_tid x wl));eauto.
  lets Hx:get_last_ecb_ptr_eq H Hlink.
  subst x9.
  instantiate (1:=eid).
  unfolds.
  splits.

  unfolds in H5.
  destructs H5.

  unfolds in H1.
  destructs H1.
  
  unfolds.
  splits.

  unfolds in H1.
  unfolds.
  intros.
  funfold Hrl.
  apply prio_wt_inq_convert in H16.
  destruct H16 as (Hprs1 & Hprs2).
  lets Hrs : prio_wt_inq_tid_neq HeqH7 H33.
  destruct Hrs.
  apply H7 in  Hprs1.
  destruct Hprs1.
  lets Hx:H1 H18.
  rewrite Int.repr_unsigned in Hx.
  destruct Hx as (tid' & nn & mm & Htg).
  simpl;auto.
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H20.
  subst tid'.
  unfold Maps.get in *;simpl in *.
  rewrite H0 in Htg.
  inverts Htg;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false;eauto.

  unfolds in H12.
  unfolds.
  intros.
  funfold Hrl.
  apply prio_wt_inq_convert in H16.
  destruct H16 as (Hprs1 & Hprs2).
  lets Hrs : prio_wt_inq_tid_neq HeqH7 H33.
  destruct Hrs.
  apply H7 in  Hprs1.
  destruct Hprs1.
  lets Hx:H12 H18.
  rewrite Int.repr_unsigned in Hx.
  destruct Hx as (tid' & nn & mm & Htg).
  simpl;auto.
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H20.
  subst tid'.
  unfold Maps.get in *;simpl in *.
  rewrite H0 in Htg.
  inverts Htg;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false;eauto.

  unfolds in H14.
  unfolds.
  intros.
  funfold Hrl.
  apply prio_wt_inq_convert in H16.
  destruct H16 as (Hprs1 & Hprs2).
  lets Hrs : prio_wt_inq_tid_neq HeqH7 H33.
  destruct Hrs.
  apply H7 in  Hprs1.
  destruct Hprs1.
  lets Hx:H14 H18.
  rewrite Int.repr_unsigned in Hx.
  destruct Hx as (tid' & nn & mm & Htg).
  simpl;auto.
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H20.
  subst tid'.
  unfold Maps.get in *;simpl in *.
  rewrite H0 in Htg.
  inverts Htg;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false;eauto.

  unfolds in H15.
  unfolds.
  intros.
  funfold Hrl.
  apply prio_wt_inq_convert in H16.
  destruct H16 as (Hprs1 & Hprs2).
  lets Hrs : prio_wt_inq_tid_neq HeqH7 H33.
  destruct Hrs.
  apply H7 in  Hprs1.
  destruct Hprs1.
  lets Hx:H15 H18.
  rewrite Int.repr_unsigned in Hx.
  destruct Hx as (tid' & nn & mm & Htg).
  simpl;auto.
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H20.
  subst tid'.
  unfold Maps.get in *;simpl in *.
  rewrite H0 in Htg.
  inverts Htg;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false;eauto.

  unfolds in H5.
  mytac.
  unfolds in H5.
  destruct H5 as (Hb&Hb'&Hb''&Hb''').
  splits;intros prio' mm nn tid'.
  
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H5.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  unfolds in Hb.
  lets Hga : Hb Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in H6.
  lets Hneqp: H6 H5 H0 Hgs.
  funfold Hrl.
  lets Hrs : prio_wt_inq_tid_neq  HeqH7 H28.
  assert ( PrioWaitInQ (Int.unsigned prio') x3 /\ prio' <> x5) .
  splits; auto.
  destruct Hrs as (_ & Hrs).
  apply Hrs in H7.
  auto.
  simpl;auto.

  assert (x = tid' \/ x <> tid') by tauto.
  destruct H5.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  unfolds in Hb'.
  lets Hga : Hb' Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in H6.
  lets Hneqp: H6 H5 H0 Hgs.
  funfold Hrl.
  lets Hrs : prio_wt_inq_tid_neq  HeqH7 H28.
  assert ( PrioWaitInQ (Int.unsigned prio') x3 /\ prio' <> x5) .
  splits; auto.
  destruct Hrs as (_ & Hrs).
  apply Hrs in H7.
  auto.
  simpl;auto.

  assert (x = tid' \/ x <> tid') by tauto.
  destruct H5.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  unfolds in Hb''.
  lets Hga : Hb'' Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in H6.
  lets Hneqp: H6 H5 H0 Hgs.
  funfold Hrl.
  lets Hrs : prio_wt_inq_tid_neq  HeqH7 H28.
  assert ( PrioWaitInQ (Int.unsigned prio') x3 /\ prio' <> x5) .
  splits; auto.
  destruct Hrs as (_ & Hrs).
  apply Hrs in H7.
  auto.
  simpl;auto.
  
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H5.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  unfolds in Hb'''.
  lets Hga : Hb''' Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in H6.
  lets Hneqp: H6 H5 H0 Hgs.
  funfold Hrl.
  lets Hrs : prio_wt_inq_tid_neq  HeqH7 H28.
  assert ( PrioWaitInQ (Int.unsigned prio') x3 /\ prio' <> x5) .
  splits; auto.
  destruct Hrs as (_ & Hrs).
  apply Hrs in H7.
  auto.
  simpl;auto.
  
  unfolds in H5;destructs H5.
  simpl in H11;simpl;auto.
  
  instantiate (1:=x2).
  eapply ECBList_P_Set_Rdy_hold;eauto.
  eapply joinsig_join_getnone; eauto.
  
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.
  eauto.
  
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.
  auto.
  
  unfolds in H7;simpl in H7;inverts H7.
  eapply ECBList_P_Set_Rdy_hold;eauto.
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.
  eapply  joinsig_get_none; eauto.
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.

  lets Heq:ecbmod_get_joinsig_join_eq H4 H8 H2.
  subst.
  clear -H9.
  unfold RLH_ECBData_P in *.
  destruct x8;destruct m0;mytac;auto;tryfalse.
  unfold RH_ECB_P in *.
  mytac.
  intros.
  apply H2 in H4.
  subst;simpl;auto.
  intros.
  apply H3.
  intro.
  destruct H4.
  subst;simpl;auto.
  unfold RH_ECB_P in *.
  mytac.
  intros.
  apply H in H1.
  subst;simpl;auto.
  intros.
  apply H0.
  intro;destruct H1;subst;simpl;auto.
  unfold RH_ECB_P in *.
  mytac.
  intros.
  apply H in H1.
  subst;simpl;auto.
  intros.
  apply H0.
  intro;destruct H1;subst;simpl;auto.
   
  unfold RH_ECB_P in *.
  mytac;auto.
  intros.
  apply H0 in H4;auto.
  subst;simpl;auto.
  auto.
  intros.
  eapply H2;eauto.
  intro.
  destruct H4.
  subst.
  simpl;auto.
  
  instantiate (1:=EcbMod.set x4 eid (m0, remove_tid x wl)).
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.
  eapply EcbMod.joinsig_set;eauto.
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.
  eapply EcbMod.my_joinsig_join_set;eauto.
Qed.


Lemma ecblist_p_tick_rdy_ectr_sem:
  forall  ectr head  vnext vprev eptr msg vdly stat prio vx vy vbitx vbity ectr' ,
    tick_rdy_ectr' eptr
                   (vnext
                      :: vprev
                      :: Vptr eptr
                      :: msg
                      :: Vint32 vdly
                      :: stat
                      :: Vint32 prio
                      :: Vint32 vx
                      :: Vint32 vy
                      :: Vint32 vbitx :: Vint32 vbity :: nil)
                   head ectr = Some ectr'->
    forall  htls x p m x0 eid edata hels cur m0 wl rtbl,
      get htls x = Some (p, wait x0 Int.one, m) ->
      x0 = os_stat_sem eid ->
      ECBList_P head Vnull ectr edata hels htls ->
      RH_TCBList_ECBList_P hels htls cur ->
      EcbMod.get hels eid = Some (m0, wl) ->
      TCBNode_P
        (vnext
           :: vprev
           :: Vptr eptr
           :: msg
           :: Vint32 vdly
           :: stat
           :: Vint32 prio
           :: Vint32 vx
           :: Vint32 vy
           :: Vint32 vbitx :: Vint32 vbity :: nil)
        rtbl (p, wait x0 Int.one, m) ->
      R_Prio_No_Dup htls ->
      ECBList_P head Vnull ectr' edata
                (EcbMod.set hels eid (m0, remove_tid x wl)) (set htls x (p, rdy, m)).
Proof.
  intros.
  unfolds in H5.
  destruct H5 as (Hm & Hp & Hrl & Hrs).
  unfolds in Hm;simpl in Hm;inverts Hm.
  unfolds in Hp;simpl in Hp;inverts Hp.
  unfolds in Hrs.
  mytac.
  unfolds in H9.
  mytac.
  unfolds in H9.
  mytac.

  assert ((p, wait (os_stat_sem eid) Int.one, m) =
          (p, wait (os_stat_sem eid) Int.one, m)) by auto.
  apply H9 in H13.
  mytac.
  unfolds in H14;simpl in H14;inverts H14.
  unfolds in H15;simpl in H15;inverts H15.
  
  lets Hx:tick_rdy_ectr_split H H4 H2.
  mytac.
  rename H19 into Hlink.
  clear H.
  unfolds in H14.
  xunfold H14; inverts H14.
  
  clear H5 H7 H8 H1 H9 H10 H11 H12.
  symmetry in HeqH7,HeqH8.
  unfolds in HeqH1;simpl in HeqH1;inverts HeqH1.
  unfolds in HeqH3;simpl in HeqH3;inverts HeqH3.
  unfolds in HeqH5;simpl in HeqH5;inverts HeqH5.
  apply ecblist_p_decompose in H2;auto.
  mytac.
  simpl in H1.
  mytac.

  eapply ecblist_p_compose' with (mq:=(m0, remove_tid x wl));eauto.
  lets Hx:get_last_ecb_ptr_eq H Hlink.
  subst x9.
  instantiate (1:=eid).
  unfolds.
  splits.

  unfolds in H5.
  destructs H5.

  unfolds in H1.
  destructs H1.
  
  unfolds.
  splits.

  unfolds in H1.
  unfolds.
  intros.
  funfold Hrl.
  apply prio_wt_inq_convert in H16.
  destruct H16 as (Hprs1 & Hprs2).
  lets Hrs : prio_wt_inq_tid_neq HeqH7 H33.
  destruct Hrs.
  apply H7 in  Hprs1.
  destruct Hprs1.
  lets Hx:H1 H18.
  rewrite Int.repr_unsigned in Hx.
  destruct Hx as (tid' & nn & mm & Htg).
  simpl;auto.
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H20.
  subst tid'.
  unfold Maps.get in *;simpl in *.
  rewrite H0 in Htg.
  inverts Htg;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false;eauto.

  unfolds in H12.
  unfolds.
  intros.
  funfold Hrl.
  apply prio_wt_inq_convert in H16.
  destruct H16 as (Hprs1 & Hprs2).
  lets Hrs : prio_wt_inq_tid_neq HeqH7 H33.
  destruct Hrs.
  apply H7 in  Hprs1.
  destruct Hprs1.
  lets Hx:H12 H18.
  rewrite Int.repr_unsigned in Hx.
  destruct Hx as (tid' & nn & mm & Htg).
  simpl;auto.
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H20.
  subst tid'.
  unfold Maps.get in *;simpl in *.
  rewrite H0 in Htg.
  inverts Htg;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false;eauto.

  unfolds in H14.
  unfolds.
  intros.
  funfold Hrl.
  apply prio_wt_inq_convert in H16.
  destruct H16 as (Hprs1 & Hprs2).
  lets Hrs : prio_wt_inq_tid_neq HeqH7 H33.
  destruct Hrs.
  apply H7 in  Hprs1.
  destruct Hprs1.
  lets Hx:H14 H18.
  rewrite Int.repr_unsigned in Hx.
  destruct Hx as (tid' & nn & mm & Htg).
  simpl;auto.
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H20.
  subst tid'.
  unfold Maps.get in *;simpl in *.
  rewrite H0 in Htg.
  inverts Htg;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false;eauto.

  unfolds in H15.
  unfolds.
  intros.
  funfold Hrl.
  apply prio_wt_inq_convert in H16.
  destruct H16 as (Hprs1 & Hprs2).
  lets Hrs : prio_wt_inq_tid_neq HeqH7 H33.
  destruct Hrs.
  apply H7 in  Hprs1.
  destruct Hprs1.
  lets Hx:H15 H18.
  rewrite Int.repr_unsigned in Hx.
  destruct Hx as (tid' & nn & mm & Htg).
  simpl;auto.
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H20.
  subst tid'.
  unfold Maps.get in *;simpl in *.
  rewrite H0 in Htg.
  inverts Htg;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false;eauto.

  unfolds in H5.
  mytac.
  unfolds in H5.
  destruct H5 as (Hb&Hb'&Hb''&Hb''').
  splits;intros prio' mm nn tid'.
  
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H5.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  unfolds in Hb.
  lets Hga : Hb Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in H6.
  lets Hneqp: H6 H5 H0 Hgs.
  funfold Hrl.
  lets Hrs : prio_wt_inq_tid_neq  HeqH7 H28.
  assert ( PrioWaitInQ (Int.unsigned prio') x3 /\ prio' <> x5) .
  splits; auto.
  destruct Hrs as (_ & Hrs).
  apply Hrs in H7.
  auto.
  simpl;auto.

  assert (x = tid' \/ x <> tid') by tauto.
  destruct H5.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  unfolds in Hb'.
  lets Hga : Hb' Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in H6.
  lets Hneqp: H6 H5 H0 Hgs.
  funfold Hrl.
  lets Hrs : prio_wt_inq_tid_neq  HeqH7 H28.
  assert ( PrioWaitInQ (Int.unsigned prio') x3 /\ prio' <> x5) .
  splits; auto.
  destruct Hrs as (_ & Hrs).
  apply Hrs in H7.
  auto.
  simpl;auto.

  assert (x = tid' \/ x <> tid') by tauto.
  destruct H5.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  unfolds in Hb''.
  lets Hga : Hb'' Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in H6.
  lets Hneqp: H6 H5 H0 Hgs.
  funfold Hrl.
  lets Hrs : prio_wt_inq_tid_neq  HeqH7 H28.
  assert ( PrioWaitInQ (Int.unsigned prio') x3 /\ prio' <> x5) .
  splits; auto.
  destruct Hrs as (_ & Hrs).
  apply Hrs in H7.
  auto.
  simpl;auto.
  
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H5.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  unfolds in Hb'''.
  lets Hga : Hb''' Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in H6.
  lets Hneqp: H6 H5 H0 Hgs.
  funfold Hrl.
  lets Hrs : prio_wt_inq_tid_neq  HeqH7 H28.
  assert ( PrioWaitInQ (Int.unsigned prio') x3 /\ prio' <> x5) .
  splits; auto.
  destruct Hrs as (_ & Hrs).
  apply Hrs in H7.
  auto.
  simpl;auto.
  
  unfolds in H5;destructs H5.
  simpl in H11;simpl;auto.
  
  instantiate (1:=x2).
  

  eapply ECBList_P_Set_Rdy_SEM_hold;eauto.
  eapply joinsig_join_getnone; eauto.
  
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.
  eauto.
  
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.
  auto.
  
  unfolds in H7;simpl in H7;inverts H7.
  eapply ECBList_P_Set_Rdy_SEM_hold;eauto.
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.
  eapply  joinsig_get_none; eauto.
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.

  lets Heq:ecbmod_get_joinsig_join_eq H4 H8 H2.
  subst.
  clear -H9.
  unfold RLH_ECBData_P in *.
  destruct x8;destruct m0;mytac;auto;tryfalse.
  unfold RH_ECB_P in *.
  mytac.
  intros.
  apply H2 in H4.
  subst;simpl;auto.
  intros.
  apply H3.
  intro.
  destruct H4.
  subst;simpl;auto.
  unfold RH_ECB_P in *.
  mytac.
  intros.
  apply H in H1.
  subst;simpl;auto.
  intros.
  apply H0.
  intro;destruct H1;subst;simpl;auto.
  unfold RH_ECB_P in *.
  mytac.
  intros.
  apply H in H1.
  subst;simpl;auto.
  intros.
  apply H0.
  intro;destruct H1;subst;simpl;auto.

   
  unfold RH_ECB_P in *.
  mytac;auto.
  intros.
  apply H0 in H4;auto.
  subst;simpl;auto.
  auto.
  intros.
  eapply H2;eauto.
  intro.
  destruct H4.
  subst.
  simpl;auto.
  
  instantiate (1:=EcbMod.set x4 eid (m0, remove_tid x wl)).
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.
  eapply EcbMod.joinsig_set;eauto.
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.
  eapply EcbMod.my_joinsig_join_set;eauto.

  
  clear H5 H7 H8 H1 H9 H10 H11 H12.
  symmetry in HeqH7,HeqH8.
  unfolds in HeqH1;simpl in HeqH1;inverts HeqH1.
  unfolds in HeqH3;simpl in HeqH3;inverts HeqH3.
  unfolds in HeqH5;simpl in HeqH5;inverts HeqH5.
  apply ecblist_p_decompose in H2;auto.
  mytac.
  simpl in H1.
  mytac.

  eapply ecblist_p_compose' with (mq:=(m0, remove_tid x wl));eauto.
  lets Hx:get_last_ecb_ptr_eq H Hlink.
  subst x9.
  instantiate (1:=eid).
  unfolds.
  splits.

  unfolds in H5.
  destructs H5.

  unfolds in H1.
  destructs H1.
  
  unfolds.
  splits.

  unfolds in H1.
  unfolds.
  intros.
  funfold Hrl.
  apply prio_wt_inq_convert in H16.
  destruct H16 as (Hprs1 & Hprs2).
  lets Hrs : prio_wt_inq_tid_neq HeqH7 H33.
  destruct Hrs.
  apply H7 in  Hprs1.
  destruct Hprs1.
  lets Hx:H1 H18.
  rewrite Int.repr_unsigned in Hx.
  destruct Hx as (tid' & nn & mm & Htg).
  simpl;auto.
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H20.
  subst tid'.
  unfold Maps.get in *;simpl in *.
  rewrite H0 in Htg.
  inverts Htg;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false;eauto.

  unfolds in H12.
  unfolds.
  intros.
  funfold Hrl.
  apply prio_wt_inq_convert in H16.
  destruct H16 as (Hprs1 & Hprs2).
  lets Hrs : prio_wt_inq_tid_neq HeqH7 H33.
  destruct Hrs.
  apply H7 in  Hprs1.
  destruct Hprs1.
  lets Hx:H12 H18.
  rewrite Int.repr_unsigned in Hx.
  destruct Hx as (tid' & nn & mm & Htg).
  simpl;auto.
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H20.
  subst tid'.
  unfold Maps.get in *;simpl in *.
  rewrite H0 in Htg.
  inverts Htg;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false;eauto.

  unfolds in H14.
  unfolds.
  intros.
  funfold Hrl.
  apply prio_wt_inq_convert in H16.
  destruct H16 as (Hprs1 & Hprs2).
  lets Hrs : prio_wt_inq_tid_neq HeqH7 H33.
  destruct Hrs.
  apply H7 in  Hprs1.
  destruct Hprs1.
  lets Hx:H14 H18.
  rewrite Int.repr_unsigned in Hx.
  destruct Hx as (tid' & nn & mm & Htg).
  simpl;auto.
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H20.
  subst tid'.
  unfold Maps.get in *;simpl in *.
  rewrite H0 in Htg.
  inverts Htg;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false;eauto.

  unfolds in H15.
  unfolds.
  intros.
  funfold Hrl.
  apply prio_wt_inq_convert in H16.
  destruct H16 as (Hprs1 & Hprs2).
  lets Hrs : prio_wt_inq_tid_neq HeqH7 H33.
  destruct Hrs.
  apply H7 in  Hprs1.
  destruct Hprs1.
  lets Hx:H15 H18.
  rewrite Int.repr_unsigned in Hx.
  destruct Hx as (tid' & nn & mm & Htg).
  simpl;auto.
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H20.
  subst tid'.
  unfold Maps.get in *;simpl in *.
  rewrite H0 in Htg.
  inverts Htg;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false;eauto.

  unfolds in H5.
  mytac.
  unfolds in H5.
  destruct H5 as (Hb&Hb'&Hb''&Hb''').
  splits;intros prio' mm nn tid'.
  
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H5.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  unfolds in Hb.
  lets Hga : Hb Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in H6.
  lets Hneqp: H6 H5 H0 Hgs.
  funfold Hrl.
  lets Hrs : prio_wt_inq_tid_neq  HeqH7 H28.
  assert ( PrioWaitInQ (Int.unsigned prio') x3 /\ prio' <> x5) .
  splits; auto.
  destruct Hrs as (_ & Hrs).
  apply Hrs in H7.
  auto.
  simpl;auto.

  assert (x = tid' \/ x <> tid') by tauto.
  destruct H5.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  unfolds in Hb'.
  lets Hga : Hb' Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in H6.
  lets Hneqp: H6 H5 H0 Hgs.
  funfold Hrl.
  lets Hrs : prio_wt_inq_tid_neq  HeqH7 H28.
  assert ( PrioWaitInQ (Int.unsigned prio') x3 /\ prio' <> x5) .
  splits; auto.
  destruct Hrs as (_ & Hrs).
  apply Hrs in H7.
  auto.
  simpl;auto.

  assert (x = tid' \/ x <> tid') by tauto.
  destruct H5.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  unfolds in Hb''.
  lets Hga : Hb'' Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in H6.
  lets Hneqp: H6 H5 H0 Hgs.
  funfold Hrl.
  lets Hrs : prio_wt_inq_tid_neq  HeqH7 H28.
  assert ( PrioWaitInQ (Int.unsigned prio') x3 /\ prio' <> x5) .
  splits; auto.
  destruct Hrs as (_ & Hrs).
  apply Hrs in H7.
  auto.
  simpl;auto.
  
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H5.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  unfolds in Hb'''.
  lets Hga : Hb''' Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in H6.
  lets Hneqp: H6 H5 H0 Hgs.
  funfold Hrl.
  lets Hrs : prio_wt_inq_tid_neq  HeqH7 H28.
  assert ( PrioWaitInQ (Int.unsigned prio') x3 /\ prio' <> x5) .
  splits; auto.
  destruct Hrs as (_ & Hrs).
  apply Hrs in H7.
  auto.
  simpl;auto.
  
  unfolds in H5;destructs H5.
  simpl in H11;simpl;auto.
  
  instantiate (1:=x2).
  eapply ECBList_P_Set_Rdy_SEM_hold;eauto.
  eapply joinsig_join_getnone; eauto.
  
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.
  eauto.
  
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.
  auto.
  
  unfolds in H7;simpl in H7;inverts H7.
  eapply ECBList_P_Set_Rdy_SEM_hold;eauto.
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.
  eapply  joinsig_get_none; eauto.
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.

  lets Heq:ecbmod_get_joinsig_join_eq H4 H8 H2.
  subst.
  clear -H9.
  unfold RLH_ECBData_P in *.
  destruct x8;destruct m0;mytac;auto;tryfalse.
  unfold RH_ECB_P in *.
  mytac.
  intros.
  apply H2 in H4.
  subst;simpl;auto.
  intros.
  apply H3.
  intro.
  destruct H4.
  subst;simpl;auto.
  unfold RH_ECB_P in *.
  mytac.
  intros.
  apply H in H1.
  subst;simpl;auto.
  intros.
  apply H0.
  intro;destruct H1;subst;simpl;auto.
  unfold RH_ECB_P in *.
  mytac.
  intros.
  apply H in H1.
  subst;simpl;auto.
  intros.
  apply H0.
  intro;destruct H1;subst;simpl;auto.

   
  unfold RH_ECB_P in *.
  mytac;auto.
  intros.
  apply H0 in H4;auto.
  subst;simpl;auto.
  auto.
  intros.
  eapply H2;eauto.
  intro.
  destruct H4.
  subst.
  simpl;auto.
  
  instantiate (1:=EcbMod.set x4 eid (m0, remove_tid x wl)).
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.
  eapply EcbMod.joinsig_set;eauto.
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.
  eapply EcbMod.my_joinsig_join_set;eauto.
Qed.




Lemma ecblist_p_tick_rdy_ectr_mbox:
  forall  ectr head  vnext vprev eptr msg vdly stat prio vx vy vbitx vbity ectr' ,
    tick_rdy_ectr' eptr
                   (vnext
                      :: vprev
                      :: Vptr eptr
                      :: msg
                      :: Vint32 vdly
                      :: stat
                      :: Vint32 prio
                      :: Vint32 vx
                      :: Vint32 vy
                      :: Vint32 vbitx :: Vint32 vbity :: nil)
                   head ectr = Some ectr'->
    forall  htls x p m x0 eid edata hels cur m0 wl rtbl,
      get htls x = Some (p, wait x0 Int.one, m) ->
      x0 = os_stat_mbox eid ->
      ECBList_P head Vnull ectr edata hels htls ->
      RH_TCBList_ECBList_P hels htls cur ->
      EcbMod.get hels eid = Some (m0, wl) ->
      TCBNode_P
        (vnext
           :: vprev
           :: Vptr eptr
           :: msg
           :: Vint32 vdly
           :: stat
           :: Vint32 prio
           :: Vint32 vx
           :: Vint32 vy
           :: Vint32 vbitx :: Vint32 vbity :: nil)
        rtbl (p, wait x0 Int.one, m) ->
      R_Prio_No_Dup htls ->
      ECBList_P head Vnull ectr' edata
                (EcbMod.set hels eid (m0, remove_tid x wl)) (set htls x (p, rdy, m)).
Proof.
  intros.
  unfolds in H5.
  destruct H5 as (Hm & Hp & Hrl & Hrs).
  unfolds in Hm;simpl in Hm;inverts Hm.
  unfolds in Hp;simpl in Hp;inverts Hp.
  unfolds in Hrs.
  mytac.
  unfolds in H9.
  mytac.
  unfolds in H11.
  mytac.

  assert ((p, wait (os_stat_mbox eid) Int.one, m) =
          (p, wait (os_stat_mbox eid) Int.one, m)) by auto.
  apply H11 in H13.
  mytac.
  unfolds in H14;simpl in H14;inverts H14.
  unfolds in H15;simpl in H15;inverts H15.
  
  lets Hx:tick_rdy_ectr_split H H4 H2.
  mytac.
  rename H19 into Hlink.
  clear H.
  unfolds in H14.
  xunfold H14; inverts H14.
  
  clear H5 H7 H8 H1 H9 H10 H11 H12.
  symmetry in HeqH7,HeqH8.
  unfolds in HeqH1;simpl in HeqH1;inverts HeqH1.
  unfolds in HeqH3;simpl in HeqH3;inverts HeqH3.
  unfolds in HeqH5;simpl in HeqH5;inverts HeqH5.
  apply ecblist_p_decompose in H2;auto.
  mytac.
  simpl in H1.
  mytac.

  eapply ecblist_p_compose' with (mq:=(m0, remove_tid x wl));eauto.
  lets Hx:get_last_ecb_ptr_eq H Hlink.
  subst x9.
  instantiate (1:=eid).
  unfolds.
  splits.

  unfolds in H5.
  destructs H5.

  unfolds in H1.
  destructs H1.
  
  unfolds.
  splits.

  unfolds in H1.
  unfolds.
  intros.
  funfold Hrl.
  apply prio_wt_inq_convert in H16.
  destruct H16 as (Hprs1 & Hprs2).
  lets Hrs : prio_wt_inq_tid_neq HeqH7 H33.
  destruct Hrs.
  apply H7 in  Hprs1.
  destruct Hprs1.
  lets Hx:H1 H18.
  rewrite Int.repr_unsigned in Hx.
  destruct Hx as (tid' & nn & mm & Htg).
  simpl;auto.
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H20.
  subst tid'.
  unfold Maps.get in *;simpl in *.
  rewrite H0 in Htg.
  inverts Htg;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false;eauto.

  unfolds in H12.
  unfolds.
  intros.
  funfold Hrl.
  apply prio_wt_inq_convert in H16.
  destruct H16 as (Hprs1 & Hprs2).
  lets Hrs : prio_wt_inq_tid_neq HeqH7 H33.
  destruct Hrs.
  apply H7 in  Hprs1.
  destruct Hprs1.
  lets Hx:H12 H18.
  rewrite Int.repr_unsigned in Hx.
  destruct Hx as (tid' & nn & mm & Htg).
  simpl;auto.
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H20.
  subst tid'.
  unfold Maps.get in *;simpl in *.
  rewrite H0 in Htg.
  inverts Htg;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false;eauto.

  unfolds in H14.
  unfolds.
  intros.
  funfold Hrl.
  apply prio_wt_inq_convert in H16.
  destruct H16 as (Hprs1 & Hprs2).
  lets Hrs : prio_wt_inq_tid_neq HeqH7 H33.
  destruct Hrs.
  apply H7 in  Hprs1.
  destruct Hprs1.
  lets Hx:H14 H18.
  rewrite Int.repr_unsigned in Hx.
  destruct Hx as (tid' & nn & mm & Htg).
  simpl;auto.
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H20.
  subst tid'.
  unfold Maps.get in *;simpl in *.
  rewrite H0 in Htg.
  inverts Htg;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false;eauto.

  unfolds in H15.
  unfolds.
  intros.
  funfold Hrl.
  apply prio_wt_inq_convert in H16.
  destruct H16 as (Hprs1 & Hprs2).
  lets Hrs : prio_wt_inq_tid_neq HeqH7 H33.
  destruct Hrs.
  apply H7 in  Hprs1.
  destruct Hprs1.
  lets Hx:H15 H18.
  rewrite Int.repr_unsigned in Hx.
  destruct Hx as (tid' & nn & mm & Htg).
  simpl;auto.
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H20.
  subst tid'.
  unfold Maps.get in *;simpl in *.
  rewrite H0 in Htg.
  inverts Htg;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false;eauto.

  unfolds in H5.
  mytac.
  unfolds in H5.
  destruct H5 as (Hb&Hb'&Hb''&Hb''').
  splits;intros prio' mm nn tid'.
  
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H5.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  unfolds in Hb.
  lets Hga : Hb Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in H6.
  lets Hneqp: H6 H5 H0 Hgs.
  funfold Hrl.
  lets Hrs : prio_wt_inq_tid_neq  HeqH7 H28.
  assert ( PrioWaitInQ (Int.unsigned prio') x3 /\ prio' <> x5) .
  splits; auto.
  destruct Hrs as (_ & Hrs).
  apply Hrs in H7.
  auto.
  simpl;auto.

  assert (x = tid' \/ x <> tid') by tauto.
  destruct H5.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  unfolds in Hb'.
  lets Hga : Hb' Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in H6.
  lets Hneqp: H6 H5 H0 Hgs.
  funfold Hrl.
  lets Hrs : prio_wt_inq_tid_neq  HeqH7 H28.
  assert ( PrioWaitInQ (Int.unsigned prio') x3 /\ prio' <> x5) .
  splits; auto.
  destruct Hrs as (_ & Hrs).
  apply Hrs in H7.
  auto.
  simpl;auto.

  assert (x = tid' \/ x <> tid') by tauto.
  destruct H5.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  unfolds in Hb''.
  lets Hga : Hb'' Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in H6.
  lets Hneqp: H6 H5 H0 Hgs.
  funfold Hrl.
  lets Hrs : prio_wt_inq_tid_neq  HeqH7 H28.
  assert ( PrioWaitInQ (Int.unsigned prio') x3 /\ prio' <> x5) .
  splits; auto.
  destruct Hrs as (_ & Hrs).
  apply Hrs in H7.
  auto.
  simpl;auto.
  
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H5.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  unfolds in Hb'''.
  lets Hga : Hb''' Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in H6.
  lets Hneqp: H6 H5 H0 Hgs.
  funfold Hrl.
  lets Hrs : prio_wt_inq_tid_neq  HeqH7 H28.
  assert ( PrioWaitInQ (Int.unsigned prio') x3 /\ prio' <> x5) .
  splits; auto.
  destruct Hrs as (_ & Hrs).
  apply Hrs in H7.
  auto.
  simpl;auto.
  
  unfolds in H5;destructs H5.
  simpl in H11;simpl;auto.
  
  instantiate (1:=x2).
  

  eapply ECBList_P_Set_Rdy_MBOX_hold;eauto.
  eapply joinsig_join_getnone; eauto.
  
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.
  eauto.
  
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.
  auto.
  
  unfolds in H7;simpl in H7;inverts H7.
  eapply ECBList_P_Set_Rdy_MBOX_hold;eauto.
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.
  eapply  joinsig_get_none; eauto.
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.

  lets Heq:ecbmod_get_joinsig_join_eq H4 H8 H2.
  subst.
  clear -H9.
  unfold RLH_ECBData_P in *.
  destruct x8;destruct m0;mytac;auto;tryfalse.
  unfold RH_ECB_P in *.
  mytac.
  intros.
  apply H2 in H4.
  subst;simpl;auto.
  intros.
  apply H3.
  intro.
  destruct H4.
  subst;simpl;auto.
  unfold RH_ECB_P in *.
  mytac.
  intros.
  apply H in H1.
  subst;simpl;auto.
  intros.
  apply H0.
  intro;destruct H1;subst;simpl;auto.
  unfold RH_ECB_P in *.
  mytac.
  intros.
  apply H in H1.
  subst;simpl;auto.
  intros.
  apply H0.
  intro;destruct H1;subst;simpl;auto.
   
  unfold RH_ECB_P in *.
  mytac;auto.
  intros.
  apply H0 in H4;auto.
  subst;simpl;auto.
  auto.
  intros.
  eapply H2;eauto.
  intro.
  destruct H4.
  subst.
  simpl;auto.
  
  instantiate (1:=EcbMod.set x4 eid (m0, remove_tid x wl)).
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.
  eapply EcbMod.joinsig_set;eauto.
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.
  eapply EcbMod.my_joinsig_join_set;eauto.

  
  clear H5 H7 H8 H1 H9 H10 H11 H12.
  symmetry in HeqH7,HeqH8.
  unfolds in HeqH1;simpl in HeqH1;inverts HeqH1.
  unfolds in HeqH3;simpl in HeqH3;inverts HeqH3.
  unfolds in HeqH5;simpl in HeqH5;inverts HeqH5.
  apply ecblist_p_decompose in H2;auto.
  mytac.
  simpl in H1.
  mytac.

  eapply ecblist_p_compose' with (mq:=(m0, remove_tid x wl));eauto.
  lets Hx:get_last_ecb_ptr_eq H Hlink.
  subst x9.
  instantiate (1:=eid).
  unfolds.
  splits.

  unfolds in H5.
  destructs H5.

  unfolds in H1.
  destructs H1.
  
  unfolds.
  splits.

  unfolds in H1.
  unfolds.
  intros.
  funfold Hrl.
  apply prio_wt_inq_convert in H16.
  destruct H16 as (Hprs1 & Hprs2).
  lets Hrs : prio_wt_inq_tid_neq HeqH7 H33.
  destruct Hrs.
  apply H7 in  Hprs1.
  destruct Hprs1.
  lets Hx:H1 H18.
  rewrite Int.repr_unsigned in Hx.
  destruct Hx as (tid' & nn & mm & Htg).
  simpl;auto.
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H20.
  subst tid'.
  unfold Maps.get in *;simpl in *.
  rewrite H0 in Htg.
  inverts Htg;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false;eauto.

  unfolds in H12.
  unfolds.
  intros.
  funfold Hrl.
  apply prio_wt_inq_convert in H16.
  destruct H16 as (Hprs1 & Hprs2).
  lets Hrs : prio_wt_inq_tid_neq HeqH7 H33.
  destruct Hrs.
  apply H7 in  Hprs1.
  destruct Hprs1.
  lets Hx:H12 H18.
  rewrite Int.repr_unsigned in Hx.
  destruct Hx as (tid' & nn & mm & Htg).
  simpl;auto.
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H20.
  subst tid'.
  unfold Maps.get in *;simpl in *.
  rewrite H0 in Htg.
  inverts Htg;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false;eauto.

  unfolds in H14.
  unfolds.
  intros.
  funfold Hrl.
  apply prio_wt_inq_convert in H16.
  destruct H16 as (Hprs1 & Hprs2).
  lets Hrs : prio_wt_inq_tid_neq HeqH7 H33.
  destruct Hrs.
  apply H7 in  Hprs1.
  destruct Hprs1.
  lets Hx:H14 H18.
  rewrite Int.repr_unsigned in Hx.
  destruct Hx as (tid' & nn & mm & Htg).
  simpl;auto.
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H20.
  subst tid'.
  unfold Maps.get in *;simpl in *.
  rewrite H0 in Htg.
  inverts Htg;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false;eauto.

  unfolds in H15.
  unfolds.
  intros.
  funfold Hrl.
  apply prio_wt_inq_convert in H16.
  destruct H16 as (Hprs1 & Hprs2).
  lets Hrs : prio_wt_inq_tid_neq HeqH7 H33.
  destruct Hrs.
  apply H7 in  Hprs1.
  destruct Hprs1.
  lets Hx:H15 H18.
  rewrite Int.repr_unsigned in Hx.
  destruct Hx as (tid' & nn & mm & Htg).
  simpl;auto.
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H20.
  subst tid'.
  unfold Maps.get in *;simpl in *.
  rewrite H0 in Htg.
  inverts Htg;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false;eauto.

  unfolds in H5.
  mytac.
  unfolds in H5.
  destruct H5 as (Hb&Hb'&Hb''&Hb''').
  splits;intros prio' mm nn tid'.
  
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H5.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  unfolds in Hb.
  lets Hga : Hb Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in H6.
  lets Hneqp: H6 H5 H0 Hgs.
  funfold Hrl.
  lets Hrs : prio_wt_inq_tid_neq  HeqH7 H28.
  assert ( PrioWaitInQ (Int.unsigned prio') x3 /\ prio' <> x5) .
  splits; auto.
  destruct Hrs as (_ & Hrs).
  apply Hrs in H7.
  auto.
  simpl;auto.

  assert (x = tid' \/ x <> tid') by tauto.
  destruct H5.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  unfolds in Hb'.
  lets Hga : Hb' Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in H6.
  lets Hneqp: H6 H5 H0 Hgs.
  funfold Hrl.
  lets Hrs : prio_wt_inq_tid_neq  HeqH7 H28.
  assert ( PrioWaitInQ (Int.unsigned prio') x3 /\ prio' <> x5) .
  splits; auto.
  destruct Hrs as (_ & Hrs).
  apply Hrs in H7.
  auto.
  simpl;auto.

  assert (x = tid' \/ x <> tid') by tauto.
  destruct H5.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  unfolds in Hb''.
  lets Hga : Hb'' Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in H6.
  lets Hneqp: H6 H5 H0 Hgs.
  funfold Hrl.
  lets Hrs : prio_wt_inq_tid_neq  HeqH7 H28.
  assert ( PrioWaitInQ (Int.unsigned prio') x3 /\ prio' <> x5) .
  splits; auto.
  destruct Hrs as (_ & Hrs).
  apply Hrs in H7.
  auto.
  simpl;auto.
  
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H5.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  unfolds in Hb'''.
  lets Hga : Hb''' Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in H6.
  lets Hneqp: H6 H5 H0 Hgs.
  funfold Hrl.
  lets Hrs : prio_wt_inq_tid_neq  HeqH7 H28.
  assert ( PrioWaitInQ (Int.unsigned prio') x3 /\ prio' <> x5) .
  splits; auto.
  destruct Hrs as (_ & Hrs).
  apply Hrs in H7.
  auto.
  simpl;auto.
  
  unfolds in H5;destructs H5.
  simpl in H11;simpl;auto.
  
  instantiate (1:=x2).
  eapply ECBList_P_Set_Rdy_MBOX_hold;eauto.
  eapply joinsig_join_getnone; eauto.
  
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.
  eauto.
  
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.
  auto.
  
  unfolds in H7;simpl in H7;inverts H7.
  eapply ECBList_P_Set_Rdy_MBOX_hold;eauto.
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.
  eapply  joinsig_get_none; eauto.
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.

  lets Heq:ecbmod_get_joinsig_join_eq H4 H8 H2.
  subst.
  clear -H9.
  unfold RLH_ECBData_P in *.
  destruct x8;destruct m0;mytac;auto;tryfalse.
  unfold RH_ECB_P in *.
  mytac.
  intros.
  apply H2 in H4.
  subst;simpl;auto.
  intros.
  apply H3.
  intro.
  destruct H4.
  subst;simpl;auto.
  unfold RH_ECB_P in *.
  mytac.
  intros.
  apply H in H1.
  subst;simpl;auto.
  intros.
  apply H0.
  intro;destruct H1;subst;simpl;auto.
  unfold RH_ECB_P in *.
  mytac.
  intros.
  apply H in H1.
  subst;simpl;auto.
  intros.
  apply H0.
  intro;destruct H1;subst;simpl;auto.
   
  unfold RH_ECB_P in *.
  mytac;auto.
  intros.
  apply H0 in H4;auto.
  subst;simpl;auto.
  auto.
  intros.
  eapply H2;eauto.
  intro.
  destruct H4.
  subst.
  simpl;auto.
  
  instantiate (1:=EcbMod.set x4 eid (m0, remove_tid x wl)).
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.
  eapply EcbMod.joinsig_set;eauto.
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.
  eapply EcbMod.my_joinsig_join_set;eauto.
Qed.



Lemma ecblist_p_tick_rdy_ectr_mutexsem:
  forall  ectr head  vnext vprev eptr msg vdly stat prio vx vy vbitx vbity ectr' ,
    tick_rdy_ectr' eptr
                   (vnext
                      :: vprev
                      :: Vptr eptr
                      :: msg
                      :: Vint32 vdly
                      :: stat
                      :: Vint32 prio
                      :: Vint32 vx
                      :: Vint32 vy
                      :: Vint32 vbitx :: Vint32 vbity :: nil)
                   head ectr = Some ectr'->
    forall  htls x p m x0 eid edata hels cur m0 wl rtbl,
      get htls x = Some (p, wait x0 Int.one, m) ->
      x0 = os_stat_mutexsem eid ->
      ECBList_P head Vnull ectr edata hels htls ->
      RH_TCBList_ECBList_P hels htls cur ->
      EcbMod.get hels eid = Some (m0, wl) ->
      TCBNode_P
        (vnext
           :: vprev
           :: Vptr eptr
           :: msg
           :: Vint32 vdly
           :: stat
           :: Vint32 prio
           :: Vint32 vx
           :: Vint32 vy
           :: Vint32 vbitx :: Vint32 vbity :: nil)
        rtbl (p, wait x0 Int.one, m) ->
      R_Prio_No_Dup htls ->
      ECBList_P head Vnull ectr' edata
                (EcbMod.set hels eid (m0, remove_tid x wl)) (set htls x (p, rdy, m)).
Proof.
  intros.
  unfolds in H5.
  destruct H5 as (Hm & Hp & Hrl & Hrs).
  unfolds in Hm;simpl in Hm;inverts Hm.
  unfolds in Hp;simpl in Hp;inverts Hp.
  unfolds in Hrs.
  mytac.
  unfolds in H9.
  mytac.
  unfolds in H12.
  mytac.

  assert ((p, wait (os_stat_mutexsem eid) Int.one, m) =
          (p, wait (os_stat_mutexsem eid) Int.one, m)) by auto.
  apply H12 in H13.
  mytac.
  unfolds in H14;simpl in H14;inverts H14.
  unfolds in H15;simpl in H15;inverts H15.
  
  lets Hx:tick_rdy_ectr_split H H4 H2.
  mytac.
  rename H19 into Hlink.
  clear H.
  unfolds in H14.
  xunfold H14; inverts H14.
  
  clear H5 H7 H8 H1 H9 H10 H11 H12.
  symmetry in HeqH7,HeqH8.
  unfolds in HeqH1;simpl in HeqH1;inverts HeqH1.
  unfolds in HeqH3;simpl in HeqH3;inverts HeqH3.
  unfolds in HeqH5;simpl in HeqH5;inverts HeqH5.
  apply ecblist_p_decompose in H2;auto.
  mytac.
  simpl in H1.
  mytac.

  eapply ecblist_p_compose' with (mq:=(m0, remove_tid x wl));eauto.
  lets Hx:get_last_ecb_ptr_eq H Hlink.
  subst x9.
  instantiate (1:=eid).
  unfolds.
  splits.

  unfolds in H5.
  destructs H5.

  unfolds in H1.
  destructs H1.
  
  unfolds.
  splits.

  unfolds in H1.
  unfolds.
  intros.
  funfold Hrl.
  apply prio_wt_inq_convert in H16.
  destruct H16 as (Hprs1 & Hprs2).
  lets Hrs : prio_wt_inq_tid_neq HeqH7 H33.
  destruct Hrs.
  apply H7 in  Hprs1.
  destruct Hprs1.
  lets Hx:H1 H18.
  rewrite Int.repr_unsigned in Hx.
  destruct Hx as (tid' & nn & mm & Htg).
  simpl;auto.
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H20.
  subst tid'.
  unfold Maps.get in *;simpl in *.
  rewrite H0 in Htg.
  inverts Htg;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false;eauto.

  unfolds in H12.
  unfolds.
  intros.
  funfold Hrl.
  apply prio_wt_inq_convert in H16.
  destruct H16 as (Hprs1 & Hprs2).
  lets Hrs : prio_wt_inq_tid_neq HeqH7 H33.
  destruct Hrs.
  apply H7 in  Hprs1.
  destruct Hprs1.
  lets Hx:H12 H18.
  rewrite Int.repr_unsigned in Hx.
  destruct Hx as (tid' & nn & mm & Htg).
  simpl;auto.
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H20.
  subst tid'.
  unfold Maps.get in *;simpl in *.
  rewrite H0 in Htg.
  inverts Htg;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false;eauto.

  unfolds in H14.
  unfolds.
  intros.
  funfold Hrl.
  apply prio_wt_inq_convert in H16.
  destruct H16 as (Hprs1 & Hprs2).
  lets Hrs : prio_wt_inq_tid_neq HeqH7 H33.
  destruct Hrs.
  apply H7 in  Hprs1.
  destruct Hprs1.
  lets Hx:H14 H18.
  rewrite Int.repr_unsigned in Hx.
  destruct Hx as (tid' & nn & mm & Htg).
  simpl;auto.
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H20.
  subst tid'.
  unfold Maps.get in *;simpl in *.
  rewrite H0 in Htg.
  inverts Htg;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false;eauto.

  unfolds in H15.
  unfolds.
  intros.
  funfold Hrl.
  apply prio_wt_inq_convert in H16.
  destruct H16 as (Hprs1 & Hprs2).
  lets Hrs : prio_wt_inq_tid_neq HeqH7 H33.
  destruct Hrs.
  apply H7 in  Hprs1.
  destruct Hprs1.
  lets Hx:H15 H18.
  rewrite Int.repr_unsigned in Hx.
  destruct Hx as (tid' & nn & mm & Htg).
  simpl;auto.
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H20.
  subst tid'.
  unfold Maps.get in *;simpl in *.
  rewrite H0 in Htg.
  inverts Htg;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false;eauto.

  unfolds in H5.
  mytac.
  unfolds in H5.
  destruct H5 as (Hb&Hb'&Hb''&Hb''').
  splits;intros prio' mm nn tid'.
  
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H5.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  unfolds in Hb.
  lets Hga : Hb Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in H6.
  lets Hneqp: H6 H5 H0 Hgs.
  funfold Hrl.
  lets Hrs : prio_wt_inq_tid_neq  HeqH7 H28.
  assert ( PrioWaitInQ (Int.unsigned prio') x3 /\ prio' <> x5) .
  splits; auto.
  destruct Hrs as (_ & Hrs).
  apply Hrs in H7.
  auto.
  simpl;auto.

  assert (x = tid' \/ x <> tid') by tauto.
  destruct H5.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  unfolds in Hb'.
  lets Hga : Hb' Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in H6.
  lets Hneqp: H6 H5 H0 Hgs.
  funfold Hrl.
  lets Hrs : prio_wt_inq_tid_neq  HeqH7 H28.
  assert ( PrioWaitInQ (Int.unsigned prio') x3 /\ prio' <> x5) .
  splits; auto.
  destruct Hrs as (_ & Hrs).
  apply Hrs in H7.
  auto.
  simpl;auto.

  assert (x = tid' \/ x <> tid') by tauto.
  destruct H5.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  unfolds in Hb''.
  lets Hga : Hb'' Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in H6.
  lets Hneqp: H6 H5 H0 Hgs.
  funfold Hrl.
  lets Hrs : prio_wt_inq_tid_neq  HeqH7 H28.
  assert ( PrioWaitInQ (Int.unsigned prio') x3 /\ prio' <> x5) .
  splits; auto.
  destruct Hrs as (_ & Hrs).
  apply Hrs in H7.
  auto.
  simpl;auto.
  
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H5.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  unfolds in Hb'''.
  lets Hga : Hb''' Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in H6.
  lets Hneqp: H6 H5 H0 Hgs.
  funfold Hrl.
  lets Hrs : prio_wt_inq_tid_neq  HeqH7 H28.
  assert ( PrioWaitInQ (Int.unsigned prio') x3 /\ prio' <> x5) .
  splits; auto.
  destruct Hrs as (_ & Hrs).
  apply Hrs in H7.
  auto.
  simpl;auto.
  
  unfolds in H5;destructs H5.
  simpl in H11;simpl;auto.
  
  instantiate (1:=x2).
  

  eapply ECBList_P_Set_Rdy_MUTEX_hold;eauto.
  eapply joinsig_join_getnone; eauto.
  
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.
  eauto.
  
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.
  auto.
  
  unfolds in H7;simpl in H7;inverts H7.
  eapply ECBList_P_Set_Rdy_MUTEX_hold;eauto.
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.
  eapply  joinsig_get_none; eauto.
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.

  lets Heq:ecbmod_get_joinsig_join_eq H4 H8 H2.
  subst.
  clear -H9.
  unfold RLH_ECBData_P in *.
  destruct x8;destruct m0;mytac;auto;tryfalse.
  unfold RH_ECB_P in *.
  mytac.
  intros.
  apply H2 in H4.
  subst;simpl;auto.
  intros.
  apply H3.
  intro.
  destruct H4.
  subst;simpl;auto.
  unfold RH_ECB_P in *.
  mytac.
  intros.
  apply H in H1.
  subst;simpl;auto.
  intros.
  apply H0.
  intro;destruct H1;subst;simpl;auto.
  unfold RH_ECB_P in *.
  mytac.
  intros.
  apply H in H1.
  subst;simpl;auto.
  intros.
  apply H0.
  intro;destruct H1;subst;simpl;auto.

   
  unfold RH_ECB_P in *.
  mytac;auto.
  intros.
  apply H0 in H4;auto.
  subst;simpl;auto.
  auto.
  intros.
  eapply H2;eauto.
  intro.
  destruct H4.
  subst.
  simpl;auto.
  
  instantiate (1:=EcbMod.set x4 eid (m0, remove_tid x wl)).
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.
  eapply EcbMod.joinsig_set;eauto.
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.
  eapply EcbMod.my_joinsig_join_set;eauto.

  
  clear H5 H7 H8 H1 H9 H10 H11 H12.
  symmetry in HeqH7,HeqH8.
  unfolds in HeqH1;simpl in HeqH1;inverts HeqH1.
  unfolds in HeqH3;simpl in HeqH3;inverts HeqH3.
  unfolds in HeqH5;simpl in HeqH5;inverts HeqH5.
  apply ecblist_p_decompose in H2;auto.
  mytac.
  simpl in H1.
  mytac.

  eapply ecblist_p_compose' with (mq:=(m0, remove_tid x wl));eauto.
  lets Hx:get_last_ecb_ptr_eq H Hlink.
  subst x9.
  instantiate (1:=eid).
  unfolds.
  splits.

  unfolds in H5.
  destructs H5.

  unfolds in H1.
  destructs H1.
  
  unfolds.
  splits.

  unfolds in H1.
  unfolds.
  intros.
  funfold Hrl.
  apply prio_wt_inq_convert in H16.
  destruct H16 as (Hprs1 & Hprs2).
  lets Hrs : prio_wt_inq_tid_neq HeqH7 H33.
  destruct Hrs.
  apply H7 in  Hprs1.
  destruct Hprs1.
  lets Hx:H1 H18.
  rewrite Int.repr_unsigned in Hx.
  destruct Hx as (tid' & nn & mm & Htg).
  simpl;auto.
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H20.
  subst tid'.
  unfold Maps.get in *;simpl in *.
  rewrite H0 in Htg.
  inverts Htg;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false;eauto.

  unfolds in H12.
  unfolds.
  intros.
  funfold Hrl.
  apply prio_wt_inq_convert in H16.
  destruct H16 as (Hprs1 & Hprs2).
  lets Hrs : prio_wt_inq_tid_neq HeqH7 H33.
  destruct Hrs.
  apply H7 in  Hprs1.
  destruct Hprs1.
  lets Hx:H12 H18.
  rewrite Int.repr_unsigned in Hx.
  destruct Hx as (tid' & nn & mm & Htg).
  simpl;auto.
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H20.
  subst tid'.
  unfold Maps.get in *;simpl in *.
  rewrite H0 in Htg.
  inverts Htg;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false;eauto.

  unfolds in H14.
  unfolds.
  intros.
  funfold Hrl.
  apply prio_wt_inq_convert in H16.
  destruct H16 as (Hprs1 & Hprs2).
  lets Hrs : prio_wt_inq_tid_neq HeqH7 H33.
  destruct Hrs.
  apply H7 in  Hprs1.
  destruct Hprs1.
  lets Hx:H14 H18.
  rewrite Int.repr_unsigned in Hx.
  destruct Hx as (tid' & nn & mm & Htg).
  simpl;auto.
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H20.
  subst tid'.
  unfold Maps.get in *;simpl in *.
  rewrite H0 in Htg.
  inverts Htg;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false;eauto.

  unfolds in H15.
  unfolds.
  intros.
  funfold Hrl.
  apply prio_wt_inq_convert in H16.
  destruct H16 as (Hprs1 & Hprs2).
  lets Hrs : prio_wt_inq_tid_neq HeqH7 H33.
  destruct Hrs.
  apply H7 in  Hprs1.
  destruct Hprs1.
  lets Hx:H15 H18.
  rewrite Int.repr_unsigned in Hx.
  destruct Hx as (tid' & nn & mm & Htg).
  simpl;auto.
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H20.
  subst tid'.
  unfold Maps.get in *;simpl in *.
  rewrite H0 in Htg.
  inverts Htg;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false;eauto.

  unfolds in H5.
  mytac.
  unfolds in H5.
  destruct H5 as (Hb&Hb'&Hb''&Hb''').
  splits;intros prio' mm nn tid'.
  
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H5.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  unfolds in Hb.
  lets Hga : Hb Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in H6.
  lets Hneqp: H6 H5 H0 Hgs.
  funfold Hrl.
  lets Hrs : prio_wt_inq_tid_neq  HeqH7 H28.
  assert ( PrioWaitInQ (Int.unsigned prio') x3 /\ prio' <> x5) .
  splits; auto.
  destruct Hrs as (_ & Hrs).
  apply Hrs in H7.
  auto.
  simpl;auto.

  assert (x = tid' \/ x <> tid') by tauto.
  destruct H5.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  unfolds in Hb'.
  lets Hga : Hb' Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in H6.
  lets Hneqp: H6 H5 H0 Hgs.
  funfold Hrl.
  lets Hrs : prio_wt_inq_tid_neq  HeqH7 H28.
  assert ( PrioWaitInQ (Int.unsigned prio') x3 /\ prio' <> x5) .
  splits; auto.
  destruct Hrs as (_ & Hrs).
  apply Hrs in H7.
  auto.
  simpl;auto.

  assert (x = tid' \/ x <> tid') by tauto.
  destruct H5.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  unfolds in Hb''.
  lets Hga : Hb'' Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in H6.
  lets Hneqp: H6 H5 H0 Hgs.
  funfold Hrl.
  lets Hrs : prio_wt_inq_tid_neq  HeqH7 H28.
  assert ( PrioWaitInQ (Int.unsigned prio') x3 /\ prio' <> x5) .
  splits; auto.
  destruct Hrs as (_ & Hrs).
  apply Hrs in H7.
  auto.
  simpl;auto.
  
  assert (x = tid' \/ x <> tid') by tauto.
  destruct H5.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  unfolds in Hb'''.
  lets Hga : Hb''' Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in H6.
  lets Hneqp: H6 H5 H0 Hgs.
  funfold Hrl.
  lets Hrs : prio_wt_inq_tid_neq  HeqH7 H28.
  assert ( PrioWaitInQ (Int.unsigned prio') x3 /\ prio' <> x5) .
  splits; auto.
  destruct Hrs as (_ & Hrs).
  apply Hrs in H7.
  auto.
  simpl;auto.
  
  unfolds in H5;destructs H5.
  simpl in H11;simpl;auto.
  
  instantiate (1:=x2).
  eapply ECBList_P_Set_Rdy_MUTEX_hold;eauto.
  eapply joinsig_join_getnone; eauto.
  
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.
  eauto.
  
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.
  auto.
  
  unfolds in H7;simpl in H7;inverts H7.
  eapply ECBList_P_Set_Rdy_MUTEX_hold;eauto.
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.
  eapply  joinsig_get_none; eauto.
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.

  lets Heq:ecbmod_get_joinsig_join_eq H4 H8 H2.
  subst.
  clear -H9.
  unfold RLH_ECBData_P in *.
  destruct x8;destruct m0;mytac;auto;tryfalse.
  unfold RH_ECB_P in *.
  mytac.
  intros.
  apply H2 in H4.
  subst;simpl;auto.
  intros.
  apply H3.
  intro.
  destruct H4.
  subst;simpl;auto.
  unfold RH_ECB_P in *.
  mytac.
  intros.
  apply H in H1.
  subst;simpl;auto.
  intros.
  apply H0.
  intro;destruct H1;subst;simpl;auto.
  unfold RH_ECB_P in *.
  mytac.
  intros.
  apply H in H1.
  subst;simpl;auto.
  intros.
  apply H0.
  intro;destruct H1;subst;simpl;auto.
   
  unfold RH_ECB_P in *.
  mytac;auto.
  intros.
  apply H0 in H4;auto.
  subst;simpl;auto.
  auto.
  intros.
  eapply H2;eauto.
  intro.
  destruct H4.
  subst.
  simpl;auto.
  
  instantiate (1:=EcbMod.set x4 eid (m0, remove_tid x wl)).
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.
  eapply EcbMod.joinsig_set;eauto.
  lets Hx: get_last_ecb_ptr_eq H Hlink.
  subst x9.
  eapply EcbMod.my_joinsig_join_set;eauto.
Qed.



Lemma tickchange_ecblist_p:
  forall h p l rtbl rgrp htls l1 l2 ll hels cur x t x2 x3 head ectr ectr' edata l' rgrp' rtbl' (m:msg),
    TcbMod.get htls x = Some (p, t, m) ->
    get_last_tcb_ptr l1 h = Some (Vptr x) ->
    TCBList_P h (l1++(l::ll)++l2) rtbl htls ->
    tickchange_l l rtbl rgrp head ectr l' rtbl' rgrp' ectr' ->
    R_Prio_No_Dup_L (l1++(l::ll)++l2) ->
    RH_TCBList_ECBList_P hels htls cur ->
    tickchange x t hels x2 x3 ->
    ECBList_P head Vnull ectr edata hels htls ->
    R_Prio_No_Dup htls ->
    ECBList_P head Vnull ectr' edata x3 (TcbMod.set htls x (p, x2, m)).
Proof.
  intros.
  rename H7 into Hnodup.
  lets Hnode:tcblist_p_imp_tcbnode_p H H0 H1.
  inverts H2.
  inverts H5.
  rewrite get_set_same;auto.
  funfold Hnode.
  unfolds in H10.
  mytac.
  unfolds in H11.
  mytac.
  unfolds in H11.
  assert ((p, wait os_stat_time n, m) = (p, wait os_stat_time n, m)) by auto.
  apply H11 in H16.
  mytac.
  unfolds in H16.
  mytac.
  unfolds in H20;simpl in H20;inverts H20.
  lets Hx:Int.eq_spec n Int.zero.
  rewrite H8 in Hx.
  subst.
  clear -H17.
  int auto.
  funfold Hnode.
  unfolds in H9.
  mytac.
  unfolds in H10.
  mytac.
  unfolds in H10.
  assert ((p, wait os_stat_time Int.one, m) = (p, wait os_stat_time Int.one, m)) by auto.
  apply H10 in H15.
  mytac.
  unfolds in H15.
  mytac.
  unfolds in H19;simpl in H19;inverts H19.
  clear -H8.
  int auto.

  destruct H7.
  subst.
  destruct H9.
  funfold Hnode.
  unfolds in H11.
  mytac.
  unfolds in H12.
  mytac.
  unfolds in H14.
  assert ( (p, wait (os_stat_q eid0) n, m) = (p, wait (os_stat_q eid0) n, m)) by auto.
  apply H14 in H17.
  mytac.
  unfolds in H17.
  mytac.
  unfolds in H21;simpl in H21;inverts H21.
  clear -H8 H5.
  int auto.
  destruct H2.
  subst.
  destruct H9.
  funfold Hnode.
  unfolds in H11.
  mytac.
  unfolds in H12.
  mytac.
  unfolds in H13.
  assert ((p, wait (os_stat_sem eid0) n, m) =
  (p, wait (os_stat_sem eid0) n, m))  by auto.
  apply H13 in H17.
  mytac.
  unfolds in H17.
  mytac.
  unfolds in H21;simpl in H21;inverts H21.
  clear -H8 H5.
  int auto.

  destruct H2.
  subst.
  destruct H9.
  funfold Hnode.
  unfolds in H11.
  mytac.
  unfolds in H12.
  mytac.
  unfolds in H15.
  assert ( (p, wait (os_stat_mbox eid0) n, m) =
        (p, wait (os_stat_mbox eid0) n, m))  by auto.
  apply H15 in H17.
  mytac.
  unfolds in H17.
  mytac.
  unfolds in H21;simpl in H21;inverts H21.
  clear -H8 H5.
  int auto.

  subst.
  destruct H9.
  funfold Hnode.
  unfolds in H11.
  mytac.
  unfolds in H12.
  mytac.
  unfolds in H16.
  assert ( (p, wait (os_stat_mutexsem eid0) n, m) =
        (p, wait (os_stat_mutexsem eid0) n, m))  by auto.
  apply H16 in H17.
  mytac.
  unfolds in H17.
  mytac.
  unfolds in H21;simpl in H21;inverts H21.
  clear -H8 H5.
  int auto.

   
  destruct H2.
  subst.
  funfold Hnode.
  unfolds in H9.
  mytac.
  unfolds in H11.
  mytac.
  unfolds in H13.
  assert ( (p, wait (os_stat_q eid0) Int.one, m) =
        (p, wait (os_stat_q eid0) Int.one, m))  by auto.
  apply H13 in H16.
  mytac.
  unfolds in H16.
  mytac.
  unfolds in H20;simpl in H20;inverts H20.
  clear -H8.
  int auto.

  destruct H2.
  subst.
  funfold Hnode.
  unfolds in H9.
  mytac.
  unfolds in H11.
  mytac.
  unfolds in H12.
  assert ( (p, wait (os_stat_sem eid0) Int.one, m) =
        (p, wait (os_stat_sem eid0) Int.one, m))  by auto.
  apply H12 in H16.
  mytac.
  unfolds in H16.
  mytac.
  unfolds in H20;simpl in H20;inverts H20.
  clear -H8.
  int auto.

  destruct H2.
  subst.
  funfold Hnode.
  unfolds in H9.
  mytac.
  unfolds in H11.
  mytac.
  unfolds in H14.
  assert (  (p, wait (os_stat_mbox eid0) Int.one, m) =
        (p, wait (os_stat_mbox eid0) Int.one, m))  by auto.
  apply H14 in H16.
  mytac.
  unfolds in H16.
  mytac.
  unfolds in H20;simpl in H20;inverts H20.
  clear -H8.
  int auto.

  subst.
  funfold Hnode.
  unfolds in H9.
  mytac.
  unfolds in H11.
  mytac.
  unfolds in H15.
  assert ((p, wait (os_stat_mutexsem eid0) Int.one, m) =
        (p, wait (os_stat_mutexsem eid0) Int.one, m))  by auto.
  apply H15 in H16.
  mytac.
  unfolds in H16.
  mytac.
  unfolds in H20;simpl in H20;inverts H20.
  clear -H8.
  int auto.

  (*--------------------------------------*)

  inverts H5.
  rewrite get_set_same;auto.

  eapply ecblist_p_stat_time_minus1_eq;eauto.
  
  unfolds in Hnode.
  mytac.
  unfolds in H10.
  mytac.
  unfolds in H13.
  mytac.
  unfolds in H13.
  assert ((p, wait os_stat_time Int.one, m) = (p, wait os_stat_time Int.one, m)) by auto.
  apply H13 in H18.
  mytac.
  unfolds in H18.
  mytac.
  unfolds in H22;simpl in H22;inverts H22.
  clear -H9.
  int auto.

  eapply ecblist_p_stat_time_minus1_eq;eauto.

  destruct H2.
  subst.
  funfold Hnode.
  unfolds in H10.
  mytac.
  unfolds in H12.
  mytac.
  unfolds in H14.
  assert ( (p, wait (os_stat_q eid0) Int.one, m) =
        (p, wait (os_stat_q eid0) Int.one, m))  by auto.
  apply H14 in H17.
  mytac.
  unfolds in H17.
  mytac.
  unfolds in H21;simpl in H21;inverts H21.
  clear -H9.
  int auto.

  destruct H2.
  subst.
  funfold Hnode.
  unfolds in H10.
  mytac.
  unfolds in H12.
  mytac.
  unfolds in H13.
  assert ( (p, wait (os_stat_sem eid0) Int.one, m) =
        (p, wait (os_stat_sem eid0) Int.one, m))  by auto.
  apply H13 in H17.
  mytac.
  unfolds in H17.
  mytac.
  unfolds in H21;simpl in H21;inverts H21.
  clear -H9.
  int auto.

  destruct H2.
  subst.
  funfold Hnode.
  unfolds in H10.
  mytac.
  unfolds in H12.
  mytac.
  unfolds in H15.
  assert (  (p, wait (os_stat_mbox eid0) Int.one, m) =
        (p, wait (os_stat_mbox eid0) Int.one, m))  by auto.
  apply H15 in H17.
  mytac.
  unfolds in H17.
  mytac.
  unfolds in H21;simpl in H21;inverts H21.
  clear -H9.
  int auto.

  subst.
  funfold Hnode.
  unfolds in H10.
  mytac.
  unfolds in H12.
  mytac.
  unfolds in H16.
  assert ((p, wait (os_stat_mutexsem eid0) Int.one, m) =
        (p, wait (os_stat_mutexsem eid0) Int.one, m))  by auto.
  apply H16 in H17.
  mytac.
  unfolds in H17.
  mytac.
  unfolds in H21;simpl in H21;inverts H21.
  clear -H9.
  int auto.
  (*--------------------------*)

  inverts H5.
  rewrite get_set_same;auto.

  unfolds in Hnode.
  mytac.
  unfolds in H11.
  mytac.
  unfolds in H16.
  mytac.
  unfolds in H16.
  mytac.
  assert ( (p, wait os_stat_time n, m) = (p, wait os_stat_time n, m)) by auto.
  apply H16 in H21.
  mytac.
  unfolds in H21;mytac.
  unfolds in H25;simpl in H25;inverts H25.
  clear-H7 H8 H9 H22.
  int auto.
  destruct  (zeq 1 (Int.unsigned n));tryfalse.
  destruct (zlt 0 (Int.unsigned n));tryfalse.
  destruct (zeq (Int.unsigned n) 0);tryfalse.
  destruct (zeq (Int.unsigned ($ (Int.unsigned n - 1))) 0);tryfalse.
  split.
  clear e.
  int auto.
  clear e.
  int auto.
  eapply ecblist_p_wait_set_rdy;eauto.

  eapply ecblist_p_stat_time_minus1_eq;eauto.

  unfolds in Hnode.
  clear H1 H0 H12 H13.
  mytac.
  unfolds in H7.
  mytac.
  clear -H2 H13.
  unfolds in H13.
  mytac.
  destruct H2.
  subst.
  unfolds in H1.
  assert (  (p, wait (os_stat_q eid) Int.one, m) =
            (p, wait (os_stat_q eid) Int.one, m)) by auto.
  apply H1 in H2.
  mytac.
  unfolds in H5;simpl in H5;inverts H5.

  destruct H2.
  subst.
  unfolds in H0.
  assert ((p, wait (os_stat_sem eid) Int.one, m) =
       (p, wait (os_stat_sem eid) Int.one, m)) by auto.
  apply H0 in H2.
  mytac.
  unfolds in H5;simpl in H5;inverts H5.
  
  destruct H2.
  subst.
  unfolds in H3.
  assert ( (p, wait (os_stat_mbox eid) Int.one, m) =
       (p, wait (os_stat_mbox eid) Int.one, m) ) by auto.
  apply H3 in H2.
  mytac.
  unfolds in H5;simpl in H5;inverts H5.

  subst.
  unfolds in H4.
  assert ((p, wait (os_stat_mutexsem eid) Int.one, m) =
       (p, wait (os_stat_mutexsem eid) Int.one, m)) by auto.
  apply H4 in H2.
  mytac.
  unfolds in H5;simpl in H5;inverts H5.

  (*--------------------------------------------------*)
  rename H1 into Htcbl.
  clear H12 H13.
  inverts H5.
  unfolds in Hnode.
  mytac.
  destruct H1.
  subst.
  unfolds in H10.
  mytac.
  unfolds in H10.
  assert ((p, rdy, m) = (p, rdy, m));auto.
  apply H10 in H13.
  mytac.
  unfolds in H16;simpl in H16;inverts H16.
  clear -H8.
  int auto.

  destruct H1;subst.
  unfolds in H10.
  mytac.
  unfolds in H12.
  mytac.
  unfolds in H13.
  assert ((p, wait (os_stat_sem eid) Int.zero, m) =
        (p, wait (os_stat_sem eid) Int.zero, m));auto.
  apply H13 in H18.
  mytac.
  unfolds in H18.
  mytac.
  unfolds in H22;simpl in H22;inverts H22.
  clear -H8.
  int auto.

  destruct H1;subst.
  unfolds in H10.
  mytac.
  unfolds in H12.
  mytac.
  unfolds in H15.
  assert ( (p, wait (os_stat_q eid) Int.zero, m) =
        (p, wait (os_stat_q eid) Int.zero, m));auto.
  apply H15 in H18.
  mytac.
  unfolds in H18.
  mytac.
  unfolds in H22;simpl in H22;inverts H22.
  clear -H8.
  int auto.

  destruct H1;subst.
  unfolds in H10.
  mytac.
  unfolds in H12.
  mytac.
  unfolds in H16.
  assert ( (p, wait (os_stat_mbox eid) Int.zero, m) =
        (p, wait (os_stat_mbox eid) Int.zero, m));auto.
  apply H16 in H18.
  mytac.
  unfolds in H18.
  mytac.
  unfolds in H22;simpl in H22;inverts H22.
  clear -H8.
  int auto.
  
  subst.
  unfolds in H10.
  mytac.
  unfolds in H12.
  mytac.
  unfolds in H17.
  assert ((p, wait (os_stat_mutexsem eid) Int.zero, m) =
        (p, wait (os_stat_mutexsem eid) Int.zero, m));auto.
  apply H17 in H18.
  mytac.
  unfolds in H18.
  mytac.
  unfolds in H22;simpl in H22;inverts H22.
  clear -H8.
  int auto.

  unfolds in Hnode.
  mytac.
  unfolds in H10.
  mytac.
  unfolds in H13.
  mytac.
  unfolds in H13.
  assert ( (p, wait os_stat_time n, m) = (p, wait os_stat_time n, m)) by auto.
  apply H13 in H19.
  mytac.
  unfolds in H19.
  mytac.
  unfolds in H23;simpl in H23;inverts H23.
  clear -H2 H8 H9 H20.
  int auto.
  clear H9.
  int auto.
  
  unfolds in Hnode.
  mytac.
  unfolds in H7.
  mytac.
  unfolds in H12.
  mytac.
  unfolds in H12.
  assert ((p, wait os_stat_time Int.one, m) = (p, wait os_stat_time Int.one, m)) by auto.
  apply H12 in H18.
  mytac.
  unfolds in H20;simpl in H20;inverts H20.
  clear -H5.
  unfolds in H5.
  mytac.
  unfolds in H4;simpl in H4;inverts H4.
  unfolds in H11;simpl in H11;inverts H11.
  assert ($ OS_STAT_RDY = $ OS_STAT_RDY ) by auto.
  apply H12 in H4.
  tryfalse.

  unfolds in Hnode.
  mytac.
  unfolds in H12.
  mytac.
  unfolds in H16.
  mytac.
  destruct H2.
  subst.
  unfolds in H18.
  assert ((p, wait (os_stat_q eid) n, m) = (p, wait (os_stat_q eid) n, m)) by auto.
  apply H18 in H2.
  mytac.
  unfolds in H2;mytac.
  unfolds in H24;simpl in H24;inverts H24.
  clear -H1 H5 H8 H9.
  int auto.
  clear H9;int auto.

  destruct H2.
  subst.
  unfolds in H17.
  assert ((p, wait (os_stat_sem eid) n, m) = (p, wait (os_stat_sem eid) n, m)) by auto.
  apply H17 in H2.
  mytac.
  unfolds in H2;mytac.
  unfolds in H24;simpl in H24;inverts H24.
  clear -H1 H5 H8 H9.
  int auto.
  clear H9;int auto.
  
  destruct H2.
  subst.
  unfolds in H19.
  assert ((p, wait (os_stat_mbox eid) n, m) = (p, wait (os_stat_mbox eid) n, m)) by auto.
  apply H19 in H2.
  mytac.
  unfolds in H2;mytac.
  unfolds in H24;simpl in H24;inverts H24.
  clear -H1 H5 H8 H9.
  int auto.
  clear H9;int auto.
  
  subst.
  unfolds in H20.
  assert ((p, wait (os_stat_mutexsem eid) n, m) = (p, wait (os_stat_mutexsem eid) n, m)) by auto.
  apply H20 in H2.
  mytac.
  unfolds in H2;mytac.
  unfolds in H24;simpl in H24;inverts H24.
  clear -H1 H5 H8 H9.
  int auto.
  clear H9;int auto.
  unfolds in H14.
  simpl in H14.
  destruct H1.
  eapply  ecblist_p_tick_rdy_ectr_q;eauto.
  destruct H1.
  eapply  ecblist_p_tick_rdy_ectr_sem;eauto.
  destruct H1.
  eapply  ecblist_p_tick_rdy_ectr_mbox;eauto.
  eapply ecblist_p_tick_rdy_ectr_mutexsem;eauto.
Qed.

Lemma tickchange_tcblist_p_hold_mid:
  forall ltlsy'' x p t m  htls'' htls rtbl hels x2 x3
         l rgrp head ectr l' rtbl' rgrp' ectr' h ll ltlsx'' ,
    joinsig x (p, t, m)  htls'' htls ->
    tickchange x t hels x2 x3 -> 
    tickchange_l l rtbl rgrp head ectr l' rtbl' rgrp' ectr' ->
    get_last_tcb_ptr ltlsy'' h = Some (Vptr x) ->
    TCBList_P h (ltlsy'' ++ (l :: ll) ++ ltlsx'') rtbl htls ->
    R_Prio_No_Dup_L (ltlsy'' ++ (l :: ll) ++ ltlsx'') ->
    TCBList_P h ((ltlsy'' ++ l' :: nil) ++ ll ++ ltlsx'') rtbl'
              (set htls x (p, x2, m)).
Proof.
  induction ltlsy''.
  intros.
  simpl in H3.
  simpl.
  mytac.
  simpl in H2.
  inverts H2.
  exists x x1 x4 (p, x2, m);splits;eauto.
  eapply tickchange_eq_ostcbnext;eauto.
  eapply tcbjoin_set;eauto.
  eapply tickchange_tcbnode_p_hold;eauto.
  lets Hx:join_tcbjoin_joinsig_eq' H6 H.
  subst x5.
  auto.
  eapply tickchange_other_tcblist_p_hold;eauto.
  unfolds in H7.
  destruct x5.
  destruct p0.
  mytac; auto.
  intros.
  assert (h <> Vptr x).
  eapply tcblist_p_tid_neq';eauto.
  simpl in H3.
  mytac.
  simpl.
  exists x0 x1 (set x4 x (p, x2, m)) x5;splits;eauto.
  eapply tcbjoin_neq;eauto.
  eapply tickchange_other_tcbnode_p_hold';eauto.
  eapply r_prio_no_dup_two_neq;eauto.
  apply TCBList_P_Split in H9.
  mytac.
  simpl in H11.
  mytac.
  unfolds in H14.
  destruct x12.
  destruct p0.
  mytac; auto.
  eapply IHltlsy'';eauto.
  eapply tcb_neq_joinsig_tcbjoin_joinsig_minus;eauto.
  clear -H6 H2.
  destruct ltlsy''.
  simpl in *.
  rewrite H6 in H2;auto.
  simpl in H2.
  simpl.
  auto.
  assert ((a :: ltlsy'') ++ (l :: ll) ++ ltlsx'' = (a::nil) ++ (ltlsy'' ++ (l :: ll) ++ ltlsx'') ++ nil).
  simpl.
  rewrite app_nil_r.
  auto.
  rewrite H3 in H4.
  eapply r_prio_no_dup_l_mid;eauto.
Qed.
  
Lemma tickstep_ecblist_p':
  forall ltls'' rtbl rgrp head lels ltls' rtbl' rgrp' lels', 
    tickstep_l ltls'' rtbl rgrp head lels ltls' rtbl' rgrp' lels' ->
    forall htls edata cur hels  hels' htls' h ltlsx'' ltls tcbx ltlsy'' htls'' h',
      R_Prio_No_Dup htls ->
      tickstep' htls hels htls' hels' htls''->
      ltls = ltlsy''++ ltls'' ++ ltlsx'' ->
      get_last_tcb_ptr ltlsy'' h = Some h' ->
      TCBList_P h' ltls'' rtbl htls'' ->
      TCBList_P h ltls rtbl htls ->
      TcbMod.join htls'' tcbx htls ->
      RH_TCBList_ECBList_P hels htls cur ->
      ECBList_P head Vnull lels edata hels htls ->
      ECBList_P head Vnull lels' edata hels' htls'.
Proof.
  introv H.
  inductions H.
  intros.
  simpl in H3.
  subst.
  inverts H0.
  auto.
  apply joinsig_false in H1;tryfalse.
  intros.
  assert (R_Prio_No_Dup_L ltls) as Hnodup.
  eapply r_prio_no_dup_join_imp with (tcbls'':=htls);eauto.
  apply TcbMod.join_comm.
  eapply TcbMod.join_emp.
  auto.
  simpl in H5.
  mytac.
  lets Hgs : tcbjoin_get_a_my H11.
  destruct x2.
  destruct p.
  lets Hsub:TcbMod.join_sub_l H7.
  lets Hres : tickstep_decompose Hgs Hsub H2.
  clear Hgs Hsub H2.
  mytac.
  lets Heq : tcbjoin_joinsig_eq H11 H2.
  subst x4.
  eapply IHtickstep_l with (h:=h) (h':=x0) (tcbx:=TcbMod.merge (TcbMod.sig x (p,x2,m)) tcbx) in H14;eauto.
  eapply r_prio_no_dup_setst_hold;eauto.
  instantiate (1:= ltlsy''++(l'::nil)).
  lets Hx: tickchange_eq_ostcbnext H10 H.
  clear -Hx.
  induction ltlsy''.
  simpl;auto.
  simpl.
  destruct ltlsy'';simpl;auto.
  eapply tickchange_other_tcblist_p_hold;eauto.
  eapply r_prio_no_dup_l_mid;eauto.
  unfolds in H12.
  mytac; auto.
  2:eapply joinsig_join_joinmergesig_eq_set;eauto.
  instantiate (1:=ltlsx'').
   lets Hx: tcb_join_joinsig_ex_joinsig H7 H2.
  mytac.
  eapply tickchange_tcblist_p_hold_mid;eauto.
  instantiate (1:=cur).
  eapply RH_TCBList_ECBList_P_tickchange;eauto.
  apply TcbMod.join_comm in H7.
  eapply TcbMod.join_joinsig_get;eauto.
  eapply tickchange_ecblist_p;eauto.
  apply TcbMod.join_comm in H7.
  eapply TcbMod.join_joinsig_get;eauto.
Qed.



Lemma tickstep_ecblist_p:
  forall h h' ltls1 ltls2 htls lels hels cur rgrp rtbl head edata rtbl' rgrp' hels' htls' lels' ltls' htls1 htls2,
    TcbMod.join htls1 htls2 htls ->
    TCBList_P h ltls1 rtbl htls1 ->
    TCBList_P h' ltls2 rtbl htls2 ->
    RH_TCBList_ECBList_P hels htls cur ->
    tcbls_rtbl_timetci_update (ltls1++ltls2) rtbl 
                              rgrp head lels =
    Some (ltls', rtbl', rgrp', lels') ->
    ECBList_P head Vnull lels edata hels htls ->
    tickstep htls hels htls' hels' ->
    R_Prio_No_Dup htls ->
    get_last_tcb_ptr ltls1 h = Some h' ->
    ECBList_P head Vnull lels' edata hels' htls'.
Proof.
  intros.
  apply tick_fixpoint_convert in H3.
  eapply tickstep_ecblist_p' with (ltlsy'':=nil) (ltlsx'':=nil) (tcbx:=TcbMod.emp) (h:=h) (h':=h);eauto.
  eapply TCBList_P_Combine;eauto.
  simpl.
  rewrite app_nil_r.
  simpl;eapply TCBList_P_Combine;eauto.
  apply TcbMod.join_comm.
  apply TcbMod.join_emp;auto.
Qed.

