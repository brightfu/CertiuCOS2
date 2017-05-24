Require Import ucos_include.
(*Require Import ucert. 
Require Import mathlib.

Require Export oscore_common.
*)

(* moved into common.v 
(*candidate lemmas for MapLib.v *)
Import MemMod.
Lemma join_merge : forall {m1 m2 m3}, join m1 m2 m3 -> m3 = merge m1 m2.
Proof.
  intros.
  apply extensionality.
  intros.
  rewrite merge_sem.
  unfold join in H; pose proof H a; clear H.
  destruct (get m1 a);
  destruct (get m2 a);
  destruct (get m3 a);
  subst; auto;
  inversion H0.
Qed.

Lemma disj_join_disj : forall m1 m2 m3 m4 m5 m6,
  join m1 m2 m3 -> join m4 m5 m6 -> disj m3 m6 ->
  disj m1 m4.
Proof.
  intros.
  pose proof join_merge H.
  pose proof join_merge H0.
  subst.
  pose proof disj_merge_elim_lr H1.
  destruct H2.
  destruct H2.
  apply disj_sym.
  auto.
Qed.
(*end of the candidate lemmas*)
*)

Fixpoint not_in {A B:Type} (e:B) (l:list A) (f:A -> option B) :=
  match l with
    | nil => True
    | h :: t => (forall e', f h = Some e' -> e' <> e) /\ not_in e t f
  end.

Fixpoint distinct' {A B:Type} (l:list A) (f:A -> option B) :=
  match l with
    | nil => True
    | h :: t => (forall e, f h = Some e -> not_in e t f) /\ distinct' t f
  end.

Definition distinct {A B:Type} (head:B) (l:list A) f := distinct' l f /\ not_in head l f. 

Fixpoint get_last {A B:Type} (l:list A) (f: A->option B) :=
  match l with
    | nil => None
    | e::nil => f e
    | h::t => get_last t f
  end.

Definition ecb_get_next_ptr (ecb: EventCtr) := let (a, b) := ecb in V_OSEventListPtr a.

Definition ecbls_ptr_distinct (ecbls: list EventCtr):= distinct' ecbls ecb_get_next_ptr. 

Lemma evsllseg_distinct :
  forall l1 l2 head s P,
    s |= evsllseg head Vnull l1 l2 ** P ->
    ecbls_ptr_distinct l1.
Proof.
  inductions l1; intros.
  unfolds; simpl; auto.

  destruct l2.
  unfold evsllseg in H; simpl in H; simpljoin1; tryfalse.
  unfold evsllseg in H; fold evsllseg in H.
  destruct a; sep pure.

  unfolds; simpl.
  split.

Lemma evsllseg_not_in_vnull :
  forall l1 l2 head s P,
    s |= evsllseg head Vnull l1 l2 ** P ->
    not_in head l1 ecb_get_next_ptr.
Proof.
  intros.
  destruct l1.
  simpl; auto.
  destruct l2.
  unfold evsllseg in H; simpl in H; simpljoin1; tryfalse.

  unfold evsllseg in H; fold evsllseg in H.
  destruct e.
  sep pure.
  simpl; split.
  intros.
  intro; substs.
  rewrite H0 in H1; inverts H1.
  destruct l1.
  simpl evsllseg in H; sep pure.
  destruct H1; substs.
Lemma AEventNode_vnull_false :
  forall s v v0 e0 P,
    s |= AEventNode Vnull v v0 e0 ** P ->
    False.
Proof.
  intros.
  unfold AEventNode in H; unfold AOSEvent in H; unfold node in H.
  sep pure.
  destruct H0; tryfalse.
Qed.

  eapply AEventNode_vnull_false; eauto.
  destruct l2.
  unfold evsllseg in H; simpl in H; simpljoin1; tryfalse.
  unfold evsllseg in H; fold evsllseg in H.
  destruct e; sep pure.

(* moved into common.v
Lemma Astruct_osevent_dup_false :
  forall p v1 v1' s,
    s |= Astruct p OS_EVENT v1 ** Astruct p OS_EVENT v1' -> False.
Proof.
  intros.
  destruct_s s.
  simpl in H; mytac.
  unfold Astruct in *.
  destruct v1; simpl in H3; tryfalse.
  destruct v1'; simpl in H4; tryfalse.
  destruct p.
  simpl in *; mytac.
  clear H13 H7.
  assert (MemMod.disj x9 x1).
  pose proof MemMod.join_disj_meq H0.
  destruct H; clear H1.
  clear H0; eapply disj_join_disj; eauto.

Lemma mapstoval_disj_false : forall a t v1 v2 m1 m2,
  (typelen t > 0)%nat -> mapstoval a t v1 m1 -> mapstoval a t v2 m2 -> MemMod.disj m1 m2 ->
  False.
Proof.
  intros.
  unfold mapstoval in *; mytac.

Lemma length_encode_val : forall t v, (typelen t > 0)%nat -> (length (encode_val t v) > 0)%nat.
Proof.
  intros.
  destruct t; destruct v;
  try solve [simpl; try (destruct a); auto];
  try solve [simpl in H; simpl; try (destruct a); destruct (typelen t * n)%nat; [omega | simpl; omega]];
  try solve [simpl in H; simpl; try (destruct a); destruct (szstruct d); [omega | simpl; omega]].
Qed.

  intros.
  pose proof length_encode_val t v1 H.
  pose proof length_encode_val t v2 H.

Lemma length_exists: forall {A:Type} (l: list A), (length l > 0)%nat -> exists h t, l = h :: t.
Proof.
  intros.
  destruct l.
  simpl in H; omega.
  eauto.
Qed.

  pose proof length_exists (encode_val t v2) H1.
  pose proof length_exists (encode_val t v1) H0.
  mytac.
  rewrite H5 in H3.
  rewrite H6 in H4.
  simpl in H3; destruct a.
  simpl in H4.
  mytac.
  unfolds in H9.
  unfolds in H7.
  substs.
  unfolds in H2.
  pose proof H2 (b, o); clear H2.
  unfolds in H4; pose proof H4 (b, o); clear H4.
  unfolds in H3; pose proof H3 (b, o); clear H3.
  rewrite MemMod.get_sig_some in *.
  destruct (MemMod.get m1 (b, o));
  destruct (MemMod.get m2 (b, o));
  destruct (MemMod.get x4 (b, o));
  destruct (MemMod.get x6 (b, o));
  tryfalse.
Qed.

  clear - H12 H6 H.
  pose proof mapstoval_disj_false (b, Int.unsigned i2) Int8u v v0 x9 x1.
  apply H0; auto.
Qed.



Lemma Astruct_osevent_dup_false' :
  forall p v1 v1' s P,
    s |= Astruct p OS_EVENT v1 ** Astruct p OS_EVENT v1' ** P -> False.
Proof.
  intros.
  destruct_s s.
  sep remember (3::nil)%nat in H.
  simpl in H; mytac.
  eapply Astruct_osevent_dup_false; eauto.
Qed.
  
Lemma AEventNode_dup_false :
  forall p v1 v2 v3 v4 e1 e2 P s,
    s |= AEventNode p v1 v2 e1 ** AEventNode p v3 v4 e2 ** P ->
    False.
Proof.
  intros.
  unfold AEventNode in H.
  destruct e1; destruct e2.
  unfold AOSEvent in H.
  unfold node in H.
  sep pure; mytac; substs.
  inverts H4.
  sep lift 3%nat in H.
  eapply Astruct_osevent_dup_false'; eauto.
  simpl in H; mytac; tryfalse.
  simpl in H; mytac; tryfalse.
  simpl in H; mytac; tryfalse.
Qed.
*)
  sep lifts (1::3::nil)%nat in H.
  eapply AEventNode_dup_false; eauto.

  clear H0.
  inductions l1.
  simpl; auto.

  destruct l2.
  unfold evsllseg in H.
  simpl in H; simpljoin1; tryfalse.

  unfold evsllseg in H; fold evsllseg in H.
  destruct a; sep pure.

  simpl.
  split.
  intros.
  intro; substs.
  rewrite H0 in H1; inverts H1.

  destruct l1.
  simpl evsllseg in H; sep pure; destruct H1; substs.
  sep lift 2%nat in H.
  eapply AEventNode_vnull_false; eauto.

  destruct l2.
  unfold evsllseg in H; simpl in H; simpljoin1; tryfalse.

  unfold evsllseg in H; fold evsllseg in H; destruct e1; sep pure.
  sep lifts (1::4::nil)%nat in H.
  eapply AEventNode_dup_false; eauto.

  eapply IHl1; eauto.
  sep lifts (3::2::1::nil)%nat in H.
  eauto.
Qed.

Lemma evsllseg_not_in_vnull' :
  forall l1 l2 head s,
    s |= evsllseg head Vnull l1 l2 ->
    not_in head l1 ecb_get_next_ptr.
Proof.
  intros.
  pose proof evsllseg_not_in_vnull l1 l2 head s Aemp.
  apply H0.
  destruct_s s.
  simpl.
  do 6 eexists.
  splits; eauto.
  apply map_join_comm.
  apply join_emp; auto.
  apply map_join_comm.
  apply join_emp; auto.
  unfolds; auto.
Qed.

  intros.
  rewrite H0 in H1; inverts H1.
  sep lift 2%nat in H.
  eapply evsllseg_not_in_vnull; eauto.

  sep lift 2%nat in H.
  unfold ecbls_ptr_distinct in IHl1.
  eapply IHl1; eauto.
Qed.

(*
Lemma hoare_pure_gen : forall P1 P2 (p:Prop) S Q a b c d,
                         (forall s, s |= P1 -> p) ->
                         {|a,b,c,d|}|-{{P1 ** P2 ** [|p|]}} S {{Q}} ->
                         {|a,b,c,d|} |- {{P1 ** P2}} S {{Q}}.
Proof.
  intros.
  apply backward_rule1 with (p:=(P1 ** P2 ** [|p|])); auto.
  intros.
  sep auto.
  destruct_s s.
  simpl in H1; mytac.
  apply (H (e, e0, x, i, (i0, i1, c0), x2, a0)); auto.
Qed.
*)

Lemma evsllseg_distinct' : 
  forall l1 l2 head s,
    s |= evsllseg head Vnull l1 l2 ->
    ecbls_ptr_distinct l1.
Proof.
  intros.
  pose proof evsllseg_distinct l1 l2 head s Aemp.
  apply H0.
  destruct_s s.
  simpl.
  do 6 eexists.
  splits; eauto.
  apply map_join_comm.
  apply join_emp; auto.
  apply map_join_comm.
  apply join_emp; auto.
  unfolds; auto.
Qed.


Lemma evsllseg_ptr_dup_false : forall l1 l2 x a1 a2 s lx ,
  s |= evsllseg (Vptr x) Vnull ((a1::l1)++(a2::l2)) lx ->
  get_last_ptr (a1::l1) = Some (Vptr x) ->
  False.
Proof.
  intros.
  apply evsllseg_not_in_vnull' in H.

Lemma get_last_not_in_false : forall {A B:Type} (l1 l2:list A) (e:B) (f:A->option B),
  get_last l1 f = Some e -> not_in e (l1 ++ l2) f -> False.
Proof.
  intro.
  intro.
  inductions l1; intros.
  simpl in H; tryfalse.
  destruct l1.
  simpl in H.
  inverts H.
  rewrite <- app_comm_cons in H0.
  simpl in H0.
  destruct H0.
  pose proof H e H2; tryfalse.

  pose proof IHl1 l2 e f.
  apply H1.
  unfold get_last in H.
  unfold get_last; auto.
  rewrite <- app_comm_cons in H0.
  unfold not_in in H0.
  destruct H0.
  unfold not_in; auto.
Qed.

Lemma not_in_get_last_ptr_false : forall l1 l2 x,
  not_in x (l1++l2) ecb_get_next_ptr -> get_last_ptr l1 = Some x ->
  False.                                  
Proof.
  inductions l1; intros.
  unfolds in H0; simpl in H0; unfolds in H0; simpl in H0; tryfalse.

  rewrite <- app_comm_cons in H.
  apply (IHl1 l2 x).
  simpl in H.
  destruct H; auto.
  
  destruct l1.
  unfolds in H0; simpl in H0; destruct a; unfolds in H0; simpl in H0.
  simpl in H.
  destruct H.
  unfold V_OSEventListPtr in H.
  apply H in H0; tryfalse.

  unfolds in H0.
  simpl in H0.
  unfolds; simpl; auto.
Qed.

  eapply not_in_get_last_ptr_false; eauto.
Qed.

Lemma val_eq_true_eq : forall v1 v2, val_eq v1 v2 = Some (Vint32 Int.one) -> v1 = v2.
Proof.
  intros.
  unfold val_eq in H.
  destruct v1; destruct v2;
  try (inversion H);
  try (destruct a; inversion H);
  auto.
  destruct (Int.eq i i0) eqn : eq1.
  pose proof Int.eq_spec i i0.
  rewrite eq1 in H0.
  substs; auto.
  inversion H.
  destruct a0.
  destruct (peq b b0) eqn : eq1;
  destruct (Int.eq i i0) eqn : eq2; substs; try inversion H.
  pose proof Int.eq_spec i i0.
  rewrite eq2 in H0; substs; auto.
Qed.

Ltac solve_Afalse_in_pre :=
  eapply backward_rule1 with (p:=Afalse);
  [intros s_1 H_1; destruct_s s_1; simpl in H_1; simpljoin1; tryfalse |
   apply pfalse_rule].

Lemma struct_type_vallist_match_os_event : forall v, struct_type_vallist_match os_ucos_h.OS_EVENT v -> exists v1 v2 v3 v4 v5 v6 tail, v = v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: tail.
Proof.
  intros.
  unfold os_ucos_h.OS_EVENT in H.
  simpl in H.
  unfolds in H.
  destruct v; tryfalse.
  destruct v0; simpljoin1; tryfalse.
  destruct v1; simpljoin1; tryfalse.
  destruct v2; simpljoin1; tryfalse.
  destruct v3; simpljoin1; tryfalse.
  destruct v4; simpljoin1; tryfalse.
  do 7 eexists; eauto.
Qed.

Lemma evsllseg_list_len_eq' : forall l1 l2 s p1 p2,
  s |= evsllseg p1 p2 l1 l2 -> length l1 = length l2.
Proof.
  inductions l1; intros.
  destruct l2.
  simpl; auto.
  simpl in H; simpljoin1.
  inversion H1.
  destruct l2.
  simpl in H; tryfalse.
  simpl.
  apply eq_S.
  unfold evsllseg in H.
  fold evsllseg in H.
  destruct a.
  destruct H.
  sep split in H.
  simpl in H; simpljoin1.
  eapply IHl1; eauto.
Qed.


Definition val_beq (v1 v2:val) :=
  match v1, v2 with
    | Vundef, Vundef => true
    | Vnull, Vnull => true
    | Vint32 i1, Vint32 i2 => Int.eq i1 i2
    | Vptr (b1, i1), Vptr (b2, i2) => peq b1 b2 && Int.eq i1 i2
    | _, _ => false
  end.

Fixpoint ptr_in_ectrls' (l:list EventCtr) (ptr:val) {struct l}:=
  match l with
    | nil => false
    | (a, b)::t => match t with
                | nil => false
                | _ :: _ => match V_OSEventListPtr a with
                              | Some ptr' => match val_beq ptr ptr' with
                                               | true => true
                                               | false => ptr_in_ectrls' t ptr
                                             end
                              | _ => ptr_in_ectrls' t ptr
                            end
              end
  end.

Definition ptr_in_ectrls (head:val) (l:list EventCtr) (ptr:val) :=
  match val_beq head ptr with
    | true => true
    | false => ptr_in_ectrls' l ptr
  end.

Lemma while_rule'' : forall spec sd linv I r ri p s e v tp tid,
  p ==> Rv e @ tp == v ->
  {|spec, sd, linv, I, r, ri|}|-tid {{p**[|v <> Vint32 Int.zero /\ v <> Vnull /\ v <> Vundef|]}}s{{p}} ->
  {|spec, sd, linv, I, r, ri|}|-tid {{p}}swhile e s{{p**[|v = Vint32 Int.zero \/ v = Vnull|]}}.
Proof.
  intros.
  eapply while_rule'.
  eapply backward_rule2; eauto.
  intros.
  eapply sep_aconj_r_aistrue_to_astar; eauto.
  intros.
  apply H in H1; eexists; eauto.
  intros.
  eapply sep_aconj_r_aisfalse_to_astar; eauto.
Qed.

Lemma evsllseg_vnull_false : forall s h t l,
  s |= evsllseg Vnull Vnull (h :: t) l -> False.
Proof.
  intros.
  simpl in H.
  destruct l.
  simpl in H; tryfalse.
  destruct h.
  unfold AEventNode in H.
  unfold AOSEvent in H.
  unfold node in H.
  sep pure; tryfalse.
Qed.

Lemma evsllseg_vnull_false_p : forall s h t l P,
  s |= evsllseg Vnull Vnull (h :: t) l ** P -> False.
Proof.
  intros.
  destruct_s s.
  simpl in H; simpljoin1.
  eapply evsllseg_vnull_false.
  unfold evsllseg; fold evsllseg.
  apply H3.
Qed.

Lemma val_beq_true_eq : forall v1 v2, val_beq v1 v2 = true -> v1 = v2.  
Proof.
  intros.
  destruct v1, v2; auto;
  try solve [simpl in H; try (destruct a); tryfalse].
  simpl in H; pose proof Int.eq_spec i i0; rewrite H in H0; substs; auto.
  simpl in H; destruct a; destruct a0.
  apply andb_true_iff in H; destruct H.
  pose proof Int.eq_spec i i0; rewrite H0 in H1; substs; auto; clear H0.

  destruct (peq b b0).
  substs; auto.
  inversion H.
Qed.

Lemma val_beq_true : forall v, val_beq v v = true.
Proof.
  intros.
  destruct v; unfolds; simpl; auto.
  rewrite Int.eq_true; auto.
  destruct a.
  apply andb_true_intro; split.
  apply peq_true; auto.
  apply Int.eq_true.
Qed.


Lemma ptr_in_ectrls_nil_false : forall head ptr,
  head <> ptr -> ptr_in_ectrls head nil ptr = false.
Proof.
  intros.
  unfolds.
  destruct (val_beq head ptr) eqn : eq1; simpl; auto.
  apply val_beq_true_eq in eq1; tryfalse.
Qed.

Lemma isptr_vundef1 : forall x,
  isptr x ->
  val_inj (bool_and (val_inj (notint (val_inj (val_eq x Vnull)))) (Vint32 Int.one)) <>Vundef.
Proof.
  intros.
  unfolds in H.
  destruct x;
  try solve [destruct H; [tryfalse | destruct H; tryfalse]].
  simpl.
  destruct (Int.ltu Int.zero (Int.notbool Int.one) && Int.ltu Int.zero Int.one); intro; tryfalse.
  simpl.
  destruct a.
  simpl.
  destruct (Int.ltu Int.zero (Int.notbool Int.zero) && Int.ltu Int.zero Int.one); simpl; intro; tryfalse.
Qed.

Lemma evsllseg_head_isptr' : forall l1 l2 s p1,
  s |= evsllseg p1 Vnull l1 l2 -> isptr p1.
Proof.
  intros.
  unfold evsllseg in H.
  destruct l1.
  simpl in H; simpljoin1.
  unfolds; auto.
  destruct l2.
  simpl in H; tryfalse.
  fold evsllseg in H.
  destruct e.
  unfold AEventNode in H.
  unfold AOSEvent in H.
  unfold node in H.
  sep pure; simpljoin1.
  unfolds; eauto.
Qed.

Lemma evsllseg_has_node : forall s x l1 l2,
  s |= evsllseg (Vptr x) Vnull l1 l2 ->
  exists h1 t1 h2 t2, l1 = h1 :: t1 /\ l2 = h2 :: t2.
Proof.
  intros.
  destruct l1.
  simpl in H; simpljoin1; tryfalse.
  destruct l2; simpl in H; simpljoin1; tryfalse.
  do 4 eexists.
  eauto.
Qed.

Lemma isptr_val_inj_vundef : forall x p, 
  isptr p -> val_inj (notint (val_inj (val_eq p (Vptr x)))) <> Vundef.
Proof.
  intros.
  unfolds in H.
  destruct p; try solve [destruct H; [tryfalse | destruct H; tryfalse]].
  simpl; destruct x; simpl; intro; tryfalse.
  simpl; destruct a, x.
  destruct (peq b b0); destruct (Int.eq i i0); intro; tryfalse.
Qed.

Lemma evsllseg_append1 : forall (v'9:list EventCtr) (v'11:list EventData) v'6 v'13 v'12 x4 (v1:val) x6 v'8 x8 v'10 v0 v1 v'9 v'11 s d i0,
  RL_Tbl_Grp_P v0 v'12 -> id_addrval' (Vptr (v'13, Int.zero)) OSEventTbl os_ucos_h.OS_EVENT = Some v'10 -> struct_type_vallist_match os_ucos_h.OS_EVENT
          (i0 :: v'12 :: x4 :: v1 :: x6 :: v'8 :: x8) ->               
  s |= evsllseg v'6 (Vptr (v'13, Int.zero)) v'9 v'11 **
       Astruct (v'13, Int.zero) os_ucos_h.OS_EVENT(i0 :: v'12 :: x4 :: v1 :: x6 :: v'8 :: x8) **
       AOSEventTbl v'10 v0 ** AEventData (i0 :: v'12 :: x4 :: v1 :: x6 :: v'8 :: x8) d ->
  s |= evsllseg v'6 v'8 (v'9 ++ (i0 :: v'12 :: x4 :: v1 :: x6 :: v'8 :: x8, v0) :: nil) (v'11 ++ d :: nil).
Proof.
  intros.
  gen v'6 v'13 v'12 x4 x6 v'8 x8 v'10 v0 v2. gen v'1 s d i0. clear - v'0.
  inductions v'0; intros.
  destruct v'1.
  unfold evsllseg in H2.
  sep split in H2.
  do 2 rewrite app_nil_l.
  simpljoin1.
  unfold evsllseg; unfold AEventNode; unfold AOSEvent; unfold node.
  sep pauto; eauto.
  unfold evsllseg in H2; sep split in H2; simpljoin1.
  inversion H4.
  destruct v'1.
  unfold evsllseg in H2; simpl in H2; simpljoin1; tryfalse.
  destruct_s s.
  unfold evsllseg in H2; fold evsllseg in H2.
  do 2 rewrite <- app_comm_cons.
  unfold evsllseg; fold evsllseg.
  destruct a.
  sep pauto; eauto.
Qed.


(*
Lemma mqsllseg_append1 : forall (v'9:list EventCtr) (v'11:list EventData) v'6 v'13 v'12 x4 (v1:val) x6 v'8 x8 v'10 v0 v1 v2 v3 v4 v'9 v'11 s,
  RL_Tbl_Grp_P v0 v'12 -> id_addrval' (Vptr (v'13, Int.zero)) OSEventTbl OS_EVENT = Some v'10 -> struct_type_vallist_match OS_EVENT
          (V$OS_EVENT_TYPE_Q :: v'12 :: x4 :: v1 :: x6 :: v'8 :: x8) ->               
  s |= mqsllseg v'6 (Vptr (v'13, Int.zero)) v'9 v'11 **
       Astruct (v'13, Int.zero) OS_EVENT(V$OS_EVENT_TYPE_Q :: v'12 :: x4 :: v1 :: x6 :: v'8 :: x8) **
       AOSEventTbl v'10 v0 ** AMsgData v1 v2 v3 v4 ->
  s |= mqsllseg v'6 v'8 (v'9 ++ (V$OS_EVENT_TYPE_Q :: v'12 :: x4 :: v1 :: x6 :: v'8 :: x8, v0) :: nil) (v'11 ++ DMsgQ v1 v2 v3 v4 :: nil).
Proof.
  intros.
  gen v'6 v'13 v'12 x4 x6 v'8 x8 v'10 v0 v2. gen v3 v4 v5 v'1 s. clear - v'0.
  inductions v'0; intros.
  destruct v'1.
  unfold mqsllseg in H2.
  sep split in H2.
  do 2 rewrite app_nil_l.
  mytac.
  unfold mqsllseg; unfold AEventNode; unfold AOSEvent; unfold node.
  sep pauto; eauto.
  unfold mqsllseg in H2; sep split in H2; mytac.
  inversion H4.
  destruct v'1.
  unfold mqsllseg in H2; simpl in H2; mytac; tryfalse.
  destruct_s s.
  unfold mqsllseg in H2; fold mqsllseg in H2.
  do 2 rewrite <- app_comm_cons.
  unfold mqsllseg; fold mqsllseg.
  destruct a.
  sep pauto; eauto.
Qed.
 *)

Lemma notbool_one_zero : Int.notbool Int.one = Int.zero.
Proof.
  unfold Int.notbool.
  rewrite Int.eq_false; auto; intro; tryfalse.
Qed.

Lemma notbool_zero_one : Int.notbool Int.zero = Int.one.
Proof.
  unfold Int.notbool.
  rewrite Int.eq_true; auto.
Qed.

Lemma evsllseg_vnull_nil_p : forall {l1 l2 s P},
  s |= evsllseg Vnull Vnull l1 l2 ** P -> l1 = nil /\ l2 = nil.
Proof.
  intros.
  destruct l1; destruct l2; auto;
  try solve [simpl in H; simpljoin1; tryfalse].
  unfold evsllseg in H; fold evsllseg in H.
  destruct e; unfold AEventNode in H; unfold AOSEvent in H; unfold node in H.
  sep pure; simpljoin1; tryfalse.
Qed.

Lemma get_last_ptr_ptr_in_ectrls_true : forall l x head h t,
  get_last_ptr l = Some (Vptr x) ->
  ptr_in_ectrls head (l ++ h::t) (Vptr x) = true.
Proof.
  intro.
  inductions l; intros.
  unfolds in H; simpl in H; unfolds in H; simpl in H; tryfalse.
  unfolds in H; simpl in H; destruct l.
  destruct a.
  unfolds.
  destruct (val_beq head (Vptr x)); auto.
  rewrite <- app_comm_cons.
  rewrite app_nil_l.
  unfolds; fold ptr_in_ectrls'.
  rewrite H.
  rewrite val_beq_true; auto.

  do 2 rewrite <- app_comm_cons.
  unfolds.
  destruct (val_beq head (Vptr x)); auto.
  unfold ptr_in_ectrls'; fold ptr_in_ectrls'.
  destruct a.

  destruct (V_OSEventListPtr v) eqn : eqx.
  destruct (val_beq (Vptr x) v1) eqn : eq1; auto.

  assert (get_last_ptr (e :: l) = Some (Vptr x)).
  unfolds; auto.
  pose proof IHl x v1 h t H0; clear IHl.
  rewrite <- app_comm_cons in H1.
  unfolds in H1.
Lemma val_beq_sym : forall v1 v2, val_beq v1 v2 = val_beq v2 v1.
Proof.
  intros.
  destruct v1, v2; try (destruct a); auto.
  unfolds.
  rewrite Int.eq_sym; auto.
  unfolds.
  destruct a0.
  rewrite Int.eq_sym.

  destruct (peq b b0) eqn : eq1.
  substs.
  rewrite eq1; auto.
  destruct (peq b0 b) eqn : eq2; substs.
  rewrite eq1 in eq2; inversion eq2.
  auto. (*why this can be proved ???*)
Qed.

  rewrite val_beq_sym in eq1.
  rewrite eq1 in H1.
  unfolds in H1; fold ptr_in_ectrls' in H1.
  auto.

  assert (get_last_ptr (e :: l) = Some (Vptr x)).
  unfolds; auto.
  pose proof IHl x Vnull h t H0; clear IHl.
  unfolds in H1.
  simpl in H1.
  auto.
Qed.

Lemma evsllseg_get_last_eq_p :
  forall (ls1 : list EventCtr) (head tail : val) (ls2 : list EventData)
    (s : RstateOP) P,
  ls1 <> nil ->
  s |= evsllseg head tail ls1 ls2 ** P -> get_last_ptr ls1 = Some tail.
Proof.
  intros.
  destruct_s s.
  simpl in H0; simpljoin1.
  eapply evsllseg_get_last_eq; eauto.
Qed.

Lemma ptr_in_ectrls_false_append : forall l head p1 p2 e, 
  ptr_in_ectrls head l p1 = false ->
  get_last_ptr l = Some p2 ->
  p1 <> p2 ->
  ptr_in_ectrls head (l ++ e :: nil) p1 = false.
Proof.
  intros.
  destruct l.
  unfolds in H0; simpl in H0; unfolds in H0; simpl in H0; tryfalse.
  gen e0.
  inductions l; intros.
  unfolds in H.
  destruct (val_beq head p1) eqn : eq1; tryfalse.
  unfolds in H0; simpl in H0; destruct e0.
  rewrite <- app_comm_cons.
  unfolds.
  rewrite eq1.
  rewrite app_nil_l.
  unfolds.
  rewrite H0.
  destruct (val_beq p1 p2) eqn : eq2.
  false.
  apply H1.
  apply val_beq_true_eq; auto.
  destruct e; auto.
  pose proof (IHl head p1 p2 e H1 a).
  assert (ptr_in_ectrls head (a :: l) p1 = false).
  unfolds in H.
  destruct (val_beq head p1) eqn : eq1; tryfalse.
  unfolds.
  rewrite eq1.
  unfolds in H; fold ptr_in_ectrls' in H.
  destruct e0; destruct (V_OSEventListPtr v).
  destruct (val_beq p1 v1); tryfalse.
  unfolds; auto.
  unfolds; auto.
  assert (get_last_ptr (a :: l) = Some p2).
  unfolds in H0; simpl in H0.
  unfolds; simpl; auto.
  pose proof H2 H3 H4.
  clear H2 H3 H4.
  unfolds in H; destruct (val_beq head p1) eqn : eq1; tryfalse.
  rewrite <- app_comm_cons.
  unfolds.
  rewrite eq1.
  unfolds in H5.
  rewrite eq1 in H5.
  unfolds in H; fold ptr_in_ectrls' in H.
  destruct e0.
  unfolds; fold ptr_in_ectrls'.
  rewrite <- app_comm_cons.  
  unfolds in H5.
  rewrite <- app_comm_cons in H5; fold ptr_in_ectrls' in H5.
  destruct (V_OSEventListPtr v) eqn : eq2.
  destruct (val_beq p1 v1) eqn : eq3; tryfalse.
  unfolds; fold ptr_in_ectrls'; auto.
  unfolds; fold ptr_in_ectrls'; auto.
Qed.

Lemma val_inj_notint_zero_eq : forall v1 v2,
  val_inj (notint (val_inj (val_eq v1 v2))) = Vint32 Int.zero -> v1 = v2.
Proof.
  intros.
  destruct v1, v2; auto;
  try solve [simpl in H; try (destruct a); tryfalse].
  simpl in H.
  destruct (Int.eq i i0) eqn : eq1.
  pose proof Int.eq_spec i i0.
  rewrite eq1 in H0; substs; auto.
  simpl in H.
  rewrite notbool_zero_one in H; tryfalse.
  simpl in H; destruct a, a0.
  destruct (peq b b0) eqn : eq1; destruct (Int.eq i i0) eqn : eq2;
  try solve [simpl in H; rewrite notbool_zero_one in H; tryfalse].
Lemma int_eq_true_eq : forall i1 i2, Int.eq i1 i2 = true -> i1 = i2.
Proof.
  intros.
  pose proof Int.eq_spec i1 i2.
  rewrite H in H0.
  auto.
Qed.

  apply int_eq_true_eq in eq2; substs; auto.
Qed.

Lemma val_inj_notint_vnull_false : forall x, val_inj (notint x) = Vnull -> False.
Proof.
  intros.
  unfolds in H.
  unfold notint in H.
  destruct x; tryfalse.
Qed.

Open Scope code_scope.
Lemma aistrue_oand : forall s b1 b2, 
    s |= Aistrue ( b1 &&ₑ b2) -> s |= Aistrue b1 /\ s |= Aistrue b2. 
Proof.
  intros.
  destruct_s s.

  simpl in H.
  simpl.
  do 2 destruct H.
  destruct (evaltype b1 (e, e0, m)); destruct (evaltype b2 (e, e0, m)); tryfalse.
  destruct (bop_int_type t t0); tryfalse.
  destruct (evalval b1 (e, e0, m)); tryfalse.
  destruct (evalval b2 (e, e0, m)); tryfalse.
  unfold bool_and in H.
  destruct v; tryfalse.
  destruct v0; tryfalse.
  destruct (Int.ltu Int.zero i2 && Int.ltu Int.zero i3) eqn : eq1; inversion H; substs; tryfalse.
  apply andb_true_iff in eq1.
  destruct eq1.
  split.
  exists (Vint32 i2).
  split; auto.

  unfolds.
  unfold Int.ltu in H1.
  rewrite Int.unsigned_zero in H1.
  destruct (zlt 0 (Int.unsigned i2)) eqn : eq1; tryfalse.
  unfold Int.eq.
  rewrite Int.unsigned_zero.
  rewrite zeq_false; auto.
  omega.
  exists (Vint32 i3).
  split; auto.
  unfolds.
  unfold Int.ltu in H2.
  rewrite Int.unsigned_zero in H2.
  destruct (zlt 0 (Int.unsigned i3)) eqn : eq1; tryfalse.
  unfold Int.eq.
  rewrite Int.unsigned_zero.
  rewrite zeq_false; auto.
  omega.
Qed.

Lemma evsllseg_ecbls_ptr_distinct:
  forall l1 l2 s head p vl P,
    s |= evsllseg head (Vptr p) l1 l2 ** Astruct p os_ucos_h.OS_EVENT vl ** P ->
    ecbls_ptr_distinct l1.
Proof.
  inductions l1; intros.
  unfolds; simpl; auto.

  destruct l2.
  simpl evsllseg in H. 
  simpl sat in H; simpljoin1; tryfalse.

  unfold evsllseg in H; fold evsllseg in H.
  destruct a.
  sep pure.

  sep remember (2::3::nil)%nat in H.
  pose proof IHl1 l2 s x p vl H1 H.
  unfolds; unfolds in H2.
  simpl.
  split; auto.
  intros.
  rewrite H0 in H3.
  inverts H3.

Lemma evsllseg_astruct_not_in :
  forall l1 l2 v p vl P s,
    s |= evsllseg v (Vptr p) l1 l2 ** Astruct p os_ucos_h.OS_EVENT vl ** P ->
    not_in v l1 ecb_get_next_ptr.
Proof.
  intros.
  destruct l1.
  simpl; auto.
  destruct l2.
  unfold evsllseg in H.
  simpl sat in H; simpljoin1; tryfalse.

  unfold evsllseg in H; fold evsllseg in H.
  destruct e; sep pure.
  simpl.
  split.
  intros.
  rewrite H0 in H1; inverts H1.
  intro; substs.
  destruct l1; destruct l2.
  unfold evsllseg in H.
  sep pure.
  destruct H1; substs.
  unfold AEventNode in H.
  unfold AOSEvent in H; unfold node in H.
  sep pure; simpljoin1; subst; inverts H1.
  sep lift 4%nat in H.
  eapply Astruct_osevent_dup_false'; eauto. 
  simpl in H; simpljoin1; tryfalse.

  unfold evsllseg in H; simpl in H; simpljoin1; tryfalse.
  unfold evsllseg in H; fold evsllseg in H.
  destruct e; sep pure.

  sep lift 3%nat in H.
  eapply AEventNode_dup_false; eauto.

  clear H0.
  inductions l1; intros.
  simpl; auto.

  destruct l2.
  unfold evsllseg in H.
  simpl in H; simpljoin1; tryfalse.
  unfold evsllseg in H; fold evsllseg in H.
  destruct a; sep pure.
  simpl.
  split.
  intros.
  rewrite H0 in H1; inverts H1.
  intro; substs.
  destruct l1.
  unfold evsllseg in H; sep pure.
  destruct H1; substs.
  unfold AEventNode at 2 in H.
  unfold AOSEvent in H; unfold node in H.
  sep pure; simpljoin1; substs; inverts H1.
  sep lift 5%nat in H.
  eapply Astruct_osevent_dup_false'; eauto.

  destruct l2.
  unfold evsllseg in H.
  simpl in H; simpljoin1; tryfalse.
  unfold evsllseg in H; fold evsllseg in H.
  destruct e1; sep pure.
  sep lift 4%nat in H.
  eapply AEventNode_dup_false; eauto.

  sep remember (3::2::4::nil)%nat in H.
  eapply IHl1; eauto.
Qed.

  eapply evsllseg_astruct_not_in; eauto.
Qed.

Lemma ecbls_ptr_distinct_get_last_eq : forall (l1 l2 l1' l2': list EventCtr) e,
  ecbls_ptr_distinct (l1++l2) -> l1++l2 = l1'++l2' ->
  get_last l1 ecb_get_next_ptr = Some e -> get_last l1' ecb_get_next_ptr = Some e ->
  l1 = l1'.
Proof.
  intro.
  inductions l1; intros.
  simpl in H1; tryfalse.
 
  destruct l1'.
  simpl in H2; tryfalse.
  substs.

  do 2 rewrite <- app_comm_cons in H0.
  inversion H0; substs.
  rewrite <- app_comm_cons in H.
  unfolds in H.
  simpl in H.
  destruct H.

  destruct l1; destruct l1'; auto.
  rewrite app_nil_l in H5.
  rewrite app_nil_l in H.
  rewrite H5 in H.
  simpl in H1.
  destruct l1'.
  simpl in H2.
  inverts H2.
  rewrite <- app_comm_cons in H.
  pose proof H e H1.  
  simpl in H2.
  unfolds in H1.
  inverts H1.
  destruct H2.
  pose proof H1 e.
  unfold ecb_get_next_ptr in H4.
  apply H4 in H6; tryfalse.

  do 2 rewrite <- app_comm_cons in H0.
  simpl in H2.
  destruct l1'.
  pose proof H e H1.
  rewrite H5 in H3.
  rewrite app_nil_l in H3.
  do 2 rewrite <- app_comm_cons in H3.
  simpl in H3.
  destruct H3.
  destruct H6.
  simpl in H4.
  destruct H4.
  destruct H8.
  pose proof H8 e H2; tryfalse.
  pose proof H e H1.
  simpl in H4.
  destruct H4.
  destruct H6.
  destruct H7.
  destruct l1'.
  simpl in H2.
  pose proof H7 e H2; tryfalse.

  false.
  assert(get_last (e4::l1') ecb_get_next_ptr = Some e).
  unfolds in H2.
  unfolds; auto.
  eapply get_last_not_in_false; eauto.
  
  simpl in H2.
  pose proof H e H2.
  false.
  assert (get_last (e1 :: l1) ecb_get_next_ptr = Some e).
  unfold get_last in H1.
  unfolds; auto.
  eapply get_last_not_in_false; eauto.

  do 2 rewrite <- app_comm_cons in H0.
  inverts H0.
  pose proof IHl1 l2 (e2::l1') l2' e.
  rewrite H0; eauto.
Qed.

Lemma get_last_get_last_ptr_eq :
  forall l, get_last_ptr l = get_last l ecb_get_next_ptr.
Proof.
  inductions l; intros.
  unfolds; simpl.
  unfolds; simpl; auto.

  unfold get_last_ptr in IHl.
  unfolds; simpl.
  rewrite <- IHl.
  destruct l; auto.
Qed.

Lemma get_last_app : forall {A B:Type} (l: list A) tail f (x:B),
  f tail = Some x ->
  get_last (l++tail::nil) f = Some x.
Proof.
  inductions l; intros.
  simpl; auto.
  rewrite <- app_comm_cons.
  simpl.
Lemma app_tail_exists_head : forall {A:Type} (l:list A) tail, 
  exists h t, (l ++ tail::nil) = h::t.
Proof.
  inductions l; intros.
  simpl; eauto.
  rewrite <- app_comm_cons.
  pose proof IHl tail.
  do 2 destruct H.
  exists a (x::x0).
  rewrite H; auto.
Qed.
  pose proof app_tail_exists_head l tail.
  do 2 destruct H0.
  rewrite H0.
  pose proof IHl tail f x H.
  rewrite H0 in H1; auto.
Qed.

Lemma app_length_tail : forall {A:Type} (l:list A) tail,
  length (l++tail::nil) = ((length l) + 1)%nat.
Proof.
  inductions l; intros.
  simpl; auto.
  rewrite <- app_comm_cons.
  simpl.
  rewrite IHl; auto.
Qed.

Lemma app_length_eq_eq : forall {A:Type} (l1:list A) l2 l1' l2',
  l1 ++ l2 = l1' ++ l2' -> length l1 = length l1' ->
  l1 = l1'.
Proof.
  inductions l1; intros.
  destruct l1'; simpl in H0; auto.
  inversion H0.

  destruct l1'.
  simpl in H0; inversion H0.
  do 2 rewrite <- app_comm_cons in H.
  inverts H.
  simpl in H0.
  inverts H0.
  erewrite IHl1; eauto.
Qed.

Lemma upd_last_ectrls_last : forall l v1 v2 v3 v4 v5 v6 v7 etbl x,
  upd_last_ectrls (l ++ ((v1::v2::v3::v4::v5::v6::v7), etbl)::nil) x =
  l ++ ((v1::v2::v3::v4::v5::x::v7), etbl)::nil.                             
Proof.
  inductions l; intros.
  simpl; auto.
  do 2 rewrite <- app_comm_cons.
  unfold upd_last_ectrls.
  simpl length.
  rewrite <- pred_of_minus.
  rewrite <- pred_Sn.
  unfold update_nth_ectrls.
  fold update_nth_ectrls.
  destruct l.
  rewrite app_nil_l.
  simpl length.
  simpl; auto.
  rewrite <- app_comm_cons.
  simpl length.
  simpl.
  assert (p :: l ++ (v1 :: v2 :: v3 :: v4 :: v5 :: x :: v7, etbl) :: nil = (p :: l) ++ (v1 :: v2 :: v3 :: v4 :: v5 :: x :: v7, etbl) :: nil).
  rewrite app_comm_cons; auto.
  rewrite H.
Lemma cons_ext : forall {A} (h:A) t1 t2, t1 = t2 -> cons h t1 = cons h t2.
Proof.
  intros; substs; auto.
Qed.
  apply cons_ext.
  unfold upd_last_ectrls in IHl.
  pose proof IHl v1 v2 v3 v4 v5 v6 v7 etbl x; clear IHl.
  rewrite <- app_comm_cons in H0.
  unfold update_nth_ectrls in H0.
  fold update_nth_ectrls in H0.
  simpl length in H0.
  rewrite <- pred_of_minus in H0.
  rewrite <- pred_Sn in H0.
  auto.
Qed.

Lemma evsllseg_merge' : forall (l1 : list EventCtr) (l1' : list EventData)
 (l2 : list EventCtr) (l2' : list EventData) (x1 x2 y : val) (s : RstateOP),
  s |= evsllseg x1 y l1 l1' ** evsllseg y x2 l2 l2' ->
  s |= evsllseg x1 x2 (l1 ++ l2) (l1' ++ l2').
Proof.
  intros.
  assert (length l1 = length l1').
  apply evsllseg_list_len_eq in H; auto.
  assert (length l2 = length l2').
  sep lift 2%nat in H.
  apply evsllseg_list_len_eq in H; auto.
  assert (s |= evsllseg x1 y l1 l1' ** evsllseg y x2 l2 l2' ** Aemp).
  sep auto.
  lets Hx: evsllseg_merge H0 H1 H2.
  clear - Hx.
  sep auto.
Qed.



(*
in this version the get filed function returns a non-optional value

Fixpoint not_in {A B:Type} (e:B) (l:list A) (get_field:A->B) :=
  match l with
    | nil => True
    | h :: t => get_field h <> e /\ not_in e t get_field
  end.

Fixpoint distinct' {A B:Type} (l:list A) (get_field:A->B) :=
  match l with
    | nil => True
    | h :: t => not_in (get_field h) t get_field /\ distinct' t get_field
  end.

Definition distinct {A B:Type} (head:B) (l:list A) get_field := distinct' l get_field /\ not_in head l get_field. 


Fixpoint get_last {A B:Type} (l:list A) (f:A->B) :=
  match l with
    | nil => None
    | e::nil => Some (f e)
    | h::t => get_last t f
  end.

Definition f := fun (n:nat) => n.

Lemma test_lemma : forall (l1 l2 l1' l2': list nat) e1 e2,
  distinct' (l1++l2) f -> l1++l2 = l1'++l2' ->
  get_last l1 f = Some e1 -> get_last l1' f = Some e2 -> e1 = e2 ->
  l1 = l1'.
Proof.
  intro.
  inductions l1; intros.
  simpl in H1; tryfalse.

  destruct l1'.
  simpl in H2; tryfalse.
  substs.

  do 2 rewrite <- app_comm_cons in H0.
  inversion H0; substs.
  rewrite <- app_comm_cons in H.
  simpl in H.
  destruct H.
  
  destruct l1; destruct l1'; auto.
  rewrite app_nil_l in H5.
  rewrite app_nil_l in H.
  rewrite H5 in H.
  simpl in H1.
  inverts H1.
  destruct l1'.
  simpl in H2.
  inverts H2.
  rewrite <- app_comm_cons in H.
  simpl in H.
  destruct H; tryfalse.
  do 2 rewrite <- app_comm_cons in H.
  simpl in H.
  simpl in H2.
  destruct l1'.
  inverts H2.
  destruct H.
  destruct H1.
  tryfalse.
  
Lemma get_last_not_in_false : forall {A B:Type} (l1 l2:list A) (e:B) (f:A->B),
  get_last l1 f = Some e -> not_in  e (l1 ++ l2) f -> False.
Proof.
  intro.
  intro.
  inductions l1; intros.
  simpl in H; tryfalse.
  destruct l1.
  simpl in H.
  inverts H.
  rewrite <- app_comm_cons in H0.
  simpl in H0.
  destruct H0; tryfalse.
  pose proof IHl1 l2 e f0.
  apply H1.
  unfold get_last in H.
  unfold get_last; auto.
  rewrite <- app_comm_cons in H0.
  unfold not_in in H0.
  destruct H0.
  unfold not_in; auto.
Qed.

  false.
  destruct H; destruct H1.
  eapply get_last_not_in_false; eauto.

  simpl in H2; inverts H2.
  false.
  rewrite <- app_comm_cons in H.
  simpl in H1.
  simpl in H.
  destruct H.
  eapply get_last_not_in_false; eauto.
  unfold get_last.
  destruct l1.
  inverts H1; tryfalse.
  simpl in H1.
  destruct l1; auto.

  do 2 rewrite <- app_comm_cons in H0.
  inverts H0.
  pose proof IHl1 l2 (n1::l1') l2' e2 e2.
  rewrite H0; eauto.
Qed.
*)


