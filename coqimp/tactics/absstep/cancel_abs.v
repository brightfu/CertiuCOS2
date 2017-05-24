Require Import include_frm.
Require Import sep_auto.

Set Implicit Arguments.

(* Aabsdata _ _ imply OSAbstMod.get *)

Lemma emp_disj:
  forall  (A B T : Type) (MC: PermMap A B T)   O ,
    disjoint O emp.
Proof.
  intros.
  unfolds.
  exists O.
  apply map_join_emp.
Qed.

Hint Resolve emp_disj : abst_solver_base.



Lemma absdata_elim :
  forall s O gamma x y P,
    (s, O, gamma) |= Aabsdata x y ** P ->
    get O x = Some y.
Proof.
  intros.
  destruct s as [ [ [ [ ] ] ] ].
  simpl in *.
  simp join.
  eapply  join_sig_get_disj; eauto.
Qed.

(*
Lemma disj_is_disjoin :
  forall a b,
    disjoint a b -> OSAbstMod.disj a b.
Proof.
  intros.
  unfold OSAbstMod.disj.
  unfold disjoint in H.
  intros.
  simpljoin.
  unfold join in H.
  simpl in H.
  unfold OSAbstMod.join in H.
  lets ff: H a0.
  destruct (OSAbstMod.get a a0);
  destruct (OSAbstMod.get b a0);
  auto.
Qed.
*)

Lemma absdata_elim' :
  forall s O O' gamma x y P,
    (s, O, gamma) |= Aabsdata x y ** P ->
    disjoint O O' ->
    get (merge O O') x = Some y.
Proof.
  intros.
  destruct s as [ [ [ [ ] ] ] ].
  simpl in *.
  simp join.
  eapply  join_sig_get_disj in H3.
  simp join.
  eapply disj_get_merge_get; eauto.
  unfolds; simpl; auto.
Qed.

Lemma get_set_idneq:
  forall (O: OSAbstMod.listset) Of id id' x y,
    disjoint O Of ->
    get O id' = Some y ->
    get O id = Some x ->
    id <> id' ->
    get (merge (set O id' y) Of) id = Some x.
Proof.
  intros.
  eapply disj_get_merge_get .
  unfolds; simpl; auto.
  eapply abst_get_set_disj; eauto.
  eapply get_set_neq; eauto.
Qed.

Lemma get_set_idneq':
  forall (O: OSAbstMod.listset) O' x y x' y' y'',
    disjoint O O' ->
    get O x = Some y ->
    get O x' = Some y' ->
    x <> x' ->
    get (merge (set O x y'') O')  x' = Some y'.
Proof.
  intros.
  eapply disj_get_merge_get .
  unfolds; simpl ; auto.
  eapply abst_get_set_disj; eauto.
  eapply get_set_neq; eauto.
Qed.

Lemma absdata_elim'' :
  forall (s : taskst) (O O' O'' : OSAbstMod.map)
         (gamma : absop) (x x': absdataid) (y y' y'' : absdata) (P : asrt),
    O'' = set O x y'' ->
    (s, O, gamma) |= Aabsdata x y ** Aabsdata x' y' ** P ->
    disjoint O O' ->
    get (merge O'' O') x' = Some y' /\ disjoint O'' O'.
Proof.
  intros.
  simpl in H0.
  simp join.
  apply join_sig_get_disj in H9.
  simp join.
  apply join_sig_get_disj in H4.
  simp join.
  assert (get O x' = Some y').
  eapply sub_get_get; eauto.
  split. 
  eapply  get_set_idneq'; eauto.
  introv Hf.
  subst x.
  tryfalse.
  eapply abst_get_set_disj; eauto.
  unfolds; simpl; auto.
  unfolds; simpl; auto.
Qed.



Lemma eqdomO_same:forall O,eqdomO O O.
Proof.
  intros.
  unfolds;split; intros.
  split; auto.
  eexists.
  split;eauto.
  unfolds.
  intros;split;auto.
Qed.
(*
Lemma set_eqdom: forall O Of id x y, OSAbstMod.disj O Of -> OSAbstMod.get O id = Some x -> eqdomO (OSAbstMod.merge O Of) (OSAbstMod.merge (OSAbstMod.set O id y) Of).
Proof.
  intros.
  eapply OSAbstMod.eqdom_merge_set; eauto.
Qed.
*)
Lemma eqdomtls_trans : forall a b c, eqdomtls a b -> eqdomtls b c -> eqdomtls a c.
Proof.
  intros.
  unfold eqdomtls in *.
  intro.
  rewrite H.
  auto.
Qed.

Lemma eqdomO_trans:forall O O' O'', eqdomO O O' -> eqdomO O' O'' -> eqdomO O O''.
Proof.
  intros; unfold eqdomO in *.
  simpljoin.
  intros; split.
  intros.
  rewrite H.
  auto.
  intros.
  lets fff: H2 H3.
  simpljoin.
  lets bb: H1 H4.
  simpljoin.
  exists x0.
  split; auto.
  eapply eqdomtls_trans; eauto.
Qed.

(*

Lemma set_eqdom': forall O O' Of id x y, OSAbstMod.disj O' Of -> OSAbstMod.get O' id = Some x ->eqdomO (OSAbstMod.merge O Of) (OSAbstMod.merge O' Of) -> eqdomO (OSAbstMod.merge O Of) (OSAbstMod.merge (OSAbstMod.set O' id y) Of).
Proof.
  intros.
  eapply eqdomO_trans;eauto.
  eapply set_eqdom;eauto.
Qed.
*)


Lemma get_set_ideq:
  forall(O: OSAbstMod.listset)  Of id y y',
    disjoint O Of ->
    get O id =  Some y' ->
    isRw y' = true ->
    get (merge (set O id y) Of) id = Some y.
Proof.
  intros.
  eapply disj_get_merge_get; eauto.
  eapply abst_get_set_disj; eauto.
  eapply get_set_eq.
Qed.

Lemma abst_disj_merge_set_eq:
  forall x y id (O: OSAbstMod.listset) Of,
    disjoint O Of ->
    get O id = Some x ->
    isRw x = true ->
    merge (set O id y) Of = set (merge O Of) id y.
Proof.
  intros.
  unfold disjoint in H.
  destruct H.
  eapply  join_merge_set_eq; eauto.
Qed.

Lemma abst_disj_merge_set_eq':
  forall x y y' x' id id' (O: OSAbstMod.listset) Of,
    disjoint O Of ->
    get O id = Some x ->
    get O id' = Some x' ->
    merge (set (set O id y) id' y') Of =set (set (merge O Of) id y) id' y'.
Proof.
  intros.
  unfolds in H.
  destruct H.
  assert (merge (set (set O id y) id' y') Of = set (merge (set O id y) Of) id' y').
  assert (id = id' \/ id <> id') by tauto.
  destruct H2.
  eapply  join_merge_set_eq; eauto.
  eapply  join_set_set; eauto.
  subst.
  eapply get_set_eq ; eauto.
  eapply  join_merge_set_eq; eauto.
  eapply  join_set_set; eauto.
  eapply get_set_neq ; eauto.
  rewrite H2.
  assert (merge (set O id y) Of = set (merge O Of) id y).
  eapply abst_disj_merge_set_eq;eauto.
  unfolds.
  eauto.
  rewrite H3.
  auto.
Qed.

Lemma abst_set_get_neq'':
  forall id1 id2 y (O: OSAbstMod.listset),
    id1<>id2 ->
    get (set O id2 y) id1 = get O id1.
Proof.
  intros.
  erewrite get_set_neq; eauto.
Qed.



Lemma abs_join_sig_set_join: 
  forall a b (O O1 : OSAbstMod.map) id, 
    join (sig id a) O1 O -> join (sig id b) O1 (set O id b).
Proof.
  intros.
  eapply  join_sig_set; eauto.
Qed.


Ltac find_absdata' Hp id :=
  match Hp with
    | ?A ** ?B =>
      match find_absdata' A id with
        | some ?a => constr:(some a)
        | none ?a =>
          match find_absdata' B id with
            | some ?b => constr:(some (a + b)%nat)
            | none ?b => constr:(none (a + b)%nat)
          end
      end
    | Aabsdata id _  => constr:(some 1%nat)
    | _ => constr:(none 1%nat)
  end.

Ltac find_absdata Hp id :=
  let x := find_absdata' Hp id in
  eval compute in x.



Lemma get_none_joinisig:
  forall (qls:EcbMod.map)  qid x, 
    get qls qid = None ->
    joinsig qid x qls (set qls qid x).
Proof.
  intros.
  unfolds.
  eapply get_join_sig_set; eauto.
Qed.





Lemma joinisig_get_none:
  forall (qls :EcbMod.map)  qls' qid x, 
    joinsig qid x qls qls' -> 
    get qls qid = None /\ qls'= (set qls qid x).
Proof.
  intros.
  split.
  apply join_sig_get_disj in H.
  simp join.
  auto.
  unfolds; simpl; auto.
  apply get_join_sig_set_rev; auto.
Qed.


Ltac absdata_solver :=
  match goal with
    | H : (_,?O,_) |= ?P |- get (merge ?O _) ?id = Some _ =>
      match find_absdata P id with
        | none _ => fail 1
        | some ?n =>
          sep lift n in H; eapply absdata_elim' in H; eauto with abst_solver_base
      end
    | H : (_,?O,_) |= ?P |- get ?O ?id = Some _ =>
      match find_absdata P id with
        | none _ => fail 1
        | some ?n =>
          sep lift n in H; eapply absdata_elim in H; eauto with abst_solver_base
      end
    | |- merge (set (set _ _ _) _ _) _ = 
         set ( set (merge _ _) _ _) _ _    =>
      eapply  abst_disj_merge_set_eq';first [absdata_solver | eauto ]
    | |- merge (set _ _ _ ) _ = set (merge _ _) _ _ =>
      eapply abst_disj_merge_set_eq;first [absdata_solver | eauto ]
    | |- get (set _ _ _) _ = Some _ => 
      try solve  [ eapply  get_set_eq; auto 
                 | erewrite abst_set_get_neq'';[ absdata_solver | auto ;try (intro; tryfalse)]]
    | |- _ _ _ _ _ => try solve [eapply get_none_joinisig;eauto]
  end.


Import DeprecatedTactic.

Lemma cancel_absdata_p:
  forall s O gamma gamma' P Q id a b,
    (forall O', (s, O', gamma) |= P -> (s, O', gamma') |= Q) ->
    ((s, O, gamma) |= Aabsdata id a ** P -> (s, set O id b, gamma') |= Aabsdata id b ** Q).
Proof.
  intros.
  simpl in *;mytac.
  exists empmem.
  destruct s as [[[[]]]].
  simpl in H5.
  simpl in H6.
  subst x;simpl in H1.
  exists m m.
  exists (sig id b) x3 (set O id b).
  simpl;mytac.
  eapply abs_join_sig_set_join; eauto.
  auto.
Qed.


Lemma cancel_absdata_p':
  forall s O gamma P id a b,
    (s, O, gamma) |= Aabsdata id a ** P -> (s, set O id b, gamma) |= Aabsdata id b ** P.
Proof.
  introv Hx.
  intros.
  simpl in *;mytac.
  exists empmem.
  destruct s as [[[[]]]].
  simpl in H5.
  simpl in H4.
  subst x;simpl in H0.
  exists m m.
  exists (sig id b) x3 (set O id b).
  simpl;mytac.
  eapply abs_join_sig_set_join; eauto.
  auto.
Qed.


Ltac get_absdata_number' P id :=
  match P with
    | ?A ** ?B => match get_absdata_number' A id with
                    | (some ?m) => constr:(some m)
                    | (none ?m) => match get_absdata_number' B id with
                                     | (some ?n) => constr:(some (m + n)%nat)
                                     | (none ?n) => constr:(none (m + n)%nat)
                                   end
                  end
    | Aabsdata id _ => constr:(some 1%nat)
    | _ => constr:(none 1%nat)
  end.

Ltac get_absdata_number P id :=
  let y := get_absdata_number' P id in
  eval compute in y.

Ltac cancel_absdata :=
  match goal with
    | H: (?s,?O,_) |= ?P |- (?s,set ?O ?id _,_) |= ?Q => 
      match (get_absdata_number P id) with
        | some ?n => match (get_absdata_number Q id) with 
                     | some ?m => 
                       sep lift n in H; sep lift m;
                       generalize dependent H; eapply cancel_absdata_p; intros
                     | _ => idtac
                   end
        | _ => idtac
      end
  end.

Ltac cancel_absdata' :=
  match goal with
    | |- (?s,set ?O ?id _,_) |= ?P => 
      match (get_absdata_number P id) with
        | some ?n => sep lift n; eapply cancel_absdata_p'; cancel_absdata'
        | _ => idtac
      end
    | _ =>idtac
  end.

(*


Ltac ins_aop :=
  match goal with
    | H: (_, ?O, ?aop) |= _ |- _ |= <|| ?aop' ||> ** _ =>
      instantiate (1:=aop')
  end.


Ltac ins_abst' P O tm:=
  match P with
    | ?P1 ** ?P2 => match (ins_abst' P2 O tm) with
                      | ?O' => ins_abst' P1 O' tm
                    end
    | HECBList (EcbMod.set ?ecbls ?x ?b) => 
      constr:(OSAbstMod.set O absecblsid (absecblist (EcbMod.set ecbls x b)))
    | HTCBList (TcbMod.set ?tcbls ?x ?b) => 
      constr:(OSAbstMod.set O abstcblsid (abstcblist (TcbMod.set tcbls x b)))
    | HTime tm => constr:(O)
    | HTime ?tm' => constr:(OSAbstMod.set O ostmid (ostm tm'))
    | _ => constr:(O)
  end.

Ltac ins_abst:=
  match goal with 
    | H: (_,?O,_) |= HECBList _ ** HTCBList _ ** HTime ?tm ** HCurTCB _ ** _ |- _|= ?P =>
      match ins_abst' P O tm with
        | ?O' => instantiate (1:=O')
      end
  end.
Ltac exists_O_aop:=
  do 2 eexists;splits;[ ins_aop;ins_abst | | ].

Definition absimp'':= fun p p' : asrt =>
forall (s : taskst) (O : osabst) (gamma : absop),
(s, O, gamma) |= p ->
forall Of : OSAbstMod.map,
OSAbstMod.disj O Of ->
exists O' gamma',
(s, O', gamma') |= p'/\
OSAbstMod.disj O' Of /\
hmstepstar gamma (OSAbstMod.merge O Of) gamma' (OSAbstMod.merge O' Of) .

Lemma absimp'_imp_absimp:
 forall P P',absimp' P P' -> absimp' P P'.
  intros.
  unfold absimp,absimp' in *.
  intros.
  lets Hx: H H0 H1.
  mytac;do 2 eexists;splits;eauto.
Qed.



Ltac disj_solver:=
    match goal with 
      | |- OSAbstMod.disj (OSAbstMod.set _ _ _) _ => 
        eapply abst_get_set_disj;[ auto;absdata_solver | disj_solver;auto ]
      | _ => auto
    end.

(*
Ltac eqdomO_solver :=
  match goal with
    | |- eqdomO _ _ => first [ eapply eqdomO_same | eapply set_eqdom'; [disj_solver | absdata_solver | eqdomO_solver]]
  end. *)

Lemma hmstepS_One:  
  forall a b c d,
    hmstep a b c d->
    hmstepstar a b c d.
Proof.
  intros.
  eapply spec_stepS;
   [
      eauto  | eapply spec_stepO].
Qed.


*)
