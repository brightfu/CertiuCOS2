Require Import include_frm.
Require Import sep_auto.
Require Import cancel_abs.


Lemma eqdom_same:forall O, eqdomO  O O.
Proof.
  intros.
  eapply eqdomO_same;eauto.
Qed.

Lemma  eqtid_same : forall O, tidsame O O.
Proof.
  intros.
  unfolds.
  auto.
Qed.

Definition eqtls (i :absdataid) x y :=
  match i with
    | abstcblsid => match x,y with
                      | abstcblist tls, abstcblist tls' => eqdomtls tls tls'
                      | _ , _ => False
                    end
    | _ => True
  end.

Import DeprecatedTactic.

Lemma tls_get_set_indom:
  forall tcbls ct x y,
    get tcbls ct = Some x ->
    eqdomtls tcbls (set tcbls ct y).
Proof.
  intros.
  unfolds.
  intros;split;intros.
  unfold indom in *.
  mytac.
  assert (ct = tid \/ ct <> tid ) by tauto.
  destruct H1.
  subst ct.
  exists y.
  eapply get_set_eq.
  exists x0.
  eapply get_set_neq.
  auto.
  auto.
  unfold indom in *.
  mytac.
  assert (ct = tid \/ ct <> tid ) by tauto.
  destruct H1.
  subst ct.
  exists x;auto.
  erewrite get_set_neq in H0; eauto.
Qed.

Lemma abst_get_set_eqdom:
  forall O x y z,
    get O x  = Some y ->
    eqtls x y z ->
    eqdomO O (set O x z).
Proof.
  introv H Hx.
  intros.
  unfolds.
  split;intros.
  split;intros.
  unfolds in H0.
  mytac.
  unfolds.
  assert (x = x0 \/ x <> x0 ) by tauto.
  destruct H1.
  subst.
  exists z.
  eapply get_set_eq.
  exists x1.
  eapply get_set_neq.
  auto.
  auto.
  unfolds.
  assert (x = x0 \/ x <> x0 ) by tauto.
  destruct H1.
  subst.
  exists y.
  auto.
  unfold indom in H0.
  destruct H0.
  erewrite get_set_neq in H0; eauto.
  assert ( x= abstcblsid \/ x <> abstcblsid) by tauto.
  destruct H1.
  subst x.
  simpl in Hx.
  destruct y;tryfalse.
  destruct z;tryfalse.
  rewrite H0 in H;inverts H.
  exists m0.
  split;auto.
  eapply get_set_eq.
  exists tls.
  split.
  eapply get_set_neq; eauto.
  unfolds.
  intros.
  split;intros; auto.
Qed.

Lemma tidsame_set:
  forall O  x y,
    x <>  curtid ->
    tidsame O (set O x y).
Proof.
  intros.
  unfolds.
  erewrite get_set_neq; eauto.
Qed.

Lemma specstep_merge_emp:
  forall r O r' O' sc, 
    spec_step r sc (merge O empabst) r' (merge O' empabst) ->
    spec_step r sc O r' O'.
Proof.
  intros.
  do 2  rewrite jl_merge_emp in H.
  auto.
Qed.

Lemma hmstep_merge_emp:
  forall r O r' O' sc, 
    hmstep r sc (merge O empabst) r' (merge O' empabst) ->
    hmstep r sc O r' O'.
Proof.
  eapply specstep_merge_emp.
Qed .



Hint Resolve eqdom_same  eqtid_same  disjoint_emp_r disjoint_emp_l.
(* some absinfer rules and tactics *)

(*Ltac can_change_aop_solver := idtac.*)


Lemma absinfer_conseq_pre :
  forall p' p q sc,
    sc  ⊢ p ⇒ q -> p' ==> p -> sc  ⊢ p' ⇒ q .
Proof.
  intros.
  eapply absinfer_conseq; eauto.
Qed.

Lemma absinfer_tri_choice2:
  forall (p : asrt) (s1 s2 : spec_code) sc,
    assertion.can_change_aop p ->
    sc ⊢  <|| s1 ?? s2 ||>  ** p ⇒  <|| s2 ||>  ** p.
Proof.
  intros.
  eapply absinfer_choice2; auto.
Qed.

Lemma absinfer_tri_choice1:
  forall (p : asrt) (s1 s2 : spec_code) sc,
    assertion.can_change_aop p ->
    sc ⊢ <|| s1 ?? s2 ||>  ** p ⇒  <|| s1 ||>  ** p.
Proof.
  intros.
  eapply absinfer_choice1; auto.
Qed.

Ltac infer_branchl := eapply absinfer_trans;[ eapply absinfer_tri_choice1; can_change_aop_solver| idtac].
Ltac infer_branchr := eapply absinfer_trans;[ eapply absinfer_tri_choice2; can_change_aop_solver| idtac].

Ltac infer_branch_first :=
  match goal with 
    | [ |- context [ <|| _ ?? _ ||> ] ] => infer_branchl
    | _ => idtac
  end.

Ltac infer_branch n := match n with 
                         | O => infer_branch_first
                         | S ?n' => infer_branchr; infer_branch n'
                       end.

Ltac exgamma :=
  match goal with
    | [ |- context [ <|| ?aa ||> ]] => eexists aa
  end.

Ltac add_END_if_ness :=
  match goal with
    | [ |-  _ ⊢ <|| _ (| _ |) ||>  ** _
              ⇒  <|| END _ ||>  ** _] => idtac
    | [ |-  _  ⊢ <|| _ ;; _ ||> ** _ 
               ⇒  <|| END _ ;; _ ||>  ** _ ] => idtac
    | [ |-  _  ⊢ <|| _ ;; _ ||> ** _ 
               ⇒  <|| _ ||>  ** _ ] => eapply absinfer_trans; [idtac|  eapply absinfer_seq_end;[ .. | sep auto];can_change_aop_solver] 
  end.

Ltac multi_step_handler :=
  match goal with
    | [ |-  _ ⊢ <|| _ (| _ |) ||>  ** _
              ⇒  <|| END _ ||>  ** _] =>
      idtac
    | [ |-  _  ⊢ <|| _ ;; _ ||> ** _ 
               ⇒  <|| _ ||>  ** _ ] =>
      eapply absinfer_seq; [can_change_aop_solver..| idtac]
  end.

Ltac tri_infer_prim:= eapply absinfer_prim; [can_change_aop_solver.. | idtac];  unfolds;  intros.

(* Ltac tri_api_mstep:= idtac. *)
(*        eapply api_mstep;[try absdata_solver .. | (* TODO *) idtac | idtac | idtac]. *)

Ltac simpl_subst_gamma :=
  match goal with 
    | [ H : ( _, _, _) |= <|| _ ||> ** _ |- _] => sep split in H
  end;
  match goal with 
    | [ H : getabsop (_, _, ?gamma) = _  |- _] => simpl in H; subst gamma
  end.

Lemma tidsame_trans : forall o o1 o2, tidsame o o1 -> tidsame o1 o2 -> tidsame o o2.
Proof.
  intros.
  unfold tidsame in *.
  rewrite H.
  auto.
Qed.

Lemma eqdomtls_same : forall x , eqdomtls x x .
  intros.
  unfolds.
  intro.
  tauto.
Qed.

Ltac multi_rec_solver1 base_lemma trans_lemma onestep_tac :=
  first [ apply base_lemma
        | eapply trans_lemma;
                 [.. | onestep_tac]
        ].

Ltac tmp := eapply tls_get_set_indom; eauto.

Ltac eqdomtls_solver1 := multi_rec_solver1 eqdomtls_same eqdomtls_trans tmp.
  (* first [ apply eqdomtls_same
   *       | eapply eqdomtls_trans;
   *         [..| eapply tls_get_set_indom; eauto]
   *       ]. *)

Ltac eqdomtls_solver :=
  try solve [unfolds; auto]; repeat eqdomtls_solver1.

Ltac eqdomO_solver1 :=
  first [ apply eqdom_same
        | eapply eqdomO_trans;
          [idtac| eapply abst_get_set_eqdom  ; [absdata_solver| eqdomtls_solver]]
        ].

Ltac eqdomO_solver := repeat eqdomO_solver1.

(*solve[
auto
|eapply abst_get_set_eqdom; [absdata_solver |  try solve [simpl;auto| simpl;eapply tls_get_set_indom;eauto]]
| eapply eqdomO_trans; eapply abst_get_set_eqdom;  [absdata_solver | try solve [simpl;auto| simpl;eapply tls_get_set_indom;eauto]]
                ].*)

Ltac tidsame_solver:=solve [auto |
                            eapply tidsame_set; auto; try (intro; tryfalse) |
                            eapply tidsame_trans; eapply tidsame_set; auto ;try (intro; tryfalse) ].

(* Ltac tri_spec_step:=
 *   eapply specstep_merge_emp;
 *   constructors; [idtac| eqdomO_solver| tidsame_solver| auto..]. *)

Ltac infer_part1 n:=
  try match goal with 
        | [ |- context[<|| ?x _ ||>] ] => unfold x
      end;
  intros;
  infer_branch n;
  add_END_if_ness;
  multi_step_handler.

Ltac tri_exists_and_solver :=match goal with
                               | |- exists _ , _ => eexists; tri_exists_and_solver
                               | |-_ /\ _ => splits; tri_exists_and_solver
                               | |-_ => solve [eauto| eauto; absdata_solver]
                             end.
Ltac tri_exists_and_solver1 :=match goal with
                                | |- exists _ , _ => eexists
                                | |-_ /\ _ => splits
                                | |-_ => solve [eauto| eauto; absdata_solver]
                              end.

Ltac absinfer_side_condition_solver :=
  match goal with
    | |- tidsame _ _ => tidsame_solver
    | |- eqdomO _ _ => eqdomO_solver
    | _ => idtac 
  end.

Ltac hmstep_call_consturctor :=
  match goal with
    | |- hmstepstar _ _ _ _ _ => constructors
    | |- hmstep _ _ _ _ _ => constructors
  end.

Ltac hmstep_solver' :=
  (* eapply specstep_merge_emp; *)
  repeat hmstep_call_consturctor;
  [idtac | idtac | idtac | apply map_join_emp | idtac..];
  [ unfolds; try tri_exists_and_solver| try absinfer_side_condition_solver..];
  try solve [repeat rewrite jl_merge_emp; try apply map_join_emp].

Ltac hmstep_solver :=
  simpl_subst_gamma;[idtac.. | hmstep_solver'].

(* constructors;[
 * unfolds;mytac;
 * try tri_exists_and_solver|eqdomO_solver|tidsame_solver|auto..]. *)

Ltac infer_part2_0 :=
  splits; [ hmstep_solver |idtac].

(* TODO *)
(* Ltac osabst_clever_rewrite := match goal with 
 *                                 | [ |- context[OSAbstMod.get (OSAbstMod.set _ ?x _ ) ?x] ]=>   erewrite (@OSAbstMod.set_a_get_a _ _ _ _ (@absdataidspec.eq_beq_true _ _ (@eq_refl _ curtid)))
 *                                 | [ |- context[OSAbstMod.get (OSAbstMod.set _ ?x _ ) ?y] ]=> erewrite OSAbstMod.set_a_get_a';[idtac| apply absdataidspec.neq_beq_false; clear;intro; tryfalse] *)
                              (* end. *)
Ltac simpl_absdata_sep :=
  match goal with
    | |- (?s, set ?O ?id _, _) |= ?P =>
      match get_absdata_number P id with
        | some ?n => sep lift n; eapply cancel_absdata_p'
        | _ => idtac
      end
  end.

(* Ltac tcblistdomsubeq_solver := idtac. *)
(*    match goal with
      | |- tcblistdomsubeq (TcbMod.set _ _ _ ) _ => eapply tcblistdomsubeq_set; eauto
      | |- tcblistdomsubeq _ (TcbMod.set _ _ _ ) => eapply tcblistdomsubeq_set'; eauto
      | |- tcblistdomsubeq _ _ => apply tcblistdomsubeq_true
    end.*)

Ltac infer_part2 :=
  tri_infer_prim; eexists;exgamma; first [infer_part2_0; repeat simpl_absdata_sep; sep auto  | idtac].

(* Ltac infer_part2':=
 *   match goal with 
 *     | [ H : ( _, ?O, _) |= <|| _ ||> ** _ |- _] =>
 *       exists O; exgamma; simpl in H
 *   end; mytac;[
 *     eapply hmstep_merge_emp;
 *     constructor;
 *     constructor; eauto;
 *     unfolds;
 *     try tri_exists_and_solver|
 *     simpl;
 *       do 6 eexists; splits; eauto;[ idtac| splits; eauto| eapply change_aop_rule; eauto| idtac..]; mytac]. *)

Ltac infer_solver n := infer_part1 n; infer_part2.

(*
                   match goal with
    | _ : (_, _, _) |= _ ** HECBList _ ** _ |- _ => infer_part2
    | _ : (_, _, _) |= _ ** HTCBList _ ** _ |- _ => infer_part2
    | _ : (_, _, _) |= _ ** HTime  _   ** _ |- _ => infer_part2
    | _ : (_, _, _) |= _ ** HCurTCB _  ** _ |- _ => infer_part2
    | _ => infer_part2
  end. 
 *)

(* Require Import include_frm.
 * Require Import os_inv.
 * Require Import abs_op.
 * Require Import sep_auto.
 * Require Import ucos_frmaop.
 * Require Import os_code_defs.
 * 
 * Local Open Scope int_scope.
 * Local Open Scope Z_scope.
 *  
 * Lemma absinfer_mutex_pend_lift_is_rdy_block:
 *   forall P mqls qid v wl p m t ct tls tid opr pr m' p' sch,
 *     ct <>tid ->
 *     Int.unsigned v <= 65535 ->
 *     can_change_aop P ->
 *     get mqls qid = Some (absmutexsem pr (Some (tid, p')), wl) ->
 *     get tls ct = Some (p, rdy, m) ->
 *     get tls tid = Some (opr, rdy, m') ->
 *     Int.eq opr pr = false ->
 *     Int.ltu p p' = true ->
 *     Int.ltu pr p = true ->
 *     absinfer sch
 *       ( <|| mutexpend (Vptr qid :: Vint32 v :: nil) ||>  ** 
 *            HECBList mqls **
 *            HTCBList tls **
 *            HTime t **
 *            HCurTCB ct ** P) 
 *       (<|| isched;;
 *            (mutexpend_to (|Vptr qid :: Vint32 v :: nil|) ??
 *             mutexpend_block_get (|Vptr qid :: Vint32 v :: nil|)) ||> **
 *            HECBList (set mqls qid (absmutexsem pr (Some (tid, p')), ct :: wl) ) **
 *            HTCBList (set (set tls ct (p,wait (os_stat_mutexsem qid) v, m)) tid (pr, rdy, m')) **
 *            HTime t **
 *            HCurTCB ct ** P).
 * Proof.
 *   infer_part1 7%nat. 
 *   infer_solver 0%nat.
 *   SearchAbout get.
 * 
 *   (* intros.
 *    * unfold mutexpend.
 *    * eapply absinfer_trans.
 *    * apply absinfer_choice2.
 *    * simpl;splits;auto.
 *    * 2:intros;eauto.
 *    * simpl;splits;auto.
 *    * eapply absinfer_trans.
 *    * apply absinfer_choice2.
 *    * simpl;splits;auto.
 *    * 2:intros;eauto.
 *    * simpl;splits;auto.
 *    * eapply absinfer_trans.
 *    * apply absinfer_choice2.
 *    * simpl;splits;auto.
 *    * 2:intros;eauto.
 *    * simpl;splits;auto.
 *    * eapply absinfer_trans.
 *    * apply absinfer_choice2.
 *    * simpl;splits;auto.
 *    * 2:intros;eauto.
 *    * simpl;splits;auto.
 *    * eapply absinfer_trans.
 *    * apply absinfer_choice2.
 *    * simpl;splits;auto.
 *    * 2:intros;eauto.
 *    * simpl;splits;auto.
 *    * eapply absinfer_trans.
 *    * apply absinfer_choice2.
 *    * simpl;splits;auto.
 *    * 2:intros;eauto.
 *    * simpl;splits;auto.
 *    * eapply absinfer_trans.
 *    * apply absinfer_choice2.
 *    * simpl;splits;auto.
 *    * 2:intros;eauto.
 *    * simpl;splits;auto.
 *    * eapply absinfer_trans.
 *    * apply absinfer_choice1.
 *    * simpl;splits;auto.
 *    * 2:intros;eauto.
 *    * simpl;splits;auto.
 *    * eapply absinfer_trans.
 *    * 2:eapply absinfer_seq_end.
 *    * 4:intros;eauto.
 *    * 2:simpl;splits;auto.
 *    * 2:simpl;splits;auto.
 *    * eapply absinfer_seq.
 *    * simpl;splits;auto.
 *    * simpl;splits;auto.
 *    * subst.
 *    * eapply absinfer_trans.
 *    * apply absinfer_choice1.
 *    * simpl;splits;auto.
 *    * 2:intros;eauto.
 *    * simpl;splits;auto.
 *    * infer_solver 0%nat.
 *    * eapply abst_get_set_eqdom.
 *    * absdata_solver.
 *    * unfolds.
 *    * assert (eqdomtls (TcbMod.set tls ct (p, wait (os_stat_mutexsem qid) v, m)) (TcbMod.set (TcbMod.set tls ct (p, wait (os_stat_mutexsem qid) v, m))
 *    *       tid (pr, rdy, m'))).
 *    * eapply tls_get_set_indom; eauto.
 *    * 
 *    * rewrite TcbMod.set_a_get_a';eauto.
 *    * eapply tidspec.neq_beq_false;eauto.
 *    * unfolds.
 *    * unfolds in H9.
 *    * intros.
 *    * split;intros.
 *    * apply H9.
 *    * unfolds in H10.
 *    * mytac.
 *    * assert (tid0 = ct \/ tid0 <> ct) by tauto.
 *    * destruct H11.
 *    * subst tid0.
 *    * eexists.
 *    * rewrite TcbMod.set_a_get_a;eauto.
 *    * eapply tidspec.eq_beq_true;eauto.
 *    * eexists.
 *    * rewrite TcbMod.set_a_get_a';eauto.
 *    * eapply tidspec.neq_beq_false;eauto.
 *    * apply H9 in H10.
 *    * unfolds in H10.
 *    * mytac.
 *    * assert (tid0 = ct \/ tid0 <> ct) by tauto.
 *    * destruct H11.
 *    * subst tid0.
 *    * eexists.
 *    * rewrite TcbMod.set_a_get_a in H10;eauto.
 *    * eapply tidspec.eq_beq_true;eauto.
 *    * eexists.
 *    * rewrite TcbMod.set_a_get_a' in H10;eauto.
 *    * eapply tidspec.neq_beq_false;eauto. *)
 * Qed. *)
