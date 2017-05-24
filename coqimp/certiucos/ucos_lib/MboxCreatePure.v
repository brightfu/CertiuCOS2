Require Import ucos_include.

Require Import OSQCreatePure.
Local Open Scope code_scope.

(*Require Import Mbox_absop.*)
Require Import Mbox_common.

Local Open Scope int_scope.
Local Open Scope Z_scope.
(* Lemma absimp_mbox_create_err_return :
 *   forall P i, 
 *     can_change_aop P ->
 *     isptr i ->
 *     absinfer ( <|| mbox_create  ( i :: nil) ||> ** P) ( <|| END (Some Vnull) ||> ** P).
 * Proof.
 *   infer_solver 0%nat.
 * 
 * Qed.
 * 
 * 
 * Lemma absimp_mbox_create_succ_return :
 *   forall P i qid  qls  tcbls curtid tm,
 *     can_change_aop P ->
 *     isptr i ->
 *     EcbMod.get qls qid = None  ->
 *     absinfer ( <|| mbox_create ( i :: nil) ||>
 *                  **HECBList qls **   HTCBList tcbls ** HTime tm **  HCurTCB curtid ** P)
 *            ( <|| END (Some (Vptr qid)) ||> **                                                                                                                 
 *                  HECBList (EcbMod.set qls qid (absmbox i,
 *                                                nil:list tid)) **HTCBList tcbls **  HTime tm **
 *                  HCurTCB curtid **P).
 * Proof.
 *   infer_solver 1%nat.
 * Qed. *)
(*
Lemma good_mboxcreate : Gooda mboxcre.
  unfold Gooda.
  intros.
  unfold mboxcre in *.
  destruct H0; intros.
   unfolds in H0.
  mytac.
  left.
   unfolds.
  exists x.
  splits; auto.
  auto.
  
  unfolds in H0.
  mytac.
  right.
  unfolds.
  exists x; splits; auto.
  exists x0 x1 x2.
  splits; auto.
  eapply OSAbstMod.join_get_get_r; eauto.
  apply OSAbstMod.join_merge_disj; auto.  
  eapply  abst_disj_merge_set_eqq; eauto.
  eapply OSAbstMod.disj_sym; auto.
  eapply OSAbstMod.disj_sym.
  eapply abst_get_set_disj; eauto.
  eapply OSAbstMod.disj_sym; auto.
Qed.
*)
(* Lemma intlemma1 :forall v'19 v'21,  id_addrval' (Vptr (v'21, Int.zero)) OSEventTbl OS_EVENT = Some v'19 -> (v'21, Int.zero+ᵢ($ 4+ᵢ($ 2+ᵢ($ 1+ᵢ($ 1+ᵢInt.zero))))) = v'19.
 *   intros.
 *   unfold id_addrval' in *.
 *   unfold id_addrval in *.
 *   simpl in H.
 *   inversion H.
 *   auto.
 * Qed. *)

Lemma ECBList_MBox_Create_prop :
  forall v'41 v'50 v'22 v'28 v'40
          v'37 v'38 v'27 x,
    RH_TCBList_ECBList_P v'37 v'38 v'40 ->
    EcbMod.get v'37 (v'41, Int.zero) = None ->
    ECBList_P v'22 Vnull v'28 v'27 v'37 v'38->
    ECBList_P (Vptr (v'41, Int.zero)) Vnull
              
              ((Vint32 (Int.repr OS_EVENT_TYPE_MBOX ):: Vint32 Int.zero :: Vint32 (Int.repr 0) :: x :: v'50 :: v'22 :: nil, INIT_EVENT_TBL) :: v'28)
              (DMbox x :: v'27)
              (EcbMod.set v'37 (v'41, Int.zero) (absmbox x, nil))
              v'38.
  intros.
  unfolds.
  fold ECBList_P.
  eexists.
  split; eauto.
  split.
  unfolds.
  split.
  unfolds.
  destruct H as (Ha1 & Ha2 & Ha3 & Ha4).
  splits;
  unfolds;
  intros;
  try solve [usimpl H2].
  unfolds in H.
  simpljoin.
  simpl in H5.
  lets Hres : prio_prop  H H7; eauto.

  assert (nat_of_Z (Int.unsigned (Int.shru ($ prio) ($ 3))) < 8)%nat.
  eapply Z_le_nat; eauto.
  split; auto.
  apply Int.unsigned_range_2.
  remember (nat_of_Z (Int.unsigned (Int.shru ($ prio) ($ 3)))) as  Heq.
  assert (x2=Int.zero) by (eapply nat8_des;eauto).
  subst x2.
  apply int_land_zero in H6; tryfalse.

  destruct H as (Ha1 & Ha2 & Ha3 & Ha4).
  split.
  unfolds.
  splits.
  unfolds.
  intros.
  destruct Ha1 as (Hab & Hac).
  lets Hre : Hac H.
  destruct Hre as (xx & yy & wt & Hec & Hin).
  unfold get in *; simpl in *.
  tryfalse.
  unfolds.
  intros.
  destruct Ha2 as (Hab & Hac).
  lets Hre : Hac H.
  destruct Hre as (xx  & wt & Hec & Hin).
  unfold get in *; simpl in *.
  tryfalse.
   unfolds.
  intros.
  destruct Ha3 as (Hab & Hac).
  lets Hre : Hac H.
  destruct Hre as (xx  & wt & Hec & Hin).
  unfold get in *; simpl in *.
  tryfalse.
  unfolds.
  intros.
  destruct Ha4 as (Hab & Hac).
  destruct Hac as (Hac & Hac').
  lets Hre : Hac H.
  destruct Hre as (xx  & wt & Hec & Hin & Hd).
  unfold get in *; simpl in *.
  tryfalse.
  unfolds.
  branch 3.
  simpl;auto.
  do 3 eexists.
  unfold V_OSEventListPtr.
  simpl nth_val .
  splits; eauto.
  instantiate (1:= (absmbox x, nil)).
  eapply ecbmod_get_sig_set; eauto.
  unfolds.
  splits.
  auto.
  unfolds.
  splits.
  auto.
  intro.
  tryfalse.
Qed.

Lemma MBox_Create_TCB_prop :
  forall v'37  x  i v'38 v'40 ,
    EcbMod.get v'37 x = None ->
    RH_TCBList_ECBList_P v'37 v'38 v'40 ->
    RH_TCBList_ECBList_P
      (EcbMod.set v'37 x (absmbox i, nil))
      v'38 v'40.
  intros.
  unfolds.
  unfolds in H0.
  destruct H0 as (Ha1 & Ha2 & Ha3 & Ha4).
  split.

  destruct Ha1.
  unfolds.
  split.
  intros.
  rewrite EcbMod.set_sem in H2.
  destruct (tidspec.beq x eid).
  destruct H2.
  inverts H2.
  lets Hres : H0 H2.
  eauto.
  intros.
  lets Hres : H1 H2.
  simpljoin.
  assert (eid = x \/ eid <> x) by tauto.
  destruct H5.
  subst.
  unfold get in *; simpl in *.
  tryfalse.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  eapply H1; eauto.

  split.

  destruct Ha2.
  unfolds.
  split.
  intros.
  rewrite EcbMod.set_sem in H2.
  destruct (tidspec.beq x eid).
  destruct H2.
  inverts H2.
  lets Hres : H0 H2.
  eauto.
  intros.
  lets Hres : H1 H2.
  simpljoin.
  assert (eid = x \/ eid <> x) by tauto.
  destruct H5.
  subst.
  unfold get in *; simpl in *.

  tryfalse.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  eapply H1; eauto.

  split.
  intros.
  destruct Ha3.
  unfolds.
  split.
  intros.
  rewrite EcbMod.set_sem in H2.
  destruct (tidspec.beq x eid).
  destruct H2.
  inverts H2.
  simpl in H3; tryfalse.
  eapply H0; eauto.
  intros.
  rewrite EcbMod.set_sem.
  lets Hres : H1 H2.
  destruct Hres as (x1&qw& Hec & Hin).
  remember (tidspec.beq x eid) as Hbool.
  destruct Hbool.
  apply eq_sym in HeqHbool.
  apply tidspec.beq_true_eq in HeqHbool.
  subst x.
  unfold get in *; simpl in *.
  tryfalse.
  do 2 eexists; splits; eauto.

  destruct Ha4.
  unfolds.
  split.
  intros.
  rewrite EcbMod.set_sem in H2.
  destruct (tidspec.beq x eid).
  destruct H2.
  inverts H2.
  lets Hres : H0 H2.
  eauto.
  destruct H1 as (H1 & H1').
  split.
  intros.

  lets Hres : H1 H2.

  simpljoin.
  assert (eid = x \/ eid <> x) by tauto.
  destruct H5.
  subst.
  unfold get in *; simpl in *.
  tryfalse.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  eapply H1; eauto.



  apply Mutex_owner_set.
  intro.
  simpljoin; tryfalse.
  auto.
Qed.
