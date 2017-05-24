Require Import ucos_include.
Require Import os_ucos_h.
Require Import symbolic_lemmas.
Import DeprecatedTactic.

Open Scope code_scope.
Open Scope list_scope.
Open Scope Z_scope.

Fixpoint is_owner_evsllseg (ptcb:tid) (l:list os_inv.EventCtr):=
  match l with
  | nil => False
  | (vl,x) :: l' =>
    match V_OSEventPtr vl with
    | Some (Vptr a) =>
      match V_OSEventType vl with
      | Some t =>
        (a = ptcb /\ t = Vint32 (Int.repr OS_EVENT_TYPE_MUTEX)) \/ is_owner_evsllseg ptcb l'
      | _ => False
      end
    | Some Vnull =>  is_owner_evsllseg ptcb l'
    | _ => False
    end
  end.

Definition is_mutex_owner (e:os_inv.EventCtr) eaddr :=
  match e with
  | (ectrl, _) =>
    match V_OSEventPtr ectrl with
    | Some p =>
      match V_OSEventType ectrl with
      | Some t =>
        p = (Vptr eaddr) /\ t = Vint32 (Int.repr OS_EVENT_TYPE_MUTEX)
      | _ => False
      end
    | _ => False
    end
  end.

Lemma evsllseg_app':
  forall (head mid : val) (vl0 : list os_inv.EventCtr) (ecbl0 : list EventData)
         (tail : val) (vl1 : list os_inv.EventCtr) (ecbl1 : list EventData),
    evsllseg head mid vl0 ecbl0 ** evsllseg mid tail vl1 ecbl1 ==>
             evsllseg head tail (vl0 ++ vl1) (ecbl0 ++ ecbl1).
Proof.
  intros.
  lets Hx: evsllseg_app head mid vl0 ecbl0 tail.
  lets Hx1: Hx vl1 ecbl1 Aemp s.
  assert (s |= evsllseg head mid vl0 ecbl0 ** evsllseg mid tail vl1 ecbl1 ** Aemp).
  sep auto.
  apply Hx1 in H0.
  sep auto.
Qed.

Lemma is_owner_evsllseg_remove_last :
  forall vl ptr node tbl eptr etype,
    V_OSEventPtr node = Some eptr ->
    V_OSEventType node = Some etype ->
    eptr <> Vptr ptr \/ etype <> Vint32 (Int.repr OS_EVENT_TYPE_MUTEX) ->
    is_owner_evsllseg ptr (vl ++ (node, tbl) :: nil) ->
    is_owner_evsllseg ptr vl.
Proof.
  inductions vl; intros.
  rewrite app_nil_l in H2.
  simpl in H2.
  destruct (V_OSEventPtr node) eqn : eq1; tryfalse.
  destruct v; tryfalse.
  destruct (V_OSEventType node) eqn : eq2; tryfalse.
  destruct H2; tryfalse.
  simpljoin1.
  inverts H.
  destruct H1; tryfalse.

  rewrite <- app_comm_cons in H2.
  unfold1 is_owner_evsllseg in H2.
  destruct a.
  destruct (V_OSEventPtr v) eqn : eq1; tryfalse.
  destruct v1; tryfalse.
  simpl.
  rewrite eq1.
  lets Hx: IHvl H H0 H1 H2; auto.

  destruct (V_OSEventType v) eqn : eq2; tryfalse.
  destruct H2.
  simpl.
  rewrite eq1; rewrite eq2.
  auto.
  eapply IHvl in H2; eauto.
  simpl.
  rewrite eq1; rewrite eq2.
  auto.
Qed.

Lemma not_is_owner_evsllseg_app :
  forall vl ptr node tbl eptr etype,
    ~ is_owner_evsllseg ptr vl ->
    V_OSEventPtr node = Some eptr ->
    V_OSEventType node = Some etype ->
    eptr <> Vptr ptr \/ etype <> Vint32 (Int.repr OS_EVENT_TYPE_MUTEX) ->
    ~ is_owner_evsllseg ptr (vl ++ (node, tbl) :: nil).
Proof.
  intros.
  intro; apply H; clear H.
  eapply is_owner_evsllseg_remove_last; eauto.
Qed.

Lemma not_is_owner_evsllseg_not_is_some_mutex_owner :
  forall vlecb vledata ecbmap tcbmap optr head s P,
    ~ is_owner_evsllseg optr vlecb ->
    s |= evsllseg head Vnull vlecb vledata ** P ->
    ECBList_P head Vnull vlecb vledata ecbmap tcbmap ->
    (*      RH_TCBList_ECBList_P ecbmap tcbmap ct -> *)
    ~ is_some_mutex_owner optr ecbmap.
Proof.
  inductions vlecb; intros.
  simpl in H1; simpljoin1.
  unfolds; intros.
  unfolds in H1; simpljoin1.
  rewrite EcbMod.emp_sem in H1; tryfalse.

  destruct vledata.
  simpl in H1; simpljoin1; tryfalse.
  unfold1 ECBList_P in H1; destruct a; simpljoin1.
  unfolds in H2; simpljoin1.
  simpl in H7; unfolds in H7.
  unfold1 evsllseg in H0; sep normal in H0.
  destruct H0; sep split in H0.
  rewrite H3 in H8; inverts H8.
  sep lift 2%nat in H0.
  unfold AEventNode in H0.
  unfold AEventData in H0.
  unfold AOSEvent in H0.
  unfold node in H0.
  sep normal in H0.
  sep destruct H0.
  sep split in H0; simpljoin1.
  inverts H8.
  lets Hx: struct_type_vallist_match_os_event H12; simpljoin1.
  simpl in H12; simpljoin1.
  clear H8 H12 H13 H15.
  sep lift 3%nat in H0.

  destruct H7.
  destruct e;
    try solve [sep split in H0; rewrite H7 in H8; tryfalse].
  sep split in H0.
  unfold1 is_owner_evsllseg in H.
  rewrite H8 in H.
  rewrite H12 in H.
  unfolds in H8; simpl in H8; inverts H8.
  assert (~ is_owner_evsllseg optr vlecb).
  clear - H H14.
  destruct v; tryfalse; auto.
  lets Hx: IHvlecb H8 H0 H6.
  simpl in H5; destruct x0; destruct e; tryfalse.
  clear - H4 Hx.
  intro; apply Hx.
  unfold is_some_mutex_owner in H; simpljoin1.
  unfolds.
  assert ((x5, Int.zero) = x \/ (x5, Int.zero) <> x) by tauto.
  destruct H0.
  substs.
  unfolds in H4.
  eapply join_get_l in H4; eauto.
  2: eapply get_sig_some.
  unfolds in H4; simpl in H4.
  rewrite H in H4; tryfalse.
  unfolds in H4.
  assert (get x1 x = Some (absmutexsem x0 (Some (optr, x2)), x3)).
  eapply perm_map_lemmas_part4.join_sig_get_r; eauto.
  eauto.

  destruct H7.
  destruct e;
    try solve [sep split in H0; rewrite H7 in H8; tryfalse].
  sep split in H0.
  rewrite H7 in H12; tryfalse.
  
  sep split in H0.
  unfold1 is_owner_evsllseg in H.
  rewrite H8 in H.
  unfold V_OSEventPtr in H; simpl nth_val in H.
  unfolds in H8; simpl in H8; inverts H8.
  assert (~ is_owner_evsllseg optr vlecb).
  clear - H H14.
  destruct x8; tryfalse; auto.
  lets Hx: IHvlecb H8 H0 H6.
  simpl in H5; destruct x0; destruct e; tryfalse.
  clear - H4 Hx.
  intro; apply Hx.
  unfold is_some_mutex_owner in H; simpljoin1.
  unfolds.
  assert ((x5, Int.zero) = x \/ (x5, Int.zero) <> x) by tauto.
  destruct H0.
  substs.
  unfolds in H4.
  eapply join_get_l in H4; eauto.
  2: eapply get_sig_some.
  unfolds in H4; simpl in H4.
  rewrite H in H4; tryfalse.
  unfolds in H4.
  assert (get x1 x = Some (absmutexsem x0 (Some (optr, x2)), x3)).
  eapply perm_map_lemmas_part4.join_sig_get_r; eauto.
  eauto.

  destruct H7.
  destruct e;
    try solve [sep split in H0; rewrite H7 in H8; tryfalse].
  sep split in H0.
  rewrite H7 in H12; tryfalse.
  sep split in H0.
  unfold1 is_owner_evsllseg in H.
  rewrite H8 in H.
  rewrite H12 in H.
  unfolds in H12; simpl in H12; inverts H12.
  assert (~ is_owner_evsllseg optr vlecb).
  clear - H H14.
  destruct m; tryfalse; auto.
  lets Hx: IHvlecb H12 H0 H6.
  simpl in H5; destruct x0; destruct e; tryfalse.
  clear - H4 Hx.
  intro; apply Hx.
  unfold is_some_mutex_owner in H; simpljoin1.
  unfolds.
  assert ((x5, Int.zero) = x \/ (x5, Int.zero) <> x) by tauto.
  destruct H0.
  substs.
  unfolds in H4.
  eapply join_get_l in H4; eauto.
  2: eapply get_sig_some.
  unfolds in H4; simpl in H4.
  rewrite H in H4; tryfalse.
  unfolds in H4.
  assert (get x1 x = Some (absmutexsem x0 (Some (optr, x2)), x3)).
  eapply perm_map_lemmas_part4.join_sig_get_r; eauto.
  eauto.

  (* mutex case *)
  destruct e;
    try solve [sep split in H0; rewrite H7 in H8; tryfalse].
  sep split in H0.
  rewrite H7 in H12; tryfalse.
  sep split in H0.

  unfolds in H13; simpl in H13; inverts H13.
  destruct v1; tryfalse.
  (* no owner *)
  simpl in H5.
  destruct x0.
  destruct e; tryfalse.
  destruct H5.
  unfolds in H5; simpljoin1.
  assert (Int.and x0 (Int.repr OS_MUTEX_KEEP_LOWER_8) = Int.repr OS_MUTEX_AVAILABLE \/ Int.and x0 (Int.repr OS_MUTEX_KEEP_LOWER_8) <> Int.repr OS_MUTEX_AVAILABLE) by tauto.
  destruct H5; substs.
  apply H18 in H5; simpljoin1.
  unfolds in H7; simpl in H7; inverts H7.
  assert (~ is_owner_evsllseg optr vlecb).
  clear - H.
  unfold1 is_owner_evsllseg in H.
  unfold V_OSEventPtr in H; simpl in H; auto.
  lets Hx: IHvlecb H5 H0 H6.
  clear - H4 Hx.
  intro; apply Hx.
  unfold is_some_mutex_owner in H; simpljoin1.
  unfolds.
  assert ((x5, Int.zero) = x \/ (x5, Int.zero) <> x) by tauto.
  destruct H0.
  substs.
  unfolds in H4.
  eapply join_get_l in H4; eauto.
  2: eapply get_sig_some.
  unfolds in H4; simpl in H4.
  rewrite H in H4; tryfalse.
  unfolds in H4.
  assert (get x1 x = Some (absmutexsem x2 (Some (optr, x3)), x4)).
  eapply perm_map_lemmas_part4.join_sig_get_r; eauto.
  eauto.
  apply H19 in H5.
  simpljoin1; tryfalse.

  (*has owner*)
  simpl in H5; destruct x0.
  destruct e; tryfalse; simpljoin1.
  unfolds in H5.
  simpljoin1.
  assert (Int.and x0 (Int.repr OS_MUTEX_KEEP_LOWER_8) = Int.repr OS_MUTEX_AVAILABLE \/ Int.and x0 (Int.repr OS_MUTEX_KEEP_LOWER_8) <> Int.repr OS_MUTEX_AVAILABLE) by tauto.
  destruct H5.
  apply H17 in H5; simpljoin1; tryfalse.
  apply H18 in H5; simpljoin1.
  inverts H5.
  unfolds in H7; simpl in H7; inverts H7.
  unfold1 is_owner_evsllseg in H.
  unfold V_OSEventPtr in H; simpl in H.
  eapply Classical_Prop.not_or_and in H; simpljoin1.
  assert (x8 <> optr).
  clear - H.
  eapply Classical_Prop.not_and_or in H.
  destruct H; auto.
  lets Hx: IHvlecb H5 H0 H6.
  clear - H4 Hx H7.
  intro; apply Hx.
  unfold is_some_mutex_owner in H; simpljoin1.
  unfolds.
  assert ((x5, Int.zero) = x \/ (x5, Int.zero) <> x) by tauto.
  destruct H0.
  substs.
  unfolds in H4.
  eapply join_get_l in H4; eauto.
  2: eapply get_sig_some.
  unfolds in H4; simpl in H4.
  rewrite H in H4; tryfalse.
  unfolds in H4.
  assert (get x1 x = Some (absmutexsem x2 (Some (optr, x3)), x4)).
  eapply perm_map_lemmas_part4.join_sig_get_r; eauto.
  eauto.
Qed.

Lemma is_mutex_owner_is_some_mutex_owner :
  forall head vlecb vledata c d optr ecbmap1 ecbmap2 ecbmap tcbmap1 s P,
    is_mutex_owner c optr ->
    s |= evsllseg head Vnull (c::vlecb) (d::vledata) ** P ->
    ECBList_P head Vnull (c::vlecb) (d::vledata) ecbmap1 tcbmap1 ->
    EcbMod.join ecbmap1 ecbmap2 ecbmap ->
    is_some_mutex_owner optr ecbmap.
Proof.
  intros.
  unfold1 ECBList_P in H1.
  unfold1 evsllseg in H0.
  destruct c; simpljoin1.
  unfolds in H.
  destruct (V_OSEventPtr v) eqn : eq1; tryfalse.
  destruct (V_OSEventType v) eqn : eq2; tryfalse.
  simpljoin1.
  unfold AEventNode in H0.
  unfold AEventData in H0.
  destruct d;
    try solve [
          sep normal in H0; sep destruct H0; sep split in H0;
          rewrite eq2 in H1; tryfalse].
  sep normal in H0; sep destruct H0; sep split in H0;
    rewrite eq2 in H8; tryfalse.
  simpl in H6.
  destruct x0.
  destruct e; tryfalse; simpljoin1.
  unfolds in H; simpljoin1.
  sep normal in H0; sep destruct H0; sep split in H0.
  rewrite eq1 in H12; inverts H12.
  assert (Int.and x0 (Int.repr OS_MUTEX_KEEP_LOWER_8) = Int.repr OS_MUTEX_AVAILABLE \/ Int.and x0 (Int.repr OS_MUTEX_KEEP_LOWER_8) <> Int.repr OS_MUTEX_AVAILABLE) by tauto.
  destruct H12; substs.
  apply H10 in H12; simpljoin1; tryfalse.
  apply H11 in H12; simpljoin1.
  inverts H12.
  clear - H2 H5.
  unfolds.
  unfolds in H5.
  eapply EcbMod.join_get_l in H5.
  2: eapply EcbMod.get_sig_some.
  eapply EcbMod.join_get_l in H2; eauto.
Qed.

Lemma OSIsOwner_proof:
    forall  vl p r logicl ct, 
      Some p =
      BuildPreI os_internal OS_IsSomeMutexOwner
                  vl logicl OS_IsSomeMutexOwnerPre ct->
      Some r =
      BuildRetI os_internal OS_IsSomeMutexOwner vl logicl OS_IsSomeMutexOwnerPost ct->
      exists t d1 d2 s,
        os_internal OS_IsSomeMutexOwner = Some (t, d1, d2, s) /\
        {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init spec.
  (* code 
Int8u ·OS_IsSomeMutexOwner·(⌞ptcb @ OS_TCB∗⌟)··{
       ⌞p @ OS_EVENT∗; x @ Int8u⌟;
       p′ =ₑ OSEventList′;ₛ
       x′ =ₑ ′0;ₛ
       WHILE (p′ !=ₑ NULL &&ₑ x′ ==ₑ ′0) {
         IF (p′ → OSEventPtr !=ₑ ptcb′ ||ₑ p′ → OSEventType !=ₑ ′OS_EVENT_TYPE_MUTEX ){
             p′ =ₑ p′→OSEventListPtr
         }ELSE{
             x′ =ₑ ′1
         }
       };ₛ
       RETURN x′ 
}·.
  *)
  
  (* p ′ =ₑ OSEventList ′;ₛ *)
  hoare unfold.
  hoare forward.
  pauto.

  (* x ′ =ₑ ′ 0;ₛ *)
  hoare forward.

  (* WHILE(p ′ !=ₑ NULL &&ₑ x ′ ==ₑ ′ 0) *)
  hoare remember (1::2::3::5::nil)%nat pre.
  eapply backward_rule1 with
  (*loop invariant *)
  (p :=
     (
       (EX (lc1:list EventCtr) (lc2:list EventCtr)
           (ld1:list EventData) (ld2:list EventData) (tail1:val),
        <|| v'15 ||> **
            LV x @ Int8u |-> Vint32 (Int.repr 0) **
            LV p @ OS_EVENT ∗ |-> tail1 **
            [| isptr tail1 |] **
            [| v'2 = lc1 ++ lc2 /\ v'1 = ld1 ++ ld2 /\
               length lc1 = length ld1 /\ length lc2 = length ld2 |] **
            [| ~ is_owner_evsllseg v'13 lc1 |] **
            evsllseg v'16 tail1 lc1 ld1 **
            evsllseg tail1 Vnull lc2 ld2 ** H0)
         \\//
         (EX a l1 l2 ld1 ld2 e d,
          <|| v'15 ||> **
              LV x @ Int8u |-> Vint32 (Int.repr 1) **
              LV p @ OS_EVENT ∗ |-> Vptr a **
              [| v'2 = l1 ++ e::l2 /\ v'1 = ld1 ++ d::ld2 /\
                 length l1 = length ld1 /\ length l2 = length ld2 |] **
              evsllseg v'16 (Vptr a) l1 ld1 ** evsllseg (Vptr a) Vnull (e::l2) (d::ld2) **
              [| is_mutex_owner e v'13|] **
              H0)     
     )).

  intros.
  substs.
  left.
  sep auto.
  instantiate (4 := nil); instantiate (3 := nil).
  simpl evsllseg at 1.
  sep split; auto.
  sep auto.
  simpl;auto.
  splits; eauto.
  sep lift 4%nat in H3.
  eapply evsllseg_list_len_eq; eauto.

  (*apply the while rule*)
  eapply seq_rule.
  eapply while_rule.
  intros.
  destruct H3.
  symbolic_execution;
    try solve
        [clear - H6; destruct x3; unfolds in H6; simpl in H6; destruct H6; simpljoin1; tryfalse;
         try (destruct a); simpl; auto].
  symbolic_execution;
    destruct x; simpl; auto.
  
  (*loop body*)
  (*select the 1st case of loop inv*)
  eapply disj_conj_distrib_pre.
  hoare forward.
  (*2 cases, the 2nd subgoal is false according to the loop condition*)
  hoare normal pre.
  hoare_split_pure_all.
  eapply aconj_aistrue_rule; eauto.
  intros.
  symbolic_execution;
  try solve
      [clear - H6; destruct v'21; unfolds in H6; simpl in H6; destruct H6; simpljoin1; tryfalse;
       try (destruct a); simpl; auto];
  eauto.
  hoare_split_pure_all.
  (**)
  
  (*prove p(v'21) is not null*)
  assert (exists x, v'21 = Vptr x).
  clear - H8 H3; simpljoin1.
  destruct v'21; unfolds in H3; simpl in H3; destruct H3; simpljoin1; tryfalse.
  rewrite Int.eq_true in H; simpl in H.
  unfold Int.notbool in H.
  rewrite eq_one_zero in H.
  unfold Int.ltu in H.
  rewrite Int.unsigned_zero in H.
  simpl in H.
  tryfalse.
  eauto.
  destruct H9; subst v'21.

  (*split out the node p points to*)
  destruct v'18; destruct v'20;
    try solve [
          unfold evsllseg at 3;
          hoare_split_pure_all; simpljoin1; tryfalse].
  unfold1 evsllseg.
  destruct e.
  unfold AEventNode; unfold AOSEvent; unfold node.
  hoare_split_pure_all.
  destruct H9; inverts H9.
  lets H9: struct_type_vallist_match_os_event H14.
  do 6 destruct H9; subst v.
    
  (* IF(p ′ → OSEventPtr !=ₑ ptcb ′ ||ₑ p ′ → OSEventType !=ₑ ′ OS_EVENT_TYPE_MUTEX) *)
  hoare forward.
  clear - H14; simpl in H14; simpljoin1.
  destruct x2; tryfalse.
  destruct v'13; simpl; auto.
  destruct a, v'13; simpl.
  destruct (peq b b0); destruct (Int.eq i i0); simpl; auto.
  clear - H14; simpl in H14; simpljoin1.
  destruct x2; tryfalse.
  destruct v'13; simpl; auto.
  destruct a, v'13; simpl.
  destruct (peq b b0); destruct (Int.eq i i0); simpl; auto.
  clear - H14; simpl in H14; simpljoin1.
  destruct x; tryfalse.
  simpl; destruct (Int.eq i (Int.repr OS_EVENT_TYPE_MUTEX)); auto.
  clear - H14; simpl in H14; simpljoin1.
  destruct x; tryfalse.
  simpl; destruct (Int.eq i (Int.repr OS_EVENT_TYPE_MUTEX)); auto.
  clear - H14; simpl in H14; simpljoin1.
  destruct v'13, x, x2; tryfalse.
  simpl; destruct (Int.eq i0 (Int.repr OS_EVENT_TYPE_MUTEX)); auto.
  destruct a; simpl; destruct (peq b0 b); destruct (Int.eq i1 i); simpl;
    destruct (Int.eq i0 (Int.repr OS_EVENT_TYPE_MUTEX)); simpl; unfold Int.notbool;
      unfold Int.ltu; rewrite Int.unsigned_zero;
        try solve [  rewrite Int.eq_true; rewrite Int.unsigned_one; simpl; auto].
  rewrite eq_one_zero; rewrite Int.unsigned_zero; simpl; auto.
  hoare_split_pure_all.
  (**)

  (* p ′ =ₑ p ′ → OSEventListPtr *)
  hoare forward.

  (* os_code_defs.x ′ =ₑ ′ 1 *)
  hoare forward.

  (* (if_true \\// if_false) ==> loop_inv *)
  unfolds in H11; simpl in H11; inverts H11.
  unfolds in H13; simpl in H13; inverts H13.
  destruct H9.
  left.
  (* if_true ==> loop_inv_left_case *)
  exists (v'17 ++ ((x :: v'23 :: x1 :: x2 :: x3 :: v'21 :: nil), v0) :: nil) v'18.
  exists (v'19 ++ e0 :: nil) v'20 v'21.
  sep auto.

  eapply evsllseg_app'.
  sep cancel 4%nat 1%nat.
  unfold evsllseg.
  eexists.
  sep split; eauto.
  unfold AEventNode.
  unfold AOSEvent.
  unfold node.
  sep auto.
  eauto.
  unfolds; simpl; auto.
  clear - H7 H16 H14; simpljoin1.
  clear H0 H1.
  simpl in H14; simpljoin1.
  clear H1 H2 H4.
  assert (x2 <> Vptr v'13 \/ x <> (Vint32 (Int.repr OS_EVENT_TYPE_MUTEX))).
  destruct v'13.
  destruct x; tryfalse.
  destruct x2; tryfalse.
  left; auto.
  destruct a.
  simpl in H.
  destruct (peq b0 b) eqn : eq2.
  destruct (Int.eq i1 i) eqn : eq3.
  simpl in H.
  destruct (Int.eq i0 (Int.repr OS_EVENT_TYPE_MUTEX)) eqn : eq1.
  unfold Int.notbool in H; simpl in H.
  rewrite eq_one_zero in H.
  unfold Int.notbool in H; simpl in H.
  rewrite eq_one_zero in H.
  unfold Int.ltu in H; rewrite Int.unsigned_zero in H.
  simpl in H; tryfalse.
  right.
  intro; inverts H1.
  rewrite Int.eq_true in eq1; tryfalse.
  left.
  intro; inverts H1.
  rewrite Int.eq_true in eq3; tryfalse.
  left.
  intro; inverts H1; tryfalse.
  clear - H1 H7.

  eapply not_is_owner_evsllseg_app; eauto.
  unfolds; simpl; auto.
  unfolds; simpl; auto.
  splits; auto.
  rewrite <- list_cons_assoc; auto.
  rewrite <- list_cons_assoc; auto.
  clear - e2.
  do 2 rewrite app_length.
  rewrite e2.
  simpl; auto.
  sep lift 6%nat in H0.
  eapply evsllseg_head_isptr; eauto.

  (* if_false ==> loop_inv_right_case *)
  right.
  exists (v'24, Int.zero) v'17 v'18 v'19 v'20.
  exists (x :: v'23 :: x1 :: x2 :: x3 :: v'21 :: nil, v0) e0.
  sep auto; eauto.
  clear - H14 H17.
  simpl in H14; simpljoin1.
  clear H0 H1 H3.
  assert (x2 = (Vptr v'13) /\ x = (Vint32 (Int.repr OS_EVENT_TYPE_MUTEX))).
  destruct v'13.
  destruct x; tryfalse.
  destruct x2; tryfalse.
  simpl in H17.
  destruct (Int.eq i0 (Int.repr OS_EVENT_TYPE_MUTEX)).
  simpl in H17.
  unfold Int.notbool in H17.
  rewrite Int.eq_true in H17.
  rewrite eq_one_zero in H17.
  unfold Int.ltu in H17; rewrite Int.unsigned_zero in H17; rewrite Int.unsigned_one in H17; simpl in H17.
  destruct H17; tryfalse.
  simpl in H17.
  unfold Int.notbool in H17.
  rewrite Int.eq_true in H17.
  unfold Int.ltu in H17; rewrite Int.unsigned_zero in H17; rewrite Int.unsigned_one in H17; simpl in H17.
  destruct H17; tryfalse.
  destruct a.
  simpl in H17.
  destruct (peq b0 b) eqn : eq1;
  destruct (Int.eq i1 i) eqn : eq2;
  destruct (Int.eq i0 (Int.repr OS_EVENT_TYPE_MUTEX)) eqn : eq3;
  substs;
  try solve
      [
        simpl in H17; unfold Int.notbool in H17; try rewrite eq_one_zero in H17;
        rewrite Int.eq_true in H17; unfold Int.ltu in H17;
        rewrite Int.unsigned_zero in H17; try rewrite Int.unsigned_one in H17;
        simpl in H17; destruct H17; tryfalse
      ]. 
  pose proof Int.eq_spec i1 i.
  rewrite eq2 in H0.
  pose proof Int.eq_spec i0 (Int.repr OS_EVENT_TYPE_MUTEX).
  rewrite eq3 in H1.
  substs; auto.
  clear - H0; simpljoin1.
  unfolds; simpl; auto.

  (*the false case by while condition and loop inv*)
  hoare normal pre.
  hoare_split_pure_all.
  destruct v'17.
  eapply aconj_aistrue_rule; eauto.
  intros.
  symbolic_execution;
  try solve
      [clear - H6; destruct v'21; unfolds in H6; simpl in H6; destruct H6; simpljoin1; tryfalse;
       try (destruct a); simpl; auto];
  eauto.
  hoare_split_pure_all; simpljoin1.
  clear - H7.
  rewrite repr_one in H7.
  rewrite repr_zero in H7.
  rewrite eq_one_zero in H7.
  simpl in H7.
  unfold Int.notbool in H7; rewrite Int.eq_true in H7.
  unfold Int.ltu in H7; rewrite Int.unsigned_zero in H7; rewrite Int.unsigned_one in H7; simpl in H7; tryfalse.

  (*there are 2 cases of loop inv, use the two cases to prove their corresponding
    return spec *)
  eapply disj_conj_distrib_pre.
  hoare forward.

  (*left case: x == 0 *)
  hoare normal pre.
  hoare_split_pure_all.
  eapply aconj_aisfalse_rule; eauto.
  intros.
  symbolic_execution;
    try solve
        [clear - H6; destruct v'21; unfolds in H6; simpl in H6; destruct H6; simpljoin1; tryfalse;
         try (destruct a); simpl; auto];
    eauto.
  hoare_split_pure_all.
  rewrite Int.eq_true in H8; simpl in H8.
  (*in this case, p(v'21) is null*)
  assert (v'21 = Vnull).
  clear - H3 H8.
  destruct v'21; unfolds in H3; destruct H3; simpljoin1; tryfalse.
  destruct a; simpl in H8.
  unfold Int.notbool in H8; rewrite Int.eq_true in H8.
  unfold Int.ltu in H8; rewrite Int.unsigned_zero in H8; rewrite Int.unsigned_one in H8; simpl in H8.
  destruct H8; tryfalse.
  subst v'21.
  
  (* RETURN x ′ *)
  substs.
  hoare forward.
  sep auto.
  destruct v'18.
  unfold1 evsllseg in H0.
  sep split in H0; simpljoin1.
  do 2 rewrite app_nil_r.
  auto.
  unfold1 evsllseg in H0.
  destruct v'20.
  simpl in H0; tryfalse.
  destruct e.
  unfold AEventNode in H0.
  unfold AOSEvent in H0.
  unfold node in H0.
  sep normal in H0.
  sep destruct H0.
  sep split in H0; simpljoin1; tryfalse.
  left.
  split; auto.
  assert (v'18 = nil /\ v'20 = nil).
  sep remember (4::nil)%nat in H0.
  destruct v'18.
  simpl evsllseg in H0.
  sep split in H0; simpljoin1; auto.
  simpl evsllseg in H0.
  destruct v'20.
  simpl in H0; tryfalse.
  destruct e.
  unfold AEventNode in H0; unfold AOSEvent in H0; unfold node in H0.
  sep normal in H0; sep destruct H0.
  sep split in H0; simpljoin1; tryfalse.
  simpljoin1.
  do 2 rewrite app_nil_r in H4.
  sep lift 3%nat in H0.
  eapply not_is_owner_evsllseg_not_is_some_mutex_owner; eauto.

  (*right case: x == 1 *)
  hoare normal pre.
  hoare_split_pure_all.
  eapply aconj_aisfalse_rule; eauto.
  intros.
  destruct v'17.
  symbolic_execution;
    try solve
        [clear - H6; destruct v'21; unfolds in H6; simpl in H6; destruct H6; simpljoin1; tryfalse;
         try (destruct a); simpl; auto];
    eauto.
  hoare_split_pure_all.

  (* RETURN x ′ *)
  hoare forward.
  sep auto.
  eapply evsllseg_app'; eauto.
  right.
  split; eauto.
  eapply ecblist_p_decompose in H4; simpljoin1.
  assert (x1 = (Vptr v'17)).
  destruct v'18.
  simpl in H0; simpljoin1.
  sep remember (3::nil)%nat in H8.
  simpl in H8; simpljoin1; auto.
  eapply ECBList_last_val in H0; simpljoin1.
  sep remember (3::nil)%nat in H8.
  simpl_sat H8; simpljoin1.
  lets Hx: evsllseg_get_last_eq H21; auto.
  unfolds in Hx.
  rewrite H0 in Hx.
  unfolds in Hx.
  rewrite H16 in Hx; inverts Hx; auto.
  auto.
  substs.
  sep remember (4::nil)%nat in H8.
  eapply is_mutex_owner_is_some_mutex_owner; eauto.
  apply EcbMod.join_comm; eauto.
  auto.
Qed.
