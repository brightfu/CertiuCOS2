Require Import ucos_include.
Require Import os_ucos_h.
Require Import sep_lemmas_ext.
Require Import symbolic_lemmas.
Require Import OSQPostPure.
Local Open Scope code_scope.
Local Open Scope nat_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.
Local Open Scope list_scope.

(*added by zhanghui*)
Lemma tcbdllflag_set_node :
  forall vltcb vltcb' p s P head vl vl',
    s |= tcbdllflag head vltcb ** P ->
    tcblist_get p head vltcb = Some vl ->
    set_node p vl' head vltcb = vltcb' ->
    same_prev_next vl vl' ->
    s |= tcbdllflag head vltcb' ** P.
Proof.
  inductions vltcb; intros.
  simpl in H0; tryfalse.

  unfold tcblist_get in H0; fold tcblist_get in H0.
  unfold set_node in H1; fold set_node in H1.
  destruct(beq_val p head) eqn : eq1.
  inverts H0.
  substs.
  unfold tcbdllflag in *; unfold dllsegflag in *; fold dllsegflag in *.
  sep normal in H; do 2 destruct H; sep split in H.
  sep normal; sep eexists.
  sep split; eauto.
  clear - H2 H1.
  unfolds in H2.
  rewrite H1 in H2.
  destruct (V_OSTCBNext vl');
    destruct (V_OSTCBPrev vl);
    destruct (V_OSTCBPrev vl'); tryfalse; simpljoin; auto.    

  destruct(V_OSTCBNext a) eqn : eq2; tryfalse.
  substs.
  unfold tcbdllflag in *; unfold dllsegflag in *; fold dllsegflag in *.
  sep normal in H.
  do 2 destruct H.
  sep split in H.
  sep normal; sep eexists; sep split; eauto.
  sep cancel 1%nat 1%nat.
  remember(set_node p vl' (nth_val' 0 a) vltcb) as vltcb'.
  rewrite eq2 in H3; inverts H3.
  eapply IHvltcb; eauto.
  unfolds in eq2.
  apply nth_val_nth_val'_some_eq in eq2; rewrite eq2 in Heqvltcb'.
  auto.
Qed.

Lemma tcblist_get_set_node_split :
  forall vltcb head p vl vl',
    tcblist_get p head vltcb = Some vl ->
    exists vltcb1 vltcb2,
      vltcb = vltcb1++vl::vltcb2 /\
      set_node p vl' head vltcb = vltcb1++vl'::vltcb2.
Proof.
  inductions vltcb; intros.
  simpl in H; tryfalse.
  unfold tcblist_get in H; fold tcblist_get in H.
  unfold set_node; fold set_node.
  destruct(beq_val p head) eqn : eq1.
  inverts H.
  do 2 eexists.
  rewrite app_nil_l; eauto.

  destruct(V_OSTCBNext a) eqn : eq2; tryfalse.
  lets Hx : IHvltcb v p vl vl' H. 
  destruct Hx; destruct H0; destruct H0.
  substs.
  exists (a::x) x0.
  rewrite <- app_comm_cons; split; auto.
  unfolds in eq2.
  apply nth_val_nth_val'_some_eq in eq2.
  rewrite eq2.
  rewrite H1.
  rewrite <- app_comm_cons; auto.
Qed.

Definition rtbl_set_one_bit rtbl rtbl' prio :=
  exists row bitx,
    0 <= Int.unsigned prio < 64 /\
(*    array_type_vallist_match Int8u rtbl /\ length rtbl = ∘ OS_RDY_TBL_SIZE /\
    array_type_vallist_match Int8u rtbl' /\ length rtbl' = ∘ OS_RDY_TBL_SIZE /\ *)
    nth_val' (Z.to_nat (Int.unsigned (prio>>ᵢ$ 3))) rtbl = Vint32 row /\
    nth_val' (Z.to_nat (Int.unsigned (prio&ᵢ$ 7))) OSMapVallist = Vint32 bitx /\
    rtbl' = update_nth_val (Z.to_nat (Int.unsigned(prio>>ᵢ$ 3))) rtbl (Vint32 (Int.or row bitx)).

(* important lemma *)
Lemma set_node_elim : 
  forall tid tcbls vltcb P s head tail t_rdy vl vl' prio st st' m m' rtbl rtbl',
    ptr_in_tcbdllseg (Vptr tid) head (set_node (Vptr t_rdy) vl' head vltcb) ->
    tcblist_get (Vptr t_rdy) head vltcb = Some vl ->
    TCBList_P head vltcb rtbl tcbls ->
    get tcbls t_rdy = Some (prio, st, m) -> (*prove this*)
    TCBNode_P vl' rtbl' (prio, st', m') -> (*prove this*)
    rtbl_set_one_bit rtbl rtbl' prio -> (*prove this*)
    R_Prio_No_Dup tcbls ->
    same_prev_next vl vl' ->
    s |= tcbdllseg head Vnull tail Vnull (set_node (Vptr t_rdy) vl' head vltcb) ** P ->
    s |= EX (l1 l2 : list vallist) (tcb_cur:vallist) (tail1 : val) (tcbls1 tcbls2 : TcbMod.map),
         tcbdllseg head Vnull tail1 (Vptr tid) l1 **
         tcbdllseg (Vptr tid) tail1 tail Vnull (tcb_cur::l2) **
         [| (set_node (Vptr t_rdy) vl' head vltcb) = l1 ++ (tcb_cur :: l2)|] **
         [|TcbMod.join tcbls1 tcbls2 (TcbMod.set tcbls t_rdy (prio, st', m'))|] **
         [|TCBList_P head l1 rtbl' tcbls1|] **
         [|TCBList_P (Vptr tid) (tcb_cur :: l2) rtbl' tcbls2|] ** P.
Proof.
  intros.
  assert(TCBList_P head  (set_node (Vptr t_rdy) vl' head vltcb) rtbl' (TcbMod.set tcbls t_rdy (prio, st', m'))).
  lets Hx: tcblist_get_set_node_split H0.
  instantiate (1:=vl') in Hx.
  simpljoin.
  rewrite H9.
  lets Hx: TCBList_P_Split H1; simpljoin.
  assert(x1 = (Vptr t_rdy)).
  rewrite H9 in H7.    
  lets Hx: tcbdllseg_distinct_tcbdllseg_next_ptr_vnull H7.

  eapply distinct_tcbdllseg_next_ptr_preserve with (vl':=vl) in Hx.
  eapply distinct_tcbdllseg_next_ptr_vnull_tcblist_get_get_last_tcb_ptr; eauto.
  apply new_inv.same_prev_next_sym; auto.
  substs.

  assert(TcbMod.get x3 t_rdy = Some (prio, st, m)) as tcbls2_get_prio.
  unfold TCBList_P in H12; fold TCBList_P in H12; simpljoin.
  inverts H12.
  clear - H10 H14 H2.
  unfold get in H2; simpl in H2.
  assert(get x3 x1 = Some x6).
  clear -H14.
  eapply join_sig_get; eauto.
  assert (get tcbls x1 = Some x6).
  assert (join x2 x3 tcbls) by eauto.
  clear - H H0.
  jeat.
  unfold get in H0; simpl in H0.
  rewrite H2 in H0; inverts H0.
  unfold get in H; simpl in H; auto.
  
  assert(TCBList_P head x rtbl' x2).
  clear -H4 H5 H10 H11 tcbls2_get_prio.
  unfolds in H4; simpljoin.
  assert(x1 = ($ 1<<ᵢ(prio&ᵢ$ 7))).
  eapply math_mapval_core_prop; auto.
  clear - H H3.
  mauto.
  substs.
  eapply TCBList_P_rtbl_add_simpl_version; eauto.
  eapply nth_val'_imp_nth_val_int; auto.
  clear - H5 tcbls2_get_prio H10.
  intros.
  unfolds in H5.
  assert(tid <> t_rdy).
  intro; substs.
  pose proof H10 t_rdy.
  destruct(TcbMod.get x2 t_rdy);
    destruct(TcbMod.get x3 t_rdy);
    destruct(TcbMod.get tcbls t_rdy); tryfalse.
  assert(TcbMod.get tcbls t_rdy = Some (prio, st, m)).
  eapply TcbMod.join_get_r; eauto.
  assert(TcbMod.get tcbls tid = Some(p, s, m0)).
  eapply TcbMod.join_get_l; eauto.
  eapply H5; eauto.

  assert(TCBList_P (Vptr t_rdy) (vl'::x0) rtbl' (set x3 t_rdy (prio, st', m'))).
  unfold TCBList_P in *; fold TCBList_P in *.
  simpljoin.
  inverts H12.
  unfolds in H6.
  rewrite H14 in H6.
  destruct (V_OSTCBNext vl'); tryfalse.
  do 4 eexists.
  splits; eauto.
  instantiate (1:=x5).
  clear - H15.
  eapply joinsig_set; eauto.

  destruct H6; substs.
  clear - H10 H15 H17 tcbls2_get_prio H4 H5.
  unfolds in H4; simpljoin.

  assert(x4 = ($ 1<<ᵢ(prio&ᵢ$ 7))).
  eapply math_mapval_core_prop; auto.
  clear - H H3.
  mauto.
  substs.
  eapply TCBList_P_rtbl_add_simpl_version; eauto.
  eapply nth_val'_imp_nth_val_int; auto.
  assert(get x3 x1 = Some x6).
  clear - H15.
  join auto.
  unfold get in H2; simpl in H2.
  rewrite tcbls2_get_prio in H2; inverts H2.
  clear - H5 tcbls2_get_prio H15 H10.
  intros.
  unfolds in H5.
  assert(tid <> x1).
  intro; substs.
  pose proof H15 x1.
  rewrite TcbMod.get_sig_some in H0.
  rewrite H in H0; tryfalse.
  assert(TcbMod.get tcbls x1 = Some (prio, st, m)).
  eapply TcbMod.join_get_r; eauto.
  assert(TcbMod.get tcbls tid = Some(p, s, m0)).
  eapply TcbMod.join_get_r; eauto.
  clear - H15 H.
  unfold TcbJoin in H15.
  unfold join, sig in H15; simpl in H15.
  eapply TcbMod.join_get_r; eauto.
  eapply H5; eauto.
  
  assert(join x2 (set x3 t_rdy (prio, st', m')) (set tcbls t_rdy (prio, st', m'))).
  clear - H10 tcbls2_get_prio.
  eapply join_set_r; eauto.
  unfold indom.
  eauto.
  
  eapply TCBList_P_Combine; eauto.
  eapply new_inv.tcbdllseg_split' in H7; eauto.
  do 5 destruct H7.
  destruct x0.
  unfold tcbdllseg in H7.
  simpl dllseg in H7.
  sep split in H7; tryfalse.

  sep auto; eauto.
Qed.

Lemma TCBList_P_tcblist_get_TCBNode_P :
  forall vltcb head rtbl tcbls tid vl abstcb,
    TCBList_P head vltcb rtbl tcbls ->
    tcblist_get (Vptr tid) head vltcb = Some vl ->
    TcbMod.get tcbls tid = Some abstcb ->
    TCBNode_P vl rtbl abstcb.
Proof.
  inductions vltcb; intros.
  simpl in H0; tryfalse.

  unfold tcblist_get in H0; fold tcblist_get in H0.
  unfold TCBList_P in H; fold TCBList_P in H; simpljoin.
  destruct (beq_val (Vptr tid) (Vptr x)) eqn : eq1.
  inverts H0.
  apply new_inv.beq_val_true_eq in eq1; inverts eq1.
  assert(TcbMod.get tcbls x = Some x2).
  eapply TcbMod.join_sig_get.
  unfold TcbJoin in H3.
  unfold join, sig in H3; simpl in H3.
  eauto.
  rewrite H1 in H; inverts H; auto.

  destruct (V_OSTCBNext a) eqn : eq2; tryfalse.
  inverts H2.
  eapply IHvltcb; eauto.

  clear - H3 H1 eq1.
  pose proof H3 tid.
  rewrite TcbMod.get_sig_none in H.
  destruct(TcbMod.get x1 tid);
    destruct(TcbMod.get tcbls tid); tryfalse.
  substs; auto.
  intro; substs.
  simpl in eq1.
  rewrite beq_addrval_true in eq1; tryfalse.
Qed.


Lemma set_node_elim_hoare : 
  forall spec sd linv inv r ri tid tcbls vltcb P s q head tail t_rdy vl vl' prio st st' m m' rtbl rtbl',
    ptr_in_tcbdllseg (Vptr tid) head (set_node (Vptr t_rdy) vl' head vltcb) ->
    tcblist_get (Vptr t_rdy) head vltcb = Some vl ->
    TCBList_P head vltcb rtbl tcbls ->
    get tcbls t_rdy = Some (prio, st, m) -> (*prove this*)
    TCBNode_P vl' rtbl' (prio, st', m') -> (*prove this*)
    rtbl_set_one_bit rtbl rtbl' prio -> (*prove this*)
    R_Prio_No_Dup tcbls ->
    same_prev_next vl vl' ->
    
    {|spec, sd, linv, inv, r, ri|} |- tid
      {{EX (l1 l2 : list vallist) (tcb_cur:vallist) (tail1 : val) (tcbls1 tcbls2 : TcbMod.map),
      tcbdllseg head Vnull tail1 (Vptr tid) l1 **
      tcbdllseg (Vptr tid) tail1 tail Vnull (tcb_cur::l2) **
      [| (set_node (Vptr t_rdy) vl' head vltcb) = l1 ++ (tcb_cur :: l2)|] **
      [|TcbMod.join tcbls1 tcbls2 (TcbMod.set tcbls t_rdy (prio, st', m'))|] **
      [|TCBList_P head l1 rtbl' tcbls1|] **
      [|TCBList_P (Vptr tid) (tcb_cur :: l2) rtbl' tcbls2|] ** P
       }} s {{q}} ->
    {|spec, sd, linv, inv, r, ri|} |- tid {{tcbdllseg head Vnull tail Vnull (set_node (Vptr t_rdy) vl' head vltcb) ** P }} s {{q}}.
Proof.
  intros.
  eapply backward_rule1.
  intros.
  eapply set_node_elim; eauto.
  auto.
Qed.

Lemma R_Prio_No_Dup_tid_eq :
  forall tcbls prio tid tid' st st' m m',
    R_Prio_No_Dup tcbls ->
    TcbMod.get tcbls tid = Some (prio, st, m) ->
    TcbMod.get tcbls tid' = Some (prio, st', m') ->
    st = st' /\ m = m'.
Proof.
  intros.
  unfolds in H.
  destruct (tidspec.beq tid tid') eqn : eq1.
  apply tidspec.beq_true_eq in eq1; substs.
  rewrite H1 in H0; inverts H0; auto.
  apply tidspec.beq_false_neq in eq1.
  lets Hx: H eq1 H0 H1; tryfalse.
Qed.

Lemma TCBNode_P_set_rdy :
  forall next prev p_event st msg msg' msg1 dly stat stat' prio prio1 tcbx tcby tcbbitx tcbbity rtbl row y bitx,
    0 <= Int.unsigned prio < 64 ->
    nth_val (Z.to_nat (Int.unsigned (prio>>ᵢ$ 3))) rtbl = Some (Vint32 row) ->
    Int.unsigned row <= 255 ->
    stat' = Int.zero ->
    y = (prio >>ᵢ $ 3) ->
    bitx = ($ 1<<ᵢ(prio&ᵢ$ 7)) ->
    TCBNode_P
      (     next
              :: prev
              :: p_event
              :: msg1
              :: dly
              :: Vint32 stat
              :: prio1
              :: tcbx :: tcby :: tcbbitx :: tcbbity :: nil)
      rtbl (prio, st, msg) ->
    TCBNode_P
      (    next
             :: prev
             :: Vnull
             :: msg'
             :: Vint32 Int.zero
             :: Vint32 stat'
             :: prio1
             :: tcbx :: tcby :: tcbbitx :: tcbbity :: nil)
      (update_nth_val (Z.to_nat (Int.unsigned y)) rtbl
                      (Vint32 (Int.or row bitx)))
      (prio, rdy, msg').
Proof.
  introv.
  do 4 intro.
  intros Hy Hbitx.
  rewrite Hy in *; clear Hy.
  rewrite Hbitx in *; clear Hbitx.
  intro.
  unfolds in H3.
  unfolds.
  simpljoin.
  splits; eauto.

  unfolds in H5; simpljoin.
  unfolds.
  do 6 eexists.
  splits; eauto.
  unfolds; simpl; eauto.
  splits; eauto.
  unfold V_OSTCBEventPtr; simpl.
  eexists; splits; eauto.

  unfolds in H4; simpl in H4; inverts H4.
  unfolds in H6; simpljoin.
  unfolds; splits.
  
  clear - H2.
  unfolds; intros.
  unfolds in H.
  simpljoin.
  unfolds in H; simpl in H; inverts H.
  splits; try solve [unfolds; simpl; auto].
  eauto.

  unfolds; intros.
  inverts H9.
  splits; try solve [unfolds; simpl; auto].
  unfolds.
  splits; try solve [unfolds; simpl; auto].
  apply prio_in_tbl_orself ; auto.

  unfolds in H6; simpljoin.
  unfolds.
  splits.
  unfolds; intros.
  unfolds in H14; simpl in H14; inverts H14.
  unfolds in H13; simpljoin.
  unfolds in H13; simpl in H13; inverts H13.
  unfolds in H15; simpl in H15; inverts H15.
  false.
  lets Hfs :  prio_notin_tbl_orself H7 H0.
  tryfalse.
  
  unfolds.
  intros.
  unfolds in H14; simpl in H14; inverts H14.
  
  unfolds; intros.
  unfolds in H13; simpl in H13; inverts H13.
  unfolds in H15; simpl in H15; inverts H15.

  unfolds; intros.
  unfolds in H14; simpl in H14; inverts H14.

  unfolds; intros.
  unfolds in H13; simpljoin.
  unfolds in H13; simpl in H13; inverts H13.
  unfolds in H15; simpl in H15; inverts H15.

  unfolds.
  splits; try solve [unfolds; introv Hf; inverts Hf].
Qed.
(*end of zhanghui*)
Lemma tcblist_get_TCBList_P_get :
  forall vltcb tcbls head rtbl tid vl prio,
    tcblist_get (Vptr tid) head vltcb = Some vl ->
    V_OSTCBPrio vl = Some (Vint32 prio) ->
    TCBList_P head vltcb rtbl tcbls ->
    exists st m, get tcbls tid = Some (prio, st, m).
Proof.
  inductions vltcb; intros.
  simpl in H; tryfalse.
  
  unfold tcblist_get in H; fold tcblist_get in H.
  destruct (beq_val (Vptr tid) head) eqn : eq1.
  inverts H.
  unfold TCBList_P in H1; fold TCBList_P in H1.
  simpljoin.
  Require Import new_inv.
  apply beq_val_true_eq in eq1; inverts eq1.
  destruct x2; destruct p.
  unfolds in H3; simpljoin.
  rewrite H0 in H3; inverts H3.
  join auto.

  destruct (V_OSTCBNext a) eqn: eq2; tryfalse.
  unfold TCBList_P in H1; fold TCBList_P in H1; simpljoin.
  rewrite eq2 in H2; inverts H2.
  lets Hx: IHvltcb H H0 H5.
  clear - H3 Hx.
  destruct Hx; destruct H.
  exists x0 x3.
  eapply join_get_r; eauto.
Qed.


(*
Lemma TCBList_P_tcblist_get_TCBNode_P :
  forall vltcb head rtbl tcbls tid vl abstcb,
    TCBList_P head vltcb rtbl tcbls ->
    tcblist_get (Vptr tid) head vltcb = Some vl ->
    TcbMod.get tcbls tid = Some abstcb ->
    TCBNode_P vl rtbl abstcb.
Proof.
  inductions vltcb; intros.
  simpl in H0; tryfalse.

  unfold tcblist_get in H0; fold tcblist_get in H0.
  unfold TCBList_P in H; fold TCBList_P in H; simpljoin.
  destruct (beq_val (Vptr tid) (Vptr x)) eqn : eq1.
  inverts H0.
  apply new_inv.beq_val_true_eq in eq1; inverts eq1.
  assert(TcbMod.get tcbls x = Some x2).
  eapply TcbMod.join_sig_get.
  unfold TcbJoin in H3.
  unfold join, sig in H3; simpl in H3.
  eauto.
  rewrite H1 in H; inverts H; auto.

  destruct (V_OSTCBNext a) eqn : eq2; tryfalse.
  inverts H2.
  eapply IHvltcb; eauto.

  clear - H3 H1 eq1.
  pose proof H3 tid.
  rewrite TcbMod.get_sig_none in H.
  destruct(TcbMod.get x1 tid);
    destruct(TcbMod.get tcbls tid); tryfalse.
  substs; auto.
  intro; substs.
  simpl in eq1.
  rewrite beq_addrval_true in eq1; tryfalse.
Qed.
*)


Lemma set_node_eq_dllflag :
  forall tcbl ptr  v'82 v'83 v'84 v'85 v'86 v'87 v'88 v'89 v'90 v'91 v'92 v'83' v'84' v'85' v'86' v'87' v'88' v'89' v'90' v'91' head,
    tcblist_get ptr head tcbl = 
    Some
      (v'82 :: v'83 :: v'84 :: v'85 :: v'86 :: v'87 :: v'88
            :: v'89 :: v'90 :: v'91 :: v'92 :: nil) ->
    eq_dllflag tcbl (set_node ptr (v'82 :: v'83' :: v'84' :: v'85' :: v'86' :: v'87' :: v'88'
                                        :: v'89' :: v'90' :: v'91' :: v'92 :: nil) head tcbl).
Proof.
  induction tcbl.
  intros.
  simpl.
  auto.
  intros.
  simpl.
  remember (beq_val ptr head).
  destruct b.
  unfold tcblist_get in H.
  rewrite <- Heqb in H.
  simpl in H.
  inverts H.
  splits; auto.
  Focus 2.
  splits; auto.
  eapply IHtcbl.
  unfolds in H.
  rewrite <- Heqb in H.
  destruct a.
  simpl in H.
  inversion H.
  simpl in H.
  fold tcblist_get in H.
  exact H.

  apply eq_dllflag_refl.
Qed.


Lemma eq_dllflag_trans :
  forall l1 l2 l3,
    eq_dllflag l1 l2 ->
    eq_dllflag l2 l3 ->
    eq_dllflag l1 l3.
Proof.
  induction l1.
  intros.
  simpl in H.
  destruct l2; tryfalse.

  simpl in H0.
  destruct l3; tryfalse.
  auto.
  intros.
  simpl in H.
  destruct l2; tryfalse.
  simpl in H0.
  destruct l3; tryfalse.
  simpl.
  simpljoin.
  splits.
  rewrite H.
  auto.
  rewrite H3.
  auto.
  eapply IHl1.
  eauto.
  eauto.
Qed.

