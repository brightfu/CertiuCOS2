(**************************  uc/OS-II  *******************************)
(*************************** OS_CORE.C *******************************)
(**Proof of Internal Fucntion: 
 Int8u OS_EventTaskRdy(OS_EVENT* pevent; void* message; int8u  msk) **)
(**************************** Code:***********************************)
(***
Int8u ·OS_EventTaskRdy·(⌞pevent @ OS_EVENT∗; message @ Void∗ ;  msk @ Int8u⌟)··{
       ⌞
        ptcb @ OS_TCB∗;
        x @ Int8u;
        y @ Int8u;
        bitx @ Int8u;
        bity @ Int8u;
        prio @ Int8u
       ⌟;

1       y′ =ₑ OSUnMapTbl′[pevent′→OSEventGrp];ₛ
2       bity′ =ₑ OSMapTbl′[y′];ₛ
3       x′ =ₑ OSUnMapTbl′[pevent′→OSEventTbl[y′]];ₛ
4       bitx′ =ₑ OSMapTbl′[x′];ₛ
5       prio′ =ₑ ((y′ ≪ ′3) +ₑ x′);ₛ
6       pevent′→OSEventTbl[y′] =ₑ pevent′→OSEventTbl[y′] &ₑ (∼bitx′);ₛ
7       If (pevent′→OSEventTbl[y′] ==ₑ ′0)
        {
8           pevent′→OSEventGrp =ₑ pevent′→OSEventGrp &ₑ (∼bity′)
        };ₛ
9       ptcb′ =ₑ OSTCBPrioTbl′[prio′];ₛ
10      ptcb′→OSTCBDly =ₑ ′0;ₛ
11      ptcb′→OSTCBEventPtr =ₑ  NULL;ₛ
12      ptcb′→OSTCBMsg =ₑ message′;ₛ
13      ptcb′→OSTCBStat =ₑ (ptcb′→OSTCBStat) &ₑ (∼msk′);ₛ
14      OSRdyGrp′ =ₑ OSRdyGrp′ |ₑ bity′;ₛ
15      OSRdyTbl′[y′] =ₑ OSRdyTbl′[y′] |ₑ bitx′;ₛ
16      RETURN prio′
 }·.
*********)                                                             
(*Require Import ucert.
Require Import mathlib.
Require Import OSEventTaskRdyPure.
Require Import lab.
Require Import new_inv.
Require Import oscore_common.
 *)

Require Import ucos_include.
Require Import OSEventTaskRdyPure.
Require Import OSTimeDlyPure.
Require Import go.

Open Scope code_scope.
Open Scope Z_scope.
Open Scope int_scope.
Open Scope list_scope.


Ltac rtmatch_solve:=   
  apply true_if_else_true;
  apply Zle_is_le_bool;
  try rewrite byte_max_unsigned_val; try rewrite max_unsigned_val;
  try omega.

Lemma lt_8_le_byte_max_unsigned_true :
  forall i,
    Int.unsigned i < 8 -> Int.unsigned i <=? Byte.max_unsigned = true.
Proof.
  intros; mauto.
Qed.

Lemma lt_64_le_byte_max_unsigned_true :
  forall i,
    Int.unsigned i < 64 -> Int.unsigned i <=? Byte.max_unsigned = true.
Proof.
  intros; mauto.
Qed.

Lemma lt_256_le_byte_max_unsigned_true :
  forall i,
    Int.unsigned i < 256 -> Int.unsigned i <=? Byte.max_unsigned = true.
Proof.
  intros; mauto.
Qed.

Lemma le_128_le_byte_max_unsigned_true :
  forall i,
    Int.unsigned i <= 128 -> Int.unsigned i <=? Byte.max_unsigned = true.
Proof.
  intros; mauto.
Qed.

Lemma z_le_255_imp_n_lt_256 :
  forall x : int32,
    Int.unsigned x <= 255 -> (Z.to_nat (Int.unsigned x) < 256)%nat.
Proof.
  apply z_le_255_imp_n; auto.
Qed.

Lemma  rl_tbl_grp_neq_zero:
  forall  v'12  px v'13 v'69,
    Int.unsigned px < 8 ->
    Int.unsigned v'12 <= 255 ->
    v'12 <> $ 0 ->
    nth_val' (Z.to_nat (Int.unsigned v'12)) OSUnMapVallist = Vint32  px -> 
    nth_val' (Z.to_nat (Int.unsigned px)) v'13 = Vint32 v'69 ->
    RL_Tbl_Grp_P v'13 (Vint32 v'12) ->
    v'69 <> $ 0.
Proof.
  introv Hran Hras Hneq Hnth Hth2 Hr.
  unfolds in Hr.
  assert (0 <=Z.to_nat (Int.unsigned px) < 8 )%nat.
  clear - Hran.
  mauto.
  apply nth_val'_imp_nth_val_int in Hth2.
  assert (Vint32 v'12 = Vint32 v'12) by auto.
  lets Hsr : Hr H Hth2 H0.
  simp join.
  lets Hneqz : math_8_255_eq Hras Hneq; eauto.
  assert ($ Z.of_nat (Z.to_nat (Int.unsigned px)) = px).
  clear -Hran.
  mauto.
  rewrite H0 in *.
  rewrite Hneqz in *.
  assert (v'69 = $ 0 \/ v'69 <> $ 0) by tauto.
  destruct H4; auto.
  apply H1 in H4.
  false.
  gen H4.
  clear - Hran.
  mauto.
Qed.

Lemma int_ltu_3_iwordsize :
  Int.ltu ($ 3) Int.iwordsize = true.
Proof.
  apply int_iwordsize_gt_3.
Qed.

Lemma disj_intro :
  forall P Q R,
    P ==> R ->
    Q ==> R ->
    P \\// Q ==> R.
Proof.
  intros.
  destruct H1.
  apply H; auto.
  apply H0; auto.
Qed.

Lemma disj_combine :
  forall F sd I r ri s P Q R S tid linv,
    P ==> S -> Q ==> S ->
    {|F, sd, linv, I, r, ri|}|-tid {{S}} s {{R}} ->
                               {|F, sd, linv, I, r, ri|}|-tid {{P\\//Q}} s {{R}}.
Proof.
  intros.
  eapply backward_rule1.
  eapply disj_intro; eauto.
  auto.
Qed.

Lemma rl_tbl_grp_p_set_hold1:
  forall v'12 v'38 v'13 v'69 v'39 v'40 v'41,
    v'12 <> Int.zero ->
    Int.unsigned v'12 <= 255 ->
    array_type_vallist_match Int8u v'13 ->
    length v'13 = ∘OS_EVENT_TBL_SIZE ->
    nth_val' (Z.to_nat (Int.unsigned v'12)) OSUnMapVallist = Vint32 v'38 ->
    Int.unsigned v'38 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned v'38)) v'13 = Vint32 v'69 ->
    Int.unsigned v'69 <= 255 ->
    nth_val' (Z.to_nat (Int.unsigned v'69)) OSUnMapVallist = Vint32 v'39 ->
    Int.unsigned v'39 <= 7 ->
(*    nth_val' (Z.to_nat (Int.unsigned ((v'38<<$ 3)+ᵢv'39))) v'36 = Vptr (v'58, Int.zero)-> *)
    nth_val' (Z.to_nat (Int.unsigned v'39)) OSMapVallist = Vint32 v'40 ->
    Int.unsigned v'40 <= 128 ->
    nth_val' (Z.to_nat (Int.unsigned v'38)) OSMapVallist = Vint32 v'41 ->
    Int.unsigned v'41 <= 128 ->
    Int.eq (v'69&ᵢInt.not v'40) Int.zero = true ->
    RL_Tbl_Grp_P v'13 (Vint32 v'12) ->
    RL_Tbl_Grp_P
      (update_nth_val (Z.to_nat (Int.unsigned v'38)) v'13
                      (Vint32 (v'69&ᵢInt.not v'40))) (Vint32 (v'12&ᵢInt.not v'41)).
Proof.
  intros.
  unfold Int.zero in *.
  pose (Int.eq_spec (v'69&ᵢInt.not v'40) ($ 0)) as Hps.
  rewrite H13 in Hps.
  unfolds in H14.
  unfolds.
  intros.
  assert (n =  (Z.to_nat (Int.unsigned v'38)) \/  n <>(Z.to_nat (Int.unsigned v'38))) as Hdisj.
  tauto.
  destruct Hdisj.
  subst n.
  apply nth_upd_eq in H16.
  inverts H16.
  assert (Int.unsigned v'38 < 8) as Ha by omega.
  assert ($ Z.of_nat (Z.to_nat (Int.unsigned v'38)) = v'38).
  clear - Ha.
  mauto.
  rewrite H16 in *.
  inverts H17.
  assert (($ 1<<ᵢv'38)&ᵢInt.not v'41 = $ 0).
  clear - Ha H11.
  mautoext.
  splits.
  split.
  intros.
  auto.
  intros.
  lets Hzs : math_8_255_eq H0 H3 H.
  rewrite Int.and_commut.
  rewrite <-Int.and_assoc.
  assert ( v'12&ᵢ($ 1<<ᵢv'38) = ($ 1<<ᵢv'38)&ᵢv'12) .
  rewrite Int.and_commut; auto.
  rewrite H19 in Hzs.
  rewrite Hzs.
  auto.
  splits.
  rewrite Int.and_assoc.
  intros.
  assert (Int.not v'41&ᵢ($ 1<<ᵢv'38) = ($ 1<<ᵢv'38)&ᵢInt.not v'41).
  apply Int.and_commut.
  rewrite H19 in H18.
  rewrite H17 in H18.
  rewrite Int.and_zero in H18.
  unfold Int.zero in H18.
  false.
  clear -Ha H18.
  gen H18.
  mauto.
  intros.
  rewrite Hps in H18.
  false.
  eapply nth_upd_neq in H16; eauto.
  inverts H17.
  assert (Vint32 v'12 = Vint32 v'12) by auto.
  lets Hsa : H14 H15 H16 H17.
  destruct Hsa.
  lets Hasd : math_nth_8_neq_not  H11 H18; try omega; eauto.
  split.
  split;
    intros.
  apply H19.
  rewrite Int.and_assoc in H21.
  rewrite Hasd in H21.
  auto.
  intros.
  apply H19 in H21.
  assert (v'12&ᵢInt.not v'41 = Int.not v'41 &ᵢ v'12).
  apply Int.and_commut.
  rewrite H22.
  rewrite Int.and_assoc.
  rewrite H21.
  rewrite Int.and_zero; auto.
  split.
  intros.
  apply H20.
  rewrite Int.and_assoc in H21.
  rewrite Hasd in H21.
  auto.
  intros.
  apply H20 in H21.
  rewrite Int.and_assoc.
  rewrite Hasd.
  auto.
Qed.

Lemma rl_tbl_grp_p_set_hold2
: forall (v'12 v'38 : int32) (v'13 : vallist)  (v'69 v'39 : int32) (v'40 v'41 : int32),
    v'12 <> Int.zero ->
    Int.unsigned v'12 <= 255 ->
    array_type_vallist_match Int8u v'13 ->
    length v'13 = ∘OS_EVENT_TBL_SIZE ->
    nth_val' (Z.to_nat (Int.unsigned v'12)) OSUnMapVallist = Vint32 v'38 ->
    Int.unsigned v'38 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned v'38)) v'13 = Vint32 v'69 ->
    Int.unsigned v'69 <= 255 ->
    nth_val' (Z.to_nat (Int.unsigned v'69)) OSUnMapVallist = Vint32 v'39 ->
    Int.unsigned v'39 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned v'39)) OSMapVallist = Vint32 v'40 ->
    Int.unsigned v'40 <= 128 ->
    nth_val' (Z.to_nat (Int.unsigned v'38)) OSMapVallist = Vint32 v'41 ->
    Int.unsigned v'41 <= 128 ->
    Int.eq (v'69&ᵢInt.not v'40) Int.zero = false->
    RL_Tbl_Grp_P v'13 (Vint32 v'12) ->
    RL_Tbl_Grp_P
      (update_nth_val (Z.to_nat (Int.unsigned v'38)) v'13
                      (Vint32 (v'69&ᵢInt.not v'40))) (Vint32 v'12).
Proof.
  intros.
  unfold Int.zero in *.
  pose (Int.eq_spec (v'69&ᵢInt.not v'40) ($ 0)) as Hps.
  rewrite H13 in Hps.
  unfolds in H14.
  unfolds.
  intros.
  assert (n =  (Z.to_nat (Int.unsigned v'38)) \/  n <>(Z.to_nat (Int.unsigned v'38))) as Hdisj.
  tauto.
  destruct Hdisj.
  subst n.
  apply nth_upd_eq in H16.
  inverts H16.
  assert (Int.unsigned v'38 < 8) as Ha by omega.
  assert ($ Z.of_nat (Z.to_nat (Int.unsigned v'38)) = v'38).
  clear - Ha.
  mauto.
  rewrite H16 in *.
  inverts H17.
  splits.
  splits.
  intros.
  lets Hsa : math_8_255_eq H0 H3 H.
  rewrite Hsa in H17.
  false.
  gen H17.
  clear - Ha.
  mauto.
  intros.
  tryfalse.
  split.
  intros.
  unfolds.
  rewrite zlt_true; auto.
  remember (v'69&ᵢInt.not v'40) as x.
  clear - Hps.
  assert (0<=Int.unsigned x) by (int auto).
  assert (0 = Int.unsigned x \/ 0 < Int.unsigned x) by omega.
  destruct H0; auto.
  false.
  apply Hps.
  rewrite H0.
  int auto.
  intros.
  lets Hzs : math_8_255_eq H0 H3 H.
  auto.
  inverts H17.
  eapply nth_upd_neq in H16;  eauto.
Qed.

Definition rel_edata_etype edata etype :=
  match edata with
  | DMsgQ _ _ _ _ =>
    etype = Int.repr OS_EVENT_TYPE_Q
  | DSem _ =>
    etype = Int.repr OS_EVENT_TYPE_SEM
  | DMbox _ =>
    etype = Int.repr OS_EVENT_TYPE_MBOX
  | DMutex _ _ =>
    etype = Int.repr OS_EVENT_TYPE_MUTEX
  end.

Lemma hoare_pure_gen : forall P1 P2 (p:Prop) S Q a b c d e f tid,
    (forall s, s |= P1 -> p) ->
    {|a,b,c,d,e,f|}|-tid {{P1 ** P2 ** [|p|]}} S {{Q}} ->
                     {|a,b,c,d,e,f|} |-tid {{P1 ** P2}} S {{Q}}.
Proof.
  intros.
  apply backward_rule1 with (p:=(P1 ** P2 ** [|p|])); auto.
  intros.
  sep auto.
  destruct_s s.
  simpl in H1; simp join.
  apply (H (e0, e1, x, i, (i0, i1, c0), x2, a0)); auto.
Qed.

Definition rel_edata_stat eid edata stat :=
  match edata with
  | DMsgQ _ _ _ _ =>
    exists n, stat = wait (os_stat_q eid) n
  | DSem _ =>
    exists n, stat = wait (os_stat_sem eid) n
  | DMbox _ =>
    exists n, stat = wait (os_stat_mbox eid) n
  | DMutex _ _ =>
    exists n, stat = wait (os_stat_mutexsem eid) n
  end.


Lemma PrioWaitInQ_RLH_ECB_ETbl_P_tcbls_ex :
  forall prio osevent etbl l tcbls te d,
    PrioWaitInQ prio etbl ->
    V_OSEventType osevent = Some (Vint32 te) ->
    rel_edata_etype d te ->
    RLH_ECB_ETbl_P l (osevent,etbl) tcbls ->
    exists tid st m, get tcbls tid = Some ($ prio, st, m) /\
                     rel_edata_stat l d st.
Proof.
  intros.
  unfold RLH_ECB_ETbl_P in H2; simp join.
  unfold RLH_ECB_ETbl_Q_P in H2; lets Hx1: H2 H; clear H2.
  unfold RLH_ECB_ETbl_SEM_P in H3; lets Hx2: H3 H; clear H3.
  unfold RLH_ECB_ETbl_MBOX_P in H4; lets Hx3: H4 H; clear H4.
  unfold RLH_ECB_ETbl_MUTEX_P in H5; lets Hx4: H5 H; clear H5.
  destruct d; simpl in H1; substs.
  apply Hx1 in H0; simp join; do 3 eexists; split; simpl; eauto.
  apply Hx2 in H0; simp join; do 3 eexists; split; simpl; eauto.
  apply Hx3 in H0; simp join; do 3 eexists; split; simpl; eauto.
  apply Hx4 in H0; simp join; do 3 eexists; split; simpl; eauto.
Qed.

Lemma nth_val_nth_val'_some_eq : forall n vl x,
  nth_val n vl = Some x -> nth_val' n vl = x.
Proof.
  inductions n; intros.
  destruct vl; simpl in H; tryfalse.
  unfolds; simpl; inverts H; auto.

  simpl.
  destruct vl; simpl in H; tryfalse.
  apply IHn in H; auto.
Qed.

Lemma tcbls_get_some_TCBList_P_ptr_in_tcblist :
  forall vltcb head tcbls tid pr st m rtbl,
    get tcbls tid = Some (pr, st, m) ->
    TCBList_P head vltcb rtbl tcbls ->
    ptr_in_tcblist (Vptr tid) head vltcb.
Proof.
  unfold get; simpl.
  inductions vltcb; intros.
  simpl in H0; substs.
  rewrite TcbMod.emp_sem in H; tryfalse.

  unfold TCBList_P in H0; fold TCBList_P in H0; simp join.
  destruct (beq_val (Vptr tid) (Vptr x)) eqn : eq1.
  unfold ptr_in_tcblist.
  unfold ptr_in_tcbdllseg; fold ptr_in_tcbdllseg.
  rewrite eq1; auto.
  
  unfold ptr_in_tcblist in *.
  unfold ptr_in_tcbdllseg; fold ptr_in_tcbdllseg.
  rewrite eq1.
  rewrite H1.
  assert (TcbMod.get x1 tid = Some (pr, st, m)).
  unfold TcbJoin in H2.
  pose proof H2 tid.
  rewrite TcbMod.get_sig_none in H0.
  destruct(TcbMod.get x1 tid);
    destruct(TcbMod.get tcbls tid); tryfalse.
  substs; auto.
  clear H0.
  intro; substs.
  simpl in eq1.
  unfolds in eq1; destruct tid.
  rewrite beq_pos_Pos_eqb_eq in eq1.
  rewrite Pos.eqb_refl in eq1.
  rewrite Int.eq_true in eq1.
  simpl in eq1; tryfalse.
  eapply IHvltcb; eauto.
Qed.

Require Import new_inv.
Lemma tcbdllseg1_init_pre :
  forall F sd I r ri s linv tid P Q vltcb head headprev tail tailnext,
    {|F, sd, linv, I, r, ri|}|-tid {{tcbdllseg1 head headprev tail tailnext vltcb nil **
                                                [|distinct_tcbdllseg_next_ptr head vltcb|] ** P}} s {{Q}} ->
                               {|F, sd, linv, I, r, ri|}|-tid {{tcbdllseg head headprev tail tailnext vltcb ** P}} s {{Q}}.
Proof.
  intros.
  eapply backward_rule1.
  eapply tcbdllseg1_init'.
  auto.
Qed.


Lemma tcbdllseg1_split_pre :
  forall F sd I r ri s linv tid P Q vltcb head headprev tail tailnext p holes,
    ptr_in_tcblist1 p head vltcb holes -> 
    {|F, sd, linv, I, r, ri|}|-tid {{ EX vl, node p vl OS_TCB_flag **
                                                  tcbdllseg1 head headprev tail tailnext vltcb ((p,vl)::holes) ** [|tcbdllseg1_get_node p head vltcb = Some vl|] **  P}} s {{Q}} ->
                               {|F, sd, linv, I, r, ri|}|-tid {{tcbdllseg1 head headprev tail tailnext vltcb holes ** P}} s {{Q}}.
Proof.
  intros.
  eapply backward_rule1.
  intros.
  eapply tcbdllseg1_split.
  sep auto.
  eauto.
  eapply backward_rule2; eauto.
  intros.
  sep pauto.
  sep lift 2%nat in H1.
  eapply ptr_in_tcbdllseg1_get_some; eauto.
  unfolds in H; simp join; auto.
Qed.

Lemma isptr_match :
  forall x,
    isptr x ->
    match x with
    | Vundef => false
    | Vnull => true
    | Vint32 _ => false
    | Vptr _ => true
    end = true.
Proof.
  intros; destruct x; unfolds in H; destruct H; tryfalse; destruct H; tryfalse; auto.
Qed.

Lemma tcbdllseg1_node_join_pre1 :
  forall F sd I r ri s linv tid P Q vltcb head headprev tail tailnext b holes vl vl',
    struct_type_vallist_match OS_TCB_flag vl' ->
    ptr_in_tcbdllseg (Vptr (b, Int.zero)) head vltcb -> 
    same_prev_next vl' vl ->
    ~ptr_in (Vptr (b, Int.zero)) holes ->
    distinct_ptr holes ->
    distinct_tcbdllseg_next_ptr head vltcb ->
    {|F, sd, linv, I, r, ri|}|-tid
                                 {{ tcbdllseg1 head headprev tail tailnext (set_node (Vptr (b, Int.zero)) vl' head vltcb) holes ** P}} s {{Q}} ->
                               {|F, sd, linv, I, r, ri|}|-tid
                                                            {{ Astruct (b, Int.zero) OS_TCB_flag vl' ** tcbdllseg1 head headprev tail tailnext vltcb (((Vptr (b, Int.zero)),vl)::holes) ** P}} s {{Q}}.
Proof.
  intros.
  eapply backward_rule2.
  eauto.
  intros.
  eapply tcbdllseg1_node_join'; eauto.
  unfold node.
  sep pauto.
Qed.

Lemma tcbdllseg1_to_tcbdllseg_pre1 :
  forall F sd I r ri s linv tid P Q vltcb head headprev tail tailnext b vl',
    {|F, sd, linv, I, r, ri|}|-tid
                                 {{ tcbdllseg head headprev tail tailnext (set_node (Vptr (b, Int.zero)) vl' head vltcb) ** P}} s {{Q}} ->
                               {|F, sd, linv, I, r, ri|}|-tid
                                                            {{ tcbdllseg1 head headprev tail tailnext (set_node (Vptr (b, Int.zero)) vl' head vltcb) nil ** P}} s {{Q}}.
Proof.
  intros.
  eapply backward_rule1.
  eapply tcbdllseg1_tcbdllseg'.
  auto.
Qed.

Lemma rl_tbl_grp_p_set_hold':
  forall v'12 v'38 v'37 v'57 v'69 v'39 v'36 v'13 v'58 v'40 v'41,
    v'12 <> Int.zero ->
    Int.unsigned v'12 <= 255 ->
    array_type_vallist_match Int8u v'13 ->
    length v'13 = ∘OS_EVENT_TBL_SIZE ->
    array_type_vallist_match Int8u v'37 ->
    length v'37 =  ∘OS_RDY_TBL_SIZE ->
    nth_val' (Z.to_nat (Int.unsigned v'12)) OSUnMapVallist = Vint32 v'38 ->
    Int.unsigned v'38 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned v'38)) v'13 = Vint32 v'69 ->
    Int.unsigned v'69 <= 255 ->
    nth_val' (Z.to_nat (Int.unsigned v'69)) OSUnMapVallist = Vint32 v'39 ->
    Int.unsigned v'39 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39))) v'36 = Vptr (v'58, Int.zero)->
    nth_val' (Z.to_nat (Int.unsigned v'39)) OSMapVallist = Vint32 v'40 ->
    Int.unsigned v'40 <= 128 ->
    nth_val' (Z.to_nat (Int.unsigned v'38)) OSMapVallist = Vint32 v'41 ->
    Int.unsigned v'41 <= 128 ->
    RL_Tbl_Grp_P v'13 (Vint32 v'12) ->
    RL_Tbl_Grp_P v'37 (Vint32 v'57) ->
    RL_Tbl_Grp_P  (update_nth_val (Z.to_nat (Int.unsigned v'38)) v'37
                                  (val_inj
                                     (or (nth_val' (Z.to_nat (Int.unsigned v'38)) v'37) (Vint32 v'40))))
                  (Vint32 (Int.or v'57 v'41)).
Proof.
  intros.
  unfold Int.zero in *.
  unfolds in H16.
  unfolds in H17.
  unfolds.
  intros.
  inverts H20.
  assert (n =  (Z.to_nat (Int.unsigned v'38)) \/  n <>(Z.to_nat (Int.unsigned v'38))) as Hdisj.
  tauto.
  destruct Hdisj.
  subst n.
  apply nth_upd_eq in H19.
  unfolds in H19.
  remember (or (nth_val' (Z.to_nat (Int.unsigned v'38)) v'37) (Vint32 v'40)) as vo.
  destruct vo; tryfalse.
  subst v0.
  assert ((Z.to_nat (Int.unsigned v'38)) < length v'37)%nat.
  rewrite H4.
  simpl.
  clear -H6.
  mauto.
  lets Hrs : array_int8u_nth_lt_len H19 ; eauto.
  destruct Hrs as (i & Hnth & Hr).
  rewrite Hnth in Heqvo.
  simpl in Heqvo.
  inverts Heqvo.
  assert (Int.unsigned v'38 < 8) as Ha by omega.
  assert ($ Z.of_nat (Z.to_nat (Int.unsigned v'38)) = v'38).
  clear - Ha.
  mauto.
  rewrite H20 in *.
  clear H20.
  split.
  split.
  intros.
  rewrite Int.and_commut in H20.
  rewrite  Int.and_or_distrib in H20.
  apply int_or_zero_split in H20.
  lets Hneq : math_nth_8_neq_zero  Ha H14.
  destruct H20.
  tryfalse.
  intros.
  apply int_or_zero_split in H20.
  destruct H20. subst.
  lets Hnz : math_nth_8_neq_zero' H12.
  omega.
  tryfalse.
  splits.
  assert (Int.unsigned v'40 <= Int.unsigned (Int.or i v'40)) .
  rewrite Int.or_commut.
  apply Int.or_le.
  lets Hgs : math_nth_8_gt_zero  H10 H12.
  assert (0 < Int.unsigned (Int.or i v'40)) by omega.
  intros.
  unfolds.
  rewrite zlt_true; auto.
  intros.
  rewrite Int.and_commut.
  rewrite Int.and_or_distrib.
  lets Has :   math_nth_8_eq_shl Ha H14.
  rewrite Has.
  rewrite Int.or_commut.
  rewrite Int.or_and_absorb.
  auto.
  apply nth_upd_neq in H19.
  assert ( Vint32 v'57 = Vint32 v'57) by auto.
  lets Hrs : H17 H18 H19 H21.
  destruct Hrs.
  splits.
  split;intros.
  apply H22.
  rewrite Int.and_commut in H24.
  rewrite Int.and_or_distrib in H24.
  apply int_or_zero_split in H24.
  destruct H24.
  rewrite Int.and_commut; auto.
  apply H22 in H24.
  rewrite Int.and_commut.
  rewrite Int.and_or_distrib .
  rewrite Int.and_commut in H24.
  rewrite H24.
  rewrite Int.and_commut.
  assert ($ 0 = Int.zero) by auto.
  rewrite H25.
  rewrite Int.or_commut.
  rewrite Int.or_zero.
  lets Hbc : math_nth_8_eq_zero H6 H14 H20; eauto.
  intros.
  split; intros.
  apply H23.
  lets Hbc : math_nth_8_eq_zero H6 H14 H20; eauto.
  rewrite Int.and_commut in H24.
  rewrite Int.and_or_distrib in H24.
  rewrite Int.and_commut in Hbc.
  rewrite Hbc in H24.
  rewrite Int.or_zero in H24.
  rewrite Int.and_commut.
  auto.
  apply H23 in H24.
  lets Hbc : math_nth_8_eq_zero H6 H14 H20; eauto.
  rewrite Int.and_commut .
  rewrite Int.and_or_distrib.
  rewrite Int.and_commut in Hbc.
  rewrite Hbc .
  rewrite Int.or_zero.
  rewrite Int.and_commut.
  auto.
  auto.
Qed.

Lemma nth_val'2nth_val:
  forall n rtbl x,
    nth_val' n rtbl = Vint32 x ->
    nth_val n rtbl = Some (Vint32 x).
Proof.
  intros.
  inductions n;
    simpl in *;  destruct rtbl; simpl in *;tryfalse; try subst; auto.
Qed.

Lemma prio_in_tbl_preserv :
  forall tbl prio prio1 y row bitx,
    nth_val' (Z.to_nat (Int.unsigned y)) tbl = Vint32 row ->
    prio_in_tbl prio tbl ->
    y = prio1>>ᵢ$ 3 ->
    bitx = $ 1<<ᵢ(prio1&ᵢ$ 7) ->
    Int.unsigned prio1 < 64 ->
    prio_in_tbl prio (update_nth_val (Z.to_nat (Int.unsigned y)) tbl
                                     (Vint32 (Int.or row bitx))).
Proof.
  intros.
  substs.
  unfold prio_in_tbl in *.
  intros.
  lets fff: H0 H1 H2.
  unfold nat_of_Z in *.
  assert ( (Z.to_nat (Int.unsigned y)) <> (Z.to_nat (Int.unsigned (prio1>>ᵢ$ 3)))  \/ (Z.to_nat (Int.unsigned y)) = (Z.to_nat (Int.unsigned (prio1>>ᵢ$ 3))) ). 
  tauto.
  elim H5; intros.
  apply nth_upd_neq in H4.
  apply fff.
  exact H4.
  intro; tryfalse.
  
  rewrite <- H6 in *.    

  lets fffb: H0 H1 H2 (nth_val'2nth_val _ _ _ H).
  apply nth_upd_eq in H4.
  simpl in H4.
  inverts H4.
  rewrite Int.and_or_distrib_l.
  rewrite fffb.
  assert ( 0<=Int.unsigned (($ 1<<ᵢ(prio1&ᵢ$ 7))) < 256).
  clear -H3; mauto.
  assert (0<=Int.unsigned x < 8).
  rewrite H1.
  rewrite Int.and_commut.
  clear.
  split.
  remember ($ 7&ᵢprio).
  int auto.
  change 8 with (Int.unsigned ($ 8)).
  assert ( Int.unsigned ($ 7&ᵢprio) <= Int.unsigned ($ 7)).
  apply Int.and_le.
  ur_rewriter.
  ur_rewriter_in H.
  omega.
  lets bbba: prio_int_disj H4 H7.
  clear -bbba H7.
  destruct bbba; intros; rewrite H.
  clear -H7; mauto.
  clear -H7; mauto.
Qed.

  Lemma rl_rtbl_priotbl_p_hold:
  forall v'36 v'12 v'13 v'38 v'69 v'39 v'58 v'40 v'41 v'57 v'37 vhold,
    (v'58, Int.zero) <> vhold ->
    RL_RTbl_PrioTbl_P v'37 v'36 vhold->
    v'12 <> Int.zero ->
    Int.unsigned v'12 <= 255 ->
    array_type_vallist_match Int8u v'13 ->
    length v'13 = ∘OS_EVENT_TBL_SIZE ->
    array_type_vallist_match Int8u v'37 ->
    length v'37 = ∘OS_EVENT_TBL_SIZE ->
    nth_val' (Z.to_nat (Int.unsigned v'12)) OSUnMapVallist = Vint32 v'38 ->
    Int.unsigned v'38 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned v'38)) v'13 = Vint32 v'69 ->
    Int.unsigned v'69 <= 255 ->
    nth_val' (Z.to_nat (Int.unsigned v'69)) OSUnMapVallist = Vint32 v'39 ->
    Int.unsigned v'39 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39))) v'36 = Vptr (v'58, Int.zero)->
    nth_val' (Z.to_nat (Int.unsigned v'39)) OSMapVallist = Vint32 v'40 ->
    Int.unsigned v'40 <= 128 ->
    nth_val' (Z.to_nat (Int.unsigned v'38)) OSMapVallist = Vint32 v'41 ->
    Int.unsigned v'41 <= 128 ->
    RL_Tbl_Grp_P v'13 (Vint32 v'12) ->
    RL_Tbl_Grp_P v'37 (Vint32 v'57) ->
    Int.unsigned v'57 <= 255 ->
    array_type_vallist_match Tint8 v'37 ->
    length v'37 = nat_of_Z OS_RDY_TBL_SIZE ->
    RL_RTbl_PrioTbl_P
      (update_nth_val (Z.to_nat (Int.unsigned v'38)) v'37
                      (val_inj
                         (or (nth_val' (Z.to_nat (Int.unsigned v'38)) v'37) (Vint32 v'40))))
      v'36 vhold.
Proof.
  introv Hnvhold.
  intros.
  unfold  RL_RTbl_PrioTbl_P  in *.
  unfolds in H17.
  unfolds in H18.
  intros.
  unfolds in H23.
  assert (  p&ᵢ$ 7  = p&ᵢ$ 7 ) by auto.
  assert (Int.shru p ($ 3) = Int.shru p ($ 3)) by auto.
  assert ( ∘(Int.unsigned (Int.shru p ($ 3))) <> Z.to_nat (Int.unsigned v'38) \/
           ∘(Int.unsigned (Int.shru p ($ 3))) = (Z.to_nat (Int.unsigned v'38)))%nat.
  tauto.

  lets Hy : math_unmap_get_y H1 H6.
  assert ( ∘(Int.unsigned (Int.shru p ($ 3))) <∘OS_EVENT_TBL_SIZE)%nat.
  clear -H22.
  mauto.
  lets Ha : nthval'_has_value H4  H27; eauto.
  destruct Ha as (x&Hnth & Htru).
  lets Hnt : nth_val'_imp_nth_val_int Hnth.
  destruct H26.
  assert ( nth_val ∘(Int.unsigned (Int.shru p ($ 3)))
                   (update_nth_val (Z.to_nat (Int.unsigned v'38)) v'37
                                   (val_inj
                                      (or (nth_val' (Z.to_nat (Int.unsigned v'38)) v'37)
                                          (Vint32 v'40)))) = Some (Vint32 x)).
  eapply nth_upd_neqrev; eauto.
  lets Hb : H23 H24 H25 H28 .
  assert (Int.unsigned (Int.shru p ($ 3))<8). 
  clear - H22.
  mauto.
  remember (Int.shru p ($3)) as px. 
  assert ($ Z.of_nat ∘(Int.unsigned px) = px).
  clear - H29.
  mauto.
  assert (prio_in_tbl p v'37 ).
  unfolds.
  intros.
  subst.
  rewrite H33 in Hnt.
  inverts Hnt.
  auto.
  eapply H; eauto.
  assert (  p&ᵢ$ 7 = v'39 \/  p&ᵢ$ 7 <> v'39).
  tauto.
  destruct H28.
  subst v'39.

  lets Hzzp : int_usigned_tcb_range H22.
  destruct Hzzp.
  remember (Int.shru p ($3)) as px.
  assert (px = v'38).
  clear - Hy  H29 H26.
  gen H26.
  mauto.
  subst v'38.
  subst px.
  assert ( (((Int.shru p ($ 3))<<ᵢ$ 3)+ᵢ(p&ᵢ$ 7)) = p).
  clear -H22.
  mauto.
  rewrite H30 in H12.
  apply nth_val'_imp_nth_val_vptr in H12.
  eexists; eauto.
  assert ( prio_in_tbl p v'37).
  unfolds.
  intros.
  subst.
  lets Hzzp : int_usigned_tcb_range H22.
  destruct Hzzp.
  remember (Int.shru p ($3)) as px.
  remember (p&ᵢ$ 7) as py.
  assert ( px = v'38).
  clear -Hy H30 H26.
  gen H26.
  mauto.
  subst v'38.
  rewrite Hnt in H31.
  inverts H31.
  remember ((val_inj
               (or (nth_val' (Z.to_nat (Int.unsigned px)) v'37)
                   (Vint32 v'40)))) as v.
  unfold val_inj in Heqv.
  rewrite H26 in Hnth.
  rewrite Hnth in Heqv.
  unfold or in Heqv.
  subst v.
  assert ( nth_val ∘(Int.unsigned (px))
                   (update_nth_val (Z.to_nat (Int.unsigned px)) v'37
                                   (Vint32 (Int.or z v'40))) =Some (Vint32 (Int.or z v'40))).
  rewrite <- H26.
  eapply update_nth; eauto.
  lets Hd : H23 H31; eauto.
  rewrite Int.and_commut in Hd.
  rewrite Int.and_or_distrib in Hd.
  lets Hzzps :  math_nth_8_eq_zero'  H13 H29 H28; eauto; try omega.
  rewrite Int.and_commut in Hzzps.
  rewrite Hzzps in Hd.
  rewrite Int.or_zero in Hd.
  rewrite Int.and_commut in Hd.
  auto.
  eapply H; eauto.
Qed.

Lemma TCBList_P_get_node_TCBNode_P :
  forall vltcb head rtbl tcbls vl tid prio st m,
    TCBList_P head vltcb rtbl tcbls ->
    tcbdllseg1_get_node (Vptr tid) head vltcb = Some vl ->
    get tcbls tid = Some (prio, st, m) ->
    TCBNode_P vl rtbl (prio, st, m).
Proof.
  unfold get; simpl.
  inductions vltcb; intros.
  simpl in H; substs.
  rewrite TcbMod.emp_sem in H1; inversion H1.

  unfold TCBList_P in H; fold TCBList_P in H.
  unfold tcbdllseg1_get_node in H0; fold tcbdllseg1_get_node in H0; simp join.
  destruct (beq_val (Vptr tid) (Vptr x)) eqn : eq1.
  inverts H0.
  pose proof H3 tid.
  rewrite H1 in H.
  apply beq_val_true_eq in eq1; inverts eq1.
  rewrite TcbMod.get_sig_some in H.
  destruct (TcbMod.get x1 x); tryfalse.
  substs; auto.
  destruct(V_OSTCBNext a); tryfalse.
  inverts H2.
  eapply IHvltcb; eauto.
  pose proof H3 tid.
  rewrite H1 in H.
  rewrite TcbMod.get_sig_none in H.
  destruct(TcbMod.get x1 tid); tryfalse.
  substs; auto.
  intro; substs.
  rewrite beq_val_true in eq1; tryfalse.
Qed.

Lemma RHL_TCB_Status_Wait_P_rel_edata_stat_rel_edata_tcbstat :
  forall x13 x12 x11 x10 i7 i6 i5 i4 i3 i2 i prio st m eid d rtbl,
    RHL_TCB_Status_Wait_P
      (x13
         :: x12
         :: x11
         :: x10
         :: Vint32 i7
         :: Vint32 i6
         :: Vint32 i5
         :: Vint32 i4
         :: Vint32 i3 :: Vint32 i2 :: Vint32 i :: nil)
      rtbl (prio, st, m) ->
    rel_edata_stat eid d st ->
    rel_edata_tcbstat d i6.
Proof.
  intros.
  unfolds in H; simp join.
  destruct d.
  clear - H2 H0; unfolds in H2.
  simpl in H0; simp join.
  pose proof H2 prio eid x m; clear H2.
  elim H; auto; intros; simp join.
  unfolds in H2; simpl in H2; inverts H2.
  simpl; auto.
  
  clear - H1 H0; unfolds in H1.
  simpl in H0; simp join.
  pose proof H1 prio eid x m; clear H1.
  elim H; auto; intros; simp join.
  unfolds in H2; simpl in H2; inverts H2.
  simpl; auto.

  clear - H3 H0; unfolds in H3.
  simpl in H0; simp join.
  pose proof H3 prio eid x m; clear H3.
  elim H; auto; intros; simp join.
  unfolds in H2; simpl in H2; inverts H2.
  simpl; auto.

  clear - H4 H0; unfolds in H4.
  simpl in H0; simp join.
  pose proof H4 prio eid x m; clear H4.
  elim H; auto; intros; simp join.
  unfolds in H2; simpl in H2; inverts H2.
  simpl; auto.
Qed.

Lemma OSEventTaskRdy_proof:
  forall vl p r ll ct, 
    Some p =
    BuildPreI os_internal OS_EventTaskRdy vl ll OS_EventTaskRdyPre ct ->
    Some r =
    BuildRetI os_internal OS_EventTaskRdy vl ll OS_EventTaskRdyPost ct ->
    exists t d1 d2 s,
      os_internal OS_EventTaskRdy = Some (t, d1, d2, s) /\
      {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init spec.
  
  hoare_split_pure_all.
  simpl in H8, H9, H10; inverts H8; inverts H9; inverts H10.
  hoare unfold.
 
  rename v'13 into egrp.
  rename v'16 into etbl.

(*get the conditions used by following reasoning steps first*)
  assert (
      exists x y erow bitx bity,
        nth_val' (Z.to_nat (Int.unsigned egrp)) OSUnMapVallist = Vint32 y /\
        Int.unsigned y < 8 /\
        nth_val' (Z.to_nat (Int.unsigned y)) etbl = Vint32 erow /\
        Int.unsigned erow < 256 /\ erow <> $ 0 /\
        nth_val' (Z.to_nat (Int.unsigned erow)) OSUnMapVallist = Vint32 x /\
        Int.unsigned x < 8 /\
        nth_val' (Z.to_nat (Int.unsigned y)) OSMapVallist = Vint32 bity /\
        Int.unsigned bity <= 128 /\
        nth_val' (Z.to_nat (Int.unsigned x)) OSMapVallist = Vint32 bitx /\
        Int.unsigned bitx <= 128
    ).
  lets Hx1: osunmapvallist_prop H16; simpljoin.
  apply Zle_bool_imp_le in H11.
  pose proof z_le_7_imp_n x H11.
  lets Hx2: array_int8u_nth_lt_len H9.
  rewrite H15 in Hx2.
  unfold OS_EVENT_TBL_SIZE in Hx2.
  lets Hx2': Hx2 H13; clear Hx2; simpljoin.
  lets Hx3: osunmapvallist_prop H23; simpljoin.
  apply Zle_bool_imp_le in H25.
  lets Hx4: osmapvallist_prop H11.
  lets Hx5: osmapvallist_prop H25.
  simp join.
  exists x1 x x0 x5 x6.
  splits; eauto.
  clear - H11; int auto.
  clear - H23; int auto.
  clear H23 H24 H26 H27.

  eapply rl_tbl_grp_neq_zero; eauto.
  int auto.
  clear - H25; int auto.
  
  destruct H8 as [x [y [erow [bitx [bity H8]]]]].
  destruct H8 as
      [unmap_egrp [y_lt8 [nth_val_etbl [erow_lt256 [erow_ne0 [unmap_erow [x_lt8 [map_y
       [bity_le128 [map_x bitx_le128]]]]]]]]]].
  simp join.
  pose proof lt_8_le_byte_max_unsigned_true y y_lt8 as y_ble_max.
  pose proof lt_8_le_byte_max_unsigned_true x x_lt8 as x_ble_max.
  pose proof lt_256_le_byte_max_unsigned_true erow as erow_ble_max.
  pose proof le_128_le_byte_max_unsigned_true bity bity_le128 as bity_ble_max.
  pose proof le_128_le_byte_max_unsigned_true bitx bitx_le128 as bitx_ble_max.
(**)

  (* y′ =ₑ OSUnMapTbl′[pevent′→OSEventGrp];ₛ *)
  hoare unfold.
  unfold AOSUnMapTbl at 2.
  hoare forward; pure_auto.
  rewrite unmap_egrp.
  rtmatch_solve.

  (*bity′ =ₑ OSMapTbl′[y′];ₛ*)
  unfold AOSMapTbl at 2.
  hoare forward.
  rewrite unmap_egrp. rtmatch_solve; rewrite y_ble_max; auto.
  eauto.
  auto.
  auto.
  simpl; rewrite map_y; rewrite bity_ble_max; auto.
  
  (*x′ =ₑ OSUnMapTbl′[pevent′→OSEventTbl[y′]];ₛ*)
  rewrite unmap_egrp.
  rewrite map_y.
  hoare forward.
  4: eauto.
  rewrite y_ble_max; auto.
  rewrite H15; simpl; auto.
  simpl; rewrite nth_val_etbl; rewrite erow_ble_max; auto.
  auto.
  auto.
  simpl; rewrite unmap_erow; rewrite x_ble_max; auto.

  (*bitx′ =ₑ OSMapTbl′[x′];ₛ*)
  hoare forward.
  2: eauto.
  simpl; rewrite unmap_erow; rewrite x_ble_max; auto.
  auto.
  auto.
  simpl; rewrite map_x; rewrite bitx_ble_max; auto.
  
  (*prio′ =ₑ ((y′ ≪ ′3) +ₑ x′);ₛ*)
  hoare forward.
  rewrite y_ble_max; auto.
  (* rewrite int_ltu_3_iwordsize.
  simpl; intro; tryfalse. *)
  rewrite unmap_erow; rewrite x_ble_max; auto.
  rewrite int_ltu_3_iwordsize.
  simpl val_inj.
  rewrite unmap_erow.
  simpl; intro; tryfalse.

  (*(pevent ′ → OSEventTbl) [y ′] &= ∼ bitx*)
  hoare forward.
  rewrite y_ble_max; auto.
  rewrite H15; simpl; auto.
  simpl; rewrite nth_val_etbl; rewrite erow_ble_max; auto.
  rewrite map_x; rewrite bitx_ble_max; auto.
  rewrite map_x; simpl; intro; tryfalse.
  rewrite nth_val_etbl; rewrite map_x; simpl; intro; tryfalse.
  rewrite y_ble_max; auto.
  apply eq_int; auto.
  rewrite H15; simpl; auto.

  (*If((pevent ′ → OSEventTbl) [y ′] ==ₑ ′0)*)
  hoare forward.
  rewrite y_ble_max; auto.
  rewrite update_nth_val_len_eq; rewrite H15; simpl; auto.
  rewrite nth_val_etbl; rewrite map_x.
  rewrite len_lt_update_get_eq; simpl.
  rewrite unsigned_int_and_not_range; auto.
  omega.
  omega.
  rewrite H15; simpl; auto.
  rewrite nth_val_etbl; rewrite map_x.
  rewrite len_lt_update_get_eq; simpl.
  destruct (Int.eq (erow&ᵢInt.not bitx) ($ 0)); simpl; intro; tryfalse.
  rewrite H15; simpl; auto.
 
  (*pevent ′ → OSEventGrp &= ∼ os_code_defs.bity ′*)
  hoare forward; pure_auto.
  
  (*combine the 2 cases after the IF stmt into one case*)
  rewrite nth_val_etbl; rewrite map_x.
  apply disj_combine with (S:=(
   EX egrp',
     [| RL_Tbl_Grp_P (update_nth_val (Z.to_nat (Int.unsigned y)) etbl
                                     (val_inj (and (Vint32 erow) (val_inj (negint (Vint32 bitx)))))) (Vint32 egrp')  /\ Int.unsigned egrp' <= 255|] **
      <|| v'18 ||>  **
      LV pevent @ os_ucos_h.OS_EVENT ∗ |-> Vptr (v'25, Int.zero) **
      Astruct (v'25, Int.zero) os_ucos_h.OS_EVENT
        (Vint32 i0 :: Vint32 egrp' :: Vint32 i1 :: x2 :: x3 :: x4 :: nil) **
      Aarray v'23 (Tarray Int8u ∘OS_EVENT_TBL_SIZE)
        (update_nth_val (Z.to_nat (Int.unsigned y)) etbl
           (val_inj (and (Vint32 erow) (val_inj (negint (Vint32 bitx)))))) **
      LV prio @ Int8u
      |-> val_inj
            (add
               (val_inj
                  (if Int.ltu ($ 3) Int.iwordsize
                   then Some (Vint32 (y<<ᵢ$ 3))
                   else None))
               (nth_val' (Z.to_nat (Int.unsigned erow)) OSUnMapVallist)
               Int32u Int8u) **
      LV os_code_defs.bitx @ Int8u |-> Vint32 bitx **
      LV os_code_defs.x @ Int8u
      |-> nth_val' (Z.to_nat (Int.unsigned erow)) OSUnMapVallist **
      LV os_code_defs.bity @ Int8u |-> Vint32 bity **
      LV os_code_defs.y @ Int8u |-> Vint32 y **
      Aie false **
      Ais nil **
      Acs (true :: nil) **
      Aisr empisr **
      A_isr_is_prop **
      AEventData
        (Vint32 i0 :: Vint32 egrp' :: Vint32 i1 :: x2 :: x3 :: x4 :: nil) v'17 **
      GAarray OSUnMapTbl (Tarray Int8u 256) OSUnMapVallist **
      GAarray OSMapTbl (Tarray Int8u 8) OSMapVallist **
      AOSRdyTblGrp v'10 v'11 **
      GAarray OSTCBPrioTbl (Tarray os_ucos_h.OS_TCB ∗ 64) v'9 **
      tcbdllseg v'19 v'20 v'21 v'22 v'12 **
      p_local OSLInv ct init_lg **
      LV ptcb @ os_ucos_h.OS_TCB ∗ |-> v' **
      LV msk @ Int8u |-> Vint32 v'6 **
      LV message @ (Void) ∗ |-> v'5 **
      A_dom_lenv
        ((msk, Int8u)
         :: (message, (Void) ∗)
            :: (pevent, os_ucos_h.OS_EVENT ∗)
               :: (ptcb, os_ucos_h.OS_TCB ∗)
                  :: (os_code_defs.x, Int8u)
                     :: (os_code_defs.y, Int8u)
                        :: (os_code_defs.bitx, Int8u)
                           :: (os_code_defs.bity, Int8u)
                              :: (prio, Int8u) :: nil))
  ).
  (*if true*)
  intros.
  sep pauto.
  simpl val_inj.


  split.
  eapply rl_tbl_grp_p_set_hold1; eauto.
  clear - y_lt8; int auto.
  clear - erow_lt256; int auto.
  clear - x_lt8; int auto.
  clear - H13 H22 H23 H15 y_lt8.
  simpl val_inj in *.
  assert(Int.unsigned y < Z.of_nat (length etbl)).
  rewrite H15; int auto.
  rewrite len_lt_update_get_eq in *; auto.
  simpl val_eq in *.
  destruct(Int.eq (erow&ᵢInt.not bitx) ($ 0)) eqn: eq1; auto.
  eapply not_and_p; eauto.
  
  (*if false*)
  intros.
  sep auto.
  simpl val_inj.
  
  split; auto.
  eapply rl_tbl_grp_p_set_hold2; eauto.
  clear - y_lt8; int auto.
  clear - erow_lt256; int auto.
  clear - x_lt8; int auto.
  clear - H23 y_lt8 H15.
  simpl val_inj in H23.
  rewrite len_lt_update_get_eq in *.
  simpl val_eq in H23.
  destruct (Int.eq (erow&ᵢInt.not bitx) ($ 0)) eqn : eq1; auto.
  destruct H23; simpl in H; tryfalse.
  rewrite H15; unfold OS_EVENT_TBL_SIZE; simpl; auto.

  (*ptcb ′ =ₑ OSTCBPrioTbl ′ [prio ′];ₛ*)
  rewrite int_ltu_3_iwordsize.
  rewrite unmap_erow.
  simpl val_inj.

  (*get the relation between event data and event type*)
  hoare_split_pure_all.
  hoare lift 15%nat pre.

  apply hoare_pure_gen with (p:=(rel_edata_etype v'17 i0)).
  intros.
  clear - H11.
  unfold AEventData in H11.
  destruct v'17; sep split in H11; unfolds in H; simpl in H; inverts H; simpl; auto.
  unfolds in H0; simpl in H0; inverts H0; simpl; auto.
  hoare_split_pure_all.
  rename H11 into rel_ed_et.
  rename v'8 into tcbls.
  rename v'9 into ptbl.  

  (*prove prio lt 64*)
  assert(Int.unsigned ((y<<ᵢ$ 3)+ᵢx) < 64) as prio_lt64.
  clear - y_lt8 x_lt8.
  mauto.

  (*prio ble max byte*)
  pose proof lt_64_le_byte_max_unsigned_true ((y<<ᵢ$ 3)+ᵢx) prio_lt64 as prio_ble_max.

  (*prove exist a tid coresponding to prio in tcbls*)
  assert(exists tid st m, get tcbls tid = Some ((y<<ᵢ$ 3)+ᵢx, st, m) /\ rel_edata_stat (v'25, Int.zero) v'17 st) as ex_tid_prio_rel.
  
  assert(($ (Int.unsigned (y<<ᵢ$ 3) + Int.unsigned x)>>ᵢ$ 3) = y) as y_shl3_shr3.
  clear - x_lt8 y_lt8.
  mauto.

  assert(($ (Int.unsigned (y<<ᵢ$ 3) + Int.unsigned x)&ᵢ$ 7) = x) as y_shl3_and7.
  clear - x_lt8 y_lt8.
  mauto.

  unfold R_ECB_ETbl_P in H6; simp join.
  eapply PrioWaitInQ_RLH_ECB_ETbl_P_tcbls_ex; eauto.
  2: unfolds; simpl; auto.
  unfolds.
  clear - prio_lt64 y_lt8 x_lt8 H9 H15 nth_val_etbl unmap_erow erow_lt256 erow_ne0 y_shl3_shr3 y_shl3_and7.
  unfold Int.add in prio_lt64.
  rewrite Int.unsigned_repr in prio_lt64.
  do 3 eexists.
  splits; eauto.
  clear - x_lt8 y_lt8.
  mauto.
  apply nth_val'_imp_nth_val_int.
  rewrite y_shl3_shr3.
  eauto.
  rewrite y_shl3_and7.
  eapply math_8_255_eq; auto.
  clear - erow_lt256.
  int auto.
  clear - y_lt8 x_lt8.
  mauto.
  destruct ex_tid_prio_rel as [tid [st [m [tcbls_tid_prio rel_ed_st]]]].

  (*prove vptr tid indexed by prio in prio table*)
  rename v'7 into vhold.
  assert (
        nth_val' (Z.to_nat (Int.unsigned ((y<<ᵢ$ 3)+ᵢx))) ptbl = Vptr tid /\ tid <> vhold
    ) as nth_val_ptbl_vhold.
  clear - H5 tcbls_tid_prio.
  unfolds in H5; destruct H5; destruct H0.
  eapply H0 in tcbls_tid_prio; simp join; split;  auto.
  
  apply nth_val_nth_val'_some_eq; auto.
  destruct nth_val_ptbl_vhold as [nth_val_ptbl tid_neq_vhold].
  
  (*do the statement*)
  hoare forward.
  rewrite prio_ble_max; auto.
  rewrite nth_val_ptbl.
  simpl; auto.
  
  (*key step: prove tid in tcbdllseg*)
  rename v'19 into head; rename v'20 into headprev;
  rename v'21 into tail; rename v'22 into tailnext;
  rename v'12 into vltcb.

  assert (ptr_in_tcblist (Vptr tid) head vltcb).
  eapply tcbls_get_some_TCBList_P_ptr_in_tcblist; eauto.

  (*get the tcb node pointed by tid*)
  hoare lift 21%nat pre.
  apply tcbdllseg1_init_pre.
  hoare_split_pure_all.
  apply tcbdllseg1_split_pre with (p:=Vptr tid).
  apply ptr_in_tcblist1_init; auto.
  hoare unfold.
  
  (*ptcb ′ → OSTCBDly =ₑ ′0;ₛ*)
  rewrite nth_val_ptbl.
  hoare forward.

  (*ptcb ′ → OSTCBEventPtr =ₑ NULL;ₛ*)
  hoare forward.

  (*ptcb ′ → OSTCBMsg =ₑ message ′;ₛ*)
  hoare forward.
  apply isptr_match; auto.

  (*ptcb ′ → OSTCBStat &= ∼ msk ′;ₛ*)
  hoare forward; pure_auto.
  
  (**)
  (*key step: put the tcb node back into the tcblist*)
  hoare lifts (3::4::nil)%nat pre.
  apply tcbdllseg1_node_join_pre1; auto.
  go.
  
  unfolds; simpl; auto.
  simpl; auto.

  apply tcbdllseg1_to_tcbdllseg_pre1.
  (**)
  
  (*OSRdyGrp ′ =ₑ OSRdyGrp ′ |ₑ os_code_defs.bity ′;ₛ*)
  hoare unfold.
  hoare forward; pure_auto.

  (*OSRdyTbl ′ [os_code_defs.y ′] =ₑ
   OSRdyTbl ′ [os_code_defs.y ′] |ₑ os_code_defs.bitx ′;ₛ*)
  rename v'10 into rtbl.
  rename i8 into rgrp.
  rename H23 into rgrp_le255.
  unfold AOSRdyTbl.
  hoare_split_pure_all.
  destruct H23.
  assert (exists i, nth_val' (Z.to_nat (Int.unsigned y)) rtbl = Vint32 i /\
                    Int.unsigned i <= 255) as nth_val_rtbl.
  assert(Int.unsigned y <= 7).
  clear - y_lt8.
  omega.
  pose proof z_le_7_imp_n y H40.
  lets Hx: array_int8u_nth_lt_len H23.
  rewrite H39 in Hx.
  unfold OS_RDY_TBL_SIZE in Hx.
  lets Hx': Hx H41; clear Hx.
  auto.
  
  destruct nth_val_rtbl as [rrow [nth_val_rtbl rrow_le_255]].

  assert (RL_Tbl_Grp_P (update_nth_val (Z.to_nat (Int.unsigned y)) rtbl
         (Vint32 (Int.or rrow bitx))) (Vint32 (Int.or rgrp bity))) as rl_tbl_grp_new. 

  assert(Int.unsigned y <= 7).
  clear - y_lt8.
  omega.
  assert(Int.unsigned x <= 7).
  clear - x_lt8.
  omega.
  assert(Int.unsigned erow <= 255).
  clear - erow_lt256.
  omega.
  
  lets Hx: rl_tbl_grp_p_set_hold' H17 H16 H9 H15 H23.
  lets Hx1: Hx H39 unmap_egrp H40 nth_val_etbl H42; clear Hx.
  lets Hx2: Hx1 unmap_erow H41 nth_val_ptbl map_x bitx_le128; clear Hx1.
  lets Hx3: Hx2 map_y bity_le128 H14 H37; clear Hx2.
  rewrite nth_val_rtbl in Hx3.
  simpl val_inj in Hx3.
  auto.

  
  assert (forall x, prio_in_tbl x rtbl -> prio_in_tbl x (update_nth_val (Z.to_nat (Int.unsigned y)) rtbl (Vint32 (Int.or rrow bitx)))) as prio_in_tbl_preserv.

  intros.
  eapply prio_in_tbl_preserv; eauto.
  clear - y_lt8 x_lt8.
  mauto.

  assert(((y<<ᵢ$ 3)+ᵢx)&ᵢ$ 7 = x).
  clear - y_lt8 x_lt8.
  mauto.

  rewrite H41.
  clear - map_x x_lt8.
  apply math_mapval_core_prop; auto.  
  
  hoare unfold.
  hoare forward.
  pure_auto.
  rewrite H39; unfold OS_RDY_TBL_SIZE; simpl; auto.
  simpl; rewrite nth_val_rtbl; pure_auto.
  pure_auto.
  rewrite nth_val_rtbl; simpl; intro; tryfalse.
  pure_auto.
  unfold OS_RDY_TBL_SIZE; simpl; auto.
  rewrite H39; unfold OS_RDY_TBL_SIZE; simpl; auto.

  (*RETURN prio ′*)
  hoare_split_pure_all.
  
  hoare forward.
  (*side conditions*)
{
  rewrite prio_ble_max; auto.
}

{
  simpl update_nth_val.
  unfold AOSUnMapTbl, AOSMapTbl.
  sep auto.
}

  eauto.
  auto.
  auto.

{
  lets Hx: rl_rtbl_priotbl_p_hold tid_neq_vhold H4 H17 H16 H9.
  lets Hx' : Hx H15 H23 H39 unmap_egrp nth_val_etbl; clear Hx.
  clear - y_lt8; int auto.
  lets Hx'' : Hx' unmap_erow nth_val_ptbl map_x map_y H14.
  clear - erow_lt256; int auto.
  clear - x_lt8; int auto.
  auto.
  auto.
  clear Hx'.
  lets Hx''':Hx'' H37 rgrp_le255 H23 H39.
  auto.
}

{
  clear - H H22.
  eapply ptr_in_tcbdllseg1_set_node; eauto.
  unfolds; simpl; auto.
}

{
  clear - H38 rl_tbl_grp_new prio_in_tbl_preserv y_lt8 x_lt8 map_x x_lt8 nth_val_rtbl.
  rewrite nth_val_rtbl.
  simpl val_inj.
  split; eauto.
}

{
  clear - rgrp_le255 bity_le128.
  rtmatch_solve.
  apply int_unsigned_or_prop; auto.
}

{
  split.
  eapply array_type_vallist_match_hold; eauto.
  rewrite H39.
  unfold OS_RDY_TBL_SIZE.
  clear - y_lt8.
  mauto.
  rewrite nth_val_rtbl.
  clear - bitx_le128 rrow_le_255.
  rtmatch_solve.
  apply int_unsigned_or_prop'; int auto.
  rewrite update_nth_val_len_eq; auto.
}
eauto.
simpl; auto.
auto.
{
  eapply array_type_vallist_match_int8u_update_hold; eauto.
  clear - y_lt8; int auto.
  clear - erow_lt256; int auto.
}
split; auto.
simpl update_nth_val; pure_auto.
pure_auto.
auto.
eauto.
auto.
auto.
eauto.
{
  lets Hx: TCBList_P_get_node_TCBNode_P H7 H22 tcbls_tid_prio.
  clear - Hx rel_ed_st.
  unfold TCBNode_P in Hx; simp join.
  clear - H2 rel_ed_st.
  unfolds in H2; simp join.
  eapply RHL_TCB_Status_Wait_P_rel_edata_stat_rel_edata_tcbstat; eauto.
}
split.
eauto.
go.
auto.
{
  clear - y_lt8 x_lt8 nth_val_rtbl.
  rewrite nth_val_rtbl.
  simpl val_inj.
  eauto.
}
auto.
Qed.

Close Scope code_scope.
