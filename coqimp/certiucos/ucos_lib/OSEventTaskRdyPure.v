Require Import ucos_include.
Require Import os_ucos_h.
Open Scope code_scope.

Open Scope Z_scope.

Lemma z_le_n_lt':
  forall x1,
    Int.unsigned x1 <= 7 ->
    (Z.to_nat (Int.unsigned x1) < ∘OS_EVENT_TBL_SIZE)%nat.
Proof.
  introv Hx.
  mauto.
Qed.

Lemma pos_to_nat_range_0_7:
  forall z, 0<=z -> z<=7 -> (0<=Z.to_nat z<=7)%nat.
Proof.
  intros.
  split.
  mauto.
  assert (Z.to_nat 7 = 7)%nat.
  clear -z.
  mauto.
  rewrite <- H1.
  eapply Z2Nat.inj_le; omega.
Qed.

  

Lemma osmapvallist_prop:forall x, (Int.unsigned x <=7) -> exists i, nth_val' (Z.to_nat (Int.unsigned x)) OSMapVallist = Vint32 i /\ Int.unsigned i <= 128.
Proof.
  intros.
  lets Hx:Int.unsigned_range x.
  destruct Hx.
  clear H1.
  remember (Int.unsigned x) as z.
  clear Heqz.


  lets Hx: pos_to_nat_range_0_7 H0 H.
  destruct Hx.
  clear H H0.
  remember (Z.to_nat z) as n.
  clear Heqn.
  do 8 (
       destruct n;
       [ 
         simpl;
         eexists;split;eauto;
         rewrite Int.unsigned_repr;
         try solve [omega];
         rewrite max_unsigned_val;omega | ]).
  omega.
Qed.

(* ** ac: Locate "&ᵢ". *)
Open Scope int_scope.
Lemma unsigned_int_and_not_range:
  forall x y,
    Int.unsigned x <= 255 ->
    Int.unsigned y<=255 ->
    Int.unsigned (x &ᵢInt.not y) <=? 255 = true.
Proof.
  intros.
  assert (Int.unsigned (x&ᵢInt.not y) <= Int.unsigned x).
  apply Int.and_le.
  assert (Int.unsigned (x&ᵢInt.not y) <= 255) by omega.
  apply Zle_imp_le_bool; auto.
Qed.


Lemma shl3_add_le_255:
  forall x1 x2, 
    Int.unsigned x1 <= 7 ->
    Int.unsigned x2 <= 7 ->
    Int.unsigned ((x1<<ᵢ$ 3)+ᵢx2) <64.
Proof.
  intros.
  mauto.
Qed.

Lemma shl3_add_le_255':
  forall x1 x2, 
    Int.unsigned x1 <= 7 ->
    Int.unsigned x2 <= 7 ->
    ((Z.to_nat (Int.unsigned ((x1<<ᵢ$ 3)+ᵢx2))) <64) %nat.
Proof.
  intros.
  mauto.
Qed.

Lemma rl_etbl_ptbl_p:
  forall l egrp i4 v'33 x6 v'22 etbl tcbls ptbl etype av,
    array_type_vallist_match Int8u etbl ->
    length etbl = ∘OS_RDY_TBL_SIZE ->
    R_ECB_ETbl_P l
                 (etype
                   :: Vint32 egrp
                   :: Vint32 i4 :: Vptr (v'33, Int.zero) 
                   :: x6 :: v'22 :: nil,
                  etbl) tcbls ->
    RL_Tbl_Grp_P etbl (Vint32 egrp) ->
    R_PrioTbl_P ptbl tcbls av->
    RL_RTbl_PrioTbl_P etbl ptbl av.
Proof.
  introv Ha Hl.
  intros.
  unfolds in H.
  unfolds in H0.
  unfolds in H1.
  unfolds.
  intros.
  unfolds in H3.
  destruct H1.
  destruct H4.
  destruct H.
  destruct H6 as (H6&Htype).
  unfolds in H6.
  unfolds in H.
  assert ( PrioWaitInQ (Int.unsigned p) etbl).
  unfolds.
  remember (Int.shru p ($3)) as px.
  remember (p &ᵢ $ 7) as py.
  lets Hxx : n07_arr_len_ex   ∘(Int.unsigned px ) Ha Hl.
  clear - Heqpx H2.
  subst px.
  mauto.
  destruct Hxx as (vx & Hth & Hvr).
  lets Has : H3 Hth; eauto.
  do 3 eexists; eauto; splits; eauto.
  rewrite Int.repr_unsigned.
  rewrite <- Heqpx.
  eauto.
  rewrite Int.repr_unsigned.
  unfold Int.one.
  subst py.
  eauto.
  destructs H.
  unfolds in Htype.
  destruct Htype.
  apply H in H7.
  unfold V_OSEventType in H7.
  simpl in H7.
  unfolds in H11;simpl in H11;inverts H11.
  assert (Some (V$OS_EVENT_TYPE_Q) = Some (V$OS_EVENT_TYPE_Q)) by auto.
  apply H7 in H11.
  Ltac mytac :=
    heat; jeauto2.
  
  mytac.
  rewrite Int.repr_unsigned in *.
  apply H4 in H11.
  eexists; eauto.
 
  destruct H11.
  unfolds in H11;simpl in H11;inverts H11.
  apply H8 in H7.
  assert (Some (V$OS_EVENT_TYPE_SEM) = Some (V$OS_EVENT_TYPE_SEM)) by auto.
  apply H7 in H11.
  mytac.
  rewrite Int.repr_unsigned in *.
  apply H4 in H11.
  eexists; eauto.
  
  destruct H11.
  unfolds in H11;simpl in H11;inverts H11.
  apply H9 in H7.
  assert (Some (V$OS_EVENT_TYPE_MBOX) = Some (V$OS_EVENT_TYPE_MBOX)) by auto.
  apply H7 in H11.
  mytac.
  rewrite Int.repr_unsigned in *.
  apply H4 in H11.
  eexists; eauto.

  unfolds in H11;simpl in H11;inverts H11.
  apply H10 in H7.
  assert (Some (V$OS_EVENT_TYPE_MUTEX) = Some (V$OS_EVENT_TYPE_MUTEX)) by auto.
  apply H7 in H11.
  mytac.
  rewrite Int.repr_unsigned in *.
  apply H4 in H11.
  eexists; eauto.
Qed.   


Lemma tcb_join_disj_get:
  forall tcbls1 tcbls2 tcbls tid x,
    TcbMod.join tcbls1 tcbls2 tcbls -> 
    TcbMod.get tcbls tid = Some x  ->
    (TcbMod.get tcbls1 tid = Some x /\ TcbMod.get tcbls2 tid = None)
    \/(TcbMod.get tcbls2 tid = Some x /\ TcbMod.get tcbls1 tid = None).
Proof.
  intros.
  pose proof H tid; clear H.
  rewrite H0 in H1.
  destruct (TcbMod.get tcbls1 tid);
  destruct (TcbMod.get tcbls2 tid);
  tryfalse; substs; auto.  
Qed.

Lemma last_eq:
  forall x2 (x4 : vallist),
    (last (x2 ++ x4 :: nil) nil) = x4.
Proof.
  inductions x2; intros.
  simpl; auto.
  simpl.
  rewrite IHx2.
  destruct x2; simpl; auto.
Qed.

Lemma tcbdllseg_isvptr:
  forall l s p1 tail1 ct p z,
    s |= tcbdllseg p1 z tail1 (Vptr ct) l ** p -> exists x, p1 = Vptr x.
Proof.
  inductions l.
  intros.
  unfold tcbdllseg in H; simpl dllseg in H.
  sep split in H.
  eauto.
  intros.
  unfold tcbdllseg in H; simpl dllseg in H.
  unfold node in H.
  sep normal in H.
  sep destruct  H.
  sep split in H.
  mytac.
Qed.


Lemma tcbdllseg_split':
  forall x1 s P v'23 v'32 x2 x3 xx y,
    s |= tcbdllseg (Vptr v'23) xx v'32 (Vptr y) (x1 ++ x2 :: x3) ** P ->
    s |= EX x v'15,
  tcbdllseg (Vptr v'23) xx x (Vptr v'15) x1 **
            tcbdllseg (Vptr v'15) x v'32 (Vptr y) (x2 :: x3)** [|x1<>nil /\ nth_val 0 (last x1 nil) = Some (Vptr v'15) \/ x1 = nil /\ Vptr v'15 = Vptr v'23 |] ** P.
Proof.
  induction x1.
  intros.
  simpl List.app in H.
  unfold tcbdllseg at 1.
  simpl dllseg at 1.
  sep auto.
  unfold tcbdllseg in *.
  intros.
  rewrite <- List.app_comm_cons in H.
  unfold1 dllseg in H.
  sep normal in H.
  sep destruct H.
  sep split in H.
  sep lift 2%nat in H.
  remember (node (Vptr v'23) a OS_TCB ** P) as X.
  lets Hx:tcbdllseg_isvptr  H.
  destruct Hx.
  subst.
  eapply IHx1 in H.
  unfold dllseg at 1.
  fold dllseg.
  sep auto.
  left.
  split;auto.
  pure_auto.

  destruct x1.
  assert (False) by tryfalse.
  tryfalse.
  simpl.
  simpl in H5.
  eauto.

  inverts H5.
  subst.
  simpl.
  auto.
Qed.  

Lemma list_app_neq_nil:
  forall x2 (x4 : vallist),
    (x2 ++ x4 :: nil  <> nil).
Proof.
  destruct x2; auto.
Qed.


(*
(*candidate lemma for MapLib*)  
Lemma join_sig_minus_tcb : forall m a x, TcbMod.get m a = Some x -> TcbMod.join (TcbMod.sig a x) (TcbMod.minus m (TcbMod.sig a x)) m.
Proof.
    intros.
    unfolds; intro.
    rewrite TcbMod.minus_sem.
    destruct(tidspec.beq a a0) eqn : eq1.
    pose proof tidspec.beq_true_eq eq1; substs.
    rewrite TcbMod.get_sig_some.
    rewrite H; auto.
    rewrite TcbMod.get_sig_none.
    destruct (TcbMod.get m a0); auto.
    apply tidspec.beq_false_neq; auto.
Qed.

Lemma tcb_get_ex_tcbjoin:
  forall x tid y,
    TcbMod.get x tid = Some y ->
    exists a,  TcbJoin tid y a x. 
Proof.
  intros.
  unfold TcbJoin.
  exists (TcbMod.minus x (TcbMod.sig tid y)).
  apply join_sig_minus_tcb.
  auto.
Qed.

Lemma in_ptbl_no_ct_get:
  forall s x tid ptbl tcbls tcbls1 tcbls2 p1 l1 rtbl ct curtcb l2 tail1 tail2 P av , 
    ct <> tid ->
    tid <> av ->
    0 <= Int.unsigned x < 64 -> 
    R_PrioTbl_P ptbl tcbls av-> 
    nth_val' ∘(Int.unsigned x) ptbl = Vptr tid ->
    TcbMod.join tcbls1 tcbls2 tcbls ->
    TCBList_P p1 l1 rtbl tcbls1 ->
    TCBList_P (Vptr ct) (curtcb :: l2) rtbl tcbls2 ->
    s |=  tcbdllseg p1 Vnull tail1 (Vptr ct) l1 **  tcbdllseg (Vptr ct) tail1 tail2 Vnull (curtcb :: l2) ** P ->
    (
      
      s|= (EX tail1' l1' tidtcb l1'' tcbls1' tcbls1'',
           tcbdllseg p1 Vnull tail1' (Vptr tid) l1' ** 
                     tcbdllseg (Vptr tid) tail1' tail1 (Vptr ct) (tidtcb::l1'') ** 
                     tcbdllseg (Vptr ct) tail1 tail2 Vnull (curtcb :: l2) ** 
                     [| TCBList_P p1 l1' rtbl tcbls1'|] **
                     [| TCBList_P (Vptr tid) (tidtcb::l1'') rtbl tcbls1'' |] **
                     [| TcbMod.join tcbls1' tcbls1'' tcbls1|] **
                     [| l1 = l1'++(tidtcb::l1'') |] ** P)
       \\//
       (EX tail2' l2' tidtcb l2'' tcbls2' tcbls2'',
        tcbdllseg p1 Vnull tail1 (Vptr ct) l1 ** 
                  tcbdllseg (Vptr ct) tail1 tail2' (Vptr tid) (curtcb :: l2') **
                  tcbdllseg (Vptr tid) tail2' tail2 Vnull (tidtcb::l2'') **
                  [| TCBList_P (Vptr ct) (curtcb::l2') rtbl tcbls2'|] **
                  [| TCBList_P (Vptr tid) (tidtcb::l2'') rtbl tcbls2''|] **
                  [| TcbMod.join tcbls2' tcbls2'' tcbls2|] **
                  [| l2 = l2'++(tidtcb::l2'') |] ** P)
    ).
Proof.
  introv Hneq Hneq2 Hrang Hr Hnth Htc Htp Htp2 Hsa.
  unfolds in Hr.
  destruct Hr as (Hr & _).
  apply nth_val'_imp_nth_val_vptr in Hnth.
  lets Hsk : Hr Hrang Hnth Hneq2.
  mytac.
  lets Hdis : tcb_join_disj_get Htc H.
  destruct Hdis as [Hc1 | Hc2].
  destruct Hc1.
  lets Has : TCBList_P_tcbmod_get Htp; eauto.
  destruct Has.
  mytac.
  left.
  exists Vnull.
  destruct l1.
  tryfalse.
  exists (nil:list vallist).
  exists v.
  exists l1.
  mytac.
  exists (TcbMod.emp) tcbls1.
  unfold tcbdllseg in *.
  simpl dllseg at 1.
  sep pauto.
  eapply TcbMod.join_emp; auto.
  simpl;auto.
  mytac.
  left.
  assert ((x2 ++ x4 :: nil) ++ x3 = x2 ++ x4 :: x3).
  rewrite <- app_assoc.
  simpl.
  auto.
  rewrite <-H4 in Htp.
  lets Hds: TCBList_P_decompose Htp H6.
  destruct x3; tryfalse.
  lets Hps : tcbdllseg_isvptr Hsa.
  mytac.
  rewrite <- H4 in Hsa.
  apply tcbdllseg_split' in Hsa.
  sep normal in Hsa.
  sep destruct Hsa.
  sep split in Hsa.
  destruct H7; mytac; tryfalse.
  rewrite last_eq  in H11.
  unfolds in H6.
  rewrite H6 in H11.
  apply eq_sym in H11.
  inverts H11.
  exists x8  (x2 ++ x4 :: nil) v x3 x6 x7.
  sep pauto.
  assert (x2 ++ x4 :: nil  <> nil) by (apply list_app_neq_nil).
  tryfalse.
  destruct Hc2.
  lets Has : TCBList_P_tcbmod_get Htp2; eauto.
  destruct Has.
  mytac.
  inverts H4.
  tryfalse.
  mytac.
  right.
  assert ((x2 ++ x4 :: nil) ++ x3 = x2 ++ x4 :: x3).
  rewrite <- app_assoc.
  simpl.
  auto.
  sep lift 2%nat in Hsa.
  rewrite H4 in Htp2.
  rewrite <- H7 in Htp2.
  lets Hds: TCBList_P_decompose Htp2 H6.
  destruct x3; tryfalse.
  mytac.
  rewrite H4 in Hsa.
  rewrite <- H7 in Hsa.
  apply tcbdllseg_split in Hsa.
  sep normal in Hsa.
  sep destruct Hsa.
  sep split in Hsa.
  destruct H11; mytac; tryfalse.
  rewrite last_eq  in H12.
  unfolds in H6.
  rewrite H6 in H12.
  apply eq_sym in H12.
  inverts H12.
  destruct x2.
  simpl in H4.
  inverts H4.
  simpl app in Hsa.
  exists x7.  exists (nil :list vallist) v x3 x5 x6.
  sep pauto.
  simpl in H4.
  inverts H4.
  exists x7.
  exists (x2 ++ x4 :: nil) v x3 x5 x6.
  sep pauto.
  rewrite <- app_assoc.
  simpl.
  auto.
  assert (x2 ++ x4 :: nil  <> nil) by (apply list_app_neq_nil).
  tryfalse.
Qed.


Lemma tcb_join_join_joinsig:
  forall x1 x2 x x1' x1'' tid vl x1''1,
    TcbMod.join x1 x2 x ->
    TcbMod.join x1' x1'' x1 -> 
    TcbJoin tid vl x1''1 x1'' -> 
    exists x', TcbJoin tid vl x' x.
Proof.
  intros.
  unfold TcbJoin in *.
  exists (TcbMod.merge (TcbMod.merge x1' x1''1) x2).
  unfolds; intro.
  pose proof H a.
  pose proof H0 a.
  pose proof H1 a.
  rewrite TcbMod.merge_sem.
  rewrite TcbMod.merge_sem.
  destruct (tidspec.beq tid a) eqn : eq1.
  pose proof tidspec.beq_true_eq eq1; substs.
  rewrite TcbMod.get_sig_some.
  rewrite TcbMod.get_sig_some in H4.
  destruct (TcbMod.get x1 a);
  destruct (TcbMod.get x2 a);
  destruct (TcbMod.get x a);
  destruct (TcbMod.get x1' a);
  destruct (TcbMod.get x1'' a);
  destruct (TcbMod.get x1''1 a);
  tryfalse; substs; auto.

  apply tidspec.beq_false_neq in eq1.
  rewrite TcbMod.get_sig_none; auto.
  rewrite TcbMod.get_sig_none in H4; auto.
  destruct (TcbMod.get x1 a);
  destruct (TcbMod.get x2 a);
  destruct (TcbMod.get x a);
  destruct (TcbMod.get x1' a);
  destruct (TcbMod.get x1'' a);
  destruct (TcbMod.get x1''1 a);
  tryfalse; substs; auto.
Qed.

Lemma tcbdllseg_get_last_tcb_ptr:
  forall l s P head headpre tail x ,
    s |= tcbdllseg head headpre tail x l ** P ->
    get_last_tcb_ptr l head = Some x.
Proof.
  inductions l.
  unfold tcbdllseg.
  simpl dllseg.
  intros.
  sep split in H.
  subst.
  simpl.
  auto.
  intros.
  unfold tcbdllseg in *.
  simpl dllseg in *.
  unfold node in H.
  sep normal in H.
  sep destruct H.
  sep split in H.
  sep lift 2%nat in H.
  apply IHl in H.
  mytac.
  simpl.
  destruct l.
  simpl in H.
  inverts H.
  auto.
  unfolds in H.
  auto.
Qed.


Lemma unmap_inrtbl': forall (x y i i0 : int32) (rtbl : vallist),
                       i <> Int.zero ->
                       array_type_vallist_match Int8u rtbl ->
                       length rtbl = ∘OS_RDY_TBL_SIZE ->
                       RL_Tbl_Grp_P rtbl (Vint32 i) ->
                       Int.unsigned i <= 255 ->
                       nth_val' (Z.to_nat (Int.unsigned i)) OSUnMapVallist = Vint32 x ->
                       nth_val' (Z.to_nat (Int.unsigned x)) rtbl = Vint32 i0 ->
                       nth_val' (Z.to_nat (Int.unsigned i0)) OSUnMapVallist = Vint32 y ->
                       prio_in_tbl ($ Int.unsigned ((x<<$ 3)+ᵢy)) rtbl.
Proof.
 introv Hneq Harr Hlen Hrl Hrg Hnth1 Hnth2 Hnth3.
  lets Hrs : math_unmap_range Hrg Hnth1.
  simpl in Hlen.
  unfold Pos.to_nat in Hlen.
  simpl in Hlen.
  rewrite <- Hlen in Hrs.
  assert (Z.to_nat (Int.unsigned x) < length rtbl)%nat by omega.
  lets Hz :  nth_val'_imply_nth_val H Hnth2.
  rewrite Hlen in Hrs.
  assert ( Vint32 i = Vint32 i) by auto.
  lets Hex : Hrl Hrs Hz H0.
  destruct Hex as (Hes1 & Hes2).
  assert (i0 = $ 0 \/   Int.ltu ($ 0) i0 = true ).
  assert (i0 = $ 0 \/ i0 <>$ 0) by tauto.
  destruct H1; auto.
  right.
  eapply int_eq_false_ltu.
  eapply Int.eq_false.
  auto.
  destruct H1.
  subst i0.
  assert (  $ 0 = $ 0) by auto.
  apply Hes1 in H1.
  clear Hes1.
  clear Hes2.
  rewrite Int.unsigned_repr in Hnth3.
  simpl in Hnth3.
  inverts Hnth3.
  unfolds.
  intros.
  subst.
  rewrite shrl_eq in Hz; auto.
  rewrite Int.repr_unsigned in H4.
  rewrite Hz in H4.
  inverts H4.
  rewrite Int.and_commut.
  rewrite Int.and_zero.
  replace ($ 0) with (Int.zero) by auto.
  rewrite  Int.add_zero.
  rewrite Int.repr_unsigned.
  eapply math_prop_int_zero_eq; eauto.
  assert ($ Z.of_nat (Z.to_nat (Int.unsigned x)) = x).
  clear -Hrs.
  apply nat_8_range_conver in Hrs.
  mauto.
  rewrite H2 in H1.
  auto.
  clear -x.
  int auto.

  assert (i0 <> $ 0).
  assert (   i0 <> $ 0 \/    i0 = $ 0) by tauto.
  destruct H2; auto.
  subst i0.
  unfolds in H1.
  rewrite zlt_false in H1.
  inverts H1.
  clear -x.
  int auto.
  apply Hes2 in H1.
  clear Hes1 Hes2.  
  lets Hex : n07_arr_len_ex  Hrs  Harr Hlen.
  destruct Hex as (v & Hex1 & Hex2).
  lets Hzd :  nth_val'_imply_nth_val H Hnth2.
  rewrite Hzd in Hex1.
  inverts Hex1.
  lets Hrzd : math_unmap_get_y Hex2 Hnth3.
  unfolds.
  introv Hx Hy.
  subst.
  introv Hnv.
  lets Heq : math_shrl_3_eq  Hrzd Hrs.
  rewrite Int.repr_unsigned in *.
  rewrite Heq in *.
  unfold nat_of_Z in *.
  erewrite Hnv in Hzd.
  inverts Hzd.
  lets Htra : Hrl Hrs Hnv H0.
  destruct Htra.
  lets Hda : math_8range_eqy Hrs Hrzd.
  rewrite Hda.
  eapply math_8_255_eq; eauto.
Qed.



Lemma not_add_os_stat_q:
   Int.unsigned ($ OS_STAT_Q&Int.not ($ OS_STAT_Q)) = 0.
Proof.
  rewrite Int.and_not_self.
  mauto.
Qed.

Lemma z_le_n_lt:
  forall x1, Int.unsigned x1 <= 7 ->
             (Z.to_nat (Int.unsigned x1) < ∘OS_RDY_TBL_SIZE)%nat.
Proof.
  intros.
  mauto.
Qed.

Lemma os_stat_q_not_and:
  (Int.eq ($ OS_STAT_Q&Int.not ($ OS_STAT_Q)) ($ OS_STAT_RDY) = true).
Proof.
   rewrite Int.and_not_self.
   unfold Int.zero.
   unfold OS_STAT_RDY.
   auto.
Qed.

Lemma tcb_join_join_joinsig':
  forall x1 x2 x x1' x1'' tid vl x1''1,
    TcbMod.join x1 x2 x ->
    TcbMod.join x1' x1'' x2 -> 
    TcbJoin tid vl x1''1 x1'' -> 
    exists x', TcbJoin tid vl x' x.
Proof.
  intros.
  unfold TcbJoin in *.
  exists (TcbMod.merge (TcbMod.merge x1' x1''1) x1).
  unfolds; intro.
  pose proof H a.
  pose proof H0 a.
  pose proof H1 a.
  rewrite TcbMod.merge_sem.
  rewrite TcbMod.merge_sem.
  destruct (tidspec.beq tid a) eqn : eq1.
  pose proof tidspec.beq_true_eq eq1; substs.
  rewrite TcbMod.get_sig_some.
  rewrite TcbMod.get_sig_some in H4.
  destruct (TcbMod.get x1 a);
  destruct (TcbMod.get x2 a);
  destruct (TcbMod.get x a);
  destruct (TcbMod.get x1' a);
  destruct (TcbMod.get x1'' a);
  destruct (TcbMod.get x1''1 a);
  tryfalse; substs; auto.

  apply tidspec.beq_false_neq in eq1.
  rewrite TcbMod.get_sig_none; auto.
  rewrite TcbMod.get_sig_none in H4; auto.
  destruct (TcbMod.get x1 a);
  destruct (TcbMod.get x2 a);
  destruct (TcbMod.get x a);
  destruct (TcbMod.get x1' a);
  destruct (TcbMod.get x1'' a);
  destruct (TcbMod.get x1''1 a);
  tryfalse; substs; auto.
Qed.
*)
Close Scope code_scope.
