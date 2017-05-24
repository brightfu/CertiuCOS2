Require Import ucos_include.
Require Import join_lib_aux.
(*Require Import ucert.
Require Import OSTimeDlyPure.
Require Import OSQPostPure.
Require Import laby.
Require Import mathlib.
*)

Require Import os_ucos_h.
Import DeprecatedTactic.
Open Scope code_scope.
Open Scope Z_scope.
Open Scope int_scope.

Lemma p_local_ostcblist_eq_ct:
  forall s P ct v'36 v'37 v'38 v'39 v'40 v'41 ct' v'44 v'48 lg,
    s|= p_local OSLInv ct lg **
     AOSTCBList' v'36 v'37 v'38 (v'39 :: v'40) v'41 ct' v'44 v'48 ** P ->
    ct' = ct.
Proof.
  intros.
  unfold p_local in H.
  unfold AOSTCBList' in H.
  unfold CurTid in H.
  sep normal in H.
  sep destruct H.
  sep lift 3%nat in H.
  apply disj_split in H.
  destruct H.
  sep normal in H.
  sep destruct H.
  sep split in H.
  destruct H0;subst.
  sep lifts (3::6::nil)%nat in H.
  eapply read_only_merge_vptr in H.
  destruct H;auto.
  sep normal in H.
  sep destruct H.
  sep split in H.
  destruct H0;subst.
  sep lifts (2::6::nil)%nat in H.
  eapply read_only_merge_vptr in H.
  destruct H;auto.
Qed.

Definition highest_rdy prio rtbl :=
  (Int.unsigned prio < 64) /\
  prio_in_tbl prio rtbl /\
  forall prio', 0 <= Int.unsigned prio' < 64-> Int.eq prio prio' = false -> prio_in_tbl prio' rtbl -> Int.ltu prio prio' = true.

Lemma get_highest_rdy:
  forall rgrp rtbl x i0 y,
    prio_in_tbl ($ OS_IDLE_PRIO) rtbl -> 
    array_type_vallist_match Int8u rtbl ->
    length rtbl = ∘OS_RDY_TBL_SIZE->
    RL_Tbl_Grp_P rtbl (Vint32 rgrp) ->
    (Int.unsigned rgrp <= 255) ->
    nth_val' (Z.to_nat (Int.unsigned rgrp)) OSUnMapVallist = Vint32 x ->
    nth_val' (Z.to_nat (Int.unsigned x)) rtbl = Vint32 i0 ->
    nth_val' (Z.to_nat (Int.unsigned i0)) OSUnMapVallist = Vint32 y ->
    highest_rdy ((x<<ᵢ$ 3) +ᵢ y) rtbl.
Proof.
  introv Hpro Harr Hlen Hrl Hrg Hnth1 Hnth2 Hnth3.
  lets Has :  unmap_inrtbl'  Hrg Hnth1 Hnth2 Hnth3; eauto.
  destruct Has.
  unfolds.
  splits; auto.
  introv Hproo Heq Hpri.
  lets Hneq : prio_in_tbl_rgrp_neq_zero Hpro Hrl; try omega; eauto.
  unfold OS_IDLE_PRIO.
  unfold OS_LOWEST_PRIO.
  clear -x.
  int auto.
  unfold Int.ltu.
  rewrite zlt_true; auto.
  clear Hpro.
  unfolds in H0.
  unfolds in Hpri.
  unfolds in Hrl.
  assert (((x<<ᵢ$ 3)+ᵢy)&ᵢ$ 7  = ((x<<ᵢ$ 3)+ᵢy)&ᵢ$ 7 ) by auto.
  assert (Int.shru((x<<ᵢ$ 3)+ᵢy) ($ 3) = Int.shru ((x<<ᵢ$ 3)+ᵢy) ($ 3))  by auto.
  assert ( prio'&ᵢ$ 7 =  prio'&ᵢ$ 7) by auto.
  assert (Int.shru prio' ($ 3) = Int.shru prio' ($ 3)) by auto.
  lets Hrs : math_unmap_range Hrg Hnth1.
  lets Hz :  nth_val'_imply_nth_val  Hnth2.
  simpl in Hlen.
  unfold Pos.to_nat in Hlen; simpl in Hlen.
  rewrite Hlen.
  omega.
  lets Hex : n07_arr_len_ex  Hrs  Harr Hlen.
  destruct Hex as (xv & Hnth & Hrsa).
  rewrite Hz in Hnth.
  inverts Hnth.
  lets Hbs :  math_unmap_range Hrsa Hnth3.
  assert ((Int.unsigned y) < 8).
  eapply nat_8_range_conver; eauto.
  lets Heqb : math_shrl_3_eq  H5 Hrs.
  rewrite <- Heqb  in Hz.
  lets Hasb : H0 H1 H2 Hz.
  lets Hpra :  math_64_le_8  Hproo.
  assert ((0 <= Z.to_nat (Int.unsigned (Int.shru prio' ($ 3))) < 8)%nat).
  eapply  nat_8_range_conver; eauto.
  lets Hex : n07_arr_len_ex  H6 Harr Hlen.
  destruct Hex as (vy & Hnty & Hnht1).
  lets  Hpy : Hpri H3 H4 Hnty.
  assert ( Vint32 rgrp = Vint32 rgrp) by auto.
  lets Hr1 : Hrl Hz H7.
  rewrite Heqb. auto.
  lets Hr2 : Hrl H6 Hnty H7. 
  destruct Hr1 as (Hr11 & Hr12).
  clear Hr11.
  destruct Hr2 as (Hr21 & Hr22).
  clear Hr21.
  rewrite nat_elim in *;try rewrite Heqb;  try  eapply  nat_8_range_conver; eauto.
  lets Hl1 : math_and_shf_ltu_true H Hasb.
  apply Hr12 in Hl1.
  lets Hl2 : math_and_shf_ltu_true Hpy. omega.
  apply Hr22 in Hl2.
  clear Hr12 Hr22.
  clear H7.
  lets Heqa : math_8range_eqy   Hrs H5;eauto.
  rewrite Heqa in *.
  rewrite Heqb in *.
  pose (Int.eq_spec  ((x<<ᵢ$ 3)+ᵢy) prio') as Hnq.
  rewrite Heq in Hnq.
  assert (Int.unsigned ((x<<ᵢ$ 3)+ᵢy) <= Int.unsigned prio').
  assert (xv= $ 0 \/ xv <> $0) by tauto.
  destruct H7.
  subst xv.
  rewrite Int.and_commut in Hasb.
  rewrite Int.and_zero in Hasb.
  assert  ($ 1<<ᵢy <> Int.zero).
  clear - H5.
  mauto.
  tryfalse.
  lets Hrszz :  math_highest_prio_select Hnth3 Hnth1 Hz Hnty;eauto; try omega.
  eapply nat_8_range_conver; eauto.
  rewrite Int.and_commut .
  assert (Int.unsigned ($ 7&ᵢprio') <= Int.unsigned ($ 7)).
  apply Int.and_le.
  rewrite Int.unsigned_repr in H8.
  omega.
  clear- x.
  int auto.
  clear -Hnq H7.
  assert (Int.unsigned ((x<<ᵢ$ 3)+ᵢy) < Int.unsigned prio' \/
          Int.unsigned ((x<<ᵢ$ 3)+ᵢy) = Int.unsigned prio') by omega.
  destruct H; auto.
  clear H7.
  false.
  apply Hnq.
  apply unsigned_inj; auto.
Qed.


Lemma nth_val'2nth_val':
  forall (rtbl : list val) (n : nat) x,
    nth_val' n rtbl = Vptr x -> nth_val n rtbl = Some (Vptr x).
Proof.
  inductions rtbl;intros;simpl in *.
  destruct n;simpl in H;tryfalse.
  destruct n.
  simpl in H.
  subst;auto.
  simpl in H.
  eapply IHrtbl;eauto.
Qed.

Lemma highest_rdy_eq':
  forall prio rtbl ptbl tcbls ct l1 l2 p1 hcurt P s t vhold,
    t <> vhold ->
    prio_in_tbl ($ OS_IDLE_PRIO) rtbl ->
    array_type_vallist_match Int8u rtbl ->
    length rtbl = ∘OS_RDY_TBL_SIZE->
    highest_rdy prio rtbl ->
    nth_val' (Z.to_nat (Int.unsigned prio)) ptbl = Vptr t ->
    R_PrioTbl_P ptbl tcbls vhold -> 
    s |= AOSTCBList p1 (Vptr ct) l1 l2 rtbl hcurt tcbls ** HTCBList tcbls ** (EX tp, GV OSTCBCur @ (Tptr tp) |-r-> Vptr ct) ** P ->
    s |= GV OSTCBCur @ os_ucos_h.OS_TCB ∗ |-> Vptr ct ** AHprio GetHPrio t ** Atrue.
Proof.
  introv Hnvhold Hpr Har Hlen Hhi Hnth Hr Hs.
  unfolds in Hhi.
  destruct Hhi as (Hpro & Hprt & Hfora).
  unfolds in Hr.
  assert (0<=Int.unsigned prio < 64).
  split; auto.
  clear -s.
  int auto.

  lets Hz :  nth_val'2nth_val' Hnth.
  destruct Hr as (Hr1 & Hr2).
  lets Hsa : Hr1 H Hz.
  destruct Hsa as (st & m & Hget);auto.
  unfold AOSTCBList in Hs.
  sep normal in Hs.
  sep destruct Hs.
  sep split in Hs.
  simpljoin1.
  sep lifts (4::1::nil)%nat in Hs.
  eapply read_only_merge_vptr in Hs.
  destruct Hs.
  sep cancel 1%nat 1%nat.
  inverts H4.
  assert (s |= HTCBList tcbls ** Atrue).
  sep auto.
  sep cancel 2%nat 2%nat.
  simpl in H4.
  mytac.
  simpl.
  split; auto.
  destruct H10 as [[]].
  simpl in H4.
  simpl.
  unfolds.
  exists tcbls prio st m.
  split; auto.
  subst o.
  rewrite get_sig.
  remember (dec abtcblsid abtcblsid) as Hb.
  destruct Hb; auto.
  destruct n.
  auto.
  split; auto.
  lets Hab :  TCBList_get_TCBNode_P Hget H1 H2 H3.
  destruct Hab as (vll & Htnode).
  unfolds in Htnode.
  destruct Htnode as (Hv1 & Hv2 & Hrl & Hrt).
  unfolds in Hrt.
  destruct Hrt as (Hrr1 & Hrr2 & Hrr3 & Hrr4).
  unfolds in Hrr1.
  unfolds in Hrr3.
  destruct Hrr3 as (Hwr1 & Hwr2 & Hwr3).
  unfolds in Hwr1.
  assert (RdyTCBblk vll rtbl prio ).
  unfolds.
  splits; auto.
  apply Hrr1 in H9.
  destruct H9 as (Hvos & Hvtc & Hexx).
  destruct Hexx.
  inverts H9.
  splits; auto.
  unfolds; auto.
  intros.
  unfolds in H12.
  destruct st'; tryfalse.
  lets Hasds : TCBList_get_TCBNode_P H10 H1 H2 H3.
  destruct Hasds as (vvll & Hcp).
  unfolds in Hcp.
  destruct Hcp as (Hcp1 & Hcp2 & Hcpr & Hcprt).
  unfolds in Hcprt.
  destruct Hcprt as (_ & Htas & _).
  unfolds in Htas.
  assert ( (prio', rdy, msg') = (prio', rdy, msg')) by auto.
  apply Htas in H13.
  destruct H13.
  unfolds in H13.
  destruct H13.
  unfolds in Hcpr.
  mytac.
  rewrite Hcp2 in H16.
  inverts H16.
  eapply   Hfora; eauto.
  unfolds in H7.
  apply Int.eq_false.

  lets Hress : H7 H9 H10 Hget.
  auto.
Qed.



Lemma highest_rdy_eq:
  forall p1 l1 l2 rtbl hcurt tcbls P i x i0 y ptbl s t ct vhold,
    prio_in_tbl ($ OS_IDLE_PRIO) rtbl -> 
    array_type_vallist_match Int8u rtbl ->
    length rtbl = ∘OS_RDY_TBL_SIZE->
    RL_Tbl_Grp_P rtbl (Vint32 i) ->
    RL_RTbl_PrioTbl_P rtbl ptbl vhold->
    (Int.unsigned i <= 255) ->
    nth_val' (Z.to_nat (Int.unsigned i)) OSUnMapVallist = Vint32 x ->
    nth_val' (Z.to_nat (Int.unsigned x)) rtbl = Vint32 i0 ->
    nth_val' (Z.to_nat (Int.unsigned i0)) OSUnMapVallist = Vint32 y ->
    nth_val' (Z.to_nat (Int.unsigned ((x<<ᵢ$ 3) +ᵢ y))) ptbl = Vptr t -> 
    R_PrioTbl_P ptbl tcbls vhold ->
    s |= AOSTCBList p1 (Vptr ct) l1 l2 rtbl hcurt tcbls ** HTCBList tcbls ** (EX tp,GV OSTCBCur @ tp ∗ |-r-> Vptr ct) ** P ->
    s |= GV OSTCBCur @ os_ucos_h.OS_TCB ∗ |-> Vptr ct ** AHprio GetHPrio t ** Atrue.
Proof.
  intros.
  eapply highest_rdy_eq'; eauto.
  unfolds in H3.
  lets Hx:unmap_inrtbl' H H0 H1 H2.
  lets Hx':Hx H4 H5 H6 H7.
  mytac.
  apply H3 in H12.
  mytac;auto.

  apply nth_val_nth_val'_some_eq in H12.
  rewrite H12 in H8;inverts H8.
  auto.
  split;auto.
  clear.
  lets Hx:Int.unsigned_range  ((x<<ᵢ$ 3)+ᵢy).
  destruct Hx;auto.
  eapply get_highest_rdy; eauto.
Qed.

Lemma hoare_pure_gen : forall P1 P2 (p:Prop) S Q a b c d e f tid,
                         (forall s, s |= P1 -> p) ->
                         {|a,b,c,d,e,f|} |-tid {{P1 ** P2 ** [|p|]}} S {{Q}} ->
                         {|a,b,c,d,e,f|} |-tid {{P1 ** P2}} S {{Q}}.
Proof.
  intros.
  apply backward_rule1 with (p:=(P1 ** P2 ** [|p|])); auto.
  intros.
  sep auto.
  destruct_s s.
  simpl in H1; simpljoin1.
  apply (H (e0, e1, x, i, (i0, i1, c0), x2, a0)); auto.
Qed.

Lemma hoare_pure_gen' : forall P (p:Prop) S Q a b c d e f tid,
                         (forall s, s |= P -> p) ->
                         {|a,b,c,d,e,f|} |-tid {{P ** [|p|]}} S {{Q}} ->
                         {|a,b,c,d,e,f|} |-tid {{P}} S {{Q}}.
Proof.
  intros.
  apply backward_rule1 with (p:=(P ** [|p|])); auto.
  intros.
  sep auto.
  eapply H; eauto.
Qed.

Lemma sc_isched_step:
  forall P v'0 t ct,
    can_change_aop P ->
    P ==> GV OSTCBCur @ (Tptr OS_TCB) |-> Vptr ct ** AHprio GetHPrio t ** Atrue //\\ HCurTCB ct ** [| ct <> t |] ** Atrue ->
    GetHPrio ⊢ <|| (ASSUME sc;;sched);; v'0 ||> ** P ⇒
      <|| (spec_done None;;sched);; v'0 ||>  ** P.
Proof.
  intros.
  apply absinfer_seq;auto.
  apply absinfer_seq;auto.
  apply absinfer_assume;auto.
  intros.
  apply H0 in H1.
  unfolds.
  destruct H1.
  exists ct t.
  destruct_s s.
  simpl in H1.
  simpl in H2.
  

  mytac;simpl;auto.
  eapply join_sig_get;eauto.
  clear -H24 H23.
  unfold GetHPrio in *.
  mytac.
  do 4 eexists;splits;eauto.
  eapply join_get_l;eauto.
Qed.


Lemma nsc_isched_step:
  forall P v'0 t ct,
    can_change_aop P ->
    P ==> GV OSTCBCur @ (Tptr OS_TCB) |-> Vptr ct ** AHprio GetHPrio t ** Atrue //\\ HCurTCB ct ** [| ct =t |] ** Atrue ->
    GetHPrio ⊢ <|| ASSUME nsc;; v'0 ||> ** P ⇒
      <|| spec_done None;;v'0 ||>  ** P.
Proof.
  intros.
  apply absinfer_seq;auto.
  apply absinfer_assume;auto.
  intros.
  apply H0 in H1.
  unfolds.
  destruct H1.
  exists ct t.
  destruct_s s.
  simpl in H1.
  simpl in H2.
  mytac;simpl;auto.
  eapply join_sig_get;eauto.
  clear -H24 H23.
  unfold GetHPrio in *.
  mytac.
  do 4 eexists;splits;eauto.
  eapply join_get_l;eauto.
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
  lets Hx: tidspec.beq_true_eq eq1; substs.
  rewrite TcbMod.set_a_get_a; auto.
  rewrite TcbMod.get_sig_some in H3; tryfalse.
  lets Hx: tidspec.beq_false_neq eq1.
  rewrite TcbMod.get_sig_none in H3; auto.
  destruct (TcbMod.get tcbls' a) eqn : eq2; tryfalse.
  apply H1 in eq2; substs.
  rewrite TcbMod.set_a_get_a'; auto.
Qed.

Lemma tickstep_eqdomtls:
  forall tls qls tls' qls' tls_sub,
    TcbMod.sub tls_sub tls ->
    tickstep' tls qls tls' qls' tls_sub->
    eqdomtls tls tls'.
Proof.
  intros.
  inductions H0.
  unfolds.
  intros.
  split;intros.
  unfolds;unfolds in H0.
  simpljoin1.
  eexists;eauto.
  unfolds in H0.
  unfolds;simpljoin1;eauto.
  assert (eqdomtls tls tls').
  subst tls'.
  eapply tls_get_set_indom;eauto.
  instantiate (1:=(p, st, msg0)).
  eapply TcbMod.get_sub_get;eauto.
  clear - H0.
  pose proof H0 t.
  rewrite TcbMod.get_sig_some in H.
  destruct (TcbMod.get tls_used' t); tryfalse.
  destruct (TcbMod.get tls_used t); tryfalse.
  subst; auto.
  lets Hx: tcbjoinsig_set_sub_sub H0 H2 H.
  apply IHtickstep' in Hx.
  clear -H4 Hx.
  unfold eqdomtls in *.
  intros.
  lets Ha: H4 tid.
  lets Hb: Hx tid.
  clear H4 Hx.
  split;
    destruct Ha,Hb.
  intros.
  apply H in H3.
  apply H1 in H3;auto.
  intros.
  apply H2 in H3.
  apply H0 in H3.
  auto.
Qed.

(*
Lemma absimp_timetick:
  forall P tls qls tls' qls' curtid tm s,
    can_change_aop P ->
    tickstep tls qls tls' qls' ->
    absinfer ( <|| timetick_spec (|nil|);;s ||>
                 ** HECBList qls **  HTCBList tls ** HTime tm **  HCurTCB curtid ** P)
           ( <|| END None;;s ||> **                                                                                                                 
                 HECBList qls'** HTCBList tls' **  HTime (Int.add tm Int.one) **
                 HCurTCB curtid **P).
Proof.
  intros.
  apply absinfer_seq;pauto.
  infer_part1 0%nat.
  eexists; exgamma.
  splits.
  simpl_subst_gamma.
  eapply specstep_merge_emp; constructors.
  unfolds; mytac; try tri_exists_and_solver.
  assert (eqdomO  
        (OSAbstMod.set (OSAbstMod.set O absecblsid (absecblist qls'))
                       abtcblsid (abstcblist tls'))
                  (OSAbstMod.set
        (OSAbstMod.set (OSAbstMod.set O absecblsid (absecblist qls'))
                       abtcblsid (abstcblist tls')) ostmid (ostm (tm+ᵢInt.one)))).
  
  
  eapply abst_get_set_eqdom.
  absdata_solver.
  simpl;auto.
  assert (eqdomO  (OSAbstMod.set O absecblsid (absecblist qls')) (OSAbstMod.set (OSAbstMod.set O absecblsid (absecblist qls'))
                                                                                abtcblsid (abstcblist tls'))).
  eapply abst_get_set_eqdom.
  absdata_solver.
  simpl.
  
  eapply tickstep_eqdomtls;eauto.
  apply TcbMod.sub_refl.
  assert (eqdomO O (OSAbstMod.set O absecblsid (absecblist qls'))).
  eapply abst_get_set_eqdom.
  absdata_solver.
  simpl;auto.
  eapply ruleLib.eqdomO_trans;eauto.
  eapply ruleLib.eqdomO_trans;eauto.
  assert (tidsame (OSAbstMod.set (OSAbstMod.set O absecblsid (absecblist qls'))
                                 abtcblsid (abstcblist tls'))
                  (OSAbstMod.set
                     (OSAbstMod.set (OSAbstMod.set O absecblsid (absecblist qls'))
                                    abtcblsid (abstcblist tls')) ostmid (ostm (tm+ᵢInt.one)))).
  tidsame_solver.
  assert (tidsame O
                  (OSAbstMod.set (OSAbstMod.set O absecblsid (absecblist qls'))
                                 abtcblsid (abstcblist tls'))).
  tidsame_solver.
  eapply tidsame_trans;eauto.
  eapply OSAbstMod.disj_emp_r;eauto.
  repeat simpl_absdata_sep; sep auto.
Qed.


Lemma absimp_toy:
  forall P tls qls curtid tm s,
    can_change_aop P ->
    absinfer ( <||toyint_spec (|nil|) ;; s||>
                 ** HECBList qls **  HTCBList tls ** HTime tm **  HCurTCB curtid ** P)
           ( <||END None;;s ||> **                                                                                                                 
                 HECBList qls** HTCBList tls **  HTime tm **
                 HCurTCB curtid **P).
Proof.
  intros.
  apply absinfer_seq;pauto.
  infer_solver 0%nat.
Qed.
 *)

Lemma prio_neq_tid_neq:
  forall p1 l1 l2 rtbl hcurt tcbls P i x i0 y ptbl s t ct vhold
         next pre eptr msg dly st p_ct tcbx tcby tcbbitx tcbbity,
    prio_in_tbl ($ OS_IDLE_PRIO) rtbl -> 
    array_type_vallist_match Int8u rtbl ->
    length rtbl = ∘OS_RDY_TBL_SIZE->
    RL_Tbl_Grp_P rtbl (Vint32 i) ->
    RL_RTbl_PrioTbl_P rtbl ptbl vhold->
    (Int.unsigned i <= 255) ->
    nth_val' (Z.to_nat (Int.unsigned i)) OSUnMapVallist = Vint32 x ->
    nth_val' (Z.to_nat (Int.unsigned x)) rtbl = Vint32 i0 ->
    nth_val' (Z.to_nat (Int.unsigned i0)) OSUnMapVallist = Vint32 y ->
    nth_val' (Z.to_nat (Int.unsigned ((x<<ᵢ$ 3) +ᵢ y))) ptbl = Vptr t -> 
    R_PrioTbl_P ptbl tcbls vhold ->
    Int.eq ((x<<ᵢ$ 3)+ᵢy) p_ct = false ->
    s |= AOSTCBList p1 (Vptr ct) l1
      ((next
          :: pre
          :: eptr
          :: msg
          :: Vint32 dly
          :: Vint32 st
          :: Vint32 p_ct
          :: Vint32 tcbx
          :: Vint32 tcby
          :: Vint32 tcbbitx :: Vint32 tcbbity :: nil)::l2) rtbl hcurt tcbls ** HTCBList tcbls ** P ->
    ct <> t.
Proof.
  intros.
  intro.
  subst t.
  unfolds in H9.
  destruct H9 as (Ha&Hb&Hc).  
  unfolds in H3.
  lets Has :  unmap_inrtbl' H H0 H5 H6 H7; eauto.
  destruct Has.
  assert (0<= Int.unsigned ((x<<ᵢ$ 3)+ᵢy)).
  lets Hran: Int.unsigned_range ((x<<ᵢ$ 3)+ᵢy).
  destruct Hran;auto.
  lets Hx: H3 H12.
  split;auto.
  destruct Hx.
  destruct H14.
  lets Hx: nth_val'2nth_val' H8.
  rewrite H14 in Hx.
  inverts Hx.
  lets Hx: Ha H14 H15.
  split;auto.
  destruct Hx.
  destruct H16.
  unfold AOSTCBList in H11.
  sep normal in H11.
  sep destruct H11.
  sep split in H11.
  simpl in H20.
  simpljoin1.
  inverts H20.
  inverts H25.
  unfolds in H23.
  destruct x9.
  destruct p.
  simpljoin1.
  unfolds in H23.
  simpl in H23.
  inverts H23.
  lets Hx:tcbjoin_get_a_my H22.
  lets Hy:TcbMod.join_get_get_r H18 Hx.
  unfold get in H16; simpl in H16.
  rewrite H16 in Hy.
  inverts Hy.
  clear -H10.
  int auto.
Qed.

Lemma prio_eq_tid_eq:
  forall p1 l1 l2 rtbl hcurt tcbls P i x i0 y ptbl s t ct vhold
         next pre eptr msg dly st p_ct tcbx tcby tcbbitx tcbbity,
    prio_in_tbl ($ OS_IDLE_PRIO) rtbl -> 
    array_type_vallist_match Int8u rtbl ->
    length rtbl = ∘OS_RDY_TBL_SIZE->
    RL_Tbl_Grp_P rtbl (Vint32 i) ->
    RL_RTbl_PrioTbl_P rtbl ptbl vhold->
    (Int.unsigned i <= 255) ->
    nth_val' (Z.to_nat (Int.unsigned i)) OSUnMapVallist = Vint32 x ->
    nth_val' (Z.to_nat (Int.unsigned x)) rtbl = Vint32 i0 ->
    nth_val' (Z.to_nat (Int.unsigned i0)) OSUnMapVallist = Vint32 y ->
    nth_val' (Z.to_nat (Int.unsigned ((x<<ᵢ$ 3) +ᵢ y))) ptbl = Vptr t -> 
    R_PrioTbl_P ptbl tcbls vhold ->
    Int.eq ((x<<ᵢ$ 3)+ᵢy) p_ct = true ->
    s |= AOSTCBList p1 (Vptr ct) l1
      ((next
          :: pre
          :: eptr
          :: msg
          :: Vint32 dly
          :: Vint32 st
          :: Vint32 p_ct
          :: Vint32 tcbx
          :: Vint32 tcby
          :: Vint32 tcbbitx :: Vint32 tcbbity :: nil)::l2) rtbl hcurt tcbls ** HTCBList tcbls ** P ->
    ct = t.
Proof.
  intros.
  assert (((x<<ᵢ$ 3)+ᵢy) = p_ct).
  clear -H10.
  lets Hx:Int.eq_spec ((x<<ᵢ$ 3)+ᵢy) p_ct.
  rewrite H10 in Hx;auto.
  subst p_ct.
  unfolds in H9.
  destruct H9 as (Ha&Hb&Hc).  
  unfolds in H3.
  lets Has :  unmap_inrtbl' H H0 H5 H6 H7; eauto.
  destruct Has.
  assert (0<= Int.unsigned ((x<<ᵢ$ 3)+ᵢy)).
  lets Hran: Int.unsigned_range ((x<<ᵢ$ 3)+ᵢy).
  destruct Hran;auto.
  lets Hx: H3 H12.
  split;auto.
  destruct Hx.
  destruct H14.
  lets Hx:nth_val'2nth_val' H8.
  rewrite H14 in Hx.
  inverts Hx.
  lets Hx: Ha H14 H15.
  split;auto.
  destruct Hx.
  destruct H16.
  unfold AOSTCBList in H11.
  sep normal in H11.
  sep destruct H11.
  sep split in H11.
  simpl in H20.
  simpljoin1.
  inverts H20.
  inverts H25.
  unfolds in H23.
  destruct x9.
  destruct p.
  simpljoin1.
  unfolds in H23.
  simpl in H23.
  inverts H23.
  lets Hx:tcbjoin_get_a_my H22.
  lets Hy:TcbMod.join_get_get_r H18 Hx.
  lets Hm: Hb H16.
  lets Hn: Hb Hy.
  simpljoin1.
  rewrite H28 in H23;inverts H23;auto.
Qed.


Lemma backward_1 :
  forall P P' Q S spec sd linv I r ri s tid,
    P ==> P' ->
    {|spec , sd, I, linv, r, ri|}|-tid {{P'**Q}}s {{S}} ->
                                   {|spec , sd, I, linv, r, ri|}|-tid {{P**Q}}s {{S}}.      
Proof.
  intros.
  eapply backward_rule1 with (p:=P'**Q).
  intros.
  sep auto.
  auto.
Qed.

Lemma gvar_off_zero:
  forall s P l x t,
    s |= G&x @ t == l ** P ->
    exists b, l = (b,Int.zero).
Proof.
  intros.
  destruct_s s.
  destruct l.
  simpl in H;simpljoin1.
  eexists;eauto.
  rewrite <- Int.unsigned_zero in H1.
  apply unsigned_inj in H1.
  subst i2;eauto.
Qed.

Lemma dllseg_head_null_elim:
  forall s v'8 v'11 v'13 x y z P,
    s |= dllseg Vnull v'8 v'11 Vnull v'13 x y z ** P ->  v'13= nil /\ v'8 = v'11.
Proof.
  intros.
  unfold dllseg in *.
  destruct v'13.
  sep split in H.
  auto.
  sep split in H.
  tryfalse.
Qed.


Lemma dllseg_head_isptr' :
  forall l v1 v2 v3 v4  t  n p P s, s |= dllseg v1 v2  v3 (Vptr v4) l t n p ** P  -> isptr v1.
Proof.
  inductions l. 
  intros.
  simpl in H.
  simpljoin1 ; unfolds; simpl; auto.
  right;eexists;auto.
  intros.
  unfold dllseg in H.
  fold dllseg in H.
  sep destroy H.
  right.
  unfold node in H3.
  sep destroy H3.
  simpljoin1.
  eauto.
Qed.

Lemma xx:
  forall a b c a' b' c' l l',(logic_isr a
                                        :: logic_is b
                                        :: logic_val c::l) = (  logic_isr a'
                                                                          :: logic_is b'
                                                                          :: logic_val c' :: l')-> c=c'.
Proof.
  intros.
  inverts H;auto.
Qed.


Lemma xxx:forall P s v'9 v'10,getisr (gettaskst s) =  isrupd v'9 0%nat false ->  getis (gettaskst s) = 0%nat :: v'10 ->  getie (gettaskst s) = false -> ( forall j : nat,
                                                                                                                                                            (0 <= j < gettopis (OSTickISR :: v'10))%nat ->
                                                                                                                                                            isrupd v'9 OSTickISR true j = false) -> s|=P ->s|= (isr_inv //\\ Aie false) ** P.
Proof.
  intros.
  destruct_s s.
  simpl.

  simpl in H,H0.
  exists empmem m m empabst o o.
  splits;simpljoin1.
  split.
  eexists;splits;simpljoin1.
  splits; eauto.
  unfolds; auto.

  exists 0%nat.
  splits;simpljoin1.
  simpl;auto.
  splits; auto.
  unfolds; auto.
  
  intros.
  omega.
  unfolds; auto.
  
  simpl in H1.
  splits; auto.
  unfolds; auto.
  auto.
Qed.

Lemma xxxx: forall s P v'10, getis (gettaskst s) = 0%nat :: v'10->
                             s |= P ->
                             s |= [|hd_error (0%nat :: v'10) = Some 0%nat|] **
                               Ais (0%nat :: v'10) ** P.
Proof.
  intros.
  destruct_s s.
  simpl.
  exists empmem m m empabst o o.
  splits;simpljoin1.
  simpl; splits; auto.
  unfolds; auto.
  
  exists empmem m m empabst o o.
  splits; auto.
  apply map_join_comm.
  apply map_join_emp.
  apply map_join_comm.
  apply map_join_emp.

  simpl in H; splits; auto.
  unfolds; auto.
Qed.

Lemma xxxxx: forall s v'9 P,  getisr (gettaskst s) = isrupd v'9 0%nat false -> s|=P ->s
                                                                                        |= ([|isrupd v'9 0%nat false 0%nat = false|] //\\
                                                                                                                                     Aisr (isrupd v'9 0%nat false)) ** P.

Proof.
  intros.
  destruct_s s.
  simpl.
  exists empmem m m empabst o o.
  splits; simpljoin1.
  split.
  unfold isrupd.
  assert (beq_nat 0 0 =true) by auto.
  rewrite H1.
  unfold emposabst.
  auto.
  unfold emposabst; simpl in H;auto.
  auto.
Qed.



Lemma ostcbcur_tp_os_tcb:
  forall P s tp v,
    s |= OSInv **  GV OSTCBCur @ tp ∗ |-r-> Vptr v ** P -> s |= OSInv **  GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr v ** P .
Proof.
  intros.
  unfold OSInv in H.
  unfold AOSTCBList' in H.
  sep normal in H.
  sep destruct H.
  sep lift 9%nat in H.
  apply disj_split in H.
  destruct H.
  sep normal in H.
  sep destruct H.
  sep split in H.
  sep lifts (3::23::nil)%nat in H.
  destruct H0.
  subst x6.
  apply read_only_merge_vptr in H.
  destruct H.
  subst.
  sep cancel 1%nat 2%nat.
  unfold OSInv.
  sep normal.
  sep eexists.
  sep semiauto;eauto.
  unfold AOSTCBList'.
  sep lift 7%nat.
  apply disj_split.
  left.
  sep auto.
  eauto.
  eauto.
  auto.
  sep normal in H.
  sep destruct H.
  sep split in H.
  sep lifts (2::23::nil)%nat in H.
  destruct H0;subst.
  apply read_only_merge_vptr in H.
  destruct H.
  subst.
  sep cancel 1%nat 2%nat.
  unfold OSInv.
  sep normal.
  sep eexists.
  sep semiauto;eauto.
  unfold AOSTCBList'.
  sep lift 7%nat.
  apply disj_split.
  right.
  sep auto.
Qed.




Lemma task_del_noexists:
  forall v'9 v'7 v'13 ct v'21 v'10 v'11 P xx xxx, 
    dllseg v'7 xx v'13 (Vptr ct) v'9 OS_TCB_flag V_OSTCBPrev V_OSTCBNext **
           dllseg (Vptr ct) v'13 v'21 Vnull (v'10 :: v'11) OS_TCB_flag V_OSTCBPrev
           V_OSTCBNext **
           dllsegflag v'7 xxx (v'9 ++ v'10 :: v'11) V_OSTCBNext **  LINV OSLInv ct (logic_val (V$ 0) :: nil) ** P ==> Afalse.
Proof.
  inductions v'9.
  intros.
  simpl dllseg in H.
  simpl dllsegflag in H.
  unfold LINV in H.
  unfold OSLInv in H.
  unfold node in H.
  sep normal in H.
  sep destruct H.
  sep split in H.
  destruct H3.
  subst.
  destruct H0.
  inverts H0.
  struct_type_vallist_match_elim.
  unfolds in H2;simpl in H2;unfolds in H4;simpl in H4;unfolds in H5;simpl in H5.
  inverts H3.
  inverts H2.
  inverts H5.
  inverts H6.
  inverts H4.
  unfold get_off_addr in H.
  simpl fst in H.
  sep lift 2%nat in H.
  apply flag_merege_false in H.
  tryfalse.

  intros.
  simpl dllseg at 1 in H.
  simpl dllsegflag in H.
  sep normal in H.
  sep destruct H.
  sep split in H.
  sep remember (2::4::5::6::7::nil)%nat in H.
  sep remember (6::nil)%nat in H.
  simpl in H.
  mytac.
  sep lifts (2::3::nil)%nat in H11.
  rewrite H1 in H2;inverts H2.
  eapply IHv'9 in H11.
  simpl in H11.
  tryfalse.
Qed.


Ltac unfolddef:=
  try
    (unfold code in *;unfold cont in *;unfold tid in *;
     unfold Maps.sub in *;unfold disjoint in *;unfold osabst in *).

Lemma os_core_common_map1 :
  forall (A B T : Type) (MC : PermMap A B T) tcbls t x x0 x3 x2,
    usePerm = false ->
    get tcbls t = Some x ->
    t <> x0 ->
    join (sig x0 x3) x2 tcbls ->
    get x2 t = Some x.
  hy.
Qed.

Lemma tcblist_get_TCBNode_P
: forall (l: list vallist) (tcbls : TcbMod.map) (head : val) (rtbl : vallist)
         (t : tidspec.A) x ,
    get tcbls t = Some x ->
    TCBList_P head l rtbl tcbls ->
    exists vl, TCBNode_P vl rtbl x.
Proof.
  inductions l.
  intros.
  simpl in H0.
  subst.
(* ** ac:   SearchAbout (get _ _ = None). *)
  rewrite map_emp_get in H.
  tryfalse.
  intros.
  simpl in H0.
  mytac.
  assert (t = x0 \/ t <> x0) by tauto.
  destruct H0;subst.
  exists a;auto.
  assert (x=x3).
  clear -H H2.
  assert (join (sig x0 x3) x2 tcbls).
  auto.
  clear H2.
  assert (get (sig x0 x3) x0 = Some x3).
  apply map_get_sig.
  eapply join_get_l in H0;eauto.
  unfolddef.
  unfolds in H0.
  simpl in H0.
  unfolds in H.
  simpl in H.
  rewrite H in H0;inverts H0.
  auto.
  subst x3;auto.
  eapply IHl with (tcbls:= x2);eauto.
  instantiate (1:= t).
  clear -H H2 H0.
  assert (join (sig x0 x3) x2 tcbls);auto.
  clear H2.

  eapply os_core_common_map1; ica.
Qed.  


Lemma highest_rdy_eq_dead':
  forall prio rtbl ptbl tcbls ct l p1 P s t vhold tail,
    t <> vhold ->
    prio_in_tbl ($ OS_IDLE_PRIO) rtbl ->
    array_type_vallist_match Int8u rtbl ->
    length rtbl = ∘OS_RDY_TBL_SIZE->
    highest_rdy prio rtbl ->
    nth_val' (Z.to_nat (Int.unsigned prio)) ptbl = Vptr t ->
    R_PrioTbl_P ptbl tcbls vhold -> 
    s |= tcblist p1 Vnull tail Vnull l rtbl tcbls ** HTCBList tcbls ** GV OSTCBCur @ (Tptr OS_TCB) |-> Vptr ct ** P ->
    s |= GV OSTCBCur @ os_ucos_h.OS_TCB ∗ |-> Vptr ct ** AHprio GetHPrio t ** Atrue.
Proof.
  introv Hnvhold Hpr Har Hlen Hhi Hnth Hr Hs.
  unfolds in Hhi.
  destruct Hhi as (Hpro & Hprt & Hfora).
  unfolds in Hr.
  assert (0<=Int.unsigned prio < 64).
  split; auto.
  clear -s.
  int auto.

  lets Hz :  nth_val'2nth_val' Hnth.
  destruct Hr as (Hr1 & Hr2).
  lets Hsa : Hr1 H Hz.
  destruct Hsa as (st & m & Hget);auto.
  unfold AOSTCBList in Hs.
  sep normal in Hs.
  sep destruct Hs.
  sep split in Hs.
  simpljoin1.
  sep cancel 3%nat 1%nat.
  assert (s |= HTCBList tcbls ** Atrue).
  sep auto.
  sep cancel 2%nat 2%nat.
  simpl in H3.
  mytac.
  simpl.
  split; auto.
  destruct H4 as [[]].
  simpl in H3.
  simpl.
  unfolds.
  exists tcbls prio st m.
  split; auto.
  subst o.
  rewrite get_sig.
  remember (dec abtcblsid abtcblsid) as Hb.
  destruct Hb; auto.
  destruct n.
  auto.
  split; auto.

  unfold tcblist in Hs.
  sep normal in Hs.
  sep split in Hs.
  lets Hab :  tcblist_get_TCBNode_P Hget H4.
  destruct Hab as (vll & Htnode).
  unfolds in Htnode.
  destruct Htnode as (Hv1 & Hv2 & Hrl & Hrt).
  unfolds in Hrt.
  destruct Hrt as (Hrr1 & Hrr2 & Hrr3 & Hrr4).
  unfolds in Hrr1.
  unfolds in Hrr3.
  destruct Hrr3 as (Hwr1 & Hwr2 & Hwr3).
  unfolds in Hwr1.
  assert (RdyTCBblk vll rtbl prio ).
  unfolds.
  splits; auto.
  apply Hrr1 in H6.
  destruct H6 as (Hvos & Hvtc & Hexx).
  destruct Hexx.
  inverts H6.
  splits; auto.
  unfolds; auto.
  intros.
  unfolds in H8.
  destruct st'; tryfalse.
  lets Hasds : tcblist_get_TCBNode_P H7 H4.
  destruct Hasds as (vvll & Hcp).
  unfolds in Hcp.
  destruct Hcp as (Hcp1 & Hcp2 & Hcpr & Hcprt).
  unfolds in Hcprt.
  destruct Hcprt as (_ & Htas & _).
  unfolds in Htas.
  assert ( (prio', rdy, msg') = (prio', rdy, msg')) by auto.
  apply Htas in H9.
  destruct H9.
  unfolds in H9.
  destruct H9.
  unfolds in Hcpr.
  mytac.
  rewrite Hcp2 in H12.
  inverts H12.
  eapply Hfora; eauto.
  apply Int.eq_false.
  unfolds in H2.
  lets Hress : H2 H6 H7 Hget.
  auto.
Qed.

Lemma highest_rdy_eq_dead
: forall (p1 : val) (l : list vallist) (rtbl : vallist)
         (tcbls : TcbMod.map) (P : asrt) 
         (i x i0 y : int32) (ptbl : vallist) (s : RstateOP)
         (t ct vhold : addrval) tail,
    prio_in_tbl ($ OS_IDLE_PRIO) rtbl ->
    array_type_vallist_match Int8u rtbl ->
    length rtbl = ∘ OS_RDY_TBL_SIZE ->
    RL_Tbl_Grp_P rtbl (Vint32 i) ->
    RL_RTbl_PrioTbl_P rtbl ptbl vhold ->
    Int.unsigned i <= 255 ->
    nth_val' (Z.to_nat (Int.unsigned i)) OSUnMapVallist = Vint32 x ->
    nth_val' (Z.to_nat (Int.unsigned x)) rtbl = Vint32 i0 ->
    nth_val' (Z.to_nat (Int.unsigned i0)) OSUnMapVallist = Vint32 y ->
    nth_val' (Z.to_nat (Int.unsigned ((x<<ᵢ$ 3) +ᵢ  y))) ptbl = Vptr t ->
    R_PrioTbl_P ptbl tcbls vhold ->
    s
      |= tcblist p1 Vnull tail Vnull l rtbl tcbls **
      HTCBList tcbls ** GV OSTCBCur @ OS_TCB ∗ |-> Vptr ct ** P ->
    s |= GV OSTCBCur @ OS_TCB ∗ |-> Vptr ct ** AHprio GetHPrio t ** Atrue.
Proof.
  intros.
  eapply highest_rdy_eq_dead'; eauto.
  unfolds in H3.
  lets Hx:unmap_inrtbl' H H0 H1 H2.
  lets Hx':Hx H4 H5 H6 H7.
  mytac.
  apply H3 in H12.
  mytac;auto.
  apply nth_val_nth_val'_some_eq in H12.
  rewrite H12 in H8;inverts H8.
  auto.
  split;auto.
  clear.
  lets Hx:Int.unsigned_range  ((x<<ᵢ$ 3)+ᵢy).
  destruct Hx;auto.
  eapply get_highest_rdy; eauto.
Qed.

Lemma highest_ct_dead_neq
: forall (p1 : val) (l : list vallist) (rtbl : vallist)
         (tcbls : TcbMod.map) (P : asrt) 
         (i x i0 y : int32) (ptbl : vallist) (s : RstateOP)
         (t ct vhold : addrval) tail,
    prio_in_tbl ($ OS_IDLE_PRIO) rtbl ->
    array_type_vallist_match Int8u rtbl ->
    length rtbl = ∘ OS_RDY_TBL_SIZE ->
    RL_Tbl_Grp_P rtbl (Vint32 i) ->
    RL_RTbl_PrioTbl_P rtbl ptbl vhold ->
    Int.unsigned i <= 255 ->
    nth_val' (Z.to_nat (Int.unsigned i)) OSUnMapVallist = Vint32 x ->
    nth_val' (Z.to_nat (Int.unsigned x)) rtbl = Vint32 i0 ->
    nth_val' (Z.to_nat (Int.unsigned i0)) OSUnMapVallist = Vint32 y ->
    nth_val' (Z.to_nat (Int.unsigned ((x<<ᵢ$ 3) +ᵢ  y))) ptbl = Vptr t ->
    R_PrioTbl_P ptbl tcbls vhold ->
    s
      |= tcblist p1 Vnull tail Vnull l rtbl tcbls ** TCB_Not_In (Vptr ct) p1 l **
      HTCBList tcbls ** GV OSTCBCur @ OS_TCB ∗ |-> Vptr ct ** P ->
    ct <> t.
Proof.
  intros.
  intro.
  subst t.
  unfold TCB_Not_In in H10.
  sep split in H10.
  mytac.
  inverts H12.
  destruct H11.
  assert (highest_rdy ((x<<ᵢ$ 3) +ᵢ y) rtbl).
  eapply get_highest_rdy;eauto.
  unfolds in H11.
  unfolds in H3.
  mytac.
  unfold tcblist in *.
  sep split in H10.
  clear H10.
  unfolds in H9.
  mytac.
  lets Hx:H3 H12.
  split;auto.
  remember ((x<<ᵢ$ 3) +ᵢ  y) as X.
  clear HeqX.
  int auto.
  mytac.
  lets Hx:H9 H16 H17.
  split;auto.
  remember ((x<<ᵢ$ 3) +ᵢ  y) as X.
  clear HeqX.
  int auto.
  mytac.
  apply nth_val'_imp_nth_val_vptr in H8.
  rewrite H8 in H16;inverts H16.
  clear -H14 H18.
  gen p1 tcbls.
  inductions l;intros.

  simpl in H14.
  subst.
  rewrite map_emp_get in H18.
  tryfalse.
  simpl in H14.
  mytac.
  destruct x1.
  simpl.
  remember (beq_pos x0 b && Int.eq Int.zero i) as X.
  destruct X.
  auto.
  rewrite H0.
  eapply IHl;eauto.
  eapply join_sig_get_neq;eauto.
  Lemma addr_eq_false_neq:
    forall x a y b,
      false = beq_pos x a && Int.eq y b ->
      (x,y)<>(a,b).
  Proof.
    intros.
    intro.
    inverts H0.
    rewrite beq_pos_Pos_eqb_eq in H.
    assert ((a =? a)%positive  = true).
    apply Pos.eqb_eq;auto.
    assert (Int.eq b b =true).
    clear;int auto.
    rewrite H0,H1 in H.
    simpl in H;tryfalse.
  Qed.
  eapply addr_eq_false_neq;eauto.
Qed.



Lemma dead_not_ready:
  forall  (rtbl : vallist)
          (tcbls : TcbMod.map)
          (i x i0 y : int32) (ptbl : vallist) 
          x0,
    prio_in_tbl ($ OS_IDLE_PRIO) rtbl ->
    array_type_vallist_match Int8u rtbl ->
    length rtbl = ∘ OS_RDY_TBL_SIZE ->
    RL_Tbl_Grp_P rtbl (Vint32 i) ->
    Int.unsigned i <= 255 ->
    nth_val' (Z.to_nat (Int.unsigned i)) OSUnMapVallist = Vint32 x ->
    nth_val' (Z.to_nat (Int.unsigned x)) rtbl = Vint32 i0 ->
    nth_val' (Z.to_nat (Int.unsigned i0)) OSUnMapVallist = Vint32 y ->
    prio_not_in_tbl x0 rtbl ->
    Int.eq ((x<<ᵢ$ 3) +ᵢ  y) x0 = false.
Proof.
  intros.
  unfolds in H7.
  apply Int.eq_false.
  intro.
  subst x0.
  assert (Int.unsigned x <= 7).
  apply math_unmap_get_y in H4.
  omega.
  auto.
  assert (((x<<ᵢ$ 3) +ᵢ  y)&ᵢ$ 7 = y).
  apply inline_bittblfunctions.ob2.
  apply math_unmap_get_y in H4.
  omega.
  auto.
  apply math_unmap_get_y in H6.
  omega.
  auto.
  lets Hx:symbolic_lemmas.array_type_vallist_match_imp_rule_type_val_match H0.
  rewrite H1.
  instantiate (1:=Z.to_nat (Int.unsigned x)).
  clear -H8.
  apply z_le_7_imp_n.
  auto.
  rewrite H5 in Hx.
  simpl in Hx.
  remember (Int.unsigned i0 <=? Byte.max_unsigned) as X.
  destruct X;tryfalse.
  clear -HeqX.
  unfold Byte.max_unsigned in *.
  unfold Byte.modulus in *.
  unfold Byte.wordsize in *.
  unfold Wordsize_8.wordsize in *.
  simpl in HeqX.
  apply Zle_bool_imp_le;auto.
  symmetry in H9.
  assert (((x<<ᵢ$ 3) +ᵢ  y) >>ᵢ $ 3  = x).
  eapply math_shrl_3_eq;eauto.
  apply math_unmap_get_y in H6.
  omega.
  
  lets Hx:symbolic_lemmas.array_type_vallist_match_imp_rule_type_val_match H0.
  rewrite H1.
  instantiate (1:=Z.to_nat (Int.unsigned x)).
  clear -H8.
  apply z_le_7_imp_n.
  auto.
  rewrite H5 in Hx.
  simpl in Hx.
  remember (Int.unsigned i0 <=? Byte.max_unsigned) as X.
  destruct X;tryfalse.
  clear -HeqX.
  unfold Byte.max_unsigned in *.
  unfold Byte.modulus in *.
  unfold Byte.wordsize in *.
  unfold Wordsize_8.wordsize in *.
  simpl in HeqX.
  apply Zle_bool_imp_le;auto.
  clear -H8.
  int auto.
  apply z_le_7_imp_n;auto.
  symmetry in H10.

  lets Hx: nth_val'_imp_nth_val_int H5.
  lets Hy:H7 H9 H10 Hx.
  
  assert (prio_in_tbl ($ Int.unsigned((x<<ᵢ$ 3) +ᵢ  y)) rtbl).
  eapply unmap_inrtbl;eauto.
  rewrite Int.repr_unsigned in H11.
  unfolds in H11.
  lets Hz:H11 H9 H10 Hx.
  rewrite Hy in Hz.
  assert (Int.unsigned y <= 7).
  
  apply math_unmap_get_y in H6.
  omega.
  auto.
  lets Hw:symbolic_lemmas.array_type_vallist_match_imp_rule_type_val_match H0.
  rewrite H1.
  instantiate (1:=Z.to_nat (Int.unsigned x)).
  clear -H8.
  apply z_le_7_imp_n.
  auto.
  rewrite H5 in Hw.
  simpl in Hw.
  remember (Int.unsigned i0 <=? Byte.max_unsigned) as X.
  destruct X;tryfalse.
  clear -HeqX.
  unfold Byte.max_unsigned in *.
  unfold Byte.modulus in *.
  unfold Byte.wordsize in *.
  unfold Wordsize_8.wordsize in *.
  simpl in HeqX.
  apply Zle_bool_imp_le;auto.
  
  clear -Hz H12.
  mauto.
  destruct H12.
  unfolds in Hz.
  rewrite H in *.
  simpl in Hz.
  int auto.
  
  destruct H.
  unfolds in Hz.
  rewrite H in *.
  simpl in Hz.
  int auto.
  
  destruct H.
  unfolds in Hz.
  rewrite H in *.
  simpl in Hz.
  int auto.
  
  destruct H.
  unfolds in Hz.
  rewrite H in *.
  simpl in Hz.
  int auto.
  
  destruct H.
  unfolds in Hz.
  rewrite H in *.
  simpl in Hz.
  int auto.
  
  destruct H.
  unfolds in Hz.
  rewrite H in *.
  simpl in Hz.
  int auto.
  
  destruct H.
  unfolds in Hz.
  rewrite H in *.
  simpl in Hz.
  int auto.

  unfolds in Hz.
  rewrite H in *.
  simpl in Hz.
  int auto.
Qed.


Lemma dead_not_in:
  forall s head tail l rtbl tcbls ct P xx,
    s |= tcblist head xx tail Vnull l rtbl tcbls ** TCB_Not_In (Vptr ct) head l ** HTCBList tcbls ** P ->
    s |= HTCBList tcbls ** [|~ indom tcbls ct|] ** Atrue.
Proof.
  intros.
  sep split.
  sep auto.
  intro.
  unfold tcblist in H.
  unfold TCB_Not_In in H.
  sep normal in H.
  sep split in H.
  destruct H2.
  destruct H3.
  inverts H3.
  destruct H2.
  unfold tcbdllseg in *.
  remember ( HTCBList tcbls ** P) as PP.
  clear HeqPP.
  clears.
  remember (x,Int.zero) as y.
  clear Heqy.
  clears.
  gen s head rtbl tcbls  PP y tail xx0.
  inductions l;intros.
  simpl dllseg in H.
  sep split in H.
  subst.
  unfolds in H1.
  subst.
  unfolds in H0.
  destruct H0.
  rewrite map_emp_get in H0.
  tryfalse.
  unfold1 TCBList_P in H1.
  mytac.
  unfold1 dllseg in H.
  unfold node in H.
  sep normal in H.
  sep destruct H.
  sep split in H.
  rewrite H6 in H2;inverts H2.
  destruct H1;inverts H1.
  struct_type_vallist_match_elim.
  unfolds in H6;simpl in H6;inverts H6.
  unfolds in H1.
  destruct H1;subst.
  assert (l=nil).
  clear -H5.
  destruct l;auto.
  simpl in H5.
  mytac;tryfalse.
  subst l.
  unfolds in H5.
  subst x1.
  assert (y = (x4,Int.zero)).
  clear -H0 H3.
  unfold TcbJoin in *.
  apply join_comm in H3.
  apply join_emp_eq in H3.
  subst.

  apply indom_sig_eq in H0.
  auto.
  subst y.
  simpl.
  assert (beq_pos x4 x4 = true).
  rewrite beq_pos_Pos_eqb_eq.
  apply Pos.eqb_eq.
  auto.
  rewrite H1.
  clear;int auto.
  destruct H1;subst x0.
  
  simpl.
  remember (os_inv.beq_addrval y (x4, Int.zero)) as X.
  destruct X;auto.

  remember (dllseg (Vptr x) (Vptr (x4, Int.zero)) tail Vnull l OS_TCB_flag
                   V_OSTCBPrev V_OSTCBNext ** PP) as X.
  remember (Astruct (x4, Int.zero) OS_TCB_flag
           (Vptr x
            :: x12
               :: x11
                  :: x10
                     :: Vint32 i5
                        :: Vint32 i4
                           :: Vint32 i3
                              :: Vint32 i2
                                 :: Vint32 i1 :: Vint32 i0 :: Vint32 i :: nil)) as Y.
  simpl in H.
  mytac.
  eapply IHl in H5;eauto.
  
  clear -H3 H0 H1 HeqX.
  unfolds in H3.
  eapply joinsig_indom_neq;eauto.
  clear -HeqX.
  destruct y;simpl in HeqX.
  assert ((b,i)<>(x4, Int.zero)).
  eapply addr_eq_false_neq;eauto.
  auto.
Qed.


Lemma tcbld_rtbl_timetci_update_tcbdllflag:
  forall l l' v'28 v'39 v'40 v'41 v'33 x7 v'43,
    tcbls_rtbl_timetci_update l v'28 
                              (Vint32 v'39) v'40 v'41 =
    Some (l', v'33, Vint32 x7, v'43) ->
    eq_dllflag l l'.
Proof.
  induction l.
  intros.
  simpl in H.
  inverts H.
  simpl;auto.
  intros.
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
  simpl in H.
  xunfold H.
  splits;auto.
  eapply IHl;eauto.
  splits;auto.
  eapply IHl;eauto.
  splits;auto.
  eapply IHl;eauto.
  splits;auto.
  
  eapply IHl;eauto.
Qed.


Lemma tcblist_p_rh_curtcb:
  forall l1 l2 l a b p x,
    join l1 l2 l ->
    TCBList_P (Vptr p) (a::x) b l2 ->
    RH_CurTCB p l.
Proof.
  intros.
  unfold1 TCBList_P in *.
  mytac.
  inverts H0.
  clear -H2 H.
  unfolds.
  unfolds in H2.
  destruct x3.
  destruct p.
  do 3 eexists.
  apply join_sig_get in H2.
  eapply join_get_get_r in H;eauto.
  auto.
Qed.


Lemma inv_change_aux':
  forall p1 p2 tcbl1 tcbcur tcbl2 rtbl tcbls ptfree lfree P t,
    AOSTCBList' p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl t tcbls ptfree **
                AOSTCBFreeList' ptfree lfree t  tcbls** p_local OSLInv t init_lg ** P <==>
                AOSTCBList_old p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl t tcbls **
                AOSTCBFreeList ptfree lfree ** tcbdllflag p1 (tcbl1 ++ tcbcur :: tcbl2) ** LINV OSLInv t init_lg ** P.
Proof.
  intros.
  split;intros.
  unfold AOSTCBList' in H.
  apply disj_split in H.
  destruct H.
  sep normal in H.
  unfold p_local in H.
  unfold CurTid in H.
  unfold LINV in H.
  unfold OSLInv in H.
  unfold init_lg in H.
  
  sep normal in H.
  sep destruct H.
  sep split in H.
  destruct H0.
  inverts H0.
  destruct H1.
  subst p2.
  sep lift 5%nat in H.
  sep lift 3%nat in H.
  sep lift 2%nat in H.
  apply read_only_merge_vptr in H.
  destruct H as (H & Ha).
  unfold LINV.
  sep semiauto.
  eauto.
  unfold AOSTCBList_old.
  sep normal.
  sep eexists.
  sep semiauto.
  sep cancel tcbdllseg.
  sep cancel tcbdllseg.
  unfold AOSTCBFreeList' in H.
  unfold AOSTCBFreeList.
  unfold OSLInv, init_lg.
  sep auto.
  destruct H.
  unfold TCBFree_Not_Eq in H.
  sep auto.
  unfold TCBFree_Eq in H.
  sep normal in H.
  sep destruct H.
  sep split in H.
  destruct H1.
  tryfalse.
  eauto.
  eauto.
  auto.
  unfold p_local in H.
  unfold CurTid in H.
  unfold LINV in H.
  unfold OSLInv in H.
  unfold TCB_Not_In in H.
  sep normal in H.
  sep destruct H.
  sep split in H.
  unfold init_lg in H0.
  inverts H0.
  destruct H1.
  destruct H1.
  subst p2.
  sep lift 4%nat in H.
  sep lift 3%nat in H.
  sep lift 2%nat in H.
  apply read_only_merge_vptr in H.
  destruct H as (H & Ha).
  subst t.
  sep lift 4%nat in H.
  inverts H5.
  sep lift 3%nat in H.
  subst ptfree.
  unfold AOSTCBFreeList' in H.
  destruct H2.
  inverts H2.
  sep normal in H.
  sep lift 7%nat in H.
  apply disj_split in H.
  destruct H.
  unfold TCBFree_Not_Eq in H.
  sep normal in H.
  sep split in H.
  tryfalse.
  unfold TCBFree_Eq in H.
  sep normal in H.
  sep destruct H.
  sep split in H.
  destruct H2.
  destruct H5;subst.
  sep lift 2%nat in H.
  sep lift 5%nat in H.
  eapply flag_merege_false in H.
  tryfalse.
(****)
  intros.
  unfold  p_local, CurTid, LINV, OSLInv.
  unfold AOSTCBList_old in H.
  
  unfold LINV, OSLInv, init_lg in H.
  sep semiauto.
  sep lift 3%nat.
  unfold AOSTCBList'.
  eapply disj_split.
  left.
  sep normal.
  subst p2.
  sep lift 5%nat in H.
  sep lift 6%nat in H.
  lets Hxx : tcbfreelist_disj_tcblist H.
  sep semiauto.

  sep cancel 2%nat 4%nat.
  sep cancel 3%nat 1%nat.
  sep lift 3%nat.
  sep cancel tcbdllflag.
  sep lift 4%nat in H.
  apply read_only_merge_vptreq in H.
  unfold AOSTCBFreeList in H.
  sep lift 5%nat.
  unfold AOSTCBFreeList'.
  sep lift 2%nat.
  eapply disj_split.
  left.
  unfold TCBFree_Not_Eq.
  sep auto.
  eauto.
  eauto.
  auto.
  split;auto.
Qed.
  
Lemma inv_change_aux:
  forall p1 p2 tcbl1 tcbcur tcbl2 rtbl tcbls ptfree lfree P t,
    AOSTCBList' p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl t tcbls ptfree **
                AOSTCBFreeList' ptfree lfree t tcbls** p_local OSLInv t init_lg ** P <==>
                AOSTCBList p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl t tcbls **
                AOSTCBFreeList ptfree lfree ** tcbdllflag p1 (tcbl1 ++ tcbcur :: tcbl2) ** p_local OSLInv t init_lg ** P.
Proof.
  intros.
  split;intros.
  apply inv_change_aux' in H.
  sep semiauto.
  unfold p_local in *.
  unfold CurTid in *.
  unfold AOSTCBList in *.
  unfold AOSTCBList_old in *.
  sep auto.
  destruct H0;subst.
  sep lift 4%nat.
  apply read_only_merge_vptreq.
  sep auto.
  eauto.
  eauto.
  auto.
  apply inv_change_aux'.
  sep semiauto.
  unfold p_local in *.
  unfold CurTid in *.
  unfold AOSTCBList in *.
  unfold AOSTCBList_old in *.
  sep auto.
  sep lift 4%nat in H.
  destruct H0;subst.
  apply read_only_merge_vptr in H.
  destruct H.
  sep auto.
  eauto.
  eauto.
  auto.
Qed.

Definition prio_in_tcbdllseg := 
fix prio_in_tcbdllseg (p : int32) (l : list vallist) {struct l} : bool :=
  match l with
    | nil => false
    | h :: l' =>
      match V_OSTCBPrio h with
        | Some (Vint32 p') =>  (Int.eq p' p) || (prio_in_tcbdllseg p l')
        | _ => prio_in_tcbdllseg p l'
      end
  end.



Lemma tickstep_prio_in_tcbls':
  forall tcbls tcbls' ecbls ecbls' p tcblsx,
    sub tcblsx tcbls ->
    prio_not_in_tcbls p tcbls ->
    tickstep' tcbls ecbls tcbls' ecbls' tcblsx->
    prio_not_in_tcbls p tcbls'.
Proof.
  intros.
  inductions H1.
  auto.
  eapply IHtickstep';eauto.
  eapply joinsig_set_sub_sub;eauto.
  unfolds.
  intro.
  unfolds in H0.
  destruct H0.
  inverts H2;mytac.
  assert (t = x \/ t <> x ) by tauto.
  destruct H3.
  subst.
  rewrite map_get_set in H2.
  inverts H2.
  exists x x0 x1.
  eapply sub_joinsig_get;eauto.
  rewrite map_get_set' in H2.
  do 3 eexists;eauto.
  auto.
  assert (t = x \/ t <> x ) by tauto.
  destruct H2.
  subst.
  rewrite map_get_set in H0.
  inverts H0.
  do 3 eexists.
  eapply sub_joinsig_get;eauto.
  rewrite map_get_set' in H0.
  do 3 eexists;eauto.
  auto.
  assert (t = x \/ t <> x ) by tauto.
  destruct H2.
  subst.
  rewrite map_get_set in H0.
  inverts H0.
  do 3 eexists.
  eapply sub_joinsig_get;eauto.
  rewrite map_get_set' in H0.
  do 3 eexists;eauto.
  auto.
  assert (t = x0 \/ t <> x0 ) by tauto.
  destruct H3.
  subst.
  rewrite map_get_set in H0.
  inverts H0.
  do 3 eexists.
  eapply sub_joinsig_get;eauto.
  rewrite map_get_set' in H0.
  do 3 eexists;eauto.
  auto.
  assert (t = x0 \/ t <> x0 ) by tauto.
  destruct H3.
  subst.
  rewrite map_get_set in H2.
  inverts H2.
  do 3 eexists.
  eapply sub_joinsig_get;eauto.
  rewrite map_get_set' in H2.
  do 3 eexists;eauto.
  auto.
Qed.

Lemma tickstep_prio_in_tcbls:
  forall tcbls tcbls' ecbls ecbls' p,
    prio_not_in_tcbls p tcbls ->
    tickstep tcbls ecbls tcbls' ecbls' ->
    prio_not_in_tcbls p tcbls'.
Proof.
  intros.
  eapply tickstep_prio_in_tcbls';eauto.
  clear;unfolds;join auto.
Qed.

Lemma prio_not_in_hl:
  forall a rtbl tcbls p x3 ,
    TCBList_P p a rtbl tcbls ->
    prio_not_in_tcbls x3 tcbls ->
    prio_in_tcbdllseg x3 a = false.
Proof.
  inductions a.
  intros.
  simpl;auto.
  intros.
  simpl.
  simpl in H.
  mytac.
  remember (V_OSTCBPrio a) as XX.
  destruct XX.
  destruct v.
  eapply IHa;eauto.
  unfolds.
  unfolds in H0.
  intro.
  destruct H0.
  mytac;do 3 eexists.
  eapply join_get_r in H;eauto.
  eapply IHa;eauto.
  unfolds.
  unfolds in H0.
  intro.
  destruct H0.
  mytac;do 3 eexists.
  eapply join_get_r in H;eauto.
  apply orb_false_iff.
  unfolds in H3.
  destruct x2.
  destruct p.
  mytac.
  rewrite H3 in HeqXX.
  inverts HeqXX.
  unfolds in H0.
  remember (Int.eq p x3) as X.
  destruct X;auto.
  destruct H0.
  exists x t m.
  eapply join_get_l;eauto.
  lets Hx: Int.eq_spec p x3.
  rewrite <- HeqX in Hx.
  subst.
  apply map_get_sig;auto.
  eapply IHa;eauto.
  unfolds.
  unfolds in H0.
  intro.
  destruct H0.
  mytac;do 3 eexists.
  eapply join_get_r;eauto.
  eapply IHa;eauto.
  unfolds.
  unfolds in H0.
  intro.
  destruct H0.
  mytac;do 3 eexists.
  eapply join_get_r;eauto.
  eapply IHa;eauto.
  unfolds.
  unfolds in H0.
  intro.
  destruct H0.
  mytac;do 3 eexists.
  eapply join_get_r;eauto.
Qed.

Fixpoint tcblist_rl l:=
  match l with
    | nil => True
    | a::l' => RL_TCBblk_P a /\ tcblist_rl l'
  end.

Lemma tcblist_p_rl:
  forall b a c d,
    TCBList_P a b c d -> tcblist_rl b.
Proof.
  inductions b.
  intros;simpl in *;auto.
  intros.
  simpl.
  simpl in H.
  mytac.
  unfolds in H2.
  destruct x2.
  destruct p.
  mytac;auto.
  eapply IHb;eauto.
Qed.

Lemma prio_not_in_tcbls_nready:
  forall x0 tcbls ptbl vhold rtbl,
    array_type_vallist_match Int8u rtbl ->
    length rtbl = ∘ OS_RDY_TBL_SIZE ->
    R_PrioTbl_P ptbl tcbls vhold ->
    RL_RTbl_PrioTbl_P rtbl ptbl vhold ->
    Int.unsigned x0 < 64 ->
    prio_not_in_tcbls x0 tcbls ->
    prio_not_in_tbl x0 rtbl.
Proof.
  intros.
  lets Hx : prio_rtbl_dec x0 H H0.
  split;auto.
  clear;int auto.
  destruct Hx;auto.
  unfolds in H4.
  destruct H4.
  unfolds in H1.
  mytac.
  unfolds in H2.
  lets Hx: H2 H5.
  split;auto.
  clear;int auto.
  mytac.
  exists x.
  eapply H1;eauto.
  split;auto.
  clear;int auto.
Qed.


Lemma tcbfree_eq_tick_hold:
  forall  s P ct x tcbls tcbls' ecbls ecbls',
    tickstep tcbls ecbls tcbls' ecbls' ->
    s |= TCBFree_Eq (Vptr ct) ct x tcbls ** P ->
    s |= TCBFree_Eq (Vptr ct) ct x tcbls' ** P.
Proof.
  introv Htickstep.
  intros.
  sep cancel 2%nat 2%nat.
  unfold TCBFree_Eq in *.
  sep auto.
  mytac;auto.
  eexists.
  split;eauto.
  clear -Htickstep H4.
  unfolds in Htickstep.
  Lemma tcbfree_eq_tick_hold':
    forall p tcbls ecbls tcbls' ecbls' tcblsx,
      sub tcblsx tcbls ->
      tickstep' tcbls ecbls tcbls' ecbls' tcblsx ->
      prio_not_in_tcbls p tcbls ->
      prio_not_in_tcbls p tcbls'.
  Proof.
    intros.
    inductions H0.
    auto.
    eapply IHtickstep';eauto.
    eapply joinsig_set_sub_sub;eauto.
    unfold prio_not_in_tcbls in *.
    intro.
    destruct H4.
    mytac.
    assert (x=t \/ x <> t) by tauto.
    destruct H2.
    subst.
    rewrite map_get_set in H4.
    inverts H4.
    Focus 2.
    rewrite map_get_set' in H4;auto.
    do 3 eexists;eauto.
    exists t st x1.
    eapply sub_joinsig_get;eauto.
  Qed.
  eapply tcbfree_eq_tick_hold';eauto.
  clear;unfolds.
  join auto.
Qed.
  

Lemma not_in_tcblist_tick_hold:
  forall a b c d a' b' c' rtbl rtbl' ct head,
    tcbls_rtbl_timetci_update a rtbl 
                              (Vint32 b) c d =
    Some (a', rtbl', Vint32 b', c') ->
    ~ ptr_in_tcblist (Vptr ct) head a ->
    ~ ptr_in_tcblist (Vptr ct) head a'.
Proof.
  intros.
  intro.
  destruct H0.
  gen b c d a' b' c' rtbl rtbl' ct head.
  inductions a.
  intros.
  simpl in *.
  inverts H;simpl in H1;tryfalse.
  intros.
  simpl.
  simpl in H.
  xunfold H.

  simpl in H1.
  destruct head;tryfalse.
  eapply IHa;eauto.
  eapply IHa;eauto.
  eapply IHa;eauto.
  remember (os_inv.beq_addrval ct a) as X.
  destruct X;auto.
  eapply IHa;eauto.
  
  simpl in H1.
  destruct head;tryfalse.
  eapply IHa;eauto.
  eapply IHa;eauto.
  eapply IHa;eauto.
  remember (os_inv.beq_addrval ct a) as X.
  destruct X;auto.
  eapply IHa;eauto.
  simpl in H1.
  destruct head;tryfalse.
  eapply IHa;eauto.
  eapply IHa;eauto.
  eapply IHa;eauto.
  remember (os_inv.beq_addrval ct a) as X.
  destruct X;auto.
  eapply IHa;eauto.
  simpl in H1.
  destruct head;tryfalse.
  eapply IHa;eauto.
  eapply IHa;eauto.
  eapply IHa;eauto.
  remember (os_inv.beq_addrval ct a) as X.
  destruct X;auto.
  eapply IHa;eauto.
Qed.

Lemma GoodFrm_dllsegflag:
  forall z x y next,
    GoodFrm (dllsegflag x y z next).
Proof.
  inductions z.
  intros.
  simpl.
  auto.
  intros.
  simpl.
  intros.
  splits;auto.
Qed.

Close Scope code_scope.
