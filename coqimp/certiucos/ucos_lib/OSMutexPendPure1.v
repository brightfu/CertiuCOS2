Require Import sem_common.
Require Import sempend_pure.
Require Import OSMutex_common.
Require Import OSQPostPure.
Open Scope code_scope.

Hint Resolve noabs_oslinv.
Hint Extern 2 (_ <= _) => apply Z.leb_le; trivial.

Lemma aux_trivial:
  forall x,  Int.unsigned x < 64 ->  Int.unsigned (x>>ᵢ$ 3) < 8.
Proof.
  intros.
  mauto.
Qed.

Lemma and7_lt8:
  forall x, Int.unsigned x < 64 -> Int.unsigned (x &ᵢ $ 7) < 8.
Proof.
  intros.
  mauto.
Qed.

Section lzh_join.
  
Lemma mund_disj_sub_l:
  forall ma mb ma',
    TcbMod.disj ma mb ->
    TcbMod.sub ma' ma ->
    TcbMod.disj ma' mb.
  intros ma mb ma'.
  unfold TcbMod.sub, TcbMod.disj, TcbMod.lookup.
  intros.
  substH H with (H a).
  substH H0 with (H0 a).
  TcbMod.rewrite_get;
    TcbMod.destruct_get;
    TcbMod.solve_sn.
  assert (None = Some b).
    apply H0.
    reflexivity.
  inversion H1.
Qed.

Hint Resolve mund_disj_sub_l.

Lemma mund_disj_sub_r:
  forall ma mb mb',
    TcbMod.disj ma mb ->
    TcbMod.sub mb' mb ->
    TcbMod.disj ma mb'.
  intros.
  eapply TcbMod.disj_trans_sub.
  eauto.
  eauto.
Qed.

Hint Resolve mund_disj_sub_r.

Lemma mund_disj_sub_w:
  forall ma mb ma' mb',
    TcbMod.disj ma mb ->
    TcbMod.sub ma' ma ->
    TcbMod.sub mb' mb ->
    TcbMod.disj ma' mb'.
  intros.
  eapply mund_disj_sub_l.
  eapply mund_disj_sub_r.
  eauto.
  eauto.
  eauto.
Qed.

Hint Resolve mund_disj_sub_w.

Lemma join_prop_mutexpend:
  forall  cur_st x2 tcbls tcbls_l tcbls_r tcbls_sub_l tcbls_sub_r p_st v'38 ptcb_addr v'52,
    TcbJoin (v'38, Int.zero) cur_st x2 tcbls_r -> 
    TcbMod.joinsig (ptcb_addr, Int.zero)
                   p_st tcbls_sub_r v'52 ->
    TcbMod.join tcbls_sub_l v'52 tcbls_l -> 
    TcbMod.join tcbls_l tcbls_r tcbls ->
    TcbMod.join x2 (TcbMod.sig (ptcb_addr, Int.zero) p_st)
                (TcbMod.merge (TcbMod.sig (ptcb_addr, Int.zero) p_st) x2)
                .
Proof.
  intros.
  rename v'38 into cur_addr.
  rename cur_st into cur_node.
  rename p_st into ptcb_node.
  rename tcbls_r into tcbls_r'.
  rename x2 into tcbls_r.
  rename v'52 into tcbls_sub_r'.

  rename H into Hr.
  rename H0 into Hsub_r.
  rename H1 into Hl.
  rename H2 into H.

  unfold TcbJoin in Hr.
  unfold join in Hr.
  unfold sig in Hr.
  simpl in Hr.
  Hint Resolve TcbMod.get_sig_some.
  assert (Fget_l: TcbMod.get tcbls_l (ptcb_addr, Int.zero) = Some ptcb_node).
  {
    eapply TcbMod.join_get_get_r.
    eauto.
    eapply TcbMod.join_get_get_l.
    eauto.
    auto.
  }
  assert (Fget_r': TcbMod.get tcbls_r' (cur_addr, Int.zero) = Some cur_node).
  {
    eapply TcbMod.join_get_get_l.
    eauto.
    auto.
  }
  Hint Resolve TcbMod.my_join_disj.
  assert (Fdisj: TcbMod.disj tcbls_l tcbls_r').
  {
    eauto.
  }
  assert (Fsub_disj: TcbMod.disj tcbls_sub_l tcbls_sub_r').
  {
    eauto.
  }
  assert (Fget_sub_r': TcbMod.get tcbls_sub_r' (ptcb_addr, Int.zero) = Some ptcb_node).
  {
    eapply TcbMod.join_get_get_l; eauto.
  }    
  assert (F1: TcbMod.disj tcbls_r
                          (TcbMod.sig (ptcb_addr, Int.zero) ptcb_node)).
  {
    eapply mund_disj_sub_w. 
    eapply TcbMod.disj_sym.
    apply Fdisj.
    Hint Resolve TcbMod.join_sub_l.
    Hint Resolve TcbMod.join_sub_r.
    eauto.
    eauto.
    Hint Resolve TcbMod.sub_sig.
    eauto.
  }    
  Hint Resolve TcbMod.disj_compat.
  assert (F2: TcbMod.compat
                tcbls_r
                (TcbMod.sig (ptcb_addr, Int.zero) ptcb_node)).
  {
    eauto.
  }

  eapply TcbMod.disj_meq_join.
  split.
  eauto.
  Hint Resolve TcbMod.meq_merge_sym.
  Hint Resolve TcbMod.compat_sym.
  auto.
Qed.

Lemma rtbl_remove_RL_RTbl_PrioTbl_P_hold'':
  forall (prio : Z) (y bitx : int32) (rtbl : vallist) 
         (ry : int32) (ptbl : vallist) (av : addrval),
    0 <= prio < 64 ->
    y = $ prio>>ᵢ$ 3 ->
    bitx = $ 1<<ᵢ($ prio&ᵢ$ 7) ->
    nth_val ∘(Int.unsigned y) rtbl = Some (Vint32 ry) ->
    RL_RTbl_PrioTbl_P rtbl ptbl av ->
    RL_RTbl_PrioTbl_P
      (update_nth_val ∘(Int.unsigned y) rtbl (Vint32 (ry&ᵢInt.not bitx)))
      (update_nth_val  (∘prio)  ptbl (Vptr av))
      av.
Proof.
  introv Hpr Hy Hb Hnth Hrl.
  unfolds in Hrl.
  unfolds.
  introv Hp Hpro.
  subst .
  remember ($ prio) as pri.
  assert ( 0 <= Int.unsigned pri < 64).
  clear -Hpr Heqpri.
  subst.
  int auto.
  assert (p = pri \/ p <> pri) by tauto.
  destruct H0.
  subst p.
  eapply  prio_update_self_not_in in Hpro; eauto.
  tryfalse.
  lets Hxs : prio_neq_in_tbl H0 Hnth Hpro; eauto.
  lets Has : Hrl Hxs; eauto.
  mytac.
  exists x.
  splits; auto.
  assert ((Z.to_nat (Int.unsigned p)) <> ∘prio).
  unfold nat_of_Z.
  introv Hf.
  apply H0.
  lets Hsas : Z2Nat.inj Hf; eauto.
  rewrite <- Hsas.
  clear - H5.
  int auto.
  eapply nth_upd_neqrev; eauto.
Qed.


Lemma join_prop_mutexpend':
  forall  cur_st x2 tcbls tcbls_l tcbls_r tcbls_sub_l tcbls_sub_r p_st v'38 ptcb_addr v'52 y,
    TcbJoin (v'38, Int.zero) cur_st x2 tcbls_r -> 
    TcbMod.joinsig (ptcb_addr, Int.zero)
                   p_st tcbls_sub_r v'52 ->
    TcbMod.join tcbls_sub_l v'52 tcbls_l -> 
    TcbMod.join tcbls_l tcbls_r tcbls ->
    TcbMod.join (TcbMod.set tcbls_l (ptcb_addr, Int.zero) y)
                (TcbMod.sig (v'38, Int.zero) cur_st)
                (TcbMod.merge (TcbMod.sig (v'38, Int.zero) cur_st)
                              (TcbMod.set tcbls_l (ptcb_addr, Int.zero) y)).
Proof.
  intros.
  rename v'38 into cur_addr.
  rename cur_st into cur_node.
  rename p_st into ptcb_node.
  rename tcbls_r into tcbls_r'.
  rename x2 into tcbls_r.
  rename v'52 into tcbls_sub_r'.

  rename H into Hr.
  rename H0 into Hsub_r.
  rename H1 into Hl.
  rename H2 into H.

  unfold TcbJoin in Hr.
  
  assert (Fget_l: TcbMod.get tcbls_l (ptcb_addr, Int.zero) = Some ptcb_node).
  {
    eapply TcbMod.join_get_get_r.
    apply Hl.
    eapply TcbMod.join_get_get_l.
    apply Hsub_r.
    apply TcbMod.get_sig_some.
  }
  assert (Fget_r': TcbMod.get tcbls_r' (cur_addr, Int.zero) = Some cur_node).
  {
    eapply TcbMod.join_get_get_l.
    apply Hr.
    apply TcbMod.get_sig_some.
  }
  assert (Fdisj: TcbMod.disj tcbls_l tcbls_r').
  {
    lets Htmp: TcbMod.join_disj_meq H.
    destruct Htmp; auto.
  }
  assert (Fsub_disj: TcbMod.disj tcbls_sub_l tcbls_sub_r').
  {
    lets Htmp: TcbMod.join_disj_meq Hl.
    destruct Htmp; auto.
  }
  assert (Fget_sub_r': TcbMod.get tcbls_sub_r' (ptcb_addr, Int.zero) = Some ptcb_node).
  {
    eapply TcbMod.join_get_get_l.
    apply Hsub_r.
    apply TcbMod.get_sig_some.
  }    

  assert (F1: TcbMod.disj (TcbMod.sig (cur_addr, Int.zero) cur_node)
                             (TcbMod.set tcbls_l (ptcb_addr, Int.zero) y)).
  {
    lets Htmp : join_join_disj_copy Hl Hsub_r.
    apply TcbMod.disj_sym in Htmp.
    eapply TcbMod.disj_set_disj_2.
    apply TcbMod.disj_sym.
    eapply TcbMod.disj_trans_sub.
    eapply TcbMod.sub_sig.
    eauto.
    auto.
    eauto.
  }
  assert (F2: TcbMod.compat
                      (TcbMod.sig (cur_addr, Int.zero) cur_node)
                      (TcbMod.set tcbls_l (ptcb_addr, Int.zero) y)).
  {
    apply TcbMod.disj_compat.
    eauto.
  }
  eapply TcbMod.disj_meq_join.
  split.
  TcbMod.solve_disj.
  eapply TcbMod.meq_merge_sym.
  eapply TcbMod.compat_sym.
  auto.
Qed.


Lemma join_mutexpend':
  forall x y x1 y1 y1' y' l1 l2 l3 L L',
    TcbJoin x y' L'  L ->
    TcbMod.join l3 l2 L' ->
    TcbMod.joinsig x1 y1' l1 l2 ->
    TcbJoin x y (TcbMod.set L' x1 y1) (TcbMod.set (TcbMod.set L x y) x1 y1).
Proof.
  intros.
  unfold TcbJoin in *.
  unfold join in *.
  unfold sig in *.
  simpl in *.
  Hint Resolve TcbMod.get_indom.
  eapply TcbMod.join_set_r.
  assert (F1: (TcbMod.set (TcbMod.sig x y') x y) = TcbMod.sig x y).
  {
    Hint Immediate TcbMod.set_sig.
    eauto.
  }
  rewrite <- F1.
  eapply TcbMod.join_set_l.
  eauto.
  eauto.
  assert (F2: TcbMod.get L' x1 = Some y1').
  {
    eapply TcbMod.join_get_get_r.
    eauto.
    Hint Resolve tcbmod_joinsig_get.
    eauto.
  }
  eauto.
Qed.  


Lemma join_prop_mutexpend'':
  forall  cur_st x2 tcbls tcbls_l tcbls_r tcbls_sub_l tcbls_sub_r p_st v'38 ptcb_addr v'52 y z,
    TcbJoin (v'38, Int.zero) cur_st x2 tcbls_r -> 
    TcbMod.joinsig (ptcb_addr, Int.zero)
                   p_st tcbls_sub_r v'52 ->
    TcbMod.join tcbls_sub_l v'52 tcbls_l -> 
    TcbMod.join tcbls_l tcbls_r tcbls ->
    TcbMod.join (TcbMod.set tcbls_l (ptcb_addr, Int.zero) z)
                (TcbMod.set tcbls_r (v'38, Int.zero)
                            y)
                (TcbMod.set
                   (TcbMod.set tcbls (v'38, Int.zero)
                               y)
                   (ptcb_addr, Int.zero) z).
Proof.
  intros.
  rename v'38 into cur_addr.
  rename cur_st into cur_node.
  rename p_st into ptcb_node.
  rename tcbls_r into tcbls_r'.
  rename x2 into tcbls_r.
  rename v'52 into tcbls_sub_r'.

  rename H into Hr.
  rename H0 into Hsub_r.
  rename H1 into Hl.
  rename H2 into H.

  unfold TcbJoin in Hr.
  unfold join in Hr.
  unfold sig in Hr.
  simpl in Hr.
  
  assert (Fget_l: TcbMod.get tcbls_l (ptcb_addr, Int.zero) = Some ptcb_node).
  {
    eapply TcbMod.join_get_get_r.
    eauto.
    eapply TcbMod.join_get_get_l.
    eauto.
    auto.
  }
  assert (Fget_r': TcbMod.get tcbls_r' (cur_addr, Int.zero) = Some cur_node).
  {
    eapply TcbMod.join_get_get_l.
    eauto.
    auto.
  }
  assert (Fdisj: TcbMod.disj tcbls_l tcbls_r').
  {
    eauto.
  }
  assert (Fsub_disj: TcbMod.disj tcbls_sub_l tcbls_sub_r').
  {
    eauto.
  }
  assert (Fget_sub_r': TcbMod.get tcbls_sub_r' (ptcb_addr, Int.zero) = Some ptcb_node).
  {
    eapply TcbMod.join_get_get_l; eauto.
  }    


  eapply TcbMod.join_set_l.
  eapply TcbMod.join_set_r.
  Hint Resolve TcbMod.get_indom.
  eauto.
  eauto.
  eauto.
Qed.

Lemma join_prop_mutexpend''':
  forall x y m n b c,
    m <> x ->
    TcbMod.join (TcbMod.sig m n) b c ->
    TcbMod.join (TcbMod.sig m n) (TcbMod.set b x y) (TcbMod.merge (TcbMod.sig m n) (TcbMod.set b x y)).
Proof.
  intros.
  eapply TcbMod.join_merge_disj.
  unfold TcbMod.disj, TcbMod.lookup.
  intros.
  substH H0 with (H0 a).
  TcbMod.rewrite_get;
    TcbMod.destruct_get;
    TcbMod.solve_sn;
  destruct (tidspec.beq m a) eqn:f1;
    destruct (tidspec.beq x a) eqn:f2; eauto.
  apply tidspec.beq_true_eq in f1.
  apply tidspec.beq_true_eq in f2.
  subst; tryfalse.
Qed.

Lemma join_prop_mutexpend'''':
  forall a b c x y b',
    TcbMod.join a b c ->
    TcbJoin x y b' b ->
    TcbMod.join b' (TcbMod.merge a (TcbMod.sig x y)) c.
Proof.
  intros.
  apply TcbMod.join_comm.
  eapply TcbMod.join_shift_l.
  eauto.
  eauto.  
Qed.

End lzh_join.

Lemma evsllseg_aux:
  forall l1 s a b l2 P,
    s |= evsllseg a b l1 l2 ** P ->
    (a = b /\ l1 = nil \/ get_last_ptr l1 = Some b) /\ length l1 = length l2.
Proof.
  inductions l1.
  intros.
  simpl in H.
  mytac.
  swallow.
  left.
  auto.
  auto.
  intros.
  unfold evsllseg in H.
  fold evsllseg in H.
  destruct l2.
  simpl in H.
  mytac; tryfalse.
  destruct a.
  sep normal in H.
  sep destruct H.
  sep lift 3%nat in H.
  lets Hxax: IHl1 H.
  mytac.
  swallow.
  2: simpl; auto.
  destruct H0.
  mytac.
  right.
  unfolds.
  simpl.
  sep split in H.
  auto.
  right.
  unfolds.
  simpl.
  destruct l1.
  unfolds in H0.
  simpl in H0.
  unfolds in H0.
  unfold nth_val in H0.
  tryfalse.
  simpl.
  auto.
Qed.


Lemma prio_neq_cur_set:
  forall tcbls_l v'38 cur_prio x xm ptcb_addr ptcb_prio,
    prio_neq_cur tcbls_l (v'38, Int.zero) cur_prio ->
    TcbMod.get tcbls_l (ptcb_addr, Int.zero) =
    Some (ptcb_prio, rdy, xm) -> 
    Int.ltu x cur_prio = true ->
    prio_neq_cur (TcbMod.set tcbls_l (ptcb_addr, Int.zero) (x, rdy, xm))
                 (v'38, Int.zero) cur_prio.
Proof.
  intros.
  unfolds.
  intros.
  unfolds in H.
  assert (tid = (ptcb_addr, Int.zero) \/ tid <> (ptcb_addr, Int.zero)) by tauto.
  destruct H4.
  subst tid.
  rewrite TcbMod.set_a_get_a in H3.
  inverts H3.
  clear -H1.
  intro.
  subst.
  int auto.
  rewrite tidspec.eq_beq_true;auto.
  rewrite TcbMod.set_a_get_a' in H3.
  eapply H;eauto.
  rewrite tidspec.neq_beq_false;auto.
Qed.

Lemma RL_RTbl_PrioTbl_P_set_vhold:
  forall v'45 v'43 x11 xm x y ptcb_prio i8 ptcb_tcby ptcb_bitx ptcb_bity v'53 os_rdy_tbl v0 v'32,
    RL_TCBblk_P
      (v'45
         :: v'43
         :: x11
         :: xm
         :: x
         :: y
         :: Vint32 ptcb_prio
         :: Vint32 i8
         :: Vint32 ptcb_tcby
         :: Vint32 ptcb_bitx
         :: Vint32 ptcb_bity :: nil) ->
    (Z.to_nat (Int.unsigned (ptcb_prio>>ᵢ$ 3)) < length os_rdy_tbl)%nat ->
    nth_val' (Z.to_nat (Int.unsigned ptcb_tcby)) os_rdy_tbl =
    Vint32 v0 ->
    RL_RTbl_PrioTbl_P os_rdy_tbl v'32 v'53 ->
    RL_RTbl_PrioTbl_P
      (update_nth_val (Z.to_nat (Int.unsigned ptcb_tcby)) os_rdy_tbl
                      (Vint32 (v0&ᵢInt.not ptcb_bitx)))
      (update_nth_val (Z.to_nat (Int.unsigned ptcb_prio)) v'32 (Vptr v'53))
      v'53.
Proof.
  intros.
  funfold H.
  lets Hx:  rtbl_remove_RL_RTbl_PrioTbl_P_hold' H2; eauto.
  unfold nat_of_Z.
  rewrite Int.repr_unsigned.
  eapply nth_val'_imply_nth_val; eauto.
  unfold nat_of_Z in Hx.
    rewrite Int.repr_unsigned in Hx.
    auto.
Qed.



Lemma R_PrioTbl_Pend_lift:
  forall ptcb_addr v'38 x v'53 v'32 tcbls cur_prio ptcb_prio xm v'46 i,
    (length v'32 = 64)%nat -> (**side condition**)
    Int.unsigned cur_prio < 64 ->
    Int.unsigned (x>>ᵢ$ 8) < 64 ->
    Int.unsigned ptcb_prio < 64 ->
    (ptcb_addr,Int.zero) <> (v'38,Int.zero) ->
    (nth_val' (Z.to_nat (Int.unsigned (x>>ᵢ$ 8))) v'32) = (Vptr v'53) ->
    R_PrioTbl_P v'32 tcbls v'53 ->
    TcbMod.get tcbls (v'38, Int.zero) = Some (cur_prio, rdy, Vnull) ->
    TcbMod.get tcbls (ptcb_addr, Int.zero) = Some (ptcb_prio, rdy, xm) ->
    R_PrioTbl_P
      (update_nth_val (Z.to_nat (Int.unsigned (x>>ᵢ$ 8)))
                      (update_nth_val (Z.to_nat (Int.unsigned ptcb_prio)) v'32 (Vptr v'53))
                      (Vptr (ptcb_addr, Int.zero)))
      (TcbMod.set
         (TcbMod.set tcbls (v'38, Int.zero)
                     (cur_prio, wait (os_stat_mutexsem (v'46, Int.zero)) i, Vnull))
         (ptcb_addr, Int.zero) (x>>ᵢ$ 8, rdy, xm)) v'53.
Proof.
  introv Hax Hcr Hx Hpt Hneq Hnth Hrp Hget1 Hget2.
  unfolds.
  splits.
  introv Hp Hnthx Hneqq.
  unfold get in *.
  simpl in *.
  unfolds in Hrp.
  destruct Hrp as (Hrp1 & Hrp2 & Hrp3).
  remember ( ∘(Int.unsigned prio)) as pm.
  remember ( (Z.to_nat (Int.unsigned (x>>ᵢ$ 8)))) as pn.
  remember (Z.to_nat (Int.unsigned ptcb_prio)) as px.
  assert (pm <> pn \/ pm = pn) as Hart by tauto.
  destruct Hart as [Hart1 | Hart2].
  lets Hres : nth_upd_neq  Hart1 Hnthx.
  assert (pm <> px \/ pm = px) as Harst by tauto.
  destruct Harst as [Harst1 | Harst2].
  lets Hres2 : nth_upd_neq  Harst1 Hres.
  lets Hasb : Hrp1 Hneqq; eauto.
  rewrite <- Heqpm; auto. 
  unfolds in Hrp3.
  assert ( tcbid = (ptcb_addr, Int.zero) \/ tcbid <>  (ptcb_addr, Int.zero)) by tauto.
  destruct H.
  subst tcbid.
  destruct Hasb as (sst & m11 & Hgs).
  unfold get in *; simpl in *.
  rewrite Hgs in Hget2.
  inverts Hget2.
  rewrite Heqpx in Harst1.
  rewrite Heqpm in Harst1.
  clear - Harst1.
  unfold nat_of_Z in Harst1.
  tryfalse.
  destruct Hasb as (sst & m11 & Hgs).
  assert ( tcbid =(v'38, Int.zero)\/ tcbid <> (v'38, Int.zero)) by tauto.
  destruct H0.
  subst tcbid.

  unfold get in *; simpl in *.
  rewrite Hget1 in Hgs.
  inverts Hgs.
  rewrite TcbMod.set_sem.
  erewrite tidspec.neq_beq_false; eauto.
  rewrite TcbMod.set_sem.
  erewrite tidspec.eq_beq_true; eauto.
  rewrite TcbMod.set_sem.
  erewrite tidspec.neq_beq_false; eauto.
  rewrite TcbMod.set_sem.
  erewrite tidspec.neq_beq_false; eauto.

  rewrite Harst2 in Hres.
  lets Heqs: nth_upd_eq  Hres.
  inverts Heqs ; tryfalse.
  rewrite Hart2 in Hnthx.
  lets Heqs: nth_upd_eq  Hnthx.
  inverts Heqs.
  rewrite Heqpm in Hart2.
  rewrite   Heqpn in Hart2.
  assert (prio = (x>>ᵢ$ 8) ).
  clear - Hart2 Hx Hp.
  unfold nat_of_Z in Hart2.
  lets Has : Z2Nat.inj Hart2.  
  clear.
  int auto.
  clear.
  int auto.
  eapply unsigned_inj; eauto.
  rewrite H.
  rewrite TcbMod.set_sem.
  erewrite tidspec.eq_beq_true; eauto.
  
  introv Hgets .
  destruct Hrp as (Hrp1 & Hrp2 & Hrp3).
  assert ( tcbid =   (ptcb_addr, Int.zero) \/ tcbid <>  (ptcb_addr, Int.zero)) by tauto.
  destruct H.
  subst tcbid.
  rewrite TcbMod.set_sem in Hgets.
  erewrite tidspec.eq_beq_true in Hgets; eauto.
  inverts Hgets.
  unfold nat_of_Z.
  lets Hxs : Hrp2 Hget2.
  destruct Hxs as (Hxs1 & Hxs2).
  split; auto.
  assert (exists xx,  nth_val (Z.to_nat (Int.unsigned (x>>ᵢ$ 8)))
                              (update_nth_val (Z.to_nat (Int.unsigned ptcb_prio)) v'32 (Vptr v'53)) =
                      Some xx).
  eapply nth_val_upd_ex; eauto.
  rewrite Hax.
  clear - Hx.
  remember ( (x>>ᵢ$ 8)) as px.
  clear Heqpx.
  mauto.
  destruct H.
(* ** ac:   Locate update_nth. *)
  Import pure_lib.
  eapply update_nth; eauto.
  rewrite TcbMod.set_sem in Hgets.
  erewrite tidspec.neq_beq_false in Hgets; eauto.
  assert ( tcbid =   (v'38, Int.zero)\/ tcbid <>   (v'38, Int.zero)) by tauto.
  destruct H0.
  subst tcbid.
  rewrite TcbMod.set_sem in Hgets.
  erewrite tidspec.eq_beq_true in Hgets; eauto.
  inverts Hgets.
  lets Hnsa : Hrp3 H Hget1 Hget2.
  lets Hxas : Hrp2 Hget1.
  destruct Hxas.
  split; auto.
  Open Scope code_scope.
  assert ( (∘(Int.unsigned prio) < length v'32)%nat).
  rewrite Hax.
  clear -Hcr.
  mauto.
(* ** ac:   Locate ">>ᵢ". *)
  Open Scope int_scope.
  assert (∘(Int.unsigned prio) =  (Z.to_nat (Int.unsigned (x>>ᵢ$ 8))) \/
          ∘(Int.unsigned prio) <>(Z.to_nat (Int.unsigned (x>>ᵢ$ 8)))) by tauto.
  destruct H3.
  rewrite <- H3 in Hnth.
  apply   nth_val'_imply_nth_val in Hnth; auto.
  rewrite Hnth in H0.
  inverts H0.
  tryfalse.
  eapply nth_upd_neqrev; eauto.
  assert ( ∘(Int.unsigned prio) <>  (Z.to_nat (Int.unsigned ptcb_prio))).
  unfold nat_of_Z.
  introv Hf.
  apply Hnsa.
  lets Has : Z2Nat.inj Hf.  
  clear .
  int auto.
  clear.
  int auto.
  eapply unsigned_inj; eauto.
  eapply nth_upd_neqrev; eauto.
  rewrite TcbMod.set_sem in Hgets.
  rewrite tidspec.neq_beq_false in Hgets; eauto.
  lets Hnsa : Hrp3 H0 Hgets Hget1 .
  lets Hnsaa :  Hrp3 H Hgets Hget2 .
  lets Hxasx : Hrp2 Hgets.
  destruct Hxasx.
  assert (∘(Int.unsigned prio) =  (Z.to_nat (Int.unsigned (x>>ᵢ$ 8))) \/
          ∘(Int.unsigned prio) <>(Z.to_nat (Int.unsigned (x>>ᵢ$ 8)))) by tauto.
  destruct H3.
  rewrite <- H3 in Hnth.
  apply   nth_val'_imply_nth_val in Hnth; auto.
  rewrite Hnth in H1.
  inverts H1.
  tryfalse.
  rewrite Hax.
  rewrite H3.
  clear -Hx.
  remember (x>>ᵢ$ 8) as Px.
  clear HeqPx.
  mauto.
  split; auto.
  eapply nth_upd_neqrev; eauto.
  assert ( ∘(Int.unsigned prio) <>  (Z.to_nat (Int.unsigned ptcb_prio))).
  unfold nat_of_Z.
  introv Hf.
  apply Hnsaa.
  lets Has : Z2Nat.inj Hf.  
  clear .
  int auto.
  clear.
  int auto.
  eapply unsigned_inj; eauto.
  eapply nth_upd_neqrev; eauto.

  unfolds.
  intros.
  unfolds in Hrp.
  destruct Hrp as (Hpr1 & Hpr2 & Hpr3).
  unfolds in Hpr3.
  assert ( (ptcb_addr, Int.zero) <> tid \/(ptcb_addr, Int.zero) = tid ) by tauto.
  destruct H2.
  rewrite TcbMod.set_sem in H0.
  rewrite tidspec.neq_beq_false in H0; eauto.
  assert (  (v'38, Int.zero) <> tid \/   (v'38, Int.zero) = tid ) by tauto.
  destruct H3.
  rewrite TcbMod.set_sem in H0.
  rewrite tidspec.neq_beq_false in H0; eauto.

  assert ( (ptcb_addr, Int.zero) <> tid' \/(ptcb_addr, Int.zero) = tid' ) by tauto.
  destruct H4.
  rewrite TcbMod.set_sem in H1.
  rewrite tidspec.neq_beq_false in H1; eauto.
  assert (  (v'38, Int.zero) <> tid' \/   (v'38, Int.zero) = tid' ) by tauto.
  destruct H5.
  rewrite TcbMod.set_sem in H1.
  rewrite tidspec.neq_beq_false in H1; eauto.
  rewrite TcbMod.set_sem in H1.
  rewrite tidspec.eq_beq_true in H1; eauto.
  inverts H1.
  lets Hrxx : Hpr3 H0 Hget1; eauto.

  rewrite TcbMod.set_sem in H1.
  rewrite tidspec.eq_beq_true in H1; eauto.
  inverts H1.
  assert ( prio <> x>>ᵢ$ 8 \/  prio = x>>ᵢ$ 8) by tauto.
  destruct H1; auto.
  rewrite <-H1 in Hnth.
  apply   nth_val'_imply_nth_val in Hnth; auto.
  lets Hxxas : Hpr2 H0.
  destruct Hxxas.
  unfold nat_of_Z in H5.
  rewrite Hnth in H5.
  inverts H5; tryfalse.
  rewrite Hax.
  rewrite <- H1 in Hx.
  clear - Hx.
  mauto.

  rewrite TcbMod.set_sem in H0.
  rewrite tidspec.eq_beq_true in H0; eauto.
  inverts H0.
  rewrite H3 in H1.
  rewrite TcbMod.set_sem in H1.
  assert ( (ptcb_addr, Int.zero) <> tid' \/(ptcb_addr, Int.zero) = tid' ) by tauto.
  destruct H0.
  rewrite tidspec.neq_beq_false in H1; eauto.
  rewrite TcbMod.set_sem in H1.
  rewrite tidspec.neq_beq_false in H1; eauto.
  rewrite <- H3 in H.
  eauto.
  rewrite tidspec.eq_beq_true in H1; eauto.
  inverts H1.
  assert ( prio <> x>>ᵢ$ 8 \/  prio = x>>ᵢ$ 8) by tauto.
  destruct H1; auto.
  rewrite <-H1 in Hnth.
  apply   nth_val'_imply_nth_val in Hnth; auto.
  lets Hxxas : Hpr2 Hget1.
  destruct Hxxas.
  unfold nat_of_Z in H4.
  rewrite Hnth in H4.
  inverts H4; tryfalse.
  rewrite Hax.
  rewrite <- H1 in Hx.
  clear - Hx.
  mauto.
  rewrite TcbMod.set_sem in H0.
  rewrite tidspec.eq_beq_true in H0; eauto.
  inverts H0.

  assert ( (ptcb_addr, Int.zero) <> tid' \/(ptcb_addr, Int.zero) = tid' ) by tauto.
  destruct H0.
  rewrite TcbMod.set_sem in H1.
  rewrite tidspec.neq_beq_false in H1; eauto.
  assert (  (v'38, Int.zero) <> tid' \/   (v'38, Int.zero) = tid' ) by tauto.
  destruct H3.
  rewrite TcbMod.set_sem in H1.
  rewrite tidspec.neq_beq_false in H1; eauto.

  assert ( prio' <> x>>ᵢ$ 8 \/  prio' = x>>ᵢ$ 8) by tauto.
  destruct H4; auto.
  rewrite <-H4 in Hnth.
  apply   nth_val'_imply_nth_val in Hnth; auto.
  lets Hxxas : Hpr2 H1.
  destruct Hxxas.
  unfold nat_of_Z in H5.
  rewrite Hnth in H5.
  inverts H4; tryfalse.
  rewrite Hax.
  rewrite <- H4 in Hx.
  clear - Hx.
  mauto.
  rewrite TcbMod.set_sem in H1.
  rewrite tidspec.eq_beq_true in H1; eauto.
  inverts H1.

  assert ( prio' <> x>>ᵢ$ 8 \/  prio' = x>>ᵢ$ 8) by tauto.
  destruct H1; auto.
  rewrite <-H1 in Hnth.
  apply   nth_val'_imply_nth_val in Hnth; auto.
  lets Hxxas : Hpr2 Hget1.
  destruct Hxxas.
  unfold nat_of_Z in H4.
  rewrite Hnth in H4.
  inverts H4; tryfalse.
  rewrite Hax.
  rewrite <- H1 in Hx.
  clear - Hx.
  mauto.
  rewrite TcbMod.set_sem in H1.
  rewrite tidspec.eq_beq_true in H1; eauto.
  inverts H1.
  tryfalse.
Qed.



  
(*
Put in OSMutex_common.v

Lemma RL_RTbl_PrioTbl_P_set:
  forall x vhold rtbl ptbl x4 x5 ptcb_addr,
    Int.unsigned x < 64 ->
    (length rtbl = 8)%nat ->
    (length ptbl = 64)%nat ->
    (ptcb_addr, Int.zero) <> vhold -> 
    nth_val' (Z.to_nat (Int.unsigned (x&$ 7))) OSMapVallist =
    Vint32 x4 ->
    nth_val' (Z.to_nat (Int.unsigned (x>>ᵢ$ 3)))
             rtbl = Vint32 x5 ->
    RL_RTbl_PrioTbl_P rtbl ptbl vhold ->
    RL_RTbl_PrioTbl_P
      (update_nth_val (Z.to_nat (Int.unsigned (x>>ᵢ$ 3)))
                      rtbl (Vint32 (Int.or x5 x4)))
      (update_nth_val (Z.to_nat (Int.unsigned x))
                      ptbl
                      (Vptr (ptcb_addr, Int.zero))) vhold.
Proof.
  introv Hx Hlen Hlen2 Hneq Hnth1 Hnth2 Hrl.
  lets Hxa : math_mapval_core_prop Hnth1.
  clear - Hx.
  mauto.
  rewrite Hxa.
  unfolds.
  introv Hp Hprio.
  unfolds in Hrl.
  assert (p <> x \/ p = x) by tauto.
  destruct H.
  assert (  prio_in_tbl p rtbl).
  eapply prio_set_rdy_in_tbl_rev with (prio0:=p)(prio:=x); eauto.
  clear -Hx.
  split; auto.
  clear.
  int auto.
  apply   nth_val'_imply_nth_val.
  rewrite Hlen.
  clear - Hx.
  mauto.
  unfold nat_of_Z.
  auto.
  lets Hxas : Hrl Hp H0.
  destruct Hxas as (tid & Hnt & Hne).
  exists tid.
  split; auto.
  eapply nth_upd_neqrev; eauto.
  introv Hf.
  apply H.
  lets Has : Z2Nat.inj Hf.  
  clear .
  int auto.
  clear.
  int auto.
  eapply unsigned_inj; eauto.
  exists  (ptcb_addr, Int.zero).
  split; auto.
  rewrite H.
  assert ( (Z.to_nat (Int.unsigned x)) < length ptbl)%nat.
  rewrite Hlen2.
  clear - Hx.
  mauto.
  lets Hxs: nth_val_exx H0.
  mytac.
  eapply aux_for_hoare_lemmas.update_nth; eauto.
Qed.
*)
  

Ltac simpl_vqm :=
  repeat
    match goal with
      | H: ?f _ = Some _ |- _ => simpl in H;inverts H
      | _ => idtac
    end.

Open Scope Z_scope.

Lemma neg_priointbl_prionotintbl:
  forall p tbl,
    Int.unsigned p < 64 ->
     array_type_vallist_match Int8u tbl ->
  length tbl = ∘OS_RDY_TBL_SIZE ->
    ~ prio_in_tbl p tbl -> prio_not_in_tbl p tbl.
Proof.
  intros.
  lets Hxxa : prio_rtbl_dec p H0 H1.
  clear - H.
  mauto.
  destruct Hxxa; auto.
  tryfalse.
Qed.


Lemma R_TCB_Status_mutexpend_lift:
  forall cur_prio ptcb_prio prio_lift x0 v'26 x12 i5 v'64 v'65 i1 v'45 v'43 x11 xm i8
         ptcb_tcby ptcb_bitx ptcb_bity v'46 v'67 x5 v0 os_rdy_tbl i,
    length os_rdy_tbl = ∘OS_RDY_TBL_SIZE ->(*added*)
    array_type_vallist_match Int8u
          (update_nth_val ∘(Int.unsigned v'64)
             (update_nth_val (Z.to_nat (Int.unsigned (prio_lift>>ᵢ$ 3)))
                (update_nth_val (Z.to_nat (Int.unsigned ptcb_tcby))
                   os_rdy_tbl (Vint32 (v0&ᵢInt.not ptcb_bitx)))
                (val_inj
                   (or
                      (nth_val' (Z.to_nat (Int.unsigned (prio_lift>>ᵢ$ 3)))
                         (update_nth_val (Z.to_nat (Int.unsigned ptcb_tcby))
                            os_rdy_tbl (Vint32 (v0&ᵢInt.not ptcb_bitx))))
                      (Vint32 ($ 1<<ᵢ(prio_lift&ᵢ$ 7))))))
             (Vint32 (v'67&ᵢInt.not v'65))) -> (*added*)

    cur_prio <> ptcb_prio ->
    ptcb_prio <> prio_lift ->
    nth_val' (Z.to_nat (Int.unsigned ptcb_tcby)) os_rdy_tbl = Vint32 v0 ->
    nth_val' (Z.to_nat (Int.unsigned (prio_lift>>ᵢ$ 3)))
             (update_nth_val (Z.to_nat (Int.unsigned ptcb_tcby)) os_rdy_tbl
                             (Vint32 (v0&ᵢInt.not ptcb_bitx))) = Vint32 x5 ->
    Int.unsigned prio_lift < 64 ->
    TCBNode_P
      (x0
         :: v'26
         :: x12
         :: Vnull
         :: V$0
         :: V$OS_STAT_RDY
         :: Vint32 cur_prio
         :: Vint32 i5
         :: Vint32 v'64
         :: Vint32 v'65 :: Vint32 i1 :: nil)
      os_rdy_tbl (cur_prio, rdy, Vnull) ->
    RL_TCBblk_P
      (v'45
         :: v'43
         :: x11
         :: xm
         :: V$0
         :: V$OS_STAT_RDY
         :: Vint32 ptcb_prio
         :: Vint32 i8
         :: Vint32 ptcb_tcby
         :: Vint32 ptcb_bitx
         :: Vint32 ptcb_bity :: nil) ->
    Int.ltu prio_lift cur_prio = true -> (*added*)
    nth_val ∘(Int.unsigned v'64)  (* added *)
          (update_nth_val (Z.to_nat (Int.unsigned (prio_lift>>ᵢ$ 3)))
             (update_nth_val (Z.to_nat (Int.unsigned ptcb_tcby)) os_rdy_tbl
                (Vint32 (v0&ᵢInt.not ptcb_bitx)))
             (val_inj
                (or
                   (nth_val' (Z.to_nat (Int.unsigned (prio_lift>>ᵢ$ 3)))
                      (update_nth_val (Z.to_nat (Int.unsigned ptcb_tcby))
                         os_rdy_tbl (Vint32 (v0&ᵢInt.not ptcb_bitx))))
                   (Vint32 ($ 1<<ᵢ(prio_lift&ᵢ$ 7)))))) = 
        Some (Vint32 v'67) ->
    R_TCB_Status_P
      (x0
         :: v'26
         :: Vptr (v'46, Int.zero)
         :: Vnull
         :: Vint32 i
         :: V$OS_STAT_MUTEX
         :: Vint32 cur_prio
         :: Vint32 i5
         :: Vint32 v'64 :: Vint32 v'65 :: Vint32 i1 :: nil)
      (update_nth_val ∘(Int.unsigned v'64)
                      (update_nth_val (Z.to_nat (Int.unsigned (prio_lift>>ᵢ$ 3)))
                                      (update_nth_val (Z.to_nat (Int.unsigned ptcb_tcby)) os_rdy_tbl
                                                      (Vint32 (v0&ᵢInt.not ptcb_bitx)))
                                      (Vint32 (Int.or x5 ($ 1<<ᵢ(prio_lift&ᵢ$ 7)))))
                      (Vint32 (v'67&ᵢInt.not v'65)))
      (cur_prio, wait (os_stat_mutexsem (v'46, Int.zero)) i, Vnull).
Proof.
  introv Hlea Har.
  intros.
  unfolds in H5.
  unfolds in H4.
  mytac.
  unfolds in H9.
  mytac.
  rewrite H2 in H7.
  simpl in H7.
  apply nth_val_nth_val'_some_eq in H7;auto.
  simpl_vqm.
  unfolds.

  splits;unfolds;intros.
  unfolds in H4.
  destruct H4.
  unfolds in H4;simpl in H4;inverts H4.
  assert ( ~prio_in_tbl prio
         (update_nth_val ∘(Int.unsigned (prio>>ᵢ$ 3))
            (update_nth_val (Z.to_nat (Int.unsigned (prio_lift>>ᵢ$ 3)))
               (update_nth_val (Z.to_nat (Int.unsigned (x>>ᵢ$ 3))) os_rdy_tbl
                  (Vint32 (v0&ᵢInt.not ($ 1<<ᵢ(x&ᵢ$ 7)))))
               (Vint32 (Int.or x5 ($ 1<<ᵢ(prio_lift&ᵢ$ 7)))))
            (Vint32 (v'67&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7)))))).
  {
    eapply prio_update_self_not_in;eauto.
    apply nth_val'2nth_val;auto.
  }
  tryfalse.

  inverts H4.
  splits;unfolds;intros.
  unfolds in H5;simpl in H5;inverts H5.
  unfolds in H5;simpl in H5;inverts H5.
  unfolds in H5;simpl in H5;inverts H5.
  unfolds in H5;simpl in H5;inverts H5.
  simpl_vqm.
  unfolds in H4.
  mytac.
  simpl_vqm.
  eexists;eauto.
  

  splits;unfolds;intros.
  inverts H4.
  inverts H4.
  inverts H4.
  inverts H4.
  inverts H4.
  splits.
  unfolds.
  splits.
  unfolds;simpl;auto.
  assert ( ~prio_in_tbl prio
         (update_nth_val ∘(Int.unsigned (prio>>ᵢ$ 3))
            (update_nth_val (Z.to_nat (Int.unsigned (prio_lift>>ᵢ$ 3)))
               (update_nth_val (Z.to_nat (Int.unsigned (x>>ᵢ$ 3))) os_rdy_tbl
                  (Vint32 (v0&ᵢInt.not ($ 1<<ᵢ(x&ᵢ$ 7)))))
               (Vint32 (Int.or x5 ($ 1<<ᵢ(prio_lift&ᵢ$ 7)))))
            (Vint32 (v'67&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7)))))).
  eapply prio_update_self_not_in;eauto.
  apply nth_val'2nth_val;auto.
  eapply neg_priointbl_prionotintbl;eauto.
  rewrite H2 in Har.
  simpl in Har;auto.
  rewrite update_nth_val_len_eq.
  rewrite update_nth_val_len_eq.
  rewrite update_nth_val_len_eq.
  auto.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
Qed.



(*moved to OSMutex_common*)
(*
Lemma vhold_not_get:
  forall tcbls_l tcbls_r tcbls ct cur_prio x2 v'32 v'53 phold,
    TcbMod.join tcbls_l tcbls_r tcbls ->
    TcbJoin ct (cur_prio, rdy, Vnull) x2 tcbls_r -> 
    R_PrioTbl_P v'32 tcbls v'53 ->
    nth_val' (Z.to_nat (Int.unsigned phold)) v'32 =
    Vptr v'53 ->
    forall (tid : tidspec.A) (p : priority) (s0 : taskstatus) (m : msg),
      TcbMod.get x2 tid = Some (p, s0, m) -> p <> phold.
Proof.
  intros.
  unfolds in H1.
  destructs H1.
  unfolds in H5.
  assert (TcbMod.get tcbls tid = Some (p,s0,m)).
  eapply TcbMod.join_get_r;eauto.
  eapply tcbjoin_get_get_my;eauto.
  clear H3.
  intro.
  subst p.
  lets Hx:H4 H6.
  destruct Hx.
  apply nth_val_nth_val'_some_eq in H3;auto.
  unfold nat_of_Z in H3.
  rewrite H3 in H2.
  inverts H2.
  tryfalse.
Qed.




Lemma vhold_not_get'
: forall (tcbls_l tcbls_r tcbls : TcbMod.map) 
         (v'32 : vallist) (v'53 : addrval) (phold : int32),
    TcbMod.join tcbls_l tcbls_r tcbls ->
    R_PrioTbl_P v'32 tcbls v'53 ->
    nth_val' (Z.to_nat (Int.unsigned phold)) v'32 = Vptr v'53 ->
    forall (tid : tidspec.A) (p : priority) (s0 : taskstatus) (m : msg),
      TcbMod.get tcbls_l tid = Some (p, s0, m) -> p <> phold.
Proof.
  intros.
  unfolds in H0.
  mytac.
  assert (TcbMod.get tcbls tid = Some (p,s0,m)).
  eapply TcbMod.join_get_l;eauto.
  clear H2.
  intro.
  subst p.
  apply H3 in H5.
  destruct H5.
  unfold nat_of_Z in H2.
  apply nth_val_nth_val'_some_eq in H2;auto.
  rewrite H1 in H2;inverts H2.
  tryfalse.
Qed.


Lemma tcbls_l_mutexpend:
  forall prio_lift  ptcb_prio v'33 v'34 v'45 v'43 x11 xm i8 ptcb_tcby ptcb_bitx ptcb_bity v'36 os_rdy_tbl tcbls_l v'32 tcbls_r tcbls ptcb_addr v0 x5 vhold,
    
    get_last_tcb_ptr v'34 v'33 = Some (Vptr (ptcb_addr,Int.zero)) -> (*added*)
    nth_val' (Z.to_nat (Int.unsigned prio_lift)) v'32 =
                  Vptr vhold -> (*added*)
    TcbMod.join tcbls_l tcbls_r tcbls ->
    R_PrioTbl_P v'32 tcbls vhold ->
    Int.unsigned prio_lift < 64 -> 
    ptcb_prio <>  prio_lift->
    TcbMod.get tcbls_l (ptcb_addr, Int.zero) =
    Some (ptcb_prio, rdy, xm) ->
    nth_val' (Z.to_nat (Int.unsigned ptcb_tcby)) os_rdy_tbl =
    Vint32 v0 ->
    nth_val' (Z.to_nat (Int.unsigned (prio_lift>>ᵢ$ 3)))
             (update_nth_val (Z.to_nat (Int.unsigned ptcb_tcby)) os_rdy_tbl
                             (Vint32 (v0&Int.not ptcb_bitx))) = Vint32 x5 ->
    TCBList_P v'33
              (v'34 ++
                    (v'45
                       :: v'43
                       :: x11
                       :: xm
                       :: V$0
                       :: V$OS_STAT_RDY
                       :: Vint32 ptcb_prio
                       :: Vint32 i8
                       :: Vint32 ptcb_tcby
                       :: Vint32 ptcb_bitx
                       :: 
                       Vint32 ptcb_bity :: nil)
                    :: v'36) os_rdy_tbl tcbls_l ->
    TCBList_P v'33
              (v'34 ++
                    (v'45
                       :: v'43
                       :: x11
                       :: xm
                       :: V$0
                       :: V$OS_STAT_RDY
                       :: Vint32 prio_lift
                       :: Vint32 (prio_lift&$ 7)
                       :: Vint32 (prio_lift>>ᵢ$ 3)
                       :: Vint32 ($ 1<<(prio_lift&$ 7)) :: Vint32 ($ 1<<(prio_lift>>ᵢ$ 3)) :: nil) :: v'36)
              (update_nth_val (Z.to_nat (Int.unsigned (prio_lift>>ᵢ$ 3)))
                              (update_nth_val (Z.to_nat (Int.unsigned ptcb_tcby)) os_rdy_tbl
                                              (Vint32 (v0&Int.not ptcb_bitx)))
                              (Vint32 (Int.or x5 ($ 1<<(prio_lift&$ 7)))))
              (TcbMod.set tcbls_l (ptcb_addr, Int.zero) (prio_lift, rdy, xm)).
Proof.
  introv Hlast Hhold.
  intros.
  apply TCBList_P_Split in H6.
  mytac.
  simpl in H9.
  mytac.
  unfolds in H10;simpl in H10;inverts H10.
  eapply TCBList_P_Combine;eauto.
  instantiate (1:= TcbMod.set x1 (ptcb_addr, Int.zero) (prio_lift, rdy, xm)).
  eapply TcbMod.join_set_r;eauto.
  unfolds.
  rewrite Hlast in H6;inverts H6.
  exists x6.
  eapply tcbjoin_get_a_my;eauto.
  eapply TCBList_P_rtbl_add_simpl_version;eauto.
  split;auto.
  clear;int auto.
  apply nth_val'2nth_val;auto.
  assert (forall (tid : tidspec.A) (p : priority) (s : taskstatus) (m : msg),
   TcbMod.get tcbls_l tid = Some (p, s, m) -> p <> prio_lift).
  eapply vhold_not_get';eauto.
  intros.
  eapply H9;eauto.
  eapply TcbMod.join_get_l;eauto.
  destruct x6.
  destruct p as (p&st).
  eapply TCBList_P_tcb_block_hold' with (tcs:= x1) (tcs':=tcbls_l) (prio:=p);eauto.
  clear -H12.
  unfolds in H12.
  mytac_H.
  unfolds in H1.
  mytac_H.
  simpl_vqm.
  auto.
  eapply tcbjoin_get_a_my;eauto.
  clear -H12.
  unfolds in H12.
  mytac_H.
  unfolds in H1.
  mytac_H.
  simpl_vqm.
  auto.
  clear -H12.
  unfolds in H12.
  mytac_H.
  unfolds in H1.
  mytac_H.
  simpl_vqm.
  auto.
  unfolds in H12.
  mytac_H.
  unfolds in H12.
  mytac_H.
  symmetry in H6.
  symmetry in Hlast.
  symmetry in H3.
  simpl_vqm.
  eapply TcbMod_join_impl_prio_neq_cur_l;eauto.
  eapply TcbMod_join_impl_prio_neq_cur_l;eauto.
  eapply R_PrioTbl_P_impl_prio_neq_cur;eauto.
  eapply TcbMod.join_get_l;eauto.
  eapply TcbMod.join_get_r;eauto.
  eapply tcbjoin_get_a_my;eauto.
  clear -H12 H4.
  unfolds in H12.
  mytac.
  unfolds in H1.
  mytac.
  simpl_vqm.
  apply nth_val'2nth_val;auto.
  simpl.
  rewrite Hlast in H6;inverts H6.
  do 4 eexists;splits;eauto.
  unfolds;simpl;eauto.
  instantiate (1:= x4).
  instantiate (1:= (prio_lift, rdy, xm)).
  eapply tcbjoin_set_my;eauto.
  destruct x6.
  destruct p.
  unfolds in H12.
  mytac.
  unfolds in H10.
  mytac.
  symmetry in Hlast.
  symmetry in H3.
  simpl_vqm.
  unfolds.
  mytac.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  unfolds.
  do 6 eexists;splits.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  split;auto.
  clear;int auto.
  splits;auto.
  eexists;split.
  unfolds;simpl;auto.
  intros.
  apply H26;auto.
  unfolds in H12.
  mytac.
  unfolds.
  splits;unfolds;intros.
  unfolds in H14.
  mytac_H.
  simpl_vqm.
  splits.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  eexists;auto.
  inverts H14.
  splits.
  2:unfolds;simpl;auto.
  2:unfolds;simpl;auto.
  unfolds.
  splits.
  unfolds;simpl;auto.
  eapply prio_in_tbl_orself;eauto.
  splits;unfolds;intros.
  unfolds in H14.
  mytac_H.
  simpl_vqm.
  assert (~prio_not_in_tbl prio
          (update_nth_val (Z.to_nat (Int.unsigned (prio>>ᵢ$ 3)))
             (update_nth_val (Z.to_nat (Int.unsigned (p>>ᵢ$ 3))) os_rdy_tbl
                (Vint32 (v0&Int.not ($ 1<<(p&$ 7)))))
             (Vint32 (Int.or x5 ($ 1<<(prio&$ 7)))))).
  eapply prio_notin_tbl_orself;eauto.
  apply nth_val'2nth_val;auto.
  false.
  simpl_vqm;false.
  simpl_vqm;false.
  simpl_vqm;false.
  simpl_vqm;false.
  splits;unfolds;intros.
  inverts H14.
  inverts H14.
  inverts H14.
  inverts H14.
  inverts H14.

  eapply TCBList_P_rtbl_add_simpl_version;eauto.
  split;auto.
  clear;int auto.
  apply nth_val'2nth_val;auto.
  assert (forall (tid : tidspec.A) (p : priority) (s : taskstatus) (m : msg),
   TcbMod.get tcbls_l tid = Some (p, s, m) -> p <> prio_lift).
  eapply vhold_not_get';eauto.
  intros.
  destruct x6.
  destruct p0.
  eapply H6;eauto.
  eapply TcbMod.join_get_r;eauto.
  eapply tcbjoin_get_get;eauto.
  destruct x6.
  destruct p.
   unfolds in H12.
  mytac_H.
  unfolds in H1.
  mytac_H.
  symmetry in Hlast.
  symmetry in H3.
  simpl_vqm.
  eapply TCBList_P_tcb_block_hold' with (tcs:= TcbMod.sig (ptcb_addr, Int.zero) (p, t, m)) (tcs':=x1) (prio:=p);eauto.
  clear -H10.
  unfolds in H10.
  mytac_H.
  simpl_vqm.
  auto.
  rewrite TcbMod.sig_sem.
  rewrite tidspec.eq_beq_true;eauto.
  unfolds in H11.
  apply TcbMod.join_comm;auto.
  clear -H10.
  unfolds in H10.
  mytac_H.
  simpl_vqm.
  auto.
  clear -H10.
  unfolds in H10.
  mytac_H.
  simpl_vqm.
  auto.
  eapply TcbMod_join_impl_prio_neq_cur_r;eauto.
  eapply TcbMod_join_impl_prio_neq_cur_r;eauto.
  eapply TcbMod_join_impl_prio_neq_cur_l;eauto.
  eapply R_PrioTbl_P_impl_prio_neq_cur;eauto.
  clear -H10.
  unfolds in H10.
  mytac_H.
  simpl_vqm.
  auto.
  eapply tcbjoin_get_a_my in H11;eauto.
  eapply TcbMod.join_get_l;eauto.
  apply nth_val'2nth_val;auto.
Qed.



Lemma ecblist_p_mutexpend_changeprio:
  forall ectl tcbls v'44  edatal ecbls ptcb_addr ptcb_prio xm prio_lift,
    TcbMod.get tcbls (ptcb_addr, Int.zero) = Some (ptcb_prio, rdy, xm) -> 
    ECBList_P v'44 Vnull ectl edatal ecbls tcbls ->
    ECBList_P v'44 Vnull ectl edatal ecbls (TcbMod.set tcbls (ptcb_addr, Int.zero) (prio_lift, rdy, xm)).
Proof.
  inductions ectl;intros.
  simpl in H0.
  mytac.
  simpl;auto.
  simpl in H0.
  mytac.
  simpl.
  destruct edatal.
  false.
  destruct a.
  mytac.
  eexists;split;eauto.
  split.
  2:do 3 eexists;splits;eauto.
  unfolds in H1.
  mytac.
  unfolds.
  splits;auto.
  unfolds.
  unfolds in H1.
  mytac.
  unfolds in H1.
  unfolds.
  intros.
  lets Hx:H1 H10 H11.
  mytac.
  assert (x3 = (ptcb_addr, Int.zero) \/ x3 <> (ptcb_addr, Int.zero)) by tauto.
  destruct H13.
  subst.
  rewrite H in H12;inverts H12.
  do 3 eexists.
  rewrite TcbMod.set_a_get_a';eauto.
  eapply tidspec.neq_beq_false;eauto.
  unfolds in H7.
  unfolds.
  intros.
  lets Hx:H7 H10 H11.
  mytac.
  assert (x3 = (ptcb_addr, Int.zero) \/ x3 <> (ptcb_addr, Int.zero)) by tauto.
  destruct H13.
  subst.
  rewrite H in H12;inverts H12.
  do 3 eexists.
  rewrite TcbMod.set_a_get_a';eauto.
  eapply tidspec.neq_beq_false;eauto.  
  unfolds in H8.
  unfolds.
  intros.
  lets Hx:H8 H10 H11.
  mytac.
  assert (x3 = (ptcb_addr, Int.zero) \/ x3 <> (ptcb_addr, Int.zero)) by tauto.
  destruct H13.
  subst.
  rewrite H in H12;inverts H12.
  do 3 eexists.
  rewrite TcbMod.set_a_get_a';eauto.
  eapply tidspec.neq_beq_false;eauto.
  unfolds in H9.
  unfolds.
  intros.
  lets Hx:H9 H10 H11.
  mytac.
  assert (x3 = (ptcb_addr, Int.zero) \/ x3 <> (ptcb_addr, Int.zero)) by tauto.
  destruct H13.
  subst.
  rewrite H in H12;inverts H12.
  do 3 eexists.
  rewrite TcbMod.set_a_get_a';eauto.
  eapply tidspec.neq_beq_false;eauto.
  
  unfolds.
  unfolds in H5.
  mytac.
  unfolds;intros.
  unfolds in H5.
  assert (tid = (ptcb_addr, Int.zero) \/ tid <> (ptcb_addr, Int.zero)) by tauto.
  destruct H11.
  subst tid.
  rewrite TcbMod.set_a_get_a in H10.
  inverts H10.
  apply tidspec.eq_beq_true;auto.
  rewrite TcbMod.set_a_get_a' in H10.
  eapply H5;eauto.
  apply tidspec.neq_beq_false;auto.

  unfolds;intros.
  unfolds in H7.
  assert (tid = (ptcb_addr, Int.zero) \/ tid <> (ptcb_addr, Int.zero)) by tauto.
  destruct H11.
  subst tid.
  rewrite TcbMod.set_a_get_a in H10.
  inverts H10.
  apply tidspec.eq_beq_true;auto.
  rewrite TcbMod.set_a_get_a' in H10.
  eapply H7;eauto.
  apply tidspec.neq_beq_false;auto.

  unfolds;intros.
  unfolds in H8.
  assert (tid = (ptcb_addr, Int.zero) \/ tid <> (ptcb_addr, Int.zero)) by tauto.
  destruct H11.
  subst tid.
  rewrite TcbMod.set_a_get_a in H10.
  inverts H10.
  apply tidspec.eq_beq_true;auto.
  rewrite TcbMod.set_a_get_a' in H10.
  eapply H8;eauto.
  apply tidspec.neq_beq_false;auto.

  unfolds;intros.
  unfolds in H9.
  assert (tid = (ptcb_addr, Int.zero) \/ tid <> (ptcb_addr, Int.zero)) by tauto.
  destruct H11.
  subst tid.
  rewrite TcbMod.set_a_get_a in H10.
  inverts H10.
  apply tidspec.eq_beq_true;auto.
  rewrite TcbMod.set_a_get_a' in H10.
  eapply H9;eauto.
  apply tidspec.neq_beq_false;auto.
Qed.




Lemma RH_TCBList_ECBList_P_changeprio:
  forall ptcb_prio tid tcbls ecbls pcur xm p',
    TcbMod.get tcbls tid = Some (ptcb_prio, rdy, xm)->
    RH_TCBList_ECBList_P ecbls tcbls pcur ->
    RH_TCBList_ECBList_P ecbls (TcbMod.set tcbls tid (p',rdy,xm)) pcur.
Proof.
  introv Ht Hrh.
  unfolds in Hrh.
  destruct Hrh as (Hrh1 & Hrh2 & Hrh3 & Hrh4).
  unfolds.
  split.
  unfolds.
  split.
  intros.
  apply Hrh1 in H.
  mytac.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H0.
  subst.
  rewrite H in Ht; inverts Ht.
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false ; eauto.
  intros.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H0.
  subst.
  rewrite  TcbMod.set_sem  in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false  in H; auto.
  eapply Hrh1 in H.
  eauto.

  split.
  unfolds.
  split.
  intros.
  apply Hrh2 in H.
  mytac.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H0.
  subst.
  rewrite H in Ht; inverts Ht.
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false ; eauto.
  intros.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H0.
  subst.
  rewrite  TcbMod.set_sem  in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false  in H; auto.
  eapply Hrh2 in H.
  eauto.

  split.
  unfolds.
  split.
  intros.
  apply Hrh3 in H.
  mytac.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H0.
  subst.
  rewrite H in Ht; inverts Ht.
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false ; eauto.
  intros.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H0.
  subst.
  rewrite  TcbMod.set_sem  in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false  in H; auto.
  eapply Hrh3 in H.
  eauto.


  split.
  intros.
  apply Hrh4 in H.
  mytac.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H0.
  subst.
  rewrite H in Ht; inverts Ht.
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false ; eauto.
  split.
  intros.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H0.
  subst.
  rewrite  TcbMod.set_sem  in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false  in H; auto.
  eapply Hrh4 in H.
  eauto.

  unfolds.
  destruct Hrh4.
  destruct H0.
  unfolds in H1.
  intros.
  apply H1 in H2.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H3.
  subst.
  rewrite  TcbMod.set_sem .
  rewrite tidspec.eq_beq_true ; eauto.
  rewrite  TcbMod.set_sem .
  rewrite tidspec.neq_beq_false ; eauto.
Qed.

*)
  
Lemma tcbdllseg_cons:
  forall s tid h p' tail tailnext l P pre,
    struct_type_vallist_match OS_TCB_flag h ->
    s |= Astruct (tid,Int.zero) OS_TCB_flag h **
         tcbdllseg p' (Vptr (tid,Int.zero)) tail tailnext l ** P ->
    V_OSTCBNext h = Some p' ->
    V_OSTCBPrev h = Some pre ->
    s |= tcbdllseg (Vptr (tid,Int.zero)) pre tail tailnext (h::l) ** P.
Proof.
  intros.
  unfold tcbdllseg.
  unfold1 dllseg.
  unfold node.
  sep auto.
Qed.

Lemma tcbdllseg_l_not_nil:
  forall head l rtbl tcbls tid v,
    TCBList_P head l rtbl tcbls ->
    TcbMod.get tcbls tid = Some v ->
    exists h l', l = h :: l'.
Proof.
  intros.
  destruct l.
  unfold TCBList_P in *.
  subst.
  rewrite TcbMod.emp_sem in H0.
  tryfalse.
  exists v0 l.
  auto.
Qed.  

(* ** ac: Print OS_TCB_flag. *)
Lemma dllseg_compose:
  forall (s : RstateOP) (P : asrt) (h hp t1 tn1 t2 tn2 : val)
         (l1 l2 : list vallist),
    s |= dllseg h hp t1 tn1 l1 OS_TCB_flag
      (fun vl : vallist => nth_val 1 vl)
      (fun vl : vallist => nth_val 0 vl) ** dllseg tn1 t1 t2 tn2 l2  OS_TCB_flag
      (fun vl : vallist => nth_val 1 vl)
      (fun vl : vallist => nth_val 0 vl)** P ->
    s |= dllseg h hp t2 tn2 (l1 ++ l2)  OS_TCB_flag
      (fun vl : vallist => nth_val 1 vl)
      (fun vl : vallist => nth_val 0 vl) ** P.
Proof.
  intros.
  generalize s P h hp t1 tn1 t2 tn2 l2 H.
  clear s P h hp t1 tn1 t2 tn2 l2 H.
  induction l1.
  intros.
  unfold tcbdllseg in H.
  unfold dllseg in H.
  fold dllseg in H.
  sep split in H.
  subst.
  simpl; auto.
  intros.
  simpl ( (a::l1) ++l2).

  unfold tcbdllseg in *.
  unfold dllseg in *.
  fold dllseg in *.
  sep normal.
  
  sep auto.

  apply astar_r_aemp_elim.
  eapply IHl1.
  sep auto.
  auto.
Qed.


Lemma ECBList_P_high_tcb_block_hold_mutex
: forall (ectrl : list EventCtr) (head tail : val)
         (msgql : list EventData) (ecbls : EcbMod.map) 
         (tcbls : TcbMod.map) (ptcb : tidspec.A) (prio : priority) 
         (m : msg) (qid : tidspec.A) (time : int32),
    ECBList_P head tail ectrl msgql ecbls tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, rdy, m) ->
    EcbMod.get ecbls qid = None ->
    ECBList_P head tail ectrl msgql ecbls
              (TcbMod.set tcbls ptcb (prio, wait (os_stat_mutexsem qid) time, m)).
Proof.
  inductions ectrl.
  intros.
  simpl.
  simpl in H.
  mytac.
  auto.  

  intros.
  simpl in H.
  mytac.
  destruct msgql; tryfalse.
  destruct a.
  mytac.
  simpl.
  exists x.
  splits; auto.
  unfolds.
  destruct H2 as (Hr1 & Hr2 & Hr3).
  destruct Hr1 as (Hra3 & Hra1 & Hra2 & Hra4).
  destruct Hr2 as (Hrb3 & Hrb1 & Hrb2 & Hrb4).
  simpl in Hr3.
  splits.
  unfolds.
  splits.
Focus 2.
{
  unfolds.
  intros.
  eapply Hra1 in H6;eauto.
  mytac.
  assert (x3 = ptcb \/ x3 <> ptcb) by tauto.
  destruct H7.
  subst.
  
  unfold get in *; simpl in *.
  rewrite H0 in H6.
  inverts H6.
  exists x3 x4 x5.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.
}
Unfocus.
Focus 2.
{
  unfolds.
  intros.
  eapply Hra2 in H6;eauto.
  mytac.
  assert (x3 = ptcb \/ x3 <> ptcb) by tauto.
  destruct H7.
  subst.
  unfold get in *; simpl in *.
  rewrite H0 in H6.
  inverts H6.
  exists x3 x4 x5.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.
}
Unfocus.
{
  unfolds.
  intros.
  eapply Hra3 in H6;eauto.
  mytac.
  assert (x3 = ptcb \/ x3 <> ptcb) by tauto.
  destruct H7.
  subst.
  unfold get in *; simpl in *.
  rewrite H0 in H6.
  inverts H6.
  exists x3 x4 x5.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.
}
{
  unfolds.
  intros.
  eapply Hra4 in H6;eauto.
  mytac.
  assert (x3 = ptcb \/ x3 <> ptcb) by tauto.
  destruct H7.
  subst.
  unfold get in *; simpl in *.
  rewrite H0 in H6.
  inverts H6.
  exists x3 x4 x5.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.
}
  unfolds.
  splits.
Focus 4.
{
  unfolds.
  intros.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.
  destruct H6.
  subst.
  rewrite TcbMod.set_sem in H2.
  rewrite tidspec.eq_beq_true in H2; eauto.
  inverts H2.
  apply ecbmod_joinsig_get in H3.
  rewrite H3 in H1.
  tryfalse.
  rewrite TcbMod.set_sem in H2.
  rewrite tidspec.neq_beq_false in H2; eauto.
}
Unfocus.

  unfolds.
  intros.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.
  destruct H6.
  subst.
  rewrite TcbMod.set_sem in H2.
  rewrite tidspec.eq_beq_true in H2; eauto.
  inverts H2.
  rewrite TcbMod.set_sem in H2.
  rewrite tidspec.neq_beq_false in H2; eauto.
  unfolds.
  intros.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.
  destruct H6.
  subst.
  rewrite TcbMod.set_sem in H2.
  rewrite tidspec.eq_beq_true in H2; eauto.
  inverts H2.
  rewrite TcbMod.set_sem in H2.
  rewrite tidspec.neq_beq_false in H2; eauto.
   unfolds.
  intros.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.
  destruct H6.
  subst.
  rewrite TcbMod.set_sem in H2.
  rewrite tidspec.eq_beq_true in H2; eauto.
  inverts H2.
  rewrite TcbMod.set_sem in H2.
  rewrite tidspec.neq_beq_false in H2; eauto.
  simpl; auto.
  do 3 eexists; splits; eauto.
  eapply IHectrl; eauto.
  eapply  ecbmod_joinsig_get_none; eauto.
Qed.

Lemma R_ECB_ETbl_P_high_tcb_block_hold_mutex:
  forall (l : addrval) (vl : vallist) (egrp : int32) 
         (v2 v3 v4 v5 : val) (etbl : vallist) (tcbls : TcbMod.map)
         (ptcb : tidspec.A) (prio : int32) (st : taskstatus) 
         (m : msg) (y bity bitx ey time : int32) (av : addrval),
    Int.unsigned prio < 64 ->
    R_PrioTbl_P vl tcbls av ->
    R_ECB_ETbl_P l
                 (V$OS_EVENT_TYPE_MUTEX :: Vint32 egrp :: v2 :: v3 :: v4 :: v5 :: nil,
                  etbl) tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, st, m) ->
    y = prio>>ᵢ$ 3 ->
    bity = $ 1<<ᵢy ->
    bitx = $ 1<<ᵢ(prio&ᵢ$ 7) ->
    nth_val ∘(Int.unsigned y) etbl = Some (Vint32 ey) ->
    R_ECB_ETbl_P l
                 (V$OS_EVENT_TYPE_MUTEX
                   :: Vint32 (Int.or egrp bity) :: v2 :: v3 :: v4 :: v5 :: nil,
                  update_nth_val ∘(Int.unsigned y) etbl (Vint32 (Int.or ey bitx)))
                 (TcbMod.set tcbls ptcb (prio, wait (os_stat_mutexsem l) time, m)).
Proof.
  introv Hran Hrs  Hre Htc Hy Hb1 Hb2 Hnth.
  subst.
  unfolds in Hre.
  destruct Hre as (Hre1 & Hre2 & Het).
  unfolds.
  splits.
  unfolds.
  splits.
  Focus 4.
{
  unfolds.
  intros.
  destruct Hre1 as (_ & _ & _ & Hre1).
  destruct Hre2 as (_ & _ & _ & Hre2).
  unfolds in Hre1.
  unfolds in Hre2.
  assert (prio = $ prio0 \/ prio <> $ prio0) by tauto.
  destruct H1.
  subst.
  exists ptcb time m.
  rewrite TcbMod.set_sem.
  erewrite tidspec.eq_beq_true; eauto.
  lets Hres : prio_wt_inq_keep Hran H1 Hnth .
  destruct Hres.
  apply H2 in H.
  apply Hre1 in H.
  mytac.
  exists x x0 x1.
  assert (x = ptcb \/ x <> ptcb) by tauto.
  destruct H4.
  subst.
  unfold get in *; simpl in *.
  rewrite Htc in H.
  inverts H.
  tryfalse.
  rewrite TcbMod.set_sem.
  erewrite tidspec.neq_beq_false; eauto.
  unfolds. 
  simpl; auto.
}
Unfocus.
Focus 2.
{
  unfolds.
  intros.
  usimpl H0.
}
Unfocus.
{
  unfolds.
  intros.
  usimpl H0.
}
{
   unfolds.
  intros.
  usimpl H0.
}
  unfolds.
  splits.
Focus 4.
{
  unfolds.
  intros.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.  
  destruct H0.
  subst.
  splits.
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  unfolds.
  rewrite Int.repr_unsigned.
  exists ( prio0&ᵢ$ 7).
  exists (Int.shru prio0 ($3)).
  exists ((Int.or ey ($ 1<<ᵢ(prio0&ᵢ$ 7)))).
  splits; eauto.
  clear - Hran.
  int auto.
  eapply update_nth; eauto.
  rewrite Int.and_commut.
  rewrite Int.or_commut.
  unfold Int.one.
  rewrite Int.and_or_absorb.
  auto.
  unfolds; simpl; auto.
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.neq_beq_false in H; eauto.
  unfolds in Hre2.
  destruct Hre2 as (_ & _ & _ & Hre2).
  lets Hasd : Hre2  H.
   destruct Hasd as (Has1 & Has2).
  splits.
  eapply prio_wt_inq_keep; eauto.
  rewrite Int.repr_unsigned.
  unfolds  in Hrs.
  destruct Hrs.
  destruct H2.
  unfolds in H3.
  lets Hdd : H3 H0 H Htc.
  eauto.
  unfolds; simpl; auto.
}
Unfocus.
Focus 2.
{
   unfolds.

  intros.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.  
  destruct H0.
  subst.
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.neq_beq_false in H; eauto.
  destruct Hre2 as (_&Hre2&_&_).
  apply Hre2 in H.
  destruct H.
  usimpl H1.
}
Unfocus.
{
   unfolds.
  intros.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.  
  destruct H0.
  subst.
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.neq_beq_false in H; eauto.
  destruct Hre2 as (Hre2&_).
  apply Hre2 in H.
  destruct H.
  usimpl H1.
}
   unfolds.
  intros.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.  
  destruct H0.
  subst.
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.neq_beq_false in H; eauto.
  destruct Hre2 as (_&_& Hre2 & _).
  apply Hre2 in H.
  destruct H.
  usimpl H1.
  simpl.
  unfolds.
  branch 4.
  unfolds; simpl; auto.
Qed.


Lemma TCBList_P_tcb_block_hold_mutex:
  forall (ptcb : addrval) (v1 v2 v3 v4 v5 : val) (v6 : int32) 
         (v8 : val) (v9 v10 : int32) (v11 : val) (rtbl : vallist)
         (vl : list (list val)) (tcbls : TcbMod.map) (prio : int32)
         (st : taskstatus) (m : msg) (qid : addrval) (time ry : int32),
    TCBList_P (Vptr ptcb)
              ((v1
                  :: v2
                  :: v3
                  :: v4
                  :: v5
                  :: Vint32 v6
                  :: Vint32 prio
                  :: v8 :: Vint32 v9 :: Vint32 v10 :: v11 :: nil) :: vl)
              rtbl tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, st, m) ->
    prio_neq_cur tcbls ptcb prio ->
    st = rdy \/ (exists n, st = wait os_stat_time n) ->
    nth_val ∘(Int.unsigned v9) rtbl = Some (Vint32 ry) ->
    TCBList_P (Vptr ptcb)
              ((v1
                  :: v2
                  :: Vptr qid
                  :: Vnull
                  :: Vint32 time
                  :: V$OS_STAT_MUTEX
                  :: Vint32 prio
                  :: v8 :: Vint32 v9 :: Vint32 v10 :: v11 :: nil) :: vl)
              (update_nth_val ∘(Int.unsigned v9) rtbl (Vint32 (ry&ᵢInt.not v10)))
              (TcbMod.set tcbls ptcb (prio, wait (os_stat_mutexsem qid) time, Vnull)).
Proof.
  introv  Htcb Htm Hst Hprio Hnth.
  unfolds in Htcb;fold TCBList_P in Htcb.
  mytac.
  inverts H.
  unfolds in H0.
  simpl in H0; inverts H0.
  unfolds.
  fold TCBList_P.
  exists x x0.
  exists x1.
  exists (prio,wait (os_stat_mutexsem qid) time,Vnull).
  splits; eauto.
  eapply tcbjoin_set; eauto.
{
  unfolds in H2.
  destruct x2.
  destruct p.
  mytac.
  unfolds in H0.
  simpl in H0; inverts H0.
  unfolds in H;simpl in H; inverts H.
  unfolds.
  split.  
  unfolds.
  simpl.
  auto.
  funfold H2.
  swallow.
  auto.
  unfolds.
  do 6 eexists; splits; try unfolds; simpl; eauto.
  splits; eauto.
  eexists.
  splits.
  unfolds;simpl; eauto.
  introv Hf.
  inverts Hf.
  lets Hexa : tcbjoin_get H1 Htm.
  inverts Hexa.
  unfolds in H4.
  split.
  unfolds.
  intros.
  simpl_hyp.
  unfolds in H.
  destruct H.
  simpl_hyp.
  unfolds in H0.
  assert (prio&ᵢ$ 7 = prio&ᵢ$ 7) by auto.
  assert (Int.shru ( prio) ($ 3) =Int.shru (prio) ($ 3)) by auto.
  assert ( nth_val ∘(Int.unsigned (Int.shru (prio) ($ 3)))
         (update_nth_val ∘(Int.unsigned (Int.shru (prio) ($ 3))) rtbl
            (Vint32 (ry&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))))) = 
           Some (Vint32  (ry&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))))).
  eapply update_nth; eauto.
  lets Hr: H0 H H2 H5.
  rewrite Int.and_assoc in Hr.
  assert (Int.not ($ 1<<ᵢ(prio&ᵢ$ 7))&ᵢ($ 1<<ᵢ(prio&ᵢ$ 7)) = $ 0).
  rewrite Int.and_commut.
  rewrite Int.and_not_self.
  auto.
  rewrite H6  in Hr.
  rewrite Int.and_zero in Hr.
  assert ( $ 1<<ᵢ(prio&ᵢ$ 7) <> $ 0) by (apply  math_prop_neq_zero2; try omega).
  unfold Int.zero in Hr.
  tryfalse.
  split.
  unfolds.
  intros.
  inverts H.
  split.
  unfolds.
  split.
  unfolds.
  intros.
  inverts H0.
  split.
  unfolds.
  intros.
  inverts H0.

  split.
  unfolds.
  intros.
  inverts H0.
  split.
  unfolds.
  intros.
  inverts H0.
  

  unfolds.
  intros.
  inverts H0.
  
  inverts H2.
  unfolds in H.
  mytac.
  inverts H.
  inverts H2.
  eauto.

  unfolds.
  split.
  unfolds.
  intros.
  inverts H.
  split.
  unfolds.
  intros.
  inverts H.
  split.
  unfolds.
  intros.
  inverts H.
  split.
  unfolds;intros.
  inverts H.

  unfolds;intros.
  inverts H.
  split.
  unfolds.
  splits; try unfolds ; simpl ; auto.

  intros.
  subst.
  apply nth_upd_eq in H2.
  inverts H2.
  rewrite Int.and_assoc.
  assert (Int.not ($ 1<<ᵢ(prio&ᵢ$ 7))&ᵢ($ 1<<ᵢ(prio&ᵢ$ 7)) = $ 0).
  rewrite Int.and_commut.
  rewrite Int.and_not_self.
  auto.
  rewrite H.
  rewrite  Int.and_zero.
  auto.
  split.
  unfolds; simpl; auto.
  unfolds; simpl; auto.
}
  unfolds in H2.
  destruct x2.
  destruct p.
  mytac; simpl_hyp.
  funfold H2.
(* ** ac:   Locate update_rtbl_tcblist_hold. *)
  eapply OSTimeDlyPure.update_rtbl_tcblist_hold; eauto.
  unfolds in Hst.
  intros.
  lets Has : tcbjoin_get_getneq H1 H.
  destruct Has.
  eapply Hst; eauto.
Qed.

Lemma RH_CurTCB_high_block_hold_mutex:
  forall (ptcb : tidspec.A) (tcbls : TcbMod.map) (prio : priority)
         (st : taskstatus) (qid : ecbid) (time : int32) 
         (m : msg),
    RH_CurTCB ptcb tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, st, m) ->
    RH_CurTCB ptcb
              (TcbMod.set tcbls ptcb (prio, wait (os_stat_mutexsem qid) time, m)).
Proof.
  introv Hr Ht.
  unfolds in Hr.
  mytac.
  unfold get in *; simpl in *.
  rewrite H in Ht.
  inverts Ht.
  unfolds.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.eq_beq_true; eauto.
Qed.

Lemma RH_TCBList_ECBList_P_high_block_hold_mutexsem:
  forall (ecbls : EcbMod.map) (tcbls : TcbMod.map) 
         (pcur : tid) (qid : tidspec.A) (m : msg) (cnt : int32) 
         (wl : waitset) (prio : priority) (time : int32) x,
    RH_TCBList_ECBList_P ecbls tcbls pcur ->
    EcbMod.get ecbls qid = Some (absmutexsem cnt x, wl) ->
    TcbMod.get tcbls pcur = Some (prio, rdy, m) ->
    RH_TCBList_ECBList_P (EcbMod.set ecbls qid (absmutexsem cnt x, pcur :: wl))
                         (TcbMod.set tcbls pcur (prio, wait (os_stat_mutexsem qid) time, m)) pcur.
Proof.
  introv Hr Ht He.
  unfolds in Hr.
  destruct Hr as (Hr3 & Hr1 & Hr2 & Hr4).
  unfolds.
  splits.
  Focus 4.
{
  unfolds.
  splits.
  intros.
  mytac.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H1.
  subst.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  simpl in H0.
  destruct H0.
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.eq_beq_true; auto.
  assert (EcbMod.get ecbls eid = Some (absmutexsem n1 n2, wl) /\ In tid wl) by eauto.
  apply Hr4 in H0.
  mytac.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H1.
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.eq_beq_true; auto.
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  assert (EcbMod.get ecbls eid = Some (absmutexsem n1 n2, wls) /\ In tid wls) by eauto.
  apply Hr4 in H2.
  mytac.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H3.
  subst.
  unfold get in *; simpl in *.
  rewrite H2 in He.
  inverts He. 
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.
  intros.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  exists cnt.
  exists x.
  exists (tid::wl).
  splits; eauto.
  rewrite EcbMod.set_sem.
  rewrite tidspec.eq_beq_true; eauto.
  simpl; left; auto.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto.
  apply Hr4 in H.
  mytac.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H2.
  subst.
  rewrite EcbMod.set_sem.
  rewrite tidspec.eq_beq_true; auto.
  do 3 eexists; splits; eauto.
  unfold get in *; simpl in *.
  rewrite H in Ht.
  inverts Ht.
  simpl.
  right; auto.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 3 eexists; splits; eauto.
  unfolds in Hr4.
  destructs Hr4.
  unfolds.
  unfolds in H1.
  clear -H1 Ht He.
  intros.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H0.
  subst.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; inverts H.
  apply H1 in Ht.
  mytac.
  assert (tid = pcur \/ tid <> pcur) by tauto.
  destruct H0.
  subst tid.
  rewrite TcbMod.set_sem. 
  rewrite tidspec.eq_beq_true;auto.
  do 3 eexists;auto.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  2:auto.
  do 3 eexists;eauto.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  apply H1 in H.
  mytac.
  assert (tid = pcur \/ tid <> pcur) by tauto.
  destruct H2.
  subst tid.
  rewrite TcbMod.set_sem. 
  rewrite tidspec.eq_beq_true;auto.
  do 3 eexists;auto.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 3 eexists;eauto.
}
  Unfocus.
  Focus 3.
{
  splits.
  intros.
  mytac.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H1.
  subst.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  assert (EcbMod.get ecbls eid =Some (absmbox n, wls) /\ In tid wls) by eauto.
  apply Hr2 in H2.
  mytac.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H3.
  subst.
  unfold get in *; simpl in *.
  rewrite H2 in He.
  inverts He. 
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.
  intros.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto.
  apply Hr2 in H.
  mytac.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H2.
  subst.
  unfold get in *; simpl in *.
  rewrite H in Ht.
  inverts Ht.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 2 eexists; splits; eauto.
}
  Unfocus.
{
  splits.
  intros.
  mytac.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H1.
  subst.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  assert (EcbMod.get ecbls eid = Some (absmsgq x0 y, qwaitset) /\ In tid qwaitset) by eauto.
  apply Hr3 in H2.
  mytac.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H3.
  subst.
  unfold get in *; simpl in *.
  rewrite H2 in He.
  inverts He. 
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.
  intros.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto.
  apply Hr3 in H.
  mytac.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H2.
  subst.
  unfold get in *; simpl in *.
  rewrite H in Ht.
  inverts Ht.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 3 eexists; splits; eauto.
}
{
  splits.
  intros.
  mytac.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H1.
  subst.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  assert (EcbMod.get ecbls eid = Some (abssem n, wls) /\ In tid wls) by eauto.
  apply Hr1 in H2.
  mytac.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H3.
  subst.
  unfold get in *; simpl in *.
  rewrite H2 in He.
  inverts He. 
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.
  intros.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto.
  apply Hr1 in H.
  mytac.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H2.
  subst.
  unfold get in *; simpl in *.
  rewrite H in Ht.
  inverts Ht.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 2 eexists; splits; eauto.
}
Qed.

Lemma R_ECB_ETbl_P_high_tcb_block_hold:
  forall (l : addrval) (vl : vallist) (egrp : int32) 
         (v2 v3 v4 v5 : val) (etbl : vallist) (tcbls : TcbMod.map)
         (ptcb : tidspec.A) (prio : int32) (st : taskstatus) 
         (m m' : msg) (y bity bitx ey time : int32) (av : addrval),
    Int.unsigned prio < 64 ->
    R_PrioTbl_P vl tcbls av ->
    R_ECB_ETbl_P l
                 (V$OS_EVENT_TYPE_MUTEX :: Vint32 egrp :: v2 :: v3 :: v4 :: v5 :: nil, etbl)
                 tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, st, m) ->
    y = prio>>ᵢ$ 3 ->
    bity = $ 1<<ᵢy ->
    bitx = $ 1<<ᵢ(prio&ᵢ$ 7) ->
    nth_val ∘(Int.unsigned y) etbl = Some (Vint32 ey) ->
    R_ECB_ETbl_P l
                 (V$OS_EVENT_TYPE_MUTEX
                   :: Vint32 (Int.or egrp bity) :: v2 :: v3 :: v4 :: v5 :: nil,
                  update_nth_val ∘(Int.unsigned y) etbl (Vint32 (Int.or ey bitx)))
                 (TcbMod.set tcbls ptcb (prio, wait (os_stat_mutexsem l) time, m')).
Proof.
  introv Hran Hrs  Hre Htc Hy Hb1 Hb2 Hnth.
  subst.
  unfolds in Hre.
  destruct Hre as (Hre1 & Hre2 & Het).
  unfolds.
  splits.
  unfolds.
  splits.
  Focus 4.
{
  unfolds.
  intros.
  destruct Hre1 as (_ & _ & _ & Hre1).
  destruct Hre2 as (_ & _ & _ & Hre2).
  unfolds in Hre1.
  unfolds in Hre2.
  assert (prio = $ prio0 \/ prio <> $ prio0) by tauto.
  destruct H1.
  subst.
  exists ptcb time m'.
  rewrite TcbMod.set_sem.
  erewrite tidspec.eq_beq_true; eauto.
  lets Hres : prio_wt_inq_keep Hran H1 Hnth .
  destruct Hres.
  apply H2 in H.
  apply Hre1 in H.
  mytac.
  exists x x0 x1.
  assert (x = ptcb \/ x <> ptcb) by tauto.
  destruct H4.
  subst.
  unfold get in *; simpl in *.
  rewrite Htc in H.
  inverts H.
  tryfalse.
  rewrite TcbMod.set_sem.
  erewrite tidspec.neq_beq_false; eauto.
  unfolds. 
  simpl; auto.
}
Unfocus.
Focus 2.
{
  unfolds.
  intros.
  usimpl H0.
}
Unfocus.
{
  unfolds.
  intros.
  usimpl H0.
}
{
   unfolds.
  intros.
  usimpl H0.
}
  unfolds.
  splits.
Focus 4.
{
  unfolds.
  intros.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.  
  destruct H0.
  subst.
  splits.
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  unfolds.
  rewrite Int.repr_unsigned.
  exists ( prio0&ᵢ$ 7).
  exists (Int.shru prio0 ($3)).
  exists ((Int.or ey ($ 1<<ᵢ(prio0&ᵢ$ 7)))).
  splits; eauto.
  clear - Hran.
  int auto.
  eapply update_nth; eauto.
  rewrite Int.and_commut.
  rewrite Int.or_commut.
  unfold Int.one.
  rewrite Int.and_or_absorb.
  auto.
  unfolds; simpl; auto.
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.neq_beq_false in H; eauto.
  unfolds in Hre2.
  destruct Hre2 as (_ & _ & _ & Hre2).
  lets Hasd : Hre2  H.
   destruct Hasd as (Has1 & Has2).
  splits.
  eapply prio_wt_inq_keep; eauto.
  rewrite Int.repr_unsigned.
  unfolds  in Hrs.
  destruct Hrs.
  destruct H2.
  unfolds in H3.
  lets Hdd : H3 H0 H Htc.
  eauto.
  unfolds; simpl; auto.
}
Unfocus.
Focus 2.
{
   unfolds.

  intros.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.  
  destruct H0.
  subst.
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.neq_beq_false in H; eauto.
  destruct Hre2 as (_&Hre2&_&_).
  apply Hre2 in H.
  destruct H.
  usimpl H1.
}
Unfocus.
{
   unfolds.
  intros.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.  
  destruct H0.
  subst.
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.neq_beq_false in H; eauto.
  destruct Hre2 as (Hre2&_).
  apply Hre2 in H.
  destruct H.
  usimpl H1.
}
   unfolds.
  intros.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.  
  destruct H0.
  subst.
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.neq_beq_false in H; eauto.
  destruct Hre2 as (_&_& Hre2 & _).
  apply Hre2 in H.
  destruct H.
  usimpl H1.
  simpl.
  unfolds.
  branch 4.
  unfolds; simpl; auto.
Qed.


Lemma ecblist_p_mutexpend:
  forall v'57 v'69 v'38 v'46 x ptcb_addr wls x3 v'48 v'28 v'30 v'40 tcbls v'44 v'27 v'29 cur_prio v'66 v'65 v'68 v'64 i os_rdy_tbl x0 v'26 x12 i5 ptbl vhold,
    ((v'44 =  Vptr (v'46, Int.zero) /\ v'27 = nil)\/ get_last_ptr v'27 = Some (Vptr (v'46, Int.zero))) /\ (length v'27 = length v'29)-> (*added*)
    R_PrioTbl_P ptbl tcbls vhold -> (*added*)
    TCBNode_P
      (x0
         :: v'26
         :: x12
         :: Vnull
         :: V$0
         :: V$OS_STAT_RDY
         :: Vint32 cur_prio
         :: Vint32 i5
         :: Vint32 v'64
         :: Vint32 v'65 :: Vint32 v'66 :: nil)
      os_rdy_tbl (cur_prio, rdy, Vnull) ->
    array_type_vallist_match Int8u v'57 ->
    RL_Tbl_Grp_P v'57 (Vint32 v'69) ->
    nth_val ∘(Int.unsigned v'64) v'57 = Some (Vint32 v'68) ->
    TcbMod.get tcbls (v'38, Int.zero) = Some (cur_prio, rdy, Vnull) ->
    EcbMod.get v'40 (v'46, Int.zero) =
    Some
      (absmutexsem (x>>ᵢ$ 8)
                   (Some (ptcb_addr, Int.zero, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), wls) ->
    ECBList_P v'44 Vnull
              (v'27 ++
                    ((V$OS_EVENT_TYPE_MUTEX
                       :: Vint32 v'69
                       :: Vint32 x :: Vptr (ptcb_addr, Int.zero) :: x3 :: v'48 :: nil,
                      v'57) :: nil) ++ v'28)
              (v'29 ++
                    (DMutex (Vint32 x) (Vptr (ptcb_addr, Int.zero)) :: nil) ++ v'30)
              v'40 tcbls ->
    ECBList_P v'44 Vnull
              (v'27 ++
                    ((V$OS_EVENT_TYPE_MUTEX
                       :: Vint32 (Int.or v'69 v'66)
                       :: Vint32 x :: Vptr (ptcb_addr, Int.zero) :: x3 :: v'48 :: nil,
                      update_nth_val ∘(Int.unsigned v'64) v'57 (Vint32 (Int.or v'68 v'65)))
                       :: nil) ++ v'28)
              (v'29 ++ (DMutex (Vint32 x) (Vptr (ptcb_addr, Int.zero)) :: nil) ++ v'30)
              (EcbMod.set v'40 (v'46, Int.zero)
                          (absmutexsem (x>>ᵢ$ 8)
                                       (Some (ptcb_addr, Int.zero, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)),
                           (v'38, Int.zero) :: wls))
              (TcbMod.set tcbls (v'38, Int.zero)
                          (cur_prio, wait (os_stat_mutexsem (v'46, Int.zero)) i, Vnull)).
Proof.
  introv Hlink Hrptiotbl.
  destruct Hlink as (Hlink&Hleneq).
  intros.
  lets Hx:Mbox_common.ecblist_p_decompose Hleneq H5.
  mytac.
  assert ( x1 = Vptr (v'46, Int.zero)).
  {
    clear -H9 Hlink H6.
    destruct v'27.
    simpl in H6.
    mytac;auto.
    destruct Hlink;mytac;auto.
    unfolds in H.
    tryfalse.
    apply ECBList_last_val in H6;auto.
    mytac.
    destruct H9;destruct Hlink.
    destruct H2;tryfalse.
    unfolds in H1.
    rewrite H in H1.
    unfolds in H1.
    false.
    destruct H2;false.
    rewrite H2 in H1;inverts H1.
    auto.
  }
  
  subst x1.
  simpl in H7.
  mytac.
  inverts H7.
  destruct x5.
  assert ((e,w) = (absmutexsem (x>>ᵢ$ 8)
                               (Some (ptcb_addr, Int.zero, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), wls)).
  {
    clear - H12 H8 H4.
    apply ecbmod_joinsig_get in H12.
    eapply EcbMod.join_get_r in H12;eauto.
    rewrite H12 in H4;inverts H4;auto.
  }

  inverts H7.
  eapply ecblist_p_compose;eauto.
  eapply EcbMod.join_set_r;eauto.
  unfolds.
  eexists.
  eapply ecbmod_joinsig_get;eauto.
  eapply ECBList_P_high_tcb_block_hold_mutex;eauto.

  eapply joinsig_join_getnone;eauto.
  simpl.
  eexists;mytac;swallow;eauto.
  clear H5.
  unfolds in H11;inverts H11.

  eapply R_ECB_ETbl_P_high_tcb_block_hold; eauto.
  clear -H.
  unfolds in H.
  mytac.
  unfolds in H1;mytac.
  simpl_vqm.
  auto.
  clear -H.
  unfolds in H.
  mytac.
  unfolds in H1;mytac.
  simpl_vqm.
  auto.
  clear -H.
  unfolds in H.
  mytac.
  unfolds in H1;mytac.
  simpl_vqm.
  auto.
  clear -H.
  unfolds in H.
  mytac.
  unfolds in H1;mytac.
  simpl_vqm.
  auto.
(*  do 3 eexists;splits;auto.
  unfolds;simpl;auto. *)
  eapply ecb_sig_join_sig'_set;eauto.
  simpl.

  unfolds in r.
  destructs r.
    
  swallow; auto.
  intros.
  tryfalse.

  eapply ECBList_P_high_tcb_block_hold_mutex;eauto.
  eapply joinsig_get_none;eauto.
Qed.

Lemma RH_TCBList_ECBList_P_high_block_hold_mutex:
  forall (ecbls : EcbMod.map) (tcbls : TcbMod.map) 
         (pcur : tid) (qid : tidspec.A) (m : msg) cnt x 
         (wl : waitset) (prio : priority) (time : int32),
    RH_TCBList_ECBList_P ecbls tcbls pcur ->
    EcbMod.get ecbls qid = Some (absmutexsem cnt x, wl) ->
    TcbMod.get tcbls pcur = Some (prio, rdy, m) ->
    RH_TCBList_ECBList_P (EcbMod.set ecbls qid (absmutexsem cnt x, pcur :: wl))
                         (TcbMod.set tcbls pcur (prio, wait (os_stat_mutexsem qid) time, m)) pcur.
Proof.
  introv Hr Ht He.
  unfolds in Hr.
  destruct Hr as (Hr3 & Hr1 & Hr2 & Hr4).
  unfolds.
  splits.
  Focus 4.
{
  unfolds.
  splits.
  intros.
  mytac.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H1.
  subst.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  simpl in H0.
  destruct H0.
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.eq_beq_true; auto.
  assert (EcbMod.get ecbls eid = Some (absmutexsem n1 n2, wl) /\ In tid wl) by eauto.
  apply Hr4 in H0.
  mytac.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H1.
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.eq_beq_true; auto.
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  assert (EcbMod.get ecbls eid = Some (absmutexsem n1 n2, wls) /\ In tid wls) by eauto.
  apply Hr4 in H2.
  mytac.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H3.
  subst.
  unfold get in *; simpl in *.
  rewrite H2 in He.
  inverts He. 
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.
  intros.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  exists cnt.
  eexists.
  exists (tid::wl).
  splits; eauto.
  rewrite EcbMod.set_sem.
  rewrite tidspec.eq_beq_true; eauto.
  simpl; left; auto.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto.
  apply Hr4 in H.
  mytac.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H2.
  subst.
  rewrite EcbMod.set_sem.
  rewrite tidspec.eq_beq_true; auto.
  do 3 eexists; splits; eauto.
  unfold get in *; simpl in *.
  rewrite H in Ht.
  inverts Ht.
  simpl.
  right; auto.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 3 eexists; splits; eauto.
  unfolds.
  intros.
   assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H0.
  subst.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
 assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H.
  subst.
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.eq_beq_true; eauto.
   destruct Hr4.
  destruct H1.
  unfolds in H2.
  apply H2 in Ht.
  mytac.
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.
   rewrite EcbMod.set_sem in H.
   rewrite tidspec.neq_beq_false in H; auto.
   assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H1.
  subst.
  
  rewrite TcbMod.set_sem ;
    rewrite tidspec.eq_beq_true; eauto.
destruct Hr4.
  destruct H3.
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.
}
  Unfocus.
  Focus 3.
{
  splits.
  intros.
  mytac.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H1.
  subst.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  assert (EcbMod.get ecbls eid =Some (absmbox n, wls) /\ In tid wls) by eauto.
  apply Hr2 in H2.
  mytac.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H3.
  subst.
  unfold get in *; simpl in *.
  rewrite H2 in He.
  inverts He. 
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.
  intros.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto.
  apply Hr2 in H.
  mytac.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H2.
  subst.
  unfold get in *; simpl in *.
  rewrite H in Ht.
  inverts Ht.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 2 eexists; splits; eauto.
}
  Unfocus.
{
  splits.
  intros.
  mytac.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H1.
  subst.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  assert (EcbMod.get ecbls eid = Some (absmsgq x0 y, qwaitset) /\ In tid qwaitset) by eauto.
  apply Hr3 in H2.
  mytac.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H3.
  subst.
  unfold get in *; simpl in *.
  rewrite H2 in He.
  inverts He. 
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.
  intros.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto.
  apply Hr3 in H.
  mytac.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H2.
  subst.
  unfold get in *; simpl in *.
  rewrite H in Ht.
  inverts Ht.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 3 eexists; splits; eauto.
}
{
  splits.
  intros.
  mytac.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H1.
  subst.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  assert (EcbMod.get ecbls eid = Some (abssem n, wls) /\ In tid wls) by eauto.
  apply Hr1 in H2.
  mytac.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H3.
  subst.
  unfold get in *; simpl in *.
  rewrite H2 in He.
  inverts He. 
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.
  intros.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto.
  apply Hr1 in H.
  mytac.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H2.
  subst.
  unfold get in *; simpl in *.
  rewrite H in Ht.
  inverts Ht.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 2 eexists; splits; eauto.
}
Qed.


Close Scope code_scope.
