Require Import sound_include.

Lemma checkis_rule_sound:
  forall  Spec  sd I r ri x aop isr is ie cs v  P pa t ,
    GoodFrm P ->
    P ==> CurLINV pa t->
    RuleSem Spec sd  pa I r ri
            (<||aop||> ** OS[isr, ie, is, cs] **  LV x @ Tint32 |-> v ** P) 
            (sprim (checkis x))
            (<||aop||> ** OS[isr, ie, is, cs] **  LV x @ Tint32 |-> (is_length is) ** P) t.
Proof.
  introv Hgood Himp Hsat.
  destruct Hsat as (Hsat1 & Hsat2).
  destruct o as [[[[G E] M]iis]ax].
  destruct ax  as [[iee iss] css].
  sep split in Hsat1.
  simpl in H0, H1,H2,H3,H.
  subst iis iee iss css.
  subst aop0.
  simpl in Hsat1.
  simp join.
  assert (x8 = x0) by join auto. 
  subst x8.
  clear H5.
  unfold emposabst in *.
  subst x10 x11.
  assert (x3 = empabst) by join auto.
  subst x3.
  assert (x4 = O) by join auto.
  subst x4.
  clear H2 H7.
  constructors; introv Hff; tryfalse.
  simpl substaskst in *.
  unfold nilcont.
  introv Hinv Hjm1 Hjm2 Hstep.
  invertstep idtac.
  unfolds in Hjm1.
  unfold joinmem in Hjm1.
  simp join.
  exists aop OO.

  rewrite H2 in H8; inverts H8.
  lets Hres :  store_join_map_join H6  H10  H0 H3; eauto.
  simp join.
  exists (x4, x5, x10, x8, (ei, si, ci)) Ms O Os.
  splits; eauto.
  constructors.
  unfolds; unfold joinmem;  join auto.
  lets Hk : Himp H4.
  assert (satp (x4, x5, x1, x8, (ei, si, ci)) O (CurLINV pa t)).
  eapply absinfer_sound.local_inv_aop_irev with aop.
  auto.
  eapply join_satp_local_inv with (M:=x) (Of:= empabst); eauto.
  unfold joinmem; join auto.
  join auto.
  constructors; introv Hfff; tryfalse.
  introv _ _ _ Hsf.
  invertstep idtac.
  unfold getmem.
  simpl substaskst in *.
  simpl get_mem  in * . 
  introv Hdisjj Hiinv Hodisj.
  exists aop OO0 O Os0.   
  inverts Hfff.
  splits; eauto.
  constructors.
  lets Hk : Himp H4.
  assert (satp (x4, x5, x1, x8, (ei, si, ci)) O (CurLINV pa t)).
  eapply absinfer_sound.local_inv_aop_irev with aop.
  unfold CurLINV.
  unfold p_local in Hk.
  sep auto.
  eapply join_satp_local_inv with (M:=x) (Of:= empabst); eauto.
  unfold joinmem; join auto.
  join auto.
  unfold lift.
  sep split; try solve [simpl; auto].
  exists x x1 x10 empabst O O.
  simpl.
  splits; eauto.
  join auto.
  exists x13 empmem x x empabst.  
  exists empabst empabst.
  splits; eauto.
  join auto.
  join auto.
  exists x13.
  splits; eauto.
  unfolds; auto.
  unfolds; auto.
  unfolds in Hfff.
  destruct  Hfff as (_&_ & Hfff &_ ).
  false.
  apply Hfff.
  unfolds; eexists; eauto.
  introv Hj Hj2 Hinvv .
  unfold nilcont.
  introv Hs.
  apply Hs.
  destruct o2 as [[[[]]]].
  destruct l as [[]].
  unfolds in Hj2.
  unfold joinmem in Hj2.
  simp join.
  lets Hsdd : store_exist_join'  (is_length i1)  H9 H0.  
  simp join.
  lets Hsdss : store_mono H6 H.
  simp join.
  lets Hsdsss : store_mono H3 H1.
  simp join.
  do 2 eexists.
  eapply checkis_step; eauto.
Qed.
