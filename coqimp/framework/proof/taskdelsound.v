Require Import sound_include.

Lemma task_delother_rule_sound:
  forall pa P  prio st msg tls' tls t e tp t1 aop r ri sd Spec I isr ie is cs,
    GoodLInvAsrt pa ->
    GoodFrm P ->
    joinsig t1 (prio, st, msg) tls' tls  ->
    indom tls t ->
    t <> t1 ->
    P ==>  Rv e @ tp == Vptr t1 //\\  CurLINV pa t ->
    RuleSem Spec sd pa I r ri 
            (
              <|| spec_del  (Vint32 prio);; aop ||>  **
                  P ** Aabsdata abstcblsid (abstcblist tls) **
                  Aabsdata curtid (oscurt t) ** OS [isr,ie,is,cs]
            ) 
            (sprim (stkfree e))
            (
              <|| aop ||>  ** P ** (EX lg,  pa t1 lg)  **
                  Aabsdata abstcblsid (abstcblist tls') ** 
                  Aabsdata curtid (oscurt t) ** OS [isr,ie,is,cs]
            ) t.

Proof.
  introv Hgi  Hfrm  Hneq Hjoin Hin Himp.
  unfolds.
  introv Hsat.
  destruct Hsat as (Hsat1 & Hsat2).
  destruct o as [[[[]]]].
  sep split in Hsat1.
  unfold sat in Hsat1; fold sat in Hsat1.  
  simp join.
  simpl in H, H8, H13,H16,H14,H15,H12,H10,H7,H5. 
  subst.
  assert (x0=empmem).
  clear - H10.
  join auto.
  subst x0.
  assert (x=m).
  clear -H5.
  join auto.
  subst x.
  clear H5 H10.  
  lets (Hks1&Hks2) : Himp H8.

  constructors; introv Hf; tryfalse.
  introv _ _ _ Hstep.
  unfold nilcont in Hstep.
  invertstep idtac.
  destruct Hf as (_&_&_&_&_&_&_&Hf).
  false.
  apply Hf.
  do 2 eexists.
  unfold nilcont.
  eauto.
  unfold nilcont in Hf.
  inverts Hf.
  introv Hsatp Hdisjj  Hjoinj.
  simpl get_smem in *.
  unfold getmem in Hdisjj.
  simpl in Hks1, Hdisjj, Hsatp.
  simp join.
  eexists.
  exists  prio aop t1.
  exists OO.
  splits; eauto.
  constructors.
  right.
  exists (set OO abstcblsid (abstcblist tls')).
  exists (set O abstcblsid (abstcblist tls')) Os.
  lets Hkb : join3_get2 H7 H12 Hjoinj.
  simp join.
  splits.
  unfolds.
  splits; eauto.  
  unfolds.
  exists tls tls' st msg.
  splits; eauto.
  eapply get_join_set_set; eauto.
  simpl; auto.
  remember (set O abstcblsid (abstcblist tls')) as OK.
  assert ( join x2 (set x3 abstcblsid (abstcblist tls')) OK) as Haps.
  eapply set_join2_join; eauto.
  assert (joinmem  (e0, e1, m, i, l) empmem  (e0, e1, m, i, l) ) as Hjm.
  unfolds.
  join auto.
  assert (   satp (e0, e1, m, i, l) x2 (CurLINV pa t)) as Hps.
  unfolds.
  eapply local_inv_irev_prop; eauto.
  lets Hsk :  absinfer_sound.join_satp_local_inv Hjm  Hps; eauto.

  introv Hs1 Hjb1 Hjb2.
  constructors; introv Hf; tryfalse.
  introv _ _ _ Hstep.
  invertstep idtac.
  unfold lift.
  introv Hspp Hdisj Hjn.
  inverts Hf.
  unfolds in Hjb1.
  simp join.
  simpl substaskst.
  exists aop OO0 O'' Os0.
  splits; eauto.
  constructors.

  lets Hbt : join3_ex2 Hjb2 H12 H7.
  simp join.
  unfolds.
  assert (   satp (x, x0, x1, x5, x6) x2 (CurLINV pa t)) as Hps.
  unfolds.
  eapply local_inv_irev_prop; eauto.
  assert (joinmem  (x, x0, x1, x5, x6) Mdel  (x, x0, x4, x5, x6)) as Hjm.
  unfolds.
  join auto.
  lets Hsk :  absinfer_sound.join_satp_local_inv Hjm   Hps; eauto.
  sep split; auto.
  unfold LINV in Hs1.
  lets Hs11 : Hs1 aop.
  sep normal in Hs11.
  sep destruct Hs11.
  sep split in Hs11.
  simpl substaskst in *.
  unfold getmem in *.
  simpl in Hdisj.
  sep normal.
  exists x7.
  exists Mdel x1  x4 Odel (set O abstcblsid (abstcblist tls'))  O''.
  simpl assertion.getmem.
  splits; eauto.
  clear - H9.
  join auto.
  clear - Hjb2.
  join auto.
  simpl substmo.
  exists x1 empmem x1 x2  (set x3 abstcblsid (abstcblist tls')) (set O abstcblsid (abstcblist tls')).
  simpl.
  splits; auto.
  clear.
  join auto.
  eapply set_join2_join; eauto.
  eapply goodfrm_prop; eauto.
  exists empmem empmem empmem.
  do 2 eexists.
  exists (set x3 abstcblsid (abstcblist tls')).
  splits; eauto.
  clear.
  join auto.
  eapply join2_sig_join; eauto.
  false.
  destruct Hf as (_&_&Hf&_).
  apply Hf.
  do 2 eexists; eauto.
Qed.



Lemma task_delself_rule_sound:
  forall pa P  prio st msg tls' tls t e tp  aop r ri sd Spec I isr ie is cs,
    GoodLInvAsrt pa ->
    GoodFrm P ->
    joinsig t (prio, st, msg) tls' tls  ->
    P ==>  Rv e @ tp == Vptr t //\\  CurLINV pa t ->
    RuleSem Spec sd pa I r ri 
            (
              <|| spec_del  (Vint32 prio);; aop ||>  **
                  P ** Aabsdata abstcblsid (abstcblist tls) **
                  Aabsdata curtid (oscurt t)**OS [isr,ie,is,cs]
            ) 
            (sprim (stkfree e))
            (
              <|| aop ||>  ** P  **
                  Aabsdata abstcblsid (abstcblist tls') ** 
                  Aabsdata curtid (oscurt t) **OS [isr,ie,is,cs]
            ) t.

Proof.
  introv Hgi  Hfrm   Hjoin  Himp.
  unfolds.
  introv Hsat.
  destruct Hsat as (Hsat1 & Hsat2).
  destruct o as [[[[]]]].
  sep split in Hsat1.
  unfold sat in Hsat1; fold sat in Hsat1.  
  simp join.
  simpl in H, H8, H13,H16,H14,H15,H12,H10,H7,H5. 
  subst.
  assert (x0=empmem).
  clear - H10.
  join auto.
  subst x0.
  assert (x=m).
  clear -H5.
  join auto.
  subst x.
  clear H5 H10.  
  lets (Hks1&Hks2) : Himp H8.

  constructors; introv Hf; tryfalse.
  introv _ _ _ Hstep.
  unfold nilcont in Hstep.
  invertstep idtac.
  destruct Hf as (_&_&_&_&_&_&_&Hf).
  false.
  apply Hf.
  do 2 eexists.
  unfold nilcont.
  eauto.
  unfold nilcont in Hf.
  inverts Hf.
  introv Hsatp Hdisjj  Hjoinj.
  simpl get_smem in *.
  unfold getmem in Hdisjj.
  simpl in Hks1, Hdisjj, Hsatp.
  simp join.
  eexists.
  exists  prio aop t.
  exists OO.
  splits; eauto.
  constructors.
  left.
  exists (set OO abstcblsid (abstcblist tls')).
  exists (set O abstcblsid (abstcblist tls')) Os.
  lets Hkb : join3_get2 H7 H12 Hjoinj.
  simp join.
  splits.
  unfolds.
  splits; eauto.  
  unfolds.
  exists tls tls' st msg.
  splits; eauto.
  eapply get_join_set_set; eauto.
  simpl; auto.
  remember (set O abstcblsid (abstcblist tls')) as OK.
  assert ( join x2 (set x3 abstcblsid (abstcblist tls')) OK) as Haps.
  eapply set_join2_join; eauto.
  assert (joinmem  (e0, e1, m, i, l) empmem  (e0, e1, m, i, l) ) as Hjm.
  unfolds.
  join auto.
  assert (   satp (e0, e1, m, i, l) x2 (CurLINV pa t)) as Hps.
  unfolds.
  eapply local_inv_irev_prop; eauto.
  lets Hsk :  absinfer_sound.join_satp_local_inv Hjm  Hps; eauto.

  constructors; introv Hf; tryfalse.
  introv _ _ _ Hstep.
  invertstep idtac.
  unfold lift.
  introv Hspp Hdisj Hjn.
  inverts Hf.
  simpl substaskst in *.
  exists aop OO0 (set O abstcblsid (abstcblist tls')) Os0.
  splits; eauto.
  constructors.
  assert (joinmem  (e0, e1, m, i, l) empmem  (e0, e1, m, i, l) ) as Hjm.
  unfolds.
  join auto.
  assert (   satp (e0, e1, m, i, l) x2 (CurLINV pa t)) as Hps.
  unfolds.
  eapply local_inv_irev_prop; eauto.
  remember (set O abstcblsid (abstcblist tls')) as OK.
  assert ( join x2 (set x3 abstcblsid (abstcblist tls')) OK) as Haps.
  eapply set_join2_join; eauto.
  lets Hsk :  absinfer_sound.join_satp_local_inv Hjm  Hps; eauto.
  sep split; auto.
  exists m empmem m x2  (set x3 abstcblsid (abstcblist tls')) (set O abstcblsid (abstcblist tls')).
  simpl.
  splits; auto.
  clear.
  join auto.
  eapply set_join2_join; eauto.
  eapply goodfrm_prop; eauto.
  exists empmem empmem empmem.
  do 2 eexists.
  exists (set x3 abstcblsid (abstcblist tls')).
  splits; eauto.
  clear.
  join auto.
  eapply join2_sig_join; eauto.
  false.
  destruct Hf as (_&_&Hf&_).
  apply Hf.
  do 2 eexists; eauto.
Qed.



