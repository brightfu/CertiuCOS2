Require Import sound_include.


Lemma task_crt_rule_sound:
  forall (Spec : funspec) (sd : ossched) 
         (I : Inv) (r : retasrt) (ri P : asrt) 
         (aop : spec_code) (tls : TcbMod.map) 
         (t1 : addrval) (prio : int32) (tls' : TcbMod.map)
         (v1 v2 : val) (e1 e2 e3 : expr) (tp1 tp3 : type)
         (pa : LocalInv) (t : tid)  (isr : isr) 
                 (ie : ie) (is : is) (cs : cs),
    GoodLInvAsrt pa ->
    GoodFrm P ->
    joinsig t1 (prio, rdy, Vnull) tls tls'  ->
    indom tls t ->
    P ==>
      Rv e1 @ tp1 == v1 //\\
                        Rv e2 @ Tptr Tvoid == v2 //\\
                                                 Rv e3 @ tp3 == Vptr t1 //\\  CurLINV pa t ->
    RuleSem Spec sd pa I r ri 
            (
              <|| spec_crt v1 v2 (Vint32 prio);; aop ||>  ** P **
                  pa t1 init_lg  **
                  Aabsdata abstcblsid (abstcblist tls) **
                  Aabsdata curtid (oscurt t) ** OS [isr, ie, is, cs]
            ) 
            (sprim (stkinit e1 e2 e3))
            (
              <|| aop ||>  ** P **
                  Aabsdata abstcblsid (abstcblist tls') ** 
                  Aabsdata curtid (oscurt t)  **   
                  OS [isr, ie, is, cs]
            ) t.
Proof.
  introv Hgi  Hfrm Hjoin Hin Himp.
  unfolds.
  introv Hsat.
  destruct Hsat as (Hsat1 & Hsat2).
  destruct o as [[[[]]]].
  sep split in Hsat1.
  unfold sat in Hsat1; fold sat in Hsat1.  
  simp join.
  simpl in H, H8,H13,H17,H18,H21,H19,H20,H17,H15,H12,H10,H7,H5.
  subst.
  assert (x6=empmem).
  clear - H15.
  join auto.
  subst x6.
  assert (x5=x0).
  clear -H10.
  join auto.
  subst x5.
  clear H10 H15.  
  lets (Hks1&Hks2&Hks3&Hks4) : Himp H8.

  constructors; introv Hf; tryfalse.
  introv _ _ _ Hstep.
  unfold nilcont in Hstep.
  invertstep idtac.
  destruct Hf as (_&_&_&_&_&_&Hf&_).
  false.
  apply Hf.
  do 4 eexists.
  unfold nilcont.
  eauto.
  unfold nilcont in Hf.
  inverts Hf.
  introv Hsatp Hdisjj  Hjoinj.
  simpl get_smem in *.
  simpl in Hks1, Hks2, Hks3.
  simp join.
  eexists.
  exists v1 v2 t1 prio.
  exists aop.
  exists OO.
  exists (set OO abstcblsid (abstcblist tls')).
  exists (e, e0, x, i, l) x0.
  exists (set O abstcblsid (abstcblist tls')) Os.
  assert (exists k, join k x8 O /\ join x2 x9 k).
  clear -H7 H12.
  join auto.
  simp join.  
  exists  (set x1 abstcblsid (abstcblist tls')) x8.
  splits; eauto.
  lets Hbs : evalval_mono H5 H6; rewrite Hbs;eauto.
  lets Hbs : evalval_mono H5 H2; rewrite Hbs;eauto.
  lets Hbs : evalval_mono H5 H; rewrite Hbs;eauto.
  constructors.
  unfolds.
  split.
  eapply joinsig_idom_neq; eauto.

  exists tls tls'.
  splits;auto.
  eapply  joinsig_join2_get2; eauto.
  eapply  joinsig_join2_get2; eauto.
  unfolds; do 6 eexists; splits; eauto.

  splits; eauto.

  eapply get_join_set_set;eauto.
  eapply joinsig_join2_get2'; eauto.
  eapply get_join_set_set; eauto.
  eapply  joinsig_join2_get2''; eauto.
  remember  (set x1 abstcblsid (abstcblist tls')) as OK.
  assert (join x2 (set x9  abstcblsid (abstcblist tls')) OK).
  
  eapply set_join2_join; eauto.
  assert (joinmem  (e, e0, x, i, l) empmem  (e, e0, x, i, l) ) as Hjmm.
  unfolds.
  clear.
  join auto.
  assert (   satp (e, e0, x, i, l) x2 (CurLINV pa t)) as Hps.
  unfolds.
  eapply local_inv_irev_prop; eauto.  
  lets Hsk :  absinfer_sound.join_satp_local_inv Hjmm H15 Hps; auto.
  simpl.
  unfolds.
  intros.
  sep split ; auto.
  
  eapply  good_linvasrt_aop_irev; eauto.
  
  constructors; introv Hf; tryfalse.
  introv _ _ _ Hstep.
  invertstep idtac.
  inverts Hf.
  simpl substaskst.
  introv Hsp Hds Hjn.
  exists aop OO0  (set x1 abstcblsid (abstcblist tls')) Os0.
  splits; eauto.
  constructors.
  remember (set x1 abstcblsid (abstcblist tls')) as OK.

  assert ( join x2 (set x9 abstcblsid (abstcblist tls')) OK) as Haps.
  eapply set_join2_join; eauto.
  assert (joinmem  (e, e0, x, i, l) empmem  (e, e0, x, i, l) ) as Hjm.
  unfolds.
  join auto.
  assert (   satp (e, e0, x, i, l) x2 (CurLINV pa t)) as Hps.
  unfolds.
  eapply local_inv_irev_prop; eauto.
  lets Hsk :  absinfer_sound.join_satp_local_inv Hjm  Haps; auto.

  unfold lift.
  sep split; auto.
  simpl.
  exists x empmem x x2  (set x9 abstcblsid (abstcblist tls'))  (set x1 abstcblsid (abstcblist tls')).
  splits; eauto.
  clear .
  join auto.

  eapply join2_sig_join; eauto.
  eapply goodfrm_prop; eauto.
  exists empmem empmem empmem.
  do 2 eexists.
  exists (set x9 abstcblsid (abstcblist tls')).
  splits; eauto.
  clear.
  join auto.
  eapply join2_sig_join; eauto.
  destruct Hf as (_&_&Hf&_).
  false.
  apply Hf.
  do 2 eexists; eauto.
Qed.

