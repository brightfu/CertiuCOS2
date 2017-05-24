Require Import sound_include.
Require Import conseqsound.


Lemma frame_sim_aux : 
  forall p sd  C gamma o o' O O' I  ri r  q frm  M Of li t,
    GoodI I sd li ->
    joinmem o M o'->
    join O Of O' -> 
    (~isalloc C /\ ~ isfree C /\ nci C /\  n_dym_com_int_cd C) -> 
    (GoodFrm frm /\ sat (substmo (o, O ,gamma) M Of) frm) -> 
    MethSimMod p sd C o gamma O li I r ri (lift q) t -> 
    MethSimMod p sd C o' gamma O' li I (fun v => (r v)**frm)  (ri**frm)  (lift (q ** frm)) t.
Proof.
  cofix Hcofix.
  introv Hgi  Hjm Hjos Hnot  Hfrm Hsim.
  inverts Hsim.
  constructors.
  (***)
  introv Hfcall Hinv Hjm1 Hjm2 Hstep.
  lets Hres: join_frame_dis  Hjm1 Hjm.
  destruct Hres as (MM & Hj1 & Hj2 ).
  lets Hinv' :  joinmem_satp_mono Hinv; eauto.
  assert (exists O1, join O Os O1 /\ join Of O1 OO) as Hatt.
  clear -Hjos Hjm2.
  join auto.
  destruct Hatt as (Ok & Hjo1 & Hjo2).
  lets Hres : H Hfcall Hinv' Hjo1 Hstep; eauto.
  destruct Hres as (gam & OO' &  oo & Mss & Ol & Oss  &Hsttar & Hjmm2 & Hjjj  & Hinvv & Hlinv  & Hsim).  
  lets Hsp : spec_stepstar_locality Hsttar Hjo2.
  destruct Hsp as (O2 & Hsp & Hspp).  
  exists gam O2. 
  lets Habs :  joinm2_join_ex1 Hjmm2 Hj2.
  destruct Habs as (ol & Habs1 & Habs2).
  exists ol Mss.
  assert (exists O, join O Oss O2 /\ join Ol Of O) as Hjo.
  clear - Hjjj Hspp.
  join auto.
  destruct Hjo as (OOl & HjO1 & HjO2).
  exists OOl  Oss.
  splits; auto.
  eapply joinmem_satp_mono_rev; eauto.
  eapply join_satp_local_inv; eauto.
  eapply Hcofix;eauto.
  eapply loststep_code_prop; eauto.
  splits; intuition eauto.
  assert (~IsFcall C)  as Hasrt; eauto.
  assert ( ~ isalloc C /\ ~ isfree C /\ nci C /\  n_dym_com_int_cd C) as Hasrt'; eauto.
  
  lets Heqenv : loststep_eqenv Hstep Hasrt Hasrt'.
  assert (eqenv oo o2') as Heq1.
  clear -Habs1 Habs2.
  unfolds in Habs1.
  unfold joinmem in *.
  join auto.
  assert (eqenv o2 o) as Heq2.
  clear -Hjm1 Hjm.
  unfolds in Hjm1.
  unfold joinmem in *.
  join auto.
  apply eqenv_comm in Heqenv.
  lets Heqevv : eqenv_trans Heq1 Heqenv. 
  lets Hks : eqenv_trans Heqevv Heq2.  
  eapply  eqenv_goodg_sat; eauto.
  (**)   

  introv  Hc Hinv Hdisj Hjoin.
  subst C.
  lets Hinv' :  joinmem_satp_mono Hinv; eauto. 
  lets Hds : joinmem_disj_disj  Hjm Hdisj.
  assert (exists O1, join O Os O1 /\ join Of O1 OO) as Hatt.
  clear -Hjos Hjoin.
  join auto.
  destruct Hatt as (Ok & Hjo1 & Hjo2).
  lets Hres : H0 Hinv' Hjo1; eauto.
  destruct Hres as (gam & OO' &  om & MM & Ol & Oss  & Ott & Off & 
                        pre & post & tpp & logc &  Hsttar & Hjmm2 & Hjjj & Hjjj1 & Htvm & Hspe & Hsatp & Hinvv&Hsas&
                        Hfo1 ).  
  lets Hsp : spec_stepstar_locality Hsttar Hjo2.
  destruct Hsp as (O2 & Hsp & Hspp).  
  assert (exists O, join O Oss O2 /\ join Ol Of O) as Hatt.
  clear - Hjjj Hspp.
  join auto.
  destruct Hatt as (Od & Hjoo1 & Hjoo2).
  
  lets Hjs :  joinmem_ex_intro Hjmm2 Hjm.
  destruct Hjs as (Mb & Hjmb & Hjjb).
  exists gam O2 om Mb Od Oss.
  assert (exists O, join Ott O Od /\ join Of Off O) as Hpa.
  clear - Hjoo2  Hjjj1.
  join auto.
  destruct Hpa as (On & Hjpn & Hjqn).
  exists Ott On pre post tpp  logc.
  splits; auto.
  splits; auto.
  eapply joinmem_satp_mono_rev; eauto.
  eapply  joinmem_satp_mono with (M :=  MM); eauto.  
  introv Hpre.
  lets Hsk : Hfo1 Hpre.
  destruct Hsk as (Hsk1 & Hsk2).
  split; auto.
  introv   Hjmj Hjon Heqenv.
  lets Hasj :  joinmem_ex_elim  Hjmj  Hjjb.
  destruct Hasj as (oo & Hjo11 & Hjo22). 
  assert (exists OO, join OO Of O'' /\ join O1 Off OO) as Haps.
  clear -Hjqn Hjon.
  join auto.
  destruct Haps as (Oz & Haps1 & Haps2).
  eapply Hcofix with (o := oo)  ; eauto.
  destruct Hnot as (Hnf&Hfr&Hnci&Hnd).
  splits; try solve [ introv Hfs; unfolds in Hfs; simp join; tryfalse].
  unfolds in Hnci.
  destruct Hnci as (ss&kee&ksss&Hcs&Hcall&Hintt).
  unfolds.
  inverts Hcs.
  do 3 eexists; splits; eauto.
  unfolds in Hnd.
  destruct Hnd. 
  split; intuition eauto.
  destruct Hfrm.
  split; auto.

  eapply eqenv_goodg_sat; intuition eauto.
  clear -Hjm  Heqenv Hjo11.
  unfold joinmem in *.
  unfold eqenv in *.
  join auto.
  eapply Hsk2; eauto.
  eapply eqenv_comm.
  clear -Hjm  Heqenv Hjo11.
  unfold joinmem in *.
  unfold eqenv in *.
  join auto.

  introv  Hc Hinv  Hdisj Hjoin.
  subst C.
  lets Hinv' :  joinmem_satp_mono Hinv; eauto.
  lets Hds : joinmem_disj_disj  Hjm Hdisj.
  assert (exists O1, join O Os O1 /\ join Of O1 OO) as Hatt.
  clear -Hjos Hjoin.
  join auto.
  destruct Hatt as (Ob & Hjo1 & Hjo2).
  lets Hres : H1  Hinv' Hjo1; eauto.
  destruct Hres as ( gam & ss  & OO' & oo& Mc  & Ol & Oss &  Oll & Oc 
                         & Hgm & Hstar& Hjom  & Hjol1 & Hjol2 &  Hinvv & Hswinv & Hlinv  &Hfo1 ).
  subst gam.
  lets Hsp : spec_stepstar_locality Hstar Hjo2.
  destruct Hsp as (O2 & Hsp & Hspp).  
  exists (sched;; ss) ss  O2.
  assert (exists O, join O Oss O2 /\ join Ol Of O) as Hatt.
  clear - Hjol1 Hspp.
  join auto.
  
  lets Hjs :  joinmem2_ex_intro Hjom Hjm.
  destruct Hjs as (ok & Hjmb & Hjjb).
  destruct Hatt as (Ok & Hjob1 & Hjob2).
  assert (exists Ot, join Ot Oc Ok /\ join Oll Of Ot) as Hza.
  clear -Hjol2 Hjob2.
  join auto.
  destruct Hza as (Ot & Hot1 & Hot2).
  exists ok Mc Ok Oss Ot Oc.
  splits; auto.
  eapply joinmem_satp_mono_rev; eauto.
  lets Hk :   joinmem_satp_mono Hjom Hinvv;auto.
  eapply joinmem_satp_mono_rev; eauto.

  lets Hkd :  join3_satp_swinv  Hswinv; eauto.
  split.
  eapply  local_inv_satp_hold; eauto.
  destruct Hfo1 as [Hfoo1 | Hfoo2].
  destruct Hfoo1 as (Hsatp & Hfo1).
  left.
  split.
  clear -Hsatp Hjm.
  unfolds in Hjm.
  simp join.
  simpl substaskst in *.
  auto.
  introv Hswinv' Hjas1 Hjas2.
  lets Hsre :  joinmem_ex_intro2 Hjjb Hjas1 .
  destruct Hsre as (oo1 & Hjoo1 & Hjoo2).
  assert (exists Od, join Od Of O''/\ join Oll Oc' Od) as Has1.
  clear - Hot2 Hjas2.
  join auto.
  destruct Has1 as (Od & Hod1 & Hod2).
  eapply Hcofix with (o:=oo1) (O':=O'');eauto.
  destruct Hnot as (Hnf&Hfr&Hnci&Hnd).
  splits; try solve [ introv Hfs; unfolds in Hfs; simp join; tryfalse].
  unfolds in Hnci.
  destruct Hnci as (sbs&kee&ksss&Hcs&Hcall&Hintt).
  unfolds.
  inverts Hcs.
  do 3 eexists; splits; eauto.
  unfolds in Hnd.
  destruct Hnd. 
  split; intuition eauto.
  destruct Hfrm.
  split; auto.
  eapply eqenv_goodg_sat; intuition eauto.
  clear -Hjoo1 Hjas1 Hjmb Hjm.
  unfold joinmem in *.
  join auto.
  eapply Hfo1 with (Mc':=Mc')(O'':=Od); eauto.
  eapply join3_satp_swinv_rev with (Mc:=Mc'); eauto.
  right.
  clear -Hfoo2 Hjm.
  unfolds in Hjm.
  simp join.
  simpl substaskst in *.
  auto.

  introv Hc Hinv  Hdisj Hjoin.
  subst.
  lets Hinv' :  joinmem_satp_mono Hinv; eauto.
  lets Hds : joinmem_disj_disj  Hjm Hdisj.
  assert (exists O1, join O Os O1 /\ join Of O1 OO) as Hatt.
  clear -Hjos Hjoin.
  join auto.
  destruct Hatt as (Ob& Hjo1 & Hjo2).
  lets Hres : H2  Hinv' Hjo1; eauto.
  destruct Hres as ( gam   & OO' & Ol'& Oss & Hstar& Hjom  &  Hinvv & Hsatp& Hpso  ).
  lets Hsp : spec_stepstar_locality Hstar Hjo2.
  destruct Hsp as (O2 & Hsp & Hspp).  
  exists gam O2.
  assert (exists O, join O Oss O2 /\ join Ol' Of O) as Hatt.
  clear - Hjom Hspp.
  join auto.
  destruct Hatt as (Ok & Hjob1 & Hjob2).
  exists Ok Oss.
  splits; auto.
  eapply joinmem_satp_mono_rev; eauto.
  eapply join_satp_local_inv; eauto.
  unfold lift  in *.
  destruct Hfrm.
  
  eapply  joinmem_frm_asrt_hold; eauto.


  introv Hc Hcal Hint Hinv  Hdisj Hjoin.
  subst.
  lets Hinv' :  joinmem_satp_mono Hinv; eauto.
  lets Hds : joinmem_disj_disj  Hjm Hdisj.
  assert (exists O1, join O Os O1 /\ join Of O1 OO) as Hatt.
  clear -Hjos Hjoin.
  join auto.
  destruct Hatt as (Ob& Hjo1 & Hjo2).
  lets Hres : H3  Hinv' Hjo1; eauto.
  destruct Hres as ( gam   & OO' & Ol'& Oss & Hstar& Hjom  &  Hinvv & Hsatp& Hpso  ).
  lets Hsp : spec_stepstar_locality Hstar Hjo2.
  destruct Hsp as (O2 & Hsp & Hspp).  
  exists gam O2.
  assert (exists O, join O Oss O2 /\ join Ol' Of O) as Hatt.
  clear - Hjom Hspp.
  join auto.
  destruct Hatt as (Ok & Hjob1 & Hjob2).
  exists Ok Oss.
  splits; auto.
  eapply joinmem_satp_mono_rev; eauto.
  eapply join_satp_local_inv; eauto.
  unfold lift  in *.
  destruct Hfrm.
  eapply  joinmem_frm_asrt_hold; eauto.

  introv Hc Hcal Hint Hinv  Hdisj Hjoin.
  subst.
  lets Hinv' :  joinmem_satp_mono Hinv; eauto.
  lets Hds : joinmem_disj_disj  Hjm Hdisj.
  assert (exists O1, join O Os O1 /\ join Of O1 OO) as Hatt.
  clear -Hjos Hjoin.
  join auto.
  destruct Hatt as (Ob& Hjo1 & Hjo2).
  lets Hres : H4  Hinv' Hjo1; eauto.
  destruct Hres as ( gam   & OO' & Ol'& Oss & Hstar& Hjom  &  Hinvv & Hsatp& Hpso  ).
  lets Hsp : spec_stepstar_locality Hstar Hjo2.
  destruct Hsp as (O2 & Hsp & Hspp).  
  exists gam O2.
  assert (exists O, join O Oss O2 /\ join Ol' Of O) as Hatt.
  clear - Hjom Hspp.
  join auto.
  destruct Hatt as (Ok & Hjob1 & Hjob2).
  exists Ok Oss.
  splits; auto.
  eapply joinmem_satp_mono_rev; eauto.
  eapply join_satp_local_inv; eauto.
  unfold lift  in *.
  destruct Hfrm.
  eapply  joinmem_frm_asrt_hold; eauto.

  introv Hc Hcal Hint Hinv  Hdisj Hjoin.
  subst.
  lets Hinv' :  joinmem_satp_mono Hinv; eauto.
  lets Hds : joinmem_disj_disj  Hjm Hdisj.
  assert (exists O1, join O Os O1 /\ join Of O1 OO) as Hatt.
  clear -Hjos Hjoin.
  join auto.
  destruct Hatt as (Ob& Hjo1 & Hjo2).
  lets Hres : H5  Hinv' Hjo1; eauto.
  destruct Hres as ( gam   & OO' & Ol'& Oss & Hstar& Hjom  &  Hinvv & Hsatp& Hpso  ).
  lets Hsp : spec_stepstar_locality Hstar Hjo2.
  destruct Hsp as (O2 & Hsp & Hspp).  
  exists gam O2.
  assert (exists O, join O Oss O2 /\ join Ol' Of O) as Hatt.
  clear - Hjom Hspp.
  join auto.
  destruct Hatt as (Ok & Hjob1 & Hjob2).
  exists Ok Oss.
  splits; auto.
  eapply joinmem_satp_mono_rev; eauto.
  eapply join_satp_local_inv; eauto.
  unfold lift  in *.
  destruct Hfrm.
  eapply  joinmem_frm_asrt_hold; eauto.

  introv Hnotp  Hinv  Hjm1 Hdisj.
  lets Hres: join_frame_dis  Hjm1 Hjm.
  destruct Hres as (MM & Hj1 & Hj2 ).
  lets Hinv' :  joinmem_satp_mono Hinv; eauto.
  assert (disjoint O Os) as Hdist.
  clear - Hjos Hdisj.
  unfold disjoint in *.
  join auto.
  lets Hres : H6 Hj1 Hdist; eauto.

  introv  Hc Hinv  Hdisj Hjoin.
  subst C.
  lets Hinv' :  joinmem_satp_mono Hinv; eauto.
  lets Hds : joinmem_disj_disj  Hjm Hdisj.
  assert (exists O1, join O Os O1 /\ join Of O1 OO) as Hatt.
  clear -Hjos Hjoin.
  join auto.
  destruct Hatt as (Ob& Hjo1 & Hjo2).
  lets Hres : H7  Hinv' Hjo1; eauto.
  destruct Hres as
      (gam& v1&v2&t' &prio&ss &O11& O22&o11&mcr& Ol& Oss& Oll & ocr 
          &Heqc & Hev1 & Hev2 & Hev3 & Hstarr & Hcrt & Hjonm1 & Hjn1 & 
          Hjn2 &  Hinvv & Hlinv & Hscr & Hsim).
  lets Hsp : spec_stepstar_locality Hstarr Hjo2.
  destruct Hsp as (O2 & Hsp & Hspp).  
  exists gam v1 v2 t' prio ss.
  lets Hscc : abs_crt_locality  Hcrt Hspp.
  destruct Hscc as (Ok & Habsa & Hjab).
  exists O2 Ok.
  lets Hjs :  joinmem2_ex_intro Hjonm1 Hjm.
  destruct Hjs as (ok & Hjmb & Hjjb).
  exists ok mcr.
  assert (exists O1 O2, join O1 Oss Ok /\ join Ol Of O1 /\join O2 ocr O1 /\ join Oll Of O2) as Hasrt.
  clear -Hjn1 Hjn2 Hspp Hjab.
  join auto.
  destruct Hasrt as (Ok1 & Ok2 & Hjk1 & Hjk2 & Hjk3 & Hjk4).
  exists Ok1 Oss Ok2 ocr.
  splits; auto.
  eapply  evalval_mono_joinmem with (M:=M); eauto.
  eapply  evalval_mono_joinmem with (M:=M); eauto.
  eapply  evalval_mono_joinmem with (M:=M); eauto.
  splits; auto.
  lets Hk :   joinmem_satp_mono_rev  Hjm  Hinvv;auto.
  eapply join_satp_local_inv with (M:=M) (Of:=Of); eauto.

  eapply joinmem_satp_ocr with (M:=M); eauto.
  eapply Hcofix with (o:=o11) (O':=Ok2);eauto.
  destruct Hnot as (Hnf&Hfr&Hnci&Hnd).
  splits; try solve [ introv Hfs; unfolds in Hfs; simp join; tryfalse].
  unfolds in Hnci.
  destruct Hnci as (sbs&kee&ksss&Hcs&Hcall&Hintt).
  unfolds.
  inverts Hcs.
  do 3 eexists; splits; eauto.
  unfolds in Hnd.
  destruct Hnd. 
  split; intuition eauto.
  destruct Hfrm.
  split; auto.
  eapply eqenv_goodg_sat; intuition eauto.
  clear - Hjmb Hjm Hjjb.
  unfold joinmem in *.
  join auto.

  introv  Hc  Hinv  Hdisj Hjoin.
  subst.
  lets Hinv' :  joinmem_satp_mono Hinv; eauto.
  lets Hds : joinmem_disj_disj  Hjm Hdisj.
  assert (exists O1, join O Os O1 /\ join Of O1 OO) as Hatt.
  clear -Hjos Hjoin.
  join auto.
  destruct Hatt as (Ob& Hjo1 & Hjo2).
  lets Hres : H8 Hinv' Hjo1; eauto.
  destruct Hres as
      (gam& prio&ss & t' &O11  &Heqc& Hev &Hstarr & Hres).
  lets Hsp : spec_stepstar_locality Hstarr Hjo2.
  destruct Hsp as (O2 & Hsp & Hspp).  
  exists gam prio ss t' O2.
  splits; auto.
  eapply  evalval_mono_joinmem with (M:=M); eauto.
  destruct Hres as [Hres1 | Hres2].
  left.
  destruct Hres1 as (O22 & Ol & Oss & Hdel & Hjon1 & Hinvv & Hlinv & Hsim).
  lets Hscc : abs_delself_locality  Hdel Hspp.
  destruct Hscc as (Ok & Habsa & Hjab).
  assert (exists O, join O Oss Ok /\ join Ol Of O) as Hasrt.
  clear - Hjab Hjon1.
  join auto.
  destruct Hasrt as (Od & Hjd1 & Hjd2).
  exists Ok Od Oss.
  splits; auto.
  lets Hk :   joinmem_satp_mono_rev  Hjm  Hinvv;auto.
  eapply join_satp_local_inv with (M:=M) (Of:=Of); eauto.
  eapply Hcofix with (o':= o' ) (O':=Od );eauto.
  destruct Hnot as (Hnf&Hfr&Hnci&Hnd).
  splits; try solve [ introv Hfs; unfolds in Hfs; simp join; tryfalse].
  unfolds in Hnci.
  destruct Hnci as (sbs&kee&ksss&Hcs&Hcall&Hintt).
  unfolds.
  inverts Hcs.
  do 3 eexists; splits; eauto.
  unfolds in Hnd.
  destruct Hnd. 
  split; intuition eauto.
  destruct Hfrm.
  split; auto.
  eapply eqenv_goodg_sat; intuition eauto.
  destruct o as [[[[]]]];
    unfolds; auto.
  
  right.
  destruct Hres2 as (O22 & Ol & Oss & Hdel & Hjon1 & Hinvv & Hlinv & Hsim).
  lets Hscc : abs_delother_locality  Hdel Hspp.
  destruct Hscc as (Ok & Habsa & Hjab).
  assert (exists O, join O Oss Ok /\ join Ol Of O) as Hasrt.
  clear - Hjab Hjon1.
  join auto.
  destruct Hasrt as (Od & Hjd1 & Hjd2).
  exists Ok Od Oss.
  splits; auto.
  lets Hk :   joinmem_satp_mono_rev  Hjm  Hinvv;auto.
  eapply join_satp_local_inv with (M:=M) (Of:=Of); eauto.
  
  introv Hsatp Hj2 Hj1.
  lets Hsai :   local_inv_satp_join_hold Hsatp; eauto.
  
  assert (exists o1, joinmem o Mdel o1 /\ joinmem o1 M o'0) as Hjmk.
  clear -Hjm Hj2.
  unfold joinmem in *.
  join auto.
  destruct Hjmk as (oo1 & Hjoo1 & Hjoo2).
  (*assert (exists OO, join OO Of O'' /\  join Ol Odel OO ) as Haxt.*)
  assert ( join Ol Of Od) by auto.
  assert ( join Od Odel O'') by auto.
  lets Hxsx: join_ex2 H9  H10.
  destruct  Hxsx as (OOk & Hook1 & Hook2).
  eapply Hcofix with (o:= oo1) (O:= OOk); eauto.
  destruct Hnot as (Hnf&Hfr&Hnci&Hnd).
  splits; try solve [ introv Hfs; unfolds in Hfs; simp join; tryfalse].
  unfolds in Hnci.
  destruct Hnci as (sbs&kee&ksss&Hcs&Hcall&Hintt).
  unfolds.
  inverts Hcs.
  do 3 eexists; splits; eauto.
  unfolds in Hnd.
  destruct Hnd. 
  split; intuition eauto.
  destruct Hfrm.
  split; auto.
  eapply eqenv_goodg_sat; intuition eauto.
  clear - Hjoo1.
  unfolds in Hjoo1.
  join auto.
Qed.  



Lemma frame_rule_all_sound :
  forall Spec sd  I r ri  p q frm s li t, 
    GoodI I sd li -> 
    GoodStmt' s ->
    GoodFrm  frm->
    p ==> CurLINV li t  ->
    RuleSem Spec sd  li I r  ri p s q t-> 
    RuleSem Spec sd  li I   (fun v =>(r v) ** frm)
            (ri**frm)   (p ** frm) s (q ** frm ) t.
Proof.
  introv HgoodI  Hgoods Hgoodfrm  Him Hsim.
  unfolds.
  introv Hsat.
  unfold nilcont.
  unfolds in Hsim.
  destruct Hsat.
  destruct H; simp join.
  simpl in H0.
  destruct o as [[[[]]]].
  lets Hks : Him H4.
  simpl substmo in *.
  eapply frame_sim_aux ; eauto.
  unfolds.
  do 6 eexists; splits; eauto.
  splits; eauto.
  introv Hf.
  unfolds in Hf.
  destruct Hf as (vl & dl & ks & Hf).
  inverts Hf.
  simpl in Hgoods; tryfalse.
  introv Hf.
  unfolds in Hf.
  destruct Hf as (vl & dl & ks & Hf).
  inverts Hf.
  simpl in Hgoods; tryfalse.
  unfolds.
  do 3 eexists; splits; eauto.
  unfolds.
  split; simpl; eauto.
  eapply GoodStmt_ndym;eauto.
  splits; eauto.
  lets Hkd : Him H4.
  eapply Hsim.
  split; auto.
  unfolds.
  intros.
  eapply  local_inv_irev_prop; eauto.
Qed.

Lemma frame_rule_sound:
  forall Spec  sd  I p q frm s aop aop' li t, 
    GoodI I sd li -> 
    GoodStmt' s -> 
    GoodFrm frm ->
    p ==> CurLINV li t  ->
    RuleSem Spec  sd li I arfalse Afalse  (<|| aop ||>  ** p) s (<|| aop' ||>  ** q) t  -> 
    RuleSem Spec  sd li I arfalse Afalse (<|| aop ||>  **p **  frm ) s (<|| aop' ||>  ** q  ** frm )  t.
Proof.
  intros.
  eapply conseq_rule_sound.
  instantiate (1:=(<|| aop ||>  **p) **  frm  ).
  sep auto.
  instantiate (1:=(<|| aop' ||>  ** q)  ** frm).
  sep auto.
  sep auto.
  assert
    (RuleSem Spec sd li I (fun v => (arfalse v)** frm) (Afalse**frm) ((<|| aop ||> **p ) ** frm) s ((<|| aop'||>**q ) ** frm) t) .
  eapply frame_rule_all_sound;eauto.
  intros.
  eapply H2.
  sep auto.
  apply conseq_rule_r_sound with (r:=(fun v : option val => arfalse v ** frm)) (ri:=Afalse**frm); auto.
  intros.
  unfold arfalse in *.
  simpl in H5.
  join auto.
  intros; simpl in H5;  join auto.
Qed.

