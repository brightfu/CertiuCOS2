Require Import  sound_include.

Import DeprecatedTactic.

Lemma  fun_seq_comp:
  forall q ri q'  FSpec sd  f s E G li  I r t   M Of ks',
    GoodI I sd li -> 
    (forall v, GoodFunAsrt (q v)) -> 
    (
      forall v o o' Ok O' ab,
        G = get_genv (get_smem o') ->
        E = get_lenv (get_smem o') ->
        (o, Ok, ab) |= q v->
        joinmem o M o' ->
        join Ok Of O' ->
        MethSimMod FSpec sd  (curs (sskip v), (kenil, ks')) o' ab O' li I r ri q' t
    )  ->
    forall c ke ks gamma  o1 o1' O1 O1',
      G = get_genv (get_smem o1) ->
      joinmem o1 M o1' -> 
      join O1 Of O1' ->
      MethSimMod FSpec sd  (c,(ke,ks ## kcall f s E kstop)) o1 gamma O1 li I arfalse Afalse q t  ->
      MethSimMod FSpec sd  (c, (ke, ks ## kcall f s E ks')) o1' gamma O1' li I r ri q' t. 
Proof.
  introv Hgi  Hgood Hforall.
  cofix Hcofix.
  introv  Hg Hjm Hjos   Hsim.
  inverts Hsim.
  assert (notabortm (c,(ke,ks ## kcall f s E kstop))\/ 
          ~notabortm(c,(ke,ks##kcall f s E kstop))) as Hasrt.
  tauto.
  destruct Hasrt as [Htrue | Hfalse].
  assert(frp (c,(ke,ks))\/~(frp (c,(ke,ks)))) as Hfre.
  tauto.
  destruct Hfre as [Hfret | Hfref].
  unfolds in Hfret.
  destruct Hfret as (v & ksv & Hfret & Hfc & Hfi).
  inverts Hfret.
  constructors;introv Hfalse;tryfalse.
  introv Hinv  Hjm2 Hdisj  Hstep.
  invertstep idtac.
  assert ( callcont (ksv ## kcall f s E ks') <> None).
  introv Hv; tryfalse.  
  assert (callcont (ksv ## kcall f s E ks')= Some (kcall f0 s0 le' ks'0)) as Hasrt.
  auto.
  rewrite call_int_none_call in H14; eauto.
  apply eq_sym in H14.
  inverts H14.  
  lets Hfcall' :  IsFcall_kstop v ksv f s E.
  lets Hres :  join_frame_dis Hjm2 Hjm.
  destruct Hres as (MM & Hj1 & Hj2 ).
  lets Hinv' :  joinmem_satp_mono Hinv; eauto.
  assert ( loststep p (curs (sfree nil v), (kenil, ksv ## kcall f s E kstop))  (ge, le, M0, i, au) (curs (sskip v),(kenil, kstop))  (ge, E, M0, i, au)) as Hstp.
  eapply ostc_step; eauto.
  eapply stmt_step; eauto.
  simpl.
  constructors; eauto.  
  lets H00 : callcont_ks_kstop  Hasrt.
  eauto.
  assert (exists O, join O1 Os O /\ join Of O OO) as Hatt.
  clear -Hjos Hdisj.
  join auto.
  destruct Hatt as (O & Hjo1 & Hjo2).
  lets Hsre : H Hfcall'  Hinv'  Hj1 Hjo1 Hstp;  eauto. 
  destruct Hsre as (gam & OO' &  oo & Mss & Ol & Oss  &Hsttar & Hjmm2 & Hjjj  & Hinvv & Hlinv  & Hsim).  

  inverts Hsim.
  lets Has : H13 Hinvv Hjjj; eauto.
  eapply   joinm2_disj ; eauto.
  destruct Has as (g1 & O11 & O12 & Oss' & Hsas & Hjls & Hssa & Hslin & Hqv).
  lets Hsa : hmstepstar_trans Hsttar Hsas.
  lets Hsp : spec_stepstar_locality Hsa Hjo2.
  destruct Hsp as (O2 & Hsp & Hspp).  
  exists g1 O2. 
  lets Habs :  joinm2_join_ex1 Hjmm2 Hj2.
  destruct Habs as (ol & Habs1 & Habs2).
  exists ol Mss.
  assert (exists O, join O Oss' O2 /\ join O12 Of O) as Hjo.
  clear - Hjls Hspp.
  join auto.
  destruct Hjo as (OOl & HjO1 & HjO2).
  exists OOl  Oss'.
  splits; auto.
  eapply joinmem_satp_mono_rev; eauto.
  eapply join_satp_local_inv; eauto.
  eapply Hforall; try eapply joinm2_getenv_eq; eauto.

  (**)
  introv   _ _ _  Hfste.
  unfolds in Hfste.
  apply Hfste.
  destruct o2 as [[[[]]]].
  eexists; exists (e, E, m, i, l) . 
  eapply ostc_step; eauto.
  eapply stmt_step; eauto.
  constructors; eauto.
  eapply call_int_none_call; eauto.
  (******)
  (**)
  constructors.
  introv Hfcall Hinv Hjm1 Hjm2 Hstep.
  lets Hres :  join_frame_dis Hjm1 Hjm.
  destruct Hres as (MM & Hj1 & Hj2 ).
  lets Hinv' :  joinmem_satp_mono Hinv; eauto.
  assert (exists O, join O1 Os O /\ join Of O OO) as Hatt.
  clear -Hjos Hjm2.
  join auto.
  destruct Hatt as (O & Hjo1 & Hjo2).
  assert (disjoint O1 Os) as Hdisj by (unfolds; eauto).

  lets Hfcall' : fcall_kstop Hfcall.
  lets Hnotb : H6 p Htrue Hinv' Hj1 Hdisj.  

  lets Hops :    not_free_cont_loc  Hfref Hstep Hnotb.                                  
  destruct Hops as (c' & ke' & ks1 & Hstpp & Hcc).
  subst C'.
  lets Hres : H p Hfcall' Hinv' Hj1  Hstpp; eauto. 
  destruct Hres as (gam & OO' &  oo & Mss & Ol & Oss  &Hsttar & Hjmm2 & Hjjj  & Hinvv & Hlinv  & Hsim).  
  lets Habs :  joinm2_join_ex1 Hjmm2 Hj2.
  destruct Habs as (ol & Habs1 & Habs2).
  lets Hsp : spec_stepstar_locality Hsttar Hjo2.
  destruct Hsp as (O2 & Hsp & Hspp).  
  assert (exists O, join O Oss O2 /\ join Ol Of O) as Hatt.
  clear - Hjjj Hspp.
  join auto.
  destruct Hatt as (Od & Hjoo1 & Hjoo2).
  exists gam O2.
  exists ol Mss Od Oss.
  splits; auto.
  eapply joinmem_satp_mono_rev; eauto.
  eapply join_satp_local_inv; eauto.
  eapply Hcofix with (o1 := oo); eauto.
  lets Heqg : loststep_keepG Hstep.
  eapply get_genv_join3_eq; eauto.

  (*****)
  introv Hc.
  inverts Hc.
  unfolds in Htrue.
  destruct Htrue as (Hf & _ ).
  false. 
  apply Hf.
  unfolds.
  do 4 eexists; eauto.
  introv Hc.
  inverts Hc.
  unfolds in Htrue.
  destruct Htrue as  ( _ &Hf&_).
  false. 
  apply Hf.
  do 2 eexists; eauto.
  introv Hc.
  inverts Hc.
  false. 
  eapply ks_puls_kcall_neq; eauto.
  introv Hc Hcal Hint.
  inverts Hc.
  false. 
  eapply callcont_not_none ;eauto.
  introv Hcc Hc Hcal Hint.
  inverts Hcc.
  false. 
  eapply callcont_not_none' ; eauto.
  (*
  introv  Hcc Hc Hcal Hint.
  inverts Hcc.
  false. eapply callcont_not_none' ; eauto.
   *)  
  introv Hc  Hcall Hint.
  inverts Hc.
  false. 
  eapply callcont_not_none ; eauto.

  introv Hn Hinv  Hjm1  Hdisj.
  lets Hres :  join_frame_dis Hjm1 Hjm.
  destruct Hres as (MM & Hj1 & Hj2 ).
  lets Hinv' :  joinmem_satp_mono Hinv; eauto.
  (*
  assert (exists O, join O1 Os O /\ join Of O OO) as Hatt.
  clear -Hjos Hjm2.
   *)
  assert (disjoint O1 Os) as Hat.
  clear -Hdisj Hjos.
  unfold disjoint in *.
  join auto.
  lets Hnotb : H6 p Htrue Hinv' Hj1 Hat. 

  eapply  loststepabt_cont_loststepabt; eauto.

  introv Hc; inverts Hc.
  destruct Htrue as  (_& _ &_&_& _& _& Hf&_).
  false. 
  apply Hf.
  do 3 eexists; eauto.

  introv Hc; inverts Hc.
  destruct Htrue as  (_&_& _ &_&_& _& _& Hf).
  false. 
  apply Hf.
  unfolds.
  do 2 eexists; eauto.
  (*
  introv Hc; inverts Hc.
  destruct Htrue as  (_&_& _ &_&_& _& _& Hf).
  false. 
  apply Hf.
  unfolds.
  do 3 eexists; eauto.
   *)
  casenot Hfalse. 
  unfolds in Cs.
  destruct Cs as (f0 & vl & tl & ks0 & Hceq).
  inverts Hceq.
  constructors; introv Hfalse; tryfalse.
  false. 
  apply Hfalse. 
  unfolds; do 4 eexists; eauto.

  inverts Hfalse.
  introv  Hinv Hdisj Hjoin.
  lets Hinv' :  joinmem_satp_mono Hinv; eauto. 

  lets Hds : joinmem_disj_disj  Hjm Hdisj.
  assert (exists O, join O1 Os O /\ join Of O OO) as Hatt.
  clear -Hjos Hjoin.
  join auto.
  destruct Hatt as (O & Hjo1 & Hjo2).
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
  assert (exists OO, join OO Of O'' /\ join O0 Off OO) as Haps.
  clear -Hjqn Hjon.
  join auto.
  destruct Haps as (Oz & Haps1 & Haps2).
  eapply Hcofix with (o1 := oo)  ; eauto.
  eapply  get_genv_jeq;eauto.
  eapply Hsk2; eauto.
  eapply get_genv_jeq; eauto.

  unfolds in Hfalse.
  destruct Hfalse as ( Hff & Hfalse); tryfalse.
  false. 
  apply Hff.
  unfolds. 
  do 4 eexists; eauto. 

  casenot Hfalse. 
  destruct Cs as (x & ks0 & Hceq).
  inverts Hceq.
  constructors; introv Hfalse; tryfalse.
  introv _ _ _ Hlss.
  invertstep tryfalse.

  inverts Hfalse.
  introv Hinv  Hdisj Hjoin.
  lets Hinv' :  joinmem_satp_mono Hinv; eauto.
  lets Hds : joinmem_disj_disj  Hjm Hdisj.
  assert (exists O, join O1 Os O /\ join Of O OO) as Hatt.
  clear -Hjos Hjoin.
  join auto.
  destruct Hatt as (O & Hjo1 & Hjo2).
  lets Hres : H1  Hinv' Hjo1; eauto.
  destruct Hres as ( gam & ss  & O' & oo& Mc  & Ol & Oss &  Oll & Oc 
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
  unfold joinmem in Hjm.
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
  eapply Hcofix with (o1:=oo1) (O1':=O'');eauto.

  eapply get_genv_joinmem_eq; eauto.
  eapply Hfo1 with (Mc':=Mc')(O'':=Od); eauto.
  
  eapply join3_satp_swinv_rev with (Mc:=Mc'); eauto.
  right.
   clear -Hfoo2 Hjm.
  unfold joinmem in Hjm.
  simp join.
  simpl substaskst in *.
  auto.

  unfolds in Hfalse. 
  destruct Hfalse as(_& Hf &_).
  false. apply Hf.
  do 2 eexists; eauto.

  casenot Hfalse. 
  destruct Cs as (vv & Hceq).
  inverts Hceq.
  false. eapply ks_puls_kcall_neq; eauto. 
  casenot Hfalse. 
  destruct Cs as (ks0 & Heqc & Hcal & Hint).
  inverts Heqc.
  false. eapply callcont_not_none; eauto.
  casenot Hfalse. 
  destruct Cs as (vv & Kss & Heq & Hcal&Hint).
  inverts Heq. 
  false. eapply callcont_not_none'; eauto.
  casenot Hfalse. 
  destruct Cs  as (ks0 & Heq & Hint & Hcal).
  inverts Heq.
  false. eapply callcont_not_none; eauto.
  
  casenot Hfalse. 
  unfolds in Cs.
  destruct Cs as (e1&e2&e3&kss&Hceq).
  inverts Hceq.
  constructors; introv Hfalse; tryfalse.
  introv _ _ _ Hlss.
  invertstep tryfalse.
  unfolds in Hfalse.
  destruct Hfalse as (_& Hfalse).
  destruct Hfalse as (_&_&_&_& _&Hfalse&_).
  false.
  apply Hfalse.
  do 4 eexists; eauto.

  introv  Hinv  Hdisj Hjoin.
  lets Hinv' :  joinmem_satp_mono Hinv; eauto.
  lets Hds : joinmem_disj_disj  Hjm Hdisj.
  assert (exists O, join O1 Os O /\ join Of O OO) as Hatt.
  clear -Hjos Hjoin.
  join auto.
  destruct Hatt as (O & Hjo1 & Hjo2).
  lets Hres : H7  Hinv' Hjo1; eauto.
  destruct Hres as
      (gam& v1&v2&t' &prio&ss &O11& O22&o11&mcr& Ol& Oss& Oll & ocr 
          &Heqc & Hev1 & Hev2 & Hev3 & Hstarr & Hcrt & Hjonm1 & Hjn1 & 
          Hjn2 &  Hinvv & Hlinv & Hscr & Hsim).
  lets Hsp : spec_stepstar_locality Hstarr Hjo2.
  destruct Hsp as (O2 & Hsp & Hspp).  
  exists gam v1 v2 t' prio ss.

  inverts Hfalse.
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
  eapply Hcofix with (o1:=o11) (O1':=Ok2);eauto.

  eapply  get_genv_joinmem3_eq; eauto.
  
  apply Classical_Prop.NNPP in Hfalse.
  unfolds  in Hfalse.
  destruct Hfalse as (e & kss & Hecq).
  inverts Hecq.
  constructors; introv Hfalse; tryfalse.
  introv _ _ _ Hlss.
  invertstep tryfalse.
  unfolds in Hfalse.
  destruct Hfalse as (_& Hfalse).
  destruct Hfalse as (_&_&_&_& _&_&Hfalse).
  false.
  apply Hfalse.
  do 2 eexists; eauto.


  inverts Hfalse.
  introv  Hinv  Hdisj Hjoin.
  lets Hinv' :  joinmem_satp_mono Hinv; eauto.
  lets Hds : joinmem_disj_disj  Hjm Hdisj.
  assert (exists O, join O1 Os O /\ join Of O OO) as Hatt.
  clear -Hjos Hjoin.
  join auto.
  destruct Hatt as (O & Hjo1 & Hjo2).
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
  eapply Hcofix with (o1:=o1 ) (O1':=Od );eauto.

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
  
  assert (exists o, joinmem o1 Mdel o /\ joinmem o M o') as Hjmk.
  clear -Hjm Hj2.
  unfold joinmem in *.
  join auto.
  destruct Hjmk as (oo1 & Hjoo1 & Hjoo2).
  (*assert (exists OO, join OO Of O'' /\  join Ol Odel OO ) as Haxt.*)
  assert ( join Ol Of Od) by auto.
  assert ( join Od Odel O'') by auto.
  lets Hxsx: join_ex2 H9  H10.
  destruct  Hxsx as (OOk & Hook1 & Hook2).
  eapply Hcofix with (o1:= oo1) (O1:= OOk); eauto.
  eapply  get_genv_join2del_eq; eauto.
Qed.



Lemma fun_free_ignore : 
  forall P f FSpec  sd I pr post vl s E' ks logicl li t,
    post_imp_linv  post li  vl logicl t->
    Some pr = BuildRetI P f vl logicl post t ->
    callcont ks = None -> 
    intcont ks = None -> 
    (
      forall (o : taskst) (O : osabst) (aop : absop) (v:option val) al,
        (o, O, aop) |= (pr v) -> 
        getaddr (get_lenv (get_smem o)) = al ->
        MethSimMod FSpec sd (curs (sfree al v), (kenil,  ks ## kcall f s E' kstop)) o 
                   aop O li I  arfalse Afalse (fun v => getasrt (post (rev vl) v logicl t)) t
    ).      
Proof.
  introv Himp Hspec Hct Hit Hsat Hgeta.
  destruct o as [[[[G E] M] isr] aux].
  simpl in Hgeta.
  rewrite <- Hgeta.
  unfold BuildRetI in Hspec.
  destruct (P f) ; tryfalse.
  destruct f0.
  destruct p as [[]].
  remember ( buildq (revlcons d d0)) as Hq.
  destruct Hq; tryfalse.
  inverts Hspec.
  (* destruct Hsat as (Hsat  & Hop).
  simpl in Hop.
  subst aop.
   *)
  unfold sat in Hsat; fold sat in Hsat.
  simpl substmo in *.
  simpl assertion.getmem in *.
  simpl getabst in *.
  mytac.
  simpl getlenv in H9.
  simpl in H10.
  mytac.

  lets Hin :  free_intro  HeqHq H9 H0; eauto.
  destruct Hin as(Hempo & Hfreels).
  subst x2.
  mytac.
  eapply free_stepn_sim_hold;  eauto.

  constructors; introv Hfalse; tryfalse.
  introv Hinv Hjm  Hjoin  Hstep.
  invertstep idtac.
  rewrite callcont_some_eq in H6; eauto.
  eapply sym_eq in H6.
  inverts H6.
  simpl substaskst in *.
  unfold joinm2 in Hjm.
  unfold joinmem in Hjm.
  mytac.
  exists aop OO (x2, E', x10, x6, x7) Ms O Os.
  splits; auto.
  constructors.
  unfolds.
  eexists.
  unfold joinmem.
  splits; do 6 eexists; eauto.
  simpl.
  unfold satp in *.
  intros.
  eapply INV_irrev_prop; eauto.
  lets Hxk : Himp H8.

  eapply  local_inv_E_irev; eauto.
  constructors; introv Hf; tryfalse.
  introv _ _  _ Hstep.
  invertstep idtac.
  
  introv   Hinvv   Hdisjj Hjon.
  exists aop OO0 O Os0  .
  inverts Hf.
  splits; eauto.
  constructors.
  lets Hxk : Himp H8.
  eapply  local_inv_E_irev; eauto.
  eapply good_fun_asrt_absop; eauto.
  apply (getprop (post (rev vl) v0 logicl t)).
  unfolds in Hf.
  destruct Hf as (_&_&Hf &_).
  false. apply Hf; eexists; eauto.
  introv _ _ _  Hstep. 
  apply Hstep.
  destruct o2 as [[[[]]]].
  do 2 eexists.
  eapply ostc_step; eauto.
  eapply stmt_step; eauto.
  constructors; eauto.
  eapply callcont_some_eq; eauto.
  Grab Existential Variables.
  eauto.
Qed.


Lemma fun_free_comp : 
  forall P f FSpec sd I pr post vl s E' logicl li t,
    Some pr = BuildRetI P f  vl logicl post t->
    (
      forall (o : taskst) (O : osabst) (aop : absop) (v:option val) al ks1,
        callcont ks1  = None -> 
        intcont ks1 = None -> 
        (o, O, aop) |= (pr v) ->
        getaddr (get_lenv (get_smem o)) = al ->
        MethSimMod FSpec sd  (curs (sfree al v), (kenil, ks1 ##  kcall f s E' kstop)) o aop O li I arfalse Afalse 
                   (fun v =>   getasrt (post (rev vl) v logicl t)) t
    )  ->
    forall c ke ks G E M isr aux O gamma, 
      MethSimMod FSpec sd  (c, (ke,ks)) (G, E, M, isr, aux) gamma O li I pr Afalse (lift Afalse) t ->
      MethSimMod FSpec sd (c, (ke, ks ## kcall f s E' kstop))  (G, E, M, isr, aux) gamma O li I arfalse Afalse 
                 (fun v =>   getasrt (post (rev vl) v logicl t)) t.
Proof.
  introv Hpr Hforal.
  cofix Hcofix.
  introv Hsim.
  assert ( notabortm (c,(ke,ks)) \/ ~  notabortm (c,(ke,ks))) as Hasrt.
  tauto.
  destruct Hasrt as [Htrue | Hfalse].
  inverts Hsim.
  constructors.
  introv Hfcall Hinv Hjm1 Hjm2 Hstep.
  assert (disjoint O Os)  as Hdisj.
  unfolds.
  eauto.
  lets Hnota : H6 p Htrue Hjm1 Hdisj; eauto.
  lets Heq :  cont_frame_mono Hnota Hstep.
  destruct Heq as (c'& ke'& ks'&  Hlstep & HC).
  subst C'.
  lets Hfcal' : fcall_not Hfcall.
  lets Hres : H Hfcal' Hinv Hjm1 Hjm2 Hlstep. 
  simp join.
  do 6 eexists; splits; eauto.
  destruct x1 as [[[[]]]].
  eapply Hcofix;eauto.
  
  introv Hc.
  inverts Hc.
  unfolds in Htrue.
  destruct Htrue as (Hf & _ ).
  false. apply Hf.
  unfolds.
  do 4 eexists; eauto.

  introv Hc.
  inverts Hc.
  unfolds in Htrue.
  destruct Htrue as  ( _ &Hf&_).
  false. apply Hf.
  do 2 eexists; eauto.

  introv Hc.
  inverts Hc.
  false. eapply ks_puls_kcall_neq; eauto.
  introv Hc Hcal Hint.
  inverts Hc.
  false. eapply callcont_not_none ;eauto.
  introv Hc Hcal Hint.
  inverts Hc.
  false. eapply callcont_not_none' ; eauto.
  introv Hc  Hcal Hint.
  inverts Hc.
 
  false. eapply callcont_not_none ; eauto.
  introv Hnot  Hinv Hjm1  Hdisj.
  lets Hnotb : H6 p Htrue Hjm1 Hdisj; eauto.  
  eapply  loststepabt_cont_loststepabt'; eauto.
  
  introv Hc.
  inverts Hc.
  destruct Htrue as  ( _&_ &_&_&_&_&Hf&_).
  false. apply Hf.
  do 4 eexists; eauto.
  
  introv Hc.
  inverts Hc.
  destruct Htrue as  ( _&_ &_&_&_&_&_&Hf).
  false. apply Hf.
  do 2 eexists; eauto.

  casenot Hfalse. 
  unfolds in Cs.
  destruct Cs as (f0 & vl' & tl & ks0 & Hceq).
  inverts Hceq.
  constructors; introv Hfalse; tryfalse.
  false.  apply Hfalse. 
  unfolds; do 4 eexists; eauto.
  inverts Hfalse.
  inverts Hsim.
  clear H H1 H2 H3 H4 H5 H6 H7 H8.
  introv  Hinv Hdisj Hjoin.
  lets Hres : H0  Hinv Hdisj Hjoin; eauto.
  simp join.
  do 12 eexists; splits; eauto.
  splits; auto.
  introv Hsat2.
  apply H9 in Hsat2.
  destruct Hsat2 .
  split; auto.
  intros.
  destruct o' as [[[[]]]].
  eapply Hcofix; eauto.

  unfolds in Hfalse.
  destruct Hfalse as ( Hff & Hfalse); tryfalse.
  false. 
  apply Hff.
  unfolds. 
  do 4 eexists; eauto. 
  casenot Hfalse. 
  destruct Cs as (x & ks0 & Hceq).
  inverts Hceq.
  constructors; introv Hfalse; tryfalse.
  introv _ _ _ Hlss.
  invertstep idtac.

  inverts Hfalse.
  introv  Hinv Hdisj Hjoin. 
  inverts Hsim.
  lets Hres : H1  Hinv Hdisj Hjoin; eauto.
  simp join.
  do 9 eexists; splits; eauto. 
  splits; eauto.
  destruct H17.
  left.
  simp join.
  splits; auto.
  introv  Hsat Hjm Hiv.
  destruct o' as [[[[]]]].
  eapply Hcofix; eauto.
  right; auto.


  unfolds in Hfalse. 
  destruct Hfalse as(_& Hf &_).
  false. apply Hf.
  do 2 eexists; eauto.

  casenot Hfalse. 
  destruct Cs as (vv & Hceq).
  inverts Hceq.
  constructors; introv Hfalse; tryfalse.
  introv _ _ _ Hstep.
  invertstep idtac.

  introv  Hinv Hjm1 Hdisj.
  inverts Hsim.
  unfold disjoint in Hdisj.
  destruct Hdisj as (z & Hdisj).

  lets Hfal : H2  Hdisj; eauto.
  unfold joinm2 in Hjm1.
  unfold joinmem in *.
  simp join.
  unfolds.
  unfold getmem.
  simpl.
  eauto.
  simp join.
  simpl in H13;tryfalse.

  casenot Hfalse. 
  destruct Cs as (ks0 & Heqc & Hcal & Hint).
  inverts Heqc.
  constructors; introv Hfalse; tryfalse.
  introv Hinv Hjm1 Hjm2 Hstep.
  invertstep idtac.
  rewrite  callcont_some_eq in H0; eauto.
  apply eq_sym in H0.
  inverts H0.
  inverts Hsim.
  lets Hes : H3 Hcal Hint Hinv Hjm2; eauto.
  unfold joinm2 in Hjm1.
  unfold joinmem in *.
  simp join.
  unfolds.
  unfold getmem.
  simpl.
  eauto.

  destruct Hes as ( gam & OO' & O' & Os' & Hstar & Hjoins & Hinvv &   Hlinvv  & Hsat).
  do 6 eexists; splits; eauto.
  eapply Hforal; eauto.
  unfold joinm2 in Hjm1.
  unfold joinmem in *.
  simp join.
  simpl.
  auto.

  introv Hcal1 Hint1.
  assert  (callcont (ks0 ## kcall f s E' kstop)  = Some (kcall f s E' kstop)).
  eapply callcont_some_eq; eauto.
  tryfalse.

  introv  _ _ _ Hstep.
  apply Hstep.
  destruct o2 as [[[[]]]].
  assert (exists al, getaddr e0 = al).
  apply  get_env_addrlist_ex.
  destruct H .
  eexists.
  exists   (e, e0, m, i, l).
  eapply ostc_step; eauto.
  eapply stmt_step; eauto.
  constructors; eauto.
  eapply callcont_some_eq; eauto.

  casenot Hfalse. 
  destruct Cs as (vv & ks0 & Heqc & Hcal& Hint).
  inverts Heqc.
  constructors; introv Hfalse; tryfalse.
  introv Hinv Hjm1 Hjm2 Hstep  .
  invertstep idtac.

  inverts Hsim.
  lets Hes : H5 Hcal Hint Hinv Hjm2 ; eauto.
  unfold joinm2 in Hjm1.
  unfold joinmem in *.
  simp join.
  unfolds.
  unfold getmem.
  simpl.
  eauto.
  simp join.
  do 6 eexists; splits; eauto.
  eapply Hforal; eauto.
  unfold joinm2 in Hjm1.
  unfold joinmem in *.
  simp join.
  simpl.
  auto.

  inverts Hfalse.
  introv  Hcal1 Hint1.
  lets Hks : callcont_intcont_kcall_none Hcal Hint1.
  assert  (callcont (ks0 ## kcall f s E' kstop)  = Some (kcall f s E' kstop)).
  eapply callcont_some_eq; eauto.
  tryfalse.

  introv  _ _ _ Hstep.
  apply Hstep.
  destruct o2 as [[[[]]]].
  assert (exists al, getaddr e0 = al).
  apply  get_env_addrlist_ex.
  destruct H.
  eexists.
  exists   (e, e0, m, i, l).
  eapply ostc_step; eauto.
  eapply stmt_step; eauto.
  constructors.  trivial. eauto. 
  eauto.
  fold AddKsToTail.
  lets Hsss  : call_int_none_call f s E' kstop  Hint. eauto.
  tryfalse.
  eauto.
  intro;tryfalse.
  eauto.

  casenot Hfalse.
  destruct Cs as (ks0 & Heq & Hint & Hcal).
  inverts Heq.
  constructors; introv Hfalse;tryfalse.
  introv _ _ _  Hlost.
  invertstep idtac.
  assert (intcont (ks0 ## kcall f s E' kstop) <> None) as Ha.  introv Ha'.  
  tryfalse.
  lets Hff :  intcont_some_kcall_none  Ha.
  tryfalse.
  inverts Hfalse.
  introv Hcal1 Hint1.
  lets Hfa : intcont_calcont_not_none f s E' kstop Hint.
  tryfalse.
  unfolds in Hfalse.
  destruct Hfalse as  (_&_&_& _ &_ &Hf&_ ).
  introv  Hinv Hjm1 Hjm2 .
  inverts Hsim.
  assert (exists OO, join O Os OO) as Hk.
  eauto.
  destruct Hk as (Ok & Hk).
  lets Hres : H5 Hcal Hint Hinv Hk; eauto.
  unfold joinm2 in Hjm1.
  unfold joinmem in *.
  simp join.
  unfolds.
  unfold getmem.
  simpl.
  eauto.
  simp join.
  simpl in H13; tryfalse.

  casenot Hfalse.
  unfolds in Cs.
  destruct Cs as (e1& e2 & e3 & kss & Heqc).
  inverts Heqc.

  constructors; introv Hfalse; tryfalse.
  introv _ _ _ Hstep.
  invertstep idtac.
  unfolds in Hfalse. 
  destruct Hfalse as(_&_&_&_&_&_&Hf &_).
  false. apply Hf.
  do 4 eexists; eauto.
  
  inverts Hfalse.
  inverts Hsim.
  clear H H0 H1 H2 H3 H4 H5 H6 H8.
  introv  Hinv Hdisj Hjoin.
  lets Hres : H7  Hinv Hdisj Hjoin; eauto.
  simp join.
  do 14 eexists; splits; eauto.
  splits; eauto.
  destruct x7 as [[[[]]]].
  eapply Hcofix; eauto.

  apply Classical_Prop.NNPP in Hfalse.
  unfolds in Hfalse.
  destruct Hfalse as (e&kss & Heqc).
  inverts Heqc.
  constructors; introv Hfalse; tryfalse.
  introv _ _ _ Hstep.
  invertstep idtac.
  unfolds in Hfalse. 
  destruct Hfalse as(_&_&_&_&_&_&_ &Hf).
  false. apply Hf.
  do 2 eexists; eauto.
  
  inverts Hfalse.
  inverts Hsim.
  clear H H0 H1 H2 H3 H4 H5 H6 H7.
  introv  Hinv Hdisj Hjoin.
  lets Hres : H8  Hinv Hdisj Hjoin; eauto.
  simp join.
  do 5 eexists; splits; eauto.
  destruct H2.
  simp join.
  left.
  do 3 eexists; splits; eauto.
  right.
  simp join.
  do 3 eexists; splits; eauto.
  intros.
  destruct o' as [[[[]]]].
  eapply Hcofix; eauto.
Qed.
