Require Import include_frm.
Require Import oscorrectness.
Require Import simulation.
Require Import auxdef.
Require Import Classical.
Require Import sep_auto.
Require Import base_tac.
Require Import soundness.
Require Import absinfer_sound.
Require Import memory_prop.
Require Import joinmemLib.
Require Import lmachLib.
Require Import contLib.
Require Import cstepLib.
Require Import rulesoundlib.
Require Import mem_join_lemmas.
Require Import perm_map_lemmas.
Import DeprecatedTactic.

Ltac unfolddef:=
  try
    (unfold code in *;unfold cont in *;unfold tid in *;unfold TMSpecMod.B in *;
     unfold mmapspec.image in *;
     unfold TOSpecMod.B in *;
     unfold omapspec.image in *;unfold Maps.sub in *;unfold disjoint in *;unfold osabst in *).

     

Lemma Goodstmt_good_clt_stmt
: forall (s : stmts) (p : progunit), GoodStmt s p -> good_clt_stmt s p.
Proof.
  intros.
  induction s;simpl in * ;auto.
  destruct H.
  split.
  apply IHs1;auto.
  apply IHs2;auto.
  destruct H.
  split.
  apply IHs1;auto.
  apply IHs2;auto.
  false.
Qed.


Lemma intcont_local
: forall (ks' : stmtcont) (c : cureval) (ke : exprcont) 
         (lenv : env) (ks : stmtcont),
    intcont ks' = None ->
    callcont ks' = None ->
    intcont (ks' ## kint c ke lenv ks) = Some (kint c ke lenv ks).
Proof.
  intros.
  induction ks';simpl;auto;tryfalse.
Qed.

Lemma int_inos_sw_still
: forall (x : var) (ks1 ks : stmtcont) (cx : cureval) 
         (kex : exprcont) (lenv : env) (po pi : progunit),
    InOS (curs (sprim (switch x)), (kenil, ks1 ## kint cx kex lenv ks))
         (pumerge po pi) ->
    InOS (SKIP , (kenil, ks1 ## kint cx kex lenv ks)) (pumerge po pi).
Proof.
  intros.
  unfold InOS.
  intros.
  destruct H as (c&ke&ks0&H&HH).
  inversion H.
  subst c ke ks0.
  exists SKIP kenil (ks1##kint cx kex lenv ks).
  split;auto.
  destruct HH.
  destruct H0 as (a&b&c&d&e&g).
  tryfalse.
  destruct H0.
  right.
  left.
  auto.
  right.
  right.
  auto.
Qed.


Lemma int_inos_stkinit_still
: forall e1 e2 e3 (ks1 ks : stmtcont) (cx : cureval) 
         (kex : exprcont) (lenv : env) (po pi : progunit),
    InOS (curs (sprim (stkinit e1 e2 e3)), (kenil, ks1 ## kint cx kex lenv ks))
         (pumerge po pi) ->
    InOS (SKIP , (kenil, ks1 ## kint cx kex lenv ks)) (pumerge po pi).
Proof.
  intros.
  unfold InOS.
  intros.
  destruct H as (c&ke&ks0&H&HH).
  inversion H.
  subst c ke ks0.
  exists SKIP kenil (ks1##kint cx kex lenv ks).
  split;auto.
  destruct HH.
  destruct H0 as (a&b&c&d&e&g).
  tryfalse.
  destruct H0.
  right.
  left.
  auto.
  right.
  right.
  auto.
Qed.


Lemma int_inos_stkfree_still
: forall e (ks1 ks : stmtcont) (cx : cureval) 
         (kex : exprcont) (lenv : env) (po pi : progunit),
    InOS (curs (sprim (stkfree e)), (kenil, ks1 ## kint cx kex lenv ks))
         (pumerge po pi) ->
    InOS (SKIP , (kenil, ks1 ## kint cx kex lenv ks)) (pumerge po pi).
Proof.
  intros.
  unfold InOS.
  intros.
  destruct H as (c&ke&ks0&H&HH).
  inversion H.
  subst c ke ks0.
  exists SKIP kenil (ks1##kint cx kex lenv ks).
  split;auto.
  destruct HH.
  destruct H0 as (a&b&c&d&g&h).
  tryfalse.
  destruct H0.
  right.
  left.
  auto.
  right.
  right.
  auto.
Qed.


Lemma inos_int
: forall (c : cureval) (ke : exprcont) (ks ks' : stmtcont)
         (c' : cureval) (ke' : exprcont) (po pi : progunit) 
         (lenv : env),
    InOS (c, (ke, ks ## kint c' ke' lenv ks')) (pumerge po pi) ->
    InOS (c, (ke, ks ## kint c' ke' lenv kstop)) (pumerge po pi).
Proof.
  unfold InOS.
  intros.
  destruct H as (c0&ke0&ks0&H1&H2).
  inversion H1.
  subst c0 ke0 ks0.
  exists c ke (ks##kint c' ke' lenv kstop).
  splits;auto.
  destruct H2.
  left;auto.
  destruct H.
  right;left.
  destruct H as (f&le&ks'0&t&d1&d2&s&s'&H).
  destruct H.
  induction ks;simpl;auto;tryfalse.
  exists f le (ks ## kint c' ke' lenv kstop) t d1 d2.
  exists s s'.
  unfold callcont in H.
  simpl in H.
  inversion H;subst f0 s0 ks'0.
  split;auto.
  right.
  right.
  intro X.
  destruct H.
  induction ks;simpl;auto;tryfalse.
Qed.


Lemma abs_crt_step_local:
  forall Of O O' t t' pri,
    disjoint O Of ->
    abs_crt_step O O' t t' pri ->
    abs_crt_step (merge Of O) (merge Of O') t t' pri.
Proof.
  intros.
  inversion H0; simpljoin.
  unfolds.
  split; auto.
  pose proof disj_indom (A:=absdataid) (B:=absdata) (T:=OSAbstMod.map).
  lets Hx: H5 H; auto; clear H5.
  exists x x0.
  splits.
  
  rewrite merge_sem.
  rewrite H2.
  pose proof Hx curtid; destruct H5.
  unfold indom in *.
  assert (exists v, get O curtid = Some v) by eauto.
  apply H5 in H7.
  destruct (get Of curtid) eqn : eq1.
  false; apply H7; eauto.
  auto.
  auto.
  
  rewrite merge_sem.
  rewrite H3.
  pose proof Hx abstcblsid; destruct H5.
  unfold indom in *.
  assert (exists v, get O abstcblsid = Some v) by eauto.
  apply H5 in H7.
  destruct (get Of abstcblsid) eqn : eq1.
  false; apply H7; eauto.
  auto.
  auto.
  
  auto. 
  erewrite <- merge_set_eq_2; eauto.
  apply disjoint_sym; auto.
Qed.


Lemma abs_crt_disj:
  forall t t' pri (O O' Of : osabst),
    disjoint Of O -> abs_crt_step O O' t t' pri -> disjoint Of O'.
Proof.
  intros.
  inversion H0; simpljoin.
  eapply disj_set_disj_2; eauto.
Qed.

Lemma abs_delself_step_local:
  forall Of O O' t t' pri,
    disjoint O Of ->
    abs_delself_step O O' t t' pri ->
    abs_delself_step (merge Of O) (merge Of O') t t' pri.
Proof.
  intros.
  inversion H0; simpljoin.
  inversion H3; simpljoin.
  unfolds.
  split; auto.

  pose proof disj_indom (A:=absdataid) (B:=absdata) (T:=OSAbstMod.map).
  lets Hx: H5 H; auto; clear H5.
  split.
  rewrite merge_sem.
  rewrite H2.
  pose proof Hx curtid; destruct H5.
  unfold indom in *.
  assert (exists v, get O curtid = Some v) by eauto.
  apply H5 in H7.
  destruct (get Of curtid) eqn : eq1.
  false; apply H7; eauto.
  auto.
  auto.
  
  unfolds.
  exists x x0 x1 x2.
  splits; auto.

  rewrite merge_sem; auto.
  rewrite H1.
  pose proof Hx abstcblsid; destruct H5.
  unfold indom in *.
  assert (exists v, get O abstcblsid = Some v) by eauto.
  apply H5 in H7.
  destruct (get Of abstcblsid) eqn : eq1.
  false; apply H7; eauto.
  auto.

  auto. 
  erewrite <- merge_set_eq_2; eauto.
  apply disjoint_sym; auto.
Qed.

  
Lemma abs_delself_disj:
  forall t t' pri (O O' Of : osabst),
    disjoint Of O -> abs_delself_step O O' t t' pri -> disjoint Of O'.
Proof.
  intros.
  inversion H0; simpljoin.
  inversion H3; simpljoin.
  eapply disj_set_disj_2; eauto.
Qed.

Lemma abs_delother_step_local:
  forall Of O O' t t' pri,
    disjoint O Of ->
    abs_delother_step O O' t t' pri ->
    abs_delother_step (merge Of O) (merge Of O') t t' pri.
Proof.
  intros.
  inversion H0; simpljoin.
  inversion H3; simpljoin.
  unfolds.
  split; auto.

  pose proof disj_indom (A:=absdataid) (B:=absdata) (T:=OSAbstMod.map).
  lets Hx: H6 H; auto; clear H6.
  split.
  rewrite merge_sem; auto.
  rewrite H2.
  pose proof Hx curtid; destruct H6.
  unfold indom in *.
  assert (exists v, get O curtid = Some v) by eauto.
  apply H6 in H8.
  destruct (get Of curtid) eqn : eq1.
  false; apply H6; eauto.
  auto.
  
  unfolds.
  exists x x0 x1 x2.
  splits; auto.

  rewrite merge_sem; auto.
  rewrite H4.
  pose proof Hx abstcblsid; destruct H6.
  unfold indom in *.
  assert (exists v, get O abstcblsid = Some v) by eauto.
  apply H6 in H8.
  destruct (get Of abstcblsid) eqn : eq1.
  false; apply H8; eauto.
  auto.

  auto. 
  erewrite <- merge_set_eq_2; eauto.
  apply disjoint_sym; auto.
Qed.


Lemma abs_delother_disj:
  forall t t' pri (O O' Of : osabst),
    disjoint Of O -> abs_delother_step O O' t t' pri -> disjoint Of O'.
Proof.
  intros.
  inversion H0; simpljoin.
  inversion H3; simpljoin.
  eapply disj_set_disj_2; eauto.
Qed.

Lemma htstepstar_compose_tail
: forall (p : hprog) (c : code) (O : osabst) (cst : clientst)
         (c' : code) (O' : osabst) (cst' : clientst) 
         (c'' : code) (cst'' : clientst) (O'' : osabst) 
         (t : tid),
    htstepstar p t c cst O c' cst' O' ->
    htstep p t c' cst' O' c'' cst'' O'' ->
    htstepstar p t c cst O c'' cst'' O''.
Proof.
  introv Ha Hb.
  inductions Ha.
  constructors; eauto.
  constructors.
  constructors; eauto.
Qed.

Lemma osapi_lift1':
  forall r O r' O' ke ks pc cst t a c, 
    hmstep c r O r' O' ->
    htstep (pc, (a,c)) t (curs (hapi_code r),(ke,ks)) cst O (curs (hapi_code r'),(ke,ks)) cst O'.
Proof.
  intros.
  eapply hapi_step;eauto.
  eapply hidapi_step;eauto.
Qed.


Lemma osapi_lift'
: forall (A : osspec) (gamma : spec_code) (O O' : osabst)
         (gamma' : spec_code) (pc : progunit) (ke : exprcont) 
         (ks : stmtcont) (cst : clientst) (t : tid),
    hmstepstar (snd A) gamma O gamma' O' ->
    htstepstar (pc, A) t (curs (hapi_code gamma), (ke, ks)) cst O
               (curs (hapi_code gamma'), (ke, ks)) cst O'.
Proof.
  intros.
  destruct A as (a,b).
  simpl snd in *.
  generalize cst pc ks.
  clear cst pc ks.
  inductions H.
  intros.
  apply ht_starO.
  intros.
  eapply osapi_lift1' with (c:=sc) (cst:=cst) (pc:=pc) in H;eauto.
  destruct cst as (D,F).
  eapply ht_starS;eauto.
Qed.


Lemma hmstep_disj:
  forall sd ab ab' O O' Of,
    disjoint Of O ->
    hmstep sd ab O ab' O' ->
    disjoint Of O'.
Proof.
  intros.
  unfolds in H.
  mytac.
  lets Hx: specstep_locality H H0.
  mytac.
  unfolds;eauto.
Qed.

Lemma hmstepstar_disj:
  forall sd ab ab' O O' Of,
    disjoint Of O ->
    hmstepstar sd ab O ab' O' ->
    disjoint Of O'.
Proof.
  intros.
  inductions H0;auto.
  apply IHspec_stepstar.
  eapply hmstep_disj;eauto.
Qed.


Lemma callcont_nonone_addcont: 
  forall ks ks1,
    callcont ks <> None -> callcont (ks ## ks1) <> None.
Proof.
  intros.
  assert (exists x, callcont ks = Some x).
  destruct (callcont ks).
  eexists;auto.
  tryfalse.
  destruct H0.
  assert (callcont (ks ## ks1)= Some (x ## ks1)).
  apply callcont_some_addcont;auto.
  intro;tryfalse.
Qed.


Lemma sstep_cont_locality : forall po pi c c' ks ks' ks'' m m',
                              sstep (pumerge po pi) c ks m c' ks' m' ->
                              sstep (pumerge po pi) c (ks ## ks'') m c' (ks' ## ks'') m'.
Proof.
  intros.
  inv H; constructors; eauto;
  try (pose proof callcont_some_addcont;
       pose proof (H ks' ks'' (kcall f s le' ks'0) H1);
       apply H0).
  apply callcont_nonone_addcont.
  auto.
  pose proof callcont_some_addcont.
  pose proof (H ks ks'' (kcall f s le' ks') H2).
  apply H0.
Qed.

Lemma cstep_cont_locality : forall po pi c c' ke ke' ks ks' ks'' m m',
                              cstep (pumerge po pi) (c, (ke, ks)) m (c', (ke', ks')) m' ->
                              cstep (pumerge po pi) (c, (ke, ks ## ks'')) m (c', (ke', ks' ## ks'')) m'.
Proof.
  intros.
  inv H.
  inv H7.
  eapply expr_step.
  auto.
  auto.
  eapply stmt_step.
  inv H7.
  auto.
  inv H7.
  eapply sstep_cont_locality.
  auto.
Qed.

Lemma loststep_cont_locality: forall c ke ks o o' c' ke' ks' po pi ks'', loststep (pumerge po pi) (c,(ke,ks)) o (c',(ke',ks')) o' -> loststep (pumerge po pi) (c,(ke,ks ## ks'')) o (c',(ke',ks' ## ks'')) o'.
Proof.
  intros.
  inv H; 
    try solve [inv H7; constructors; eauto].
  eapply ostc_step.
  eapply cstep_cont_locality.
  auto.

  inv H7.
  eapply exint_step; eauto.
  pose proof intcont_some_addcont.
  pose proof (H ks0 ks'' (kint c' ke' le' ks') H8).
  apply H0.
  inv H6.
  eapply eoi_step; eauto.
  inverts H3.
  eapply checkis_step; eauto.
Qed.

Lemma cstep_no_api_local:
  forall po pi c ke ks c' ke' ks' o o',
  no_call_api (c,(ke,ks)) po -> 
  cstep pi (c, (ke, ks)) o (c', (ke', ks')) o' -> 
  cstep (pumerge po pi) (c, (ke, ks)) o (c', (ke', ks')) o'.
Proof.
  intros.
  inverts H0;inverts H8.
  eapply expr_step;eauto.
  eapply stmt_step;eauto.
  inverts H9;constructors;eauto.
  instantiate (1:=t).
  simpl in H.
  unfold pumerge.
  destruct H.
  rewrite H.
  rewrite H2;auto.
Qed.

Lemma loststep_no_api_local:
  forall po pi c ke ks c' ke' ks' o o',
  no_call_api (c,(ke,ks)) po -> 
  loststep pi (c, (ke, ks)) o (c', (ke', ks')) o' -> 
  loststep (pumerge po pi) (c, (ke, ks)) o (c', (ke', ks')) o'.
Proof.
  intros.
  inverts H0;first [eapply checkis_step | constructors];eauto;tryfalse.
  eapply cstep_no_api_local;eauto.
Qed.

Lemma inos_int':forall c ke ks ks' c' ke' po pi lenv, InOS (c, (ke, ks ## kint c' ke' lenv kstop)) (pumerge po pi) -> InOS (c, (ke, ks ## kint c' ke' lenv ks')) (pumerge po pi).
Proof.
  unfold InOS.
  intros.
  destruct H as (c0&ke0&ks0&H1&H2).
  inversion H1.
  subst c0 ke0 ks0.
  exists c ke (ks##kint c' ke' lenv ks').
  splits;auto.
  destruct H2.
  left;auto.
  destruct H.
  right;left.
  destruct H as (f&le&ks'0&t&d1&d2&s&s'&H).
  destruct H.
  induction ks;simpl;auto;tryfalse.
  exists f le (ks ## kint c' ke' lenv ks') t d1 d2.
  exists s s'.
  unfold callcont in H.
  simpl in H.
  inversion H;subst f0 s0 ks'0.
  split;auto.
  right.
  right.
  intro X.
  destruct H.
  induction ks;simpl;auto;tryfalse.
Qed.

Lemma int_nabt_lift
: forall (pc po pi : progunit) (ip : intunit) 
         (c : cureval) (ke : exprcont) (ks : stmtcont) 
         (o : taskst) (cst : clientst) (tid : tid) 
         (ks' : stmtcont) (cx : cureval) (kex : exprcont) 
         (lenv : env),
    no_call_api (c, (ke, ks)) po ->
    InOS (c, (ke, ks ## kint cx kex lenv kstop)) (pumerge po pi) ->
    ~ loststepabt pi (c, (ke, ks)) o ->
    ~
      ltstepabt (pc, (po, pi, ip)) tid (c, (ke, ks ## kint cx kex lenv ks'))
      cst o.
Proof.
  introv Hnoos.
  intros.
  intro X.
  destruct H0.
  inversion X.
  unfold loststepabt.
  intro X'.
  destruct H1.
  inversion H0;subst.
  mytac.
  left.
  destruct x as (c'&(ke'&ks'')).
  exists (c',(ke',ks''##kint cx kex lenv ks')) x0 cst.
  eapply inapi_step;eauto.
  eapply loststep_cont_locality;eauto.
  eapply loststep_no_api_local;eauto.
  eapply inos_int';eauto.
Qed.

Lemma isiret_nabt
: forall (pc po pi : progunit) (ip : intunit) 
         (t : tid) (c' : cureval) (ke' : exprcont) 
         (ks' : stmtcont) (c : cureval) (ke : exprcont) 
         (lenv : env) (ks : stmtcont) (cst : clientst) 
         (Ge Ee : env) (M M' : mem) (ir : isr) (ls : localst) 
         (O : osabst) (i : hid) (isrreg : isr) (si : is) 
         (I : Inv) (ab : absop) (G : env) lasrt t lg,
    IsIRet (c', (ke', ks')) ->
    (Ge, Ee, M', ir, ls, O, ab) |= iretasrt i isrreg si I G lasrt t lg->
    ~
      ltstepabt (pc, (po, pi, ip)) t (c', (ke', ks' ## kint c ke lenv ks))
      cst (Ge, Ee, M, ir, ls).
Proof.
    intros.
  unfold iretasrt in H0.
  intro X.
  inversion X.
  subst.
  inversion H1;subst pc0 po0 pi0 ip0.
  destruct H2.
  left.
  unfold IsIRet in H.
  destruct H as (ks0&Ha&Ha1&Ha2).
  inversion Ha;subst c' ke' ks0.
  assert (intcont ( ks' ## kint c ke lenv ks) = Some (kint c ke lenv ks)).
  eapply intcont_local;eauto.
  destruct ls as ((ie&is)&cs).
  exists (c,(ke,ks)) ((Ge, lenv, M, ir, (true, si, cs))) cst.
  lets H100 : H0.
  unfold sat in H100; fold sat in H100; simpl in H100; mytac.
  eapply inapi_step;eauto.
  eapply exint_step;eauto.
  unfold InOS.
  exists (curs (sprim exint)) kenil (ks'##kint c ke lenv ks).
  splits;auto.
  right.
  right.
  rewrite H.
  auto.
Qed.

Lemma no_os_goodks : forall p ks, no_os p ks -> goodks p ks.
Proof.
  intros.
  destruct p as (pc&((po&pi)&ip)).
  induction ks;subst;tryfalse;auto.
  unfold no_os in H.
  unfold goodks.
  destruct (pumerge po pi f);tryfalse;auto.
Qed.

Lemma no_os_goodks': forall pc po pi ip ks, no_os (pc,(po,pi,ip)) ks -> goodks (pc,(po,pi,ip)) ks.
Proof.
  intros.
  induction ks;auto;tryfalse.
  unfold goodks.
  unfold no_os in H.
  destruct (pumerge po pi f).
  inversion H.
  unfold no_os.
  apply H.
Qed.


Lemma goodks_int_inos: forall pc po pi ip c ke lenv ks ks' ks'' f s le', goodks (pc, (po, pi, ip)) (ks' ## kint c ke lenv ks) -> callcont (ks' ## kint c ke lenv ks) =
                                                                                                                                 Some (kcall f s le' ks'' ## kint c ke lenv ks)  -> ((exists f0 le0 ks'0 t0 d1 d2 s0 s',
                                                                                                                                                                                        callcont (ks' ## kint c ke lenv ks) = Some (kcall f0 s0 le0 ks'0) /\
                                                                                                                                                                                        pumerge po pi f0 = Some (t0, d1, d2, s')) \/
                                                                                                                                                                                     intcont (ks' ## kint c ke lenv ks) <> None) -> (
                                                                           (exists f0 le0 ks'0 t0 d1 d2 s0 s',
                                                                              callcont (ks'' ## kint c ke lenv ks) = Some (kcall f0 s0 le0 ks'0) /\
                                                                              pumerge po pi f0 = Some (t0, d1, d2, s')) \/
                                                                           intcont (ks'' ## kint c ke lenv ks) <> None).
Proof.
  induction ks';simpl;intros;auto;tryfalse;try solve [eapply IHks';eauto].
  inversion H0.
  subst f0 s0 le'.
  apply addcont_same_remove in H6.
  subst ks''.
  destruct (pumerge po pi f).
  clear - H.
  induction ks';simpl;auto;subst;tryfalse.
  simpl in H.
  left.
  exists f.
  destruct (pumerge po pi f).
  destruct f0.
  destruct p.
  destruct p.
  do 8 eexists;split;eauto.
  assert (~no_os (pc, (po, pi, ip)) (ks' ## kint c ke lenv ks)).
  clear.
  induction ks';simpl;auto.
  destruct (pumerge po pi f);auto.
  destruct H0;auto.
  apply no_os_goodks in H.
  clear -H.
  induction ks';simpl;auto;subst;tryfalse.
  simpl in H.
  left.
  exists f.
  destruct (pumerge po pi f).
  destruct f0.
  destruct p.
  destruct p.
  do 8 eexists;split;eauto.
  assert (~no_os (pc, (po, pi, ip)) (ks' ## kint c ke lenv ks)).
  clear.
  induction ks';simpl;auto.
  destruct (pumerge po pi f);auto.
  destruct H0;auto.
Qed.

Lemma callcont_int:forall ks' c ke lenv ks le' ks'1 f s, callcont (ks' ## kint c ke lenv ks) = Some (kcall f s le' ks'1) -> exists ks'',callcont (ks') = Some  (kcall f s le' ks'').
Proof.
  intros.
  induction ks';tryfalse;auto.
  simpl in H.
  inversion H.
  subst ks'1;subst.
  exists ks'.
  simpl.
  auto.
Qed.
Lemma callcont_int_nonone:
  forall (ks' : stmtcont) (c : cureval) (ke : exprcont) 
         (lenv : env) (ks : stmtcont) ,
    callcont (ks' ## kint c ke lenv ks) <> None ->
    callcont ks' <> None.
Proof.
  intros.
  induction ks';simpl in H;auto;tryfalse.
Qed.
Lemma callcont_int_local: forall ks' c ke lenv ks f s le' ks'',callcont (ks' ## kint c ke lenv ks) =
                                                               Some (kcall f s le' ks'' ## kint c ke lenv ks) -> callcont ks' = Some (kcall f s le' ks'').
Proof.
  intros.
  induction ks';simpl;auto;tryfalse.
  simpl in H.
  inversion H.
  apply addcont_same_remove in H4.
  subst;auto.
Qed.

Lemma callsome_intnone:forall ks' c ke lenv ks , callcont ks'<>None ->  intcont (ks' ## kint c ke lenv ks) = None.
Proof.
  intros.
  induction ks';simpl;auto;tryfalse.
  simpl in H.
  tryfalse.
  simpl in H.
  tryfalse.
Qed.
Lemma intcont_dec:forall ks, intcont ks <> None -> (exists c ke lenv ks', intcont ks = Some (kint c ke lenv ks')).
Proof.
  intros.
  induction ks;simpl in H;eauto;tryfalse.
  exists c e e0 ks.
  simpl.
  auto.
Qed.

Lemma ks_add_int_false: forall ks ks' c ke le, ks<> ks' ## kint c ke le ks.
Proof.
  intros.
  intro.
  assert (len_stmtcont ks = len_stmtcont (ks' ## kint c ke le ks)).
  apply contLib.stmtcont_eq_length.
  auto.
  clear H.
  rewrite contLib.length_addcont in H0.
  simpl in H0.
  omega.
Qed.

Lemma goodks_int_inos': forall ks' c ke lenv ks pc po pi ip c' ke',goodks (pc, (po, pi, ip)) (ks' ## kint c ke lenv ks) -> InOS (c', (ke', ks' ## kint c ke lenv ks)) (pumerge po pi).
Proof.
  intros.
  unfold InOS.
  do 3 eexists;split;eauto.
  right.
  induction ks';simpl;auto;subst;tryfalse.
  simpl in H.
  left.
  exists f.
  destruct (pumerge po pi f).
  destruct f0.
  destruct p.
  destruct p.
  do 8 eexists;split;eauto.
  assert (~no_os (pc, (po, pi, ip)) (ks' ## kint c ke lenv ks)).
  clear.
  induction ks';simpl;auto.
  destruct (pumerge po pi f);auto.
  destruct H0;auto.
Qed.

Lemma goodks_int_int_inos: 
  forall pc po pi ip c ke lenv ks ks' x2 c0 ke0 le', 
    goodks (pc, (po, pi, ip)) (ks' ## kint c ke lenv ks) -> 
    InOS (curs (sprim exint), (kenil, ks' ## kint c ke lenv ks))
         (pumerge po pi) -> 
    intcont (ks' ## kint c ke lenv ks) =
    Some (kint c0 ke0 le' x2 ## kint c ke lenv ks) ->
    InOS (c0, (ke0, x2 ## kint c ke lenv ks)) (pumerge po pi).
Proof.
  induction ks';simpl;intros;auto;tryfalse;simpl in H1; try solve [eapply IHks';eauto;
                                                                   unfold InOS in *;
                                                                   do 4 destruct H0;
                                                                   inversion H0;subst;
                                                                   do 3 eexists;split;eauto].
  inversion H1.
  destruct (ks_add_int_false ks x2 c0 ke0 le');auto.
  inversion H1.
  subst.
  apply addcont_same_remove in H6.
  subst x2.
  eapply goodks_int_inos';eauto.
Qed.
Lemma ltstep_no_exint
: forall (c' : cureval) (ke' : exprcont) (ks' : stmtcont) 
         (c : cureval) (ke : exprcont) (lenv : env) 
         (ks : stmtcont) (pc po pi : progunit) (ip : intunit)
         (cst cst' : clientst) (Cl' : code) (o2 o'' : taskst) 
         (t : tid),
    InOS (c', (ke', ks' ## kint c ke lenv ks)) (pumerge po pi) ->
    ltstep (pc, (po, pi, ip)) t (c', (ke', ks' ## kint c ke lenv ks)) cst
           o2 Cl' cst' o'' ->
    ~
      ((c', (ke', ks')) = (curs (sprim exint), (kenil, ks')) /\
       callcont ks' = None /\ intcont ks' = None) ->
    goodks (pc, (po, pi, ip)) (ks' ## kint c ke lenv ks) ->
    exists c'' ke'' ks'',
      Cl' = (c'', (ke'', ks'' ## kint c ke lenv ks)) /\
      InOS (c'', (ke'', ks'' ## kint c ke lenv ks)) (pumerge po pi) /\
      cst' = cst /\
      loststep (pumerge po pi) (c', (ke', ks')) o2 (c'', (ke'', ks'')) o''.
Proof.
   intros.     
  inversion H0;subst;tryfalse.
  inversion H3;subst pc0 po0 pi0 ip0.
  inversion H4;subst;tryfalse.
  inversion H6;subst;tryfalse.
  inversion H7;subst c0 ke0 ks0.
  exists c'0 ke'0 ks'.
  splits;auto.
  unfold InOS.
  exists c'0 ke'0 (ks'##kint c ke lenv ks).
  splits;auto.
  unfold InOS in H5.
  destruct H5 as (c0&ke0&ks0&Ha1&Ha2).
  inversion Ha1;subst c0 ke0 ks0.
  destruct Ha2.
  destruct H5 as (f&vl&fc&tl&Ha&Haa).
  inversion H8;tryfalse.
  destruct H5.
  right.
  left;auto.
  right. right.
  auto.
  apply ostc_step.
  eapply expr_step;eauto.
  inversion H8;subst;tryfalse.
  inversion H7.
  subst c' ke' ks0.
  exists (cure e2) kenil (kassignr e1 t1 ks').
  splits;auto.
  unfold InOS.
  exists (cure e2) kenil (kassignr e1 t1 ks' ## kint c ke lenv ks).
  splits;auto.
  unfold InOS in H5.
  destruct H5 as (c0&ke0&ks0&Ha1&Ha2).
  inversion Ha1;subst c0 ke0 ks0.
  destruct Ha2.
  do 5 destruct H5.
  tryfalse.
  destruct H5.
  right.
  left.
  do 8 destruct H5.
  exists x x0 x1 x2 x3 x4.
  exists x5 x6.
  destruct H5.
  splits;auto.
  right.
  right.
  auto.
  apply ostc_step.
  eapply stmt_step;eauto.
  eapply sassign_step;eauto.
(*-----------------------------------*)
  inversion H7.
  subst c' ke'.
  assert (exists ksx, ks'= kassignr e t0 ksx).
  destruct ks';tryfalse.
  inversion H12.
  subst.
  exists ks';auto. 
  destruct H9.
  subst ks'.
  exists (cure (eaddrof e)) kenil (kassignl v t0 x).
  splits.
  destruct x;unfold AddKsToTail in H12;inversion H12;subst;simpl;auto.
  unfold InOS.
  exists (cure (eaddrof e)) kenil (kassignl v t0 x ## kint c ke lenv ks).
  splits;auto.
  unfold InOS in H5.
  destruct H5 as (c0&ke0&ks0&Ha1&Ha2).
  inversion Ha1;subst c0 ke0 ks0.
  destruct Ha2.
  do 5 destruct H5.
  tryfalse.
  destruct H5.
  right.
  left.
  do 8 destruct H5.
  exists x0 x1 x2 x3 x4 x5.
  exists x6 x7.
  destruct H5.
  splits;auto.
  right.
  right.
  auto.
  auto.
  apply ostc_step.
  eapply stmt_step;eauto.
  eapply sassignrv_step;eauto.
  (*-----------------------------------*)
  inversion H7.
  subst c' ke'.
  assert (exists ksx, ks'= kassignl v t0 ksx).
  destruct ks';tryfalse.
  inversion H13.
  subst.
  exists ks';auto. 
  destruct H9.
  subst ks'.
  exists SKIP kenil x.
  splits.
  destruct x;unfold AddKsToTail in H13;inversion H13;subst;simpl;auto.
  unfold InOS.
  exists SKIP kenil (x ## kint c ke lenv ks).
  splits;auto.
  unfold InOS in H5.
  destruct H5 as (c0&ke0&ks0&Ha1&Ha2).
  inversion Ha1;subst c0 ke0 ks0.
  destruct Ha2.
  do 5 destruct H5.
  tryfalse.
  destruct H5.
  right.
  left.
  do 8 destruct H5.
  exists x0 x1 x2 x3 x4 x5.
  exists x6 x7.
  destruct H5.
  splits;auto.
  right.
  right.
  auto.
  auto.
  apply ostc_step.
  eapply stmt_step;eauto.
  eapply sassignend_step;eauto.
(*-----------------------------------*)
  inversion H7.
  subst c' ke' ks0.
  exists (curs (scall f el)) kenil (kassignr e t0 ks').
  splits;auto.
  unfold InOS.
  exists (curs (scall f el)) kenil ( kassignr e t0 ks'## kint c ke lenv ks).
  splits;auto.
  unfold InOS in H5.
  destruct H5 as (c0&ke0&ks0&Ha1&Ha2).
  inversion Ha1;subst c0 ke0 ks0.
  destruct Ha2.
  do 5 destruct H5.
  tryfalse.
  destruct H5.
  right.
  left.
  do 8 destruct H5.
  exists x x0 x1 x2 x3 x4.
  exists x5 x6.
  destruct H5.
  splits;auto.
  right.
  right.
  auto.
  auto.
  apply ostc_step.
  eapply stmt_step;eauto.
  eapply scalle_step;eauto.
(*-----------------------------------*)
  inversion H7.
  subst c' ke' ks0.
  exists (cure e) kenil (kfuneval f nil (t0 :: nil) el ks').
  splits;auto.
  unfold InOS.
  exists (cure e) kenil (kfuneval f nil (t0 :: nil) el ks'## kint c ke lenv ks).
  splits;auto.
  unfold InOS in H5.
  destruct H5 as (c0&ke0&ks0&Ha1&Ha2).
  inversion Ha1;subst c0 ke0 ks0.
  destruct Ha2.
  do 5 destruct H5.
  tryfalse.
  destruct H5.
  right.
  left.
  do 8 destruct H5.
  exists x x0 x1 x2 x3 x4.
  exists x5 x6.
  destruct H5.
  splits;auto.
  right.
  right.
  auto.
  auto.
  apply ostc_step.
  eapply stmt_step;eauto.
  eapply spcall_step;eauto.
  (*-----------------------------------*)
  inversion H7.
  subst c' ke' ks'0.
  exists (curs (sfexec f nil nil)) kenil (ks').
  splits;auto.
  unfold InOS.
  exists (curs (sfexec f nil nil)) kenil (ks'## kint c ke lenv ks).
  splits;auto.
  unfold InOS in H5.
  destruct H5 as (c0&ke0&ks0&Ha1&Ha2).
  inversion Ha1;subst c0 ke0 ks0.
  destruct Ha2.
  do 5 destruct H5.
  tryfalse.
  destruct H5.
  right.
  left.
  do 8 destruct H5.
  exists x x0 x1 x2 x3 x4.
  exists x5 x6.
  destruct H5.
  splits;auto.
  right.
  right.
  auto.
  auto.
  apply ostc_step.
  eapply stmt_step;eauto.
  eapply snpcall_step;eauto.
(*-----------------------------------*)
  inversion H7.
  subst c' ke'.
  assert (exists ksx, ks'= kfuneval f vl tl (e::el) ksx).
  destruct ks';tryfalse.
  inversion H13.
  subst.
  exists ks';auto. 
  destruct H10.
  subst ks'.
  exists (cure e) kenil (kfuneval f (v :: vl) (t0 :: tl) el x).
  splits.
  destruct x;unfold AddKsToTail in H13;inversion H13;subst;simpl;auto.
  unfold InOS.
  exists (cure e) kenil (kfuneval f (v :: vl) (t0 :: tl) el x ## kint c ke lenv ks).
  splits;auto.
  unfold InOS in H5.
  destruct H5 as (c0&ke0&ks0&Ha1&Ha2).
  inversion Ha1;subst c0 ke0 ks0.
  destruct Ha2.
  do 5 destruct H5.
  tryfalse.
  destruct H5.
  right.
  left.
  do 8 destruct H5.
  exists x0 x1 x2 x3 x4 x5.
  exists x6 x7.
  destruct H5.
  splits;auto.
  right.
  right.
  auto.
  auto.
  apply ostc_step.
  eapply stmt_step;eauto.
  eapply svfeval_step;eauto.
  (*-------------------------------------------------------*)
  inversion H7.
  subst c' ke'.
  assert (exists ksx, ks'= kfuneval f vl tl nil ksx).
  destruct ks';tryfalse.
  inversion H12.
  subst.
  exists ks';auto. 
  destruct H9.
  subst ks'.
  exists (curs (sfexec f (v :: vl) tl)) kenil x.
  splits.
  destruct x;unfold AddKsToTail in H12;inversion H12;subst;simpl;auto.
  unfold InOS.
  exists (curs (sfexec f (v :: vl) tl)) kenil ( x ## kint c ke lenv ks).
  splits;auto.
  unfold InOS in H5.
  destruct H5 as (c0&ke0&ks0&Ha1&Ha2).
  inversion Ha1;subst c0 ke0 ks0.
  destruct Ha2.
  do 5 destruct H5.
  tryfalse.
  destruct H5.
  right.
  left.
  do 8 destruct H5.
  exists x0 x1 x2 x3 x4 x5.
  exists x6 x7.
  destruct H5.
  splits;auto.
  right.
  right.
  auto.
  auto.
  apply ostc_step.
  eapply stmt_step;eauto.
  eapply svfevalnil_step;eauto.
  (*-----------------------------------*)
  inversion H7.
  subst c' ke' ks0.
  exists (curs (salloc vl (revlcons d1 d2))) kenil (kcall f s le ks').
  splits;auto.
  unfold InOS.
  exists (curs (salloc vl (revlcons d1 d2))) kenil (kcall f s le ks' ## kint c ke lenv ks).
  splits;auto.
  right.
  left.
  exists f le (ks'##kint c ke lenv ks) t0 d1 d2. 
  exists s s.
  splits;auto.
  apply ostc_step.
  eapply stmt_step;eauto.
  eapply sfexec_step;eauto.
(*-----------------------------------*)
  inversion H7.
  subst c' ke' ks'0.

  exists (curs (salloc vl dl)) kenil ks'.
  splits;auto.
  unfold InOS.
  exists (curs (salloc vl dl)) kenil (ks'##kint c ke lenv ks).
  splits;auto.
  unfold InOS in H5.
  destruct H5 as (c0&ke0&ks0&Ha1&Ha2).
  inversion Ha1;subst c0 ke0 ks0.
  destruct Ha2.
  do 5 destruct H5.
  tryfalse.
  destruct H5.
  right.
  left.
  do 8 destruct H5.
  exists x0 x1 x2 x3 x4 x5.
  exists x6 x7.
  destruct H5.
  splits;auto.
  right.
  right.
  auto.
  auto.
  apply ostc_step.
  eapply stmt_step;eauto.
  eapply sallocp_step;eauto.
(*-----------------------------------*)
  inversion H7.
  subst c' ke' ks'0.
  exists (curs (salloc nil dl)) kenil ks'.
  splits;auto.
  unfold InOS.
  exists (curs (salloc nil dl)) kenil (ks'##kint c ke lenv ks).
  splits;auto.
  unfold InOS in H5.
  destruct H5 as (c0&ke0&ks0&Ha1&Ha2).
  inversion Ha1;subst c0 ke0 ks0.
  destruct Ha2.
  do 5 destruct H5.
  tryfalse.
  destruct H5.
  right.
  left.
  do 8 destruct H5.
  exists x0 x1 x2 x3 x4 x5.
  exists x6 x7.
  destruct H5.
  splits;auto.
  right.
  right.
  auto.
  auto.
  apply ostc_step.
  eapply stmt_step;eauto.
  eapply salloclv_step;eauto.
(*-----------------------------------*)
  inversion H7.
  subst c' ke'.
  assert (exists ksx, ks'= kcall f s E ksx).
  destruct ks';tryfalse.
  inversion H12.
  subst.
  exists ks';auto. 
  destruct H9.
  subst ks'.
  exists (curs s) kenil (kcall f s E x).
  splits;auto.
  unfold InOS.
  exists (curs s) kenil (kcall f s E x##kint c ke lenv ks).
  splits;auto.
  unfold InOS in H5.
  destruct H5 as (c0&ke0&ks0&Ha1&Ha2).
  inversion Ha1;subst c0 ke0 ks0.
  destruct Ha2.
  do 5 destruct H5.
  tryfalse.
  destruct H5.
  right.
  left.
  do 8 destruct H5.
  exists x0 x1 x2 x3 x4 x5.
  exists x6 x7.
  destruct H5.
  splits;auto.
  right.
  right.
  auto.
  auto.
  apply ostc_step.
  eapply stmt_step;eauto.
  eapply sallocend_step;eauto.
  (*-----------------------------------*)
  inversion H7.
  subst c' ke' ks'0.
  exists (curs (sfree (getaddr le) None)) kenil ks'.
  splits;auto.
  unfold InOS.
  exists (curs (sfree (getaddr le) None)) kenil  (ks' ## kint c ke lenv ks).
  splits;auto.
  unfold InOS in H5.
  destruct H5 as (c0&ke0&ks0&Ha1&Ha2).
  inversion Ha1;subst c0 ke0 ks0.
  destruct Ha2.
  do 5 destruct H5.
  tryfalse.
  destruct H5.
  do 8 destruct H5.
  right.
  left.
  exists x x0 x1 x2 x3 x4.
  exists x5 x6. 
  destruct H5.
  splits;auto.
  right.
  right.
  auto.
  auto.
  apply ostc_step.
  eapply stmt_step;eauto.


  apply callcont_int in H10.
  destruct H10.
  eapply sret_step with (f:=f) (s:=s) (le':=le') (ks':= x);eauto.
(*-----------------------------------*)
  inversion H7.
  subst c' ke' ks0.
  exists (cure e) kenil (kret ks').
  splits;auto.
  unfold InOS.
  exists (cure e) kenil  (kret  ks' ## kint c ke lenv ks).
  splits;auto.
  unfold InOS in H5.
  destruct H5 as (c0&ke0&ks0&Ha1&Ha2).
  inversion Ha1;subst c0 ke0 ks0.
  destruct Ha2.
  do 5 destruct H5.
  tryfalse.
  destruct H5.
  do 8 destruct H5.
  right.
  left.
  exists x x0 x1 x2 x3 x4.
  exists x5 x6.
  destruct H5.
  splits;auto.
  right.
  right.
  auto.
  auto.
  apply ostc_step.
  eapply stmt_step;eauto.
  eapply srete_step;eauto.
(*-----------------------------------*)
  inversion H7.
  subst c' ke'.
  assert (exists ksx, ks'= kret ksx).
  destruct ks';tryfalse.
  inversion H13.
  subst.
  exists ks';auto. 
  destruct H9.
  subst ks'.
  exists (curs (sfree (getaddr le) (Some v))) kenil x.
  splits;auto.
  destruct x;unfold AddKsToTail in H13;inversion H13;subst;simpl;auto.
  unfold InOS.
  exists (curs (sfree (getaddr le) (Some v))) kenil  (x ## kint c ke lenv ks).
  splits;auto.
  unfold InOS in H5.
  destruct H5 as (c0&ke0&ks0&Ha1&Ha2).
  inversion Ha1;subst c0 ke0 ks0.
  destruct Ha2.
  do 5 destruct H5.
  tryfalse.
  destruct H5.
  do 8 destruct H5.
  right.
  left.
  exists  x0 x1 x2 x3 x4 x5.
  exists x6 x7.
  destruct H5.
  splits;auto.
  right.
  right.
  auto.
  auto.
  apply ostc_step.
  eapply stmt_step;eauto.
  assert (ks'0 = x ## kint c ke lenv ks).
  destruct x;unfold AddKsToTail in H13;inversion H13;subst;simpl;auto.
  subst ks'0.

  apply callcont_int_nonone in H10.
  eapply sretv_step ;eauto.
(*-----------------------------------*)
  inversion H7.
  subst c' ke' ks'0.
  exists (curs (sfree al v)) kenil ks'.
  splits;auto.
  unfold InOS.
  exists (curs (sfree al v)) kenil  (ks' ## kint c ke lenv ks).
  splits;auto.
  unfold InOS in H5.
  destruct H5 as (c0&ke0&ks0&Ha1&Ha2).
  inversion Ha1;subst c0 ke0 ks0.
  destruct Ha2.
  do 5 destruct H5.
  tryfalse.
  destruct H5.
  do 8 destruct H5.
  right.
  left.
  exists  x x0 x1 x2 x3 x4.
  exists x5 x6.
  destruct H5.
  splits;auto.
  right.
  right.
  auto.
  auto.
  apply ostc_step.
  eapply stmt_step;eauto.
  eapply sfree_step ;eauto.
  (*-----------------------------------*)
  inversion H7.
  subst c' ke' ks0.
  lets Hcall:H11.
  apply callcont_int in H11.
  destruct H11 as (ks''&H11).
  apply callcont_some_addcont with (ks1:=kint c ke lenv ks) in H11.
  rewrite H11 in Hcall.
  inversion Hcall;subst ks'0.
  exists (curs (sskip v)) kenil ks''.
  splits;auto.
  unfold InOS.
  exists (curs (sskip v)) kenil (ks''##kint c ke lenv ks).
  splits;auto.
  unfold InOS in H5.
  destruct H5 as (c0&ke0&ks0&Ha&Ha1).
  inversion Ha;subst c0 ke0 ks0.
  destruct Ha1.
  do 5 destruct H5.
  inversion H5.

  right.
  eapply goodks_int_inos;eauto.
  apply ostc_step.
  eapply stmt_step;eauto.
  eapply sfreeend_step with (f:=f) (s:=s) (le':=le');eauto.

  eapply callcont_int_local;eauto.
  (*----------------------------------*)
  inversion H7.
  subst c' ke' ks0.
  exists (curs s1) kenil (kseq s2 ks').
  splits;auto.
  unfold InOS.
  exists (curs s1) kenil  (kseq s2 ks' ## kint c ke lenv ks).
  splits;auto.
  unfold InOS in H5.
  destruct H5 as (c0&ke0&ks0&Ha1&Ha2).
  inversion Ha1;subst c0 ke0 ks0.
  destruct Ha2.
  do 5 destruct H5.
  tryfalse.
  destruct H5.
  do 8 destruct H5.
  right.
  left.
  exists x x0 x1 x2 x3 x4.
  exists x5 x6.
  destruct H5.
  splits;auto.
  right.
  right.
  auto.
  auto.
  apply ostc_step.
  eapply stmt_step;eauto.
  eapply sseq_step;eauto.
  (*----------------------------------*)
  inversion H7.
  subst c' ke'.
  assert (exists ksx, ks'= kseq s ksx).
  destruct ks';tryfalse.
  inversion H12.
  subst.
  exists ks';auto. 
  destruct H9.
  subst ks'.
  exists (curs s) kenil (x).
  splits;auto.
  destruct x;unfold AddKsToTail in H12;inversion H12;subst;simpl;auto.
  unfold InOS.
  exists (curs s) kenil  (x ## kint c ke lenv ks).
  splits;auto.
  unfold InOS in H5.
  destruct H5 as (c0&ke0&ks0&Ha1&Ha2).
  inversion Ha1;subst c0 ke0 ks0.
  destruct Ha2.
  do 5 destruct H5.
  tryfalse.
  destruct H5.
  do 8 destruct H5.
  right.
  left.
  exists x0 x1 x2 x3 x4 x5.
  exists x6 x7.
  destruct H5.
  splits;auto.
  right.
  right.
  auto.
  auto.
  apply ostc_step.
  eapply stmt_step;eauto.
  eapply svseq_step;eauto.
  (*----------------------------------*)
  inversion H7.
  subst c' ke'.
  assert (exists ksx, ks'= kseq s ksx).
  destruct ks';tryfalse.
  inversion H12.
  subst.
  exists ks';auto. 
  destruct H9.
  subst ks'.
  exists (curs s) kenil (x).
  splits;auto.
  destruct x;unfold AddKsToTail in H12;inversion H12;subst;simpl;auto.
  unfold InOS.
  exists (curs s) kenil  (x ## kint c ke lenv ks).
  splits;auto.
  unfold InOS in H5.
  destruct H5 as (c0&ke0&ks0&Ha1&Ha2).
  inversion Ha1;subst c0 ke0 ks0.
  destruct Ha2.
  do 5 destruct H5.
  tryfalse.
  destruct H5.
  do 8 destruct H5.
  right.
  left.
  exists x0 x1 x2 x3 x4 x5.
  exists x6 x7.
  destruct H5.
  splits;auto.
  right.
  right.
  auto.
  auto.
  apply ostc_step.
  eapply stmt_step;eauto.
  eapply sskip_step;eauto.
  (*----------------------------------*)
  inversion H7.
  subst c' ke' ks0.
  exists (cure e) kenil (kif s1 s2 ks').
  splits;auto.
  unfold InOS.
  exists (cure e) kenil  (kif s1 s2 ks' ## kint c ke lenv ks).
  splits;auto.
  unfold InOS in H5.
  destruct H5 as (c0&ke0&ks0&Ha1&Ha2).
  inversion Ha1;subst c0 ke0 ks0.
  destruct Ha2.
  do 5 destruct H5.
  tryfalse.
  destruct H5.
  do 8 destruct H5.
  right.
  left.
  exists x x0 x1 x2 x3 x4.
  exists x5 x6.
  destruct H5.
  splits;auto.
  right.
  right.
  auto.
  auto.
  apply ostc_step.
  eapply stmt_step;eauto.
  eapply sif_step;eauto.
  (*----------------------------------*)
  inversion H7.
  subst c' ke' ks0.
  exists (cure e) kenil (kif s (sskip None) ks').
  splits;auto.
  unfold InOS.
  exists (cure e) kenil  (kif s (sskip None) ks' ## kint c ke lenv ks).
  splits;auto.
  unfold InOS in H5.
  destruct H5 as (c0&ke0&ks0&Ha1&Ha2).
  inversion Ha1;subst c0 ke0 ks0.
  destruct Ha2.
  do 5 destruct H5.
  tryfalse.
  destruct H5.
  do 8 destruct H5.
  right.
  left.
  exists x x0 x1 x2 x3 x4.
  exists x5 x6.
  destruct H5.
  splits;auto.
  right.
  right.
  auto.
  auto.
  apply ostc_step.
  eapply stmt_step;eauto.
  eapply sifthen_step;eauto.
  (*----------------------------------*)
  inversion H7.
  subst c' ke'.
  assert (exists ksx, ks'= kif s1 s2 ksx).
  destruct ks';tryfalse.
  inversion H13.
  subst.
  exists ks';auto. 
  destruct H10.
  subst ks'.
  exists (curs s1) kenil (x).
  splits;auto.
  destruct x;unfold AddKsToTail in H13;inversion H13;subst;simpl;auto.
  unfold InOS.
  exists (curs s1) kenil  (x ## kint c ke lenv ks).
  splits;auto.
  unfold InOS in H5.
  destruct H5 as (c0&ke0&ks0&Ha1&Ha2).
  inversion Ha1;subst c0 ke0 ks0.
  destruct Ha2.
  do 5 destruct H5.
  tryfalse.
  destruct H5.
  do 8 destruct H5.
  right.
  left.
  exists x0 x1 x2 x3 x4 x5.
  exists x6 x7.
  destruct H5.
  splits;auto.
  right.
  right.
  auto.
  auto.
  apply ostc_step.
  eapply stmt_step;eauto.
  eapply svift_step;eauto.
(*----------------------------------*)
  inversion H7.
  subst c' ke'.
  assert (exists ksx, ks'= kif s1 s2 ksx).
  destruct ks';tryfalse.
  inversion H13.
  subst.
  exists ks';auto. 
  destruct H10.
  subst ks'.
  exists (curs s2) kenil (x).
  splits;auto.
  destruct x;unfold AddKsToTail in H13;inversion H13;subst;simpl;auto.
  unfold InOS.
  exists (curs s2) kenil  (x ## kint c ke lenv ks).
  splits;auto.
  unfold InOS in H5.
  destruct H5 as (c0&ke0&ks0&Ha1&Ha2).
  inversion Ha1;subst c0 ke0 ks0.
  destruct Ha2.
  do 5 destruct H5.
  tryfalse.
  destruct H5.
  do 8 destruct H5.
  right.
  left.
  exists x0 x1 x2 x3 x4 x5.
  exists x6 x7.
  destruct H5.
  splits;auto.
  right.
  right.
  auto.
  auto.
  apply ostc_step.
  eapply stmt_step;eauto.
  eapply sviff_step;eauto.
  (*----------------------------------*)
  inversion H7.
  subst c' ke' ks0.
  exists (cure e) kenil (kwhile e s ks').
  splits;auto.
  unfold InOS.
  exists (cure e) kenil  (kwhile e s ks' ## kint c ke lenv ks).
  splits;auto.
  unfold InOS in H5.
  destruct H5 as (c0&ke0&ks0&Ha1&Ha2).
  inversion Ha1;subst c0 ke0 ks0.
  destruct Ha2.
  do 5 destruct H5.
  tryfalse.
  destruct H5.
  do 8 destruct H5.
  right.
  left.
  exists x x0 x1 x2 x3 x4.
  exists x5 x6.
  destruct H5.
  splits;auto.
  right.
  right.
  auto.
  auto.
  apply ostc_step.
  eapply stmt_step;eauto.
  eapply swhile_step;eauto.
  (*----------------------------------*)
  inversion H7.
  subst c' ke'.
  assert (exists ksx, ks'= kwhile e s ksx).
  destruct ks';tryfalse.
  inversion H13.
  subst.
  exists ks';auto. 
  destruct H10.
  subst ks'.
  exists (curs s) kenil (kseq (swhile e s) x).
  splits;auto.
  destruct x;unfold AddKsToTail in H13;inversion H13;subst;simpl;auto.
  unfold InOS.
  exists (curs s) kenil  (kseq (swhile e s) x ## kint c ke lenv ks).
  splits;auto.
  unfold InOS in H5.
  destruct H5 as (c0&ke0&ks0&Ha1&Ha2).
  inversion Ha1;subst c0 ke0 ks0.
  destruct Ha2.
  do 5 destruct H5.
  tryfalse.
  destruct H5.
  do 8 destruct H5.
  right.
  left.
  exists x0 x1 x2 x3 x4 x5.
  exists x6 x7.
  destruct H5.
  splits;auto.
  right.
  right.
  auto.
  auto.
  apply ostc_step.
  eapply stmt_step;eauto.
  eapply svwhilet_step;eauto.
  (*----------------------------------*)
  inversion H7.
  subst c' ke'.
  assert (exists ksx, ks'= kwhile e s ksx).
  destruct ks';tryfalse.
  inversion H13.
  subst.
  exists ks';auto. 
  destruct H10.
  subst ks'.
  exists SKIP kenil (x).
  splits;auto.
  destruct x;unfold AddKsToTail in H13;inversion H13;subst;simpl;auto.
  unfold InOS.
  exists SKIP kenil  (x ## kint c ke lenv ks).
  splits;auto.
  unfold InOS in H5.
  destruct H5 as (c0&ke0&ks0&Ha1&Ha2).
  inversion Ha1;subst c0 ke0 ks0.
  destruct Ha2.
  do 5 destruct H5.
  tryfalse.
  destruct H5.
  do 8 destruct H5.
  right.
  left.
  exists x0 x1 x2 x3 x4 x5.
  exists x6 x7.
  destruct H5.
  splits;auto.
  right.
  right.
  auto.
  auto.
  apply ostc_step.
  eapply stmt_step;eauto.
  eapply svwhilef_step;eauto.
  (*----------------------------------*)
  inversion H6.
  subst c' ke' ks0.
  apply not_and_or  in H1.
  destruct H1;tryfalse.
  apply not_and_or in H1.
  destruct H1.


  apply callsome_intnone with (c:=c) (ke:=ke) (lenv:=lenv) (ks:=ks)in H1.
  rewrite H7 in H1.
  tryfalse.
  apply intcont_dec in H1.
  do 4 destruct H1.
  lets Hf:H1.
  apply intcont_some_addcont with (ks1:=kint c ke lenv ks) in H1.
  rewrite H1 in H7.
  inversion H7.
  subst ks'0.
  subst.
  exists c0 ke0 x2.
  splits;auto.



  eapply goodks_int_int_inos;eauto.
  eapply exint_step;eauto.
  (*-------------------------------------*)
  inversion H6.
  subst c' ke' ks0.
  exists SKIP kenil ks'.
  splits;auto.
  unfold InOS.
  exists SKIP kenil (ks' ## kint c ke lenv ks).
  splits;auto.
  unfold InOS in H5.
  destruct H5 as (c0&ke0&ks0&H5).
  destruct H5.
  inversion H5;subst c0 ke0 ks0.
  destruct H7.
  do 5 destruct H7.
  tryfalse.
  destruct H7.
  right.
  left.
  auto.
  right.
  right.
  auto.
  eapply eoi_step;eauto.
  (*-------------------------------------*)
  inversion H6.
  subst c' ke' ks0.
  exists SKIP kenil ks'.
  splits;auto.
  unfold InOS.
  exists SKIP kenil (ks' ## kint c ke lenv ks).
  splits;auto.
  unfold InOS in H5.
  destruct H5 as (c0&ke0&ks0&H5).
  destruct H5.
  inversion H5;subst c0 ke0 ks0.
  destruct H7.
  do 5 destruct H7.
  tryfalse.
  destruct H7.
  right.
  left.
  auto.
  right.
  right.
  auto.
  eapply cli_step;eauto.
  (*-------------------------------------*)
  inversion H6.
  subst c' ke' ks0.
  exists SKIP kenil ks'.
  splits;auto.
  unfold InOS.
  exists SKIP kenil (ks' ## kint c ke lenv ks).
  splits;auto.
  unfold InOS in H5.
  destruct H5 as (c0&ke0&ks0&H5).
  destruct H5.
  inversion H5;subst c0 ke0 ks0.
  destruct H7.
  do 5 destruct H7.
  tryfalse.
  destruct H7.
  right.
  left.
  auto.
  right.
  right.
  auto.
  eapply sti_step;eauto.
  (*-------------------------------------*)
  inversion H6.
  subst c' ke' ks0.
  exists SKIP kenil ks'.
  splits;auto.
  unfold InOS.
  exists SKIP kenil (ks' ## kint c ke lenv ks).
  splits;auto.
  unfold InOS in H5.
  destruct H5 as (c0&ke0&ks0&H5).
  destruct H5.
  inversion H5;subst c0 ke0 ks0.
  destruct H7.
  do 5 destruct H7.
  tryfalse.
  destruct H7.
  right.
  left.
  auto.
  right.
  right.
  auto.
  eapply encrit_step;eauto.
  (*-------------------------------------*)
  inversion H6.
  subst c' ke' ks0.
  exists SKIP kenil ks'.
  splits;auto.
  unfold InOS.
  exists SKIP kenil (ks' ## kint c ke lenv ks).
  splits;auto.
  unfold InOS in H5.
  destruct H5 as (c0&ke0&ks0&H5).
  destruct H5.
  inversion H5;subst c0 ke0 ks0.
  destruct H7.
  do 5 destruct H7.
  tryfalse.
  destruct H7.
  right.
  left.
  auto.
  right.
  right.
  auto.
  eapply excrit_step;eauto.
  (*-------------------------------------*)
  inversion H6.
  subst c' ke' ks0.
  exists SKIP kenil ks'.
  splits;auto.
  unfold InOS.
  exists SKIP kenil (ks' ## kint c ke lenv ks).
  splits;auto.
  unfold InOS in H5.
  destruct H5 as (c0&ke0&ks0&H5).
  destruct H5.
  inversion H5;subst c0 ke0 ks0.
  destruct H7.
  do 5 destruct H7.
  tryfalse.
  destruct H7.
  right.
  left.
  auto.
  right.
  right.
  auto.
  eapply checkis_step;eauto.
Qed.

Lemma no_call_api_loststep_eq
: forall (C C' : code) (tst tst' : taskst) (po pi : progunit)
         (ip : intunit),
    no_call_api_os po pi ip ->
    no_call_api C po ->
    loststep (pumerge po pi) C tst C' tst' -> loststep pi C tst C' tst'.
Proof.
  introv Hos.
  intros.
  inverts H0; first[eapply checkis_step | constructors];eauto.
  inverts H1.
  eapply expr_step;eauto.
  eapply stmt_step;eauto.
  inverts H2;constructors;eauto.
  instantiate (1:=t).
  simpl in H.
  destruct H.
  unfold pumerge in H3.
  rewrite H in H3.
  destruct (pi f);tryfalse.
  auto.
Qed.

Lemma no_call_api_os_stmt:forall po pi ip f t d1 d2 s, no_call_api_os po pi ip -> pumerge po pi f = Some (t, d1, d2, s) -> no_call_api_stmt s po.
Proof.
  intros.
  unfold pumerge in H0.
  unfolds in H.
  destructs H.
  unfold no_call_api_pu in *.
  remember (po f) as X;destruct X;tryfalse;auto.
  rewrite HeqX in H0.
  apply H in H0;auto.
  remember (pi f) as X;destruct X;tryfalse;auto.
  rewrite HeqX0 in H0.
  apply H1 in H0;auto.
Qed.
Lemma no_call_api_os_callcont:
  forall ks po f s le ks',
    no_call_api_scont ks po -> 
    callcont ks = Some (kcall f s le ks') -> 
    no_call_api_scont ks' po.
Proof.
  induction ks;intros;simpl in *;tryfalse;auto;try solve [destructs H;eapply IHks;eauto].
  inverts H0.
  destructs H;eauto.
  eapply IHks;eauto.
  eapply IHks;eauto.
  eapply IHks;eauto.
Qed.

Lemma no_call_api_os_intcont:
  forall ks po c le ks' ke,
    no_call_api_scont ks po -> 
    intcont ks = Some (kint c ke le ks') -> 
    no_call_api_cureval c po /\
    no_call_api_scont ks' po.
Proof.
  induction ks;intros;simpl in *;tryfalse;auto;try solve [destructs H;eapply IHks;eauto].
  inverts H0.
  destructs H;eauto.
  eapply IHks;eauto.
  eapply IHks;eauto.
  eapply IHks;eauto.
Qed. 

Lemma no_call_api_loststep_still
: forall (C C' : code) (tst tst' : taskst) (po pi : progunit)
         (ip : intunit),
    no_call_api_os po pi ip ->
    no_call_api C po ->
    loststep (pumerge po pi) C tst C' tst' -> no_call_api C' po.
Proof.
     introv Hos.
  intros.
  inverts H0.
  inverts H1.
  inverts H2;auto.
  inverts H2; try solve [
                    simpl in H;simpl;
                    auto ; try solve [mytac;auto]].
  simpl.
  simpl in H;mytac.

  eapply no_call_api_os_stmt;eauto.
  auto.
  auto.
  simpl.
  simpl in H.

  split;auto.
  eapply no_call_api_os_callcont;eauto.
  destruct H;auto.
  simpl in H.
  simpl.
  eapply no_call_api_os_intcont;eauto.
  destruct H;auto.
  mytac;auto.
  mytac;auto.
  mytac;auto.
  mytac;auto.
  mytac;auto.
  mytac;auto.
Qed.   


Lemma goodks_noinos_noos: 
  forall pc po pi ip ks f vl tl,
    goodks (pc, (po, pi, ip)) ks ->
    ~ InOS (curs (sfexec f vl tl), (kenil, ks)) (pumerge po pi) ->
    no_os (pc,(po,pi,ip)) ks.                      
Proof.
  intros.
  unfold InOS in H0.
  apply not_ex_all_not with (n:=curs (sfexec f vl tl)) in H0.
  apply not_ex_all_not with (n:= kenil) in H0.
  apply not_ex_all_not with (n:= ks) in H0.
  apply not_and_or in H0.
  destruct H0;tryfalse.
  apply not_or_and in H0.
  destruct H0.
  apply not_or_and in  H1.
  destruct H1.
  induction ks;simpl;tryfalse;auto.
  apply not_ex_all_not with (n:=f0) in H1.
  apply not_ex_all_not with (n:= e) in H1.
  apply not_ex_all_not with (n:= ks) in H1.
  unfold goodks in H;simpl in H.
  destruct (pumerge po pi f0);tryfalse.
  destruct f1 as (((t&d1)&d2)&s').
  apply not_ex_all_not with (n:=t) in H1.
  apply not_ex_all_not with (n:= d1) in H1.
  apply not_ex_all_not with (n:= d2) in H1.
  apply not_ex_all_not with (n:=s) in H1.
  apply not_ex_all_not with (n:= s') in H1.
  destruct H1.
  split;simpl;auto.
  auto.
Qed.



Lemma goodks_callcont_still: 
  forall pc po pi ip ks f s lenv ks'',
    goodks (pc, (po, pi, ip)) ks ->
    callcont ks = Some (kcall f s lenv ks'')->
    goodks (pc,(po,pi,ip)) ks''.                      
Proof.
  intros.
  induction ks;subst;tryfalse;auto.
  simpl in H0.
  inversion H0;subst.
  unfold goodks in H.
  destruct (pumerge po pi f);tryfalse;simpl;auto.
  apply no_os_goodks;auto.
Qed.

Lemma goodks_intcont_still: 
  forall pc po pi ip ks c ke lenv ks'',
    goodks (pc, (po, pi, ip)) ks ->
    intcont ks = Some (kint c ke lenv ks'')->
    goodks (pc,(po,pi,ip)) ks''.                      
Proof.
  intros.
  induction ks;subst;tryfalse;auto.
  simpl in H0.
  inversion H0;subst.
  unfold goodks in H.
  fold goodks in H;auto.
Qed.

Lemma ltstep_goodks
: forall (p : lprog) (t : tid) (c' : cureval) 
         (ke' : exprcont) (ks' : stmtcont) (c'' : cureval) 
         (ke'' : exprcont) (ks'' : stmtcont) (cst : clientst) 
         (o : taskst) (cst' : clientst) (o' : taskst),
    ltstep p t (c', (ke', ks')) cst o (c'', (ke'', ks'')) cst' o' ->
    goodks p ks' -> goodks p ks''.
Proof.
    intros.
  inversion H;try inversion H5;subst;auto.
  inversion H2;subst.
  inversion H11;subst;auto.
  inversion H12;simpl;auto;tryfalse;subst;inversion H11;subst;auto.
  destruct (pumerge po pi f);auto.
  eapply goodks_noinos_noos;eauto.
  eapply goodks_callcont_still;eauto.
 
  inversion H2;try inversion H9;try inversion H10;subst;auto.
  inversion H1;subst.
  inversion H11;subst;auto.
  inversion H13;simpl;auto;tryfalse;subst;inversion H11;subst;auto.
  destruct (pumerge po pi f);auto.
  tryfalse.
  eapply goodks_callcont_still;eauto.
  eapply goodks_intcont_still;eauto.
  inversion H6;simpl;auto;tryfalse;subst;inversion H11;subst;auto.
Qed.

Lemma lpstep_goodks:
  forall p S S' cst cst' t t' T T',
    lpstep p T cst S t T'
           cst' S' t' -> good_t_ks p T -> good_t_ks p T'.
Proof.
  unfold good_t_ks.
  intros.
  inversion H;subst.
  destruct (tid_eq_dec x t').
  subst x.
  assert (get (set T t' C') t'= Some C').
  apply map_get_set.
  unfolddef.
  rewrite H2 in H1.
  inversion H1 ;subst C'.
  inversion H8.
  subst.
  apply H0 in H3.
  simpl.
  auto.
  assert (get (set T t' C') x =get T x).
  eapply map_get_set';eauto.
  unfolddef.
  rewrite H2 in H1.
  apply H0 in H1.
  auto.
  (*------------------------*)
  destruct (tid_eq_dec t' x).
  subst x.
  assert (get (set T t' C') t'= Some C').
  apply map_get_set.
  unfolddef.
  rewrite H3 in H1.
  inversion H1 ;subst C'.
  destruct C as (c'&(ke'&ks')).
  apply H0 in H2.
  eapply ltstep_goodks;eauto.
  assert (get (set T t' C') x =get T x).
  eapply map_get_set';eauto.
  unfolddef.
  rewrite H3 in H1.
  apply H0 in H1.
  auto.

  (*-----------------------------*)
  destruct (tid_eq_dec t x).
  subst x.
  assert (get (set T t (SKIP , (kenil, ks0))) t = Some (SKIP,(kenil,ks0))).
  apply map_get_set.
  unfolddef.
  rewrite H2 in H1.
  inversion H1.
  subst.
  apply H0 in H6;auto.
  assert (get (set T t (SKIP , (kenil, ks0))) x = get T x).
  eapply map_get_set';eauto.
  unfolddef.
  rewrite H2 in H1.
  apply H0 in H1.
  auto.
  (*-----------------------------*)
  destruct (tid_eq_dec t'0 x).
  subst x.
  rewrite map_get_set in H1.
  unfold nilcont in H1;inverts H1.
  simpl;auto.
  destruct (tid_eq_dec t' x).
  subst x.
  rewrite map_get_set' in H1;auto.
  rewrite map_get_set in H1;auto.
  inverts H1.
  apply H0 in H3.
  auto.
  rewrite map_get_set' in H1;auto.
  rewrite map_get_set' in H1;auto.
  apply H0 in H1;auto.
  (*-----------------------------*)
  destruct (tid_eq_dec t'0 x).
  subst x.
  rewrite map_get_set in H1.
  unfold nilcont in H1;inverts H1.
  simpl;auto.
  destruct (tid_eq_dec t' x).
  subst x.
  rewrite map_get_set' in H1;auto.
  rewrite map_get_set in H1;auto.
  inverts H1.
  apply H0 in H3.
  auto.
  rewrite map_get_set' in H1;auto.
  rewrite map_get_set' in H1;auto.
  apply H0 in H1;auto.
  (*-----------------------------*)
  destruct (tid_eq_dec t' x).
  subst x.
  rewrite map_get_set in H1.
  inverts H1.
  apply H0 in H3;auto.
  rewrite map_get_set' in H1;auto.
  apply H0 in H1;auto.
Qed.

Lemma ltstep_good_is : forall p t C1 C2 cst1 cst2 tst1 tst2 m1 m2 r1 r2 ie1 ie2 is1 is2 cs1 cs2,
                         ltstep p t C1 cst1 tst1 C2 cst2 tst2 ->
                         tst1 = (m1, r1, (ie1, is1, cs1)) ->
                         tst2 = (m2, r2, (ie2, is2, cs2)) ->
                         good_is is1 ->
                         good_is is2.
Proof.
  intros.
  subst.
  inverts H; eauto.
  inverts H1; eauto.
  simpl in H2.
  destruct H2.
  auto.
Qed.


Lemma Steq_projS_tid_neq_is_eq : forall t' t S S' m m' r r' ie ie' is is' cs cs',
                                   t' <> t ->
                                   Steq S S' t ->
                                   projS S t' = Some (m, r, (ie, is, cs)) ->
                                   projS S' t' = Some (m', r', (ie', is', cs')) ->
                                   is = is'.
Proof.
  intros.
  unfolds Steq.
  destruct S. destruct p. destruct S'. destruct p. destruct H0.
  unfold Dteq in H0. destruct c. destruct p. destruct c0. destruct p.
  pose proof H0 t' H. clear H0.
  unfold Piteq in H3.
  pose proof H3 t' H. clear H3.
  simpl in H1. destruct (get c t') eqn : eq1; tryfalse.
  destruct (get l t') eqn : eq2; tryfalse.
  inverts H1.
  simpl in H2.
  symmetry in H4.
  rewrite H4 in H2.
  symmetry in H0.
  rewrite H0 in H2.
  inverts H2.
  auto.
Qed.

  
Lemma lpstep_good_is_S : forall p S cst t S' cst' t' T T', 
                           good_is_S S ->
                           lpstep p T cst S t T' cst' S' t' ->
                           good_is_S S'.
Proof.
  intros.
  unfolds.
  intros.
  destruct tst.
  destruct p0.
  destruct p0.
  destruct p0.
  destruct l.
  destruct p0.
  inv H0.
  destruct (tidspec.beq t0 t') eqn : eq1.
  apply tidspec.beq_true_eq in eq1.
  subst.
  inv H8.
  rewrite H1 in H6.
  inv H6.

  unfolds in H.
  pose proof (H t' (ge, le, m0,  ir, (true, si, nil)) H5). clear H.
  simpl in H0.
  simpl.
  auto.
  apply tidspec.beq_false_neq in eq1.
  assert (exists e m i, projS S t0 = Some (e, e0, m, i, (i0, i1, c))).
  unfolds in H1. destruct S'. destruct p.
  destruct (projD c0 t0) eqn : eq2; tryfalse.
  destruct (get l t0) eqn : eq3; tryfalse.
  unfolds in eq2. destruct c0. destruct p0.
  destruct (get c0 t0) eqn : eq4; tryfalse.
  unfolds in H7. destruct S. destruct p0. destruct H7.
  unfolds in H0. destruct c1. destruct p0. pose proof H0 t0 eq1. clear H0. rewrite eq4 in H4.
  unfolds in H2. pose proof H2 t0 eq1. clear H2. rewrite eq3 in H0.
  destruct l. destruct p. destruct p.
  do 3 eexists.
  unfolds.
  unfold projD.
  rewrite H4. rewrite H0.
  inv H1. inv eq2.
  auto.
  do 3 destruct H0.
  unfolds in H. pose proof H t0 (x, e0, x0, x1, (i0, i1, c)) H0. clear H.
  simpl in H2.
  auto.

  destruct (tidspec.beq t0 t') eqn : eq1.
  apply tidspec.beq_true_eq in eq1.
  subst.

  unfolds in H. pose proof H t' tst H4. clear H.
  destruct tst. destruct p0. destruct s. destruct p0. destruct l. destruct p0.
  rewrite H5 in H1.
  inverts H1.
  eapply ltstep_good_is; eauto.
  assert (Steq S S' t' ) as H100.
  auto.
  apply tidspec.beq_false_neq in eq1.
  assert (projS S' t0 = Some (e, e0, m, i, (i0, i1, c))) as H200.
  auto.
  unfolds in H6. destruct S. destruct p0. destruct S'. destruct p0.
  destruct H6.
  unfolds in H0. destruct c1. destruct p0. destruct c0. destruct p0.
  pose proof H0 t0 eq1. clear H0.
  unfolds in H3.
  pose proof H3 t0 eq1. clear H3.
  simpl in H1.
  destruct (get c1 t0) eqn : eq2; tryfalse.
  destruct (get l0 t0) eqn : eq3; tryfalse.
  inverts H1.
  assert (exists e e0 m i i0 i1 c, projS (e2, c0, m1, i2, l) t0 = Some (e, e0, m, i, (i0, i1, c))).
  unfold projS. unfold projD.
  do 7 eexists.
  rewrite H6.
  rewrite H0.
  auto.
  do 7 destruct H1.
  unfolds in H. pose proof H t0 (x, x0, x1, x2, (x3, x4, x5)) H1. clear H.
  simpl in H3.
  assert (x4 = i1).
  eapply Steq_projS_tid_neq_is_eq; eauto.
  substs.
  auto.
  
  unfolds in H. 
  assert (projS (ge, les, m0, ir, au) t0 = Some (e, e0, m0, i, (i0, i1, c))).
  clear -H1.
  unfold projS in *.
  unfold projD in *.
  destruct (get les t0);tryfalse;auto.
  destruct (get au t0);tryfalse;auto.
  inverts H1.
  auto.
  pose proof H t0 (e, e0, m0, i, (i0, i1, c)) H0. clear H.
  simpl in H2.
  auto.

  clear - H H1.
  destruct S as [[[[]]]].
  unfolds in H.
  unfold Snewt in H1.
  destruct (tidspec.beq t'0 t0) eqn :eq1.
  lets Hx: tidspec.beq_true_eq eq1; substs.
  unfolds in H1.
  unfold Dnewt, Tlnewt in H1.
  simpl in H1.
  do 2 rewrite set_a_get_a in H1.
  inverts H1.
  simpl; auto.
  assert(projS (e1, c0, m0, i2, l) t0 = Some (e, e0, m, i, (i0, i1, c))).
  unfold projS in H1.
  unfolds.
  unfold Dnewt, Tlnewt in H1.
  unfold projD in *.
  lets Hx: tidspec.beq_false_neq eq1.
  do 2 rewrite set_a_get_a' in H1; auto.
  lets Hx: H H0; auto.

  clear - H H1.
  destruct S as [[[[]]]].
  unfolds in H.
  unfold Snewt in H1.
  destruct (tidspec.beq t'0 t0) eqn :eq1.
  lets Hx: tidspec.beq_true_eq eq1; substs.
  unfolds in H1.
  unfold Dnewt, Tlnewt in H1.
  simpl in H1.
  do 2 rewrite set_a_get_a in H1.
  inverts H1.
  simpl; auto.
  assert(projS (e1, c0, m0, i2, l) t0 = Some (e, e0, m, i, (i0, i1, c))).
  unfold projS in H1.
  unfolds.
  unfold Dnewt, Tlnewt in H1.
  unfold projD in *.
  lets Hx: tidspec.beq_false_neq eq1.
  do 2 rewrite set_a_get_a' in H1; auto.
  lets Hx: H H0; auto.

  clear - H H1.
  destruct S' as [[[[]]]].
  unfolds in H.
  lets Hx: H H1; auto.
Qed.

Lemma tasks_set_a_set_a : forall T a val1 val2, TasksMod.set (TasksMod.set T a val1) a val2 = TasksMod.set T a val2.
Proof.
  intros.
  apply TasksMod.extensionality.
  intro.
  destruct (tidspec.beq a a0) eqn:eq1.
  rewrite TasksMod.set_a_get_a.
  rewrite TasksMod.set_a_get_a.
  auto.
  auto.
  auto.
  rewrite TasksMod.set_a_get_a'.
  rewrite TasksMod.set_a_get_a'.
  rewrite TasksMod.set_a_get_a'.
  auto.
  auto.
  auto.
  auto.
Qed.

Lemma tasks_set_set: forall T t c c', TasksMod.set T t c' = TasksMod.set (TasksMod.set T t c) t c'.
Proof.
  intros.
  symmetry.
  apply tasks_set_a_set_a.
Qed.

Lemma spec_step_tidsame:
  forall sd c O c' O',
    spec_step sd c O c' O' -> tidsame O O'.
Proof.
  intros.
  inductions H; unfolds; auto.
  unfold tidsame in H1.
  destruct (get O curtid) eqn : eq1;
    destruct (get O' curtid) eqn : eq2;
    tryfalse.
  inverts H1.
  assert (get OO curtid = Some a0).
  eapply join_get_get_l; eauto.
  assert (get OO' curtid = Some a0).
  eapply join_get_get_l; eauto.
  rewrite H1; rewrite H4; auto.

  pose proof H2 curtid.
  pose proof H3 curtid.
  unfold get in *; simpl in *.
  rewrite eq1 in H4.
  rewrite eq2 in H5.
  destruct (OSAbstMod.get Of curtid);
    destruct (OSAbstMod.get OO curtid);
    destruct (OSAbstMod.get OO' curtid);
    tryfalse; substs; auto.
Qed.

Lemma hapistep_tidsame: forall A  cd cd' O O',hapistep  A cd O cd' O' -> tidsame O O'.
Proof.
  intros.
  inverts H;unfolds;auto.
  eapply spec_step_tidsame;eauto.
Qed.

Lemma  htstep_tidsame: forall p  c cst c' cst' O O' t,htstep p t c cst O c' cst' O' -> tidsame O O'.
Proof.
  intros.
  inverts H.
  unfolds;auto.
  eapply hapistep_tidsame;eauto.
Qed.

Lemma tasks_get_set: forall T t a,  TasksMod.get (TasksMod.set T t a) t = Some a.
Proof.
  intros.
  apply TasksMod.set_a_get_a.
  apply tidspec.eq_beq_true.
  reflexivity.
Qed.


Lemma th_ttop_lift
: forall (Th : TasksMod.map) (C C' : code) (p : hprog) 
         (O O' : osabst) (cst cst' : clientst) 
         (t : addrval),
    get O curtid = Some (oscurt t) ->
    htstepstar p t C cst O C' cst' O' ->
    get Th t = Some C ->
    hpstepstar p Th cst O (TasksMod.set Th t C') cst' O'.
Proof.
  introv Hc.
  intros.
  generalize H0,H.
  generalize Th.
  clear H0.
  clear Th.
  induction H;subst.
  intros.
  assert (TasksMod.set Th t c = Th).
  eapply TasksMod.get_set_same;eauto. 
  rewrite H1.
  eapply hp_stepO.
  intros.
  apply hp_stepS with (T':=TasksMod.set Th t c') (cst':=cst') (O':=O').
  constructors; eauto.
  assert (TasksMod.set Th t c'' =TasksMod.set (TasksMod.set Th t c') t c'').
  apply tasks_set_set.
  rewrite H3.
  apply IHhtstepstar;auto.
  apply htstep_tidsame in H.
  unfold tidsame in H.
  rewrite <-H ;auto.
  apply tasks_get_set.
Qed.
  
Lemma th_no_create_lift:
  forall Th C C' t  p O O' cst cst',
    get O curtid = Some (oscurt t) ->
    htstepstar p t C cst O C' cst' O' ->
    TasksMod.get Th t = Some C ->
    hpstepstar p Th cst O (set Th t C') cst' O'.
Proof.
  intros.
  eapply th_ttop_lift;eauto.
Qed.


Lemma  htstepstar_tidsame:
  forall p c cst c' cst' O O' t,
    htstepstar p t c cst O c' cst' O' -> tidsame O O'.
Proof.
  intros.
  induction H.
  unfolds;auto.
  apply htstep_tidsame in H.
  unfold tidsame in *.
  rewrite H;eauto.
Qed.
  
Lemma ge_n_change
: forall (p : lprog) (T : tasks) (cst : clientst) 
         (S : osstate) (t : tid) (T' : tasks) (cst' : clientst)
         (S' : osstate) (t' : tid),
    lpstep p T cst S t T' cst' S' t' -> gets_g S = gets_g S'.
Proof.
  intros.
  inversion H;subst.

  (* case 1 *)
  destruct S;
  destruct p;
  destruct c;
  destruct p;
  destruct S';
  destruct p;
  destruct c0;
  destruct p;
  simpl;
  unfold projS in *;
  unfold projD in *;
  destruct (get c0 t');tryfalse;
  destruct (get l0 t');tryfalse;
  match goal with [H: Some _ = Some _ |- _] => inversion H; clear H end;
  subst tst';
  unfold projS in *;
  unfold projD in *;
  destruct (get c t');tryfalse;
  destruct (get l t');tryfalse;
   match goal with [H: Some _ = Some _ |- _] => inversion H; clear H end;
   subst tst;tryfalse;
   match goal with [H: lintstep _ _ _ _ _ |- _] => inversion H end;
  subst;auto;tryfalse .


  (* case 2 *)
  destruct S.
  destruct p0.
  destruct c.
  destruct p0.
  destruct S'.
  destruct p0.
  destruct c0.
  destruct p0.
  simpl.
  unfold gets_g; simpl.
  unfold projS in *.
  unfold projD in *.
  destruct (get c0 t');tryfalse.
  destruct (get l0 t');tryfalse.
  match goal with [H: Some _ = Some _ |- _] => inversion H; clear H end.
  subst tst'.
  unfold projS in *.
  unfold projD in *.
  destruct (get c t');tryfalse.
  destruct (get l t');tryfalse.
   match goal with [H: Some _ = Some _ |- _] => inversion H; clear H end.
   subst tst;tryfalse.
   match goal with [H: ltstep _ _ _ _ _ _ _ _|- _] => inversion H end; subst; auto.
   match goal with [H: loststep _ _ _ _ _  |- _] => inversion H end;subst;auto.
   match goal with [H: cstep _ _ _ _ _ |- _] => inversion H end; subst; auto.
   match goal with [H: estep _ _ _ _ _ _ |- _] => inversion H end; subst; auto.
   match goal with [H: sstep _ _ _ _ _ _ _ |- _] => inversion H end; subst; auto;  
   congruence.
   congruence.

   (* case 3 *)
   auto.

   (* case 4 *)
   destruct S as [[[[]]]].
   simpl.
   unfolds; simpl; auto.

   destruct S as [[[[]]]].
   simpl.
   unfolds; simpl; auto.

   destruct S' as [[[[]]]].
   simpl; auto.
Qed.

Lemma eqdomO_refl :
  forall O, eqdomO O O.
Proof.
  intros; unfolds; split; intro.
  split; intros; auto.
  intros.
  exists tls.
  split; auto.
  unfolds; intros; split; intros; auto.
Qed.


Lemma eqdomO_disj_eqdomO:
  forall O O' Of,
    eqdomO O O' ->
    OSAbstMod.disj O Of -> 
    eqdomO (OSAbstMod.merge O Of) (OSAbstMod.merge O' Of).
Proof.
  intros.
  unfold eqdomO in H; destruct H.
  unfolds; split.
  unfold indom in *.
  unfold get in *; simpl in *.
  intro; do 2 rewrite OSAbstMod.merge_sem.
  pose proof H x; destruct H2.
  split; intros; mytac;
  destruct(OSAbstMod.get O x) eqn : eq1;
    destruct(OSAbstMod.get Of x) eqn : eq2;
    destruct(OSAbstMod.get O' x) eqn : eq3;
    tryfalse; inverts H4; eauto.

  intros.
  rewrite OSAbstMod.merge_sem in *.
  unfold indom in *.
  unfold get in *; simpl in *.
  
  destruct(OSAbstMod.get O abstcblsid) eqn : eq1;
    destruct(OSAbstMod.get Of abstcblsid) eqn : eq2;
    destruct(OSAbstMod.get O' abstcblsid) eqn : eq3;
    tryfalse; inverts H2; try (eapply H1; eauto).
  assert(Some (abstcblist tls) = Some (abstcblist tls)); auto.
  apply H1 in H2; mytac; tryfalse.
  pose proof H abstcblsid; unfold OSAbstMod.indom in H2; destruct H2.
  assert(exists b, OSAbstMod.get O' abstcblsid = Some b) by eauto.
  apply H3 in H4; mytac.
  rewrite eq1 in H4; tryfalse.
  exists tls.
  split; auto.
  unfolds; intro; split; intros; auto.
Qed.


Lemma spec_step_eqdomo:
  forall sd O O' c c',
    spec_step sd c O c' O' -> eqdomO O O'.
Proof.
  intros.
  inductions H.
  eapply join_eqdom_eqdom; eauto.

  unfolds;split;[intros;split;auto|intros;eexists;split;eauto].
  unfolds.
  intros;split;auto.
  auto.
  unfolds;split;[intros;split;auto|intros;eexists;split;eauto].
  unfolds.
  intros;split;auto.
  unfolds;split;[intros;split;auto|intros;eexists;split;eauto].
  unfolds.
  intros;split;auto.
  apply eqdomO_refl.
  apply eqdomO_refl.
Qed.


Lemma hapistep_eqdomO :
  forall A C C' O O',
    hapistep A C O C' O' -> eqdomO O O'.
Proof.
  intros.
  inversion H; substs;
  try(apply eqdomO_refl).
  eapply spec_step_eqdomo; eauto.
Qed.


Lemma htstep_eqdomO :
  forall p t C C' cst cst' O O',
    htstep p t C cst O C' cst' O' -> eqdomO O O'.
Proof.
  intros.
  inversion H; substs.
  apply eqdomO_refl.      
  eapply hapistep_eqdomO; eauto.
Qed.

Lemma eqdomO_eqdomTO :
  forall O O' T,
    eqdomO O O' -> eqdomTO T O -> eqdomTO T O'.
Proof.
  intros.
  unfold eqdomO in H; unfold eqdomTO in *; unfold TcbMod.indom in *.
  mytac.
  eapply H2 in H0; mytac.
  exists x0; split; auto.
  intros.
  pose proof H1 t; clear H1; destruct H4.
  clear H2.
  unfold eqdomtls in H3; pose proof H3 t.
  unfold TcbMod.indom in H2; destruct H2.
  unfold indom in H4.
  assert(exists v, get x0 t = Some v) by eauto.
  eapply H4 in H6.
  eapply H5 in H6; eauto.
Qed.


Lemma eqdomTO_setT :
  forall T T' t C C' O,
    TasksMod.get T t = Some C -> eqdomTO T O ->
    TasksMod.set T t C' = T' ->
    eqdomTO T' O.
Proof.
  intros.
  unfold eqdomTO in *.
  mytac.
  eexists; split; eauto.
  intros.
  pose proof H2 t0; destruct H1.
  destruct(tidspec.beq t t0) eqn : eq1.
  lets Hx: tidspec.beq_true_eq eq1; substs.
  unfold get in *; simpl in *.
  rewrite TasksMod.set_a_get_a; eauto.
  rewrite TasksMod.set_a_get_a'; auto.
  eapply H3; eauto.
Qed.

Lemma htistep_eqdomO :
  forall ispec C C' O O',
    htistep ispec C O C' O' -> eqdomO O O'.
Proof.
  intros.
  inversion H; substs.
  apply eqdomO_refl.
Qed.

Lemma eqdomO_set2 :
  forall O t x x',
    OSAbstMod.get O t = Some x ->
    t <> abtcblsid ->
    eqdomO O (OSAbstMod.set O t x').
Proof.
  intros.
  unfold eqdomO; unfold indom; unfold get; simpl; split.
  intros.
  destruct (absdataidspec.beq t x0) eqn : eq1.
  pose proof absdataidspec.beq_true_eq eq1; substs.
  split; intros.
  rewrite OSAbstMod.set_a_get_a; eauto.
  eauto.

  split; intros.
  rewrite OSAbstMod.set_a_get_a'; auto.
  rewrite OSAbstMod.set_a_get_a' in H1; auto.

  intros.
  rewrite OSAbstMod.set_a_get_a'.
  eexists; split; eauto.
  unfolds; intros; split; intros; auto.
  apply absdataidspec.neq_beq_false; eauto.
Qed.

Lemma hpstep_eqdomO :
  forall p T T' cst cst' O O',
    eqdomTO T O ->
    hpstep p T cst O T' cst' O' ->
    eqdomTO T' O'.
Proof.  
  intros.
  inversion H0; substs.
  assert(eqdomO O O').
  eapply htstep_eqdomO; eauto.

  intros.
  eapply eqdomO_eqdomTO; eauto.
  eapply eqdomTO_setT; eauto.

  assert(eqdomO O O').
  eapply htistep_eqdomO; eauto.
  
  eapply eqdomO_eqdomTO; eauto.
  eapply eqdomTO_setT; eauto.

  eapply eqdomTO_setT; eauto.
  eapply eqdomO_eqdomTO; eauto.
  eapply eqdomO_set2; eauto.

  unfold eqdomTO.
  rewrite set_a_get_a.
  eexists; splits; eauto.
  intros.
  destruct (tidspec.beq t' t0) eqn : eq1.
  lets Hx: tidspec.beq_true_eq eq1; substs.
  rewrite set_a_get_a; eauto.
  lets Hx: tidspec.beq_false_neq eq1.
  rewrite set_a_get_a'; eauto.
  destruct (tidspec.beq t t0) eqn : eq2.
  lets Hx1: tidspec.beq_true_eq eq2; substs.
  rewrite set_a_get_a; eauto.
  lets Hx1: tidspec.beq_false_neq eq2.
  rewrite set_a_get_a'; eauto.
  unfolds in H; simpljoin.
  rewrite H in H10; inverts H10.
  eapply H3.
  exists x.
  clear - H12 eq1 H2.
  unfold join in *; simpl in *.
  pose proof H12 t0.
  unfold get in *; simpl in *.
  rewrite H2 in H.
  rewrite TcbMod.get_sig_none in H.
  destruct (TcbMod.get tls t0); tryfalse; substs; auto.
  apply tidspec.beq_false_neq; auto.

  unfold eqdomTO.
  rewrite set_a_get_a.
  eexists; splits; eauto.
  intros.
  destruct (tidspec.beq t' t0) eqn : eq1.
  lets Hx: tidspec.beq_true_eq eq1; substs.
  rewrite set_a_get_a; eauto.
  lets Hx: tidspec.beq_false_neq eq1.
  rewrite set_a_get_a'; eauto.
  destruct (tidspec.beq t t0) eqn : eq2.
  lets Hx1: tidspec.beq_true_eq eq2; substs.
  rewrite set_a_get_a; eauto.
  lets Hx1: tidspec.beq_false_neq eq2.
  rewrite set_a_get_a'; eauto.
  unfolds in H; simpljoin.
  rewrite H in H8; inverts H8.
  eapply H3.
  exists x.
  clear - H10 eq1 H2.
  unfold join in *; simpl in *.
  pose proof H10 t0.
  unfold get in *; simpl in *.
  rewrite H2 in H.
  rewrite TcbMod.get_sig_none in H.
  destruct (TcbMod.get tls t0); tryfalse; substs; auto.
  apply tidspec.beq_false_neq; auto.

  unfold eqdomTO.
  rewrite set_a_get_a.
  eexists; splits; eauto.
  intros.
  destruct (tidspec.beq t t0) eqn : eq1.
  lets Hx: tidspec.beq_true_eq eq1; substs.
  rewrite set_a_get_a; eauto.
  lets Hx: tidspec.beq_false_neq eq1.
  rewrite set_a_get_a'; eauto.
  destruct H2.
  assert (get tls t0 = Some x).
  eapply join_get_get_l; eauto.
  unfolds in H; simpljoin.
  eapply H4.
  rewrite H in H7; inverts H7.
  eauto.
Qed.

Lemma hpstep_eqdomto :
  forall (T : tasks) (O : osabst) (cst cst' : clientst) 
         (T' : tasks) (O' : osabst) (p : hprog),
    eqdomTO T O -> hpstepstar p T cst O T' cst' O' -> eqdomTO T' O'.
Proof.
  intros.
  gen H.
  inductions H0; intros; auto.
  apply IHhpstepstar.
  eapply hpstep_eqdomO; eauto.  
Qed.

Definition task_no_dead :=
  fun (O : osabst) (t : tid) =>
    forall tls, get O abtcblsid = Some (abstcblist tls) -> indom tls t.

Lemma hmstep_nodead_still:
  forall o C C' O O' t',
    hmstep o C O C' O' ->
    task_no_dead O' t' ->
    task_no_dead O t'.
Proof.
  intros.
  inductions H; auto.
  unfold task_no_dead in *.
  simpljoin.
  unfold eqdomO in H0; simpljoin.
  unfold indom in *.
  intros.

  unfold get in *; simpl in *.
  pose proof H2 abtcblsid.
  rewrite H6 in H7.
  destruct (OSAbstMod.get Of abtcblsid) eqn : eq1;
    destruct (OSAbstMod.get O abtcblsid) eqn : eq2;
    tryfalse.
  substs.
  pose proof H3 abtcblsid.
  rewrite eq1 in H7.
  destruct (OSAbstMod.get O' abtcblsid);
    destruct (OSAbstMod.get OO' abtcblsid);
    tryfalse.
  substs.
  eapply H4; auto.
  
  substs.
  pose proof H3 abtcblsid.
  rewrite eq1 in H7.
  pose proof H5 tls.
  assert(Some (abstcblist tls) = Some (abstcblist tls)) by auto.
  apply H8 in H9; simpljoin.
  rewrite H9 in H7.
  destruct (OSAbstMod.get OO' abtcblsid) eqn : eq3;
    tryfalse.
  substs.
  pose proof H4 x.
  assert(Some (abstcblist x) = Some (abstcblist x)) by auto.
  apply H7 in H11.
  unfolds in H10.
  pose proof H10 t'.
  destruct H12.
  unfold indom in H13.
  eapply H13 in H11.
  eauto.
Qed.

Lemma hapistep_nodead_still:
  forall A C C' O O' t',
    hapistep A C O C' O' ->
    task_no_dead O' t' ->
    task_no_dead O t'.
Proof.
  intros.
  inv H; auto.
  destruct A.
  simpl in H1.
  eapply hmstep_nodead_still; eauto.
Qed.


Lemma htstep_nodead_still:
  forall P t C C' cst cst' O O' t',
    htstep P t C cst O C' cst' O' ->
    task_no_dead O' t' ->
    task_no_dead O t'.
Proof.
  intros.
  inv H; auto.
  eapply hapistep_nodead_still; eauto.
Qed.

Lemma htstepstar_nodead_still:
  forall P t C C' cst cst' O O' t',
    htstepstar P t C cst O C' cst' O' ->
    task_no_dead O' t' ->
    task_no_dead O t'.
Proof. 
  intros.
  inductions H; auto.
  apply IHhtstepstar in H1.

  clear - H H1.
  eapply htstep_nodead_still; eauto.
Qed.


Lemma hpstep_star
: forall (p : hprog) (T T' T'' : tasks) (cst cst' cst'' : clientst)
         (O O' O'' : osabst),
    hpstepstar p T cst O T' cst' O' ->
    hpstep p T' cst' O' T'' cst'' O'' ->
    hpstepstar p T cst O T'' cst'' O''.
Proof.
  intros.
  inductions H.
  eapply hp_stepS; eauto.
  eapply hp_stepO.

  apply IHhpstepstar in H1.
  eapply hp_stepS; eauto.
Qed.


Lemma th_no_create_lift_ev
: forall (Th : tasks) (C C' : code) (t : tid) 
         (p : hprog) (O O' : osabst) (cst cst' : clientst) 
         (ev : val),
    get O curtid = Some (oscurt t) ->
    get Th t = Some C ->
    htstepevstar p t C cst O C' cst' O' ev ->
    hpstepevstar p Th cst O (TasksMod.set Th t C') cst' O' ev.
Proof.
  introv Hn.
  intros.
  inversion H0;subst.
  eapply hp_stepev with (T':=TasksMod.set Th t c') (T'':=TasksMod.set Th t c'') (O':=O'0);eauto. 
  eapply th_ttop_lift;eauto.
  constructors;eauto.
  apply htstepstar_tidsame in H1.
  unfold tidsame in H1.
  rewrite <- Hn;auto.
  apply tasks_get_set.
  assert (TasksMod.set (TasksMod.set Th t c') t c''= TasksMod.set Th t c'').
  eapply  tasks_set_a_set_a.
  auto.
  assert (TasksMod.set (TasksMod.set Th t c'') t C' = TasksMod.set Th t C' ).
  eapply tasks_set_a_set_a.
  rewrite <- H4.
  eapply th_ttop_lift;eauto.
  apply htstepstar_tidsame in H1.
  unfold tidsame in H1.
  rewrite <- Hn;auto.
  apply tasks_get_set.
Qed.


Lemma htstepevstar_tidsame
: forall (p : hprog) (c : code) (cst : clientst) 
         (c' : code) (cst' : clientst) (O O' : osabst) 
         (ev : val) (t : tid),
    htstepevstar p t c cst O c' cst' O' ev -> tidsame O O'.
Proof.
  intros.
  induction H.
  apply htstepstar_tidsame in H.
  apply htstepstar_tidsame in H1.
  inverts H0.
  unfold tidsame in *;rewrite H;auto.
Qed.

Lemma htstep_O_local:
  forall p t C cst O C' cst' O' OO Of,
    htstep p t C cst O C' cst' O' ->
    join O Of OO ->
    exists OO',
      htstep p t C cst OO C' cst' OO' /\ join O' Of OO'.
Proof.
  intros.
  inversion H.
  subst O'.
  subst.
  exists OO.
  split.
  eapply htclt_step with (O:=OO);eauto.
  auto.
  subst.
  inversion H2;subst;tryfalse.
  exists OO.
  split.
  eapply hapi_step;eauto.
  eapply hapienter_step;eauto.
  auto.
  apply join_comm in H0.
  lets Hx: specstep_locality H0 H1.
  destruct Hx.
  exists x.
  destruct H3.
  split.
  eapply hapi_step;eauto.
  eapply hidapi_step;eauto.
  apply join_comm;auto.
  exists OO.
  split;auto.
  eapply hapi_step;eauto.
  eapply hapiexit_step;eauto.
  exists OO.
  split;auto.
  eapply hapi_step;eauto.
  eapply hintex_step;eauto.
Qed.


Lemma htstepstar_O_local:
  forall p t C cst O C' cst' O' OO Of,
    htstepstar p t C cst O C' cst' O' ->
    join O Of OO ->
    exists OO',
      htstepstar p t C cst OO C' cst' OO' /\ join O' Of OO'.
Proof.
  intros.
  gen Of OO.
  induction H.
  intros.
  exists OO.
  split;auto.
  constructors.
  intros.
  lets Hx:htstep_O_local H H1.
  mytac.
  apply IHhtstepstar in H3.
  mytac.
  eexists;split;eauto.
  eapply ht_starS;eauto.
Qed.

Lemma htstepevstar_O_local
: forall (p : hprog) (t : tid) (C : code) (cst : clientst) 
         (O : osabst) (C' : code) (cst' : clientst) 
         (O' OO Of : osabst) ev,
    htstepevstar p t C cst O C' cst' O' ev ->
    join O Of OO ->
    exists OO', htstepevstar p t C cst OO C' cst' OO' ev /\ join O' Of OO'.
Proof.
  intros.
  inverts H.
  lets Hx: htstepstar_O_local H1 H0.
  simpljoin.
  assert (htstepev p t c' cst'0 O'0 c'' cst'0 O'0 ev) as H_bak by auto.
  inversion H2; substs.
  
  clear H16 H17.
  lets Hx: htstepstar_O_local H3 H4.
  simpljoin.
  exists x0.
  split; auto.
  constructors; eauto.
  constructors; eauto.
Qed.

Lemma ltstepev_goodks :forall p t c ke ks c' ke' ks' o o' cst cst' ev, goodks p ks -> 
                                                                       ltstepev p t (c,(ke,ks)) cst o (c',(ke',ks')) cst' o' ev -> goodks p ks'.
Proof.
  intros.
  inversion H0;subst.
  inversion H2;subst.
  inversion H12;subst.
  inversion H9;subst;auto.
Qed.

Lemma tasks_set_get_neq: forall T t t' a, t<>t' -> TasksMod.get (TasksMod.set T t a) t' =  TasksMod.get T t'.
Proof.
  intros.
  apply TasksMod.set_a_get_a'.
  apply tidspec.neq_beq_false.
  apply H.
Qed.

Lemma lpstepev_goodks
: forall (p : lprog) (S S' : osstate) (cst cst' : clientst) 
         (t t' : tid) (T T' : tasks) (ev : val),
    lpstepev p T cst S t T' cst' S' t' ev ->
    good_t_ks p T -> good_t_ks p T'.
Proof.
  unfold good_t_ks.
  intros.
  inversion H.
  subst.
  destruct (tid_eq_dec t' x).
  subst x.
  assert (TasksMod.get (TasksMod.set T t' C') t'= Some C').
  apply tasks_get_set.
  unfold get in *; unfold set in *;  simpl in *.
  rewrite H3 in H1.
  inversion H1 ;subst C'.
  destruct C as (c'&(ke'&ks')).
  apply H0 in H2.
  eapply ltstepev_goodks;eauto.
  assert (TasksMod.get (TasksMod.set T t' C') x =TasksMod.get T x).
  eapply tasks_set_get_neq; eauto.

  unfold get in *; unfold set in *;  simpl in *.
  rewrite H3 in H1.
  apply H0 in H1.
  auto.
Qed.


Lemma hpstepev_eqdomTO :
  forall p T T' cst cst' O O' ev,
    eqdomTO T O -> hpstepev p T cst O T' cst' O' ev ->
    eqdomTO T' O'.
Proof.
  intros.
  inversion H0; substs.
  eapply eqdomTO_setT; eauto.
Qed.

Lemma htstepevstar_nodead_still:
  forall P t C C' cst cst' O O' t' ev,
    htstepevstar P t C cst O C' cst' O' ev->
    task_no_dead O' t' ->
    task_no_dead O t'.
Proof.
  intros.
  inverts H.
  lets Hx: htstepstar_nodead_still H1.
  eapply Hx.
  inverts H2.
  lets Hx1: htstepstar_nodead_still H3.
  eapply Hx1; auto.
Qed.

Lemma hpstepev_eqdomto
: forall (T : tasks) (O : osabst) (cst cst' : clientst) 
         (T' : tasks) (O' : osabst) (p : hprog) (ev : val),
    eqdomTO T O -> hpstepevstar p T cst O T' cst' O' ev -> eqdomTO T' O'.
Proof.
  intros.
  inversion H0; substs.
  assert(eqdomTO T'0 O'0).
  eapply hpstep_eqdomto; eauto.

  assert(eqdomTO T'' O'0).
  eapply hpstepev_eqdomTO; eauto.
  eapply hpstep_eqdomto; eauto.
Qed.

Lemma cltstep_eqo :
  forall t (pc po pi : progunit) 
         (ip : intunit) (cst cst' : clientst) (o o' : taskst) 
         (c c' : code),
    ~ InOS c (pumerge po pi) ->
    ltstep (pc, (po, pi, ip)) t c cst o c' cst' o' -> o = o'.
Proof.
  intros.
  inversion H0; subst; tryfalse || auto.
Qed.

Lemma goodks_callcont_os:
  forall pc po pi ip f s le ks' ks,
    callcont ks = Some (kcall f s le ks') ->
    goodks (pc,(po,pi,ip)) ks ->
    ( exists f0 le1 ks'' t0 d1 d2 s0 s',
        callcont ks' = Some (kcall f0 s0 le1 ks'') /\
        pumerge po pi f0 = Some (t0, d1, d2, s')) ->
    exists a b c d, pumerge po pi f = Some (a,b,c,d).
Proof.
  intros.
  induction ks;subst;tryfalse;auto.
  simpl in H,H0.
  inversion H;subst.
  destruct (pumerge po pi f).
  destruct f0.
  destruct p.
  destruct p.
  do 4 eexists;eauto.
  clear H IHks.
  induction ks';subst;auto;tryfalse.
  destruct H1.
  do 8 destruct H;tryfalse.
  simpl in H0.
  destruct H1.
  do 8 destruct H.
  inversion H;subst.
  rewrite H1 in H0.
  false.
Qed.

Lemma goodks_intcont_os: forall pc po pi ip f s le ks' ks, callcont ks = Some (kcall f s le ks') -> goodks (pc,(po,pi,ip)) ks ->intcont ks' <> None -> exists a b c d, pumerge po pi f = Some (a,b,c,d).
Proof.
  intros.
  induction ks;subst;tryfalse;auto.
  simpl in H, H0.
  inversion H;subst.
  destruct (pumerge po pi f).
  destruct f0.
  destruct p.
  destruct p.
  do 4 eexists;eauto.
  clear H IHks.
  induction ks';subst;auto;tryfalse.
  simpl in H1.
  false.
  simpl in H1.
  false.
Qed.

Lemma step_to_inos_dec :
  forall (c : cureval) (ke : exprcont) (ks : stmtcont)
         (pc po pi : progunit) (ip : intunit) t
         (cst cst' : clientst) (C' : code) (o : taskst),
    good_clt (c, (ke, ks)) pi ->
    goodks (pc, (po, pi, ip)) ks ->
    ~ InOS (c, (ke, ks)) (pumerge po pi) ->
    ltstep (pc, (po, pi, ip)) t (c, (ke, ks)) cst o C' cst' o ->
    (exists f a vl tl ks0,
       po f = Some a /\ C' = (curs (sfexec f vl tl), (kenil, ks0))) \/
    ~ InOS C' (pumerge po pi).
Proof.
  introv H.
  intros Hgoodks.
  intros.
  destruct C' as (c'&(ke'&ks')).
  inversion H1;subst;tryfalse.
  inversion H2;subst pc0 po0 pi0 ip0.

  clear H2 H4 H1 H17.
  inversion H3;subst.
  right.
  inversion H10;subst c0 ke0 ks'.
  unfold InOS in *.
  intro HH.
  destruct H0.
  destruct HH as (c0&ke0&ks0&HH).
  destruct HH.
  inversion H0;subst c0 ke0 ks0.
  exists c ke ks;split;auto.
  destruct H1.
  inversion H11;subst;do 5 destruct H1;tryfalse.
  right.
  auto.
  inversion H10;subst c0 ke ks0.
  unfold InOS in *.
  inversion H11;subst.

  right;intro HH;destruct H0.
  destruct HH as (c0&ke0&ks0&HH).
  destruct HH.
  inversion H0;subst.
  do 3 eexists;split;eauto.
  destruct H1.
  do 5 destruct H1;tryfalse.
  right.
  auto.

  right;intro HH;destruct H0.
  destruct HH as (c'&ke'&ks'&HH).
  destruct HH.
  inversion H0;subst.
  do 3 eexists;split;eauto.
  destruct H1.
  do 5 destruct H1;tryfalse.
  right.
  auto.

  right;intro HH;destruct H0.
  destruct HH as (c'&ke'&ks0&HH).
  destruct HH.
  inversion H0;subst.
  do 3 eexists;split;eauto.
  destruct H5.
  do 5 destruct H5;tryfalse.
  right.
  auto.

  right;intro HH;destruct H0.
  destruct HH as (c'&ke'&ks0&HH).
  destruct HH.
  inversion H0;subst.
  do 3 eexists;split;eauto.
  destruct H1.
  do 5 destruct H1;tryfalse.
  right.
  auto.

  right;intro HH;destruct H0.
  destruct HH as (c'&ke'&ks0&HH).
  destruct HH.
  inversion H0;subst.
  do 3 eexists;split;eauto.
  destruct H1.
  do 5 destruct H1;tryfalse.
  right.
  auto.

  destruct (classic (exists a,po f = Some a)).
  left.
  destruct H1.
  do 5 eexists;split;eauto.

  right;intro HH;destruct H0.
  destruct HH as (c'&ke'&ks0&HH).
  destruct HH.
  unfold good_clt in H.
  destruct H.
  simpl in H.
  do 3 eexists;splits;eauto.
  destruct H2.
  do 5 destruct H2.
  inversion H0;subst.
  inversion H0;subst.
  unfold pumerge in H5.
  destruct (po x).
  destruct H1.
  exists f;auto.
  rewrite H in H5.
  tryfalse.
  inversion H0;subst.
  right.
  auto.

  right;intro HH;destruct H0.
  destruct HH as (c'&ke'&ks'0&HH).
  destruct HH.
  inversion H0;subst.
  do 3 eexists;split;eauto.
  destruct H1.
  do 5 destruct H1;tryfalse.
  right.
  auto.

  destruct (classic (exists a,po f = Some a)).
  left.
  destruct H1.
  do 5 eexists;split;eauto.

  right;intro HH;destruct H0.
  destruct HH as (c'&ke'&ks0&HH).
  destruct HH.
  unfold good_clt in H.
  destruct H.
  simpl in H,H4.
  destruct H4.
  do 3 eexists;splits;eauto.
  destruct H2.
  do 5 destruct H2.
  inversion H0;subst.
  inversion H0;subst.
  unfold pumerge in H6.
  destruct (po x).
  destruct H1.
  exists f;auto.
  rewrite H5 in H6.
  tryfalse.
  inversion H0;subst.
  right.
  auto.

  right;intro HH;destruct H0.
  destruct HH as (c'&ke'&ks'0&HH).
  destruct HH.
  inversion H0;subst.
  do 3 eexists;split;eauto.
  destruct H8.
  do 5 destruct H8;tryfalse.
  destruct H8.
  do 9 destruct H8.
  simpl in H8.
  inversion H8;subst.
  left.
  do 4 eexists;split;eauto.
  right.
  right.
  auto.

  right;intro HH;destruct H0.
  destruct HH as (c'&ke'&ks0&HH).
  destruct HH.
  inversion H0;subst.
  do 3 eexists;split;eauto.
  destruct H8.
  do 5 destruct H8;tryfalse.
  right.
  auto.

  right;intro HH;destruct H0.
  destruct HH as (c'&ke'&ks0&HH).
  destruct HH.
  inversion H0;subst.
  do 3 eexists;split;eauto.
  destruct H5.
  do 5 destruct H5;tryfalse.
  right.
  auto.

  destruct (classic (exists f a vl tl, s = sfexec f vl tl /\ po f = Some a)).
  do 5 destruct H1.
  left.
  subst s.
  do 5 eexists;split;eauto.

  right;intro HH;destruct H0.
  destruct HH as (c'&ke'&ks0'&HH).
  destruct HH.
  inversion H0;subst.
  do 3 eexists;split;eauto.
  destruct H2.
  do 5 destruct H2;tryfalse.
  inversion H2;subst.
  destruct H1.
  unfold pumerge in H4.
  exists x x1 x0 x2;split;eauto.
  unfold good_clt in H.
  destruct H.
  simpl in H1.
  destruct H1.
  destruct (po x);auto.
  rewrite H1 in H4;tryfalse.
  right.
  auto.

  right;intro HH;destruct H0.
  destruct HH as (c'&ke'&ks0&HH).
  destruct HH.
  inversion H0;subst.
  do 3 eexists;split;eauto.
  destruct H1.
  do 5 destruct H1;tryfalse.
  right.
  auto.

  right;intro HH;destruct H0.
  destruct HH as (c'&ke'&ks0&HH).
  destruct HH.
  inversion H0;subst.
  do 3 eexists;split;eauto.
  destruct H1.
  do 5 destruct H1;tryfalse.
  right.
  simpl in H1.
  auto.

  right;intro HH;destruct H0.
  destruct HH as (c'&ke'&ks0&HH).
  destruct HH.
  inversion H0;subst.
  do 3 eexists;split;eauto.
  destruct H1.
  do 5 destruct H1;tryfalse.
  right.
  simpl in H1.
  auto.

  right;intro HH;destruct H0.
  destruct HH as (c'&ke'&ks0&HH).
  destruct HH.
  inversion H0;subst.
  do 3 eexists;split;eauto.
  destruct H5.
  do 5 destruct H5;tryfalse.
  right.
  auto.

  right;intro HH;destruct H0.
  destruct HH as (c'&ke'&ks0&HH).
  destruct HH.
  inversion H0;subst.
  do 3 eexists;split;eauto.
  destruct H5.
  do 5 destruct H5;tryfalse.
  right.
  destruct H5.
  left.
  eapply goodks_callcont_os in H5;eauto.
  do 4 destruct H5;
    do 8 eexists;split;eauto.
  left. 
  eapply goodks_intcont_os in H5;eauto.
  do 4 destruct H5.
  do 8 eexists;split;eauto.

  destruct (classic (exists f a vl tl, s1 = sfexec f vl tl /\ po f = Some a)).
  do 5 destruct H1.
  left.
  subst s1.
  do 5 eexists;split;eauto.
  right;intro HH;destruct H0.
  destruct HH as (c'&ke'&ks0'&HH).
  destruct HH.
  inversion H0;subst.
  do 3 eexists;split;eauto.
  destruct H2.
  do 5 destruct H2;tryfalse.
  inversion H2;subst.
  destruct H1.
  unfold pumerge in H4.
  exists x x1 x0 x2;split;eauto.
  unfold good_clt in H.
  destruct H.
  simpl in H.
  destruct H.
  destruct (po x);auto.
  rewrite H in H4;tryfalse.
  right.
  auto.

  destruct (classic (exists f a vl tl, s = sfexec f vl tl /\ po f = Some a)).
  do 5 destruct H1.
  left.
  subst s.
  do 5 eexists;split;eauto.
  right;intro HH;destruct H0.
  destruct HH as (c'&ke'&ks0'&HH).
  destruct HH.
  inversion H0;subst.
  do 3 eexists;split;eauto.
  destruct H2.
  do 5 destruct H2;tryfalse.
  inversion H2;subst.
  destruct H1.
  unfold pumerge in H4.
  exists x x1 x0 x2;split;eauto.
  unfold good_clt in H.
  destruct H.
  simpl in H1.
  destruct H1.
  destruct (po x);auto.
  rewrite H1 in H4;tryfalse.
  right.
  auto.

  destruct (classic (exists f a vl tl, s = sfexec f vl tl /\ po f = Some a)).
  do 5 destruct H1.
  left.
  subst s.
  do 5 eexists;split;eauto.
  right;intro HH;destruct H0.
  destruct HH as (c'&ke'&ks0'&HH).
  destruct HH.
  inversion H0;subst.
  do 3 eexists;split;eauto.
  destruct H2.
  do 5 destruct H2;tryfalse.
  inversion H2;subst.
  destruct H1.
  unfold pumerge in H4.
  exists x x1 x0 x2;split;eauto.
  unfold good_clt in H.
  destruct H.
  simpl in H1.
  destruct H1.
  destruct (po x);auto.
  rewrite H1 in H4;tryfalse.
  right.
  auto.

  right;intro HH;destruct H0.
  destruct HH as (c'&ke'&ks0&HH).
  destruct HH.
  inversion H0;subst.
  do 3 eexists;split;eauto.
  destruct H1.
  do 5 destruct H1;tryfalse.
  right.
  simpl in H1.
  auto.

  right;intro HH;destruct H0.
  destruct HH as (c'&ke'&ks0&HH).
  destruct HH.
  inversion H0;subst.
  do 3 eexists;split;eauto.
  destruct H1.
  do 5 destruct H1;tryfalse.
  right.
  simpl in H1.
  auto.

  destruct (classic (exists f a vl tl, s1 = sfexec f vl tl /\ po f = Some a)).
  do 5 destruct H1.
  left.
  subst s1.
  do 5 eexists;split;eauto.
  right;intro HH;destruct H0.
  destruct HH as (c'&ke'&ks0'&HH).
  destruct HH.
  inversion H0;subst.
  do 3 eexists;split;eauto.
  destruct H2.
  do 5 destruct H2;tryfalse.
  inversion H2;subst.
  destruct H1.
  unfold pumerge in H4.
  exists x x1 x0 x2;split;eauto.
  unfold good_clt in H.
  destruct H.
  simpl in H1.
  destruct H1.
  destruct (po x);auto.
  rewrite H1 in H4;tryfalse.
  right.
  auto.

  destruct (classic (exists f a vl tl, s2 = sfexec f vl tl /\ po f = Some a)).
  do 5 destruct H1.
  left.
  subst s2.
  do 5 eexists;split;eauto.
  right;intro HH;destruct H0.
  destruct HH as (c'&ke'&ks0'&HH).
  destruct HH.
  inversion H0;subst.
  do 3 eexists;split;eauto.
  destruct H2.
  do 5 destruct H2;tryfalse.
  inversion H2;subst.
  destruct H1.
  unfold pumerge in H4.
  exists x x1 x0 x2;split;eauto.
  unfold good_clt in H.
  destruct H.
  simpl in H1.
  destruct H1.
  destruct H5.
  destruct (po x);auto.
  rewrite H5 in H4;tryfalse.
  right.
  auto.

  right;intro HH;destruct H0.
  destruct HH as (c'&ke'&ks0&HH).
  destruct HH.
  inversion H0;subst.
  do 3 eexists;split;eauto.
  destruct H1.
  do 5 destruct H1;tryfalse.
  right.
  simpl in H1.
  auto.

  destruct (classic (exists f a vl tl, s = sfexec f vl tl /\ po f = Some a)).
  do 5 destruct H1.
  left.
  subst s.
  do 5 eexists;split;eauto.
  right;intro HH;destruct H0.
  destruct HH as (c'&ke'&ks0'&HH).
  destruct HH.
  inversion H0;subst.
  do 3 eexists;split;eauto.
  destruct H2.
  do 5 destruct H2;tryfalse.
  inversion H2;subst.
  destruct H1.
  unfold pumerge in H4.
  exists x x1 x0 x2;split;eauto.
  unfold good_clt in H.
  destruct H.
  simpl in H1.
  destruct H1.
  destruct (po x);auto.
  rewrite H1 in H4;tryfalse.
  right.
  auto.

  right;intro HH;destruct H0.
  destruct HH as (c'&ke'&ks0&HH).
  destruct HH.
  inversion H0;subst.
  do 3 eexists;split;eauto.
  destruct H1.
  do 5 destruct H1;tryfalse.
  right.
  simpl in H1.
  auto.
Qed.

Lemma sstep_pumerge :
  forall pc po pi c c' ks ks' m m',
    sstep (pumerge pc po) c ks m c' ks' m' ->
    ~InOS (c, (kenil, ks)) (pumerge po pi) ->
    sstep pc c ks m c' ks' m'.
Proof.
  intros.
  inversion H; subst; try (constructors; eauto).
  unfold pumerge in H3.
  destruct (pc f) eqn : eq1.
  inversion H3.
  auto.
  destruct (po f) eqn : eq2.
  false.
  apply H0.
  unfold InOS.
  do 3 eexists.
  split.
  auto.
  left.
  do 4 eexists.
  split.
  auto.
  unfold pumerge.
  rewrite eq2.
  auto.
  inversion H3.
Qed.

Lemma cstep_pumerge : forall pc po pi c c' m m', cstep (pumerge pc po) c m c' m' -> ~InOS c (pumerge po pi) -> cstep pc c m c' m'.
Proof.
  intros.
  inversion H.
  subst.
  pose proof expr_step.
  pose proof (H1 pc (c0, (ke, ks)) m m' c0 c'0 ke ke' ks).
  apply H3.
  auto.
  auto.  
  subst.
  pose proof stmt_step.
  eapply H1.
  auto.
  eapply sstep_pumerge.
  eauto.
  eauto.
Qed.

Lemma cltstep1_eq
: forall (pc po pi : progunit) (ip : intunit) 
         (cst cst' : clientst) (o : taskst) (O : osabst) 
         (A : osspec) (c c' : code) t,
    ltstep (pc, (po, pi, ip)) t c cst o c' cst' o ->
    good_clt c pi ->
    ~ InOS c (pumerge po pi) -> htstep (pc, A) t c cst O c' cst' O.
Proof.
  intros.
  inversion H;subst;unfolds in H0;simpl in H0;try destruct H0;tryfalse.
  inversion H2;subst pc0 po0 pi0 ip0.
  eapply htclt_step;eauto.
  eapply cstep_pumerge; eauto.
Qed.

Lemma pumerge_get: forall po pi f t d1 d2 s, po f= Some (t, d1, d2, s) -> (pumerge po pi) f = Some (t,d1,d2,s).
Proof.
  intros.
  unfold pumerge.
  rewrite H.
  auto.
Qed.

Lemma no_inos_pc:
  forall f vl tl ks0 pc po pi t0 d1 d2 s,
    ~ InOS (curs (sfexec f vl tl), (kenil, ks0)) (pumerge po pi) ->
    pumerge pc po f = Some (t0, d1, d2, s) -> pc f = Some ( t0, d1 , d2 , s).
Proof.
  intros.
  unfold InOS in *.
  assert (~ exists a, po f = Some a).
  intro X.
  destruct H.
  destruct X.
  do 3 eexists;split;eauto.
  left.
  do 2 eexists.
  exists x.
  eexists.
  split;eauto.
  destruct x.
  destruct p.
  destruct p.
  eapply pumerge_get;eauto.
  unfold pumerge in H0.
  destruct (pc f);auto.
  destruct (po f);tryfalse.
  destruct H1.
  exists f0.
  auto.
Qed.

Lemma good_clt_scont_callcont: forall ks ks' f s le p, good_clt_scont ks p-> callcont ks = Some (kcall f s le ks') -> good_clt_scont ks' p.
Proof.
  intros.
  induction ks;tryfalse;auto.
  simpl in H0.
  simpl in H.
  destruct H.
  apply IHks;auto.
  simpl in H0.
  simpl in H.
  inversion H0;subst.
  destruct H;auto.
  simpl in H, H0.
  destruct H1;auto.
  simpl in H.
  destruct H;auto.
  apply IHks;auto.
  simpl in H,H0.
  destruct H;destruct H1;auto.
  apply IHks;auto.
  simpl in H,H0.
  destruct H;auto.
Qed.

Lemma clt_step_good_clt
: forall (pc po pi : progunit) (ip : intunit) 
         t (c : cureval) (ke : exprcont) 
         (ks : stmtcont) (cst : clientst) (o : taskst) 
         (cst' : clientst) (o' : taskst) (C' : code),
    ltstep (pc, (po, pi, ip)) t (c, (ke, ks)) cst o C' cst' o' ->
    GoodClient pc po pi ->
    good_clt (c, (ke, ks)) pi ->
    ~ InOS (c, (ke, ks)) (pumerge po pi) -> good_clt C' pi.
Proof.
  intros.
  inversion H;subst;tryfalse.
  destruct C' as (c'&(ke'&ks')).

  unfold good_clt in *.
  unfold good_clt_cureval, good_clt_scont in *.
  destruct H1.
  split.
  inversion H4;subst;simpl;tryfalse.
  inversion H16;subst;tryfalse;simpl;auto.
  induction H16;subst;tryfalse;simpl;auto;inversion H3;subst pc0 po0 pi0 ip0.
  inversion H15;subst.
  fold good_clt_scont in H6.
  simpl in H1;auto.
  inversion H15;subst.
  simpl in H1;auto.
  inversion H15;subst.
  fold good_clt_scont in H6.
  destruct H6.
  auto.
  inversion H15;subst.
  fold good_clt_scont in H6.
  destruct H6;auto.
  inversion H15;subst.
  simpl in H1.
  destruct H1;auto.
  inversion H15;subst.
  destruct H6;auto.
  inversion H15;subst.
  destruct H6;auto.
  inversion H15;subst.
  destruct H6;auto.
  inversion H15;subst.
  destruct H6.
  destruct H8;auto.
  destruct H9;auto.
  inversion H15;subst.
  destruct H6;auto.

  inversion H4;subst;simpl;tryfalse.
  inversion H16;subst;tryfalse;inversion H15;subst;try fold good_clt_scont;
  fold good_clt_scont in H6;auto.
  inversion H3;subst pc0 po0 pi0 ip0.
  inversion H15;subst.
  inversion H16;subst;tryfalse;simpl;auto;
  try fold good_clt_scont;
  fold good_clt_scont in H6;auto.
  destruct H6;auto.
  splits;auto.
  assert (pc f = Some (t0,d1,d2,s)).
  eapply no_inos_pc;eauto.
  unfold GoodClient in *.
  destruct H0 as (H0&Hpudisj).
  apply H0 in H13.

  apply Goodstmt_good_clt_stmt;auto.

  eapply good_clt_scont_callcont;eauto.
  splits;auto.
  simpl in H1;destruct H1;auto.
  destruct H6;auto.
  destruct H6;auto.
  simpl in H1;destruct H1;splits;auto.
  destruct H6.
  destruct H7;auto.
  destruct H6;destruct H7;auto.
  destruct H6;auto.
Qed.

Lemma step_fexec_ninos
: forall (c : cureval) (ke : exprcont) (ks : stmtcont)
         t (f : fid) (vl : vallist) 
         (tl : typelist) (ks' : stmtcont) (cst cst' : clientst)
         (o o' : taskst) (pc po pi : progunit) (ip : intunit),
    ~ InOS (c, (ke, ks)) (pumerge po pi) ->
    ltstep (pc, (po, pi, ip)) t (c, (ke, ks)) cst o
           (curs (sfexec f vl tl), (kenil, ks')) cst' o' ->
    ~ InOS (SKIP , (kenil, ks')) (pumerge po pi).
Proof.
  intros.
  inversion H0;subst;tryfalse.
  inversion H1;subst pc0 po0 pi0 ip0.
  inversion H2;subst.
  inversion H13;subst;tryfalse.
  inversion H10;subst c0 ke ks0.
  inversion H12;subst;tryfalse.
  intro X .
  destruct H.
  unfold InOS in *.
  destruct X.
  do 3 destruct H.
  inversion H;subst x x0 x1.
  do 3 eexists;split;eauto.
  destruct H4.
  do 5 destruct H4;tryfalse.
  right;auto.

  intro X ; destruct H.
  unfold InOS in *.
  destruct X.
  do 3 destruct H.
  inversion H;subst x x0 x1.
  do 3 eexists;split;eauto.
  destruct H4.
  do 5 destruct H4;tryfalse.
  right;auto.

  intro X ; destruct H.
  unfold InOS in *.
  destruct X.
  do 3 destruct H.
  inversion H;subst x x0 x1.
  do 3 eexists;split;eauto.
  destruct H4.
  do 5 destruct H4;tryfalse.
  right;auto.

  intro X ; destruct H.
  unfold InOS in *.
  destruct X.
  do 3 destruct H.
  inversion H;subst x x0 x1.
  do 3 eexists;split;eauto.
  destruct H4.
  do 5 destruct H4;tryfalse.
  right;auto.
  intro X ; destruct H.
  unfold InOS in *.
  destruct X.
  do 3 destruct H.
  inversion H;subst x x0 x1.
  do 3 eexists;split;eauto.
  destruct H4.
  do 5 destruct H4;tryfalse.
  right;auto.

  intro X ; destruct H.
  unfold InOS in *.
  destruct X.
  do 3 destruct H.
  inversion H;subst x x0 x1.
  do 3 eexists;split;eauto.

  intro X ; destruct H.
  unfold InOS in *.
  destruct X.
  do 3 destruct H.
  inversion H;subst x x0 x1.
  do 3 eexists;split;eauto.

  destruct H4.
  do 5 destruct H4;tryfalse.
  right;auto.

  intro X ; destruct H.
  unfold InOS in *.
  destruct X.
  do 3 destruct H.
  inversion H;subst x x0 x1.
  do 3 eexists;split;eauto.

  destruct H4.
  do 5 destruct H4;tryfalse.
  right;auto.

  intro X ; destruct H.
  unfold InOS in *.
  destruct X.
  do 3 destruct H.
  inversion H;subst x x0 x1.
  do 3 eexists;split;eauto.

  destruct H4.
  do 5 destruct H4;tryfalse.
  right;auto.
Qed.


Lemma stepev_still_inos
: forall (C : code) (pc po pi : progunit) (ip : intunit)
         t (C' : code) (cst: clientst) 
         (o: taskst) (ev : val),
    ~ InOS C (pumerge po pi) ->
    ltstepev (pc, (po, pi, ip)) t C cst o C' cst o ev ->
    ~ InOS C' (pumerge po pi).
Proof.
  intros.
  inversion H0.
  inversion H1.
  subst.
  inversion H2.
  subst.
  inversion H5.
  subst.
  intro.
  apply H.
  unfold InOS in H7.
  do 4 destruct H7.
  inversion H7.
  subst.
  destruct H8.
  do 4 destruct H8.
  destruct H8.
  inversion H8.
  destruct H8.
  do 8 destruct H8.
  unfold InOS.
  do 3 eexists.
  split.
  auto.
  right.
  left.
  do 8 eexists.
  split.
  eapply H8.
  eapply H8.

  unfold InOS.
  do 3 eexists.
  split.
  auto.
  right.
  right.
  auto.
Qed.

Lemma cltstepev_eq
: forall (pc po pi : progunit) (ip : intunit) 
         (cst cst' : clientst) (o : taskst) (O : osabst) 
         t (A : osspec) (c c' : code) 
         (ev : val),
    ltstepev (pc, (po, pi, ip)) t c cst o c' cst' o ev ->
    ~ InOS c (pumerge po pi) -> htstepev (pc, A) t c cst O c' cst' O ev.
Proof.
  intros.
  inversion H.
  inversion H1.
  subst.
  constructors; eauto.
  inversion H2.
  inversion H5.
  subst.
  assert (sstepev pc0 (curs (sprint e)) ks' (ge, le, M) SKIP  ks' (ge, le, M) ev).
  constructors; eauto.
  assert (cstepev pc0 (curs (sprint e), (kenil, ks')) (ge, le, M) (SKIP , (kenil, ks')) (ge, le, M) ev).
  constructors; eauto.
  auto.
Qed.

Lemma clt_stepev_good_clt
: forall (pc po pi : progunit) (ip : intunit) 
         t (c : cureval) (ke : exprcont) 
         (ks : stmtcont) (cst : clientst) (o : taskst) 
         (cst' : clientst) (o' : taskst) (C' : code) 
         (ev : val),
    ltstepev (pc, (po, pi, ip)) t (c, (ke, ks)) cst o C' cst' o' ev ->
    good_clt (c, (ke, ks)) pi ->
    ~ InOS (c, (ke, ks)) (pumerge po pi) -> good_clt C' pi.
Proof.
  intros.
  destruct C' as (c'&(ke'&ks')).
  inversion H;subst.
  inversion H3;subst.
  inversion H14;subst.
  inversion H11;subst.
  unfold good_clt in *.
  destruct H0;split;auto.
Qed.


Lemma sstep_pumerge' :
  forall pc po pi c c' ks ks' m m',
    sstep pc c ks m c' ks' m' ->
    ~InOS (c, (kenil, ks)) (pumerge po pi) ->
    sstep (pumerge pc po) c ks m c' ks' m'.
Proof.
  intros.
  inversion H; subst; try (constructors; eauto).
  unfold pumerge.
  rewrite H3.
  auto.
Qed.

Lemma cstep_pumerge' :
  forall pc po pi c c' m m',
    cstep pc c m c' m' -> ~InOS c (pumerge po pi) -> cstep (pumerge pc po) c m c' m'.
Proof.
  intros.
  inversion H; subst.
  eapply expr_step.
  auto.
  auto.
  eapply stmt_step.
  auto.
  eapply sstep_pumerge'.
  apply H2.
  apply H0.
Qed.

Definition no_api_code := 
  fun c : code =>
    forall (ke : exprcont) (ks : stmtcont) (x : spec_code),
      c <> (curs (hapi_code x), (ke, ks)).
Lemma cltstep_eqabt
: forall (pc po pi : progunit) (ip : intunit) 
         (ge : env) (envs : cltenvs) (m : mem) (o : taskst) 
         (O : osabst) t (A : osspec) 
         (c : code),
    ~ IsEnd c ->
    ~ IsCrt c ->
    ~ IsDel c ->
    ~ IsSc c ->
    eqdomOS (po, pi, ip) A ->
    no_api_code c ->
    ltstepabt (pc, (po, pi, ip)) t c (ge, envs, m) o ->
    ~ InOS c (pumerge po pi) -> htstepabt (pc, A) t c (ge, envs, m) O.
Proof.
  introv Hnoend Hnocrt Hnodel Hnosc.
  introv H.
  introv Hnoapicode.
  intros.

  inversion H0;subst.
  apply not_or_and in H3.
  destruct H3.
  constructors;eauto.

  intro.
  mytac.
  destruct H3.
  exists x o x0.
  inverts H5.
  inverts H2.
  eapply clt_step;eauto.
  eapply cstep_pumerge';eauto.
  inverts H2.
  inverts H3;auto;tryfalse.
  unfolds in H.
  destructs H.
  assert ( (exists fdef, po0 f = Some fdef)).
  apply H.
  eexists;eauto.
  mytac.
  destruct x as (((a,b),c),d).
  destruct H1.
  unfolds.
  do 3 eexists.
  splits;eauto.
  left.
  do 4 eexists;split;eauto.
  eapply pumerge_get;eauto.

  intro.
  destruct H4.
  inverts H2.
  mytac.
  inverts H2.
  inverts H5.
  inverts H6.
  do 4 eexists.
  constructors;eauto.
  constructors;eauto.
  constructors;eauto.
Qed.

Lemma n_tlmatch_abt
: forall (pc : progunit)
         (po : fid -> option (type * decllist * decllist * stmts))
         (pi : progunit) (ip : intunit) (f : fid) (tp : type)
         (d1 d2 : decllist) (s : stmts) (tl : list type) 
         (vl : list val) (ks : stmtcont) t 
         (cst : clientst) (o : taskst),
    ~ (tlmatch (rev tl) d1 /\ dl_vl_match d1 (rev vl) = true) ->
    po f = Some (tp, d1, d2, s) ->
    ltstepabt (pc, (po, pi, ip)) t (curs (sfexec f vl tl), (kenil, ks))
              cst o.
Proof.
  intros.
  constructors;eauto.
  intros X.
  destruct H.
  destruct X.
  do 3 destruct H.
  inversion H;subst;tryfalse.
  inversion H1;subst pc0 po0 pi0 ip0.
  destruct H3.
  unfold InOS.
  do 3 eexists;split;eauto.
  left.
  do 4 eexists;split;eauto.
  eapply pumerge_get;eauto.
  inversion H1;subst pc0 po0 pi0 ip0.
  inversion H2;subst;tryfalse.
  inversion H4;subst;tryfalse.
  inversion H6;subst;tryfalse.
  inversion H5;subst.
  inversion H6;subst;tryfalse.
  assert (pumerge po pi f = Some (tp,d1,d2,s)).
  apply pumerge_get;auto.
  rewrite H13 in H7;inversion H7;subst.
  split;auto.
  eapply tl_vl_dl'';eauto.
  destruct H.
  do 3 destruct H.
  inversion H;subst;tryfalse.
  inversion H2;subst;tryfalse.
  inversion H5;subst;tryfalse.
Qed.

Lemma hn_tlmatch_abt
: forall (pc : fid -> option function)
         (B : fid -> option (api_code * (type * list type))) 
         (C : osintspec) (ab : api_code) (f : fid) 
         (tp : type) (tl' tl : list type) (vl : vallist) 
         (ks : stmtcont) (ge : env) (envs : cltenvs) 
         (m : mem) (O : osabst) (sc : ossched) t,
    pc f = None ->
    ~ (rev tl = tl' /\ tl_vl_match tl vl = true) ->
    B f = Some (ab, (tp, tl')) ->
    htstepabt (pc, (B, C, sc)) t (curs (sfexec f vl tl), (kenil, ks))
              (ge, envs, m) O.
Proof.
  intros.
  constructors;eauto.
  unfolds.
  intro.
  unfolds in H2.
  mytac;tryfalse.

  unfold IsCrt.
  intro; simpljoin.

  unfold IsDel.
  intro; simpljoin.

  unfold IsSc.
  intro; simpljoin.

  intro.
  mytac.
  inverts H2.
  inverts H3.
  inverts H4.
  inverts H2.
  inverts H3;tryfalse.
  inverts H2.
  inverts H3.
  rewrite H11 in H;tryfalse.
  inverts H3.
  inverts H4.
  inverts H5.
  inverts H2.
  rewrite H7 in H1;inverts H1.
  destruct H0.
  split;auto.
  apply List.rev_involutive.
  rewrite <- tl_vl_rev_match;auto.
  intro.
  mytac.
  inverts H2.
  inverts H4.
  inverts H5.
  inverts H2.
Qed.

Lemma fexec_abt_eq
: forall (pc po pi : progunit) (ip : intunit) 
         (A : osspec) (t : type) (d1 d2 : decllist) 
         (s : stmts) tid (o : taskst) 
         (O : osabst) (cst cst' : clientst) (dl : typelist) 
         (vl : vallist) (f : fid) (ks : stmtcont),
    GoodClient pc po pi ->
    po f = Some (t, d1, d2, s) ->
    eqdomOS (po, pi, ip) A ->
    ltstepabt (pc, (po, pi, ip)) tid (curs (sfexec f vl dl), (kenil, ks))
              cst o ->
    htstepabtstar (pc, A) tid (curs (sfexec f vl dl), (kenil, ks)) cst' O.
Proof.
  intros.
  eapply htabtstar.
  exists (curs (sfexec f vl dl), (kenil, ks)) cst' O.
  splits.
  eapply ht_starO;eauto.
  unfold IsEnd.
  eapply htstep_abt;eauto.
  intro.
  unfolds in H3.
  mytac;inverts H3.

  unfold IsCrt.
  intro; simpljoin.

  unfold IsDel.
  intro; simpljoin.

  unfold IsSc.
  intro; simpljoin. 
 
  assert(po f=Some (t,d1,d2,s));auto.
  inversion H2.
  subst.
  inversion H4;subst pc0 po0 pi0 ip0.

  intro X.
  mytac.
  destruct H5.
  left.
  destruct o as [[[[]]]].
  exists ((curs (salloc vl (revlcons d1 d2))),(kenil,kcall f s e0 ks)).
  eexists; instantiate (1 := (e,empenv,m,i,l)).
  exists cst.
  eapply inapi_step;eauto.
  eapply ostc_step;eauto.
  eapply stmt_step;eauto.
  assert ( tlmatch (rev dl) d1 /\ tl_vl_match dl vl = true).

  inversion H6;subst;tryfalse.
  inversion H4;subst pc0 A0.
  inversion H5;subst;tryfalse.
  inversion H8;tryfalse.
  inversion H8;subst;tryfalse.
  inversion H7;subst f0.
  unfold GoodClient in *.
  destruct H.
  destruct H15.
  assert (pc f <> None).
  intro XZ;tryfalse.
  apply H15 in H20.
  tryfalse.

  inversion H4;subst pc0 A.
  inversion H5;subst.
  inverts H9.
  unfold eqdomOS in *.
  destruct H1.
  destruct H7.
  lets Hf: H7 H0 H11.
  simpl in Hf.
  rewrite List.rev_involutive.
  split.
  destruct Hf;auto.
  rewrite <- tl_vl_rev_match;auto.
 
  destruct H4.
  eapply sfexec_step;eauto.
  eapply pumerge_get;eauto.

  unfold InOS.
  do 3 eexists;splits;eauto.
  left.
  do 4 eexists;split;eauto.
  eapply pumerge_get;eauto.

  intro X.
  mytac.
  inversion H3;subst;tryfalse.
  inversion H5;subst;tryfalse.
  inversion H7;subst;tryfalse.
Qed.

Lemma TStWoMemEq_emple_tst_same :
  forall o,
    TStWoMemEq (emple_tst o) (emple_tst o).
Proof.
  intros.
  unfolds.
  destruct o.
  destruct p.
  destruct s.
  destruct p.
  simpl.
  auto.
Qed.

Lemma join_join_join_exists :
  forall
    {A B T : Type} {MC : PermMap A B T}
    m1 m2 m3 m4 m5 m6 m7 mx,
    usePerm = true ->
    join m1 m2 m3 ->
    join m3 m4 m5 ->
    join m5 m6 m7 ->
    join m1 m6 mx ->
    exists mxx, join mx m2 mxx /\ join m3 m6 mxx.
Proof.
  intros.
  exists (merge mx m2).
  split.
  hy.
  hy.
Qed.


Lemma alloc_locality
: forall (p : lprog) (o : taskst) (Ms : mem)
         (Mf : mem) (o2 : taskst) tid 
         (o'' : taskst) (vl : vallist) (dl : decllist) 
         (ks : stmtcont) (cst cst' : clientst) (C' : code),
    joinm2 o Ms Mf o2 ->
    ltstep p tid (curs (salloc vl dl), (kenil, ks)) cst o2 C' cst' o'' ->
    exists o',
      ltstep p tid (curs (salloc vl dl), (kenil, ks)) cst o C' cst' o' /\
      joinm2 o' Ms Mf o'' /\
      TStWoMemEq (emple_tst o') (emple_tst o).
Proof.
  intros.
  unfold joinm2 in *.
  rename H0 into H1.
  destruct H as (o1&H&H0).

  assert (
      (exists o1' o',
         ltstep p tid (curs (salloc vl dl), (kenil, ks)) cst o C' cst' o' /\
         joinmem o' Ms o1' /\
         joinmem o1' Mf o'' /\ TStWoMemEq (emple_tst o') (emple_tst o))
      ->
      (exists o',
         ltstep p tid (curs (salloc vl dl), (kenil, ks)) cst o C' cst' o' /\
         (exists o0, joinmem o' Ms o0 /\ joinmem o0 Mf o'') /\
         TStWoMemEq (emple_tst o') (emple_tst o))
    ).
  intros; simpljoin.
  eexists.
  splits; eauto.
  apply H2; clear H2.
  
  inv H1.
  do 2 eexists; split; [constructors; eauto | split; [ eauto | split; [ eauto | apply TStWoMemEq_emple_tst_same ]]].
  
  inverts H3; try solve [inversion H1].
  inverts H1; inverts H2; try solve [inversion H3].

  (* sstep *)
  destruct o1; destruct p; destruct s; destruct p.
  destruct o; destruct p; destruct s; destruct p.
  destruct m; destruct p.
  unfolds in H.
  do 7 destruct H.
  destruct H1.
  unfolds in H0.
  do 7 destruct H0.
  destruct H5.
  inverts H.
  inverts H1.
  inverts H0.
  inverts H5.
  (* inverts sstep, 3 cases left *)
  inverts H3.
  (* sallocp_step *)
  inverts H1.
  pose proof alloc_store_exist_mem_env.
  pose proof H x v b t le M le' M' M'' H7 H9 H15; clear H.
  destruct H0.
  do 2 destruct H.
  destruct H0.
  destruct H1.
  pose proof alloc_locality_pre2.
  pose proof H5 x (b, 0%Z) t v b le le' x1 Ms x7 Mf M M' M'' x0 H2 H6 H H1 H7 H9 H15; clear H5.
  destruct H8.
  do 2 destruct H5.
  destruct H8.
  
  assert (exists Mx, join x4 Ms Mx /\ join x7 x0 Mx).  (** this is NOT wrong **)
  eapply join_join_join_exists; eauto.
  do 2 destruct H11.
  do 2 eexists.
  split.
  eapply inapi_step; eauto.
  eapply ostc_step; eauto.
  eapply stmt_step; eauto.
  eapply sallocp_step; eauto.
  split.
  unfolds.
  do 6 eexists.
  split.
  auto.
  split.
  auto.
  apply H11.
  split.
  unfolds.
  do 6 eexists.
  split.
  auto.
  split.
  auto.

  clear - H1 H6 H12.
  join auto.
  simpl; auto.

  inverts H1.
  pose proof alloc_exist_mem_env.
  pose proof H x t le M le' M' H13; clear H.
  destruct H0.
  do 4 destruct H.
  destruct H0.
  destruct H1.
  pose proof alloc_locality_pre1.
  pose proof H5 x (x3, 0%Z) t x4 le le' x1 Ms x7 Mf M M' x0 H2 H6 H H1 H13; clear H5.
  destruct H7.
  destruct H5.
  assert (exists Mx, join x5 Ms Mx /\ join x7 x0 Mx).
  eapply join_join_join_exists; eauto.
  
  do 2 destruct H8.
  do 2 eexists.
  split.
  eapply inapi_step; eauto.
  eapply ostc_step; eauto.
  eapply stmt_step; eauto.
  eapply salloclv_step; eauto.
  split.
  unfolds.
  do 6 eexists.
  split; auto.
  split; auto.
  apply H8.
  split.
  unfolds.
  do 6 eexists.
  split; auto.
  split; auto.
  clear - H1 H6 H9.
  join auto.
  simpl; auto.

  do 2 eexists.
  split.
  eapply inapi_step; eauto.
  eapply ostc_step; eauto.
  eapply stmt_step; eauto.
  eapply sallocend_step; eauto.
  split.
  unfolds.
  do 6 eexists.
  split.
  auto.
  split.
  auto.
  eauto.
  split.
  unfolds.
  do 6 eexists.
  split.
  auto.
  split.
  auto.
  auto.
  simpl.
  auto.
Qed.

Lemma dl_add_nil_eq:
  forall dl, dl_add dl dnil =dl.
Proof.
  intros.
  induction dl.
  auto.
  unfold dl_add.
  unfold dl_add in IHdl.
  rewrite IHdl.
  auto.
Qed.

Lemma dladd_revlcons_eq:
  forall d1 d2, dladd d1 d2 = revlcons d1 d2.
Proof.
  intros.
  inductions d1; inductions d2; simpl; auto.  
Qed.

Fixpoint asrt_add_cell_to_tail (cell p:asrt):=
  match p with 
    | Aemp =>  (cell ** Aemp)
    | p1 ** p2 => (p1 ** (asrt_add_cell_to_tail cell p2))
    | _ => p ** cell
  end.

Lemma asrt_add_cell_to_tail_pqr:
  forall p q r,
    p ** (asrt_add_cell_to_tail q r) = asrt_add_cell_to_tail q (p ** r).
Proof.
  intros.
  induction r;simpl;auto.
Qed.

Lemma dl_add_move :
  forall dl' dl d1 d2 i t, dl_add dl' (dcons i t dl) = revlcons d1 d2 -> dl_add (dl_add dl' (dcons i t dnil)) dl = revlcons d1 d2.
Proof.
  intros.
  rewrite <- H; clear.
  gen dl' dl i t.
  induction dl', dl; intros; simpl in *; auto.
  rewrite IHdl'; auto.
  rewrite IHdl'; auto.
Qed.

Lemma buildp_add_v:
  forall dl' vl' p i t v,
    good_decllist (dl_add dl' (dcons i t dnil))= true ->
    length_eq vl' dl' -> buildp dl' vl' = Some p ->
    buildp (dl_add dl' (dcons i t dnil)) (vl'++v::nil) = Some ( asrt_add_cell_to_tail (Alvarmapsto i t true v) p).
Proof.
  induction dl'.
  intros.
  simpl in H1.
  destruct vl';tryfalse.
  inversion H1;subst p.
  simpl.
  auto.
  induction vl'.
  intros.
  simpl in H0.
  false.
  intros.
  simpl.
  simpl in H;rewrite H.
  assert (exists a,buildp dl' vl' = Some a).
  simpl in H1.
  destruct ( negb (in_decllist i dl') && good_decllist dl');tryfalse.
  destruct (buildp dl' vl');tryfalse.
  exists a0;auto.
  destruct H2.
  assert ( buildp (dl_add dl' (dcons i0 t0 dnil)) (vl' ++ v :: nil) =
           Some (asrt_add_cell_to_tail (Alvarmapsto i0 t0 true v) x)).
  apply IHdl'.
  apply andb_true_iff in H;destruct H;auto.
  simpl in H0;auto.
  auto.
  rewrite H3.
  simpl in H1.
  destruct ( negb (in_decllist i dl') && good_decllist dl');tryfalse.
  rewrite H2 in H1.
  inversion H1;subst p.
  assert (Alvarmapsto i t true a ** asrt_add_cell_to_tail (Alvarmapsto i0 t0 true v) x = asrt_add_cell_to_tail (Alvarmapsto i0 t0 true v) (Alvarmapsto i t true a ** x));rewrite asrt_add_cell_to_tail_pqr;auto.
Qed.

Lemma buildp_add:
  forall dl' vlh p i t,
    good_decllist (dl_add dl' (dcons i t dnil))=true ->
    buildp dl' vlh = Some p ->
    buildp (dl_add dl' (dcons i t dnil)) vlh = Some ( asrt_add_cell_to_tail (EX v : val, Alvarmapsto i t true v) p).
Proof.
  induction dl'.
  intros.
  simpl in H0.
  destruct vlh;tryfalse.
  inversion H0;subst p.
  simpl.
  auto.
  induction vlh.
  intros.
  assert (exists p',buildp dl' nil =Some p').
  simpl in H.
  simpl in H0.
  destruct (negb (in_decllist i dl') && good_decllist dl');tryfalse.
  destruct (buildp dl' nil);tryfalse.
  exists a;auto.
  destruct H1.
  assert (buildp (dl_add dl' (dcons i0 t0 dnil)) nil =
          Some (asrt_add_cell_to_tail (EX v : val, Alvarmapsto i0 t0 true v) x)).
  apply IHdl';auto.
  simpl in H.
  apply andb_true_iff in H;destruct H;auto.
  simpl.
  simpl in H;rewrite H.
  rewrite H2.
  simpl in H0.
  destruct (negb (in_decllist i dl') && good_decllist dl');tryfalse.
  rewrite H1 in H0.
  inversion H0;subst p.
  rewrite <- asrt_add_cell_to_tail_pqr;auto.
  intros.
  simpl in H.
  simpl.
  rewrite H.
  assert (exists p',buildp dl' vlh = Some p' ).
  simpl in H0.
  destruct (negb (in_decllist i dl') && good_decllist dl');tryfalse.
  destruct ( buildp dl' vlh);tryfalse.
  exists a0;auto.
  destruct H1.
  simpl in H0.
  destruct (negb (in_decllist i dl') && good_decllist dl');tryfalse.
  rewrite H1 in H0.
  inversion H0;subst p.
  assert (buildp (dl_add dl' (dcons i0 t0 dnil)) vlh =
          Some (asrt_add_cell_to_tail (EX v : val, Alvarmapsto i0 t0 true v) x)).
  apply IHdl';auto.
  apply andb_true_iff in H;destruct H;auto.
  rewrite H2.
  rewrite <- asrt_add_cell_to_tail_pqr;auto.
Qed.

Lemma good_dl_add:
  forall d1 d2 dl' i t dl,
    good_decllist (revlcons d1 d2) = true ->
    dl_add dl' (dcons i t dl) = revlcons d1 d2 ->
    good_decllist (dl_add dl' (dcons i t dnil)) =true.
Proof.
  intros.
  rewrite <- H0 in H.
  clear -H.
  induction dl'.
  simpl.
  auto.
  simpl.
  simpl in H.
  apply andb_true_iff in H.
  destruct H.
  apply andb_true_iff.
  split.
  clear -H.
  induction dl'.
  simpl in H.
  simpl.
  rewrite negb_orb.
  apply andb_true_iff.
  split;auto.
  rewrite negb_orb in H.
  apply andb_true_iff in H.
  destruct H;auto.
  simpl.
  simpl in H.
  rewrite negb_orb in H.
  rewrite negb_orb.
  apply andb_true_iff.
  apply andb_true_iff in H.
  destruct H.
  split;auto.
  auto.
Qed.

Lemma addtail_length_eq:
  forall vl' dl' v x t,length_eq vl' dl' ->  length_eq (vl' ++ v :: nil) (dl_add dl' (dcons x t dnil)).
Proof.
  intros.
  gen vl' dl' v x t.
  induction vl', dl'; intros; simpl in *; tryfalse || auto.
Qed.

Open Scope nat_scope.
Ltac sassocrH H :=
  match type of H with
    | _ |= (_ ** _) ** _ => sep assocr in H; sassocrH H
    | _ => idtac
  end.
Ltac sassoclH H :=
  match type of H with
    | _ |= _ ** (_ ** _) => sep assocl in H; sassoclH H
    | _ => idtac
  end.
Ltac sassocr :=
  match goal with
    | |- _ |= (_ ** _) ** _ => sep assocr; sassocr
    | _ => idtac
  end.
Ltac sassocl :=
  match goal with
    | |- _ |= _ ** (_ ** _) => sep assocl; sassocl
    | _ => idtac
  end.
Ltac scommH H :=
  match type of H with
    | _ |= _ ** _ => sep comm in H
    | _ => idtac
  end.
Ltac scomm :=
  match goal with
    | |- _ |= _ ** _ => sep comm
    | _ => idtac
  end.

Ltac slift n :=
  match eval compute in n with
    | 0 => fail
    | 1 => sassocr
    | S ?n' => sassocr; scomm; slift n'
  end.
Ltac sliftH H n :=
  match eval compute in n with
    | 0 => fail
    | 1 => sassocrH H
    | S ?n' => sassocrH H; scommH H; sliftH H n'
  end.

Ltac hypSearch' Hp Assn :=
  match Hp with
    | ?A ** ?B => match hypSearch' A Assn with
                   | some ?l => constr:(some l)
                   | none ?l => match hypSearch' B Assn with
                                  | some ?r => constr:(some (l+r))
                                  | none ?r => constr:(none (l+r))
                                end
                 end
    | Assn => constr:(some 1)
    | _ => constr:(none 1)
  end.

Ltac hypSearch Hp Assn :=
  let x := hypSearch' Hp Assn in
  eval compute in x.

Theorem StarComm : 
  forall P Q,
    P ** Q ==> Q ** P.
Proof.
  intros.
  simpl in *.
  mytac.
  do 6 eexists; mytac.
  5 : eauto.
  5 : eauto.
  auto.
  2 : auto.
  apply join_comm; auto.
  apply OSAbstMod.join_comm; auto.
Qed.

Theorem StarEmpIL :
  forall P, P ==> Aemp ** P.
Proof.
  intros.
  destruct_s s.
  simpl in *.
  do 6 eexists; mytac; eauto.
Qed.

Theorem StarEmpIR : 
  forall P, P ==> P ** Aemp.
Proof.
  intros.
  apply StarComm.
  apply StarEmpIL; auto.
Qed.

Theorem StarEmpEL : 
  forall P, Aemp ** P ==> P.
Proof.
  intros.
  destruct_s s.
  simpl in H; mytac.
  auto.
Qed.

Theorem StarEmpER : 
  forall P, P ** Aemp ==> P.
Proof.
  intros.
  apply StarComm in H.
  apply StarEmpEL in H; auto.
Qed.


Ltac listgoalSearch' lg Hp n :=
  match lg with
    | nil => constr:(@None)
    | ?a :: ?lg' => match hypSearch Hp a with
                      | some _ => constr:(Some n)
                      | _ => listgoalSearch' lg' Hp (S n)
                    end
  end.

Ltac listgoalSearch lg Hp := listgoalSearch' lg Hp 1.


Ltac asrt2list' Hp l :=
  match Hp with
    | ?A ** ?B => let rl := asrt2list' B l in
                 asrt2list' A rl
    | ?A => constr:(A :: l)
  end.

Ltac asrt2list Hp := asrt2list' Hp (@nil asrt).

Ltac goalSearch G Hp :=
  let lg := asrt2list G in
  let x := listgoalSearch lg Hp in
  eval compute in x.

Theorem StarMono : 
  forall P Q P' Q',
    P ==> P' -> Q ==> Q' -> P ** Q ==> P' ** Q'.
Proof.
  intros.
  simpl in *.
  mytac.
  do 6 eexists; mytac; eauto.
Qed.

Ltac sauto' :=
  slift 1;
  let s' := fresh in
  let H' := fresh in
  match goal with
    | H : ?s |= ?A |- ?s |= ?A => exact H
    | H : ?s |= ?X |- ?s |= ?Y =>
      match X with
        | ?A ** ?B =>
          match Y with
            | A ** ?D =>
              apply StarMono with (P:=A) (Q:=B);
                [intros s' H'; exact H' | idtac | exact H];
                first [ clear s H; intros s H 
                      | clear H; first [intros s' H | intros H]];
                sliftH H 1; sauto'
            | ?C ** ?D =>
              match hypSearch B C with
                | some ?n => sliftH H (S n); sauto'
                | none _ => match goalSearch D (A ** B) with
                              | Some ?m => slift (S m); sauto'
                              | @None => idtac
                            end
              end
            | A => apply StarEmpER; sauto'
            | ?C => match hypSearch B C with
                      | some ?n => sliftH H (S n); sauto'
                      | none _ => idtac
                    end
          end
        | ?A =>
          match Y with
            | A ** ?C => apply StarEmpIR in H; sauto'
            | ?B ** ?C => match hypSearch C A with
                           | some ?n => slift (S n); sauto'
                           | _ => idtac
                         end
            | ?B => idtac
          end
      end
    | _ => fail
  end.

Ltac hypSearch_Aemp' Hp :=
  match Hp with
    | ?A ** ?B => match hypSearch_Aemp' A with
                      | some ?l => constr:(some l)
                      | none ?l => match hypSearch_Aemp' B with
                                     | some ?r => constr:(some (l+r))
                                     | none ?r => constr:(none (l+r))
                                   end
                    end
    | Aemp => constr:(some 1)
    | _ => constr:(none 1)
  end.

Ltac hypSearch_Aemp Hp :=
  let x := hypSearch_Aemp' Hp in
  eval compute in x.


Ltac sclearAempH H :=
  match type of H with
    | ?s |= ?A => match hypSearch_Aemp A with
                     | some ?n => sliftH H n;
                                 apply StarEmpEL in H; sclearAempH H
                     | _ => idtac
                   end
    | _ => fail
  end.

Ltac sclearAemp :=
  match goal with
    | |- ?s |= ?A => match hypSearch_Aemp A with
                        | some ?n => slift n;
                                    apply StarEmpIL; sclearAemp
                        | _ => idtac
                      end
    | _ => fail
  end.

Ltac sauto :=
  match goal with
    | H : ?s |= _ |- ?s |= _ =>
      sliftH H 1; sauto';
      match goal with
        | |- _ |= _ => sclearAempH H; sclearAemp
        | _ => idtac
      end
    | _ => idtac
  end.


Lemma asrt_add_cell_to_tail_sateq_star:
  forall p q ge le M i au O ab,   
    (ge, le, M, i, au, O, ab) |= p ** q ->
    (ge, le, M, i, au, O, ab) |= (asrt_add_cell_to_tail p q).
Proof.
  induction q;unfold asrt_add_cell_to_tail;intros;fold asrt_add_cell_to_tail; sauto.
  destruct H0.
  destruct r.
  destruct t.
  destruct p0.
  destruct s.
  destruct p0.
  eapply IHq2.
  sauto.
Qed.

Lemma fresh_join :
  forall M x m1 m2,
    fresh M x ->
    join m1 m2 M ->
    fresh m1 x.
Proof.
  intros.
  unfold fresh in H.
  unfold fresh.
  intros.
  apply H in H1.
  intro.
  apply H1.
  unfolds.
  unfolds in H2.
  destruct H2.
  destruct x0.
  lets Hx: mem_join_get_get_l H0 H2; simpljoin.
  eauto.
Qed.

Lemma allocb_minus :
  forall len M m1 m2 b i,
    fresh M b -> join m1 m2 M ->
    minus (allocb M b i len) m2 = allocb m1 b i len.
Proof.
  intro.
  induction len; intros.
  simpl.
  eapply extensionality.
  intro.
  eapply mem_join_minus_get; auto.
    
  simpl.
  assert (~ indom m2 (b, i)).
  apply join_sub_r in H0.
  unfolds in H.
  assert ((b, i) = (b, i)).
  auto.
  pose proof (H (b, i) i H1). clear H1.
  intro.
  apply H2.
(* ** ac:   Check indom_sub_indom. *)
  Lemma indom_sub_indomp :
    forall (A B T : Type) (MC : PermMap A B T) m1 m2 a,
      usePerm = true ->
      indom m1 a ->
      Maps.sub m1 m2 ->
      indom m2 a.
    intros.
    indom_rewrite.
    unfold indom.
    infer' (pnil, Maps.sub m1 m2) a.
    exists x; auto.
    exists (flip x); auto.
    (** TODO **)
  Qed.

  eapply indom_sub_indomp; auto.
  apply H1.
  auto.
  rewrite mem_minus_set_comm.
  erewrite IHlen; auto.
  auto.
Qed.

Lemma alloc_minus_mem :
  forall i t le M le' M' m1 m2,
    alloc i t le M le' M' ->
    join m1 m2 M ->
    alloc i t le m1 le' (minus M' m2).
Proof.
  intros.
  unfolds in H; mytac.
  unfolds.
  eexists.
  split.
  eapply fresh_join.
  apply H.
  apply H0.
  split.
  clear H2. clears.
  erewrite allocb_minus; auto.
  split; auto.
Qed.

Lemma storebytes_minus :
  forall m1 m2 M M' M'' i t le le' b o v,
    join m1 m2 M ->
    alloc i t le M le' M' ->
    EnvMod.get le' i = Some (b, t) ->
    storebytes M' (b, o) (encode_val t v) = Some M'' ->
    storebytes (minus M' m1) (b, o) (encode_val t v) = Some (minus M'' m1).
Proof.
  intros.
  gen m1 m2 M M' M'' i le le' b o.
  induction (encode_val t v); intros.
  simpl.
  simpl in H2.
  inv H2.
  auto.

  simpl in H2.
  unfold get in *; simpl in *.
  destruct (HalfPermMap.get M' (b, o)) eqn : eq1; tryfalse.
  destruct b0.
  destruct b0; tryfalse.
  destruct (storebytes M' (b, (o + 1)%Z) l) eqn : eq2; tryfalse.
  pose proof (IHl m1 m2 M H M' m i le le' H0 b H1 (o + 1)%Z eq2). clear IHl.
  simpl.
  unfold get; simpl.
  destruct (HalfPermMap.get (minus M' m1) (b, o)) eqn : eq3.
  change offset with Z in H3.
  rewrite H3.
  destruct b0.

  assert (HalfPermMap.get (minus M' m1) (b, o) = Some (true, c)) as Hxx.
  assert (get m1 (b, o) = None).
  unfolds in H0; simpljoin.
  rewrite EnvMod.set_a_get_a in H1; inverts H1.
  unfolds in H0.
  pose proof H0 (b, o) o.
  assert ((b, o) = (b, o)) by auto.
  apply H1 in H4; clear H1.
  destruct (get m1 (b, o)) eqn : eq4; auto.
  false; apply H4.
  unfolds.
  destruct p.
  clear - H eq4.
  lets Hx: mem_join_get_get_l H eq4.
  destruct Hx.
  eauto.
  apply identspec.eq_beq_true; auto.

  eapply mem_get_minus_get; auto.
  rewrite eq3 in Hxx; inverts Hxx.
  inv H2.
  assert (set (minus m m1) (b, o) (true, a) = minus (set m (b, o) (true, a)) m1).
  eapply extensionality.
  intro.
  destruct (addr_eq_dec (b, o) a0) eqn : eq4.
  substs.
  rewrite set_a_get_a.
  rewrite minus_semp; auto.
  rewrite set_a_get_a.
  unfolds in H0; simpljoin.
  rewrite EnvMod.set_a_get_a in H1; inverts H1.
  unfolds in H0.
  pose proof H0 (b, o) o.
  assert ((b, o) = (b, o)) by auto.
  apply H1 in H2.
  unfolds in H2.
  assert (get m1 (b, o) = None ) as Hxx1.
  destruct (get m1 (b, o)) eqn : eqx; auto.
  false; apply H2.
  unfolds.
  clear - H eqx.
  destruct p.
  lets Hx: mem_join_get_get_l H eqx.
  destruct Hx; eauto.
  unfold get in *; simpl in *.
  rewrite Hxx1; auto.
  apply identspec.eq_beq_true; auto.
  
  rewrite set_a_get_a'.
  rewrite minus_semp; auto.
  rewrite minus_semp; auto.
  rewrite set_a_get_a'.
  auto.
  auto.
  auto.
  unfold set in *; simpl in *.
  rewrite H2.
  auto.

  false.
  unfolds in H0; mytac.
  rewrite EnvMod.set_a_get_a in H1.
  inv H1.

(* ** ac:   Check minus_semp. *)
  generalize (@minus_semp _ _ _ memMap); intro Hxx.
  rewrite Hxx in eq3; clear Hxx.
  2:auto.
  unfold get in *; simpl in *.
  rewrite eq1 in eq3.
  apply join_sub_l in H.
  destruct (HalfPermMap.get m1 (b, o)) eqn : eq4; tryfalse.
  unfolds in H0.
  assert ((b, o) = (b, o)).
  auto.
  pose proof (H0 (b, o) o H1).
  assert (indom M (b, o)).
  {
    eapply indom_sub_indomp; auto.
    unfold indom.
    unfold get.
    simpl.
    exists b0.
    apply eq4.
    auto.
  }
  
  auto.
  apply identspec.eq_beq_true.
  auto.
Qed.

Lemma alloc_le_sat:
  forall i t  le M le' M' dl',
    eq_dom_env le (getlenvdom dl') ->
    alloc i t le M le' M' ->
    eq_dom_env le' (getlenvdom (dl_add dl' (dcons i t dnil))).
Proof.
  intros.
  unfolds in H0; mytac.
  unfolds.
  intros.
  destruct (identspec.beq i x0) eqn : eq1.
  apply identspec.beq_true_eq in eq1.
  subst.
  split; intros.

  assert (~ (ListSet.set_In (x0, t0) (getlenvdom dl'))).
  intro.
  apply H2.
  unfolds in H.
  pose proof H x0 t0. clear H.
  apply H4 in H3. clear H4.
  destruct H3.
  unfolds.
  eexists.
  apply H.
  clear H H0 H2. clears.
  rewrite EnvMod.set_a_get_a.
  gen t le x x0 t0.
  inductions dl'; intros.
  simpl in H1.
  destruct H1; tryfalse.
  inverts H.
  eexists.
  auto.
  simpl in H1.
  destruct H1.
  inverts H.
  false.
  apply H3.
  simpl.
  left.
  auto.
  assert (~ ListSet.set_In (x0, t1) (getlenvdom dl')).
  intro.
  apply H3.
  simpl.
  right.
  auto.
  eapply IHdl'; eauto.
  apply identspec.eq_beq_true.
  auto.
  rewrite EnvMod.set_a_get_a in H1.
  destruct H1.
  inverts H1.
  clear H H0 H2. clears.
  inductions dl'; intros.
  simpl. left. auto.
  simpl. right. apply IHdl'.
  apply identspec.eq_beq_true.
  auto.

  split; intros.
  assert (ListSet.set_In (x0, t0) (getlenvdom dl')).
  clear H H0 H2. clears.
  gen i t x0 t0.
  inductions dl'; intros.
  simpl in H1.
  destruct H1.
  inverts H.
  apply identspec.beq_false_neq in eq1.
  false.
  false.
  simpl in H1.
  destruct H1.
  inverts H.
  simpl.
  left.
  auto.
  simpl.
  right.
  eapply IHdl'; eauto.
  rewrite EnvMod.set_a_get_a'.
  unfolds in H.
  pose proof H x0 t0.
  apply H4 in H3.
  destruct H3.
  eexists.
  apply H3.
  auto.

  rewrite EnvMod.set_a_get_a' in H1.
  unfolds in H.
  pose proof H x0 t0. clear H.
  apply H3 in H1. clear H3.
  clear H0 H2. clears.
  inductions dl'.
  simpl in H1.
  false.
  simpl in H1.
  destruct H1.
  inverts H.
  simpl.
  left.
  auto.
  simpl.
  right.
  eapply IHdl'; eauto.
  auto.
Qed.


Lemma buildp_le_mono :
  forall dl vl P ge le lex le' M ir au O ab,
    buildp dl vl = Some P ->
    (ge, le, M, ir, au, O, ab) |= P ->
    join le lex le' ->
    (ge, le', M, ir, au, O, ab) |= P.
Proof.
  inductions dl; intros.
  simpl in H.
  destruct vl.
  inverts H.
  simpl; auto.
  tryfalse.

  destruct vl.
  unfold buildp in H; fold buildp in H.
  destruct (good_decllist (dcons i t dl));
    destruct (buildp dl nil) eqn : eq1; tryfalse.
  inverts H.
  remember (EX v : val, LV i @ t |-> v) as X.
  simpl in H0; simpljoin.
  remember (EX v : val, LV i @ t |-> v) as X.
  simpl.
  do 6 eexists; splits; eauto.
  substs.
  simpl in H4; simpljoin.
  simpl.
  do 8 eexists; splits; eauto.
  exists x11.
  splits; auto.
  clear - H7 H1.
  jeat.

  unfold buildp in H; fold buildp in H.
  destruct (good_decllist (dcons i t dl));
    destruct (buildp dl vl) eqn : eq1; tryfalse.
  inverts H.
  remember (LV i @ t |-> v) as X.
  simpl in H0; simpljoin.
  remember (LV i @ t |-> v) as X.
  simpl.
  do 6 eexists; splits; eauto.
  substs.
  simpl in H4; simpljoin.
  simpl.
  do 7 eexists; splits; eauto.
  exists x10.
  splits; auto.
  clear - H7 H1.
  jeat.
Qed.

Lemma alloc_store_sat:
  forall ge le le' i t M M' M'' ir au O ab p b v dl vl lasrt tid,
    buildp dl vl = Some p ->
    alloc i t le M le' M' ->
    EnvMod.get le' i = Some (b, t) ->
    storebytes M' (b, 0%Z) (encode_val t v) = Some M'' ->
    (ge, le, M, ir, au, O, ab) |= p ** p_local lasrt tid init_lg ->
    (ge, le', M'', ir, au, O, ab) |= (Alvarmapsto i t true v) ** p ** p_local lasrt tid init_lg.
Proof.
  intros.
  lets Hx: lmachLib.alloc_store_exist_mem_env H0 H1 H2.
  simpljoin.
  remember (p ** p_local lasrt tid init_lg) as X.
  sep lift 2%nat.
  simpl.
  do 6 eexists; splits; eauto.
  apply join_comm.
  apply join_emp; eauto.

  substs.
  remember (p_local lasrt tid init_lg) as Q.
  simpl in H3; simpljoin.
  remember (p_local lasrt tid init_lg) as Q.
  simpl.
  do 6 eexists; splits; eauto.
  eapply buildp_le_mono; eauto.
  substs.
  simpl in H11.
  simpljoin.
  simpl.
  do 6 eexists; splits; eauto.
  do 8 eexists; splits; eauto.
  do 6 eexists; splits; eauto.
  eapply GoodLInvAsrt_change_lenv; eauto.
  unfolds in H19.
  apply H19.
  do 7 eexists; splits; eauto.
  apply join_emp; auto.
  apply join_emp; eauto.
  exists b.
  splits; eauto.
  unfolds; auto.
  unfolds; auto.
Qed.


Lemma  alloc_v_step_asrt': 
  forall ge le le' M'' b M' M i0 au O ab p dl' x t v vl lasrt tid,
    buildp dl' vl = Some p ->
    (ge, le, M, i0, au, O, ab)
      |= (p ** p_local lasrt tid init_lg ** Aie true ** Ais nil ** Acs nil ** Aisr empisr) **
      A_dom_lenv (getlenvdom dl') ->
    alloc x t le M le' M' ->
    EnvMod.get le' x = Some (b, t) ->
    store t M' (b, 0%Z) v = Some M'' ->
    (ge, le', M'', i0, au, O, ab)
      |= (( asrt_add_cell_to_tail (Alvarmapsto x t true v) p) **
         p_local lasrt tid init_lg ** Aie true ** Ais nil ** Acs nil ** Aisr empisr) ** A_dom_lenv (getlenvdom (dl_add dl' (dcons x t dnil))).
Proof.
  intros.
  sep normal in H0.
  sep remember (3::4::5::6::7::nil)%nat in H0.
  sep normal.
  simpl in H0; mytac.
  destruct au, p0.
  sep remember (3::4::5::6::7::nil)%nat.
  simpl.
  substs.
  do 5 (
  exists empmem M'' M'' empabst O O;
  splits; eauto;
  try solve [apply join_emp; auto];
  try (unfold emposabst; splits; auto)).
  eapply alloc_le_sat; eauto.
  lets Hx: alloc_store_sat H H1 H2 H3 H29.
  sep cancel 3%nat 2%nat.
  destruct_s H0.
  eapply asrt_add_cell_to_tail_sateq_star; auto.
Qed.


Lemma alloc_sat :
  forall ge le le' i t M M' ir au O ab p dl vl lasrt tid,
    buildp dl vl = Some p ->
    alloc i t le M le' M' ->
    (ge, le, M, ir, au, O, ab) |= p ** p_local lasrt tid init_lg ->
    (ge, le', M', ir, au, O, ab) |= (EX v : val, Alvarmapsto i t true v) ** p ** p_local lasrt tid init_lg.
Proof.
  intros.
  lets Hx: alloc_exist_mem_env H0.
  simpljoin.
  remember (p ** p_local lasrt tid init_lg) as X.
  sep lift 2%nat.
  simpl.
  do 6 eexists; splits; eauto.
  apply join_comm.
  apply join_emp; eauto.

  substs.
  remember (p_local lasrt tid init_lg) as Q.
  simpl in H1; simpljoin.
  remember (p_local lasrt tid init_lg) as Q.
  simpl.
  do 6 eexists; splits; eauto.
  eapply buildp_le_mono; eauto.
  substs.
  simpl in H9.
  simpljoin.
  simpl.
  do 6 eexists; splits; eauto.
  do 8 eexists; splits; eauto.
  do 6 eexists; splits; eauto.
  eapply GoodLInvAsrt_change_lenv; eauto.
  apply H17.
  do 8 eexists; splits; eauto.
  apply join_emp; auto.
  apply join_emp; eauto.
  exists x1.
  splits; eauto.
  clear - H5.
  jeat.
  unfolds; auto.
  unfolds; auto.
Qed.


Lemma  alloc_step_asrt: 
  forall p ge le le' M' M i0 au O ab dl' i t vl lasrt tid,
    buildp dl' vl = Some p ->
    (ge, le, M, i0, au, O, ab)
      |= (p ** p_local lasrt tid init_lg ** Aie true ** Ais nil ** Acs nil ** Aisr empisr) **
      A_dom_lenv (getlenvdom dl') ->
    alloc i t le M le' M' ->
    (ge, le', M', i0, au, O, ab)
      |= ((asrt_add_cell_to_tail (EX v : val, Alvarmapsto i t true v) p ) **
         p_local lasrt tid init_lg ** Aie true ** Ais nil ** Acs nil ** Aisr empisr )**
      A_dom_lenv (getlenvdom (dl_add dl' (dcons i t dnil))).
Proof.
  intros.
  sep normal in H0.
  sep remember (3::4::5::6::7::nil)%nat in H0.
  sep normal.
  simpl in H0; mytac.
  destruct au, p0.
  sep remember (3::4::5::6::7::nil)%nat.
  simpl.
  substs.
  do 5 (
  exists empmem M' M' empabst O O;
  splits; eauto;
  try solve [apply join_emp; auto];
  try (unfold emposabst; splits; auto)).
  eapply alloc_le_sat; eauto.
  lets Hx: alloc_sat H H1 H27.
  sep cancel 3%nat 2%nat.
  destruct_s H0.
  eapply asrt_add_cell_to_tail_sateq_star; auto.
Qed.


Lemma list_move:
  forall vl' (v:val) vl, vl'++(v::vl)= (vl'++v::nil)++vl.
Proof.
  intros; simpl.
  rewrite app_assoc_reverse.
  simpl; auto.
Qed.


Lemma buildp_add_nil:
  forall vl' p i t v,
    length_eq vl' dnil ->
    buildp dnil vl' = Some p ->
    buildp (dl_add dnil (dcons i t dnil)) (vl'++v::nil) = Some ( Alvarmapsto i t true v ** p).
Proof.
  intros.
  destruct vl'; tryfalse.
  simpl in H0.
  inverts H0.
  simpl.
  auto.
Qed.


Lemma alloc_trans :
  forall (pc : progunit)
         (po : fid -> option (type * decllist * decllist * stmts))
         (pi : progunit) (ip : intunit) (f : fid) (ft : type)
         (d1 d2 : decllist) (s : stmts) (vlh : list val) 
         tid (o o' : taskst) (O : osabst)
         (cst cst' : clientst) (C' : code) (ks : stmtcont) 
         (vl : list val) (dl : decllist) lasrt,
    po f = Some (ft, d1, d2, s) ->
    good_decllist (revlcons d1 d2) = true ->
    (exists dl' vl' p,
       (vl <> nil -> length_eq vl' dl') /\
       dl_add dl' dl = revlcons d1 d2 /\
       vl' ++ vl = vlh /\
       buildp dl' vl' = Some p /\
       (forall ab : absop,
          (o, O, ab)
            |= (p ** p_local lasrt tid init_lg** Aie true ** Ais nil ** Acs nil ** Aisr empisr) **
            A_dom_lenv (getlenvdom dl'))) ->
    ltstep (pc, (po, pi, ip)) tid
           (curs (salloc vl dl), (kenil, kcall f s empenv ks)) cst o C' cst' o' ->
    cst' = cst /\
    (exists dl'' vl'' p dl''' vl''',
       C' = (curs (salloc vl'' dl''), (kenil, kcall f s empenv ks)) /\
       dl_add dl''' dl'' = revlcons d1 d2 /\
       vl''' ++ vl'' = vlh /\
       buildp dl''' vl''' = Some p /\
       (vl <> nil -> length_eq vl''' dl''') /\
       ~ (vl = nil /\ dl = dnil) /\
       (forall ab : absop,
          (o', O, ab)
            |= (p ** p_local lasrt tid init_lg ** Aie true ** Ais nil ** Acs nil ** Aisr empisr) **
            A_dom_lenv (getlenvdom dl'''))) \/
    cst' = cst /\
    (exists p,
       C' = (curs s, (kenil, kcall f s empenv ks)) /\
       vl = nil /\
       dl = dnil /\
       buildp (dladd d1 d2) vlh = Some p /\
       (forall ab : absop,
          (o', O, ab)
            |= (p ** p_local lasrt tid init_lg ** Aie true ** Ais nil ** Acs nil ** Aisr empisr) **
            A_dom_lenv (getlenvdom (dladd d1 d2)))).
Proof.
  introv H.
  intro Hgooddl.
  intros.
  assert (InOS (curs (salloc vl dl), (kenil, kcall f s empenv ks)) (pumerge po pi)).
  unfold InOS.
  do 3 eexists.
  splits;eauto.
  right.
  left.
  do 8 eexists;splits;simpl;eauto.
  eapply pumerge_get.
  eauto.
  destruct vl.
  destruct dl.
  right.

  inversion H1;subst;tryfalse.
  splits;auto.
  destruct H0 as (dl'&vl'&p&Hf&Hf1&Hf2&Hf3&Hf4).
  exists p.
  inversion H3;subst pc0 po0 pi0 ip0.

  inversion H4;subst;tryfalse.
  inversion H0;subst;tryfalse.
  inversion H7;tryfalse.
  inversion H7;subst;tryfalse.
  inversion H6.
  subst f0 s0 E ks1.
  auto.

  rewrite dl_add_nil_eq in Hf1.
  rewrite dladd_revlcons_eq.
  subst dl'.
  splits;auto.
  rewrite List.app_nil_r.
  auto.
  (*------------------------------------*)
  inversion H1;tryfalse;subst.
  inversion H4;tryfalse;subst.
  inversion H6;tryfalse;subst.
  inversion H8;tryfalse.
  inversion H8;tryfalse;subst.
  inversion H7.
  left.
  subst x t0 dl0 ks'.
  destruct H0 as (dl'&vl'&p&Hf&Hf1&Hf2&Hf3&Hf4).
  rewrite List.app_nil_r in Hf2.
  subst vl'.
  inversion H3;subst pc0 po0 pi0 ip0.
  splits;auto.

  exists dl (nil:vallist) (asrt_add_cell_to_tail (EX v : val, Alvarmapsto i t true v) p) (dl_add dl' (dcons i t dnil)) vlh.
  splits;auto.
  eapply dl_add_move;eauto.
  apply List.app_nil_r.
  eapply buildp_add;eauto.
  eapply good_dl_add;eauto.
  intros;tryfalse.
  intro X.
  destruct X;tryfalse.
  auto.
  intros.
  eapply alloc_step_asrt;eauto.
  (*-----------------------------------*)
  inversion H1;tryfalse;subst.
  inversion H4;tryfalse;subst.
  inversion H6;tryfalse;subst.
  inversion H8;tryfalse.
  inversion H8;tryfalse;subst.
  inversion H7.
  subst v0 vl0 dl ks'.
  destruct H0 as (dl'&vl'&p&Hf&Hf1&Hf2&Hf3&Hf4).
  left.
  splits;auto.

  destruct dl'.
  exists dl0 vl (Alvarmapsto x t true v ** p). 
  exists (dl_add dnil (dcons x t dnil)) (vl'++(v::nil)).
  splits;auto.
  (*eapply dl_add_move;eauto.*)
  rewrite <- list_move.
  auto.
  eapply buildp_add_nil;eauto.
  intros.
  eapply addtail_length_eq;eauto.
  intro X.
  destruct X;tryfalse.
  intros.
  assert (buildp dnil vl' = Some p);auto.
  simpl in Hf3.
  destruct vl';tryfalse.
  inversion Hf3;subst p.
  assert (Alvarmapsto x t true v ** Aemp = asrt_add_cell_to_tail (Alvarmapsto x t true v) Aemp).
  simpl.
  auto.
  rewrite H9.
  eapply alloc_v_step_asrt' with (M':=M');eauto.

  exists dl0 vl (asrt_add_cell_to_tail (Alvarmapsto x t true v) p). 
  exists (dl_add (dcons i0 t0 dl') (dcons x t dnil)) (vl'++(v::nil)).
  splits;auto.
  eapply dl_add_move;eauto.
  rewrite <- list_move.
  auto.
  eapply buildp_add_v;eauto.
  eapply good_dl_add;eauto.
  intros.
  eapply addtail_length_eq;eauto.
  intro X.
  destruct X;tryfalse.
  intros.
  eapply alloc_v_step_asrt' with (M':=M');eauto.
Qed.

Lemma good_dl_le_step'
: forall (pc : progunit)
         (po : fid -> option (type * decllist * decllist * stmts))
         (pi : progunit) (ip : intunit) (f : fid) (ft : type)
         (d1 d2 : decllist) (s : stmts) (dl dl' : decllist) 
         (cst : clientst) (o : taskst) (cst' : clientst) 
         (o' : taskst) (le : env) (ks : stmtcont) t
         (vl' vl : vallist),
    po f = Some (ft, d1, d2, s) ->
    GoodStmt' s ->
    good_dl_le dl o ->
    ltstep (pc, (po, pi, ip)) t
           (curs (salloc vl dl), (kenil, kcall f s le ks)) cst o
           (curs (salloc vl' dl'), (kenil, kcall f s le ks)) cst' o' ->
    good_dl_le dl' o'.
Proof.
  intros.
  rename H0 into H100.
  rename H1 into H0.
  rename H2 into H1.
  inverts H1.

  inverts H2.
  inverts H3.
  inverts H11.
  inverts H12.
  inverts H9.
  inverts H11.
  inverts H6.
  inverts H9.
  simpl in H0.
  destruct H0.
  destruct H1.
  auto.
  inverts H10.
  inverts H12.
  simpl in H0.
  destruct H0.
  destruct H1.
  auto.
  false.
  inverts H2.
  (*loststep 2 cases*)
  inverts H3.
  (*cstep 2 cases*)
  inverts H1.
  (*1*)
  inverts H10.
  inverts H11.
  (*2*)
  inverts H8.
  inverts H10.
  (*sstep 3 cases*)
  (*1*)
  simpl in H0.
  destruct H0.
  destruct H1.
  apply andb_true_iff in H0.
  destruct H0.
  unfold alloc in H12.
  destruct H12.
  destruct H5.
  destruct H6.
  destruct H7.
  subst.
  clear H4 H13 H15 H1 H5 H7 H H3.
  clears.
  apply negb_true_iff in H0.
  induction dl'.
  simpl.
  auto.
  simpl in H0.
  apply orb_false_iff in H0.
  destruct H0.
  simpl in H2.
  destruct H2.
  destruct H2.
  apply IHdl' in H0.
  simpl.
  split.
  auto.
  split.
  intro.
  apply H2.
  unfold EnvMod.indom in H4.
  destruct H4.
  rewrite EnvMod.set_a_get_a' in H4.
  unfold EnvMod.indom.
  exists x1.
  auto.
  auto.
  auto.
  auto.
  (*2*)
  simpl in H0.
  destruct H0.
  destruct H1.
  unfold alloc in H13.
  destruct H13.
  destruct H3.
  destruct H5.
  destruct H6.
  clear H3 H5.
  subst. clear H6 H4 H.
  apply andb_true_iff in H0.
  destruct H0.
  clear H0.
  clears.
  apply negb_true_iff in H.
  induction dl'.
  simpl.
  auto.
  simpl in H.
  apply orb_false_iff in H.
  destruct H.
  simpl in H2.
  destruct H2.
  destruct H3.
  apply IHdl' in H0.
  simpl.
  split.
  auto.
  split.
  intro.
  apply H1.
  unfold EnvMod.indom in H5.
  destruct H5.
  rewrite EnvMod.set_a_get_a' in H5.
  false.
  apply H3.
  unfolds.
  exists x1.
  auto.
  auto.
  auto.
  auto.
  (*3*)
  unfold GoodStmt' in H100.
  false.
  (*loststep case 2*)
  inverts H10.
Qed.


Lemma tstep_alloc_nabt
: forall
    (p : progunit *
         ((fid -> option (type * decllist * decllist * stmts)) *
          progunit * intunit)) t 
    (vl : list val) (dl : decllist) (ks : stmtcont) 
    (cst : clientst) (o : taskst) (d1 d2 : decllist) 
    (f : fid) (s : stmts) (le : env) (ft : type),
    vl = nil \/ (exists i t0 dl', dl = dcons i t0 dl') ->
    fst (fst (snd p)) f = Some (ft, d1, d2, s) ->
    good_dl_le dl o ->
    ~ ltstepabt p t (curs (salloc vl dl), (kenil, kcall f s le ks)) cst o.
Proof.
  intros.
  destruct p.
  destruct p0.
  destruct p0.
  simpl in H0.
  destruct o. destruct p1.
  destruct s0. destruct p1.
  pose proof (fresh_exist m) as H100.
  destruct H100.
  rename H2 into H100.
  destruct H.
  subst.

  intro.
  inverts H.
  inverts H2.
  apply H3. clear H3.
  left.
  destruct dl.
  do 3 eexists.
  eapply inapi_step; eauto.
  eapply ostc_step; eauto.
  eapply stmt_step; eauto.
  eapply sallocend_step.
  unfold InOS.
  do 3 eexists.
  split.
  eauto.
  right.
  left.
  do 8 eexists.
  split.
  simpl.
  eauto.
  unfold pumerge.
  rewrite H0.
  eauto.

  do 3 eexists.
  eapply inapi_step; eauto.
  eapply ostc_step; eauto.
  eapply stmt_step; eauto.
  eapply salloclv_step; eauto.
  unfold alloc.
  eexists.
  split.
  eauto.
  split.
  eauto.
  split.
  simpl in H1.
  destruct H1.
  destruct H1.
  auto.
  eauto.
  unfold InOS.
  do 3 eexists.
  split.
  eauto.
  right.
  left.
  do 8 eexists.
  split.
  simpl.
  eauto.
  unfold pumerge.
  rewrite H0.
  eauto.

  do 3 destruct H.
  subst.
  intro.
  inverts H.
  apply H3. clear H3.
  inverts H2.
  left.
  destruct vl.
  do 3 eexists.
  eapply inapi_step; eauto.
  eapply ostc_step; eauto.
  eapply stmt_step; eauto.
  eapply salloclv_step; eauto.
  unfold alloc.
  eexists.
  split.
  eauto.
  split.
  eauto.
  split.
  simpl in H1.
  destruct H1.
  destruct H1.
  auto.
  eauto.
  unfold InOS.
  do 3 eexists.
  split.
  eauto.
  right.
  left.
  do 8 eexists.
  split.
  simpl.
  eauto.
  unfold pumerge.
  rewrite H0.
  eauto.
  pose proof (allocb_store_mem_ex x1 m x v) as H200.
  destruct H200.
  rename H into H200.
  do 3 eexists.
  eapply inapi_step; eauto.
  eapply ostc_step; eauto.
  eapply stmt_step; eauto.
  eapply sallocp_step; eauto.
  unfold alloc.
  eexists.
  split.
  eauto.
  split.
  eauto.
  split.
  simpl in H1.
  destruct H1.
  destruct H1.
  auto.
  eauto.
  rewrite EnvMod.set_a_get_a.
  eauto.
  apply identspec.eq_beq_true.
  auto.
  unfold InOS.
  do 3 eexists.
  split.
  eauto.
  right.
  left.
  do 8 eexists.
  split.
  simpl.
  eauto.
  unfold pumerge.
  rewrite H0.
  eauto.
Qed.


Lemma ndym_cont_red : forall ks f s E ks',
                        n_dym_com_int_scont (ks ## kcall f s E ks') -> 
                        n_dym_com_int_scont ks.
Proof.
  inductions ks; auto; tryfalse.
  intros; simpl;auto.
  intros; simpl; eauto.
  simpl in H.
  destruct H.
  split; eauto.
  intros;simpl in *.
  destruct H.
  splits; eauto.
  intros; simpl in *.
  destruct H.
  destruct H0.
  splits; eauto.
  intros; simpl in *.
  destruct H.
  splits; eauto.
Qed.

Lemma n_dym_com_int_cd_cont : forall c ke ks1 ks f s E, 
    n_dym_com_int_cd  (c, (ke, ks1 ## kcall f s E ks)) ->  n_dym_com_int_cd  (c, (ke, ks1)).
Proof.
  intros. simpl.
  unfolds in H.
  destruct H.
  splits; eauto.
  eapply  ndym_cont_red; eauto.
Qed.


Lemma inos_call:
   forall c ke ks1 f s ks po pi, InOS (c, (ke, ks1 ## kcall f s empenv kstop)) (pumerge po pi) -> InOS (c, (ke, ks1 ## kcall f s empenv ks)) (pumerge po pi).
Proof.
  intros.
  unfold InOS in *.
  do 4 destruct H.
  inverts H.
  destruct H0.
  do 5 destruct H.
  subst.
  do 3 eexists.
  split.
  eauto.
  left.
  do 4 eexists.
  split.
  eauto.
  eauto.

  destruct H.
  do 9 destruct H.
  do 3 eexists.
  split.
  eauto.
  right.
  left.
  pose proof contLib.callcont_addkcall_imply_callcont_addkcall_exist.
  pose proof (H1 ks1 f s empenv kstop x1 x7 x2 x3 ks).
  apply H2 in H.
  destruct H.
  do 8 eexists.
  split.
  apply H.
  eauto.

  do 3 eexists.
  split.
  eauto.
  right.
  right.
  apply contLib.intcont_some_kcall_none in H.
  intro.
  apply H.
  eapply contLib.intcont_none_addcont.
  apply H0.
Qed.

Lemma ltstep_inos_loststep :
  forall pc po pi ip tid c o c' cst cst' o', 
    ltstep (pc, (po, pi, ip)) tid  c  cst o c' cst' o' ->
    InOS c (pumerge po pi) ->
    loststep (pumerge po pi) c o c' o'.
Proof.
  introv Hstep Hn.
  inverts Hstep; inverts H; tryfalse; auto.
Qed.

Lemma kassignr_ex :
  forall e t ks0 ks1 f s E ks, 
    kassignr e t ks0 = ks1 ## kcall f s E ks -> 
    exists ks', ks1 =   kassignr e t ks' /\ ks0 = ks' ## kcall f s E ks.
Proof.
  intros.
  destruct ks1; tryfalse;  simpl in *.
  inverts H.
  eexists; eauto.
Qed.

Lemma kassignl_ex :
  forall e t ks0 ks1 f s E ks, 
    kassignl e t ks0 = ks1 ## kcall f s E ks -> 
    exists ks', ks1 =   kassignl e t ks' /\ ks0 = ks' ## kcall f s E ks.
Proof.
  intros.
  destruct ks1; tryfalse;  simpl in *.
  inverts H.
  eexists; eauto.
Qed.

Lemma kfuneval_ex1 :
  forall   ks0 ks1 f0 vl tl e el f s E ks, 
    kfuneval f0 vl tl (e :: el) ks0 = ks1 ## kcall f s E ks -> 
    exists ks', ks1 =   kfuneval f0 vl tl (e :: el) ks' /\ ks0 = ks' ## kcall f s E ks.
Proof.
  intros.
  destruct ks1; tryfalse;  simpl in *.
  inverts H.
  eexists; eauto.
Qed.

Lemma kfuneval_ex2 :
  forall ks0 ks1 f0 vl tl f s E ks, 
    kfuneval f0 vl tl nil ks0 = ks1 ## kcall f s E ks -> 
    exists ks', ks1 =   kfuneval f0 vl tl nil ks' /\ ks0 = ks' ## kcall f s E ks.
Proof.
  intros.
  destruct ks1; tryfalse;  simpl in *.
  inverts H.
  eexists; eauto.
Qed.

Lemma kcall_ex :
  forall  f0 s0  E'   ks0 ks1  f s E ks,
    ks1 <> kstop -> 
    kcall f0 s0 E' ks0= ks1 ## kcall f s E ks -> 
    exists ks', ks1 =   kcall f0 s0 E'  ks' /\ ks0 = ks' ## kcall f s E ks.
Proof.
  intros.
  destruct ks1; tryfalse;  simpl in *.
  inverts H0.
  eexists; splits; eauto.
Qed. 

Lemma intcont_notnone_callcont_none :
  forall ks1 ks2, intcont ks1 <> None -> callcont (ks1##ks2) = None.
Proof.
  inductions ks1; intros; simpl in *; tryfalse; eauto.
Qed.


Lemma kret_ex :
  forall ks0 ks1 f s E ks, 
    kret ks0 = ks1 ## kcall f s E ks -> 
    exists ks', ks1 =   kret  ks' /\ ks0 = ks' ## kcall f s E ks.
Proof.
  intros.
  destruct ks1; tryfalse;  simpl in *.
  inverts H.
  eexists; eauto.
Qed. 


Lemma callcont_not_none_ex :
  forall ks,
    callcont ks <> None ->
    exists f s le ks0,  
      callcont ks = Some (kcall f s le ks0).
Proof.
  inductions ks; introv Hnq; simpl in Hnq; tryfalse; try ( apply IHks in Hnq;
  simpl; auto).
  simpl. do 4 eexists; eauto.
Qed.


Lemma kif_ex :
  forall  s1 s2   ks0 ks1  f s E ks, 
    kif s1 s2 ks0 = ks1 ## kcall f s E ks -> 
    exists ks', ks1 =  kif s1 s2  ks' /\ ks0 = ks' ## kcall f s E ks.
Proof.
  intros.
  destruct ks1; tryfalse;  simpl in *.
  inverts H.
  eexists; eauto.
Qed.


Lemma intcont_kcall_intcont :
  forall ks f s E ks' c ke le ks'',
    intcont (ks ## kcall f s E ks')
    =  Some (kint c ke le ks'') -> exists kss,  intcont ks =  Some (kint c ke le kss).
Proof.
  inductions ks; intros; simpl in *; tryfalse; eauto.
  inverts H.
  eexists; eauto.
Qed.


Lemma kseq_ex :
  forall  s0   ks0 ks1  f s E ks, 
    kseq s0 ks0 = ks1 ## kcall f s E ks -> 
    exists ks', ks1 =  kseq s0 ks' /\ ks0 = ks' ## kcall f s E ks.
Proof.
  intros.
  destruct ks1; tryfalse;  simpl in *.
  inverts H.
  eexists; eauto.
Qed.

Lemma kwhile_ex :
  forall  e s0    ks0 ks1  f s E ks, 
    kwhile e s0 ks0 = ks1 ## kcall f s E ks -> 
    exists ks', ks1 =  kwhile e s0  ks' /\ ks0 = ks' ## kcall f s E ks.
Proof.
  intros.
  destruct ks1; tryfalse;  simpl in *.
  inverts H.
  eexists; eauto.
Qed. 

Lemma loststep_nofree_notabt :
  forall p c ke ks1 ks o2 Cl'  o'' s f, 
    loststep p (c, (ke, ks1 ## kcall f s empenv ks))  o2 Cl' o'' ->
    (~ ((c, (ke, ks1)) = (curs sret, (kenil, ks1)) /\ callcont ks1 = None/\intcont ks1=None))->
    ( forall v ksx,
        ~(
            (c, (ke, ks1)) = (curs (sskip (Some v)), (kenil, kret ksx)) /\
            callcont ksx = None/\intcont ksx =None)) ->
    (forall  (vl : vallist) (dl : decllist),
       (c, (ke, ks1)) <> (curs (salloc vl dl), (kenil, kstop))) ->
    (forall (al : freelist) (v : option val),
       ~
         (c = curs (sfree al v) /\
          callcont ks1 = None /\ intcont ks1 = None)) -> 
    ~ loststepabt p (c, (ke, ks1)) o2.
Proof.
  introv Hstep1 Hret  Hrete Halloc  Hfree Hstep2.
  apply Hstep2.
  inverts Hstep1; tryfalse.
  inverts H; tryfalse.
  inverts H0; do 2 eexists; eapply ostc_step; eapply expr_step; eauto.
  inverts H0.
  inverts H1. 
  try ( do 2 eexists; eapply ostc_step; eapply stmt_step; constructors; eauto).
  apply kassignr_ex in H3.
  destruct H3 as (ks'&Heqk & Hks).
  subst ks1.
  try ( do 2 eexists; eapply ostc_step; eapply stmt_step; constructors; eauto).
  apply kassignl_ex in H.
  destruct H as (ks''&Heqk & Hks).
  subst ks1.
  try ( do 2 eexists; eapply ostc_step; eapply stmt_step; constructors; eauto).
  try ( do 2 eexists; eapply ostc_step; eapply stmt_step; constructors; eauto).
  try ( do 2 eexists; eapply ostc_step; eapply stmt_step; constructors; eauto).
  try ( do 2 eexists; eapply ostc_step; eapply stmt_step; constructors; eauto).
  apply kfuneval_ex1 in H.
  destruct H as (ks''&Heqk & Hks).
  subst ks1.
  try ( do 2 eexists; eapply ostc_step; eapply stmt_step; constructors; eauto).
  apply kfuneval_ex2  in H3.
  destruct H3 as (ks''&Heqk & Hks).
  subst ks1.
  try ( do 2 eexists; eapply ostc_step; eapply stmt_step; constructors; eauto).
  try ( do 2 eexists; eapply ostc_step; eapply stmt_step; constructors; eauto).
  try ( do 2 eexists; eapply ostc_step; eapply stmt_step; constructors; eauto).
  try ( do 2 eexists; eapply ostc_step; eapply stmt_step; constructors; eauto).
  lets Hre : Halloc (nil : vallist) (dnil:decllist).
  assert (ks1 = kstop \/ ks1 <> kstop) by tauto.
  destruct H.
  subst ks1.
  tryfalse.
  lets Hdd : kcall_ex H H3.
  destruct Hdd as (kss & Hks & Hks0).
  subst ks1.
  try ( do 2 eexists; eapply ostc_step; eapply stmt_step; constructors; eauto).
  apply Classical_Prop.not_and_or in Hret.
  destruct Hret.
  tryfalse.
  apply Classical_Prop.not_and_or in H.
  destruct H.
  lets Hrs :   callcont_not_none_ex H.
  destruct Hrs as (ff&ss&lee&kss0&heq).
  try ( do 2 eexists; eapply ostc_step; eapply stmt_step; constructors; eauto).
  try ( do 2 eexists; eapply ostc_step; eapply stmt_step; constructors; eauto).
  eapply intcont_notnone_callcont_none with (ks2 := kcall f s empenv ks) in H; tryfalse.
  try ( do 2 eexists; eapply ostc_step; eapply stmt_step; constructors; eauto).
  apply kret_ex  in H.
  destruct H as (kss'&Heqk & Hks).
  subst ks1.
  subst ks'.
  lets Hrss : Hrete v kss'.
  apply Classical_Prop.not_and_or in Hrss.
  destruct Hrss.
  tryfalse.
  apply Classical_Prop.not_and_or in H.
  destruct H.
  lets Hrs :   callcont_not_none_ex H.
  destruct Hrs as (ff&ss&lee&kss0&heq).
  try ( do 2 eexists; eapply ostc_step; eapply stmt_step; constructors; eauto).
  eapply intcont_notnone_callcont_none with (ks2 := kcall f s empenv ks) in H; tryfalse.
  try ( do 2 eexists; eapply ostc_step; eapply stmt_step; constructors; eauto).
  lets Hrss : Hfree (nil:freelist) v.
  apply Classical_Prop.not_and_or in Hrss.
  destruct Hrss.
  tryfalse.
  apply Classical_Prop.not_and_or in H.
  destruct H.
  lets Hrs :   callcont_not_none_ex H.
  destruct Hrs as (ff&ss&lee&kss0&heq).
  try ( do 2 eexists; eapply ostc_step; eapply stmt_step; constructors; eauto).
  eapply intcont_notnone_callcont_none with (ks2 := kcall f s empenv ks) in H; tryfalse.
  try ( do 2 eexists; eapply ostc_step; eapply stmt_step; constructors; eauto).
  apply kseq_ex in H3.
  destruct H3 as (kss'&Heqk & Hks).
  subst ks1.
  try ( do 2 eexists; eapply ostc_step; eapply stmt_step; constructors; eauto).
  apply kseq_ex in H3.
  destruct H3 as (kss'&Heqk & Hks).
  subst ks1.
  try ( do 2 eexists; eapply ostc_step; eapply stmt_step; constructors; eauto).
  try ( do 2 eexists; eapply ostc_step; eapply stmt_step; constructors; eauto). 
  try ( do 2 eexists; eapply ostc_step; eapply stmt_step; constructors; eauto). 
  apply kif_ex in H.
  destruct H as (kss'&Heqk & Hks).
  subst ks1.
  try ( do 2 eexists; eapply ostc_step; eapply stmt_step; constructors; eauto).
  apply kif_ex in H.
  destruct H as (kss'&Heqk & Hks).
  subst ks1.
  ( do 2 eexists; eapply ostc_step; eapply stmt_step; eauto).  eapply sviff_step; eauto.
  try ( do 2 eexists; eapply ostc_step; eapply stmt_step; constructors; eauto).
  apply  kwhile_ex  in H.
  destruct H as (kss'&Heqk & Hks).
  subst ks1.
  try ( do 2 eexists; eapply ostc_step; eapply stmt_step; constructors; eauto).
  apply  kwhile_ex in H.
  destruct H as (kss'&Heqk & Hks).
  subst ks1.
  ( do 2 eexists; eapply ostc_step; eapply stmt_step; eauto).  
  eapply svwhilef_step; eauto.
  inverts H.
  apply  intcont_kcall_intcont in H0.
  destruct H0.
  try ( do 2 eexists; eapply  exint_step ; eauto).
  inverts H.
  try ( do 2 eexists; eapply  eoi_step ; eauto).
  inverts H.
  try ( do 2 eexists; eapply  cli_step ; eauto).
  inverts H.
  try ( do 2 eexists; eapply  sti_step ; eauto).
  inverts H.
  try ( do 2 eexists; eapply  encrit_step ; eauto).
  inverts H.
  try ( do 2 eexists; eapply  excrit_step ; eauto).
  inverts H.
  try ( do 2 eexists; eapply  checkis_step ; eauto).

  Grab Existential Variables.
  trivial.
  trivial.
  trivial.
  trivial.
Qed.

Lemma ltstep_inos_nupd_clst :  
  forall pc po pi ip tid c o c' cst  cst' o', 
    ltstep (pc, (po, pi, ip)) tid  c  cst o c' cst' o' ->
    InOS c (pumerge po pi) ->
    cst = cst'.
Proof.
  introv Hstep Hinos.
  inverts Hstep; eauto; tryfalse.
Qed.

Lemma intcont_ndym:
  forall ks ks' s ke E,
    intcont ks = Some (kint s ke E ks') ->
    ~ n_dym_com_int_scont ks.
Proof.
  inductions ks; intros; simpl in *; tryfalse.
  introv Hs.
  destruct Hs.
  apply IHks in H.
  tryfalse.
  auto.
  eapply IHks; eauto.
  eapply IHks; eauto.
  eapply IHks; eauto.
  introv Hs.
  destruct Hs as (Hs1& Hs2 & Hs3).
  apply IHks in H; tryfalse.
  introv Hs.
  destruct Hs as (Hs1& Hs2).
  apply IHks in H; tryfalse.
  eapply IHks; eauto.
  auto.
Qed.

Lemma loststep_not_alloc:
  forall p c ke ks c' ke' ks'  o  o', 
    n_dym_com_int_cd  (c, (ke, ks)) -> 
    loststep p (c, (ke, ks))  o (c',(ke',ks')) o' -> 
    (forall  (vl : vallist) (dl : decllist),
       (c, (ke, ks)) <> (curs (salloc vl dl), (kenil, kstop))) ->
    (forall (vl : vallist) (dl : decllist),
       (c', (ke', ks')) <> (curs (salloc vl dl), (kenil, kstop))).
Proof.
  introv Hdy  Hstep Hnot.
  intros.
  introv Hs.
  inverts Hs.
  inverts Hstep; tryfalse.
  invertstep tryfalse.
  simpl in Hdy.
  destruct Hdy. destruct H0 . tryfalse.
  simpl in Hdy.
  destruct Hdy. destruct H0 . tryfalse.
  simpl in Hdy.
  destruct Hdy. destruct H0 . tryfalse.
  simpl in Hdy.
  destruct Hdy. destruct H0 . destruct H1.  tryfalse.
  inverts H6.  
  simpl in Hdy.
  destruct  Hdy.
  apply intcont_ndym in H7; tryfalse.
Qed.

Lemma loststep_not_free :
  forall p c ke ks c' ke' ks'  o  o', 
    n_dym_com_int_cd  (c, (ke, ks)) -> 
    loststep p (c, (ke, ks))  o (c',(ke',ks')) o' -> 
    (forall (al : freelist) (v : option val),
       ~
         (c = curs (sfree al v) /\
          callcont ks = None /\ intcont ks = None)) ->
    (forall al v,~ (c' = curs (sfree al v) /\ callcont ks' = None/\intcont ks'=None)).
Proof.
  introv Hdy  Hstep Hnot.
  intros.
  introv Hs.
  destruct Hs as (Hc & Hcall & Hint).
  subst c'.
  inverts Hstep; tryfalse.
  invertstep tryfalse.
  lets Hf : Hnot ((b,t)::al) v.
  apply Hf; splits; eauto.
  simpl in Hdy.
  destruct Hdy.
  destruct H; tryfalse.
  simpl in Hdy.
  destruct Hdy.
  destruct H0; tryfalse.
  simpl in Hdy.
  destruct Hdy.
  destruct H0; tryfalse.
  simpl in Hdy.
  destruct Hdy.
  destruct H0; tryfalse.
  simpl in Hdy.
  destruct Hdy.
  destruct H0; tryfalse.
  destruct H1; tryfalse.
  simpl in Hdy.
  destruct Hdy.
  destruct H0; tryfalse.
  inverts H6.  
  simpl in Hdy.
  destruct  Hdy.
  apply intcont_ndym in H7; tryfalse.
Qed.

Lemma tstep_to_osstep :
  forall (pc po pi : progunit) (ip : intunit) 
         tid (c : cureval) (ke : exprcont)
         (ks1 ks : stmtcont) (cst : clientst) (o2 : taskst) 
         (Cl' : code) (cst' : clientst) (o'' : taskst) 
         (s : stmts) (f : fid),
    n_dym_com_int_cd (c, (ke, ks1 ## kcall f s empenv ks)) ->
    ltstep (pc, (po, pi, ip)) tid (c, (ke, ks1 ## kcall f s empenv ks))
           cst o2 Cl' cst' o'' ->
    ~
      ((c, (ke, ks1)) = (curs sret, (kenil, ks1)) /\
       callcont ks1 = None /\ intcont ks1 = None) ->
    ~
      (exists v ksx,
         (c, (ke, ks1)) = (curs (sskip (Some v)), (kenil, kret ksx)) /\
         callcont ksx = None /\ intcont ksx = None) ->
    (forall (vl : vallist) (dl : decllist),
       (c, (ke, ks1)) <> (curs (salloc vl dl), (kenil, kstop))) ->
    (forall (al : freelist) (v : option val),
       ~
         (c = curs (sfree al v) /\ callcont ks1 = None /\ intcont ks1 = None)) ->
    InOS (c, (ke, ks1 ## kcall f s empenv kstop)) (pumerge po pi) ->
    exists c' ke' ks1',
      cst' = cst /\
      loststep (pumerge po pi) (c, (ke, ks1)) o2 (c', (ke', ks1')) o'' /\
      Cl' = (c', (ke', ks1' ## kcall f s empenv ks)) /\
      (forall (vl : vallist) (dl : decllist),
         (c', (ke', ks1')) <> (curs (salloc vl dl), (kenil, kstop))) /\
      (forall (al : freelist) (v : option val),
         ~
           (c' = curs (sfree al v) /\
            callcont ks1' = None /\ intcont ks1' = None)).
Proof.
  introv Hdy Hstep Hret Hrete Halloc Hfree Hinos . 
  apply n_dym_com_int_cd_cont in Hdy.
  
  lets Hinoss  :  inos_call ks  Hinos. 
  assert (~loststepabt (pumerge po pi) (c, (ke, ks1)) o2) as Habt.
  lets Hstep': ltstep_inos_loststep  Hstep Hinoss.
  eapply loststep_nofree_notabt; eauto.
  
  lets Hstep': ltstep_inos_loststep Hstep Hinoss; eauto.

  lets Hres : cont_frame_mono  Habt Hstep'.
  destruct Hres as (c'&ke'&ks''&Hloste & Heq).
  exists c' ke' ks''.
  split.
  apply eq_sym.
  eapply ltstep_inos_nupd_clst; eauto.
  splits; eauto.
  eapply  loststep_not_alloc; eauto.
  eapply loststep_not_free; eauto.
Qed.

Lemma inos_call':
  forall po pi f t d1 d2 s c ke ks ks',
    po f = Some (t, d1, d2, s) ->
    InOS (c, (ke, ks ## kcall f s empenv ks')) (pumerge po pi) ->
    InOS (c, (ke, ks ## kcall f s empenv kstop)) (pumerge po pi).
Proof.
  intros.
  unfold InOS in *.
  do 4 destruct H0.
  inverts H0.
  destruct H1.
  do 5 destruct H0.
  subst.
  do 3 eexists.
  split.
  eauto.
  left.
  do 4 eexists.
  split.
  eauto.
  eauto.

  destruct H0.
  do 9 destruct H0.
  do 3 eexists.
  split.
  eauto.
  right.
  left.
  pose proof contLib.callcont_addkcall_imply_callcont_addkcall_exist.
  pose proof (H2 ks f s empenv ks' x1 x7 x2 x3 kstop).
  apply H3 in H0.
  destruct H0.
  do 8 eexists.
  split.
  apply H0.
  eauto.

  do 3 eexists.
  split.
  eauto.
  right.
  right.
  intro.
  apply H0.
  eapply contLib.intcont_none in H1.
  eauto.
Qed.

Lemma ks_add_call_false :
  forall ks ks' f s le, ks<> ks' ## kcall f s le ks.
Proof.
  intros.
  intro.
  assert (len_stmtcont ks = len_stmtcont (ks' ## kcall f s le ks)).
  apply contLib.stmtcont_eq_length.
  auto.
  clear H.
  rewrite contLib.length_addcont in H0.
  simpl in H0.
  omega.
Qed.

Lemma goodks_call_inos:
  forall pc po pi ip  lenv ks ks' ks'' f s f' s' le' t d1 d2,
    po f = Some (t,d1 ,d2,s) ->
    goodks (pc, (po, pi, ip)) (ks' ## kcall f s lenv ks) ->
    callcont (ks' ## kcall f s lenv ks) = Some (kcall f' s' le' (ks'' ## kcall f s lenv ks))->
    ((exists f0 le0 ks'0 t0 d1 d2 s0 s',
        callcont (ks' ## kcall f s lenv ks) = Some (kcall f0 s0 le0 ks'0) /\
        pumerge po pi f0 = Some (t0, d1, d2, s')) \/ intcont (ks' ## kcall f s lenv ks) <> None) ->
    ((exists f0 le0 ks'0 t0 d1 d2 s0 s',
        callcont (ks'' ## kcall f s lenv ks) = Some (kcall f0 s0 le0 ks'0) /\
        pumerge po pi f0 = Some (t0, d1, d2, s')) \/
     intcont (ks'' ## kcall f s lenv ks) <> None).
Proof.
  induction ks';simpl;intros;auto;tryfalse;try solve [eapply IHks';eauto].
  inversion H1.
  subst f' s' le'.
  destruct (ks_add_call_false ks ks'' f s lenv).
  auto.
  inversion H1.
  subst f' s' le'.
  apply addcont_same_remove in H7.
  subst ks''.
  destruct (pumerge po pi f).
  clear - H H0. 
  induction ks';simpl;auto;subst;tryfalse.
  simpl in H0.
  left.
  exists f0.
  assert (pumerge po pi f0 = Some (t,d1,d2,s0)).
  apply pumerge_get;auto.
  rewrite H1 in H0.
  exists lenv ks t d1 d2 s0. 
  exists s0.
  split;auto.
  simpl in H0.
  left.
  exists f.
  destruct (pumerge po pi f).
  destruct f1.
  destruct p.
  destruct p.
  do 7 eexists ;split;eauto.
  assert (~no_os (pc, (po, pi, ip)) (ks' ## kcall f0 s0 lenv ks)).
  clear -H.
  apply pumerge_get with (pi:=pi)in H.
  induction ks';simpl;auto.
  rewrite H;auto.
  destruct (pumerge po pi f);auto.
  destruct H1;auto.

  apply no_os_goodks in H0.
  clear - H H0. 
  induction ks';simpl;auto;subst;tryfalse.
  simpl in H0.
  left.
  exists f0.
  assert (pumerge po pi f0 = Some (t,d1,d2,s0)).
  apply pumerge_get;auto.
  rewrite H1 in H0.
  exists lenv ks t d1 d2 s0. 
  exists s0.
  split;auto.
  simpl in H0.
  left.
  exists f.
  destruct (pumerge po pi f).
  destruct f1.
  destruct p.
  destruct p.
  do 7 eexists ;split;eauto.
  assert (~no_os (pc, (po, pi, ip)) (ks' ## kcall f0 s0 lenv ks)).
  clear -H.
  apply pumerge_get with (pi:=pi)in H.
  induction ks';simpl;auto.
  rewrite H;auto.
  destruct (pumerge po pi f);auto.
  destruct H1;auto.
Qed.


Lemma goodks_int_call_inos' :
  forall pc po pi ip ks1 f  c' ke' le' t d1 d2 s ks ks'',
    pumerge po pi f = Some (t,d1,d2,s) ->
    goodks (pc, (po, pi, ip)) (ks1 ## kcall f s empenv ks) ->
    intcont (ks1 ## kcall f s empenv ks) = Some (kint c' ke' le' ks'') ->
    (exists f0 le ks' t0 d0 d3 s0 s',
       callcont ks''= Some (kcall f0 s0 le ks') /\
       pumerge po pi f0 = Some (t0, d0, d3, s')) \/
    intcont ks''<> None.
Proof.
  induction ks1;simpl;intros;auto;tryfalse;try solve [eapply IHks1;eauto].
  inversion H1;subst.
  clear -H H0.
  induction ks1;simpl;auto;subst;tryfalse.
  simpl in H0.
  left.
  rewrite H in H0.
  do 8 eexists;split;eauto.
  simpl in H0.
  left.
  exists f0.
  destruct (pumerge po pi f0).
  destruct f1.
  destruct p.
  destruct p.
  do 7 eexists ;split;eauto.
  assert (~no_os (pc, (po, pi, ip)) (ks1 ## kcall f s empenv ks)).
  clear -H.
  induction ks1;simpl;auto.
  rewrite H;auto.
  destruct (pumerge po pi f0);auto.
  destruct H1;auto.
Qed.

Lemma goodks_int_call_inos :
  forall pc po pi ip ks1 f  c' ke' le' ks1' t d1 d2 s ks,
    po f = Some (t,d1,d2,s) ->
    goodks (pc, (po, pi, ip)) (ks1 ## kcall f s empenv ks) ->
    intcont (ks1 ## kcall f s empenv ks) = Some (kint c' ke' le' (ks1' ## kcall f s empenv ks)) ->
    InOS  (c', (ke', ks1' ## kcall f s empenv ks)) (pumerge po pi).
Proof.
  intros.
  unfold InOS.
  do 3 eexists;split;eauto.
  right.
  apply pumerge_get with (pi:=pi)in H .
  eapply goodks_int_call_inos';eauto.
Qed.

Lemma inos_step_still :
  forall (c : cureval) (ke : exprcont) (ks1 : stmtcont) 
         (f : fid) (pc : progunit)
         (po : fid -> option (type * decllist * decllist * stmts))
         (pi : progunit) (ip : intunit) tid 
         (c' : cureval) (ke' : exprcont) (ks1' : stmtcont)
         (cst cst' : clientst) (o o' : taskst) (ks : stmtcont) 
         (s : stmts) (t : type) (d1 d2 : decllist),
    po f = Some (t, d1, d2, s) ->
    goodks (pc, (po, pi, ip)) (ks1 ## kcall f s empenv ks) ->
    InOS (c, (ke, ks1 ## kcall f s empenv kstop)) (pumerge po pi) ->
    ltstep (pc, (po, pi, ip)) tid (c, (ke, ks1 ## kcall f s empenv ks))
           cst o (c', (ke', ks1' ## kcall f s empenv ks)) cst' o' ->
    InOS (c', (ke', ks1' ## kcall f s empenv kstop)) (pumerge po pi).
Proof.
  intros.

  apply inos_call with (ks:=ks)in H1.
  eapply inos_call' with (ks':=ks);eauto.
  inversion H2;subst.
  inversion H3;subst pc0 po0 pi0 ip0;clear H3.
  destruct H5.
  auto.

  inversion H3;subst pc0 po0 pi0 ip0;clear H3.
  inversion H4;subst.
  inversion H3;subst.
  inversion H13;subst c0 ke0.
  assert (ks1 = ks1').
  eapply addcont_same_remove;eauto.
  subst ks1'.
  unfold InOS.
  unfold InOS in H1.
  do 3 eexists;split;eauto.
  do 3 destruct H1.
  destruct H1.
  inversion H1;subst x x0 x1.
  destruct H6.
  do 5 destruct H6.
  subst c.
  inversion H14;tryfalse.
  right;auto.


  unfold InOS.
  unfold InOS in H1.
  do 3 eexists;split;eauto.
  inversion H13;subst c0 ks0 ke;clear H13.
  do 3 destruct H1.
  destruct H1.
  inversion H1;subst x x0 x1.
  destruct H6.
  do 5 destruct H6.
  subst c.
  inversion H14;subst;tryfalse;simpl;auto.
  right.

  left.
  simpl.
  do 8 eexists;split;eauto.

  clear H1 H4.
  inversion H14;subst;tryfalse;simpl;auto; try solve [simpl;auto | rewrite <- H1 in H6;simpl in H6;auto | rewrite <- H8 in H6;simpl in H6;auto].

  right.
  left.
  do 8 eexists;split;eauto.

  right.

  eapply goodks_call_inos;eauto.


  inversion H12;subst.
  eapply goodks_int_call_inos;eauto.

  inversion H11;subst.
  unfold InOS in *.
  do 4 destruct H1.
  inversion H1;subst.
  destruct H3.
  do 5 destruct H3;tryfalse.
  do 3 eexists;split;eauto.

  inversion H12;subst.
  unfold InOS in *.
  do 4 destruct H1.
  inversion H1;subst.
  destruct H3.
  do 5 destruct H3;tryfalse.
  do 3 eexists;split;eauto.

  inversion H12;subst.
  unfold InOS in *.
  do 4 destruct H1.
  inversion H1;subst.
  destruct H3.
  do 5 destruct H3;tryfalse.
  do 3 eexists;split;eauto.

  inversion H12;subst.
  unfold InOS in *.
  do 4 destruct H1.
  inversion H1;subst.
  destruct H3.
  do 5 destruct H3;tryfalse.
  do 3 eexists;split;eauto.

  inversion H12;subst.
  unfold InOS in *.
  do 4 destruct H1.
  inversion H1;subst.
  destruct H3.
  do 5 destruct H3;tryfalse.
  do 3 eexists;split;eauto.

  inversion H8;subst.
  unfold InOS in *.
  do 4 destruct H1.
  inversion H1;subst.
  destruct H3.
  do 5 destruct H3;tryfalse.

  do 3 eexists;split;eauto.
Qed.

Lemma ltstep_eqg :
  forall (p : lprog) t (T : code) 
         (cst : clientst) (S : taskst) (T' : code) 
         (S' : taskst) (cst' : clientst) (G : env),
    ltstep p t T cst S T' cst' S' ->
    fst (fst (fst (fst S))) = G -> fst (fst (fst (fst S'))) = G.
Proof.
  intros.
  destruct S as [[[[]]]].
  destruct S' as [[[[]]]].
  simpl in *.
  subst e.
  inverts H.
  inverts H6;auto.
  inverts H1;auto.
  inverts H7;auto.
  inverts H0;auto.
  inverts H0;try solve [ auto | inverts H;inverts H1;auto ].
  inverts H11;inverts H14;auto.
Qed.


Lemma retv_step :
  forall (pc : progunit)
         (po : fid -> option (type * decllist * decllist * stmts))
         (pi : progunit) (ip : intunit) tid 
         (v : option val) (ksx : stmtcont) (f : fid) 
         (s : stmts) (ks : stmtcont) (cst : clientst) 
         (o : taskst) (C' : code) (cst' : clientst) 
         (o' : taskst) (ft : type) (d1 d2 : decllist),
    po f = Some (ft, d1, d2, s) ->
    callcont ksx = None ->
    intcont ksx = None ->
    ltstep (pc, (po, pi, ip)) tid
           (curs (sskip v), (kenil, kret ksx ## kcall f s empenv ks)) cst o C'
           cst' o' ->
    o' = o /\
    cst' = cst /\
    C' =
    (curs (sfree (getaddr (snd (fst (get_smem o)))) v),
     (kenil, ksx ## kcall f s empenv ks)).
Proof.
  intros.
  inversion H2;tryfalse.
  subst.
  inversion H3;subst pc0 po0 pi0 ip0.
  destruct H5.
  unfold InOS.
  do 3 eexists;splits;eauto.
  right.
  left.
  simpl.
  apply pumerge_get with (pi:=pi) in H.
  assert (callcont (ksx ## kcall f s empenv ks) = Some (kcall f s empenv ks)).
  eapply call_int_none_call;eauto.
  do 8 eexists;splits;simpl;eauto.
  subst.
  inversion H3;subst pc0 po0 pi0 ip0.
  inversion H4;subst;tryfalse.
  inversion H6;inversion H7;subst.
  inversion H8;tryfalse.
  inversion H8;subst;tryfalse.
  simpl;auto.
Qed.
  
Lemma ret_step :
  forall (pc : progunit)
         (po : fid -> option (type * decllist * decllist * stmts))
         (pi : progunit) (ip : intunit) tid 
         (ks1 : stmtcont) (f : fid) (s : stmts) (ks : stmtcont)
         (cst : clientst) (o : taskst) (C' : code) 
         (cst' : clientst) (o' : taskst) (ft : type) 
         (d1 d2 : decllist),
    po f = Some (ft, d1, d2, s) ->
    callcont ks1 = None ->
    intcont ks1 = None ->
    ltstep (pc, (po, pi, ip)) tid
           (curs sret, (kenil, ks1 ## kcall f s empenv ks)) cst o C' cst' o' ->
    o' = o /\
    cst' = cst /\
    C' =
    (curs (sfree (getaddr (snd (fst (get_smem o)))) None),
     (kenil, ks1 ## kcall f s empenv ks)).
Proof.
  intros.
  inversion H2;tryfalse.
  subst.
  inversion H3;subst pc0 po0 pi0 ip0.
  destruct H5.
  unfold InOS.
  do 3 eexists;splits;eauto.
  right.
  left.
  simpl.
  apply pumerge_get with (pi:=pi) in H.
  assert (callcont (ks1 ## kcall f s empenv ks) = Some (kcall f s empenv ks)).
  eapply call_int_none_call;eauto.
  do 8 eexists;splits;simpl;eauto.
  subst.
  inversion H3;subst pc0 po0 pi0 ip0.
  inversion H4;subst;tryfalse.
  inversion H6;inversion H7;subst.
  inversion H8;tryfalse.
  inversion H8;subst;tryfalse.
  simpl;auto.
Qed.

Lemma tstepev_osstepabt :
  forall (pc po pi : progunit) (ip : intunit) 
         tid (c : cureval) (ke : exprcont) 
         (ks1 : stmtcont) (f : fid) (s : stmts) (empenv : env)
         (ks : stmtcont) (cst cst' : clientst) (Cl' : code) 
         (o2 o2': taskst) (ev : val),
    ltstepev (pc, (po, pi, ip)) tid (c, (ke, ks1 ## kcall f s empenv ks))
             cst o2 Cl' cst' o2' ev ->
    notabort (c, (ke, ks1)) /\ loststepabt pi (c, (ke, ks1)) o2.
Proof.
  intros. 
  inversion H;subst.
  inversion H0;subst pc0 po0 pi0 ip0.
  unfold notabort.
  splits.
  inversion H1.
  subst.
  inversion H4;subst.
  splits;intro X;unfolds in X;mytac;tryfalse.
  unfolds.
  intro X.
  mytac.
  inversion H1;subst.
  inversion H4;subst.
  mytac.
  inversion H3;subst;tryfalse.
  inversion H0;subst.
  inversion H8;tryfalse.
  inversion H8;subst;tryfalse.
Qed.


Lemma nabt_lift :
  forall (pc po pi : progunit) (ip : intunit) 
         (c : cureval) (ke : exprcont) (ks : stmtcont) 
         (o : taskst) (cst : clientst) tid 
         (ks' : stmtcont) (f : fid) (s : stmts),
    no_call_api (c, (ke, ks)) po ->
    InOS (c, (ke, ks ## kcall f s empenv kstop)) (pumerge po pi) ->
    ~ loststepabt pi (c, (ke, ks)) o ->
    ~
      ltstepabt (pc, (po, pi, ip)) tid (c, (ke, ks ## kcall f s empenv ks'))
      cst o.
Proof.
  introv Hnoos.
  intros.
  intro X.
  destruct H0.
  inversion X.
  unfold loststepabt.
  intro X'.
  destruct H1.
  inversion H0;subst.
  mytac.
  left.
  destruct x as (c'&(ke'&ks'')).
  exists (c',(ke',ks''##kcall f s empenv ks')) x0 cst.
  eapply inapi_step;eauto.
  eapply loststep_cont_locality;eauto.
  eapply loststep_no_api_local;eauto.
  eapply inos_call;eauto.
Qed.

Lemma inos_sw_still :
  forall (x : var) (ks1 ks : stmtcont) (f : fid) 
         (s : stmts) (po pi : progunit),
    InOS (curs (sprim (switch x)), (kenil, ks1 ## kcall f s empenv ks))
         (pumerge po pi) ->
    InOS (SKIP , (kenil, ks1 ## kcall f s empenv ks)) (pumerge po pi).
Proof.
  unfold InOS.
  intros.
  destruct H as (c&ke&ks0&H&HH).
  inversion H.
  subst c ke ks0.
  exists SKIP kenil (ks1##kcall f s empenv ks).
  split;auto.
  destruct HH.
  destruct H0 as (a&b&c&d&e&g).
  tryfalse.
  destruct H0.
  right.
  left.
  auto.
  right.
  right.
  auto.
Qed.

Lemma env_can_get :
  forall le, exists x, getaddr le = x.
Proof.
  intros.
  unfold getaddr.
  destruct le.
  induction lst.
  exists (nil:freelist).
  auto.
  simpl in i.
  simpl.
  destruct a.
  destruct b.
  destruct i.
  apply IHlst in H0.
  destruct H0.
  exists ((b,t)::x).
  subst;auto.
Qed.

Lemma isret_nabt :
  forall (c : cureval) (ke : exprcont) (ks1 : stmtcont)
         (pc po pi : progunit) (ip : intunit) tid 
         (f : fid) (s : stmts) (cst : clientst) (o : taskst) 
         (ks : stmtcont),
    IsRet (c, (ke, ks1)) ->
    InOS (c, (ke, ks1 ## kcall f s empenv kstop)) (pumerge po pi) ->
    ~
      ltstepabt (pc, (po, pi, ip)) tid (c, (ke, ks1 ## kcall f s empenv ks))
      cst o.
Proof.
  intros.
  unfold IsRet in H.
  mytac.
  intro X.
  inversion X.
  destruct H3.
  subst.
  left.
  destruct o as [[]].
  destruct s0 as [[]].
  destruct (env_can_get e0).
  do 3 eexists.
  eapply inapi_step;eauto.
  inversion H;subst pc0 po0 pi0 ip0.
  eapply ostc_step;eauto.
  eapply stmt_step;eauto.
  eapply sret_step;eauto.
  assert (callcont (x##kcall f s empenv ks) = Some (kcall f s empenv ks)).
  eapply  call_int_none_call;eauto.
  eapply H4.
  inversion H;subst;auto.
  apply inos_call.
  auto.
Qed.

Lemma isrete_nabt :
  forall (c : cureval) (ke : exprcont) (ks1 : stmtcont)
         (pc po pi : progunit) (ip : intunit) tid 
         (f : fid) (s : stmts) (cst : clientst) (o : taskst) 
         (ks : stmtcont),
    IsRetE (c, (ke, ks1)) ->
    InOS (c, (ke, ks1 ## kcall f s empenv kstop)) (pumerge po pi) ->
    ~
      ltstepabt (pc, (po, pi, ip)) tid (c, (ke, ks1 ## kcall f s empenv ks))
      cst o.
Proof.
  intros.
  unfold IsRetE in H.
  mytac.
  intro X.
  inversion X.
  destruct H3.
  subst.
  left.
  destruct o as [[]].
  destruct s0 as [[]].
  destruct (env_can_get e0).
  do 3 eexists.
  eapply inapi_step;eauto.
  inversion H;subst pc0 po0 pi0 ip0.
  eapply ostc_step;eauto.
  eapply stmt_step;eauto.
  assert (callcont (kret x0##kcall f s empenv ks) = Some (kcall f s empenv ks)).
  eapply  call_int_none_call;simpl;eauto.
  assert ( callcont (kret x0 ## kcall f s empenv ks)<>None).
  intro.
  tryfalse.
  eapply sretv_step;eauto.
  inversion H;subst;auto.
  apply inos_call.
  auto.
Qed.

Lemma inos_stkinit_still:
  forall (e1 e2 e3 : expr) (ks1 ks : stmtcont) 
         (lenv : env) (po pi : progunit) f s,
    InOS (curs (sprim (stkinit e1 e2 e3)), (kenil, ks1 ##  kcall f s lenv ks))
         (pumerge po pi) ->
    InOS (SKIP , (kenil, ks1 ## kcall f s lenv ks)) (pumerge po pi).
Proof.
  intros.
  unfold InOS in H; simpljoin.
  destruct H0.
  simpljoin; tryfalse.
  unfolds.
  destruct H.
  simpljoin.
  do 3 eexists.
  split; eauto.
  right.
  left.
  do 8 eexists.
  split; eauto.

  do 3 eexists; splits; eauto.
Qed.

Lemma inos_stkfree_still:
  forall (e : expr) (ks1 ks : stmtcont)
         (lenv : env) (po pi : progunit) f s,
    InOS (curs (sprim (stkfree e)), (kenil, ks1 ##  kcall f s lenv ks))
         (pumerge po pi) ->
    InOS (SKIP , (kenil, ks1 ##   kcall f s lenv ks)) (pumerge po pi).
Proof.
  intros.
  unfolds in H.
  simpljoin.
  destruct H0.
  simpljoin; tryfalse.

  destruct H.
  unfolds.
  do 3 eexists.
  split; eauto.

  unfolds.
  do 3 eexists.
  split; eauto.
Qed.


Lemma freeb_sub :
  forall len i b M M',
    freeb M b i len = Some M' -> Maps.sub M' M.
Proof.
  intro.
  inductions len; intros.
  simpl in H.
  inverts H.
  apply sub_refl.
  simpl in H.
  destruct (get M (b, i)) eqn : eq1; tryfalse.
  destruct p.
  destruct b0; tryfalse.
  destruct (freeb M b (i + 1) len) eqn : eq2; tryfalse.
  pose proof IHlen (i + 1)%Z b M m0 eq2; clear IHlen.
  inversion H.

  eapply mem_sub_del; auto.
Qed.


Lemma free_sub :
  forall t b M M',
    free t b M = Some M' -> Maps.sub M' M.
Proof.
  intros.
  unfolds in H.
  eapply freeb_sub.
  apply H.
Qed.

Lemma mem_get_eq :
  forall (m1:mem) m2 a,
    m1 = m2 -> get m1 a = get m2 a.
Proof.
  intros.
  substs.
  auto.
Qed.

Lemma freeb_consistent :
  forall len m1 m1' m2 m2' x1 x2 x2' b i a,
    freeb m1 b i len = Some m1' -> freeb m2 b i len = Some m2' ->
    get m1 a = Some x1 -> get m1' a = None ->
    get m2 a = Some x2 -> get m2' a = Some x2' ->
    False.
Proof.
  intro.
  inductions len; intros.
  simpl in H.
  simpl in H0.
  inverts H.
  rewrite H2 in H1.
  false.
  simpl in H.
  destruct (get m1 (b, i)) eqn : eq1; tryfalse.
  destruct p as (p1&p2).
  destruct p1; tryfalse.
  destruct (freeb m1 b (i + 1) len ) eqn : eq2; tryfalse.
  simpl in H0.
  destruct (get m2 (b, i)) eqn : eq3; tryfalse.
  destruct p as (p3&p4).
  destruct p3; tryfalse.
  destruct (freeb m2 b (i + 1) len ) eqn : eq4; tryfalse.
  inversion H; clear H.
  inversion H0; clear H0.
  assert (get m a = None).
  destruct (get m a) eqn : eq5.
  apply mem_get_eq with (a := a) in H6.
  rewrite H2 in H6.
  
  apply mem_get_eq with (a := a) in H5.
  rewrite H4 in H5.
  destruct (addr_eq_dec (b, i) a) eqn : eq6.
  substs.

  rewrite mem_get_del_none in H5; tryfalse.

  clear - H6 eq5 n.
  rewrite mem_get_del_get_eq in H6; auto.
  unfold get, del in *; simpl in *.
  rewrite H6 in eq5; tryfalse.
  auto.

  assert (get m0 a = Some x2').
  apply mem_get_eq with (a := a) in H6.
  rewrite H2 in H6.
  apply mem_get_eq with (a := a) in H5.
  rewrite H4 in H5.
  destruct (addr_eq_dec (b, i) a) eqn : eq6.
  substs.
  rewrite mem_get_del_none in H5; tryfalse.

  rewrite mem_get_del_get_eq in H5; auto.

  pose proof IHlen m1 m m2 m0 x1 x2 x2' b (i + 1)%Z a eq2 eq4 H1 H H3 H0.
  false.
Qed.

Lemma freeb_inconsistent :
  forall len m1 m2 m3 m4 a b i x1,
    freeb m1 b i len = Some m2 -> get m1 a = Some x1 -> get m2 a = None ->
    get m3 a = None -> freeb m3 b i len = Some m4 ->
    False.
Proof.
  intro.
  induction len; intros.
  simpl in H.
  simpl in H3.
  inverts H.
  rewrite H1 in H0.
  false.

  simpl in H.
  destruct (get m1 (b, i)) eqn : eq1; tryfalse.
  destruct p as (p1&p2).
  destruct p1; tryfalse.
  destruct (freeb m1 b (i + 1)%Z len) eqn : eq2; tryfalse.
  inversion H; clear H.
  simpl in H3.
  destruct (get m3 (b, i)) eqn : eq3; tryfalse.
  destruct p as (p3&p4).
  destruct p3; tryfalse.
  destruct (freeb m3 b (i + 1)%Z len) eqn : eq4; tryfalse.
  inversion H3; clear H3.
  apply mem_get_eq with (a := a) in H5.
  rewrite H1 in H5.
  apply mem_get_eq with (a := a) in H4.

  destruct (addr_eq_dec (b, i) a) eqn : eq5.
  substs.
  unfold get, del in *; simpl in *.
  rewrite eq3 in H2; tryfalse.
  
  destruct (get m a) eqn : eq6; tryfalse.
  rewrite mem_get_del_get_eq in H5; auto.
  tryfalse.

  eapply IHlen.
  apply eq2.
  apply H0.
  auto.
  apply H2.
  apply eq4.
Qed.

Lemma free_consistent :
  forall t m1 m1' m2 m2' x1 x2 x2' b a,
    free t b m1 = Some m1' -> free t b m2 = Some m2' ->
    get m1 a = Some x1 -> get m1' a = None ->
    get m2 a = Some x2 -> get m2' a = Some x2' ->
    False.
Proof.
  intros.
  unfolds in H.
  unfolds in H0.
  pose proof freeb_consistent; eauto.
Qed.

Lemma free_inconsistent :
  forall t m1 m2 m3 m4 a b x1,
    free t b m1 = Some m2 -> get m1 a = Some x1 -> get m2 a = None ->
    get m3 a = None -> free t b m3 = Some m4 ->
    False.
Proof.
  intros.
  unfolds in H.
  unfolds in H3.
  pose proof freeb_inconsistent; eauto.
Qed.


Lemma free_local:
  forall m t b M'' M M' Ms Mf x,
    free t b m = Some M'' -> free t b M = Some M' ->
    join m Ms x -> join x Mf M -> join (merge M'' Ms) Mf M'.
Proof.
  intros.
  lets Hx: free_frame_prop H H0 H1 H2.
  simpljoin.
  eapply mem_join_join_merge12_join; eauto.
Qed.

Lemma free_join_disj:
  forall t b m Ms x M'',
    free t b m = Some M'' ->
    join m Ms x -> disjoint M'' Ms.
Proof.
  intros.
  pose proof free_sub.
  pose proof H1 t b m M'' H; clear H1.
  lets Hx: mem_join_disjoint_eq_merge H0.
  destruct Hx.
  substs.
  eapply mem_sub_disj.
  instantiate (1 := m).
  join auto.
  auto.
Qed.


Lemma free_step :
  forall (pc : progunit)
         (po : fid -> option (type * decllist * decllist * stmts))
         (pi : progunit) (ip : intunit) (al : freelist) 
         (o : taskst) (O : osabst) (Ms : mem)  
         (Mf : mem) (o2 o'' : taskst) (cst cst' : clientst) 
         (Cl' : code) (v : option val) (ks1 ks : stmtcont) 
         (f : fid) (s : stmts) (ft : type) (d1 d2 : decllist)
         tid lasrt M,
    po f = Some (ft, d1, d2, s) ->
    callcont ks1 = None ->
    intcont ks1 = None ->
    freels al (get_mem (get_smem o)) M ->
    InitTaskSt lasrt tid (emple_tst (substaskst o M), O) ->
    joinm2 o Ms Mf o2 ->
    ltstep (pc, (po, pi, ip)) tid
           (curs (sfree al v), (kenil, ks1 ## kcall f s empenv ks)) cst o2 Cl'
           cst' o'' ->
    o'' = emple_tst o2 /\
    cst' = cst /\
    Cl' = (curs (sskip v), (kenil, ks)) /\
    freels nil (get_mem (get_smem o)) M \/
    (exists o' al',
       joinm2 o' Ms Mf o'' /\
       cst' = cst /\
       Cl' = (curs (sfree al' v), (kenil, ks1 ## kcall f s empenv ks)) /\
       freels al' (get_mem (get_smem o')) M /\
       InitTaskSt lasrt tid (emple_tst (substaskst o' M), O)).
Proof.
  intros.
  unfold joinm2 in H4.
  rename H5 into H6.
  destruct H4 as (o1 & H4 & H5).

  destruct o as [[[[]]]].
  simpl in H2.
  simpl in H3.
  unfold InitTaskSt in H3.
  mytac.
  simpl in H3, H7.

  destruct al.
  simpl in H2.
  inversion H2.
  subst M m.
  assert (InOS (curs (sfree nil v), (kenil, ks1 ## kcall f s empenv ks)) (pumerge po pi)).
  unfolds.
  do 3 eexists;split;eauto.
  right.
  left.
  assert (callcont (ks1 ## kcall f s empenv ks) = Some (kcall f s empenv ks)).
  eapply call_int_none_call;eauto.
  do 8 eexists;split;eauto.
  eapply pumerge_get;eauto.
  inversion H6;subst;tryfalse.
  inversion H9;subst pc0 po0 pi0 ip0.
  clear H7 H9 H11.
  inversion H10;subst;tryfalse.
  inversion H7; substs.
  inversion H11; tryfalse.
  inversion H11; subst; tryfalse.
  inversion H9; subst.
  assert (callcont (ks1 ## kcall f s empenv ks) = Some (kcall f s empenv ks)).
  eapply call_int_none_call;eauto.
  rewrite H12 in H14.
  inversion H14;subst f0 s0 le' ks';clear H14.
  left.
  splits;auto.

  inversion H2.
  subst.
  assert (InOS (curs (sfree ((b, t) :: al) v), (kenil, ks1 ## kcall f s empenv ks)) (pumerge po pi)).
  unfolds.
  do 3 eexists;split;eauto.
  right.
  left.
  assert (callcont (ks1 ## kcall f s empenv ks) = Some (kcall f s empenv ks)).
  eapply call_int_none_call;eauto.
  do 8 eexists;split;eauto.
  eapply pumerge_get;eauto.
  
  inversion H6;subst;tryfalse.
  inversion H9;subst pc0 po0 pi0 ip0.
  clear H9 H12.
  inversion H11;subst;tryfalse.
  inversion H9;subst.
  inversion H14;tryfalse.
  inversion H14;subst;tryfalse.
  right.
  unfold joinmem in H4.
  do 6 destruct H4.
  destruct H4.
  destruct H15.
  inversion H15;subst.
  clear H18.
  inversion H12.
  subst b0 t0 al0 v0 ks'.
  unfold joinmem in H5.
  do 6 destruct H5.
  destruct H5.
  inversion H5;subst.
  destruct H15.
  inversion H15;subst x5 x6 x8 x9 x10.
  clear H5 H15.
  inversion H4;subst ge le x1 i au.
  clear H4.
  clear H6 H11 H14 H9 H12.

  assert (
      (exists o' o1' al',
         joinmem o1' Mf (e, e0, M', i0, l) /\
         joinmem o' Ms o1' /\
         cst' = cst' /\
         (curs (sfree al v), (kenil, ks1 ## kcall f s empenv ks)) =
         (curs (sfree al' v), (kenil, ks1 ## kcall f s empenv ks)) /\
         freels al' (get_mem (get_smem o')) M /\
         InitTaskSt lasrt tid (emple_tst (substaskst o' M), O)) ->
      (exists o' al',
         joinm2 o' Ms Mf (e, e0, M', i0, l) /\
         cst' = cst' /\
         (curs (sfree al v), (kenil, ks1 ## kcall f s empenv ks)) =
         (curs (sfree al' v), (kenil, ks1 ## kcall f s empenv ks)) /\
         freels al' (get_mem (get_smem o')) M /\
         InitTaskSt lasrt tid (emple_tst (substaskst o' M), O))
    ).
  intros.
  clear - H4.
  simpljoin.
  unfold joinm2.
  do 2 eexists.
  splits; eauto.
  apply H4; clear H4.

  exists (e,e0, M'', i0 ,l) (e,e0,(merge M'' Ms),i0,l) al;splits;simpl;auto.
  unfold joinmem;simpl.
  do 6 eexists ;splits;eauto.
  eapply free_local;eauto.
  do 6 eexists ;splits;eauto.
  eapply join_merge_disj.
  eapply free_join_disj;eauto.
  unfold InitTaskSt.
  simpl.
  splits;auto.
Qed.


Lemma freeb_mem_join :
  forall len M M1 M2 M' b o,
    join M M1 M2 ->
    freeb M b o len = Some M' ->
    exists M'', freeb M2 b o len = Some M''.
Proof.
  intro.
  induction len; intros.
  simpl in H0.
  simpl.
  eexists; auto.
  simpl in H0.
  unfold get in *; simpl in *.
  destruct (HalfPermMap.get M (b, o)) eqn : eq1; tryfalse.
  destruct (freeb M b (o + 1)%Z len) eqn : eq2; tryfalse.
  pose proof IHlen M M1 M2 m b (o + 1)%Z H eq2.
  destruct H1.
  simpl.
  rewrite H1.
  destruct b0.
  destruct b0; tryfalse.
  assert (get M2 (b, o) = Some (true, c)).
  eapply mem_join_get_get_l_true; eauto.
  unfold get in *; simpl in *.
  rewrite H2; eauto.

  destruct b0.
  destruct b0; tryfalse.
Qed.

Lemma free_step_mem_join :
  forall M M1 M2 M3 M4 M' t b,
    join M M1 M2 ->
    join M2 M3 M4 ->
    free t b M = Some M' ->
    exists M'', free t b M4 = Some M''.
Proof.
  intros.
  unfold free in *.
  assert (exists Mx, join M Mx M4).
  join auto.
  destruct H2 as [Mx].
  clear H H0.
  eapply freeb_mem_join.
  apply H2.
  eauto.
Qed.


Lemma free_nabt :
  forall (o o'' : taskst) (pc : progunit)
         (po : fid -> option (type * decllist * decllist * stmts))
         (pi : progunit) (ip : intunit) tid 
         (f : fid) (ft : type) (d1 d2 : decllist) (s : stmts)
         (ks ks1 : stmtcont) (cst : clientst) (al : freelist)
         (v : option val) (Ms Mf : mem) M,
    callcont ks1 = None ->
    intcont ks1 = None ->
    po f = Some (ft, d1, d2, s) ->
    joinm2 o Ms Mf o'' ->
    freels al (get_mem (get_smem o)) M ->
    ~
      ltstepabt (pc, (po, pi, ip)) tid
      (curs (sfree al v), (kenil, ks1 ## kcall f s empenv ks)) cst o''.
Proof.
  intros.
  rename H3 into H4.
  unfolds in H2.
  destruct H2 as (o' & H2 & H3).
  
  assert (InOS (curs (sfree al v), (kenil, ks1 ## kcall f s empenv ks)) (pumerge po pi)).
  unfold InOS.
  do 3 eexists;splits;eauto.
  right.
  left.
  assert (callcont (ks1 ## kcall f s empenv ks) = Some (kcall f s empenv ks)).
  eapply  call_int_none_call;simpl;eauto.
  do 8 eexists;split;eauto.
  eapply pumerge_get;eauto.
  intro X.
  inversion X.
  destruct H7.
  inversion H6;subst pc0 po0 pi0 ip0.
  subst.
  left.
  destruct o as [[[[]]]].
  clear X H6.
  destruct al.
  unfold joinmem in H2.
  do 7 destruct H2.
  inversion H2;subst.
  destruct H6;subst o'.
  clear H2.
  unfold joinmem in H3.
  destruct H3.
  do 6 destruct H2.
  inversion H2;subst.
  destruct H3;subst o''.
  clear H2.
  do 2 eexists.
  instantiate (2 := (curs (sskip v),(kenil,ks))).
  instantiate (1 := (x5,empenv,x8, x9, x10)).
  exists cst.
  eapply inapi_step;eauto.
  eapply ostc_step;eauto.
  eapply stmt_step;eauto.
  assert (callcont (ks1 ## kcall f s empenv ks) = Some (kcall f s empenv ks)).
  eapply call_int_none_call;eauto.
  eapply sfreeend_step;eauto.
  unfold joinmem in H2.
  do 7 destruct H2.
  inversion H2;subst.
  destruct H6;subst o'.
  clear H2.
  unfold joinmem in H3.
  destruct H3.
  do 6 destruct H2.
  inversion H2;subst.
  destruct H3;subst o''.
  clear H2.
  simpl in H4.
  inversion H4;subst;tryfalse.
  lets Hm:free_step_mem_join H7 H6 H8.
  destruct Hm.
  exists (curs (sfree al v), (kenil, ks1 ## kcall f s empenv ks)) (x5,x6,x,x9,x10) cst.
  eapply inapi_step;eauto.
  eapply ostc_step;eauto.
  eapply stmt_step;eauto.
  eapply sfree_step;eauto.
Qed.
