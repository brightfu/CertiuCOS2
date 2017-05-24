Require Export ucos_include.
Require Import os_ucos_h.
(**Pure Lemmas for OSQCreat**)

Open Scope code_scope.
Open Scope int_scope.
Open Scope Z_scope.

Lemma RL_Tbl_init_prop :  RL_Tbl_Grp_P INIT_EVENT_TBL (Vint32 Int.zero).
Proof.
  unfolds.
  intros.
  splits.
  intros.
  inverts H1.
  split.
  simpl in H0.
  intros.
  destruct H.
  lets Hex : nat8_des H2 H0.
  auto.
  intros.
  rewrite Int.and_zero_l.
  auto.
  inverts H1.
  split.
  rewrite Int.and_zero_l.
  intros.
  apply leftmoven in H.
  unfold Int.zero in H1.
  tryfalse.
  simpl in H0.
  lets Hesx : nat8_des H H0.
  intros.
  unfold Int.zero in Hesx.
  int auto.
  remember (zlt 0 (Int.unsigned v)) as Hb.
  destruct Hb; 
  tryfalse.
  assert (Int.unsigned v = 0)%Z.
  subst v.
  apply unsigned_zero.
  omega.
Qed.

Lemma WLF_OSQ_prop: forall v'47 v'46 i,
                      val_inj
                        (bool_or
                           (val_inj
                              (if Int.ltu ($ OS_MAX_Q_SIZE) i
                               then Some (Vint32 Int.one)
                               else Some (Vint32 Int.zero)))
                           (val_inj
                              (if Int.eq i ($ 0)
                               then Some (Vint32 Int.one)
                               else Some (Vint32 Int.zero)))) = Vint32 Int.zero \/
                      val_inj
                        (bool_or
                           (val_inj
                              (if Int.ltu ($ OS_MAX_Q_SIZE) i
                               then Some (Vint32 Int.one)
                               else Some (Vint32 Int.zero)))
                           (val_inj
                              (if Int.eq i ($ 0)
                               then Some (Vint32 Int.one)
                               else Some (Vint32 Int.zero)))) = Vnull -> 
                      WellformedOSQ
                        (v'47
                           :: Vptr (v'46, Int.zero+ᵢ($ 4+ᵢInt.zero))
                           :: Vptr (v'46, (Int.zero+ᵢ($ 4+ᵢInt.zero))+ᵢInt.mul ($ 4) i)
                           :: Vptr (v'46, Int.zero+ᵢ($ 4+ᵢInt.zero))
                           :: Vptr (v'46, Int.zero+ᵢ($ 4+ᵢInt.zero))
                           :: Vint32 i :: V$0 :: Vptr (v'46, Int.zero) :: nil).
Proof.
  intros.
  remember (Int.ltu ($ OS_MAX_Q_SIZE) i) as Hbool.
  remember (Int.eq i ($ 0)) as Hbol.
  destruct Hbool;destruct Hbol;
  destruct H; simpl in H; tryfalse.
  unfold OS_MAX_Q_SIZE in HeqHbool.
  assert (  0 < Int.unsigned i <= 20).
  clear H .
  int auto.
  unfolds.
  unfold V_OSQStart ,  V_OSQEnd , V_OSQIn,   V_OSQOut,  V_OSQSize,   V_qfreeblk.
  do 7 eexists.
  splits; try (unfold nth_val; eauto).
  simpl; eauto.
  unfold qend_right, arrayelem_addr_right.
  split.
  unfold OS_MAX_Q_SIZE.
  int auto.
  split.
  int auto.
  int auto.
  split.
  unfold ptr_offset_right, ptr_minus.
  rewrite Pos2Z.inj_eqb.
  assert ((Z.pos v'46 =? Z.pos v'46) = true).
  apply  Z.eqb_eq; auto.
  rewrite H1.
  split.
  simpl.
  clear - i.
  repeat progress int auto.
  split.
  split.
  clear -H0.
  repeat progress int auto.
  simpl typelen.
  clear - H0.
  repeat progress int auto.
  assert ( (0 + (4 + 0) + 4 * Int.unsigned i - (0 + (4 + 0))) = 4 * Int.unsigned i) by omega.
  rewrite H1.
  assert ((4 * Int.unsigned i) = ( Int.unsigned i * 4)) by omega.
  rewrite H2.
  assert (( Int.unsigned i * 4 ) mod 4 = 0) by apply  Z_mod_mult.
  simpl Z.of_nat.
  rewrite H3.
  auto.
  simpl; omega.
  simpl typelen.
  simpl Z.of_nat.
  clear -H0.
  int auto.
  repeat progress int auto.
  erewrite Z_prop; try solve [ auto || omega].
  int auto.
  int auto.
  erewrite Z_prop; try solve [ auto || omega]; int auto.
  erewrite Z_prop; try solve [ auto || omega]; int auto.
  int auto.
  int auto.
  int auto.
  int auto.
  int auto.
  int auto.
  unfold  ptr_offset_right, ptr_minus.
  split.
  rewrite Pos2Z.inj_eqb.
  assert ((Z.pos v'46 =? Z.pos v'46) = true).
  apply  Z.eqb_eq; auto.
  rewrite H1.
  simpl typelen.
  simpl Z.of_nat.
  eexists.
  splits.
  split.
  repeat progress  int auto.
  int auto.
  eauto.
  int auto.
  simpl.
  assert (Z.to_nat 0 = 0)%nat.
  simpl; auto.
  unfold nat_of_Z.
  rewrite <- H3.
  eapply Z2Nat.inj_lt; try omega.
  clear -H0 H2.
  repeat progress int auto.
  simpl.
  rewrite Zdiv_0_l.
  omega.
  simpl.
  rewrite Zdiv_0_l.
  omega.
  clear -H0 H2.
  int auto.
  rewrite Pos2Z.inj_eqb.
  assert ((Z.pos v'46 =? Z.pos v'46) = true).
  apply  Z.eqb_eq; auto.
  rewrite H1.
  simpl typelen.
  simpl Z.of_nat.
  eexists.
  splits.
  split.
  repeat progress  int auto.
  int auto.
  eauto.
  int auto.
  simpl.
  clear -n H0 H2.
  assert (Z.to_nat 0 = 0)%nat.
  simpl; auto.
  unfold nat_of_Z.
  rewrite <- H.
  eapply Z2Nat.inj_lt; try omega.
  simpl.
  rewrite Zdiv_0_l.
  omega.
  int auto.
Qed.

Lemma OSQCRT_TCB_prop :
  forall v'37  x  i v'38 v'40 ,
    EcbMod.get v'37 x = None ->
    RH_TCBList_ECBList_P v'37 v'38 v'40 ->
    RH_TCBList_ECBList_P
      (EcbMod.set v'37 x  (absmsgq nil i, nil))
      v'38 v'40.
Proof.
  intros.
  unfolds.
  unfolds in H0.
  destruct H0 as (Ha1 & Ha2 & Ha3 & Ha4).
  split.
  intros.
  destruct Ha1.
  unfolds.
  split.
  intros.
  rewrite EcbMod.set_sem in H2.
  destruct (tidspec.beq x eid).
  destruct H2.
  inverts H2.
  simpl in H3; tryfalse.
  eapply H0; eauto.
  intros.
  rewrite EcbMod.set_sem.
  lets Hres : H1 H2.
  destruct Hres as (x1&y1&qw& Hec & Hin).
  remember (tidspec.beq x eid) as Hbool.
  destruct Hbool.
  apply eq_sym in HeqHbool.
  apply tidspec.beq_true_eq in HeqHbool.
  subst x.
  tryfalse.
  unfold get in *; simpl in *.
  tryfalse.
  do 3 eexists; splits; eauto.
  split.
  destruct Ha2.
  unfolds.
  split.
  intros.
  rewrite EcbMod.set_sem in H2.
  destruct (tidspec.beq x eid).
  destruct H2.
  inverts H2.
  lets Hres : H0 H2.
  eauto.
  intros.
  lets Hres : H1 H2.
  simp join.
  assert (eid = x \/ eid <> x) by tauto.
  destruct H5.
  subst.
  unfold get in *; simpl in *.
  tryfalse.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  eapply H1; eauto.
   split.
  destruct Ha3.
  unfolds.
  split.
  intros.
  rewrite EcbMod.set_sem in H2.
  destruct (tidspec.beq x eid).
  destruct H2.
  inverts H2.
  lets Hres : H0 H2.
  eauto.
  intros.
  lets Hres : H1 H2.
  simp join.
  assert (eid = x \/ eid <> x) by tauto.
  destruct H5.
  subst.
  unfold get in *.
  simpl in *.
  tryfalse.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  eapply H1; eauto.
  destruct Ha4.
  unfolds.
  split.
  intros.
  rewrite EcbMod.set_sem in H2.
  destruct (tidspec.beq x eid).
  destruct H2.
  inverts H2.
  lets Hres : H0 H2.
  eauto.
  split.
  intros.
  assert (TcbMod.get v'38 tid = Some (p, wait (os_stat_mutexsem eid) t, msg)) as Hasd; auto.
  apply H1 in H2.
  simp join.
  assert (eid = x \/ eid <> x) by tauto.
  destruct H5.
  subst.
  unfold get in *; simpl in *.
  tryfalse.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  eapply H1; eauto.
  unfolds.
  intros.
  assert (eid = x \/ eid <> x) by tauto.
  destruct H3.
  subst.
  rewrite EcbMod.set_sem in H2.
   rewrite tidspec.eq_beq_true in H2; auto.
   inverts H2.
 rewrite EcbMod.set_sem in H2.
   rewrite tidspec.neq_beq_false in H2; auto.
   eapply H1; eauto.
Qed.

Lemma ECBList_OSQCRT_prop :
  forall v'41 v'48 v'50 v'22 v'28 v'40
         v'47 v'46 i v'37 v'38 v'45 v'43 x0 v'27,
    RH_TCBList_ECBList_P v'37 v'38 v'40 ->
    EcbMod.get v'37 (v'41, Int.zero) = None ->
    ECBList_P v'22 Vnull v'28 v'27 v'37 v'38->
    ECBList_P (Vptr (v'41, Int.zero)) Vnull
              ((V$OS_EVENT_TYPE_Q
                 :: Vint32 Int.zero
                 :: V$0 :: Vptr (v'48, Int.zero) :: v'50 :: v'22 :: nil,
                INIT_EVENT_TBL) :: v'28)
              (DMsgQ (Vptr (v'48, Int.zero))
                     (v'47
                        :: Vptr (v'46, Int.zero+ᵢ($ 4+ᵢInt.zero))
                        :: Vptr (v'46, (Int.zero+ᵢ($ 4+ᵢInt.zero))+ᵢInt.mul ($ 4) i)
                        :: Vptr (v'46, Int.zero+ᵢ($ 4+ᵢInt.zero))
                        :: Vptr (v'46, Int.zero+ᵢ($ 4+ᵢInt.zero))
                        :: Vint32 i :: V$0 :: Vptr (v'46, Int.zero) :: nil)
                     (v'43 :: x0 :: nil) v'45 :: v'27)
              (EcbMod.set v'37 (v'41, Int.zero) (absmsgq nil  i, nil))
              v'38.
Proof.
  intros.
  unfolds.
  fold ECBList_P.
  eexists.
  split; eauto.
  split.
  unfolds.
  split.
  unfolds.
  destruct H as (Ha1 & Ha2 & Ha3 & Ha4).
  splits.
  unfolds.
  intros.
  unfolds in H.
  simp join.
  simpl in H5.
  lets Hres : prio_prop  H H7; eauto.
  assert (∘(Int.unsigned (Int.shru ($ prio) ($ 3))) < 8)%nat.
  eapply Z_le_nat; eauto.
  split; auto.
  apply Int.unsigned_range_2.
  remember (∘(Int.unsigned (Int.shru ($ prio) ($ 3)))) as  Heq.
  assert (x2=Int.zero) by (eapply nat8_des;eauto).
  subst x2.
  apply int_land_zero in H6; tryfalse.
  unfolds.
  intros.
  usimpl H2.
  unfolds.
  intros.
  usimpl H2.
   unfolds.
  intros.
  usimpl H2.
  destruct H as (Ha1 & Ha2 & Ha3 & Ha4).
  split.
  unfolds.
  splits.
  unfolds.
  intros.
  destruct Ha1 as (Hab & Hac).
  lets Hre : Hac H.
  destruct Hre as (xx & yy & wt & Hec & Hin).
  unfold get in *; simpl in *.
  tryfalse.
  unfolds.
  intros.
  destruct Ha2 as (Hab & Hac).
  lets Hre : Hac H.
  destruct Hre as (xx  & wt & Hec & Hin).
  unfold get in *; simpl in *.
  tryfalse.
   unfolds.
  intros.
  destruct Ha3 as (Hab & Hac).
  lets Hre : Hac H.
  destruct Hre as (xx  & wt & Hec & Hin).
  unfold get in *; simpl in *.
  tryfalse.
  unfolds.
  intros.
  destruct Ha4 as (Hab & Hac & Hacc).
  lets Hre : Hac H.
  destruct Hre as (xx  & wt & Hec & Hin & Hd).
  unfold get in *; simpl in *.
  tryfalse.
  unfolds.
  branch 1.
  simpl;auto.
  do 3 eexists.
  unfold V_OSEventListPtr.
  simpl nth_val .
  splits; eauto.
  instantiate (1:= (absmsgq nil  i, nil)).
  eapply ecbmod_get_sig_set; eauto.
  unfolds.
  splits.
  unfolds.
  do 7 eexists.
  splits; try (  unfolds; simpl; eauto).
  splits.
  splits.
  intros.
  false.
  intros.
  false.
  intros.
  auto.
  intros.
  simp join.
  unfolds.
  auto.
  unfolds.
  eexists.
  splits.
  unfolds; simpl; eauto.
  simpl.
  clear -i.
  mauto.
  unfolds.
  eexists .
  splits.
  unfolds; simpl; eauto.
  rewrite Int.repr_unsigned.
  auto.
  apply Int.unsigned_range.
  clear -i.
  int auto.
  unfolds.
  splits; auto.
Qed.

Lemma  joinsig_neq_get_none:
  forall (A B T : Type) (PermMap0 : PermMap A B T)  x y a  M m,
    x <> y -> 
    joinsig y a m M -> 
    get m x = None -> 
    get M x = None.
Proof.
  unfold TcbJoin.
  intros.
  hy.
  (** TODO: Notation TcbJoin is very ugly! **)
Qed.
  
Lemma  joinsig_neq_get_none_ecbmod:
  forall   x y a  M (m: EcbMod.map),
    x <> y -> 
    joinsig y a m M -> 
    get m x = None -> 
    get M x = None.
  Proof.
    intros.
    eapply  joinsig_neq_get_none; eauto.
Qed.


Lemma ecblist_star_not_inh :
    forall v'28 v'24  eid  v'27 v'37 v'38 s vl P,
              ECBList_P v'24 Vnull v'28 v'27 v'37 v'38 ->
              s |= Astruct eid OS_EVENT vl  **
                evsllseg v'24 Vnull v'28 v'27  ** P ->
              EcbMod.get v'37 eid = None.
Proof.
  inductions v'28;intros.
  simpl in H; simp join.
  unfolds.
  simpl.
  auto.
  unfold ECBList_P in H.
  fold ECBList_P in H.
  simp join.
  destruct v'27.
  tryfalse.
  destruct a.
  simp join.
  unfold evsllseg in H0.
  fold evsllseg in H0.
  sep normal in H0.
  sep destruct H0.
  sep split in H0.
  rewrite H in H5.
  inverts H5.
  sep lower 2%nat in H0. 
  sep lower 3%nat in H0.
  sep lower 1%nat in H0.
  lets Hrs : IHv'28 H4 H0.
  unfold AEventNode in H0.
  unfold AOSEvent in H0.
  unfold node in H0.
  sep normal in H0.
  sep destruct H0.
  sep split in H0.
  simp join.
  inverts H5.
  sep lift 3%nat in H0.
  lets Hs : astruct_neq_ptr H0;
    try solve
        [intro Hf;  unfolds in Hf; destruct Hf as [ Hx | Hf]; try destruct Hf;  simp join; tryfalse].
  eapply joinsig_neq_get_none_ecbmod; eauto.
Qed.

(*
Lemma absimp_qcre_err_return :
  forall P i, 
    can_change_aop P -> 
    (Int.unsigned i <=? 65535 = true) -> 
    absinfer ( <|| qcre (Vint32 i :: nil)||> ** P) ( <|| END  (Some Vnull) ||> ** P).
Proof.
  introv Hc Hi.
  unfolds qcre.
  eapply absinfer_trans.
  eapply absinfer_choice1; eauto.
  eapply absinfer_prim; eauto.
  unfolds.
  intros.
  sep split in H.
  simpl in H0.
  subst.
  exists O (END Some Vnull).
  split; try sep auto.
  eapply hmstep_merge_emp.
  constructors; eauto.
  unfolds.
  eexists.
  splits; eauto.
Qed.

Lemma absimp_qcre_succ_return:
  forall P i qid  qls  tcbls curtid tm,
    can_change_aop P ->
    Int.ltu ($ Q_SIZE) i  = false ->
    EcbMod.get qls qid = None ->
    absinfer ( <||  qcre (Vint32 i :: nil) ||>
                    **HECBList qls **   HTCBList tcbls ** HTime tm **  HCurTCB curtid ** P)
             ( <||  END  (Some (Vptr qid)) ||> **                                                                                                                 
                    HECBList (EcbMod.set qls qid (absmsgq (nil:list val)
                                                          i,
                                                  nil:list tid)) **HTCBList tcbls **  HTime tm **
                    HCurTCB curtid **P).
Proof.
  introv Hc Hi Hjs.
  unfolds qcre.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  pauto.
  2:sep auto.
  pauto.
  eapply absinfer_prim; eauto.
  pauto.
  pauto.
  unfolds.
  intros.
  exists (OSAbstMod.set O absecblsid (absecblist (EcbMod.set qls qid (absmsgq nil i, nil)))).
  exists (END Some (Vptr qid)).
  splits.
  2: cancel_absdata; sep auto.
  sep split in H.
  simpl in H0.
  subst gamma.
  eapply specstep_merge_emp.
  constructors; eauto.
  unfolds.
  eexists.
  splits; eauto.
  do 3 eexists; splits; eauto.
  absdata_solver.
  eapply get_none_joinisig; eauto.
  eapply abst_get_set_eqdom.
  absdata_solver.
  unfolds; auto.
  eapply tidsame_set;eauto.
Qed.
*)

Lemma int_ltu_maxq_eq :
  forall i,
    Int.ltu ($ OS_MAX_Q_SIZE) i = true->
    Int.eq i ($0) = false.
Proof.
  intros.
  unfold OS_MAX_Q_SIZE in H.
  int auto.
Qed.

  
Lemma val_inj_boolor_false:
  forall i,
    val_inj
      (bool_or
         (val_inj
            (if Int.ltu ($ OS_MAX_Q_SIZE) i
             then Some (Vint32 Int.one)
             else Some (Vint32 Int.zero)))
         (val_inj
            (if Int.eq i ($ 0)
             then Some (Vint32 Int.one)
             else Some (Vint32 Int.zero)))) = Vint32 Int.zero \/
    val_inj
      (bool_or
         (val_inj
            (if Int.ltu ($ OS_MAX_Q_SIZE) i
             then Some (Vint32 Int.one)
             else Some (Vint32 Int.zero)))
         (val_inj
            (if Int.eq i ($ 0)
             then Some (Vint32 Int.one)
             else Some (Vint32 Int.zero)))) = Vnull ->
    Int.ltu ($ Q_SIZE) i = false .
Proof.
  intros.
  remember (  Int.ltu ($ Q_SIZE) i ) as Hbool.
  destruct Hbool; auto.
  unfold Q_SIZE in HeqHbool.
  rewrite <- HeqHbool in H.
  apply eq_sym in HeqHbool.
  apply  int_ltu_maxq_eq in HeqHbool.
  rewrite HeqHbool in H.
  simpl in H.
  assert (Int.ltu Int.zero Int.one = true) as Has.
  clear -i.
  int auto.
  rewrite Has in H.
  simpl in H.
  destruct H; tryfalse.
Qed.

Close Scope code_scope.
Close Scope int_scope.
Close Scope Z_scope.


