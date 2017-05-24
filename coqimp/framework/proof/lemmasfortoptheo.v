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
Require Import invariant_prop.
Require Import join_prop.
Require Import rulesoundlib.
Require Import step_prop.
(*
Require Import progtaskstepLib.*)

Import DeprecatedTactic.

Ltac unfoldbug:= try (unfold code in *;unfold tid in *;unfold cont in *).
Ltac unfolddef:=
  try
    (unfold code in *;unfold cont in *;unfold tid in *;unfold TMSpecMod.B in *;
     unfold mmapspec.image in *;
     unfold TOSpecMod.B in *;
     unfold omapspec.image in *;unfold Maps.sub in *;unfold disjoint in *;unfold osabst in *).
     
Inductive lintstep' : hid -> intunit -> code -> taskst -> code -> taskst -> Prop :=
  li_step : forall (C : code) (c : cureval) (ke : exprcont) 
                   (ks : stmtcont) (ir : isr) (si : is) 
                   (i : hid),
            forall (s : stmts) (theta : intunit) (ge le : env) (m : mem),
              C = (c, (ke, ks)) ->
              higherint ir i ->
              (i < INUM)%nat ->
              theta i = Some s ->
              lintstep' i theta C (ge, le, m, ir, (true, si, nil))
                        (curs s, (kenil, kint c ke le ks))
                        (ge, empenv, m, isrupd ir i true, (false, i :: si, nil)).




(*******************************************************)
(*******************************************************)
(*******************************************************)
(*******************************************************)
(*******************************************************)
(*******************************************************)

(*--------*)



(*
Lemma merge_set_eq:forall O O' x y, merge (set O x y) O' = set (merge O O') x y. 
Proof.
  intros.
  apply extensionality.
  intro.
  rewrite merge_sem.
  destruct (absdataidspec.beq x a) eqn : eq1.
  apply absdataidspec.beq_true_eq in eq1.
  substs.
  rewrite set_a_get_a.
  rewrite set_a_get_a.
  destruct (get O' a); auto.
  apply absdataidspec.eq_beq_true; auto.
  apply absdataidspec.eq_beq_true; auto.
  rewrite set_a_get_a'; auto.
  rewrite set_a_get_a'; auto.
  rewrite merge_sem.
  auto.
Qed.


Lemma disj_indom_set_disj: forall O O' x y, indom O x -> disj O O' ->
                                            disj (set O x y) O'.
Proof.
  intros.
  unfold disj.
  intro.
  unfold disj in H0; pose proof H0 a; clear H0.
  unfold indom in H; destruct H.
  destruct (absdataidspec.beq x a) eqn : eq1.
  apply absdataidspec.beq_true_eq in eq1.
  substs.
  rewrite set_a_get_a.
  rewrite H in H1.
  auto.
  apply absdataidspec.eq_beq_true; auto.
  rewrite set_a_get_a'; auto.
Qed.

(*
Lemma GetHPrio_sub_eq: forall o o1 o2 o3 O O' x y, GetHPrio o x -> GetHPrio o1 y -> join o o3 O -> join o1 o2 (merge O O') -> x=y.
Proof.
  intros.
  assert (forall x y, OSAbstMod.get o abtcblsid = Some x -> OSAbstMod.get o1 abtcblsid = Some y -> x = y).
  intros.
  clear H H0.
  unfold join in H1; pose proof H1 abtcblsid; clear H1.
  unfold join in H2; pose proof H2 abtcblsid; clear H2.
  rewrite merge_sem in H0.
  destruct (get o abtcblsid) eqn : eq1;
  destruct (get o3 abtcblsid) eqn : eq2;
  destruct (get O abtcblsid) eqn : eq3;
  destruct (get o2 abtcblsid) eqn : eq4;
  destruct (get O' abtcblsid) eqn : eq5;
  destruct (get o1 abtcblsid) eqn : eq6;
  tryfalse;
  substs; auto;
  inv H4; inv H3; auto.
  unfolds in H; do 4 destruct H.
  destruct H.
  unfolds in H0; do 4 destruct H0.
  destruct H0.
  pose proof H3 (abstcblist x0) (abstcblist x4) H H0; clear H3.
  inv H6.
  clear H1 H2 H H0; clears.
  destruct H5.
  destruct H0.
  destruct H4.
  destruct H3.
  destruct ( tidspec.beq x y) eqn : eq1.
  apply tidspec.beq_true_eq in eq1.
  auto.
  apply tidspec.beq_false_neq in eq1.
  assert (y<>x).
  intro.
  symmetry in H5.
  apply eq1 in H5.
  false.
  pose proof H1 x x1 x2 x3 eq1 H2 H3; clear H1.
  pose proof H4 y x5 x6 x7 H5 H H0; clear H4.
  unfold Int.ltu in *.
  destruct (zlt (Int.unsigned x5) (Int.unsigned x1));tryfalse.
  destruct (zlt (Int.unsigned x1) (Int.unsigned x5));tryfalse.
  omega.
Qed.*)
*)




(*
Lemma swi_rdy_inv''':forall (o : taskst) (Ol Os : map) (Ms Mc : MemMod.map) 
         (I : Inv) (t t' : tid) (S : osstate)
         (o' : env * EnvSpec.B * mem * isr * LocalStSpec.B)  b tp  Mcc sc,
       good_is_S S ->
       GoodI I sc->
       disj Ol Os ->
       MemMod.disj Mc Ms ->
       (forall ab : absop, (substaskst o Ms, Os, ab) |= INV I) ->
       (forall ab : absop, (substaskst o Mc, Ol, ab) |= SWINV I) ->
       (forall ab : absop, (substaskst o Mc, Ol, ab) |=  AHprio sc t' ** Atrue) ->
       projS S t = Some o ->
       projS S t' = Some o' ->
       EnvMod.get (get_genv (get_smem o)) OSTCBCur = Some (b,(Tptr tp)) ->
       store (Tptr tp) Mc (b,0%Z) (Vptr t') = Some Mcc -> 
       exists Mc' Ms' Ol' Os',
       MemMod.disj Mc' Ms' /\
       MemMod.merge Mc' Ms' = MemMod.merge Mcc Ms /\
       disj Ol' Os' /\
       merge Ol' Os' = set (merge Ol Os) curtid (oscurt t') /\
       (forall ab : absop, (substaskst o' Ms', Os', ab) |= INV I) /\
       (forall ab : absop, (substaskst o' Mc', Ol', ab) |= RDYINV I).
Proof.
  intros.
  assert (forall ab : absop, (substaskst o Mcc,set Ol curtid (oscurt t'), ab) |= SWINV I).
  unfold GoodI in *.
  destructs H0.
  intros.
  assert (substaskst o Mcc= substaskst (substaskst o Mc) Mcc).
  destruct o as [[[[]]]];simpl;auto.
  rewrite H13.
  eapply H11;eauto.
  destruct o as [[[[]]]].
  simpl;eauto.
  destruct o as [[[[]]]];simpl;eauto.
  rewrite <- merge_set_eq.
  eapply swi_rdy_inv';eauto.
  apply GoodI_SWINV_indom_curt with (sc:=sc) in H4;auto.
  eapply disj_indom_set_disj;auto.
  eapply disj_store_disj;eauto.
Qed.


Lemma p_eq: forall (pc po pi pc0 po0 pi0:progunit)  (ip ip0:intunit), (pc, (po, pi, ip)) = (pc0, (po0, pi0, ip0)) -> pc = pc0/\ po=po0/\pi=pi0/\ip=ip0.
Proof.
  intros.
  inversion H;subst.
  auto.
Qed.

Lemma code_eq_dec: forall (c c':code), c=c'\/c<>c'.
Proof.
  intros.
  eapply classic.
Qed.

Lemma stmts_dec: forall (s:stmts) s', s= s' \/ s<>s'.
Proof.
  intros.
  eapply classic.
Qed.

(*
Lemma code_eq_stkinit:
  forall (C:code),
    ~(exists e1 e2 e3 ks, C = (curs (sprim (stkinit e1 e2 e3)), (kenil, ks)))\/
    (exists e1 e2 e3 ks, C = (curs (sprim (stkinit e1 e2 e3)), (kenil, ks))).
Proof.
  intros.
  assert ((exists e1 e2 e3 ks, C = (curs (sprim (stkinit e1 e2 e3)), (kenil, ks))) \/
          ~(exists e1 e2 e3 ks, C = (curs (sprim (stkinit e1 e2 e3)), (kenil, ks)))).
  apply classic.
  destruct H;auto.
Qed.

Lemma code_eq_stkfree:
  forall (C:code),
    ~(exists e ks, C = (curs (sprim (stkfree e)), (kenil, ks)))\/
    (exists e ks, C = (curs (sprim (stkfree e)), (kenil, ks))).
Proof.
  intros.
  assert ( (exists e ks, C = (curs (sprim (stkfree e)), (kenil, ks))) \/
           ~(exists e ks, C = (curs (sprim (stkfree e)), (kenil, ks)))).
  apply classic.
  destruct H;auto.
Qed.*)
 *)

Lemma exint_dec: forall c ke ks, ((c,(ke,ks)) = (curs (sprim exint),(kenil,ks))/\callcont ks=None/\intcont ks=None)\/ ~((c,(ke,ks)) = (curs (sprim exint),(kenil,ks))/\callcont ks=None/\intcont ks=None).
Proof.
  intros.
  apply classic.
Qed.


  
(*--------------------------------------------------*)



Lemma api_tlmatch
: forall (po pi : progunit) (ip : intunit) (B : osapispec)
         (C : osintspec) (f : fid) (tp : type) (d1 d2 : decllist) 
         (s : stmts) (D : ossched),
    eqdomOS (po, pi, ip) (B, C, D) ->
    po f = Some (tp, d1, d2, s) ->
    exists ab tl tp0, B f = Some (ab, (tp0, tl)) /\ tlmatch tl d1.
Proof.
  intros.
  unfold eqdomOS in H.
  destruct H.
  destruct H1.
  assert (exists fdef, po f = Some fdef).
  exists (tp, d1, d2, s).
  auto.
  apply H in H3.
  destruct H3.
  destruct x.
  destruct f0.
  do 3 eexists.
  split;eauto.
  eapply H1 with (fspec := (a,(t,t0))) in H0;eauto.
  destruct H0.
  simpl in *;auto.
Qed.

Lemma init_emple
: forall lasrt tid (o : taskst) (O : osabst),
    InitTaskSt lasrt tid (o, O) -> snd (fst (get_smem o)) = emp.
Proof.
  intros.
  unfold InitTaskSt in H.
  destruct H.
  destruct o as [[[[]]]].
  simpl in H0.
  simpl;auto.
Qed.

Lemma good_dl_le_init'
: forall (dl : decllist) (ge : env) (M : mem) (ir : isr) (aux : localst),
    good_decllist dl = true -> good_dl_le dl (ge, emp, M, ir, aux).
Proof.
  intros.
  gen ge M ir aux H.
  induction dl; intros.
  simpl.
  auto.
  simpl.
  simpl in H.
  apply andb_true_iff in H.
  destruct H.
  eapply IHdl in H0.
  split.
  apply andb_true_iff.
  split.
  auto.
  unfolds in H0.
  destruct dl.
  simpl.
  auto.
  destruct H0.
  auto.
  split.
  intro.
  unfold EnvMod.indom in H1.
  destruct H1.
  pose proof (EnvMod.emp_sem i).
  false.
  eapply H0.
Qed.

Lemma InitAemp
: forall (genv lenv : env) (M : mem) (ir : isr) 
         (aux : localst) (O : osabst) lasrt t,
    InitTaskSt lasrt t (genv, lenv, M, ir, aux, O) ->
    forall ab : absop,
      (genv, lenv, M, ir, aux, O, ab)
        |= (Aemp ** p_local lasrt t init_lg ** Aie true ** Ais nil ** Acs nil ** Aisr empisr) **
        A_dom_lenv (getlenvdom dnil).
Proof.
  intros.
  unfolds in H.
  destruct H.
  simpl in H0.
  subst.
  simpl in H.
  lets Hx:H ab.
  unfold p_local.
  sep auto.
  simpl.
  unfold empenv.
  simpl.
  unfolds.
  intros.
  splits;intros.
  unfolds in H4.
  tryfalse.
  mytac.
  tryfalse.
Qed.


Lemma emple_subs_inv
: forall (o o' : taskst) (Ms : mem) (Os : osabst) (I : Inv),
    TStWoMemEq (emple_tst o') (emple_tst o) ->
    satp (substaskst o Ms) Os (INV I) ->
    satp (substaskst o' Ms) Os (INV I).
Proof.
  intros.
  unfolds;intros.
  lets Hx:H0 aop.
  clear H0;rename Hx into H0.
  destruct o as [[[[]]]].
  destruct o' as [[[[]]]].
  trysimplsall.
  unfolds in H.
  simpl in H.
  mytac.
  eapply  INV_irrev_prop; eauto.
Qed.


Lemma join_eqe
: forall (o : taskst) (M M': mem) (o' : taskst),
    joinm2 o M M' o' -> get_lenv (get_smem o) = get_lenv (get_smem o').
Proof.
  intros.
  destruct o as [[[[]]]].
  destruct o' as [[[[]]]].
  unfolds in H.
  unfold joinmem in H.
  mytac.
  simpl;auto.
Qed.

Lemma good_dl_le_care
: forall (o o' : taskst) (dl : decllist),
    get_lenv (get_smem o) = get_lenv (get_smem o') ->
    good_dl_le dl o -> good_dl_le dl o'.
Proof.
  intros.
  destruct o.
  destruct p.
  destruct o'.
  destruct p.
  simpl in H.
  destruct s.
  destruct p.
  destruct s0.
  destruct p.
  simpl in H.
  subst.
  induction dl.
  simpl.
  auto.
  simpl in H0.
  destruct H0.
  destruct H0.
  simpl.
  split; auto.
Qed.


Lemma higherint_update_eq:
  forall (i : hid) (ir : isr), higherint ir i -> ir = isrupd ir i false.
Proof.
  intros.
  unfold higherint in H.
  Import Coq.Logic.FunctionalExtensionality.
  apply functional_extensionality_dep.
  intros.
  assert (x=i \/ x<>i) by tauto.
  destruct H0.
  unfold isrupd.

  symmetry in H0.
  assert (i=x) by auto.
  apply beq_nat_true_iff  in H0.
  rewrite H0.
  apply H.
  omega.
  unfold isrupd.
  apply beq_nat_false_iff in H0.
  rewrite NPeano.Nat.eqb_sym.
  rewrite H0.
  auto.
Qed.

Lemma dl_add_nil_eq
: forall dl : decllist, dl_add dl dnil = dl.
Proof.
  induction dl; intros.
  simpl.
  auto.
  simpl.
  rewrite IHdl.
  auto.
Qed.

Lemma eq_tp
: forall (po pi : progunit) (ip : intunit) (A : osspec) 
         (f : fid) (ab : api_code) (t : type) (tl : typelist) 
         (ft : type) (d1 d2 : decllist) (s : stmts),
    eqdomOS (po, pi, ip) A ->
    fst (fst A) f = Some (ab, (t, tl)) ->
    po f = Some (ft, d1, d2, s) -> ft = t /\ tlmatch tl d1.
Proof.
  intros.
  unfold eqdomOS in H.
  destruct A as (B&C).
  destruct B as (B & A).
  destruct H as (Ha1&Ha2&Ha3).
  assert (exists fdef, po f= Some fdef).
  exists (ft, d1, d2, s).
  auto.
  apply Ha1 in H.
  destruct H as (fspec& H).
  simpl in H0.
  rewrite H0 in H.
  inversion H.
  subst fspec.
  clear H.
  apply Ha2 with (fspec := (ab, (t, tl)))in H1.
  destruct H1.
  simpl in H,H1.
  split;auto.
  auto.
Qed.


Lemma tlmatch_trans'': forall t1 t2 d1 , tlmatch t1 d1 -> tlmatch t2 d1 -> t1 =t2.
Proof.
  induction t1.
  induction t2.
  intros.
  auto.
  intros.
  unfold tlmatch in H.
  destruct d1.
  unfold tlmatch in H0. 
  inversion H0.
  inversion H.
  induction t2.
  intros.
  destruct d1.
  simpl in H.
  inversion H.
  simpl in H0.
  inversion H0.
  intros.
  destruct d1.
  simpl in H.
  inversion H.
  simpl in H,H0.
  destruct H.
  destruct H0.
  subst a a0.
  assert (t1=t2).
  eapply IHt1 ;eauto.
  subst t1;auto.
Qed.


Lemma tlmatch_trans: forall d1 t1 t2, tlmatch t1 d1 -> tlmatch t2 d1 -> t1 =t2.
Proof.
  intros.
  eapply tlmatch_trans'';eauto.
Qed.

Fixpoint length_eq_td (tl:typelist) (dl:decllist) :=
  match tl with
    | nil => match dl with
               | dnil => True
               | _ => False
             end
    | t::tl' => match dl with 
                  | dcons a b dl' => length_eq_td tl' dl'
                  | _ => False
                end
  end.

Lemma tlmatch_lengtheq: forall tl dl, tlmatch tl dl -> length_eq_td tl dl.
Proof.
  induction tl.
  intros.
  simpl in *.
  destruct dl;tryfalse.
  auto.
  induction dl.
  intros.
  simpl in H.
  false.
  intros.
  simpl.
  simpl in H.
  destruct H.
  apply IHtl in H.
  auto.
Qed.

Lemma tl_dl_vl_eq
: forall (tl : list type) (dl : decllist) (vl : list val),
    tlmatch (rev tl) dl -> length vl = length tl -> length_eq vl dl.
Proof.
  intros.
  apply tlmatch_lengtheq in H.
  assert (length (rev tl) = length tl).
  apply List.rev_length.
  rewrite <- H1 in H0.
  remember (rev tl) as tln.
  clear H1.
  clear Heqtln tl.
  generalize vl dl tln H H0.
  clear.
  induction vl.
  intros.
  simpl in H0.
  destruct tln;simpl in H0;tryfalse.
  destruct dl;simpl in *;tryfalse.
  auto.
  induction dl.
  intros.
  destruct tln;simpl in *;tryfalse.
  intros.
  simpl.
  destruct tln.
  simpl in H0;tryfalse.
  simpl in H, H0.
  inversion H0.
  eapply IHvl;eauto.
Qed.


Lemma app_cons_length_lt : forall {A : Type} vl vl' vl'' (v : A),
                             vl ++ v :: vl' = vl'' ->
                             (length vl < length vl'')%nat.
Proof.
  intros.
  substs.
  gen vl' v.
  inductions vl; intros.
  simpl.
  omega.
  simpl.
  apply lt_n_S.
  apply IHvl.
Qed.


Lemma length_dl_revlcons_add : forall dl1 dl2 dl,
                                 dl = revlcons dl1 dl2 ->
                                 length_dl dl = (length_dl dl1 + length_dl dl2)%nat.
Proof.
  intro.
  induction dl1; intros.
  simpl in H.
  substs.
  simpl.
  auto.
  simpl in H.
  pose proof IHdl1 (dcons i t dl2) dl H; clear IHdl1.
  simpl in H0.
  simpl.
  omega.
Qed.

Lemma length_length_dl_eq : forall vl dl,
                              length_eq vl dl -> length vl = length_dl dl.
Proof.
  intro.
  induction vl; intros.
  simpl.
  destruct dl; simpl in H.
  simpl; auto.
  false.
  simpl in H.
  destruct dl; tryfalse.
  simpl.
  apply eq_S.
  apply IHvl.
  auto.
Qed.

Lemma dl_add_dnil_eq : forall dl,
                         dl_add dl dnil = dl.
Proof.
  induction dl; intros.
  simpl.
  auto.
  simpl.
  rewrite IHdl.
  auto.
Qed.

Lemma sub_len_neq
: forall (vl' : list val) (vlh : vallist) (d1 : decllist) 
         (v : val) (vl : list val) (dl' d2 : decllist),
    length_eq vlh d1 ->
    vl' ++ v :: vl = vlh ->
    dl_add dl' dnil = revlcons d1 d2 -> ~ length_eq vl' dl'.
Proof.
  intros.
  apply app_cons_length_lt in H0.
  apply length_dl_revlcons_add in H1.
  apply length_length_dl_eq in H.
  intro.
  apply length_length_dl_eq in H2.
  rewrite H in H0.
  rewrite H2 in H0.
  rewrite dl_add_dnil_eq in H1.
  rewrite H1 in H0.
  omega.
Qed.


Lemma ret_dec:forall c ke ks,~ ((c, (ke, ks)) = (curs sret, (kenil, ks)) /\ callcont ks = None/\intcont ks=None)\/((c, (ke, ks)) = (curs sret, (kenil, ks)) /\ callcont ks = None/\intcont ks=None).
Proof.
  intros.
  assert ( 
      ((c, (ke, ks)) = (curs sret, (kenil, ks)) /\
       callcont ks = None /\ intcont ks = None) \/
      ~( (c, (ke, ks)) = (curs sret, (kenil, ks)) /\
         callcont ks = None /\ intcont ks = None)).
  eapply classic.
  destruct H;auto.
Qed.

Lemma retv_dec: forall c ke ks, ~(exists v ksx, (c,(ke,ks))= (curs (sskip (Some v)),(kenil,kret ksx))/\callcont ksx = None/\intcont ksx=None) \/  (exists v ksx, (c,(ke,ks))= (curs (sskip (Some v)),(kenil,kret ksx))/\callcont ksx = None/\intcont ksx=None).
Proof.
  intros.
  assert ((exists v ksx, (c,(ke,ks))= (curs (sskip (Some v)),(kenil,kret ksx))/\callcont ksx = None/\intcont ksx=None) \/  ~(exists v ksx, (c,(ke,ks))= (curs (sskip (Some v)),(kenil,kret ksx))/\callcont ksx = None/\intcont ksx=None)).
  eapply classic.
  destruct H;auto.
Qed.


Lemma join_tst_wo_mem_eq
: forall (o o' : taskst) (M M': mem), joinm2 o M M' o' -> TStWoMemEq o o'.
Proof.
  intros.
  unfolds in H.
  mytac.
  unfold joinmem in *.
  mytac.
  unfolds.
  splits;auto.
Qed.


Lemma fun_goodks
: forall (pc po pi : progunit) (ip : intunit) 
         (ks1 : stmtcont) (f : fid) (s : stmts) (ks : stmtcont),
    goodks (pc, (po, pi, ip)) (ks1 ## kcall f s empenv ks) ->
    goodks (pc, (po, pi, ip)) ks.
Proof.
  induction ks1;simpl;auto;intros.
  destruct (pumerge po pi f);auto.
  induction ks;auto.
  simpl.
  unfold no_os in H.
  destruct (pumerge po pi f0).
  inversion H.
  auto.
  unfold no_os in H.
  unfold goodks.
  tryfalse.
  destruct (pumerge po pi f).
  eapply IHks1;eauto.
  apply IHks1 with (f:=f0) (s:=s0) ;auto.

  eapply no_os_goodks';eauto.
  false.
Qed.


Lemma proj_stneq_ex: forall S S' t t' or, 
                       Steq S S' t -> t'<>t ->  projS S t' = Some or ->
                       projS S' t' =
                       Some
                         (
                           ((gets_g S'),
                            (get_env (get_smem or)),
                            (gets_m S')),
                           
                           
                           (snd (fst S')),
                           (snd or) 
                         ).
Proof.
    unfold Steq. unfold projS.
  intros.
  destruct or.
  destruct p.
  destruct p.
  destruct p.
  destruct S.
  destruct p.
  destruct S'.
  destruct p.
  destruct H.
  unfold Dteq in H.
  destruct c.
  destruct p.
  destruct c0.
  destruct p.
  unfold Piteq in H2.
  pose proof (H t' H0).
  pose proof (H2 t' H0).
  unfold projD in H1.
  destruct (get c t') eqn:eq1.
  destruct (get l0 t') eqn:eq2.
  unfold projD.
  rewrite <- H3.
  rewrite <- H4.
  simpl.
  unfold gets_g.
  unfold get_env.
  unfold gets_m.
  simpl.
  inversion H1.
  subst.
  reflexivity.
  inversion H1.
  inversion H1.
Qed.

Lemma IntSeq'': 
  forall pc (po:progunit) pi ip A p c ke ks t I r
         lenv si isrreg (oi:taskst) o Oi ab absi c' ke' ks' i ch keh ksh ge OO lasrt lg Ml Ol,
    (*OSAbstMod.get O curtid = Some (oscurt t) ->*)
    no_call_api_os po pi ip ->
    no_call_api (c',(ke',ks')) po->
    GoodI I (snd A) lasrt ->
    join Oi Ol OO ->
    joinmem oi Ml o ->
    r = iretasrt i isrreg si I ge lasrt t lg->
    (snd (fst A)) i = Some absi ->
    (*ab = (absi b,(ch,(keh,ksh))) \/ ab =  (absi b,(ch,(keh,ksh))) ->*)
    ( forall Mlinv Olinv, satp ((ge,lenv,Mlinv),(isrupd isrreg i false),(true,si,nil)) Olinv (p_local lasrt t lg) ->
    TaskSim (pc,(po,pi,ip)) (c,(ke,ks)) ((ge,lenv,(merge Ml Mlinv)),(isrupd isrreg i false),(true,si,nil)) (pc,A) (ch,(keh,ksh))(merge Ol Olinv) lasrt I p t) ->
    goodks (pc,(po,pi,ip)) (ks'##kint c ke lenv ks) ->
    MethSim pi (snd A) (c',(ke',ks')) oi ab Oi lasrt I retfalse r retfalse t-> 
    InOS (c',(ke', ks'## kint c ke lenv ks)) (pumerge po pi) ->
    TaskSim (pc,(po,pi,ip)) (c',(ke', ks'## kint c ke lenv ks)) o (pc,A) (curs (hapi_code ab),(kenil,kevent ch keh ksh)) OO lasrt I p t.
Proof.
  cofix CIH.
  introv Hnocallos.
  introv Hnocallc.
  introv Hgoodi.
  intros.
  destruct o as [[[[]]]].
  unfolds in H0.
  destruct H0 as (Ge&Ee&M1&M2&ir0&ls&Hf1&Hf2&Hf3).
  inversion Hf2.
  subst Ge Ee M2 ir0 ls.
  rename M1 into mi.
  subst oi.
  clear Hf2.
  apply task_sim.
  intros.
  
  destruct (exint_dec c' ke' ks').
  destruct H10 as (Hc&Hcallcont &Hintcont).
  inverts Hc.
  inverts H9;tryfalse.
  inverts H11;tryfalse.
  inverts H9;tryfalse.
  inverts H13;tryfalse.
  inverts H13;tryfalse.
  inversion H10;subst pc0 po0 pi0 ip0.
  subst.
  clear H10.
  inverts H9.

  assert (intcont (ks' ## kint c ke lenv ks) = Some (kint c ke lenv ks)).

  eapply intcont_local;eauto.
  rewrite H1 in H13.
  inversion H13;subst c0 ke0 le' ks'0.
  clear H13.
  
  unfolds in H7.
  mytac.
  rename x into o1.
  unfold joinmem in H9.
  destruct H9 as (Ge&Ee&M1&M2&ir0&ls&Hf1&Hf2&Hf4).
  inversion Hf2.
  subst Ge Ee M2 ir0 ls.
  subst o1.
  clear Hf2.
  unfold joinmem in H7.
  destruct H7 as (Ge&Ee&M0&M2&ir0&ls&Hf1&Hf2&Hf5).
  inversion Hf2.
  subst Ge Ee M2 ir0 ls.
  inverts Hf1.
  clear Hf2.
  
  inversion H5;subst.
  assert (disjoint Oi Os).
  clear -H H8.
  unfolds;geat.

  assert ( (curs (sprim exint), (kenil, ks')) =
           (curs (sprim exint), (kenil, ks'))) as Hc by auto.
  unfolds in H18;destruct H18.
  lets Hmsim:H14 Hc Hcallcont Hintcont H18;eauto.
  unfold getmem.
  simpl.
  clear -Hf3 Hf5.
  unfolds;join auto.
  destruct Hmsim as (gamma'&OO'&O'&Os'&Hhmstep&Hojoin'&Hinv'&Hlinv'&Hrspec).
  unfold iretasrt in Hrspec.
 
  lets Hsub:ret_st Hrspec.
  destruct Hsub as (Ha1&Ha2&Ha3&Ha4&Ha5).
  subst.
  simpl substaskst in *.

  
  eapply iret_spec with (m:=mi) (O:=O') (Os:=Os') (Ms:=Ms) (is':= si) (i:=i) (isrreg:= isrreg) (ab':=spec_done None) (MM:=merge mi Ms) (OO:=OO') in Hinv';eauto.
  
  destruct Hinv' as (Mlinv'&Mx'&Olinv'&Ox'&Hff3&Hff4&Hff5&Hff6).
  exists (ch,(keh,ksh)) (merge Ol OO') (ge,lenv,(merge Ml Mlinv'), isrupd isrreg i false,(true,si,(nil:cs))).
  exists Mx' (merge Ol Olinv') Ox'.

  simpl substaskst in *.
  splits;auto.
  Focus 2.
  unfold joinm2.
  exists (ge,lenv, M1, ( isrupd isrreg i false), (true,si,(nil:cs))).
  splits;unfolds.
  do 6 eexists;splits;eauto.

  eapply join_join_merge;eauto.
  do 6 eexists;splits;eauto.

  eapply htstepstar_compose_tail with (c':=(curs (hapi_code (spec_done None)), (kenil, kevent ch keh ksh))) (O':=(merge Ol OO')).

  eapply osapi_lift' with (cst:=cst') (pc:=pc) (A:=A) (t:=t) (ke:=kenil) (ks:= kevent ch keh ksh)in Hhmstep;eauto.
  eapply htstepstar_O_local with (Of:=Ol) (OO:=OO0)in Hhmstep.
  mytac.
  apply join_comm in H20.
  apply map_join_merge' in H20;subst.
  instantiate (1:=cst').
  assert (gamma' = (END None)).
  clear -Hrspec.
  simpl in Hrspec;mytac.
  subst gamma'.
  eapply H19.
  clear -H H8 H18.
  join auto.

  eapply hapi_step;eauto.
  eapply hintex_step;eauto.
  assert (disjoint Ol x).
  clear - H H8 H18.
  unfolds;join auto.

  eapply hmstepstar_disj in H19;eauto.
  clear -H19 Hff4.

  eapply join_disj_merge_merge;eauto.

  eapply inv_ncare_le;eauto.
  assert (disjoint Ml Mlinv').
  clear -Hff3 Hf5 Hf3.

  eapply join_join_join_merge_disj with (Ms:=Ms);eauto.
  assert (disjoint Ol Olinv').
  assert (disjoint Ol x).
  clear - H H8 H18.
  unfolds;join auto.
  eapply hmstepstar_disj in Hhmstep;eauto.
  clear -Hff4 Hhmstep.
  unfold disjoint in *.
  join auto.
  assert ( (merge Ol Olinv') = (merge Olinv' Ol)).
  apply disjoint_merge_sym;auto.
  rewrite H21.
  rewrite disjoint_merge_sym;auto.
  eapply CurLINV_merge_hold;eauto.
  apply disj_sym;auto.
  apply disj_sym;auto.
  assert (satp (ge, le, Mlinv', isrupd isrreg i false, (true, si, nil)) Olinv'
           (CurLINV lasrt t)).
  clear -Hff6.
  unfold satp in *.
  intros.
  lets Hx: Hff6 aop.
  unfold CurLINV.
  unfold p_local in *.
  exists lg.
  sep auto.
  eapply CurLINV_ignore_int;eauto.
  eapply H3;eauto.

  eapply p_local_ignore_int;eauto.
  eapply map_join_merge.
  join auto.
  
  (*-----------------------------------------*)
  
  unfolds in H7.
  mytac.
  rename x into o1.
  unfold joinmem in H7.
  destruct H7 as (Ge&Ee&M2&M1&ir0&ls&Hf1&Hf2&Hf4).
  inversion Hf1.
  subst Ge Ee M2 ir0 ls.
  subst o1.
  clear Hf1.
  unfold joinmem in H11.
  destruct H11 as (Ge&Ee&M2&M0&ir0&ls&Hf1&Hf2&Hf5).
  inversion Hf1.
  subst Ge Ee M2 ir0 ls.
  inverts Hf1.
  subst o2.
  rename M0 into m0.
  rename m into M0.
  
  inversion H5;subst.

  
  lets Hltstep: ltstep_no_exint H6 H9 H10 H4;eauto.
  destruct Hltstep as (c''&ke''&ks''&Hcl'&Hinos&Hcsteq&Hosstep).
  rename  Hosstep into Hossteppre.

  lets Hosstep: no_call_api_loststep_eq Hossteppre;eauto.
  eapply H1 with (Ms:=Ms) (Mf:=merge Ml Mf) (Os:=Os) (OO:=merge Os Oi) in Hosstep;auto.
  subst Cl' cst'.
  destruct Hosstep as (gamma'&OO'&o'&Ms'&O'&Os'&Hhmstep&Hlj&Hhj&Hinv'&Hlinv'&Hmsim).
  rename ge into GG.
  destruct o' as ((((ge&le)&m)&ir)&((ie&is)&cs)).
  unfold joinm2 in Hlj.
  destruct Hlj as (o1&Hlj&Hlj').
  unfolds in Hlj.
  destruct Hlj as (Ge&Ee&Mx&M'&ir0&ls&Hf1&Hf2&Hff3).
  inversion Hf1.
  subst Ge Ee Mx ir0 ls.
  subst o1.
  clear Hf1.
  unfold joinmem in Hlj'.
  destruct Hlj' as (Ge&Ee&Mx&m0'&ir0&ls&Hf1&Hf2&Hff4).
  inversion Hf1.
  subst Ge Ee Mx ir0 ls.
  subst o''.
  clear Hf1.
  exists (curs (hapi_code gamma'), (kenil, kevent ch keh ksh)) (merge Ol OO') (ge,le,(merge Ml m),ir,(ie,is,cs)) Ms' (merge Ol O') Os'.
  splits;auto.


  eapply osapi_lift' with (cst:=cst) (pc:=pc) (A:=A) (t:=t) (ke:=kenil) (ks:= kevent ch keh ksh)in Hhmstep;eauto.
  eapply htstepstar_O_local with (Of:=Ol) (OO:=OO0)in Hhmstep.
  mytac.
  apply join_comm in H19.
  apply map_join_merge' in H19;subst.
  auto.
  eapply join_join_join_merge with (Ms:=OO);eauto.
  apply join_comm;auto.


  unfold joinm2.
  exists (ge, le, (merge Ml M'), ir, (ie, is, cs)).
  split;unfolds.
  do 6 eexists;splits;eauto.
  eapply join_disj_merge_merge;eauto.

  apply disj_sym.
  eapply disj_merge_join_disj_intro;eauto.
  clear -Hf3 Hf4 Hf5.
  unfolds;join auto.
  do 6 eexists;splits;eauto.

  eapply disj_join_join_merge;eauto.
  clear -Hf3 Hf4 Hf5.
  unfolds;join auto.
  eapply join_disj_merge_merge;eauto.
  eapply hmstepstar_disj;eauto.
  eapply disj_merge_intro_r;eauto.
  split;unfolds;join auto.

  assert (disjoint Ml m).
  eapply disj_merge_join_disj_intro in Hff4;eauto.
  clear - Hff3 Hff4;unfold disjoint in *;join auto.
  unfolds;join auto.
  assert (disjoint Ol O').
  assert (disjoint Ol OO').
  eapply hmstepstar_disj in Hhmstep;eauto.
  eapply disj_merge_intro_r;eauto.
  split;unfolds;join auto.
  clear -H19 Hhj.
  unfold disjoint in *.
  join auto.
  assert ( (merge Ol O') = (merge O' Ol)).
  apply disjoint_merge_sym;auto.
  rewrite H20.
  rewrite disjoint_merge_sym;auto.
  eapply CurLINV_merge_hold;eauto.
  apply disj_sym;auto.
  apply disj_sym;auto.

  eapply CIH with  (isrreg:=isrreg) (si:=si) (Ml:=Ml) (ab:=gamma');eauto.

  eapply no_call_api_loststep_still;eauto.
  apply join_comm.
  apply join_merge_disj.
  assert (disjoint Ol OO').
  eapply hmstepstar_disj;eauto.
  eapply disj_merge_intro_r;eauto.
  split;unfolds;join auto.
  unfold disjoint in *;join auto.
  unfolds.
  do 6 eexists;splits;eauto.
  apply join_comm.
  apply join_merge_disj.
  eapply disj_merge_join_disj_intro in Hff4;eauto.
  clear - Hff3 Hff4;unfold disjoint in *;join auto.
  unfolds;join auto.

  eapply ltstep_goodks;eauto.

  unfolds.
  exists ((e, e0, merge mi Ms, i0, l)).
  split;unfolds;
  do 6 eexists;splits;eauto.
  apply join_merge_disj.
  unfolds;join auto.

  eapply join_merge_merge_recompose;eauto.
  apply join_comm.
  apply join_merge_disj.
  unfolds;join auto.

  (*--------------------------------------------*)

  intros.
  inversion H9;subst;tryfalse.
  (*------------------------------------*)
  intros.
  inversion H0;subst c' ke' ks0.
  inversion H5;subst.
  simpl substaskst in *.
  apply H11 with (ks:=ks') (x0:=x) (OO:=merge Oi Os)in H7;auto.
  destruct H7 as (gamma'&sleft&OO'&oll&Mc&O'&Os'&Oll&Oc&Hgammaeq&Hhm&Hlj&Hhj&Hhj'&Hinv&Hswinv&Hlinv&Hmsim).
  rename ge into GG.
  subst gamma'.
  destruct oll as [[[[]]]].
  unfolds in Hlj.
  destruct Hlj as (Ge&Ee&Mll&m0'&ir0&ls&Hf1&Hf2&Hff4).
  inversion Hf1.
  subst Ge Ee m0 ir0 ls.
  inversion Hf2;subst e1 e2 m0' i1 l0.
  clear Hf2.
  clear Hf1.
  exists (curs (hapi_code (sched;; sleft)), (kenil,kevent ch keh ksh)) sleft (kenil,kevent ch keh ksh).
  exists (merge Ol OO') Mc (e,e0,(merge Ml Mll),i0,l).
  exists (merge Ol O') Os' (merge Ol Oll) Oc.
  splits;auto.
  intros.
  eapply osapi_lift' with (cst:=cst) (pc:=pc) (A:=A) (t:=t) (ke:=kenil) (ks:= kevent ch keh ksh)in Hhm;eauto.
  eapply htstepstar_O_local with (Of:=Ol) (OO:=OO0)in Hhm.
  mytac.
  apply join_comm in H7.
  apply map_join_merge' in H7;subst.
  auto.

  eapply join_join_join_merge';eauto.
  apply join_comm;auto.
  unfolds.
  do 6 eexists;splits;eauto.
  eapply join_join_join_merge;eauto.
  apply join_comm;auto.
  eapply join_disj_merge_merge;eauto.
  eapply hmstepstar_disj;eauto.
  eapply disj_merge_intro_r;eauto.
  split;unfolds;join auto.
  eapply join_disj_merge_merge;eauto.
  assert (disjoint Ol OO').
  eapply hmstepstar_disj;eauto.
  eapply disj_merge_intro_r;eauto.
  split;unfolds;join auto.
  unfold disjoint in *;join auto.
  splits;auto.

  eapply linvtrue_merge_hold;eauto.
  unfolds;join auto.
  assert (disjoint Ol OO').
  eapply hmstepstar_disj;eauto.
  eapply disj_merge_intro_r;eauto.
  split;unfolds;join auto.
  unfold disjoint in *;join auto.
  destruct Hmsim.
  Focus 2.
  right;auto.
  left.
  mytac.
  simpl getsched;auto.
  intros.
  eapply CIH with (isrreg:=isrreg) (si:=si) (Ml:=Ml) (ab:=sleft) (oi:=(e, e0, merge Mll Mc', i0, l)) (Ol:=Ol) (Oi:=merge Oll Oc');eauto.
  assert (disjoint Oll Ol).
  assert (disjoint Ol OO').
  eapply hmstepstar_disj;eauto.
  eapply disj_merge_intro_r;eauto.
  split;unfolds;join auto.
  unfold disjoint in *;join auto.
  apply join_comm in H20.
  eapply disj_join_join_merge;eauto.
  rewrite disjoint_merge_sym;auto.
  destruct o' as [[[[]]]].
  unfolds in H19;mytac.
  unfolds;do 6 eexists;splits;eauto.
  assert (disjoint Mll Ml).
  unfolds;join auto.
  eapply disj_join_join_merge;eauto.
  rewrite disjoint_merge_sym;auto.
  apply join_comm;auto.
  eapply H7;eauto.
  unfolds;do 6 eexists;splits;eauto.
  apply join_merge_disj.
  unfolds in H19;mytac.
  assert (disjoint Mll Ml).
  unfolds;join auto.
  apply disj_sym.
  eapply disj_merge_join_disj_intro;eauto.
  rewrite disjoint_merge_sym;eauto.
  apply join_comm;eauto.
  assert (disjoint Oll Ol).
  assert (disjoint Ol OO').
  eapply hmstepstar_disj;eauto.
  eapply disj_merge_intro_r;eauto.
  split;unfolds;join auto.
  unfold disjoint in *;join auto.
  apply join_merge_disj.
  apply disj_sym.
  eapply disj_merge_join_disj_intro;eauto.
  rewrite disjoint_merge_sym;eauto.
  apply join_comm;eauto.

  eapply int_inos_sw_still.
  eauto.
  unfold getmem in *;simpl.
  unfolds in H8;simpl in H8.
  unfolds;join auto.
  apply join_merge_disj.
  unfolds;join auto.
  (*-------------------------------------*)
  unfold IsEnd.
  intros.
  inversion H5.
  subst.
  destruct H0 as (v&H0).
  inversion H0;tryfalse.
  destruct ks';tryfalse.
  (*--------------------------------------*)
  intros.
  inversion H5;subst.
  unfold joinm2 in H11.
  mytac.
 
  unfold joinmem in H1.
  destruct H1 as (Ge&Ee&M0&M2&ir0&ls&Hf1&Hf2&Hff3).
  inverts Hf1.
  subst x.

  unfold joinmem in H11.
  destruct H11 as (g&e&M1&M3&ir&ls0&Hf1&Hf2&Hf4).
  inversion Hf1;subst g e M1 ir ls0.
  subst o';clear Hf1.

  simpl substaskst in *.
  cut (joinm2 (Ge, Ee, mi, ir0, ls) Ms (merge Ml Mf) (Ge, Ee, M3, ir0, ls)).
  intros.
  lets Habt: H21 H10 H1;eauto.
  Focus 2.

  eapply int_nabt_lift in Habt;eauto. 
  destruct Habt;eauto.

  eapply inos_int;eauto.
  unfolds;join auto.

  unfold notabort.
  splits;eauto.
  
  unfold IsSwitch.
  auto.
  intro X.
  destruct H7.
  unfolds.
  mytac.
  do 2 eexists;eauto.

  intro X.
  unfold IsEnd in X.
  destruct X as (v&X).

  assert (  disjoint (getmem (Ge, Ee, mi, ir0, ls)) Ms).
  unfold getmem.
  unfolds.
  simpl.
  join auto.
  assert (exists Ox, join Oi Os Ox).
  join auto.
  destruct H24.
  lets XX: H17 X H10  H11 H24;eauto. 
  
  mytac.
  unfold retfalse in H29.
  unfold sat in H29.
  inversion H29.
  
  intro X.
  unfold IsRet  in  X.
  destruct X as (ks0&X&XX&XXX).
  
  assert (  disjoint (getmem (Ge, Ee, mi, ir0, ls)) Ms).
  unfold getmem.
  unfolds.
  simpl.
  join auto.
  assert (exists Ox, join Oi Os Ox).
  join auto.
  destruct H24.
  lets Hx: H18 X H10  H11 H24;eauto. 
  mytac.
  unfold retfalse in H29.
  unfold sat in H29.
  inversion H29.

  intro X.
  unfold IsRetE  in  X.
  destruct X as (v&ks0&X&XX&XXX).
  
  assert (  disjoint (getmem (Ge, Ee, mi, ir0, ls)) Ms).
  unfold getmem.
  unfolds.
  simpl.
  join auto.
  assert (exists Ox, join Oi Os Ox).
  join auto.
  destruct H24.
  lets Hx: H19 X H10  H11 H24;eauto. 
  mytac.
  unfold retfalse in H29.
  unfold sat in H29.
  inversion H29.

  intro X.
  assert (IsIRet (c', (ke', ks'))) as Hf;auto.
  unfold IsIRet in X.
  destruct X as (ks0&X&XX&XXX).
  assert (  disjoint (getmem (Ge, Ee, mi, ir0, ls)) Ms).
  unfold getmem.
  unfolds.
  simpl.
  join auto.
  assert (exists Ox, join Oi Os Ox).
  join auto.
  destruct H24.
  lets Hx: H20 X XXX H11 H24;eauto. 
  mytac.

  eapply isiret_nabt in Hf;eauto.

  intros X.
  unfolds in X.
  destruct H8;unfolds.
  mytac.
  eauto.
  
  intros X.
  unfolds in X.
  destruct H9;unfolds.
  mytac.
  eauto.
  
  unfolds.
  exists (Ge,Ee,merge mi Ms,ir0,ls).
  split;unfolds;do 6 eexists;splits;eauto.
  apply join_merge_disj.
  unfolds;join auto.
  eapply join_merge_merge_recompose;eauto.

  (*-------------stkinit---------------*)
  intros.
  inverts H0.
  inverts H5.
  simpl substaskst in *.
  clear H0 H10 H11 H12 H13 H14 H15 H17.
  eapply H16 with (OO:=merge Oi Os) in H7;eauto.
  destruct H7 as (gamma'&v1&v2&t'&pri&sleft&OO'&OO''&ol&Mcre&O'&Os'&Oll&Ocre&H7).
  mytac.
  
  exists (curs (hapi_code (spec_crt v1 v2 (Vint32 pri);; sleft)), (kenil,kevent ch keh ksh)) v1 v2 t' pri.
  exists sleft (kenil,kevent ch keh ksh).
  exists (merge Ol OO') (merge Ol OO'').
  destruct ol as [[[[]]]].
  unfolds in H13.
  destruct H13 as (g&le&Mll&M3&ir&ls0&Hf1&Hf2&Hf4).
  inversion Hf2;subst g le M3 ir ls0.
  inverts Hf1;clear Hf2.
  exists (e, e0, merge Ml Mll, i0, l) Mcre (merge Ol O') Os' (merge Ol Oll) Ocre.
  simpl get_smem in *.
  splits;eauto.
  eapply evalval_eq_prop;eauto.
  unfolds;join auto.
  eapply evalval_eq_prop;eauto.
  unfolds;join auto.
  eapply evalval_eq_prop;eauto.
  unfolds;join auto.
  intros.
  
  eapply osapi_lift' with (cst:=cst) (pc:=pc) (A:=A) (t:=t) (ke:=kenil) (ks:= kevent ch keh ksh)in H11;eauto.
  eapply htstepstar_O_local with (Of:=Ol) (OO:=OO0)in H11.
  mytac.
  apply join_comm in H1.
  apply map_join_merge' in H1;subst.
  auto.
  eapply join_join_join_merge';eauto.
  apply join_comm;auto.

  eapply abs_crt_step_local;eauto.
  apply disj_sym.
  eapply hmstepstar_disj;eauto.
  eapply disj_merge_intro_r;eauto.
  split;unfolds;join auto.
  unfolds;do 6 eexists;splits;eauto.
  eapply join_join_join_merge;eauto.
  apply join_comm;auto.
  splits;eauto.
  eapply join_disj_merge_merge;eauto.

  eapply abs_crt_disj;eauto.
  eapply hmstepstar_disj;eauto.
  eapply disj_merge_intro_r;eauto.
  split;unfolds;join auto.
  eapply join_disj_merge_merge;eauto.
  assert (disjoint Ol OO'').
  eapply abs_crt_disj;eauto.
  eapply hmstepstar_disj;eauto.
  eapply disj_merge_intro_r;eauto.
  split;unfolds;join auto.
  unfold disjoint in *.
  join auto.
  assert(disjoint Ml Mll).
  unfolds;join auto.
  assert (disjoint Ol Oll).
  assert (disjoint Ol OO'').
  eapply abs_crt_disj;eauto.
  eapply hmstepstar_disj;eauto.
  eapply disj_merge_intro_r;eauto.
  split;unfolds;join auto.
  unfold disjoint in *;join auto.
  assert ( (merge Ol Oll) = (merge Oll Ol)).
  apply disjoint_merge_sym;auto.
  rewrite H13.
  rewrite disjoint_merge_sym;auto.
  eapply CurLINV_merge_hold;eauto.
  apply disj_sym;auto.
  apply disj_sym;auto.
  eapply CIH;eauto.
  apply join_comm.
  apply join_merge_disj.
  assert (disjoint Ol OO'').
  eapply abs_crt_disj;eauto.
  eapply hmstepstar_disj;eauto.
  eapply disj_merge_intro_r;eauto.
  split;unfolds;join auto.
  unfold disjoint in *;join auto.
  unfolds.
  do 6 eexists;splits;eauto.
  apply join_comm.
  apply join_merge_disj.
  unfolds;join auto.
  eapply int_inos_stkinit_still;eauto.
  unfold getmem in *;simpl.
  simpl in H8.
  unfold disjoint in *;join auto.
  apply join_merge_disj.
  unfolds;join auto.
  (*-------------stk free----------------*)
  intros.
  inverts H0.
  inverts H5.
  simpl substaskst in *.
  clear H0 H10 H11 H12 H13 H14 H15 H16.
  eapply H17 with (OO:=merge Oi Os) in H7;eauto.
  destruct H7 as (gamma'&pri&sleft&t'&OO'&OO''&O'&Os'&Oll&H7).
  mytac.
  destruct H7.
  (*del self*)
  mytac.
  exists (curs (hapi_code (spec_del (Vint32 pri);; sleft)), (kenil,kevent ch keh ksh)) pri.
  exists sleft (kenil,kevent ch keh ksh) t'.
  exists (merge Ol OO') (merge Ol OO'').
  exists (merge Ol O') Os'.
  simpl get_smem in *.
  splits;eauto.
  eapply evalval_eq_prop;eauto.
  unfolds;join auto.
  intros.
  eapply osapi_lift' with (cst:=cst) (pc:=pc) (A:=A) (t:=t) (ke:=kenil) (ks:= kevent ch keh ksh)in H5;eauto.
  eapply htstepstar_O_local with (Of:=Ol) (OO:=OO0)in H5.
  mytac.
  apply join_comm in H13.
  apply map_join_merge' in H13;subst.
  auto.
  eapply join_join_join_merge';eauto.
  apply join_comm;auto.
  left.
  splits;auto.
  eapply abs_delself_step_local;eauto.
  apply disj_sym.
  eapply hmstepstar_disj;eauto.
  eapply disj_merge_intro_r;eauto.
  split;unfolds;join auto.
  eapply join_join_join_merge;eauto.

  apply join_merge_disj.
  eapply abs_delself_disj;eauto.
  eapply hmstepstar_disj;eauto.
  eapply disj_merge_intro_r;eauto.
  split;unfolds;join auto.
  assert (m = merge mi Ml).
  eapply map_join_merge';auto.
  subst m.
  assert (disjoint Ol O').
  assert (disjoint Ol OO'').
  eapply abs_delself_disj;eauto.
  eapply hmstepstar_disj;eauto.
  eapply disj_merge_intro_r;eauto.
  split;unfolds;join auto.
  unfold disjoint in *;join auto.
  assert ( (merge Ol O') = (merge O' Ol)).
  apply disjoint_merge_sym;auto.
  rewrite H14.
  eapply CurLINV_merge_hold;eauto.
  unfolds;join auto.
  apply disj_sym;auto.
  eapply CIH;eauto.
  apply join_comm.
  apply join_merge_disj.
  assert (disjoint Ol OO'').
  eapply abs_delself_disj;eauto.
  eapply hmstepstar_disj;eauto.
  eapply disj_merge_intro_r;eauto.
  split;unfolds;join auto.
  unfold disjoint in *;join auto.
  unfolds.
  do 6 eexists;splits;eauto.

  eapply int_inos_stkfree_still;eauto.

  (*del other*)
  mytac.
  exists (curs (hapi_code (spec_del (Vint32 pri);; sleft)), (kenil,kevent ch keh ksh)) pri.
  exists sleft (kenil,kevent ch keh ksh) t'.
  exists (merge Ol OO') (merge Ol OO'').
  exists (merge Ol O') Os'.
  simpl get_smem in *.
  splits;eauto.
  eapply evalval_eq_prop;eauto.
  unfolds;join auto.
  intros.
  eapply osapi_lift' with (cst:=cst) (pc:=pc) (A:=A) (t:=t) (ke:=kenil) (ks:= kevent ch keh ksh)in H5;eauto.
  eapply htstepstar_O_local with (Of:=Ol) (OO:=OO0)in H5.
  mytac.
  apply join_comm in H13.
  apply map_join_merge' in H13;subst.
  auto.
  eapply join_join_join_merge';eauto.
  apply join_comm;auto.
  right.
  splits;auto.
  eapply abs_delother_step_local;eauto.
  apply disj_sym.
  eapply hmstepstar_disj;eauto.
  eapply disj_merge_intro_r;eauto.
  split;unfolds;join auto.
  eapply join_join_join_merge;eauto.

  apply join_merge_disj.
  eapply abs_delother_disj;eauto.
  eapply hmstepstar_disj;eauto.
  eapply disj_merge_intro_r;eauto.
  split;unfolds;join auto.
  assert (m = merge mi Ml).
  eapply map_join_merge';auto.
  subst m.
  assert (disjoint Ol O').
  assert (disjoint Ol OO'').
  eapply abs_delother_disj;eauto.
  eapply hmstepstar_disj;eauto.
  eapply disj_merge_intro_r;eauto.
  split;unfolds;join auto.
  unfold disjoint in *;join auto.
  assert ( (merge Ol O') = (merge O' Ol)).
  apply disjoint_merge_sym;auto.
  rewrite H14.
  eapply CurLINV_merge_hold;eauto.
  unfolds;join auto.
  apply disj_sym;auto.
  intros.
  assert (joinmem (e, e0, mi, i0, l) Mdel (e, e0, merge mi Mdel, i0, l)).
  destruct o' as [[[[]]]].
  unfolds in H14.
  destruct H14 as (Ge&Ee&M&m0'&ir0&ls&Hf1&Hf2&Hff4).
  inversion Hf1.
  subst Ge Ee M ir0 ls.
  inverts Hf2.
  clear Hf1.
  unfolds.
  do 6 eexists;splits;eauto.
  apply join_merge_disj.
  unfolds;join auto.
  assert (join O' Odel (merge O' Odel)).
  apply join_merge_disj.
  assert (disjoint Ol O').
  assert (disjoint Ol OO'').
  eapply abs_delother_disj;eauto.
  eapply hmstepstar_disj;eauto.
  eapply disj_merge_intro_r;eauto.
  split;unfolds;join auto.
  unfold disjoint in *;join auto.
  rewrite disjoint_merge_sym in H15;auto.

  apply disj_sym.
  apply join_comm in H15.
  eapply disj_merge_join_disj_intro;eauto.
  apply disj_sym;auto.
  lets Hx:H12 H13 H16 H18.
  assert (disjoint Ol O').
  assert (disjoint Ol OO'').
  eapply abs_delother_disj;eauto.
  eapply hmstepstar_disj;eauto.
  eapply disj_merge_intro_r;eauto.
  split;unfolds;join auto.
  unfold disjoint in *;join auto.
  eapply CIH with (isrreg:=isrreg) (si:=si) (Ml:=Ml) (ab:=sleft) (oi:=(e, e0, merge mi Mdel, i0, l)) (Ol:=Ol) (Oi:=merge O' Odel);eauto.
  apply join_comm in H15.
  eapply disj_join_join_merge;eauto.
  rewrite disjoint_merge_sym in H15;auto.
  apply disj_sym;auto.
  destruct o' as [[[[]]]].
  unfolds in H14.
  destruct H14 as (Ge&Ee&M&m0'&ir0&ls&Hf1&Hf2&Hff4).
  inversion Hf1.
  subst Ge Ee M ir0 ls.
  inverts Hf2.
  clear Hf1.
  unfolds;do 6 eexists;splits;eauto.
  clear - Hff4 Hf3.
  eapply join_join_join_merge';eauto.
  apply join_comm;auto.
  eapply int_inos_stkfree_still;eauto. 
  unfold getmem in *;simpl.
  simpl in H8.
  unfold disjoint in *;join auto.
  apply join_merge_disj.
  unfolds;join auto.
Qed.



Lemma IntSeq': forall pc po pi ip (A:osspec) O Oi Mi I ch keh ksh c ke ks Mc t s Ms Os Ms' Os' p lenv  ge le m ir ie is cs sh i lasrt,
                 ip i = Some s ->
                 (snd (fst A)) i = Some sh->
                 no_call_api_os po pi ip ->
                 GoodI I (snd A) lasrt ->
                 TaskSim (pc,(po,pi,ip)) ( c, (ke, ks)) (substaskst  ((ge,le,m),ir,(ie,is,cs)) Mc) (pc,A) (ch,(keh,ksh)) O lasrt I p t -> 
                 fst (fst (get_smem  ((ge,le,m),ir,(ie,is,cs)))) = ge ->

                 lintstep' i ip (c ,(ke, ks))  ((ge,le,m),ir,(ie,is,cs)) ((curs s), (kenil, (kint c ke lenv  ks))) (ge, empenv, m, isrupd ir i true, (false, i :: is, nil)) ->
                 (forall ab, sat (((substaskst  ((ge,le,m),ir,(ie,is,cs)) Ms),Os),ab) (INV I)) ->
                 (forall ab, sat (((ge, empenv,Ms', isrupd ir i true, (false, i :: is, nil)),Os'),ab) (INV I)) ->
                 join Oi Os' Os ->
                 disjoint O Os ->
                 join Mi Ms' Ms ->
                 disjoint Mc Ms ->
                 satp ((ge,le,Mc),ir,(ie,is,cs)) O (CurLINV lasrt t) ->
                 (
                   forall (i:hid) ispec isrreg si G lg t, 
                     (snd (fst A)) i = Some ispec ->
                     (
                       exists (s:stmts) p r,
                         ip i = Some s /\ 
                         p = ipreasrt i isrreg si ispec I G lasrt t lg /\ 
                         r = iretasrt i isrreg si I G lasrt t lg /\
                         MethSimAsrt pi (snd A) lasrt I retfalse r p s Afalse t
                     )
                 )->
                 eqdomOS (po,pi,ip) A ->
                 goodks (pc,(po,pi,ip)) ks->
                 TaskSim (pc,(po,pi,ip)) ((curs s), (kenil, (kint c ke lenv ks))) 
                         ((ge, empenv, merge Mc Mi, isrupd ir i true, (false, i :: is, nil))) (pc,A) ((curs (hapi_code sh)), (kenil, kevent ch keh ksh)) (merge O Oi) lasrt I p t.
Proof.
  introv Hcl.
  introv Hch.
  introv Hnoos.
  introv Hgoodi.
  intros.

  lets Hx:curlinv_p_local_trans H8.
  destruct Hx as (Ml&Mlinv&Ol&Olinv&lg&Hjoinml&Hjoinol&Hplocal).
  simpl in H0.
  inversion H1;subst.
  assert (kint c ke lenv ks = kstop ## kint c ke lenv ks).
  simpl;auto.
  rewrite H12.
  unfold eqdomOS in H10.
  destruct A as ((B&C)&sc).
  destruct H10.
  destruct H13.
  destruct (H14 i).
  assert (exists idef,ip i = Some idef).
  exists s;auto.
  apply H15 in H17.
  destruct H17.
  assert (disjoint O Oi).
  unfold disjoint in *;join auto.
  assert (merge O Oi = merge Oi O).
  apply disjoint_merge_sym;auto.
  rewrite H20.
  assert (disjoint Mc Mi).
  unfold disjoint in *;join auto.
  assert (merge Mc Mi = merge Mi Mc).
  apply disjoint_merge_sym;auto.
  rewrite H22.
  eapply IntSeq'' with (absi:=x) (i:=i) (Ol:=Ol) (ge:=ge) (Ml:=Ml) (Oi:=merge Oi Olinv) (oi:=(ge, empenv, merge Mi Mlinv, isrupd ir i true, (false, i :: is, nil))) (isrreg:=ir) (lg:=lg) (si:=is);eauto.
  clear -Hnoos H30.
  unfolds in Hnoos.
  mytac;unfold no_call_api_ipu in *.
  apply H1 in H30;simpl;auto.
  eapply join_disj_merge_merge;eauto.
  apply join_comm;auto.
  apply disj_sym;auto.
  unfold joinmem.
  do 6 eexists;splits;eauto.
  eapply join_disj_merge_merge;eauto.
  apply join_comm;auto.
  apply disj_sym;auto.
  
  intros.
  lets Hx: p_local_exact Hplocal H23.
  destruct Hx;subst.
  simpl substaskst in *.
  apply join_merge in Hjoinml.
  apply join_merge in Hjoinol.
  subst;auto.
  rewrite <- higherint_update_eq;auto.

  unfold MethSimAsrt in H9.
  simpl in H9.
  assert (C i = Some x) as Hhc;auto.
  eapply H9 with (si:=is) (isrreg:=ir) (G:=ge) (lg:=lg) (t:=t) in H17.
  destruct H17 as (S0&p0&r&Hip&Hp&Hr&Hmsim).
  rewrite Hip in H30;inverts H30.
  assert ((((ge, empenv, (merge Mi Mlinv),  isrupd ir i true, (false, i::is, nil)) ,
           (merge Oi Olinv), (x )) |= ipreasrt i ir is (x ) I ge lasrt t lg) /\ satp (ge, empenv, (merge Mi Mlinv),  isrupd ir i true, (false, i::is, nil))  (merge Oi Olinv) (CurLINV lasrt t)).

  eapply en_int_inv with (Ms':=Ms') (Os':=Os') (Ms:=Ms) (Os:=Os) (Mi:=Mi) (Oi:=Oi);eauto.
  unfold disjoint in *;join auto.
  unfold disjoint in *;join auto.
  unfold substaskst in H2.

  eapply INV_irrev_prop ;eauto.
  eapply p_local_ignore_int;eauto.
  subst p0.
  apply Hmsim in H17.
  simpl snd.
  subst r.
  unfold retfalse at 2.
  unfold lift in H17.
  unfold nilcont in H17.
 
  simpl in Hch.
  rewrite Hch in Hhc;inverts Hhc.
  auto.
  unfold InOS.
  exists (curs s) kenil (kstop##kint c ke lenv ks).
  splits;auto.
  Grab Existential Variables.
  trivial.
Qed.
(*
Lemma init_subs: forall o o' Ms O, InitTaskSt (substaskst o empmem, O) -> InitTaskSt (substaskst o' empmem, O) -> substaskst o' Ms = substaskst o Ms.
Proof.
  unfold InitTaskSt.
  intros.
  destruct o', o.
  destruct p ,p0.
  destruct s,s0.
  destruct p,p0.
  simpl.
  simpl in H.
  simpl in H0.
  destruct H as (H1&H2&H3&H4&H5).
  subst.
  destruct H0 as (H1'&H2'&H3'&H4'&H5').
  subst.
  destruct H5;destruct H5'.
  subst.
  auto.
Qed.*)

Lemma inos_lift: forall v ks po pi,
                   ~ InOS (SKIP, (kenil, ks)) (pumerge po pi) ->
                   ~ InOS (curs (sskip v), (kenil, ks)) (pumerge po pi).
Proof.
  unfold InOS.
  intros.
  intro X.
  destruct H.
  destruct X as (c&ke&ks0&X&X').
  inversion X;subst c ke ks0.
  exists SKIP kenil ks.
  splits;auto.
  destruct X'.
  destruct H as (f&vl&fc&tl&H&HH).
  inversion H.
  right.
  auto.
Qed.


Lemma GoodStmt_to_GoodStmt': forall s p, GoodStmt s p ->GoodStmt' s.
Proof.
  intros.
  induction s;simpl;auto;simpl in H.
  destruct H.
  split.
  apply IHs1;eauto.
  apply IHs2;eauto.
  destruct H.
  split.
  apply IHs1;eauto.
  apply IHs2;eauto.
Qed.

Lemma goodstmt'_n_dym_com_s: forall s, GoodStmt' s -> n_dym_com_s s.
Proof.
  induction s;simpl;auto.
Qed.


Lemma n_dym_ks_call: forall ks' ks f s, n_dym_com_int_scont (ks'##kcall f s empenv ks) -> n_dym_com_int_scont ks.
Proof.
  induction ks';intros;simpl;auto;try solve [simpl in H;destruct H;auto |simpl in H;destruct H;eapply IHks';eauto | simpl in H;eapply IHks';eauto].
  simpl in H.
  destruct H.
  destruct H0.
  eapply IHks';eauto.
Qed.

Lemma goodstmt_n_dym_com_s: forall s p , GoodStmt s p-> n_dym_com_s s.
Proof.
  intros.
  induction s;simpl;auto.
  simpl in H.
  destruct H.
  split.
  eapply GoodStmt_to_GoodStmt';eauto.
  eapply GoodStmt_to_GoodStmt';eauto.
  simpl in H.
  eapply GoodStmt_to_GoodStmt';eauto.
  simpl in H.
  eapply GoodStmt_to_GoodStmt';eauto.
  simpl in H;destruct H.
  split.
  eapply GoodStmt_to_GoodStmt';eauto.
  eapply GoodStmt_to_GoodStmt';eauto.
Qed.


Lemma pumerge_get_ex:forall p p' f t d1 d2 s, (pumerge p p') f= Some (t,d1,d2,s) -> p f =Some (t,d1,d2,s)\/ p' f = Some (t,d1,d2,s).
Proof.
  intros.
  unfold pumerge in *.
  destruct (p f).
  left;auto.
  destruct (p' f);tryfalse.
  right;auto.
Qed.

Lemma callcont_ndymint:forall ks f s le ks', callcont ks = Some (kcall f s le ks') -> n_dym_com_int_scont ks -> n_dym_com_int_scont ks'. 
Proof.
  induction ks;intros;simpl;auto;tryfalse;
  try solve [simpl in H0;simpl in H;
             destruct H0;
             eapply IHks;eauto |
             inversion H;subst;
             simpl in H0;
             destruct H0;auto | simpl in H0;
               simpl in H;eapply IHks;eauto ].
  simpl in H0.
  destruct H0.
  destruct H1;eapply IHks;eauto. 
Qed.

Lemma ltstep_n_dym_com_int_cd:  
  forall pc po pi ip t c' ke' ks' c'' ke'' ks'' cst o cst' o', 
    (forall f t d1 d2 s, po f = Some (t,d1,d2,s) -> good_decllist (revlcons d1 d2) = true/\GoodStmt' s) ->
    (forall f t d1 d2 s, pi f = Some (t,d1,d2,s) -> good_decllist (revlcons d1 d2) = true/\GoodStmt' s) ->
    GoodClient pc po pi ->
    ltstep (pc,(po,pi,ip)) t (c', (ke', ks' )) cst o (c'', (ke'', ks'' )) cst' o' -> n_dym_com_int_cd (c', (ke', ks' )) -> n_dym_com_int_cd (c'', (ke'', ks'' )).
Proof.
  intros.
  assert ( forall (f : fid) (a : type) (b c : decllist) (s : stmts),
             pc f = Some (a, b, c, s) -> GoodStmt' s).
  intros.
  apply H1 in H4.
  eapply GoodStmt_to_GoodStmt';eauto.
  clear H1.
  rename H4 into H1.
  unfold n_dym_com_int_cd in *.
  destruct H3.
  inversion H2;subst.
  inversion H5;subst pc0 po0 pi0 ip0;clear H5.

  inversion H6;subst.

  inversion H15;subst;clear H15.
  inversion H16;subst;simpl;split;auto.
  inversion H15;subst.
  inversion H16;subst;simpl;split;auto;try solve [simpl in H3;destruct H3;auto| simpl in H4;destruct H4;auto|simpl in H4;destruct H4;eapply goodstmt'_n_dym_com_s;eauto].
  split;auto. 
  apply pumerge_get_ex in H9.
  inversion H5;subst ge0 le0 M0.
  inversion H8;subst.
  destruct H9.
  apply H1 in H9;auto.
  apply H in H9;destruct H9;auto.
  eapply callcont_ndymint;eauto.
  simpl in H3.
  destruct H3;eapply goodstmt'_n_dym_com_s;eauto.
  simpl in H4.
  destruct H4.
  destruct H5;auto.
  simpl in H4.
  destruct H4;destruct H5.
  eapply goodstmt'_n_dym_com_s;eauto.
  simpl in H4;destruct H4;destruct H5;auto.
  inversion H5;subst pc0 po0 pi0 ip0.
  inversion H6;subst;try solve [inversion H14;subst;
                                simpl;auto | inversion H15;subst;
                                             simpl;auto].
  Focus 2.
  inversion H15;subst.
  Lemma int_ndymint_false:forall ks c ke le ks', intcont ks = Some (kint c ke le ks') -> ~(n_dym_com_int_scont ks).
  Proof.
    intros.
    induction ks;simpl;auto;tryfalse.
    simpl in H.
    apply or_not_and.
    right;auto.
    simpl in H.
    apply or_not_and.
    right.
    apply or_not_and.
    right.
    apply IHks;auto.
    simpl in H.
    apply or_not_and.
    right;apply IHks;auto.
  Qed.
  apply int_ndymint_false in H16;false.

  inversion H8;subst.
  inversion H16;subst;clear H16.
  inversion H17;subst;simpl;split;auto.
  inversion H16;subst.
  inversion H17;subst;simpl;split;auto;try solve [simpl in H3;destruct H3;auto| simpl in H4;destruct H4;auto|simpl in H4;destruct H4;eapply goodstmt'_n_dym_com_s;eauto].
  split;auto. 
  apply pumerge_get_ex in H11.
  destruct H11.
  apply H in H9;destruct H9;auto.
  apply H0 in H9;destruct H9;auto.

  eapply callcont_ndymint;eauto.
  simpl in H3.
  destruct H3;eapply goodstmt'_n_dym_com_s;eauto.
  simpl in H4.
  destruct H4.
  destruct H10;auto.
  simpl in H4.
  destruct H4;destruct H10.
  eapply goodstmt'_n_dym_com_s;eauto.
  simpl in H4;destruct H4;destruct H10;auto.
  inversion H11;subst.
  split;auto.
Qed.

Lemma ltstepev_n_dym_com_int_cd:  
  forall pc po pi ip t c' ke' ks' c'' ke'' ks'' cst o cst' o' ev, 
    (forall f t d1 d2 s, po f = Some (t,d1,d2,s) -> good_decllist (revlcons d1 d2) = true/\GoodStmt' s) ->
    (forall f t d1 d2 s, pi f = Some (t,d1,d2,s) -> good_decllist (revlcons d1 d2) = true/\GoodStmt' s) ->
    GoodClient pc po pi ->
    ltstepev (pc,(po,pi,ip)) t (c', (ke', ks' )) cst o (c'', (ke'', ks'' )) cst' o' ev-> n_dym_com_int_cd (c', (ke', ks' )) -> n_dym_com_int_cd (c'', (ke'', ks'' )).
Proof.
  intros.
  inversion H2;subst.
  inversion H5;subst.
  inversion H13;subst.
  inversion H16;subst;simpl;auto.
Qed.


Lemma tlmatch_dec':forall tl dl (vl:vallist), ~(tlmatch tl dl/\ dl_vl_match dl (rev vl)=true)\/ (tlmatch tl dl /\ dl_vl_match dl (rev vl)=true).
Proof.
  intros.
  assert ((tlmatch tl dl /\ dl_vl_match dl (rev vl)=true) \/
          ~(tlmatch tl dl /\ dl_vl_match dl (rev vl)=true)).
  eapply classic.
  destruct H.
  right.
  auto.
  left;auto.
Qed.


Lemma pumerge_get: forall po pi f t d1 d2 s, po f= Some (t, d1, d2, s) -> (pumerge po pi) f = Some (t,d1,d2,s).
Proof.
  intros.
  unfold pumerge.
  rewrite H.
  auto.
Qed.


Lemma funbody'_inos: forall s po pi f ft d1 d2 s', GoodStmt' s-> po f = Some (ft,d1,d2,s') -> InOS (curs s,(kenil, kcall f s' empenv kstop)) (pumerge po pi).
Proof.
  intros.
  unfold InOS.
  exists (curs s) kenil (kcall f s' empenv kstop).
  splits;auto.
  right.
  left.
  exists f (empenv:env) kstop ft d1. 
  exists d2 s' s'.
  split;simpl;auto.
  apply pumerge_get.
  auto.
Qed.

Lemma cstep_no_api_elim:
  forall po pi c ke ks c' ke' ks' o o',
  no_call_api (c,(ke,ks)) po -> 
  cstep (pumerge po pi) (c, (ke, ks)) o (c', (ke', ks')) o' ->
  cstep pi (c, (ke, ks)) o (c', (ke', ks')) o'.
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
  unfold pumerge in H2.
  rewrite H in H2;auto.
  destruct (pi f);auto;tryfalse.
Qed.

Lemma loststep_no_api_elim:
  forall po pi c ke ks c' ke' ks' o o',
  no_call_api (c,(ke,ks)) po -> 
  loststep (pumerge po pi) (c, (ke, ks)) o (c', (ke', ks')) o' ->
  loststep pi (c, (ke, ks)) o (c', (ke', ks')) o'. 
Proof.
  intros.
  inverts H0;first [eapply checkis_step | constructors];eauto;tryfalse.
  eapply cstep_no_api_elim;eauto.
Qed.

Lemma XXXX: forall ksx f s kstop ks, ksx ## (kcall f s empenv kstop ## ks) =  ksx ## kcall f s empenv kstop ## ks.
Proof.
  intro ksx.
  inductions ksx; intros;
  try solve [simpl; auto];
  try solve [simpl; rewrite <- IHksx; auto].
Qed.


Lemma SmCTaskSim': 
  forall (pc po pi:progunit) (ip:intunit) (A:osspec) I o O  c ke ks1 ks2 ks ch keh lasrt (tid:tid),
    satp o O (CurLINV lasrt tid) ->
    no_fun_same po pi ->
    no_call_api_os po pi ip ->
    (*good_ret_funs pc po pi ->*)
    True ->
    (forall f t d1 d2 s, po f = Some (t,d1,d2,s) -> good_decllist (revlcons d1 d2) = true/\GoodStmt' s) ->
    (forall f t d1 d2 s, pi f = Some (t,d1,d2,s) -> good_decllist (revlcons d1 d2) = true/\GoodStmt' s) ->
    (
      forall (f:fid) ab  vl p r ft G tid, 
        (fst (fst A)) f = Some (ab,ft) ->
        Some p = BuildPreA po f (ab,ft) vl G lasrt tid init_lg ->
        Some r = BuildRetA po f (ab,ft) vl G lasrt tid init_lg->
        (
          exists t d1 d2 s,
            po f = Some (t, d1, d2, s)/\
            GoodStmt' s /\
            MethSimAsrt pi (snd A) lasrt I r Afalse p s Afalse tid
        )
    ) -> 
    (eqdomOS (po,pi,ip) A /\GoodClient pc po pi/\ goodks (pc,(po,pi,ip)) (ks1##(ks2##ks))/\n_dym_com_int_cd (c,(ke,ks1##(ks2##ks)))/\ good_clt (SKIP, (kenil,ks)) pi/\ (*good_ret_c (c,(ke,(ks1##(ks2##ks))))*) True)->
    (
      (~InOS (c,(ke,ks)) (pumerge po pi) /\ 
       (c=ch/\ke=keh/\ks1=kstop/\ks2=kstop) ) \/  
      (exists f vl tl s d1 d2 ft, 
         po f = Some (ft,d1,d2,s)/\ c = curs (sfexec f vl tl)/\ ke=kenil/\ ch =c /\keh=kenil/\
         ks1=kstop/\ks2=kstop/\~InOS (SKIP,(kenil,ks)) (pumerge po pi))\/
      (exists f vl , exists dl vlh s d1 d2 ft tl, 
         po f = Some (ft,d1,d2,s) /\ c =curs (salloc vl dl)/\ke=kenil/\
         ch = curs (sfexec f vlh tl)/\keh=kenil/\
         ks1=kstop/\ks2=kcall f s emp kstop/\
         ~InOS (SKIP,(kenil,ks)) (pumerge po pi))\/
      (exists f s d1 d2 ft, 
         po f = Some (ft,d1,d2,s)/\ keh=kenil/\ks2=kcall f s emp kstop/\ 
          (forall vl dl,(c,(ke,ks1))<>(curs (salloc vl dl),(kenil,kstop)))/\
          (forall al v,  ~ (c=curs (sfree al v) /\ callcont ks1 = None/\intcont ks1=None))/\
          ~InOS (SKIP,(kenil,ks)) (pumerge po pi))\/
      
      (exists (al:freelist) f s d1 d2 ft v,
         po f = Some (ft,d1,d2,s)/\ keh=kenil/\ks2=kcall f s emp kstop/\ ke=kenil/\
         c=curs (sfree al v)/\ callcont ks1 = None /\ intcont ks1 =None/\
         ~InOS (SKIP,(kenil,ks)) (pumerge po pi))
    )->
    (
      ~InOS (c,(ke,ks)) (pumerge po pi) ->
      c=ch-> ke=keh -> ks1=kstop -> ks2=kstop ->
      InitTaskSt lasrt tid (pair o O) /\ good_clt (c,(ke,ks)) pi
    ) -> 
    (
      forall f vl tl s d1 d2 ft, 
        po f = Some (ft,d1,d2,s)-> c = curs (sfexec f vl tl) -> ke=kenil -> ch =c -> keh=kenil->
        ks1=kstop -> ks2=kstop ->  ~InOS (SKIP,(kenil,ks)) (pumerge po pi) ->
        InitTaskSt lasrt tid (pair o O)
    ) ->
    (
      (forall f vl dl vlh s d1 d2 ft tl, 
         po f = Some (ft,d1,d2,s)-> c =curs (salloc vl dl)->ke=kenil->
         ch = curs (sfexec f vlh tl)->
         ks1=kstop -> ks2=kcall f s emp kstop ->
         ~InOS (SKIP,(kenil,ks)) (pumerge po pi) ->
         (
           tlmatch (List.rev tl) d1 /\ tl_vl_match tl vlh =true /\ good_dl_le dl o /\ True (*get_genv (get_smem o) = InitG*) /\
           exists dl' vl' p,  
             (vl<>nil -> length_eq vl' dl') /\ 
             dl_add dl' dl=revlcons d1 d2/\ vl' ++ vl = vlh/\buildp dl' vl'=Some p /\
             (forall ab,sat ((o,O),ab) ((p ** p_local lasrt tid init_lg ** (Aie true) ** (Ais nil)** (Acs nil) ** (Aisr empisr))** A_dom_lenv (getlenvdom dl')))))
    ) ->
    (
      forall f s d1 d2 ft ab tt, 
        po f = Some (ft,d1,d2,s) -> keh=kenil -> ks2=kcall f s emp kstop ->
        (forall vl dl,(c,(ke,ks1))<>(curs (salloc vl dl),(kenil,kstop)))->
        (forall al v,  ~ (c=curs (sfree al v) /\ callcont ks1 = None/\intcont ks1=None))->
        ~InOS (SKIP,(kenil,ks)) (pumerge po pi) ->
        (fst (fst A)) f = Some (ab,tt) ->
        (exists R vlh AC, InOS (c,(ke,ks1##kcall f s emp kstop)) (pumerge po pi)/\ch = curs (hapi_code AC) /\Some R = BuildRetA po f (ab,tt) vlh (get_genv (get_smem o)) lasrt tid init_lg /\ no_call_api (c,(ke,ks1)) po /\
                          MethSim pi (snd A) (c,(ke,ks1)) o AC O lasrt I R Afalse retfalse tid
        )     
    )->
    
    (
      forall (al:freelist)  f s d1 d2 ft v,
         po f = Some (ft,d1,d2,s) -> keh=kenil -> ks2=kcall f s emp kstop -> ke=kenil ->
         c=curs (sfree al v) ->  callcont ks1 = None -> intcont ks1 = None->
         ~InOS (SKIP,(kenil,ks)) (pumerge po pi) ->
         exists M,
          (freels al (get_mem (get_smem o)) M /\ 
          InitTaskSt lasrt tid ((emple_tst (substaskst o M)),O)/\ ch=curs (sskip v)/\keh=kenil)
    ) 
    ->
    TaskSim (pc, (po,pi,ip)) (c,(ke,ks1##(ks2##ks))) o (pc, A) (ch,(keh,ks)) O lasrt I (InitTaskSt lasrt tid) tid.
Proof.
  cofix CIH.
  introv Hlinv.
  introv Hnofunsame.
  introv Hnoos.
  introv Hgoodretos.
  introv Hgoodpo.
  introv Hgoodpi.  
  intros.
  destruct H0 as (H0&Hgoodclient&Hgoodks&Hndymint&Hgoodclt&Hgoodretc).
  destruct H1 as [Hc1 | Hc2].
  lets Hinit:H2 Hc1.
  destruct Hc1 as (Hninos&Hceq&Hkeeq&Hks1&Hks2).
  subst ks1 ks2.
  subst ch keh.
  assert (kstop##(kstop##ks)=ks).
  simpl;auto.
  rewrite H1.
  apply task_sim.
  intros.
  assert (o2=o'').

  eapply cltstep_eqo;eauto.
  subst o''.
  lets Hc':step_to_inos_dec Hninos H10;eauto. 
  apply Hinit;auto.
  destruct Hc'.
  destruct H11 as (f&a&vl&tl&ks'&Hpf&Hc').
  subst Cl'.
  inversion H10;tryfalse.
  subst  cst'0 C'.
  subst tst cst0 C p t cst cst' m m'.
  exists (curs (sfexec f vl tl), (kenil, ks')) OO o Ms O Os.
  splits;auto.

  eapply ht_starS with (c':=(curs (sfexec f vl tl), (kenil, ks'))) (O':=OO).

  eapply cltstep1_eq;eauto.
  eapply Hinit;auto.
  eapply ht_starO.
  assert (ks'=kstop##(kstop##ks')).
  simpl;auto.
  rewrite H14.
  apply CIH;auto;intros;tryfalse.
  splits;auto.
  simpl.
  simpl in Hgoodks.
  eapply ltstep_goodks;eauto.
  simpl in Hndymint.
  eapply ltstep_n_dym_com_int_cd with(pc:=pc) (po:=po) (pi:=pi) (ip:=ip);eauto.

  apply clt_step_good_clt in H10;auto.
  simpl in H10.
  simpl.
  split;auto.
  destruct H10;auto.
  apply Hinit;auto.
(*  eapply ltstep_good_ret;eauto.*)
  right.
  left.
  destruct a as (((ft&d1)&d2)&s).
  exists f vl tl s d1.
  exists d2 ft.
  splits;auto.
  (simpl;auto).
  eapply step_fexec_ninos;eauto.
  splits;try apply Hinit;auto.
  eapply clt_step_good_clt;eauto.
  apply Hinit;auto.
  apply Hinit;auto.

  inversion H10;tryfalse.
  subst cst'0 tst C' C t p cst cst' m m'.
  subst cst0.
  exists  Cl' OO o Ms O Os.
  splits;auto.
  (eapply ht_starS;try eapply cltstep1_eq;eauto;try eapply ht_starO).
  apply Hinit;auto.
  destruct Cl' as (cn&(ken&ksn)).
  assert (ksn=kstop ##(kstop##ksn)).
  (simpl;auto).
  rewrite H15.
  apply CIH;auto;intros;tryfalse.
  splits;auto.
  simpl.
  simpl in Hgoodks.
  eapply ltstep_goodks;eauto.
  simpl in Hndymint.
  eapply ltstep_n_dym_com_int_cd with(pc:=pc) (po:=po) (pi:=pi) (ip:=ip);eauto.
  apply clt_step_good_clt in H10;auto.
  unfold good_clt in *;destruct H10;simpl;auto.
  apply Hinit;auto.
  (*eapply ltstep_good_ret;eauto.*)
  left.
  (splits;auto).
  splits;try apply Hinit;auto.
  rewrite <- H15.
  eapply clt_step_good_clt;eauto.
  apply Hinit;auto.
  apply Hinit;auto.
 
  intros.
  assert (o2=o''/\cst=cst').
  inverts H10;split;auto.
  destruct H11;subst o'' cst'.
  assert (ltstepev (pc, (po, pi, ip)) tid (c, (ke, ks)) cst o2 Cl' cst o2 ev) as Hlstepev;auto.

  apply stepev_still_inos in H10;auto.
  exists Cl' OO o Ms O Os.
  splits;auto.
  destruct cst as (D&F).
  eapply htev_stepstar with (c':= (c, (ke, ks))) (c'':=Cl') (O':=OO);eauto.
  apply ht_starO.

  eapply cltstepev_eq;eauto.
  apply ht_starO.
  destruct Cl' as (cn&(ken&ksn)).
  assert (ksn=kstop ##(kstop##ksn)).
  simpl;auto.
  rewrite H11.
  apply CIH;auto;intros;tryfalse.

  splits;auto.
  simpl;simpl in Hgoodks.

  eapply ltstepev_goodks;eauto.
  simpl in Hndymint.
  eapply ltstepev_n_dym_com_int_cd with(pc:=pc) (po:=po) (pi:=pi) (ip:=ip);eauto.

  apply clt_stepev_good_clt in Hlstepev;auto.
  unfold good_clt in *;destruct Hlstepev;simpl;auto.
  apply Hinit;auto.
  (*eapply ltstepev_good_ret;eauto.*)
  left.
  splits;auto.
  split;try apply Hinit;auto.

  eapply clt_stepev_good_clt;eauto.
  apply Hinit;auto.
  apply Hinit;auto.

  intros.
  assert (InitTaskSt lasrt tid (o, O) /\ good_clt (c, (ke, ks)) pi) by auto.
  destruct H11.
  inverts H7.
  simpl in H12.
  destruct H12.
  tryfalse.

  intros.
  exists O Os (c,(ke,ks)) OO.
  splits;auto.
  intros.
  apply ht_starO.
  apply Hinit;auto.
  intros.
  unfold IsEnd in H7.
  apply htabtstar.
  exists (c,(ke,ks)) cst OOO.
  splits;auto.
  apply ht_starO.
  destruct cst.
  destruct p.
  eapply cltstep_eqabt;eauto.
  intro. 
  unfolds in H16.
  mytac.
  subst c x3.
  clear -Hndymint.
  unfolds in Hndymint.
  destruct Hndymint.
  unfolds in H.
  simpl in H.
  false.
  intro. 
  unfolds in H16.
  mytac.
  subst c x1.
  clear -Hndymint.
  unfolds in Hndymint.
  destruct Hndymint.
  unfolds in H.
  simpl in H.
  false.
  intro. 
  unfolds in H16.
  mytac.
  subst c x0.
  clear -Hndymint.
  unfolds in Hndymint.
  destruct Hndymint.
  unfolds in H.
  simpl in H.
  false.

  
  unfolds.
  intros.
  intro.
  inverts H16.
  clear -Hndymint.
  unfolds in Hndymint.
  destruct Hndymint.
  unfolds in H.
  simpl in H.
  false.

  intros.
  assert (InitTaskSt lasrt tid (o, O) /\ good_clt (c, (ke, ks)) pi) by auto.
  destruct H11.
  inverts H7.
  simpl in H12.
  destruct H12.
  tryfalse.

  
  intros.
  assert (InitTaskSt lasrt tid (o, O) /\ good_clt (c, (ke, ks)) pi) by auto.
  destruct H11.
  inverts H7.
  simpl in H12.
  destruct H12.
  tryfalse.
  
  (*---------------------------------------------*)
  destruct Hc2 as [Hc|Hc2].
  destruct Hc as (f&vl&tl&s&d1&d2&ft&Hpf&Hc&Hke&Hch&Hkeh&Hks1&Hks2&Hninos). 
  subst.

  destruct (tlmatch_dec' (List.rev tl) d1 vl) as [Hntlmatch | Htlmatch].
  apply task_sim;intros;tryfalse.

  eapply n_tlmatch_abt in Hntlmatch;eauto.
  inversion Hntlmatch;subst.
  destruct H11.
  inversion H10;subst.
  left.
  exists Cl' o'' cst';eauto.
  inversion H9;subst.
  inversion H11;subst.
  inversion H14;subst;tryfalse.
  unfold IsEnd in H1.
  destruct H1;tryfalse.

  eapply htabtstar.
  exists (curs (sfexec f vl tl), (kenil, ks)) cst OOO.
  split.
  apply ht_starO.

  destruct A as ((B&CC)&sc).
  assert (exists ab tl tp, B f = Some (ab,(tp,tl))/\tlmatch tl d1).

  eapply api_tlmatch;eauto.
  destruct H15 as (ab&tl'&tpp&H21f&H22f).
  assert (pc f = None) as Hpcnone.
  unfold GoodClient in Hgoodclient.
  destruct Hgoodclient.
  assert (po f <> None).
  intro X.
  rewrite Hpf in X;tryfalse.
  destruct H16.
  apply H18;auto.
  destruct cst.
  destruct p.

  eapply hn_tlmatch_abt;eauto.
  intro H'.
  destruct H'.
  destruct Hntlmatch.
  split.
  subst tl'.
  auto.
  subst tl'.
  eapply tl_vl_dl'';eauto.

  (*-------------------------------*)
  destruct Htlmatch as (Htlmatch).
  apply task_sim.
  intros.
  inversion H10;tryfalse.
  subst cst cst' p t C cst0 tst C' cst'0 o''.
  destruct H13.
  unfold InOS.
  exists (curs (sfexec f vl tl)) kenil ks.
  split;auto.
  left.
  inversion H11;subst po0 pi0.
  exists f vl (ft, d1, d2, s) tl;split;auto. 
  apply pumerge_get;auto.
  inversion H11.
  subst cst0 tst C' t p pc0 po0 pi0 ip0 cst' tst'.
  destruct o as (a&aux).
  destruct a as (cmem&ir).
  destruct cmem as (a&mem).
  destruct a as (genv&lenv).
  unfold joinm2 in H8.
  destruct H8 as (o1&Hjoin1&Hjoin2).
  unfold joinmem in Hjoin1.
  destruct Hjoin1 as (GG&EE&M1&M2&ir0&ls&Heq&Ho0&Hmjoin).
  inversion Heq;subst GG EE mem ir0 ls.
  subst o1.
  unfold joinmem in Hjoin2.
  destruct Hjoin2 as (GG&EE&Mx&M3&ir0&ls&Heq'&Ho0'&Hmjoin').
  inversion Heq';subst GG EE Mx ir0 ls.
  subst o2.
  exists (curs (sfexec f vl tl), (kenil, ks)) OO  (genv,(emp:env),M1,ir,aux) Ms O Os.
  inversion H12.
  inversion H21.
  (inversion H23;tryfalse).
  (inversion H23;tryfalse).
  subst C0.
  inversion H22; subst ks0 c. 
  subst.
  inversion H41;subst f0 vl0 tl0.
  inversion H29;subst ge le M.
  splits;auto.
  apply ht_starO.
  unfold joinm2.
  exists (genv, (emp:env), M2, ir, aux).
  split;unfold joinmem.
  (exists genv (emp:env) M1 M2 ir aux;splits;auto).
  (exists genv (emp:env) M2 M3 ir aux;splits;auto).

  eapply inv_substask_emple;eauto.
  eapply CurLINV_ignore_int;eauto.

  assert (kcall f s0 lenv ks1 = kstop## (kcall f s0 lenv kstop ## ks1)).
  (simpl;auto).
  rewrite H8.
  assert (po f = Some (ft,d1,d2,s));auto.
  apply pumerge_get with (pi:=pi) in Hpf.
  rewrite Hpf in H31.
  inversion H31;subst t d0 d3 s0.
  assert (InitTaskSt lasrt tid (genv, lenv, M1, ir, aux, O)).
  (eapply H3;eauto).
  assert (snd (fst (get_smem (genv, lenv, M1, ir, aux)))=emp).

  eapply init_emple.
  eauto.
  simpl in H16.
  subst lenv.
  apply CIH;auto;intros;tryfalse.
  splits;auto.
  assert (kstop ## (kcall f s empenv kstop ## ks1) = kcall f s empenv ks1).
  simpl;auto.
  rewrite H16.
  simpl in Hgoodks.
  eapply ltstep_goodks;eauto.
  simpl in Hndymint.
  eapply ltstep_n_dym_com_int_cd with(pc:=pc) (po:=po) (pi:=pi) (ip:=ip);eauto.
  (*eapply ltstep_good_ret;eauto.*)
  right.
  right.
  left.
  exists f vl  (revlcons d1 d2) vl.
  exists s d1 d2 ft tl.
  (splits;auto).
  inversion H19.
  subst f0 vlh tl0.
  rewrite H16 in H14.
  inversion H14;subst s0 d0 d3 ft0.
  inversion H17;subst vl0 dl.
  splits;auto.

  apply good_dl_le_init';auto.
  apply Hgoodpo in H16;auto. 
  destruct H16;auto.
  exists dnil (nil:vallist) Aemp.
  splits;auto.
  intros.

  apply InitAemp;auto.
  destruct (H19 vl (revlcons d1 d2)).
  auto.
  (tryfalse).
  (tryfalse).
  (tryfalse).
  (tryfalse).
  (tryfalse).
  (tryfalse).

  (intros;tryfalse).
  (intros;tryfalse).

  intros.
  inversion H10;tryfalse.
  inversion H12.
  (inversion H27;tryfalse).
  (intros;tryfalse).
  intros.
  unfold IsEnd in H7;destruct H7;tryfalse.
  intros.
  (eapply fexec_abt_eq;eauto).
  intros.
  inverts H7.
  intros;inverts H7.
  (*-------------------------------------*)
  destruct Hc2 as [Hc | Hc2].
  destruct Hc as (f&vl&dl&vlh&s&d1&d2&ft&tl&Hpf&Hc&Hke&Hch&Hkeh&Hks1&Hks2&Hninos).
  subst.
  assert (kstop##(kcall f s empenv kstop##ks)=kcall f s empenv ks).
  (simpl;auto).
  rewrite H1.
  lets Hst:H4 Hpf Hninos;eauto.
  apply task_sim.
  intros.

  lets Hlstep: alloc_locality H8 H10;eauto.
  destruct Hlstep as (o'&Hltstep').
  destruct Hltstep' as (Hlstep'&Hjoin1&Heqwom).

  apply alloc_trans with (ft:=ft) (d1:=d1) (d2:=d2) (s:=s) (vlh:=vlh) (O:=O) (f:=f) (lasrt:=lasrt)in Hlstep';auto.
  Focus 2.
  apply Hgoodpo in Hpf ;destruct Hpf;auto.
  Focus 2.
  destruct Hst as (Hst'&Hst''&Hgooddl&Hinitg&Hst''').
  (auto).
  destruct Hlstep'.
  destruct H11.
  exists (curs (sfexec f vlh tl), (kenil, ks)) OO o' Ms O Os.
  splits;auto.
  
  subst cst'.
  (apply ht_starO).

  eapply emple_subs_inv;eauto.

  eapply alloc_curlinv_hold with (o:=o);eauto.
  destruct H12 as (dl''&vl''&p&dl'''&vl'''&Hcl'&Hdladd&Hvladd&Hbp&Hleneq&Hnoend&Hst').
  subst Cl'.
  assert (kcall f s empenv ks = kstop##(kcall f s empenv kstop ## ks)).
  (simpl;auto).
  rewrite H12.
  apply CIH;auto;intros;tryfalse.
  eapply alloc_curlinv_hold with (o:=o);eauto.
  splits;auto.
  right.
  right.
  left.
  exists f vl'' dl'' vlh s d1.
  exists d2 ft tl.
  (splits;auto).
  inversion H16;subst f0 vlh0 tl0.
  inversion H14;subst vl0 dl0.
  rewrite Hpf in H13;inversion H13;subst ft0 d0 d3 s0.
  splits;destruct Hst;destruct H21;destruct H22 as (Hgooddl&H22);auto.

  assert (good_dl_le dl o2).

  apply join_eqe in H8.

  eapply good_dl_le_care in H8;eauto.
  apply good_dl_le_care with (o:= o'').
  apply join_eqe in Hjoin1.
  auto.

  eapply good_dl_le_step' ;eauto.
  apply Hgoodpo in Hpf ;destruct Hpf;auto.
  destruct o as [[[[]]]].
  unfold joinm2 in *.
  destruct H8 as (o1&H8&H88).
  destruct Hjoin1 as (o1'&Hjoin1&Hjoin2).
  unfold joinmem in H8, H88, Hjoin1, Hjoin2.
  do 6 destruct H8;destruct H8;subst.
  inversion H8;subst.
  destruct H88.
  do 6 destruct H11.
  destruct H23;subst o1.
  destruct H24;subst o2.
  inversion H11;subst.
  destruct Hjoin1.
  do 6 destruct H23;subst o'.
  simpl.
  simpl in Heqwom.
  destruct Heqwom.
  subst x.
  destruct H22.
  auto.
  exists dl''' vl''' p.
  (splits;auto).
  intros.
  assert (vl<>nil).

  intro X.
  subst vl.
  inversion H10;tryfalse.
  inversion H30;tryfalse.
  inversion H53;tryfalse.
  inversion H50;subst c.
  inversion H52;tryfalse.
  subst.
  destruct Hnoend;auto.
  inversion H30;tryfalse.
  inversion H47;tryfalse.
  inversion H56;tryfalse.
  inversion H55;tryfalse.
  subst c;inversion H53.
  subst dl.
  destruct Hnoend;auto.
  apply Hleneq in H29;auto.
  destruct (H16 vl'' dl'');auto.
  destruct H11.
  destruct H12 as (p&Hcl'&Hf&Hf'&Hbp&Hst').
  subst cst' Cl' vl dl.

  destruct Hst as (Htlmatch&Hleneq&Hgooddl&Hinitg&dl'&vl'&p'&Hffk&Hdl&Hvl&Hbp'&Hpre).
  assert (vlh=vlh++nil).
  (apply List.app_nil_end).
  rewrite <- Hvl in H11 at 1.
  apply List.app_inv_tail in H11.
  subst vl'.
  clear Hvl.
 
  rewrite dl_add_nil_eq in Hdl.
  subst dl'.

  lets Hasrts:build_api_asrt H0 Hpf Hbp'.
  eapply tl_vl_dl'';eauto.
  destruct Hasrts as (pf&rf&ab&tt&Hhf&Hbpre&Hbret).
  lets Hmsim:H Hhf Hbpre Hbret.
  destruct Hmsim as (t'&d3&d4&s'&Hpf'&Hmsim).
  rewrite Hpf in Hpf'.
  inversion Hpf';subst t' d3 d4 s'.
  clear Hpf'.
  unfold MethSimAsrt in Hmsim.
  destruct tt as (t'&tl').
 
  lets Hteq:eq_tp H0 Hhf Hpf.
  destruct Hteq;subst t'.
  
  lets Htleq:tlmatch_trans H12 Htlmatch.
  subst tl'.
  clear H12.

  lets Hpp:bp_bpa H0 Hpf Hhf Hbpre Hbp';eauto.
  apply Hpp in Hpre;eauto.

  apply Hmsim in Hpre.

  assert (o''=o2).
  inversion H10;auto;tryfalse.
  inversion H12;tryfalse.
  inversion H22;tryfalse.
  inversion H36;tryfalse.
  inversion H35;tryfalse.
  auto.
  subst o''.

  exists (curs (hapi_code (ab (rev vlh)) ), (kenil, ks)) OO o Ms O Os.
  splits;auto.

  destruct cst.
  eapply ht_starS.
  2:apply ht_starO.

  eapply hapi_step;eauto.
  destruct A as ((B&C)&sc).
  eapply hapienter_step with (vl:=rev vlh);eauto.

  rewrite <- tl_vl_rev_match.
  auto.

  rewrite List.rev_involutive.
  rewrite List.rev_involutive.
  auto.
  assert (kcall f s empenv ks = kstop ## (kcall f s empenv kstop ##ks)).
  simpl;auto.
  rewrite H11.
  apply CIH;auto;intros;tryfalse.

  splits;auto.
  simpl in Hndymint.
  simpl;auto.
  destruct Hndymint.
  destruct H13.
  splits;auto.
  eapply goodstmt'_n_dym_com_s;eauto.
  (*eapply ltstep_good_ret;eauto.*)

  right.
  right.
  right.
  left.
  exists f s d1 d2 ft.
  splits;auto.
  intros.
  intro X.
  inversion X.
  destruct Hmsim.
  subst s.
  simpl in H12.
  inversion H12.
  intros.
  intro X.
  destruct X.
  inversion H12.
  subst s.
  destruct Hmsim.
  simpl in H14;inversion H14.

  rename Hpre into HoO.
  unfold nilcont in HoO.
  inversion H14;subst f0.
  rewrite Hpf in H12;inversion H12;subst ft0 d0 d3 s0.
  rewrite H18 in Hhf;inversion Hhf;subst ab0.
  exists rf vlh (ab (rev vlh)).
  splits;auto.
  destruct Hmsim.
  assert (kstop##kcall f s empenv kstop = kcall f s empenv kstop).
  simpl;auto.
  rewrite H22.

  eapply funbody'_inos;eauto. 
  eauto.


  clear -Hpf Hnoos.
  simpl.
  unfold no_call_api_os in Hnoos.
  destructs Hnoos.
  unfolds in H;apply H in Hpf;auto.

  inversion H16.
  destruct Hmsim;subst s;tryfalse.
  intros.
  inversion H10.
  inversion H12.
  inversion H27;tryfalse.
  intros;tryfalse.
  intros.
  unfold IsEnd in H7.
  destruct H7.
  inversion H7.
  intros.
  assert (vl=nil\/ exists i t dl', dl=dcons i t dl').
  destruct vl.
  left.
  auto.
  destruct Hst as (Hf1&Hf2&Hst).
  destruct Hst as (Hgooddl&Hinitg&dl'&vl'&p&Hst1&Hst2&Hst3&Hst4).
  right.
  assert (v::vl<>nil).
  auto.
  apply Hst1 in H16.
  destruct dl.
  assert (length_eq vlh d1).

  eapply tl_dl_vl_eq;eauto.
  eapply tl_vl_match_leneq;eauto.
  assert (~length_eq vl' dl').

  eapply sub_len_neq;eauto.
  destruct H18;auto.
  exists i t dl;auto.

  eapply tstep_alloc_nabt in H15;simpl;eauto.
  (tryfalse).
  destruct Hst as (Hst1&Hs2&Hst3&Hst).
  apply join_eqe in H12.
  eapply good_dl_le_care in H12;eauto.

  intros.
  inverts H7.
  intros;inverts H7.
  (*-----------------------------------*)
  destruct Hc2 as [Hc|Hc2].
  destruct Hc as (f&s&d1&d2&ft&Hpf&Hkeh&Hks2&Hnalloc&Hnfree&Hninos).
  subst.
  assert ( ks1 ## (kcall f s empenv kstop ## ks) = ks1 ## kcall f s empenv ks).
  simpl;auto.
  rewrite H1.
  destruct A as ((B&C)&sc).
  lets Hhf:api_tlmatch H0 Hpf.
  destruct Hhf as (ab&tl&tp&Hhf&Htlmatch).

  lets Hmsim': H5 Hpf Hnalloc Hninos ;auto.
  lets Hmsim: Hmsim' Hhf.
  clear Hmsim'.
  constructors.
  intros.
  destruct Hmsim as (R&vlh&AC&Hinos&Hmap&Hr&Hnocallapi&Hmsim).

  destruct (ret_dec c ke ks1 ).
  destruct (retv_dec c ke ks1).
  inversion Hmsim.
  subst.

  lets Hlosstep': tstep_to_osstep Hndymint H10 H11 H12 Hnalloc.
  lets Hlosstep: Hlosstep' Hnfree Hinos.
  clear Hlosstep'.
  destruct Hlosstep as (c'&ke'&ks1'&H'&Hlosstep&Hc'&Hnalloc'&Hnfree').

  eapply loststep_no_api_elim in Hlosstep;eauto.
  subst cst'.
  lets Hmsim':H13 H7 H8 H9 Hlosstep;eauto.
  destruct Hmsim' as (gamma'&OO'&o'&Ms'&O'&Os'&Hhmstep&Hjoin'&HOjoin&Hinv&Hlinv'&Hmsim').
  assert (satp (substaskst o' Ms') Os' (INV I)).
  auto.

  lets Htstep:osapi_lift' Hhmstep.
  eexists.
  exists OO' o' Ms' O' Os'.
  splits;auto.
  eauto.
  subst Cl'.
  assert (ks1'##(kcall f s empenv ks) = ks1' ## (kcall f s empenv kstop ## ks)).
  simpl;auto.
  rewrite H23.
  apply CIH;auto;intros.
  splits;auto.
  eapply ltstep_goodks;eauto.
  simpl in Hndymint.
  eapply ltstep_n_dym_com_int_cd with(pc:=pc) (po:=po) (pi:=pi) (ip:=ip);eauto.
  (*eapply ltstep_good_ret;eauto.*)
  right.
  right.
  right.
  left.
  exists f s d1 d2 ft.
  splits;auto.

  inversion H28.
  inversion H30.
  inversion H29;subst f0.
  rewrite Hpf in H24;inversion H24;subst ft0 d0 d3 s0.
  subst. 
  tryfalse.
  inversion H26;subst f0.
  simpl in H30.
  rewrite Hhf in H30;inversion H30;subst ab0.
  subst tt.
  exists R vlh gamma'.
  splits;auto.

  subst s0.

  eapply inos_step_still with (ks1:=ks1);eauto.
  destruct o2 as [[[[]]]].

  lets Hx:ltstep_eqg e H10.
  assert ((get_genv (get_smem o)) = (get_genv (get_smem o'))).
  clear -Hx Hjoin' H8.
  unfold joinm2 in *;mytac.
  unfold joinmem in *.
  mytac.
  simpl in Hx.
  simpl.
  symmetry.
  apply Hx;auto.
  rewrite <- H31.
  auto.
  eapply no_call_api_loststep_still;eauto.
  eapply loststep_no_api_local;eauto.

  destruct  Hnfree' with al (v).
  split;auto.

  (*----------------------------*)
  destruct H12 as (v&ksx&Hc&Hcallcont&Hintcont).
  inversion Hc;subst c ke ks1;clear Hc.
  inversion Hmsim.
  subst.

  lets Hmsim': H16 Hcallcont Hintcont H9;eauto.

  apply disj_sym.
  clear -H8.
  destruct o as [[[[]]]].
  unfolds.
  unfolds in H8;mytac.
  unfold joinmem in *;mytac.
  unfold getmem;simpl.
  geat.

  destruct Hmsim' as (gamma'&OO'& O'&Os'&Hhmstep&HOjoin'&Hinv'&Hlinv'&Hret).
  exists (curs (sskip (Some v)),(kenil,ks)) OO' o Ms O' Os'.

  assert (o''=o2/\cst'=cst/\ Cl' = (curs (sfree (getaddr (snd (fst (get_smem o2)))) (Some v)),(kenil,ksx ## kcall f s empenv ks))).

  eapply retv_step;eauto.
  destruct H21 as (H227&H228&H229);subst o'' cst' Cl'.
  splits;auto.

  destruct cst.
  lets Hhtstep: osapi_lift' Hhmstep.
  eauto.

  Lemma hret_spec:
    forall (o : taskst) (O : osabst) (ab : osapi) (abs : absop) 
           (R : retasrt) (vl : vallist) (po : progunit) v 
           (f : fid) G lasrt t,
      Some R = BuildRetA po f ab vl G lasrt t init_lg->
      (o, O, abs) |= R v ->
      abs = spec_done v.
  Proof.
    intros.
    unfolds in H.
    destruct (po f);tryfalse.
    destruct f0.
    destruct p.
    destruct p.
    destruct (buildq (revlcons d0 d));tryfalse.
    inverts H.
    destruct H0.
    destruct H0.
    mytac.
    simpl in H4.
    mytac.
  Qed.
  
  lets Hx:hret_spec Hr Hret.
  subst gamma'.

  eapply htstepstar_compose_tail;eauto.
  eapply hapi_step;eauto.
  eapply hapiexit_step;eauto.
  assert (ksx ## kcall f s empenv ks = ksx ## (kcall f s empenv kstop ## ks)).
  simpl;auto.
  rewrite H21.
  apply CIH;auto;intros;tryfalse.
  splits;auto.
  (*eapply ltstep_good_ret;eauto.*)
  right.
  right.
  right.
  right.
  exists (getaddr (snd (fst (get_smem o2)))). 
  exists f s d1 d2 ft ( Some v).
  splits;auto.
  destruct (H26 (getaddr (snd (fst (get_smem o2)))) (Some v)).
  splits;auto.
  inversion H24;subst f0 s0.
  inversion H26;subst al v0.
  assert ((snd (fst (get_smem o2)))=(snd (fst (get_smem o)))).
  assert (TStWoMemEq o o2).

  eapply join_tst_wo_mem_eq;eauto.
  unfold TStWoMemEq in H30.
  unfold get_smem.
  destruct o as [[[[]]]].
  destruct o2 as [[[[]]]].
  simpl.
  mytac.
  
  rewrite H30.

  lets Hrvspec:retv_spec Hr Hret.
  destruct Hrvspec.
  destruct H31.
  eexists;splits;eauto.

  (*------------------*)

  destruct H11 as (Hc&Hcallcont&Hintcont).
  inversion Hc.
  subst c ke;clear Hc.
  inversion Hmsim.
  subst.
  lets Hmsim': H14 Hcallcont Hintcont H9;eauto. 
  clear -H8.
  unfolds.
  unfold joinm2 in H8.
  mytac;unfold joinmem in *.
  mytac.
  unfold getmem.
  simpl.
  geat.
  
  destruct Hmsim' as (gamma'&OO'&O'&Os'&Hhmstep&HOjoin'&Hinv'&Hlinv'&Hret).
  exists (SKIP,(kenil,ks)) OO' o Ms O' Os'.
  assert (o''=o2/\cst'=cst/\ Cl' = (curs (sfree (getaddr (snd (fst (get_smem o2))) )None ),(kenil,ks1 ## kcall f s empenv ks))).

  eapply ret_step;eauto.
  destruct H20 as (H227&H228&H229);subst o'' cst' Cl'.
  splits;auto.
 
  lets Hhtstep: osapi_lift' Hhmstep.
  lets Hx:hret_spec Hr Hret.
  subst gamma'.
  eapply htstepstar_compose_tail;eauto.
  eapply hapi_step;eauto.
  eapply hapiexit_step;eauto.
  assert (ks1 ## kcall f s empenv ks = ks1 ## (kcall f s empenv kstop ## ks)).
  simpl;auto.
  rewrite H20.
  apply CIH;auto;intros;tryfalse.
  splits;auto.
  right.
  right.
  right.
  right.
  exists (getaddr (snd (fst (get_smem o2)))). 
  exists f s d1 d2 ft (None: option val).
  splits;auto.
  destruct (H25 (getaddr (snd (fst (get_smem o2)))) None).
  splits;auto.
  inversion H23;subst f0 s0.
  inversion H25;subst al.
  assert ((snd (fst (get_smem o2)))=(snd (fst (get_smem o)))).
  assert (TStWoMemEq o o2).
  eapply join_tst_wo_mem_eq;eauto.
  unfold TStWoMemEq in H29.
  unfold get_smem.
  destruct o.
  destruct p.
  destruct s0.
  destruct p.
  destruct o2.
  destruct p.
  destruct s0.
  destruct p.
  simpl.
  mytac.
  rewrite H29.

  lets Hrvspec:ret_spec Hr Hret.
  destruct Hrvspec.
  destruct H30.
  eexists;splits;eauto.
  (*-----------------------------------------------*)

  intros.
  destruct Hmsim as (R&vlh&AC&Hinos&Hmap&Hr&Hnocallapi&Hmsim).
  inversion Hmsim.
  subst.

  lets Habt:tstepev_osstepabt H10.
  destruct Habt.
  eapply H17 with (Ms:=Ms)  in H7;eauto.
  destruct H7;eauto.
  unfolds;geat.
  (*-------------------------------------------*)
  intros.
  destruct Hmsim as (R&vlh&AC&Hinos&Hmap&Hr&Hnocallapi&Hmsim).
  inversion Hmsim.
  subst.
  inversion H7;subst c ke ks0.
  lets HH: H12 H8 H10;eauto.
  destruct HH as (gamma'&sleft&OO'&ol&Mc&O'&Os'&Ol&Oc&Hgamma&Hhmstep&Hmjoin&Hojoin'&Hojoin&Hinv'&Hswinv&Hlinv'&Hmsim').
  subst.
  exists (curs (hapi_code (spec_seq sched sleft)),(kenil,ks)) sleft (kenil, ks).
  exists OO' Mc ol O' Os' Ol.
  exists Oc. 

  splits;eauto.
  intros.
  eapply osapi_lift';eauto.
  splits;auto.
  destruct Hmsim';rename H20 into Hmsim'.
  left.
  destruct Hmsim' as (Hswpre&Hmsim').
  splits;unfold getsched;auto.
  
  intros;eauto.
  lets Hmsim'':Hmsim' H20 H21 H22.
  assert (ks1##kcall f s empenv ks = (ks1 ## (kcall f s empenv kstop ## ks))).
  simpl;auto.
  rewrite H23.
  apply CIH;auto;intros;tryfalse.
  destruct o as [[[[]]]].
  simpl substaskst in H20.
  destruct ol as [[[[]]]].
  unfolds in Hmjoin;mytac.
  destruct Hlinv' with (aop:=spec_done None).
  eapply joinmem_swinv_linv;eauto.  
  splits;auto.
  right.
  right.
  right.
  left.
  exists f s d1 d2 ft.
  splits;auto.
  intros.
  intro X.
  destruct X.
  tryfalse.
  inversion H26;subst f0 s0.
  rewrite Hpf in H24;inversion H24;subst ft0 d0 d3.
  simpl in H30.
  rewrite Hhf in H30.
  inversion H30;subst ab0 tt.
  clear H24 H30 H26.
  exists R vlh sleft.
  splits;auto.

  eapply inos_sw_still;eauto.
  assert ((get_genv (get_smem o)) = (get_genv (get_smem o'))).
  clear - Hmjoin H21.
  unfold joinmem in *.
  mytac.
  simpl;auto.
  rewrite <- H24;auto.

  (*--------------*)
  right.
  unfold getsched.
  simpl snd in *;auto.

  (*---------------------------------*)
  intros.
  destruct Hmsim as (R&vlh&AC&Hinos&Hmap&Hr&Hnocallapi&Hmsim).
  inversion Hmsim.
  subst.
  unfold IsEnd in H7.
  destruct H7 as (v&Hcd).
  inversion Hcd;tryfalse.
  unfold AddKsToTail in H22.
  destruct ks1;tryfalse.

  (*---------------------------------*)
  intros.
  destruct Hmsim as (R&vlh&AC&Hinos&Hmap&Hr&Hnocallapi&Hmsim).
  inversion Hmsim.
  subst.
  assert (disjoint O Os).
  unfolds;eauto.
  lets Habt: H22 H11 H12 H25;eauto.
  Focus 2.

  eapply nabt_lift in Habt;eauto. 
  destruct Habt;eauto.

  unfold notabort.
  splits;eauto.
  
  unfold IsSwitch.
  intro X.
  destruct H8.
  destruct X as (x0&ks0&X).
  exists x0 (ks1 ## kcall f s empenv ks).
  inversion X;subst c ke.
  auto.
  intro X.
  unfold IsEnd in X.
  destruct X as (v&X).
  assert (disjoint (getmem o) Ms).
  clear -H12.
  unfold joinm2 in *.
  mytac.
  unfold joinmem in *.
  mytac.
  unfold getmem.
  unfold disjoint;simpl.
  geat.

  lets XX: H18 X H11 H26 H13;eauto. 
  destruct XX as (gamma'&OO'&O'&Os'&XX1&XX2&XX3&XX4).
  unfold retfalse in XX4.
  unfold sat in XX4.
  destruct XX4;false.

  intro X.

  eapply isret_nabt in X;destruct X;eauto.
  intro X.
  eapply isrete_nabt in X;destruct X;eauto.
  intro X.
  unfold IsIRet in X.
  destruct X as (ks0&X&XX).
  assert (disjoint (getmem o) Ms).
  clear -H12.
  unfold joinm2 in *.
  mytac.
  unfold joinmem in *.
  mytac.
  unfold getmem.
  unfold disjoint;simpl.
  geat.
  destruct XX.
  lets XXX:H21 X H28 H27 H26 H13;eauto.
  mytac.
  simpl in H33;false.

  unfold IsStkInit in *.
  intro X.
  destruct H9.
  destruct X as (e1&e2&e3&ks0&X).
  exists e1 e2 e3 (ks1 ## kcall f s empenv ks).
  inversion X;subst c ke.
  auto.

  unfold IsStkFree in *.
  intro X.
  destruct H10.
  destruct X as (e&ks0&X).
  exists e (ks1 ## kcall f s empenv ks).
  inversion X;subst c ke.
  auto.

  (*--------------------------------*)
  intros.
  inverts H7.
  subst.
  destruct Hmsim as (R&vlh&AC&Hinos&Hmap&Hr&Hnocallapi&Hmsim).
  inversion Hmsim.
  subst.
  lets Hx:H17 H8 H9 H10;eauto.

  destruct Hx as (gamma'&v1&v2&t'&pri&sleft&OO'&OO''&ol&Mcre&O'&Os'&Ol&Ocre&Hx).
  mytac.
  eexists.
  exists v1 v2 t' pri sleft (kenil,ks).
  exists OO' OO'' ol Mcre O' Os'.
  exists Ol Ocre.
  splits;eauto.
  intros.
  eapply osapi_lift';eauto.
  splits;eauto.
  assert (ks1##kcall f s empenv ks = (ks1 ## (kcall f s empenv kstop ## ks))).
  simpl;auto.
  rewrite H19.
  apply CIH;auto;intros;tryfalse.
  splits;auto.
  right.
  right.
  right.
  left.
  do 5 eexists;splits;eauto.
  intros.
  intro.
  destruct H32;tryfalse.
  do 3 eexists.
  splits;eauto.

  inverts H34.
  rewrite H32 in Hpf;inverts Hpf.
  eapply inos_stkinit_still;eauto.
  inverts H34.
  simpl in H38;rewrite H38 in Hhf;inverts Hhf;eauto.
  assert ((get_genv (get_smem ol)) = (get_genv (get_smem o))).
  clear -H25.
  destruct o as [[[[]]]].
  unfold joinmem in H25.
  simpl in H25;mytac.
  simpl;auto.
  rewrite H34;eauto.
  (*---------------------------*)
  intros.
  inverts H7.
  destruct Hmsim as (R&vlh&AC&Hinos&Hmap&Hr&Hnocallapi&Hmsim).
  inversion Hmsim.
  subst.
  lets Hx:H18 H8 H9 H10;eauto.
  destruct Hx as (gamma'&pri&sleft&t'&OO'&OO''&O'&Os'&Hx).
  mytac.
  eexists.
  exists pri sleft (kenil,ks) t' OO' OO''.
  exists O' Os'.
  splits;eauto.
  intros.
  eapply osapi_lift';eauto.
  destruct H22.
  left.
  mytac;auto.
  assert (ks1##kcall f s empenv ks = (ks1 ## (kcall f s empenv kstop ## ks))).
  simpl;auto.
  rewrite H26.
  apply CIH;auto;intros;tryfalse.
  splits;auto.
  right.
  right.
  right.
  left.
  do 5 eexists;splits;eauto.
  intros.
  intro.
  destruct H27;tryfalse.
  do 3 eexists.
  splits;eauto.
  inverts H29;rewrite H27 in Hpf;inverts Hpf.
  eapply inos_stkfree_still;eauto.
  inverts H29.
  simpl in H33;rewrite H33 in Hhf;inverts Hhf.
  eauto.

  mytac.
  right.
  splits;auto.
  intros.
  lets Hx:H25 H26 H27 H28.
  assert (ks1##kcall f s empenv ks = (ks1 ## (kcall f s empenv kstop ## ks))).
  simpl;auto.
  rewrite H29.
  apply CIH;auto;intros;tryfalse.
  eapply join_satp_local_inv;eauto.
  splits;auto.
  right.
  right.
  right.
  left.
  do 5 eexists;splits;eauto.
  intros.
  intro.
  destruct H30;tryfalse.
  do 3 eexists;splits;eauto.
  inverts H32;rewrite H30 in Hpf;inverts Hpf.
  eapply inos_stkfree_still;eauto.
  inverts H32.
  simpl in H36;rewrite H36 in Hhf;inverts Hhf.
  assert ((get_genv (get_smem o')) = (get_genv (get_smem o))).
  clear -H27.
  destruct o as [[[[]]]].
  unfolds in H27.
  mytac;simpl;auto.
  rewrite H32.
  eauto.
  (*------------------------------------------------*)
  destruct Hc2 as (al&f&s&d1&d2&ft&v&Hpf&Hkeh&Hks2&Hke&Hc&Hcallcont&Hintcont&Hninos).
  subst keh ks2 c ke.
  lets Hfree: H6 Hpf Hninos;eauto.
  assert (ks1 ## (kcall f s empenv kstop ## ks)= ks1 ## kcall f s empenv ks).
  simpl;auto.
  rewrite H1.
  clear H1.
  destruct Hfree as (M&Hf1&Hf2&Hf3&Hf4).
  subst ch.
  apply task_sim.
  intros.

  assert (ltstep (pc, (po, pi, ip)) tid
          (curs (sfree al v), (kenil, ks1 ## kcall f s empenv ks)) cst o2 Cl'
          cst' o'') as Hgg by auto.

  apply free_step with (lasrt:=lasrt) (o:=o) (O:=O) (Ms:=Ms) (M:=M) (Mf:=Mf) (d1:=d1) (d2:=d2) (ft:=ft) in H9;auto.
  destruct H9 as [Hfree | Hfree'].

  assert ( o''= emple_tst o2 /\ cst'= cst /\ Cl' = (curs (sskip v), (kenil,ks))/\freels nil (get_mem (get_smem o)) M);auto.
  destruct H9;destruct H10;destruct H11;subst o'' cst' Cl'.
  exists (curs (sskip v),(kenil,ks)) OO (emple_tst o) Ms O Os.
  splits;auto.
  apply ht_starO.
  clear -H7.
  destruct o as [[[[]]]];unfold joinm2 in *.
  destruct H7.
  exists (emple_tst x).
  unfold joinmem in *;mytac.
  simpl.
  do 6 eexists;simpl;splits;eauto.
  do 6 eexists;simpl;splits;eauto.
  
  destruct o as [[[[]]]].
  unfold emple_tst.
  eapply inv_ncare_le;eauto.
  destruct o as [[[[]]]].
  unfold emple_tst.
  eapply CurLINV_ignore_int;eauto.
  
  assert (ks =kstop ## (kstop ##ks)).
  simpl;auto.
  rewrite H9.
  apply CIH;auto;intros;tryfalse.

  
  destruct o as [[[[]]]].
  unfold emple_tst.
  eapply CurLINV_ignore_int;eauto.
  splits;auto.
  simpl.
  simpl in Hgoodks.

  eapply fun_goodks;eauto.
  simpl.
  simpl in Hndymint.
  destruct Hndymint.
  split;auto.
  eapply n_dym_ks_call;eauto.

  left.
  rewrite <- H9.
  splits;auto.

  apply inos_lift;auto.
  inverts H12.
  destruct o as [[[[]]]].
  simpl in Hf2.
  simpl emple_tst;splits;auto.

  (*Guarded.*)
  destruct Hfree' as (o'&al'&Hjoin&Hcst'&Hcl'&Hfreels'&Hinit').
  subst cst' Cl'.
  exists (curs (sskip v),(kenil,ks)) OO o' Ms O Os.
  splits;auto.
  apply ht_starO.
  destruct o,o'.
  destruct p,p0.
  destruct s0,s1.
  destruct p,p0.
  simpl in Hinit',Hf2.
  unfold InitTaskSt in *.
  assert (i=empisr /\ l = (true, nil, nil) /\ i0=empisr /\ l0=(true, nil, nil)).
  clear -Hinit' Hf2.
  destruct Hf2, Hinit'.
  unfold satp in H.
  lets Hx:H (spec_done None).
  lets Hy:H1 (spec_done None).
  destruct l as [[]].
  destruct l0 as [[]].
  simpl in Hx.
  mytac;auto.
  simpl in Hy;mytac;auto.
  simpl in Hy;mytac;auto.
  mytac.
  clear -Hgg Hjoin H1 H7.
  simpl in H1;simpl.
  destruct o2 as [[[[]]]].
  destruct o'' as [[[[]]]].
  lets Hx:ltstep_eqg Hgg.
  simpl in Hx.
  assert (e3=e3) by auto.
  apply Hx in H.
  subst.
  unfold joinm2 in *.
  unfold joinmem in *.
  mytac.  
  intros;eapply inv_ncare_le;eauto.

  
  eapply free_curlinv_still;eauto.
 
  assert (ks1 ## kcall f s empenv ks = ks1 ## (kcall f s empenv kstop ## ks)).
  simpl;auto.
  rewrite H9.
  clear H9.
  apply CIH;auto;intros;tryfalse.
  eapply free_curlinv_still;eauto.
  splits;auto.
  right.
  right.
  right.
  right.
  exists al' f s d1 d2 ft.
  exists v.
  splits;auto.
  destruct (H13 al' v).
  splits;auto.
  inversion H13;subst al0 v0.
  exists M.
  splits;auto.

  intros;tryfalse.
  inversion H9;subst;tryfalse.
  inversion H11;subst;tryfalse.
  inversion H14;subst;tryfalse.
  intros;tryfalse.
  intros.
  unfold IsEnd in H1.
  destruct H1.
  inversion H1.
  intros.

  lets Hnabt: free_nabt Hcallcont Hintcont Hpf H11 Hf1.
  destruct Hnabt.
  eauto.
  intros;tryfalse.
  intros;tryfalse.
Qed.


Lemma SmCTaskSim:
  forall pc OS1 (A:osspec) lasrt I o O t C,
    no_fun_same (get_afun OS1) (get_ifun OS1) ->
    (*good_ret_funs pc (get_afun OS1) (get_ifun OS1) ->*)
    no_call_api_os (get_afun OS1) (get_ifun OS1) (get_lint OS1) ->
    (forall f t d1 d2 s, (fst (fst OS1)) f = Some (t,d1,d2,s) -> good_decllist (revlcons d1 d2) = true/\GoodStmt' s) ->
    (forall f t d1 d2 s, (snd (fst OS1)) f = Some (t,d1,d2,s) -> good_decllist (revlcons d1 d2) = true/\GoodStmt' s) ->
    (
      forall (f:fid) ab vl p r ft G tid, 
        (fst (fst A)) f = Some (ab,ft) ->
        Some p = BuildPreA (fst (fst OS1)) f (ab,ft) vl G lasrt tid init_lg->
        Some r = BuildRetA (fst (fst OS1)) f (ab,ft) vl G lasrt tid init_lg->
        (
          exists  t d1 d2 s,
            (fst (fst OS1)) f = Some (t, d1, d2, s)/\ GoodStmt' s/\
            MethSimAsrt (snd (fst OS1)) (snd A) lasrt I r Afalse p s Afalse tid
        )
    ) -> 
    (GoodClient pc (fst (fst OS1)) (snd (fst OS1))/\eqdomOS OS1 A) ->
    InitTaskSt lasrt t (pair o O) ->
    (exists s, C= nilcont s /\ GoodStmt s (snd (fst OS1)) /\ True (*/\ good_retef_stmt s kstop*)) ->
    TaskSim (pc, OS1) C o ( pc, A) C O lasrt I (InitTaskSt lasrt t) t.
Proof.
  introv Hnofunsame.
  (*introv Hgoodret.*)
  introv Hnoos.
  introv Hgoodpo.
  intro Hgoodpi.
  intros.
  destruct H2.
  destruct H2.
  subst C.
  unfold nilcont.
  assert (kstop= kstop ##(kstop##kstop)).
  simpl;auto.
  rewrite H2 at 1.
  destruct OS1 as ((po&pi)&ip).
  simpl in Hgoodpo.
  apply SmCTaskSim';auto;intros;subst;tryfalse.
  unfolds in H1.
  destruct H1.
  unfold CurLINV.
  exists init_lg.
  lets Hx:H1 aop.
  sep auto.
  splits;auto.
  destruct H0;auto.
  destruct H0.
  simpl in H0.
  auto.
  simpl in H3.
  destruct H3. 
  simpl.
  auto.
  simpl;split;auto.
  destruct H3.
  eapply goodstmt_n_dym_com_s;eauto.
  simpl;auto.

  left.
  splits;auto.
  unfold InOS.
  intro X.
  destruct X as (c&ke&ks&X&XX).
  inversion X;subst c ke ks.
  destruct XX.
  destruct H4 as (f&vl&fc&tl&H4).
  destruct H4.
  inversion H4.
  subst x.
  simpl in H3.
  destruct H3.
  inversion H3.
  destruct H4.
  destruct H4 as (f&le&ks'&to&d1&d2&s&s'&HX&HXX).
  simpl in HX.
  inversion HX.
  simpl in H4.
  destruct H4.
  auto.
  splits;auto.

  unfold good_clt;split;simpl;auto.
  apply Goodstmt_good_clt_stmt.
  destruct H3;simpl in H3.
  auto.
Qed.

Lemma GoodP_to_S: forall p po pi f a b c s, GoodClient p po pi-> p f = Some (a,b,c,s)-> GoodStmt s pi. 
Proof.
  unfold GoodClient.
  intros.
  eapply H;eauto.
Qed.

Lemma projs_steq_projs:
  forall Sl S' t' t'0 or ge le ir m ir' i si,
    t'0 <> t' ->
    projS Sl t' = Some (ge, le, m, ir, (true, si, nil)) ->
    projS S' t' = Some (ge, empenv, m, ir', (false, i :: si, nil)) ->
    Steq Sl S' t' ->
    projS Sl t'0 = Some or -> projS S' t'0 = Some (fst (fst or), snd (fst S'), snd or).
Proof.
  unfold tid.
  introv Htneq.
  intros.
  destruct Sl.
  destruct p.
  destruct S'.
  destruct p.
  unfold projS in *.
  unfold Steq in H1.
  destruct H1.
  unfold Dteq in H1.
  unfold Piteq in H3.
  destruct c.
  destruct p.
  destruct c0.
  destruct p.
  remember (projD (e0, c0, m1) t'0) as X.
  unfold tid in *.
  destruct X;tryfalse.
  remember (get l0 t'0) as Y.
  destruct Y;tryfalse.
  remember (projD (e, c, m0) t') as XX.
  unfold tid in *.
  destruct XX;tryfalse.
  remember (get l t') as YY.
  destruct YY;tryfalse.
  remember (projD (e, c, m0) t'0) as XXX.
  destruct XXX;tryfalse.
  remember (get l t'0) as YYY.
  destruct YYY;tryfalse.
  inverts H.
  inverts H2.
  simpl.
  remember (projD (e0, c0, m1) t') as Z.
  destruct Z;tryfalse.
  remember (get l0 t') as ZZ.
  destruct ZZ;tryfalse.
  lets H11: H1 Htneq.
  clear H1.
  lets H13 : H3 Htneq.
  clear H3.
  inverts H0.
  unfold projD in *.
  unfold tid in *.
  rewrite H11 in *.
  rewrite <- HeqYYY in *.
  rewrite <- HeqY in *.
  inverts H13.
  rewrite <- H11 in *.
  destruct (get c t');tryfalse.
  inverts HeqXX.
  destruct (get c0 t');tryfalse.
  inverts HeqZ.
  destruct (get c t'0);tryfalse.
  rewrite <-HeqXXX in HeqX.
  inverts HeqX.
  auto.
  lets H11: H1 Htneq.
  clear H1.
  lets H13 : H3 Htneq.
  clear H3.
  rewrite <- H13 in *.
  destruct (projD (e, c, m0) t'0);tryfalse.
  destruct (get l t'0);tryfalse.
  lets H11: H1 Htneq.
  clear H1.
  lets H13 : H3 Htneq.
  clear H3.
  unfold projD in *.
  unfold tid in *.
  rewrite <- H11 in *.
  destruct (get c t'0);tryfalse.
Qed.




(*******************************************************)
(*******************************************************)
(*******************************************************)
(*******************************************************)
(*******************************************************)
(*******************************************************)



Lemma tasks_set_get_neq: forall T t t' a, t<>t' -> TasksMod.get (TasksMod.set T t a) t' =  TasksMod.get T t'.
Proof.
  intros.
  apply TasksMod.set_a_get_a'.
  apply tidspec.neq_beq_false.
  apply H.
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
  pose proof tidspec.beq_true_eq t t0 eq1; substs.
  assert(exists x0, TcbMod.get x t0 = Some x0) by eauto.
  apply H3 in H4.
  destruct H4.
  exists C'.
  apply TasksMod.set_a_get_a;auto.
  rewrite TasksMod.set_a_get_a';auto.
  apply H3.
  eexists;eauto.
Qed.


Lemma change_tstm_trans': forall o M Ms, substaskst (substaskst o M) Ms = substaskst o Ms.
Proof.
  unfold substaskst.
  intros.
  destruct o.
  destruct p.
  destruct s.
  destruct p.
  reflexivity.
Qed.


Lemma repl_change_tstm_trans: forall o M Ms, substaskst (substaskst o M) Ms = substaskst o Ms.
Proof.
  apply change_tstm_trans'.
Qed.



  

Lemma tsimtopsim: 
  forall pl Tl Sl ph Th O cst t,
    get O curtid = Some (oscurt t)->
    (
      exists (pc:progunit) (A:osspec) po pi ip Tm To Ol Os Ms Ml I lasrt ,
        no_fun_same po pi/\
        True /\
        (*good_ret_funs pc po pi /\*)
        no_call_api_os po pi ip /\ 
        (forall f t d1 d2 s, po f = Some (t,d1,d2,s) -> good_decllist (revlcons d1 d2) = true/\GoodStmt' s) /\ (forall f t d1 d2 s, pi f = Some (t,d1,d2,s) -> good_decllist (revlcons d1 d2) = true/\GoodStmt' s) /\
        pl = (pc, ( po, pi, ip)) /\ ph = (pc, A) /\ (GoodClient pc po pi/\ True /\ good_t_ks pl Tl /\ good_is_S Sl/\GoodI I (snd A) lasrt(*/\eqdomcstO cst O*) ) 

        /\

        join Ml Ms (snd (fst (fst Sl))) 

        /\

        partM Ml Tl Tm

        /\               
   
        join Ol Os O /\

        partO Ol Tl To

        /\

        (exists o o', projS Sl t = Some o /\ substaskst o Ms = o' /\(forall ab, sat ((pair o' Os),ab) (INV I) )) 
        
        /\
        
        (
          exists o o' Mc Oc Cl Ch,
            TMSpecMod.maps_to Tm t Mc /\
            TOSpecMod.maps_to To t Oc /\
            projS Sl t = Some o /\ substaskst o Mc = o' /\ 
            get Th t = Some Ch /\ get Tl t = Some Cl /\
            satp o' Oc (CurLINV lasrt t) /\ 
            TaskSim pl Cl o' ph Ch Oc lasrt I (InitTaskSt lasrt t) t
        )
          
        /\

        (
          forall t' Ch,
            ~(t'=t) ->
            get Th t' = Some Ch ->
            task_no_dead O t' ->
            (
              exists o M' Cl O', 
                TMSpecMod.maps_to Tm t' M' /\
                TOSpecMod.maps_to To t' O' /\
                projS Sl t' = Some o /\
                satp (substaskst o M') O' (EX lg, LINV lasrt t' lg ** Atrue) /\
                get Tl t' = Some Cl/\
                (
                  forall Mr Or, 
                    (forall ab, sat ((pair (RdyChange (substaskst o Mr)) Or),ab) (RDYINV I t'))/\ 
                    disjoint Mr M' /\
                    disjoint Or O' ->
                    (
                      exists M'',
                        M''= merge Mr M' /\ 
                        TaskSim pl Cl (RdyChange (substaskst o M'')) ph Ch (merge Or O') lasrt I (InitTaskSt lasrt t') t'
                    )
                )                 
                  
            )
        )

       /\ eqdomTO Th O /\  eqdomOS (po, pi, ip) A
          
       /\ 
       (
          forall (f:fid) ab vl p r ft G tid, 
            (fst (fst A)) f = Some (ab,ft )->
            Some p = BuildPreA po f (ab,ft) vl G lasrt tid init_lg->
            Some r = BuildRetA po f (ab,ft) vl G lasrt tid init_lg->
            (
              exists t d1 d2 s,
                po f = Some (t, d1, d2, s)/\ GoodStmt' s /\
                 MethSimAsrt pi (snd A) lasrt I r Afalse p s Afalse tid
            )
       )
       /\ 
       (
          forall (i:hid) ispec isrreg si G lg tid, 
            (snd (fst A)) i = Some ispec ->
            (
              exists (s:stmts) p r,
                ip i = Some s /\ 
                p = ipreasrt i isrreg si (ispec ) I G lasrt tid lg/\ 
                r = iretasrt i isrreg si I G lasrt tid lg /\
                MethSimAsrt pi (snd A) lasrt I retfalse r p s Afalse tid
        )
       )
    )
->
ProgSim pl Tl Sl ph Th O cst t.   
Proof.
  cofix CIH.
  introv Hosabsttid.
  intros.
  destruct H as (pc & A & po & pi & ip & Tm & To & Ol & Os &Ms & Ml & I & lasrt & H).
  destruct H as (Hnofunsame&Hgoodret&Hnocallapi&Hgoodpo&Hgoodpi &  H).
  destruct H as (Hpl & Hph &Hgoodpc& Hmjoin & Hmpart & HOjoin 
                 & HOpart & Hinv & Hcsim & Hrsim & Heqdomto & Heqdomos
                 & Hapimsem & Hintmsem).
  destruct Hgoodpc as (Hgoodpc&Hgoodg&Hgoodks&Hgoodiss&Hgoodi).
  apply prog_sim.
  auto.
  intros. 
  subst.
  inversion H;tryfalse.

  (*---------------------------interrupt step -------------------------------*)
  inversion H0.
  subst.
  inversion H6.
  subst.
  
  destruct Hcsim as (o&o'&Mc&Oc&Cl&Ch&Htmspec&Htospec&Hproj&Hrepl&Htasksch&Htaskscl&Hlinv&Hcsim).
  destruct Ch as (ch,(keh,ksh)).
  destruct A as ((apispec,intspec),sc).
  assert (exists absi, intspec i = Some absi).
  unfold eqdomOS in Heqdomos.
  destruct Heqdomos as (Heqdomos1&Heqdomos2&Heqdomos3).
  simpl in Heqdomos3.
  lets Hx: Heqdomos3 i.
  destruct Hx.
  apply H2.
  eexists;eauto.
  destruct H2.

  
  exists (TasksMod.set Th t' (curs (hapi_code (x )),(kenil,kevent ch keh ksh))) O.
  split.
  subst.
  eapply hp_stepS.
  2:apply hp_stepO.
  eapply hi_step;eauto.
  constructors;eauto.
  apply CIH.
  
  auto.
  exists pc0 ((apispec,intspec),sc) po0 pi0 ip0.
  assert (lintstep ip0 (c, (ke, ks)) (ge, le, m, ir, (true, si, nil))
         (curs s, (kenil, kint c ke le ks))
         (ge, empenv, m, isrupd ir i true, (false, i :: si, nil))) as Hintstep.
  auto.
  apply int_mem_trans with (Ms:=Ms) (I:=I) (Os:=Os) (Ml:=Ml) (sd:=sc) (li:=lasrt)in H6.
  destruct H6 as (Ms'& Ml'& Os' &Ol'&H6).
  exists (TMSpecMod.put Tm t' (merge Mc Ml')).
  exists (TOSpecMod.put To t' (merge Oc Ol')).
  exists (merge Ol Ol') Os' Ms' (merge Ml Ml') I.
  exists lasrt.
  split;auto.
  split;auto.
  splits;auto.
  splits;auto.
  
  eapply lpstep_goodks;eauto.
  eapply lpstep_good_is_S;eauto.
  assert (  (snd (fst (fst S'))) = (snd (fst (fst (ge, empenv, m, isrupd ir i true, (false, i :: si, (nil:cs)))))) ).


  eapply projs_eqm in H4.
  eauto.
  assert ( (snd (fst (fst Sl))) = (snd (fst (fst (ge, le, m, ir, (true, si, (nil:cs)))))) ).
  apply projs_eqm with t'.
  auto.
  simpl in H10.
  simpl in H11.
  rewrite H10.
  rewrite H11 in *.


  eapply join_join_join_merge;eauto.
  destruct H6;auto.
  
  split.

  apply part_merge_m.
  Focus 2.
  destruct H6.
  clear -H6 Hmjoin.
  unfolds.
  join auto.
  apply Htmspec.
  auto.
  split.
  eapply join_join_join_merge;eauto.
  destructs H6;auto.
  split.
  apply part_merge_o.
  Focus 2.
  destructs H6.
  clear -H10 HOjoin.
  unfolds.
  join auto.
  apply Htospec.
  auto.
  
  splits;auto.
  do 2 eexists;splits;eauto.

  destructs H6.
  auto.
  
  exists (ge, (empenv:env), m, isrupd ir i true, (false, i :: si, (nil:cs))) (substaskst (ge, (empenv:env), m, isrupd ir i true, (false, i :: si, (nil:cs))) (merge Mc Ml')) (merge Mc Ml') (merge Oc Ol') ((curs s), (kenil, ( kint c ke le ks))) (curs (hapi_code (x)), (kenil, kevent ch keh ksh)).
  splits.
  apply  TMSpecMod.ext_mapsto.
  auto.
  auto.
  auto.
  apply  TasksMod.set_a_get_a.
  unfold tidspec.beq.
  apply tidspec.eq_beq_true.
  auto.
  apply  TasksMod.set_a_get_a.
  unfold tidspec.beq.
  apply tidspec.eq_beq_true.
  auto.
  
  rewrite H3 in Hproj.
  inverts Hproj.
  simpl in Hrepl.
  subst o'.
  simpl substaskst.

  eapply CurLINV_merge_hold.
  assert (disjoint Mc Ms).
  eapply part_disjm;eauto.
  clear -Hmjoin.
  unfolds;join auto.
  destruct H6.
  clear -H6 H10.
  unfold disjoint in *.
  join auto.
  assert (disjoint Oc Os).
  eapply part_disjo;eauto.
  clear -HOjoin.
  unfolds;join auto.
  destructs H6.
  clear -H11 H10.
  unfold disjoint in *.
  join auto.
  eapply CurLINV_ignore_int;eauto.

    
  assert (Cl= (c, (ke, ks))) as Hfuck1l.
  unfold tid in *.
  rewrite H1 in Htaskscl.
  inversion Htaskscl;tryfalse;auto.
  rewrite H3 in Hproj.
  inverts Hproj.
  simpl in Hrepl.
  subst o'.
  simpl substaskst.

  destruct H6 as ( Hmsjoin & Hosjoin & Hg1).
  subst Cl.

  
  assert (lintstep' i ip0 (c, (ke, ks)) (ge, le, m, ir, (true, si, nil))
               (curs s, (kenil, kint c ke le ks))
               (ge, empenv, m, isrupd ir i true, (false, i :: si, nil))).
  subst.
  eapply li_step;eauto.

  eapply IntSeq' with (c:=c) (ke:=ke) (ks:=ks) (Mi:=Ml')
                            (s:=s)  (t:=t') (I:=I) (p:=(InitTaskSt lasrt t')) (O:=Oc) (Oi:=Ol')
                            (Mc:=Mc)  (Ms':=Ms')
                            (Os':=Os');eauto.
  simpl substaskst.
  auto.
  destruct Hinv.
  destruct H10.
  destructs H10.
  rewrite H10 in H3;inverts H3.
  simpl in H11.
  subst x1.
  auto.
  eapply part_disjo;eauto.
  clear -HOjoin.
  unfolds;eauto.
  eapply part_disjm;eauto.
  clear -Hmjoin.
  unfolds;eauto.
 
  intros.
  assert (t'0<>t') as Hneqt.
  auto.
  apply Hrsim with (Ch:=Ch)in H10;auto.
  destruct H10 as (or&M'&Clr&O'&Hrsim').
  destruct Hrsim' as (Htmspecr&Htospecr&Hprojr&Hsatlinv&Htasksmod&Hrsim'').

  exists ((fst (fst or)),(snd (fst S')),(snd or)) M' Clr O'.
  splits;auto.
  

  apply tm_mapsto_put' with (t:=t') (a:=merge Mc Ml');auto.
  apply to_mapsto_put' with (t:=t') (a:=merge Oc Ol');auto.

  subst o'.

  eapply projs_steq_projs;eauto.
  destruct or as [[[[]]]].
  simpl.
  simpl in Hsatlinv.
  eapply LInv_ignore_int;eauto.


  rewrite tasks_set_get_neq;auto.
  intros.
  rename H12 into Hnodead.
  assert (RdyChange (substaskst or Mr) =RdyChange( substaskst (fst (fst or), snd (fst S'), snd or) Mr)).
  destruct or as [[[[]]]].
  simpl.
  auto.
  rewrite <- H12 in *.
  apply Hrsim'' in H10.
  mytac.
  eexists;splits;eauto.

  assert (RdyChange (substaskst or (merge Mr M')) =RdyChange( substaskst (fst (fst or), snd (fst S'), snd or) (merge Mr M'))).
  destruct or as [[[[]]]].
  simpl.
  auto.
  rewrite <- H0.
  auto.

  rewrite TasksMod.set_a_get_a' in H11.
  auto.
  apply tidspec.neq_beq_false.
  auto.
  clear -Heqdomto Htasksch.

  eapply eqdomTO_setT;eauto.

  auto.
  simpl.
  rewrite H3 in Hproj;inverts Hproj.
  simpl in Hrepl;subst.
  apply projs_eqm with (t:=t') in H3.
  rewrite H3 in Hmjoin.
  simpl in Hmjoin;auto.

  destruct Hinv as (or&or'&Hon&Honrep&Hg).
  rewrite Hon in H3.
  inversion H3;tryfalse;auto.
  subst or.
  simpl in Honrep;subst or'.
  auto.
  (*---------------------------interrupt step end -------------------------------*)



  (*--------------------------- normal step  -------------------------------*)
  subst.
  destruct Hcsim as (o&o'&Mc&Oc&Cl&Ch&Htmspec&Htospec&Hproj&Hrepl&Htasksch&Htaskscl&Hsatlinv&Hcsim).
  assert (o=tst).
  rewrite H2 in Hproj.
  inversion Hproj;tryfalse;auto.
  subst tst.
  unfold tid in *.
  rewrite Htaskscl in H0.
  inverts H0.
  rename C into Cl.

  inversion Hcsim.
  subst.
  destruct Hinv as (on&on'&Hproj'&Hrepl'&Hinv).
  rewrite Hproj' in H2.
  inverts H2.
  assert (substaskst (substaskst o Mc) Ms = on').
  rewrite <- Hrepl'.



  apply repl_change_tstm_trans.
  subst.
  rewrite <- H2 in Hinv.
  unfold satp in *.
  apply H0 with (Cl':=C') (cst:=cst) (cst':=cst') (o'':=tst')
                          (o2:=o) (Mf:=minus Ml Mc) (OO:=merge Oc Os) in Hinv.
  destruct Hinv as (Ch'&OO'&o'&Ms'&O'&Os'&Hhtstep&Hjoin2l&Hjoinh&Hinv&Htlinv&Htsim).

  
  eapply htstepstar_O_local with (Of:= (minus Ol Oc)) (OO:=O) in Hhtstep.
  mytac.

  exists (set Th t' Ch') x.
  split.

  apply th_no_create_lift  with (C:=Ch);auto.

  apply CIH.

  rename H11 into Hhtstep.
  apply htstepstar_tidsame in Hhtstep;auto.
  unfold tidsame in Hhtstep.
  unfold get in Hhtstep,Hosabsttid.
  simpl in Hhtstep.
  simpl in Hosabsttid.
  rewrite Hosabsttid in Hhtstep;auto.

  exists pc A po pi ip (TMSpecMod.put Tm t' (get_mem (get_smem o'))).
  subst.

  exists (TOSpecMod.put To t' O') (minus x Os') Os' Ms' (minus (get_mem (get_smem tst')) Ms').
  exists I lasrt.

  
  destruct tst' as [[[[]]]].
  splits;auto.

  splits;auto.
  splits;auto.

  eapply lpstep_goodks;eauto.
  eapply lpstep_good_is_S;eauto.
  
  assert (snd (fst (fst S')) = snd (fst (fst (e, e0, m, i, l)))).
  apply projs_eqm with (t:=t');auto.
  rewrite H13.
  simpl.

  eapply joinm2_minus_join;eauto.
  simpl.
  eapply partm_task_get_set;eauto.

  eapply partM_normal;eauto.
  eapply join_join_minus;eauto.
  
  eapply parto_task_get_set;eauto.
  eapply partO_normal;eauto.
  
 
  exists (e, e0, m, i, l) (e, e0, Ms', i, l).
  splits;auto.
  
  assert (substaskst o' Ms'= (e, e0, Ms', i, l)) as Hrepltrans.
  clear -Hjoin2l.
  unfolds in Hjoin2l.
  mytac.
  unfold joinmem in *.
  mytac.
  simpl;auto.
  rewrite Hrepltrans in Hinv.
  auto.

  exists (e, e0, m, i, l) o'
         (get_mem (get_smem o')) O' C' Ch'.
  splits;auto.
  clear -Hjoin2l.
  unfolds in Hjoin2l.
  mytac.
  unfold joinmem in *.
  mytac.
  simpl.
  auto.
  apply map_get_set.
  apply map_get_set.

  splits;auto.
  intros.
  
  rename H15 into Hnodead.
  assert (t'0<>t');auto.

  apply Hrsim with (Ch:=Ch0) in H13.

  destruct H13 as (or&M'r&Clr&O'r&Htmr&Htor&Hprojr&Hrlinv&Htasksr&Hsimr).

  exists (((gets_g S'),(get_env (get_smem or)),(gets_m S')),(snd (fst S')),
          (snd or)) M'r Clr O'r.
  splits;auto.
  apply tm_mapsto_put' with (t:=t') (a:=get_mem (get_smem o'));auto.
  apply to_mapsto_put' with (t:=t') (a:=O');auto.

  
  apply proj_stneq_ex with (S:=Sl) (t:=t'); auto.
  2:rewrite tasks_set_get_neq;auto.
  intros.
  eapply LInv_ignore_int.
  assert (substaskst
            (gets_g Sl, get_env (get_smem or), gets_m S', snd (fst or), snd or) M'r = substaskst or M'r).

  simpl.
  clear -Hprojr H4.
  destruct Sl as [[[[]]]].
  destruct S' as [[[[]]]].
  destruct or as [[[[]]]].
  unfold gets_g,get_env.
  simpl in *.
  unfold tid in *.
  remember (get c t'0) as X.
  destruct X;tryfalse.
  remember (get l t'0) as Y.
  destruct Y;tryfalse.
  inverts Hprojr.
  auto.

  assert (gets_g Sl = gets_g S') by (eapply ge_n_change;eauto).
  rewrite <- H16.
  simpl in H13.
  erewrite H13.
  eauto.

  intros.
  
  assert (gets_g Sl = gets_g S') by (eapply ge_n_change;eauto).
  assert (forall Mr,RdyChange
            (substaskst
               (gets_g S', get_env (get_smem or), 
               gets_m S', snd (fst S'), snd or) Mr) = RdyChange (substaskst or Mr)).
  intros.
  simpl.
  clear -Hprojr H4 H16.
  destruct Sl as [[[[]]]].
  destruct S' as [[[[]]]].
  destruct or as [[[[]]]].
  unfold gets_g,get_env in *.
  simpl in *.
  unfold tid in *.
  remember (get c t'0) as X.
  destruct X;tryfalse.
  remember (get l t'0) as Y.
  destruct Y;tryfalse.
  subst e.
  inverts Hprojr.
  auto.

  rewrite H17 in H13.
  apply Hsimr in H13.
  mytac.
  eexists.
  erewrite H17.
  splits;eauto.
  
  rewrite <- H14. auto.
  symmetry.
  apply tasks_set_get_neq;auto.
  eapply htstepstar_nodead_still;eauto.
  eapply hpstep_eqdomto with (T:=Th) (O:=O) (cst:=cst) (cst':=cst') (p:=(pc,A));eauto.
  apply th_no_create_lift with (C:=Ch);auto.

  eapply join_merge_minus;eauto.
  eapply parto_sub;eauto.

  eapply joinm2_merge_minus;eauto.
  assert ( (snd (fst (fst Sl))) = (snd (fst (fst o)) )).
  apply projs_eqm with t'.
  auto.
  destruct o as [[[[]]]].
  simpl in H11.
  simpl get_smem.
  simpl get_mem.
  rewrite <- H11;auto.
  eapply part_sub;eauto.
  apply join_merge_disj.
  eapply part_disjo;eauto.
  unfolds;eauto.
  auto.
  (**Guarded.**)

  
  (*--------------------------- normal step end -----------------------------*)

  
  (*-----------------------------switch step ---------------------------*)


  subst.
  inversion H0;subst pc0 po0 pi0 ip0.

  (*keep the name of H*)
  rename H9 into H10.
  rename H8 into H9.
  
  rename H4 into H5.
  rename H3 into H4.
  rename H2 into H3.
  rename H1 into H2.

  
  assert (projS (ge, les, m, ir, au) t = Some tst) as H1 by auto.
  (*----------------*)
  destruct Hcsim as (o&o'&Mc&Oc&Cl&Ch&Hcsim).
  destruct Hcsim as (Htm&Hto&Hproj&Hsubs&Hth&Htl&Hlinv&Hcsim).
  inversion Hcsim.
  subst.
  assert (Cl= (curs (sprim (switch x)), (kenil, ks))).
  unfold tid in *.
  unfold get in Htl.
  simpl in Htl.
  unfold get in H5.
  simpl in H5.
  rewrite H5 in Htl.
  inverts Htl.
  auto.
  eapply H8 with (OO:=merge Oc Os) (Ms:=Ms) (Os:=Os) in H15.
  destruct H15 as (Ch'&sleft&k&OO'&Mc'&ol&O'&Os'&Olc&Occ&Hhch&Hhtstep&Hljoin&Hhjoin&Hhjoin'&Hinv'&Hswinv&Hlinv'&H15).
  destruct H15.
  destruct H15 as (Hswpre&H15).
  eapply htstepstar_O_local with (Of:= (minus Ol Oc)) (OO:=O) (cst:=cst') in Hhtstep.

  Focus 2.
  eapply join_merge_minus;eauto.
  eapply parto_sub;eauto.

  mytac.
  
  rewrite repl_change_tstm_trans in *.
  exists (set Th t (curs (hapi_code sleft), k)) (set x0 curtid (oscurt t')).

  (*HHHH*)
  assert (  hpstep (pc, A) (set Th t (curs (hapi_code (sched;; sleft)), k)) cst' x0
                   (TasksMod.set Th t (curs (hapi_code sleft), k)) cst' (set x0 curtid (oscurt t')) /\  forall ab, (tst, x0 , ab) |= AHprio (snd A) t' ** Atrue).
 
  eapply sw_same_t with (l:=l) (tp:=tp) (x:=x) (tst:=tst) (t':=t');eauto.
  unfolds in Hgoodi.
  mytac;simpl;auto.

  apply htstepstar_tidsame in H16.
  unfolds in H16.
  rewrite <- H16.
  auto.

  rewrite H2 in Hproj;inverts Hproj.
  rewrite H17 in H2;inverts H2.
  simpl snd.
  unfold getsched in Hswpre.
  simpl snd in Hswpre.
  unfold satp in *.
 
  eapply swpre_prop with (M:=Mc');eauto.
  intros.
  unfold SWPRE_NDEAD in Hswpre.
  lets Hx:Hswpre ab.
  destruct Hx.
  eauto.
  
  apply projs_eqm in H17.
  destruct o as [[[[]]]].
  simpl in H17.
  simpl.
  subst m0.

  eapply part_sub with (Mc:=Mc) in Hmpart;eauto.
  eapply sub_join_sub;eauto.
  clear -Hmpart Hljoin.
  unfold joinmem in *.
  mytac.
  simpl in H0;inverts H0.
  unfold Maps.sub in *.
  destruct Hmpart.
  unfold TMSpecMod.B in *.
  unfold mmapspec.image in *.
  join auto.
  clear -Hhjoin' Hhjoin H18.
  unfolds Maps.sub.
  unfold TOSpecMod.B in *.
  unfold omapspec.image in *.
  geat.
  
  assert (hpstepstar (pc, A) Th cst' O
                     (set Th t (curs (hapi_code sleft), k)) cst' (set x0 curtid (oscurt t')) ) as Hpstepstar.
  
  assert (hpstepstar (pc, A) Th cst' O 
                     (set Th t (curs (hapi_code sleft), k)) cst' (set x0 curtid (oscurt t')) ) as Hhpstep.

  assert (hpstepstar (pc, A) Th cst' O
                     (set Th t (curs (hapi_code  (sched;; sleft)), k)) cst' x0).
  apply th_no_create_lift with (C:=Ch);auto.

  eapply hpstep_star with (T':=(set Th t (curs (hapi_code  (sched;; sleft)), k))) (cst':=cst') (O':=x0);eauto. 

  destruct H0;auto.
  auto.

  rename H0 into HHHH.
  destruct HHHH as (Hxx&HHHH).
  clear Hxx.
  

  assert (forall ab,(substaskst o Mc', Occ, ab) |= AHprio (snd A) t' ** Atrue).
  eapply lemma_trans_temp;eauto.
  unfolds in Hgoodi;destructs Hgoodi;auto.
  intros.
  lets Hx:Hswpre ab.
  unfold SWPRE_NDEAD in Hx;destruct Hx.
  eauto.
  clear -Hhjoin' Hhjoin H18.
  unfolds Maps.sub.
  unfold TOSpecMod.B in *.
  unfold omapspec.image in *.
  geat.
  clear HHHH.
  rename H0 into HHHH.
  split;auto.
  apply CIH.
  eapply map_get_set.
  destruct (tid_eq_dec t t').

  (*--------cur == highest rdy-------------*)
  subst t'.

  assert (o=tst).
  rewrite H2 in Hproj.

  inversion Hproj;tryfalse;auto.
  subst tst.
  destruct o as [[[[]]]].
  unfold joinmem in Hljoin.
  destruct Hljoin.
  do 5 destruct H0.
  destructs H0.
  simpl in H19.
  inversion H19;subst x2 x7 x3 x6 x5.
  subst ol.
  unfold substaskst in *.
  unfold get_smem in*.
  unfold get_genv in *.

  apply projs_eqg in Hproj.
  simpl in Hproj.
  subst e.

  assert ( ((ge, e0, Mc', i, l0), Occ,(spec_done None)) |= SWPRE (snd A) x t) as Hnmc';auto.
  lets Hx:Hswpre (END None).
  unfold SWPRE_NDEAD in Hx.
  destruct Hx;eauto.
  eapply swpre_store with (b:=b) (tp:=(Tptr tp)) (t:=t) in Hnmc';auto.

  destruct Hnmc' as (Mc'n&Hmc'n).
  lets Hnmc:join_store' H21 Hmc'n.
  destruct Hnmc as(Mcn&Hmcn).
  lets Hnmpart:part_store_part Hmpart Htm Hmcn.
  destruct Hnmpart as (Ml'&Hstoreml&Hmpartn).
  assert (set O' curtid (oscurt t) = O') as Ho'set.
  clear -Hswinv Hhjoin' Hgoodi.
  unfolds in Hgoodi.
  lets Hx:Hswinv (spec_done None).
  destructs Hgoodi.
  apply H0 in Hx.
  mytac.
  eapply join_get_get_r in Hhjoin';eauto.
  apply get_set_same;auto.
  exists pc A po pi ip (TMSpecMod.put Tm t Mcn).
  exists (TOSpecMod.put To t O') (merge O' (minus Ol Oc)) Os' Ms Ml' I.
  exists lasrt.
  splits;auto.
  splits;auto.
  splits;auto.
  eapply lpstep_goodks;eauto.
  clear -Hgoodiss.
  unfold good_is_S in *.
  intros.
  destruct tst.
  destruct p.
  destruct p.
  destruct p.
  destruct l.
  destruct p.
  assert (projS (ge, les, m, ir, au) t = Some (e, e0, m, i, (i0, i1, c))).
  unfold projS in *.
  unfold projD in *.
  unfold tid in *.
  destruct (get les t);tryfalse;auto.
  destruct (get au t);tryfalse;auto.
  inverts H;auto.
  apply Hgoodiss in H0.
  auto.
  simpl.
  apply join_comm.
  eapply join_store_join;eauto.
  eapply join_comm;eauto.
  eapply partm_task_get_set;eauto.
  apply htstepstar_tidsame in H16.
  unfold tidsame in H16.
  unfold get in H16,Hosabsttid.
  simpl in H16.
  simpl in Hosabsttid.
  rewrite Hosabsttid in H16.
  unfold tid in *.
  rewrite <- Ho'set.
  eapply join_join_join_merge_set;eauto.

  eapply parto_task_get_set;eauto.
  
  eapply new_part_o;eauto.
  clear -Hhjoin H18.
  eapply join_join_disj_l;eauto.

  destruct x1.
  destruct p.
  destruct p.
  destruct p.
  exists (e, e1, m', i0, l1) (e, e1, Ms, i0, l1).
  rewrite H2 in H17;inverts H17.
  splits;auto.
  clear -H2.
  unfold projS in *.
  unfold projD in *.
  unfold tid in *.
  destruct (get les t);tryfalse.
  destruct (get au t);tryfalse.
  inverts H2;auto.

  exists  (ge, e0, m', i, l0) (ge,e0,Mcn,i,l0) Mcn  O' (SKIP, (kenil, ks)) (curs (hapi_code sleft), k).
  splits;auto.
  clear -H2.
  unfold projS in *.
  unfold projD in *.
  unfold tid in *.
  destruct (get les t);tryfalse.
  destruct (get au t);tryfalse.
  inverts H2;auto. 
  apply map_get_set.
  apply map_get_set.

  eapply curlinv_switch_self;eauto.
  unfolds;intros.
  lets Hx:Hswpre aop.
  unfold SWPRE_NDEAD in Hx;destruct Hx.
  eauto.
  eapply H15 with (Mc':=Mc'n);eauto.
  Focus 2.
  unfold joinmem.
  do 6 eexists;splits;eauto.
  eapply join_store_join;eauto.
  
  unfolds;intros.
  lets Hnswinv: goodI_swinv_samet Hgoodi Hswinv HHHH.
  eauto.
  eauto.
  eapply Hlinv'.
  destruct Hnswinv as (Hswinvget&Hnswinv).
  destruct Hswinvget.
  destruct H0.
  destructs H0.
  rewrite H0 in H9;inversion H9;subst x2 x3.
  eapply Hnswinv;eauto.
  splits;auto.

  intros.
  assert (t'<>t) as Htneq;auto.
  apply Hrsim with (Ch:=Ch0) in H0.
  destruct H0 as (or&Mr'&Clr&Or'&Hrtm&Hrto&Hrproj&Hrlinv&Hrts&H0).
  exists (substaskst or m') Mr' Clr Or'.
  splits;auto.
  eapply tm_mapsto_put';eauto.
  eapply to_mapsto_put';eauto.
  destruct or as [[[[]]]].
  unfold substaskst.
  clear -Hrproj.
  unfold projS in *.
  unfold projD in *.
  unfolddef.
  destruct ( get les t' );tryfalse.
  destruct ( get au t'  );tryfalse.
  inverts Hrproj;auto.
  2:rewrite tasks_set_get_neq;auto.
  destruct or as [[[[]]]].
  simpl.
  auto.
  
  destruct or as [[[[]]]].
  unfold substaskst.
  auto.
  rewrite tasks_set_get_neq in H22;auto.
  eapply htstepstar_nodead_still;eauto.
  clear -H23.
  unfolds.
  unfolds in H23.
  intros.
  apply H23.
  rewrite map_get_set';auto.
  apply  hpstep_eqdomto in Hpstepstar;auto.
  eauto.
  (*--------cur <> highest rdy-------------*)
  assert (exists C, TasksMod.get (TasksMod.set Th t (curs (hapi_code sleft), k)) t' = Some C).

  eapply sw_has_code with (l:=l) (tp:=(Tptr tp)) (x:=x) (tst:=tst) (O:=x0) (sd:=snd A);auto.
  unfolds in Hgoodi;destructs Hgoodi;auto.
  assert (o=tst).
  rewrite H2 in Hproj.
  inversion Hproj;tryfalse;auto.
  subst tst.
  eapply swpre_prop with (M:=Mc');eauto.
  
  intros.
  lets Hx:Hswpre ab.
  unfold SWPRE_NDEAD in Hx;destruct Hx;eauto.
  
  assert (Maps.sub Mc Ml).
  apply part_sub with (T:=Tl) (Tm:=Tm) (t:=t);auto.
  clear -Hljoin H0 Hmjoin H2.
  destruct o as [[[[]]]].
  simpl in *.
  unfolddef.
  destruct (get les t);tryfalse.
  destruct (get au t);tryfalse.
  inverts H2.
  unfolds in Hljoin.
  mytac.
  geat.
  clear -Hhjoin Hhjoin' H18.
  unfolddef.
  
  geat.

  apply hpstep_eqdomto in Hpstepstar;auto.
  unfold eqdomTO in *.
  clear -Hpstepstar.
  mytac.
  eexists;split;eauto.
  Lemma abst_set_get_neq: forall id1 id2 y O, id1<>id2 ->  OSAbstMod.get (OSAbstMod.set O id2 y) id1 = OSAbstMod.get O id1.
  Proof.
    intros.
    apply OSAbstMod.set_a_get_a'.
    apply absdataidspec.neq_beq_false.
    auto.
  Qed.
  rewrite abst_set_get_neq in H;auto.
 

  destruct H0 as (Cn&Hcn).
  rewrite tasks_set_get_neq in Hcn;auto.
  assert (TasksMod.get Th t' = Some Cn) as Hcode;auto.
  apply Hrsim in Hcn;auto.
  destruct Hcn as (on&Mn&Cn'&On&Htmn&Hton&Hprojn&Hlinvn&Htasksn&Hcn).
  assert (disjoint Mc' Ms).
  clear -Hljoin Hmjoin Hmpart Htm.
  destruct o.
  destruct p.
  destruct p.
  destruct p.
  simpl in *.
  unfold joinmem in *.
  mytac.
  assert (disjoint x2 Ms). 
  apply part_disjm with (M:=Ml) (T:=Tl) (Tm:=Tm) (t:=t);auto.
  unfolddef.
  clear -Hmjoin.
  geat.
  clear -H1 H.
  unfolddef.
  geat.
  

  assert (exists Mcc,store (Tptr tp) Mc' (b,0%Z) (Vptr t') = Some Mcc).
  destruct o as [[[[]]]];unfold substaskst in Hswpre.
  assert ((e, e0, Mc', i, l0, Occ, (spec_done None)) |= SWPRE (snd A) x t);auto.
  lets Hx:Hswpre (END None).
  unfold SWPRE_NDEAD in Hx.
  destruct Hx;eauto.
  eapply swpre_store with (ab:=spec_done None);eauto.
  clear -Hproj H9.
  simpl in Hproj.
  unfolddef.
  destruct (get les t);tryfalse.
  destruct (get au t);tryfalse.
  inverts Hproj.
  unfold get in H9;simpl in H9;auto.
  destruct H19 as (Mcc&Hmcc).


  eapply swi_rdy_inv'''' with (o:=o) (Ol:=Occ) (Os:=Os') (OO:=merge Occ Os') (I:=I) (t:=t) (t':=t') (S:=(ge, les, m, ir, au)) (o':=on) (tp:=tp) (Mcc:=Mcc) (b:=b) (sc:=snd A) (li:=lasrt) in H0;auto.

  destruct H0 as (Mc'0&Ms'&Oc'0&Os''&OO''&Hndisj&Hnmerge&Hnojoin&Hnoset&H0).
  exists pc A po pi ip.
  exists (TMSpecMod.put (TMSpecMod.put Tm t (minus Mc Mc')) t' (merge Mn Mc'0))
         (TOSpecMod.put (TOSpecMod.put To t Olc) t' (merge On Oc'0))
         ((merge (merge Oc'0 Olc) (minus Ol Oc))) Os''.
  exists Ms' (merge (minus Ml Mc') Mc'0) I lasrt.
  assert (Maps.sub Mc' Mc).
  clear -Hljoin.
  destruct o as [[[[]]]].
  unfold joinmem in Hljoin.
  simpl in Hljoin.
  mytac.
  unfolddef.
  unfold Maps.sub.
  geat.
  assert (Maps.sub Mc Ml).
  eapply part_sub with (T:=Tl) (Tm:=Tm) (t:=t);eauto.

  lets Hsubtrans: sub_trans H19 H21.
  splits;auto.
  splits;auto.
  splits;auto.
  eapply lpstep_goodks;eauto.
  clear -Hgoodiss.
  unfold good_is_S in *.
  intros.
  destruct tst.
  destruct p.
  destruct p.
  destruct p.
  destruct l.
  destruct p.
  assert (projS (ge, les, m, ir, au) t = Some (e, e0, m, i, (i0, i1, c))).
  unfold projS in *.
  unfold projD in *.
  unfolddef.
  destruct (get les t);tryfalse;auto.
  destruct (get au t);tryfalse;auto.
  inverts H;auto.
  apply Hgoodiss in H0.
  auto.
  simpl.

 
  eapply mem_join_merge_minus_join_store' with (Ms:=Ms) (Mc:=Mc') (Mcc:=Mcc) (Mc':=Mc'0) (m':=m');eauto.
 
  eapply partm_task_get_set;eauto.

  apply partm_merge_disj.
  assert (Maps.sub Mc'0 (merge Mc'0 Ms')).

  apply sub_merge_l;auto.
  rewrite Hnmerge in H22.

  erewrite store_sub_minus_eq ;eauto.

  eapply store_sub_disj_disj with (M2:=Mc') (Ms:=Ms) ;eauto.
  clear -Hmjoin.
  simpl in *;unfolds.
  join auto.
  
  unfold TMSpecMod.maps_to.
  unfold TMSpecMod.put.
  destruct TMSpecMod.beq_A;tryfalse.
  unfold TMSpecMod.maps_to in Htmn;auto.
 
  apply partm_minus_sub;auto.

  assert (get Occ curtid = Some (oscurt t)).
  clear -Hgoodi Hswinv.
  unfolds in Hgoodi.
  mytac.
  unfolds in Hswinv.
  lets Hx:Hswinv (spec_done None).
  eapply H0 in Hx.
  mytac.
  auto.
  eapply join_complex;eauto.

  assert (get Occ curtid = Some (oscurt t)).
  clear -Hgoodi Hswinv.
  unfolds in Hgoodi.
  mytac.
  unfolds in Hswinv.
  lets Hx:Hswinv (spec_done None).
  eapply H0 in Hx.
  mytac.
  auto.
  eapply parto_task_get_set;eauto.

  eapply parto_complex;eauto.
  eapply disj_complex with (Occ:=Occ);eauto.

  eapply disj_complex';eauto.
  
  exists (substaskst on m') (substaskst on Ms').
  splits;auto.
  destruct on as [[[[]]]].
  clear -Hprojn.
  unfold projS in *;unfold projD in *.
  unfolddef.
  destruct (get les t');tryfalse.
  destruct (get au t');tryfalse.
  inverts Hprojn.
  simpl;auto.
  apply repl_change_tstm_trans.

  destruct H0;auto.
  
  assert (get Occ curtid = Some (oscurt t)).
  clear -Hgoodi Hswinv.
  unfolds in Hgoodi.
  mytac.
  unfolds in Hswinv.
  lets Hx:Hswinv (spec_done None).
  eapply H0 in Hx.
  mytac.
  auto.
  exists (substaskst on m') ( substaskst on (merge Mn Mc'0)) (merge Mn Mc'0) (merge On Oc'0) Cn' Cn.
  splits;auto.
  clear -Hprojn.
  unfold projS in *;unfold projD in *.
  unfolddef.
  destruct (get les t');tryfalse.
  destruct (get au t');tryfalse.
  inverts Hprojn.
  simpl;auto.
  destruct on as [[[[]]]];simpl;auto.
  rewrite tasks_set_get_neq;auto.
  rewrite tasks_set_get_neq;auto.

  destruct H0.
  eapply switch_linv;eauto.

  destruct ol as [[[[]]]].
  destruct o as [[[[]]]].
  eapply disj_complex'' with (t:=t) (t':=t');eauto.
  unfolds in Hljoin.
  mytac.
  simpl in e4;inverts e4.
  eauto.

  eapply disj_complex''' with (Occ:=Occ);eauto.
  
  assert ( (forall ab : absop, (substaskst on Ms', Os'', ab) |= INV I) /\
           (forall ab : absop, (substaskst on Mc'0, Oc'0, ab) |= RDYINV I t')) as H177;auto.
  destruct H0.

  assert ( (forall ab : absop, (RdyChange (substaskst on Mc'0), Oc'0, ab) |= RDYINV I t') /\ disjoint Mc'0 Mn /\ disjoint Oc'0 On).
  split.
  assert (RdyChange (substaskst on Mc'0)=substaskst on Mc'0).

  eapply rdyinv_isremp with (I:=I) (O:=Oc'0) (M:=Mc'0);eauto.
  rewrite H24;auto.
  split.
  destruct ol as [[[[]]]].
  destruct o as [[[[]]]].
  eapply disj_complex'' with (t:=t);eauto.
  unfolds in Hljoin.
  mytac.
  simpl in e4;inverts e4.
  eauto.
  eapply disj_complex''';eauto.
  assert (exists M'',
            M'' = merge Mc'0 Mn /\
            TaskSim (pc, (po, pi, ip)) Cn' (RdyChange (substaskst on M''))
                    (pc, A) Cn (merge Oc'0 On) lasrt I (InitTaskSt lasrt t') t').
  apply Hcn.
  auto.

  destruct H25 as (M''&Hm''merge&Htsim).
  rewrite Hm''merge in Htsim.
  assert (RdyChange (substaskst on (merge Mc'0 Mn))=substaskst on (merge Mc'0 Mn)).
  eapply rdyinv_isremp with (I:=I) (O:=Oc'0) (M:=Mc'0);eauto.
  rewrite H25 in Htsim.

  destructs H24.
  assert (merge Mc'0 Mn = merge Mn Mc'0).
  rewrite disjoint_merge_sym;auto.
  assert (merge Oc'0 On = (merge On Oc'0)).
  rewrite disjoint_merge_sym;auto.
  rewrite <- H28.
  rewrite <- H29.
  auto.

  splits;auto.
  intros.
  rename H24 into Hdead.
  destruct (tid_eq_dec t'0 t).
  subst t'0.
  assert (get (set Th t (curs (hapi_code sleft), k)) t = Some (curs (hapi_code sleft), k)).
  eapply map_get_set.
  unfold code in *.
  rewrite H23 in H24.
  inverts H24.
  exists (substaskst o m') (minus Mc Mc') (SKIP, (kenil,ks)) Olc.
  splits;auto.
  unfold TMSpecMod.maps_to.
  unfold TMSpecMod.put.
  destruct (TMSpecMod.beq_A t t');tryfalse.
  destruct (TMSpecMod.beq_A t t );tryfalse.
  auto.
  
  unfold TOSpecMod.maps_to.
  unfold TOSpecMod.put.
  destruct (TOSpecMod.beq_A t t');tryfalse.
  destruct (TOSpecMod.beq_A t t );tryfalse.
  auto.
  clear -Hproj.
  destruct o as [[[[]]]].
  unfold projS in *;unfold projD in *.
  unfolddef.
  destruct (get les t);tryfalse.
  destruct (get au t);tryfalse.
  inverts Hproj.
  simpl;auto.

  rewrite repl_change_tstm_trans.

  erewrite joinmem_substaskst_minus;eauto.
  apply map_get_set.

  intros.
  
  destruct H24 as (Hrinv&Hrdisj&Hodisj).
  assert ( forall ab : absop,
             (RdyChange (substaskst o Mr), Or, ab) |= SWINVt I t).
 
  apply swi_rdy_eq_swi with (M:=Mc') (O:=Occ);auto.
  rewrite repl_change_tstm_trans in Hrinv.
  
  assert (RdyChange (substaskst o Mr)=substaskst o Mr).
  apply swinv_isremp in Hswinv.
  clear -Hswinv.
  destruct o as [[[[]]]].
  simpl in *.
  inverts Hswinv;auto.
  rewrite H24 in Hrinv;auto.

  assert (RdyChange (substaskst o Mr)=substaskst (substaskst o Mc) Mr).
  apply swinv_isremp in Hswinv.
  clear -Hswinv.
  destruct o as [[[[]]]].
  simpl in *.
  inverts Hswinv;auto.
  rewrite H25 in *.

  apply H15 with (o':=substaskst o (merge Mr (minus Mc Mc'))) (O'':= merge Or Olc) in H24.
  exists (merge Mr (minus Mc Mc')).
  split;auto.
  assert (RdyChange (substaskst (substaskst o m') (merge Mr (minus Mc Mc'))) = substaskst o (merge Mr (minus Mc Mc'))).
  clear -H25.
  destruct o as [[[[]]]].
  simpl in *.
  inverts H25;auto.
  rewrite H26.
  auto.
  clear -Hrdisj Hljoin.
  unfold joinmem in *.
  destruct o as [[[[]]]].
  mytac.
  simpl in *.
  inverts H0.
  do 6 eexists;splits;eauto.

  apply join_minus in H1.
  unfolddef.
  rewrite H1 in *.
  apply join_comm.
  apply join_merge_disj;auto.
  apply join_comm.
  apply join_merge_disj;auto.

  
  assert (t'0<>t) as Htneq;auto.
  apply Hrsim with (Ch:=Ch0) in n0.
  destruct n0 as (or&Mr'&Clr&Or'&Htmr&Htor&Hprojr&Hlinv''&Htsr&n0).
  exists (substaskst or m') Mr' Clr Or'.
  splits;auto.
  unfold TMSpecMod.maps_to, TMSpecMod.put.
  destruct TMSpecMod.beq_A;tryfalse;auto.
  destruct TMSpecMod.beq_A;tryfalse;auto.
  unfold TOSpecMod.maps_to, TOSpecMod.put.
  destruct TOSpecMod.beq_A;tryfalse;auto.
  destruct TOSpecMod.beq_A;tryfalse;auto.
  
  clear -Hprojr.
  destruct or as [[[[]]]].
  unfold projS in *;unfold projD in *.
  unfolddef.
  destruct (get les t'0);tryfalse;destruct (get au t'0 );tryfalse.
  inverts Hprojr;simpl;auto.
  rewrite repl_change_tstm_trans;auto.
  rewrite tasks_set_get_neq;auto.
  intros.
  assert (substaskst (substaskst or m') Mr= substaskst or Mr).
  apply change_tstm_trans';auto. 
  rewrite H25 in H24.
  eapply n0 in H24;eauto.
  destruct H24.
  exists x2.
  assert (substaskst (substaskst or m') x2= substaskst or x2).
  apply change_tstm_trans';auto. 
  rewrite H26.
  auto.

  rewrite tasks_set_get_neq in H23;auto.
  eapply htstepstar_nodead_still;eauto.
  clear -Hdead.
  unfolds.
  unfolds in Hdead.
  intros.
  apply Hdead.
  rewrite map_get_set' ;auto.
  apply hpstep_eqdomto in Hpstepstar;auto.
  apply join_merge_disj.
  clear -Hhjoin Hhjoin'.
  unfolddef.
  geat.

  clear -H9 Hproj.
  destruct o as [[[[]]]].
  simpl in *.
  unfolddef.
  destruct (get les t);tryfalse.
  destruct (get au t);tryfalse.
  inverts Hproj.
  auto.
  eapply htstepstar_nodead_still;eauto.

  eapply AHprio_local with (O:=x0) in HHHH.

  eapply ahprio_nodead;eauto.
  clear -Hhjoin Hhjoin' H18.
  unfolddef.
  unfolddef.
  join auto.
  Focus 2.
  unfolds;intros.
  rewrite repl_change_tstm_trans.
  mytac.
  rewrite H16 in Hproj;inverts Hproj;auto.
  Focus 2.
  destruct o as [[[[]]]].
  unfold getmem;simpl.
  eapply part_disjm with (M:=Ml) (T:=Tl) (Tm:=Tm) (t:=t);eauto.
  clear -Hmjoin.
  simpl in Hmjoin.
  unfolddef;geat.
  Focus 2.
  apply join_merge_disj.
  eapply part_disjo with (M:=Ol) (T:=Tl) (Tm:=To) (t:=t);eauto.
  clear -HOjoin.
  unfolddef;geat.

  (*-----------switch dead case-----------------*)
  eapply htstepstar_O_local with (Of:= (minus Ol Oc)) (OO:=O) (cst:=cst') in Hhtstep.

  Focus 2.
  eapply join_merge_minus;eauto.
  eapply parto_sub;eauto.
  
  mytac.
  
  rewrite repl_change_tstm_trans in *.
  exists (set Th t (curs (hapi_code sleft), k)) (set x0 curtid (oscurt t')).
  (*HHHH*)
  assert (  hpstep (pc, A) (set Th t (curs (hapi_code (sched;; sleft)), k)) cst' x0
                   (TasksMod.set Th t (curs (hapi_code sleft), k)) cst' (set x0 curtid (oscurt t')) /\  forall ab, (tst, x0 , ab) |= AHprio (snd A) t' ** Atrue).

  eapply sw_same_t with (l:=l) (tp:=tp) (x:=x) (tst:=tst) (t':=t');eauto.
  unfolds in Hgoodi.
  mytac;simpl;auto.

  apply htstepstar_tidsame in H16.
  unfolds in H16.
  rewrite <- H16.
  auto.
  rewrite H2 in Hproj;inverts Hproj.
  rewrite H17 in H2;inverts H2.
  simpl snd.
  
  unfold getsched in H15.
  simpl snd in H15.
  unfold satp in *.
  
  unfold SWPRE_DEAD in H15.
  assert (forall aop,  (substaskst o Mc', Occ, aop)
        |= SWPRE (snd A) x t).
  intros.
  lets Hx:H15 aop.
  destruct Hx;auto.
  eapply swpre_prop with (M:=Mc');eauto.
  
  apply projs_eqm in H17.
  destruct o as [[[[]]]].
  simpl in H17.
  simpl.
  subst m0.

  eapply part_sub with (Mc:=Mc) in Hmpart;eauto.
  eapply sub_join_sub;eauto.
  clear -Hmpart Hljoin.
  unfold joinmem in *.
  mytac.
  simpl in H0;inverts H0.
  unfold Maps.sub in *.
  destruct Hmpart.
  unfold TMSpecMod.B in *.
  unfold mmapspec.image in *.
  join auto.
  clear -Hhjoin' Hhjoin H18.
  unfolds Maps.sub.
  unfold TOSpecMod.B in *.
  unfold omapspec.image in *.
  geat.
  
  assert (hpstepstar (pc, A) Th cst' O
                     (set Th t (curs (hapi_code sleft), k)) cst' (set x0 curtid (oscurt t')) ) as Hpstepstar.
  
  assert (hpstepstar (pc, A) Th cst' O 
                     (set Th t (curs (hapi_code sleft), k)) cst' (set x0 curtid (oscurt t')) ) as Hhpstep.

  assert (hpstepstar (pc, A) Th cst' O
                     (set Th t (curs (hapi_code  (sched;; sleft)), k)) cst' x0).
  apply th_no_create_lift with (C:=Ch);auto.
  eapply hpstep_star with (T':=(set Th t (curs (hapi_code  (sched;; sleft)), k))) (cst':=cst') (O':=x0);eauto. 

  destruct H0;auto.
  auto.

  rename H0 into HHHH.
  destruct HHHH as (Hxx&HHHH).
  clear Hxx.
  assert (forall aop,  (substaskst o Mc', Occ, aop)
                         |= SWPRE (snd A) x t).
  intros.
  lets Hx:H15 aop.
  destruct Hx;auto.
  
  assert (forall ab,(substaskst o Mc', Occ, ab) |= AHprio (snd A) t' ** Atrue).
  eapply lemma_trans_temp;eauto.
  unfolds in Hgoodi;destructs Hgoodi;auto.
  clear -Hhjoin' Hhjoin H18.
  unfolds Maps.sub.
  unfold TOSpecMod.B in *.
  unfold omapspec.image in *.
  geat.
  clear HHHH.
  rename H0 into HHHH.
  split;auto.
  apply CIH.
  eapply map_get_set.
  destruct (tid_eq_dec t t').
  (* cur == high rdy -> false *)
  subst t'.
  false.
  eapply swdead_ahprio_false;eauto.
  unfolds in Hgoodi;mytac;auto.
  (* cur <> high rdy *)
  
  assert (exists C, TasksMod.get (TasksMod.set Th t (curs (hapi_code sleft), k)) t' = Some C).
 
  eapply sw_has_code with (l:=l) (tp:=(Tptr tp)) (x:=x) (tst:=tst) (O:=x0) (sd:=snd A);auto.
  unfolds in Hgoodi;destructs Hgoodi;auto.
  assert (o=tst).
  rewrite H2 in Hproj.
  inversion Hproj;tryfalse;auto.
  subst tst.
  eapply swpre_prop with (M:=Mc');eauto.
  
  assert (Maps.sub Mc Ml).
  apply part_sub with (T:=Tl) (Tm:=Tm) (t:=t);auto.
  clear -Hljoin H0 Hmjoin H2.
  destruct o as [[[[]]]].
  simpl in *.
  unfolddef.
  destruct (get les t);tryfalse.
  destruct (get au t);tryfalse.
  inverts H2.
  unfolds in Hljoin.
  mytac.
  geat.
  clear -Hhjoin Hhjoin' H18.
  unfolddef.
  geat.
  apply hpstep_eqdomto in Hpstepstar;auto.
  unfold eqdomTO in *.
  clear -Hpstepstar.
  mytac.
  eexists;split;eauto.
 
  rewrite abst_set_get_neq in H;auto.
 

  destruct H0 as (Cn&Hcn).
  rewrite tasks_set_get_neq in Hcn;auto.
  assert (TasksMod.get Th t' = Some Cn) as Hcode;auto.
  apply Hrsim in Hcn;auto.
  destruct Hcn as (on&Mn&Cn'&On&Htmn&Hton&Hprojn&Hlinvn&Htasksn&Hcn).
  assert (disjoint Mc' Ms).
  clear -Hljoin Hmjoin Hmpart Htm.
  destruct o.
  destruct p.
  destruct p.
  destruct p.
  simpl in *.
  unfold joinmem in *.
  mytac.
  assert (disjoint x2 Ms). 
  apply part_disjm with (M:=Ml) (T:=Tl) (Tm:=Tm) (t:=t);auto.
  unfolddef.
  clear -Hmjoin.
  geat.
  clear -H1 H.
  unfolddef.
  geat.
  

  assert (exists Mcc,store (Tptr tp) Mc' (b,0%Z) (Vptr t') = Some Mcc).
  rename HHHH into Hswpre.
  destruct o as [[[[]]]];unfold substaskst in Hswpre.
  assert ((e, e0, Mc', i, l0, Occ, (spec_done None)) |= SWPRE (snd A) x t);auto.
  eapply swpre_store with (ab:=spec_done None);eauto.
  clear -Hproj H9.
  simpl in Hproj.
  unfolddef.
  destruct (get les t);tryfalse.
  destruct (get au t);tryfalse.
  inverts Hproj.
  unfold get in H9;simpl in H9;auto.
  destruct H21 as (Mcc&Hmcc).
  

  lets Hx:aux_atrue Hlinv'.
  destruct Hx as (o1&M2&O1&O2&Hjoinf&Hjoinof&Hlinvf).

  eapply swi_rdy_inv_dead with (o:=o) (Ol:=Occ) (Os:=Os') (OO:=merge O' Os') (I:=I) (t:=t) (t':=t') (S:=(ge, les, m, ir, au)) (Ms:=Ms) (o':=on) (tp:=tp) (Mcc:=Mcc) (b:=b) (sc:=snd A) (o1:=o1) (M2:=M2) (O1:=O1) (O2:=O2) (li:=lasrt)in H0;eauto.
       
  destruct H0 as (Mc'0&Ms'&Oc'0&Os''&OO''&Olx'&Hndisj&Hnmerge&Hnojoin&Hnojoinx&Hnoset&H0).
  exists pc A po pi ip.
  exists (TMSpecMod.put (TMSpecMod.put Tm t M2) t' (merge Mn Mc'0))
         (TOSpecMod.put (TOSpecMod.put To t O2) t' (merge On Oc'0))
         ((merge (merge Oc'0 O2) (minus Ol Oc))) Os''.
  exists Ms' (merge (merge (minus Ml Mc) M2) Mc'0) I lasrt.
  assert (Maps.sub Mc' Mc).
  clear -Hljoin.
  destruct o as [[[[]]]].
  unfold joinmem in Hljoin.
  simpl in Hljoin.
  mytac.
  unfolddef.
  unfold Maps.sub.
  geat.
  assert (Maps.sub Mc Ml).
  eapply part_sub with (T:=Tl) (Tm:=Tm) (t:=t);eauto.
  
  lets Hsubtrans: sub_trans H21 H22.
  splits;auto.
  splits;auto.
  splits;auto.
  eapply lpstep_goodks;eauto.
  clear -Hgoodiss.
  unfold good_is_S in *.
  intros.
  destruct tst.
  destruct p.
  destruct p.
  destruct p.
  destruct l.
  destruct p.
  assert (projS (ge, les, m, ir, au) t = Some (e, e0, m, i, (i0, i1, c))).
  unfold projS in *.
  unfold projD in *.
  unfolddef.
  destruct (get les t);tryfalse;auto.
  destruct (get au t);tryfalse;auto.
  inverts H;auto.
  apply Hgoodiss in H0.
  auto.
  simpl.

  eapply mem_join_merge_minus_join_store'f with (Ms:=Ms) (Mc:=Mc) (Mcc:=Mcc) (Mc'0:=Mc'0) (m':=m');eauto.
  eapply partm_task_get_set;eauto.
  apply partm_merge_disj.

  eapply disj'f;eauto.
  (*
  assert (Maps.sub Mc'0 (merge Mc'0 Ms')).
  apply sub_merge_l;auto.
  rewrite Hnmerge in H23.
(* ** ac:   Check  store_sub_minus_eq. *)
  erewrite store_sub_minus_eq ;eauto.

  eapply store_sub_disj_disj with (M2:=Mc') (Ms:=Ms) ;eauto.
  clear -Hmjoin.
  simpl in *;unfolds.
  join auto.
  *)
  unfold TMSpecMod.maps_to.
  unfold TMSpecMod.put.
  destruct TMSpecMod.beq_A;tryfalse.
  unfold TMSpecMod.maps_to in Htmn;auto.
  apply partm_minus_subf;auto.
  clear - Hjoinf Hljoin.
  destruct ol as [[[[]]]].
  destruct o as [[[[]]]].
  simpl in *.
  unfold joinmem in *.
  mytac.
  unfolds.
  join auto.
  
  assert (get Occ curtid = Some (oscurt t)).
  clear -Hgoodi Hswinv.
  unfolds in Hgoodi.
  mytac.
  unfolds in Hswinv.
  lets Hx:Hswinv (spec_done None).
  eapply H0 in Hx.
  mytac.
  auto.
  

  eapply join_complexf with (OO'0:=OO') (O'0:=O');eauto.

  assert (get Occ curtid = Some (oscurt t)).
  clear -Hgoodi Hswinv.
  unfolds in Hgoodi.
  mytac.
  unfolds in Hswinv.
  lets Hx:Hswinv (spec_done None).
  eapply H0 in Hx.
  mytac.
  auto.
  eapply parto_task_get_set;eauto.
  eapply parto_complex;eauto.
  unfolds;eauto.
  eapply disj_complex'f with (O1:=O1) (O2:=O2) (Olx':=Olx') ;eauto.
  
  exists (substaskst on m') (substaskst on Ms').
  splits;auto.
  destruct on as [[[[]]]].
  clear -Hprojn.
  unfold projS in *;unfold projD in *.
  unfolddef.
  destruct (get les t');tryfalse.
  destruct (get au t');tryfalse.
  inverts Hprojn.
  simpl;auto.
  apply repl_change_tstm_trans.

  destruct H0;auto.
  
  assert (get Occ curtid = Some (oscurt t)).
  clear -Hgoodi Hswinv.
  unfolds in Hgoodi.
  mytac.
  unfolds in Hswinv.
  lets Hx:Hswinv (spec_done None).
  eapply H0 in Hx.
  mytac.
  auto.
  exists (substaskst on m') ( substaskst on (merge Mn Mc'0)) (merge Mn Mc'0) (merge On Oc'0) Cn' Cn.
  splits;auto.
  clear -Hprojn.
  unfold projS in *;unfold projD in *.
  unfolddef.
  destruct (get les t');tryfalse.
  destruct (get au t');tryfalse.
  inverts Hprojn.
  simpl;auto.
  destruct on as [[[[]]]];simpl;auto.
  rewrite tasks_set_get_neq;auto.
  rewrite tasks_set_get_neq;auto.
  destruct H0.
  eapply switch_linv;eauto.
  destruct ol as [[[[]]]].
  destruct o as [[[[]]]].
  eapply disj_complex''f with (t:=t) (t':=t');eauto.
  instantiate (1:=m0).
  clear -Hjoinf.
  unfolds in Hjoinf;mytac.
  unfold getmem.
  simpl.
  unfolds;eauto.
  unfolds in Hljoin.
  mytac.
  simpl in H26;inverts H26.
  eauto.
  eapply disj_complex'''f with (O1:=O1) (O2:=O2) (Occ:=Occ) (Olx':=Olx');eauto.
  
  assert ( (forall ab : absop, (substaskst on Ms', Os'', ab) |= INV I) /\
           (forall ab : absop, (substaskst on Mc'0, Oc'0, ab) |= RDYINV I t')) as H177;auto.
  destruct H0.

  assert ( (forall ab : absop, (RdyChange (substaskst on Mc'0), Oc'0, ab) |= RDYINV I t') /\ disjoint Mc'0 Mn /\ disjoint Oc'0 On).
  split.
  assert (RdyChange (substaskst on Mc'0)=substaskst on Mc'0).
  eapply rdyinv_isremp with (I:=I) (O:=Oc'0) (M:=Mc'0);eauto.
  rewrite H25;auto.
  split.
  destruct ol as [[[[]]]].
  destruct o as [[[[]]]].
  eapply disj_complex''f with (t:=t);eauto.
  instantiate (1:=m0).
  clear -Hjoinf.
  unfolds in Hjoinf;mytac.
  unfold getmem.
  simpl.
  unfolds;eauto.
  unfolds in Hljoin.
  mytac.
  simpl in H28;inverts H28.
  eauto.
  eapply disj_complex'''f;eauto.
  assert (exists M'',
            M'' = merge Mc'0 Mn /\
            TaskSim (pc, (po, pi, ip)) Cn' (RdyChange (substaskst on M''))
                    (pc, A) Cn (merge Oc'0 On) lasrt I (InitTaskSt lasrt t') t').
  apply Hcn.
  auto.

  destruct H26 as (M''&Hm''merge&Htsim).
  rewrite Hm''merge in Htsim.
  assert (RdyChange (substaskst on (merge Mc'0 Mn))=substaskst on (merge Mc'0 Mn)).
  eapply rdyinv_isremp with (I:=I) (O:=Oc'0) (M:=Mc'0);eauto.
  rewrite H26 in Htsim.

  destructs H25.
  assert (merge Mc'0 Mn = merge Mn Mc'0).
  rewrite disjoint_merge_sym;auto.
  assert (merge Oc'0 On = (merge On Oc'0)).
  rewrite disjoint_merge_sym;auto.
  rewrite <- H29.
  rewrite <- H30.
  auto.

  splits;auto.
  intros.
  rename H25 into Hdead.
  destruct (tid_eq_dec t'0 t).
  
  subst t'0.
  assert (task_no_dead x0 t).
  clear -Hdead.
  unfolds.
  unfolds in Hdead.
  intros.
  apply Hdead.
  rewrite map_get_set';auto.

  false.
  eapply nodead_swpredead_false;eauto.
  clear -Hhjoin Hhjoin' H18.
  unfolddef.
  unfolddef.
  join auto.

  assert (t'0<>t) as Htneq;auto.
  apply Hrsim with (Ch:=Ch0) in n0.
  destruct n0 as (or&Mr'&Clr&Or'&Htmr&Htor&Hprojr&Hlinv''&Htsr&n0).
  exists (substaskst or m') Mr' Clr Or'.
  splits;auto.
  unfold TMSpecMod.maps_to, TMSpecMod.put.
  destruct TMSpecMod.beq_A;tryfalse;auto.
  destruct TMSpecMod.beq_A;tryfalse;auto.
  unfold TOSpecMod.maps_to, TOSpecMod.put.
  destruct TOSpecMod.beq_A;tryfalse;auto.
  destruct TOSpecMod.beq_A;tryfalse;auto.
  
  clear -Hprojr.
  destruct or as [[[[]]]].
  unfold projS in *;unfold projD in *.
  unfolddef.
  destruct (get les t'0);tryfalse;destruct (get au t'0 );tryfalse.
  inverts Hprojr;simpl;auto.
  rewrite repl_change_tstm_trans;auto.
  rewrite tasks_set_get_neq;auto.
  intros.
  assert (substaskst (substaskst or m') Mr= substaskst or Mr).
  apply change_tstm_trans';auto. 
  rewrite H26 in H25.
  eapply n0 in H25;eauto.
  destruct H25.
  exists x2.
  assert (substaskst (substaskst or m') x2= substaskst or x2).
  apply change_tstm_trans';auto. 
  rewrite H27.
  auto.

  rewrite tasks_set_get_neq in H24;auto.
  eapply htstepstar_nodead_still;eauto.
  clear -Hdead.
  unfolds.
  unfolds in Hdead.
  intros.
  apply Hdead.
  rewrite map_get_set';auto.
  apply hpstep_eqdomto in Hpstepstar;auto.
  apply join_merge_disj.
  clear -Hhjoin Hhjoin'.
  unfolddef.
  geat.

  apply disj_sym.
  eapply part_disjm;eauto.
  unfolds;eauto.
  clear -H9 Hproj.
  destruct o as [[[[]]]].
  simpl in *.
  unfolddef.
  destruct (get les t);tryfalse.
  destruct (get au t);tryfalse.
  inverts Hproj.
  auto.
  eapply htstepstar_nodead_still;eauto.
  eapply AHprio_local with (O:=x0) in H19.
  eapply ahprio_nodead;eauto.
  clear -Hhjoin Hhjoin' H18.
  unfolddef.
  unfolddef.
  join auto.
  
  (*-----------------------------switch case end-------------------------------*)

  (*-----------------------------stkinit step--------------------------------------*)
  subst t'.
  subst.
  inversion H0;subst pc0 po0 pi0 ip0;clear H0.
  destruct Hcsim as (o&o'&Mc&Oc&Cl&Ch&Htm&Hto&Hproj&Hsubst&Htgeth&Htgetl&Hlinv&Hcsim).
  unfolddef.
  rewrite Htgetl in H1;inverts H1.
  inverts Hcsim.
  assert ( (curs (sprim (stkinit e1 e2 e3)), (kenil, ks)) =  (curs (sprim (stkinit e1 e2 e3)), (kenil, ks))) by auto.
  destruct o as [[[[]]]].
  rewrite Hproj in H13;inverts H13.
  simpl in Hsubst.
  subst o'.
  simpl substaskst in *.
  destruct Hinv as (o1&o1'&Hproj1&Hsubsub&Hinv).
  rewrite Hproj in Hproj1.
  inverts Hproj1.
  simpl in Hsubsub.
  subst o1'.
  eapply H12 with (Ms:=Ms) (Os:=Os) (OO:=merge Oc Os)in H15;eauto.
  Focus 2.
  unfold getmem;simpl.
  eapply part_disjm with (M:=Ml) (T:=Tl) (Tm:=Tm) (t:=t);eauto.
  clear -Hmjoin.
  simpl in Hmjoin.
  unfolddef;geat.
  Focus 2.
  apply join_merge_disj.
  eapply part_disjo with (M:=Ol) (T:=Tl) (Tm:=To) (t:=t);eauto.
  clear -HOjoin.
  unfolddef;geat.
  destruct H15 as (Ch'&v11&v12&t'&p&sh&k&OO'&OO''&ol&Mcre&O'&Os'&Olc&Ocre&H15).
  mytac.
  subst.
  destruct Sl as [[[[]]]].
  simpl in Hproj.
  unfolddef.
  remember (get c t) as getle.
  destruct getle;tryfalse.
  remember (get l t) as getaux.
  destruct getaux;tryfalse.
  simpl get_smem in *.
  simpl snd in *.
  simpl fst in *.
  inverts Hproj.
  assert (Maps.sub Mc Ml).
  eapply part_sub;eauto.
  assert (Maps.sub Mc m).
  eapply sub_trans;eauto.
  clear -Hmjoin.
  unfolds.
  geat.
  unfolds in H27.
  destruct H27.
  simpl in H15.
  lets Hx:evalval_mono H27 H15.
  rewrite Hx in *.
  rewrite H15 in H5;inverts H5.
  clear Hx.
  simpl in H16.
  lets Hx:evalval_mono H27 H16.
  rewrite Hx in *.
  rewrite H16 in H6;inverts H6.
  clear Hx.
  simpl in H17.
  lets Hx:evalval_mono H27 H17.
  rewrite Hx in *.
  rewrite H17 in H7;inverts H7.
  clear Hx.
  eapply htstepstar_O_local with (Of:= (minus Ol Oc)) (OO:=O) (cst:=(ge, cenvs, M)) in H18.
  destruct H18.
  destruct H5 as (Hhtstepstar&Hjoin').
  assert (htstepstar (pc, A) t Ch (ge, cenvs, M) O
                  (curs (hapi_code (spec_crt v1 v (Vint32 p);; sh)), k)
                  (ge, cenvs, M) x0) as Htstepstar;auto.
  eapply th_no_create_lift in Hhtstepstar;eauto.
  destruct k as (keh,ksh).
  inverts H19.
  mytac.
  assert (hpstepstar  (pc, A) Th (ge, cenvs, M) O (set (set Th t
                     (curs (hapi_code  sh), (keh,ksh))) t'0 (nilcont s)) (ge, set cenvs t'0 le, M') (merge (set OO' abtcblsid (abstcblist x2)) (minus Ol Oc)) ).

  eapply hpstep_star;eauto.
  assert ((set Th t (curs (hapi_code sh), (keh,ksh))) = set (set Th t (curs (hapi_code (spec_crt v1 v (Vint32 p);; sh)), (keh,ksh))) t (curs (hapi_code sh), (keh,ksh))).

  apply set_set_eq.
  rewrite H19.
  eapply hpcrt_step;eauto.
  apply map_get_set.
  eapply join_get_get_l;eauto.
  eapply join_get_get_l;eauto.
  assert (x0 = merge OO' (minus Ol Oc)).
  apply map_join_merge';auto.
  symmetry.
  subst x0.
  eapply join_merge_set_eq;eauto.
  clear -H18.
  unfold joinsig in *.
  join auto.
  do 2 eexists;split;eauto.

  assert (merge (set OO' abtcblsid (abstcblist x2)) (minus Ol Oc) = set x0 abtcblsid (abstcblist x2)).
  assert (x0 = merge OO' (minus Ol Oc)).
  apply map_join_merge';auto.
  subst x0.
  eapply join_merge_set_eq;eauto.

  rewrite H28 in *.
  apply CIH;auto.
  rewrite <-Hosabsttid.
  apply htstepstar_tidsame in Htstepstar.
  unfold tidsame in Htstepstar.
  unfolddef.
  rewrite Htstepstar.
  apply map_get_set';auto.

  destruct ol as [[[[]]]].
  unfolds in H20.
  do 6 destruct H20.
  destructs H20.
  inversion H29;subst x3 x4 x6 x7 x8;clear H29.
  inversion H20;subst e4 e5 x5 i l0;clear H20.
  rename m0 into Mlc.
  exists pc A po pi ip.
  rename t'0 into t'.
  exists (TMSpecMod.put (TMSpecMod.put Tm t Mlc) t' Mcre)
         (TOSpecMod.put (TOSpecMod.put To t Olc) t' Ocre)
         ((merge O' (minus Ol Oc))) Os'.
  exists Ms Ml I lasrt.
  splits;auto.
  splits;auto.
  splits;auto.
  
  eapply lpstep_goodks;eauto.
  clear -Hgoodiss.
  unfold good_is_S in *.
  unfold Snewt.
  unfold Dnewt.
  unfold Tlnewt.
  simpl.
  intros.
  destruct tst.
  destruct p.
  destruct p.
  destruct p.
  destruct l0.
  destruct p.
  assert (t =t' \/ t <> t') by tauto.
  destruct H0.
  subst t'.
  unfolddef.
  rewrite map_get_set in H.
  rewrite map_get_set in H.
  inverts H.
  simpl;auto.
  rewrite map_get_set' in H;auto.
  rewrite map_get_set' in H;auto.
  
  assert (projS (e, c, m, ir, l) t = Some (e0, e1, m, i, (i0, i1, c0))).
  unfold projS in *.
  unfold projD in *.
  unfolddef.
  destruct (get c t);tryfalse;auto.
  destruct (get l t);tryfalse;auto.
  inverts H;auto.
  apply Hgoodiss in H1.
  auto.


  eapply crt_partm;eauto.

  eapply join_crt;eauto.

  eapply crt_parto;eauto.
  exists (e,e0,m,ir,au) (e,e0,Ms,ir,au).
  splits;simpl;auto.
  unfolddef.
  rewrite map_get_set';auto.
  rewrite <- Heqgetle.
  unfold Tlnewt.
  rewrite map_get_set';auto.
  rewrite <- Heqgetaux.
  auto.

  (*------------current task------------------*)
  exists (e,e0,m,ir,au) (e,e0,Mlc,ir,au) Mlc Olc  (SKIP , (kenil, ks)) (curs (hapi_code sh), (keh, ksh)).
  splits;simpl;auto.
  eapply TMSpecMod.mapsto_mapsto_put;eauto.
  eapply TOSpecMod.mapsto_mapsto_put;eauto.
  unfolddef.
  rewrite map_get_set';auto.
  rewrite <- Heqgetle.
  unfold Tlnewt.
  rewrite map_get_set';auto.
  rewrite <- Heqgetaux.
  auto.
  rewrite map_get_set';auto.
  apply map_get_set.
  rewrite map_get_set';auto.
  apply map_get_set.

  splits;auto.
  intros.
  assert (t'0 = t' \/ t'0 <> t') by tauto.
  (* ---------- new task ---------------*)
  destruct H32.
  subst t'0.
  unfold Snewt.
  unfold Dnewt, Tlnewt.
  exists (e,(empenv:env),m,ir,(true,(nil:is),(nil:cs))) Mcre (nilcont s) Ocre.
  splits;auto.
  simpl.
  rewrite map_get_set.
  rewrite map_get_set.
  auto.


  simpl substaskst.
  eapply linv_change_linv_aux with (e':=empenv) (aux':=(true,nil,nil)) (ir':=ir) in H25;eauto.
  clear -H25.
  unfold LINV.
  exists init_lg.
  unfolds in H25.
  lets Hx:H25 aop.
  sep auto.
  apply map_get_set.

  intros.
  eexists;split;eauto.
  simpl RdyChange.
  rewrite map_get_set in H29;inverts H29.
  eapply SmCTaskSim;eauto.
  unfolds.
  simpl.
  destructs H32.
  simpl RdyChange in H29.

  split;auto.
  eapply crt_init;eauto.
  eapply linv_change_linv_aux;eauto.
  eexists;splits;eauto.
  simpl;auto.
  clear -Hgoodpc H9.
  unfolds in  Hgoodpc.
  mytac.
  eapply H;eauto.

  (*-----------other tasks-------------*)
  rewrite map_get_set' in H29;auto.
  rewrite map_get_set' in H29;auto.
  assert (t'0<>t) by auto.
  eapply Hrsim in H20;eauto.
  mytac.
  exists x3 x4 x5 x6.
  splits;auto.
  eapply TMSpecMod.mapsto_mapsto_put;eauto.
  eapply TMSpecMod.mapsto_mapsto_put;eauto.
  eapply TOSpecMod.mapsto_mapsto_put;eauto.
  eapply TOSpecMod.mapsto_mapsto_put;eauto.
  unfold Snewt.
  unfold Dnewt,Tlnewt;simpl.
  unfolddef.
  rewrite map_get_set';auto.
  rewrite map_get_set';auto.
  rewrite map_get_set';auto.
  rewrite map_get_set';auto.
  eapply htstepstar_nodead_still;eauto.
  
  
  clear -H32 H31 H18 H7 Hjoin'.
  assert (get x0 abtcblsid = Some (abstcblist x1)).
  eapply join_get_l;eauto.
  unfold task_no_dead in *.
  intros.
  rewrite H in H0;inverts H0.
  eapply joinsig_indom_neq;eauto.  
  apply H31.
  rewrite map_get_set;auto.

  apply hpstep_eqdomto in H19;auto.
  eapply join_merge_minus;eauto.
  eapply parto_sub;eauto.

  (*-----------------------------stkinit skip step--------------------------------------------*)
  subst t'.
  subst.
  inversion H0;subst pc0 po0 pi0 ip0;clear H0.
  destruct Hcsim as (o&o'&Mc&Oc&Cl&Ch&Htm&Hto&Hproj&Hsubst&Htgeth&Htgetl&Hlinv&Hcsim).
  unfolddef.
  rewrite Htgetl in H1;inverts H1.
  inverts Hcsim.
  assert ( (curs (sprim (stkinit e1 e2 e3)), (kenil, ks)) =  (curs (sprim (stkinit e1 e2 e3)), (kenil, ks))) by auto.
  destruct o as [[[[]]]].
  rewrite Hproj in H12;inverts H12.
  simpl in Hsubst.
  subst o'.
  simpl substaskst in *.
  destruct Hinv as (o1&o1'&Hproj1&Hsubsub&Hinv).
  rewrite Hproj in Hproj1.
  inverts Hproj1.
  simpl in Hsubsub.
  subst o1'.
  eapply H11 with (Ms:=Ms) (Os:=Os) (OO:=merge Oc Os)in H14;eauto.
  Focus 2.
  unfold getmem;simpl.
  eapply part_disjm with (M:=Ml) (T:=Tl) (Tm:=Tm) (t:=t);eauto.
  clear -Hmjoin.
  simpl in Hmjoin.
  unfolddef;geat.
  Focus 2.
  apply join_merge_disj.
  eapply part_disjo with (M:=Ol) (T:=Tl) (Tm:=To) (t:=t);eauto.
  clear -HOjoin.
  unfolddef;geat.
  destruct H14 as (Ch'&v11&v12&t'&p&sh&k&OO'&OO''&ol&Mcre&O'&Os'&Olc&Ocre&H14).
  mytac.
  subst.
  destruct Sl as [[[[]]]].
  simpl in Hproj.
  unfolddef.
  remember (get c t) as getle.
  destruct getle;tryfalse.
  remember (get l t) as getaux.
  destruct getaux;tryfalse.
  simpl get_smem in *.
  simpl snd in *.
  simpl fst in *.
  inverts Hproj.
  assert (Maps.sub Mc Ml).
  eapply part_sub;eauto.
  assert (Maps.sub Mc m).
  eapply sub_trans;eauto.
  clear -Hmjoin.
  unfolds.
  geat.

  unfolds in H26.
  destruct H26.
  simpl in H14.
  lets Hx:evalval_mono H26 H14.
  rewrite Hx in *.
  rewrite H14 in H5;inverts H5.
  clear Hx.
  simpl in H15.
  lets Hx:evalval_mono H26 H15.
  rewrite Hx in *.
  rewrite H15 in H6;inverts H6.
  clear Hx.
  simpl in H16.
  lets Hx:evalval_mono H26 H16.
  rewrite Hx in *.
  rewrite H16 in H7;inverts H7.
  clear Hx.
  eapply htstepstar_O_local with (Of:= (minus Ol Oc)) (OO:=O) (cst:=(ge, cenvs, M)) in H17.
  destruct H17.
  destruct H5 as (Hhtstepstar&Hjoin').
  assert (htstepstar (pc, A) t Ch (ge, cenvs, M) O
                  (curs (hapi_code (spec_crt v1 v (Vint32 p);; sh)), k)
                  (ge, cenvs, M) x0) as Htstepstar;auto.
  eapply th_no_create_lift in Hhtstepstar;eauto.
  destruct k as (keh,ksh).
  inverts H18.
  mytac.

  assert (hpstepstar  (pc, A) Th (ge, cenvs, M) O (set (set Th t
                     (curs (hapi_code  sh), (keh,ksh))) t'0 (nilcont (sskip None))) (ge, cenvs, M) (merge (set OO' abtcblsid (abstcblist x2)) (minus Ol Oc)) ).

  eapply hpstep_star;eauto.
  assert ((set Th t (curs (hapi_code sh), (keh,ksh))) = set (set Th t (curs (hapi_code (spec_crt v1 v (Vint32 p);; sh)), (keh,ksh))) t (curs (hapi_code sh), (keh,ksh))).
  apply set_set_eq.
  rewrite H18.
  eapply hpcrtskip_step;eauto.
  apply map_get_set.
  eapply join_get_get_l;eauto.
  eapply join_get_get_l;eauto.
  assert (x0 = merge OO' (minus Ol Oc)).
  apply map_join_merge';auto.
  symmetry.
  subst x0.
  eapply join_merge_set_eq;eauto.
  clear -H17.
  unfold joinsig in *.
  join auto.
  do 2 eexists;split;eauto.

  assert (merge (set OO' abtcblsid (abstcblist x2)) (minus Ol Oc) = set x0 abtcblsid (abstcblist x2)).
  assert (x0 = merge OO' (minus Ol Oc)).
  apply map_join_merge';auto.
  subst x0.
  eapply join_merge_set_eq;eauto.

  rewrite H27 in *.
  apply CIH;auto.
  rewrite <-Hosabsttid.
  apply htstepstar_tidsame in Htstepstar.
  unfold tidsame in Htstepstar.
  unfolddef.
  rewrite Htstepstar.
  apply map_get_set';auto.

  destruct ol as [[[[]]]].
  unfolds in H19.
  do 6 destruct H19.
  destructs H19.
  inversion H28;subst x3 x4 x6 x7 x8;clear H28.
  inversion H19;subst e4 e5 x5 i l0;clear H19.
  rename m0 into Mlc.
  exists pc A po pi ip.
  rename t'0 into t'.
  exists (TMSpecMod.put (TMSpecMod.put Tm t Mlc) t' Mcre)
         (TOSpecMod.put (TOSpecMod.put To t Olc) t' Ocre)
         ((merge O' (minus Ol Oc))) Os'.
  exists Ms Ml I lasrt.
  splits;auto.
  splits;auto.
  splits;auto.
  
  eapply lpstep_goodks;eauto.
  clear -Hgoodiss.
  unfold good_is_S in *.
  unfold Snewt.
  unfold Dnewt.
  unfold Tlnewt.
  simpl.
  intros.
  destruct tst.
  destruct p.
  destruct p.
  destruct p.
  destruct l0.
  destruct p.
  assert (t =t' \/ t <> t') by tauto.
  destruct H0.
  subst t'.
  unfolddef.
  rewrite map_get_set in H.
  rewrite map_get_set in H.
  inverts H.
  simpl;auto.
  rewrite map_get_set' in H;auto.
  rewrite map_get_set' in H;auto.
  
  assert (projS (e, c, m, ir, l) t = Some (e0, e1, m, i, (i0, i1, c0))).
  unfold projS in *.
  unfold projD in *.
  unfolddef.
  destruct (get c t);tryfalse;auto.
  destruct (get l t);tryfalse;auto.
  inverts H;auto.
  apply Hgoodiss in H1.
  auto.
  eapply crt_partm;eauto.
  eapply join_crt;eauto.
  eapply crt_parto;eauto.
  exists (e,e0,m,ir,au) (e,e0,Ms,ir,au).
  splits;simpl;auto.
  unfolddef.
  rewrite map_get_set';auto.
  rewrite <- Heqgetle.
  unfold Tlnewt.
  rewrite map_get_set';auto.
  rewrite <- Heqgetaux.
  auto.

  (*------------current task------------------*)
  exists (e,e0,m,ir,au) (e,e0,Mlc,ir,au) Mlc Olc  (SKIP , (kenil, ks)) (curs (hapi_code sh), (keh, ksh)).
  splits;simpl;auto.
  eapply TMSpecMod.mapsto_mapsto_put;eauto.
  eapply TOSpecMod.mapsto_mapsto_put;eauto.
  unfolddef.
  rewrite map_get_set';auto.
  rewrite <- Heqgetle.
  unfold Tlnewt.
  rewrite map_get_set';auto.
  rewrite <- Heqgetaux.
  auto.
  rewrite map_get_set';auto.
  apply map_get_set.
  rewrite map_get_set';auto.
  apply map_get_set.

  splits;auto.
  intros.
  assert (t'0 = t' \/ t'0 <> t') by tauto.
  (* ---------- new task ---------------*)
  destruct H31.
  subst t'0.
  unfold Snewt.
  unfold Dnewt, Tlnewt.
  exists (e,(empenv:env),m,ir,(true,(nil:is),(nil:cs))) Mcre (nilcont (sskip None)) Ocre.
  splits;auto.
  simpl.
  rewrite map_get_set.
  rewrite map_get_set.
  auto.
  simpl substaskst.
  eapply linv_change_linv_aux with (e':=empenv) (aux':=(true,nil,nil)) (ir':=ir) in H24;eauto.
  clear -H24.
  unfold LINV.
  exists init_lg.
  unfolds in H24.
  lets Hx:H24 aop.
  sep auto.
  apply map_get_set.

  intros.
  eexists;split;eauto.
  simpl RdyChange.
  rewrite map_get_set in H28;inverts H28.
  eapply SmCTaskSim;eauto.
  unfolds.
  simpl.
  destructs H31.
  simpl RdyChange in H28.
  split;auto.
  eapply crt_init;eauto.
  eapply linv_change_linv_aux;eauto.
  eexists;splits;eauto.
  simpl;auto.

  (*-----------other tasks-------------*)
  rewrite map_get_set' in H28;auto.
  rewrite map_get_set' in H28;auto.
  assert (t'0<>t) by auto.
  eapply Hrsim in H19;eauto.
  mytac.
  exists x3 x4 x5 x6.
  splits;auto.
  eapply TMSpecMod.mapsto_mapsto_put;eauto.
  eapply TMSpecMod.mapsto_mapsto_put;eauto.
  eapply TOSpecMod.mapsto_mapsto_put;eauto.
  eapply TOSpecMod.mapsto_mapsto_put;eauto.
  unfold Snewt.
  unfold Dnewt,Tlnewt;simpl.
  unfolddef.
  rewrite map_get_set';auto.
  rewrite map_get_set';auto.
  rewrite map_get_set';auto.
  rewrite map_get_set';auto.
  eapply htstepstar_nodead_still;eauto.
  
  
  clear -H31 H30 H17 H7 Hjoin'.
  assert (get x0 abtcblsid = Some (abstcblist x1)).
  eapply join_get_l;eauto.
  unfold task_no_dead in *.
  intros.
  rewrite H in H0;inverts H0.
  
  eapply joinsig_indom_neq;eauto.
  apply H30;rewrite map_get_set;auto.
  apply hpstep_eqdomto in H18;auto.
  eapply join_merge_minus;eauto.
  eapply parto_sub;eauto.
  
  (*------------------------------stkfree case----------------------------------------*)
  subst t'.
  subst.
  
  inversion H0;subst pc0 po0 pi0 ip0;clear H0.
  destruct Hcsim as (o&o'&Mc&Oc&Cl&Ch&Htm&Hto&Hproj&Hsubst&Htgeth&Htgetl&Hlinv&Hcsim).
  unfolddef.
  rewrite Htgetl in H1;inverts H1.
  inverts Hcsim.
  assert ( (curs (sprim (stkfree e)), (kenil, ks)) =  (curs (sprim (stkfree e)), (kenil, ks))) by auto.
  destruct o as [[[[]]]].
  rewrite Hproj in H8;inverts H8.
  simpl in Hsubst.
  subst o'.
  simpl substaskst in *.
  destruct Hinv as (o1&o1'&Hproj1&Hsubsub&Hinv).
  rewrite Hproj in Hproj1.
  inverts Hproj1.
  simpl in Hsubsub.
  subst o1'.
  eapply H6 with (Ms:=Ms) (Os:=Os) (OO:=merge Oc Os)in H9;eauto.
  Focus 2.
  unfold getmem;simpl.
  eapply part_disjm with (M:=Ml) (T:=Tl) (Tm:=Tm) (t:=t);eauto.
  clear -Hmjoin.
  simpl in Hmjoin.
  unfolddef;geat.
  Focus 2.
  apply join_merge_disj.
  eapply part_disjo with (M:=Ol) (T:=Tl) (Tm:=To) (t:=t);eauto.
  clear -HOjoin.
  unfolddef;geat.
  destruct H9 as (Ch'&p&sh&k&t'&OO'&OO''&O'&Os'&H9).
  mytac.
  subst.
  destruct S' as [[[[]]]].
  simpl in Hproj.
  unfolddef.
  remember (get c t) as getle.
  destruct getle;tryfalse.
  remember (get l t) as getaux.
  destruct getaux;tryfalse.
  simpl get_smem in *.
  simpl snd in *.
  simpl fst in *.
  inverts Hproj.
  assert (Maps.sub Mc Ml).
  eapply part_sub;eauto.
  rename m0 into m.
  assert (Maps.sub Mc m).
  eapply sub_trans;eauto.
  clear -Hmjoin.
  unfolds.
  geat.

  unfolds in H12.
  destruct H12.
  simpl in H9.
  lets Hx:evalval_mono H12 H9.
  rewrite Hx in *.
  rewrite H7 in H9;inverts H9.
  clear Hx.

  eapply htstepstar_O_local with (Of:= (minus Ol Oc)) (OO:=O) (cst:=(ge, cenvs, M)) in H10.
  destruct H10.
  destruct H9 as (Hhtstepstar&Hjoin').
  assert (htstepstar (pc, A) t Ch (ge, cenvs, M) O
                  (curs (hapi_code (spec_del (Vint32 p);; sh)), k)
                  (ge, cenvs, M) x0) as Htstepstar;auto.
  eapply th_no_create_lift in Hhtstepstar;eauto.
  destruct k as (keh,ksh).

  destruct H11.
  (*-------------------stkfree self----------------------*)
  mytac.
  inverts H9.
  rename t' into t.
  mytac.
  inverts H15;mytac.
  assert (hpstepstar  (pc, A) Th (ge, cenvs, M) O  (set Th t
                     (curs (hapi_code sh), (keh,ksh))) (ge, del cenvs t, M) (merge (set OO' abtcblsid (abstcblist x2)) (minus Ol Oc)) ).

  eapply hpstep_star;eauto.
  eapply hpdel_step;eauto.
  apply map_get_set.
  erewrite <- set_set_eq;eauto.
  eapply join_get_get_l;eauto.
  assert (x0 = merge OO' (minus Ol Oc)).
  apply map_join_merge';auto.
  symmetry.
  subst x0.
  eapply join_merge_set_eq;eauto.
  unfolds in H16.
  eapply join_get_get_l;eauto.
  eapply map_get_sig.
  unfold joinsig in H16.
  clear -H16.
  join auto.
  eapply join_get_l;eauto.
  do 2 eexists;split;eauto.
  assert (merge (set OO' abtcblsid (abstcblist x2)) (minus Ol Oc) = set x0 abtcblsid (abstcblist x2)).
  assert (x0 = merge OO' (minus Ol Oc)).
  apply map_join_merge';auto.
  subst x0.
  eapply join_merge_set_eq;eauto.

  rewrite H18 in *.
  apply CIH;auto.
  rewrite <-Hosabsttid.
  apply htstepstar_tidsame in Htstepstar.
  unfold tidsame in Htstepstar.
  unfolddef.
  rewrite Htstepstar.
  apply map_get_set';auto.

  exists pc A po pi ip.
  exists Tm
         (TOSpecMod.put To t O')
         (merge O' (minus Ol Oc)) Os'.
  exists Ms Ml I lasrt.
  splits;auto.
  splits;auto.
  splits;auto.
  
  eapply lpstep_goodks;eauto.
  eapply partm_task_get_set;eauto.
  eapply join_crt;eauto.
  eapply new_part_o;eauto.

  eapply get_set_join_disj_l;eauto.
  eapply parto_task_get_set;eauto.
  exists (e0,e1,m,ir,au) (e0,e1,Ms,ir,au).
  splits;auto.
  unfolds.
  unfold projD.
  unfolddef.
  rewrite <- Heqgetle.
  rewrite <- Heqgetaux.
  auto.
  exists (e0,e1,m,ir,au) (e0,e1,Mc,ir,au) Mc O' (SKIP , (kenil, ks)) (curs (hapi_code sh), (keh, ksh)).
  splits;auto.
  unfolds.
  unfold projD.
  unfolddef.
  rewrite <- Heqgetle.
  rewrite <- Heqgetaux.
  auto.
  apply map_get_set.
  apply map_get_set.

  splits;auto.
  intros.
  rewrite map_get_set' in H20;auto.
  apply Hrsim in H20;auto.
  mytac.
  do 4 eexists;splits;eauto.
  apply TOSpecMod.mapsto_mapsto_put;auto.
  rewrite map_get_set';auto.
  eapply htstepstar_nodead_still;eauto.
  eapply join_get_get_l in H15;eauto.
  clear -H15 H16 H21.
  unfold task_no_dead in *.
  intros.
  unfolddef.
  rewrite H in H15;inverts H15.
  rewrite map_get_set in H21.
  assert (Some (abstcblist x2) = Some (abstcblist x2)) by auto.
  apply H21 in H0.
  unfolds in H16.
  unfold indom in *.
  mytac.
  eexists.
  eapply join_get_get_r;eauto.
  eapply hpstep_eqdomto;eauto.
  
  (*-------------------stkfree other----------------------*)
  mytac.
  inverts H9.
  mytac.
  inverts H16;mytac.
  assert (hpstepstar  (pc, A) Th (ge, cenvs, M) O  (set Th t
                     (curs (hapi_code sh), (keh,ksh))) (ge, del cenvs t', M) (merge (set OO' abtcblsid (abstcblist x2)) (minus Ol Oc)) ).

  eapply hpstep_star;eauto.
  eapply hpdel_step with (t':=t');eauto.
  apply map_get_set.
  erewrite <- set_set_eq;eauto.
  eapply join_get_get_l;eauto.
  assert (x0 = merge OO' (minus Ol Oc)).
  apply map_join_merge';auto.
  symmetry.
  subst x0.
  eapply join_merge_set_eq;eauto.
  unfolds in H17.
  eapply join_get_get_l;eauto.
  eapply map_get_sig.
  unfold joinsig in H17.
  clear -H17.
  join auto.
  eapply join_get_l;eauto.
  do 2 eexists;split;eauto.
  assert (merge (set OO' abtcblsid (abstcblist x2)) (minus Ol Oc) = set x0 abtcblsid (abstcblist x2)).
  assert (x0 = merge OO' (minus Ol Oc)).
  apply map_join_merge';auto.
  subst x0.
  eapply join_merge_set_eq;eauto.

  rewrite H19 in *.
  apply CIH;auto.
  rewrite <-Hosabsttid.
  apply htstepstar_tidsame in Htstepstar.
  unfold tidsame in Htstepstar.
  unfolddef.
  rewrite Htstepstar.
  apply map_get_set';auto.

  assert (task_no_dead O t').
  eapply htstepstar_nodead_still;eauto.
  eapply join_get_get_l in H16;eauto.
  clear -H16 H17.
  unfolds.
  intros.
  unfolddef;rewrite H in H16;inverts H16.
  unfolds.
  unfolds in H17.
  eexists.
  eapply join_get_get_l;eauto.
  apply map_get_sig;auto.
  assert (exists Ch,get Th t' = Some Ch).
  eapply hpstep_eqdomto with (O':=x0)in Heqdomto;eauto.
  eapply join_get_get_l in H16;eauto.
  clear -H17 H16 Heqdomto H15.
  unfolds in Heqdomto.
  mytac.
  unfolddef.
  auto.
  rewrite H16 in H;inverts H.
  assert (get x t' = Some (p,x3,x4)).
  unfolds in H17.
  eapply join_get_get_l in H17;eauto.
  apply map_get_sig.
  assert (exists y,get x t' = Some y) by eauto.
  eapply H0 in H1.
  mytac.
  rewrite map_get_set' in H1;eauto.
  mytac.
  assert (t'<>t) by auto.
  lets Hx:Hrsim H22 H21 H20.
  destruct Hx as (od&Md&Cld&Od&Hx).
  mytac.
  destruct od as [[[[]]]].
  unfold projS in H25.
  unfold projD in H25.
  unfolddef.
  remember (get c t') as Hled.
  remember (get l t') as Hauxd.
  destruct Hled;tryfalse.
  destruct Hauxd;tryfalse.
  inverts H25.
  simpl substaskst in *.

  lets Hx: linv_split H26.
  destruct Hx as (Mdc&Mdl&Odc&Odl&Hx).
  mytac.
  exists pc A po pi ip.
  exists (TMSpecMod.put (TMSpecMod.put Tm t (merge Mc Mdc)) t' Mdl)
         (TOSpecMod.put (TOSpecMod.put To t (merge O' Odc)) t' Odl)
         (merge O' (minus Ol Oc)) Os'.
  exists Ms Ml I lasrt.
  splits;auto.
  splits;auto.
  splits;auto.
  
  eapply lpstep_goodks;eauto.
  eapply partm_task_get_set;eauto.

  eapply delother_partm;eauto.
  eapply join_crt;eauto.
  assert ( partO (merge O' (minus Ol Oc)) (set Tl t (SKIP , (kenil, ks)))
                 (TOSpecMod.put To t O')).
  eapply new_part_o;eauto.
  eapply get_set_join_disj_l;eauto.
  eapply parto_task_get_set;eauto.
  assert ( (TOSpecMod.put (TOSpecMod.put To t O') t (merge O' Odc)) = (TOSpecMod.put To t (merge O' Odc))).
  apply TOSpecMod.put_xx_update.
  rewrite <- H32.
  eapply delother_parto;eauto.
  eapply to_mapsto_put';eauto.
  
  exists (e2,e1,m0,i,au) (e2,e1,Ms,i,au).
  splits;auto.
  unfolds.
  unfold projD.
  unfolddef.
  rewrite <- Heqgetle.
  rewrite <- Heqgetaux.
  auto.
  
  exists (e2,e1,m0,i,au) (e2,e1,(merge Mc Mdc),i,au) (merge Mc Mdc) (merge O' Odc) (SKIP , (kenil, ks)) (curs (hapi_code sh), (keh, ksh)).
  splits;auto.
  eapply TMSpecMod.mapsto_mapsto_put;eauto.
  eapply TOSpecMod.mapsto_mapsto_put;eauto.
  unfolds.
  unfold projD.
  unfolddef.
  rewrite <- Heqgetle.
  rewrite <- Heqgetaux.
  auto.
  apply map_get_set.
  apply map_get_set.
  eapply CurLINV_merge_hold;eauto.
  eapply disj_trans_sub with (m2:=Md).
  unfolds;geat.

  clear -Hmpart Htm H23 H22.

  
  eapply partm_neq_disj;eauto.
  eapply disj_trans_sub with (m2:=Od).
  unfolds;geat.

  eapply disj_complex'''';eauto.
  eapply H14;eauto.
  
  eapply LINV_ignore_int;eauto.
  unfolds.
  do 6 eexists;splits;eauto.
  eapply join_merge_disj.
  eapply disj_trans_sub with (m2:=Md).
  unfolds;geat.
  eapply partm_neq_disj;eauto.
  eapply join_merge_disj.
  eapply disj_trans_sub with (m2:=Od).
  unfolds;geat.
  eapply disj_complex'''';eauto.

  splits;auto.
  
  intros.
  assert (t'0 = t' \/ t'0 <> t') by tauto.
  destruct H34.
  subst t'0.
  clear -H17 H33 H16 Hjoin'.
  unfolds in H33.
  rewrite map_get_set in H33;auto.
  assert ( Some (abstcblist x2) = Some (abstcblist x2) ) by auto.
  apply H33 in H.
  unfolds in H17.
  eapply map_join_get_no_perm1 in H17;eauto.
  unfolds in H.
  mytac.
  unfolddef.
  rewrite e in H17.
  tryfalse.
  apply map_get_sig.
  rewrite map_get_set' in H32;eauto.
  assert (task_no_dead O t'0).
  eapply htstepstar_nodead_still;eauto.
  
  eapply join_get_get_l in H16;eauto.
  clear -H33 H34 H17 H16.
  unfold task_no_dead in *.
  intros.
  unfolddef.
  rewrite H in H16;inverts H16.
  rewrite map_get_set in H33.
  assert (Some (abstcblist x2) = Some (abstcblist x2)) by auto.
  apply H33 in H0.
  unfold indom in *.
  mytac.
  eexists.
  eapply join_get_get_r;eauto.

  lets Hx: Hrsim H31 H32 H35.
  mytac.
  exists x7 x8 x9 x10;splits;eauto.
  eapply TMSpecMod.mapsto_mapsto_put;eauto.
  eapply TMSpecMod.mapsto_mapsto_put;eauto.
  eapply TOSpecMod.mapsto_mapsto_put;eauto.
  eapply TOSpecMod.mapsto_mapsto_put;eauto.
  rewrite map_get_set';auto.
  eapply hpstep_eqdomto;eauto.

  eapply join_merge_minus;eauto.
  eapply parto_sub;eauto.
  (*Guarded.*)
  (*------------------------------event case----------------------------------------*)
  
  intros.
  assert (lpstepev pl Tl cst Sl t Tl' cst' S' t' ev) as Hlpstep by auto.
  inverts H.
  destruct Hcsim as (o&o'&Mc&Oc&Cl&Ch&Hcsim).
  destruct Hcsim as (Htm&Hto&Hproj&Hsubs&Hth&Htl&Hlinv&Hcsim).
  inverts Hcsim.
  destruct Hinv as (oi&oi'&Ha1&Ha2&Ha3).
  unfolddef.
  assert (o=oi).  
  rewrite Ha1 in Hproj.
  inverts Hproj.
  auto.
  subst oi.
  assert (tst=o).
  rewrite H2 in Hproj.
  inverts Hproj;auto.
  subst tst.
  destruct o as [[[[]]]].
  simpl in Ha2;subst oi'.

  simpl in Hsubs;subst o'.
  simpl substaskst in *.
  unfold satp in *.
  rename t' into t.
  rewrite Htl in H0;inverts H0.
  eapply H1 with(cst:=cst') (cst':=cst') (Cl':=C') (Mf:=minus Ml Mc)
                            (o2:=(e, e0, m, i, l)) (ev:=ev) (OO:=merge Oc Os) (o'':=(e, e0, m, i, l))in Ha3;eauto.
  
  destruct Ha3 as (Ch'&O'&o'&Ms'&Oc'&Os'&Htstep&Hjoin2&Hhjoin&Hinv'&Hlinv'&Htsim).

  eapply htstepevstar_O_local with (Of:= (minus Ol Oc)) (OO:=O) in Htstep.
  mytac.

  exists (set Th t Ch') x.
  split.

  apply th_no_create_lift_ev  with (C:=Ch);auto.

  apply CIH.

  rename H0 into Hhtstep.
  apply htstepevstar_tidsame in Hhtstep;auto.
  unfold tidsame in Hhtstep.
  unfold get in Hhtstep,Hosabsttid.
  simpl in Hhtstep.
  simpl in Hosabsttid.
  rewrite Hosabsttid in Hhtstep;auto.

  exists pc A po pi ip (TMSpecMod.put Tm t (get_mem (get_smem o'))).
  subst.

  exists (TOSpecMod.put To t Oc') (minus x Os') Os' Ms' (minus m Ms').
  exists I lasrt.

  splits;auto.
  splits;auto.
  splits;auto.

  eapply lpstepev_goodks;eauto.
  assert (snd (fst (fst S')) = snd (fst (fst (e, e0, m, i, l)))).
  apply projs_eqm with (t:=t);auto.
  rewrite H10.
  simpl.

  eapply joinm2_minus_join;eauto.
  simpl. 
  eapply partm_task_get_set;eauto.
  eapply partM_normal;eauto.
  eapply join_join_minus;eauto.
  eapply parto_task_get_set;eauto.
  eapply partO_normal;eauto.
  (*
  unfold partM in Hmpart.
  destruct Hmpart as (Hsub&Hdisjeach).
  unfold partM.
  split.
  intros.
  destruct (tid_eq_dec t t0).
  exists (get_mem (get_smem o')).
  rewrite <- e1.
  split.
  apply TMSpecMod.mapsto_put. 
  eapply joinm2_sub;eauto.
  assert ( TasksMod.get (TasksMod.set Tl t0 C') t =TasksMod.get Tl t ).
  eapply tasks_set_get_neq;eauto.
  destruct Hsub with t0 as (mm&Hmpas&Hsubm).
  exists mm.
  split.
  apply tm_mapsto_put';auto.
  assert (Maps.sub mm (minus Ml Mc)).
  apply minus_sub;auto.
  apply Hdisjeach with (t1:=t0) (m1:=mm)in Htm;auto.
  eapply sub_join_trans' with (o:=o') (M':=minus Ml Mc);eauto.
  
  intros.
  destruct (tid_eq_dec t1 t).
  rewrite e1 in H11.
  assert (TMSpecMod.maps_to (TMSpecMod.put Tm t (get_mem (get_smem o'))) t (get_mem (get_smem o'))).
  apply TMSpecMod.ext_mapsto.
  unfold TMSpecMod.maps_to in H11.
  unfold TMSpecMod.maps_to in H13.
  subst t1.
  rewrite H11 in H13.
  inverts H13.
  assert (t<>t2) as Hneq.
  auto.
  apply Hdisjeach  with (m1:=Mc) (m2:= m2) in H10.
  assert (Maps.sub m2 (minus Ml Mc)) as Hfu.
  assert (TasksMod.get (set Tl t C') t2 = TasksMod.get Tl t2).
  apply tasks_set_get_neq;auto.
  apply minus_sub;auto.
  destruct Hsub with t2 as (mn&Htm'&Hsub').
  assert ( TMSpecMod.maps_to Tm t2 m2).
  apply TMSpecMod.ext_presv_mapsto with (x:=t) (y:=get_mem (get_smem o'));auto.
  assert (mn=m2).
  unfold TMSpecMod.maps_to in H14.
  unfold TMSpecMod.maps_to in Htm'.
  rewrite H14 in Htm'.
  inversion Htm';tryfalse;auto.
  subst mn.
  apply Hsub'.
  apply Hdisjeach with (m1:=Mc) (m2:=m2)in Hneq;auto.
  apply disj_sym;auto.
  apply TMSpecMod.ext_presv_mapsto with (x:=t) (y:=get_mem (get_smem o'));auto.
  apply disj_sym.
  eapply joinm2_sub_disj with (M1:=Ms');eauto.
  auto.
  assert ( TasksMod.get (set Tl t C') t2 =TasksMod.get Tl t2 ).
  apply tasks_set_get_neq with (t:=t);auto.
  apply TMSpecMod.ext_presv_mapsto with (x:=t) (y:=get_mem (get_smem o'));auto.
  destruct (tid_eq_dec t2 t). 
  subst t2.
  assert (TMSpecMod.maps_to (TMSpecMod.put Tm t (get_mem (get_smem o'))) t (get_mem (get_smem o'))).
  apply TMSpecMod.ext_mapsto.
  unfold TMSpecMod.maps_to in H12.
  unfold TMSpecMod.maps_to in H13.
  rewrite H12 in H13.
  inverts H13.
  assert (t<>t1) as Hneq.
  auto.
  clear H10.
  assert (t<>t1) as H10.
  auto.
  apply Hdisjeach  with (m1:=Mc) (m2:= m1)in H10.
  assert (Maps.sub m1 (minus Ml Mc)) as Hfu.
  assert (TasksMod.get (set Tl t C') t1 = TasksMod.get Tl t1).
  apply tasks_set_get_neq;auto.
  apply minus_sub;auto.
  destruct Hsub with t1 as (mn&Htm'&Hsub').
  assert ( TMSpecMod.maps_to Tm t1 m1).
  apply TMSpecMod.ext_presv_mapsto with (x:=t) (y:=get_mem (get_smem o'));auto.
  unfold TMSpecMod.maps_to in H14.
  unfold TMSpecMod.maps_to in Htm'.
  rewrite H14 in Htm'.
  inverts Htm'.
  apply Hsub'.
  apply Hdisjeach with (m1:=Mc) (m2:=m1) in Hneq;auto.
  apply disj_sym;auto.
  apply TMSpecMod.ext_presv_mapsto with (x:=t) (y:=get_mem (get_smem o'));auto.
  eapply joinm2_sub_disj with (M1:=Ms');eauto.
  auto.
  assert ( TasksMod.get (set Tl t C') t1 =TasksMod.get Tl t1 ).
  apply tasks_set_get_neq with (t:=t);auto.
  apply TMSpecMod.ext_presv_mapsto with (x:=t) (y:=get_mem (get_smem o'));auto.
  apply Hdisjeach with (t1:=t1) (t2:=t2);auto.
  apply TMSpecMod.ext_presv_mapsto with (x:=t) (y:=get_mem (get_smem o'));auto.
  apply TMSpecMod.ext_presv_mapsto with (x:=t) (y:=get_mem (get_smem o'));auto.

  eapply join_join_minus;eauto.

  unfold partO in HOpart.
  destruct HOpart as (Hsub&Hdisjeach).
  unfold partO.
  split.
  intros.
  destruct (tid_eq_dec t t0).
  exists Oc'.
  rewrite <- e1.
  split.
  apply TOSpecMod.mapsto_put.

  eapply join_join_sub_minus;eauto.
  assert ( TasksMod.get (TasksMod.set Tl t0 C') t =TasksMod.get Tl t ).
  eapply tasks_set_get_neq;eauto.
  destruct Hsub with t0 as (mm&Hmpas&Hsubm).
  exists mm.
  split.
  apply to_mapsto_put';auto.
  assert (Maps.sub mm (minus Ol Oc)).
  apply minus_sub;auto.
  apply Hdisjeach with (t1:=t0) (m1:=mm)in Hto;auto.

  eapply join_join_sub_sub_minus with (M2:=minus Ol Oc);eauto.
  
  intros.
  destruct (tid_eq_dec t1 t).
  rewrite e1 in H11.
  assert (TOSpecMod.maps_to (TOSpecMod.put To t Oc') t Oc').
  apply TOSpecMod.ext_mapsto.
  unfold TOSpecMod.maps_to in H11.
  unfold TOSpecMod.maps_to in H13.
  subst t1.
  rewrite H11 in H13.
  inverts H13.
  assert (t<>t2) as Hneq.
  auto.
  apply Hdisjeach  with (m1:=Oc) (m2:= m2) in H10.
  assert (Maps.sub m2 (minus Ol Oc)) as Hfu.
  assert (TasksMod.get (set Tl t C') t2 = TasksMod.get Tl t2).
  apply tasks_set_get_neq;auto.
  apply minus_sub;auto.
  destruct Hsub with t2 as (mn&Htm'&Hsub').
  assert ( TOSpecMod.maps_to To t2 m2).
  apply TOSpecMod.ext_presv_mapsto with (x:=t) (y:=Oc');auto.
  assert (mn=m2).
  unfold TOSpecMod.maps_to in H14.
  unfold TOSpecMod.maps_to in Htm'.
  rewrite H14 in Htm'.
  inversion Htm';tryfalse;auto.
  subst mn.
  apply Hsub'.
  apply Hdisjeach with (m1:=Oc) (m2:=m2)in Hneq;auto.
  apply disj_sym;auto.
  apply TOSpecMod.ext_presv_mapsto with (x:=t) (y:=Oc');auto.
  apply disj_sym.
  eapply join_join_sub_disj with (M2:=(minus Ol Oc));eauto.

  auto.
  assert ( TasksMod.get (set Tl t C') t2 =TasksMod.get Tl t2 ).
  apply tasks_set_get_neq with (t:=t);auto.
  apply TOSpecMod.ext_presv_mapsto with (x:=t) (y:=Oc');auto.
  destruct (tid_eq_dec t2 t). 
  subst t2.
  assert (TOSpecMod.maps_to (TOSpecMod.put To t Oc') t Oc').
  apply TOSpecMod.ext_mapsto.
  unfold TOSpecMod.maps_to in H12.
  unfold TOSpecMod.maps_to in H13.
  rewrite H12 in H13.
  inverts H13.
  assert (t<>t1) as Hneq.
  auto.
  clear H10.
  assert (t<>t1) as H10.
  auto.
  apply Hdisjeach  with (m1:=Oc) (m2:= m1)in H10.
  assert (Maps.sub m1 (minus Ol Oc)) as Hfu.
  assert (TasksMod.get (set Tl t C') t1 = TasksMod.get Tl t1).
  apply tasks_set_get_neq;auto.
  apply minus_sub;auto.
  destruct Hsub with t1 as (mn&Htm'&Hsub').
  assert ( TOSpecMod.maps_to To t1 m1).
  apply TOSpecMod.ext_presv_mapsto with (x:=t) (y:=Oc');auto.
  unfold TOSpecMod.maps_to in H14.
  unfold TOSpecMod.maps_to in Htm'.
  rewrite H14 in Htm'.
  inverts Htm'.
  apply Hsub'.
  apply Hdisjeach with (m1:=Oc) (m2:=m1) in Hneq;auto.
  apply disj_sym;auto.
  apply TOSpecMod.ext_presv_mapsto with (x:=t) (y:=Oc');auto.
  eapply join_join_sub_disj with (M2:=(minus Ol Oc));eauto.
  auto.
  assert ( TasksMod.get (set Tl t C') t1 =TasksMod.get Tl t1 ).
  apply tasks_set_get_neq with (t:=t);auto.
  apply TOSpecMod.ext_presv_mapsto with (x:=t) (y:=Oc');auto.
  apply Hdisjeach with (t1:=t1) (t2:=t2);auto.
  apply TOSpecMod.ext_presv_mapsto with (x:=t) (y:=Oc');auto.
  apply TOSpecMod.ext_presv_mapsto with (x:=t) (y:=Oc');auto.
*)
  exists (e, e0, m, i, l) (e, e0, Ms', i, l).
  splits;auto.
  
  assert (substaskst o' Ms'= (e, e0, Ms', i, l)) as Hrepltrans.
  clear -Hjoin2.
  unfolds in Hjoin2.
  mytac.
  unfold joinmem in *.
  mytac.
  simpl;auto.
  rewrite Hrepltrans in Hinv'.
  auto.

  exists (e, e0, m, i, l) o'
         (get_mem (get_smem o')) Oc' C' Ch'.
  splits;auto.
  clear -Hjoin2.
  unfolds in Hjoin2.
  mytac.
  unfold joinmem in *.
  mytac.
  simpl.
  auto.
  apply map_get_set.
  apply map_get_set.

  splits;auto.
  intros.
  
  rename H12 into Hnodead.
  assert (t'<>t);auto.

  apply Hrsim with (Ch:=Ch0) in H10.

  destruct H10 as (or&M'r&Clr&O'r&Htmr&Htor&Hprojr&Hrlinv&Htasksr&Hsimr).

  exists (((gets_g S'),(get_env (get_smem or)),(gets_m S')),(snd (fst S')),
          (snd or)) M'r Clr O'r.
  splits;auto.
  apply tm_mapsto_put' with (t:=t) (a:=get_mem (get_smem o'));auto.
  apply to_mapsto_put' with (t:=t) (a:=Oc');auto.

  
  apply proj_stneq_ex with (S:=S') (t:=t); auto.
  destruct S' as [[[[]]]].
  simpl.
  split;intros.
  auto.
  unfolds.
  intros;auto.
  
  intros.
  eapply LInv_ignore_int.
  assert (substaskst
            (gets_g S', get_env (get_smem or), gets_m S', snd (fst or), snd or) M'r = substaskst or M'r).

  simpl.
  clear -Hprojr.
  destruct S' as [[[[]]]].
  destruct or as [[[[]]]].
  unfold gets_g,get_env.
  simpl in *.
  unfold tid in *.
  remember (get c t') as X.
  destruct X;tryfalse.
  remember (get l t') as Y.
  destruct Y;tryfalse.
  inverts Hprojr.
  auto.
  simpl in H10.
  erewrite H10.
  eauto.
  rewrite map_get_set';auto.
  
  intros.

  assert (forall Mr,RdyChange
            (substaskst
               (gets_g S', get_env (get_smem or), 
               gets_m S', snd (fst S'), snd or) Mr) = RdyChange (substaskst or Mr)).
  intros.
  simpl.
  clear -Hprojr.
  destruct S' as [[[[]]]].
  destruct or as [[[[]]]].
  unfold gets_g,get_env in *.
  simpl in *.
  unfold tid in *.
  remember (get c t') as X.
  destruct X;tryfalse.
  remember (get l t') as Y.
  destruct Y;tryfalse.
  inverts Hprojr.
  auto.

  rewrite H13 in H10.
  apply Hsimr in H10.
  mytac.
  eexists.
  erewrite H13.
  splits;eauto.
  
  rewrite <- H11. auto.
  symmetry.
  apply tasks_set_get_neq;auto.

  eapply htstepevstar_nodead_still;eauto.

  eapply hpstepev_eqdomto with (T:=Th) (O:=O) (p:=(pc,A));eauto.
  eapply th_no_create_lift_ev with (C:=Ch);eauto.

  eapply join_merge_minus;eauto.
  eapply parto_sub;eauto.
 
  assert ((e, e0, Mc, i, l) = substaskst (e, e0, m, i, l) Mc).
  simpl;auto.
  rewrite H0.
  eapply joinm2_merge_minus;eauto.
  assert ( (snd (fst (fst S'))) = (snd (fst (fst (e, e0, m, i, l))) )).
  apply projs_eqm with t.
  auto.
  simpl.
  simpl in H9.
  rewrite H9 in Hmjoin;auto.
  eapply part_sub;eauto.
  apply join_merge_disj.
  eapply part_disjo;eauto.
  unfolds;eauto.
  auto.

  (*-----------------------abort case---------------------------*)
  intros.
  inverts H.
  subst.
  destruct Hcsim as (o&o'&Mc&Oc&Cl&Ch&Htm&Hto&Hproj&Hsubs&Hth&Htl&Hlinv&Hcsim).
  rewrite Hproj in H1.
  inversion H1; tryfalse.
  subst tst.

  inversion Hcsim.
  subst.
  unfolddef.
  rewrite  H0 in Htl.
  inversion Htl;tryfalse.
  subst C.

  apply H10 with (cst:=cst)(Os:=Os) (Ms:=Ms) (o':=o) (Mf:=minus Ml Mc) (OO:=merge Oc Os) (OOO:=O) (Of:=minus Ol Oc) in H3;auto.
  
  apply  hp_stepstarabt.
  inversion H3.
  subst.
  destruct H13 as (c'&cst'&O'&Htstepstar&Htstepabt).
  exists (set Th t c') cst' O'.
  split.

  apply th_ttop_lift with (C:=Ch);auto.
  apply hpabt_step with (C:=c') (t:=t);auto.
  apply htstepstar_tidsame in Htstepstar.
  unfold tidsame in Htstepstar.
  rewrite <- Htstepstar;auto.
  apply map_get_set;auto.
  destruct Hinv as (x&x'&Hinv).
  mytac.
  rewrite H13 in Hproj;inverts Hproj.
  unfolds.
  destruct o as [[[[]]]];simpl substaskst in *;auto.
  Focus 3.
  eapply join_merge_minus;eauto.
  eapply parto_sub;eauto.
  
  eapply joinm2_merge_minus;eauto.
  assert ( (snd (fst (fst Sl))) = (snd (fst (fst o)) )).
  apply projs_eqm with t.
  auto.
  simpl.
  simpl in H13.
  destruct o as [[[[]]]].
  unfold get_smem,get_mem.
  rewrite H13 in Hmjoin;simpl in Hmjoin;auto.

  eapply part_sub;eauto.
  
  apply join_merge_disj.
  eapply part_disjo;eauto.
  unfolds;eauto.
  auto.
 
  destruct Hcsim as (o&o'&Mc&Oc&Cl&Ch&Htm&Hto&Hproj&Hsubs&Hth&Htl&Hlinv&Hcsim).
  rewrite Hproj in H1.
  inversion H1; tryfalse.
  subst tst.
  destruct o as [[[[]]]].
  simpl in Hsubs;subst o'.
  destruct Hinv as (o1&o1'&Hproj1&Hsubsub&Hinv).
  rewrite Hproj in Hproj1.
  inverts Hproj1.
  simpl in Hsubsub.
  subst o1'.
  inverts Hcsim.
  assert ((curs (sprim (stkinit e1 e2 e3)), (kenil, ks)) = (curs (sprim (stkinit e1 e2 e3)), (kenil, ks))) by auto.
  unfolddef.
  rewrite Htl in H0;inverts H0.
  eapply H7 with (Ms:=Ms) (Os:=Os) (OO:=merge Oc Os) in H9.
 
  simpl get_smem in *.
  mytac.
  destruct H3.
  
  destruct Sl as [[[[]]]].
  unfolds in Hproj.
  unfold projD in Hproj.
  unfolddef.
  destruct (get c t);tryfalse.
  destruct (get l0 t);tryfalse.
  inverts Hproj.
  exists x0 x1 x2;splits.
  eapply evalval_eq_prop;eauto.
  eapply sub_join_sub with (M1:=Ml);eauto.
  eapply part_sub with (T:=Tl) (Tm:=Tm) (t:=t);eauto.
  
  eapply evalval_eq_prop;eauto.
  eapply sub_join_sub with (M1:=Ml);eauto.
  eapply part_sub with (T:=Tl) (Tm:=Tm) (t:=t);eauto.
  
  eapply evalval_eq_prop;eauto.
  eapply sub_join_sub with (M1:=Ml);eauto.
  eapply part_sub with (T:=Tl) (Tm:=Tm) (t:=t);eauto.
  simpl substaskst in *;auto.
  exists (merge Mc Ms).
  unfold getmem;simpl.
  apply join_merge_disj.
  eapply part_disjm;eauto.
  clear -Hmjoin;unfolds;geat.
  apply join_merge_disj.
  eapply part_disjo;eauto.
  clear -HOjoin;unfolds;geat.
  
  destruct Hcsim as (o&o'&Mc&Oc&Cl&Ch&Htm&Hto&Hproj&Hsubs&Hth&Htl&Hlinv&Hcsim).
  rewrite Hproj in H1.
  inversion H1; tryfalse.
  subst tst.
  destruct o as [[[[]]]].
  simpl in Hsubs;subst o'.
  destruct Hinv as (o1&o1'&Hproj1&Hsubsub&Hinv).
  rewrite Hproj in Hproj1.
  inverts Hproj1.
  simpl in Hsubsub.
  subst o1'.
  inverts Hcsim.
  assert ((curs (sprim (stkfree e)), (kenil, ks)) = (curs (sprim (stkfree e)), (kenil, ks))) by auto.
  unfolddef.
  rewrite Htl in H0;inverts H0.
  eapply H8 with (Ms:=Ms) (Os:=Os) (OO:=merge Oc Os) in H9.
 
  simpl get_smem in *.
  mytac.
  destruct H3.
  
  destruct Sl as [[[[]]]].
  unfolds in Hproj.
  unfold projD in Hproj.
  unfolddef.
  destruct (get c t);tryfalse.
  destruct (get l0 t);tryfalse.
  inverts Hproj.
  exists x3.
  eapply evalval_eq_prop;eauto.
  eapply sub_join_sub with (M1:=Ml);eauto.
  eapply part_sub with (T:=Tl) (Tm:=Tm) (t:=t);eauto.
  simpl substaskst in *;auto.
  exists (merge Mc Ms).
  unfold getmem;simpl.
  apply join_merge_disj.
  eapply part_disjm;eauto.
  clear -Hmjoin;unfolds;geat.
  apply join_merge_disj.
  eapply part_disjo;eauto.
  clear -HOjoin;unfolds;geat.

  destruct Hcsim as (o&o'&Mc&Oc&Cl&Ch&Htm&Hto&Hproj&Hsubs&Hth&Htl&Hlinv&Hcsim).
  rewrite Hproj in H1.
  inversion H1; tryfalse.
  subst tst.
  destruct o as [[[[]]]].
  simpl in Hsubs;subst o'.
  destruct Hinv as (o1&o1'&Hproj1&Hsubsub&Hinv).
  rewrite Hproj in Hproj1.
  inverts Hproj1.
  simpl in Hsubsub.
  subst o1'.
  inverts Hcsim.
  assert ((curs (sprim (switch x)), (kenil, ks)) = (curs (sprim (switch x)), (kenil, ks))) by auto.
  unfolddef.
  rewrite Htl in H0;inverts H0.
  eapply H4 with (Ms:=Ms) (Os:=Os) (OO:=merge Oc Os) in H9.
  simpl substaskst in *.
  simpl get_smem in *.
  mytac.
  destruct H3.

  simpl get_genv.
  simpl get_mem.
  destruct Sl as [[[[]]]].
  unfolds in Hproj.
  unfold projD in Hproj.
  unfolddef.
  destruct (get c t);tryfalse.
  destruct (get l0 t);tryfalse.
  inverts Hproj.
  destruct H16;mytac.
  eapply swpre_hpswitch_nabt.
  unfold satp in *.
  eapply swpre_prop;eauto.
  intros.
  lets Hx:H0 ab.
  unfold SWPRE_NDEAD in Hx;destruct Hx;eauto.
  simpl.
  clear -H10 Htm Hmpart Hmjoin.
  unfolds in H10.
  mytac.
  eapply part_sub in Htm;eauto.
  simpl in Hmjoin.
  unfold Maps.sub in *;mytac.
  unfolddef.
  geat.
  instantiate (1:=x9).
  clear;unfolds;geat.
  assert (satp (e, e0, x4, i, l) x9 (SWPRE (getsched (pc, A)) x t)).
  clear -H0.
  unfold satp in *;intros.
  lets Hx:H0 aop.
  destruct Hx;auto.
  eapply swpre_hpswitch_nabt.
  unfold satp in *.
  eapply swpre_prop;eauto.
  simpl.
  clear -H10 Htm Hmpart Hmjoin.
  unfolds in H10.
  mytac.
  eapply part_sub in Htm;eauto.
  simpl in Hmjoin.
  unfold Maps.sub in *;mytac.
  unfolddef.
  geat.
  instantiate (1:=x9).
  clear;unfolds;geat.
  simpl substaskst in *;auto.
  exists (merge Mc Ms).
  unfold getmem;simpl.
  apply join_merge_disj.
  eapply part_disjm;eauto.
  clear -Hmjoin;unfolds;geat.
  apply join_merge_disj.
  eapply part_disjo;eauto.
  clear -HOjoin;unfolds;geat.
  Grab Existential Variables.
  trivial.
  trivial.
  trivial.
  trivial.
Qed.

Lemma ApiMethSim: 
  forall (OS1:oscode) (A:osspec) Spec I lasrt,    
    GoodI I (snd A) lasrt->
    (
      WFFuncsSim (snd (fst OS1)) Spec (snd A) lasrt I
    ) ->
    (
      forall (f:fid) ab vl p r ft G tid, 
        (fst (fst A)) f = Some (ab,ft) ->
        Some p = BuildPreA (fst (fst OS1)) f (ab,ft) vl G lasrt tid init_lg->
        Some r = BuildRetA (fst (fst OS1)) f (ab,ft) vl G lasrt tid init_lg->
        (
          exists t d1 d2 s,
            (fst (fst OS1)) f = Some (t, d1, d2, s)/\ GoodStmt' s /\
            InfRules Spec (snd A) lasrt I r Afalse p s Afalse tid
        )
    )
    ->
    
    (
      forall (f:fid) ab vl p r ft G tid , 
        (fst (fst A)) f = Some (ab,ft) ->
        Some p = BuildPreA (fst (fst OS1)) f (ab,ft) vl G lasrt tid init_lg ->
        Some r = BuildRetA (fst (fst OS1)) f (ab,ft) vl G lasrt tid init_lg->
        (
          exists t d1 d2 s,
            (fst (fst OS1)) f = Some (t, d1, d2, s)/\ GoodStmt' s /\
            MethSimAsrt (snd (fst OS1)) (snd A) lasrt I r Afalse p s Afalse tid 
        )
    ).
Proof.
  introv goodi.
  intros.
  eapply H0 in H1;eauto.
  destruct H1 as (t&d1&d2&s&Ha1&Ha2&Ha3).
  exists t d1 d2 s;splits;auto.
  unfold MethSimAsrt.
  eapply MethSim_to_Methsim';eauto.
Qed.

Lemma IntMethSim: 
  forall (OS1:oscode) (A:osspec) Spec I lasrt, 
    GoodI I (snd A) lasrt->
    (
      WFFuncsSim (snd (fst OS1)) Spec (snd A) lasrt I
    ) ->
    (
      forall (i:hid) ispec isrreg si G tid lg, 
        (snd (fst A)) i = Some ispec ->
        (
          exists (s:stmts) p r,
            (snd OS1) i = Some s /\ 
            p = ipreasrt i isrreg si (ispec ) I G lasrt tid lg /\ 
            r = iretasrt i isrreg si I G lasrt tid lg /\
            InfRules Spec (snd A) lasrt I retfalse r p s Afalse tid
        )
    )
    ->
    
    (
      forall (i:hid) ispec  isrreg si G lg tid, 
        (snd (fst A)) i = Some ispec ->
        (
          exists (s:stmts) p r,
            (snd OS1) i = Some s /\ 
            p = ipreasrt i isrreg si (ispec) I G lasrt tid lg /\ 
            r = iretasrt i isrreg si I G lasrt tid lg /\
            MethSimAsrt (snd (fst OS1)) (snd A) lasrt I retfalse r p s Afalse tid
        )
    ).
Proof.
  introv goodi.
  intros.
  eapply H0 in H1.
  destruct H1 as (s&p&r&Ha1&Ha2&Ha3&Ha4).
  exists s p r.
  splits;eauto.
  unfold MethSimAsrt.
  simpl.
  eapply MethSim_to_Methsim';eauto.
Qed.

 
Lemma dladd_revlcons_eq: forall d1 d2, dladd d1 d2 = revlcons d1 d2.
Proof.
  intros.
  inductions d1; inductions d2; simpl; auto.  
Qed.


Lemma r_lift_rule: forall Spec sd I r' r p p' s f ab vl P G lasrt tid lg,
                     Some r = BuildRetA P f ab vl G lasrt tid lg->
                     Some p = BuildPreA P f ab vl G lasrt tid lg->
                     Some r' = BuildRetA' P f ab vl lasrt tid lg ->
                     Some p' = BuildPreA' P f ab vl lasrt tid lg->
                     {|Spec, sd, lasrt, I, r', Afalse|}|-tid {{p'}} s {{Afalse}} ->
                                                         {|Spec, sd, lasrt, I, r, Afalse|}|-tid {{p}} s {{Afalse}}.
Proof.
  introv Hr Hp Hr' Hp'.
  unfolds in Hr.
  unfolds in Hp.
  unfolds in Hr'.
  unfolds in Hp'.
  destruct (P f); tryfalse.
  destruct f0.
  destruct p0.
  destruct p0.
  rewrite dladd_revlcons_eq in *.
  remember (buildp (revlcons d0 d) vl) as Hasrt.
  destruct (dl_vl_match d0 (rev vl));tryfalse.
  destruct Hasrt; tryfalse.
  inverts Hp.
  inverts Hp'.
  remember ( buildq (revlcons d0 d)) as Hddd.
  destruct Hddd; tryfalse.
  inverts Hr'.
  inverts Hr.
  introv Hsim.
  eapply genv_introret_rule.
  auto.
Qed.

Lemma bpr'_to_bpr: forall osc (A:osspec) I Spec lasrt, 
                     (
                       forall (f:fid) ab vl p r ft tid, 
                         (fst (fst A)) f = Some (ab,ft) ->
                         Some p = BuildPreA' (get_afun osc) f (ab,ft) vl lasrt tid init_lg->
                         Some r = BuildRetA' (get_afun osc) f (ab,ft) vl lasrt tid init_lg->
                         (
                           exists  t d1 d2 s,
                             (get_afun osc) f = Some (t, d1, d2, s)/\ GoodStmt' s /\
                             InfRules Spec (snd A) lasrt I r Afalse p s Afalse tid
                         )
                     ) ->
                     (
                       forall (f:fid) ab vl p r ft G tid , 
                         (fst (fst A)) f = Some (ab,ft) ->
                         Some p = BuildPreA (get_afun osc) f (ab,ft) vl G lasrt tid init_lg->
                         Some r = BuildRetA (get_afun osc) f (ab,ft) vl G lasrt tid init_lg->
                         (
                           exists  t d1 d2 s,
                             (get_afun osc) f = Some (t, d1, d2, s)/\ GoodStmt' s /\
                             InfRules Spec (snd A) lasrt I r Afalse p s Afalse tid
                         )
                     ).
Proof.   
  intros.
  assert (exists p', Some p' = BuildPreA' (get_afun osc) f (ab, ft) vl lasrt tid init_lg).
  clear -H1.
  unfolds in H1.
  unfold BuildPreA'.
  destruct ((get_afun osc)).
  destruct f0.
  destruct p0.
  destruct p0.
  rewrite dladd_revlcons_eq.
  destruct (dl_vl_match d0 (rev vl));tryfalse.
  remember (buildp (revlcons d0 d) vl) as Hr.
  destruct Hr; tryfalse.  
  inverts H1.
  eexists; eauto.
  tryfalse.
  assert (exists p', Some p' = BuildRetA' (get_afun osc) f (ab, ft) vl lasrt tid init_lg).
  clear -H2.
  unfolds in H2.
  unfold BuildRetA'.
  destruct ((get_afun osc)).
  destruct f0.
  destruct p.
  destruct p.
  rewrite dladd_revlcons_eq.
  remember (buildq (revlcons d0 d) ) as Hr.
  destruct Hr; tryfalse.  
  inverts H2.
  eexists; eauto.
  tryfalse.

  destruct H3 as (p'&Hp).
  destruct H4 as (r'&Hr).
  assert (Some r' = BuildRetA' (get_afun osc) f (ab,ft) vl  lasrt tid init_lg) as Hrr;auto.
  eapply H in Hr;eauto.
  destruct Hr as (t&d1&d2&s&Hr1&Hr2&Hr3).
  exists t d1 d2 s;splits;auto.
  eapply r_lift_rule ;eauto.
Qed.

Lemma int_bpr'_to_bpr :
  forall osc (A:osspec) I Spec lasrt,
    EqDomInt (get_lint osc) (snd (fst A)) ->
    (forall (i : nat) (isrreg : isr) (si : is) 
            (p r : asrt) (t : tid) (lg : list logicvar),
       Some p = BuildintPre i  (snd (fst A)) isrreg si I lasrt t lg ->
       Some r = BuildintRet i  (snd (fst A)) isrreg si I lasrt t lg ->
       exists s,
         (get_lint osc) i = Some s /\
         {|Spec, snd A, lasrt, I, inferules.retfalse, r|}|- t {{p}} s
                                                           {{Afalse}}) ->
    (
      forall (i:hid) ispec isrreg si G t lg, 
        (snd (fst A)) i = Some ispec ->
        (
          exists (s:stmts) p r,
            (get_lint osc) i = Some s /\ 
            p = ipreasrt i isrreg si (ispec ) I G lasrt t lg/\ 
            r = iretasrt i isrreg si I G lasrt t lg /\
            InfRules Spec (snd A) lasrt I retfalse r p s Afalse t
        )
  ).
Proof.
  intros.
  assert (exists p, Some p = BuildintPre i (snd (fst A)) isrreg si I lasrt t lg).
  unfold BuildintPre.
  rewrite H1.
  eexists;eauto.
  destruct H2.
  assert (exists p, Some p = BuildintRet i (snd (fst A)) isrreg si I lasrt t lg).
  unfold BuildintRet.
  rewrite H1.
  eexists;eauto.
  destruct H3.
  lets Hx: H0 H2 H3.
  destruct Hx.
  destruct H4.
  unfold BuildintPre in H2.
  unfold BuildintRet in H3.
  rewrite H1 in *.
  inverts H2.
  inverts H3.
  exists x1.
  do 2 eexists.
  splits;auto.
  unfold ipreasrt,iretasrt.
  eapply genv_introexint_rule; eauto.
Qed.




Lemma eqdomsot_get_exproj:
  forall t S O T,
    indom T t ->
    eqdomto T O ->
    eqdomSO S O ->
    exists o, projS S t = Some o.
Proof.
  intros.
  unfolds in H0.
  mytac.
  lets Hx:H2 t.
  clear H2.
  unfolds in H1.
  destruct S as [[[[]]]].
  rewrite H0 in H1.
  unfolds in H.
  apply Hx in H.
  destruct H1.
  unfolds in H1.
  assert (exists a, TcbMod.get x t = Some a) as XX.
  auto.
  apply H1 in H.
  unfolds in H2.
  apply H2 in XX.
  clear -H XX.
  unfolds in H.
  unfolds in XX.
  mytac.
  exists (e,x0,m,i,x).
  unfolds;simpl;auto.
  unfold get in *.
  simpl in *.
  rewrite H.
  rewrite H0.
  auto.
Qed.


Lemma init_goodis:
  forall S O I lasrt sd init,
    init S O ->
    side_condition I lasrt sd init init_lg ->
    good_is_S S.
Proof.
  intros.
  unfolds in H.
  mytac.
  apply H0 in X.
  destruct X.
  clear H0 H2 H.
  induction H1.
  subst.
  unfolds.

  intros.
  destruct tst.
  destruct p.
  destruct p.
  destruct p.
  destruct l.
  destruct p.
  unfolds in H.
  unfold projD in H.
  assert (t0 = t \/ t0 <> t) by tauto.
  destruct H0;subst.
  rewrite map_get_sig in H.
  rewrite map_get_sig in H.
  inverts H.
  unfold init_cur in H3.
  unfold init_rdy in H3.
  lets Hx:H3 (spec_done None).
  simpl in Hx.
  mytac.
  simpl;auto.
  rewrite map_get_sig' in H;auto.
  tryfalse.
  unfolds.
  intros.
  assert (t0 = t \/ t0 <> t) by tauto.
  destruct H8.
  subst.
  
  destruct tst.
  destruct p.
  destruct p.
  destruct p.
  destruct l.
  destruct p.
  unfolds in H7.

  unfold projD in H7.

  eapply join_sig_get_disj in H0;eauto.
  destruct H0.
  eapply join_sig_get_disj in H1;eauto.
  unfold tid in *.
  rewrite H in H7.
  destruct H1.
  rewrite H1 in H7.
  inverts H7.
  lets Hx: H5 (spec_done None).
  simpl in Hx;mytac;auto.
  simpl;auto.

  destruct tst.
  destruct p.
  destruct p.
  destruct p.
  destruct l.
  destruct p.
  unfolds in IHinitst.
  assert (projS (G, envs', M', isr, lst') t0 = Some (e, e0, M', i, (i0, i1, c))).
  unfolds.
  unfold projD.
 

  unfolds in H7.
  destruct S.
  destruct p.
  inverts H.
  unfold projD in H7.
  remember (get envs t0 ) as X.
  destruct X;tryfalse.
  remember ( get lst t0 ) as Y.
  destruct Y;tryfalse.
  eapply join_get_get_r_rev with (a:=t0) in H0;eauto.
  eapply join_get_get_r_rev with (a:=t0) in H1;eauto.
  rewrite H0.
  rewrite H1.
  inverts H7.
  auto.
  eapply map_get_sig';eauto.
  eapply map_get_sig';eauto.
  apply IHinitst in H9.
  auto.
Qed.

Theorem toptheorem':
  forall (osc:oscode) (A:osspec) (init:InitAsrt) lasrt (I:Inv) (Spec:funspec),
    no_fun_same (get_afun osc)  (get_ifun osc)->
    True ->
    True ->
    (*good_ret_pu (get_afun osc) ->*)
    (*good_ret_pu (get_ifun osc)  ->*)
    no_call_api_os (get_afun osc) (get_ifun osc) (get_lint osc) -> 
    (forall f t d1 d2 s, (fst (fst osc)) f = Some (t,d1,d2,s) -> good_decllist (revlcons d1 d2) = true/\GoodStmt' s) ->
    (forall f t d1 d2 s, (snd (fst osc)) f = Some (t,d1,d2,s) -> good_decllist (revlcons d1 d2) = true/\GoodStmt' s) ->
    (forall (i : nat) (isrreg : isr) (si : is) 
            (p r : asrt) (lg : list logicvar) (t : tid) ,
       Some p = BuildintPre i  (snd (fst A)) isrreg si I lasrt t lg ->
       Some r = BuildintRet i  (snd (fst A)) isrreg si I lasrt t lg ->
       exists s,
         (get_lint osc) i = Some s /\
         {|Spec, snd A, lasrt, I, inferules.retfalse, r|}|- t {{p}} s
                                                              {{Afalse}}) ->
    (
      forall (f:fid) ab vl p r ft tid , 
        (fst (fst A)) f = Some (ab,ft) ->
        Some p = BuildPreA' (get_afun osc) f (ab,ft) vl lasrt tid init_lg ->
        Some r = BuildRetA' (get_afun osc) f (ab,ft) vl lasrt tid init_lg->
        (
          exists  t d1 d2 s,
            (get_afun osc) f = Some (t, d1, d2, s)/\ GoodStmt' s /\
            InfRules Spec (snd A) lasrt I r Afalse  p s Afalse tid
        )
    )->
    
    WFFunEnv (get_ifun osc) Spec (snd A) lasrt I-> 
    (
      eqdomOS osc A /\
      side_condition I lasrt (snd A) init init_lg
    ) ->
    OSCorrect osc A init.
Proof. 
  intros osc A init lasrt I Spec Hnofunsame Hxpo Hxpi Hnoos Hgoodpo Hgoodpi Hint Hapi Hifun Hside.
  unfold OSCorrect.
  introv Hitideq.
  intros.
  unfold WellClient in H1.
  destruct H1 as (H1&Hxpc).
  apply progsim_imply_eref.
  unfold oscorrectness.prog_sim.
  subst.
  splits;auto.
  apply tsimtopsim.
  auto.
  destruct Hside as (Heqdomos&Hside).
  assert (eqdomTO T O) as HeqdomTO.
  unfolds in H.
  mytac.
  unfolds in H.
  unfolds.
  mytac.
  eexists;splits;eauto.
  intros.
  eapply H6;eauto.
  
  assert (eqdomto T O) as Heqdomto.
  unfolds in H.
  mytac.
  unfolds in H.
  unfolds.
  mytac.
  eexists;splits;eauto.
  
  lets Hx: init_partmo T Hitideq H0 Hside.
  auto.
  destruct Hx as (Tm & To & Ml & Ms & Ol & Os & Hinitst).
  
  exists pc A (get_afun osc) (get_ifun osc) (get_lint osc) Tm.
  exists To Ol Os Ms Ml I.
  exists lasrt. 
  splits;auto.

  unfolds get_afun, get_ifun, get_lint.
  destruct osc.
  destruct p.
  simpl.
  auto.
  split;auto.
  inversion Hside.
  splits;auto.
  unfolds;auto.
  lets Hx:H4 H0.
  destruct Hx.
  unfolds in H.
  destruct H.
  unfolds.
  intros.
  apply H7 in H8.
  mytac.
  unfolds in H8.
  inverts H8.
  simpl.
  destruct osc.
  destruct p.
  auto.


  eapply init_goodis;eauto.
  mytac;auto.
  
  do 2 eexists.
  splits;eauto.
  unfold InitTasks in H.
  destruct H.
  unfolds in H.
  mytac.
  unfolds in H2.
  destruct H2.
  do 6 eexists;splits;eauto.
  unfold CurLINV.
  clear -H12.
  unfold satp in *.
  intros.
  lets Hx: H12 aop.
  clear H12.
  sep auto.
  instantiate (1:=init_lg).
  sep auto.

  
  apply SmCTaskSim;auto.


  eapply ApiMethSim with (Spec:=Spec);auto.
  unfolds in Hside.
  destruct Hside;auto.
  apply WFFunEnv_imply_WFFuncsSim;auto.
  eapply bpr'_to_bpr;eauto.
  split;auto.
  
  unfolds.
  splits;auto.
  unfolds.
  split;eauto.
  clear -H13.
  destruct x1 as [[[[]]]].
  simpl in H13.
  simpl;auto.
  apply H16 in H2.
  mytac.
  eexists;eauto.
  (*--------------*)
  intros.
  lets Hx: H8 H16.
  unfolds;eauto.
  mytac.
  do 4 eexists;splits;eauto.
  exists init_lg.
  unfold satp in *.
  lets Hx:H22 aop.
  sep auto.
  
  intros.


  Lemma eqdomsot_get_exproj':
    forall t S O T Ch,
      TasksMod.get T t = Some Ch ->
      eqdomto T O ->
      eqdomSO S O ->
      exists o, projS S t = Some o.
  Proof.
    intros.
    eapply eqdomsot_get_exproj;eauto.
    unfolds;eauto.
  Qed.
  destruct H21.
  destruct x4 as [[[[]]]].
  destruct l as [[]].
  simpl substaskst in *.
  simpl RdyChange in *.
  eexists;split;auto.

  
  apply SmCTaskSim;auto.
  
  apply ApiMethSim with (Spec:=Spec) .
  unfolds in Hside.
  destruct Hside;auto.
  apply WFFunEnv_imply_WFFuncsSim;auto.
  eapply bpr'_to_bpr;eauto.
  split;auto.
  unfolds.
  splits;auto.
  unfold InitTaskSt.
  unfold satp in *.
  simpl fst in *.
  simpl snd.
  destruct H24.
  unfold RDYINV in H22.
  split.
  intros.
  lets Hx:H21 aop.
  lets Hy:H22 aop.
  destruct Hx.
  clear H21 H22.
  
  destruct H24.
  destruct H22;auto.
  unfold CurTid.
  Lemma merge_star:
    forall P Q M1 M2 G E a b O1 O2 d,
      disjoint M1 M2 ->
      disjoint O1 O2 ->
      ((G,E,M1),a,b,O1,d) |= P ->
      ((G,E,M2),a,b,O2,d) |= Q ->
      ((G,E,merge M1 M2),a,b,merge O1 O2,d) |= P ** Q.
  Proof.
    intros.
    simpl in *.
    exists M1 M2 (merge M1 M2) O1 O2 (merge O1 O2).
    mytac.
    apply join_merge_disj;auto.
    apply join_merge_disj;auto.
    auto.
    auto.
  Qed.
  
  eapply merge_star;eauto.
  unfolds;eauto.
  clear Hy.
  sep auto.
  clear -H25.
  simpl in *.
  mytac.
  auto.
  
  assert (i = empisr).
  simpl in Hy.
  mytac.
  subst i;auto.
  unfold SWINVt in H25.
  unfold SWINV in H25.
  assert (i0=true).
  clear -Hy.
  simpl in Hy;mytac.
  subst i0.
  clear -H25.
  simpl in H25;mytac;tryfalse.
  clear -H23.
  simpl in H23;simpl;auto.
  unfolds in H.
  destruct H.
  
  apply H21 in H17.
  mytac.
  eexists;splits;eauto.

  unfolds in H.
  destruct H;auto.

  destruct osc.
  destruct p.
  unfolds get_afun,get_ifun,get_lint.
  simpl fst.
  simpl snd.
  auto.
  
  apply ApiMethSim with (Spec:=Spec) .
  unfolds in Hside.
  destruct Hside;auto.
  apply WFFunEnv_imply_WFFuncsSim;auto.
  eapply bpr'_to_bpr;eauto.

  apply IntMethSim with (Spec:=Spec).
  unfolds in Hside.
  destruct Hside;auto.
  apply WFFunEnv_imply_WFFuncsSim;auto.
  eapply int_bpr'_to_bpr;eauto.
  unfold EqDomInt.
  clear -Heqdomos.
  unfolds in Heqdomos.
  destruct osc.
  destruct p.
  destruct A.
  destruct p1.
  simpl in *.
  mytac.
  auto.
Qed.



Theorem toptheorem:
  forall osc A (init:InitAsrt) (I:Inv) (Spec:funspec) li,
    no_fun_same (get_afun osc)  (get_ifun osc)->
    no_call_api_os (get_afun osc) (get_ifun osc) (get_lint osc) ->
    (forall f t d1 d2 s, (fst (fst osc)) f = Some (t,d1,d2,s) ->
                         good_decllist (revlcons d1 d2) = true /\ GoodStmt' s) ->
    (forall f t d1 d2 s, (snd (fst osc)) f = Some (t,d1,d2,s) ->
                         good_decllist (revlcons d1 d2) = true/\GoodStmt' s) ->
    GoodI I (snd A) li->
    (
      forall i isrreg si p r tid lg,
        Some p = BuildintPre i (snd (fst A)) isrreg si I li tid lg ->
        Some r = BuildintRet i (snd (fst A)) isrreg si I li tid lg ->
        exists s,
          (get_lint osc) i = Some s /\
          {|Spec , (snd A), li, I, retfalse, r|}|-tid {{p}}s {{Afalse}}
      
    )->
    (
      forall (f:fid) ab vl p r ft tid, 
        (fst (fst A)) f = Some (ab,ft) ->
        Some p = BuildPreA' (get_afun osc) f (ab,ft) vl li tid init_lg ->
        Some r = BuildRetA' (get_afun osc) f (ab,ft) vl li tid init_lg ->
        (
          exists  t d1 d2 s,
            (get_afun osc) f = Some (t, d1, d2, s) /\
            InfRules Spec (snd A) li I r Afalse p s Afalse tid
        )
    )->
    WFFunEnv (get_ifun osc) Spec (snd A) li I ->
    (
      eqdomOS osc A /\ 
      side_condition I li (snd A) init init_lg
    )
->
OSCorrect osc A init.
Proof.
  intros.
  eapply toptheorem';eauto.
  intros.
  lets Hx:H5 H8 H9 H10.
  mytac.
  do 4 eexists;splits;eauto.
  unfold get_afun in *.
  lets Hx:H1 H11.
  destruct Hx;auto.
Qed.
   
