Require Import ucos_include.
Require Import os_ucos_h.
Require Import sep_lemmas_ext.
Require Import linv_solver.
Require Import inline_definitions.
Require Import inline_bittblfunctions.
Require Import inline_tactics.
Require Import symbolic_lemmas.
Require Import new_inv.
Require Import protect.
Require Import OSQPostPure.
Local Open Scope code_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.
Local Open Scope list_scope.

Lemma nv'2nv:
  forall vl n x,
    nth_val' n vl = x ->
    x <> Vundef ->
    nth_val n vl = Some x.
Proof.
  induction vl.
  induction n.
  intros.
  simpl in H.
  tryfalse.
  intros.
  simpl in H.
  tryfalse.

  induction n.
  intros.
  simpl in H.
  simpl.
  inverts H.
  auto.
  intros.
  simpl.
  simpl in H.
  apply IHvl.
  auto.
  auto.
Qed.
Lemma intro_or_l:
  forall a b c,
    a ** c ==> (a\\//b)**c.
Proof.
  intros.
  rewrite disj_split.
  left.
  auto.
Qed.
Lemma intro_or_r:
  forall a b c,
    b ** c ==> (a\\//b)**c.
Proof.
  intros.
  rewrite disj_split.
  right.
  auto.
Qed.

Lemma Z_and_onebitmask:
  forall a b,
    0<=b ->
    Z.land a (Z.shiftl 1 b) = Z.shiftl 1 b \/ Z.land a (Z.shiftl 1 b) = 0.
Proof.
  intros.
  
  assert (Z.testbit a b = true \/ Z.testbit a b= false).
  destruct (Z.testbit a b); tauto.
  destruct H0.

  left.
  eapply Byte.equal_same_bits.
  intros.
  rewrite Z.land_spec.

  assert ( b = i \/ b <> i).
  tauto.
  destruct H2.
  subst.
  rewrite H0.
  simpl.
  auto.
  assert (i = (i-b)+b).
  omega.
  rewrite H3 at 2 3.
  rewrite Z.shiftl_spec_alt.
  rewrite Byte.Ztestbit_1.
  assert (i - b <> 0).
  omega.
  remember ( zeq (i - b) 0 ).
  destruct s.
  tryfalse.
  simpl.
  rewrite andb_false_r.
  reflexivity.
  auto.
  
  right.

  eapply Byte.equal_same_bits.
  intros.
  assert (i = (i-b)+b).
  omega.
  rewrite Z.land_spec.
  rewrite H2 at 2 .
  rewrite Z.shiftl_spec_alt.
  rewrite Byte.Ztestbit_1.
  rewrite Byte.Ztestbit_0.
  assert ( i = b \/ i <> b).
  tauto.
  destruct H3.
  subst.
  rewrite H0.
  simpl.
  reflexivity.

  remember ( zeq (i - b) 0 ).
  destruct s.
  assert (i = b).
  omega.
  tryfalse.
  simpl.
  rewrite andb_false_r.
  reflexivity.
  auto.
 
Qed.

Lemma and_onebitmask:
  forall z x ,
    Int.unsigned x <= 7 ->
    z&ᵢ($ 1 <<ᵢ x) = $ 1 <<ᵢ x \/ z&ᵢ($ 1 <<ᵢ x) = $ 0.
Proof.
  intros.
  unfold Int.and.
  unfold Int.shl.
  repeat ur_rewriter.
  Focus 2.
  mauto.
  assert (0 <= Int.unsigned x).
  int auto.

  lets bb: Z_and_onebitmask (Int.unsigned z) (Int.unsigned x) H0.
  destruct bb.
  left.
  rewrite H1.
  auto.
  right.
  rewrite H1.
  auto.
Qed.

Lemma not_prio_in_tbl_is_prio_not_in_tbl:
  forall p rtbl,
    ~prio_in_tbl p rtbl ->
    prio_not_in_tbl p rtbl.
Proof.
  intros.
  unfold prio_in_tbl in H.
  unfold prio_not_in_tbl.
  intros.
  assert (z&ᵢ($ 1 <<ᵢ x) = $ 1 <<ᵢ x \/ z&ᵢ($ 1 <<ᵢ x) = $ 0).
  apply and_onebitmask.
  subst.
  rewrite Int.and_commut.
  eapply Zle_trans.

  apply Int.and_le. 
  clear.
  int auto.

  destruct H3.

  false.
  apply H.
  intros.
  rewrite <- H4 in H0.
  subst.
  rewrite H6 in H2.
  inverts H2.
  auto.
  auto.
Qed.

Lemma join_two_sig_is_false_auto:
  forall (A B T : Type) (MC : PermMap A B T) key v1 v2 m1 m2 m3,
    usePerm = false ->
    join (sig key v1) m2 m3 ->
    join (sig key v2) m1 m2 ->
    False.
  intros.
  let i := calc_ins in
  infer' i key; crush.
Qed.

Lemma join_two_sig_is_false:
  forall key v1 v2 m1 m2 m3,
    TcbMod.join (TcbMod.sig key v1) m2 m3 ->
    TcbMod.join (TcbMod.sig key v2) m1 m2 ->
    False.
  intros.
  assert (join (sig key v1) m2 m3).
  {
    auto.
  }
  assert (join (sig key v2) m1 m2).
  {
    unfold join.
    auto.
  }
  eapply join_two_sig_is_false_auto with (MC := TcbMap).
  eauto.
  exact H1.
  exact H2.
  (** auto type inferrence has big problem with Type Class instant !! **)
Qed.

Lemma tcbjoinsig_unique_auto :
  forall (A B T : Type) (MC : PermMap A B T) key v1 v2 ma ma' m,
    usePerm = false ->
    join (sig key v1) ma m ->
    join (sig key v2) ma' m ->
    ma = ma' /\ v1 = v2.
  intros.
  split.
  hy.
  let l := calc_ins_for_context in
  infer' l key; crush.
Qed.  
  
Lemma tcbjoinsig_unique :
  forall key v1 v2 ma ma' m,
    TcbMod.join (TcbMod.sig key v1) ma m ->
    TcbMod.join (TcbMod.sig key v2) ma' m ->
    ma = ma' /\ v1 = v2.
  intros.
  eapply tcbjoinsig_unique_auto; ica.
Qed.

Lemma Tcblist_p_hold_for_change_headprev:
  forall x1 v'48 x hnleft l v'30 x2 x',
    TCBList_P x1 ((v'48 :: x :: hnleft) :: l) v'30 x2 ->
    TCBList_P x1 ((v'48 :: x' :: hnleft) :: l) v'30 x2.
Proof.
  intros.
  unfold1 TCBList_P in *.
  simpljoin.
  repeat tri_exists_and_solver1.
Qed.

Lemma join_get_none_auto:
  forall (A B T : Type) (MC : PermMap A B T) a b c p,
    usePerm = false ->
    get a p = None ->
    join b c a ->
    get b p= None.
  intros.
  hy.
Qed.
  
Lemma join_get_none:
  forall a b c p,
    EcbMod.get a p = None ->
    EcbMod.join b c a ->
    EcbMod.get b p= None.
Proof.
  intros.
  change (get b p = None).
  eapply join_get_none_auto; ica.
Qed.

Lemma some_join_lemma0_auto:
  forall (A B T : Type) (MC : PermMap A B T) a b c ab bc abc,
    usePerm = false ->
    join a b ab ->
    join c ab abc ->
    join a bc abc ->
    join c b bc.
  intros.
  hy.
Qed.  

Lemma some_join_lemma0:
  forall a b c ab bc abc,
    TcbMod.join a b ab ->
    TcbMod.join c ab abc ->
    TcbMod.join a bc abc ->
    TcbMod.join c b bc.
  intros.
  change (join c b bc).
  eapply some_join_lemma0_auto; eauto.
Qed.

Definition poi_AOSTCBList head tcbmap rtbl hcurt tcbls ptfree :=
  EX tail,
  tcbdllseg head Vnull tail Vnull tcbls **
            GV OSTCBList @ (Tptr OS_TCB) |-> head **
            GV OSTCBCur  @ (Tptr OS_TCB) |-r-> Vptr hcurt **
                                                    [| head <> Vnull |] **
                                                    [| ptr_in_tcbdllseg (Vptr hcurt) head tcbls |] **
                                                    tcbdllflag head tcbls **
                                                    [| TCBList_P head tcbls rtbl tcbmap |] **
                                                    [| Vptr hcurt <> ptfree |] .



Definition poi_OSINV :=
  EX eventl osql qblkl msgql ectrl
     ptbl p1 rtbl rgrp tcbls ecbls tcbmap t ct vhold ptfree lfree,
  AOSEventFreeList eventl ** AOSQFreeList osql ** 
                   AOSQFreeBlk qblkl ** (* free lists *)
                   AECBList ectrl msgql ecbls  tcbmap ** (* msgq *)
                   AOSMapTbl ** AOSUnMapTbl ** AOSTCBPrioTbl ptbl rtbl tcbmap vhold ** 
                   AOSIntNesting ** (* tables *)
                   poi_AOSTCBList p1 tcbmap rtbl ct tcbls ptfree **
                   (* AOSTCBList' p1 p2 tcbl1 (tcbcur::tcbl2) rtbl ct tcbmap ptfree ** *)
                   AOSTCBFreeList' ptfree lfree ct tcbmap**
                   AOSRdyTblGrp rtbl rgrp ** AOSTime (Vint32 t) **(* tcblist & rdy table *)
                   HECBList ecbls ** HTCBList tcbmap ** HTime t ** HCurTCB ct **  AGVars **
                   [| RH_TCBList_ECBList_P ecbls tcbmap ct|] **
                   (* [| RH_CurTCB ct tcbmap|] ** *)
                   A_isr_is_prop.

Lemma tcbdllseg_split' :
  forall l p1 p2 tail2 rtbl tcbls P,
    ptr_in_tcbdllseg p2 p1 l ->
    TCBList_P p1 l rtbl tcbls ->
    tcbdllseg p1 Vnull tail2 Vnull l **
              P
              ==>
              EX l1 l2 tail1 tcbls1 tcbls2,
  tcbdllseg p1 Vnull tail1 p2 l1 **
            tcbdllseg p2 tail1 tail2 Vnull l2 **
            [|l = l1 ++ l2|] **          
            [|TcbMod.join tcbls1 tcbls2 tcbls|] **          
            [|TCBList_P p1 l1 rtbl tcbls1|] **
            [|TCBList_P p2 l2 rtbl tcbls2|] **
            P.
Proof.
  intros.
  eapply tcbdllseg_split.
  sep pauto.
Qed.



Lemma poi_OSINV_imply_OSInv :
  forall Q,
    poi_OSINV ** Q ==> OSInv **Q.
  intro; intros.
  unfold OSInv.
  unfold poi_OSINV in H.
  sep destruct H.
  sep lift 9%nat in H.
  unfold poi_AOSTCBList in H.
  sep normal in H.
  sep destruct H.
  sep split in H.
  eapply tcbdllseg_split' in H.
  2: eauto.
  2 : eauto.

  sep normal in H.
  sep destruct H.
  sep split in H.
  destruct x18.
  unfold tcbdllseg in H.
  unfold1 dllseg in H.
  sep split in H.
  inverts H9.
  sep pauto.
  sep cancel AOSEventFreeList.
  sep cancel AOSQFreeList.
  sep cancel AOSQFreeBlk.
  sep cancel AECBList.
  sep cancel AOSTCBPrioTbl.
  sep cancel AOSTCBFreeList'.
  unfold poi_AOSTCBList in H.
  unfold AOSTCBList'.
  eapply intro_or_l.
  sep cancel AOSRdyTblGrp.
  sep pauto.
  eauto.
  eauto.
  eauto.
Qed.



Lemma dllseg_normal_split:
  forall l1 l2 h hp t tn P,
    tcbdllseg h hp t tn (l1++l2) ** P ==> EX t1 tn1, tcbdllseg h hp t1 tn1 l1 ** tcbdllseg tn1 t1 t tn l2 ** P.
Proof.
  induction l1.
  intros.
  sep pauto.
  simpl in H.
  sep cancel 1%nat 2%nat.
  unfold tcbdllseg.
  unfold dllseg.
  sep pauto.
  intros.
  change ( (a::l1) ++ l2 ) with (a:: (l1 ++ l2)) in H.
  unfold tcbdllseg in *.
  unfold1 dllseg in H.
  sep normal in H.
  sep destruct H.
  unfold1 dllseg.
  sep lift 4%nat in H.
  eapply IHl1 in H.
  sep destruct H.
  sep normal.
  sep pauto.
Qed.

Definition hle2wait a  eid : tcbstats :=
  match a with
      abssem _ => os_stat_sem eid
    | absmsgq _ _ => os_stat_q eid
    | absmbox _ => os_stat_mbox eid
    | absmutexsem _ _ => os_stat_mutexsem eid
  end.

Definition poi_R_ET ecbmap tcbmap :=
  forall eid wls tid hle,
    (get ecbmap eid = Some (hle, wls) /\ In tid wls) ->
    (exists prio msg t, 
       get tcbmap tid = Some (prio, wait (hle2wait hle eid) t, msg)).

(* Definition isWait4Ecb x t :=
 *       x = os_stat_sem t \/ x = os_stat_q t \/ x = os_stat_mbox t \/ x = os_stat_mutexsem t. *)

Definition poi_R_TE ecbmap tcbmap :=
  forall p tid eid t msg waitstat ,
    isWait4Ecb waitstat eid -> 
    get tcbmap tid = Some (p, wait waitstat t, msg) ->
    (exists hle wls,
       get ecbmap eid = Some (hle, wls) /\
       In tid wls /\ hle2wait hle eid = waitstat).


Definition poi_RH_T_E_P ecbmap tcbmap :=
  RH_TCBList_ECBList_MUTEX_OWNER ecbmap tcbmap /\
  poi_R_TE ecbmap tcbmap /\
  poi_R_ET ecbmap tcbmap.

Lemma poi_is_rtep:
  forall a b c,
    poi_RH_T_E_P a b <-> RH_TCBList_ECBList_P a b c.
Proof.
  intros.
  split.
  intros.
  unfolds in H.
  simpljoin.
  unfolds.
  splits.
  {
    unfolds.
    splits; auto.
    {
      intros.
      unfolds in H1.
      lets bb: H1 H2.
      unfold hle2wait in bb.
      auto.
    }
    {
      intros.
      unfolds in H0.
      lets bb: H0 H2.
      unfolds.
      tauto.
      simpljoin.
      unfolds in H5.
      destruct x; tryfalse.
      eauto.
    }
  }
  {
    unfolds.
    splits; auto.
    {
      intros.
      unfolds in H1.
      lets bb: H1 H2.
      unfold hle2wait in bb.
      auto.
    }
    {
      intros.
      unfolds in H0.
      lets bb: H0 H2.
      unfolds.
      tauto.
      simpljoin.
      unfolds in H5.
      destruct x; tryfalse.
      eauto.
    }
  }{
    unfolds.
    splits; auto.
    {
      intros.
      unfolds in H1.
      lets bb: H1 H2.
      unfold hle2wait in bb.
      auto.
    }
    {
      intros.
      unfolds in H0.
      lets bb: H0 H2.
      unfolds.
      tauto.
      simpljoin.
      unfolds in H5.
      destruct x; tryfalse.
      eauto.
    }
  }
  
  {
    unfolds.
    splits; auto.
    {
      intros.
      unfolds in H1.
      lets bb: H1 H2.
      unfold hle2wait in bb.
      auto.
    }
    {
      intros.
      unfolds in H0.
      lets bb: H0 H2.
      unfolds.
      tauto.
      simpljoin.
      unfolds in H5.
      destruct x; tryfalse.
      eauto.
    }
  }

  intros.
  unfolds.
  splits.
  unfolds in H.
  simpljoin.
  unfolds in H2.
  simpljoin.
  auto.
  {
    unfolds.
    intros.
    unfolds in H.
    simpljoin.
    destruct waitstat.
    Focus 3.
    unfolds in H0.
    destruct H0; tryfalse.
    destruct H0; tryfalse.
    destruct H0; tryfalse.

    {
      unfolds in H2.
      simpljoin.
      unfolds in H0.
      destruct H0.
      inverts H0.
      lets bb: H5 H1.
      simpljoin.
      repeat tri_exists_and_solver1.
      destruct H0; tryfalse.
      destruct H0; tryfalse.
    }
    
    {
      unfolds in H.
      simpljoin.
      unfolds in H0.
      destruct H0; tryfalse.
      destruct H0; tryfalse.
      inverts H0.
      lets bb: H5 H1.
      simpljoin.
      repeat tri_exists_and_solver1.
      destruct H0; tryfalse.
    }
    
    {
      unfolds in H3.
      simpljoin.
      unfolds in H0.
      destruct H0; tryfalse.
      destruct H0; tryfalse.
      destruct H0; tryfalse.
      inverts H0.
      lets bb: H5 H1.
      simpljoin.
      repeat tri_exists_and_solver1.
    }
    
    {
      unfolds in H4.
      simpljoin.
      unfolds in H0.
      destruct H0; tryfalse.
      destruct H0; tryfalse.
      destruct H0; tryfalse.
      inverts H0.
      lets bb: H5 H1.
      simpljoin.
      repeat tri_exists_and_solver1.
    }
  }
  
  unfolds.
  intros.
  destruct hle.
  {
    unfolds in H.
    destruct H.
    destruct H1.
    destruct H2.

    unfolds  in H1.
    destruct H1.
    lets bb: H1 H0.
    eauto.
  }
  {
    unfolds in H.
    destruct H.
    destruct H1.
    destruct H2.
    unfolds  in H.
    destruct H.
    lets bb: H H0.
    eauto.
  }
  {
    unfolds in H.
    destruct H.
    destruct H1.
    destruct H2.
    unfolds  in H2.
    destruct H2.
    lets bb: H2 H0.
    eauto.
  }
  {
    unfolds in H.
    destruct H.
    destruct H1.
    destruct H2.
    unfolds  in H3.
    destruct H3.
    lets bb: H3 H0.
    eauto.
  }
Qed.

(* ** ac: Print R_ECB_ETbl_P. *)

(* ** ac: Print RLH_ECB_ETbl_Q_P . *)
(* ** ac: Print PrioWaitInQ. *)
(* ** ac: Print RLH_ECB_ETbl_Q_P . *)
(* ** ac: Print RLH_ECB_ETbl_SEM_P . *)

(* ** ac: Print RLH_ECB_ETbl_P. *)

(* Definition hle2wait a  eid : tcbstats :=
 *   match a with
 *       abssem _ => os_stat_sem eid
 *     | absmsgq _ _ => os_stat_q eid
 *     | absmbox _ => os_stat_mbox eid
 *     | absmutexsem _ _ => os_stat_mutexsem eid
 *   end. *)


Definition hightcbwaitstate_magicnum_match a b:=
  match a with
    | os_stat_sem _ => Some (V$ OS_EVENT_TYPE_SEM) = b
    | os_stat_q _ => Some (V$ OS_EVENT_TYPE_Q ) = b
    | os_stat_mbox _ =>Some (V$ OS_EVENT_TYPE_MBOX) = b
    | os_stat_mutexsem _ =>Some (V$ OS_EVENT_TYPE_MUTEX) =b 
    | _ =>  False
  end.


(* ** ac: Print RLH_ECB_ETbl_P. *)
(* ** ac: Print RLH_ECB_ETbl_Q_P. *)
Definition poi_RLE_HT ecbptr (ecb: os_inv.EventCtr) tcbmap :=
  let (osevent, etcb) := ecb in
  (forall prio :Z,
     PrioWaitInQ prio etcb ->
     exists tid0 n m hwb, get tcbmap tid0 = Some ($ prio, wait hwb n, m) /\
                          hightcbwaitstate_magicnum_match hwb (V_OSEventType osevent) /\
                          isWait4Ecb hwb ecbptr).

(* ** ac: Print RLH_ECB_ETbl_P. *)
(* ** ac: Print RHL_ECB_ETbl_P. *)
(* ** ac: Print RHL_ECB_ETbl_Q_P. *)
(* ** ac: Print R_ECB_ETbl_P. *)

Lemma RLH_ECB_ETbl_P_is_poi:
  forall a b c,
    Event_Type_P (fst b) ->
    RLH_ECB_ETbl_P a b c <-> poi_RLE_HT a b c.
Proof.
  intros.
  split.
  intros.
  unfold RLH_ECB_ETbl_P in H0.
  simpljoin.
  unfolds.
  destruct b.
  intros.
  unfolds in H.
  
  destruct H.
  {
    simpl in H.
    unfolds in H0.
    lets bb: H0 H4 H.
    simpljoin.
    do 4 eexists.
    splits; eauto.
    unfolds.
    auto.
    unfolds.
    tauto.
  }
  
  destruct H.
  {
    simpl in H.
    lets bb: H1 H4 H.
    simpljoin.
    do 4 eexists.
    splits; eauto.
    unfolds.
    auto.
    unfolds.
    tauto.
  }

  
  destruct H.
  {
    simpl in H.
    lets bb: H2 H4 H.
    simpljoin.
    do 4 eexists.
    splits; eauto.
    unfolds.
    auto.
    unfolds.
    tauto.
  }

  {
    simpl in H.
    lets bb: H3 H4 H.
    simpljoin.
    do 4 eexists.
    splits; eauto.
    unfolds.
    auto.
    unfolds.
    tauto.
  }

  intros.
  unfolds in H0.
  destruct b.
  
  unfolds.
  splits.
  {
    unfolds.
    intros.
    lets bb: H0 H1.
    simpljoin.
    unfolds in H4.
    rewrite H2 in H4.
    destruct x2; tryfalse.
    unfolds in H5.
    repeat (destruct H5; tryfalse).
    eauto.
  }
  {
    unfolds.
    intros.
    lets bb: H0 H1.
    simpljoin.
    unfolds in H4.
    rewrite H2 in H4.
    destruct x2; tryfalse.
    unfolds in H5.
    repeat (destruct H5; tryfalse).
    eauto.
  }

  {
    unfolds.
    intros.
    lets bb: H0 H1.
    simpljoin.
    unfolds in H4.
    rewrite H2 in H4.
    destruct x2; tryfalse.
    unfolds in H5.
    repeat (destruct H5; tryfalse).
    eauto.
  }

  {
    unfolds.
    intros.
    lets bb: H0 H1.
    simpljoin.
    unfolds in H4.
    rewrite H2 in H4.
    destruct x2; tryfalse.
    unfolds in H5.
    repeat (destruct H5; tryfalse).
    eauto.
  }

Qed.


(* ** ac: Print RHL_ECB_ETbl_P. *)
(* ** ac: Print RHL_ECB_ETbl_Q_P. *)


Definition poi_RHT_LE ecbptr (ecb: os_inv.EventCtr) tcbmap :=
  let (osevent, etcb) := ecb in
  forall prio m n tid0 hwb,
    get tcbmap tid0 = Some (prio, wait hwb n, m) ->
    isWait4Ecb hwb ecbptr ->
    hightcbwaitstate_magicnum_match hwb (V_OSEventType osevent)  /\
    PrioWaitInQ (Int.unsigned prio) etcb .


Lemma RHL_ECB_ETbl_P_is_poi:
  forall a b c,
    Event_Type_P (fst b) ->
    RHL_ECB_ETbl_P a b c <-> poi_RHT_LE a b c.
Proof.
  intros.
  split.


  intros.
  unfolds in H0.
  simpljoin.
  unfolds in H.
  unfolds.
  destruct b.
  intros.
  destruct H.
  {
    simpl in H.
    unfolds in H5.
    rewrite H .
    
    destruct H5; subst.
    {
      lets bb: H1 H4.
      simpljoin; auto.
      rewrite H in H6; tryfalse.
    }
    destruct H5; subst.
    {
      lets bb: H0 H4.
      simpljoin; auto.
      rewrite H in H6.
      splits; auto.
    }
    destruct H5; subst.
    {
      lets bb: H2 H4.
      simpljoin; auto.
      rewrite H in H6; tryfalse.
    }
    {
      lets bb: H3 H4.
      simpljoin; auto.
      rewrite H in H6; tryfalse.
    }
  }
  destruct H.
  {
    simpl in H.
    unfolds in H5.
    rewrite H .
    
    destruct H5; subst.
    {
      lets bb: H1 H4.
      simpljoin; auto.
      rewrite H in H6; tryfalse.
      splits; auto.
    }
    destruct H5; subst.
    {
      lets bb: H0 H4.
      simpljoin; auto.
      rewrite H in H6.
      tryfalse; splits; auto.
    }
    destruct H5; subst.
    {
      lets bb: H2 H4.
      simpljoin; auto.
      rewrite H in H6; tryfalse.
    }
    {
      lets bb: H3 H4.
      simpljoin; auto.
      rewrite H in H6; tryfalse.
    }
  }
  destruct H.
  {
    simpl in H.
    unfolds in H5.
    rewrite H .
    
    destruct H5; subst.
    {
      lets bb: H1 H4.
      simpljoin; auto.
      rewrite H in H6.
      tryfalse; splits; auto.
    }
    destruct H5; subst.
    {
      lets bb: H0 H4.
      simpljoin; auto.
      rewrite H in H6.
      tryfalse; splits; auto.
    }
    destruct H5; subst.
    {
      lets bb: H2 H4.
      simpljoin; auto.
      rewrite H in H6.
      tryfalse; splits; auto.
    }
    {
      lets bb: H3 H4.
      simpljoin; auto.
      rewrite H in H6.
      tryfalse; splits; auto.
    }
  }
  {
    simpl in H.
    unfolds in H5.
    rewrite H .
    
    destruct H5; subst.
    {
      lets bb: H1 H4.
      simpljoin; auto.
      rewrite H in H6.
      tryfalse; splits; auto.
    }
    destruct H5; subst.
    {
      lets bb: H0 H4.
      simpljoin; auto.
      rewrite H in H6.
      tryfalse; splits; auto.
    }
    destruct H5; subst.
    {
      lets bb: H2 H4.
      simpljoin; auto.
      rewrite H in H6.
      tryfalse; splits; auto.
    }
    {
      lets bb: H3 H4.
      simpljoin; auto.
      rewrite H in H6.
      tryfalse; splits; auto.
    }
  }

  intros.
  unfolds.
  unfolds in H0.
  destruct b.

  splits.
  {
    unfolds.
    intros.
    assert (  hightcbwaitstate_magicnum_match (os_stat_q a) (V_OSEventType v) /\
              PrioWaitInQ (Int.unsigned prio) v0
           ).
    eapply H0; eauto.
    unfolds; auto.
    simpljoin.
    splits; auto.
  }
  {
    unfolds.
    intros.
    assert (  hightcbwaitstate_magicnum_match (os_stat_sem a) (V_OSEventType v) /\
              PrioWaitInQ (Int.unsigned prio) v0
           ).
    eapply H0; eauto.
    unfolds; auto.
    simpljoin.
    splits; auto.
  }
  {
    unfolds.
    intros.
    assert (  hightcbwaitstate_magicnum_match (os_stat_mbox a) (V_OSEventType v) /\
              PrioWaitInQ (Int.unsigned prio) v0
           ).
    eapply H0; eauto.
    unfolds; auto.
    simpljoin.
    splits; auto.
  }
  {
    unfolds.
    intros.
    assert (  hightcbwaitstate_magicnum_match (os_stat_mutexsem a) (V_OSEventType v) /\
              PrioWaitInQ (Int.unsigned prio) v0
           ).
    eapply H0; eauto.
    unfolds; auto.
    simpljoin.
    splits; auto.
  }
Qed.


Definition poi_RLEHT   ecbptr (ecb: os_inv.EventCtr) tcbmap :=
  poi_RHT_LE ecbptr ecb tcbmap /\
  poi_RLE_HT ecbptr ecb tcbmap /\
  Event_Type_P (fst ecb).

(* ** ac: Print ECBList_P. *)
Lemma R_ECB_ETbl_P_is_poi:
  forall a b c,
    R_ECB_ETbl_P a b c <-> poi_RLEHT a b c.
Proof.
  intros.
  split.
  intros.
  unfolds in H.
  unfolds.
  simpljoin.
  rewrite RHL_ECB_ETbl_P_is_poi in H0.
  rewrite RLH_ECB_ETbl_P_is_poi in H.
  tauto.
  tauto.
  auto.
  intros.
  unfolds in H; simpljoin.
  
  unfolds.
  rewrite RHL_ECB_ETbl_P_is_poi .
  rewrite RLH_ECB_ETbl_P_is_poi .
  tauto.
  auto.
  auto.
Qed.

(* Definition isWait4Ecb x t :=
 *       x = os_stat_sem t \/ x = os_stat_q t \/ x = os_stat_mbox t \/ x = os_stat_mutexsem t. *)


(* Definition isWait4Ecb x t :=
 *       x = os_stat_sem t \/ x = os_stat_q t \/ x = os_stat_mbox t \/ x = os_stat_mutexsem t. *)

(* Definition poi_R_TE ecbmap tcbmap :=
 *     forall p tid eid t msg waitstat ,
 *       isWait4Ecb waitstat eid -> 
 *        get tcbmap tid = Some (p, wait waitstat t, msg) ->
 *        (exists hle wls,
 *           get ecbmap eid = Some (hle, wls) /\
 *           In tid wls /\ hle2wait hle eid = waitstat). *)

Lemma TcbIsWait:
  forall x11 v'13 x23 x5 i13 x17 x0 v'30 v'43 ,
    R_TCB_Status_P
      (x11
         :: v'13
         :: x23
         :: x5
         :: Vint32 i13
         :: Vint32 x17
         :: Vint32 v'43
         :: Vint32 (v'43&ᵢ$ 7)
         :: Vint32 (v'43 >>ᵢ $ 3)
         :: Vint32 ($ 1<<ᵢ(v'43&ᵢ$ 7))
         :: Vint32 ($ 1<<ᵢ(v'43 >>ᵢ $ 3)) :: nil)
      v'30 (v'43, x0, x5) ->
    x17 = $ OS_STAT_SEM \/
    x17 = $ OS_STAT_Q \/ x17 = $ OS_STAT_MBOX \/ x17 = $ OS_STAT_MUTEX ->
    exists wt ept, x23 = Vptr ept /\ x0 = wait wt i13 /\ isWait4Ecb wt ept.
Proof.
  intros.
  destruct x0.
  unfolds in H.
  simpljoin.
  
  unfolds in H1.
  simpljoin.
  lets bb: H1 (eq_refl (v'43, rdy, x5)).
  simpljoin.
  inverts H5.
  clear -H0.
  repeat (destruct H0; tryfalse).
  repeat (destruct H; tryfalse).

  unfolds in H.
  simpljoin.
  unfolds in H2.
  simpljoin.


  assert (WaitTCBblk
            (x11
               :: v'13
               :: x23
               :: x5
               :: Vint32 i13
               :: Vint32 x17
               :: Vint32 v'43
               :: Vint32 (v'43&ᵢ$ 7)
               :: Vint32 (v'43 >>ᵢ $ 3)
               :: Vint32 ($ 1<<ᵢ(v'43&ᵢ$ 7))
               :: Vint32 ($ 1<<ᵢ(v'43 >>ᵢ $ 3)) :: nil)

            v'30 v'43 i13
         ).
  unfolds.
  go.
  apply not_prio_in_tbl_is_prio_not_in_tbl.
  intro.
  assert (RdyTCBblk
            (x11
               :: v'13
               :: x23
               :: x5
               :: Vint32 i13
               :: Vint32 x17
               :: Vint32 v'43
               :: Vint32 (v'43&ᵢ$ 7)
               :: Vint32 (v'43 >>ᵢ $ 3)
               :: Vint32 ($ 1<<ᵢ(v'43&ᵢ$ 7))
               :: Vint32 ($ 1<<ᵢ(v'43 >>ᵢ $ 3)) :: nil)
            v'30
            v'43).
  unfolds.
  go.
  lets bb: H H9.
  simpljoin.
  rename H8 into myhyp.

  destruct t.
  Focus 3.
  unfolds in H3.
  simpljoin.
  unfolds in H3.
  lets bb: H3 (eq_refl (v'43, wait os_stat_time i, x5)).
  simpljoin.
  inverts H14.
  clear -H0.
  destruct H0; tryfalse.
  repeat (destruct H; tryfalse).
  {
    unfolds in H3.
    simpljoin.
    unfolds in H8.
    lets bbb: H8 (eq_refl (v'43, wait (os_stat_sem e) i, x5)).
    simpljoin.
    inverts H13.
    inverts H14.
    unfolds in H12.
    simpljoin.
    inverts H14.
    repeat tri_exists_and_solver1.
    unfolds.
    tauto.
  }
  {
    unfolds in H3.
    simpljoin.
    lets bbb: H9 (eq_refl (v'43, wait (os_stat_q e) i, x5)).
    simpljoin.
    inverts H13.
    inverts H14.
    unfolds in H12.
    simpljoin.
    inverts H14.
    repeat tri_exists_and_solver1.
    unfolds.
    tauto.
  }
  {
    unfolds in H3.
    simpljoin.
    lets bbb: H10 (eq_refl (v'43, wait (os_stat_mbox e) i, x5)).
    simpljoin.
    inverts H13.
    inverts H14.
    unfolds in H12.
    simpljoin.
    inverts H14.
    repeat tri_exists_and_solver1.
    unfolds.
    tauto.
  }
  {
    unfolds in H3.
    simpljoin.
    lets bbb: H11 (eq_refl (v'43, wait (os_stat_mutexsem e) i, x5)).
    simpljoin.
    inverts H13.
    inverts H14.
    unfolds in H12.
    simpljoin.
    inverts H14.
    repeat tri_exists_and_solver1.
    unfolds.
    tauto.
  }
Qed.



Lemma dllseg_split_node_tail:
  forall l head headprev tail tailnext a t prev next P,
    dllseg head headprev tail tailnext (a::l) t prev next ** P <==>
           EX tail' l' vl, dllseg head headprev tail' tail l' t prev next ** P ** node tail vl t **
                                  [| a::l = l' ++ vl::nil /\  prev vl = Some tail'  /\next vl = Some tailnext |] .
Proof.
  induction l.
  intros.
  split.
  intros.
  sep pauto.
  unfold1 dllseg in *.
  sep pauto.
  sep cancel node.
  instantiate (1 := nil).
  unfold dllseg.
  sep pauto.
  simpl.
  unfold1 dllseg in H.
  sep normal in H.
  sep destruct H.
  sep split in H.
  splits; auto.
  subst.
  auto.

  intros.
  unfold1 dllseg.
  sep destruct H.
  sep split in H.
  simpljoin.
  assert (x0 = nil).
  clear -H0.
  gen a.
  gen x1.
  induction x0.
  intros.
  auto.
  intros.
  simpl in H0.

  inverts H0.
  false.
  gen x1.
  clear IHx0.
  clear a.
  induction x0.
  intros.
  simpl in H2.
  inverts H2.
  intros.
  simpl in H2.
  inverts H2.
  subst x0.
  simpl in H0.
  inverts H0.
  unfold1 dllseg in H.
  sep split in H.
  unfold node in *.
  sep pauto.
  intro; tryfalse.
  
  intros.
  split.
  intros.
  remember (a::l).
  unfold1 dllseg in H.
  sep normal in H.
  sep destruct H.
  sep split in H.
  sep lift 2%nat in H.
  subst l0.
  apply IHl in H.
  sep pauto.
  sep cancel 3%nat 2%nat.
  2: splits; eauto.
  instantiate (1 := (a0 :: x1)).
  unfold1 dllseg.
  sep pauto.
  simpl.
  rewrite <- H3.
  auto.

  intros.
  remember (a::l).
  unfold1 dllseg.
  sep normal.
  sep destruct H.
  destruct x0.

  sep eexists.
  sep split in H.
  simpljoin.
  inverts H0.
  unfold1 dllseg in H.
  sep normal in H.
  sep destruct H.
  sep split in H.
  sep eexists.
  sep lift 4%nat.
  subst l0.
  rewrite IHl.
  simpljoin.
  simpl in e.
  inverts e.
  sep pauto.
  Grab Existential Variables.
  exact (V$1).
Qed.

Lemma dllseg_tail_not_null:
  forall l head headprev tailnext a t prev next P,
    dllseg head headprev Vnull tailnext (a::l) t prev next ** P ==> Afalse.
Proof.
  induction l.
  intros.
  unfold1 dllseg in H.
  sep normal in H.
  sep destruct H.
  sep split in H.
  apply H4.
  auto.
  intros.
  remember (a::l).
  unfold1 dllseg in H.
  sep normal in H.
  sep destruct H.
  sep split in H.
  sep lift 2%nat in H.
  subst l0.
  eapply IHl.
  eauto.
Qed.


Lemma dllsegflag_split:
  forall l1 l2 head endstnl next P,
    dllsegflag head endstnl (l1++ l2) next ** P<==> EX h2, dllsegflag head h2 l1 next ** dllsegflag h2 endstnl l2 next ** P.
Proof.
  induction l1.
  intros.
  split.
  intros.
  simpl (nil++l2) in H.
  sep pauto.
  sep cancel 1%nat 2%nat.
  unfold dllsegflag.
  sep pauto.
  intros.
  sep destruct H.
  simpl (nil ++ l2).
  unfold1 dllsegflag in H.
  sep split in H.
  subst x.
  auto.


  intros.
  split.
  intros.
  simpl ((a::l1) ++ l2) in H.
  unfold1 dllsegflag in H.
  sep normal in H.
  sep destruct H.
  sep lift 4%nat in H.
  rewrite IHl1 in H.
  sep destruct H.
  sep pauto.
  unfold1 dllsegflag.
  sep pauto.
  sep cancel 3%nat 1%nat.
  eauto.
  auto.
  intros.

  sep destruct H.
  unfold1 dllsegflag in H.
  sep normal in H.
  sep destruct H.
  simpl ((a:: l1) ++ l2).
  unfold1 dllsegflag.
  sep pauto.
  sep lift 2%nat.
  rewrite IHl1.
  sep pauto.
  auto.
Qed.
Lemma dllsegflag_last_next_is_endstnl:
  forall l head endstnl endp next s P,
    s |= dllsegflag head endstnl (l++ (endp :: nil)) next  ** P ->
    next endp = Some endstnl.
Proof.
  induction l.
  intros.
  simpl (nil ++ endp :: nil) in H.
  unfold dllsegflag in H.
  sep normal in H.
  sep destruct H.
  sep split in H.
  subst.
  auto.

  intros.
  simpl ((a ::l ) ++ endp :: nil) in H.
  unfold1 dllsegflag in H.
  
  sep normal in H.
  sep destruct H.
  sep split in H.
  sep lift 2%nat in H.
  eapply IHl.
  eauto.
Qed.


Lemma goodlinv:
  GoodLInvAsrt OSLInv.
Proof.
  unfolds.
  unfold OSLInv.
  intros.
  unfold GoodLocalInvAsrt.
  simpl.
  unfold p_exact.
  splits.
  auto.
  intros.
  unfold satp in *.
  lets bb: H sched.
  lets bb2: H0 sched.
  simpl in bb.
  simpl in bb2.
  simpljoin.
  inverts H7.
  unfold emposabst in *.
  simpljoin.
  splits; auto.
  unfold mapstoval in *.
  simpljoin.
  unfold mapstoval in *.
  unfolds in H10.
  destruct H10; subst.
  simpl in H4, H5.
  simpljoin.
  unfold ptomval in *.
  subst.
  apply join_comm in H1.
  apply join_comm in H2.
  assert (x0 = x7).
  eapply map_join_deter.
  eauto.
  eauto.
  subst x0.
  eapply map_join_deter.
  eauto.
  eauto.

  simpl in H4, H5.
  simpljoin.
  unfold ptomval in *.
  subst.
  apply join_comm in H1.
  apply join_comm in H2.
  assert (x0 = x7).
  eapply map_join_deter.
  eauto.
  eauto.
  subst x0.
  eapply map_join_deter.
  eauto.
  eauto.
Qed.

Lemma RLH_ECBData_irrelevant_wl:
  forall a b c c',
    RLH_ECBData_P a (b,c) ->
    RLH_ECBData_P a (b,remove_tid c' c).
Proof.
  unfold RLH_ECBData_P.
  intros.
  destruct a.
  destruct b; auto.
  simpljoin; splits ; auto.
  Lemma nil_remove_nil :
    forall b,
      remove_tid b nil = nil.
  Proof.
    auto.
  Qed.

  Lemma remove_tid_not_nil:
    forall  b a ,
      remove_tid a b <> nil ->
      b <> nil.
  Proof.
    induction b.
    intros.
    simpl in H.
    auto.
    intros.
    intro.
    inverts H0.
  Qed.

  Hint Resolve nil_remove_nil remove_tid_not_nil:remove_lib.
  Lemma RH_ECB_P_hold_for_remove:
    forall a b c,
      RH_ECB_P (a, b) ->
      RH_ECB_P (a, remove_tid c b).
  Proof.
    unfold RH_ECB_P.
    intros.
    destruct a; simpljoin; splits; eauto with remove_lib.
    intros.
    lets bb: H H1.
    subst.
    simpl; auto.
    intro.
    lets bb: H H1.
    subst; simpl; auto.
    
    intro.
    lets bb: H H1.
    subst; simpl; auto.
    
    intro.
    subst.
    assert (b = nil).
    eapply H.
    auto.
    subst; simpl; auto.
  Qed.

  eapply RH_ECB_P_hold_for_remove; eauto.
  destruct b; tryfalse; 
  simpljoin;
  splits; auto; eapply RH_ECB_P_hold_for_remove; eauto.
  
  destruct b; tryfalse; 
  simpljoin;
  splits; auto; eapply RH_ECB_P_hold_for_remove; eauto.

  destruct b; tryfalse; 
  simpljoin;
  splits; auto; eapply RH_ECB_P_hold_for_remove; eauto.
Qed.

Lemma AED_changegrp:
  forall a grp grp' b c d e f g P,
    AEventData (a:: grp:: b:: c:: d:: e:: f :: nil) g **P  ==>
               AEventData (a:: grp' :: b :: c :: d ::e ::f ::nil) g ** P. 
Proof.
  intros.
  unfold AEventData in *.
  destruct g;
    sep pauto.
Qed.

Lemma app_last:
  forall {T:Type} (l1 l2: list T) d,
    last (l1 ++ l2) d= match l2 with
                         | nil => last l1 d
                         | _ => last l2 d
                       end.
Proof.
  induction l1.
  simpl.
  intros.
  induction l2.
  reflexivity.
  simpl.
  auto.

  intros.
  simpl.
  remember (l1 ++ l2).
  destruct l.
  apply eq_sym in Heql.
  eapply app_eq_nil in Heql.
  simpljoin.
  rewrite Heql.
  rewrite IHl1.
  destruct l1; auto.
  destruct l2.
  tryfalse.
  auto.
Qed.

Fixpoint list_all_P {T:Type} (P: T->Prop) (l: list T)  :=
  match l with
    |nil => True
    | a :: l' => P a /\ list_all_P  P l'
  end.

Lemma ptr_in_tcblist_app:
  forall l1 l2 target head ,
    list_all_P (fun x => V_OSTCBNext x <> None) l1 ->
    ptr_in_tcblist target head (l1 ++ l2) <->
    ptr_in_tcblist target head l1 \/ ptr_in_tcblist target (val_inj (get_last_tcb_ptr l1 head)) l2.
Proof.
  induction l1.
  intros.
  simpl.
  tauto.
  intros.
  simpl ((a::l1) ++ l2).
  rename H into legal_list.
  split.
  intros.
  unfold ptr_in_tcblist in H.
  unfold1 ptr_in_tcbdllseg in H.
  remember (beq_val target head).
  destruct b.
  left.
  simpl.
  rewrite <- Heqb.
  auto.
  unfold ptr_in_tcblist at 1.
  unfold1 ptr_in_tcbdllseg.
  rewrite <- Heqb.
  remember (V_OSTCBNext a).
  destruct o.
  Focus 2.
  tryfalse.
  apply eq_sym in Heqo.
  apply IHl1 in H.
  destruct H.
  tauto.
  right.
(* ** ac:   SearchAbout ptr_in_tcblist. *)
  Lemma get_last_tcb_ptr_cons:
    forall l h hn a,
      V_OSTCBNext a = Some hn ->
      get_last_tcb_ptr (a::l) h = get_last_tcb_ptr l hn.
  Proof.
    intros.
    simpl.
    destruct l.
    simpl.
    auto.
    simpl.
    auto.
  Qed.
(* ** ac:   Show. *)
  rewrite (get_last_tcb_ptr_cons _ _ _ _ Heqo).
  auto.
  unfold1 @list_all_P in legal_list.
  tauto.

  intros.
  destruct H.
  unfold ptr_in_tcblist in *.
  unfold1 ptr_in_tcbdllseg in *.
  remember (beq_val target head).
  destruct b; auto.
  remember (V_OSTCBNext a).
  destruct o; tryfalse.
  apply IHl1.
  unfold1 @list_all_P in legal_list.
  tauto.
  left; auto.

  unfold ptr_in_tcblist in *.
  unfold1 ptr_in_tcbdllseg in *.
  remember (beq_val target head).
  destruct b; auto.
  remember (V_OSTCBNext a).
  destruct o; tryfalse.
  apply IHl1.
  unfold1 @list_all_P in legal_list.
  tauto.
  right.

  apply eq_sym in Heqo.
  rewrite (get_last_tcb_ptr_cons _ _ _ _ Heqo) in H.
  auto.
  unfold1 @list_all_P in legal_list.
  simpljoin.
  tryfalse.
Qed.

Lemma TCBLP_imply_dictinct_list :
  forall l head rtbl tcbmap,
    TCBList_P head l rtbl tcbmap ->
    distinct_tcbdllseg_next_ptr head l.
Proof.
  induction l.
  intros.
  simpl.
  auto.

  intros.
  unfold1 TCBList_P in H.
  simpljoin.
  simpl.
  rewrite H0.
  lets backup: H3.
  apply IHl in H3.
  destruct l.
  auto.
  splits; auto.
  intro.
  Lemma ptr_in_tcbdllseg1_is_normal:
    forall a b c,
      ptr_in_tcbdllseg1 a b c<-> ptr_in_tcbdllseg a b c .
    unfold ptr_in_tcbdllseg1.
    unfold ptr_in_tcbdllseg.
    tauto.
  Qed.

  rewrite ptr_in_tcbdllseg1_is_normal in H.
  Lemma ptr_in_tcbdllseg_TCBList_P_map_join:
    forall tcbls  head rtbl tcbmap ptr,
      TCBList_P head tcbls rtbl tcbmap ->
      ptr_in_tcbdllseg (Vptr ptr) head tcbls ->
      exists aa bb, TcbJoin ptr aa bb tcbmap.
  Proof.
    induction tcbls.
    intros.
    simpl in H0.
    tryfalse.

    intros.
    unfold1 TCBList_P in H.
    simpljoin.
    unfold1 ptr_in_tcbdllseg in H0.
    remember (beq_val (Vptr ptr) (Vptr x)).
    destruct b.
    assert (Vptr ptr = Vptr x).
    apply beq_val_true_eq.
    auto.
    inverts H.
    Focus 2.
    rewrite H1 in H0.
    lets bb: IHtcbls H4 H0.
    simpljoin.
    clear -H2 H.
    unfold TcbJoin in *.
    exists x3.
    assert (exists bb, join x4 (sig x x2) bb).
    join auto.
    simpljoin.
    exists x0.
    join auto.
    eauto.
  Qed.
  lets asdfasfd: ptr_in_tcbdllseg_TCBList_P_map_join backup H.
  simpljoin.
  unfold TcbJoin in *.
  clear -H1 H4.
  unfold join, sig in *; simpl in *.
  eapply join_two_sig_is_false.
  exact H1.
  eauto.
Qed.

Lemma distinct_is_unique_first:
  forall l1 head ptr target l2,
    list_all_P (fun x => V_OSTCBNext x <> None) l1 ->
    distinct_tcbdllseg_next_ptr head (l1++(target :: l2)) ->
    get_last_tcb_ptr l1 head = Some ptr ->
    ~ ptr_in_tcblist ptr head l1 .
Proof.
  induction l1.
  intros.
  simpl.
  auto.
  introv HHHH.

  intros.
  lets backup: H.
  simpl in H.
  remember (l1 ++ target :: l2).
  destruct l; tryfalse.
  false.
  destruct l1 ; tryfalse.
  
  rewrite Heql in *.
  remember (V_OSTCBNext a).
  destruct o.
  simpljoin.
  apply eq_sym in Heqo.

  erewrite  get_last_tcb_ptr_cons in H0.
  2: eauto.

  simpl in HHHH.
  simpljoin.
  lets bbb: IHl1 H3 H1 H0.
  intro.
  unfold ptr_in_tcblist in H4.
  unfold ptr_in_tcbdllseg in H4.
  remember (beq_val ptr head).
  destruct b.
  assert (ptr = head).
  eapply beq_val_true_eq.
  auto.
  subst ptr.
  apply H.
  apply ptr_in_tcblist_app.
  auto.
  rewrite H0.
  simpl.
  right.
  rewrite beq_val_true.
  auto.

  rewrite Heqo in H4.
  fold ptr_in_tcbdllseg in H4.
  apply bbb ; auto.

  unfolds in HHHH.
  simpljoin; tryfalse.
Qed.

Lemma distinct_is_unique_second:
  forall l1 head ptr target l2 l2head,
    list_all_P (fun x => V_OSTCBNext x <> None) l1 ->
    V_OSTCBNext target = Some l2head ->
    distinct_tcbdllseg_next_ptr head (l1++(target :: l2)) ->
    get_last_tcb_ptr l1 head = Some ptr ->
    ~ ptr_in_tcblist ptr l2head l2 .
Proof.
  induction l1.
  introv HHH.
  intros.
  simpl in H1.
  inverts H1.
  simpl in H0.
  destruct l2.
  simpl.
  auto.
  rewrite H in H0.
  simpljoin.
  auto.

  intros.
  simpl in H1.
  unfolds in H.
  fold @list_all_P in H.
  simpljoin.
  remember (V_OSTCBNext a).
  destruct o; tryfalse.
  remember (l1 ++ target :: l2).
  destruct l.
  destruct l1; tryfalse.
  simpljoin.

  erewrite get_last_tcb_ptr_cons in H2.
  2:eauto.
  rewrite Heql in *.
  lets bb: IHl1 H3 H0 H4 H2.
  auto.
Qed.

Lemma tcblist_p_hold_for_del_a_tcb_at_head :
  forall l head hn xx x0 i13 x21 v'53 hleft hnleft v'48 tcbmap_left v'41 v'30 tcbmap  status msg prev,
    0 <= Int.unsigned v'53 < 64 ->
    R_Prio_No_Dup tcbmap ->
    (forall x : int32,
       prio_in_tbl x v'30 ->
       Int.eq x v'53 = false ->
       prio_in_tbl x
                   (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'30
                                   (val_inj
                                      (and (Vint32 v'41) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7)))))))) ->
    nth_val' (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'30 = Vint32 v'41 ->
    TcbMod.join (TcbMod.sig head (v'53, status, msg)) tcbmap_left tcbmap ->
    TCBList_P (Vptr head)
              ((hn :: prev :: xx :: x0 :: i13 :: x21 :: Vint32 v'53 :: hleft)
                 :: (v'48 :: Vptr head :: hnleft) :: l)
              v'30 tcbmap ->
    TCBList_P hn
              ((v'48 :: prev :: hnleft) :: l)
              (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'30
                              (val_inj (and (Vint32 v'41) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7)))))))
              tcbmap_left.
Proof.
  introv HHH.
  intros.


  eapply OSTimeDlyPure.update_rtbl_tcblist_hold.
  auto.
  eapply nv'2nv.
  exact H1.
  intro; tryfalse.
  intros.
  assert ( tid = head \/ tid <> head) by tauto.
  destruct H5.
  subst head.
  intro.
  assert (exists bb, TcbMod.join (sig tid (a,b,c)) bb tcbmap_left).
  clear -H4.
  eapply tcb_get_join.
  auto.
  simpljoin.
  

  eapply join_two_sig_is_false.
  exact H2.
  eauto.

  assert (TcbMod.get tcbmap head = Some (v'53, status, msg)).
  go.
  assert (TcbMod.get tcbmap tid = Some (a, b, c)).
  go.
  lets fff: H H6 H7.
  auto.
  auto.
  
  remember ( (v'48 :: Vptr head :: hnleft) :: l).
  unfold1 TCBList_P in H3.
  simpljoin.
  inverts H4.
  inverts H3.

  
  

  lets bbbb: tcbjoinsig_unique H2 H5.
  simpljoin.

  
  
  eapply Tcblist_p_hold_for_change_headprev.
  eauto.
Qed.


Lemma r_priotbl_p_hold_for_del_a_tcb:
  forall priotbl tcbmap vhold head v'53 status msg tcbmap_left,
    0 <= Int.unsigned v'53 < 64 ->
    length priotbl = 64%nat ->
    R_PrioTbl_P priotbl tcbmap vhold ->
    TcbMod.join (TcbMod.sig head (v'53, status, msg)) tcbmap_left tcbmap ->
    R_PrioTbl_P (update_nth_val (Z.to_nat (Int.unsigned v'53)) priotbl Vnull)
                tcbmap_left vhold.
Proof.
  introv hello kitty.
  protect hello.
  intros.
  unfold R_PrioTbl_P.
  splits.
  intros.
  assert (exists tt,  nth_val (Z.to_nat (Int.unsigned prio)) priotbl = Some tt) as hyp.
  Lemma nth_val_exists:
    forall n vl,
      (n < length vl)%nat ->
      exists a, nth_val n vl = Some a.
  Proof.
    intros n vl.
    gen n.
    induction vl.
    intros.
    simpl.
    simpl in H.
    omega.
    induction n.
    intros.
    simpl; eauto.
    intros.
    simpl.
    eapply IHvl.
    simpl in H.
    omega.
  Qed.


  eapply nth_val_exists.
  rewrite kitty.
  clear -H1.
  mauto.
  destruct hyp as (tt, hyp).
  assert ( head = tcbid \/ head <> tcbid) by tauto.
  destruct H4.
  subst head.
  unfolds in H.
  destruct H.
  destruct H4.
  assert (get tcbmap tcbid = Some (v'53, status, msg)).
  unfold get ; simpl.
  go.
  lets bb: H4  H6.
  simpljoin.
  unfold nat_of_Z in *.
  assert ( v'53 = prio \/ v'53 <> prio) by tauto.
  destruct H10.
  subst v'53.

  
  erewrite hoare_assign.update_nth in H2.
  inverts H2.
  eauto.
  

  erewrite nth_upd_neqrev in H2.
  3: eauto.
  inverts H2.
  assert ( 0<= Int.unsigned prio < 64) by omega.
  lets bbb: H H2 hyp H8.
  rename hello into H11.
  lets bbbb: H H11 H7 H8.
  simpljoin.
  rewrite H13 in H12.
  inverts H12.
  tryfalse.

  Lemma to_nat_unsigned_neq:
    forall a b,
      a<>b ->
      Z.to_nat (Int.unsigned a) <> Z.to_nat (Int.unsigned b).
  Proof.
    intros.
    intro.
    eapply Z2Nat.inj in H0.
    apply H.
    apply unsigned_inj.
    auto.
    clear; int auto.
    clear; int auto.
  Qed.

  eapply to_nat_unsigned_neq.
  auto.


  assert ( v'53 = prio \/ v'53 <> prio) by tauto.
  destruct H5.

  subst v'53.
  erewrite hoare_assign.update_nth in H2.
  inverts H2.
  eauto.
  
  erewrite nth_upd_neqrev in H2.
  3: eauto.
  inverts H2.

  unfolds in H.
  destruct H.
  lets bb: H H1 hyp H3.
  destruct bb.
  destruct H6.
  eapply join_get_or in H6.
  2:auto.
  2:eauto.
  unfold get in H6; simpl in H6.
  destruct H6.
  rewrite TcbMod.get_a_sig_a' in H6.
  inverts H6.
  go.
  eauto.
  unfold nat_of_Z.
  eapply to_nat_unsigned_neq; auto.


  (* part2 *)
  {
    intros.
    unfolds in H.
    simpljoin.
    lets back: H1.
    eapply join_get_r in H1.
    2:auto.
    2: eauto.
    lets bb: H2 H1.
    simpljoin.
    splits; auto.
    assert ( tcbid = head \/ tcbid <> head) by tauto.
    destruct H6.
    false.
    subst head.
    clear -back H0.

(* ** ac:     SearchAbout join. *)
(* ** ac:     Check map_join_get_some. *)
(* ** ac:     Check TcbMod.map_join_get_some. *)
    lets bb: TcbMod.map_join_get_some H0.
    auto.
    apply bb.
    2: exact back.
    go.
    ifsimpl.
    false.
    assert (tidspec.beq tcbid tcbid = true).
    go.
    rewrite H in H1.
    tryfalse.
    


    assert (TcbMod.get tcbmap head = Some (v'53, status, msg)).
    go.
    unfolds in H3.
    lets bbb: H3 H6 H1 H7.
    unfold nat_of_Z.
    erewrite nth_upd_neqrev .
    eauto.
    eapply to_nat_unsigned_neq.
    eauto.
    auto.
  }

  {
    unfolds in H.
    simpljoin.
    unfold R_Prio_No_Dup in *.
    intros.
    eapply join_get_r in H4; eauto.
    eapply join_get_r in H5; eauto.
  }
Qed.

Lemma rtbl_remove_RL_RTbl_PrioTbl_P_hold':
  forall (prio : Z) (y bitx : int32) (rtbl : vallist) 
         (ry : int32) (ptbl : vallist) (av : addrval),
    0 <= prio < 64 ->
    y = $ prio>>ᵢ$ 3 ->
    bitx = $ 1<<ᵢ($ prio&ᵢ$ 7) ->
    nth_val ∘(Int.unsigned y) rtbl = Some (Vint32 ry) ->
    RL_RTbl_PrioTbl_P rtbl ptbl av ->
    RL_RTbl_PrioTbl_P
      (update_nth_val ∘(Int.unsigned y) rtbl (Vint32 (ry&ᵢInt.not bitx)))
      (update_nth_val  (∘prio)  ptbl Vnull)
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
  simpljoin.
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
Definition at_most_once_in_ecbmap ptr ecbmap :=
  forall x y wl x' y' wl',
    EcbMod.get ecbmap x' = Some (y', wl') /\In ptr wl' ->
    EcbMod.get ecbmap x = Some (y, wl) /\ In ptr wl ->
    x' = x .
Lemma at_most_once_lemma:
  forall ecbmap tcbmap ptr, 
    poi_RH_T_E_P ecbmap tcbmap ->
    at_most_once_in_ecbmap  ptr ecbmap.
Proof.
  intros.
  unfolds.
  intros.
  unfolds in H.
  destruct H.
  destruct H2.
  lets bb: H3 H0.
  lets bbb: H3 H1.
  simpljoin.
  rewrite H5 in H4.
  inverts H4.
  unfold hle2wait in H10.
  destruct y'; destruct y; tryfalse; inverts H10; reflexivity.
Qed.


Lemma isw4e_hle2w_same :
  forall a b c,
    isWait4Ecb (hle2wait a b) c ->
    b = c.
Proof.
  unfold isWait4Ecb.
  unfold hle2wait.
  intros.
  destruct a.
  destruct H; tryfalse.
  inverts H.
  auto.

  destruct H; tryfalse.
  destruct H; tryfalse.
  destruct H; tryfalse.
  destruct H; tryfalse.
  inverts H; auto.
  destruct H; tryfalse.
  destruct H; tryfalse.
  destruct H; tryfalse.
  destruct H; tryfalse.
  inverts H; auto.
  destruct H; tryfalse.
  destruct H; tryfalse.
  destruct H; tryfalse.
  inverts H; auto.
Qed.

Lemma priowaitinq_is_prio_in_tbl:
  forall a b z,
    Int.unsigned a < 64 ->
    nth_val ∘ (Int.unsigned ( a >>ᵢ $ 3)) b = Some (Vint32 z) ->
    prio_in_tbl a b <->
    PrioWaitInQ (Int.unsigned a) b .
Proof.
  intros.
  split.
  intros.
  unfolds.
  unfolds in H.
  repeat tri_exists_and_solver1.
  clear.
  int auto.
  int auto.
  eapply H1.
  int auto.
  eauto.
  int auto.
  intros.
  unfolds in H1.
  simpljoin.
  unfolds.
  intros.
  rewrite Int.repr_unsigned in H5.
  subst.
  rewrite H7 in H0.
  inverts H0.

  rewrite Int.repr_unsigned in H4.
  rewrite H4 in H7.
  inverts H7.
  apply H5.
Qed.


Lemma poi_RHT_LE_hold_for_del_tcb:
  forall ecbhead i7 v'28 i8 x29 x30 x4 v'37 tcbmap tcbmap_left x v'53 i13 x0 v'51 v'50 head,
    R_Prio_No_Dup tcbmap ->
    (forall x : int32,
       prio_in_tbl x v'37 ->
       Int.eq x v'53 = false ->
       prio_in_tbl x
                   (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'37
                                   (val_inj
                                      (and (Vint32 v'51) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7)))))))) ->
    TcbMod.join
      (TcbMod.sig head (v'53, wait (hle2wait x ecbhead) i13, x0))
      tcbmap_left tcbmap ->
    poi_RHT_LE ecbhead
               (Vint32 i7 :: Vint32 v'28 :: Vint32 i8 :: x29 :: x30 :: x4 :: nil, v'37)
               tcbmap ->
    poi_RHT_LE ecbhead
               (Vint32 i7 :: Vint32 v'50 :: Vint32 i8 :: x29 :: x30 :: x4 :: nil,
                update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'37
                               (val_inj (and (Vint32 v'51)
                                             (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7)))))))
               tcbmap_left.
Proof.
  introv HHH.
  intros.
  
  remember (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'37
                           (val_inj
                              (and (Vint32 v'51) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7))))))).

  protect Heql.

  unfolds.
  intros.
  unfolds in H1.

  assert (get tcbmap tid0 = Some (prio, wait hwb n, m)).
  unfold get in *; simpl in *.
  go.
  lets bb: H1 H4 H3.
  simpljoin.
  unfold V_OSEventType in *.
  simpl in *.
  splits ;auto.

(* ** ac:   Show. *)
  lets backup: H6.
  unfolds in H6.
  simpljoin.
  Lemma nth_val_upd_exsits:
    forall b a  c aa bb (P: _ -> Prop),
      P c ->
      P bb ->
      nth_val a b = Some c ->
      exists d, nth_val a (update_nth_val aa b bb)  = Some d /\ P d.
  Proof.
    induction b.
    introv HH HHH.
    intros.
    simpl in H.

    inverts H.
    introv HH HHH.
    intros.
    simpl in H.
    destruct a0.
    inverts H.
    simpl.
    destruct aa.
    simpl.
    eauto.

    simpl.
    eauto.

    simpl.
    destruct aa.
    simpl.
    eauto.
    simpl.
    eapply IHb.
    exact HH.
    auto.
    Unshelve.
    auto.
  Qed.


  unprotect Heql.
  subst l.
  assert (exists d, nth_val (Z.to_nat (Int.unsigned (prio>>ᵢ $ 3))) (update_nth_val
                                                                       (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'37
                                                                       (Vint32 (v'51&ᵢInt.not ($ 1<<ᵢ(v'53&ᵢ$ 7)))))
                    = Some d /\ exists pp, d = Vint32 pp).
  eapply nth_val_upd_exsits.
  eauto.
  eauto.
  unfold nat_of_Z in H9.
  rewrite Int.repr_unsigned in H9.
  exact H9.
  simpljoin.

  rewrite Int.repr_unsigned in H9.
  eapply priowaitinq_is_prio_in_tbl.
  auto.
  exact H7.
  eauto.
  rewrite Int.repr_unsigned in *.
  
  eapply H.
  rewrite  priowaitinq_is_prio_in_tbl .
  auto.
  auto.
  eauto.
  
  assert (prio = v'53 \/ prio <> v'53) by tauto.
  destruct H8.
  subst.
  false.
  clear -H0 H2 HHH.
  unfolds in HHH.
  assert ( head = tid0 \/ head <> tid0).
  tauto.
  destruct H.
  subst.
  clear -H2 H0.
  {
    eapply TcbMod.map_join_get_some.
    auto.
    eauto.
    2: eauto.
    apply TcbMod.get_a_sig_a.
    go.
    
  }
  assert (TcbMod.get tcbmap head = Some  (v'53, wait (hle2wait x ecbhead) i13, x0)).
  go.
  assert (TcbMod.get tcbmap tid0 = Some (v'53, wait hwb n, m)).  
  eapply TcbMod.join_get_r.
  eauto.
  auto.
  lets bbb: HHH H H1 H3.
  apply bbb.
  auto.
  
  clear -H8.
  int auto.
  false.
  apply H8.
  apply unsigned_inj.
  auto.
Qed.

Lemma poi_RHTEP_hold_for_del_a_tcb:
  forall ecbmap tcbmap tcbmap_left v'53 x v'15 i13 x0 head x14,
    ~ is_some_mutex_owner head ecbmap ->
    In head x14 ->
    TcbMod.join (TcbMod.sig head
                            (v'53, wait (hle2wait x (v'15, Int.zero)) i13, x0)
                ) tcbmap_left tcbmap ->
    get ecbmap (v'15, Int.zero) = Some (x, x14) ->
    poi_RH_T_E_P ecbmap tcbmap ->
    poi_RH_T_E_P (EcbMod.set ecbmap (v'15, Int.zero)
                             (x, remove_tid head x14)) 
                 tcbmap_left.
Proof.
  introv someHH.
  intros.
  lets backup: H2.

  unfold poi_RH_T_E_P in H2.
  simpljoin.
  splits; auto.
  Focus 2.
  unfold poi_R_TE in *.
  intros.
  assert ( (v'15, Int.zero) = eid \/ (v'15, Int.zero) <> eid) by tauto.
  destruct H7; intros.
  {
    subst.
    rewrite EcbMod.set_a_get_a.
    assert (get tcbmap tid = Some (p, wait waitstat t, msg)).
    go.
    unfold get in *; simpl in *.
    go.
    lets bb: H3 H5 H7.
    simpljoin.

    change  ((fun x =>
                x = Some (x1, x2)) (get ecbmap (v'15, Int.zero))) in H8.
    rewrite H1 in H8.
    inverts H8.
    
    repeat tri_exists_and_solver1.
    assert (head = tid \/ head <> tid) by tauto.
    destruct H8.
    subst head.
    clear -H0 H6.
    false.
(* ** ac:     SearchAbout TcbMod.join. *)
    eapply TcbMod.map_join_get_some.
    auto.
    eauto.
    2: eauto.
    
    go.
(* ** ac:     SearchAbout (tidspec.beq). *)
    rewrite CltEnvMod.beq_refl.
    eauto.
(* ** ac:     SearchAbout In. *)
    rewrite tidneq_inwt_in.
    auto.
    auto.
    go.
  }
  {
    rewrite EcbMod.set_a_get_a'.
    2:go.
    eapply H3.
    auto.
    unfold get in *; simpl in *.
    go.
    
  }
  Unfocus.
  Focus 2.

  lets bb: at_most_once_lemma backup .
  instantiate (TEMP1 := head).
  
  unfold poi_R_ET in *.
  intros.
  clear backup.
  lets backup: H3.
  unfold get in *; simpl in *.
  assert ( (v'15, Int.zero) = eid \/ (v'15, Int.zero) <> eid).
  tauto.
  destruct H6; subst.
  rewrite EcbMod.set_a_get_a in H5.
  simpljoin.
  inverts H5.
  assert (tid = head \/ tid <> head) by tauto.
  destruct H5.
  subst.
(* ** ac:   SearchAbout In. *)
  lets bbbb: in_wtset_rm_notin H.
  tryfalse.
  rewrite tidneq_inwt_in in H6.
  2: auto.
  2:go.

  assert ( EcbMod.get ecbmap (v'15, Int.zero) = Some (hle, x14) /\ In tid x14) by tauto.
  lets bbbb: H4 H7.
  simpljoin.
  eapply TcbMod.join_get_or in H8.
  2: eauto.
  destruct H8.
  rewrite TcbMod.get_a_sig_a' in H8.
  inverts H8.
  go.
  eauto.
  assert ( head = tid \/ head <> tid) by tauto.
  destruct H7.

  rewrite EcbMod.set_a_get_a' in H5.
  2: go.
  assert ( EcbMod.get ecbmap (v'15, Int.zero) = Some (x, x14) /\ In head x14 ).
  tauto.
  unfolds in bb.
  subst head.
  lets bbb : bb H8 H5.
  tryfalse.
  
  rewrite EcbMod.set_a_get_a' in H5.
  2:go.
  lets bbb: H4 H5.
  simpljoin.
  eapply TcbMod.join_get_or in H8.
  2: eauto.
  destruct H8.
  rewrite TcbMod.get_a_sig_a' in H8.
  inverts H8.
  go.
  eauto.

  {
    unfolds.
    intros.
    assert ( eid = (v'15, Int.zero) \/ eid <> (v'15, Int.zero)).
    tauto.
    destruct H6.
    subst.
    {
      unfolds in H2.
      unfold get in *; simpl in *.
      rewrite EcbMod.set_a_get_a in H5.
      inverts H5.
      lets bbb: H2 H1.
      simpljoin.
      eapply TcbMod.join_get_or in H5.
      2:eauto.
      destruct H5.
      assert ( head = tid \/ head <> tid).
      tauto.
      destruct H6.
      subst.
      rewrite TcbMod.get_a_sig_a in H5.
      inverts H5.
      false.
      apply someHH.
      unfolds.
      eauto.
      go.

      rewrite TcbMod.get_a_sig_a' in H5.
      inverts H5.
      go.

      eauto.
      go.
    }

    {
      unfolds in H2.
      unfold get in *; simpl in *.
      rewrite EcbMod.set_a_get_a' in H5.

      lets bb: H2 H5.
      simpljoin.
      eapply TcbMod.join_get_or in H7.
      2:eauto.
      destruct H7.
      assert ( head = tid \/ head <> tid).
      tauto.
      destruct H8.
      subst.
      rewrite TcbMod.get_a_sig_a in H7.
      inverts H5.
      false.
      apply someHH.
      unfolds.
      eauto.
      go.

      rewrite TcbMod.get_a_sig_a' in H7.
      inverts H7.
      go.

      eauto.
      
      go.
    }
  }
  
Qed.

Lemma ECBLP_hold4del_a_tcb:
  forall v'8 x11 i7 v'28 i8 x29 x30 v'6 v'37 x15 x23 x22 x24 ecbmap tcbmap v'53 tcbmap_left v'50 v'51 v'15 i13 x0 x head x14 x25 x26,
    (* at_most_once_in_ecbmap head ecbmap -> *)

    Int.unsigned v'53 < 64 ->
    nth_val' (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'37 = Vint32 v'51 ->
    R_Prio_No_Dup tcbmap ->

    (* Int.unsigned a < 64 ->
     * nth_val ∘ (Int.unsigned ( a >>ᵢ $ 3)) b = Some (Vint32 z) -> *)
    In head x14 ->
    join x25 x26 ecbmap ->
    ECBList_P v'8 (Vptr (v'15, Int.zero)) x11 x23 x25 tcbmap ->
    R_Prio_No_Dup tcbmap ->
    ECBList_P (Vptr (v'15, Int.zero)) Vnull
              ((Vint32 i7 :: Vint32 v'28 :: Vint32 i8 :: x29 :: x30 :: v'6 :: nil,
                v'37) :: x15) (x22 :: x24) x26 tcbmap ->

    get ecbmap (v'15, Int.zero) = Some (x, x14) ->
    ECBList_P v'8 Vnull
              (x11 ++
                   (Vint32 i7 :: Vint32 v'28 :: Vint32 i8 :: x29 :: x30 :: v'6 :: nil,
                    v'37) :: x15) (x23 ++ x22 :: x24) ecbmap tcbmap ->
    RL_Tbl_Grp_P
      (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'37
                      (val_inj
                         (and (Vint32 v'51) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7)))))))
      (Vint32 v'50) ->
    (forall x : int32,
       prio_in_tbl x v'37 ->
       Int.eq x v'53 = false ->
       prio_in_tbl x
                   (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'37
                                   (val_inj
                                      (and (Vint32 v'51) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7)))))))) ->
    TcbMod.join (TcbMod.sig head
                            (v'53, wait (hle2wait x (v'15, Int.zero)) i13, x0)
                ) tcbmap_left tcbmap ->
    ECBList_P v'8 Vnull
              (x11 ++
                   (Vint32 i7 :: Vint32 v'50 :: Vint32 i8 :: x29 :: x30 :: v'6 :: nil,
                    update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'37
                                   (val_inj (and (Vint32 v'51) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7)))))))
                   :: x15) (x23 ++ x22 :: x24)
              (EcbMod.set ecbmap (v'15, Int.zero)
                          (x, remove_tid head x14))
              tcbmap_left.
Proof.
  introv HHHa HHHb.
  intros.
  eapply ecblist_p_compose.
  instantiate (2 := x25).
  instantiate (1 := (set x26 (v'15, Int.zero) (x, remove_tid head x14))).
(* ** ac:   SearchAbout EcbMod.join. *)
  eapply EcbMod.join_set_r.
  assumption.
  clear -H4.
  unfold1 ECBList_P in H4.
  simpljoin.
  unfold TcbJoin in *.
  inverts H.
  unfold join,sig in *; simpl in *.
  unfolds.
  eexists.
  go.

  
  instantiate (1 := (Vptr (v'15, Int.zero))).

  Definition ecb_no_exists_tcb (ecbmap: EcbMod.map)(tcbmap: TcbMod.map) :=
    forall ptr tptr p msg hwb n,
      get tcbmap tptr = Some (p, wait hwb n, msg) ->
      isWait4Ecb hwb ptr ->
      get ecbmap ptr = None.

  Lemma ecblist_p_hold_for_part_tcbmap:
    forall ll ecbmap tcbmap ,
    forall tcbmap_left tcbmap_del head tail hl ,
      join tcbmap_left tcbmap_del tcbmap ->
      ECBList_P head tail ll hl ecbmap tcbmap ->
      ecb_no_exists_tcb ecbmap tcbmap_del ->
      ECBList_P head tail ll hl ecbmap tcbmap_left.
  Proof.
    
    induction ll.
    intros.
    simpl in H0.
    simpljoin.
    simpl.
    auto.

    intros.
    unfold1 ECBList_P in H0.
    simpljoin.
    destruct hl; tryfalse.
    destruct a.
    simpljoin.
    unfold1 ECBList_P.
    repeat tri_exists_and_solver1.
    Focus 2.
    eapply IHll.
    
    eauto.
    eauto.
    unfolds in H3.

(* ** ac:     Print sub. *)
    Lemma ecb_no_exists_tcb_sub:
      forall a b c,
        sub  a b->
        ecb_no_exists_tcb b c ->
        ecb_no_exists_tcb a c.
    Proof.
      intros.
      unfolds in H.
      simpljoin.
      unfold ecb_no_exists_tcb in *.
      intros.
      lets bbb: H0 H1 H2.
      unfold get,join in *; simpl in *.
(* ** ac:       SearchAbout (EcbMod.get _ _ = None). *)

      eapply join_get_none.
      eauto.
      eauto.
    Qed.
(* ** ac:     Show. *)
    eapply ecb_no_exists_tcb_sub.
    2: eauto.
    unfolds.
    apply join_comm in H3.
    eauto.
    
    
    rewrite R_ECB_ETbl_P_is_poi.
    rewrite R_ECB_ETbl_P_is_poi in H2.

    unfold poi_RLEHT in *.
    simpljoin.
    splits; auto.
    unfolds.
    intros.
    eapply H2.
    eapply join_get_l.
    auto.
    eauto.
    eauto.
    auto.

    unfolds.
    intros.
    lets bb: H6 H8.
    simpljoin.
    eapply join_get_or in H9.
    2:auto.
    2: eauto.
    destruct H9.
    repeat tri_exists_and_solver1.

    unfolds in H1.
    lets bbb: H1 H9 H11.
    false.
    unfolds in H3.
    unfold join,sig,get in *; simpl in *.
    clear -H3 bbb.

    erewrite EcbMod.join_get_l in bbb.
    inverts bbb.
    eauto.
    go.
(* ** ac:     SearchAbout (tidspec.beq). *)
    rewrite CltEnvMod.beq_refl.
    eauto.
    
  Qed.
  eapply  ecblist_p_hold_for_part_tcbmap.
  apply join_comm.
  eauto.
  auto.


  {
    unfolds.
    intros.
    assert (head = tptr \/ head <> tptr).
    tauto.
    destruct H12.
    subst.
    unfold get in H10; simpl in H10.
    rewrite TcbMod.get_a_sig_a in H10.
    inverts H10.
    
    lets bb: isw4e_hle2w_same H11.
    inverts bb.
    clear -H4 H1.
    unfold get, join, sig in *; simpl in *.
    simpljoin.
    inverts H.
    unfold get, join, sig in *; simpl in *.
    eapply joinsig_join_getnone.
    exact H3.
    eauto.

    go.

    rewrite TcbMod.get_a_sig_a' in H10.
    inverts H10.
    go.
    
  }

  (* part 2 *)
  {
    unfold1 ECBList_P in H4.
    simpljoin.
    inverts H4.
    inverts H11.
    
    unfold1 ECBList_P .
    assert (x2 = (x, x14)).
    clear -H12 H5 H1.
    unfolds in H12.
    unfold join,sig,get in *; simpl in *.
    assert (EcbMod.get ecbmap (v'15, Int.zero) = Some x2).
    go.
    rewrite H in H5.
    inverts H5.
    reflexivity.
    subst x2.
    eexists.
    splits; eauto.
    Focus 2.

    do 3 eexists.
    splits.
    go.
    instantiate (2 := (x, remove_tid head x14)).
    instantiate (1 := x3).
    {
      unfold TcbJoin in *.
      eapply map_tactics.join_sig_set.
      auto.
      eauto.

    }
    eapply RLH_ECBData_irrelevant_wl.
    auto.
    
    eapply  ecblist_p_hold_for_part_tcbmap.
    apply join_comm.
    exact H9.
    assumption.

    unfolds.
    intros.
    unfold get in *; simpl in *.
    assert (head = tptr \/ head <> tptr) by tauto.
    destruct H15.
    subst.
    rewrite TcbMod.get_a_sig_a in H4.
    inverts H4.

    lets bb: isw4e_hle2w_same H11.
    subst ptr.
    clear -H12.
    {
      unfold sig in *; simpl in *.

      eapply joinsig_get_none.
      eauto.
      
      
    }
    go.
    rewrite TcbMod.get_a_sig_a' in H4.
    inverts H4.
    go.
    

    {
      rewrite R_ECB_ETbl_P_is_poi.
      rewrite R_ECB_ETbl_P_is_poi in H10.
      unfolds in H10.
      
      unfolds.
      splits.
      {
        simpljoin.
        
        eapply  poi_RHT_LE_hold_for_del_tcb.
        go.
        go.
        go.
        go.

      }
      
      {
        simpljoin.
        unfold poi_RLE_HT in *.
(* ** ac:         SearchAbout PrioWaitInQ. *)
        intros.
        simpl in H15.
        assert (prio = Int.unsigned ($ prio)).
        clear -H15.
        unfolds in H15.
        simpljoin.
        clear -H4 H.
        int auto.

        
        rewrite H16 in H15.
        rewrite prio_wt_inq_tid_neq in H15; auto.
        rewrite <- H16 in H15.
        simpljoin.
        lets bb: H10 H15.
        simpljoin.
        unfold V_OSEventType in *.
        simpl in *.
        repeat tri_exists_and_solver1.
        unfold get in *; simpl in *.
        eapply TcbMod.join_get_or in H18.
        2: eauto.
        destruct H18.
        2: eauto.
        assert (head = x1 \/ head <> x1) by tauto.
        destruct H21.
        subst x1.

        rewrite TcbMod.get_a_sig_a in H18.
        inverts H18.
        tryfalse.
        go.

        rewrite TcbMod.get_a_sig_a' in H18.
        inverts H18.
        go.
      }
      simpl.
      simpljoin.
      simpl in H11.
      unfold Event_Type_P in *.
      unfold V_OSEventType in *.
      simpl in *.
      auto.
    }
    
  }
Qed.

Lemma derive_delother_rule:
  forall pa P  prio st msg tls' tls t e tp t1 aop r ri sd Spec I isr ie is cs,
    GoodLInvAsrt pa ->
    GoodFrm P ->
    joinsig t1 (prio, st, msg) tls' tls  ->
    indom tls t ->
    t <> t1 ->
    P ==>  Rv e @ tp == Vptr t1 //\\  CurLINV pa t ->
    InfRules Spec sd pa I r ri 
             (
               <|| spec_del  (Vint32 prio);; aop ||>  **
                   Aabsdata abstcblsid (abstcblist tls) **
                   Aabsdata curtid (oscurt t) **
                   OS[isr, ie, is, cs]  **
                   P
             ) 
             (sprim (stkfree e))
             (
               <|| aop ||>   ** (EX lg,  pa t1 lg)  **
                   Aabsdata abstcblsid (abstcblist tls') ** 
                   Aabsdata curtid (oscurt t) **
                   OS[isr, ie, is, cs] **
                   P
             ) t.
Proof.
  intros.
  eapply backward_rule1.
  instantiate (1:= (
                    <|| spec_del (Vint32 prio);; aop ||> ** P**
                        HTCBList tls ** HCurTCB t ** OS [isr, ie, is, cs] 
                        
                  )).
  intro.
  intros.
  sep pauto.
  eapply forward_rule2.
  eapply delother_rule; eauto.
  intro.
  intro.
  sep pauto.
Qed.
Lemma ptr_in_tcbdllseg_change_head:
  forall target head vl heada heada',
    V_OSTCBNext heada = V_OSTCBNext heada' ->
    ptr_in_tcbdllseg target head (heada::vl) ->
    ptr_in_tcbdllseg target head (heada'::vl) .
Proof.
  intros.
  unfold1 ptr_in_tcbdllseg in *.
  destruct (beq_val target head).
  auto.
  rewrite <- H.
  auto.
Qed.



Lemma ptr_in_tcbdllseg_not_head:
  forall target head vl heada head',
    (val_inj (V_OSTCBNext heada)) = head' ->
    ptr_in_tcbdllseg target head (heada::vl) ->
    target <> head ->
    ptr_in_tcbdllseg target head' vl.
Proof.
  introv HH.
  subst head'.
  intros.
  unfold1 ptr_in_tcbdllseg in H.
  remember (beq_val target head).
  destruct b.
  apply eq_sym in Heqb.
  apply beq_val_true_eq in Heqb.
  tryfalse.
  destruct (V_OSTCBNext heada).
  simpl.
  auto.
  inverts H.
Qed.

Fixpoint poi_llseg {T U:Type} (head tail : T) (l : list U) cond : asrt :=
  match l with
    | nil =>  [| head = tail |]
    | vl :: l' =>
      EX  (head' : T),
      cond head vl head' **
           poi_llseg head' tail l' cond 
  end.

Lemma split_poillseg :
  forall {T U :Type} (l1 l2 : list U) (head tailnext : T) cond P,
    poi_llseg head tailnext (l1 ++ l2) cond ** P<==>
              EX mid,
  poi_llseg head mid l1 cond **
            poi_llseg mid tailnext l2 cond ** P.
Proof.
  induction l1.
  intros.
  splits.
  intros.
  simpl (nil ++ l2) in H.
  sep eexists.
  unfold poi_llseg.
  sep pauto.
  intros.

  simpl (nil ++ l2) .
  sep pauto.
  unfold poi_llseg in H.
  sep pauto.

  split.
  intros.
  simpl  ( (a::l1) ++ l2) in H.
  unfold poi_llseg in H.
  sep normal in H.
  sep destruct H.
  sep split in H.
  sep lift 2%nat in H.
  apply IHl1 in H.
  sep pauto.
  unfold poi_llseg.
  sep pauto.
  sep cancel 3%nat 1%nat.
  sep pauto.
  intro.
  
  simpl  ( (a::l1) ++ l2) .
  unfold poi_llseg.
  sep destruct H.
  unfold poi_llseg in H.
  sep normal in H.
  sep destruct H.
  sep split in H.
  sep normal.
  sep eexists.
  sep split.
  sep lift 2%nat.
  rewrite IHl1.
  sep eexists.
  sep cancel 1%nat 3%nat.
  sep pauto.
Qed.

Lemma dllseg_is_poi :
  forall l head headprev tail tailnext t pre next P,
    ((dllseg head headprev tail tailnext l t pre next)  ** P) <==>
                                                              (poi_llseg (head, headprev) (tailnext, tail) l
                                                                         (fun h vl h' =>
                                                                            let (head, headprev) := h in 
                                                                            let (h', hp' ) := h' in 
                                                                            [| hp' = head /\
                                                                               head <> Vnull /\
                                                                               next vl = Some h' /\
                                                                               pre vl = Some headprev  |] **
                                                                                                          node head vl t 
                                                                         )) ** P .
Proof.
  induction l.
  intros.
  split.
  intros.
  unfold poi_llseg, dllseg in *.
  sep pauto.
  intros.
  
  unfold poi_llseg, dllseg in *.
  sep pauto.
  inverts H0.
  auto.

  inverts H0.
  auto.

  intros.
  split.
  intros.
  unfold1 dllseg in H.
  unfold1 @poi_llseg .
  sep normal.
  sep normal in H.
  sep destruct H.
  sep eexists.
  sep split.
  sep lift 2%nat.
  
  apply IHl.
  sep pauto.
  intros.

  unfold1 @poi_llseg in H.
  unfold1 dllseg .
  sep normal in  H.
  sep destruct H.
  destruct x.
  sep split in H.
  sep pauto.
  eapply StarEmpEL.
  sep lift 2%nat.
  apply IHl.
  sep pauto.
  eauto.        
  auto.
Qed.
Lemma dllsegflag_is_poi :
  forall l head tailnext next P,
    ((dllsegflag head tailnext l next)  ** P) <==>
                                              (poi_llseg head tailnext l
                                                         (fun h vl h' =>
                                                            EX a,
                                                            [|h = Vptr a /\
                                                              next vl = Some h' |] **
                                                                                   PV get_off_addr a ($ 24) @ Int8u |-r-> (V$ 1) 

                                                         )) ** P .
Proof.
  induction l.
  intros.
  split.
  intros.
  unfold poi_llseg, dllsegflag in *.
  sep pauto.
  intros.
  
  unfold poi_llseg, dllsegflag in *.
  sep pauto.

  intros.
  split.
  intros.
  unfold1 dllsegflag in H.
  unfold1 @poi_llseg .
  sep normal.
  sep normal in H.
  sep destruct H.
  sep eexists.
  sep split.
  sep lift 2%nat.
  
  apply IHl.
  sep pauto.
  sep cancel 1%nat 2%nat.
  eauto.
  
  sep split in  H.
  eauto.
  intros.

  unfold1 @poi_llseg in H.
  unfold1 dllsegflag .
  sep pauto.
  eapply StarEmpEL.
  sep lift 2%nat.
  sep cancel 1%nat 1%nat.
  sep lift 2%nat.
  apply IHl.
  sep pauto.
  eauto.        
  auto.
Qed.
Lemma list_all_P_app:
  forall {T:Type} l1 (P : T -> Prop) l2,
    list_all_P P (l1 ++ l2) <-> list_all_P P l1 /\ list_all_P P l2.
Proof.
  induction l1.
  intros.
  split.
  simpl.
  tauto.
  simpl.
  tauto.

  intros.
  splits.
  simpl.
  intros.
  simpljoin.
  rewrite IHl1 in H0.
  tauto.
  simpl.
  intros.
  rewrite IHl1.
  tauto.
Qed.
Lemma TCBLP_imply_nextnotnull_list:
  forall vl head rdytbl tcbmap a,
    TCBList_P head vl rdytbl tcbmap ->
    get_last_tcb_ptr vl Vnull= Some (Vptr a) ->
    list_all_P (fun x10 : vallist => V_OSTCBNext x10 <> None) vl.
Proof.
  induction vl.
  simpl.
  intros.
  auto.
  intros.
  simpl.
  split.
  unfold1 TCBList_P in H.
  simpljoin.
  rewrite H1.
  intro; tryfalse.
  unfold1 TCBList_P in H.
  
  simpljoin.
  
  simpl in H0.
  destruct vl.
  simpl; auto.
  eapply IHvl.
  eauto.
  exact H0.
Qed.



Lemma get_last_tcb_ptr_appsig:
  forall a b c d,
    get_last_tcb_ptr (a ++ (b::c)::nil) d = Some b.
Proof.
  
  induction a.
  simpl.
  intros.
  reflexivity.

  
  intros.

  simpl ((a :: a0) ++ (b :: c) :: nil) .
  remember (a0 ++ (b::c) ::nil).
  simpl.
  destruct l.
  destruct a0.
  inverts Heql.
  inverts Heql.
  unfold get_last_tcb_ptr in IHa.
  lets bbb: IHa b c d.
  rewrite <- Heql in bbb.
  auto.
Qed.
Lemma ptr_in_tcblist_last_ir:
  forall l target head vl vl',
    ptr_in_tcblist target head (l++ (vl::nil)) ->
    ptr_in_tcblist target head (l++ (vl'::nil)) .
Proof.
  induction l.
  simpl.
  intros.
  destruct (beq_val target head); auto.
  destruct (V_OSTCBNext vl); tryfalse.

  intros.
  unfold ptr_in_tcblist in *.
  unfold ptr_in_tcbdllseg in H;
    simpl in H;
    fold ptr_in_tcbdllseg in H.
  simpl.


  destruct (beq_val target head); auto.
  destruct (V_OSTCBNext a); auto.
  eapply IHl.
  eauto.
Qed.

Lemma ptr_in_tcblist_change_first:
  forall l target head vl vl' next,
    ptr_in_tcblist target head ((next ::vl)::l) ->
    ptr_in_tcblist target head ((next ::vl')::l) .
Proof.
  intros.
  unfold ptr_in_tcblist in *.
  unfold ptr_in_tcbdllseg in *.
  auto.
Qed.

Lemma R_Prio_No_Dup_hold_for_subset:
  forall a b c,
    TcbMod.join a b c ->
    R_Prio_No_Dup c ->
    R_Prio_No_Dup a.
Proof.
  intros.
  unfold R_Prio_No_Dup in *.
  intros.
  unfold get in *; simpl in *.
  assert (TcbMod.get c tid =Some (prio, st, m)).
  go.
  assert (TcbMod.get c tid' =Some (prio', st', m')).
  go.
  eapply H0; eauto.
Qed.


Lemma TCBList_P_hold_for_last_change:
  forall head vl next next' last rdytbl tcbmap,
    TCBList_P head (vl++((next::last)::nil)) rdytbl tcbmap ->
    TCBList_P head (vl++((next'::last)::nil)) rdytbl tcbmap.
Proof.
  intros.

(* ** ac:   SearchAbout TCBList_P. *)
  eapply TCBList_P_Split in H.
  simpljoin.
(* ** ac:   SearchAbout TCBList_P. *)
  eapply TCBList_P_Combine.
  eauto.
  eauto.
  eauto.
  unfold1 TCBList_P in *.
  simpljoin.
  repeat tri_exists_and_solver1.
  go.
Qed.



Lemma derive_delself_rule:
  forall pa P  prio st msg tls' tls t e tp  aop r ri sd Spec I isr ie is cs,
    GoodLInvAsrt pa ->
    GoodFrm P ->
    joinsig t (prio, st, msg) tls' tls  ->
    P ==>  Rv e @ tp == Vptr t //\\  CurLINV pa t ->
    InfRules Spec sd pa I r ri 
             (
               <|| spec_del  (Vint32 prio);; aop ||>  **
                   Aabsdata abstcblsid (abstcblist tls) **
                   Aabsdata curtid (oscurt t) **
                   OS[isr, ie, is, cs] ** P
             ) 
             (sprim (stkfree e))
             (
               <|| aop ||>  **
                   Aabsdata abstcblsid (abstcblist tls') ** 
                   Aabsdata curtid (oscurt t) **
                   OS[isr, ie, is, cs]  
                   ** P
             ) t.
Proof.
  intros.
  eapply backward_rule1.
  instantiate (1:= (
                    <|| spec_del (Vint32 prio);; aop ||> ** P**
                        HTCBList tls ** HCurTCB t ** OS [isr, ie, is, cs] 
                        
                  )).
  intro.
  intros.
  sep pauto.
  eapply forward_rule2.
  eapply delself_rule; eauto.
  intro.
  intro.
  sep pauto.
Qed.

