Require Import ucos_include.
Require Import os_ucos_h.
Require Import sep_lemmas_ext.
Require Import linv_solver.
Require Import inline_definitions.
Require Import inline_bittblfunctions.
Require Import inline_tactics.
Require Import symbolic_lemmas.
Require Import new_inv.
Require Import task_pure.
Require Import protect.
Local Open Scope code_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.
Local Open Scope list_scope.
(* Lemma intro_or_l:
 *     forall a b c,
 *       a ** c ==> (a\\//b)**c.
 *   Admitted.
 * Lemma intro_or_r:
 *    forall a b c,
 *      b ** c ==> (a\\//b)**c.
 *  Admitted.
 * 
 * 
 * 
 *       Definition poi_AOSTCBList head tcbmap rtbl hcurt tcbls ptfree :=
 *       EX tail,
 *        tcbdllseg head Vnull tail Vnull tcbls **
 *        GV OSTCBList @ (Tptr OS_TCB) |-> head **
 *        GV OSTCBCur  @ (Tptr OS_TCB) |-r-> Vptr hcurt **
 *        [| head <> Vnull |] **
 *        [| ptr_in_tcbdllseg (Vptr hcurt) head tcbls |] **
 *        tcbdllflag head tcbls **
 *        [| TCBList_P head tcbls rtbl tcbmap |] **
 *        [| Vptr hcurt <> ptfree |] .
 * 
 *     Definition poi_OSINV :=
 *         EX eventl osql qblkl msgql ectrl
 *         ptbl p1 rtbl rgrp tcbls ecbls tcbmap t ct vhold ptfree lfree,
 *                    AOSEventFreeList eventl ** AOSQFreeList osql ** 
 *                    AOSQFreeBlk qblkl ** (* free lists *)
 *                    AECBList ectrl msgql ecbls  tcbmap ** (* msgq *)
 *                    AOSMapTbl ** AOSUnMapTbl ** AOSTCBPrioTbl ptbl rtbl tcbmap vhold ** 
 *                    AOSIntNesting ** (* tables *)
 *                    poi_AOSTCBList p1 tcbmap rtbl ct tcbls ptfree **
 *                    (* AOSTCBList' p1 p2 tcbl1 (tcbcur::tcbl2) rtbl ct tcbmap ptfree ** *)
 *                    AOSTCBFreeList' ptfree lfree ct**
 *                    AOSRdyTblGrp rtbl rgrp ** AOSTime (Vint32 t) **(* tcblist & rdy table *)
 *                    HECBList ecbls ** HTCBList tcbmap ** HTime t ** HCurTCB ct **  AGVars **
 *                    [| RH_TCBList_ECBList_P ecbls tcbmap ct|] **
 *                    (* [| RH_CurTCB ct tcbmap|] ** *)
 *                    A_isr_is_prop.
 *  
 * Lemma tcbdllseg_split' :
 *   forall l p1 p2 tail2 rtbl tcbls P,
 *     ptr_in_tcbdllseg p2 p1 l ->
 *     TCBList_P p1 l rtbl tcbls ->
 *     tcbdllseg p1 Vnull tail2 Vnull l **
 *     P
 *     ==>
 *     EX l1 l2 tail1 tcbls1 tcbls2,
 *     tcbdllseg p1 Vnull tail1 p2 l1 **
 *     tcbdllseg p2 tail1 tail2 Vnull l2 **
 *     [|l = l1 ++ l2|] **          
 *     [|TcbMod.join tcbls1 tcbls2 tcbls|] **          
 *     [|TCBList_P p1 l1 rtbl tcbls1|] **
 *     [|TCBList_P p2 l2 rtbl tcbls2|] **
 *     P.
 *   Proof.
 *     intros.
 *     eapply tcbdllseg_split.
 *     sep pauto.
 *   Qed.
 * 
 *     
 *     
 *     Lemma poi_OSINV_imply_OSInv :
 *       forall Q,
 *           poi_OSINV ** Q ==> OSInv **Q.
 *     intro; intros.
 *     unfold OSInv.
 *     unfold poi_OSINV in H.
 *     sep destruct H.
 *     sep lift 9%nat in H.
 *     unfold poi_AOSTCBList in H.
 *     sep normal in H.
 *     sep destruct H.
 *     sep split in H.
 *     eapply tcbdllseg_split' in H.
 *     2: eauto.
 *     2 : eauto.
 * 
 *     sep normal in H.
 *     sep destruct H.
 *     sep split in H.
 *     destruct x18.
 *     unfold tcbdllseg in H.
 *     unfold1 dllseg in H.
 *     sep split in H.
 *     inverts H9.
 *     sep pauto.
 *     sep cancel AOSEventFreeList.
 *     sep cancel AOSQFreeList.
 *     sep cancel AOSQFreeBlk.
 *     sep cancel AECBList.
 *     sep cancel AOSTCBPrioTbl.
 *     sep cancel AOSTCBFreeList'.
 *     unfold poi_AOSTCBList in H.
 *     unfold AOSTCBList'.
 *     eapply intro_or_l.
 *     sep cancel AOSRdyTblGrp.
 *     sep pauto.
 *     eauto.
 *     eauto.
 *     eauto.
 *   Qed.
 * 
 * 
 * 
 *    Lemma dllseg_normal_split:
 *     forall l1 l2 h hp t tn P,
 *       tcbdllseg h hp t tn (l1++l2) ** P ==> EX t1 tn1, tcbdllseg h hp t1 tn1 l1 ** tcbdllseg tn1 t1 t tn l2 ** P.
 *   Proof.
 *     induction l1.
 *     intros.
 *     sep pauto.
 *     simpl in H.
 *     sep cancel 1%nat 2%nat.
 *     unfold tcbdllseg.
 *     unfold dllseg.
 *     sep pauto.
 *     intros.
 *     change ( (a::l1) ++ l2 ) with (a:: (l1 ++ l2)) in H.
 *     unfold tcbdllseg in *.
 *     unfold1 dllseg in H.
 *     sep normal in H.
 *     sep destruct H.
 *     unfold1 dllseg.
 *     sep lift 4%nat in H.
 *     eapply IHl1 in H.
 *     sep destruct H.
 *     sep normal.
 *     sep pauto.
 *   Qed.
 *  
 *     Definition hle2wait a  eid : tcbstats :=
 *       match a with
 *           abssem _ => os_stat_sem eid
 *         | absmsgq _ _ => os_stat_q eid
 *         | absmbox _ => os_stat_mbox eid
 *         | absmutexsem _ _ => os_stat_mutexsem eid
 *       end.
 * 
 *     Definition poi_R_ET ecbmap tcbmap :=
 *       forall eid wls tid hle,
 *          (get ecbmap eid = Some (hle, wls) /\ In tid wls) ->
 *          (exists prio msg t, 
 *             get tcbmap tid = Some (prio, wait (hle2wait hle eid) t, msg)).
 *  
 * Definition isWait4Ecb x t :=
 *       x = os_stat_sem t \/ x = os_stat_q t \/ x = os_stat_mbox t \/ x = os_stat_mutexsem t.
 *    
 *     Definition poi_R_TE ecbmap tcbmap :=
 *         forall p tid eid t msg waitstat ,
 *           isWait4Ecb waitstat eid -> 
 *            get tcbmap tid = Some (p, wait waitstat t, msg) ->
 *            (exists hle wls,
 *               get ecbmap eid = Some (hle, wls) /\
 *               In tid wls /\ hle2wait hle eid = waitstat).
 * 
 * 
 *     Definition poi_RH_T_E_P ecbmap tcbmap :=
 *       RH_TCBList_ECBList_MUTEX_OWNER ecbmap tcbmap /\
 *       poi_R_TE ecbmap tcbmap /\
 *       poi_R_ET ecbmap tcbmap.
 * 
 *     Lemma poi_is_rtep:
 *       forall a b c,
 *         poi_RH_T_E_P a b <-> RH_TCBList_ECBList_P a b c.
 *     Proof.
 *       intros.
 *       split.
 *       intros.
 *       unfolds in H.
 *       simpljoin.
 *       unfolds.
 *       splits.
 *       {
 *         unfolds.
 *         splits; auto.
 *         {
 *           intros.
 *           unfolds in H1.
 *           lets bb: H1 H2.
 *           unfold hle2wait in bb.
 *           auto.
 *         }
 *         {
 *           intros.
 *           unfolds in H0.
 *           lets bb: H0 H2.
 *           unfolds.
 *           tauto.
 *           simpljoin.
 *           unfolds in H5.
 *           destruct x; tryfalse.
 *           eauto.
 *         }
 *       }
 *       {
 *         unfolds.
 *         splits; auto.
 *         {
 *           intros.
 *           unfolds in H1.
 *           lets bb: H1 H2.
 *           unfold hle2wait in bb.
 *           auto.
 *         }
 *         {
 *           intros.
 *           unfolds in H0.
 *           lets bb: H0 H2.
 *           unfolds.
 *           tauto.
 *           simpljoin.
 *           unfolds in H5.
 *           destruct x; tryfalse.
 *           eauto.
 *         }
 *       }{
 *         unfolds.
 *         splits; auto.
 *         {
 *           intros.
 *           unfolds in H1.
 *           lets bb: H1 H2.
 *           unfold hle2wait in bb.
 *           auto.
 *         }
 *         {
 *           intros.
 *           unfolds in H0.
 *           lets bb: H0 H2.
 *           unfolds.
 *           tauto.
 *           simpljoin.
 *           unfolds in H5.
 *           destruct x; tryfalse.
 *           eauto.
 *         }
 *       }
 *       
 *       {
 *         unfolds.
 *         splits; auto.
 *         {
 *           intros.
 *           unfolds in H1.
 *           lets bb: H1 H2.
 *           unfold hle2wait in bb.
 *           auto.
 *         }
 *         {
 *           intros.
 *           unfolds in H0.
 *           lets bb: H0 H2.
 *           unfolds.
 *           tauto.
 *           simpljoin.
 *           unfolds in H5.
 *           destruct x; tryfalse.
 *           eauto.
 *         }
 *       }
 * 
 *       intros.
 *       unfolds.
 *       splits.
 *       unfolds in H.
 *       simpljoin.
 *       unfolds in H2.
 *       simpljoin.
 *       auto.
 *       {
 *         unfolds.
 *         intros.
 *         unfolds in H.
 *         simpljoin.
 *         destruct waitstat.
 *         Focus 3.
 *         unfolds in H0.
 *         destruct H0; tryfalse.
 *         destruct H0; tryfalse.
 *         destruct H0; tryfalse.
 * 
 *         {
 *           unfolds in H2.
 *           simpljoin.
 *           unfolds in H0.
 *           destruct H0.
 *           inverts H0.
 *           lets bb: H5 H1.
 *           simpljoin.
 *           repeat tri_exists_and_solver1.
 *           destruct H0; tryfalse.
 *           destruct H0; tryfalse.
 *         }
 *  
 *         {
 *           unfolds in H.
 *           simpljoin.
 *           unfolds in H0.
 *           destruct H0; tryfalse.
 *           destruct H0; tryfalse.
 *           inverts H0.
 *           lets bb: H5 H1.
 *           simpljoin.
 *           repeat tri_exists_and_solver1.
 *           destruct H0; tryfalse.
 *         }
 *  
 *         {
 *           unfolds in H3.
 *           simpljoin.
 *           unfolds in H0.
 *           destruct H0; tryfalse.
 *           destruct H0; tryfalse.
 *           destruct H0; tryfalse.
 *           inverts H0.
 *           lets bb: H5 H1.
 *           simpljoin.
 *           repeat tri_exists_and_solver1.
 *         }
 *  
 *         {
 *           unfolds in H4.
 *           simpljoin.
 *           unfolds in H0.
 *           destruct H0; tryfalse.
 *           destruct H0; tryfalse.
 *           destruct H0; tryfalse.
 *           inverts H0.
 *           lets bb: H5 H1.
 *           simpljoin.
 *           repeat tri_exists_and_solver1.
 *         }
 *       }
 *       
 *       unfolds.
 *       intros.
 *       destruct hle.
 *       {
 *         unfolds in H.
 *         destruct H.
 *         destruct H1.
 *         destruct H2.
 * 
 *         unfolds  in H1.
 *         destruct H1.
 *         lets bb: H1 H0.
 *         eauto.
 *       }
 *        {
 *         unfolds in H.
 *         destruct H.
 *         destruct H1.
 *         destruct H2.
 *         unfolds  in H.
 *         destruct H.
 *         lets bb: H H0.
 *         eauto.
 *       }
 *        {
 *         unfolds in H.
 *         destruct H.
 *         destruct H1.
 *         destruct H2.
 *         unfolds  in H2.
 *         destruct H2.
 *         lets bb: H2 H0.
 *         eauto.
 *       }
 *        {
 *         unfolds in H.
 *         destruct H.
 *         destruct H1.
 *         destruct H2.
 *         unfolds  in H3.
 *         destruct H3.
 *         lets bb: H3 H0.
 *         eauto.
 *       }
 *     Qed.
 * 
 * 
 *     Lemma TcbIsWait:
 *       forall x11 v'13 x23 x5 i13 x17 x0 v'30 v'43 ,
 *         R_TCB_Status_P
 *           (x11
 *              :: v'13
 *              :: x23
 *              :: x5
 *              :: Vint32 i13
 *              :: Vint32 x17
 *              :: Vint32 v'43
 *              :: Vint32 (v'43&ᵢ$ 7)
 *              :: Vint32 (v'43 >>ᵢ $ 3)
 *              :: Vint32 ($ 1<<ᵢ(v'43&ᵢ$ 7))
 *              :: Vint32 ($ 1<<ᵢ(v'43 >>ᵢ $ 3)) :: nil)
 *           v'30 (v'43, x0, x5) ->
 *         x17 = $ OS_STAT_SEM \/
 *         x17 = $ OS_STAT_Q \/ x17 = $ OS_STAT_MBOX \/ x17 = $ OS_STAT_MUTEX ->
 *         exists wt ept, x23 = Vptr ept /\ x0 = wait wt i13 /\ isWait4Ecb wt ept.
 *     Proof.
 *       intros.
 *       destruct x0.
 *       unfolds in H.
 *       simpljoin.
 *         
 *       unfolds in H1.
 *       simpljoin.
 *       lets bb: H1 (eq_refl (v'43, rdy, x5)).
 *       simpljoin.
 *       inverts H5.
 *       clear -H0.
 *       repeat (destruct H0; tryfalse).
 *       repeat (destruct H; tryfalse).
 * 
 *       unfolds in H.
 *       simpljoin.
 *       unfolds in H2.
 *       simpljoin.
 * 
 * 
 *       assert (WaitTCBblk
 *                 (x11
 *                    :: v'13
 *                    :: x23
 *                    :: x5
 *                    :: Vint32 i13
 *                    :: Vint32 x17
 *                    :: Vint32 v'43
 *                    :: Vint32 (v'43&ᵢ$ 7)
 *                    :: Vint32 (v'43 >>ᵢ $ 3)
 *                    :: Vint32 ($ 1<<ᵢ(v'43&ᵢ$ 7))
 *                    :: Vint32 ($ 1<<ᵢ(v'43 >>ᵢ $ 3)) :: nil)
 * 
 *                 v'30 v'43 i13
 *              ).
 *       unfolds.
 *       go.
 *       Lemma not_prio_in_tbl_is_prio_not_in_tbl:
 *         forall p rtbl,
 *           ~prio_in_tbl p rtbl ->
 *           prio_not_in_tbl p rtbl.
 *       Proof.
 *         intros.
 *         unfold prio_in_tbl in H.
 *         unfold prio_not_in_tbl.
 *         intros.
 *       Admitted.
 *       apply not_prio_in_tbl_is_prio_not_in_tbl.
 *       intro.
 *       assert (RdyTCBblk
 *                 (x11
 *                    :: v'13
 *                    :: x23
 *                    :: x5
 *                    :: Vint32 i13
 *                    :: Vint32 x17
 *                    :: Vint32 v'43
 *                    :: Vint32 (v'43&ᵢ$ 7)
 *                    :: Vint32 (v'43 >>ᵢ $ 3)
 *                    :: Vint32 ($ 1<<ᵢ(v'43&ᵢ$ 7))
 *                    :: Vint32 ($ 1<<ᵢ(v'43 >>ᵢ $ 3)) :: nil)
 *                 v'30
 *                 v'43).
 *       unfolds.
 *       go.
 *       lets bb: H H9.
 *       simpljoin.
 *       rename H8 into myhyp.
 * 
 *       destruct t.
 *       Focus 3.
 *       unfolds in H3.
 *       simpljoin.
 *       unfolds in H3.
 *       lets bb: H3 (eq_refl (v'43, wait os_stat_time i, x5)).
 *       simpljoin.
 *       inverts H14.
 *       clear -H0.
 *       destruct H0; tryfalse.
 *       repeat (destruct H; tryfalse).
 *       {
 *         unfolds in H3.
 *         simpljoin.
 *         unfolds in H8.
 *         lets bbb: H8 (eq_refl (v'43, wait (os_stat_sem e) i, x5)).
 *         simpljoin.
 *         inverts H13.
 *         inverts H14.
 *         unfolds in H12.
 *         simpljoin.
 *         inverts H14.
 *         repeat tri_exists_and_solver1.
 *         unfolds.
 *         tauto.
 *       }
 *       {
 *         unfolds in H3.
 *         simpljoin.
 *         lets bbb: H9 (eq_refl (v'43, wait (os_stat_q e) i, x5)).
 *         simpljoin.
 *         inverts H13.
 *         inverts H14.
 *         unfolds in H12.
 *         simpljoin.
 *         inverts H14.
 *         repeat tri_exists_and_solver1.
 *         unfolds.
 *         tauto.
 *       }
 *       {
 *         unfolds in H3.
 *         simpljoin.
 *         lets bbb: H10 (eq_refl (v'43, wait (os_stat_mbox e) i, x5)).
 *         simpljoin.
 *         inverts H13.
 *         inverts H14.
 *         unfolds in H12.
 *         simpljoin.
 *         inverts H14.
 *         repeat tri_exists_and_solver1.
 *         unfolds.
 *         tauto.
 *       }
 *       {
 *         unfolds in H3.
 *         simpljoin.
 *         lets bbb: H11 (eq_refl (v'43, wait (os_stat_mutexsem e) i, x5)).
 *         simpljoin.
 *         inverts H13.
 *         inverts H14.
 *         unfolds in H12.
 *         simpljoin.
 *         inverts H14.
 *         repeat tri_exists_and_solver1.
 *         unfolds.
 *         tauto.
 *       }
 *     Qed. *)


Local Ltac sifs := 
  match goal with
    | |- context[if ?e then _ else _] => destruct e; sifs
    | |- _ <> _ => try solve [simpl; intro; tryfalse]
    | _ => idtac
  end.


Lemma absimp_taskdel_prio_invalid:
  forall P v3 sch,
    can_change_aop P ->
    Int.ltu (Int.repr OS_LOWEST_PRIO) v3 = true ->
    (* Int.eq (Int.repr OS_PRIO_SELF) v3 = false -> *)
    absinfer sch ( <|| taskdelcode ((Vint32 v3) :: nil) ||> ** P)
             ( <|| END (Some (Vint32 (Int.repr OS_PRIO_INVALID))) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma absimp_taskdel_prio_is_idle:
  forall P v3 sch,
    can_change_aop P ->
    Int.eq (Int.repr OS_IDLE_PRIO) v3 = true ->
    absinfer sch ( <|| taskdelcode ((Vint32 v3) :: nil) ||> ** P)
             ( <|| END (Some (Vint32 (Int.repr OS_TASK_DEL_IDLE))) ||> ** P).
Proof.
  infer_solver 2%nat.
Qed.


Lemma absimp_taskdel_prio_no_such_tcb:
  forall P v3 sch mqls tls t ct,
    can_change_aop P ->
    (~ exists tid st msg, TcbMod.get tls tid= Some (v3, st, msg))  ->
    absinfer sch ( <|| taskdelcode ((Vint32 v3) :: nil) ||>
 ** HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P)
             ( <|| END (Some (Vint32 (Int.repr OS_TASK_DEL_ERR))) ||>
 ** HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P) .
Proof.
  infer_solver 1%nat.
Qed.

Lemma hl_get_ecb_can_split_ecblist:
  forall l hd tl ecbls hecbls tcbls tid he ,
    EcbMod.get hecbls tid = Some he ->
    ECBList_P hd tl l ecbls hecbls tcbls ->
    exists l1 l2 pt pt2 ecbls1 ecbls2 hecbls1 hecbls2, 
      join hecbls1 hecbls2 hecbls /\
      l = l1 ++ (pt :: l2) /\
      ecbls = ecbls1 ++ (pt2 :: ecbls2) /\
      ECBList_P hd (Vptr tid) l1 ecbls1 hecbls1 tcbls /\ 
      ECBList_P (Vptr tid) tl (pt::l2) (pt2::ecbls2) hecbls2 tcbls.
Proof.
  induction l.
  intros.
  simpl in H0.
  simpljoin.
  false.
  intros.
  unfold1 ECBList_P in H0.
  simpljoin.
  destruct ecbls.
  tryfalse.
  destruct a.
  simpljoin.
  unfold TcbJoin in H2.
  assert (get (sig x x0) tid = Some he \/ get x1 tid = Some he).
  unfold get,sig,join in *; simpl in *.
  eapply  EcbMod.join_get_or.
  exact H2.
  auto.
  destruct H5.
  Focus 2.
  lets bb: IHl H5 H4.
  repeat destruct bb.
  repeat destruct H6.
  exists ( (v,v0) :: x3).
  exists x4.
  exists x5.
  exists x6.
  exists (e::x7).
  exists x8.
  assert (exists bb, join (sig x x0) x9 bb).
  eexists.
  join auto.
  destruct H8.
  exists x11.
  exists x10.
  splits.
  join auto.
  simpl.
  simpljoin.
  simpljoin.
  auto.
  unfold1 ECBList_P.
  simpljoin.
  repeat tri_exists_and_solver1.
  simpljoin; auto.
  cut ( x = tid).
  intro.
  exists (@nil (os_inv.EventCtr)).
  exists l.
  exists (v, v0).
  exists e.
  exists (@nil EventData).
  exists ecbls.
  do 2 eexists.
  splits.
  2:eauto.
  2:eauto.
  2:simpl.
  2:splits; auto.
  instantiate (1:= hecbls).
  join auto.
  Focus 2.
  unfold1 ECBList_P.
  repeat tri_exists_and_solver1.
  subst; auto.
  subst; auto.
  subst; auto.
  
  unfold get,sig,join in *; simpl in *.
  assert (x = tid \/ x <> tid) by tauto.
  destruct H6; auto.
  rewrite EcbMod.get_a_sig_a' in H5.
  inversion H5.
  go.
Qed.

Lemma evsllseg_split:
  forall l1 l1' l2 l2' hd tl  P,
    length l1 = length l1' ->
    evsllseg hd tl (l1 ++ l2) (l1' ++ l2')  ** P ==>
             EX pp, evsllseg hd pp l1 l1' ** evsllseg pp tl l2 l2' ** P.
Proof.
  induction l1.
  intros.
  simpl in H.
  destruct l1'; tryfalse.
  unfold evsllseg at 1.
  sep pauto.
  intros.
  destruct l1'; tryfalse.
  unfold1 evsllseg.
  destruct a.
  sep normal .
  change ( (((v, v0) ::l1 ) ++ l2) ) with ( (v,v0) :: l1++l2) in H0.
  change ( ((e ::l1' ) ++ l2') ) with ( e :: l1'++l2') in H0.
  unfold1 evsllseg in H0.
  sep normal in H0.
  sep destruct H0.
  sep lift 3%nat in H0.
  simpl in H.
  assert (length l1 = length l1') by omega.
  lets bbb: IHl1 H1 H0.
  sep destruct bbb.
  clear H0.
  sep pauto.
Qed.

Lemma ecblistp_evsllseg_tlsame:
  forall ls1 hd tl tl' ls2 hls tcbls P s,
       ECBList_P hd tl ls1 ls2 hls tcbls ->
       s |= evsllseg hd tl' ls1 ls2 ** P ->
       tl  = tl'.
Proof.
  induction ls1.
  intros.
  simpl in H.
  simpljoin.
  unfold evsllseg in H0.
  sep split in H0.
  tauto.
  intros.
  unfold1 ECBList_P in H.
  simpljoin.
  destruct ls2; tryfalse.
  destruct a; simpljoin.
  unfold1 evsllseg in H0.
  sep normal in H0.
  sep destruct H0.
  sep split in H0.
  rewrite H in H5.
  inverts H5.
  eapply IHls1.
  eauto.
  sep lift 2%nat in H0.
  eauto.
Qed.

 
  Lemma OSTCBflag_des:
    forall v'11,
      struct_type_vallist_match OS_TCB_flag v'11 ->
      exists a1 a2 a3 a4 a5 a6 a7 a8 a9 a10,
        exists a11,
        v'11 = (a1::a2::a3::a4::a5::a6::Vint32 a7::a8::a9::a10::a11::nil).
  Proof.
    intros.
    destruct v'11; simpl in H; tryfalse.
    destruct v'11; simpl in H; simpljoin; tryfalse.
    destruct v'11; simpl in H; simpljoin; tryfalse.
    destruct v'11; simpl in *; simpljoin; tryfalse.
    destruct v'11; simpl in *; simpljoin; tryfalse.
    destruct v'11; simpl in *; simpljoin; tryfalse.
    destruct v'11; simpl in *; simpljoin; tryfalse.
    destruct v'11; simpl in *; simpljoin; tryfalse.
    destruct v'11; simpl in *; simpljoin; tryfalse.
    destruct v'11; simpl in *; simpljoin; tryfalse.
    destruct v'11; simpl in *; simpljoin; tryfalse.
    destruct v'11; simpl in *; simpljoin; tryfalse.
    destruct v5; tryfalse.
    repeat tri_exists_and_solver1.
  Qed.
  
Theorem TaskDeleteProof:
  forall  vl p r tid, 
    Some p =
    BuildPreA' os_api OSTaskDel taskdelapi vl  OSLInv tid init_lg ->
    Some r =
    BuildRetA' os_api OSTaskDel taskdelapi vl  OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api OSTaskDel = Some (t, d1, d2, s) /\
      {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-tid {{p}}s {{Afalse}}.
Proof.
  init_spec.
  hoare unfold.
  hoare forward.
  math simpls.
  sifs.
  
  hoare unfold.
  hoare abscsq.
  apply noabs_oslinv.
  eapply absimp_taskdel_prio_is_idle.
  go.
  (* left. *)
  change OS_IDLE_PRIO with 63 in *.
  int auto.
  hoare forward.
  hoare forward.
  hoare unfold.
  hoare forward.
  math simpls.
  sifs.
  math simpls.
  sifs.
  sifs.
  (* math simpls.
   * sifs.
   * sifs.
   * sifs. *)
  hoare unfold.
  hoare abscsq.
  apply noabs_oslinv.
  eapply absimp_taskdel_prio_invalid.
  go.
  change OS_LOWEST_PRIO with 63 in *.
  change OS_IDLE_PRIO with 63 in *.
  change OS_PRIO_SELF with 255 in *.
  int auto.
  destruct H.
  inversion H.
  inversion H.
  hoare forward.
  (* change OS_LOWEST_PRIO with 63 in *.
   * change OS_IDLE_PRIO with 63 in *.
   * change OS_PRIO_SELF with 255 in *.
   * int auto.
   * false.
   * apply H0.
   * simpl.
   * change  (Int.ltu Int.zero Int.zero) with false.
   * change  (Int.ltu Int.zero Int.one) with true.
   * simpl.
   * change  (Int.ltu Int.zero Int.one) with true.
   * change  (Int.ltu Int.zero (Int.notbool Int.one)) with false.
   * simpl.
   * auto.
   * hoare forward. *)

  hoare forward.
  hoare unfold.
  hoare forward prim.
  hoare unfold.
  unfold AOSTCBList.
  hoare normal pre.
  hoare_split_pure_all.
  unfold1 tcbdllseg.
  unfold1 dllseg.
  unfold node.
  hoare normal pre.
  hoare_split_pure_all.
  simpljoin.
  inverts H12.
(* ** ac:   Check OSTCBflag_des. *)
                               
  lets bb: OSTCBflag_des H16.
  simpljoin.
                              
  (* hoare forward. *)
  
  (* math simpls.
   * sifs.
   * hoare forward.
   * auto.
   * hoare forward.
   * clear -H12.
   * simpl in H12; simpljoin; auto.
   * clear -H12.
   * simpl in H12.
   * simpljoin.
   * clear -H5.
   * destruct x5; tryfalse.
   * simpl.
   * sifs.
   * 
   * instantiate (Goal4 := Afalse).
   * hoare unfold.
   * hoare abscsq.
   * apply noabs_oslinv.
   * {
   *   eapply   absimp_taskdel_prio_is_idle.
   *   go.
   *   clear -H8.
   *   right.
   *   remember (Int.eq i ($ OS_PRIO_SELF)).
   *   destruct b.
   *   clear -Heqb.
   *   unfold OS_PRIO_SELF in *.
   *   
   *   int auto.
   *   simpl in H8.
   *   tryfalse.
   * }
   * hoare forward prim.
   * unfold AOSTCBList.
   * unfold1 tcbdllseg.
   * unfold1 dllseg.
   * unfold node.
   * sep pauto.
   * sep cancel 2%nat 1%nat.
   * do 3 sep cancel 2%nat 1%nat.
   * eauto.
   * go.
   * go.
   * go.
   * go.
   * go.
   * splits; auto.
   * go.
   * 
   * hoare forward.
   * Set Printing Depth 999.
   * Show.
   * assert (exists cur_prio, x5 = Vint32 cur_prio).
   * clear -H12.
   * unfolds in H12; simpl in H12; simpljoin.
   * destruct x5; tryfalse.
   * eauto.
   * simpljoin.
   * 
   * 
   * eapply backward_rule1.
   * intro.
   * intros.
   * Check OS_PRIO_SELF.
   *   instantiate (p := EX prio_to_del,
   *                ( 
   *     Astruct (v'27, Int.zero) OS_TCB_flag
   *       (x :: x0 :: x1 :: x2 :: x3 :: x4 :: Vint32 x10 :: x6 :: x7 :: x8 :: x9 :: nil) **
   *     dllseg v'26 (Vptr (v'27, Int.zero)) v'23 Vnull v'13 OS_TCB_flag
   *       V_OSTCBPrev V_OSTCBNext **
   *     GV OSTCBList @ OS_TCB ∗ |-> v'9 **
   *     dllseg v'9 Vnull v'22 (Vptr (v'27, Int.zero)) v'11 OS_TCB_flag
   *       V_OSTCBPrev V_OSTCBNext **
   *     GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (v'27, Int.zero) **
   *     AOSEventFreeList v'3 **
   *     AOSQFreeList v'4 **
   *     AOSQFreeBlk v'5 **
   *     AECBList v'7 v'6 v'16 v'17 **
   *     AOSMapTbl **
   *     AOSUnMapTbl **
   *     AOSTCBPrioTbl v'8 v'14 v'17 v'19 **
   *     AOSIntNesting **
   *     AOSTCBFreeList v'20 v'21 **
   *     AOSRdyTblGrp v'14 v'15 **
   *     AOSTime (Vint32 v'18) **
   *     HECBList v'16 **
   *     HTCBList v'17 **
   *     HTime v'18 **
   *     HCurTCB (v'27, Int.zero) **
   *     AGVars **
   *     A_isr_is_prop **
   *     tcbdllflag v'9
   *       (v'11 ++
   *        (x
   *         :: x0 :: x1 :: x2 :: x3 :: x4 :: Vint32 x10 :: x6 :: x7 :: x8 :: x9 :: nil)
   *        :: v'13) **
   *     p_local OSLInv (v'27, Int.zero) init_lg **
   *      <|| taskdelcode (Vint32 i :: nil) ||>  **
   *     Aisr empisr **
   *     Aie false **
   *     Ais nil **
   *     Acs (true :: nil) **
   *     atoy_inv' **
   *     LV os_code_defs.x @ OS_TCB ∗ |-> v'2 **
   *     LV self @ Int8u |-> v'1 **
   *     LV ptcb @ OS_TCB ∗ |-> v'0 **
   *     LV pevent @ OS_EVENT ∗ |-> v' **
   *     LV prio @ Int8u |-> Vint32 prio_to_del **
   *     A_dom_lenv
   *       ((prio, Int8u)
   *        :: (pevent, OS_EVENT ∗)
   *           :: (ptcb, OS_TCB ∗)
   *              :: (self, Int8u) :: (os_code_defs.x, OS_TCB ∗) :: nil)) 
   *                 **
   *                 [| Int.unsigned prio_to_del < OS_LOWEST_PRIO |] **
   *                 [| i = $ OS_PRIO_SELF /\ prio_to_del = x10 \/ i = prio_to_del|]
   *             ).
   * 
   * destruct H8.
   * sep split in H8.
   * destruct H8.
   * sep split in H8.
   * simpl in H8.
   * inversion H8.
   * sep pauto.
   * sep cancel 2%nat 1%nat.
   * repeat sep cancel 1%nat 1%nat.
   * assumption.
   * left.
   * splits; auto.
   * clear -H13.
   * unfold OS_PRIO_SELF in *.
   * assert ( i = $255 \/ i <> $255).
   * tauto.
   * destruct H; auto.
   * false.
   * apply H13.
   * clear H13.
   * int auto.
   * false.
   * apply H.
   * SearchAbout (Int.unsigned _ = Int.unsigned _).
   * apply unsigned_inj.
   * exact e.
   * clear -H7 H15.
   * unfold1 TCBList_P in H7.
   * simpljoin.
   * unfolds in H2.
   * destruct x13; destruct p.
   * simpljoin.
   * inverts H4.
   * unfolds in H5.
   * simpljoin.
   * inverts H4.
   * clear -H15 H20.
   * 
   * 
   * unfold OS_IDLE_PRIO in *.
   * unfold OS_LOWEST_PRIO in *.
   * destruct H15; tryfalse.
   * unfold val_eq in H.
   * int auto.
   * unfold val_eq in H.
   * int auto.
   * 
   * sep pauto.
   * (* right. *)
   * (* splits; auto. *)
   * clear -H0 H13.
   * destruct H0.
   * unfold OS_LOWEST_PRIO in *.
   * unfold OS_PRIO_SELF in *.
   * int auto.
   * destruct H13; tryfalse.
   * destruct (Int.ltu ($ OS_LOWEST_PRIO) i); destruct ( Int.eq i ($ OS_LOWEST_PRIO)); destruct (Int.eq i ($ OS_PRIO_SELF)); simpl in H; tryfalse.
   * (* clear -H0 H13.
   *  * destruct H0.
   *  * unfold OS_LOWEST_PRIO in *.
   *  * unfold OS_PRIO_SELF in *.
   *  * int auto.
   *  * destruct H13; tryfalse.
   *  * destruct (Int.ltu ($ OS_LOWEST_PRIO) i); destruct ( Int.eq i ($ OS_LOWEST_PRIO)); destruct (Int.eq i ($ OS_PRIO_SELF)); simpl in H; tryfalse.
   *  * 
   *  * destruct (Int.ltu ($ OS_LOWEST_PRIO) i); destruct ( Int.eq i ($ OS_LOWEST_PRIO)); destruct (Int.eq i ($ OS_PRIO_SELF)); simpl in H; tryfalse. *)
   * clear H H0.
   * inverts H9.
   * inverts H10.
   * clear H11. *)
  
  hoare unfold.
  assert (Int.unsigned i < 64).
  clear -H0.
  change OS_LOWEST_PRIO with 63 in *.
  int auto.
  destruct H0;
  tryfalse.
  assert (Int.unsigned i <> 63).
  clear -H.
  change OS_IDLE_PRIO with 63 in *.
  destruct H; int auto.
  clear H H0.
  rename H13 into H.
  rename H14 into H0.
  

  unfold  OS_LOWEST_PRIO in *.
  assert (   rule_type_val_match OS_TCB ∗ (nth_val' (Z.to_nat (Int.unsigned i)) v'8) = true).
  eapply symbolic_lemmas.array_type_vallist_match_imp_rule_type_val_match.
  rewrite H7.
  clear -H.
  mauto.
  auto.

  hoare forward.
  math simpls.
  assumption.
  
  assert (exists t , TcbMod.get v'17 ((v'28, Int.zero)) = Some (x5, t, x2)).
  unfold1 TCBList_P in H11.
  simpljoin.
  unfolds in H18.
  destruct x11; destruct p.
  simpljoin.
  inverts H20.
  unfolds in H22; simpl in H22.
  inverts H18.
  inverts H11.
  unfold join,sig,get in *; simpl in *.
  unfold join,sig,get in *; simpl in *.
  eexists.
  go.
  destruct H14 as (hello & kitty).
  protect kitty.
 
  hoare forward.
  (* math simpls. *)
  (* assumption. *)
  (* clear -
   * bsimplr.
   * 
   * lets backup: H7.
   * (******)
   * unfold1  TCBList_P in H7.
   * simpljoin.
   * unfolds in H15.
   * destruct x11; destruct p.
   * simpljoin.
   * inverts H24; inverts H26; inverts H9; inverts H7.
   * assert ((if Int.unsigned p <=? Byte.max_unsigned then true else false) = true ).
   * simpl in H12.
   * simpljoin.
   * assumption.
   * math simpl in H7.
   * unfolds in H27.
   * simpljoin.
   * inverts H37; inverts H9; inverts H30; inverts H26; inverts H29; inverts H24; inverts H27.
   * assert (   rule_type_val_match OS_TCB ∗ (nth_val' (Z.to_nat (Int.unsigned x)) v'7) = true).
   * eapply symbolic_lemmas.array_type_vallist_match_imp_rule_type_val_match.
   * rewrite H19.
   * clear -H39.
   * mauto.
   * auto. *)
  (*  unfolds in H9.
   *  remember ( nth_val' (Z.to_nat (Int.unsigned x)) v'7 ).
   *  destruct v; tryfalse.
   *  false.
   *  {
   *  
   *    clear -H17 H10 H5 H9 Heqv.
   *    unfolds in H17.
   *    simpljoin.
   *    assert (get v'16 (v'26, Int.zero) = Some (x, t, m)).
   *    unfold join, sig, get in *; simpl in *.
   *    unfold join, sig, get in *; simpl in *.
   *    go.
   *    lets bb: H0 H2.
   *    simpljoin.
   *    unfold nat_of_Z in H3.
   *    Lemma nv'2nv:
   *      forall vl n x,
   *        nth_val' n vl = x ->
   *        x <> Vundef ->
   *        nth_val n vl = Some x.
   *    Proof.
   *      induction vl.
   *      induction n.
   *      intros.
   *      simpl in H.
   *      tryfalse.
   *      intros.
   *      simpl in H.
   *      tryfalse.
   * 
   *      induction n.
   *      intros.
   *      simpl in H.
   *      simpl.
   *      inverts H.
   *      auto.
   *      intros.
   *      simpl.
   *      simpl in H.
   *      apply IHvl.
   *      auto.
   *      auto.
   *    Qed.
   *    assert (  nth_val' (Z.to_nat (Int.unsigned x)) v'7 = Vnull) as H9.
   *    auto.
   *    
   *    apply nv'2nv in H9.
   *    rewrite H9 in H3.
   *    tryfalse.
   *    intro; tryfalse.
   * } *)

  (* assert ( (exists a, nth_val' (Z.to_nat (Int.unsigned v'10)) v'8 = Vptr a )\/ nth_val' (Z.to_nat (Int.unsigned v'10)) v'8 = Vnull).
   * 
   * unfolds in H14.
   * destruct ( nth_val' (Z.to_nat (Int.unsigned v'10)) v'8 ); tryfalse.
   * right; reflexivity.
   * left. 
   * eauto 2. *)
  (* destruct H15; simpljoin; rewrite H15. *)
  
  (* hoare forward. *)
  (* unfolds in H14. *)
  (* clear -H14. *)
  destruct ( nth_val' (Z.to_nat (Int.unsigned i)) v'8 ); tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  unfold val_eq in H17.
  destruct a; tryfalse.
  
  hoare unfold.
  hoare abscsq.

  apply noabs_oslinv.
  eapply absimp_taskdel_prio_no_such_tcb.
  go.
  {
    intro.
    apply H14.
    destruct H13.
    Focus 2.
    simpljoin.
    rewrite H13.
    simpl.
    destruct x11.
    reflexivity.
    false.
    simpljoin.
    unfolds in H6.
    simpljoin.
    lets bb: H20 H19.
    simpljoin.
    unfold nat_of_Z in H22.
    apply nv'2nv in H13.
    rewrite H13 in H22.
    inverts H22.
    intro; tryfalse.
  }

  hoare forward prim.
  unfold AOSTCBPrioTbl.
  unfold AOSTCBList.
  sep pauto.
  sep cancel tcbdllflag.
  sep cancel 4%nat 1%nat.
  
  unfold tcbdllseg.
  unfold1 dllseg.
  sep pauto.
  unfold node.
  sep pauto.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat .
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  eauto.
  go.
  go.
  go.
  go.
  go.
  go.
  go.
  hoare forward.
  hoare forward.
  hoare_split_pure_all.

  
  (* destruct H14; simpljoin.
   * rewrite H.
   * auto.
   * 
   * rewrite H.
   * auto.
   * unfolds in H9.
   * clear -H9.
   * destruct H9; simpljoin.
   * rewrite H.
   * simpl;intro;tryfalse.
   * 
   * rewrite H.
   * simpl;intro;tryfalse.
   * destruct x0; tryfalse.
   * hoare unfold.
   * false.
   * {
   *   clear -H17 H10 H5 H9 H24.
   *   unfolds in H17.
   *   simpljoin.
   *   assert (get v'16 (v'26, Int.zero) = Some (x, t, m)).
   *   unfold join, sig, get in *; simpl in *.
   *   unfold join, sig, get in *; simpl in *.
   *   go.
   *   lets bb: H0 H2.
   *   simpljoin.
   *   unfold nat_of_Z in H3.
   *   Lemma nv'2nv:
   *     forall vl n x,
   *       nth_val' n vl = x ->
   *       x <> Vundef ->
   *       nth_val n vl = Some x.
   *   Proof.
   *     induction vl.
   *     induction n.
   *     intros.
   *     simpl in H.
   *     tryfalse.
   *     intros.
   *     simpl in H.
   *     tryfalse.
   * 
   *     induction n.
   *     intros.
   *     simpl in H.
   *     simpl.
   *     inverts H.
   *     auto.
   *     intros.
   *     simpl.
   *     simpl in H.
   *     apply IHvl.
   *     auto.
   *     auto.
   *   Qed.
   * 
   *   unfolds in H9.
   *   destruct H9.
   *   apply nv'2nv in H6.
   *   rewrite H6 in H3.
   *   inverts H3.
   *   intro;tryfalse.
   *   simpljoin.
   *   rewrite H6 in H24.
   *   simpl in H24.
   *   destruct x0.
   *   simpl in H24; tryfalse.
   *   
   * }
   * instantiate (1:= Afalse).
   * unfolds in H9.
   * destruct H9.
   * {
   *   false.
   *   clear -H17 H10 H5 H9 .
   *   unfolds in H17.
   *   simpljoin.
   *   assert (get v'16 (v'26, Int.zero) = Some (x, t, m)).
   *   unfold join, sig, get in *; simpl in *.
   *   unfold join, sig, get in *; simpl in *.
   *   go.
   *   lets bb: H0 H2.
   *   simpljoin.
   *   unfold nat_of_Z in H3.
   *   apply nv'2nv in H9.
   *   rewrite H9 in H3.
   *   inverts H3.
   *   intro; tryfalse.
   * }
   * simpljoin. *)

  
  (* hoare forward. *)
  unfold os_task.PlaceHolder.
  hoare unfold.
  assert (exists p, (nth_val' (Z.to_nat (Int.unsigned i)) v'8) = Vptr p).
  clear -H13 H14.
  destruct H14.
  unfolds in H13.
  
  destruct (nth_val' (Z.to_nat (Int.unsigned i)) v'8); tryfalse.
  destruct H13; tryfalse.
  assumption.
  destruct (nth_val' (Z.to_nat (Int.unsigned i)) v'8); tryfalse.
  destruct a; simpl in H.
  tryfalse.
  clear H13 H14.
  simpljoin.
  rewrite H13.
  
  eapply seq_rule.
  {
    eapply ift_rule''.
    intro.
    intros.
    eapply symbolic_lemmas.bop_rv.
    sep_get_rv.
    eapply symbolic_lemmas.addrof_gvar_rv.
    gen_notin_lenv H14 OSPlaceHolder.
    eapply symbolic_lemmas.dom_lenv_imp_notin_lenv.
    eauto.
    sep cancel A_dom_lenv.
    sep cancel Agvarenv'.
    eauto.
    eauto.
    simpl.
    destruct x; destruct v'19.
    destruct ( Int.eq i0 i1 ); destruct (peq b b0); simpl; intro; tryfalse.
    simpl.
    eauto.
    hoare unfold.
    instantiate (1:=Afalse).
    hoare abscsq.
    apply noabs_oslinv.
    eapply   absimp_taskdel_prio_no_such_tcb.
    go.
    {
      intro.
      apply H14.
      assert ( x <> v'19 \/ x = v'19).
      tauto.
      destruct H20.
      simpl.
      destruct x; destruct v'19.
      remember (peq b b0).
      destruct s.
      subst.
(* ** ac:       SearchAbout (Int.eq ). *)
      rewrite Int.eq_false.
      reflexivity.
      intro; tryfalse.
      reflexivity.
      subst x.
      simpl.
      false.
      simpljoin.
      unfolds in H6.
      simpljoin.
      lets bb: H20 H19.
      simpljoin.
      unfold nat_of_Z in H22.
      apply nv'2nv in H13.
      rewrite H13 in H22.
      inverts H22.
      apply H23; reflexivity.
      intro; tryfalse.
    }
    hoare forward prim.
    unfold AOSTCBPrioTbl.
    unfold AOSTCBList.
    sep pauto.
    sep cancel tcbdllflag.
    sep cancel 4%nat 1%nat.
    
    unfold tcbdllseg.
    unfold1 dllseg.
    unfold node.
    sep pauto.
    sep cancel 2%nat 1%nat.
    sep cancel 2%nat 1%nat .
    sep cancel 2%nat 1%nat.
    sep cancel 2%nat 1%nat.
    eauto.
    go.
    go.
    go.
    go.
    go.
    go.
    go.
    hoare forward.
  }

  (********)




  
  hoare forward.
  hoare unfold.
  (**********************)
  (* last is H15 *)
  hoare forward.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aisr.
  
  sep cancel Aop.
  sep cancel AECBList.
  sep cancel tcbdllflag.
  sep cancel AOSRdyTblGrp.
  unfold AOSTCBList.
  unfold AOSTCBPrioTbl.
  sep pauto.
  sep cancel 5%nat 1%nat.
  unfold tcbdllseg.
  unfold1 dllseg.
  sep pauto.
  unfold node.
  sep pauto.
  sep cancel dllseg.
  sep cancel Astruct.
  sep cancel 2%nat 1%nat.
  eauto.
  go.
  go.
  go.
  go.
  go.
  go.
  go.
  go.
  go.

Lemma retpost_issomemutexowner: 
  retpost OS_IsSomeMutexOwnerPost.
Proof.
  unfolds.
  intros.
  unfold getasrt in H.
  unfold  OS_IsSomeMutexOwnerPost in H.
  unfold  OS_IsSomeMutexOwnerPost' in H.
  sep normal in H.
  sep destruct H.
  sep split in H.
  destruct H4.
  simpljoin.
  intro; tryfalse.
  simpljoin.
  intro; tryfalse.
Qed.


exact retpost_issomemutexowner. (* retpost*)
  intro;intros.
  linv_solver.
  linv_solver.
  unfold OS_IsSomeMutexOwnerPost.
  unfold getasrt.
  unfold OS_IsSomeMutexOwnerPost'.
  hoare unfold.
  apply eq_sym in H20.
  inverts H20.
  destruct H21.
  Focus 2.
  (* is some mutex owner *)
  simpljoin.
  inverts H18.
  hoare forward.
  change (Int.eq ($ 1) ($ 1)) with true.
  (* simpl; intro; tryfalse. *)
  hoare unfold.
  instantiate (1:=Afalse).
  hoare abscsq.
  apply noabs_oslinv.
  
  
Lemma absimp_taskdel_some_mutex_owner:
  forall P v3 sch mqls tls t ct tid ,
    can_change_aop P ->
    (exists x y z w tt mm , TcbMod.get tls tid = Some (v3, tt, mm) /\ EcbMod.get mqls x = Some (absmutexsem y (Some (tid, z)), w)) ->
    absinfer sch ( <|| taskdelcode ((Vint32 v3) :: nil) ||>
 ** HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P)
             ( <|| END (Some (Vint32 (Int.repr  OS_TASK_DEL_SOME_MUTEX_OWNER))) ||>
 ** HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P) .
Proof.
  intros.
  simpljoin.
  infer_solver 3%nat.
Qed.
eapply absimp_taskdel_some_mutex_owner.
go.
unfolds in H20.
instantiate (1 := (v'40)).
simpljoin.
{
  assert (v'40 <> v'19) as some_pure.
  clear -H14.
  intro.
  subst.
  simpl in H14.
  destruct v'19; simpl in H14.
  rewrite peq_true in H14.
  rewrite Int.eq_true in H14.
  simpl in H14.
  destruct H14; tryfalse.
  unfolds in H6.
  simpljoin.
  unfold nat_of_Z in H6.
  assert (0 <= Int.unsigned i < 64).
  clear -H.
  int auto.
  apply nv'2nv in H13.
  lets bb: H6 H25 H13 some_pure.
  simpljoin.
  repeat tri_exists_and_solver1.
  intro; tryfalse.
}
hoare forward prim.
eauto.
go.
hoare forward.
hoare forward.
hoare unfold.
false.
clear -H18.
int auto.
destruct H18; tryfalse.
simpljoin.
inverts H18.
rename H20 into some_pure_hyp.

hoare forward.
change (Int.eq ($ 0) ($ 1)) with false.
(* simpl; intro;tryfalse. *)
hoare unfold.
false.
clear -H18.
int auto.
instantiate (1:=Afalse).
hoare forward.
hoare unfold.
clear H18.

(**********************)




  
  
  Lemma valinjbopevallemma:
    forall x v'19, val_inj (bop_eval (Vptr x) (Vptr v'19) OS_TCB ∗ (Int8u) ∗ oeq) =
        Vint32 Int.zero \/
        val_inj (bop_eval (Vptr x) (Vptr v'19) OS_TCB ∗ (Int8u) ∗ oeq) =
        Vnull -> x <> v'19.
  Proof.
    intros.
    destruct H.
    simpl in H.
    destruct x; destruct v'19.
    intro.
    inverts H0.
    rewrite peq_true in H.
    rewrite Int.eq_true in H.
    inverts H.
    simpl in H.
    destruct x; destruct v'19.
    destruct (peq b b0); destruct (Int.eq i i0); tryfalse.
  Qed.

  apply valinjbopevallemma in H14.
  unfold AOSTCBList.
  hoare unfold.
  (* change (dllseg v'26 (Vptr (v'27, Int.zero)) v'23 Vnull v'13 OS_TCB_flag
   *                (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) ) with (tcbdllseg v'26 (Vptr (v'27, Int.zero)) v'23 Vnull v'13).
   * change (dllseg v'9 Vnull v'22 (Vptr (v'27, Int.zero)) v'11 OS_TCB_flag
   *                (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) ) with (tcbdllseg v'9 Vnull v'22 (Vptr (v'27, Int.zero)) v'11). *)
  rename v'19 into vhold.
  rename v'28 into cur_tcb_blk.
  rename v'17 into tcbmap.
  rename v'8 into priotbl.
  rename v'40 into todelptr.
  assert (exists st m, TcbMod.get tcbmap todelptr = Some (i, st, m)). 
  unfolds in H6.
  simpljoin.
  apply H6.
  splits.
  clear; int auto.
  omega.
  unfold nat_of_Z.
  eapply nv'2nv.
  assumption.
  intro; tryfalse.
  assumption.
  simpljoin.
  rename v'13 into l2.
  rename v'11 into l1.
  remember  (v'27
         :: v'23
            :: x1
               :: x2 :: x3 :: x4 :: Vint32 x5 :: x6 :: x7 :: x8 :: x9 :: nil) as tcbcur.
  protect Heqtcbcur.

  eapply backward_rule1.
  intro.
  intros.
  Set Printing Depth 999.
(* ** ac:   Show. *)

  instantiate (1 := (
                     [|ptr_in_tcbdllseg (Vptr (cur_tcb_blk, Int.zero)) v'9 (l1++ tcbcur::l2)|] **
                    tcbdllseg v'9 Vnull v'12 Vnull (l1++tcbcur::l2) **
                    [|TCBList_P v'9 (l1++tcbcur::l2) v'14 tcbmap|] **
            <|| taskdelcode (Vint32 i :: nil) ||>  **
                    GV OSTCBList @ OS_TCB ∗ |-> v'9 **
           (* tcbdllseg v'9 Vnull v'10 (Vptr (cur_tcb_blk, Int.zero)) l1 ** *)
           GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
           (* tcbdllseg (Vptr (cur_tcb_blk, Int.zero)) v'10 v'12 Vnull
            *   (tcbcur :: l2) ** *)
           Aie false **
           Ais nil **
           Acs (true :: nil) **
           Aisr empisr **
           AECBList v'7 v'6 v'16 tcbmap **
           tcbdllflag v'9 (l1 ++ tcbcur :: l2) **
           AOSRdyTblGrp v'14 v'15 **
           AOSTCBPrioTbl priotbl v'14 tcbmap vhold **
           HECBList v'16 **
           HTCBList tcbmap **
           HCurTCB (cur_tcb_blk, Int.zero) **
           A_isr_is_prop **
           p_local OSLInv (cur_tcb_blk, Int.zero) init_lg **
           LV self @ Int8u |-> (V$ 0) **
           LV ptcb @ OS_TCB ∗ |-> Vptr todelptr **
           AOSEventFreeList v'3 **
           AOSQFreeList v'4 **
           AOSQFreeBlk v'5 **
           AOSMapTbl **
           AOSUnMapTbl **
           AOSIntNesting **
           AOSTCBFreeList v'20 v'21 **
           AOSTime (Vint32 v'18) **
           HTime v'18 **
           AGVars **
           atoy_inv' **
           LV os_code_defs.x @ OS_TCB ∗ |-> v'2 **
           LV pevent @ OS_EVENT ∗ |-> v' **
           LV prio @ Int8u |-> Vint32 i **
           A_dom_lenv
             ((prio, Int8u)
              :: (pevent, OS_EVENT ∗)
                 :: (ptcb, OS_TCB ∗)
                    :: (self, Int8u) :: (os_code_defs.x, OS_TCB ∗) :: nil)
                   )).
           (*  <|| taskdelcode (Vint32 i :: nil) ||>  **
            * LV ptcb @ OS_TCB ∗ |-> Vptr v'41 **
            * (* PV vhold @ Int8u |-> x5 ** *)
            * (* Astruct (cur_tcb_blk, Int.zero) OS_TCB_flag tcbcur ** *)
            * (* tcbdllseg v'26 (Vptr (cur_tcb_blk, Int.zero)) v'23 Vnull l2 ** *)
            * GV OSTCBList @ OS_TCB ∗ |-> v'9 **
            * (* tcbdllseg v'9 Vnull v'22 (Vptr (cur_tcb_blk, Int.zero)) l1 ** *)
            * GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
            * AOSEventFreeList v'3 **
            * AOSQFreeList v'4 **
            * AOSQFreeBlk v'5 **
            * AECBList v'7 v'6 v'16 tcbmap **
            * AOSMapTbl **
            * AOSUnMapTbl **
            * (* GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64) priotbl ** *)
            * (* G& OSPlaceHolder @ Int8u == vhold ** *)
            * AOSTCBPrioTbl priotbl v'14 tcbmap vhold **
            * AOSIntNesting **
            * AOSTCBFreeList v'20 v'21 **
            * AOSRdyTblGrp v'14 v'15 **
            * AOSTime (Vint32 v'18) **
            * HECBList v'16 **
            * HTCBList tcbmap **
            * HTime v'18 **
            * HCurTCB (cur_tcb_blk, Int.zero) **
            * AGVars **
            * A_isr_is_prop **
            * tcbdllflag v'9 (l1 ++ tcbcur :: l2) **
            * p_local OSLInv (cur_tcb_blk, Int.zero) init_lg **
            * Aisr empisr **
            * Aie false **
            * Ais nil **
            * Acs (true :: nil) **
            * atoy_inv' **
            * LV os_code_defs.x @ OS_TCB ∗ |-> v'2 **
            * LV self @ Int8u |-> (V$ 0) **
            * LV pevent @ OS_EVENT ∗ |-> v' **
            * LV prio @ Int8u |-> Vint32 v'10 **
            * A_dom_lenv
            *   ((prio, Int8u)
            *    :: (pevent, OS_EVENT ∗)
            *       :: (ptcb, OS_TCB ∗)
            *          :: (self, Int8u) :: (os_code_defs.x, OS_TCB ∗) :: nil)
            *         )). *)
  eapply tcbdllseg_combine.
  sep pauto.
  sep cancel 1%nat 1%nat.
  sep cancel 1%nat 1%nat.
  sep cancel tcbdllflag.
  sep cancel Aop.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aisr.
  assumption.
  (* sep cancel Aop.
   * sep cancel Aop.
   * unfold1 tcbdllseg.
   * unfold tcbdllseg in H17.
   * unfold1 dllseg.
   * sep pauto.
   * sep cancel 3%nat 2%nat.
   * unfold node.
   * sep pauto.
   * sep cancel 2%nat 1%nat.
   * repeat sep cancel 1%nat 1%nat.
   * assumption.
   * intro; tryfalse.
   * unprotect Heqtcbcur; inverts Heqtcbcur; go.
   * unprotect Heqtcbcur; inverts Heqtcbcur; go. *)
  go.
  go.
  go.

  hoare_split_pure_all.
  assert (ptr_in_tcbdllseg (Vptr todelptr) v'9 (l1++tcbcur ::l2)).
  Lemma tcbget_ptr_in_tcblist:
     forall tcblst head rtbl tcbmap x xx,
      TCBList_P head tcblst rtbl tcbmap ->
      get tcbmap x = Some xx ->
      ptr_in_tcbdllseg (Vptr x) head tcblst.
  Proof.
    induction tcblst.
    intros.
    simpl in H.
    subst tcbmap.
(* ** ac:     SearchAbout (get empenv _ = _). *)
    rewrite map_emp_get in H0.
    inverts H0.
    intros.
    unfold1 ptr_in_tcbdllseg.
    remember (beq_val (Vptr x) head).
    destruct b.
    auto.
    unfold1 TCBList_P in H.
    simpljoin.
    rewrite H1.
    eapply IHtcblst.
    exact H4.
    assert ( x <> x0).
    intro.
    subst x0.
(* ** ac:     SearchAbout beq_val. *)
    rewrite beq_val_true in Heqb.
    tryfalse.
    unfold join,get,sig in *; simpl in *.
    eapply TcbMod.join_get_or in H2.
    destruct H2; eauto.
    rewrite TcbMod.get_a_sig_a' in H2.
    inverts H2.
    go.
    eauto.
  Qed.

  eapply tcbget_ptr_in_tcblist.
  eauto.
  eauto.
  eapply backward_rule1.
  intro.
  intros.
  eapply tcbdllseg_split' in H27.
  eauto.
  exact H26.
  eauto.
  clear Heqtcbcur.
  remember (l1  ++ tcbcur :: l2) as tcblst.
  protect Heqtcblst.
  hoare unfold.
  clear dependent v'29.
  clear dependent v'30.
  (*v*)
  destruct v'11.
  simpl.
  unfold tcbdllseg.
  simpl.
  hoare unfold.
  inverts H20.

  unfold tcbdllseg.
  unfold1 dllseg .
  unfold node.
  hoare_split_pure_all.
  simpljoin .
  inverts H20.
  rename v'29 into todelblock.
  hoare unfold.
  hoare forward.
  (* intro; tryfalse. *)
  go.
  clear -H20.
  destruct H20; subst; simpl; intro; tryfalse.
  simpljoin; subst; tryfalse.
  simpl in H0.
  destruct x; tryfalse.
  hoare unfold.

  
Lemma absimp_taskdel_prio_HAS_NO_NEXT:
  forall P v3 sch mqls tls t ct,
    can_change_aop P ->
    absinfer sch ( <|| taskdelcode ((Vint32 v3) :: nil) ||>
 ** HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P)
             ( <|| END (Some (Vint32 (Int.repr OS_TASK_DEL_HAS_NO_NEXT))) ||>
 ** HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P) .
Proof.
  infer_solver 4%nat.
Qed.

  hoare abscsq.
  apply noabs_oslinv.
  {
    apply absimp_taskdel_prio_HAS_NO_NEXT.
    go.
  }
  remember
(v'28
            :: v'13
               :: x22
                  :: x21
                     :: Vint32 i13
                        :: Vint32 i12
                           :: Vint32 i11
                              :: Vint32 i10
                                 :: Vint32 i9
                                    :: Vint32 i8 :: Vint32 i7 :: nil) 
   as todelblk.
  rename v'11 into l2'.
  rename v'8 into l1'.
  eapply backward_rule1.
  intro.
  intros.
  Set Printing Depth 999.
(* ** ac:   Show. *)
  instantiate (1:= (
                     [|ptr_in_tcbdllseg (Vptr (todelblock, Int.zero)) v'9 (l1'++ todelblk::l2')|] **
                    tcbdllseg v'9 Vnull v'12 Vnull (l1'++todelblk::l2') **
                    [|TCBList_P v'9 (l1'++todelblk::l2') v'14 tcbmap|] **
<|| END Some (V$ OS_TASK_DEL_HAS_NO_NEXT) ||>  **
           HECBList v'16 **
           HTCBList tcbmap **
           HTime v'18 **
           HCurTCB (cur_tcb_blk, Int.zero) **
           (* Astruct (todelblock, Int.zero) OS_TCB_flag todelblk ** *)
           (* dllseg v'28 (Vptr (todelblock, Int.zero)) v'12 Vnull l2'
            *   OS_TCB_flag (fun vl : vallist => nth_val 1 vl)
            *   (fun vl : vallist => nth_val 0 vl) **
            * dllseg v'9 Vnull v'13 (Vptr (todelblock, Int.zero)) l1'
            *   OS_TCB_flag (fun vl : vallist => nth_val 1 vl)
            *   (fun vl : vallist => nth_val 0 vl) ** *)
           GV OSTCBList @ OS_TCB ∗ |-> v'9 **
           GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
           Aie false **
           Ais nil **
           Acs (true :: nil) **
           Aisr empisr **
           AECBList v'7 v'6 v'16 tcbmap **
           tcbdllflag v'9 (l1' ++ todelblk :: l2') **
           AOSRdyTblGrp v'14 v'15 **
           AOSTCBPrioTbl priotbl v'14 tcbmap vhold **
           A_isr_is_prop **
           p_local OSLInv (cur_tcb_blk, Int.zero) init_lg **
           LV self @ Int8u |-> (V$ 0) **
           LV ptcb @ OS_TCB ∗ |-> Vptr (todelblock, Int.zero) **
           AOSEventFreeList v'3 **
           AOSQFreeList v'4 **
           AOSQFreeBlk v'5 **
           AOSMapTbl **
           AOSUnMapTbl **
           AOSIntNesting **
           AOSTCBFreeList v'20 v'21 **
           AOSTime (Vint32 v'18) **
           AGVars **
           atoy_inv' **
           LV os_code_defs.x @ OS_TCB ∗ |-> v'2 **
           LV pevent @ OS_EVENT ∗ |-> v' **
           LV prio @ Int8u |-> Vint32 i **
           A_dom_lenv
             ((prio, Int8u)
              :: (pevent, OS_EVENT ∗)
                 :: (ptcb, OS_TCB ∗)
                    :: (self, Int8u) :: (os_code_defs.x, OS_TCB ∗) :: nil)
                  )).


                    
(* <|| END Some (V$ OS_TASK_DEL_HAS_NO_NEXT) ||>  **
 *            HECBList v'16 **
 *            HTCBList tcbmap **
 *            HTime v'18 **
 *            HCurTCB (cur_tcb_blk, Int.zero) **
 *            (* Astruct (v'32, Int.zero) OS_TCB_flag todelblk **
 *             * dllseg v'27 (Vptr (v'32, Int.zero)) v'29 Vnull l2' OS_TCB_flag
 *             *   (fun vl : vallist => nth_val 1 vl)
 *             *   (fun vl : vallist => nth_val 0 vl) **
 *             * dllseg v'9 Vnull v'13 (Vptr (v'32, Int.zero)) l1' OS_TCB_flag
 *             *   (fun vl : vallist => nth_val 1 vl)
 *             *   (fun vl : vallist => nth_val 0 vl) ** *)
 *            LV ptcb @ OS_TCB ∗ |-> Vptr (v'32, Int.zero) **
 *            (* PV vhold @ Int8u |-> v'12 ** *)
 *            GV OSTCBList @ OS_TCB ∗ |-> v'9 **
 *            GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
 *            AOSEventFreeList v'3 **
 *            AOSQFreeList v'4 **
 *            AOSQFreeBlk v'5 **
 *            AECBList v'7 v'6 v'16 tcbmap **
 *            AOSMapTbl **
 *            AOSUnMapTbl **
 *            AOSTCBPrioTbl priotbl v'14 tcbmap vhold **
 *            (* GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64) priotbl ** *)
 *            (* G& OSPlaceHolder @ Int8u == vhold ** *)
 *            AOSIntNesting **
 *            AOSTCBFreeList v'20 v'21 **
 *            AOSRdyTblGrp v'14 v'15 **
 *            AOSTime (Vint32 v'18) **
 *            AGVars **
 *            A_isr_is_prop **
 *            tcbdllflag v'9 (l1' ++ todelblk :: l2') **
 *            p_local OSLInv (cur_tcb_blk, Int.zero) init_lg **
 *            Aisr empisr **
 *            Aie false **
 *            Ais nil **
 *            Acs (true :: nil) **
 *            atoy_inv' **
 *                     LV os_code_defs.x @ OS_TCB ∗ |-> v'2 **
 *            LV self @ Int8u |-> (V$ 0) **
 *            LV pevent @ OS_EVENT ∗ |-> v' **
 *            LV prio @ Int8u |-> Vint32 v'10 **
 *            A_dom_lenv
 *              ((prio, Int8u)
 *               :: (pevent, OS_EVENT ∗)
 *               :: (ptcb, OS_TCB ∗) :: (self, Int8u) :: (os_code_defs.x, OS_TCB ∗) :: nil)
 *                    )). *)

  eapply tcbdllseg_combine.
  sep pauto.
  sep cancel tcbdllflag.
  sep cancel Aop.
  unfold tcbdllseg.
  unfold1 dllseg.
  unfold node.
  sep pauto.
  go.
  go.
  go.
  go.
  hoare_split_pure_all.
  unprotect Heqtcblst.
  instantiate (1:=Afalse).
  (* change (  ( fun xxx => {|OS_spec, GetHPrio, OSLInv, I,
   *  fun v : option val =>
   *  ( <|| END v ||>  **
   *   p_local OSLInv (cur_tcb_blk, Int.zero) init_lg **
   *   ((EX v0 : val, LV prio @ Int8u |-> v0) **
   *    (EX v0 : val, LV pevent @ OS_EVENT ∗ |-> v0) **
   *    (EX v0 : val, LV ptcb @ OS_TCB ∗ |-> v0) **
   *    (EX v0 : val, LV self @ Int8u |-> v0) **
   *    (EX v0 : val, LV x @ OS_TCB ∗ |-> v0) ** Aemp) **
   *   Aie true ** Ais nil ** Acs nil ** Aisr empisr) **
   *  A_dom_lenv
   *    ((prio, Int8u)
   *     :: (pevent, OS_EVENT ∗)
   *        :: (ptcb, OS_TCB ∗) :: (self, Int8u) :: (x, OS_TCB ∗) :: nil),
   *  Afalse|}|- (cur_tcb_blk, Int.zero)
   *  {{tcbdllseg v'9 Vnull v'23 Vnull xxx **
   *     <|| END Some (V$ OS_TASK_DEL_ERR) ||>  **
   *    HECBList v'16 **
   *    HTCBList tcbmap **
   *    HTime v'18 **
   *    HCurTCB (cur_tcb_blk, Int.zero) **
   *    LV ptcb @ OS_TCB ∗ |-> Vptr (v'28, Int.zero) **
   *    PV vhold @ Int8u |-> v'12 **
   *    GV OSTCBList @ OS_TCB ∗ |-> v'9 **
   *    GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
   *    AOSEventFreeList v'3 **
   *    AOSQFreeList v'4 **
   *    AOSQFreeBlk v'5 **
   *    AECBList v'7 v'6 v'16 tcbmap **
   *    AOSMapTbl **
   *    AOSUnMapTbl **
   *    GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64) priotbl **
   *    G& OSPlaceHolder @ Int8u == vhold **
   *    AOSIntNesting **
   *    AOSTCBFreeList v'20 v'21 **
   *    AOSRdyTblGrp v'14 v'15 **
   *    AOSTime (Vint32 v'18) **
   *    AGVars **
   *    A_isr_is_prop **
   *    tcbdllflag v'9 xxx **
   *    p_local OSLInv (cur_tcb_blk, Int.zero) init_lg **
   *    Aisr empisr **
   *    Aie false **
   *    Ais nil **
   *    Acs (true :: nil) **
   *    atoy_inv' **
   *    LV x @ OS_TCB ∗ |-> v'2 **
   *    LV self @ Int8u |-> v'1 **
   *    LV pevent @ OS_EVENT ∗ |-> v' **
   *    LV prio @ Int8u |-> Vint32 v'10 **
   *    A_dom_lenv
   *      ((prio, Int8u)
   *       :: (pevent, OS_EVENT ∗)
   *          :: (ptcb, OS_TCB ∗) :: (self, Int8u) :: (x, OS_TCB ∗) :: nil)}} 
   *  EXIT_CRITICAL;ₛ
   *  RETURN ′ OS_TASK_DEL_ERR {{Afalse}}
   *        ) (l1' ++ todelblk :: l2') ).
   * rewrite Heqtcblst. *)
  eapply backward_rule1.
  intros.
  eapply tcbdllseg_split' in H55.
  eauto.
  exact H24.
  eauto.
  hoare unfold.
  destruct v'11.
  unfold tcbdllseg; unfold dllseg.
  hoare_split_pure_all.
  inverts H59.
  rewrite H55.
  hoare forward prim.
  sep cancel tcbdllflag.
  unfold AOSTCBList.
  sep pauto.
  
  (* sep cancel 1%nat 1%nat.
   * sep cancel 1%nat 1%nat.
   * do 2 sep cancel 2%nat 1%nat.
   * eauto. *)
  go.
  go.
  go.
  go.
  hoare forward.
  hoare forward.
  hoare_split_pure_all.
  assert (exists n, v'28 = Vptr n).
  clear -H20 H21.
  destruct H21; simpljoin; destruct H20; simpljoin; subst; simpl in *; tryfalse.
  eauto.
  eauto.
  clear H21 H20.
  simpljoin.
  rename v'8 into l1'.
  rename v'11 into l2'.
  
  (*   false.
   *   clear -H17 H10 H5 H9  H26.
   *   unfolds in H17.
   *   simpljoin.
   *   assert (get v'16 (v'26, Int.zero) = Some (x, t, m)).
   *   unfold join, sig, get in *; simpl in *.
   *   unfold join, sig, get in *; simpl in *.
   *   go.
   *   lets bb: H0 H2.
   *   simpljoin.
   *   unfold nat_of_Z in H3.
   *   apply nv'2nv in H9.
   *   rewrite H9 in H3.
   *   inverts H3.
   *   clear -H4 H26.
   *   Lemma valinj_eq:
   *     forall x y,
   *       val_inj (val_eq (Vptr x) (Vptr y)) <> Vint32 Int.zero ->
   *       x = y.
   *   Proof.
   *     SearchAbout val_eq.
   *     intros.
   *     unfold val_eq in H.
   *     destruct x; destruct y.
   *     destruct (peq b b0).
   *     subst.
   *     remember (Int.eq i i0).
   *     destruct b.
   *     assert (i = i0).
   *     clear -Heqb.
   *     int auto.
   *     SearchAbout Int.unsigned.
   *     SearchAbout (Int.unsigned _ = Int.unsigned _).
   *     apply unsigned_inj.
   *     auto.
   *     subst; auto.
   *     simpl in H.
   *     tryfalse.
   *     simpl in H.
   *     tryfalse.
   *   Qed.
   *   Show.
   *   apply H4.
   *   apply valinj_eq.
   *   auto.
   *   intro; tryfalse.
   * } *)

  (* assert ( x1 = (v'26, Int.zero)).
   * {
   *   clear -H17 H10 H5 H9  .
   *   unfolds in H17.
   *   simpljoin.
   *   assert (get v'16 (v'26, Int.zero) = Some (x, t, m)).
   *   unfold join, sig, get in *; simpl in *.
   *   unfold join, sig, get in *; simpl in *.
   *   go.
   *   lets bb: H0 H2.
   *   simpljoin.
   *   unfold nat_of_Z in H3.
   *   apply nv'2nv in H9.
   *   rewrite H9 in H3.
   *   inverts H3.
   *   auto.
   *   intro; tryfalse.
   * }
   * 
   * subst x1. *)
  lets backup: H30.
  unfold1 TCBList_P in H30.
  simpljoin.
  inverts H20.
  inverts H21.
  unfolds in H30.
  destruct x14; destruct p.
  simpljoin.
  inverts H20; inverts H21.
  assert ( (p, t, m) = (i, x, x0)).
  clear -H22 H23 H28.
  assert (get tcbmap (todelblock, Int.zero) =Some  (p, t, m)).
  unfold get,sig, join in *; simpl in *.
  unfold get,sig, join in *; simpl in *.
  go.
  unfold get,sig, join in *; simpl in *.
  unfold get,sig, join in *; simpl in *.
  rewrite H in H23.
  inverts H23.
  reflexivity.
  inverts H20.
  unfolds in H30.
  simpljoin.
  inverts H20; inverts H56; inverts H63; inverts H30.
  inverts H54; inverts H21; inverts H55.

  change ((OSRdyTbl ′ [ptcb ′ → OSTCBY] &= ∼ ptcb ′ → OSTCBBitX;ₛ
                                                                  If(OSRdyTbl ′ [ptcb ′ → OSTCBY] ==ₑ ′ 0)
                                                                  {OSRdyGrp ′ &= ∼ ptcb ′ → OSTCBBitY}  )) with (      inline_call inline_bittbl_clearbit ((OSRdyGrp ′):: (OSRdyTbl ′)::(ptcb ′ → OSTCBBitX)::(ptcb ′ → OSTCBBitY)::(ptcb ′ → OSTCBY)::nil)
                                                                                                                ).
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  unfold GAarray.
  unfold AOSRdyGrp.
  unfold Agvarmapsto at 3.
  hoare unfold.

  Ltac inline_forward :=
    match goal with
      | |- {| _ , _ , _, _, _, _|} |- _ {{ _ }} inline_call ?inline_record _ {{ _ }} => eapply backward_rule2; [eapply (inl_proof inline_record)  | intro;intros;inline_pre_unfolder inline_record |idtac..]
    end.
  eapply seq_rule.

  inline_forward.
  Focus 2.
  sep pauto.
  sep cancel Aop.
  sep cancel 4%nat 2%nat.
  sep cancel 2%nat 1%nat.
  eauto.
  (* unfold AOSRdyGrp in H56.
   * sep normal in H56.
   * sep lift 21%nat in H56. *)
  instantiate (1 := x11).
  omega.
  go.
  math simpls.
  go.
  go.
  clear -H.
  mauto.

  2:go.

  
  intro.
  intros.
  (* rewrite H9 in H45. *)
  lrv_solver.
  (* intro; tryfalse. *)
  go.
  (* intro; tryfalse. *)
  go.
  (* intro; tryfalse. *)
  go.
  intro.
  intros.
  linv_solver.
  inline_post_unfolder inline_bittbl_clearbit.
  hoare unfold.
  inverts H58.
  eapply backward_rule1.
  intro.
  intros.
  sep lift 2%nat in H58.
  sep lift 5%nat in H58.
  eapply GrefArray in H58.
  sep lift 3%nat in H58.
  sep lift 4%nat in H58.
  apply GrefPV in H58.
  eauto.
  hoare unfold.
  (* rewrite H9. *)
  hoare forward.
  (* intro; tryfalse. *)
  go.
  (* assert (isptr x14).
   * clear -H12.
   * simpl in H12.
   * simpljoin.
   * destruct x14; tryfalse.
   * unfolds; simpl; auto.
   * unfolds; simpl; eauto. *)

  Lemma absimp_taskdel_succ:
  forall P v3 sch t tls mqls ct ,
    can_change_aop P ->
    (* Int.lt ($ 63) v3 = false ->
     * (* OSAbstMod.get O abtcblsid = Some (abstcblist tls) -> *)
     * ~ (exists t' st msg, TcbMod.get tls t' = Some (v3, st, msg)) ->
     * (exists t', TcbMod.join tls (TcbMod.sig t' (v3, rdy, Vnull)) tls' )-> *)
    absinfer sch ( <|| taskdelcode ((Vint32 v3) :: nil) ||> **
                       HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P)
             ( <|| taskdel_clear_waitls_bit (|((Vint32 v3) :: nil)|) ;;sdel ((Vint32 v3):: nil);;isched ;; END (Some (Vint32 (Int.repr NO_ERR))) ||> **  HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P).
Proof.
  intros.
  unfold taskdelcode.
  infer_branch 6%nat.
  unfold sdel.
  eapply absinfer_eq.
Qed.

(* ** ac: Show. *)

  Lemma absimp_taskdel_rdy_succ:
  forall P v3 sch t tls mqls ct ,
    can_change_aop P ->
    (* Int.lt ($ 63) v3 = false ->
     * (* OSAbstMod.get O abtcblsid = Some (abstcblist tls) -> *)
     * ~ (exists t' st msg, TcbMod.get tls t' = Some (v3, st, msg)) ->
     * (exists t', TcbMod.join tls (TcbMod.sig t' (v3, rdy, Vnull)) tls' )-> *)
    absinfer sch ( <|| taskdelcode ((Vint32 v3) :: nil) ||> **
                       HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P)
             ( <|| sdel ((Vint32 v3):: nil);;isched ;; END (Some (Vint32 (Int.repr NO_ERR))) ||> **  HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P).
Proof.
  intros.
  unfold taskdelcode.
  infer_branch 5%nat.
  unfold sdel.
  eapply absinfer_eq.
Qed.


  destruct H62.

  {
hoare abscsq.
apply noabs_oslinv.
eapply absimp_taskdel_rdy_succ.
go.


    (* not in wait list *)
    subst x21.
    rewrite (H64 (eq_refl  ($ OS_STAT_RDY))). 
    hoare forward.
    (* intro; tryfalse. *)
    (* intro; tryfalse. *)
    hoare_split_pure_all.
    false.
    clear -H58.
    int auto.
    instantiate (1:=Afalse).
    hoare forward.
    hoare unfold.
    clear H58.
    hoare forward.
    hoare forward.
    Require Import taskdelete_ready.
    
    eapply task_delete_ready with 
 (v'27 := v'27) (x20 := x20) (x19 := x19) (x18 := x18) (x17 := x17) ( i6 := i6) ( i5 := i5 ) ( i4 := i4) ( i3 := i3) ( i2 := i2) (i1 := i1 ) ( i0 := i0) ( l2 := l2) ( v'33 := v'33 )  ( v'25 := v'25 ) (l1' := l1' )  ( v'13 := v'13 )  (v'29 := v'29); 
     eauto.
    
  }
  {
hoare abscsq.
apply noabs_oslinv.
eapply absimp_taskdel_succ.
go.

    (* in some wait list  *)
    (* simpljoin.
     * destruct H39.
     * (* rdy *)
     * false.
     * subst x23; lets bb: H38 (eq_refl ($ OS_STAT_RDY)).
     * inverts bb. *)
    (* assert (exists v, x5 = Vint32 v).
     * clear -H12.
     * unfolds in H12.
     * simpl in H12.
     * simpljoin.
     * destruct x3; tryfalse.
     * eauto.
     * simpljoin. *)
    lets bb: TcbIsWait H53 H58.
    simpljoin.
    rename v'16 into ecbmap.

   
    lets bbackup: H2.
      
    rewrite <- poi_is_rtep in H2.
    unfolds in H2.
    simpljoin.
    unfolds in H61.
    lets cc: H61 H72 H23.
    simpljoin.
      

    (* destruct H56.
     * (* wait sem *)
     * {
     *   subst x17.
     *   unfolds in H52.
     *   simpljoin.
     *   unfolds in H59.
     *   simpljoin.
     *   unfolds in H70.
     *   assert (WaitTCBblk
     *       (x11
     *        :: v'13
     *           :: x23
     *              :: x5
     *                 :: Vint32 i13
     *                    :: V$ OS_STAT_SEM
     *                       :: Vint32 v'43
     *                          :: Vint32 (v'43&ᵢ$ 7)
     *                             :: Vint32 (v'43 >>ᵢ $ 3)
     *                                :: Vint32 ($ 1<<ᵢ(v'43&ᵢ$ 7))
     *                                   :: Vint32 ($ 1<<ᵢ(v'43 >>ᵢ $ 3)) :: nil)
     *       v'30
     *       v'43
     *       i13).
     *   (* assert (  WaitTCBblk
     *    *             (x0
     *    *                :: v'21
     *    *                :: Vptr x
     *    *                :: m
     *    *                :: Vint32 x1
     *    *                :: V$ OS_STAT_SEM
     *    *                :: Vint32 v'43
     *    *                :: Vint32 (v'43&ᵢ$ 7)
     *    *                :: Vint32 (v'43 >>ᵢ $ 3)
     *    *                :: Vint32 ($ 1<<ᵢ(v'43&ᵢ$ 7))
     *    *                :: Vint32 ($ 1<<ᵢ(v'43 >>ᵢ $ 3)) :: nil)
     *    *             v'30 v'43 x1 ). *)
     *   {
     *     unfolds.
     *     splits.
     *     go.
     *     Lemma not_prio_in_tbl_is_prio_not_in_tbl:
     *       forall p rtbl,
     *         ~prio_in_tbl p rtbl ->
     *         prio_not_in_tbl p rtbl.
     *     Proof.
     *       intros.
     *       unfold prio_in_tbl in H.
     *       unfold prio_not_in_tbl.
     *       intros.
     *     Admitted.
     * 
     *     Focus 2.
     *     go.
     * 
     *     apply not_prio_in_tbl_is_prio_not_in_tbl.
     *     intro.
     *     assert (RdyTCBblk
     *               (x11
     *        :: v'13
     *           :: x23
     *              :: x5
     *                 :: Vint32 i13
     *                    :: V$ OS_STAT_SEM
     *                       :: Vint32 v'43
     *                          :: Vint32 (v'43&ᵢ$ 7)
     *                             :: Vint32 (v'43 >>ᵢ $ 3)
     *                                :: Vint32 ($ 1<<ᵢ(v'43&ᵢ$ 7))
     *                                   :: Vint32 ($ 1<<ᵢ(v'43 >>ᵢ $ 3)) :: nil)
     *               v'30
     *               v'43).
     *     unfolds.
     *     go.
     *     lets bb: H52 H75.
     *     simpljoin.
     *     inverts H76.
     *   }
     *   Print  V_OSTCBEventPtr.
     *   Print RLH_Wait_P.
     *   Print  RLH_RdyI_P.
     *   Print WaitTCBblk.
     *   lets bb: H70 H74 (eq_refl (Some (V$ OS_STAT_SEM))) (eq_refl (Some (Vptr x))).
     *   simpljoin.
     *   assert (exists n wls, get v'15 x = Some (abssem n, wls) /\ In (v'26, Int.zero) wls).
     *   unfolds in H2.
     *   simpljoin.
     *   unfolds in H54; simpljoin.
     *   eapply H57.
     * 
     *   unfold join, sig, get in *; simpl in *.
     *   unfold join, sig, get in *; simpl in *.
     *   go.
     *   simpljoin.
     *   Print AECBList.
     *   SearchAbout ECBList_P.
     *   Print AECBList.
     *   unfold AECBList.
     *   hoare normal pre.
     *   hoare_split_pure_all. *)
    unfold AECBList.
    hoare normal pre.
    hoare unfold.
    lets cc: hl_get_ecb_can_split_ecblist H73 H75.
    simpljoin.

    hoare lift 2%nat pre.
    eapply backward_rule1.
    eapply evsllseg_split.
(* ** ac:     SearchAbout (length _ = length _). *)
    eapply ecblistp_length_eq_1; eauto.
    hoare normal pre.
    hoare_split_pure_all.
    hoare_assert_pure (v'6 = Vptr x12).
    symmetry.
    eapply ecblistp_evsllseg_tlsame; eauto.


    hoare unfold.
    unfold1 evsllseg.
    destruct x16.
    hoare unfold.
    unfold AEventNode.
    unfold AOSEvent.
    unfold node.
    unfold AOSEventTbl.
    hoare unfold.

    hoare forward.
    (* intro; tryfalse. *)
    (* intro; tryfalse. *)
    change (
        (pevent ′ → OSEventTbl) [ptcb ′ → OSTCBY] &= ∼ ptcb ′ → OSTCBBitX;ₛ
                                                                            If((pevent ′ → OSEventTbl) [ptcb ′ → OSTCBY] ==ₑ ′ 0)
                                                                            {pevent ′ → OSEventGrp &= ∼ ptcb ′ → OSTCBBitY}
      ) with (
      inline_call inline_bittbl_clearbit ((pevent′→OSEventGrp):: (pevent′→OSEventTbl)::(ptcb ′ → OSTCBBitX)::(ptcb ′ → OSTCBBitY)::(ptcb ′ → OSTCBY)::nil)
    ).

    hoare_split_pure_all.
    inline_forward.
    Focus 2.
    sep pauto.
    sep cancel Aop.
    sep cancel 2%nat 2%nat.

    8: exact H87.
    unfold Astruct in H83 at 1.
    unfold OS_EVENT in H83 at 1.
    unfold Astruct' in H83.
    (* (PV (v'25, Int.zero) @ Int8u |-> Vint32 i1 **
     *         PV (v'25, Int.zero +ᵢ  $ Z.of_nat (typelen Int8u)) @ 
     *         Int8u |-> Vint32 i0 **
     *         PV (v'25,
     *            (Int.zero +ᵢ  $ Z.of_nat (typelen Int8u)) +ᵢ
     *            $ Z.of_nat (typelen Int8u)) @ Int16u |-> 
     *         Vint32 i2 **
     *         PV (v'25,
     *            ((Int.zero +ᵢ  $ Z.of_nat (typelen Int8u)) +ᵢ
     *             $ Z.of_nat (typelen Int8u)) +ᵢ  $ Z.of_nat (typelen Int16u)) @
     *         (Void) ∗ |-> x16 **
     *         PV (v'25,
     *            ((((Int.zero +ᵢ  $ Z.of_nat (typelen Int8u)) +ᵢ
     *               $ Z.of_nat (typelen Int8u)) +ᵢ  
     *              $ Z.of_nat (typelen Int16u)) +ᵢ
     *             $ Z.of_nat (typelen (Void) ∗)) +ᵢ
     *            $ Z.of_nat (typelen (Tarray Int8u ∘ OS_EVENT_TBL_SIZE))) @
     *         STRUCT os_event ⋆ |-> v'5 ** Aemp) *)
    sep normal in H83.
    sep cancel 2%nat 1%nat.
    eauto.
    instantiate (1:= v'43).
    clear -H; omega.
    unfolds.
    math simpls.
    assumption.
    assumption.
    clear -H; mauto.
    intro; intros.
    lrv_solver.


    Theorem struct_member_array_rv'':
      forall s x t l (* vl *) tid decl id t' n P ad perm,
        s |=  LV x @ (Tptr t) |=> Vptr l @ perm  (* ** Astruct l t vl  *)** P->
        t = Tstruct tid decl ->
        good_decllist decl = true ->
        ftype id decl = Some (Tarray t' n) ->
        id_addrval l id t = Some ad ->
        s |= Rv (efield (ederef (evar x)) id) @ (Tarray t' n) == Vptr ad.
    Proof.

      Import DeprecatedTactic.
      intros.
      destruct s as [[[[[[]]]]]].
      simpl in *;mytac.
      rewrite H12.
      rewrite H2.
      unfold load;unfold loadm.
      rewrite Int.unsigned_zero in H13.
      lets Hf: mapstoval_loadbytes H13.
      simpl;auto.
      destruct Hf.
      destruct H.
      lets Hf: loadbytes_local H4 H.
      assert ( loadbytes m (x13, 0%Z) (typelen (Tptr (Tstruct tid decl))) = Some x2);auto.
      rewrite H5.
      rewrite H0.
      destruct l.
      unfold getoff.
      unfold evaltype.
      rewrite H12.
      unfold id_addrval in H3.
      remember (field_offset id decl ) as X.
      destruct X;tryfalse.
      rewrite Int.repr_unsigned.
      simpl.
      rewrite Int.repr_unsigned.
      inverts H3;auto.
      rewrite H12.
      auto.
      intro; tryfalse.
    Qed.

    eapply struct_member_array_rv''.
    sep cancel 13%nat 1%nat.
    eauto.
    unfold OS_EVENT.
    auto.
    unfolds; simpl.
    reflexivity.

    unfolds; simpl.
    reflexivity.

    assumption.

    Theorem struct_member_lv:
      forall s x t (* vl *) tid decl id t' a b off,
        s |= Rv (evar x) @ (Tptr t) == Vptr (a, b)  (* Astruct l t vl ** *) ->
        t = Tstruct tid decl ->
        good_decllist decl = true ->
        ftype id decl = Some t' ->
        field_offset id decl = Some off ->
        s |= Lv (efield (ederef (evar x)) id) @ t' == (a, b +ᵢ off).
    Proof.
      intros.
      destruct s as [[[[[[]]]]]].
      simpl in *.

      unfold getoff.
      simpl.
      simpljoin.
      destruct (get e0 x).
      destruct p.
      rewrite H.
      destruct l.
      inverts H4.
      splits; auto.
      rewrite H3.
      rewrite Int.repr_unsigned.
      auto.

      destruct (get e x).
      destruct p.
      rewrite H.
      inverts H4.
      rewrite H3.
      splits; auto.

      rewrite Int.repr_unsigned.
      auto.
      inverts H4.
      
    Qed.
(* ** ac:     Show. *)

    eapply struct_member_lv.
    symbolic_execution.
    unfold OS_EVENT; auto.
    unfolds; reflexivity.
    reflexivity.
    reflexivity.
    (* intro; tryfalse. *)
    go.
    (* intro; tryfalse. *)
    go.
    (* intro; tryfalse. *)
    go.

    linv_solver.


    hoare forward.

    Focus 2.
    hoare unfold.
    false.
    clear -H78.
    destruct H78; int auto.


    
    inline_post_unfolder inline_bittbl_clearbit.
    hoare unfold.
    inverts H78.
    hoare forward.
    hoare forward.
    hoare unfold.
    hoare forward.
    math simpls.
    clear -H; mauto.
    clear H101 H102 H103.

    (* destruct H39; clear H43.
     * false; subst x11; apply H35; reflexivity. *)

    (* simpljoin.
     * clear H41. *)
    destruct l2'.
    unfold1 dllseg.
    hoare unfold.
    inverts H101.
    unfold1 dllseg.
    unfold node.
    hoare unfold.
    Require Import taskdelete_waiting.
    eapply task_deletewaiting with 
 (v'27 := v'27) (x20 := x20) (x19 := x19) (x18 := x18) (x17 := x17) ( i6 := i6) ( i5 := i5 ) ( i4 := i4) ( i3 := i3) ( i2 := i2) (i1 := i1 ) ( i0 := i0) ( l2 := l2) ( v'33 := v'33 )  ( v'25 := v'25 ) (l1' := l1' ) ( v'15 := v'15) ( v'13 := v'13 ) (v'14 := v'14) (v'29 := v'29); eauto.

  }
  
Qed.
