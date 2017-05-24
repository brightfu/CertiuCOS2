(**************************  uc/OS-II  ******************************)
(*************************** OS_Q.C *********************************)
(*******Proofs for API Fucntion:  void* OSQCreate(INT16U size)*******)
(*************************** Code: **********************************)
(* 
OS_EVENT  *OSQCreate ( INT16U size)
{
    OS_EVENT  *pevent;
    OS_Q      *pq;
    OS_Q_FREEBLK *pqblk;
    void **start;

1   if(size>OS_MAX_Q_SIZE || size == 0)
2       return ((OS_EVENT * )0);
3   OS_ENTER_CRITICAL();
4   pevent = OSEventFreeList;
5   if (OSEventFreeList != (OS_EVENT * )0)
    {
6       OSEventFreeList = (OS_EVENT * ) OSEventFreeList->OSEventPtr;
    }
7   OS_EXIT_CRITICAL();
8   if (pevent != (OS_EVENT * )0)
    {
9       OS_ENTER_CRITICAL();
10      pq = OSQFreeList;
11      pqblk=OSQFreeBlk;
12      if (pq != (OS_Q * )0&& pqblk!=(OS_Q_FREEBLK * )0)
        {
13          OSQFreeList  = OSQFreeList->OSQPtr;
14          OSQFreeList  = (OS_Q * ) OSQFreeBlk ->nextblk;
15          pq->qfreeblk = pqblk;
16          start        = pqblk -> msgqueuetbl;
17          pq->OSQStart = start;
18          pq->OSQEnd   = &start[size];
19          pq->OSQIn           = start;
20          pq->OSQOut          = start;
21          pq->OSQSize         = size;
22          pq->OSQEntries      = 0;
23          OS_EventWaitListInit(pevent);
24          pevent->OSEventType = OS_EVENT_TYPE_Q;
25          pevent->OSEventCnt  = 0;
26          pevent->OSEventPtr  = pq;   
27          pevent-> OSEventListPtr = OSEventList         
28          pevent->pevent
29          OS_EXIT_CRITICAL();
        } 
        else
        {
30          pevent->OSEventPtr = (void * )OSEventFreeList;
31          OSEventFreeList    = pevent;
32          OS_EXIT_CRITICAL();
33          pevent = (OS_EVENT * )0;
       }
    }
33  return (pevent);
}
*)
(***************************************************************)
Require Import ucos_include.
Require Import absop_rules.
Require Import OSQCreatePure.


Require Import os_ucos_h.
Open Scope code_scope.
Open Scope int_scope.

Lemma  vaj_inj_isptr2_or :
  forall  p q, 
    isptr p -> 
    isptr q -> 
    val_inj
      (bool_and (val_inj (notint (val_inj (val_eq p Vnull))))
                (val_inj (notint (val_inj (val_eq q Vnull))))) =
    Vint32 Int.zero \/
    val_inj
      (bool_and (val_inj (notint (val_inj (val_eq p Vnull))))
                (val_inj (notint (val_inj (val_eq q Vnull))))) = Vnull -> 
    p = Vnull \/ q = Vnull. 
Proof.
  intros.
  unfold isptr in *.
  destruct H, H0;simp join; simpl in *;try(auto).
  destruct x0, x in H1.
  simpl in H1.
  destruct H1; 
    false.
Qed.

Lemma  vaj_inj_isptr2 :
  forall  p q, 
    isptr p -> 
    isptr q -> 
    val_inj
      (bool_and (val_inj (notint (val_inj (val_eq p Vnull))))
                (val_inj (notint (val_inj (val_eq q Vnull))))) <>
    Vint32 Int.zero -> exists x y, p = Vptr x /\ q = Vptr y. 
Proof.
  intros.
  unfold isptr in *.
  destruct H, H0; simp join;  simpl in *; tryfalse.
  unfold Int.notbool in H1.
  false.
  int auto.
  destruct x.
  simpl in H1.
  false.
  int auto.
  destruct x.
  simpl in H1.
  false.
  int auto.
  destruct x0, x.
  eauto.
Qed.

Lemma OSQCreateProof:
  forall tid vl p r, 
    Some p =
    BuildPreA' os_api OSQCreate
               (qcre, (Tptr os_ucos_h.OS_EVENT, Tint16 :: nil)) vl OSLInv tid init_lg ->
    Some r =
    BuildRetA' os_api OSQCreate
               (qcre, (Tptr os_ucos_h.OS_EVENT, Tint16 :: nil)) vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api OSQCreate = Some (t, d1, d2, s) /\
      {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|}|-tid {{p}}s {{Afalse}}.
Proof.
  init_spec.
  (*L1-L2 : if(size>OS_MAX_Q_SIZE) return ((OS_EVENT * )0);*)

  hoare forward;pure_auto.
  hoare unfold pre.
  (*Lin1: error input size*)
  hoare abscsq.
  apply noabs_oslinv.
  eapply  absimp_qcre_err_return; eauto.
  go.
  pure_auto.
  hoare forward; pure_auto.
  (*elim the false case*)
  hoare forward.
  (*L3:  OS_ENTER_CRITICAL();*)
  hoare forward prim; pure_auto.
  (*L4: pevent = OSEventFreeList;*)
  hoare unfold pre.
  hoare forward; pure_auto.
  (* Print ecbf_sllseg. *)
  destruct v'3; hoare unfold pre.
  hoare forward; pure_auto.
  pure intro.
  false. apply H4;  int auto.
  unfold OS_MAX_Q_SIZE; omega.
  hoare forward.
  instantiate (1:=Atrue).
  pure intro.
  false. apply H4; int auto.
  unfold OS_MAX_Q_SIZE; omega.
  hoare forward prim.
  sep_unfold.
  instantiate (2:=nil).
  unfold_ecbfsll.
  sep pauto.
  pure_auto.
  hoare forward;pure_auto.
  pure intro.
  false. apply H4. simpl;auto.
  hoare forward.
  instantiate (1:=Atrue).
  pure intro.
  false. apply H4; int auto.
  unfold OS_MAX_Q_SIZE; omega.
  pure intro.
  hoare abscsq.
  apply noabs_oslinv.
  eapply absimp_qcre_err_return; eauto. 
  pure_auto.
  pure_auto.
  hoare forward.
  (****)
  hoare forward. 
  pure_auto.
  pure_auto.
  hoare unfold pre.
  hoare forward; pure_auto.
  hoare forward.
  hoare unfold pre.
  hoare forward prim.
  sep_unfold.
  instantiate (2:=v'3).
  unfold_ecbfsll.
  sep pauto.
  sep cancel ecbf_sllseg. 
  eauto.
  pure_auto.
  Focus 2.
  hoare unfold pre.
  unfold Int.notbool in H5.
  rewrite eq_zero_zero in H5.
  destruct H5; inverts H5. 
  hoare forward;pure_auto.

  Focus 2.
  hoare forward.
  Focus 2.
  hoare unfold pre.
  unfold Int.notbool in H15.
  rewrite eq_zero_zero in H15.
  destruct H15; inverts H15. 
  Unfocus.
  hoare unfold pre.
  hoare forward prim;  pure_auto.
  instantiate (1:=
                 (
                   LV pevent @ OS_EVENT ∗ |-> Vptr (v'26, Int.zero) **
                      p_local OSLInv tid init_lg **
                      (EX v1 v2 v3, LV start @ ((Void) ∗) ∗ |-> v1 **
                                       LV pqblk @ OS_Q_FREEBLK ∗ |-> v2 **
                                       LV pq @ OS_Q ∗ |-> v3) **
                      LV size @ Int16u |-> Vint32 i ** Aie true ** Ais nil ** Acs nil ** Aisr empisr 
                      **<|| END (Some ( Vptr (v'26, Int.zero)) ) ||>**
                      A_dom_lenv
                      ((size, Int16u)
                         :: (pevent, OS_EVENT ∗)
                         :: (pq, OS_Q ∗)
                         :: (pqblk, OS_Q_FREEBLK ∗) :: (start, ((Void) ∗) ∗) :: nil))
                   \\//
                   (
                     LV pevent @ OS_EVENT ∗ |->Vnull ** p_local OSLInv tid init_lg **
                        (EX v1 v2 v3, LV start @ ((Void) ∗) ∗ |-> v1 **
                                         LV pqblk @ OS_Q_FREEBLK ∗ |-> v2 **
                                         LV pq @ OS_Q ∗ |-> v3) **
                        LV size @ Int16u |-> Vint32 i ** Aie true ** Ais nil ** Acs nil ** Aisr empisr **<|| END (Some Vnull)||> **
                        A_dom_lenv
                        ((size, Int16u)
                           :: (pevent, OS_EVENT ∗)
                           :: (pq, OS_Q ∗)
                           :: (pqblk, OS_Q_FREEBLK ∗) :: (start, ((Void) ∗) ∗) :: nil))).
  Focus 2.
  hoare unfold pre.
  hoare forward.
  hoare unfold pre.
  hoare forward.
  hoare unfold pre.
  hoare forward.
  hoare unfold pre.
  hoare forward.
  pure_auto.
  hoare unfold pre.
  hoare forward.
  pure_auto.
  hoare unfold pre.
  hoare forward; pure_auto.
  hoare unfold pre.
  clear H23 H24.
  lets Has :  vaj_inj_isptr2 H20 H21 H22.
  simp join.
  destruct v'28.
  simpl qblkf_sllseg.
  hoare unfold pre.
  inverts H23.
  destruct v'27.
  simpl sllseg .
  hoare unfold pre.
  inverts H23.
  unfold_qblkfsll.
  unfold_sll.
  hoare unfold pre.
  instantiate (1:= (A_dom_lenv
                      ((size, Int16u)
                         :: (pevent, OS_EVENT ∗)
                         :: (pq, OS_Q ∗)
                         :: (pqblk, OS_Q_FREEBLK ∗) :: (start, ((Void) ∗) ∗) :: nil) **
                      LV pevent @ OS_EVENT ∗ |-> Vptr (v'26, Int.zero) ** p_local OSLInv tid init_lg **
                      (EX v1 v2 v3, LV start @ ((Void) ∗) ∗ |-> v1 **
                                       LV pqblk @ OS_Q_FREEBLK ∗ |-> v2 **
                                       LV pq @ OS_Q ∗ |-> v3) **
                      LV size @ Int16u |-> Vint32 i ** Aie true ** Ais nil ** Acs nil ** Aisr empisr) **<|| END (Some ( Vptr (v'26, Int.zero)) ) ||>).
  simpl in H6; inverts H6.
  hoare forward.
  pure_auto.
  hoare unfold pre.
  hoare forward;pure_auto.
  hoare unfold pre.
  hoare forward;pure_auto.
  hoare forward.
  eauto.
  hoare forward;pure_auto.
  hoare unfold pre.
  simpl in H27; inverts H27.
  (***)
  hoare forward. 
  pure_auto.
  hoare forward. 
  hoare forward.
  hoare forward.
  pure_auto.
  hoare forward.
  hoare forward.
  
  remember (Aarray (v'48, Int.zero+ᵢ($ 4+ᵢInt.zero))
                   (Tarray (Void) ∗ ∘OS_MAX_Q_SIZE) v'47) as Hr.
  sep cancel Aarray.
  sep pauto.
  sep cancel Aisr.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel 1%nat 1%nat.
  eauto.
  splits;simpl; auto.
  pure_auto.
  sep auto.
  sep auto.
  hoare unfold pre.
  inverts H41.
  hoare forward.
  hoare forward.
  hoare forward.
  hoare unfold pre.
  hoare forward. 
  pure_auto.
  hoare forward.
  hoare unfold pre.
  
  hoare_assert_pure ( EcbMod.get v'39 (v'46, Int.zero) = None).
  sep lifts (5::6::nil)%nat in H41.
  lets Hs : ecblist_star_not_inh  H41; eauto.
  hoare unfold pre.
  hoare abscsq.
  apply noabs_oslinv.
  eapply  absimp_qcre_succ_return; eauto.
  pure_auto.
  eapply  val_inj_boolor_false; auto.

  hoare forward prim.
  unfold AOSQFreeList.
  unfold AOSQFreeBlk.
  unfold qblkf_sll.
  unfold os_inv.sll.
  unfold AECBList.
  sep pauto.
  sep cancel qblkf_sllseg.
  sep cancel sllseg.
  instantiate (3:= ( (V$OS_EVENT_TYPE_Q
                       :: Vint32 Int.zero
                       :: V$0 :: Vptr (v'50, Int.zero) :: v'54 :: v'24 :: nil),  INIT_EVENT_TBL) ::v'30).
  instantiate (2:= (DMsgQ (Vptr  (v'50, Int.zero))  
                          (v'49
                             :: Vptr (v'48, Int.zero+ᵢ($ 4+ᵢInt.zero))
                             :: Vptr (v'48, (Int.zero+ᵢ($ 4+ᵢInt.zero))+ᵢInt.mul ($ 4) i)
                             :: Vptr (v'48, Int.zero+ᵢ($ 4+ᵢInt.zero))
                             :: Vptr (v'48, Int.zero+ᵢ($ 4+ᵢInt.zero))
                             :: Vint32 i :: V$0 :: Vptr (v'48, Int.zero) :: nil)  (v'45 :: x4 :: nil)  v'47 ):: v'29).
  unfold evsllseg. fold evsllseg.
  unfold_msg.
  unfold AEventData.
  unfold AMsgData.
  unfold AOSQCtr.
  unfold_msg.
  sep pauto.
  sep cancel evsllseg.
  sep cancel 3%nat 4%nat.
  sep cancel 5%nat 3%nat.
  sep cancel Astruct.
  sep cancel 3%nat 2%nat.
  sep cancel Aarray.
  eauto.
  simpl; auto.
  Focus 2.
  unfolds.
  simpl;eauto.
  apply RL_Tbl_init_prop.
  simpl;auto.
  simpl. splits;  pure_auto.
  splits;[auto | pure_auto].
  unfolds; simpl; eauto.
  apply WLF_OSQ_prop;auto.
  splits; [ auto | pure_auto].
  simpl;auto.
  splits; [auto | pure_auto].
  eapply ECBList_OSQCRT_prop;eauto.
  apply OSQCRT_TCB_prop ; auto.
  pure_auto.
  sep semiauto.

  instantiate (1:=
                 (
                   LV pevent @ OS_EVENT ∗ |->Vnull **  p_local OSLInv tid init_lg **
                      (EX v1 v2 v3, LV start @ ((Void) ∗) ∗ |-> v1 ** 
                                       LV pqblk @ OS_Q_FREEBLK ∗ |-> v2 **
                                       LV pq @ OS_Q ∗ |-> v3) **
                      LV size @ Int16u |-> Vint32 i ** Aie true ** Ais nil ** Acs nil ** Aisr empisr) **<|| END (Some Vnull)||> **
                                                                                                      A_dom_lenv
                                                                                                      ((size, Int16u)
                                                                                                         :: (pevent, OS_EVENT ∗)
                                                                                                         :: (pq, OS_Q ∗)
                                                                                                         :: (pqblk, OS_Q_FREEBLK ∗) :: (start, ((Void) ∗) ∗) :: nil)).
  hoare unfold pre.

  hoare forward;pure_auto.
   hoare forward.
  hoare forward prim.
  unfold AOSEventFreeList.
  unfold_ecbfsll.
  unfold AOSQFreeList.
  unfold_sll.
  unfold AOSQFreeBlk.
  unfold qblkf_sll.
  sep pauto.
  sep cancel qblkf_sllseg.
  sep cancel sllseg.
  instantiate (2:=( (Vint32 i1 :: Vint32 i0 :: Vint32 i2 :: x2 :: x3 :: v'47 :: nil) :: v'22)).
  unfold_ecbfsll.
  sep pauto.
  sep cancel  ecbf_sllseg.
  sep cancel Astruct.
  sep cancel Aarray.
  eauto.
  simpl; auto.
  unfolds; simpl; auto.
  splits; [auto | pure_auto].
  pure_auto.
  hoare abscsq.
  apply noabs_oslinv.
  eapply absimp_qcre_err_return; pure_auto.
  hoare forward.
  sep semiauto.
  destruct H22; [left; sep auto  | right; sep auto].
Qed. 
