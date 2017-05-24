(**************************  uc/OS-II  ******************************)
(*************************** OS_MBOX.C ******************************)
(****Proofs for API Fucntion:  OS_EVENT* OSMboxCreate(Void* msg) ****)
(***************************** Code: ********************************)
(***
OS_EVENT ∗ ·OSMboxCreate·(⌞message @ Void ∗⌟)··{
           ⌞
              pevent @ OS_EVENT∗
           ⌟;

1            ENTER_CRITICAL;ₛ
2            pevent′ =ₑ OSEventFreeList′;ₛ
3            If (OSEventFreeList′ !=ₑ NULL)
             {
4                OSEventFreeList′ =ₑ  〈OS_EVENT∗〉 OSEventFreeList′→OSEventListPtr
             };ₛ
5           If (pevent′ !=ₑ NULL)
            {
6              OS_EventWaitListInit(­pevent′­);ₛ
7              pevent′→OSEventType =ₑ ′OS_EVENT_TYPE_MBOX;ₛ
8              pevent′→OSEventCnt =ₑ ′0;ₛ
9              pevent′→OSEventPtr =ₑ message′;ₛ
10             pevent ′ → OSEventListPtr =ₑ OSEventList ′;ₛ
11             OSEventList′ =ₑ pevent′
           };ₛ
12         EXIT_CRITICAL;ₛ
13         RETURN pevent′
}·.
}
 ***)
Require Import ucos_include.
Require Import Mbox_common.
Require Import mbox_absop_rules.
Require Import sep_lemmas_ext.

Open Scope code_scope.

Lemma MboxCreateProof:
    forall tid vl p r, 
      Some p =
      BuildPreA' os_api OSMboxCreate
                 mbox_createapi vl OSLInv tid init_lg ->
      Some r =
      BuildRetA' os_api OSMboxCreate
                 mbox_createapi vl OSLInv tid init_lg ->
      exists t d1 d2 s,
        os_api OSMboxCreate = Some (t, d1, d2, s) /\
        {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|}|- tid {{p}}s {{Afalse}}.
Proof.
  init_spec.
  (*L1-L2 : if(size>OS_MAX_Q_SIZE) return ((OS_EVENT * )0);*)
  hoare forward prim; pauto.
  hoare unfold.
  (*L3:  OS_ENTER_CRITICAL();*)
  hoare forward ; pauto.
  (*L4: pevent = OSEventFreeList;*)
  destruct v'0; hoare unfold.
  {
  hoare forward; pauto.
  pure intro.
  false. apply H3;  int auto.

  instantiate (1:=Afalse).
  hoare forward prim.
  hoare forward.

  (* hoare forward. *)
  (* hoare forward. *)
  hoare unfold.

  unfold Int.notbool, Int.one, Int.zero in H4.
  unfold Int.eq in H4.
  do 2 rewrite Int.unsigned_repr in H4.
  simpl in H4.
  tryfalse.

  rewrite max_unsigned_val.
  omega.
  rewrite max_unsigned_val.
  omega.
  rewrite max_unsigned_val.
  omega.

  instantiate (1:=Afalse).
  


  hoare forward prim.
  pure intro.
  hoare forward prim.
  sep_unfold.

  sep pauto.
  instantiate (2:=nil).
  unfold ecbf_sll.
  simpl ecbf_sllseg.
  

  sep pauto.
  pauto.
  hoare abscsq.
  apply noabs_oslinv.
  eapply absimp_mbox_create_err_return.
  can_change_aop_solver.
  auto.
  hoare forward.
  }

  hoare forward.
  pure intro.
  hoare unfold.
  hoare forward.

  go.
  pauto.

hoare forward.
Focus 2.
hoare_split_pure_all.
elim H4; intros.
tryfalse.
tryfalse.

(* succ path*)
hoare forward.
Focus 2.
hoare forward.
hoare_split_pure_all.
Focus 2.
hoare_split_pure_all.
destruct H12; intros.
int auto.
int auto.
Unfocus.

hoare unfold.

hoare forward.

sep cancel 4%nat 5%nat.

unfolds in H5.
unfolds in H5.
simpl in H5.
inverts H5.
(* change (Int.add Int.zero
 *           (Int.add (Int.repr 4)
 *              (Int.add (Int.repr 2)
 *                 (Int.add (Int.repr 1) (Int.add (Int.repr 1) Int.zero))))) with 
 * rewrite (@intlemma1 v'22 v'24); auto. *)
sep cancel Aarray.
sep cancel Aisr.
sep cancel Aie.
sep cancel Ais.
sep cancel Acs.
sep cancel Aop.
eauto.

go.
go.

Require Import linv_solver.
linv_solver.
linv_solver.

unfold_funpost.
(* hoare unfold. *)
(* inverts H23. *)
unfold AECBList.


instantiate (1 := (
EX  v'19 v'28 , 
                       <|| mbox_create (x :: nil)||>  **
           A_dom_lenv
             ((message, (Void) ∗) :: (pevent, os_ucos_h.OS_EVENT ∗) :: nil) **
             GV OSEventList @ os_ucos_h.OS_EVENT ∗ |-> Vptr (v'23, Int.zero) **
           LV pevent @ os_ucos_h.OS_EVENT ∗ |-> Vptr (v'23, Int.zero)  **
           Astruct (v'23, Int.zero) os_ucos_h.OS_EVENT
             (Vint32 (Int.repr OS_EVENT_TYPE_MBOX)
              :: Vint32 Int.zero
                 :: Vint32 (Int.repr 0) :: x :: v'28 :: v'19 :: nil)  **
           evsllseg v'19 Vnull v'4 v'3 **
           Aisr empisr **
           Aie false **
           Ais nil **
           Acs (true :: nil)  **
           Aarray
             (v'23,
             Int.add Int.zero
               (Int.add (Int.repr 4)
                  (Int.add (Int.repr 2)
                     (Int.add (Int.repr 1) (Int.add (Int.repr 1) Int.zero)))))
             (Tarray Int8u ∘ OS_EVENT_TBL_SIZE) INIT_EVENT_TBL **
           A_isr_is_prop **
           p_local OSLInv tid init_lg **
           GV OSEventFreeList @ os_ucos_h.OS_EVENT ∗ |-> v'20 **
           ecbf_sllseg v'20 Vnull v'0 os_ucos_h.OS_EVENT
             (fun vl : vallist => nth_val 5 vl) **
           AOSQFreeList v'1 **
           AOSQFreeBlk v'2 **
           AOSMapTbl **
           AOSUnMapTbl **
           AOSTCBPrioTbl v'5 v'11 v'14 v'16 **
           AOSIntNesting **
           AOSTCBList v'6 v'7 v'8 (v'9 :: v'10) v'11 tid v'14 **
           AOSTCBFreeList v'17 v'18 **
           AOSRdyTblGrp v'11 v'12 **
           AOSTime (Vint32 v'15) **
           HECBList v'13 **
           HTCBList v'14 **
           HTime v'15 **
           HCurTCB tid **
           AGVars **
           tcbdllflag v'6 (v'8 ++ v'9 :: v'10) **
           atoy_inv' ** LV message @ (Void) ∗ |-> x **
                                                     [| ECBList_P v'19 Vnull v'4 v'3 v'13 v'14 |] 

            )).
(* instantiate ( Goal3:= (
 *      EX  (v'26 v'27 : int32) (v'28 v'29 v'30 v'20 : val),
 *      <|| mbox_create (x :: nil) ||>  **
 *          LV pevent @ os_ucos_h.OS_EVENT ∗ |-> Vptr (v'23, Int.zero)   **
 *      Astruct (v'23, Int.zero) OS_EVENT
 *        (Vint32 ($OS_EVENT_TYPE_MBOX)
 *         :: Vint32 Int.zero :: V$0 :: x :: v'28 :: v'29 :: nil) **
 *      GV OSEventList @ OS_EVENT ∗ |->Vptr v'20 **
 *      evsllseg v'20 Vnull v'4 v'3  **
 *      Aisr empisr **
 *      Aie false **
 *      Ais nil **
 *      Acs (true :: nil) **
 *      Aarray (v'25, Int.zero+ᵢ($ 4+ᵢ($ 2+ᵢ($ 1+ᵢ($ 1+ᵢInt.zero)))))
 *        (Tarray Int8u ∘OS_EVENT_TBL_SIZE) INIT_EVENT_TBL **
 *      A_isr_is_prop **
 *      A_dom_lenv ((message, (Void) ∗) :: (pevent, OS_EVENT ∗) :: nil) **
 *      GV OSEventFreeList @ OS_EVENT ∗ |-> v'20  **
 *      ecbf_sllseg v'21 Vnull v'0 OS_EVENT (fun vl : vallist => nth_val 5 vl) **
 *      AOSQFreeList v'1 **
 *      AOSQFreeBlk v'2 **
 *      AOSMapTbl **
 *      AOSUnMapTbl **
 *      AOSTCBPrioTbl v'5 v'11 v'14 v'17 **
 *      AOSIntNesting **
 *      AOSTCBList v'6 v'7 v'8 (v'9 :: v'10) v'11 v'16 v'14 **
 *      AOSTCBFreeList v'18 v'19 **
 *      AOSRdyTblGrp v'11 v'12 **
 *      AOSTime (Vint32 v'15) **
 *      HECBList v'13 **
 *      HTCBList v'14 **
 *      HTime v'15 **
 *      HCurTCB v'16 ** AGVars ** atoy_inv' ** LV message @ (Void) ∗ |-> x **
 *      [| ECBList_P v'20 Vnull v'4 v'3 v'13 v'14 |] (**)
 * )). *)

hoare normal pre.
(* ** ac: Print Ltac hoare_split_pure_all. *)
(* ** ac: Print Ltac hoare_ex_intro. *)
repeat (apply ex_intro_rule; intros).
(* ** ac: Print Ltac hoare_split_pure_all. *)
hoare_split_pure_all'.
hoare unfold.
  hoare forward.
  hoare forward.
  hoare forward.
 pauto.
 hoare unfold.
 hoare forward.
 pauto.
 hoare unfold.
 hoare forward.
 inversion H25.
 inverts H26.
 sep pauto.
 sep semiauto.
 (* idtac. *)
 (* sep auto. *)
 hoare unfold.
 hoare_assert_pure ( EcbMod.get v'13 (v'23, Int.zero) = None).
 sep lifts (12::13::nil)%nat in H27.
 Require Import OSQCreatePure.
(* in OSQ *)
lets Hs : ecblist_star_not_inh H20 H27.
 auto.

 hoare unfold.


 hoare abscsq.
 apply noabs_oslinv.
 eapply absimp_mbox_create_succ_return.
 can_change_aop_solver.
 auto.
 exact H27.

 hoare forward prim.
 unfold AOSEventFreeList.
 unfold AECBList.
 sep pauto.
 unfold ecbf_sll.


 instantiate (7:=( (Vint32 (Int.repr OS_EVENT_TYPE_MBOX)
                            :: Vint32 Int.zero :: Vint32 (Int.repr 0) :: x :: v'24 :: v'19 :: nil), INIT_EVENT_TBL) :: v'4).


 instantiate (6:= ( (DMbox x) :: v'3)).
 sep cancel ecbf_sllseg.
 unfold evsllseg.
 fold evsllseg.
 sep pauto.

 unfold_msg.
 unfold AEventNode.
 unfold AEventData.
 unfold AMsgData.
 unfold AOSQCtr.
 unfold_msg.
 sep pauto.
 sep cancel evsllseg.
 sep cancel Astruct.
 sep cancel Aarray.
 instantiate (1:= (   LV pevent @ Tptr os_ucos_h.OS_EVENT  |-> Vptr (v'23, Int.zero) **
   LV message @ Tptr Tvoid |-> x **
   A_dom_lenv ((message, Tptr Tvoid ):: (pevent, Tptr os_ucos_h.OS_EVENT ) :: nil))).
 sep auto.
 
 
(* in OSQCreatePure.v *)
 pauto.
 apply RL_Tbl_init_prop.
 unfold V_OSEventGrp.
 simpl.
 auto.
 simpl.
 auto.

 unfold array_type_vallist_match.
 splits; auto.
 splits; simpl; auto.
 pauto.
 compute; auto.

 Require Import MboxCreatePure.
 eapply ECBList_MBox_Create_prop; eauto.
 
 eapply  MBox_Create_TCB_prop; eauto.
 
 pauto.
 
 hoare unfold.
 hoare forward.
 
 
 (* Grab Existential Variables.
  * exact Afalse.
  * exact Afalse. *)
Qed.
