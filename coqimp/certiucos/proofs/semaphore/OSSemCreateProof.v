(**************************  uc/OS-II  ****************************)
(*************************** OS_SEM.C *****************************)
(****Proof of API Fucntion:  OS_EVENT* OSSemCreate(INT16U cnt) ****)
(***************************** Code: ******************************)
(*
OS_EVENT  *OSSemCreate (INT16U cnt)
{
    OS_EVENT  *pevent;


1    OS_ENTER_CRITICAL();
2    pevent = OSEventFreeList; 
3    if (OSEventFreeList != (OS_EVENT * )0) { 
4        OSEventFreeList = (OS_EVENT * )OSEventFreeList->OSEventPtr;
    }
5    if (pevent != (OS_EVENT * )0) {
6         OS_EventWaitListInit(pevent);        
7         pevent->OSEventType = OS_EVENT_TYPE_SEM;
8         pevent->OSEventCnt  = cnt;           
9         pevent->OSEventPtr  = (void * )0;
10        pevent->OSEventListPtr = OSEventList;
11        OSEventList = pevent;
    }
12    OS_EXIT_CRITICAL();
13    return (pevent);
}
*)
Require Import sem_common.
Require Import semacc_pure.

Open Scope code_scope.

Lemma OSSemCreProof: 
  forall tid vl p r, 
    Some p =
    BuildPreA' os_api OSSemCreate
               (semcre, (Tptr os_ucos_h.OS_EVENT, Tint16 :: nil)) vl OSLInv tid init_lg ->
    Some r =
    BuildRetA' os_api OSSemCreate
               (semcre, (Tptr os_ucos_h.OS_EVENT, Tint16 :: nil)) vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api OSSemCreate = Some (t, d1, d2, s) /\
      {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|} |- tid {{p}}s {{Afalse}}.
Proof.
  init_spec.

  hoare forward prim; pure_auto.
  hoare unfold.
  hoare forward; pure_auto.
  destruct v'0; hoare unfold.
  
(***************************** OSEventFreeList = Null **************************)
  lzh_hoare_if;
  match goal with
    | H: Vint32 (Int.notbool Int.one) <> Vint32 Int.zero /\
         Vint32 (Int.notbool Int.one) <> Vnull /\
         Vint32 (Int.notbool Int.one) <> Vundef |- _ =>
      destruct H as (H & _);
      unfold Int.notbool in H;
      rewrite Int.eq_false in H; eauto;
      tryfalse
    | _ => idtac
  end.
  pure_auto.
  pure_auto.

  clear Hif_false.
  hoare abscsq.
  apply noabs_oslinv.
  eapply semcre_absimp_no_free; pure_auto.
  
  lzh_hoare_if;
  match goal with
    | H: Vint32 (Int.notbool Int.one) <> Vint32 Int.zero /\
         Vint32 (Int.notbool Int.one) <> Vnull /\
         Vint32 (Int.notbool Int.one) <> Vundef |- _ =>
      destruct H as (H & _);
      unfold Int.notbool in H;
      rewrite Int.eq_false in H; eauto;
      tryfalse
    | _ => idtac
  end.
  pure_auto.
  pure_auto.
  
  clear Hif_false.
  hoare unfold.
  hoare forward prim.
  sep_unfold.
  instantiate (2:=nil).
  sep pauto.
  unfold ecbf_sll.
  unfold ecbf_sllseg.
  sep pauto.

  pure_auto.
  hoare forward; pure_auto.

(***************************** OSEventFreeList <> Null *****************************)
  rename v'23 into pevent_block.
  rename v'21 into pevent_event_tbl.
  lzh_hoare_if;
  match goal with
    | H: Vint32 (Int.notbool Int.zero) = Vint32 Int.zero \/
         Vint32 (Int.notbool Int.zero) = Vnull |- _ =>
      unfold Int.notbool in H; simpl in H;
      rewrite Int.eq_true in H; auto;
      destruct H; tryfalse
    | _ => idtac
  end.
  pure_auto.
  pure_auto.
  clear LHift_true.
  hoare forward;pure_auto.

  clear Hif_true.
  inverts H5. (** unfold pevent_event_tbl **)
  lzh_hoare_if; pure_auto.

  (** pevent <> null **)
  clear LHift_true.
  unfold AECBList.
  hoare_split_pure_all.
  hoare forward.

  instantiate (2 := semcre (Vint32 i :: nil)).
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel Aisr.
  sep cancel Ais.
  sep cancel Aie.
  sep cancel Acs.
  sep pauto.
  pure_auto.
  apply Z.leb_le; auto.
  apply Z.leb_le; auto.
  apply Z.leb_le; auto.
  pure_auto.

  intros.
  sep auto.

  intros.
  sep auto.

  hoare unfold.
  hoare_split_pure_all.
  heat.
  inverts H18.
  rename v'23 into pevent_block.
  (*
  assert (Htmp: v'23 = pevent_block).
  {
    inverts H5.
    auto.
  }
  subst v'23.
  clear H5.
  *)
  hoare forward.
  hoare forward.
  pure_auto.
  hoare forward.
  hoare forward.
  pure_auto.
  (* ** ac: SearchAbout (isptr _). *)
  (* assert (Htmp: isptr v'19). *)
  (* { *)
  (*   sep lift 11%nat in H5. *)
  (*   generalize (evsllseg_isptr H5). *)
  (*   intros. *)
  (*   auto. *)
  (* } *)
  (* pure_auto. *)
  hoare forward.

  instantiate (1:= fun _ =>
         [| ECBList_P v'19 Vnull v'4 v'3 v'13 v'14 |] ** (** this is needed **)
         <|| semcre (Vint32 i :: nil) ||>  **
          A_dom_lenv
            ((cnt, Int16u) :: (pevent, OS_EVENT ∗) :: nil) **
          GV OSEventList @ OS_EVENT ∗
          |-> Vptr (pevent_block, Int.zero) **
          LV pevent @ OS_EVENT ∗
          |-> Vptr (pevent_block, Int.zero) **
          Astruct (pevent_block, Int.zero) OS_EVENT
            (V$ OS_EVENT_TYPE_SEM
             :: Vint32 Int.zero
                :: Vint32 i :: Vnull :: v'27 :: v'19 :: nil) **
          Aisr empisr **
          Aie false **
          Ais nil **
          Acs (true :: nil) **
          Aarray
            (pevent_block,
            Int.zero +ᵢ
            ($ 4 +ᵢ  ($ 2 +ᵢ  ($ 1 +ᵢ  ($ 1 +ᵢ  Int.zero)))))
            (Tarray Int8u ∘ OS_EVENT_TBL_SIZE) INIT_EVENT_TBL **
          A_isr_is_prop **
          p_local OSLInv tid init_lg **
          evsllseg v'19 Vnull v'4 v'3 **
          GV OSEventFreeList @ OS_EVENT ∗ |-> v'20 **
          ecbf_sllseg v'20 Vnull v'0 OS_EVENT
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
          atoy_inv' ** LV cnt @ Int16u |-> Vint32 i).
  sep auto.

  hoare_split_pure_all.

  (* ** ac: Check semcre_ecblist_star_not_inh. *)
  (* ** ac: Check ECBList_P. *)
  rename v'13 into event_map.
  hoare_assert_pure (get event_map (pevent_block, Int.zero) = None).
  {
    eapply semcre_ecblist_star_not_inh.
    eauto.
    instantiate (3 := s0).
    sep cancel Astruct.
    sep cancel evsllseg.
    sep pauto.
  }
  hoare_split_pure_all.
  hoare abscsq.
  apply noabs_oslinv.
  (* ** ac: Check semcre_absimp_succ. *)
  
  eapply semcre_absimp_succ.
  can_change_aop_solver.
  pure_auto.
  eauto.
  
  hoare forward prim. 
  unfold AECBList.
  (* ** ac: Check ECBList_P. *)
  (* ** ac: Print EventData. *)
  instantiate (3:=
                 ((V$OS_EVENT_TYPE_SEM
                    :: Vint32 Int.zero :: Vint32 i :: Vnull :: v'27 :: v'19 :: nil), INIT_EVENT_TBL)::v'4).
  instantiate (2:=
                 (DSem i)::v'3). 
  sep pauto.
  unfold evsllseg.
  sep pauto.
  fold evsllseg.
  lzh_unfold_event.
  sep pauto.
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel evsllseg.
  unfold AOSEventFreeList.
  sep pauto.
  unfold ecbf_sll.
  sep cancel ecbf_sllseg.
  eauto.

  clear -H1.
  int auto.
  instantiate (1:=Vint32 Int.zero).

  apply semcre_RL_Tbl_init_prop.
  auto.
  auto.

  unfold array_type_vallist_match.
  splits; pauto.
  splits; [auto | struct_type_match_solver].

  assert (Htmp: isptr v'19).
  {
    sep lift 4%nat in H12.
    generalize (evsllseg_isptr H12).
    intros.
    auto.
  }
  pure_auto.
  pure_auto.
  (*************  ECBList_P **************)

  eapply semcre_ECBList_P; eauto.

  eapply semcre_RH_TCBList_ECBList_P; eauto.
  pauto.

  hoare forward.
  (************ Return ************)
  match goal with
    | H: Vint32 (Int.notbool Int.zero) = Vint32 Int.zero \/
         Vint32 (Int.notbool Int.zero) = Vnull |- _ =>
      unfold Int.notbool in H; simpl in H;
      rewrite Int.eq_true in H; auto;
      destruct H; tryfalse
    | _ => idtac
  end.

  Grab Existential Variables.
  exact Afalse.
  exact Afalse.
Qed.
