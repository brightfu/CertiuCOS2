(**************************  uc/OS-II  ****************************)
(*************************** OS_SEM.C *****************************)
(******Proof of API Fucntion:
           int8u OSSemPend(OS_EVENT* pevent, Int16u timeout) ******)
(***************************** Code: ******************************)

(*
(****
Definition OSSemPend_impl  :=
Int8u ·OSSemPend·(⌞pevent @ OS_EVENT∗; timeout @ Int16u⌟)··{
       ⌞legal @ Int8u⌟;


 1       If (pevent′ ==ₑ NULL){
 2            RETURN (OSSemPend) ′OS_ERR_PEVENT_NULL
        };ₛ
 3        ENTER_CRITICAL;ₛ
 4        legal′ =ᶠ OS_EventSearch(·pevent′·);ₛ
 5        If (legal′ ==ₑ ′0){
 6            EXIT_CRITICAL;ₛ
 7            RETURN (OSSemPend) ′OS_ERR_PEVENT_NULL
        };ₛ
 8        If (pevent′→OSEventType !=ₑ ′OS_EVENT_TYPE_SEM){
 9            EXIT_CRITICAL;ₛ
10            RETURN (OSSemPend) ′OS_ERR_PEVENT_NULL
        };ₛ
11        If (OSTCBCur′→OSTCBPrio ==ₑ ′OS_IDLE_PRIO){
12            EXIT_CRITICAL;ₛ
13            RETURN (OSSemPend) ′OS_ERR_PEVENT_NULL
        };ₛ
14        If ( (OSTCBCur′→OSTCBStat  !=ₑ ′OS_STAT_RDY) ||ₑ (OSTCBCur′→OSTCBDly  !=ₑ ′0)){
15            EXIT_CRITICAL;ₛ
16            RETURN (OSSemPend) ′OS_ERR_PEVENT_NULL
        };ₛ     
17        If (pevent′→OSEventCnt >ₑ ′0){
18            −−pevent′→OSEventCnt;ₛ
19            EXIT_CRITICAL;ₛ
20            RETURN (OSSemPend) ′OS_NO_ERR
        };ₛ
21        OSTCBCur′→OSTCBStat =ₑ ′OS_STAT_SEM;ₛ
22        OSTCBCur′→OSTCBDly =ₑ timeout′;ₛ
23        OS_EventTaskWait(­pevent′­);ₛ (* 加一句将Curtid变为当前最高的优先级，可以保证在临界区外保持这一性质 *)
24        EXIT_CRITICAL;ₛ
25        OS_Sched(­);ₛ
26        ENTER_CRITICAL;ₛ
27        If (OSTCBCur′→OSTCBDly ==ₑ ′0){

28            EXIT_CRITICAL;ₛ
29            RETURN (OSSemPend) ′OS_TIMEOUT
        };ₛ
30        OSTCBCur′→OSTCBEventPtr =ₑ NULL;ₛ
31        EXIT_CRITICAL;ₛ
32        RETURN (OSSemPend) ′OS_NO_ERR
}· .

****)
*)
Require Import sem_common.
Require Import sempend_pure.
Open Scope code_scope.

(* use this old hoare_if to avoid large modification *)
Ltac lzh_find_ret_stmt stmts :=
  match stmts with
    | sseq ?s ?rs =>
      match s with
        | srete _ => constr:(some 1%nat)
        | _ => lzh_find_ret_stmt rs
      end
    | srete _ => constr:(some 1%nat)
    | _ => constr:(none 1%nat)
  end.

Ltac lzh_hoare_if :=
  hoare_unfold;
  hoare forward; 
  match goal with
    | |- {|_, _, _, _, _, _|} |- ?ct {{?p ** [|?v <> Vint32 Int.zero /\
                                            ?v <> Vnull /\
                                            ?v <> Vundef|]}} ?stmts {{_}} =>
      (* idtac "if block proof"; *)
      let x := lzh_find_ret_stmt stmts in
        match x with
          | some _ => instantiate (1:=Afalse)
          | none _ => idtac
        end;
      hoare_split_pure_all;
      lzh_val_inj_simpl; tryfalse

    | |- {|_, _, _, _, _, _|} |- ?ct {{_}} _ {{_}} => 
      (* idtac "if all"; *)
      hoare forward;
      hoare_split_pure_all;
      lzh_val_inj_simpl; tryfalse
      (* first proof if-true condition, then proof if-false condition *)
    | _ => pauto
  end.

Hint Resolve CltEnvMod.beq_refl: brel .
Hint Resolve noabs_oslinv.
Hint Extern 2 (_ <= _) => apply Z.leb_le; trivial.


Lemma sempend_part1: forall
  (i : int32)
  (H1 : Int.unsigned i <= 65535)
  (v' : val)
  (v'0 : list vallist)
  (v'1 : list vallist)
  (v'2 : list vallist)
  (v'3 : list EventData)
  (v'4 : list os_inv.EventCtr)
  (v'5 : vallist)
  (v'6 : val)
  (v'7 : val)
  (v'8 : list vallist)
  (v'9 : vallist)
  (v'10 : list vallist)
  (v'11 : vallist)
  (v'12 : val)
  (v'13 : EcbMod.map)
  (v'14 : TcbMod.map)
  (v'15 : int32)
  (v'16 : addrval)
  (v'17 : val)
  (v'18 : list vallist)
  (v'21 : list os_inv.EventCtr)
  (v'22 : list os_inv.EventCtr)
  (v'23 : list EventData)
  (v'24 : list EventData)
  (v'26 : vallist)
  (v'27 : val)
  (v'29 : list vallist)
  (v'31 : list vallist)
  (v'32 : vallist)
  (v'33 : val)
  (v'34 : EcbMod.map)
  (v'35 : TcbMod.map)
  (v'37 : val)
  (v'39 : vallist)
  (v'41 : val)
  (v'42 : EcbMod.map)
  (v'43 : EcbMod.map)
  (v'44 : EcbMod.map)
  (v'46 : addrval)
  (H5 : ECBList_P v'41 Vnull v'22 v'24 v'43 v'35)
  (H19 : EcbMod.join v'42 v'44 v'34)
  (H14 : length v'21 = length v'23)
  (H18 : isptr v'41)
  (H11 : $ 1 <> $ 0)
  (v'19 : addrval)
  (v'25 : block)
  (H13 : array_type_vallist_match Int8u v'39)
  (H21 : length v'39 = ∘ OS_EVENT_TBL_SIZE)
  (x2 : val)
  (x3 : val)
  (i0 : int32)
  (H23 : Int.unsigned i0 <= 255)
  (i2 : int32)
  (H24 : Int.unsigned i2 <= 65535)
  (H25 : isptr x2)
  (H20 : RL_Tbl_Grp_P v'39 (Vint32 i0))
  (H26 : isptr v'41)
  (H4 : ECBList_P v'37 (Vptr (v'25, Int.zero)) v'21 v'23 v'42 v'35)
  (H2 : isptr (Vptr (v'25, Int.zero)))
  (H16 : id_addrval' (Vptr (v'25, Int.zero)) OSEventTbl OS_EVENT =
        Some v'19)
  (H22 : Int.unsigned ($ OS_EVENT_TYPE_SEM) <= 255)
  (H7 : R_ECB_ETbl_P (v'25, Int.zero)
         (V$ OS_EVENT_TYPE_SEM
          :: Vint32 i0 :: Vint32 i2 :: x2 :: x3 :: v'41 :: nil,
         v'39) v'35)
  (x : waitset)
  (H8 : EcbMod.joinsig (v'25, Int.zero) (abssem i2, x) v'43 v'44)
  (Hget : EcbMod.get v'34 (v'25, Int.zero) = Some (abssem i2, x))
  (H3 : ECBList_P v'37 Vnull
         (v'21 ++
          ((V$ OS_EVENT_TYPE_SEM
            :: Vint32 i0 :: Vint32 i2 :: x2 :: x3 :: v'41 :: nil,
           v'39) :: nil) ++ v'22)
         (v'23 ++ (DSem i2 :: nil) ++ v'24) v'34 v'35)
  (H6 : RLH_ECBData_P (DSem i2) (abssem i2, x))
  (v'20 : val)
  (v'36 : val)
  (v'38 : TcbMod.map)
  (v'40 : TcbMod.map)
  (v'45 : val)
  (v'47 : block)
  (H28 : v'27 <> Vnull)
  (H29 : join v'38 v'40 v'35)
  (H30 : TCBList_P v'27 v'29 v'32 v'38)
  (H27 : Vptr (v'47, Int.zero) <> Vnull)
  (x9 : val)
  (x10 : val)
  (H34 : isptr x10)
  (H35 : isptr x9)
  (i8 : int32)
  (H36 : Int.unsigned i8 <= 65535)
  (i7 : int32)
  (H37 : Int.unsigned i7 <= 255)
  (i6 : int32)
  (H38 : Int.unsigned i6 <= 255)
  (i5 : int32)
  (H39 : Int.unsigned i5 <= 255)
  (i4 : int32)
  (H40 : Int.unsigned i4 <= 255)
  (i3 : int32)
  (H41 : Int.unsigned i3 <= 255)
  (i1 : int32)
  (H42 : Int.unsigned i1 <= 255)
  (H33 : isptr v'20)
  (H12 : isptr v'45)
  (H31 : TCBList_P (Vptr (v'47, Int.zero))
          ((v'45
            :: v'20
               :: x10
                  :: x9
                     :: Vint32 i8
                        :: Vint32 i7
                           :: Vint32 i6
                              :: Vint32 i5
                                 :: Vint32 i4
                                    :: Vint32 i3
                                       :: Vint32 i1 :: nil) :: v'31)
          v'32 v'40)
  (H : RH_TCBList_ECBList_P v'13 v'14 (v'47, Int.zero))
  (H0 : RH_CurTCB (v'47, Int.zero) v'14)
  (H9 : RH_TCBList_ECBList_P v'34 v'35 (v'47, Int.zero))
  (H10 : RH_CurTCB (v'47, Int.zero) v'35)
  (H15 : Int.eq i6 ($ OS_IDLE_PRIO) = false)
  (H17 : Int.eq i7 ($ OS_STAT_RDY) = true)
  (H32 : Int.eq i8 ($ 0) = true)
  (H43 : Int.ltu ($ 0) i2 = false)
(* ================================= *) ,
   {|OS_spec, GetHPrio, OSLInv, I,
   fun v : option val =>
   ( <|| END v ||>  **
    p_local OSLInv (v'47, Int.zero) init_lg **
    ((EX v0 : val, LV timeout @ Int16u |-> v0) **
     (EX v0 : val, LV pevent @ OS_EVENT ∗ |-> v0) **
     (EX v0 : val, LV legal @ Int8u |-> v0) ** Aemp) **
    Aie true ** Ais nil ** Acs nil ** Aisr empisr) **
   A_dom_lenv
     ((timeout, Int16u)
      :: (pevent, OS_EVENT ∗) :: (legal, Int8u) :: nil), Afalse|}
   |- (v'47, Int.zero)
   {{Astruct (v'47, Int.zero) OS_TCB_flag
       (v'45
        :: v'20
           :: x10
              :: x9
                 :: Vint32 i8
                    :: Vint32 i7
                       :: Vint32 i6
                          :: Vint32 i5
                             :: Vint32 i4
                                :: Vint32 i3 :: Vint32 i1 :: nil) **
     dllseg v'45 (Vptr (v'47, Int.zero)) v'36 Vnull v'31
       OS_TCB_flag (fun vl : vallist => nth_val 1 vl)
       (fun vl : vallist => nth_val 0 vl) **
     GV OSTCBList @ OS_TCB ∗ |-> v'27 **
     dllseg v'27 Vnull v'20 (Vptr (v'47, Int.zero)) v'29
       OS_TCB_flag (fun vl : vallist => nth_val 1 vl)
       (fun vl : vallist => nth_val 0 vl) **
     GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (v'47, Int.zero) **
     AEventData
       (V$ OS_EVENT_TYPE_SEM
        :: Vint32 i0 :: Vint32 i2 :: x2 :: x3 :: v'41 :: nil)
       (DSem i2) **
     Astruct (v'25, Int.zero) OS_EVENT
       (V$ OS_EVENT_TYPE_SEM
        :: Vint32 i0 :: Vint32 i2 :: x2 :: x3 :: v'41 :: nil) **
     Aarray v'19 (Tarray Int8u ∘ OS_EVENT_TBL_SIZE) v'39 **
     Aie false **
     Ais nil **
     Acs (true :: nil) **
     Aisr empisr **
     GV OSEventList @ OS_EVENT ∗ |-> v'37 **
     evsllseg v'37 (Vptr (v'25, Int.zero)) v'21 v'23 **
     evsllseg v'41 Vnull v'22 v'24 **
     A_isr_is_prop **
     tcbdllflag v'27
       (v'29 ++
        (v'45
         :: v'20
            :: x10
               :: x9
                  :: Vint32 i8
                     :: Vint32 i7
                        :: Vint32 i6
                           :: Vint32 i5
                              :: Vint32 i4
                                 :: Vint32 i3 :: Vint32 i1 :: nil)
        :: v'31) **
     AOSRdyTblGrp v'32 v'33 **
     AOSTCBPrioTbl v'26 v'32 v'35 v'46 **
     HECBList v'34 **
     HTCBList v'35 **
     HCurTCB (v'47, Int.zero) **
      <|| sem_pend (Vptr (v'25, Int.zero) :: Vint32 i :: nil) ||>  **
     p_local OSLInv (v'47, Int.zero) init_lg **
     LV legal @ Int8u |-> (V$ 1) **
     AOSEventFreeList v'0 **
     AOSQFreeList v'1 **
     AOSQFreeBlk v'2 **
     AOSMapTbl **
     AOSUnMapTbl **
     AOSIntNesting **
     AOSTCBFreeList v'17 v'18 **
     AOSTime (Vint32 v'15) **
     HTime v'15 **
     AGVars **
     atoy_inv' **
     LV timeout @ Int16u |-> Vint32 i **
     LV pevent @ OS_EVENT ∗ |-> Vptr (v'25, Int.zero) **
     A_dom_lenv
       ((timeout, Int16u)
        :: (pevent, OS_EVENT ∗) :: (legal, Int8u) :: nil)}} 
   If(OSTCBCur ′ → OSTCBMsg !=ₑ NULL)
        {EXIT_CRITICAL;ₛ
        RETURN ′ OS_ERR_PEVENT_NULL}  ;ₛ
   OSTCBCur ′ → OSTCBStat =ₑ ′ OS_STAT_SEM;ₛ
   OSTCBCur ′ → OSTCBDly =ₑ timeout ′;ₛ
   OS_EventTaskWait (­ pevent ′­);ₛ
   EXIT_CRITICAL;ₛ
   OS_Sched (­);ₛ
   ENTER_CRITICAL;ₛ
   If(OSTCBCur ′ → OSTCBMsg ==ₑ NULL)
        {EXIT_CRITICAL;ₛ
        RETURN ′ OS_TIMEOUT}  ;ₛ
   EXIT_CRITICAL;ₛ
   RETURN ′ OS_NO_ERR {{Afalse}}
.
Proof.
  intros.
  lzh_simpl_int_eq.
  subst.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  hoare_split_pure_all.
  mytac.
  assert (Fget: TcbMod.get v'40 (v'47, Int.zero) = Some (i6, rdy, x9)).
  {
    lets Ftmp: sempend_TCBListP_head_in_tcb_rdy H31; eauto.
  }
  lzh_hoare_if.
  
  assert (x9 <> Vnull).
  {
    clear -H46.
    rename H46 into H.
    rename x9 into x.
    destruct x.
    pure_auto.
    {
      unfold val_eq in H.
      unfold val_inj in H.
      unfold notint in H.
      unfold Int.notbool in H.
      mytac.
      rewrite Int.eq_false in H.
      tryfalse.
      auto.
    }
    pure_auto.
    pure_auto.        
  }        
  clear H46.

  hoare abscsq.
  auto.
  
  eapply absinfer_sem_pend_msg_not_null_return;eauto.
  eapply TcbMod.join_get_r; eauto.
  can_change_aop_solver.

  hoare lift 12%nat pre. 
  fold_AEventNode_r.
  compose_evsllseg.
  fold_AECBList.

  hoare forward prim.
  (***** ex critical ****)
  unfold AOSTCBList.
  unfold tcbdllseg.
  sep pauto.
  sep cancel 3%nat 1%nat.
  unfold dllseg.
  fold dllseg.
  unfold node.
  sep pauto.
  sep cancel Astruct.
  sep cancel dllseg.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  sep pauto.
  sep cancel AOSRdyGrp.
  sep pauto.
  auto.
  unfolds; simpl; auto.
  unfolds; simpl; auto.
  split; auto.
  struct_type_match_solver.

  (** unfold tcblist_P **)
  eauto.
  eauto.
  eauto.
  pauto.

  hoare forward.
(****************** msg <> null finished *****************)
(****************** msg = null begin *********************)

  assert (x9 = Vnull).
  {
    clear -H46.
    rename H46 into H.
    rename x9 into x.
    destruct x.
    {
      unfold val_eq in H; unfold notint in H; unfold val_inj in H.
      destruct H as [H1 | H2]; tryfalse.
    }
    auto.
    {
      unfold val_eq in H; unfold notint in H; unfold val_inj in H.
      destruct H as [H1 | H2]; tryfalse.
    }
    {
      unfold val_eq in H; unfold notint in H; unfold val_inj in H.
      destruct a.
      unfold Int.notbool in H.
      rewrite Int.eq_true in H.
      destruct H as [? | ?]; tryfalse.
    }      
  } 
  clear H46.
  subst.
  
  hoare forward.
  hoare forward.
  clear -H1.
  pauto.
  
  hoare lifts (14::12::18::nil)%nat pre.
  transform_pre a_isr_is_prop_split ltac:(idtac).
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  unfold AOSRdyGrp.
  hoare_split_pure_all.

  hoare_unfold.
  hoare forward.

  unfold node.
  sep pauto.
  sep cancel Astruct.
  instantiate  (2:=DSem i2).
  unfold AEventNode.
  unfold AOSEvent.
  unfold AEventData.
  unfold node.
  unfold AEventData.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  unfold AOSRdyGrp.
  unfold AOSEventTbl.
  sep pauto.
  sep cancel Aarray.

  sep cancel Astruct.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aisr.
  sep cancel 1%nat 1%nat.
  sep pauto.
  
  clear -H24; int auto.
  unfolds; simpl; auto.
  unfolds; simpl; auto.
  pure_auto.
  eauto.
  unfolds; simpl; auto.
  eauto.
  pure_auto.
  split; auto.
  struct_type_match_solver.
  split.
  reflexivity.
  struct_type_match_solver.
  split.
  simpl; reflexivity.
  eexists; split; eauto.
  unfolds; simpl; eauto.
  apply Int.eq_false; auto.
 
  eapply tcblist_p_node_rl_sem; eauto.
  unfold AEventData; pure_auto.

  intros.
  sep auto.
  intros.
  sep auto.

  hoare_ex_intro.
  unfold OS_EventTaskWaitPost.

  unfold OS_EventTaskWaitPost'.
  unfold getasrt.

  hoare_split_pure_all.
  lzh_inverts_logic.
  inverts H50.
  unfold V_OSTCBY,V_OSTCBBitX,V_OSTCBBitY,V_OSEventGrp in H51.
  simpl in H51.
  mytac_H.
  inverts H48.
  inverts H50.
  inverts H51.
  inverts H56.
(******************  function call finished **************)
  assert (Hcnt:i2 = $ 0).
  {
    clear -H43.
    apply semacc_ltu_zero_false.
    auto.
  }
  
  subst i2.
  
  hoare abscsq.
  auto.
  eapply absinfer_sem_pend_block; eauto.
  can_change_aop_solver.
  
  eapply TcbMod.join_get_r; eauto.

  unfold AOSTCBPrioTbl.
  hoare_split_pure_all.
  lets cp : H31.
  destruct cp as (td & vv & tcblss & asbs & Hveq & Hnes & Htcj & Htp & Htlis).
  destruct asbs.
  destruct p.
  destruct Htp as (_ & _ & Hrsl & _).
  
  funfold Hrsl.
  assert (0<= Int.unsigned x0 < 64).
  {
    clear -H60 H68.
    omega.
  }
  assert (prio_neq_cur v'35 (v'47, Int.zero) x0).
  {
    eapply R_PrioTbl_P_impl_prio_neq_cur; eauto.  
    eapply TcbMod.join_get_r.
    eauto.
    eauto.
  }
  inverts Hveq.

  (* ** ac: SearchAbout (A_isr_is_prop). *)
  hoare lifts (10::8::nil)%nat pre.
  transform_pre add_a_isr_is_prop ltac:(idtac).
  
  hoare forward prim.
  

  unfold AOSTCBList.
  unfold tcbdllseg.
  unfold dllseg at 2.
  fold dllseg.
  sep pauto.
  repeat (sep cancel dllseg).
  sep cancel node.
  (* AOSPrioTbl *)
  unfold AOSTCBPrioTbl.
  sep pauto.

  (** tcbdllflag **)
  (* ** ac: Check tcbdllflag_hold. *)
  (* ** ac: Check tcbdllflag_hold_middle. *)
  
  (* AECBList *)
  unfold AECBList.
  instantiate (1:=
           A_dom_lenv
             ((timeout, Int16u)
              :: (pevent, OS_EVENT ∗) :: (legal, Int8u) :: nil) **
           LV legal @ Int8u |-> (V$1) **
           LV timeout @ Int16u |-> Vint32 i **
           LV pevent @ OS_EVENT ∗ |-> Vptr (v'25, Int.zero)).
  sep pauto.
  eapply evsllseg_compose.
  
  instantiate (2:=
                 (V$OS_EVENT_TYPE_SEM
                   :: Vint32 (Int.or v'63 ($ 1<<ᵢ(x0 >>ᵢ $ 3))) 
                   :: V$0 :: x2 :: x3 :: v'41 :: nil)).
  unfold V_OSEventListPtr; simpl;  auto. 
  auto.  
  auto.
  repeat (sep cancel evsllseg).

  inverts H49.
  sep cancel AEventNode.
  sep cancel A_dom_lenv.
  sep cancel 1%nat 1%nat.
  unfold AEventData in H56.
  sep split in H56.
  sep lift 2%nat.
  eapply tcbdllflag_hold.
  2: eauto.
  unfold update_nth_val.
  eapply tcbdllflag_hold_middle.
  simpl; auto.
  (** sep assertions end here ~ **)

  rewrite list_prop1.
  rewrite list_prop1.

  eapply ecblist_p_compose.
  
  eapply EcbMod.join_set_r.
  eauto.
  eexists.
  eapply EcbMod.join_get_l.
  eauto.
  apply EcbMod.get_a_sig_a.
  eapply CltEnvMod.beq_refl.

  (**** ecblist_P ****)
  Focus 2.
  
  instantiate (1:=(Vptr (v'25, Int.zero))).
  unfold ECBList_P; fold ECBList_P.
  eexists; split.
  eauto.
  split.
  Focus 2.
  do 3 eexists; splits.
  unfolds; simpl; auto.
  instantiate (2 := (abssem Int.zero, (v'47, Int.zero) :: x)).

  unfold TcbJoin.
  unfold join.
  simpl.
  unfold sig; simpl.
  erewrite <- EcbMod.set_sig.
  (* ** ac: Check EcbMod.join_set_l. *)
  eapply EcbMod.join_set_l.
  eauto.
  unfold EcbMod.indom; eexists.
  apply EcbMod.get_a_sig_a.
  auto with brel.
  unfold RLH_ECBData_P.
  splits; auto.
  unfolds; split; intros; auto.
  clear -H57; tryfalse.
  eapply  ECBList_P_high_tcb_block_hold_sem; eauto.
  eapply TcbMod.join_get_r; eauto.
  
  eapply ejoin_get_none_r.
  2:eauto.
  apply EcbMod.get_a_sig_a.
  auto with brel.

  eapply R_ECB_ETbl_P_high_tcb_block_hold; eauto.
  eapply TcbMod.join_get_r; eauto.

  (* ** ac: Check ECBList_P_high_tcb_block_hold_sem. *)
  eapply  ECBList_P_high_tcb_block_hold_sem; eauto.
  eapply TcbMod.join_get_r; eauto.

  eapply ejoin_get_none_l.
  2:eauto.
  eapply EcbMod.join_get_l; eauto.
  apply EcbMod.get_a_sig_a.

  auto with brel.
  (** ECBList_P ends here ~ **)
  
  Require Import Mbox_common.
  Require Import OSTimeDlyPure.
  Open Scope code_scope.
  eapply  TcbMod_set_R_PrioTbl_P_hold ; eauto.
  eapply TcbMod.join_get_r; eauto.

  (* ** ac: Check rtbl_remove_RL_RTbl_PrioTbl_P_hold. *)
  eapply  rtbl_remove_RL_RTbl_PrioTbl_P_hold ; eauto.
  (*
  clear -H53 H57.
  assert (0 <= Int.unsigned x0 < 64) by omega.
  clear -H.
  mauto.
  clear -H53 H57.
  assert (0 <= Int.unsigned x0 < 64) by omega.
  clear -H.
  mauto.
  *)
  Import sempend_pure.
  eapply TCBList_P_tcb_block_hold; eauto.


  eapply TcbMod_join_impl_prio_neq_cur_r; eauto.


  eapply TCBList_P_tcb_block_hold' with (prio := x0); eauto.

  eapply TcbMod_join_impl_prio_neq_cur_r; eauto.
  eapply TcbMod.join_comm; eauto.
  inverts H49.
  unfold join; simpl.
  eapply TcbMod.join_set_r; eauto.
  unfolds; eexists; eauto.

  unfold V_OSTCBPrev; simpl nth_val; auto.
  unfold V_OSTCBNext; simpl nth_val; auto.

  eapply  RH_CurTCB_high_block_hold_sem ; eauto.
  eapply TcbMod.join_get_r; eauto.

  eapply RH_TCBList_ECBList_P_high_block_hold_sem; eauto.
  eapply TcbMod.join_get_r; eauto.

  pure_auto.
(******************** ex_critical finished ***********************)
(* schedule *)
  hoare forward prim.
  hoare forward.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aisr.
  sep cancel 1%nat 1%nat.
  sep cancel 1%nat 1%nat.
  sep pauto.
  unfold isflag.
  pure_auto.
  pure_auto.
  intros.
  sep destruct H56.
  sep eexists.
  sep cancel 7%nat 1%nat.
  sep auto.
  intros.
  sep destruct H56.
  sep eexists.
  sep cancel 7%nat 1%nat.
  sep auto.
  
  (* ** ac: Print OS_SchedPost. *)
  unfold OS_SchedPost.
  unfold OS_SchedPost'.
  unfold getasrt.
  hoare_split_pure_all.
  lzh_inverts_logic.

(* enter critical *)  
  hoare forward prim.
  hoare_unfold.
  clear H31 Fget.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  hoare_split_pure_all.
  mytac.
  (* ** ac: Check low_stat_q_impl_high_stat_q. *)
  assert (Fget: exists prio st, TcbMod.get v'75 (v'47, Int.zero) = Some (prio, st, x11)).
  {
    lets Ftmp: low_stat_q_impl_high_stat_q; eauto.
  }
  mytac_H.

  lzh_hoare_if.
  (* ** ac: idtac "0". *)
(**************  time out *******************)
  lzh_simpl_int_eq.
  subst.

  hoare abscsq.
  auto.
  eapply absinfer_sem_pend_to_timeout; eauto.
  eapply TcbMod.join_get_r; eauto.
  can_change_aop_solver.
  
  hoare forward prim.
  unfold AOSTCBList.
  sep pauto.
  unfold tcbdllseg.
  sep pauto.
  sep cancel 3%nat 1%nat.
  unfold dllseg; fold dllseg.
  unfold node.
  sep pauto.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  sep pauto.
  unfolds; auto.
  unfolds; auto.
  
  split; auto.
  struct_type_match_solver.
  eauto.
  eauto.
  eauto.
  pure_auto.

  (* ** ac: idtac "1". *)
  hoare forward.
(******************** time out finished *********************)
  hoare_unfold.

  hoare abscsq.
  auto.
  (* ** ac: Check absinfer_sem_pend_to_succ. *)
  eapply absinfer_sem_pend_to_succ with (m:=Vptr x5); eauto.
  can_change_aop_solver.
  eapply TcbMod.join_get_r; eauto.
  pure_auto.
  
  hoare forward prim.
  unfold AOSTCBList.
  sep pauto.
  unfold tcbdllseg.
  sep pauto.
  sep cancel 3%nat 1%nat.
  unfold dllseg; fold dllseg.
  unfold node.
  sep pauto.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  sep pauto.
  unfolds; auto.
  unfolds; auto.

  (* ** ac: idtac "2". *)
  split; auto.
  struct_type_match_solver.
  eauto.
  eauto.
  eauto.
  pure_auto.
  lzh_simpl_int_eq.
  hoare forward.
Qed.

Lemma OSSemPendProof:
    forall tid vl p r, 
      Some p =
      BuildPreA' os_api OSSemPend
                 sem_pendapi vl OSLInv tid init_lg ->
      Some r =
      BuildRetA' os_api OSSemPend
                 sem_pendapi vl OSLInv tid init_lg ->
      exists t d1 d2 s,
        os_api OSSemPend = Some (t, d1, d2, s) /\
        {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|} |- tid {{p}}s {{Afalse}}.
Proof.
  init_spec.

  (* L1 - L2 *)
  lzh_hoare_if.
  subst.
  hoare abscsq.
  auto.
  eapply absinfer_sem_pend_null_return; pure_auto.
  
  unfold tl_vl_match; unfold type_val_match; pure_auto.

  hoare forward.

  (* L3 *)
  hoare forward prim.

  (* L4 *)
  hoare_unfold.
  hoare forward.

  sep cancel Aie.
  sep cancel Ais.
  sep cancel Aisr.
  sep cancel Acs.
  sep cancel tcbdllflag.
  sep cancel AECBList.
  sep cancel AOSRdyTblGrp.
  sep cancel AOSTCBList.
  sep cancel AOSTCBPrioTbl.
  sep pauto.
  pure_auto.
  pure_auto.

  apply retpost_osev.
  sep pauto.
  sep destruct H3.
  apply adisj_elim in H3.
  destruct H3.
  sep auto.
  sep auto.
  intros.
  sep auto.

  unfold OS_EventSearchPost.
  unfold OS_EventSearchPost'.
  unfold getasrt.
  hoare_split_pure_all.
  unfold OS_EventSearchPost.
  unfold OS_EventSearchPost'.
  unfold getasrt. (* getasrt is meaning of notation PRE *)
  eapply backward_rule1.
  intros.
  eapply disj_star_elim; eauto.

  (* 由于os_eventsearch(pevent)可能找到，也可能找不到，所以，这里就天然的要分成两种情况 *)
  hoare forward.
  
(************************************  legal == 0 **********************************)
  Focus 2. (* proof legal == 0 branch first *)
  lzh_hoare_if.
  pure_auto.
  lzh_inverts_logic.
  hoare abscsq.
  auto.
  eapply absinfer_sem_pend_p_not_legal_return; pure_auto.
  
  hoare forward prim.
  sep pauto.
  pure_auto.
  hoare forward.
(**********************************************************************************)
(***********************************  legal == 1 **********************************)
  lzh_hoare_if.
  pure_auto.
  lzh_inverts_logic.
  lets Hget: eventsearch_after_get_H H3 H8; eauto.
  
  lzh_hoare_if.
  pure_auto.
  pure_auto.
  pure_auto.
  
  transform_pre sem_eventtype_neq_sem ltac:(sep cancel AEventData).
  hoare_split_pure_all.
  hoare abscsq.
  auto.
  eapply absinfer_sem_pend_wrong_type_return; pure_auto.
  auto.
  
  (*********  exit critical ***********)
  fold_AEventNode_r.
  compose_evsllseg.
  fold_AECBList.

  hoare forward prim.
  sep pauto.
  pure_auto.
  hoare forward.
(*******************************  type != sem finished **********************)
(*******************************  type = sem ********************************)
  lzh_simpl_int_eq.
  subst.
  transform_pre semacc_triangle_sem ltac:(sep cancel AEventData).
  hoare_split_pure_all.
  destruct H12 as [? [? ?]]. subst.

  hoare_unfold.
  lzh_hoare_if.
  pure_auto.
(*****************************  Curtid == OS_IDLE_PRIO *********************)

  hoare lift 7%nat pre. 
  fold_AEventNode_r.
  compose_evsllseg.
  fold_AECBList.
  lzh_simpl_int_eq.
  subst.

  hoare abscsq.
  auto.
  eapply absinfer_sem_pend_from_idle_return; eauto.
  can_change_aop_solver.

  lets Htmp: TCBListP_head_in_tcb H31.
  mytac.
  do 2 eexists.
  eapply TcbMod.join_get_r.
  eauto.
  eauto.

  hoare forward prim.
  
  unfold AOSTCBList.
  unfold tcbdllseg.
  sep pauto.
  sep cancel 3%nat 1%nat.
  unfold dllseg.
  fold dllseg.
  unfold node.
  sep pauto.
  split; auto.
  struct_type_match_solver.

  eauto.
  eauto.
  eauto.
  pure_auto.

  hoare forward.
(******************** Curtid == idle finished *********************)
(******************** Curtid <> idle begin: ***********************)

(******************** OSTCBCur is not rdy : a weird situation !*************************)
  lzh_hoare_if.
  pure_auto.
  pure_auto.
  pure_auto.
  pure_auto.
  pure_auto.

  Open Scope int_scope.
  assert (Heq: Int.eq i7 ($ OS_STAT_RDY) = false \/
               Int.eq i8 ($ 0) = false).
  {
    clear -H17.
    destruct (Int.eq i7 ($ OS_STAT_RDY)). 
    destruct (Int.eq i8 ($ 0)). 
    mytac.
    simpl in H.
    unfold Int.notbool in H.
    rewrite Int.eq_false in H; int auto.
    simpl in H. tryfalse.
    auto. auto.
  }
  
  clear H17.

  unfold1 TCBList_P in H31.
  mytac.
  unfolds in H31; inverts H31; inverts H17.
  unfold TCBNode_P in *.
  destruct x5. destruct p.
  mytac.
  unfold V_OSTCBNext, V_OSTCBMsg, V_OSTCBPrio, V_OSTCBDly, V_OSTCBStat in *.
  unfold TcbJoin in *.
  (* ** ac: Check join_get_get_r. *)
  assert (TcbMod.get v'40 (v'47, Int.zero) = Some (p, t, m)).
  {
    lets H100 : TcbMod.get_sig_some (v'47, Int.zero) (p, t, m).
    eapply TcbMod.join_get_get_l; eauto.
  }
  assert (TcbMod.get v'35 (v'47, Int.zero) = Some (p, t, m)).
  {
    eapply TcbMod.join_get_get_r; eauto.
  }
  (* ** ac: Locate low_stat_nordy_imp_high. *)

  lets Hnrdy: r_tcb_status_p_nrdy H45 Heq.
  hoare abscsq.
  auto.
  
  eapply absinfer_sem_pend_not_ready_return;eauto.
  can_change_aop_solver.

  hoare lift 12%nat pre. 
  fold_AEventNode_r.
  compose_evsllseg.
  fold_AECBList.

  hoare forward prim.
  (***** ex critical ****)

  unfold AOSTCBList.
  unfold tcbdllseg.
  sep pauto.
  sep cancel 3%nat 1%nat.
  unfold dllseg.
  fold dllseg.
  unfold node.
  sep pauto.
  split; auto.
  struct_type_match_solver.

  (** unfold tcblist_P **)
  unfolds.
  do 4 eexists.
  fold TCBList_P.
  splits; eauto.
  unfolds; auto.
  unfolds; auto.
  eauto.
  auto.
  pure_auto.

  hoare forward.
(********* OSTCBCur is not rdy finished ****************)
  assert (Heq: Int.eq i7 ($ OS_STAT_RDY) = true
               /\ Int.eq i8 ($ 0) = true).
  {
    clear -H17.

    Ltac lzh_val_inj_simpl_tmp :=
      repeat match goal with
        | |- ?x = ?x /\ ?y = ?y => auto
        | H: context [val_inj] |- _ =>
            simpl in H;
            try unfold Int.notbool in H;
            try rewrite Int.eq_true in H;
            try rewrite Int.eq_false in H;
            simpl in H;
            try rewrite sempend_ltu_ass1 in H;
            try rewrite sempend_ltu_ass2 in H;
            simpl in H
        | H: Vint32 Int.one = Vint32 Int.zero \/ _ |- _=>
            destruct H; tryfalse 
        | |- Int.zero <> Int.one =>
            int auto
        | |- Int.one <> Int.zero =>
            int auto
             end.

    destruct (Int.eq i7 ($ OS_STAT_RDY)); destruct (Int.eq i8 ($ 0));
      lzh_val_inj_simpl_tmp.
  }
  
  clear H17.
  inverts Heq.

(****************** cnt > 0, succ return ******************)
  hoare_unfold.
  lzh_hoare_if.
  pure_auto.
  pure_auto.
    
  hoare forward.
  (* pure_auto. *)
  struct_type_match_solver.
  pure_auto.
  
  transform_pre semacc_triangle_sem ltac:(sep cancel AEventData).
  hoare_split_pure_all.
  mytac.
  inverts H45.
  
  hoare abscsq.
  auto.
  eapply absinfer_sem_pend_inst_get_return; pure_auto. 

  (******* fold AECBList  *****)
  Require Import semacc_pure.
  transform_pre semacc_new_fundation ltac:(sep cancel AEventData).
  clear H6 H7.
  hoare_split_pure_all.
  fold_AEventNode_r.
  compose_evsllseg.

  lets Hnewjoin: ecb_get_set_join_join Hget H8 H19.
  mytac.

  assert (
      ECBList_P v'37 Vnull
                (v'21 ++
                      ((V$OS_EVENT_TYPE_SEM
                         :: Vint32 i0 :: Vint32 (i2-ᵢ$ 1):: x2 :: x3 :: v'41 :: nil, v'39) :: nil) ++
                      v'22)
                (v'23 ++ (DSem (i2-ᵢ$ 1) :: nil) ++ v'24) 
                (EcbMod.set v'34 (v'25, Int.zero) (abssem (i2-ᵢ$ 1), x0))
                v'35).
  {
    eapply semacc_compose_EcbList_P; eauto.
  }
  clear H3.
  fold_AECBList.
  hoare forward prim.
  (********** cancel AOSTCBList ******)
  unfold AOSTCBList.
  unfold tcbdllseg.
  sep pauto.
  sep cancel 4%nat 1%nat.
  unfold dllseg.
  fold dllseg.
  unfold node.
  sep pauto.
  sep cancel Astruct.
  sep cancel dllseg.
  sep pauto.
  unfolds; auto.
  unfolds; auto.
  split; [auto | struct_type_match_solver].
  eauto.
  eauto.
  eauto.
  eapply semacc_RH_TCBList_ECBList_P_hold; eauto.
  pure_auto.
  
  hoare forward.
(********************** cnt > 0 finished *********************************)
  eapply sempend_part1; eauto.
Qed.
