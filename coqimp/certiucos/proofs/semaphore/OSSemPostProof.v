(**************************  uc/OS-II  ****************************)
(*************************** OS_SEM.C *****************************)
(******Proof of API Fucntion: int8u OSSemPost(OS_EVENT* pevent) ***)
(***************************** Code: ******************************)
(***
Definition OSSemPost_impl := 
Int8u ·OSSemPost·(⌞pevent @ OS_EVENT∗⌟)··{
       ⌞
         legal @ Int8u;
         x  @ Int8u
       ⌟;


 1        If (pevent′ ==ₑ NULL){
 2            RETURN (OSSemPost) ′OS_ERR_PEVENT_NULL
        };ₛ
 3        ENTER_CRITICAL;ₛ
 4        legal′ =ᶠ OS_EventSearch(·pevent′·);ₛ
 5       If (legal′ ==ₑ ′0){
 6           EXIT_CRITICAL;ₛ
 7           RETURN (OSSemPost) ′OS_ERR_PEVENT_NULL
        };ₛ
 8      If (pevent′→OSEventType !=ₑ ′OS_EVENT_TYPE_SEM){
 9           EXIT_CRITICAL;ₛ
10           RETURN (OSSemPost) ′OS_ERR_PEVENT_NULL
        };ₛ
11       If (pevent′→OSEventGrp !=ₑ ′0){
12           x′ =ₑ ′OS_STAT_SEM;ₛ 
13           OS_EventTaskRdy(­pevent′, (void * )NULL, x′­);ₛ
14           EXIT_CRITICAL;ₛ
15           OS_Sched(­);ₛ
16           RETURN (OSSemPost) ′OS_NO_ERR
        };ₛ
17       If (pevent′→OSEventCnt <ₑ ′65535){
18           pevent′→OSEventCnt =ₑ pevent′→OSEventCnt +ₑ ′1;ₛ
19           EXIT_CRITICAL;ₛ
20           RETURN (OSSemPost) ′OS_NO_ERR
        };ₛ
21       EXIT_CRITICAL;ₛ
22       RETURN (OSSemPost) ′OS_SEM_OVF
}·.

***)
Require Import sem_common.
Require Import sempend_pure.
Require Import sempost_pure.
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
  lzh_hoare_unfold;
  hoare forward; 
  match goal with
    | |- {|_, _, _, _, _, _|} |- ?ct {{?p ** [|?v <> Vint32 Int.zero /\
                                       ?v <> Vnull /\
                                       ?v <> Vundef|]}} ?stmts {{_}} =>
      (* ** ac: idtac "if block proof"; *)
      let x := lzh_find_ret_stmt stmts in
        match x with
          | some _ => instantiate (1:=Afalse)
          | none _ => idtac
        end;
      hoare_split_pure_all;
      lzh_val_inj_simpl; tryfalse

    | |- {|_, _, _, _, _, _|} |- ?ct {{_}} _ {{_}} => 
      (* ** ac: idtac "if all"; *)
      hoare forward;
      hoare_split_pure_all;
      lzh_val_inj_simpl; tryfalse
      (* first proof if-true condition, then proof if-false condition *)
    | _ => pauto
  end.

Hint Resolve noabs_oslinv.
Hint Extern 2 (_ <= _) => apply Z.leb_le; trivial.

Lemma sempost_part_0: forall
  (tid : tid)
  (v' : val)
  (v'0 : val)
  (v'1 : list vallist)
  (v'2 : list vallist)
  (v'3 : list vallist)
  (v'4 : list EventData)
  (v'5 : list os_inv.EventCtr)
  (v'6 : vallist)
  (v'7 : val)
  (v'8 : val)
  (v'9 : list vallist)
  (v'10 : vallist)
  (v'11 : list vallist)
  (v'12 : vallist)
  (v'13 : val)
  (v'14 : EcbMod.map)
  (v'15 : TcbMod.map)
  (v'16 : int32)
  (v'17 : addrval)
  (v'18 : val)
  (v'19 : list vallist)
  (H : RH_TCBList_ECBList_P v'14 v'15 tid)
  (H0 : RH_CurTCB tid v'15)
  (v'22 : list os_inv.EventCtr)
  (v'23 : list os_inv.EventCtr)
  (v'24 : list EventData)
  (v'25 : list EventData)
  (v'27 : vallist)
  (v'28 : val)
  (v'29 : val)
  (v'30 : list vallist)
  (v'31 : vallist)
  (v'32 : list vallist)
  (v'33 : vallist)
  (v'34 : val)
  (v'35 : EcbMod.map)
  (v'36 : TcbMod.map)
  (v'38 : val)
  (v'40 : vallist)
  (v'42 : val)
  (v'43 : EcbMod.map)
  (v'44 : EcbMod.map)
  (v'45 : EcbMod.map)
  (v'47 : addrval)
  (H4 : ECBList_P v'42 Vnull v'23 v'25 v'44 v'36)
  (H18 : EcbMod.join v'43 v'45 v'35)
  (H8 : RH_TCBList_ECBList_P v'35 v'36 tid)
  (H9 : RH_CurTCB tid v'36)
  (H13 : length v'22 = length v'24)
  (H17 : isptr v'42)
  (H10 : $ 1 <> $ 0)
  (v'20 : addrval)
  (v'26 : block)
  (H12 : array_type_vallist_match Int8u v'40)
  (H20 : length v'40 = ∘ OS_EVENT_TBL_SIZE)
  (x2 : val)
  (x3 : val)
  (i : int32)
  (H22 : Int.unsigned i <= 255)
  (i1 : int32)
  (H23 : Int.unsigned i1 <= 65535)
  (H24 : isptr x2)
  (H19 : RL_Tbl_Grp_P v'40 (Vint32 i))
  (H25 : isptr v'42)
  (H3 : ECBList_P v'38 (Vptr (v'26, Int.zero)) v'22 v'24 v'43
         v'36)
  (H1 : isptr (Vptr (v'26, Int.zero)))
  (H15 : id_addrval' (Vptr (v'26, Int.zero)) OSEventTbl OS_EVENT =
        Some v'20)
  (H21 : Int.unsigned ($ OS_EVENT_TYPE_SEM) <= 255)
  (H6 : R_ECB_ETbl_P (v'26, Int.zero)
         (V$ OS_EVENT_TYPE_SEM
          :: Vint32 i :: Vint32 i1 :: x2 :: x3 :: v'42 :: nil,
         v'40) v'36)
  (x : waitset)
  (H7 : EcbMod.joinsig (v'26, Int.zero) (abssem i1, x) v'44 v'45)
  (Hget : EcbMod.get v'35 (v'26, Int.zero) = Some (abssem i1, x))
  (H2 : ECBList_P v'38 Vnull
         (v'22 ++
          ((V$ OS_EVENT_TYPE_SEM
            :: Vint32 i :: Vint32 i1 :: x2 :: x3 :: v'42 :: nil,
           v'40) :: nil) ++ v'23)
         (v'24 ++ (DSem i1 :: nil) ++ v'25) v'35 v'36)
  (H5 : RLH_ECBData_P (DSem i1) (abssem i1, x))
  (H11 : Int.eq i ($ 0) = false)
(* ================================= *) ,
   {|OS_spec, GetHPrio, OSLInv, I,
   fun v : option val =>
   ( <|| END v ||>  **
    p_local OSLInv tid init_lg **
    ((EX v0 : val, LV pevent @ OS_EVENT ∗ |-> v0) **
     (EX v0 : val, LV legal @ Int8u |-> v0) **
     (EX v0 : val, LV os_code_defs.x @ Int8u |-> v0) ** Aemp) **
    Aie true ** Ais nil ** Acs nil ** Aisr empisr) **
   A_dom_lenv
     ((pevent, OS_EVENT ∗)
      :: (legal, Int8u) :: (os_code_defs.x, Int8u) :: nil),
   Afalse|}|- tid
   {{AEventData
       (V$ OS_EVENT_TYPE_SEM
        :: Vint32 i :: Vint32 i1 :: x2 :: x3 :: v'42 :: nil)
       (DSem i1) **
     Astruct (v'26, Int.zero) OS_EVENT
       (V$ OS_EVENT_TYPE_SEM
        :: Vint32 i :: Vint32 i1 :: x2 :: x3 :: v'42 :: nil) **
     Aarray v'20 (Tarray Int8u ∘ OS_EVENT_TBL_SIZE) v'40 **
     Aie false **
     Ais nil **
     Acs (true :: nil) **
     Aisr empisr **
     GV OSEventList @ OS_EVENT ∗ |-> v'38 **
     evsllseg v'38 (Vptr (v'26, Int.zero)) v'22 v'24 **
     evsllseg v'42 Vnull v'23 v'25 **
     A_isr_is_prop **
     AOSTCBList v'28 v'29 v'30 (v'31 :: v'32) v'33 tid v'36 **
     tcbdllflag v'28 (v'30 ++ v'31 :: v'32) **
     AOSRdyTblGrp v'33 v'34 **
     AOSTCBPrioTbl v'27 v'33 v'36 v'47 **
     HECBList v'35 **
     HTCBList v'36 **
     HCurTCB tid **
      <|| sem_post (Vptr (v'26, Int.zero) :: nil) ||>  **
     p_local OSLInv tid init_lg **
     LV legal @ Int8u |-> (V$ 1) **
     AOSEventFreeList v'1 **
     AOSQFreeList v'2 **
     AOSQFreeBlk v'3 **
     AOSMapTbl **
     AOSUnMapTbl **
     AOSIntNesting **
     AOSTCBFreeList v'18 v'19 **
     AOSTime (Vint32 v'16) **
     HTime v'16 **
     AGVars **
     atoy_inv' **
     LV os_code_defs.x @ Int8u |-> v'0 **
     LV pevent @ OS_EVENT ∗ |-> Vptr (v'26, Int.zero) **
     A_dom_lenv
       ((pevent, OS_EVENT ∗)
        :: (legal, Int8u) :: (os_code_defs.x, Int8u) :: nil)}} 
   os_code_defs.x ′ =ₑ ′ OS_STAT_SEM;ₛ
   OS_EventTaskRdy (­pevent ′, 〈 (Void) ∗ 〉 pevent ′,
   os_code_defs.x ′­);ₛ
   EXIT_CRITICAL;ₛ
   OS_Sched (­);ₛ
   RETURN ′ OS_NO_ERR {{Afalse}}
.
Proof.
  intros.
  hoare forward.

  hoare_unfold.
  unfold AOSTCBPrioTbl.
  unfold AOSTCBList.
  hoare_split_pure_all.
  destruct H14; subst v'29.
  
(****************************** L2: event_task_rdy ******************************)
  destruct H28.
  hoare forward.
  
  unfold_msg.
  sep cancel AEventData.
  sep pauto.
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aisr.
  sep cancel 1%nat 1%nat.
  sep cancel AOSRdyTblGrp.
  instantiate (2:= (v'30 ++ v'31 :: v'32)).
  eapply tcbdllseg_compose.
  sep cancel tcbdllseg.
  sep cancel tcbdllseg.
  sep pauto.

  eauto.
  unfold V_OSEventGrp; simpl.
  auto.
  pauto.
  pauto.
  split; auto.
  struct_type_match_solver.

  split.
  unfold V_OSEventGrp; simpl; eauto.
  lzh_simpl_int_eq. auto.
  simpl; eauto.
  simpl; eauto.
  pure_auto.

  Require Import tcblist_setnode_lemmas.

  (* ** ac: SearchAbout TCBList_P. *)
  Import OSQPostPure.
  (* ** ac: Locate tcbdllseg_get_last_tcb_ptr. *)
  (* ** ac: Check tcbdllseg_get_last_tcb_ptr. *)

  eapply TCBList_P_Combine.
  eapply tcbdllseg_get_last_tcb_ptr.
  instantiate (5:=s).
  sep cancel 3%nat 1%nat.
  sep pauto.
  2:eauto.
  2:eauto.
  eauto.
  
  eauto.
  eauto.
  eauto.

  eapply tcbdllseg_combine_ptr_in_tcblist.
  instantiate (7:=s).
  sep cancel tcbdllseg.
  sep cancel tcbdllseg.
  eauto.

  pure_auto.
  pure_auto.

  intros.
  sep auto.

  intros.
  sep auto.

  (** event task rdy precondition finished **) 
  Set Printing Depth 500.
  hoare unfold.

  inverts H62.

  (** renameing **)
  rename v'26 into pevent_addr.
  rename tid into ctcb.
  rename v'90 into htcb_addr. (** highest tcb in pevent waitlist **)
  rename H35 into Hhtcb.
  rename H56 into Hctcb_in_tcblist.
  rename v'66 into tcblist_head.
  rename v'30 into tcblist_seg1.
  rename v'31 into ctcb_node.
  rename v'32 into tcblist_seg2.
  rename H39 into Hrel_et.

  (* ** ac: Print prio_in_tbl. *)
  rename v'53 into rtbl.
  (* ** ac: Print TCBList_P. *)

  rename v'49 into tcbls.
  rename v'39 into tcbls1.
  rename v'41 into tcbls2.
  (** tcbls = tcbls1 ++ tcbls2, tcbls2 = cur_node ++ tcbls2' **)
  
  remember (tcblist_seg1 ++ ctcb_node :: tcblist_seg2) as tcblist.


  

  (* ** ac: Check absimp_sem_post_ex_wt_succ_return. *)
  (* ** ac: Print GetHWait. *)
  
  (* ** ac: Locate post_exwt_succ_pre_sem. *)
  (* ** ac: Check post_exwt_succ_pre_sem. *)

  (* ** ac: Print priority. *)
  (* ** ac: Print rel_edata_tcbstat. *)
  (* ** ac: Print GetHWait. *)
  rename v'85 into hprio.
  assert (exists hprio', hprio = Vint32 hprio').
  {
    clear - H66. (** struct_type_vallist_match **)
    (* ** ac: SearchAbout struct_type_vallist_match. *)
    (* ** ac: Print struct_type_vallist_match. *)
    rename H66 into H.
    unfold struct_type_vallist_match in H.
    unfold OS_TCB_flag in H.
    unfold struct_type_vallist_match' in H.
    mytac.
    clear - H5.
    (* ** ac: SearchAbout (rule_type_val_match Int8u _). *)
    apply rule_type_val_match_int8u_elim in H5.
    mytac.
  }
    
  destruct H33.
  subst hprio.
  rename x0 into hprio.
  
  rename v'79 into hnext.
  rename v'86 into htcbx.
  rename v'87 into htcby.
  rename v'88 into hbitx.
  rename v'89 into hbity.

  (* ** ac: Check tcblist_get_TCBList_P_get. *)
  (* ** ac: Check sem_post_get_tcb_stat. *)
  (* ** ac: Check rh_tcblist_ecblist_p_post_exwt_aux_sem. *)
  (* ** ac: Check rh_tcblist_ecblist_p_post_exwt_sem. *)
  assert (Hhtcb_get: exists st m, get tcbls (htcb_addr, Int.zero) = Some (hprio, st, m)).
  {        
    eapply tcblist_get_TCBList_P_get.
    eauto.
    pure_auto.
    eauto.
  }

  destruct Hhtcb_get as (st & msg & Hhtcb_get).

  assert (Hs1: Int.unsigned v'73 <= 7).
  {
    (* ** ac: Check osunmapvallist_prop. *)
    clear - H40 H22.
    apply osunmapvallist_prop in H22.
    mytac.
    rewrite H in H40.
    inverts H40.
    pure_auto.
  }
  
  assert (Hs2: Int.unsigned v'74 <= 255).
  {
    (* ** ac: Check array_int8u_nth_lt_len. *)
    clear - H41 Hs1 H52 H20.
    assert (Z.to_nat (Int.unsigned v'73) < length v'59)%nat.
    {
      rewrite H20; unfold OS_EVENT_TBL_SIZE.
      mauto.
    }
    lets Hx: array_int8u_nth_lt_len H52 H.
    mytac.
    rewrite H41 in H0.
    inverts H0.
    auto.
  }

  assert (Hs3: Int.unsigned v'72 <= 7).
  {
    clear - H42 Hs2.
    lets Hx: osunmapvallist_prop Hs2.
    mytac.
    rewrite H in H42; inverts H42.
    pure_auto.
  }

  rename x into pwls.
  (* ** ac: Check post_exwt_succ_pre_sem. *)
  generalize Hhtcb_get; intro Hhtcb_join.
  apply map_join_get_sig in Hhtcb_join.
  destruct Hhtcb_join as (tcbls' & Hhtcb_join).
  assert (Hpre: pwls <> nil /\ GetHWait tcbls pwls (htcb_addr, Int.zero) /\ TcbMod.get tcbls (htcb_addr, Int.zero) = Some (hprio, st, msg) /\ hprio = ((v'73<<ᵢ$ 3) +ᵢ  v'72)).
  {
    apply map_join_get_sig in Hhtcb_get.
    destruct Hhtcb_get.
    (* ** ac: Check post_exwt_succ_pre_sem. *)
    apply semacc_int_eq_false in H11.
    eapply post_exwt_succ_pre_sem; eauto.
  }
    
  (* ** ac: Print GetHWait. *)
  (* ** ac: Print PrioWaitInQ. *)
  (* ** ac: Check post_exwt_succ_pre_sem. *)
  (* ** ac: Locate post_exwt_succ_pre_sem. *)
  destruct Hpre as [ ? [? [? ?]]].
  subst hprio.
  
  hoare_abscsq.
  auto.
  
  eapply absimp_sem_post_ex_wt_succ_return.
  can_change_aop_solver.
  eauto.
  eauto.
  eauto.
  eauto.
  
  unfold AEventData.
  unfold_msg.
  hoare_split_pure_all.
  destruct H37.
  inverts H37.
  rename v'28 into pevent_addr.

  unfolds in H45; simpl in H45; inverts H45.
  (* ** ac: Check sem_post_get_tcb_stat. *)
  rename v'59 into etbl.

  rename H61 into Htcblist_p.
  lets Hhtcb_node: TCBList_P_tcblist_get_TCBNode_P Htcblist_p Hhtcb Hhtcb_get. 
  generalize Hhtcb_node; intro Htmp.
  unfolds in Htmp.
  mytac.
  inverts H37; inverts H45.
  rename H53 into Hh_tcbblk.
  rename H54 into Hh_tcbstat.
  unfolds in Hh_tcbblk.
  mytac.
  inverts H37.
  inverts H56; inverts H72; inverts H53; inverts H55; inverts H45; inverts H54.

  rename v'73 into p1.
  rename v'72 into p2.
  remember ((p1<<ᵢ$ 3) +ᵢ  p2) as hprio. 
  
  (* ** ac: Check sem_post_get_tcb_stat. *)

  assert (Hx: x6 = $ OS_STAT_SEM).
  {
    clear - Hrel_et.
    unfolds in Hrel_et.
    auto.
  }
  subst x6.

  assert (Hp1: (hprio >>ᵢ $ 3) =  p1).
  {
    subst hprio.
    clear - Hs1 Hs2 Hs3.
    clear Hs2.
    mauto.
  }

  assert (Hp2: hprio &ᵢ ($ 7) = p2).
  {
    subst hprio.
    clear - Hs1 Hs3.
    mauto.
  }    

  assert (Hs4: Int.unsigned v'91 <= 255).
  {
    clear - Hs1 H32 H64 H49.
    assert (Z.to_nat (Int.unsigned p1) < length rtbl)%nat.
    {
      rewrite H64.
      unfold OS_RDY_TBL_SIZE.
      mauto.
    }
    lets Htmp: array_int8u_nth_lt_len H49 H. 
    mytac.
      rewrite H32 in H0.
      inverts H0.
      auto.
  }
  
  (* ** ac: Check set_node_elim_hoare. *)
  
  assert (Htmp: v'75 = $ 1 <<ᵢ p2).
  {
    eapply math_mapval_core_prop.
    clear - Hs3.
    mauto.
    auto.
  }
  subst v'75.
  
  assert (Hno_dup: R_Prio_No_Dup tcbls).
  {
    clear - H30.
    unfolds in H30.
    mytac.
  }
  (** zhang hui's lemma **)
  hoare lift 19%nat pre.
  (* ** ac: Check set_node_elim_hoare. *)
  eapply set_node_elim_hoare with (tid:=ctcb) (tcbls:=tcbls); eauto.
  {
    eapply TCBNode_P_set_rdy; auto.
    3:eauto.

    rewrite Hp1.
    apply nth_val'2nth_val; eauto.

    auto.
  }
  {
    unfolds.
    rewrite Hp1.
    rewrite Hp2.
    do 2 eexists.
    splits; eauto.
  }
  {
    unfolds.
    unfold V_OSTCBNext , V_OSTCBPrev.
    simpl.
    auto.
  }
  
(************************* exit critical ***********************************)
  instantiate (1 := (pevent_addr, Int.zero)).
  hoare_split_pure_all.
  subst hprio.
  rewrite Hp1 in *.
  rewrite Hp2 in *.
  hoare forward prim.
  sep normal.
  sep eexists.
  sep cancel AOSEventFreeList.
  sep cancel AOSQFreeList.
  sep cancel AOSQFreeBlk.
  sep cancel AOSMapTbl.
  sep cancel AOSUnMapTbl.
  sep cancel AOSIntNesting.
  sep cancel AOSTCBFreeList.
  sep cancel AOSTime.
  sep cancel AGVars.
  sep cancel A_isr_is_prop.
  sep cancel 5%nat 5%nat.
  sep cancel 5%nat 5%nat.
  sep cancel 5%nat 5%nat.
  sep cancel 5%nat 5%nat.
  sep split; auto.
  sep cancel 5%nat 6%nat.
  sep cancel atoy_inv'.
  sep cancel AOSRdyTblGrp.

  (** AECBList **)
  unfold AECBList.
  sep normal.
  sep eexists.
  sep cancel 11%nat 1%nat.
  eapply lzh_evsllseg_compose.
  sep cancel evsllseg.
  sep cancel evsllseg.
  unfold AEventNode.
  unfold_msg.
  sep normal.
  sep eexists.
  sep split; auto.
  sep cancel Astruct.
  sep cancel Aarray.
  instantiate (13 := DSem i1).
  unfold AEventData.
  sep split; auto.

  (** AOSTCBPrioTbl **)
  unfold AOSTCBPrioTbl.
  sep normal.
  sep eexists.
  sep split; auto.
  sep cancel 5%nat 1%nat.
  sep cancel 4%nat 1%nat.
  sep cancel 8%nat 1%nat.

  (** AOSTCBList **)
  unfold AOSTCBList.
  sep normal.
  sep eexists.
  sep split; auto.
  sep cancel 4%nat 1%nat.
  sep cancel tcbdllseg.
  sep cancel 3%nat 1%nat.
  sep cancel tcbdllseg.
  
  (** tcbdllflag **)
  {
    sep lift 3%nat in H55.
    unfold AEventData in H55.
    eapply tcbdllflag_set_node in H55; eauto.
    unfolds; simpl; auto.
  }

  (** TCBList_P **)
  eauto.
  eauto.
  eauto.
  split; auto.

  (** R_PrioTbl_P **)
  eapply r_priotbl_p_set_hold; auto; eauto.
  eauto.
  split; auto.

  clear - H23.
  int auto.

  (** ecblist_p **)
  (* ** ac: Locate ecblist_p_post_exwt_hold_sem. *)
  (* ** ac: Check ecblist_p_post_exwt_hold_sem. *)
  (* ** ac: Print RL_RTbl_PrioTbl_P. *)
   
  eapply ecblist_p_post_exwt_hold_sem with (v'12:=v'57) (v'39:=p2) (v'69:=v'74) (v'38:=p1) (v'13:=etbl) (v'36:=v'52); eauto.
  
  eapply rl_etbl_ptbl_p; auto; eauto.

  lzh_simpl_int_eq; auto.
  
  clear - Hs3.
  mauto.

  (* ** ac: SearchAbout RL_Tbl_Grp_P. *)
  eauto.

  go.
  go.
  go.
  split;auto.
  go.
  simpl.
  eauto.
  go.

  assert (Htmp: ctcb = (htcb_addr, Int.zero) \/ ctcb <> (htcb_addr, Int.zero)) by tauto.
  destruct Htmp.
  subst ctcb.
  unfolds.
  unfold get; simpl.
  rewrite TcbMod.set_a_get_a.
  eauto.
  apply tidspec.eq_beq_true; auto.
  eapply rh_curtcb_set_nct; auto.
  

  assert (exists xl,st = wait (os_stat_sem (pevent_addr, Int.zero)) xl).
  {
    eapply rh_tcblist_ecblist_p_post_exwt_aux_sem ;eauto.
    clear -H35.
    unfolds in H35;mytac;auto.
  }
  destruct H56.
  subst st.

  eapply rh_tcblist_ecblist_p_post_exwt_sem;eauto.
  (* ** ac: Check rh_tcblist_ecblist_p_post_exwt_sem. *)
  clear -H35.
  unfolds in H35;mytac;auto.

  unfold AEventData.
  pure_auto.
  
  hoare_split_pure_all.
  hoare forward.
  sep normal.
  sep eexists.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aisr.
  sep cancel 1%nat 1%nat.
  sep cancel 1%nat 2%nat.
  sep split; auto.
  exact_s.
  unfold isflag.
  auto.
  pure_auto.
  intros.
  sep eexists.
  sep destruct H68.
  sep cancel 7%nat 1%nat.
  sep auto.

  intros.
  sep destruct H68.
  sep lift 7%nat in H68.
  sep eexists.
  sep cancel 1%nat 1%nat.
  sep auto.


  hoare unfold.
  inverts H68.
  hoare forward.
  sep cancel 5%nat 1%nat.
  sep cancel 5%nat 1%nat.
  sep normal.
  sep eexists.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aisr.
  exact_s.

  Grab Existential Variables.
  auto.
  auto.
  auto.
Qed.  

Lemma OSSemPostProof:
  forall tid vl p r,
    Some p =
    BuildPreA' os_api OSSemPost
               sem_postapi vl OSLInv tid init_lg ->
    Some r =
    BuildRetA' os_api OSSemPost
               sem_postapi vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api OSSemPost = Some (t, d1, d2, s) /\
      {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|} |- tid {{p}} s {{Afalse}}.
Proof.
  init_spec.

  (* L1 - L2 *)
  lzh_hoare_if.
  hoare abscsq.  
  auto.
  eapply absimp_sem_post_null_return; pure_auto.
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
  intros.
  sep pauto.
  sep destruct H2.
  (* ** ac: Check disj_star_elim. *)
  (* ** ac: SearchAbout (_ \\// _). *)
  apply adisj_elim in H2.
  destruct H2.
  sep auto.
  sep auto.
  
  intros.
  sep auto.

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
  inverts H6.
  hoare abscsq.
  auto.
  eapply absimp_sem_post_p_not_legal_return; pauto.

  hoare forward prim.
  sep pauto.
  pure_auto.
  hoare forward.
(**********************************************************************************)
(***********************************  legal == 1 **********************************)
  lzh_hoare_if.
  pure_auto.
  inverts H16.
  lets Hget: eventsearch_after_get_H H2 H7; eauto.

  lzh_hoare_if.
  pure_auto.
  pure_auto.
  pure_auto.
  
  transform_pre sem_eventtype_neq_sem ltac:(sep cancel AEventData).
  hoare_split_pure_all.
  hoare abscsq.
  auto.
  eapply absimp_sem_post_wrong_type_return; pauto.

  (*********  exit critical ***********)
  fold_AEventNode_r.
  compose_evsllseg.
  fold_AECBList.

  hoare forward prim.
  exact_s.
  pauto.
  hoare forward.
(*******************************  type != sem finished **********************)
(*******************************  type = sem ********************************)
  lzh_simpl_int_eq.
  subst.
  transform_pre semacc_triangle_sem ltac:(sep cancel AEventData).
  hoare_split_pure_all.
  destruct H11 as [? [? ?]]. subst.

  hoare_unfold.
  lzh_hoare_if.
  pure_auto.
  pure_auto.
  pure_auto.
(************************** Grp = 0, no task wait ************************)
  Focus 2.
  lzh_hoare_if.
  pure_auto.
  pure_auto.
  
  lzh_simpl_int_eq.
  unfold AOSTCBPrioTbl.
  hoare_split_pure_all.
  assert (Hnil : x = nil).
  {
    lets Fnil: sempost_grp_wls_nil' H11 H6; eauto.
  }
  subst x.
  hoare forward.
  (* pure_auto. *)
  struct_type_match_solver.
  (* pure_auto. *)

  hoare abscsq.
  auto.
  eapply absimp_sem_post_put_sem_return; pauto.
  
  transform_pre sempost_inc_cnt_prop ltac:(sep cancel AEventData).
  hoare_split_pure_all.
  clear H5 H6.

  hoare forward prim.
  unfold AECBList.
  sep pauto.
  eapply lzh_evsllseg_compose.
  sep cancel evsllseg.
  sep cancel evsllseg.
  unfold AEventNode.
  sep cancel AEventData.
  unfold AOSEvent.
  unfold node.
  unfold AOSEventTbl.
  sep pauto; eauto.
  sep cancel Astruct.
  sep cancel Aarray.
  unfold AOSTCBPrioTbl.
  sep pauto.
  sep cancel 2%nat 1%nat.
  sep pauto.
  auto.
  auto.
  
  split; [auto | apply sempost_struct_type_vallist_match_sem; auto (* struct_type_vallist_match *)].
  unfolds; simpl.
  auto.
  eauto.
  eauto.
 
  lets Hnewjoin: ecb_get_set_join_join Hget H7 H18.
  destruct Hnewjoin as [? [? ?]].
  eapply semacc_compose_EcbList_P; eauto.


  eapply sempost_inc_RH_TCBList_ECBList_P_hold; eauto.
  pauto.
  hoare forward.

(********************** cnt = 65535, overflow! ************************)
  lzh_simpl_int_eq.
  unfold AOSTCBPrioTbl.
  hoare_split_pure_all.
  assert (Hnil : x = nil).
  {
    lets Fnil: sempost_grp_wls_nil' H11 H6; eauto.
  }
  subst x.
  hoare abscsq.
  auto.
  eapply absimp_sem_post_ovf_err_return; pauto.

  fold_AEventNode_r.
  compose_evsllseg.
  fold_AECBList.

  hoare forward prim.
  unfold AOSTCBPrioTbl.
  sep pauto.
  pauto.
  hoare forward.
(**************** trivial cases are all finished! ***********************)
  eapply sempost_part_0; eauto.
Qed.  
  
 
  
  
