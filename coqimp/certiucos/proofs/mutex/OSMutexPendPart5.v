Require Import sem_common.
Require Import sempend_pure.
Require Import OSMutex_common.
Require Import OSQPostPure.
Require Import mutex_pend_pure.
Open Scope code_scope.
Set Printing Depth 999.
Open Scope list_scope.

Lemma mutex_pend_ptcb_is_cur_err: forall
  (i : int32)
  (H1 : Int.unsigned i <= 65535)
  (v' v'0 v'1 v'2 v'3 v'4 : val)
  (v'5 v'6 v'7 : list vallist)
  (v'8 : list EventData)
  (v'9 : list os_inv.EventCtr)
  (v'10 : vallist)
  (v'11 v'12 : val)
  (v'13 : list vallist)
  (v'14 : vallist)
  (v'15 : list vallist)
  (v'16 : vallist)
  (v'17 : val)
  (v'18 : EcbMod.map)
  (v'19 : TcbMod.map)
  (v'20 : int32)
  (v'21 : addrval)
  (v'22 : val)
  (v'23 : list vallist)
  (v'26 v'27 : list os_inv.EventCtr)
  (v'28 v'29 : list EventData)
  (v'31 : vallist)
  (v'32 : val)
  (v'34 v'36 : list vallist)
  (v'37 : vallist)
  (v'38 : val)
  (v'39 : EcbMod.map)
  (tcbls : TcbMod.map)
  (v'42 : val)
  (v'44 : vallist)
  (v'46 : val)
  (v'47 v'48 v'49 : EcbMod.map)
  (v'51 : addrval)
  (H5 : ECBList_P v'46 Vnull v'27 v'29 v'48 tcbls)
  (H11 : EcbMod.join v'47 v'49 v'39)
  (H14 : length v'26 = length v'28)
  (v'24 : addrval)
  (pevent_addr : block)
  (H13 : array_type_vallist_match Int8u v'44)
  (H19 : length v'44 = ∘ OS_EVENT_TBL_SIZE)
  (H20 : isptr v'46)
  (x3 : val)
  (i0 : int32)
  (H22 : Int.unsigned i0 <= 255)
  (H18 : RL_Tbl_Grp_P v'44 (Vint32 i0))
  (H25 : isptr v'46)
  (H4 : ECBList_P v'42 (Vptr (pevent_addr, Int.zero)) v'26 v'28 v'47 tcbls)
  (H2 : isptr (Vptr (pevent_addr, Int.zero)))
  (H16 : id_addrval' (Vptr (pevent_addr, Int.zero)) OSEventTbl OS_EVENT = Some v'24)
  (H21 : Int.unsigned ($ OS_EVENT_TYPE_MUTEX) <= 255)
  (wls : waitset)
  (v'25 v'41 : val)
  (tcbls_l tcbls_r : TcbMod.map)
  (cur_addr : block)
  (H29 : v'32 <> Vnull)
  (Htcbjoin_whole : join tcbls_l tcbls_r tcbls)
  (Htcblist_subl : TCBList_P v'32 v'34 v'37 tcbls_l)
  (H28 : Vptr (cur_addr, Int.zero) <> Vnull)
  (x12 : val)
  (H35 : isptr x12)
  (cur_prio : int32)
  (H39 : Int.unsigned cur_prio <= 255)
  (i5 : int32)
  (H40 : Int.unsigned i5 <= 255)
  (i4 : int32)
  (H41 : Int.unsigned i4 <= 255)
  (i3 : int32)
  (H42 : Int.unsigned i3 <= 255)
  (i1 : int32)
  (H43 : Int.unsigned i1 <= 255)
  (H34 : isptr v'25)
  (H0 : RH_CurTCB (cur_addr, Int.zero) v'19)
  (H : RH_TCBList_ECBList_P v'39 tcbls (cur_addr, Int.zero))
  (H10 : RH_CurTCB (cur_addr, Int.zero) tcbls)
  (st : taskstatus)
  (Hneq_idle : cur_prio <> $ OS_IDLE_PRIO)
  (H37 : Int.unsigned ($ 0) <= 65535)
  (H38 : Int.unsigned ($ OS_STAT_RDY) <= 255)
  (H36 : isptr Vnull)
  (Hgetcur_subr : TcbMod.get tcbls_r (cur_addr, Int.zero) = Some (cur_prio, st, Vnull))
  (Hgetcur : TcbMod.get tcbls (cur_addr, Int.zero) = Some (cur_prio, st, Vnull))
  (x0 : val)
  (x2 : TcbMod.map)
  (Htcblist_subr : TCBList_P x0 v'36 v'37 x2)
  (x : int32)
  (F2 H23 : Int.unsigned x <= 65535)
  (Fneq_i2_1 : Int.unsigned (x >>ᵢ $ 8) <= 255)
  (Fneq_i2_2 : Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) <= 255)
  (Hmutex_not_avail : x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 <> $ OS_MUTEX_AVAILABLE)
  (Feq_i2_1 : x >>ᵢ $ 8 = Int.modu (x >>ᵢ $ 8) ($ Byte.modulus))
  (Hcur_prio : Int.ltu (x >>ᵢ $ 8) cur_prio = true)
  (ptcb_tid : addrval)
  (H24 : isptr (Vptr ptcb_tid))
  (H7 : R_ECB_ETbl_P (pevent_addr, Int.zero) (V$ OS_EVENT_TYPE_MUTEX :: Vint32 i0 :: Vint32 x :: Vptr ptcb_tid :: x3 :: v'46 :: nil, v'44)
         tcbls)
  (H3 : ECBList_P v'42 Vnull
         (v'26 ++ ((V$ OS_EVENT_TYPE_MUTEX :: Vint32 i0 :: Vint32 x :: Vptr ptcb_tid :: x3 :: v'46 :: nil, v'44) :: nil) ++ v'27)
         (v'28 ++ (DMutex (Vint32 x) (Vptr ptcb_tid) :: nil) ++ v'29) v'39 tcbls)
  (H8 : EcbMod.joinsig (pevent_addr, Int.zero) (absmutexsem (x >>ᵢ $ 8) (Some (ptcb_tid, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), wls) v'48 v'49)
  (Hget : EcbMod.get v'39 (pevent_addr, Int.zero) = Some (absmutexsem (x >>ᵢ $ 8) (Some (ptcb_tid, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), wls))
  (H26 : RH_ECB_P (absmutexsem (x >>ᵢ $ 8) (Some (ptcb_tid, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), wls))
  (H6 : RLH_ECBData_P (DMutex (Vint32 x) (Vptr ptcb_tid)) (absmutexsem (x >>ᵢ $ 8) (Some (ptcb_tid, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), wls))
  (ptcb_prio : priority)
  (xm : msg)
  (xs : taskstatus)
  (H_ptcb : TcbMod.get tcbls ptcb_tid = Some (ptcb_prio, xs, xm))
  (H12 : isptr x0)
  (Hcurnode : TCBNode_P
               (x0
                :: v'25
                   :: x12 :: Vnull :: V$ 0 :: V$ OS_STAT_RDY :: Vint32 cur_prio :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i1 :: nil)
               v'37 (cur_prio, st, Vnull))
  (Htcbjoin_right : TcbJoin (cur_addr, Int.zero) (cur_prio, st, Vnull) x2 tcbls_r)
  (LHift_true : val_inj
                 (let (b, ofs) := ptcb_tid in
                  if peq b cur_addr
                  then if Int.eq ofs Int.zero then Some (Vint32 Int.one) else Some (Vint32 Int.zero)
                  else Some (Vint32 Int.zero)) <> Vint32 Int.zero /\
               val_inj
                 (let (b, ofs) := ptcb_tid in
                  if peq b cur_addr
                  then if Int.eq ofs Int.zero then Some (Vint32 Int.one) else Some (Vint32 Int.zero)
                  else Some (Vint32 Int.zero)) <> Vnull /\
               val_inj
                 (let (b, ofs) := ptcb_tid in
                  if peq b cur_addr
                  then if Int.eq ofs Int.zero then Some (Vint32 Int.one) else Some (Vint32 Int.zero)
                  else Some (Vint32 Int.zero)) <> Vundef)
(* ================================= *) ,
   {|OS_spec, GetHPrio, OSLInv, I,
   fun v : option val =>
   ( <|| END v ||>  **
    p_local OSLInv (cur_addr, Int.zero) init_lg **
    ((EX v0 : val, LV timeout @ Int16u |-> v0) **
     (EX v0 : val, LV pevent @ OS_EVENT ∗ |-> v0) **
     (EX v0 : val, LV legal @ Int8u |-> v0) **
     (EX v0 : val, LV pip @ Int8u |-> v0) **
     (EX v0 : val, LV mprio @ Int8u |-> v0) **
     (EX v0 : val, LV os_code_defs.isrdy @ Int8u |-> v0) **
     (EX v0 : val, LV ptcb @ OS_TCB ∗ |-> v0) ** (EX v0 : val, LV pevent2 @ OS_EVENT ∗ |-> v0) ** Aemp) **
    Aie true ** Ais nil ** Acs nil ** Aisr empisr) **
   A_dom_lenv
     ((timeout, Int16u)
      :: (pevent, OS_EVENT ∗)
         :: (legal, Int8u)
            :: (pip, Int8u) :: (mprio, Int8u) :: (os_code_defs.isrdy, Int8u) :: (ptcb, OS_TCB ∗) :: (pevent2, OS_EVENT ∗) :: nil),
   Afalse|}|- (cur_addr, Int.zero)
   {{ <|| mutexpend (Vptr (pevent_addr, Int.zero) :: Vint32 i :: nil) ||>  **
     LV ptcb @ OS_TCB ∗ |-> Vptr ptcb_tid **
     LV mprio @ Int8u |-> Vint32 (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) **
     LV pip @ Int8u |-> Vint32 (x >>ᵢ $ 8) **
     Astruct (cur_addr, Int.zero) OS_TCB_flag
       (x0 :: v'25 :: x12 :: Vnull :: V$ 0 :: V$ OS_STAT_RDY :: Vint32 cur_prio :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i1 :: nil) **
     dllseg x0 (Vptr (cur_addr, Int.zero)) v'41 Vnull v'36 OS_TCB_flag (fun vl : vallist => nth_val 1 vl)
       (fun vl : vallist => nth_val 0 vl) **
     GV OSTCBList @ OS_TCB ∗ |-> v'32 **
     dllseg v'32 Vnull v'25 (Vptr (cur_addr, Int.zero)) v'34 OS_TCB_flag (fun vl : vallist => nth_val 1 vl)
       (fun vl : vallist => nth_val 0 vl) **
     GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_addr, Int.zero) **
     AEventData (V$ OS_EVENT_TYPE_MUTEX :: Vint32 i0 :: Vint32 x :: Vptr ptcb_tid :: x3 :: v'46 :: nil)
       (DMutex (Vint32 x) (Vptr ptcb_tid)) **
     Astruct (pevent_addr, Int.zero) OS_EVENT (V$ OS_EVENT_TYPE_MUTEX :: Vint32 i0 :: Vint32 x :: Vptr ptcb_tid :: x3 :: v'46 :: nil) **
     Aarray v'24 (Tarray Int8u ∘ OS_EVENT_TBL_SIZE) v'44 **
     Aie false **
     Ais nil **
     Acs (true :: nil) **
     Aisr empisr **
     GV OSEventList @ OS_EVENT ∗ |-> v'42 **
     evsllseg v'42 (Vptr (pevent_addr, Int.zero)) v'26 v'28 **
     evsllseg v'46 Vnull v'27 v'29 **
     A_isr_is_prop **
     tcbdllflag v'32
       (v'34 ++
        (x0
         :: v'25 :: x12 :: Vnull :: V$ 0 :: V$ OS_STAT_RDY :: Vint32 cur_prio :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i1 :: nil)
        :: v'36) **
     AOSRdyTblGrp v'37 v'38 **
     AOSTCBPrioTbl v'31 v'37 tcbls v'51 **
     HECBList v'39 **
     HTCBList tcbls **
     HCurTCB (cur_addr, Int.zero) **
     p_local OSLInv (cur_addr, Int.zero) init_lg **
     LV legal @ Int8u |-> (V$ 1) **
     AOSEventFreeList v'5 **
     AOSQFreeList v'6 **
     AOSQFreeBlk v'7 **
     AOSMapTbl **
     AOSUnMapTbl **
     AOSIntNesting **
     AOSTCBFreeList v'22 v'23 **
     AOSTime (Vint32 v'20) **
     HTime v'20 **
     AGVars **
     atoy_inv' **
     LV pevent2 @ OS_EVENT ∗ |-> v'4 **
     LV os_code_defs.isrdy @ Int8u |-> v'2 **
     LV timeout @ Int16u |-> Vint32 i **
     LV pevent @ OS_EVENT ∗ |-> Vptr (pevent_addr, Int.zero) **
     A_dom_lenv
       ((timeout, Int16u)
        :: (pevent, OS_EVENT ∗)
           :: (legal, Int8u)
              :: (pip, Int8u) :: (mprio, Int8u) :: (os_code_defs.isrdy, Int8u) :: (ptcb, OS_TCB ∗) :: (pevent2, OS_EVENT ∗) :: nil)}} 
   EXIT_CRITICAL;ₛ
   RETURN ′ OS_ERR_MUTEX_DEADLOCK {{Afalse}}
.
Proof.
  intros.
  destruct ptcb_tid as (ptcb_addr& ptcb_off).
  assert (Hptcb_is_cur: ptcb_addr = cur_addr /\ ptcb_off = Int.zero).
  {
    clear -LHift_true.
    generalize LHift_true.
    clear LHift_true.
    destruct (peq ptcb_addr cur_addr) eqn:F1;
      destruct (Int.eq ptcb_off Int.zero) eqn:F2;
      unfold val_inj;
      lzh_simpl_int_eq;
      subst;
      solve [auto
            | intro H; destruct H; tryfalse].
  }
  clear LHift_true.
  destruct Hptcb_is_cur as (Htmp1 & Htmp2);
    subst ptcb_addr; subst ptcb_off.
(************************* intro cur_stat = rdy *************************)
  hoare lift 22%nat pre.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  hoare_split_pure_all.

  
  transform_pre AOSRdyTblGrp_fold ltac:(sep cancel GAarray;
                                        sep cancel AOSRdyGrp).
  rename v'37 into os_rdy_tbl.
  destruct H9 as (Hrtbl_type & Hrtbl_len).
  destruct H15 as (Hgrp1 & Hgrp2).

  hoare lifts (2::3::4::5::6::7::8::9::10::11::12::13::14
                ::15::16::17::18::19::20::21::22::nil)%nat pre.

  
  assert (Htmp1: st = rdy).
  {
    clear -Hcurnode Hrtbl_type Hrtbl_len.
    eapply mutexpend_TCBNode_P_in_tcb_rdy; eauto.
  }
  subst st.
(***************************** imply rdy end *****************************)
(****************************** ex critical ******************************)
  hoare abscsq.
  Hint Resolve noabs_oslinv.
  Hint Extern 2 (_ <= _) => apply Z.leb_le; trivial.
  auto.
  eapply absinfer_mutex_pend_ptcb_is_cur; eauto.
  can_change_aop_solver.
  
  hoare forward prim.

  {
    (** * AECBList *)
    unfold AECBList.
    sep pauto.
    
    eapply lzh_evsllseg_compose.
    sep cancel evsllseg.
    sep cancel evsllseg.
    unfold AEventNode.
    sep pauto.
    sep cancel AEventData.
    unfold AOSEvent.
    sep pauto.
    unfold AOSEventTbl.
    unfold node.
    sep pauto.
    sep cancel 9%nat 1%nat.
    sep cancel Aarray.

    (** * AOSTCBList *)
    unfold AOSTCBList.
    unfold tcbdllseg.
    sep pauto.
    sep cancel 6%nat 1%nat.
    unfold dllseg.
    fold dllseg.
    unfold node.
    sep pauto.
    sep cancel Astruct.
    sep cancel dllseg.
    sep cancel 4%nat 1%nat.
    exact_s.
    unfolds; auto.
    unfolds; auto.
    split; [auto | struct_type_match_solver].
    unfold TCBList_P.
    fold TCBList_P.
    do 4 eexists.
    splits; eauto.
    unfolds; auto.
    eauto.
    eauto.
    eauto.
    split; [auto | struct_type_match_solver].
    eauto.
    unfolds; auto.
    eauto.
    unfolds; auto.
    eauto.
    eauto.
    eauto.
  }
  pauto.
  hoare forward.
Qed.

Lemma mutex_pend_ptcb_is_idle_err_left_to_cur: forall
  (i : int32)
  (H1 : Int.unsigned i <= 65535)
  (v' v'0 v'1 v'2 v'3 v'4 : val)
  (v'5 v'6 v'7 : list vallist)
  (v'8 : list EventData)
  (v'9 : list os_inv.EventCtr)
  (v'10 : vallist)
  (v'11 v'12 : val)
  (v'13 : list vallist)
  (v'14 : vallist)
  (v'15 : list vallist)
  (v'16 : vallist)
  (v'17 : val)
  (v'18 : EcbMod.map)
  (v'19 : TcbMod.map)
  (v'20 : int32)
  (v'21 : addrval)
  (v'22 : val)
  (v'23 : list vallist)
  (v'26 v'27 : list os_inv.EventCtr)
  (v'28 v'29 : list EventData)
  (v'31 : vallist)
  (v'32 : val)
  (v'36 : list vallist)
  (v'37 : vallist)
  (v'38 : val)
  (v'39 : EcbMod.map)
  (tcbls : TcbMod.map)
  (v'42 : val)
  (v'44 : vallist)
  (v'46 : val)
  (v'47 v'48 v'49 : EcbMod.map)
  (v'51 : addrval)
  (H5 : ECBList_P v'46 Vnull v'27 v'29 v'48 tcbls)
  (H11 : EcbMod.join v'47 v'49 v'39)
  (H14 : length v'26 = length v'28)
  (v'24 : addrval)
  (pevent_addr : block)
  (H13 : array_type_vallist_match Int8u v'44)
  (H19 : length v'44 = ∘ OS_EVENT_TBL_SIZE)
  (H20 : isptr v'46)
  (x3 : val)
  (i0 : int32)
  (H22 : Int.unsigned i0 <= 255)
  (H18 : RL_Tbl_Grp_P v'44 (Vint32 i0))
  (H25 : isptr v'46)
  (H4 : ECBList_P v'42 (Vptr (pevent_addr, Int.zero)) v'26 v'28
         v'47 tcbls)
  (H2 : isptr (Vptr (pevent_addr, Int.zero)))
  (H16 : id_addrval' (Vptr (pevent_addr, Int.zero)) OSEventTbl
          OS_EVENT = Some v'24)
  (H21 : Int.unsigned ($ OS_EVENT_TYPE_MUTEX) <= 255)
  (wls : waitset)
  (v'25 v'41 : val)
  (tcbls_l tcbls_r : TcbMod.map)
  (cur_addr : block)
  (H29 : v'32 <> Vnull)
  (Htcbjoin_whole : join tcbls_l tcbls_r tcbls)
  (H28 : Vptr (cur_addr, Int.zero) <> Vnull)
  (x12 : val)
  (H35 : isptr x12)
  (cur_prio : int32)
  (H39 : Int.unsigned cur_prio <= 255)
  (i5 : int32)
  (H40 : Int.unsigned i5 <= 255)
  (i4 : int32)
  (H41 : Int.unsigned i4 <= 255)
  (i3 : int32)
  (H42 : Int.unsigned i3 <= 255)
  (i1 : int32)
  (H43 : Int.unsigned i1 <= 255)
  (H34 : isptr v'25)
  (H0 : RH_CurTCB (cur_addr, Int.zero) v'19)
  (H : RH_TCBList_ECBList_P v'39 tcbls (cur_addr, Int.zero))
  (H10 : RH_CurTCB (cur_addr, Int.zero) tcbls)
  (st : taskstatus)
  (Hneq_idle : cur_prio <> $ OS_IDLE_PRIO)
  (H37 : Int.unsigned ($ 0) <= 65535)
  (H38 : Int.unsigned ($ OS_STAT_RDY) <= 255)
  (H36 : isptr Vnull)
  (Hgetcur_subr : TcbMod.get tcbls_r (cur_addr, Int.zero) =
                 Some (cur_prio, st, Vnull))
  (Hgetcur : TcbMod.get tcbls (cur_addr, Int.zero) =
            Some (cur_prio, st, Vnull))
  (x0 : val)
  (x2 : TcbMod.map)
  (Htcblist_subr : TCBList_P x0 v'36 v'37 x2)
  (x : int32)
  (F2 H23 : Int.unsigned x <= 65535)
  (Fneq_i2_1 : Int.unsigned (x >>ᵢ $ 8) <= 255)
  (Fneq_i2_2 : Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) <= 255)
  (Hmutex_not_avail : x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 <>
                     $ OS_MUTEX_AVAILABLE)
  (Feq_i2_1 : x >>ᵢ $ 8 = Int.modu (x >>ᵢ $ 8) ($ Byte.modulus))
  (Hcur_prio : Int.ltu (x >>ᵢ $ 8) cur_prio = true)
  (ptcb_prio : priority)
  (xm : msg)
  (xs : taskstatus)
  (H12 : isptr x0)
  (Hcurnode : TCBNode_P
               (x0
                :: v'25
                   :: x12
                      :: Vnull
                         :: V$ 0
                            :: V$ OS_STAT_RDY
                               :: Vint32 cur_prio
                                  :: Vint32 i5
                                     :: Vint32 i4
                                        :: 
                                        Vint32 i3
                                        :: 
                                        Vint32 i1 :: nil) v'37
               (cur_prio, st, Vnull))
  (Htcbjoin_right : TcbJoin (cur_addr, Int.zero)
                     (cur_prio, st, Vnull) x2 tcbls_r)
  (v'33 v'35 : list vallist)
  (v'43 v'45 : val)
  (tcbls_sub_l v'52 tcbls_sub_r : TcbMod.map)
  (Htcbjoin_sub_whole : TcbMod.join tcbls_sub_l v'52 tcbls_l)
  (Htcblist_sub_left : TCBList_P v'32 v'33 v'37 tcbls_sub_l)
  (Htcblist_sub_right : TCBList_P v'45 v'35 v'37 tcbls_sub_r)
  (ptcb_addr : block)
  (x11 : val)
  (H31 : isptr x11)
  (i11 : int32)
  (H33 : Int.unsigned i11 <= 65535)
  (i10 : int32)
  (H44 : Int.unsigned i10 <= 255)
  (i8 : int32)
  (H46 : Int.unsigned i8 <= 255)
  (i7 : int32)
  (H47 : Int.unsigned i7 <= 255)
  (i6 : int32)
  (H48 : Int.unsigned i6 <= 255)
  (i2 : int32)
  (H49 : Int.unsigned i2 <= 255)
  (H30 : isptr v'43)
  (H17 : isptr v'45)
  (H24 : isptr (Vptr (ptcb_addr, Int.zero)))
  (H7 : R_ECB_ETbl_P (pevent_addr, Int.zero)
         (V$ OS_EVENT_TYPE_MUTEX
          :: Vint32 i0
             :: Vint32 x
                :: Vptr (ptcb_addr, Int.zero)
                   :: x3 :: v'46 :: nil, v'44) tcbls)
  (H3 : ECBList_P v'42 Vnull
         (v'26 ++
          ((V$ OS_EVENT_TYPE_MUTEX
            :: Vint32 i0
               :: Vint32 x
                  :: Vptr (ptcb_addr, Int.zero)
                     :: x3 :: v'46 :: nil, v'44) :: nil) ++ v'27)
         (v'28 ++
          (DMutex (Vint32 x) (Vptr (ptcb_addr, Int.zero)) :: nil) ++
          v'29) v'39 tcbls)
  (H8 : EcbMod.joinsig (pevent_addr, Int.zero)
         (absmutexsem (x >>ᵢ $ 8)
            (Some
               (ptcb_addr, Int.zero, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)),
         wls) v'48 v'49)
  (Hget : EcbMod.get v'39 (pevent_addr, Int.zero) =
         Some
           (absmutexsem (x >>ᵢ $ 8)
              (Some
                 (ptcb_addr, Int.zero,
                 x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), wls))
  (H26 : RH_ECB_P
          (absmutexsem (x >>ᵢ $ 8)
             (Some
                (ptcb_addr, Int.zero,
                x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), wls))
  (H6 : RLH_ECBData_P
         (DMutex (Vint32 x) (Vptr (ptcb_addr, Int.zero)))
         (absmutexsem (x >>ᵢ $ 8)
            (Some
               (ptcb_addr, Int.zero, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)),
         wls))
  (H_ptcb : TcbMod.get tcbls (ptcb_addr, Int.zero) =
           Some (ptcb_prio, xs, xm))
  (H_ptcb_not_cur : (ptcb_addr, Int.zero) <> (cur_addr, Int.zero))
  (H_ptcb_in_left : TcbMod.get tcbls_l (ptcb_addr, Int.zero) =
                   Some (ptcb_prio, xs, xm))
  (Htcbjoin_sub_right : TcbMod.joinsig (ptcb_addr, Int.zero)
                         (ptcb_prio, xs, xm) tcbls_sub_r v'52)
  (Hget_last_tcb : get_last_tcb_ptr v'33 v'32 =
                  Some (Vptr (ptcb_addr, Int.zero)))
  (H32 : isptr xm)
  (H45 : Int.unsigned ptcb_prio <= 255)
  (Hptcb_node : TCBNode_P
                 (v'45
                  :: v'43
                     :: x11
                        :: xm
                           :: Vint32 i11
                              :: Vint32 i10
                                 :: Vint32 ptcb_prio
                                    :: Vint32 i8
                                       :: 
                                       Vint32 i7
                                       :: 
                                       Vint32 i6
                                       :: 
                                       Vint32 i2 :: nil) v'37
                 (ptcb_prio, xs, xm))
  (Htcblist_subl : TCBList_P v'32
                    (v'33 ++
                     (v'45
                      :: v'43
                         :: x11
                            :: xm
                               :: Vint32 i11
                                  :: Vint32 i10
                                     :: Vint32 ptcb_prio
                                        :: 
                                        Vint32 i8
                                        :: 
                                        Vint32 i7
                                        :: 
                                        Vint32 i6
                                        :: 
                                        Vint32 i2 :: nil)
                     :: v'35) v'37 tcbls_l)
  (Hptcb_blk : RL_TCBblk_P
                (v'45
                 :: v'43
                    :: x11
                       :: xm
                          :: Vint32 i11
                             :: Vint32 i10
                                :: Vint32 ptcb_prio
                                   :: Vint32 i8
                                      :: Vint32 i7
                                         :: 
                                         Vint32 i6
                                         :: 
                                         Vint32 i2 :: nil))
  (Hptcb_stat : R_TCB_Status_P
                 (v'45
                  :: v'43
                     :: x11
                        :: xm
                           :: Vint32 i11
                              :: Vint32 i10
                                 :: Vint32 ptcb_prio
                                    :: Vint32 i8
                                       :: 
                                       Vint32 i7
                                       :: 
                                       Vint32 i6
                                       :: 
                                       Vint32 i2 :: nil) v'37
                 (ptcb_prio, xs, xm))
  (LHift_true : Int.eq ptcb_prio ($ OS_IDLE_PRIO) = true)
(* ================================= *) ,
   {|OS_spec, GetHPrio, OSLInv, I,
   fun v : option val =>
   ( <|| END v ||>  **
    p_local OSLInv (cur_addr, Int.zero) init_lg **
    ((EX v0 : val, LV timeout @ Int16u |-> v0) **
     (EX v0 : val, LV pevent @ OS_EVENT ∗ |-> v0) **
     (EX v0 : val, LV legal @ Int8u |-> v0) **
     (EX v0 : val, LV pip @ Int8u |-> v0) **
     (EX v0 : val, LV mprio @ Int8u |-> v0) **
     (EX v0 : val, LV os_code_defs.isrdy @ Int8u |-> v0) **
     (EX v0 : val, LV ptcb @ OS_TCB ∗ |-> v0) **
     (EX v0 : val, LV pevent2 @ OS_EVENT ∗ |-> v0) ** Aemp) **
    Aie true ** Ais nil ** Acs nil ** Aisr empisr) **
   A_dom_lenv
     ((timeout, Int16u)
      :: (pevent, OS_EVENT ∗)
         :: (legal, Int8u)
            :: (pip, Int8u)
               :: (mprio, Int8u)
                  :: (os_code_defs.isrdy, Int8u)
                     :: (ptcb, OS_TCB ∗)
                        :: (pevent2, OS_EVENT ∗) :: nil),
   Afalse|}|- (cur_addr, Int.zero)
   {{Astruct (ptcb_addr, Int.zero) OS_TCB_flag
       (v'45
        :: v'43
           :: x11
              :: xm
                 :: Vint32 i11
                    :: Vint32 i10
                       :: Vint32 ptcb_prio
                          :: Vint32 i8
                             :: Vint32 i7
                                :: Vint32 i6 :: Vint32 i2 :: nil) **
     tcbdllseg v'32 Vnull v'43 (Vptr (ptcb_addr, Int.zero)) v'33 **
     tcbdllseg v'45 (Vptr (ptcb_addr, Int.zero)) v'25
       (Vptr (cur_addr, Int.zero)) v'35 **
      <||
     mutexpend (Vptr (pevent_addr, Int.zero) :: Vint32 i :: nil)
     ||>  **
     LV ptcb @ OS_TCB ∗ |-> Vptr (ptcb_addr, Int.zero) **
     LV mprio @ Int8u |-> Vint32 (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) **
     LV pip @ Int8u |-> Vint32 (x >>ᵢ $ 8) **
     Astruct (cur_addr, Int.zero) OS_TCB_flag
       (x0
        :: v'25
           :: x12
              :: Vnull
                 :: V$ 0
                    :: V$ OS_STAT_RDY
                       :: Vint32 cur_prio
                          :: Vint32 i5
                             :: Vint32 i4
                                :: Vint32 i3 :: Vint32 i1 :: nil) **
     dllseg x0 (Vptr (cur_addr, Int.zero)) v'41 Vnull v'36
       OS_TCB_flag (fun vl : vallist => nth_val 1 vl)
       (fun vl : vallist => nth_val 0 vl) **
     GV OSTCBList @ OS_TCB ∗ |-> v'32 **
     GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_addr, Int.zero) **
     AEventData
       (V$ OS_EVENT_TYPE_MUTEX
        :: Vint32 i0
           :: Vint32 x
              :: Vptr (ptcb_addr, Int.zero) :: x3 :: v'46 :: nil)
       (DMutex (Vint32 x) (Vptr (ptcb_addr, Int.zero))) **
     Astruct (pevent_addr, Int.zero) OS_EVENT
       (V$ OS_EVENT_TYPE_MUTEX
        :: Vint32 i0
           :: Vint32 x
              :: Vptr (ptcb_addr, Int.zero) :: x3 :: v'46 :: nil) **
     Aarray v'24 (Tarray Int8u ∘ OS_EVENT_TBL_SIZE) v'44 **
     Aie false **
     Ais nil **
     Acs (true :: nil) **
     Aisr empisr **
     GV OSEventList @ OS_EVENT ∗ |-> v'42 **
     evsllseg v'42 (Vptr (pevent_addr, Int.zero)) v'26 v'28 **
     evsllseg v'46 Vnull v'27 v'29 **
     A_isr_is_prop **
     tcbdllflag v'32
       ((v'33 ++
         (v'45
          :: v'43
             :: x11
                :: xm
                   :: Vint32 i11
                      :: Vint32 i10
                         :: Vint32 ptcb_prio
                            :: Vint32 i8
                               :: Vint32 i7
                                  :: Vint32 i6
                                     :: Vint32 i2 :: nil)
         :: v'35) ++
        (x0
         :: v'25
            :: x12
               :: Vnull
                  :: V$ 0
                     :: V$ OS_STAT_RDY
                        :: Vint32 cur_prio
                           :: Vint32 i5
                              :: Vint32 i4
                                 :: Vint32 i3
                                    :: Vint32 i1 :: nil) :: v'36) **
     AOSRdyTblGrp v'37 v'38 **
     AOSTCBPrioTbl v'31 v'37 tcbls v'51 **
     HECBList v'39 **
     HTCBList tcbls **
     HCurTCB (cur_addr, Int.zero) **
     p_local OSLInv (cur_addr, Int.zero) init_lg **
     LV legal @ Int8u |-> (V$ 1) **
     AOSEventFreeList v'5 **
     AOSQFreeList v'6 **
     AOSQFreeBlk v'7 **
     AOSMapTbl **
     AOSUnMapTbl **
     AOSIntNesting **
     AOSTCBFreeList v'22 v'23 **
     AOSTime (Vint32 v'20) **
     HTime v'20 **
     AGVars **
     atoy_inv' **
     LV pevent2 @ OS_EVENT ∗ |-> v'4 **
     LV os_code_defs.isrdy @ Int8u |-> v'2 **
     LV timeout @ Int16u |-> Vint32 i **
     LV pevent @ OS_EVENT ∗ |-> Vptr (pevent_addr, Int.zero) **
     A_dom_lenv
       ((timeout, Int16u)
        :: (pevent, OS_EVENT ∗)
           :: (legal, Int8u)
              :: (pip, Int8u)
                 :: (mprio, Int8u)
                    :: (os_code_defs.isrdy, Int8u)
                       :: (ptcb, OS_TCB ∗)
                          :: (pevent2, OS_EVENT ∗) :: nil)}} 
   EXIT_CRITICAL;ₛ
   RETURN ′ OS_ERR_MUTEX_IDLE {{Afalse}}
.
Proof.
  intros.
  idtac.
  assert (Hptcb_prio_idle: ptcb_prio = $ OS_IDLE_PRIO).
  {
    clear -LHift_true.
    lzh_simpl_int_eq.
    auto.
  }    
  clear LHift_true.
  subst ptcb_prio.
  
(************************* intro cur_stat = rdy *************************)
  hoare lift 24%nat pre.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  hoare_split_pure_all.

  
  transform_pre AOSRdyTblGrp_fold ltac:(sep cancel GAarray;
                                        sep cancel AOSRdyGrp).
  rename v'37 into os_rdy_tbl.
  destruct H9 as (Hrtbl_type & Hrtbl_len).
  destruct H15 as (Hgrp1 & Hgrp2).

  hoare lifts (2::3::4::5::6::7::8::9::10::11::12::13::14
                ::15::16::17::18::19::20::21::23::24::nil)%nat pre.
  
  assert (Htmp1: st = rdy).
  {
    clear -Hcurnode Hrtbl_type Hrtbl_len.
    eapply mutexpend_TCBNode_P_in_tcb_rdy; eauto.
  }
  subst st.
(***************************** imply rdy end *****************************)
(****************************** ex critical ******************************)
  hoare abscsq.
  auto.
  eapply absinfer_mutex_pend_ptcb_is_idle; eauto.
  can_change_aop_solver.
  
  hoare forward prim.

  {
    (** * AECBList *)
    unfold AECBList.
    sep pauto.
    
    eapply lzh_evsllseg_compose.
    sep cancel evsllseg.
    sep cancel evsllseg.
    unfold AEventNode.
    sep pauto.
    sep cancel AEventData.
    unfold AOSEvent.
    sep pauto.
    unfold AOSEventTbl.
    unfold node.
    sep pauto.
    sep cancel 11%nat 1%nat.
    sep cancel Aarray.

    (** * AOSTCBList *)
    unfold AOSTCBList.
    unfold tcbdllseg.
    sep pauto.
    (**** cancel right first *)
    sep lift 2%nat.
    unfold dllseg.
    fold dllseg.
    sep pauto.
    sep cancel 8%nat 2%nat.
    unfold node.
    sep pauto.
    sep cancel 7%nat 1%nat.
    (**** cancel left *)
    (* ** ac: Check tcbdllseg_compose. *)
    eapply tcbdllseg_compose with
      (l1:=v'33)
      (l2:=(v'45
             :: v'43
                :: x11
                   :: xm
                      :: Vint32 i11
                         :: Vint32 i10
                            :: V$OS_IDLE_PRIO
                               :: Vint32 i8
                                  :: Vint32 i7
                                     :: Vint32 i6 :: Vint32 i2 :: nil)::v'35).
    sep cancel tcbdllseg.
    unfold tcbdllseg in *.
    unfold dllseg.
    fold dllseg.
    sep pauto.
    unfold node.
    sep pauto.
    sep cancel Astruct.
    sep cancel dllseg.
    sep cancel 4%nat 1%nat.
    exact_s.
    
    split; [auto | struct_type_match_solver].
    pure_auto.
    (* unfolds; auto. *)
    split; [auto | struct_type_match_solver].
    unfolds; auto.
    unfolds; auto.

    (**** cancel tcblist_p right *)
    unfold TCBList_P.
    fold TCBList_P.
    do 4 eexists.
    splits; eauto.
    unfolds; auto.
    (**** cancel tcblist_p left *)
    eapply TCBList_P_Combine with 
      (l1:=v'33)
      (l2:=(v'45
             :: v'43
                :: x11
                   :: xm
                      :: Vint32 i11
                         :: Vint32 i10
                            :: V$OS_IDLE_PRIO
                               :: Vint32 i8
                                  :: Vint32 i7
                                     :: Vint32 i6 :: Vint32 i2 :: nil)::v'35).
    eauto.
    apply Htcbjoin_sub_whole.
    auto.
    unfold TCBList_P.
    fold TCBList_P.
    do 4 eexists.
    splits; eauto.
    unfolds; auto.

    eauto.
    eauto.
    split; [auto | struct_type_match_solver].
    eauto.
    unfolds; auto.
    eauto.
    unfolds; auto.
    eauto.
    eauto.
    eauto.
  }
  pauto.
  hoare forward.
Qed.

Lemma mutex_pend_ptcb_is_not_rdy_left_to_cur: forall
  (i : int32)
  (H1 : Int.unsigned i <= 65535)
  (v' v'0 v'1 v'2 v'3 v'4 : val)
  (v'5 v'6 v'7 : list vallist)
  (v'8 : list EventData)
  (v'9 : list os_inv.EventCtr)
  (v'10 : vallist)
  (v'11 v'12 : val)
  (v'13 : list vallist)
  (v'14 : vallist)
  (v'15 : list vallist)
  (v'16 : vallist)
  (v'17 : val)
  (v'18 : EcbMod.map)
  (v'19 : TcbMod.map)
  (v'20 : int32)
  (v'21 : addrval)
  (v'22 : val)
  (v'23 : list vallist)
  (v'26 v'27 : list os_inv.EventCtr)
  (v'28 v'29 : list EventData)
  (v'31 : vallist)
  (v'32 : val)
  (v'36 : list vallist)
  (v'37 : vallist)
  (v'38 : val)
  (v'39 : EcbMod.map)
  (tcbls : TcbMod.map)
  (v'42 : val)
  (v'44 : vallist)
  (v'46 : val)
  (v'47 v'48 v'49 : EcbMod.map)
  (v'51 : addrval)
  (H5 : ECBList_P v'46 Vnull v'27 v'29 v'48 tcbls)
  (H11 : EcbMod.join v'47 v'49 v'39)
  (H14 : length v'26 = length v'28)
  (v'24 : addrval)
  (pevent_addr : block)
  (H13 : array_type_vallist_match Int8u v'44)
  (H19 : length v'44 = ∘ OS_EVENT_TBL_SIZE)
  (H20 : isptr v'46)
  (x3 : val)
  (i0 : int32)
  (H22 : Int.unsigned i0 <= 255)
  (H18 : RL_Tbl_Grp_P v'44 (Vint32 i0))
  (H25 : isptr v'46)
  (H4 : ECBList_P v'42 (Vptr (pevent_addr, Int.zero)) v'26 v'28
         v'47 tcbls)
  (H2 : isptr (Vptr (pevent_addr, Int.zero)))
  (H16 : id_addrval' (Vptr (pevent_addr, Int.zero)) OSEventTbl
          OS_EVENT = Some v'24)
  (H21 : Int.unsigned ($ OS_EVENT_TYPE_MUTEX) <= 255)
  (wls : waitset)
  (v'25 v'41 : val)
  (tcbls_l tcbls_r : TcbMod.map)
  (cur_addr : block)
  (H29 : v'32 <> Vnull)
  (Htcbjoin_whole : join tcbls_l tcbls_r tcbls)
  (H28 : Vptr (cur_addr, Int.zero) <> Vnull)
  (x12 : val)
  (H35 : isptr x12)
  (cur_prio : int32)
  (H39 : Int.unsigned cur_prio <= 255)
  (i5 : int32)
  (H40 : Int.unsigned i5 <= 255)
  (i4 : int32)
  (H41 : Int.unsigned i4 <= 255)
  (i3 : int32)
  (H42 : Int.unsigned i3 <= 255)
  (i1 : int32)
  (H43 : Int.unsigned i1 <= 255)
  (H34 : isptr v'25)
  (H0 : RH_CurTCB (cur_addr, Int.zero) v'19)
  (H : RH_TCBList_ECBList_P v'39 tcbls (cur_addr, Int.zero))
  (H10 : RH_CurTCB (cur_addr, Int.zero) tcbls)
  (st : taskstatus)
  (Hneq_idle : cur_prio <> $ OS_IDLE_PRIO)
  (H37 : Int.unsigned ($ 0) <= 65535)
  (H38 : Int.unsigned ($ OS_STAT_RDY) <= 255)
  (H36 : isptr Vnull)
  (Hgetcur_subr : TcbMod.get tcbls_r (cur_addr, Int.zero) =
                 Some (cur_prio, st, Vnull))
  (Hgetcur : TcbMod.get tcbls (cur_addr, Int.zero) =
            Some (cur_prio, st, Vnull))
  (x0 : val)
  (x2 : TcbMod.map)
  (Htcblist_subr : TCBList_P x0 v'36 v'37 x2)
  (x : int32)
  (F2 H23 : Int.unsigned x <= 65535)
  (Fneq_i2_1 : Int.unsigned (x >>ᵢ $ 8) <= 255)
  (Fneq_i2_2 : Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) <= 255)
  (Hmutex_not_avail : x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 <>
                     $ OS_MUTEX_AVAILABLE)
  (Feq_i2_1 : x >>ᵢ $ 8 = Int.modu (x >>ᵢ $ 8) ($ Byte.modulus))
  (Hcur_prio : Int.ltu (x >>ᵢ $ 8) cur_prio = true)
  (ptcb_prio : priority)
  (xm : msg)
  (xs : taskstatus)
  (H12 : isptr x0)
  (Hcurnode : TCBNode_P
               (x0
                :: v'25
                   :: x12
                      :: Vnull
                         :: V$ 0
                            :: V$ OS_STAT_RDY
                               :: Vint32 cur_prio
                                  :: Vint32 i5
                                     :: Vint32 i4
                                        :: 
                                        Vint32 i3
                                        :: 
                                        Vint32 i1 :: nil) v'37
               (cur_prio, st, Vnull))
  (Htcbjoin_right : TcbJoin (cur_addr, Int.zero)
                     (cur_prio, st, Vnull) x2 tcbls_r)
  (v'33 v'35 : list vallist)
  (v'43 v'45 : val)
  (tcbls_sub_l v'52 tcbls_sub_r : TcbMod.map)
  (Htcbjoin_sub_whole : TcbMod.join tcbls_sub_l v'52 tcbls_l)
  (Htcblist_sub_left : TCBList_P v'32 v'33 v'37 tcbls_sub_l)
  (Htcblist_sub_right : TCBList_P v'45 v'35 v'37 tcbls_sub_r)
  (ptcb_addr : block)
  (x11 : val)
  (H31 : isptr x11)
  (i11 : int32)
  (H33 : Int.unsigned i11 <= 65535)
  (ptcb_stat : int32)
  (H44 : Int.unsigned ptcb_stat <= 255)
  (i8 : int32)
  (H46 : Int.unsigned i8 <= 255)
  (i7 : int32)
  (H47 : Int.unsigned i7 <= 255)
  (i6 : int32)
  (H48 : Int.unsigned i6 <= 255)
  (i2 : int32)
  (H49 : Int.unsigned i2 <= 255)
  (H30 : isptr v'43)
  (H17 : isptr v'45)
  (H24 : isptr (Vptr (ptcb_addr, Int.zero)))
  (H7 : R_ECB_ETbl_P (pevent_addr, Int.zero)
         (V$ OS_EVENT_TYPE_MUTEX
          :: Vint32 i0
             :: Vint32 x
                :: Vptr (ptcb_addr, Int.zero)
                   :: x3 :: v'46 :: nil, v'44) tcbls)
  (H3 : ECBList_P v'42 Vnull
         (v'26 ++
          ((V$ OS_EVENT_TYPE_MUTEX
            :: Vint32 i0
               :: Vint32 x
                  :: Vptr (ptcb_addr, Int.zero)
                     :: x3 :: v'46 :: nil, v'44) :: nil) ++ v'27)
         (v'28 ++
          (DMutex (Vint32 x) (Vptr (ptcb_addr, Int.zero)) :: nil) ++
          v'29) v'39 tcbls)
  (H8 : EcbMod.joinsig (pevent_addr, Int.zero)
         (absmutexsem (x >>ᵢ $ 8)
            (Some
               (ptcb_addr, Int.zero, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)),
         wls) v'48 v'49)
  (Hget : EcbMod.get v'39 (pevent_addr, Int.zero) =
         Some
           (absmutexsem (x >>ᵢ $ 8)
              (Some
                 (ptcb_addr, Int.zero,
                 x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), wls))
  (H26 : RH_ECB_P
          (absmutexsem (x >>ᵢ $ 8)
             (Some
                (ptcb_addr, Int.zero,
                x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), wls))
  (H6 : RLH_ECBData_P
         (DMutex (Vint32 x) (Vptr (ptcb_addr, Int.zero)))
         (absmutexsem (x >>ᵢ $ 8)
            (Some
               (ptcb_addr, Int.zero, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)),
         wls))
  (H_ptcb : TcbMod.get tcbls (ptcb_addr, Int.zero) =
           Some (ptcb_prio, xs, xm))
  (H_ptcb_not_cur : (ptcb_addr, Int.zero) <> (cur_addr, Int.zero))
  (H_ptcb_in_left : TcbMod.get tcbls_l (ptcb_addr, Int.zero) =
                   Some (ptcb_prio, xs, xm))
  (Htcbjoin_sub_right : TcbMod.joinsig (ptcb_addr, Int.zero)
                         (ptcb_prio, xs, xm) tcbls_sub_r v'52)
  (Hget_last_tcb : get_last_tcb_ptr v'33 v'32 =
                  Some (Vptr (ptcb_addr, Int.zero)))
  (H32 : isptr xm)
  (H45 : Int.unsigned ptcb_prio <= 255)
  (Hptcb_node : TCBNode_P
                 (v'45
                  :: v'43
                     :: x11
                        :: xm
                           :: Vint32 i11
                              :: Vint32 ptcb_stat
                                 :: Vint32 ptcb_prio
                                    :: Vint32 i8
                                       :: 
                                       Vint32 i7
                                       :: 
                                       Vint32 i6
                                       :: 
                                       Vint32 i2 :: nil) v'37
                 (ptcb_prio, xs, xm))
  (Htcblist_subl : TCBList_P v'32
                    (v'33 ++
                     (v'45
                      :: v'43
                         :: x11
                            :: xm
                               :: Vint32 i11
                                  :: Vint32 ptcb_stat
                                     :: Vint32 ptcb_prio
                                        :: 
                                        Vint32 i8
                                        :: 
                                        Vint32 i7
                                        :: 
                                        Vint32 i6
                                        :: 
                                        Vint32 i2 :: nil)
                     :: v'35) v'37 tcbls_l)
  (Hptcb_blk : RL_TCBblk_P
                (v'45
                 :: v'43
                    :: x11
                       :: xm
                          :: Vint32 i11
                             :: Vint32 ptcb_stat
                                :: Vint32 ptcb_prio
                                   :: Vint32 i8
                                      :: Vint32 i7
                                         :: 
                                         Vint32 i6
                                         :: 
                                         Vint32 i2 :: nil))
  (Hptcb_stat : R_TCB_Status_P
                 (v'45
                  :: v'43
                     :: x11
                        :: xm
                           :: Vint32 i11
                              :: Vint32 ptcb_stat
                                 :: Vint32 ptcb_prio
                                    :: Vint32 i8
                                       :: 
                                       Vint32 i7
                                       :: 
                                       Vint32 i6
                                       :: 
                                       Vint32 i2 :: nil) v'37
                 (ptcb_prio, xs, xm))
  (Hptcb_prio_not_idle : ptcb_prio <> $ OS_IDLE_PRIO)
  (Hptcb_prio_scope_obv : 0 <= Int.unsigned ptcb_prio)
  (Hptcb_prio_scope : Int.unsigned ptcb_prio < 64)
  (Hif_ptcb_is_not_rdy : ptcb_stat <> $ OS_STAT_RDY \/ i11 <> $ 0)
(* ================================= *) ,
   {|OS_spec, GetHPrio, OSLInv, I,
   fun v : option val =>
   ( <|| END v ||>  **
    p_local OSLInv (cur_addr, Int.zero) init_lg **
    ((EX v0 : val, LV timeout @ Int16u |-> v0) **
     (EX v0 : val, LV pevent @ OS_EVENT ∗ |-> v0) **
     (EX v0 : val, LV legal @ Int8u |-> v0) **
     (EX v0 : val, LV pip @ Int8u |-> v0) **
     (EX v0 : val, LV mprio @ Int8u |-> v0) **
     (EX v0 : val, LV os_code_defs.isrdy @ Int8u |-> v0) **
     (EX v0 : val, LV ptcb @ OS_TCB ∗ |-> v0) **
     (EX v0 : val, LV pevent2 @ OS_EVENT ∗ |-> v0) ** Aemp) **
    Aie true ** Ais nil ** Acs nil ** Aisr empisr) **
   A_dom_lenv
     ((timeout, Int16u)
      :: (pevent, OS_EVENT ∗)
         :: (legal, Int8u)
            :: (pip, Int8u)
               :: (mprio, Int8u)
                  :: (os_code_defs.isrdy, Int8u)
                     :: (ptcb, OS_TCB ∗)
                        :: (pevent2, OS_EVENT ∗) :: nil),
   Afalse|}|- (cur_addr, Int.zero)
   {{Astruct (ptcb_addr, Int.zero) OS_TCB_flag
       (v'45
        :: v'43
           :: x11
              :: xm
                 :: Vint32 i11
                    :: Vint32 ptcb_stat
                       :: Vint32 ptcb_prio
                          :: Vint32 i8
                             :: Vint32 i7
                                :: Vint32 i6 :: Vint32 i2 :: nil) **
     tcbdllseg v'32 Vnull v'43 (Vptr (ptcb_addr, Int.zero)) v'33 **
     tcbdllseg v'45 (Vptr (ptcb_addr, Int.zero)) v'25
       (Vptr (cur_addr, Int.zero)) v'35 **
      <||
     mutexpend (Vptr (pevent_addr, Int.zero) :: Vint32 i :: nil)
     ||>  **
     LV ptcb @ OS_TCB ∗ |-> Vptr (ptcb_addr, Int.zero) **
     LV mprio @ Int8u |-> Vint32 (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) **
     LV pip @ Int8u |-> Vint32 (x >>ᵢ $ 8) **
     Astruct (cur_addr, Int.zero) OS_TCB_flag
       (x0
        :: v'25
           :: x12
              :: Vnull
                 :: V$ 0
                    :: V$ OS_STAT_RDY
                       :: Vint32 cur_prio
                          :: Vint32 i5
                             :: Vint32 i4
                                :: Vint32 i3 :: Vint32 i1 :: nil) **
     dllseg x0 (Vptr (cur_addr, Int.zero)) v'41 Vnull v'36
       OS_TCB_flag (fun vl : vallist => nth_val 1 vl)
       (fun vl : vallist => nth_val 0 vl) **
     GV OSTCBList @ OS_TCB ∗ |-> v'32 **
     GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_addr, Int.zero) **
     AEventData
       (V$ OS_EVENT_TYPE_MUTEX
        :: Vint32 i0
           :: Vint32 x
              :: Vptr (ptcb_addr, Int.zero) :: x3 :: v'46 :: nil)
       (DMutex (Vint32 x) (Vptr (ptcb_addr, Int.zero))) **
     Astruct (pevent_addr, Int.zero) OS_EVENT
       (V$ OS_EVENT_TYPE_MUTEX
        :: Vint32 i0
           :: Vint32 x
              :: Vptr (ptcb_addr, Int.zero) :: x3 :: v'46 :: nil) **
     Aarray v'24 (Tarray Int8u ∘ OS_EVENT_TBL_SIZE) v'44 **
     Aie false **
     Ais nil **
     Acs (true :: nil) **
     Aisr empisr **
     GV OSEventList @ OS_EVENT ∗ |-> v'42 **
     evsllseg v'42 (Vptr (pevent_addr, Int.zero)) v'26 v'28 **
     evsllseg v'46 Vnull v'27 v'29 **
     A_isr_is_prop **
     tcbdllflag v'32
       ((v'33 ++
         (v'45
          :: v'43
             :: x11
                :: xm
                   :: Vint32 i11
                      :: Vint32 ptcb_stat
                         :: Vint32 ptcb_prio
                            :: Vint32 i8
                               :: Vint32 i7
                                  :: Vint32 i6
                                     :: Vint32 i2 :: nil)
         :: v'35) ++
        (x0
         :: v'25
            :: x12
               :: Vnull
                  :: V$ 0
                     :: V$ OS_STAT_RDY
                        :: Vint32 cur_prio
                           :: Vint32 i5
                              :: Vint32 i4
                                 :: Vint32 i3
                                    :: Vint32 i1 :: nil) :: v'36) **
     AOSRdyTblGrp v'37 v'38 **
     AOSTCBPrioTbl v'31 v'37 tcbls v'51 **
     HECBList v'39 **
     HTCBList tcbls **
     HCurTCB (cur_addr, Int.zero) **
     p_local OSLInv (cur_addr, Int.zero) init_lg **
     LV legal @ Int8u |-> (V$ 1) **
     AOSEventFreeList v'5 **
     AOSQFreeList v'6 **
     AOSQFreeBlk v'7 **
     AOSMapTbl **
     AOSUnMapTbl **
     AOSIntNesting **
     AOSTCBFreeList v'22 v'23 **
     AOSTime (Vint32 v'20) **
     HTime v'20 **
     AGVars **
     atoy_inv' **
     LV pevent2 @ OS_EVENT ∗ |-> v'4 **
     LV os_code_defs.isrdy @ Int8u |-> v'2 **
     LV timeout @ Int16u |-> Vint32 i **
     LV pevent @ OS_EVENT ∗ |-> Vptr (pevent_addr, Int.zero) **
     A_dom_lenv
       ((timeout, Int16u)
        :: (pevent, OS_EVENT ∗)
           :: (legal, Int8u)
              :: (pip, Int8u)
                 :: (mprio, Int8u)
                    :: (os_code_defs.isrdy, Int8u)
                       :: (ptcb, OS_TCB ∗)
                          :: (pevent2, OS_EVENT ∗) :: nil)}} 
   EXIT_CRITICAL;ₛ
   RETURN ′ OS_ERR_NEST {{Afalse}}
.
Proof.
  intros.
(************************* intro cur_stat = rdy *************************)
  hoare lift 24%nat pre.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  hoare_split_pure_all.

  
  transform_pre AOSRdyTblGrp_fold ltac:(sep cancel GAarray;
                                        sep cancel AOSRdyGrp).
  rename v'37 into os_rdy_tbl.
  destruct H9 as (Hrtbl_type & Hrtbl_len).
  destruct H15 as (Hgrp1 & Hgrp2).

  hoare lifts (2::3::4::5::6::7::8::9::10::11::12::13::14
                ::15::16::17::18::19::20::21::23::24::nil)%nat pre.
  
  assert (Htmp1: st = rdy).
  {
    clear -Hcurnode Hrtbl_type Hrtbl_len.
    eapply mutexpend_TCBNode_P_in_tcb_rdy; eauto.
  }
  subst st.
(***************************** imply rdy end *****************************)
  assert (Htmp: Int.eq ptcb_stat ($ OS_STAT_RDY) = false \/
                Int.eq i11 ($ 0) = false).
  {
    clear -Hif_ptcb_is_not_rdy.
    destruct Hif_ptcb_is_not_rdy.
    left. rewrite Int.eq_false; auto.
    right; rewrite Int.eq_false; auto.
  }
    
  assert (xs <> rdy).
  {
    clear -Hptcb_stat Htmp.
    (* ** ac: Locate r_tcb_status_p_nrdy. *)
    Require Import Mbox_common.
    eapply r_tcb_status_p_nrdy.
    eauto.
    eauto.
  }
  
(****************************** ex critical ******************************)
  hoare abscsq.
  auto.
  eapply absinfer_mutex_pend_ptcb_is_not_rdy; eauto.
  can_change_aop_solver.
  
  hoare forward prim.

  {
    (** * AECBList *)
    unfold AECBList.
    sep pauto.
    
    eapply lzh_evsllseg_compose.
    sep cancel evsllseg.
    sep cancel evsllseg.
    unfold AEventNode.
    sep pauto.
    sep cancel AEventData.
    unfold AOSEvent.
    sep pauto.
    unfold AOSEventTbl.
    unfold node.
    sep pauto.
    sep cancel 11%nat 1%nat.
    sep cancel Aarray.

    (** * AOSTCBList *)
    unfold AOSTCBList.
    unfold tcbdllseg.
    sep pauto.
    (**** cancel right first *)
    sep lift 2%nat.
    unfold dllseg.
    fold dllseg.
    sep pauto.
    sep cancel 8%nat 2%nat.
    unfold node.
    sep pauto.
    sep cancel 7%nat 1%nat.
    (**** cancel left *)
    eapply tcbdllseg_compose with
      (l1:=v'33)
      (l2:=((v'45
              :: v'43
                 :: x11
                    :: xm
                       :: Vint32 i11
                          :: Vint32 ptcb_stat
                             :: Vint32 ptcb_prio
                                :: Vint32 i8
                                   :: Vint32 i7
                                      :: Vint32 i6 :: Vint32 i2 :: nil)::v'35)).
    sep cancel tcbdllseg.
    unfold tcbdllseg.
    unfold dllseg.
    fold dllseg.
    sep pauto.
    unfold node.
    sep pauto.
    sep cancel Astruct.
    sep cancel 1%nat 1%nat.
    sep cancel 4%nat 1%nat.
    exact_s.
    
    split; [auto | struct_type_match_solver].
    pure_auto.
    (* unfolds; auto. *)
    split; [auto | struct_type_match_solver].
    unfolds; auto.
    unfolds; auto.

    (**** cancel tcblist_p right *)
    unfold TCBList_P.
    fold TCBList_P.
    do 4 eexists.
    splits; eauto.
    unfolds; auto.
    (**** cancel tcblist_p left *)
    eapply TCBList_P_Combine with 
      (l1:=v'33)
      (l2:=(v'45
             :: v'43
                :: x11
                   :: xm
                      :: Vint32 i11
                      :: Vint32 ptcb_stat
                      :: Vint32 ptcb_prio
                      :: Vint32 i8
                      :: Vint32 i7
                      :: Vint32 i6 :: Vint32 i2 :: nil)::v'35).
    eauto.
    apply Htcbjoin_sub_whole.
    auto.
    unfold TCBList_P.
    fold TCBList_P.
    do 4 eexists.
    splits; eauto.
    unfolds; auto.

    eauto.
    eauto.
    split; [auto | struct_type_match_solver].
    eauto.
    unfolds; auto.
    eauto.
    unfolds; auto.
    eauto.
    eauto.
    eauto.
  }
  pauto.
  hoare forward.
Qed.

Lemma mutex_pend_cur_prio_eql_mprio_left_to_cur: forall
  (i : int32)
  (H1 : Int.unsigned i <= 65535)
  (v' v'0 v'1 v'2 v'3 v'4 : val)
  (v'5 v'6 v'7 : list vallist)
  (v'8 : list EventData)
  (v'9 : list os_inv.EventCtr)
  (v'10 : vallist)
  (v'11 v'12 : val)
  (v'13 : list vallist)
  (v'14 : vallist)
  (v'15 : list vallist)
  (v'16 : vallist)
  (v'17 : val)
  (v'18 : EcbMod.map)
  (v'19 : TcbMod.map)
  (v'20 : int32)
  (v'21 : addrval)
  (v'22 : val)
  (v'23 : list vallist)
  (v'26 v'27 : list os_inv.EventCtr)
  (v'28 v'29 : list EventData)
  (v'31 : vallist)
  (v'32 : val)
  (v'36 : list vallist)
  (os_rdy_tbl : vallist)
  (v'38 : val)
  (v'39 : EcbMod.map)
  (tcbls : TcbMod.map)
  (v'42 : val)
  (v'44 : vallist)
  (v'46 : val)
  (v'47 v'48 v'49 : EcbMod.map)
  (v'51 : addrval)
  (H5 : ECBList_P v'46 Vnull v'27 v'29 v'48 tcbls)
  (H11 : EcbMod.join v'47 v'49 v'39)
  (H14 : length v'26 = length v'28)
  (v'24 : addrval)
  (pevent_addr : block)
  (H13 : array_type_vallist_match Int8u v'44)
  (H19 : length v'44 = ∘ OS_EVENT_TBL_SIZE)
  (H20 : isptr v'46)
  (x3 : val)
  (i0 : int32)
  (H22 : Int.unsigned i0 <= 255)
  (H18 : RL_Tbl_Grp_P v'44 (Vint32 i0))
  (H25 : isptr v'46)
  (H4 : ECBList_P v'42 (Vptr (pevent_addr, Int.zero)) v'26 v'28
         v'47 tcbls)
  (H2 : isptr (Vptr (pevent_addr, Int.zero)))
  (H16 : id_addrval' (Vptr (pevent_addr, Int.zero)) OSEventTbl
          OS_EVENT = Some v'24)
  (H21 : Int.unsigned ($ OS_EVENT_TYPE_MUTEX) <= 255)
  (wls : waitset)
  (v'25 v'41 : val)
  (tcbls_l tcbls_r : TcbMod.map)
  (cur_addr : block)
  (H29 : v'32 <> Vnull)
  (Htcbjoin_whole : join tcbls_l tcbls_r tcbls)
  (H28 : Vptr (cur_addr, Int.zero) <> Vnull)
  (x12 : val)
  (H35 : isptr x12)
  (cur_prio : int32)
  (H39 : Int.unsigned cur_prio <= 255)
  (i5 : int32)
  (H40 : Int.unsigned i5 <= 255)
  (i4 : int32)
  (H41 : Int.unsigned i4 <= 255)
  (i3 : int32)
  (H42 : Int.unsigned i3 <= 255)
  (i1 : int32)
  (H43 : Int.unsigned i1 <= 255)
  (H34 : isptr v'25)
  (H0 : RH_CurTCB (cur_addr, Int.zero) v'19)
  (H : RH_TCBList_ECBList_P v'39 tcbls (cur_addr, Int.zero))
  (H10 : RH_CurTCB (cur_addr, Int.zero) tcbls)
  (Hneq_idle : cur_prio <> $ OS_IDLE_PRIO)
  (H37 : Int.unsigned ($ 0) <= 65535)
  (H38 : Int.unsigned ($ OS_STAT_RDY) <= 255)
  (H36 : isptr Vnull)
  (x0 : val)
  (x2 : TcbMod.map)
  (Htcblist_subr : TCBList_P x0 v'36 os_rdy_tbl x2)
  (x : int32)
  (F2 H23 : Int.unsigned x <= 65535)
  (Fneq_i2_1 : Int.unsigned (x >>ᵢ $ 8) <= 255)
  (Fneq_i2_2 : Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) <= 255)
  (Hmutex_not_avail : x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 <>
                     $ OS_MUTEX_AVAILABLE)
  (Feq_i2_1 : x >>ᵢ $ 8 = Int.modu (x >>ᵢ $ 8) ($ Byte.modulus))
  (Hcur_prio : Int.ltu (x >>ᵢ $ 8) cur_prio = true)
  (ptcb_prio : priority)
  (xm : msg)
  (H12 : isptr x0)
  (v'33 v'35 : list vallist)
  (v'43 v'45 : val)
  (tcbls_sub_l v'52 tcbls_sub_r : TcbMod.map)
  (Htcbjoin_sub_whole : TcbMod.join tcbls_sub_l v'52 tcbls_l)
  (Htcblist_sub_left : TCBList_P v'32 v'33 os_rdy_tbl tcbls_sub_l)
  (Htcblist_sub_right : TCBList_P v'45 v'35 os_rdy_tbl
                         tcbls_sub_r)
  (ptcb_addr : block)
  (x11 : val)
  (H31 : isptr x11)
  (i11 : int32)
  (H33 : Int.unsigned i11 <= 65535)
  (ptcb_stat : int32)
  (H44 : Int.unsigned ptcb_stat <= 255)
  (i8 : int32)
  (H46 : Int.unsigned i8 <= 255)
  (ptcb_tcby : int32)
  (H47 : Int.unsigned ptcb_tcby <= 255)
  (ptcb_bitx : int32)
  (H48 : Int.unsigned ptcb_bitx <= 255)
  (i2 : int32)
  (H49 : Int.unsigned i2 <= 255)
  (H30 : isptr v'43)
  (H17 : isptr v'45)
  (H24 : isptr (Vptr (ptcb_addr, Int.zero)))
  (H7 : R_ECB_ETbl_P (pevent_addr, Int.zero)
         (V$ OS_EVENT_TYPE_MUTEX
          :: Vint32 i0
             :: Vint32 x
                :: Vptr (ptcb_addr, Int.zero)
                   :: x3 :: v'46 :: nil, v'44) tcbls)
  (H3 : ECBList_P v'42 Vnull
         (v'26 ++
          ((V$ OS_EVENT_TYPE_MUTEX
            :: Vint32 i0
               :: Vint32 x
                  :: Vptr (ptcb_addr, Int.zero)
                     :: x3 :: v'46 :: nil, v'44) :: nil) ++ v'27)
         (v'28 ++
          (DMutex (Vint32 x) (Vptr (ptcb_addr, Int.zero)) :: nil) ++
          v'29) v'39 tcbls)
  (H8 : EcbMod.joinsig (pevent_addr, Int.zero)
         (absmutexsem (x >>ᵢ $ 8)
            (Some
               (ptcb_addr, Int.zero, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)),
         wls) v'48 v'49)
  (Hget : EcbMod.get v'39 (pevent_addr, Int.zero) =
         Some
           (absmutexsem (x >>ᵢ $ 8)
              (Some
                 (ptcb_addr, Int.zero,
                 x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), wls))
  (H26 : RH_ECB_P
          (absmutexsem (x >>ᵢ $ 8)
             (Some
                (ptcb_addr, Int.zero,
                x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), wls))
  (H6 : RLH_ECBData_P
         (DMutex (Vint32 x) (Vptr (ptcb_addr, Int.zero)))
         (absmutexsem (x >>ᵢ $ 8)
            (Some
               (ptcb_addr, Int.zero, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)),
         wls))
  (H_ptcb_not_cur : (ptcb_addr, Int.zero) <> (cur_addr, Int.zero))
  (Hget_last_tcb : get_last_tcb_ptr v'33 v'32 =
                  Some (Vptr (ptcb_addr, Int.zero)))
  (H32 : isptr xm)
  (H45 : Int.unsigned ptcb_prio <= 255)
  (Htcblist_subl : TCBList_P v'32
                    (v'33 ++
                     (v'45
                      :: v'43
                         :: x11
                            :: xm
                               :: Vint32 i11
                                  :: Vint32 ptcb_stat
                                     :: Vint32 ptcb_prio
                                        :: 
                                        Vint32 i8
                                        :: 
                                        Vint32 ptcb_tcby
                                        :: 
                                        Vint32 ptcb_bitx
                                        :: 
                                        Vint32 i2 :: nil)
                     :: v'35) os_rdy_tbl tcbls_l)
  (Hptcb_blk : RL_TCBblk_P
                (v'45
                 :: v'43
                    :: x11
                       :: xm
                          :: Vint32 i11
                             :: Vint32 ptcb_stat
                                :: Vint32 ptcb_prio
                                   :: Vint32 i8
                                      :: Vint32 ptcb_tcby
                                         :: 
                                         Vint32 ptcb_bitx
                                         :: 
                                         Vint32 i2 :: nil))
  (Hptcb_prio_not_idle : ptcb_prio <> $ OS_IDLE_PRIO)
  (Hptcb_prio_scope_obv : 0 <= Int.unsigned ptcb_prio)
  (Hptcb_prio_scope : Int.unsigned ptcb_prio < 64)
  (Hif_ptcb_is_rdy1 : ptcb_stat = $ OS_STAT_RDY)
  (Hif_ptcb_is_rdy2 : i11 = $ 0)
  (Hrtbl_type : array_type_vallist_match Int8u os_rdy_tbl)
  (Hrtbl_len : length os_rdy_tbl = ∘ OS_RDY_TBL_SIZE)
  (Hgrp1 : RL_Tbl_Grp_P os_rdy_tbl v'38)
  (Hgrp2 : prio_in_tbl ($ OS_IDLE_PRIO) os_rdy_tbl)
  (H_ptcb : TcbMod.get tcbls (ptcb_addr, Int.zero) =
           Some (ptcb_prio, rdy, xm))
  (H_ptcb_in_left : TcbMod.get tcbls_l (ptcb_addr, Int.zero) =
                   Some (ptcb_prio, rdy, xm))
  (Htcbjoin_sub_right : TcbMod.joinsig (ptcb_addr, Int.zero)
                         (ptcb_prio, rdy, xm) tcbls_sub_r v'52)
  (Hptcb_node : TCBNode_P
                 (v'45
                  :: v'43
                     :: x11
                        :: xm
                           :: Vint32 i11
                              :: Vint32 ptcb_stat
                                 :: Vint32 ptcb_prio
                                    :: Vint32 i8
                                       :: 
                                       Vint32 ptcb_tcby
                                       :: 
                                       Vint32 ptcb_bitx
                                       :: 
                                       Vint32 i2 :: nil)
                 os_rdy_tbl (ptcb_prio, rdy, xm))
  (Hptcb_stat : R_TCB_Status_P
                 (v'45
                  :: v'43
                     :: x11
                        :: xm
                           :: Vint32 i11
                              :: Vint32 ptcb_stat
                                 :: Vint32 ptcb_prio
                                    :: Vint32 i8
                                       :: 
                                       Vint32 ptcb_tcby
                                       :: 
                                       Vint32 ptcb_bitx
                                       :: 
                                       Vint32 i2 :: nil)
                 os_rdy_tbl (ptcb_prio, rdy, xm))
  (Hgetcur_subr : TcbMod.get tcbls_r (cur_addr, Int.zero) =
                 Some (cur_prio, rdy, Vnull))
  (Hgetcur : TcbMod.get tcbls (cur_addr, Int.zero) =
            Some (cur_prio, rdy, Vnull))
  (Hcurnode : TCBNode_P
               (x0
                :: v'25
                   :: x12
                      :: Vnull
                         :: V$ 0
                            :: V$ OS_STAT_RDY
                               :: Vint32 cur_prio
                                  :: Vint32 i5
                                     :: Vint32 i4
                                        :: 
                                        Vint32 i3
                                        :: 
                                        Vint32 i1 :: nil)
               os_rdy_tbl (cur_prio, rdy, Vnull))
  (Htcbjoin_right : TcbJoin (cur_addr, Int.zero)
                     (cur_prio, rdy, Vnull) x2 tcbls_r)
  (Hcur_prio_eql_mprio : Int.eq (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)
                          cur_prio = true)
(* ================================= *) ,
   {|OS_spec, GetHPrio, OSLInv, I,
   fun v : option val =>
   ( <|| END v ||>  **
    p_local OSLInv (cur_addr, Int.zero) init_lg **
    ((EX v0 : val, LV timeout @ Int16u |-> v0) **
     (EX v0 : val, LV pevent @ OS_EVENT ∗ |-> v0) **
     (EX v0 : val, LV legal @ Int8u |-> v0) **
     (EX v0 : val, LV pip @ Int8u |-> v0) **
     (EX v0 : val, LV mprio @ Int8u |-> v0) **
     (EX v0 : val, LV os_code_defs.isrdy @ Int8u |-> v0) **
     (EX v0 : val, LV ptcb @ OS_TCB ∗ |-> v0) **
     (EX v0 : val, LV pevent2 @ OS_EVENT ∗ |-> v0) ** Aemp) **
    Aie true ** Ais nil ** Acs nil ** Aisr empisr) **
   A_dom_lenv
     ((timeout, Int16u)
      :: (pevent, OS_EVENT ∗)
         :: (legal, Int8u)
            :: (pip, Int8u)
               :: (mprio, Int8u)
                  :: (os_code_defs.isrdy, Int8u)
                     :: (ptcb, OS_TCB ∗)
                        :: (pevent2, OS_EVENT ∗) :: nil),
   Afalse|}|- (cur_addr, Int.zero)
   {{Astruct (ptcb_addr, Int.zero) OS_TCB_flag
       (v'45
        :: v'43
           :: x11
              :: xm
                 :: Vint32 i11
                    :: Vint32 ptcb_stat
                       :: Vint32 ptcb_prio
                          :: Vint32 i8
                             :: Vint32 ptcb_tcby
                                :: Vint32 ptcb_bitx
                                   :: Vint32 i2 :: nil) **
     tcbdllseg v'32 Vnull v'43 (Vptr (ptcb_addr, Int.zero)) v'33 **
     tcbdllseg v'45 (Vptr (ptcb_addr, Int.zero)) v'25
       (Vptr (cur_addr, Int.zero)) v'35 **
      <||
     mutexpend (Vptr (pevent_addr, Int.zero) :: Vint32 i :: nil)
     ||>  **
     LV ptcb @ OS_TCB ∗ |-> Vptr (ptcb_addr, Int.zero) **
     LV mprio @ Int8u |-> Vint32 (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) **
     LV pip @ Int8u |-> Vint32 (x >>ᵢ $ 8) **
     Astruct (cur_addr, Int.zero) OS_TCB_flag
       (x0
        :: v'25
           :: x12
              :: Vnull
                 :: V$ 0
                    :: V$ OS_STAT_RDY
                       :: Vint32 cur_prio
                          :: Vint32 i5
                             :: Vint32 i4
                                :: Vint32 i3 :: Vint32 i1 :: nil) **
     dllseg x0 (Vptr (cur_addr, Int.zero)) v'41 Vnull v'36
       OS_TCB_flag (fun vl : vallist => nth_val 1 vl)
       (fun vl : vallist => nth_val 0 vl) **
     GV OSTCBList @ OS_TCB ∗ |-> v'32 **
     GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_addr, Int.zero) **
     AEventData
       (V$ OS_EVENT_TYPE_MUTEX
        :: Vint32 i0
           :: Vint32 x
              :: Vptr (ptcb_addr, Int.zero) :: x3 :: v'46 :: nil)
       (DMutex (Vint32 x) (Vptr (ptcb_addr, Int.zero))) **
     Astruct (pevent_addr, Int.zero) OS_EVENT
       (V$ OS_EVENT_TYPE_MUTEX
        :: Vint32 i0
           :: Vint32 x
              :: Vptr (ptcb_addr, Int.zero) :: x3 :: v'46 :: nil) **
     Aarray v'24 (Tarray Int8u ∘ OS_EVENT_TBL_SIZE) v'44 **
     Aie false **
     Ais nil **
     Acs (true :: nil) **
     Aisr empisr **
     GV OSEventList @ OS_EVENT ∗ |-> v'42 **
     evsllseg v'42 (Vptr (pevent_addr, Int.zero)) v'26 v'28 **
     evsllseg v'46 Vnull v'27 v'29 **
     A_isr_is_prop **
     tcbdllflag v'32
       ((v'33 ++
         (v'45
          :: v'43
             :: x11
                :: xm
                   :: Vint32 i11
                      :: Vint32 ptcb_stat
                         :: Vint32 ptcb_prio
                            :: Vint32 i8
                               :: Vint32 ptcb_tcby
                                  :: Vint32 ptcb_bitx
                                     :: Vint32 i2 :: nil)
         :: v'35) ++
        (x0
         :: v'25
            :: x12
               :: Vnull
                  :: V$ 0
                     :: V$ OS_STAT_RDY
                        :: Vint32 cur_prio
                           :: Vint32 i5
                              :: Vint32 i4
                                 :: Vint32 i3
                                    :: Vint32 i1 :: nil) :: v'36) **
     AOSRdyTblGrp os_rdy_tbl v'38 **
     AOSTCBPrioTbl v'31 os_rdy_tbl tcbls v'51 **
     HECBList v'39 **
     HTCBList tcbls **
     HCurTCB (cur_addr, Int.zero) **
     p_local OSLInv (cur_addr, Int.zero) init_lg **
     LV legal @ Int8u |-> (V$ 1) **
     AOSEventFreeList v'5 **
     AOSQFreeList v'6 **
     AOSQFreeBlk v'7 **
     AOSMapTbl **
     AOSUnMapTbl **
     AOSIntNesting **
     AOSTCBFreeList v'22 v'23 **
     AOSTime (Vint32 v'20) **
     HTime v'20 **
     AGVars **
     atoy_inv' **
     LV pevent2 @ OS_EVENT ∗ |-> v'4 **
     LV os_code_defs.isrdy @ Int8u |-> v'2 **
     LV timeout @ Int16u |-> Vint32 i **
     LV pevent @ OS_EVENT ∗ |-> Vptr (pevent_addr, Int.zero) **
     A_dom_lenv
       ((timeout, Int16u)
        :: (pevent, OS_EVENT ∗)
           :: (legal, Int8u)
              :: (pip, Int8u)
                 :: (mprio, Int8u)
                    :: (os_code_defs.isrdy, Int8u)
                       :: (ptcb, OS_TCB ∗)
                          :: (pevent2, OS_EVENT ∗) :: nil)}} 
   EXIT_CRITICAL;ₛ
   RETURN ′ OS_ERR_MUTEX_DEADLOCK {{Afalse}}
.  
Proof.
  intros.
  idtac.
  assert (Htmp: (x &ᵢ $ OS_MUTEX_KEEP_LOWER_8) = cur_prio).
  {
    clear -Hcur_prio_eql_mprio.
    lzh_simpl_int_eq.
    auto.
  }
  clear Hcur_prio_eql_mprio.
  rename Htmp into Hcur_prio_eql_mprio.

(****************************** ex critical ******************************)
  hoare abscsq.
  auto.
  eapply absinfer_mutex_pend_cur_prio_eql_mprio; eauto.
  can_change_aop_solver.
  
  hoare forward prim.

  {
    (** * AECBList *)
    unfold AECBList.
    sep pauto.
    
    eapply lzh_evsllseg_compose.
    sep cancel evsllseg.
    sep cancel evsllseg.
    unfold AEventNode.
    sep pauto.
    sep cancel AEventData.
    unfold AOSEvent.
    sep pauto.
    unfold AOSEventTbl.
    unfold node.
    sep pauto.
    sep cancel 11%nat 1%nat.
    sep cancel Aarray.

    (** * AOSTCBList *)
    unfold AOSTCBList.
    unfold tcbdllseg.
    sep pauto.
    (**** cancel right first *)
    sep lift 2%nat.
    unfold dllseg.
    fold dllseg.
    sep pauto.
    sep cancel 8%nat 2%nat.
    unfold node.
    sep pauto.
    sep cancel 7%nat 1%nat.
    (**** cancel left *)
    eapply tcbdllseg_compose with
      (l1:=v'33)
      (l2:=(v'45
             :: v'43
                :: x11
                   :: xm
                      :: V$0
                         :: V$OS_STAT_RDY
                            :: Vint32 ptcb_prio
                               :: Vint32 i8
                                  :: Vint32 ptcb_tcby
                                     :: Vint32 ptcb_bitx :: Vint32 i2 :: nil)::v'35).
    sep cancel tcbdllseg.
    unfold tcbdllseg.
    unfold dllseg.
    fold dllseg.
    sep pauto.
    unfold node.
    sep pauto.
    sep cancel Astruct.
    sep cancel 1%nat 1%nat.
    sep cancel 4%nat 1%nat.
    exact_s.
    
    split; [auto | struct_type_match_solver].
    pure_auto.
    (* unfolds; auto. *)
    split; [auto | struct_type_match_solver].
    unfolds; auto.
    unfolds; auto.

    (**** cancel tcblist_p right *)
    unfold TCBList_P.
    fold TCBList_P.
    do 4 eexists.
    splits; eauto.
    unfolds; auto.
    (**** cancel tcblist_p left *)
    eapply TCBList_P_Combine with 
      (l1:=v'33)
      (l2:=(v'45
             :: v'43
                :: x11
                   :: xm
                      :: V$0
                         :: V$OS_STAT_RDY
                            :: Vint32 ptcb_prio
                               :: Vint32 i8
                                  :: Vint32 ptcb_tcby
                                     :: Vint32 ptcb_bitx :: Vint32 i2 :: nil)::v'35).
    eauto.
    apply Htcbjoin_sub_whole.
    auto.
    unfold TCBList_P.
    fold TCBList_P.
    do 4 eexists.
    splits; eauto.
    unfolds; auto.

    eauto.
    eauto.
    split; [auto | struct_type_match_solver].
    eauto.
    unfolds; auto.
    eauto.
    unfolds; auto.
    eauto.
    eauto.
    eauto.
  }
  pauto.
  hoare forward.
Qed.

Open Scope nat_scope.
Lemma mutex_pend_pip_is_not_hold_left_to_cur: forall
  (i : int32)
  (H1 : (Int.unsigned i <= 65535)%Z)
  (v' v'0 v'1 v'2 v'3 v'4 : val)
  (v'5 v'6 v'7 : list vallist)
  (v'8 : list EventData)
  (v'9 : list os_inv.EventCtr)
  (v'10 : vallist)
  (v'11 v'12 : val)
  (v'13 : list vallist)
  (v'14 : vallist)
  (v'15 : list vallist)
  (v'16 : vallist)
  (v'17 : val)
  (v'18 : EcbMod.map)
  (v'19 : TcbMod.map)
  (v'20 : int32)
  (v'21 : addrval)
  (v'22 : val)
  (v'23 : list vallist)
  (v'26 v'27 : list os_inv.EventCtr)
  (v'28 v'29 : list EventData)
  (ptbl : vallist)
  (v'32 : val)
  (v'36 : list vallist)
  (os_rdy_tbl : vallist)
  (v'38 : val)
  (v'39 : EcbMod.map)
  (tcbls : TcbMod.map)
  (v'42 : val)
  (v'44 : vallist)
  (v'46 : val)
  (v'47 v'48 v'49 : EcbMod.map)
  (v'51 : addrval)
  (H5 : ECBList_P v'46 Vnull v'27 v'29 v'48 tcbls)
  (H11 : EcbMod.join v'47 v'49 v'39)
  (H14 : length v'26 = length v'28)
  (v'24 : addrval)
  (pevent_addr : block)
  (H13 : array_type_vallist_match Int8u v'44)
  (H19 : length v'44 = ∘ OS_EVENT_TBL_SIZE)
  (H20 : isptr v'46)
  (x3 : val)
  (i0 : int32)
  (H22 : (Int.unsigned i0 <= 255)%Z)
  (H18 : RL_Tbl_Grp_P v'44 (Vint32 i0))
  (H25 : isptr v'46)
  (H4 : ECBList_P v'42 (Vptr (pevent_addr, Int.zero)) v'26 v'28
         v'47 tcbls)
  (H2 : isptr (Vptr (pevent_addr, Int.zero)))
  (H16 : id_addrval' (Vptr (pevent_addr, Int.zero)) OSEventTbl
          OS_EVENT = Some v'24)
  (H21 : (Int.unsigned ($ OS_EVENT_TYPE_MUTEX) <= 255)%Z)
  (wls : waitset)
  (v'25 v'41 : val)
  (tcbls_l tcbls_r : TcbMod.map)
  (cur_addr : block)
  (H29 : v'32 <> Vnull)
  (Htcbjoin_whole : join tcbls_l tcbls_r tcbls)
  (H28 : Vptr (cur_addr, Int.zero) <> Vnull)
  (x12 : val)
  (H35 : isptr x12)
  (cur_prio : int32)
  (H39 : (Int.unsigned cur_prio <= 255)%Z)
  (i5 : int32)
  (H40 : (Int.unsigned i5 <= 255)%Z)
  (i4 : int32)
  (H41 : (Int.unsigned i4 <= 255)%Z)
  (i3 : int32)
  (H42 : (Int.unsigned i3 <= 255)%Z)
  (i1 : int32)
  (H43 : (Int.unsigned i1 <= 255)%Z)
  (H34 : isptr v'25)
  (H0 : RH_CurTCB (cur_addr, Int.zero) v'19)
  (H : RH_TCBList_ECBList_P v'39 tcbls (cur_addr, Int.zero))
  (H10 : RH_CurTCB (cur_addr, Int.zero) tcbls)
  (Hneq_idle : cur_prio <> $ OS_IDLE_PRIO)
  (H37 : (Int.unsigned ($ 0) <= 65535)%Z)
  (H38 : (Int.unsigned ($ OS_STAT_RDY) <= 255)%Z)
  (H36 : isptr Vnull)
  (x0 : val)
  (x2 : TcbMod.map)
  (Htcblist_subr : TCBList_P x0 v'36 os_rdy_tbl x2)
  (x : int32)
  (F2 H23 : (Int.unsigned x <= 65535)%Z)
  (Fneq_i2_1 : (Int.unsigned (x >>ᵢ $ 8) <= 255)%Z)
  (Fneq_i2_2 : (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) <= 255)%Z)
  (Hmutex_not_avail : x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 <>
                     $ OS_MUTEX_AVAILABLE)
  (Feq_i2_1 : x >>ᵢ $ 8 = Int.modu (x >>ᵢ $ 8) ($ Byte.modulus))
  (Hcur_prio : Int.ltu (x >>ᵢ $ 8) cur_prio = true)
  (ptcb_prio : priority)
  (xm : msg)
  (H12 : isptr x0)
  (v'33 v'35 : list vallist)
  (v'43 v'45 : val)
  (tcbls_sub_l v'52 tcbls_sub_r : TcbMod.map)
  (Htcbjoin_sub_whole : TcbMod.join tcbls_sub_l v'52 tcbls_l)
  (Htcblist_sub_left : TCBList_P v'32 v'33 os_rdy_tbl tcbls_sub_l)
  (Htcblist_sub_right : TCBList_P v'45 v'35 os_rdy_tbl
                         tcbls_sub_r)
  (ptcb_addr : block)
  (x11 : val)
  (H31 : isptr x11)
  (i11 : int32)
  (H33 : (Int.unsigned i11 <= 65535)%Z)
  (ptcb_stat : int32)
  (H44 : (Int.unsigned ptcb_stat <= 255)%Z)
  (i8 : int32)
  (H46 : (Int.unsigned i8 <= 255)%Z)
  (ptcb_tcby : int32)
  (H47 : (Int.unsigned ptcb_tcby <= 255)%Z)
  (ptcb_bitx : int32)
  (H48 : (Int.unsigned ptcb_bitx <= 255)%Z)
  (i2 : int32)
  (H49 : (Int.unsigned i2 <= 255)%Z)
  (H30 : isptr v'43)
  (H17 : isptr v'45)
  (H24 : isptr (Vptr (ptcb_addr, Int.zero)))
  (H7 : R_ECB_ETbl_P (pevent_addr, Int.zero)
         ((V$ OS_EVENT_TYPE_MUTEX
           :: Vint32 i0
              :: Vint32 x
                 :: Vptr (ptcb_addr, Int.zero)
                    :: x3 :: v'46 :: nil)%list, v'44) tcbls)
  (H3 : ECBList_P v'42 Vnull
         (v'26 ++
          (((V$ OS_EVENT_TYPE_MUTEX
             :: Vint32 i0
                :: Vint32 x
                   :: Vptr (ptcb_addr, Int.zero)
                      :: x3 :: v'46 :: nil)%list, v'44) :: nil) ++
          v'27)
         (v'28 ++
          (DMutex (Vint32 x) (Vptr (ptcb_addr, Int.zero)) :: nil) ++
          v'29) v'39 tcbls)
  (H8 : EcbMod.joinsig (pevent_addr, Int.zero)
         (absmutexsem (x >>ᵢ $ 8)
            (Some
               (ptcb_addr, Int.zero, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)),
         wls) v'48 v'49)
  (Hget : EcbMod.get v'39 (pevent_addr, Int.zero) =
         Some
           (absmutexsem (x >>ᵢ $ 8)
              (Some
                 (ptcb_addr, Int.zero,
                 x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), wls))
  (H26 : RH_ECB_P
          (absmutexsem (x >>ᵢ $ 8)
             (Some
                (ptcb_addr, Int.zero,
                x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), wls))
  (H6 : RLH_ECBData_P
         (DMutex (Vint32 x) (Vptr (ptcb_addr, Int.zero)))
         (absmutexsem (x >>ᵢ $ 8)
            (Some
               (ptcb_addr, Int.zero, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)),
         wls))
  (H_ptcb_not_cur : (ptcb_addr, Int.zero) <> (cur_addr, Int.zero))
  (Hget_last_tcb : get_last_tcb_ptr v'33 v'32 =
                  Some (Vptr (ptcb_addr, Int.zero)))
  (H32 : isptr xm)
  (H45 : (Int.unsigned ptcb_prio <= 255)%Z)
  (Htcblist_subl : TCBList_P v'32
                    (v'33 ++
                     (v'45
                      :: v'43
                         :: x11
                            :: xm
                               :: Vint32 i11
                                  :: Vint32 ptcb_stat
                                     :: Vint32 ptcb_prio
                                        :: 
                                        Vint32 i8
                                        :: 
                                        Vint32 ptcb_tcby
                                        :: 
                                        Vint32 ptcb_bitx
                                        :: 
                                        Vint32 i2 :: nil)%list
                     :: v'35) os_rdy_tbl tcbls_l)
  (Hptcb_blk : RL_TCBblk_P
                (v'45
                 :: v'43
                    :: x11
                       :: xm
                          :: Vint32 i11
                             :: Vint32 ptcb_stat
                                :: Vint32 ptcb_prio
                                   :: Vint32 i8
                                      :: Vint32 ptcb_tcby
                                         :: 
                                         Vint32 ptcb_bitx
                                         :: 
                                         Vint32 i2 :: nil)%list)
  (Hptcb_prio_not_idle : ptcb_prio <> $ OS_IDLE_PRIO)
  (Hptcb_prio_scope_obv : (0 <= Int.unsigned ptcb_prio)%Z)
  (Hptcb_prio_scope : (Int.unsigned ptcb_prio < 64)%Z)
  (Hif_ptcb_is_rdy1 : ptcb_stat = $ OS_STAT_RDY)
  (Hif_ptcb_is_rdy2 : i11 = $ 0)
  (Hrtbl_type : array_type_vallist_match Int8u os_rdy_tbl)
  (Hrtbl_len : length os_rdy_tbl = ∘ OS_RDY_TBL_SIZE)
  (Hgrp1 : RL_Tbl_Grp_P os_rdy_tbl v'38)
  (Hgrp2 : prio_in_tbl ($ OS_IDLE_PRIO) os_rdy_tbl)
  (H_ptcb : TcbMod.get tcbls (ptcb_addr, Int.zero) =
           Some (ptcb_prio, rdy, xm))
  (H_ptcb_in_left : TcbMod.get tcbls_l (ptcb_addr, Int.zero) =
                   Some (ptcb_prio, rdy, xm))
  (Htcbjoin_sub_right : TcbMod.joinsig (ptcb_addr, Int.zero)
                         (ptcb_prio, rdy, xm) tcbls_sub_r v'52)
  (Hptcb_node : TCBNode_P
                 (v'45
                  :: v'43
                     :: x11
                        :: xm
                           :: Vint32 i11
                              :: Vint32 ptcb_stat
                                 :: Vint32 ptcb_prio
                                    :: Vint32 i8
                                       :: 
                                       Vint32 ptcb_tcby
                                       :: 
                                       Vint32 ptcb_bitx
                                       :: 
                                       Vint32 i2 :: nil)%list
                 os_rdy_tbl (ptcb_prio, rdy, xm))
  (Hptcb_stat : R_TCB_Status_P
                 (v'45
                  :: v'43
                     :: x11
                        :: xm
                           :: Vint32 i11
                              :: Vint32 ptcb_stat
                                 :: Vint32 ptcb_prio
                                    :: Vint32 i8
                                       :: 
                                       Vint32 ptcb_tcby
                                       :: 
                                       Vint32 ptcb_bitx
                                       :: 
                                       Vint32 i2 :: nil)%list
                 os_rdy_tbl (ptcb_prio, rdy, xm))
  (Hgetcur_subr : TcbMod.get tcbls_r (cur_addr, Int.zero) =
                 Some (cur_prio, rdy, Vnull))
  (Hgetcur : TcbMod.get tcbls (cur_addr, Int.zero) =
            Some (cur_prio, rdy, Vnull))
  (Hcurnode : TCBNode_P
               (x0
                :: v'25
                   :: x12
                      :: Vnull
                         :: V$ 0
                            :: V$ OS_STAT_RDY
                               :: Vint32 cur_prio
                                  :: Vint32 i5
                                     :: Vint32 i4
                                        :: 
                                        Vint32 i3
                                        :: 
                                        Vint32 i1 :: nil)%list
               os_rdy_tbl (cur_prio, rdy, Vnull))
  (Htcbjoin_right : TcbJoin (cur_addr, Int.zero)
                     (cur_prio, rdy, Vnull) x2 tcbls_r)
  (Hif_false : Int.eq (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) cur_prio =
              false)
  (Hnocur : Int.eq cur_prio (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = false)
  (H_cur_prio_scope : (Int.unsigned cur_prio < 64)%Z)
  (Hx_scope1 : (Int.unsigned (x >>ᵢ $ 8) < 64)%Z)
  (Hif_can_lift1 : ptcb_prio <> x >>ᵢ $ 8)
  (Hif_can_lift2 : Int.ltu cur_prio (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) =
                  true)
  (v'30 : val)
  (Hptbl_1 : array_type_vallist_match OS_TCB ∗ ptbl)
  (Hptbl_2 : length ptbl = 64)
  (H15 : RL_RTbl_PrioTbl_P os_rdy_tbl ptbl v'51)
  (H27 : R_PrioTbl_P ptbl tcbls v'51)
  (Hif_true : val_inj
               (uop_eval
                  (val_inj
                     (bop_eval
                        (nth_val'
                           (Z.to_nat (Int.unsigned (x >>ᵢ $ 8)))
                           ptbl) (Vptr v'51) 
                        OS_TCB ∗ OS_TCB ∗ oeq)) oppsite) <>
             Vint32 Int.zero /\
             val_inj
               (uop_eval
                  (val_inj
                     (bop_eval
                        (nth_val'
                           (Z.to_nat (Int.unsigned (x >>ᵢ $ 8)))
                           ptbl) (Vptr v'51) 
                        OS_TCB ∗ OS_TCB ∗ oeq)) oppsite) <>
             Vnull /\
             val_inj
               (uop_eval
                  (val_inj
                     (bop_eval
                        (nth_val'
                           (Z.to_nat (Int.unsigned (x >>ᵢ $ 8)))
                           ptbl) (Vptr v'51) 
                        OS_TCB ∗ OS_TCB ∗ oeq)) oppsite) <>
             Vundef)
(* ================================= *) ,
   {|OS_spec, GetHPrio, OSLInv, I,
   fun v : option val =>
   ( <|| END v ||>  **
    p_local OSLInv (cur_addr, Int.zero) init_lg **
    ((EX v0 : val, LV timeout @ Int16u |-> v0) **
     (EX v0 : val, LV pevent @ OS_EVENT ∗ |-> v0) **
     (EX v0 : val, LV legal @ Int8u |-> v0) **
     (EX v0 : val, LV pip @ Int8u |-> v0) **
     (EX v0 : val, LV mprio @ Int8u |-> v0) **
     (EX v0 : val, LV os_code_defs.isrdy @ Int8u |-> v0) **
     (EX v0 : val, LV ptcb @ OS_TCB ∗ |-> v0) **
     (EX v0 : val, LV pevent2 @ OS_EVENT ∗ |-> v0) ** Aemp) **
    Aie true ** Ais nil ** Acs nil ** Aisr empisr) **
   A_dom_lenv
     ((timeout, Int16u)
      :: (pevent, OS_EVENT ∗)
         :: (legal, Int8u)
            :: (pip, Int8u)
               :: (mprio, Int8u)
                  :: (os_code_defs.isrdy, Int8u)
                     :: (ptcb, OS_TCB ∗)
                        :: (pevent2, OS_EVENT ∗) :: nil)%list,
   Afalse|}|- (cur_addr, Int.zero)
   {{PV v'51 @ Int8u |-> v'30 **
     Astruct (ptcb_addr, Int.zero) OS_TCB_flag
       (v'45
        :: (v'43
            :: x11
               :: xm
                  :: Vint32 i11
                     :: Vint32 ptcb_stat
                        :: Vint32 ptcb_prio
                           :: Vint32 i8
                              :: Vint32 ptcb_tcby
                                 :: Vint32 ptcb_bitx
                                    :: Vint32 i2 :: nil)%list) **
     tcbdllseg v'32 Vnull v'43 (Vptr (ptcb_addr, Int.zero)) v'33 **
     tcbdllseg v'45 (Vptr (ptcb_addr, Int.zero)) v'25
       (Vptr (cur_addr, Int.zero)) v'35 **
      <||
     mutexpend
       (Vptr (pevent_addr, Int.zero) :: Vint32 i :: nil)%list
     ||>  **
     LV ptcb @ OS_TCB ∗ |-> Vptr (ptcb_addr, Int.zero) **
     LV mprio @ Int8u |-> Vint32 (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) **
     LV pip @ Int8u |-> Vint32 (x >>ᵢ $ 8) **
     Astruct (cur_addr, Int.zero) OS_TCB_flag
       (x0
        :: (v'25
            :: x12
               :: Vnull
                  :: V$ 0
                     :: V$ OS_STAT_RDY
                        :: Vint32 cur_prio
                           :: Vint32 i5
                              :: Vint32 i4
                                 :: Vint32 i3
                                    :: Vint32 i1 :: nil)%list) **
     dllseg x0 (Vptr (cur_addr, Int.zero)) v'41 Vnull v'36
       OS_TCB_flag (fun vl : vallist => nth_val 1 vl)
       (fun vl : vallist => nth_val 0 vl) **
     GV OSTCBList @ OS_TCB ∗ |-> v'32 **
     GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_addr, Int.zero) **
     AEventData
       (V$ OS_EVENT_TYPE_MUTEX
        :: Vint32 i0
           :: Vint32 x
              :: Vptr (ptcb_addr, Int.zero) :: x3 :: v'46 :: nil)%list
       (DMutex (Vint32 x) (Vptr (ptcb_addr, Int.zero))) **
     Astruct (pevent_addr, Int.zero) OS_EVENT
       (V$ OS_EVENT_TYPE_MUTEX
        :: (Vint32 i0
            :: Vint32 x
               :: Vptr (ptcb_addr, Int.zero)
                  :: x3 :: v'46 :: nil)%list) **
     Aarray v'24 (Tarray Int8u ∘ OS_EVENT_TBL_SIZE) v'44 **
     Aie false **
     Ais nil **
     Acs (true :: nil)%list **
     Aisr empisr **
     GV OSEventList @ OS_EVENT ∗ |-> v'42 **
     evsllseg v'42 (Vptr (pevent_addr, Int.zero)) v'26 v'28 **
     evsllseg v'46 Vnull v'27 v'29 **
     A_isr_is_prop **
     tcbdllflag v'32
       ((v'33 ++
         (v'45
          :: v'43
             :: x11
                :: xm
                   :: Vint32 i11
                      :: Vint32 ptcb_stat
                         :: Vint32 ptcb_prio
                            :: Vint32 i8
                               :: Vint32 ptcb_tcby
                                  :: Vint32 ptcb_bitx
                                     :: Vint32 i2 :: nil)%list
         :: v'35) ++
        (x0
         :: v'25
            :: x12
               :: Vnull
                  :: V$ 0
                     :: V$ OS_STAT_RDY
                        :: Vint32 cur_prio
                           :: Vint32 i5
                              :: Vint32 i4
                                 :: Vint32 i3
                                    :: Vint32 i1 :: nil)%list
        :: v'36) **
     AOSRdyTblGrp os_rdy_tbl v'38 **
     GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64) ptbl **
     G& OSPlaceHolder @ Int8u == v'51 **
     HECBList v'39 **
     HTCBList tcbls **
     HCurTCB (cur_addr, Int.zero) **
     p_local OSLInv (cur_addr, Int.zero) init_lg **
     LV legal @ Int8u |-> (V$ 1) **
     AOSEventFreeList v'5 **
     AOSQFreeList v'6 **
     AOSQFreeBlk v'7 **
     AOSMapTbl **
     AOSUnMapTbl **
     AOSIntNesting **
     AOSTCBFreeList v'22 v'23 **
     AOSTime (Vint32 v'20) **
     HTime v'20 **
     AGVars **
     atoy_inv' **
     LV pevent2 @ OS_EVENT ∗ |-> v'4 **
     LV os_code_defs.isrdy @ Int8u |-> v'2 **
     LV timeout @ Int16u |-> Vint32 i **
     LV pevent @ OS_EVENT ∗ |-> Vptr (pevent_addr, Int.zero) **
     A_dom_lenv
       ((timeout, Int16u)
        :: (pevent, OS_EVENT ∗)
           :: (legal, Int8u)
              :: (pip, Int8u)
                 :: (mprio, Int8u)
                    :: (os_code_defs.isrdy, Int8u)
                       :: (ptcb, OS_TCB ∗)
                          :: (pevent2, OS_EVENT ∗) :: nil)%list}} 
   EXIT_CRITICAL;ₛ
   RETURN ′ OS_ERR_MUTEXPR_NOT_HOLDER {{Afalse}}
.  
Proof.
  intros.

  idtac.
  
(****************************** ex critical ******************************)
  hoare abscsq.
  auto.
  eapply absinfer_mutex_pend_pip_is_not_hold; eauto.
  can_change_aop_solver.
  
  hoare forward prim.

  {
    (** * AECBList *)
    unfold AECBList.
    sep pauto.
    
    eapply lzh_evsllseg_compose.
    sep cancel evsllseg.
    sep cancel evsllseg.
    unfold AEventNode.
    sep pauto.
    sep cancel AEventData.
    unfold AOSEvent.
    sep pauto.
    unfold AOSEventTbl.
    unfold node.
    sep pauto.
    sep cancel 12%nat 1%nat.
    sep cancel Aarray.

    (** * AOSTCBList *)
    unfold AOSTCBList.
    unfold tcbdllseg.
    sep pauto.
    (**** cancel right first *)
    sep lift 2%nat.
    unfold dllseg.
    fold dllseg.
    sep pauto.
    sep cancel 9%nat 2%nat.
    unfold node.
    sep pauto.
    sep cancel 8%nat 1%nat.
    (**** cancel left *)
    eapply tcbdllseg_compose with
      (l1:=v'33)
      (l2:=(v'45
             :: v'43
                :: x11
                   :: xm
                      :: V$0
                         :: V$OS_STAT_RDY
                            :: Vint32 ptcb_prio
                               :: Vint32 i8
                                  :: Vint32 ptcb_tcby
                                     :: Vint32 ptcb_bitx :: Vint32 i2 :: nil)::v'35).
    sep cancel tcbdllseg.
    unfold tcbdllseg.
    unfold dllseg.
    fold dllseg.
    sep pauto.
    unfold node.
    sep pauto.
    sep cancel Astruct.
    sep cancel 2%nat 1%nat.

    
    unfold AOSTCBPrioTbl.
    sep pauto.
    sep cancel 1%nat 1%nat.
    sep cancel 5%nat 1%nat.
    sep cancel 4%nat 1%nat.
    exact_s.

    eauto.
    eauto.
        
    split; [auto | struct_type_match_solver].
    pure_auto.
    (* unfolds; auto. *)
    split; [auto | struct_type_match_solver].
    unfolds; auto.
    unfolds; auto.

    (**** cancel tcblist_p right *)
    unfold TCBList_P.
    fold TCBList_P.
    do 4 eexists.
    splits; eauto.
    unfolds; auto.
    (**** cancel tcblist_p left *)
    eapply TCBList_P_Combine with 
      (l1:=v'33)
      (l2:=(v'45
             :: v'43
                :: x11
                   :: xm
                      :: V$0
                         :: V$OS_STAT_RDY
                            :: Vint32 ptcb_prio
                               :: Vint32 i8
                                  :: Vint32 ptcb_tcby
                                     :: Vint32 ptcb_bitx :: Vint32 i2 :: nil)::v'35).
    eauto.
    apply Htcbjoin_sub_whole.
    auto.
    unfold TCBList_P.
    fold TCBList_P.
    do 4 eexists.
    splits; eauto.
    unfolds; auto.

    eauto.
    eauto.
    split; [auto | struct_type_match_solver].
    eauto.
    unfolds; auto.
    eauto.
    unfolds; auto.
    eauto.
    eauto.
    eauto.
  }
  pauto.
  hoare forward.
Qed.

Close Scope nat_scope.

Lemma mutex_pend_ptcb_is_idle_err_right_to_cur: forall
  (i : int32)
  (H1 : Int.unsigned i <= 65535)
  (v' v'0 v'1 v'2 v'3 v'4 : val)
  (v'5 v'6 v'7 : list vallist)
  (v'8 : list EventData)
  (v'9 : list os_inv.EventCtr)
  (v'10 : vallist)
  (v'11 v'12 : val)
  (v'13 : list vallist)
  (v'14 : vallist)
  (v'15 : list vallist)
  (v'16 : vallist)
  (v'17 : val)
  (v'18 : EcbMod.map)
  (v'19 : TcbMod.map)
  (v'20 : int32)
  (v'21 : addrval)
  (v'22 : val)
  (v'23 : list vallist)
  (v'26 v'27 : list os_inv.EventCtr)
  (v'28 v'29 : list EventData)
  (v'31 : vallist)
  (v'32 : val)
  (v'34 : list vallist)
  (v'37 : vallist)
  (v'38 : val)
  (v'39 : EcbMod.map)
  (tcbls : TcbMod.map)
  (v'42 : val)
  (v'44 : vallist)
  (v'46 : val)
  (v'47 v'48 v'49 : EcbMod.map)
  (v'51 : addrval)
  (H5 : ECBList_P v'46 Vnull v'27 v'29 v'48 tcbls)
  (H11 : EcbMod.join v'47 v'49 v'39)
  (H14 : length v'26 = length v'28)
  (v'24 : addrval)
  (pevent_addr : block)
  (H13 : array_type_vallist_match Int8u v'44)
  (H19 : length v'44 = ∘ OS_EVENT_TBL_SIZE)
  (H20 : isptr v'46)
  (x3 : val)
  (i0 : int32)
  (H22 : Int.unsigned i0 <= 255)
  (H18 : RL_Tbl_Grp_P v'44 (Vint32 i0))
  (H25 : isptr v'46)
  (H4 : ECBList_P v'42 (Vptr (pevent_addr, Int.zero)) v'26 v'28
         v'47 tcbls)
  (H2 : isptr (Vptr (pevent_addr, Int.zero)))
  (H16 : id_addrval' (Vptr (pevent_addr, Int.zero)) OSEventTbl
          OS_EVENT = Some v'24)
  (H21 : Int.unsigned ($ OS_EVENT_TYPE_MUTEX) <= 255)
  (wls : waitset)
  (v'25 v'41 : val)
  (tcbls_l tcbls_r : TcbMod.map)
  (cur_addr : block)
  (H29 : v'32 <> Vnull)
  (Htcbjoin_whole : join tcbls_l tcbls_r tcbls)
  (Htcblist_subl : TCBList_P v'32 v'34 v'37 tcbls_l)
  (H28 : Vptr (cur_addr, Int.zero) <> Vnull)
  (x12 : val)
  (H35 : isptr x12)
  (cur_prio : int32)
  (H39 : Int.unsigned cur_prio <= 255)
  (i5 : int32)
  (H40 : Int.unsigned i5 <= 255)
  (i4 : int32)
  (H41 : Int.unsigned i4 <= 255)
  (i3 : int32)
  (H42 : Int.unsigned i3 <= 255)
  (i1 : int32)
  (H43 : Int.unsigned i1 <= 255)
  (H34 : isptr v'25)
  (H0 : RH_CurTCB (cur_addr, Int.zero) v'19)
  (H : RH_TCBList_ECBList_P v'39 tcbls (cur_addr, Int.zero))
  (H10 : RH_CurTCB (cur_addr, Int.zero) tcbls)
  (st : taskstatus)
  (Hneq_idle : cur_prio <> $ OS_IDLE_PRIO)
  (H37 : Int.unsigned ($ 0) <= 65535)
  (H38 : Int.unsigned ($ OS_STAT_RDY) <= 255)
  (H36 : isptr Vnull)
  (Hgetcur_subr : TcbMod.get tcbls_r (cur_addr, Int.zero) =
                 Some (cur_prio, st, Vnull))
  (Hgetcur : TcbMod.get tcbls (cur_addr, Int.zero) =
            Some (cur_prio, st, Vnull))
  (x0 : val)
  (tcbls_r' : TcbMod.map)
  (x : int32)
  (F2 H23 : Int.unsigned x <= 65535)
  (Fneq_i2_1 : Int.unsigned (x >>ᵢ $ 8) <= 255)
  (Fneq_i2_2 : Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) <= 255)
  (Hmutex_not_avail : x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 <>
                     $ OS_MUTEX_AVAILABLE)
  (Feq_i2_1 : x >>ᵢ $ 8 = Int.modu (x >>ᵢ $ 8) ($ Byte.modulus))
  (Hcur_prio : Int.ltu (x >>ᵢ $ 8) cur_prio = true)
  (ptcb_prio : priority)
  (xm : msg)
  (xs : taskstatus)
  (H12 : isptr x0)
  (Hcurnode : TCBNode_P
               (x0
                :: v'25
                   :: x12
                      :: Vnull
                         :: V$ 0
                            :: V$ OS_STAT_RDY
                               :: Vint32 cur_prio
                                  :: Vint32 i5
                                     :: Vint32 i4
                                        :: 
                                        Vint32 i3
                                        :: 
                                        Vint32 i1 :: nil) v'37
               (cur_prio, st, Vnull))
  (Htcbjoin_right : TcbJoin (cur_addr, Int.zero)
                     (cur_prio, st, Vnull) tcbls_r' tcbls_r)
  (v'33 v'35 : list vallist)
  (v'43 v'45 : val)
  (tcbls_sub_l v'52 tcbls_sub_r : TcbMod.map)
  (Htcbjoin_sub_whole : TcbMod.join tcbls_sub_l v'52 tcbls_r')
  (Htcblist_sub_left : TCBList_P x0 v'33 v'37 tcbls_sub_l)
  (Htcblist_sub_right : TCBList_P v'45 v'35 v'37 tcbls_sub_r)
  (ptcb_addr : block)
  (x10 : val)
  (H31 : isptr x10)
  (i11 : int32)
  (H33 : Int.unsigned i11 <= 65535)
  (i10 : int32)
  (H44 : Int.unsigned i10 <= 255)
  (i8 : int32)
  (H46 : Int.unsigned i8 <= 255)
  (i7 : int32)
  (H47 : Int.unsigned i7 <= 255)
  (i6 : int32)
  (H48 : Int.unsigned i6 <= 255)
  (i2 : int32)
  (H49 : Int.unsigned i2 <= 255)
  (H30 : isptr v'43)
  (H17 : isptr v'45)
  (H24 : isptr (Vptr (ptcb_addr, Int.zero)))
  (H7 : R_ECB_ETbl_P (pevent_addr, Int.zero)
         (V$ OS_EVENT_TYPE_MUTEX
          :: Vint32 i0
             :: Vint32 x
                :: Vptr (ptcb_addr, Int.zero)
                   :: x3 :: v'46 :: nil, v'44) tcbls)
  (H3 : ECBList_P v'42 Vnull
         (v'26 ++
          ((V$ OS_EVENT_TYPE_MUTEX
            :: Vint32 i0
               :: Vint32 x
                  :: Vptr (ptcb_addr, Int.zero)
                     :: x3 :: v'46 :: nil, v'44) :: nil) ++ v'27)
         (v'28 ++
          (DMutex (Vint32 x) (Vptr (ptcb_addr, Int.zero)) :: nil) ++
          v'29) v'39 tcbls)
  (H8 : EcbMod.joinsig (pevent_addr, Int.zero)
         (absmutexsem (x >>ᵢ $ 8)
            (Some
               (ptcb_addr, Int.zero, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)),
         wls) v'48 v'49)
  (Hget : EcbMod.get v'39 (pevent_addr, Int.zero) =
         Some
           (absmutexsem (x >>ᵢ $ 8)
              (Some
                 (ptcb_addr, Int.zero,
                 x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), wls))
  (H26 : RH_ECB_P
          (absmutexsem (x >>ᵢ $ 8)
             (Some
                (ptcb_addr, Int.zero,
                x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), wls))
  (H6 : RLH_ECBData_P
         (DMutex (Vint32 x) (Vptr (ptcb_addr, Int.zero)))
         (absmutexsem (x >>ᵢ $ 8)
            (Some
               (ptcb_addr, Int.zero, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)),
         wls))
  (H_ptcb : TcbMod.get tcbls (ptcb_addr, Int.zero) =
           Some (ptcb_prio, xs, xm))
  (H_ptcb_not_cur : (ptcb_addr, Int.zero) <> (cur_addr, Int.zero))
  (H_ptcb_in_right : TcbMod.get tcbls_r' (ptcb_addr, Int.zero) =
                    Some (ptcb_prio, xs, xm))
  (Htcbjoin_sub_right : TcbMod.joinsig (ptcb_addr, Int.zero)
                         (ptcb_prio, xs, xm) tcbls_sub_r v'52)
  (Hget_last_tcb : get_last_tcb_ptr v'33 x0 =
                  Some (Vptr (ptcb_addr, Int.zero)))
  (H32 : isptr xm)
  (H45 : Int.unsigned ptcb_prio <= 255)
  (Hptcb_node : TCBNode_P
                 (v'45
                  :: v'43
                     :: x10
                        :: xm
                           :: Vint32 i11
                              :: Vint32 i10
                                 :: Vint32 ptcb_prio
                                    :: Vint32 i8
                                       :: 
                                       Vint32 i7
                                       :: 
                                       Vint32 i6
                                       :: 
                                       Vint32 i2 :: nil) v'37
                 (ptcb_prio, xs, xm))
  (Htcblist_subr : TCBList_P x0
                    (v'33 ++
                     (v'45
                      :: v'43
                         :: x10
                            :: xm
                               :: Vint32 i11
                                  :: Vint32 i10
                                     :: Vint32 ptcb_prio
                                        :: 
                                        Vint32 i8
                                        :: 
                                        Vint32 i7
                                        :: 
                                        Vint32 i6
                                        :: 
                                        Vint32 i2 :: nil)
                     :: v'35) v'37 tcbls_r')
  (Hptcb_blk : RL_TCBblk_P
                (v'45
                 :: v'43
                    :: x10
                       :: xm
                          :: Vint32 i11
                             :: Vint32 i10
                                :: Vint32 ptcb_prio
                                   :: Vint32 i8
                                      :: Vint32 i7
                                         :: 
                                         Vint32 i6
                                         :: 
                                         Vint32 i2 :: nil))
  (Hptcb_stat : R_TCB_Status_P
                 (v'45
                  :: v'43
                     :: x10
                        :: xm
                           :: Vint32 i11
                              :: Vint32 i10
                                 :: Vint32 ptcb_prio
                                    :: Vint32 i8
                                       :: 
                                       Vint32 i7
                                       :: 
                                       Vint32 i6
                                       :: 
                                       Vint32 i2 :: nil) v'37
                 (ptcb_prio, xs, xm))
  (LHift_true : Int.eq ptcb_prio ($ OS_IDLE_PRIO) = true)
(* ================================= *) ,
   {|OS_spec, GetHPrio, OSLInv, I,
   fun v : option val =>
   ( <|| END v ||>  **
    p_local OSLInv (cur_addr, Int.zero) init_lg **
    ((EX v0 : val, LV timeout @ Int16u |-> v0) **
     (EX v0 : val, LV pevent @ OS_EVENT ∗ |-> v0) **
     (EX v0 : val, LV legal @ Int8u |-> v0) **
     (EX v0 : val, LV pip @ Int8u |-> v0) **
     (EX v0 : val, LV mprio @ Int8u |-> v0) **
     (EX v0 : val, LV os_code_defs.isrdy @ Int8u |-> v0) **
     (EX v0 : val, LV ptcb @ OS_TCB ∗ |-> v0) **
     (EX v0 : val, LV pevent2 @ OS_EVENT ∗ |-> v0) ** Aemp) **
    Aie true ** Ais nil ** Acs nil ** Aisr empisr) **
   A_dom_lenv
     ((timeout, Int16u)
      :: (pevent, OS_EVENT ∗)
         :: (legal, Int8u)
            :: (pip, Int8u)
               :: (mprio, Int8u)
                  :: (os_code_defs.isrdy, Int8u)
                     :: (ptcb, OS_TCB ∗)
                        :: (pevent2, OS_EVENT ∗) :: nil),
   Afalse|}|- (cur_addr, Int.zero)
   {{Astruct (ptcb_addr, Int.zero) OS_TCB_flag
       (v'45
        :: v'43
           :: x10
              :: xm
                 :: Vint32 i11
                    :: Vint32 i10
                       :: Vint32 ptcb_prio
                          :: Vint32 i8
                             :: Vint32 i7
                                :: Vint32 i6 :: Vint32 i2 :: nil) **
     tcbdllseg x0 (Vptr (cur_addr, Int.zero)) v'43
       (Vptr (ptcb_addr, Int.zero)) v'33 **
     tcbdllseg v'45 (Vptr (ptcb_addr, Int.zero)) v'41 Vnull v'35 **
      <||
     mutexpend (Vptr (pevent_addr, Int.zero) :: Vint32 i :: nil)
     ||>  **
     LV ptcb @ OS_TCB ∗ |-> Vptr (ptcb_addr, Int.zero) **
     LV mprio @ Int8u |-> Vint32 (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) **
     LV pip @ Int8u |-> Vint32 (x >>ᵢ $ 8) **
     Astruct (cur_addr, Int.zero) OS_TCB_flag
       (x0
        :: v'25
           :: x12
              :: Vnull
                 :: V$ 0
                    :: V$ OS_STAT_RDY
                       :: Vint32 cur_prio
                          :: Vint32 i5
                             :: Vint32 i4
                                :: Vint32 i3 :: Vint32 i1 :: nil) **
     GV OSTCBList @ OS_TCB ∗ |-> v'32 **
     dllseg v'32 Vnull v'25 (Vptr (cur_addr, Int.zero)) v'34
       OS_TCB_flag (fun vl : vallist => nth_val 1 vl)
       (fun vl : vallist => nth_val 0 vl) **
     GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_addr, Int.zero) **
     AEventData
       (V$ OS_EVENT_TYPE_MUTEX
        :: Vint32 i0
           :: Vint32 x
              :: Vptr (ptcb_addr, Int.zero) :: x3 :: v'46 :: nil)
       (DMutex (Vint32 x) (Vptr (ptcb_addr, Int.zero))) **
     Astruct (pevent_addr, Int.zero) OS_EVENT
       (V$ OS_EVENT_TYPE_MUTEX
        :: Vint32 i0
           :: Vint32 x
              :: Vptr (ptcb_addr, Int.zero) :: x3 :: v'46 :: nil) **
     Aarray v'24 (Tarray Int8u ∘ OS_EVENT_TBL_SIZE) v'44 **
     Aie false **
     Ais nil **
     Acs (true :: nil) **
     Aisr empisr **
     GV OSEventList @ OS_EVENT ∗ |-> v'42 **
     evsllseg v'42 (Vptr (pevent_addr, Int.zero)) v'26 v'28 **
     evsllseg v'46 Vnull v'27 v'29 **
     A_isr_is_prop **
     tcbdllflag v'32
       (v'34 ++
        (x0
         :: v'25
            :: x12
               :: Vnull
                  :: V$ 0
                     :: V$ OS_STAT_RDY
                        :: Vint32 cur_prio
                           :: Vint32 i5
                              :: Vint32 i4
                                 :: Vint32 i3
                                    :: Vint32 i1 :: nil)
        :: v'33 ++
           (v'45
            :: v'43
               :: x10
                  :: xm
                     :: Vint32 i11
                        :: Vint32 i10
                           :: Vint32 ptcb_prio
                              :: Vint32 i8
                                 :: Vint32 i7
                                    :: Vint32 i6
                                       :: 
                                       Vint32 i2 :: nil) :: v'35) **
     AOSRdyTblGrp v'37 v'38 **
     AOSTCBPrioTbl v'31 v'37 tcbls v'51 **
     HECBList v'39 **
     HTCBList tcbls **
     HCurTCB (cur_addr, Int.zero) **
     p_local OSLInv (cur_addr, Int.zero) init_lg **
     LV legal @ Int8u |-> (V$ 1) **
     AOSEventFreeList v'5 **
     AOSQFreeList v'6 **
     AOSQFreeBlk v'7 **
     AOSMapTbl **
     AOSUnMapTbl **
     AOSIntNesting **
     AOSTCBFreeList v'22 v'23 **
     AOSTime (Vint32 v'20) **
     HTime v'20 **
     AGVars **
     atoy_inv' **
     LV pevent2 @ OS_EVENT ∗ |-> v'4 **
     LV os_code_defs.isrdy @ Int8u |-> v'2 **
     LV timeout @ Int16u |-> Vint32 i **
     LV pevent @ OS_EVENT ∗ |-> Vptr (pevent_addr, Int.zero) **
     A_dom_lenv
       ((timeout, Int16u)
        :: (pevent, OS_EVENT ∗)
           :: (legal, Int8u)
              :: (pip, Int8u)
                 :: (mprio, Int8u)
                    :: (os_code_defs.isrdy, Int8u)
                       :: (ptcb, OS_TCB ∗)
                          :: (pevent2, OS_EVENT ∗) :: nil)}} 
   EXIT_CRITICAL;ₛ
   RETURN ′ OS_ERR_MUTEX_IDLE {{Afalse}}
.
Proof.
  intros.
  assert (Hptcb_prio_idle: ptcb_prio = $ OS_IDLE_PRIO).
  {
    clear -LHift_true.
    lzh_simpl_int_eq.
    auto.
  }    
  clear LHift_true.
  subst ptcb_prio.
  
(************************* intro cur_stat = rdy *************************)
  hoare lift 24%nat pre.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  hoare_split_pure_all.

  
  transform_pre AOSRdyTblGrp_fold ltac:(sep cancel GAarray;
                                        sep cancel AOSRdyGrp).
  rename v'37 into os_rdy_tbl.
  destruct H9 as (Hrtbl_type & Hrtbl_len).
  destruct H15 as (Hgrp1 & Hgrp2).

  hoare lifts (2::3::4::5::6::7::8::9::10::11::12::13::14
                ::15::16::17::18::19::20::21::23::24::nil)%nat pre.
  
  assert (Htmp1: st = rdy).
  {
    clear -Hcurnode Hrtbl_type Hrtbl_len.
    eapply mutexpend_TCBNode_P_in_tcb_rdy; eauto.
  }
  subst st.
(***************************** imply rdy end *****************************)
(****************************** ex critical ******************************)
  hoare abscsq.
  auto.
  eapply absinfer_mutex_pend_ptcb_is_idle; eauto.
  can_change_aop_solver.
  
  hoare forward prim.

  {
    (** * AECBList *)
    unfold AECBList.
    sep pauto.
    
    eapply lzh_evsllseg_compose.
    sep cancel evsllseg.
    sep cancel evsllseg.
    unfold AEventNode.
    sep pauto.
    sep cancel AEventData.
    unfold AOSEvent.
    sep pauto.
    unfold AOSEventTbl.
    unfold node.
    sep pauto.
    sep cancel 11%nat 1%nat.
    sep cancel Aarray.

    (** * AOSTCBList *)
    unfold AOSTCBList.
    unfold tcbdllseg.
    sep pauto.
    (**** cancel left first *)
    sep cancel dllseg.
    (**** cancel right *)
    unfold dllseg.
    fold dllseg.
    sep pauto.
    unfold node.
    sep pauto.
    sep cancel 7%nat 1%nat.
    
    eapply tcbdllseg_compose with
      (l1:=v'33)
      (l2:=(v'45
             :: v'43
                :: x10
                   :: xm
                      :: Vint32 i11
                         :: Vint32 i10
                            :: V$OS_IDLE_PRIO
                               :: Vint32 i8
                                  :: Vint32 i7
                                     :: Vint32 i6 :: Vint32 i2 :: nil)::v'35).
    sep cancel tcbdllseg.
    unfold tcbdllseg.
    unfold dllseg.
    fold dllseg.
    sep pauto.
    unfold node.
    sep pauto.
    sep cancel Astruct.
    sep cancel 1%nat 1%nat.
    sep cancel 4%nat 1%nat.
    exact_s.
    
    split; [auto | struct_type_match_solver].
    pure_auto.
    split; [auto | struct_type_match_solver].
    unfolds; auto.
    unfolds; auto.

    (**** cancel tcblist_p right *)
    unfold TCBList_P.
    fold TCBList_P.
    do 4 eexists.
    splits.
    eauto.
    unfolds; simpl; auto.
    eapply Htcbjoin_right.
    eauto.
    
    eapply TCBList_P_Combine with 
      (l1:=v'33)
      (l2:=(v'45
             :: v'43
                :: x10
                   :: xm
                      :: Vint32 i11
                         :: Vint32 i10
                            :: V$OS_IDLE_PRIO
                               :: Vint32 i8
                                  :: Vint32 i7
                                     :: Vint32 i6 :: Vint32 i2 :: nil)::v'35).
    eauto.
    eauto.
    eauto.

    unfold TCBList_P.
    fold TCBList_P.
    do 4 eexists.
    splits; eauto.
    unfolds; auto.
    eauto.
    eauto.
    eauto.
    split; [auto | struct_type_match_solver].
    eauto.
    unfolds; auto.
    auto.
    unfolds; auto.
    eauto.
    eauto.

    eauto.
  }
  pauto.
  hoare forward.
Qed.

Lemma mutex_pend_ptcb_is_not_rdy_right_to_cur: forall
  (i : int32)
  (H1 : Int.unsigned i <= 65535)
  (v' v'0 v'1 v'2 v'3 v'4 : val)
  (v'5 v'6 v'7 : list vallist)
  (v'8 : list EventData)
  (v'9 : list os_inv.EventCtr)
  (v'10 : vallist)
  (v'11 v'12 : val)
  (v'13 : list vallist)
  (v'14 : vallist)
  (v'15 : list vallist)
  (v'16 : vallist)
  (v'17 : val)
  (v'18 : EcbMod.map)
  (v'19 : TcbMod.map)
  (v'20 : int32)
  (v'21 : addrval)
  (v'22 : val)
  (v'23 : list vallist)
  (v'26 v'27 : list os_inv.EventCtr)
  (v'28 v'29 : list EventData)
  (v'31 : vallist)
  (v'32 : val)
  (v'34 : list vallist)
  (v'37 : vallist)
  (v'38 : val)
  (v'39 : EcbMod.map)
  (tcbls : TcbMod.map)
  (v'42 : val)
  (v'44 : vallist)
  (v'46 : val)
  (v'47 v'48 v'49 : EcbMod.map)
  (v'51 : addrval)
  (H5 : ECBList_P v'46 Vnull v'27 v'29 v'48 tcbls)
  (H11 : EcbMod.join v'47 v'49 v'39)
  (H14 : length v'26 = length v'28)
  (v'24 : addrval)
  (pevent_addr : block)
  (H13 : array_type_vallist_match Int8u v'44)
  (H19 : length v'44 = ∘ OS_EVENT_TBL_SIZE)
  (H20 : isptr v'46)
  (x3 : val)
  (i0 : int32)
  (H22 : Int.unsigned i0 <= 255)
  (H18 : RL_Tbl_Grp_P v'44 (Vint32 i0))
  (H25 : isptr v'46)
  (H4 : ECBList_P v'42 (Vptr (pevent_addr, Int.zero)) v'26 v'28
         v'47 tcbls)
  (H2 : isptr (Vptr (pevent_addr, Int.zero)))
  (H16 : id_addrval' (Vptr (pevent_addr, Int.zero)) OSEventTbl
          OS_EVENT = Some v'24)
  (H21 : Int.unsigned ($ OS_EVENT_TYPE_MUTEX) <= 255)
  (wls : waitset)
  (v'25 v'41 : val)
  (tcbls_l tcbls_r : TcbMod.map)
  (cur_addr : block)
  (H29 : v'32 <> Vnull)
  (Htcbjoin_whole : join tcbls_l tcbls_r tcbls)
  (Htcblist_subl : TCBList_P v'32 v'34 v'37 tcbls_l)
  (H28 : Vptr (cur_addr, Int.zero) <> Vnull)
  (x12 : val)
  (H35 : isptr x12)
  (cur_prio : int32)
  (H39 : Int.unsigned cur_prio <= 255)
  (i5 : int32)
  (H40 : Int.unsigned i5 <= 255)
  (i4 : int32)
  (H41 : Int.unsigned i4 <= 255)
  (i3 : int32)
  (H42 : Int.unsigned i3 <= 255)
  (i1 : int32)
  (H43 : Int.unsigned i1 <= 255)
  (H34 : isptr v'25)
  (H0 : RH_CurTCB (cur_addr, Int.zero) v'19)
  (H : RH_TCBList_ECBList_P v'39 tcbls (cur_addr, Int.zero))
  (H10 : RH_CurTCB (cur_addr, Int.zero) tcbls)
  (st : taskstatus)
  (Hneq_idle : cur_prio <> $ OS_IDLE_PRIO)
  (H37 : Int.unsigned ($ 0) <= 65535)
  (H38 : Int.unsigned ($ OS_STAT_RDY) <= 255)
  (H36 : isptr Vnull)
  (Hgetcur_subr : TcbMod.get tcbls_r (cur_addr, Int.zero) =
                 Some (cur_prio, st, Vnull))
  (Hgetcur : TcbMod.get tcbls (cur_addr, Int.zero) =
            Some (cur_prio, st, Vnull))
  (x0 : val)
  (tcbls_r' : TcbMod.map)
  (x : int32)
  (F2 H23 : Int.unsigned x <= 65535)
  (Fneq_i2_1 : Int.unsigned (x >>ᵢ $ 8) <= 255)
  (Fneq_i2_2 : Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) <= 255)
  (Hmutex_not_avail : x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 <>
                     $ OS_MUTEX_AVAILABLE)
  (Feq_i2_1 : x >>ᵢ $ 8 = Int.modu (x >>ᵢ $ 8) ($ Byte.modulus))
  (Hcur_prio : Int.ltu (x >>ᵢ $ 8) cur_prio = true)
  (ptcb_prio : priority)
  (xm : msg)
  (xs : taskstatus)
  (H12 : isptr x0)
  (Hcurnode : TCBNode_P
               (x0
                :: v'25
                   :: x12
                      :: Vnull
                         :: V$ 0
                            :: V$ OS_STAT_RDY
                               :: Vint32 cur_prio
                                  :: Vint32 i5
                                     :: Vint32 i4
                                        :: 
                                        Vint32 i3
                                        :: 
                                        Vint32 i1 :: nil) v'37
               (cur_prio, st, Vnull))
  (Htcbjoin_right : TcbJoin (cur_addr, Int.zero)
                     (cur_prio, st, Vnull) tcbls_r' tcbls_r)
  (v'33 v'35 : list vallist)
  (v'43 v'45 : val)
  (tcbls_sub_l v'52 tcbls_sub_r : TcbMod.map)
  (Htcbjoin_sub_whole : TcbMod.join tcbls_sub_l v'52 tcbls_r')
  (Htcblist_sub_left : TCBList_P x0 v'33 v'37 tcbls_sub_l)
  (Htcblist_sub_right : TCBList_P v'45 v'35 v'37 tcbls_sub_r)
  (ptcb_addr : block)
  (x10 : val)
  (H31 : isptr x10)
  (i11 : int32)
  (H33 : Int.unsigned i11 <= 65535)
  (ptcb_stat : int32)
  (H44 : Int.unsigned ptcb_stat <= 255)
  (i8 : int32)
  (H46 : Int.unsigned i8 <= 255)
  (i7 : int32)
  (H47 : Int.unsigned i7 <= 255)
  (i6 : int32)
  (H48 : Int.unsigned i6 <= 255)
  (i2 : int32)
  (H49 : Int.unsigned i2 <= 255)
  (H30 : isptr v'43)
  (H17 : isptr v'45)
  (H24 : isptr (Vptr (ptcb_addr, Int.zero)))
  (H7 : R_ECB_ETbl_P (pevent_addr, Int.zero)
         (V$ OS_EVENT_TYPE_MUTEX
          :: Vint32 i0
             :: Vint32 x
                :: Vptr (ptcb_addr, Int.zero)
                   :: x3 :: v'46 :: nil, v'44) tcbls)
  (H3 : ECBList_P v'42 Vnull
         (v'26 ++
          ((V$ OS_EVENT_TYPE_MUTEX
            :: Vint32 i0
               :: Vint32 x
                  :: Vptr (ptcb_addr, Int.zero)
                     :: x3 :: v'46 :: nil, v'44) :: nil) ++ v'27)
         (v'28 ++
          (DMutex (Vint32 x) (Vptr (ptcb_addr, Int.zero)) :: nil) ++
          v'29) v'39 tcbls)
  (H8 : EcbMod.joinsig (pevent_addr, Int.zero)
         (absmutexsem (x >>ᵢ $ 8)
            (Some
               (ptcb_addr, Int.zero, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)),
         wls) v'48 v'49)
  (Hget : EcbMod.get v'39 (pevent_addr, Int.zero) =
         Some
           (absmutexsem (x >>ᵢ $ 8)
              (Some
                 (ptcb_addr, Int.zero,
                 x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), wls))
  (H26 : RH_ECB_P
          (absmutexsem (x >>ᵢ $ 8)
             (Some
                (ptcb_addr, Int.zero,
                x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), wls))
  (H6 : RLH_ECBData_P
         (DMutex (Vint32 x) (Vptr (ptcb_addr, Int.zero)))
         (absmutexsem (x >>ᵢ $ 8)
            (Some
               (ptcb_addr, Int.zero, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)),
         wls))
  (H_ptcb : TcbMod.get tcbls (ptcb_addr, Int.zero) =
           Some (ptcb_prio, xs, xm))
  (H_ptcb_not_cur : (ptcb_addr, Int.zero) <> (cur_addr, Int.zero))
  (H_ptcb_in_right : TcbMod.get tcbls_r' (ptcb_addr, Int.zero) =
                    Some (ptcb_prio, xs, xm))
  (Htcbjoin_sub_right : TcbMod.joinsig (ptcb_addr, Int.zero)
                         (ptcb_prio, xs, xm) tcbls_sub_r v'52)
  (Hget_last_tcb : get_last_tcb_ptr v'33 x0 =
                  Some (Vptr (ptcb_addr, Int.zero)))
  (H32 : isptr xm)
  (H45 : Int.unsigned ptcb_prio <= 255)
  (Hptcb_node : TCBNode_P
                 (v'45
                  :: v'43
                     :: x10
                        :: xm
                           :: Vint32 i11
                              :: Vint32 ptcb_stat
                                 :: Vint32 ptcb_prio
                                    :: Vint32 i8
                                       :: 
                                       Vint32 i7
                                       :: 
                                       Vint32 i6
                                       :: 
                                       Vint32 i2 :: nil) v'37
                 (ptcb_prio, xs, xm))
  (Htcblist_subr : TCBList_P x0
                    (v'33 ++
                     (v'45
                      :: v'43
                         :: x10
                            :: xm
                               :: Vint32 i11
                                  :: Vint32 ptcb_stat
                                     :: Vint32 ptcb_prio
                                        :: 
                                        Vint32 i8
                                        :: 
                                        Vint32 i7
                                        :: 
                                        Vint32 i6
                                        :: 
                                        Vint32 i2 :: nil)
                     :: v'35) v'37 tcbls_r')
  (Hptcb_blk : RL_TCBblk_P
                (v'45
                 :: v'43
                    :: x10
                       :: xm
                          :: Vint32 i11
                             :: Vint32 ptcb_stat
                                :: Vint32 ptcb_prio
                                   :: Vint32 i8
                                      :: Vint32 i7
                                         :: 
                                         Vint32 i6
                                         :: 
                                         Vint32 i2 :: nil))
  (Hptcb_stat : R_TCB_Status_P
                 (v'45
                  :: v'43
                     :: x10
                        :: xm
                           :: Vint32 i11
                              :: Vint32 ptcb_stat
                                 :: Vint32 ptcb_prio
                                    :: Vint32 i8
                                       :: 
                                       Vint32 i7
                                       :: 
                                       Vint32 i6
                                       :: 
                                       Vint32 i2 :: nil) v'37
                 (ptcb_prio, xs, xm))
  (Hptcb_prio_not_idle : ptcb_prio <> $ OS_IDLE_PRIO)
  (Hptcb_prio_scope_obv : 0 <= Int.unsigned ptcb_prio)
  (Hptcb_prio_scope : Int.unsigned ptcb_prio < 64)
  (Hif_ptcb_is_not_rdy : ptcb_stat <> $ OS_STAT_RDY \/ i11 <> $ 0)
(* ================================= *) ,
   {|OS_spec, GetHPrio, OSLInv, I,
   fun v : option val =>
   ( <|| END v ||>  **
    p_local OSLInv (cur_addr, Int.zero) init_lg **
    ((EX v0 : val, LV timeout @ Int16u |-> v0) **
     (EX v0 : val, LV pevent @ OS_EVENT ∗ |-> v0) **
     (EX v0 : val, LV legal @ Int8u |-> v0) **
     (EX v0 : val, LV pip @ Int8u |-> v0) **
     (EX v0 : val, LV mprio @ Int8u |-> v0) **
     (EX v0 : val, LV os_code_defs.isrdy @ Int8u |-> v0) **
     (EX v0 : val, LV ptcb @ OS_TCB ∗ |-> v0) **
     (EX v0 : val, LV pevent2 @ OS_EVENT ∗ |-> v0) ** Aemp) **
    Aie true ** Ais nil ** Acs nil ** Aisr empisr) **
   A_dom_lenv
     ((timeout, Int16u)
      :: (pevent, OS_EVENT ∗)
         :: (legal, Int8u)
            :: (pip, Int8u)
               :: (mprio, Int8u)
                  :: (os_code_defs.isrdy, Int8u)
                     :: (ptcb, OS_TCB ∗)
                        :: (pevent2, OS_EVENT ∗) :: nil),
   Afalse|}|- (cur_addr, Int.zero)
   {{Astruct (ptcb_addr, Int.zero) OS_TCB_flag
       (v'45
        :: v'43
           :: x10
              :: xm
                 :: Vint32 i11
                    :: Vint32 ptcb_stat
                       :: Vint32 ptcb_prio
                          :: Vint32 i8
                             :: Vint32 i7
                                :: Vint32 i6 :: Vint32 i2 :: nil) **
     tcbdllseg x0 (Vptr (cur_addr, Int.zero)) v'43
       (Vptr (ptcb_addr, Int.zero)) v'33 **
     tcbdllseg v'45 (Vptr (ptcb_addr, Int.zero)) v'41 Vnull v'35 **
      <||
     mutexpend (Vptr (pevent_addr, Int.zero) :: Vint32 i :: nil)
     ||>  **
     LV ptcb @ OS_TCB ∗ |-> Vptr (ptcb_addr, Int.zero) **
     LV mprio @ Int8u |-> Vint32 (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) **
     LV pip @ Int8u |-> Vint32 (x >>ᵢ $ 8) **
     Astruct (cur_addr, Int.zero) OS_TCB_flag
       (x0
        :: v'25
           :: x12
              :: Vnull
                 :: V$ 0
                    :: V$ OS_STAT_RDY
                       :: Vint32 cur_prio
                          :: Vint32 i5
                             :: Vint32 i4
                                :: Vint32 i3 :: Vint32 i1 :: nil) **
     GV OSTCBList @ OS_TCB ∗ |-> v'32 **
     dllseg v'32 Vnull v'25 (Vptr (cur_addr, Int.zero)) v'34
       OS_TCB_flag (fun vl : vallist => nth_val 1 vl)
       (fun vl : vallist => nth_val 0 vl) **
     GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_addr, Int.zero) **
     AEventData
       (V$ OS_EVENT_TYPE_MUTEX
        :: Vint32 i0
           :: Vint32 x
              :: Vptr (ptcb_addr, Int.zero) :: x3 :: v'46 :: nil)
       (DMutex (Vint32 x) (Vptr (ptcb_addr, Int.zero))) **
     Astruct (pevent_addr, Int.zero) OS_EVENT
       (V$ OS_EVENT_TYPE_MUTEX
        :: Vint32 i0
           :: Vint32 x
              :: Vptr (ptcb_addr, Int.zero) :: x3 :: v'46 :: nil) **
     Aarray v'24 (Tarray Int8u ∘ OS_EVENT_TBL_SIZE) v'44 **
     Aie false **
     Ais nil **
     Acs (true :: nil) **
     Aisr empisr **
     GV OSEventList @ OS_EVENT ∗ |-> v'42 **
     evsllseg v'42 (Vptr (pevent_addr, Int.zero)) v'26 v'28 **
     evsllseg v'46 Vnull v'27 v'29 **
     A_isr_is_prop **
     tcbdllflag v'32
       (v'34 ++
        (x0
         :: v'25
            :: x12
               :: Vnull
                  :: V$ 0
                     :: V$ OS_STAT_RDY
                        :: Vint32 cur_prio
                           :: Vint32 i5
                              :: Vint32 i4
                                 :: Vint32 i3
                                    :: Vint32 i1 :: nil)
        :: v'33 ++
           (v'45
            :: v'43
               :: x10
                  :: xm
                     :: Vint32 i11
                        :: Vint32 ptcb_stat
                           :: Vint32 ptcb_prio
                              :: Vint32 i8
                                 :: Vint32 i7
                                    :: Vint32 i6
                                       :: 
                                       Vint32 i2 :: nil) :: v'35) **
     AOSRdyTblGrp v'37 v'38 **
     AOSTCBPrioTbl v'31 v'37 tcbls v'51 **
     HECBList v'39 **
     HTCBList tcbls **
     HCurTCB (cur_addr, Int.zero) **
     p_local OSLInv (cur_addr, Int.zero) init_lg **
     LV legal @ Int8u |-> (V$ 1) **
     AOSEventFreeList v'5 **
     AOSQFreeList v'6 **
     AOSQFreeBlk v'7 **
     AOSMapTbl **
     AOSUnMapTbl **
     AOSIntNesting **
     AOSTCBFreeList v'22 v'23 **
     AOSTime (Vint32 v'20) **
     HTime v'20 **
     AGVars **
     atoy_inv' **
     LV pevent2 @ OS_EVENT ∗ |-> v'4 **
     LV os_code_defs.isrdy @ Int8u |-> v'2 **
     LV timeout @ Int16u |-> Vint32 i **
     LV pevent @ OS_EVENT ∗ |-> Vptr (pevent_addr, Int.zero) **
     A_dom_lenv
       ((timeout, Int16u)
        :: (pevent, OS_EVENT ∗)
           :: (legal, Int8u)
              :: (pip, Int8u)
                 :: (mprio, Int8u)
                    :: (os_code_defs.isrdy, Int8u)
                       :: (ptcb, OS_TCB ∗)
                          :: (pevent2, OS_EVENT ∗) :: nil)}} 
   EXIT_CRITICAL;ₛ
   RETURN ′ OS_ERR_NEST {{Afalse}}
.
Proof.
  intros.
  
  hoare lift 24%nat pre.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  hoare_split_pure_all.

  
  transform_pre AOSRdyTblGrp_fold ltac:(sep cancel GAarray;
                                        sep cancel AOSRdyGrp).
  rename v'38 into os_rdy_tbl.
  destruct H9 as (Hrtbl_type & Hrtbl_len).
  destruct H15 as (Hgrp1 & Hgrp2).

  hoare lifts (2::3::4::5::6::7::8::9::10::11::12::13::14
                ::15::16::17::18::19::20::21::23::25::nil)%nat pre.
  
  assert (Htmp1: st = rdy).
  {
    clear -Hcurnode Hrtbl_type Hrtbl_len.
    eapply mutexpend_TCBNode_P_in_tcb_rdy; eauto.
  }
  subst st.
(***************************** imply rdy end *****************************)
  assert (Htmp: Int.eq ptcb_stat ($ OS_STAT_RDY) = false \/
                Int.eq i11 ($ 0) = false).
  {
    clear -Hif_ptcb_is_not_rdy.
    destruct Hif_ptcb_is_not_rdy.
    left. rewrite Int.eq_false; auto.
    right; rewrite Int.eq_false; auto.
  }
    
  assert (xs <> rdy).
  {
    clear -Hptcb_stat Htmp.
    eapply r_tcb_status_p_nrdy.
    eauto.
    eauto.
  }
  
(****************************** ex critical ******************************)
  hoare abscsq.
  auto.
  eapply absinfer_mutex_pend_ptcb_is_not_rdy; eauto.
  can_change_aop_solver.

  hoare forward prim.

  {
    (** * AECBList *)
    unfold AECBList.
    sep pauto.
    
    eapply lzh_evsllseg_compose.
    sep cancel evsllseg.
    sep cancel evsllseg.
    unfold AEventNode.
    sep pauto.
    sep cancel AEventData.
    unfold AOSEvent.
    sep pauto.
    unfold AOSEventTbl.
    unfold node.
    sep pauto.
    sep cancel 11%nat 1%nat.
    sep cancel Aarray.

    (** * AOSTCBList *)
    unfold AOSTCBList.
    unfold tcbdllseg.
    sep pauto.
    (**** cancel left first *)
    sep cancel dllseg.
    (**** cancel right *)
    unfold dllseg.
    fold dllseg.
    sep pauto.
    unfold node.
    sep pauto.
    sep cancel 7%nat 1%nat.
    
    eapply tcbdllseg_compose with
      (l1:=v'33)
      (l2:=(v'45
              :: v'43
                 :: x10
                    :: xm
                       :: Vint32 i11
                          :: Vint32 ptcb_stat
                             :: Vint32 ptcb_prio
                                :: Vint32 i8
                                   :: Vint32 i7
                                      :: Vint32 i6 :: Vint32 i2 :: nil)::v'35).
    sep cancel tcbdllseg.
    unfold tcbdllseg.
    unfold dllseg.
    fold dllseg.
    sep pauto.
    unfold node.
    sep pauto.
    sep cancel Astruct.
    sep cancel 1%nat 1%nat.
    sep cancel 4%nat 1%nat.
    exact_s.
    
    split; [auto | struct_type_match_solver].
    pure_auto.
    split; [auto | struct_type_match_solver].
    unfolds; auto.
    unfolds; auto.

    (**** cancel tcblist_p right, and left is maybe disappeared automatically... *)
    unfold TCBList_P.
    fold TCBList_P.
    do 4 eexists.
    splits.
    eauto.
    unfolds; simpl; auto.
    eapply Htcbjoin_right.
    eauto.
    
    eapply TCBList_P_Combine with 
      (l1:=v'33)
      (l2:=(v'45
              :: v'43
                 :: x10
                    :: xm
                       :: Vint32 i11
                          :: Vint32 ptcb_stat
                             :: Vint32 ptcb_prio
                                :: Vint32 i8
                                   :: Vint32 i7
                                      :: Vint32 i6 :: Vint32 i2 :: nil)::v'35).
    eauto.
    eauto.
    eauto.

    unfold TCBList_P.
    fold TCBList_P.
    do 4 eexists.
    splits; eauto.
    unfolds; auto.
    eauto.
    eauto.
    eauto.
    split; [auto | struct_type_match_solver].
    eauto.
    unfolds; auto.
    auto.
    unfolds; auto.
    eauto.
    eauto.

    eauto.
  }
  pauto.
  hoare forward.
Qed.

Lemma mutex_pend_cur_prio_eql_mprio_right_to_cur: forall
  (i : int32)
  (H1 : Int.unsigned i <= 65535)
  (v' v'0 v'1 v'2 v'3 v'4 : val)
  (v'5 v'6 v'7 : list vallist)
  (v'8 : list EventData)
  (v'9 : list os_inv.EventCtr)
  (v'10 : vallist)
  (v'11 v'12 : val)
  (v'13 : list vallist)
  (v'14 : vallist)
  (v'15 : list vallist)
  (v'16 : vallist)
  (v'17 : val)
  (v'18 : EcbMod.map)
  (v'19 : TcbMod.map)
  (v'20 : int32)
  (v'21 : addrval)
  (v'22 : val)
  (v'23 : list vallist)
  (v'26 v'27 : list os_inv.EventCtr)
  (v'28 v'29 : list EventData)
  (v'31 : vallist)
  (v'32 : val)
  (v'34 : list vallist)
  (os_rdy_tbl : vallist)
  (v'38 : val)
  (v'39 : EcbMod.map)
  (tcbls : TcbMod.map)
  (v'42 : val)
  (v'44 : vallist)
  (v'46 : val)
  (v'47 v'48 v'49 : EcbMod.map)
  (v'51 : addrval)
  (H5 : ECBList_P v'46 Vnull v'27 v'29 v'48 tcbls)
  (H11 : EcbMod.join v'47 v'49 v'39)
  (H14 : length v'26 = length v'28)
  (v'24 : addrval)
  (pevent_addr : block)
  (H13 : array_type_vallist_match Int8u v'44)
  (H19 : length v'44 = ∘ OS_EVENT_TBL_SIZE)
  (H20 : isptr v'46)
  (x3 : val)
  (i0 : int32)
  (H22 : Int.unsigned i0 <= 255)
  (H18 : RL_Tbl_Grp_P v'44 (Vint32 i0))
  (H25 : isptr v'46)
  (H4 : ECBList_P v'42 (Vptr (pevent_addr, Int.zero)) v'26 v'28
         v'47 tcbls)
  (H2 : isptr (Vptr (pevent_addr, Int.zero)))
  (H16 : id_addrval' (Vptr (pevent_addr, Int.zero)) OSEventTbl
          OS_EVENT = Some v'24)
  (H21 : Int.unsigned ($ OS_EVENT_TYPE_MUTEX) <= 255)
  (wls : waitset)
  (v'25 v'41 : val)
  (tcbls_l tcbls_r : TcbMod.map)
  (cur_addr : block)
  (H29 : v'32 <> Vnull)
  (Htcbjoin_whole : join tcbls_l tcbls_r tcbls)
  (Htcblist_subl : TCBList_P v'32 v'34 os_rdy_tbl tcbls_l)
  (H28 : Vptr (cur_addr, Int.zero) <> Vnull)
  (x12 : val)
  (H35 : isptr x12)
  (cur_prio : int32)
  (H39 : Int.unsigned cur_prio <= 255)
  (i5 : int32)
  (H40 : Int.unsigned i5 <= 255)
  (i4 : int32)
  (H41 : Int.unsigned i4 <= 255)
  (i3 : int32)
  (H42 : Int.unsigned i3 <= 255)
  (i1 : int32)
  (H43 : Int.unsigned i1 <= 255)
  (H34 : isptr v'25)
  (H0 : RH_CurTCB (cur_addr, Int.zero) v'19)
  (H : RH_TCBList_ECBList_P v'39 tcbls (cur_addr, Int.zero))
  (H10 : RH_CurTCB (cur_addr, Int.zero) tcbls)
  (Hneq_idle : cur_prio <> $ OS_IDLE_PRIO)
  (H37 : Int.unsigned ($ 0) <= 65535)
  (H38 : Int.unsigned ($ OS_STAT_RDY) <= 255)
  (H36 : isptr Vnull)
  (x0 : val)
  (tcbls_r' : TcbMod.map)
  (x : int32)
  (F2 H23 : Int.unsigned x <= 65535)
  (Fneq_i2_1 : Int.unsigned (x >>ᵢ $ 8) <= 255)
  (Fneq_i2_2 : Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) <= 255)
  (Hmutex_not_avail : x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 <>
                     $ OS_MUTEX_AVAILABLE)
  (Feq_i2_1 : x >>ᵢ $ 8 = Int.modu (x >>ᵢ $ 8) ($ Byte.modulus))
  (Hcur_prio : Int.ltu (x >>ᵢ $ 8) cur_prio = true)
  (ptcb_prio : priority)
  (xm : msg)
  (H12 : isptr x0)
  (v'33 v'35 : list vallist)
  (v'43 v'45 : val)
  (tcbls_sub_l v'52 tcbls_sub_r : TcbMod.map)
  (Htcbjoin_sub_whole : TcbMod.join tcbls_sub_l v'52 tcbls_r')
  (Htcblist_sub_left : TCBList_P x0 v'33 os_rdy_tbl tcbls_sub_l)
  (Htcblist_sub_right : TCBList_P v'45 v'35 os_rdy_tbl
                         tcbls_sub_r)
  (ptcb_addr : block)
  (x10 : val)
  (H31 : isptr x10)
  (i11 : int32)
  (H33 : Int.unsigned i11 <= 65535)
  (ptcb_stat : int32)
  (H44 : Int.unsigned ptcb_stat <= 255)
  (i8 : int32)
  (H46 : Int.unsigned i8 <= 255)
  (ptcb_tcby : int32)
  (H47 : Int.unsigned ptcb_tcby <= 255)
  (ptcb_bitx : int32)
  (H48 : Int.unsigned ptcb_bitx <= 255)
  (i2 : int32)
  (H49 : Int.unsigned i2 <= 255)
  (H30 : isptr v'43)
  (H17 : isptr v'45)
  (H24 : isptr (Vptr (ptcb_addr, Int.zero)))
  (H7 : R_ECB_ETbl_P (pevent_addr, Int.zero)
         (V$ OS_EVENT_TYPE_MUTEX
          :: Vint32 i0
             :: Vint32 x
                :: Vptr (ptcb_addr, Int.zero)
                   :: x3 :: v'46 :: nil, v'44) tcbls)
  (H3 : ECBList_P v'42 Vnull
         (v'26 ++
          ((V$ OS_EVENT_TYPE_MUTEX
            :: Vint32 i0
               :: Vint32 x
                  :: Vptr (ptcb_addr, Int.zero)
                     :: x3 :: v'46 :: nil, v'44) :: nil) ++ v'27)
         (v'28 ++
          (DMutex (Vint32 x) (Vptr (ptcb_addr, Int.zero)) :: nil) ++
          v'29) v'39 tcbls)
  (H8 : EcbMod.joinsig (pevent_addr, Int.zero)
         (absmutexsem (x >>ᵢ $ 8)
            (Some
               (ptcb_addr, Int.zero, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)),
         wls) v'48 v'49)
  (Hget : EcbMod.get v'39 (pevent_addr, Int.zero) =
         Some
           (absmutexsem (x >>ᵢ $ 8)
              (Some
                 (ptcb_addr, Int.zero,
                 x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), wls))
  (H26 : RH_ECB_P
          (absmutexsem (x >>ᵢ $ 8)
             (Some
                (ptcb_addr, Int.zero,
                x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), wls))
  (H6 : RLH_ECBData_P
         (DMutex (Vint32 x) (Vptr (ptcb_addr, Int.zero)))
         (absmutexsem (x >>ᵢ $ 8)
            (Some
               (ptcb_addr, Int.zero, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)),
         wls))
  (H_ptcb_not_cur : (ptcb_addr, Int.zero) <> (cur_addr, Int.zero))
  (Hget_last_tcb : get_last_tcb_ptr v'33 x0 =
                  Some (Vptr (ptcb_addr, Int.zero)))
  (H32 : isptr xm)
  (H45 : Int.unsigned ptcb_prio <= 255)
  (Htcblist_subr : TCBList_P x0
                    (v'33 ++
                     (v'45
                      :: v'43
                         :: x10
                            :: xm
                               :: Vint32 i11
                                  :: Vint32 ptcb_stat
                                     :: Vint32 ptcb_prio
                                        :: 
                                        Vint32 i8
                                        :: 
                                        Vint32 ptcb_tcby
                                        :: 
                                        Vint32 ptcb_bitx
                                        :: 
                                        Vint32 i2 :: nil)
                     :: v'35) os_rdy_tbl tcbls_r')
  (Hptcb_blk : RL_TCBblk_P
                (v'45
                 :: v'43
                    :: x10
                       :: xm
                          :: Vint32 i11
                             :: Vint32 ptcb_stat
                                :: Vint32 ptcb_prio
                                   :: Vint32 i8
                                      :: Vint32 ptcb_tcby
                                         :: 
                                         Vint32 ptcb_bitx
                                         :: 
                                         Vint32 i2 :: nil))
  (Hptcb_prio_not_idle : ptcb_prio <> $ OS_IDLE_PRIO)
  (Hptcb_prio_scope_obv : 0 <= Int.unsigned ptcb_prio)
  (Hptcb_prio_scope : Int.unsigned ptcb_prio < 64)
  (Hif_ptcb_is_rdy1 : ptcb_stat = $ OS_STAT_RDY)
  (Hif_ptcb_is_rdy2 : i11 = $ 0)
  (Hrtbl_type : array_type_vallist_match Int8u os_rdy_tbl)
  (Hrtbl_len : length os_rdy_tbl = ∘ OS_RDY_TBL_SIZE)
  (Hgrp1 : RL_Tbl_Grp_P os_rdy_tbl v'38)
  (Hgrp2 : prio_in_tbl ($ OS_IDLE_PRIO) os_rdy_tbl)
  (H_ptcb : TcbMod.get tcbls (ptcb_addr, Int.zero) =
           Some (ptcb_prio, rdy, xm))
  (H_ptcb_in_right : TcbMod.get tcbls_r' (ptcb_addr, Int.zero) =
                    Some (ptcb_prio, rdy, xm))
  (Htcbjoin_sub_right : TcbMod.joinsig (ptcb_addr, Int.zero)
                         (ptcb_prio, rdy, xm) tcbls_sub_r v'52)
  (Hptcb_node : TCBNode_P
                 (v'45
                  :: v'43
                     :: x10
                        :: xm
                           :: Vint32 i11
                              :: Vint32 ptcb_stat
                                 :: Vint32 ptcb_prio
                                    :: Vint32 i8
                                       :: 
                                       Vint32 ptcb_tcby
                                       :: 
                                       Vint32 ptcb_bitx
                                       :: 
                                       Vint32 i2 :: nil)
                 os_rdy_tbl (ptcb_prio, rdy, xm))
  (Hptcb_stat : R_TCB_Status_P
                 (v'45
                  :: v'43
                     :: x10
                        :: xm
                           :: Vint32 i11
                              :: Vint32 ptcb_stat
                                 :: Vint32 ptcb_prio
                                    :: Vint32 i8
                                       :: 
                                       Vint32 ptcb_tcby
                                       :: 
                                       Vint32 ptcb_bitx
                                       :: 
                                       Vint32 i2 :: nil)
                 os_rdy_tbl (ptcb_prio, rdy, xm))
  (Hgetcur_subr : TcbMod.get tcbls_r (cur_addr, Int.zero) =
                 Some (cur_prio, rdy, Vnull))
  (Hgetcur : TcbMod.get tcbls (cur_addr, Int.zero) =
            Some (cur_prio, rdy, Vnull))
  (Hcurnode : TCBNode_P
               (x0
                :: v'25
                   :: x12
                      :: Vnull
                         :: V$ 0
                            :: V$ OS_STAT_RDY
                               :: Vint32 cur_prio
                                  :: Vint32 i5
                                     :: Vint32 i4
                                        :: 
                                        Vint32 i3
                                        :: 
                                        Vint32 i1 :: nil)
               os_rdy_tbl (cur_prio, rdy, Vnull))
  (Htcbjoin_right : TcbJoin (cur_addr, Int.zero)
                     (cur_prio, rdy, Vnull) tcbls_r' tcbls_r)
  (Hcur_prio_eql_mprio : Int.eq (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)
                          cur_prio = true)
(* ================================= *) ,
   {|OS_spec, GetHPrio, OSLInv, I,
   fun v : option val =>
   ( <|| END v ||>  **
    p_local OSLInv (cur_addr, Int.zero) init_lg **
    ((EX v0 : val, LV timeout @ Int16u |-> v0) **
     (EX v0 : val, LV pevent @ OS_EVENT ∗ |-> v0) **
     (EX v0 : val, LV legal @ Int8u |-> v0) **
     (EX v0 : val, LV pip @ Int8u |-> v0) **
     (EX v0 : val, LV mprio @ Int8u |-> v0) **
     (EX v0 : val, LV os_code_defs.isrdy @ Int8u |-> v0) **
     (EX v0 : val, LV ptcb @ OS_TCB ∗ |-> v0) **
     (EX v0 : val, LV pevent2 @ OS_EVENT ∗ |-> v0) ** Aemp) **
    Aie true ** Ais nil ** Acs nil ** Aisr empisr) **
   A_dom_lenv
     ((timeout, Int16u)
      :: (pevent, OS_EVENT ∗)
         :: (legal, Int8u)
            :: (pip, Int8u)
               :: (mprio, Int8u)
                  :: (os_code_defs.isrdy, Int8u)
                     :: (ptcb, OS_TCB ∗)
                        :: (pevent2, OS_EVENT ∗) :: nil),
   Afalse|}|- (cur_addr, Int.zero)
   {{Astruct (ptcb_addr, Int.zero) OS_TCB_flag
       (v'45
        :: v'43
           :: x10
              :: xm
                 :: Vint32 i11
                    :: Vint32 ptcb_stat
                       :: Vint32 ptcb_prio
                          :: Vint32 i8
                             :: Vint32 ptcb_tcby
                                :: Vint32 ptcb_bitx
                                   :: Vint32 i2 :: nil) **
     tcbdllseg x0 (Vptr (cur_addr, Int.zero)) v'43
       (Vptr (ptcb_addr, Int.zero)) v'33 **
     tcbdllseg v'45 (Vptr (ptcb_addr, Int.zero)) v'41 Vnull v'35 **
      <||
     mutexpend (Vptr (pevent_addr, Int.zero) :: Vint32 i :: nil)
     ||>  **
     LV ptcb @ OS_TCB ∗ |-> Vptr (ptcb_addr, Int.zero) **
     LV mprio @ Int8u |-> Vint32 (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) **
     LV pip @ Int8u |-> Vint32 (x >>ᵢ $ 8) **
     Astruct (cur_addr, Int.zero) OS_TCB_flag
       (x0
        :: v'25
           :: x12
              :: Vnull
                 :: V$ 0
                    :: V$ OS_STAT_RDY
                       :: Vint32 cur_prio
                          :: Vint32 i5
                             :: Vint32 i4
                                :: Vint32 i3 :: Vint32 i1 :: nil) **
     GV OSTCBList @ OS_TCB ∗ |-> v'32 **
     dllseg v'32 Vnull v'25 (Vptr (cur_addr, Int.zero)) v'34
       OS_TCB_flag (fun vl : vallist => nth_val 1 vl)
       (fun vl : vallist => nth_val 0 vl) **
     GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_addr, Int.zero) **
     AEventData
       (V$ OS_EVENT_TYPE_MUTEX
        :: Vint32 i0
           :: Vint32 x
              :: Vptr (ptcb_addr, Int.zero) :: x3 :: v'46 :: nil)
       (DMutex (Vint32 x) (Vptr (ptcb_addr, Int.zero))) **
     Astruct (pevent_addr, Int.zero) OS_EVENT
       (V$ OS_EVENT_TYPE_MUTEX
        :: Vint32 i0
           :: Vint32 x
              :: Vptr (ptcb_addr, Int.zero) :: x3 :: v'46 :: nil) **
     Aarray v'24 (Tarray Int8u ∘ OS_EVENT_TBL_SIZE) v'44 **
     Aie false **
     Ais nil **
     Acs (true :: nil) **
     Aisr empisr **
     GV OSEventList @ OS_EVENT ∗ |-> v'42 **
     evsllseg v'42 (Vptr (pevent_addr, Int.zero)) v'26 v'28 **
     evsllseg v'46 Vnull v'27 v'29 **
     A_isr_is_prop **
     tcbdllflag v'32
       (v'34 ++
        (x0
         :: v'25
            :: x12
               :: Vnull
                  :: V$ 0
                     :: V$ OS_STAT_RDY
                        :: Vint32 cur_prio
                           :: Vint32 i5
                              :: Vint32 i4
                                 :: Vint32 i3
                                    :: Vint32 i1 :: nil)
        :: v'33 ++
           (v'45
            :: v'43
               :: x10
                  :: xm
                     :: Vint32 i11
                        :: Vint32 ptcb_stat
                           :: Vint32 ptcb_prio
                              :: Vint32 i8
                                 :: Vint32 ptcb_tcby
                                    :: Vint32 ptcb_bitx
                                       :: 
                                       Vint32 i2 :: nil) :: v'35) **
     AOSRdyTblGrp os_rdy_tbl v'38 **
     AOSTCBPrioTbl v'31 os_rdy_tbl tcbls v'51 **
     HECBList v'39 **
     HTCBList tcbls **
     HCurTCB (cur_addr, Int.zero) **
     p_local OSLInv (cur_addr, Int.zero) init_lg **
     LV legal @ Int8u |-> (V$ 1) **
     AOSEventFreeList v'5 **
     AOSQFreeList v'6 **
     AOSQFreeBlk v'7 **
     AOSMapTbl **
     AOSUnMapTbl **
     AOSIntNesting **
     AOSTCBFreeList v'22 v'23 **
     AOSTime (Vint32 v'20) **
     HTime v'20 **
     AGVars **
     atoy_inv' **
     LV pevent2 @ OS_EVENT ∗ |-> v'4 **
     LV os_code_defs.isrdy @ Int8u |-> v'2 **
     LV timeout @ Int16u |-> Vint32 i **
     LV pevent @ OS_EVENT ∗ |-> Vptr (pevent_addr, Int.zero) **
     A_dom_lenv
       ((timeout, Int16u)
        :: (pevent, OS_EVENT ∗)
           :: (legal, Int8u)
              :: (pip, Int8u)
                 :: (mprio, Int8u)
                    :: (os_code_defs.isrdy, Int8u)
                       :: (ptcb, OS_TCB ∗)
                          :: (pevent2, OS_EVENT ∗) :: nil)}} 
   EXIT_CRITICAL;ₛ
   RETURN ′ OS_ERR_MUTEX_DEADLOCK {{Afalse}}
.
Proof.
  intros.
  assert (Htmp: (x &ᵢ $ OS_MUTEX_KEEP_LOWER_8) = cur_prio).
  {
    clear -Hcur_prio_eql_mprio.
    lzh_simpl_int_eq.
    auto.
  }
  clear Hcur_prio_eql_mprio.
  rename Htmp into Hcur_prio_eql_mprio.

(****************************** ex critical ******************************)
  hoare abscsq.
  auto.
  eapply absinfer_mutex_pend_cur_prio_eql_mprio; eauto.
  can_change_aop_solver.

  hoare forward prim.

  {
    (** * AECBList *)
    unfold AECBList.
    sep pauto.
    
    eapply lzh_evsllseg_compose.
    sep cancel evsllseg.
    sep cancel evsllseg.
    unfold AEventNode.
    sep pauto.
    sep cancel AEventData.
    unfold AOSEvent.
    sep pauto.
    unfold AOSEventTbl.
    unfold node.
    sep pauto.
    sep cancel 11%nat 1%nat.
    sep cancel Aarray.

    (** * AOSTCBList *)
    unfold AOSTCBList.
    unfold tcbdllseg.
    sep pauto.
    (**** cancel left first *)
    sep cancel dllseg.
    (**** cancel right *)
    unfold dllseg.
    fold dllseg.
    sep pauto.
    unfold node.
    sep pauto.
    sep cancel 7%nat 1%nat.
    
    eapply tcbdllseg_compose with
      (l1:=v'33)
      (l2:=(v'45
             :: v'43
                :: x10
                   :: xm
                      :: V$0
                         :: V$OS_STAT_RDY
                            :: Vint32 ptcb_prio
                               :: Vint32 i8
                                  :: Vint32 ptcb_tcby
                                     :: Vint32 ptcb_bitx :: Vint32 i2 :: nil)::v'35).
    sep cancel tcbdllseg.
    unfold tcbdllseg.
    unfold dllseg.
    fold dllseg.
    sep pauto.
    unfold node.
    sep pauto.
    sep cancel Astruct.
    sep cancel 1%nat 1%nat.
    sep cancel 4%nat 1%nat.
    exact_s.
    
    
    split; [auto | struct_type_match_solver].
    pure_auto.
    split; [auto | struct_type_match_solver].
    unfolds; auto.
    unfolds; auto.

    (**** cancel tcblist_p right *)
    unfold TCBList_P.
    fold TCBList_P.
    do 4 eexists.
    splits.
    eauto.
    unfolds; simpl; auto.
    eapply Htcbjoin_right.
    eauto.
    
    eapply TCBList_P_Combine with 
      (l1:=v'33)
      (l2:=(v'45
             :: v'43
                :: x10
                   :: xm
                      :: V$0
                         :: V$OS_STAT_RDY
                            :: Vint32 ptcb_prio
                               :: Vint32 i8
                                  :: Vint32 ptcb_tcby
                                     :: Vint32 ptcb_bitx :: Vint32 i2 :: nil)::v'35).
    eauto.
    eauto.
    eauto.

    unfold TCBList_P.
    fold TCBList_P.
    do 4 eexists.
    splits; eauto.
    unfolds; auto.
    eauto.
    eauto.
    eauto.
    split; [auto | struct_type_match_solver].
    eauto.
    unfolds; auto.
    auto.
    unfolds; auto.
    eauto.
    eauto.

    eauto.
  }
  pauto.
  hoare forward.
Qed.

Lemma mutex_pend_pip_is_not_hold_right_to_cur: forall
  (i : int32)
  (H1 : Int.unsigned i <= 65535)
  (v' v'0 v'1 v'2 v'3 v'4 : val)
  (v'5 v'6 v'7 : list vallist)
  (v'8 : list EventData)
  (v'9 : list os_inv.EventCtr)
  (v'10 : vallist)
  (v'11 v'12 : val)
  (v'13 : list vallist)
  (v'14 : vallist)
  (v'15 : list vallist)
  (v'16 : vallist)
  (v'17 : val)
  (v'18 : EcbMod.map)
  (v'19 : TcbMod.map)
  (v'20 : int32)
  (v'21 : addrval)
  (v'22 : val)
  (v'23 : list vallist)
  (v'26 v'27 : list os_inv.EventCtr)
  (v'28 v'29 : list EventData)
  (ptbl : vallist)
  (v'32 : val)
  (v'34 : list vallist)
  (os_rdy_tbl : vallist)
  (v'38 : val)
  (v'39 : EcbMod.map)
  (tcbls : TcbMod.map)
  (v'42 : val)
  (v'44 : vallist)
  (v'46 : val)
  (v'47 v'48 v'49 : EcbMod.map)
  (v'51 : addrval)
  (H5 : ECBList_P v'46 Vnull v'27 v'29 v'48 tcbls)
  (H11 : EcbMod.join v'47 v'49 v'39)
  (H14 : length v'26 = length v'28)
  (v'24 : addrval)
  (pevent_addr : block)
  (H13 : array_type_vallist_match Int8u v'44)
  (H19 : length v'44 = ∘ OS_EVENT_TBL_SIZE)
  (H20 : isptr v'46)
  (x3 : val)
  (i0 : int32)
  (H22 : Int.unsigned i0 <= 255)
  (H18 : RL_Tbl_Grp_P v'44 (Vint32 i0))
  (H25 : isptr v'46)
  (H4 : ECBList_P v'42 (Vptr (pevent_addr, Int.zero)) v'26 v'28
         v'47 tcbls)
  (H2 : isptr (Vptr (pevent_addr, Int.zero)))
  (H16 : id_addrval' (Vptr (pevent_addr, Int.zero)) OSEventTbl
          OS_EVENT = Some v'24)
  (H21 : Int.unsigned ($ OS_EVENT_TYPE_MUTEX) <= 255)
  (wls : waitset)
  (v'25 v'41 : val)
  (tcbls_l tcbls_r : TcbMod.map)
  (cur_addr : block)
  (H29 : v'32 <> Vnull)
  (Htcbjoin_whole : join tcbls_l tcbls_r tcbls)
  (Htcblist_subl : TCBList_P v'32 v'34 os_rdy_tbl tcbls_l)
  (H28 : Vptr (cur_addr, Int.zero) <> Vnull)
  (x12 : val)
  (H35 : isptr x12)
  (cur_prio : int32)
  (H39 : Int.unsigned cur_prio <= 255)
  (i5 : int32)
  (H40 : Int.unsigned i5 <= 255)
  (i4 : int32)
  (H41 : Int.unsigned i4 <= 255)
  (i3 : int32)
  (H42 : Int.unsigned i3 <= 255)
  (i1 : int32)
  (H43 : Int.unsigned i1 <= 255)
  (H34 : isptr v'25)
  (H0 : RH_CurTCB (cur_addr, Int.zero) v'19)
  (H : RH_TCBList_ECBList_P v'39 tcbls (cur_addr, Int.zero))
  (H10 : RH_CurTCB (cur_addr, Int.zero) tcbls)
  (Hneq_idle : cur_prio <> $ OS_IDLE_PRIO)
  (H37 : Int.unsigned ($ 0) <= 65535)
  (H38 : Int.unsigned ($ OS_STAT_RDY) <= 255)
  (H36 : isptr Vnull)
  (x0 : val)
  (tcbls_r' : TcbMod.map)
  (x : int32)
  (F2 H23 : Int.unsigned x <= 65535)
  (Fneq_i2_1 : Int.unsigned (x >>ᵢ $ 8) <= 255)
  (Fneq_i2_2 : Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) <= 255)
  (Hmutex_not_avail : x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 <>
                     $ OS_MUTEX_AVAILABLE)
  (Feq_i2_1 : x >>ᵢ $ 8 = Int.modu (x >>ᵢ $ 8) ($ Byte.modulus))
  (Hcur_prio : Int.ltu (x >>ᵢ $ 8) cur_prio = true)
  (ptcb_prio : priority)
  (xm : msg)
  (H12 : isptr x0)
  (v'33 v'35 : list vallist)
  (v'43 v'45 : val)
  (tcbls_sub_l v'52 tcbls_sub_r : TcbMod.map)
  (Htcbjoin_sub_whole : TcbMod.join tcbls_sub_l v'52 tcbls_r')
  (Htcblist_sub_left : TCBList_P x0 v'33 os_rdy_tbl tcbls_sub_l)
  (Htcblist_sub_right : TCBList_P v'45 v'35 os_rdy_tbl
                         tcbls_sub_r)
  (ptcb_addr : block)
  (x10 : val)
  (H31 : isptr x10)
  (i11 : int32)
  (H33 : Int.unsigned i11 <= 65535)
  (ptcb_stat : int32)
  (H44 : Int.unsigned ptcb_stat <= 255)
  (i8 : int32)
  (H46 : Int.unsigned i8 <= 255)
  (ptcb_tcby : int32)
  (H47 : Int.unsigned ptcb_tcby <= 255)
  (ptcb_bitx : int32)
  (H48 : Int.unsigned ptcb_bitx <= 255)
  (i2 : int32)
  (H49 : Int.unsigned i2 <= 255)
  (H30 : isptr v'43)
  (H17 : isptr v'45)
  (H24 : isptr (Vptr (ptcb_addr, Int.zero)))
  (H7 : R_ECB_ETbl_P (pevent_addr, Int.zero)
         (V$ OS_EVENT_TYPE_MUTEX
          :: Vint32 i0
             :: Vint32 x
                :: Vptr (ptcb_addr, Int.zero)
                   :: x3 :: v'46 :: nil, v'44) tcbls)
  (H3 : ECBList_P v'42 Vnull
         (v'26 ++
          ((V$ OS_EVENT_TYPE_MUTEX
            :: Vint32 i0
               :: Vint32 x
                  :: Vptr (ptcb_addr, Int.zero)
                     :: x3 :: v'46 :: nil, v'44) :: nil) ++ v'27)
         (v'28 ++
          (DMutex (Vint32 x) (Vptr (ptcb_addr, Int.zero)) :: nil) ++
          v'29) v'39 tcbls)
  (H8 : EcbMod.joinsig (pevent_addr, Int.zero)
         (absmutexsem (x >>ᵢ $ 8)
            (Some
               (ptcb_addr, Int.zero, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)),
         wls) v'48 v'49)
  (Hget : EcbMod.get v'39 (pevent_addr, Int.zero) =
         Some
           (absmutexsem (x >>ᵢ $ 8)
              (Some
                 (ptcb_addr, Int.zero,
                 x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), wls))
  (H26 : RH_ECB_P
          (absmutexsem (x >>ᵢ $ 8)
             (Some
                (ptcb_addr, Int.zero,
                x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), wls))
  (H6 : RLH_ECBData_P
         (DMutex (Vint32 x) (Vptr (ptcb_addr, Int.zero)))
         (absmutexsem (x >>ᵢ $ 8)
            (Some
               (ptcb_addr, Int.zero, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)),
         wls))
  (H_ptcb_not_cur : (ptcb_addr, Int.zero) <> (cur_addr, Int.zero))
  (Hget_last_tcb : get_last_tcb_ptr v'33 x0 =
                  Some (Vptr (ptcb_addr, Int.zero)))
  (H32 : isptr xm)
  (H45 : Int.unsigned ptcb_prio <= 255)
  (Htcblist_subr : TCBList_P x0
                    (v'33 ++
                     (v'45
                      :: v'43
                         :: x10
                            :: xm
                               :: Vint32 i11
                                  :: Vint32 ptcb_stat
                                     :: Vint32 ptcb_prio
                                        :: 
                                        Vint32 i8
                                        :: 
                                        Vint32 ptcb_tcby
                                        :: 
                                        Vint32 ptcb_bitx
                                        :: 
                                        Vint32 i2 :: nil)
                     :: v'35) os_rdy_tbl tcbls_r')
  (Hptcb_blk : RL_TCBblk_P
                (v'45
                 :: v'43
                    :: x10
                       :: xm
                          :: Vint32 i11
                             :: Vint32 ptcb_stat
                                :: Vint32 ptcb_prio
                                   :: Vint32 i8
                                      :: Vint32 ptcb_tcby
                                         :: 
                                         Vint32 ptcb_bitx
                                         :: 
                                         Vint32 i2 :: nil))
  (Hptcb_prio_not_idle : ptcb_prio <> $ OS_IDLE_PRIO)
  (Hptcb_prio_scope_obv : 0 <= Int.unsigned ptcb_prio)
  (Hptcb_prio_scope : Int.unsigned ptcb_prio < 64)
  (Hif_ptcb_is_rdy1 : ptcb_stat = $ OS_STAT_RDY)
  (Hif_ptcb_is_rdy2 : i11 = $ 0)
  (Hrtbl_type : array_type_vallist_match Int8u os_rdy_tbl)
  (Hrtbl_len : length os_rdy_tbl = ∘ OS_RDY_TBL_SIZE)
  (Hgrp1 : RL_Tbl_Grp_P os_rdy_tbl v'38)
  (Hgrp2 : prio_in_tbl ($ OS_IDLE_PRIO) os_rdy_tbl)
  (H_ptcb : TcbMod.get tcbls (ptcb_addr, Int.zero) =
           Some (ptcb_prio, rdy, xm))
  (H_ptcb_in_right : TcbMod.get tcbls_r' (ptcb_addr, Int.zero) =
                    Some (ptcb_prio, rdy, xm))
  (Htcbjoin_sub_right : TcbMod.joinsig (ptcb_addr, Int.zero)
                         (ptcb_prio, rdy, xm) tcbls_sub_r v'52)
  (Hptcb_node : TCBNode_P
                 (v'45
                  :: v'43
                     :: x10
                        :: xm
                           :: Vint32 i11
                              :: Vint32 ptcb_stat
                                 :: Vint32 ptcb_prio
                                    :: Vint32 i8
                                       :: 
                                       Vint32 ptcb_tcby
                                       :: 
                                       Vint32 ptcb_bitx
                                       :: 
                                       Vint32 i2 :: nil)
                 os_rdy_tbl (ptcb_prio, rdy, xm))
  (Hptcb_stat : R_TCB_Status_P
                 (v'45
                  :: v'43
                     :: x10
                        :: xm
                           :: Vint32 i11
                              :: Vint32 ptcb_stat
                                 :: Vint32 ptcb_prio
                                    :: Vint32 i8
                                       :: 
                                       Vint32 ptcb_tcby
                                       :: 
                                       Vint32 ptcb_bitx
                                       :: 
                                       Vint32 i2 :: nil)
                 os_rdy_tbl (ptcb_prio, rdy, xm))
  (Hgetcur_subr : TcbMod.get tcbls_r (cur_addr, Int.zero) =
                 Some (cur_prio, rdy, Vnull))
  (Hgetcur : TcbMod.get tcbls (cur_addr, Int.zero) =
            Some (cur_prio, rdy, Vnull))
  (Hcurnode : TCBNode_P
               (x0
                :: v'25
                   :: x12
                      :: Vnull
                         :: V$ 0
                            :: V$ OS_STAT_RDY
                               :: Vint32 cur_prio
                                  :: Vint32 i5
                                     :: Vint32 i4
                                        :: 
                                        Vint32 i3
                                        :: 
                                        Vint32 i1 :: nil)
               os_rdy_tbl (cur_prio, rdy, Vnull))
  (Htcbjoin_right : TcbJoin (cur_addr, Int.zero)
                     (cur_prio, rdy, Vnull) tcbls_r' tcbls_r)
  (Hif_false : Int.eq (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) cur_prio =
              false)
  (Hnocur : Int.eq cur_prio (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = false)
  (H_cur_prio_scope : Int.unsigned cur_prio < 64)
  (Hx_scope1 : Int.unsigned (x >>ᵢ $ 8) < 64)
  (Hif_can_lift1 : ptcb_prio <> x >>ᵢ $ 8)
  (Hif_can_lift2 : Int.ltu cur_prio (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) =
                  true)
  (v'30 : val)
  (Hptbl_1 : array_type_vallist_match OS_TCB ∗ ptbl)
  (Hptbl_2 : length ptbl = 64%nat)
  (H15 : RL_RTbl_PrioTbl_P os_rdy_tbl ptbl v'51)
  (H27 : R_PrioTbl_P ptbl tcbls v'51)
  (Hif_true : val_inj
               (uop_eval
                  (val_inj
                     (bop_eval
                        (nth_val'
                           (Z.to_nat (Int.unsigned (x >>ᵢ $ 8)))
                           ptbl) (Vptr v'51) 
                        OS_TCB ∗ OS_TCB ∗ oeq)) oppsite) <>
             Vint32 Int.zero /\
             val_inj
               (uop_eval
                  (val_inj
                     (bop_eval
                        (nth_val'
                           (Z.to_nat (Int.unsigned (x >>ᵢ $ 8)))
                           ptbl) (Vptr v'51) 
                        OS_TCB ∗ OS_TCB ∗ oeq)) oppsite) <>
             Vnull /\
             val_inj
               (uop_eval
                  (val_inj
                     (bop_eval
                        (nth_val'
                           (Z.to_nat (Int.unsigned (x >>ᵢ $ 8)))
                           ptbl) (Vptr v'51) 
                        OS_TCB ∗ OS_TCB ∗ oeq)) oppsite) <>
             Vundef)
(* ================================= *) ,
   {|OS_spec, GetHPrio, OSLInv, I,
   fun v : option val =>
   ( <|| END v ||>  **
    p_local OSLInv (cur_addr, Int.zero) init_lg **
    ((EX v0 : val, LV timeout @ Int16u |-> v0) **
     (EX v0 : val, LV pevent @ OS_EVENT ∗ |-> v0) **
     (EX v0 : val, LV legal @ Int8u |-> v0) **
     (EX v0 : val, LV pip @ Int8u |-> v0) **
     (EX v0 : val, LV mprio @ Int8u |-> v0) **
     (EX v0 : val, LV os_code_defs.isrdy @ Int8u |-> v0) **
     (EX v0 : val, LV ptcb @ OS_TCB ∗ |-> v0) **
     (EX v0 : val, LV pevent2 @ OS_EVENT ∗ |-> v0) ** Aemp) **
    Aie true ** Ais nil ** Acs nil ** Aisr empisr) **
   A_dom_lenv
     ((timeout, Int16u)
      :: (pevent, OS_EVENT ∗)
         :: (legal, Int8u)
            :: (pip, Int8u)
               :: (mprio, Int8u)
                  :: (os_code_defs.isrdy, Int8u)
                     :: (ptcb, OS_TCB ∗)
                        :: (pevent2, OS_EVENT ∗) :: nil),
   Afalse|}|- (cur_addr, Int.zero)
   {{PV v'51 @ Int8u |-> v'30 **
     Astruct (ptcb_addr, Int.zero) OS_TCB_flag
       (v'45
        :: v'43
           :: x10
              :: xm
                 :: Vint32 i11
                    :: Vint32 ptcb_stat
                       :: Vint32 ptcb_prio
                          :: Vint32 i8
                             :: Vint32 ptcb_tcby
                                :: Vint32 ptcb_bitx
                                   :: Vint32 i2 :: nil) **
     tcbdllseg x0 (Vptr (cur_addr, Int.zero)) v'43
       (Vptr (ptcb_addr, Int.zero)) v'33 **
     tcbdllseg v'45 (Vptr (ptcb_addr, Int.zero)) v'41 Vnull v'35 **
      <||
     mutexpend (Vptr (pevent_addr, Int.zero) :: Vint32 i :: nil)
     ||>  **
     LV ptcb @ OS_TCB ∗ |-> Vptr (ptcb_addr, Int.zero) **
     LV mprio @ Int8u |-> Vint32 (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) **
     LV pip @ Int8u |-> Vint32 (x >>ᵢ $ 8) **
     Astruct (cur_addr, Int.zero) OS_TCB_flag
       (x0
        :: v'25
           :: x12
              :: Vnull
                 :: V$ 0
                    :: V$ OS_STAT_RDY
                       :: Vint32 cur_prio
                          :: Vint32 i5
                             :: Vint32 i4
                                :: Vint32 i3 :: Vint32 i1 :: nil) **
     GV OSTCBList @ OS_TCB ∗ |-> v'32 **
     dllseg v'32 Vnull v'25 (Vptr (cur_addr, Int.zero)) v'34
       OS_TCB_flag (fun vl : vallist => nth_val 1 vl)
       (fun vl : vallist => nth_val 0 vl) **
     GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_addr, Int.zero) **
     AEventData
       (V$ OS_EVENT_TYPE_MUTEX
        :: Vint32 i0
           :: Vint32 x
              :: Vptr (ptcb_addr, Int.zero) :: x3 :: v'46 :: nil)
       (DMutex (Vint32 x) (Vptr (ptcb_addr, Int.zero))) **
     Astruct (pevent_addr, Int.zero) OS_EVENT
       (V$ OS_EVENT_TYPE_MUTEX
        :: Vint32 i0
           :: Vint32 x
              :: Vptr (ptcb_addr, Int.zero) :: x3 :: v'46 :: nil) **
     Aarray v'24 (Tarray Int8u ∘ OS_EVENT_TBL_SIZE) v'44 **
     Aie false **
     Ais nil **
     Acs (true :: nil) **
     Aisr empisr **
     GV OSEventList @ OS_EVENT ∗ |-> v'42 **
     evsllseg v'42 (Vptr (pevent_addr, Int.zero)) v'26 v'28 **
     evsllseg v'46 Vnull v'27 v'29 **
     A_isr_is_prop **
     tcbdllflag v'32
       (v'34 ++
        (x0
         :: v'25
            :: x12
               :: Vnull
                  :: V$ 0
                     :: V$ OS_STAT_RDY
                        :: Vint32 cur_prio
                           :: Vint32 i5
                              :: Vint32 i4
                                 :: Vint32 i3
                                    :: Vint32 i1 :: nil)
        :: v'33 ++
           (v'45
            :: v'43
               :: x10
                  :: xm
                     :: Vint32 i11
                        :: Vint32 ptcb_stat
                           :: Vint32 ptcb_prio
                              :: Vint32 i8
                                 :: Vint32 ptcb_tcby
                                    :: Vint32 ptcb_bitx
                                       :: 
                                       Vint32 i2 :: nil) :: v'35) **
     AOSRdyTblGrp os_rdy_tbl v'38 **
     GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64) ptbl **
     G& OSPlaceHolder @ Int8u == v'51 **
     HECBList v'39 **
     HTCBList tcbls **
     HCurTCB (cur_addr, Int.zero) **
     p_local OSLInv (cur_addr, Int.zero) init_lg **
     LV legal @ Int8u |-> (V$ 1) **
     AOSEventFreeList v'5 **
     AOSQFreeList v'6 **
     AOSQFreeBlk v'7 **
     AOSMapTbl **
     AOSUnMapTbl **
     AOSIntNesting **
     AOSTCBFreeList v'22 v'23 **
     AOSTime (Vint32 v'20) **
     HTime v'20 **
     AGVars **
     atoy_inv' **
     LV pevent2 @ OS_EVENT ∗ |-> v'4 **
     LV os_code_defs.isrdy @ Int8u |-> v'2 **
     LV timeout @ Int16u |-> Vint32 i **
     LV pevent @ OS_EVENT ∗ |-> Vptr (pevent_addr, Int.zero) **
     A_dom_lenv
       ((timeout, Int16u)
        :: (pevent, OS_EVENT ∗)
           :: (legal, Int8u)
              :: (pip, Int8u)
                 :: (mprio, Int8u)
                    :: (os_code_defs.isrdy, Int8u)
                       :: (ptcb, OS_TCB ∗)
                          :: (pevent2, OS_EVENT ∗) :: nil)}} 
   EXIT_CRITICAL;ₛ
   RETURN ′ OS_ERR_MUTEXPR_NOT_HOLDER {{Afalse}}
.
Proof.
  intros.
  
(****************************** ex critical ******************************)
  hoare abscsq.
  auto.
  eapply absinfer_mutex_pend_pip_is_not_hold; eauto.
  can_change_aop_solver.

  hoare forward prim.

  {
    (** * AECBList *)
    unfold AECBList.
    sep pauto.
    
    eapply lzh_evsllseg_compose.
    sep cancel evsllseg.
    sep cancel evsllseg.
    unfold AEventNode.
    sep pauto.
    sep cancel AEventData.
    unfold AOSEvent.
    sep pauto.
    unfold AOSEventTbl.
    unfold node.
    sep pauto.
    sep cancel 12%nat 1%nat.
    sep cancel Aarray.

    (** * AOSTCBList *)
    unfold AOSTCBList.
    unfold tcbdllseg.
    sep pauto.
    (**** cancel left first *)
    sep cancel dllseg.
    (**** cancel right *)
    unfold dllseg.
    fold dllseg.
    sep pauto.
    unfold node.
    sep pauto.
    sep cancel 8%nat 1%nat.
    
    eapply tcbdllseg_compose with
      (l1:=v'33)
      (l2:=(v'45
             :: v'43
                :: x10
                   :: xm
                      :: V$0
                         :: V$OS_STAT_RDY
                            :: Vint32 ptcb_prio
                               :: Vint32 i8
                                  :: Vint32 ptcb_tcby
                                     :: Vint32 ptcb_bitx :: Vint32 i2 :: nil)::v'35).
    sep cancel tcbdllseg.
    unfold tcbdllseg.
    unfold dllseg.
    fold dllseg.
    sep pauto.
    unfold node.
    sep pauto.
    sep cancel Astruct.
    sep cancel 2%nat 1%nat.
    unfold AOSTCBPrioTbl.
    sep pauto.
    sep cancel 1%nat 1%nat.
    sep cancel 5%nat 1%nat.
    sep cancel 4%nat 1%nat.
    exact_s.

    eauto.
    eauto.
    go.
    pure_auto.
    go.
    go.
    go.
    go.
    
    (**** cancel tcblist_p right *)
    unfold TCBList_P.
    fold TCBList_P.
    do 4 eexists.
    splits.
    eauto.
    unfolds; simpl; auto.
    eapply Htcbjoin_right.
    eauto.
    
    eapply TCBList_P_Combine with 
      (l1:=v'33)
      (l2:=(v'45
             :: v'43
                :: x10
                   :: xm
                      :: V$0
                         :: V$OS_STAT_RDY
                            :: Vint32 ptcb_prio
                               :: Vint32 i8
                                  :: Vint32 ptcb_tcby
                                     :: Vint32 ptcb_bitx :: Vint32 i2 :: nil)::v'35).
    eauto.
    eauto.
    eauto.

    unfold TCBList_P.
    fold TCBList_P.
    do 4 eexists.
    splits; eauto.
    unfolds; auto.
    eauto.
    eauto.
    eauto.
    split; [auto | struct_type_match_solver].
    eauto.
    unfolds; auto.
    auto.
    unfolds; auto.
    eauto.
    eauto.

    eauto.
  }
  pauto.
  hoare forward.
Qed.
