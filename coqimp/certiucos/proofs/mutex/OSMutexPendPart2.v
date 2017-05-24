Require Import sem_common.
Require Import sempend_pure.
Require Import OSMutex_common.
Require Import OSQPostPure.
Require Import mutex_pend_pure.
Require Import OSMutexPendPure1.
Require Import OSEventTaskRdyPure.

Require Import OSTimeDlyPure.
Require Import Mbox_common.
Require Import symbolic_lemmas.
Open Scope code_scope.

Hint Resolve noabs_oslinv.
Hint Extern 2 (_ <= _) => apply Z.leb_le; trivial.

Open Scope list_scope.
Open Scope int_scope.
Open Scope Z_scope.

Ltac simpl_vqm :=
  repeat
    match goal with
      | H: _ = Some _ |- _ => simpl in H;inverts H
      | _ => idtac
    end.

Lemma mutex_pend_ptcb_is_rdy_right_to_cur: forall
  (i : int32)
  (H1 : Int.unsigned i <= 65535)
  (v' : val)
  (v'0 : val)
  (v'1 : val)
  (v'2 : val)
  (v'3 : val)
  (v'4 : val)
  (v'5 : list vallist)
  (v'6 : list vallist)
  (v'7 : list vallist)
  (v'8 : list EventData)
  (v'9 : list EventCtr)
  (v'10 : vallist)
  (v'11 : val)
  (v'12 : val)
  (v'13 : list vallist)
  (v'14 : vallist)
  (v'15 : list vallist)
  (v'16 : vallist)
  (v'17 : val)
  (v'18 : EcbMod.map)
  (v'19 : TcbMod.map)
  (v'20 : int32)
  (v'21 : addrval)
  (v'22 : addrval)
  (v'23 : val)
  (v'24 : list vallist)
  (H0 : RH_CurTCB v'21 v'19)
  (v'27 : list EventCtr)
  (v'28 : list EventCtr)
  (v'29 : list EventData)
  (v'30 : list EventData)
  (ptbl : vallist)
  (v'33 : val)
  (v'35 : list vallist)
  (os_rdy_tbl : vallist)
  (v'39 : val)
  (v'40 : EcbMod.map)
  (tcbls : TcbMod.map)
  (v'44 : val)
  (v'46 : vallist)
  (v'48 : val)
  (v'49 : EcbMod.map)
  (v'50 : EcbMod.map)
  (v'51 : EcbMod.map)
  (v'53 : addrval)
  (H5 : ECBList_P v'48 Vnull v'28 v'30 v'50 tcbls)
  (H11 : EcbMod.join v'49 v'51 v'40)
  (H14 : length v'27 = length v'29)
  (v'25 : addrval)
  (pevent_addr : block)
  (H13 : array_type_vallist_match Int8u v'46)
  (H19 : length v'46 = ∘OS_EVENT_TBL_SIZE)
  (H20 : isptr v'48)
  (x3 : val)
  (i0 : int32)
  (H22 : Int.unsigned i0 <= 255)
  (H18 : RL_Tbl_Grp_P v'46 (Vint32 i0))
  (H25 : isptr v'48)
  (H4 : ECBList_P v'44 (Vptr (pevent_addr, Int.zero)) v'27 v'29 v'49 tcbls)
  (H2 : isptr (Vptr (pevent_addr, Int.zero)))
  (H16 : id_addrval' (Vptr (pevent_addr, Int.zero)) OSEventTbl OS_EVENT =
        Some v'25)
  (H21 : Int.unsigned ($ OS_EVENT_TYPE_MUTEX) <= 255)
  (wls : waitset)
  (v'26 : val)
  (v'42 : val)
  (tcbls_l : TcbMod.map)
  (tcbls_r : TcbMod.map)
  (cur_addr : block)
  (H29 : v'33 <> Vnull)
  (Htcbjoin_whole : TcbMod.join tcbls_l tcbls_r tcbls)
  (Htcblist_subl : TCBList_P v'33 v'35 os_rdy_tbl tcbls_l)
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
  (H34 : isptr v'26)
  (H : RH_TCBList_ECBList_P v'40 tcbls (cur_addr, Int.zero))
  (H10 : RH_CurTCB (cur_addr, Int.zero) tcbls)
  (Hneq_idle : cur_prio <> $ OS_IDLE_PRIO)
  (H37 : Int.unsigned ($ 0) <= 65535)
  (H38 : Int.unsigned ($ OS_STAT_RDY) <= 255)
  (H36 : isptr Vnull)
  (x0 : val)
  (tcbls_r' : TcbMod.map)
  (x : int32)
  (F2 : Int.unsigned x <= 65535)
  (H23 : Int.unsigned x <= 65535)
  (Fneq_i2_1 : Int.unsigned (x>>ᵢ$ 8) <= 255)
  (Fneq_i2_2 : Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) <= 255)
  (Hmutex_not_avail : x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 <> $ OS_MUTEX_AVAILABLE)
  (Feq_i2_1 : x>>ᵢ$ 8 = Int.modu (x>>ᵢ$ 8) ($ Byte.modulus))
  (Hcur_prio : Int.ltu (x>>ᵢ$ 8) cur_prio = true)
  (ptcb_prio : priority)
  (xm : msg)
  (H12 : isptr x0)
  (v'34 : list vallist)
  (v'36 : list vallist)
  (v'43 : val)
  (v'45 : val)
  (tcbls_sub_l : TcbMod.map)
  (v'52 : TcbMod.map)
  (tcbls_sub_r : TcbMod.map)
  (Htcbjoin_sub_whole : TcbMod.join tcbls_sub_l v'52 tcbls_r')
  (Htcblist_sub_left : TCBList_P x0 v'34 os_rdy_tbl tcbls_sub_l)
  (Htcblist_sub_right : TCBList_P v'45 v'36 os_rdy_tbl tcbls_sub_r)
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
  (H27 : isptr v'45)
  (H24 : isptr (Vptr (ptcb_addr, Int.zero)))
  (H7 : R_ECB_ETbl_P (pevent_addr, Int.zero)
         (V$OS_EVENT_TYPE_MUTEX
          :: Vint32 i0
             :: Vint32 x :: Vptr (ptcb_addr, Int.zero) :: x3 :: v'48 :: nil,
         v'46) tcbls)
  (H3 : ECBList_P v'44 Vnull
         (v'27 ++
          ((V$OS_EVENT_TYPE_MUTEX
            :: Vint32 i0
               :: Vint32 x :: Vptr (ptcb_addr, Int.zero) :: x3 :: v'48 :: nil,
           v'46) :: nil) ++ v'28)
         (v'29 ++
          (DMutex (Vint32 x) (Vptr (ptcb_addr, Int.zero)) :: nil) ++ v'30)
         v'40 tcbls)
  (H8 : EcbMod.joinsig (pevent_addr, Int.zero)
         (absmutexsem (x>>ᵢ$ 8)
            (Some (ptcb_addr, Int.zero, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), wls)
         v'50 v'51)
  (Hget : EcbMod.get v'40 (pevent_addr, Int.zero) =
         Some
           (absmutexsem (x>>ᵢ$ 8)
              (Some (ptcb_addr, Int.zero, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), wls))
  (H26 : RH_ECB_P
          (absmutexsem (x>>ᵢ$ 8)
             (Some (ptcb_addr, Int.zero, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), wls))
  (H6 : RLH_ECBData_P (DMutex (Vint32 x) (Vptr (ptcb_addr, Int.zero)))
         (absmutexsem (x>>ᵢ$ 8)
            (Some (ptcb_addr, Int.zero, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), wls))
  (H_ptcb_not_cur : (ptcb_addr, Int.zero) <> (cur_addr, Int.zero))
  (H32 : isptr xm)
  (H45 : Int.unsigned ptcb_prio <= 255)
  (Htcblist_subr : TCBList_P x0
                    (v'34 ++
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
                                                 Vint32 i2 :: nil) :: v'36)
                    os_rdy_tbl tcbls_r')
  (H17 : RL_TCBblk_P
          (v'45
           :: v'43
              :: x10
                 :: xm
                    :: Vint32 i11
                       :: Vint32 ptcb_stat
                          :: Vint32 ptcb_prio
                             :: Vint32 i8
                                :: Vint32 ptcb_tcby
                                   :: Vint32 ptcb_bitx :: Vint32 i2 :: nil))
  (Hptcb_prio_not_idle : ptcb_prio <> $ OS_IDLE_PRIO)
  (Hptcb_prio_scope_obv : 0 <= Int.unsigned ptcb_prio)
  (Hptcb_prio_scope : Int.unsigned ptcb_prio < 64)
  (Hif_ptcb_is_rdy1 : ptcb_stat = $ OS_STAT_RDY)
  (Hif_ptcb_is_rdy2 : i11 = $ 0)
  (H_ptcb : TcbMod.get tcbls (ptcb_addr, Int.zero) = Some (ptcb_prio, rdy, xm))
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
                                       :: Vint32 ptcb_tcby
                                          :: Vint32 ptcb_bitx
                                             :: Vint32 i2 :: nil) os_rdy_tbl
                 (ptcb_prio, rdy, xm))
  (H50 : R_TCB_Status_P
          (v'45
           :: v'43
              :: x10
                 :: xm
                    :: Vint32 i11
                       :: Vint32 ptcb_stat
                          :: Vint32 ptcb_prio
                             :: Vint32 i8
                                :: Vint32 ptcb_tcby
                                   :: Vint32 ptcb_bitx :: Vint32 i2 :: nil)
          os_rdy_tbl (ptcb_prio, rdy, xm))
  (Hgetcur_subr : TcbMod.get tcbls_r (cur_addr, Int.zero) =
                 Some (cur_prio, rdy, Vnull))
  (Hgetcur : TcbMod.get tcbls (cur_addr, Int.zero) =
            Some (cur_prio, rdy, Vnull))
  (Hcurnode : TCBNode_P
               (x0
                :: v'26
                   :: x12
                      :: Vnull
                         :: V$0
                            :: V$OS_STAT_RDY
                               :: Vint32 cur_prio
                                  :: Vint32 i5
                                     :: Vint32 i4
                                        :: Vint32 i3 :: Vint32 i1 :: nil)
               os_rdy_tbl (cur_prio, rdy, Vnull))
  (Htcbjoin_right : TcbJoin (cur_addr, Int.zero) (cur_prio, rdy, Vnull)
                     tcbls_r' tcbls_r)
  (Hif_false : Int.eq (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) cur_prio = false)
  (Hnocur : Int.eq cur_prio (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = false)
  (H_cur_prio_scope : Int.unsigned cur_prio < 64)
  (Hx_scope1 : Int.unsigned (x>>ᵢ$ 8) < 64)
  (Hif_can_lift1 : ptcb_prio <> x>>ᵢ$ 8)
  (Hif_can_lift2 : Int.ltu cur_prio (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = true)
  (v'31 : val)
  (Hptbl_1 : array_type_vallist_match OS_TCB ∗ ptbl)
  (Hptbl_2 : length ptbl = 64%nat)
  (H15 : RL_RTbl_PrioTbl_P os_rdy_tbl ptbl v'53)
  (H51 : R_PrioTbl_P ptbl tcbls v'53)
  (H_pip_is_hold : val_inj
                    (uop_eval
                       (val_inj
                          (bop_eval
                             (nth_val' (Z.to_nat (Int.unsigned (x>>ᵢ$ 8)))
                                ptbl) (Vptr v'53) OS_TCB ∗ 
                             OS_TCB ∗ oeq)) oppsite) = 
                  Vint32 Int.zero \/
                  val_inj
                    (uop_eval
                       (val_inj
                          (bop_eval
                             (nth_val' (Z.to_nat (Int.unsigned (x>>ᵢ$ 8)))
                                ptbl) (Vptr v'53) OS_TCB ∗ 
                             OS_TCB ∗ oeq)) oppsite) = Vnull)
  (H9 : array_type_vallist_match Int8u os_rdy_tbl)
  (H54 : length os_rdy_tbl = ∘OS_RDY_TBL_SIZE)
  (H52 : rule_type_val_match Int8u v'39 = true)
  (H53 : RL_Tbl_Grp_P os_rdy_tbl v'39)
  (H55 : prio_in_tbl ($ OS_IDLE_PRIO) os_rdy_tbl)
  (Hptcb_tcby : ptcb_tcby = ptcb_prio>>ᵢ$ 3)
  (Hptcb_bitx : ptcb_bitx = $ 1<<ᵢ(ptcb_prio&ᵢ$ 7))
  (Hptcb_tcby_scope : Int.unsigned (ptcb_prio>>ᵢ$ 3) < 8)
  (Hptcb_bitx_scope : Int.unsigned (ptcb_prio>>ᵢ$ 3) < 8)
  (Hif_false : val_inj
                (val_eq
                   (val_inj
                      (and
                         (nth_val' (Z.to_nat (Int.unsigned ptcb_tcby))
                            os_rdy_tbl) (Vint32 ptcb_bitx))) 
                   (V$0)) = Vint32 Int.zero \/
              val_inj
                (val_eq
                   (val_inj
                      (and
                         (nth_val' (Z.to_nat (Int.unsigned ptcb_tcby))
                            os_rdy_tbl) (Vint32 ptcb_bitx))) 
                   (V$0)) = Vnull)
  (Hgetlast: 
     get_last_tcb_ptr v'34 x0 = Some (Vptr (ptcb_addr,Int.zero)))
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
   {{ <||
     mutexpend (Vptr (pevent_addr, Int.zero) :: Vint32 i :: nil)
     ||>  **
     A_dom_lenv
       ((timeout, Int16u)
        :: (pevent, OS_EVENT ∗)
           :: (legal, Int8u)
              :: (pip, Int8u)
                 :: (mprio, Int8u)
                    :: (os_code_defs.isrdy, Int8u)
                       :: (ptcb, OS_TCB ∗)
                          :: (pevent2, OS_EVENT ∗) :: nil) **
     GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64)
       (update_nth_val (Z.to_nat (Int.unsigned (x >>ᵢ $ 8)))
          (update_nth_val (Z.to_nat (Int.unsigned ptcb_prio))
             ptbl (Vptr v'53)) (Vptr (ptcb_addr, Int.zero))) **
     PV v'53 @ Int8u |-> v'31 **
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
       (Vptr (ptcb_addr, Int.zero)) v'34 **
     tcbdllseg v'45 (Vptr (ptcb_addr, Int.zero)) v'42 Vnull v'36 **
     LV ptcb @ OS_TCB ∗ |-> Vptr (ptcb_addr, Int.zero) **
     LV mprio @ Int8u |-> Vint32 (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) **
     LV pip @ Int8u |-> Vint32 (x >>ᵢ $ 8) **
     Astruct (cur_addr, Int.zero) OS_TCB_flag
       (x0
        :: v'26
           :: x12
              :: Vnull
                 :: V$ 0
                    :: V$ OS_STAT_RDY
                       :: Vint32 cur_prio
                          :: Vint32 i5
                             :: Vint32 i4
                                :: Vint32 i3 :: Vint32 i1 :: nil) **
     GV OSTCBList @ OS_TCB ∗ |-> v'33 **
     dllseg v'33 Vnull v'26 (Vptr (cur_addr, Int.zero)) v'35
       OS_TCB_flag (fun vl : vallist => nth_val 1 vl)
       (fun vl : vallist => nth_val 0 vl) **
     GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_addr, Int.zero) **
     AEventData
       (V$ OS_EVENT_TYPE_MUTEX
        :: Vint32 i0
           :: Vint32 x
              :: Vptr (ptcb_addr, Int.zero) :: x3 :: v'48 :: nil)
       (DMutex (Vint32 x) (Vptr (ptcb_addr, Int.zero))) **
     Astruct (pevent_addr, Int.zero) OS_EVENT
       (V$ OS_EVENT_TYPE_MUTEX
        :: Vint32 i0
           :: Vint32 x
              :: Vptr (ptcb_addr, Int.zero) :: x3 :: v'48 :: nil) **
     Aarray v'25 (Tarray Int8u ∘ OS_EVENT_TBL_SIZE) v'46 **
     Aie false **
     Ais nil **
     Acs (true :: nil) **
     Aisr empisr **
     GV OSEventList @ OS_EVENT ∗ |-> v'44 **
     evsllseg v'44 (Vptr (pevent_addr, Int.zero)) v'27 v'29 **
     evsllseg v'48 Vnull v'28 v'30 **
     A_isr_is_prop **
     tcbdllflag v'33
       (v'35 ++
        (x0
         :: v'26
            :: x12
               :: Vnull
                  :: V$ 0
                     :: V$ OS_STAT_RDY
                        :: Vint32 cur_prio
                           :: Vint32 i5
                              :: Vint32 i4
                                 :: Vint32 i3
                                    :: Vint32 i1 :: nil)
        :: v'34 ++
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
                                       Vint32 i2 :: nil) :: v'36) **
     GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
       os_rdy_tbl **
     GV OSRdyGrp @ Int8u |-> v'39 **
     G& OSPlaceHolder @ Int8u == v'53 **
     HECBList v'40 **
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
     AOSTCBFreeList v'23 v'24 **
     AOSTime (Vint32 v'20) **
     HTime v'20 **
     AGVars **
     atoy_inv' **
     LV pevent2 @ OS_EVENT ∗ |-> v'4 **
     LV os_code_defs.isrdy @ Int8u |-> v'2 **
     LV timeout @ Int16u |-> Vint32 i **
     LV pevent @ OS_EVENT ∗ |-> Vptr (pevent_addr, Int.zero)}} 
   OSRdyTbl ′ [ptcb ′ → OSTCBY] &= ∼ ptcb ′ → OSTCBBitX;ₛ
   If(OSRdyTbl ′ [ptcb ′ → OSTCBY] ==ₑ ′ 0)
        {OSRdyGrp ′ &= ∼ ptcb ′ → OSTCBBitY}  ;ₛ
   ptcb ′ → OSTCBPrio =ₑ pip ′;ₛ
   ptcb ′ → OSTCBY =ₑ ptcb ′ → OSTCBPrio ≫ ′ 3;ₛ
   ptcb ′ → OSTCBBitY =ₑ OSMapTbl ′ [ptcb ′ → OSTCBY];ₛ
   ptcb ′ → OSTCBX =ₑ ptcb ′ → OSTCBPrio &ₑ ′ 7;ₛ
   ptcb ′ → OSTCBBitX =ₑ OSMapTbl ′ [ptcb ′ → OSTCBX];ₛ
   OSRdyGrp ′ =ₑ OSRdyGrp ′ |ₑ ptcb ′ → OSTCBBitY;ₛ
   OSRdyTbl ′ [ptcb ′ → OSTCBY] =ₑ
   OSRdyTbl ′ [ptcb ′ → OSTCBY] |ₑ ptcb ′ → OSTCBBitX;ₛ
   OSTCBCur ′ → OSTCBStat =ₑ ′ OS_STAT_MUTEX;ₛ
   OSTCBCur ′ → OSTCBDly =ₑ timeout ′;ₛ
   OS_EventTaskWait (­ pevent ′­);ₛ
   EXIT_CRITICAL;ₛ
   OS_Sched (­);ₛ
   ENTER_CRITICAL;ₛ
   If(OSTCBCur ′ → OSTCBMsg !=ₑ NULL)
        {EXIT_CRITICAL;ₛ
        RETURN ′ OS_NO_ERR}  ;ₛ
   EXIT_CRITICAL;ₛ
   RETURN ′ OS_TIMEOUT {{Afalse}}
.
Proof.
  intros.

  
  assert (0<=Int.unsigned ptcb_tcby <=7) as Hrange_py.
  {
    clear -H17.
    unfolds in H17.
    mytac.
    simpl_vqm.
    clear -H5 H12.
    mauto.
  }

  assert (Hif_ptcb_is_rdy:
           exists v, nth_val' (Z.to_nat (Int.unsigned ptcb_tcby)) os_rdy_tbl = Vint32 v
                     /\ Int.and v ptcb_bitx <> Int.zero /\ Int.unsigned v<= 255).
  {
    (* ** ac: Check array_type_match_get_value. *)
    clear - Hif_false0 H9 H54 H17 Hrange_py.
    unfolds in H17.
    mytac.
    simpl_vqm.
    (* ** ac: Check array_type_match_get_value. *)
    lets Hx: array_type_match_get_value H9 H54.
    eauto.
    destruct Hx.
    exists x0.
    apply nth_val_nth_val'_some_eq in H1;auto.
    split;auto.
    split.
    rewrite H1 in *.
    simpl in Hif_false0.
    remember (Int.eq (x0 &ᵢ($ 1<<ᵢ(x&ᵢ$ 7))) ($ 0)) as X;destruct X;tryfalse.
    simpl in Hif_false0;destruct Hif_false0;tryfalse.
    simpl in Hif_false0.
    clear -HeqX.
    symmetry in HeqX.
    intro.
    rewrite H in HeqX.
    clear -HeqX.
    int auto.
    (* ** ac: Locate array_type_vallist_match_imp_rule_type_val_match. *)
    lets Hx:symbolic_lemmas.array_type_vallist_match_imp_rule_type_val_match H9.
    instantiate (1:= Z.to_nat (Int.unsigned (x>>ᵢ$ 3))).
    rewrite H54.
    apply z_le_7_imp_n;auto.
    rewrite H1 in Hx.
    simpl in Hx.
    remember (Int.unsigned x0 <=? Byte.max_unsigned) as X;destruct X;tryfalse.
    eapply Zle_bool_imp_le;eauto.
  }
  
  clear Hif_false0.
  
  hoare forward.
  (* pure_auto. *)
  struct_type_match_solver.
  rewrite H54.
  simpl.
  omega.
  Import symbolic_lemmas.
  apply array_type_vallist_match_imp_rule_type_val_match;auto.
  rewrite H54.
  apply z_le_7_imp_n;destruct Hrange_py;auto.
  (* pure_auto. *)
  struct_type_match_solver.
  (* pure_auto. *)
  destruct Hif_ptcb_is_rdy.
  destruct H57.
  rewrite H57.
  simpl;auto.
  (* pure_auto. *)
  (* pure_auto. *)
  struct_type_match_solver.
  subst.
  clear -Hrange_py.
  simpl.
  omega.
  rewrite H54.
  subst.
  clear -Hrange_py;simpl;omega.

  
  destruct Hif_ptcb_is_rdy as (v0 & Hif_ptcb_rdy1 & Hif_ptcb_rdy2&Hrangev).
  subst.
  rewrite Hif_ptcb_rdy1 in *.
  Open Scope Z_scope.
  assert (exists x,nth_val' (Z.to_nat (Int.unsigned (ptcb_prio>>ᵢ$ 3)))
                            (update_nth_val (Z.to_nat (Int.unsigned (ptcb_prio>>ᵢ$ 3))) os_rdy_tbl
                                            (Vint32 (v0 &ᵢInt.not ($ 1<<ᵢ(ptcb_prio&ᵢ$ 7))))) = Vint32 x /\ Int.unsigned x <= 255).
  {
    eapply array_int8u_nth_lt_len;eauto.
  
    eapply array_type_vallist_match_int8u_update_hold;eauto.
    destruct Hrange_py;auto.
    clear -H17.
    unfolds in H17.
    mytac.
    simpl_vqm.
    clear -H5 H12.
    mauto.

    rewrite update_nth_val_len_eq.
    rewrite H54.
    apply z_le_7_imp_n;destruct Hrange_py;auto.
  }
  
  clear Hptcb_bitx_scope.
  lzh_hoare_if.
  (* pure_auto. *)
  rewrite update_nth_val_len_eq.
  rewrite H54.
  simpl;clear -Hrange_py;omega.

  Set Printing Depth 300.
  
  (* ** ac: Check array_type_vallist_match_imp_rule_type_val_match. *)
  assert (Htmp: rule_type_val_match Int8u
                  (nth_val' (Z.to_nat (Int.unsigned (ptcb_prio >>ᵢ $ 3)))
                            (update_nth_val (Z.to_nat (Int.unsigned (ptcb_prio >>ᵢ $ 3)))
                                            os_rdy_tbl (Vint32 (v0&ᵢInt.not ($ 1<<ᵢ(ptcb_prio&ᵢ$ 7)))))) = true).
  {
    apply array_type_vallist_match_imp_rule_type_val_match;auto.
    rewrite update_nth_val_len_eq.
    rewrite H54.
    apply z_le_7_imp_n;destruct Hrange_py;auto.
    apply array_type_vallist_match_int8u_update_hold_255;auto.
    omega.
  }
  {
    clear - Htmp.
    unfold rule_type_val_match in Htmp.
    auto.
  }

  {
    simpl.
    mytac.
    rewrite H56.
    simpl;auto.
    destruct (Int.eq x ($ 0));auto.
    pure_auto.
    pure_auto.
  }
  
  hoare forward.
  (* pure_auto. *)
  struct_type_match_solver.
  (* pure_auto. *)
  clear -H52.
  destruct v'39;simpl in H52;tryfalse.
  simpl;auto.
  pure_auto.
  
  rename i2 into ptcb_bity.
  rename Hif_true into Hif_rdytbl_tcby_eq_zero.
  simpl in Hif_rdytbl_tcby_eq_zero.

  hoare forward.
  rtmatch_solve.

  assert (Int.unsigned (x>>ᵢ$ 8) <= 255
          /\
          Int.unsigned ((x>>ᵢ$ 8)>>ᵢ$ 3) <= 255
          /\
          Int.unsigned ((x>>ᵢ$ 8) &ᵢ $ 7) <= 255) as Hauxrange.
  {
    clear -H26.
    unfolds in H26.
    mytac.
    swallow.
    omega.
    
    apply aux_trivial in H2.
    omega.
 
    apply and7_lt8 in H2;omega.
  }
  
  destruct Hauxrange as (Hauxrange1&Hauxrange2&Hauxrange3).
  hoare forward.
  (* pure_auto. *)
  struct_type_match_solver.
  (* { *)
  (*   rewrite postintlemma4. *)
  (*   (* pure_auto. *) *)
  (* } *)
  
  unfold AOSMapTbl.
  hoare forward.
  (* pure_auto. *)
  
  struct_type_match_solver.

  {
    rewrite postintlemma4.
    unfold val_inj.
    pure_auto.
  }
    
  {
    eapply aux_trivial.
    clear -H26.
    unfolds in H26.
    mytac.
  }

  {
    eapply aux_trivial.
    clear -H26.
    unfolds in H26.
    mytac.
  }

  {
    eapply array_type_vallist_match_imp_rule_type_val_match;eauto.
    2:simpl;splits;go.
    simpl.
    apply z_le_7_imp_n.
    clear -H26.
    unfolds in H26.
    mytac.
    apply aux_trivial in H2.
    clear -H2;int auto.
  }
  assert (Int.ltu ($ 3) Int.iwordsize = true).
  {
    clear;int auto.
  }
  
  rewrite H57.
  
  assert (exists vx, nth_val' (Z.to_nat
                         (Int.unsigned ((x>>ᵢ$ 8)>>ᵢ$ 3)))
                              OSMapVallist = Vint32 vx /\ Int.unsigned vx <=128).
  {
    (* ** ac: Locate osmapvallist_prop. *)
    Require Import OSEventTaskRdyPure.
    Open Scope code_scope.
    eapply osmapvallist_prop;eauto.
    clear -H26.
    unfolds in H26.
    mytac.
    apply aux_trivial in H2;omega.
  }

  idtac.
  destruct H58.
  destruct H58.
  rewrite H58.
  hoare forward.
  (* pure_auto. *)
  simpl val_inj.
  struct_type_match_solver.
  pure_auto.
 
  hoare forward.
  (* pure_auto. *)
  struct_type_match_solver.
  
  eapply and7_lt8.
  clear -H26.
  unfolds in H26.
  mytac.

  clear -H26.
  unfolds in H26.
  mytac.
  clear -H2.
  apply and7_lt8;auto.

  eapply array_type_vallist_match_imp_rule_type_val_match;eauto.
  simpl.
  apply z_le_7_imp_n.
  assert (Int.unsigned ((x>>ᵢ$ 8)&ᵢ$ 7) < 8).
  {
    eapply and7_lt8.
    clear -H26.
    unfolds in H26.
    mytac.
  }
  auto.
  omega.

  simpl;splits;go.
  
  assert (exists vx, nth_val' (Z.to_nat
                                 (Int.unsigned ((x>>ᵢ$ 8)&ᵢ$ 7)))
                              OSMapVallist = Vint32 vx /\ Int.unsigned vx <=128).
  {
    eapply osmapvallist_prop;eauto.
    clear -H26.
    unfolds in H26.
    mytac.
    clear -H2.
    remember (x>>ᵢ$ 8) as Y.
    clear HeqY.
    mauto.
  }

  destruct H60.
  destruct H60.
  rewrite H60.
  hoare forward.
  simpl in H54;destruct v'39;tryfalse;simpl;auto.
  rtmatch_solve.
  eapply le255_and_le255.
  clear -H52.
  unfolds in H52.
  remember (Int.unsigned i2 <=? Byte.max_unsigned) as X;destruct X;tryfalse.
  eapply Zle_bool_imp_le;eauto.
  (* pure_auto. *)
  struct_type_match_solver.
  destruct v'39;simpl in H54;tryfalse.
  simpl.
  pure_auto.

  assert (Int.ltu ($ 3) Int.iwordsize = true) as Hpred1.
  {
    clear;int auto.
  }
  rewrite Hpred1 in *.
  simpl val_inj in *.

  assert (exists xx, nth_val' (Z.to_nat (Int.unsigned ((x>>ᵢ$ 8)>>ᵢ$ 3)))
                              (update_nth_val (Z.to_nat (Int.unsigned  (ptcb_prio>>ᵢ$ 3))) os_rdy_tbl
                                              (Vint32 (v0&ᵢInt.not ($ 1<<ᵢ(ptcb_prio&ᵢ$ 7))))) = Vint32 xx /\ Int.unsigned xx <= 255) as Hfx1.
  {
    eapply array_int8u_nth_lt_len;eauto.
    eapply array_type_vallist_match_int8u_update_hold;eauto.
    destruct Hrange_py;auto.
    clear -H17.
    unfolds in H17.
    mytac.
    simpl_vqm.
    clear -H5 H12.
    mauto.
    rewrite update_nth_val_len_eq.
    rewrite H54.
    apply z_le_7_imp_n;destruct Hrange_py;auto.
    clear -H26.
    unfolds in H26.
    mytac.
    apply aux_trivial in H2;omega.
  }
    
  hoare forward.
  (* pure_auto. *)
  struct_type_match_solver.
  clear -H26.
  unfolds in H26.
  mytac.
  apply aux_trivial in H2;auto.
  rewrite update_nth_val_len_eq.
  rewrite H54.
  simpl.
  clear -H26.
  unfolds in H26.
  mytac.
  apply aux_trivial in H2;auto.
  eapply array_type_vallist_match_imp_rule_type_val_match;eauto.
  simpl.
  rewrite update_nth_val_len_eq.
  rewrite H54.
  apply z_le_7_imp_n.
  assert (Int.unsigned ((x>>ᵢ$ 8)>>ᵢ$ 3) < 8).
  eapply aux_trivial.
  clear -H26.
  unfolds in H26.
  mytac.
  auto.
  omega.
  eapply array_type_vallist_match_int8u_update_hold;eauto.
  destruct Hrange_py;omega.
  clear -H17.
  unfolds in H17.
  mytac.
  simpl_vqm.
  clear -H12.
  mauto.
  (* pure_auto. *)
  
  struct_type_match_solver.
  destruct Hfx1 as (fx&Hfx1'&Hfx'').
  rewrite Hfx1'.
  simpl;auto.
  (* pure_auto. *)
  (* pure_auto. *)
  struct_type_match_solver.
  simpl.
  eapply aux_trivial.
  clear -H26.
  unfolds in H26.
  mytac.
  auto.
  rewrite update_nth_val_len_eq.
  rewrite H54.
  simpl.
  eapply aux_trivial.
  clear -H26.
  unfolds in H26.
  mytac.

  hoare forward.
  hoare forward.
  rtmatch_solve.
  auto.
  transform_pre a_isr_is_prop_split ltac:(sep cancel Aisr;
                                          sep cancel Ais;
                                          sep cancel A_isr_is_prop).
  hoare_split_pure_all.
  (* ** os_eventtaskwait (pevent) *)
  unfold AEventData.
  hoare_split_pure_all.
  clear H63 H64 H65.
  Open Scope list_scope.
  assert (  RL_TCBblk_P
     (v'45
      :: v'43
         :: x10
            :: xm
               :: V$0
                  :: V$OS_STAT_MUTEX
                     :: Vint32 (x>>ᵢ$ 8)
                        :: Vint32 ((x>>ᵢ$ 8)&ᵢ$ 7)
                           :: Vint32 ((x>>ᵢ$ 8)>>ᵢ$ 3)
                           :: Vint32 x2 :: Vint32 x1 :: nil)) as Hnewrltcbblkp.
  {
    unfolds.
    exists (x>>ᵢ$ 8);do 5 eexists;splits;eauto.
    unfolds;simpl;auto.
    unfolds;simpl;auto.
    unfolds;simpl;auto.
    unfolds;simpl;auto.
    unfolds;simpl;auto.
    clear -H26.
    unfolds in H26.
    mytac.
    split.
    clear; int auto.
    auto.
    splits;auto.
    symmetry.
    eapply math_mapval_core_prop;eauto.
  
    clear -H26.
    unfolds in H26.
    mytac.
    clear -H2.
    apply and7_lt8;auto.
    symmetry.
    eapply math_mapval_core_prop;eauto.
    clear -H26.
    unfolds in H26.
    mytac.
    clear -H2.
    apply aux_trivial;auto.
    eexists;split.
    unfolds;simpl;eauto.
    intros;tryfalse.
  }
  
  hoare forward.
  {
    unfold node.
    instantiate (2:=(DMutex (Vint32 x) (Vptr (ptcb_addr, Int.zero)))).
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
    sep cancel 16%nat 1%nat.
    sep cancel Aarray.
    sep cancel 5%nat 1%nat.
    instantiate (2:=mutexpend (Vptr (pevent_addr, Int.zero) :: Vint32 i :: nil)).
    sep cancel 1%nat 1%nat.
    sep cancel Aie.
    sep cancel Ais.
    sep cancel Acs.
    sep cancel Aisr.
    exact_s.
    unfolds; auto.
    unfolds; auto.
    unfolds; auto.
    split.
    destruct v'39;
      simpl in H52;tryfalse.
    simpl.
    rewrite e.
    (* ** ac: Locate event_wait_rl_tbl_grp. *)
    eapply OSTimeDlyPure.event_wait_rl_tbl_grp;eauto.
    eapply array_type_vallist_match_int8u_update_hold;eauto.
    clear -H17.
    unfolds in H17.
    mytac.
    simpl_vqm.
    clear -H12.
    mauto.
    eapply OSTimeDlyPure.event_wait_rl_tbl_grp';eauto.
    rewrite len_lt_update_get_eq in Hif_rdytbl_tcby_eq_zero.
    clear -Hif_rdytbl_tcby_eq_zero.
    assert (forall x y,Vint32 x = Vint32 y -> x = y).
    {
      intros.
      inverts H;auto.
    }
    apply H in Hif_rdytbl_tcby_eq_zero.
    rewrite Hif_rdytbl_tcby_eq_zero.
    clear;int auto.
    rewrite H54.
    simpl;omega.
    
    eapply idle_in_rtbl_hold';eauto.
    clear -H26.
    unfolds in H26.
    mytac.
    apply aux_trivial in H2;omega.
    rewrite update_nth_val_len_eq.
    rewrite H54.
    auto.
    eapply array_type_vallist_match_int8u_update_hold;eauto.
    clear -H17.
    unfolds in H17.
    mytac.
    simpl_vqm.
    clear -H12.
    mauto.
    
    clear -H55 H17  Hptcb_prio_not_idle Hif_ptcb_rdy1.
    unfolds in H17.
    mytac.
    simpl_vqm.
    eapply prio_neq_in_tbl_rev;eauto.
    unfold OS_IDLE_PRIO.
    unfold OS_LOWEST_PRIO.
    clear.
    int auto.
    eapply nth_val'2nth_val;eauto.
    destruct v'39;simpl in H54;simpl;auto.
    rtmatch_solve.
    apply int_unsigned_or_prop;auto.
    apply Zle_bool_imp_le.
    apply unsigned_int_and_not_range;auto.
    clear -H52.
    apply Zle_bool_imp_le.
    unfolds in H52.
    remember ( Int.unsigned i2 <=? Byte.max_unsigned) as X.
    destruct X;tryfalse.
    auto.
    split.
    4:eauto.
    7:go.
    6:auto.
    5:auto.
    4:unfolds;simpl;auto.
    3:go.

    eapply array_type_vallist_match_int8u_update_hold';eauto.
    rewrite update_nth_val_len_eq.
    rewrite H54;auto.
    eapply array_type_vallist_match_int8u_update_hold;eauto.
    clear -H17.
    unfolds in H17.
    mytac.
    simpl_vqm.
    clear -H12.
    mauto.
    rewrite update_nth_val_len_eq.
    rewrite H54.
    auto.
    clear -H26.
    unfolds in H26.
    mytac.
    apply aux_trivial in H2;omega.
    eapply array_type_vallist_match_int8u_update_hold;eauto.
    clear -H17.
    unfolds in H17.
    mytac.
    simpl_vqm.
    clear -H12.
    mauto.
    rewrite update_nth_val_len_eq.
    rewrite update_nth_val_len_eq.
    rewrite H54.
    auto.
  }
  {
    split.
    auto.
    unfold V_OSTCBPrio.
    exists cur_prio.
    split; auto.
    rewrite Int.eq_false; auto.
  }    
  2:go.
  unfolds.
  clear - Hcurnode.
  unfolds in Hcurnode.
  mytac.
  simpl_vqm.
  unfolds in H1.
  mytac.
  simpl_vqm.
  do 6 eexists;splits.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  split;auto.
  splits;auto.
  eexists.
  split.
  unfolds;simpl;auto.
  intros;tryfalse.

  intros.
  sep auto.
  intros.
  sep auto.
  (* ** exit_critical *)
  hoare_ex_intro.
  unfold OS_EventTaskWaitPost.
  unfold OS_EventTaskWaitPost'.
  unfold getasrt.
  hoare_split_pure_all.
  inverts H63.
  unfold V_OSTCBY,V_OSTCBBitX,V_OSTCBBitY,V_OSEventGrp in H65.
  simpl in H65.
  mytac_H.
  inverts H64.
  inverts H65; inverts H66; inverts H68; inverts H67; inverts H73.

  assert (Hos_grp_scope: exists os_grp, v'39 = Vint32 os_grp /\
                         Int.unsigned os_grp <= Byte.max_unsigned).
  {
    clear -H52.
    destruct v'39;tryfalse.
    eexists;simpl in H52;split;auto.
    apply Zle_bool_imp_le.
    destruct (Int.unsigned i <=? Byte.max_unsigned);auto;tryfalse.
  }
  
  destruct Hos_grp_scope as (os_grp & Htmp & Hos_grp_scope).
  inverts Htmp.
  clear H63.
  unfold AEventNode.
  unfold AOSEvent.
  unfold AOSEventTbl.
  unfold AEventData.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  unfold AOSRdyGrp.
  unfold node.
  hoare_split_pure_all.
  
  rename H69 into Hfn.
  clear H80 H81 H82.
  mytac_H.
  inverts H63.
  inverts H71.
  unfolds in H67;simpl in H67;inverts H67.
  subst.


(**************************** simplify begin ****************************)
 
  transform_pre add_a_isr_is_prop ltac:(sep cancel Aisr;
                                        sep cancel Ais).

(****************  simplify end *************************************)
  (* ** Untile now, preparation must have done *)
  Focus 1.
  hoare abscsq.
  auto.
  eapply absinfer_mutex_pend_lift_is_rdy_block.
  instantiate (1:= (ptcb_addr, Int.zero)).
  auto.
  auto.
  go.
  eauto.
  eauto.
  eauto.
  clear -Hif_can_lift1.
  apply Int.eq_false;auto.
  clear -Hcur_prio Hif_can_lift2.
  auto.
  clear -Hcur_prio Hif_can_lift2.
  auto.

  inverts H70.
  hoare forward prim.
  (* cancel AECBList *)
  unfold AECBList.
  sep pauto.
  
  eapply evsllseg_compose.
  4: sep cancel evsllseg.
  4: sep cancel evsllseg.
  instantiate (1:=
                 (V$OS_EVENT_TYPE_MUTEX
                   :: Vint32 (Int.or v'67 v'64)
                   :: Vint32 x :: Vptr (ptcb_addr, Int.zero) :: x3 :: v'48 :: nil)).
  unfolds; simpl; eauto.
  eauto.
  instantiate (1:=DMutex (Vint32 x) (Vptr (ptcb_addr, Int.zero))).
  eauto.
  lzh_unfold_event.
  sep pauto.
  sep cancel Astruct.
  sep cancel Aarray.

  (* cancel AOSTCBList *)
  Focus 1.
  sep lift 3%nat.
  unfold AOSTCBList.
  sep pauto.
  unfold tcbdllseg.

  unfold tcbdllseg in H63.
  sep cancel 13%nat 1%nat.

  instantiate (10:=
                 (x0
                    :: v'26
                    :: Vptr (v'46, Int.zero)
                    :: Vnull
                    :: Vint32 i
                    :: V$ OS_STAT_MUTEX
                    :: Vint32 cur_prio
                    :: Vint32 i5
                    :: Vint32 v'62
                    :: Vint32 v'63
                    :: 
                    Vint32 v'64 :: nil)).
  instantiate (8:= v'34 ++ ( (v'45
              :: v'43
                 :: x10
                    :: xm
                       :: V$0
                          :: V$OS_STAT_RDY
                             :: Vint32 (x>>ᵢ$ 8)
                                :: Vint32 ((x>>ᵢ$ 8) &ᵢ$ 7)
                                   :: Vint32 ((x>>ᵢ$ 8)>>ᵢ$ 3)
                                   :: Vint32 x2 :: Vint32 x1 :: nil) :: v'36)).

  simpl dllseg.
  unfold node.
  sep pauto.
  unfold tcbdllseg in *.
  sep cancel 1%nat 1%nat.

  eapply dllseg_compose.
  sep cancel 8%nat 1%nat.
  simpl dllseg.
  unfold node.
  sep pauto.
  sep cancel Astruct.
  sep cancel dllseg.

  (* 2:pure_auto. *)
  2:go;omega.
  2:unfolds;simpl;auto.
 
  (* sep cancel AOSMapTbl *)
  unfold AOSMapTbl.
  sep cancel 12%nat 1%nat.

  (* sep cancel AOSTCBPrioTbl *)
  unfold AOSTCBPrioTbl.
  sep pauto.
  sep cancel 9%nat 2%nat.
  sep pauto.

  (* OSRdyGrp need update ?  Yes! *)
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  unfold AOSRdyGrp.
  sep pauto.

  {
    (* ** ac: SearchAbout tcbdllflag. *)
    (* ** ac: Check tcbdllflag_hold. *)
    eapply tcbdllflag_hold.
    Focus 2.
    sep cancel 5%nat 1%nat.
    exact_s.

    idtac.
    (* ** ac: Check tcbdllflag_hold_node2. *)

    eapply tcbdllflag_hold_node2'.
    unfolds.
    swallow; go.
    unfolds; swallow; go.
  }  
  
  Focus 3.
  split.
  eapply array_type_vallist_match_hold;eauto.
  eapply array_type_vallist_match_hold;eauto.
  rewrite Hptbl_2.
  clear -H17.
  unfolds in H17.
  mytac.
  simpl_vqm.
  mauto.
  rewrite update_nth_val_len_eq.
  rewrite Hptbl_2.
  clear -Hnewrltcbblkp.
  unfolds in Hnewrltcbblkp.
  mytac.
  simpl_vqm.
  clear- H12.
  remember (x>>ᵢ$ 8) as X.
  clear HeqX.
  mauto.
  rewrite update_nth_val_len_eq.
  rewrite update_nth_val_len_eq.
  auto.
  (** cancel R_PrioTbl_P *)


  eapply R_PrioTbl_Pend_lift;eauto.
  clear -H_pip_is_hold.
  remember ((nth_val' (Z.to_nat (Int.unsigned (x>>ᵢ$ 8)))
                                ptbl)) as X.
  destruct v'53;destruct X;simpl in *;destruct H_pip_is_hold;tryfalse.
  destruct a.
  destruct (peq b0 b).
  remember (Int.eq i0 i) as Y.
  destruct Y;tryfalse.
  lets Hx: Int.eq_spec i0 i.
  rewrite <- HeqY in Hx.
  subst;auto.
  false.
  destruct a.
  destruct (peq b0 b);destruct (Int.eq i0 i);tryfalse.

  rewrite H77.
  simpl.
  eapply OSTimeDlyPure.rtbl_remove_RL_RTbl_PrioTbl_P_hold with (prio := cur_prio);eauto.
  clear -Hcurnode.
  unfolds in Hcurnode.
  mytac_H.
  unfolds in H1.
  mytac_H.
  simpl_vqm.
  auto.
  clear -Hcurnode.
  unfolds in Hcurnode.
  mytac_H.
  unfolds in H1.
  mytac_H.
  simpl_vqm.
  auto.
  clear -Hcurnode.
  unfolds in Hcurnode.
  mytac_H.
  unfolds in H1.
  mytac_H.
  simpl_vqm.
  auto.
  rewrite H77 in Hfn.
  auto.

  eapply RL_RTbl_PrioTbl_P_set;eauto.
  rewrite update_nth_val_len_eq;auto.
  rewrite update_nth_val_len_eq;auto.
  
  unfolds in H51.
  clear -H_ptcb H51.
  mytac.
  apply H0 in H_ptcb.
  destruct H_ptcb;auto.
  
  eapply RL_RTbl_PrioTbl_P_set_vhold;eauto.
  rewrite H54.
  clear -H17.
  unfolds in H17.
  mytac.
  unfolds in H1.
  mytac.
  simpl_vqm.
  unfold OS_RDY_TBL_SIZE.
  mauto.
  rewrite H77.

  instantiate (1:=
                 TcbMod.set
                   (TcbMod.set tcbls_r (v'37, Int.zero) (cur_prio, wait (os_stat_mutexsem (v'46, Int.zero)) i, Vnull))
                   (ptcb_addr, Int.zero)
                   ((x>>ᵢ$ 8),rdy, xm)).
  simpl.
  do 4 eexists;splits;auto;eauto.
  unfolds;simpl;auto.
  instantiate (1:=TcbMod.set tcbls_r' (ptcb_addr, Int.zero) (x>>ᵢ$ 8, rdy, xm)).
  instantiate (1:=(cur_prio, wait (os_stat_mutexsem (v'46, Int.zero)) i, Vnull)).

  eapply join_mutexpend';eauto.

  lets Hx: math_mapval_core_prop H60.
  clear -H26.
  unfolds in H26.
  mytac.
  remember (x>>ᵢ$ 8) as X.
  clear HeqX.
  mauto.
  subst x2.


  simpl.
  mytac.
  swallow.
  unfolds;simpl;auto.
  unfolds;simpl;auto.

  clear -Hcurnode.
  unfolds in Hcurnode.
  unfold RL_TCBblk_P in *.
  mytac_H.
  simpl_vqm.
  do 6 eexists.
  splits.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  auto.
  splits; auto.
  eexists; split.
  go.
  intros; tryfalse.
  
  eapply R_TCB_Status_mutexpend_lift with (prio_lift:=  x>>ᵢ$ 8) (ptcb_prio:=ptcb_prio);eauto.
  clear -H51 Hgetcur H_ptcb  H_ptcb_not_cur.
  unfolds in H51.
  mytac.
  
(*  unfolds in H1.
  lets Hx:H1 Hgetcur H_ptcb.
  auto.
  auto.
  clear -H26.
  unfolds in H26.
  mytac.
  auto.
 *)

  simpl val_inj.
  eapply TCBList_P_tcb_block_hold' with
    (tcs:=TcbMod.sig (v'37,Int.zero) (cur_prio,rdy,Vnull))
    (tcs':=TcbMod.merge (TcbMod.sig (v'37,Int.zero) (cur_prio,rdy,Vnull))
                        (TcbMod.set tcbls_r' (ptcb_addr, Int.zero) (x>>ᵢ$ 8, rdy, xm))).
  instantiate (1:=cur_prio).
  clear -Hcurnode.
  unfolds in Hcurnode.
  mytac_H.
  simpl_vqm.
  unfolds in H1.
  mytac_H.
  simpl_vqm.
  auto.
  apply TcbMod.get_sig_some.

  apply TcbMod.join_comm.
  eapply join_prop_mutexpend''' with (m:=(v'37,Int.zero));eauto.
  unfold TcbJoin in *.
  eauto.
  
  rewrite H77 in Hfn.
  simpl in Hfn.
  apply math_mapval_core_prop in H60.
  subst x2.
  apply math_mapval_core_prop in H58.
  subst x1.
 
  eapply tcbls_l_mutexpend;eauto.

  clear -H_pip_is_hold.
  remember (nth_val' (Z.to_nat (Int.unsigned (x>>ᵢ$ 8))) ptbl) as X.
  clear HeqX.
  destruct v'53;destruct X;simpl in *;destruct H_pip_is_hold;tryfalse.
  destruct a.
  destruct (peq b0 b).
  remember (Int.eq i0 i) as Y.
  destruct Y;tryfalse.
  lets Hx: Int.eq_spec i0 i.
  rewrite <- HeqY in Hx.
  subst;auto.
  false.
  destruct a.
  destruct (peq b0 b);destruct (Int.eq i0 i);tryfalse.
  
  instantiate (1:= TcbMod.merge tcbls_l (TcbMod.sig (v'37,Int.zero) (cur_prio, rdy, Vnull) )).

  eapply join_prop_mutexpend'''';eauto.

  clear -H26.
  unfolds in H26.
  mytac.
  remember (x>>ᵢ$ 8) as X.
  clear HeqX.
  mauto.
  clear -H26.
  unfolds in H26.
  mytac.
  remember (x>>ᵢ$ 8) as X.
  clear HeqX.
  mauto.
  clear -Hcurnode.
  unfolds in Hcurnode.
  mytac_H.
  simpl_vqm.
  unfolds in H1.
  mytac_H.
  simpl_vqm.
  auto.
  clear -Hcurnode.
  unfolds in Hcurnode.
  mytac_H.
  simpl_vqm.
  unfolds in H1.
  mytac_H.
  simpl_vqm.
  auto.

  eapply prio_neq_cur_set;eauto.
  eapply TcbMod_join_impl_prio_neq_cur_r with (tcbls:= tcbls_r);eauto.
  eapply TcbMod_join_impl_prio_neq_cur_r with (tcbls:= tcbls);eauto.
  eapply R_PrioTbl_P_impl_prio_neq_cur;eauto.
  clear -Hcurnode.
  unfolds in Hcurnode.
  mytac_H.
  simpl_vqm.
  unfolds in H1.
  mytac_H.
  simpl_vqm.
  auto.

  unfold TcbJoin in *.
  eauto.
  
  rewrite H77 in Hfn.
  simpl in Hfn.
  auto.
  (*----*)
  instantiate (1:=tcbls_l).
  eapply TCBList_P_tcb_block_hold' with (tcs':=tcbls) (tcs:=tcbls_r) (prio:=cur_prio);eauto.
  clear -Hcurnode.
  unfolds in Hcurnode.
  mytac_H.
  unfolds in H1.
  mytac_H.
  simpl_vqm.
  auto.
 
  lets Hx: math_mapval_core_prop H60.
  clear -H26.
  unfolds in H26.
  mytac.
  remember (x>>ᵢ$ 8) as X.
  clear HeqX.
  mauto.
  subst x2.
  rewrite H77.
  eapply TCBList_P_rtbl_add_simpl_version;eauto.
  clear -H26.
  unfolds in H26.
  mytac.
  auto.
  clear - H2;int auto.

  apply nth_val'2nth_val;auto.

  eapply vhold_not_get' with (tcbls_r:=tcbls_r);eauto.
  clear -H_pip_is_hold.
  remember (nth_val' (Z.to_nat (Int.unsigned (x>>ᵢ$ 8))) ptbl) as X.
  clear HeqX.
  destruct v'53;destruct X;simpl in *;destruct H_pip_is_hold;tryfalse.
  destruct a.
  destruct (peq b0 b).
  remember (Int.eq i0 i) as Y.
  destruct Y;tryfalse.
  lets Hx: Int.eq_spec i0 i.
  rewrite <- HeqY in Hx.
  subst;auto.
  false.
  destruct a.
  destruct (peq b0 b);destruct (Int.eq i0 i);tryfalse.

  eapply TCBList_P_tcb_block_hold' with (tcs:=tcbls_r) (tcs':=tcbls) ;eauto.
  eapply tcbjoin_get_get_my;eauto.
  eapply TcbMod_join_impl_prio_neq_cur_l with (tcbls:= tcbls);eauto.
  eapply R_PrioTbl_P_impl_prio_neq_cur;eauto.
  apply nth_val'2nth_val;auto.
  clear -Hcurnode.
  unfolds in Hcurnode.
  mytac_H.
  simpl_vqm.
  unfolds in H1.
  mytac_H.
  simpl_vqm.
  auto.
  clear -Hcurnode.
  unfolds in Hcurnode.
  mytac_H.
  simpl_vqm.
  unfolds in H1.
  mytac_H.
  simpl_vqm.
  auto.
  eapply TcbMod_join_impl_prio_neq_cur_l with (tcbls:= tcbls);eauto.
  eapply R_PrioTbl_P_impl_prio_neq_cur;eauto.
  clear -Hcurnode.
  unfolds in Hcurnode.
  mytac_H.
  unfolds in H1.
  mytac_H.
  simpl_vqm.
  auto.
  eapply TcbMod.join_set_r;eauto.
  eapply TcbMod.join_set_r;eauto.
  unfolds.
  eexists.
  eapply tcbjoin_get_a_my;eauto.
  eexists.
  rewrite TcbMod.set_a_get_a';eauto.
  eapply tcbjoin_get_get_my;eauto.
  apply tidspec.neq_beq_false;auto.

  instantiate (1:=  Vint32 (Int.or v'67 v'64)).
  2:unfolds;simpl;auto.
  2:auto.
  clear -Hcurnode H83 H18 H13.
  eapply event_wait_rl_tbl_grp;eauto.
  unfolds in Hcurnode.
  mytac_H.
  eauto.
  apply nth_val_nth_val'_some_eq;auto.
  
  assert (array_type_vallist_match Int8u
                                   (update_nth_val ∘(Int.unsigned v'62) v'55 (val_inj (or (nth_val' ∘(Int.unsigned v'62) v'55) (Vint32 v'64))))).
  {
    eapply array_type_vallist_match_int8u_update_hold';eauto.
    clear -Hcurnode.
    unfolds in Hcurnode.
    mytac_H.
    simpl_vqm.
    unfolds in H1.
    mytac_H.
    simpl_vqm.
    mauto.
    clear -Hcurnode.
    unfolds in Hcurnode.
    mytac_H.
    simpl_vqm.
    unfolds in H1.
    mytac_H.
    simpl_vqm.
    mauto.
  }
  
  apply nth_val_nth_val'_some_eq in H83.
  rewrite H83 in H70;simpl in H70;auto.

  eapply ecblist_p_mutexpend_changeprio;eauto.
  rewrite TcbMod.set_a_get_a'.
  eauto.
  eapply tidspec.neq_beq_false;auto.


  eapply ecblist_p_mutexpend;eauto.
  clear -H63.
  sep lift 18%nat in H63.

  eapply evsllseg_aux;eauto.
  unfolds.
  rewrite TcbMod.set_a_get_a'.
  rewrite TcbMod.set_a_get_a.
  do 3 eexists;eauto.
  apply tidspec.eq_beq_true;auto.
  apply tidspec.neq_beq_false;auto.
  
 
  eapply RH_TCBList_ECBList_P_changeprio;eauto.
  rewrite TcbMod.set_a_get_a';eauto.
  apply tidspec.neq_beq_false;auto.
  eapply RH_TCBList_ECBList_P_high_block_hold_mutex;eauto.
  go.

  hoare forward.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aisr.
  sep cancel 1%nat 1%nat.
  sep cancel 1%nat 1%nat.
  exact_s.

  unfold isflag.
  auto.
  
  go.
  intros.
  sep auto.
  sep cancel 1%nat 1%nat.
  sep auto.

  intros.
  sep auto.
  sep cancel 1%nat 1%nat.
  sep auto.
  
  clear.
  hoare unfold.
  inverts H.
  hoare forward prim.
  hoare unfold.
  hoare forward.
  go.

  pure_auto.
  pure_auto.
    
  instantiate (1:=Afalse).
  hoare_split_pure_all.
  hoare abscsq.
  auto.
  unfolds in H13;destruct H13.
  subst x7.
  simpl in H2;destructs H2.
  destruct n.
  int auto.
  destruct e. 
    
  simpl in H8.
  mytac_H.
  destruct x4.
  destruct p.
  assert (m = Vptr x0).
  {
    clear -t.
    unfolds in t.
    mytac.
    simpl_vqm.
    auto.
  }
  subst m.
  eapply mutexpend_block_get_step with (m:=Vptr x0);eauto.
  go.
  eapply TcbMod.join_get_r;eauto.
  inverts e.
  eapply tcbmod_joinsig_get;eauto.
  pure_auto.
  
  hoare forward prim.
  unfold AOSTCBList.
  unfold tcbdllseg.
  simpl dllseg at 2.
  unfold node.
  sep pauto.
  eauto.
  eauto.
  auto.
  go.
  go.


  hoare forward.

  hoare forward prim.
  hoare_split_pure_all.
  assert (x7 = Vnull).
  {
    unfolds in H13.
    clear -H2 H13.
    destruct H13.
    auto.
    destruct H.
    subst;destruct x;simpl in H2;destruct H2;tryfalse.
  }
  
  hoare abscsq.
  auto.
  simpl in H8.
  mytac_H.
  destruct x3.
  destruct p.
  eapply mutexpend_block_timeout_step;eauto.
  go.
  assert (m = Vnull).
  {
    clear -t.
    unfolds in t.
    mytac.
    simpl_vqm.
    auto.
  }
  subst m.
  eapply TcbMod.join_get_r;eauto.
  inverts e.
  eapply tcbmod_joinsig_get;eauto.

  hoare forward prim.
  unfold AOSTCBList.
  unfold tcbdllseg.
    simpl dllseg at 2.
    unfold node.
    sep pauto.
    eauto.
    eauto.
    auto.
    go.
    go.
    hoare forward.

  Set Printing Depth 500.
  idtac.
  Require Import OSMutexPendPart4.
  eapply mutex_pend_ptcb_is_rdy_right_to_cur' with (tcbls_r':=tcbls_r') (tcbls_sub_l := tcbls_sub_l);eauto.
Qed.

Lemma mutex_pend_can_not_lift_right_to_cur: forall
  (i : int32)
  (H1 : Int.unsigned i <= 65535)
  (v' : val)
  (v'0 : val)
  (v'1 : val)
  (v'2 : val)
  (v'3 : val)
  (v'4 : val)
  (v'5 : list vallist)
  (v'6 : list vallist)
  (v'7 : list vallist)
  (v'8 : list EventData)
  (v'9 : list EventCtr)
  (v'10 : vallist)
  (v'11 : val)
  (v'12 : val)
  (v'13 : list vallist)
  (v'14 : vallist)
  (v'15 : list vallist)
  (v'16 : vallist)
  (v'17 : val)
  (v'18 : EcbMod.map)
  (v'19 : TcbMod.map)
  (v'20 : int32)
  (v'21 : addrval)
  (v'22 : addrval)
  (v'23 : val)
  (v'24 : list vallist)
  (H0 : RH_CurTCB v'21 v'19)
  (v'27 : list EventCtr)
  (v'28 : list EventCtr)
  (v'29 : list EventData)
  (v'30 : list EventData)
  (v'32 : vallist)
  (v'33 : val)
  (v'35 : list vallist)
  (v'38 : vallist)
  (v'39 : val)
  (v'40 : EcbMod.map)
  (tcbls : TcbMod.map)
  (v'44 : val)
  (v'46 : vallist)
  (v'48 : val)
  (v'49 : EcbMod.map)
  (v'50 : EcbMod.map)
  (v'51 : EcbMod.map)
  (v'53 : addrval)
  (H5 : ECBList_P v'48 Vnull v'28 v'30 v'50 tcbls)
  (H11 : EcbMod.join v'49 v'51 v'40)
  (H14 : length v'27 = length v'29)
  (v'25 : addrval)
  (pevent_addr : block)
  (H13 : array_type_vallist_match Int8u v'46)
  (H19 : length v'46 = ∘OS_EVENT_TBL_SIZE)
  (H20 : isptr v'48)
  (x3 : val)
  (i0 : int32)
  (H22 : Int.unsigned i0 <= 255)
  (H18 : RL_Tbl_Grp_P v'46 (Vint32 i0))
  (H25 : isptr v'48)
  (H4 : ECBList_P v'44 (Vptr (pevent_addr, Int.zero)) v'27 v'29 v'49 tcbls)
  (H2 : isptr (Vptr (pevent_addr, Int.zero)))
  (H16 : id_addrval' (Vptr (pevent_addr, Int.zero)) OSEventTbl OS_EVENT =
        Some v'25)
  (H21 : Int.unsigned ($ OS_EVENT_TYPE_MUTEX) <= 255)
  (wls : waitset)
  (v'26 : val)
  (v'42 : val)
  (tcbls_l : TcbMod.map)
  (tcbls_r : TcbMod.map)
  (cur_addr : block)
  (H29 : v'33 <> Vnull)
  (Htcbjoin_whole : TcbMod.join tcbls_l tcbls_r tcbls)
  (Htcblist_subl : TCBList_P v'33 v'35 v'38 tcbls_l)
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
  (H34 : isptr v'26)
  (H : RH_TCBList_ECBList_P v'40 tcbls (cur_addr, Int.zero))
  (H10 : RH_CurTCB (cur_addr, Int.zero) tcbls)
  (Hneq_idle : cur_prio <> $ OS_IDLE_PRIO)
  (H37 : Int.unsigned ($ 0) <= 65535)
  (H38 : Int.unsigned ($ OS_STAT_RDY) <= 255)
  (H36 : isptr Vnull)
  (x0 : val)
  (tcbls_r' : TcbMod.map)
  (x : int32)
  (F2 : Int.unsigned x <= 65535)
  (H23 : Int.unsigned x <= 65535)
  (Fneq_i2_1 : Int.unsigned (x>>ᵢ$ 8) <= 255)
  (Fneq_i2_2 : Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) <= 255)
  (Hmutex_not_avail : x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 <> $ OS_MUTEX_AVAILABLE)
  (Feq_i2_1 : x>>ᵢ$ 8 = Int.modu (x>>ᵢ$ 8) ($ Byte.modulus))
  (Hcur_prio : Int.ltu (x>>ᵢ$ 8) cur_prio = true)
  (ptcb_prio : priority)
  (xm : msg)
  (H12 : isptr x0)
  (v'34 : list vallist)
  (v'36 : list vallist)
  (v'43 : val)
  (v'45 : val)
  (tcbls_sub_l : TcbMod.map)
  (v'52 : TcbMod.map)
  (tcbls_sub_r : TcbMod.map)
  (Htcbjoin_sub_whole : TcbMod.join tcbls_sub_l v'52 tcbls_r')
  (Htcblist_sub_left : TCBList_P x0 v'34 v'38 tcbls_sub_l)
  (Htcblist_sub_right : TCBList_P v'45 v'36 v'38 tcbls_sub_r)
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
  (H27 : isptr v'45)
  (H24 : isptr (Vptr (ptcb_addr, Int.zero)))
  (H7 : R_ECB_ETbl_P (pevent_addr, Int.zero)
         (V$OS_EVENT_TYPE_MUTEX
          :: Vint32 i0
             :: Vint32 x :: Vptr (ptcb_addr, Int.zero) :: x3 :: v'48 :: nil,
         v'46) tcbls)
  (H3 : ECBList_P v'44 Vnull
         (v'27 ++
          ((V$OS_EVENT_TYPE_MUTEX
            :: Vint32 i0
               :: Vint32 x :: Vptr (ptcb_addr, Int.zero) :: x3 :: v'48 :: nil,
           v'46) :: nil) ++ v'28)
         (v'29 ++
          (DMutex (Vint32 x) (Vptr (ptcb_addr, Int.zero)) :: nil) ++ v'30)
         v'40 tcbls)
  (H8 : EcbMod.joinsig (pevent_addr, Int.zero)
         (absmutexsem (x>>ᵢ$ 8)
            (Some (ptcb_addr, Int.zero, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), wls)
         v'50 v'51)
  (Hget : EcbMod.get v'40 (pevent_addr, Int.zero) =
         Some
           (absmutexsem (x>>ᵢ$ 8)
              (Some (ptcb_addr, Int.zero, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), wls))
  (H26 : RH_ECB_P
          (absmutexsem (x>>ᵢ$ 8)
             (Some (ptcb_addr, Int.zero, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), wls))
  (H6 : RLH_ECBData_P (DMutex (Vint32 x) (Vptr (ptcb_addr, Int.zero)))
         (absmutexsem (x>>ᵢ$ 8)
            (Some (ptcb_addr, Int.zero, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), wls))
  (H_ptcb_not_cur : (ptcb_addr, Int.zero) <> (cur_addr, Int.zero))
  (H32 : isptr xm)
  (H45 : Int.unsigned ptcb_prio <= 255)
  (Htcblist_subr : TCBList_P x0
                    (v'34 ++
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
                                                 Vint32 i2 :: nil) :: v'36)
                    v'38 tcbls_r')
  (H17 : RL_TCBblk_P
          (v'45
           :: v'43
              :: x10
                 :: xm
                    :: Vint32 i11
                       :: Vint32 ptcb_stat
                          :: Vint32 ptcb_prio
                             :: Vint32 i8
                                :: Vint32 i7 :: Vint32 i6 :: Vint32 i2 :: nil))
  (Hptcb_prio_not_idle : ptcb_prio <> $ OS_IDLE_PRIO)
  (Hptcb_prio_scope_obv : 0 <= Int.unsigned ptcb_prio)
  (Hptcb_prio_scope : Int.unsigned ptcb_prio < 64)
  (Hif_ptcb_is_rdy1 : ptcb_stat = $ OS_STAT_RDY)
  (Hif_ptcb_is_rdy2 : i11 = $ 0)
  (H_ptcb : TcbMod.get tcbls (ptcb_addr, Int.zero) = Some (ptcb_prio, rdy, xm))
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
                                       :: Vint32 i7
                                          :: Vint32 i6 :: Vint32 i2 :: nil)
                 v'38 (ptcb_prio, rdy, xm))
  (H50 : R_TCB_Status_P
          (v'45
           :: v'43
              :: x10
                 :: xm
                    :: Vint32 i11
                       :: Vint32 ptcb_stat
                          :: Vint32 ptcb_prio
                             :: Vint32 i8
                                :: Vint32 i7 :: Vint32 i6 :: Vint32 i2 :: nil)
          v'38 (ptcb_prio, rdy, xm))
  (Hgetcur_subr : TcbMod.get tcbls_r (cur_addr, Int.zero) =
                 Some (cur_prio, rdy, Vnull))
  (Hgetcur : TcbMod.get tcbls (cur_addr, Int.zero) =
            Some (cur_prio, rdy, Vnull))
  (Hcurnode : TCBNode_P
               (x0
                :: v'26
                   :: x12
                      :: Vnull
                         :: V$0
                            :: V$OS_STAT_RDY
                               :: Vint32 cur_prio
                                  :: Vint32 i5
                                     :: Vint32 i4
                                        :: Vint32 i3 :: Vint32 i1 :: nil)
               v'38 (cur_prio, rdy, Vnull))
  (Htcbjoin_right : TcbJoin (cur_addr, Int.zero) (cur_prio, rdy, Vnull)
                     tcbls_r' tcbls_r)
  (Hif_false : Int.eq (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) cur_prio = false)
  (Hnocur : Int.eq cur_prio (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = false)
  (H_cur_prio_scope : Int.unsigned cur_prio < 64)
  (Hx_scope1 : Int.unsigned (x>>ᵢ$ 8) < 64)
  (LHif_false : val_inj
                 (bool_and
                    (val_inj
                       (notint
                          (val_inj
                             (if Int.eq ptcb_prio (x>>ᵢ$ 8)
                              then Some (Vint32 Int.one)
                              else Some (Vint32 Int.zero)))))
                    (val_inj
                       (if Int.ltu cur_prio (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)
                        then Some (Vint32 Int.one)
                        else Some (Vint32 Int.zero)))) = 
               Vint32 Int.zero \/
               val_inj
                 (bool_and
                    (val_inj
                       (notint
                          (val_inj
                             (if Int.eq ptcb_prio (x>>ᵢ$ 8)
                              then Some (Vint32 Int.one)
                              else Some (Vint32 Int.zero)))))
                    (val_inj
                       (if Int.ltu cur_prio (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)
                        then Some (Vint32 Int.one)
                        else Some (Vint32 Int.zero)))) = Vnull)
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
                                :: Vint32 i6
                                   :: Vint32 i2 :: nil) **
     tcbdllseg x0 (Vptr (cur_addr, Int.zero)) v'43
       (Vptr (ptcb_addr, Int.zero)) v'34 **
     tcbdllseg v'45 (Vptr (ptcb_addr, Int.zero)) v'42 Vnull v'36 **
      <||
     mutexpend (Vptr (pevent_addr, Int.zero) :: Vint32 i :: nil)
     ||>  **
     LV ptcb @ OS_TCB ∗ |-> Vptr (ptcb_addr, Int.zero) **
     LV mprio @ Int8u |-> Vint32 (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) **
     LV pip @ Int8u |-> Vint32 (x >>ᵢ $ 8) **
     Astruct (cur_addr, Int.zero) OS_TCB_flag
       (x0
        :: v'26
           :: x12
              :: Vnull
                 :: V$ 0
                    :: V$ OS_STAT_RDY
                       :: Vint32 cur_prio
                          :: Vint32 i5
                             :: Vint32 i4
                                :: Vint32 i3 :: Vint32 i1 :: nil) **
     GV OSTCBList @ OS_TCB ∗ |-> v'33 **
     dllseg v'33 Vnull v'26 (Vptr (cur_addr, Int.zero)) v'35
       OS_TCB_flag (fun vl : vallist => nth_val 1 vl)
       (fun vl : vallist => nth_val 0 vl) **
     GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_addr, Int.zero) **
     AEventData
       (V$ OS_EVENT_TYPE_MUTEX
        :: Vint32 i0
           :: Vint32 x
              :: Vptr (ptcb_addr, Int.zero) :: x3 :: v'48 :: nil)
       (DMutex (Vint32 x) (Vptr (ptcb_addr, Int.zero))) **
     Astruct (pevent_addr, Int.zero) OS_EVENT
       (V$ OS_EVENT_TYPE_MUTEX
        :: Vint32 i0
           :: Vint32 x
              :: Vptr (ptcb_addr, Int.zero) :: x3 :: v'48 :: nil) **
     Aarray v'25 (Tarray Int8u ∘ OS_EVENT_TBL_SIZE) v'46 **
     Aie false **
     Ais nil **
     Acs (true :: nil) **
     Aisr empisr **
     GV OSEventList @ OS_EVENT ∗ |-> v'44 **
     evsllseg v'44 (Vptr (pevent_addr, Int.zero)) v'27 v'29 **
     evsllseg v'48 Vnull v'28 v'30 **
     A_isr_is_prop **
     tcbdllflag v'33
       (v'35 ++
        (x0
         :: v'26
            :: x12
               :: Vnull
                  :: V$ 0
                     :: V$ OS_STAT_RDY
                        :: Vint32 cur_prio
                           :: Vint32 i5
                              :: Vint32 i4
                                 :: Vint32 i3
                                    :: Vint32 i1 :: nil)
        :: v'34 ++
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
                                       Vint32 i2 :: nil) :: v'36) **
     AOSRdyTblGrp v'38 v'39 **
     AOSTCBPrioTbl v'32 v'38 tcbls v'53 **
     HECBList v'40 **
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
     AOSTCBFreeList v'23 v'24 **
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
   OSTCBCur ′ → OSTCBStat =ₑ ′ OS_STAT_MUTEX;ₛ
   OSTCBCur ′ → OSTCBDly =ₑ timeout ′;ₛ
   OS_EventTaskWait (­ pevent ′­);ₛ
   EXIT_CRITICAL;ₛ
   OS_Sched (­);ₛ
   ENTER_CRITICAL;ₛ
   If(OSTCBCur ′ → OSTCBMsg !=ₑ NULL)
        {EXIT_CRITICAL;ₛ
        RETURN ′ OS_NO_ERR}  ;ₛ
   EXIT_CRITICAL;ₛ
   RETURN ′ OS_TIMEOUT {{Afalse}}
.
Proof.
  intros.
  Set Printing Depth 500.
  idtac.
  rename LHif_false into H_can_not_lift.
  hoare forward.
  hoare forward.
  clear -H1;pauto.
  hoare forward.
  sep cancel 1%nat 1%nat.
  unfold node.
  sep normal.
  exists cur_addr.
  sep split.

  sep cancel 2%nat 1%nat.
  unfold AEventNode.
  unfold AOSEvent.
  unfold node.
  unfold AOSEventTbl.
  sep normal.
  sep eexists.
  sep split;eauto.
  sep cancel 11%nat 1%nat.
  sep cancel Aarray.
  sep cancel AEventData.
  sep cancel AOSRdyTblGrp.
  
  (* ** ac: Check a_isr_is_prop_split. *)
  sep lifts (13::11::17::nil)%nat in H9.
  apply a_isr_is_prop_split in H9.
  
  instantiate (1:=
          A_dom_lenv
            ((timeout, Int16u)
             :: (pevent, OS_EVENT ∗)
                :: (legal, Int8u)
                   :: (pip, Int8u)
                      :: (mprio, Int8u)
                         :: (os_code_defs.isrdy, Int8u)
                            :: (ptcb, OS_TCB ∗)
                               :: (pevent2, OS_EVENT ∗) :: nil) **
          Astruct (ptcb_addr, Int.zero) OS_TCB_flag
            (v'45
             :: v'43
                :: x10
                   :: xm
                      :: V$ 0
                         :: V$ OS_STAT_RDY
                            :: Vint32 ptcb_prio
                               :: Vint32 i8
                                  :: Vint32 i7
                                     :: Vint32 i6
                                        :: 
                                        Vint32 i2 :: nil) **
          tcbdllseg x0 (Vptr (cur_addr, Int.zero)) v'43
            (Vptr (ptcb_addr, Int.zero)) v'34 **
          tcbdllseg v'45 (Vptr (ptcb_addr, Int.zero)) v'42 Vnull
            v'36 **
          LV ptcb @ OS_TCB ∗ |-> Vptr (ptcb_addr, Int.zero) **
          LV mprio @ Int8u
          |-> Vint32 (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) **
          LV pip @ Int8u |-> Vint32 (x >>ᵢ $ 8) **
          GV OSTCBList @ OS_TCB ∗ |-> v'33 **
          dllseg v'33 Vnull v'26 (Vptr (cur_addr, Int.zero))
            v'35 OS_TCB_flag (fun vl : vallist => nth_val 1 vl)
            (fun vl : vallist => nth_val 0 vl) **
          (* Aie false **
          Ais nil **
          Acs (true :: nil) **
          Aisr empisr ** *)
          GV OSEventList @ OS_EVENT ∗ |-> v'44 **
          evsllseg v'44 (Vptr (pevent_addr, Int.zero)) v'27 v'29 **
          evsllseg v'48 Vnull v'28 v'30 **
          (* A_isr_is_prop ** *) (** the only difference **)
          tcbdllflag v'33
            (v'35 ++
             (x0
              :: v'26
                 :: x12
                    :: Vnull
                       :: V$ 0
                          :: V$ OS_STAT_RDY
                             :: Vint32 cur_prio
                                :: Vint32 i5
                                   :: Vint32 i4
                                      :: Vint32 i3
                                         :: 
                                         Vint32 i1 :: nil)
             :: v'34 ++
                (v'45
                 :: v'43
                    :: x10
                       :: xm
                          :: V$ 0
                             :: V$ OS_STAT_RDY
                                :: Vint32 ptcb_prio
                                   :: Vint32 i8
                                      :: Vint32 i7
                                         :: 
                                         Vint32 i6
                                         :: 
                                         Vint32 i2 :: nil)
                :: v'36) **
          AOSTCBPrioTbl v'32 v'38 tcbls v'53 **
          HECBList v'40 **
          HTCBList tcbls **
          HCurTCB (cur_addr, Int.zero) **
          LV legal @ Int8u |-> (V$ 1) **
          AOSEventFreeList v'5 **
          AOSQFreeList v'6 **
          AOSQFreeBlk v'7 **
          AOSMapTbl **
          AOSUnMapTbl **
          AOSIntNesting **
          AOSTCBFreeList v'23 v'24 **
          AOSTime (Vint32 v'20) **
          HTime v'20 **
          AGVars **
          atoy_inv' **
          LV pevent2 @ OS_EVENT ∗ |-> v'4 **
          LV os_code_defs.isrdy @ Int8u |-> v'2 **
          LV timeout @ Int16u |-> Vint32 i **
          LV pevent @ OS_EVENT ∗
          |-> Vptr (pevent_addr, Int.zero)).

  sep auto.

  unfolds;simpl;auto.
  split;auto;go.

  sep auto.
  sep auto.
  sep auto.
  sep auto.
  
  split;auto;go.
  split.
  simpl;auto.
  eexists;split.
  unfolds;simpl;auto.
  clear -Hneq_idle.
  eapply Int.eq_false;eauto.
  unfolds.
  clear -Hcurnode.
  unfolds in Hcurnode.
  mytac.
  unfolds in H1.
  mytac.
  do 6 eexists;splits;eauto.
  unfolds;simpl;eauto.
  splits; auto.
  eexists;split.
  unfolds;simpl;auto.
  intros.
  tryfalse.
  clear.
  pure_auto.

  intros.
  sep auto.
  intros.
  sep auto.
  
  unfold_funpost.
  pure intro.
  inverts H9.
  simpl in H52;inverts H52.
  simpl in H53;inverts H53.
  simpl in H54;inverts H54.
  simpl in H59;inverts H59.

  assert (Int.eq ptcb_prio (x>>ᵢ$ 8) <> false \/
   Int.ltu (x &ᵢ$ OS_MUTEX_KEEP_LOWER_8) cur_prio = true) as Hcondition.
  {
    clear -H_can_not_lift Hnocur.
    simpl in H_can_not_lift.
    remember (Int.eq ptcb_prio (x>>ᵢ$ 8)) as X.
    destruct X;simpl in H_can_not_lift.
    left;auto.
    (* pure_auto. *)
    right.
    remember (Int.ltu cur_prio (x &ᵢ$ OS_MUTEX_KEEP_LOWER_8)) as Y.
    destruct Y;simpl in H_can_not_lift.
    remember (Int.ltu Int.zero (Int.notbool Int.zero) &&
                      Int.ltu Int.zero Int.one) as Z.
    destruct Z;simpl in H_can_not_lift.
    destruct H_can_not_lift;tryfalse.
    clear -HeqZ.
    false.
    clear -HeqY Hnocur.
    symmetry in HeqY.

    apply ltu_eq_false_ltu';auto.
  }
    
  hoare abscsq.
  auto.
  eapply mutexpend_block_no_lift_step;eauto.
  go.
  clear H_can_not_lift.

  hoare lifts (9::7::nil)%nat pre.
  eapply backward_rule1.
  eapply add_a_isr_is_prop.
  hoare forward prim.
  unfold AOSTCBPrioTbl.
  unfold AOSTCBPrioTbl in H9.
  sep pauto.
  sep cancel 1%nat 1%nat.
  sep cancel 17%nat 2%nat.
  unfold AOSTCBList.
  unfold tcbdllseg.
  sep pauto.
  instantiate (12:= v'26).
  instantiate (10:=v'35).
  instantiate (7:=
                 (x0
                :: v'26
                   :: (Vptr (pevent_addr, Int.zero))
                      :: Vnull
                         :: Vint32 i
                            :: V$OS_STAT_MUTEX
                               :: Vint32 cur_prio
                                  :: Vint32 i5
                                     :: Vint32 v'63
                                        :: Vint32 v'64 :: Vint32 v'65 :: nil)).
  instantiate (5:=
                v'34 ++ ((v'45
                           :: v'43
                           :: x10
                           :: xm
                           :: V$0
                           :: V$OS_STAT_RDY
                           :: Vint32 ptcb_prio
                           :: Vint32 i8
                           :: Vint32 i7
                           :: Vint32 i6 :: Vint32 i2 :: nil)::v'36)).
  simpl update_nth_val in H9.
  unfold tcbdllseg in H9.
  sep cancel 10%nat 1%nat.

  simpl dllseg.
  sep pauto.
  eapply dllseg_compose.
  sep cancel 4%nat 1%nat.
  simpl dllseg.
  unfold node.
  sep pauto.
  sep cancel Astruct.
  sep cancel dllseg.


  unfold AECBList.
  sep pauto.
  eapply evsllseg_compose;eauto.
  instantiate (2:=(V$OS_EVENT_TYPE_MUTEX
             :: Vint32 (Int.or v'68 v'65)
                :: Vint32 x
                   :: Vptr (ptcb_addr, Int.zero) :: x3 :: v'48 :: nil)).
  unfolds.
  simpl;auto.
  sep cancel 1%nat 1%nat.
  sep cancel evsllseg.
  sep cancel evsllseg.

  {
    (* ** ac: SearchAbout tcbdllflag. *)
    (* ** ac: Check tcbdllflag_hold. *)
    eapply tcbdllflag_hold.
    Focus 2.
    sep cancel 5%nat 1%nat.
    exact_s.

    idtac.
    (* ** ac: Check tcbdllflag_hold_node2. *)

    eapply tcbdllflag_hold_node2'.
    unfolds.
    swallow; go.
    unfolds; swallow; go.
  }
  
  2:pure_auto.
  2:split;auto;go.
  2:go.
  9:go.

  eapply ecblist_p_compose;eauto.
  eapply EcbMod.join_set_r.
  eauto.
  eexists.
  eapply EcbMod.join_get_l.
  eauto.
  apply EcbMod.get_a_sig_a.
  auto with brel.

  
  eapply ECBList_P_high_tcb_block_hold_mutex; eauto.
  eapply joinsig_join_getnone;eauto.
  {
    simpl.
    eexists.
    split;auto.
    split.

    unfolds in Hcurnode.
    destruct Hcurnode as (Hmsg&Hprio&Hrl&Hx).
    simpl in Hmsg;inverts Hmsg.
    simpl in Hprio;inverts Hprio.
    unfolds in Hrl.
    destruct Hrl as (prio&xx1&y&bitx&bity&stat&Hprio&Hxx&Hy&Hbitx&Hbity&Hstat).
    simpl in Hprio;inverts Hprio.
    simpl in Hxx;inverts Hxx.
    simpl in Hy;inverts Hy.
    simpl in Hbitx;inverts Hbitx.
    simpl in Hbity;inverts Hbity.
    mytac.
    eapply R_ECB_ETbl_P_high_tcb_block_hold_mutex;eauto.
    exists  (absmutexsem (x>>ᵢ$ 8)
                         (Some (ptcb_addr, Int.zero, x &ᵢ$ OS_MUTEX_KEEP_LOWER_8)),  (cur_addr, Int.zero) ::wls) v'50.
    eexists.
    split.
    unfolds;simpl;eauto.
    splits;eauto.
    eapply EcbMod.joinsig_set;eauto.
    split.
    unfolds.
    do 2 eexists.
    splits;auto.
    intros.
    subst;tryfalse.
    intros.
    eexists;eauto.
    unfolds.
    clear -H26.
    unfolds in H26.
    destructs H26.
    splits;intros;tryfalse;auto.
    eapply H0;eauto.
    (* pure_auto. *)
    
    eapply  ECBList_P_high_tcb_block_hold_mutex; eauto.
   
    eapply ejoin_get_none_r.
    2:eauto.
    apply EcbMod.get_a_sig_a.
    auto with brel.
  }
  
  eapply TCBList_P_tcb_block_hold_mutex with (prio := cur_prio) (tcbls:=tcbls_r); eauto.
  simpl.
  do 4 eexists;splits.
  auto.
  unfolds;simpl;eauto.
  unfold sig; simpl.
  unfold TcbJoin in *.
  eauto.
  unfolds.
  splits;try solve [unfolds;simpl;auto].
  3:eauto.
  unfolds in Hcurnode.
  instantiate (1:=  (Int.repr OS_STAT_RDY)).
  instantiate (1:= V$0).
  instantiate (1:= x12).
  clear -Hcurnode.
  mytac.
  auto.
  clear -Hcurnode.
  unfolds in Hcurnode.
  mytac.
  auto.
  eapply TcbMod_join_impl_prio_neq_cur_r;eauto.
  eapply R_PrioTbl_P_impl_prio_neq_cur;eauto.
  clear -Hcurnode.
  unfolds in Hcurnode.
  destructs Hcurnode.
  inverts H.
  inverts H0.
  unfolds in H1.
  mytac.
  inverts H;inverts H5;inverts H12;inverts H1;inverts H4;inverts H0;inverts H3.
  auto.
  instantiate (1:=tcbls_l).
  eapply TCBList_P_tcb_block_hold' with (tcs:=tcbls_r) (prio:= cur_prio);eauto.
  clear -Hcurnode.
  unfolds in Hcurnode.
  destructs Hcurnode.
  inverts H.
  inverts H0.
  unfolds in H1.
  mytac.
  inverts H;inverts H5;inverts H12;inverts H1;inverts H4;inverts H0;inverts H3.
  auto.
  clear -Hcurnode.
  unfolds in Hcurnode.
  destructs Hcurnode.
  inverts H.
  inverts H0.
  unfolds in H1.
  mytac.
  inverts H;inverts H5;inverts H12;inverts H1;inverts H4;inverts H0;inverts H3.
  auto.
  clear -Hcurnode.
  unfolds in Hcurnode.
  destructs Hcurnode.
  inverts H.
  inverts H0.
  unfolds in H1.
  mytac.
  inverts H;inverts H5;inverts H12;inverts H1;inverts H4;inverts H0;inverts H3.
  auto.
  eapply TcbMod_join_impl_prio_neq_cur_l;eauto.
  eapply R_PrioTbl_P_impl_prio_neq_cur;eauto.
  clear -Hcurnode.
  unfolds in Hcurnode.
  destructs Hcurnode.
  inverts H.
  inverts H0.
  unfolds in H1.
  mytac.
  inverts H;inverts H5;inverts H12;inverts H1;inverts H4;inverts H0;inverts H3.
  auto.
  eapply TcbMod.join_set_r;eauto.
  eexists.
  eapply tcbmod_joinsig_get;eauto.
  eapply TcbMod_set_R_PrioTbl_P_hold;eauto.
  eapply rtbl_remove_RL_RTbl_PrioTbl_P_hold with (prio := cur_prio); eauto.
  clear -Hcurnode.
  unfolds in Hcurnode.
  destructs Hcurnode.
  inverts H.
  inverts H0.
  unfolds in H1.
  mytac.
  inverts H;inverts H5;inverts H12;inverts H1;inverts H4;inverts H0;inverts H3.
  auto.
  clear -Hcurnode.
  unfolds in Hcurnode.
  destructs Hcurnode.
  inverts H.
  inverts H0.
  unfolds in H1.
  mytac.
  inverts H;inverts H5;inverts H12;inverts H1;inverts H4;inverts H0;inverts H3.
  auto.
  clear -Hcurnode.
  unfolds in Hcurnode.
  destructs Hcurnode.
  inverts H.
  inverts H0.
  unfolds in H1.
  mytac.
  inverts H;inverts H5;inverts H12;inverts H1;inverts H4;inverts H0;inverts H3.
  auto.

  eapply RH_CurTCB_high_block_hold_mutex;eauto.


  eapply RH_TCBList_ECBList_P_high_block_hold_mutexsem;eauto.

  (** os_sched **)
  hoare forward.

  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aisr.
  sep cancel 1%nat 1%nat.
  sep cancel 1%nat 1%nat.
  exact_s.

  unfold isflag; auto.

  go.

  intros.
  sep auto.
  sep cancel 1%nat 1%nat.
  sep auto.

  intros.
  sep auto.
  sep cancel 1%nat 1%nat.
  sep auto.
  
  unfold_funpost.

  hoare forward prim.
  hoare unfold.
  hoare forward.
  go.
  pure_auto.
  pure_auto.
  
  instantiate (1:=Afalse).
  inverts H51.
  hoare_split_pure_all.
  destructs H51.

  assert (x9 <> Vnull).
  {
    clear -H51 H66.
    unfolds in H66.
    destruct H66.
    subst x9.
    simpl in H51.
    destruct H51.
    int auto.
    destruct H;subst;auto.
    (* pure_auto. *)
  }
  
  hoare abscsq.
  auto.
  
  simpl in H61.
  mytac.
  inverts e.
  destruct x5.
  destruct p.
  eapply mutexpend_block_get_step;eauto.
  go.
  assert (x9 = m).
  {
    clear -t.
    unfolds in t.
    mytac.
    unfolds in H;simpl in H;inverts H.
    auto.
  }
  
  subst x9.
  eapply TcbMod.join_joinsig_get;eauto.

  hoare forward prim.
  unfold AOSTCBList.
  sep pauto.
  unfold tcbdllseg.
  sep cancel 3%nat 1%nat.
  unfold dllseg;fold dllseg.
  unfold node.
  sep pauto;eauto.
  go.
  eauto.
  eauto.
  auto.
  go.
  hoare forward.

  (** if false **)
  hoare forward prim.

  hoare_split_pure_all.
  assert (x9 = Vnull).
  {
    clear -H53 H66.
    unfolds in H66.
    destruct H66.
    auto.
    destruct H.
    subst x9.
    simpl in H53.
    destruct x.
    destruct H53;simpl in H.
    false.
    false.
  }
  
  subst x9.
  inverts H51.
  hoare abscsq.
  auto.
  
  simpl in H61.
  mytac.
  inverts e.
  destruct x5.
  destruct p.
  assert ( m = Vnull).
  {
    clear -t.
    unfolds in t.
    mytac.
    unfolds in H;simpl in H;inverts H.
    auto.
  }
  
  eapply mutexpend_block_timeout_step;eauto.
  go.
  subst m.
  eapply TcbMod.join_joinsig_get;eauto.

  hoare forward prim.
  unfold AOSTCBList.
  sep pauto.
  unfold tcbdllseg.
  sep cancel 3%nat 1%nat.
  unfold dllseg;fold dllseg.
  unfold node.
  sep pauto;eauto.
  go.
  eauto.
  eauto.
  auto.
  go.
  hoare forward.
Qed.
