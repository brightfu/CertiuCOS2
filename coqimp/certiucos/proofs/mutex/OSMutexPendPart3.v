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

Set Printing Depth 300.
Open Scope code_scope.

Hint Resolve noabs_oslinv.
Hint Extern 2 (_ <= _) => apply Z.leb_le; trivial.

Open Scope list_scope.
Open Scope nat_scope.

Lemma mutex_pend_ptcb_is_rdy_left_to_cur': forall
  (i : int32)
  (H1 : (Int.unsigned i <= 65535)%Z)
  (v' v'0 v'1 v'2 v'3 v'4 : val)
  (v'5 v'6 v'7 : list vallist)
  (v'8 : list EventData)
  (v'9 : list EventCtr)
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
  (v'21 v'22 : addrval)
  (v'23 : val)
  (v'24 : list vallist)
  (H0 : RH_CurTCB v'21 v'19)
  (v'27 v'28 : list EventCtr)
  (v'29 v'30 : list EventData)
  (v'32 : vallist)
  (v'33 : val)
  (v'37 : list vallist)
  (os_rdy_tbl : vallist)
  (v'39 : val)
  (v'40 : EcbMod.map)
  (tcbls : TcbMod.map)
  (v'44 : val)
  (v'46 : vallist)
  (v'48 : val)
  (v'49 v'50 v'51 : EcbMod.map)
  (v'53 : addrval)
  (H5 : ECBList_P v'48 Vnull v'28 v'30 v'50 tcbls)
  (H11 : EcbMod.join v'49 v'51 v'40)
  (H14 : length v'27 = length v'29)
  (v'25 : addrval)
  (pevent_addr : block)
  (H13 : array_type_vallist_match Int8u v'46)
  (H19 : length v'46 = ∘ OS_EVENT_TBL_SIZE)
  (H20 : isptr v'48)
  (x3 : val)
  (i0 : int32)
  (H22 : (Int.unsigned i0 <= 255)%Z)
  (H18 : RL_Tbl_Grp_P v'46 (Vint32 i0))
  (H25 : isptr v'48)
  (H4 : ECBList_P v'44 (Vptr (pevent_addr, Int.zero)) v'27 v'29
         v'49 tcbls)
  (H2 : isptr (Vptr (pevent_addr, Int.zero)))
  (H16 : id_addrval' (Vptr (pevent_addr, Int.zero)) OSEventTbl
          OS_EVENT = Some v'25)
  (H21 : (Int.unsigned (Int.repr OS_EVENT_TYPE_MUTEX) <= 255)%Z)
  (wls : waitset)
  (v'26 v'42 : val)
  (tcbls_l tcbls_r : TcbMod.map)
  (cur_addr : block)
  (H29 : v'33 <> Vnull)
  (Htcbjoin_whole : TcbMod.join tcbls_l tcbls_r tcbls)
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
  (H34 : isptr v'26)
  (H : RH_TCBList_ECBList_P v'40 tcbls (cur_addr, Int.zero))
  (H10 : RH_CurTCB (cur_addr, Int.zero) tcbls)
  (st : taskstatus)
  (Hneq_idle : cur_prio <> Int.repr OS_IDLE_PRIO)
  (H37 : (Int.unsigned (Int.repr 0) <= 65535)%Z)
  (H38 : (Int.unsigned (Int.repr OS_STAT_RDY) <= 255)%Z)
  (H36 : isptr Vnull)
  (Hgetcur_subr : TcbMod.get tcbls_r (cur_addr, Int.zero) =
                 Some (cur_prio, st, Vnull))
  (Hgetcur : TcbMod.get tcbls (cur_addr, Int.zero) =
            Some (cur_prio, st, Vnull))
  (x0 : val)
  (x2 : TcbMod.map)
  (Htcblist_subr : TCBList_P x0 v'37 os_rdy_tbl x2)
  (x : int32)
  (F2 H23 : (Int.unsigned x <= 65535)%Z)
  (Hmutex_not_avail : Int.and x (Int.repr OS_MUTEX_KEEP_LOWER_8) <>
                     Int.repr OS_MUTEX_AVAILABLE)
  (Hcur_prio : Int.ltu (Int.shru x (Int.repr 8)) cur_prio = true)
  (ptcb_prio : priority)
  (xm : msg)
  (xs : taskstatus)
  (H12 : isptr x0)
  (Hcurnode : TCBNode_P
               (x0
                :: v'26
                   :: x12
                      :: Vnull
                         :: Vint32 (Int.repr 0)
                            :: Vint32 (Int.repr OS_STAT_RDY)
                               :: Vint32 cur_prio
                                  :: Vint32 i5
                                     :: Vint32 i4
                                        :: 
                                        Vint32 i3
                                        :: 
                                        Vint32 i1 :: nil)
               os_rdy_tbl (cur_prio, st, Vnull))
  (Htcbjoin_right : TcbJoin (cur_addr, Int.zero)
                     (cur_prio, st, Vnull) x2 tcbls_r)
  (v'34 v'36 : list vallist)
  (v'43 v'45 : val)
  (tcbls_sub_l v'52 tcbls_sub_r : TcbMod.map)
  (Htcbjoin_sub_whole : TcbMod.join tcbls_sub_l v'52 tcbls_l)
  (Htcblist_sub_left : TCBList_P v'33 v'34 os_rdy_tbl tcbls_sub_l)
  (Htcblist_sub_right : TCBList_P v'45 v'36 os_rdy_tbl tcbls_sub_r)
  (ptcb_addr : block)
  (x11 : val)
  (H31 : isptr x11)
  (i11 : int32)
  (H33 : (Int.unsigned i11 <= 65535)%Z)
  (i10 : int32)
  (H44 : (Int.unsigned i10 <= 255)%Z)
  (i8 : int32)
  (H46 : (Int.unsigned i8 <= 255)%Z)
  (ptcb_tcby : int32)
  (H47 : (Int.unsigned ptcb_tcby <= 255)%Z)
  (ptcb_bitx : int32)
  (H48 : (Int.unsigned ptcb_bitx <= 255)%Z)
  (i2 : int32)
  (H49 : (Int.unsigned i2 <= 255)%Z)
  (H30 : isptr v'43)
  (H27 : isptr v'45)
  (H24 : isptr (Vptr (ptcb_addr, Int.zero)))
  (H7 : R_ECB_ETbl_P (pevent_addr, Int.zero)
         (Vint32 (Int.repr OS_EVENT_TYPE_MUTEX)
          :: Vint32 i0
             :: Vint32 x
                :: Vptr (ptcb_addr, Int.zero)
                   :: x3 :: v'48 :: nil, v'46) tcbls)
  (H3 : ECBList_P v'44 Vnull
         (v'27 ++
          ((Vint32 (Int.repr OS_EVENT_TYPE_MUTEX)
            :: Vint32 i0
               :: Vint32 x
                  :: Vptr (ptcb_addr, Int.zero)
                     :: x3 :: v'48 :: nil, v'46) :: nil) ++ v'28)
         (v'29 ++
          (DMutex (Vint32 x) (Vptr (ptcb_addr, Int.zero)) :: nil) ++
          v'30) v'40 tcbls)
  (H8 : EcbMod.joinsig (pevent_addr, Int.zero)
         (absmutexsem (Int.shru x (Int.repr 8))
            (Some
               (ptcb_addr, Int.zero,
               Int.and x (Int.repr OS_MUTEX_KEEP_LOWER_8))), wls)
         v'50 v'51)
  (Hget : EcbMod.get v'40 (pevent_addr, Int.zero) =
         Some
           (absmutexsem (Int.shru x (Int.repr 8))
              (Some
                 (ptcb_addr, Int.zero,
                 Int.and x (Int.repr OS_MUTEX_KEEP_LOWER_8))),
           wls))
  (H26 : RH_ECB_P
          (absmutexsem (Int.shru x (Int.repr 8))
             (Some
                (ptcb_addr, Int.zero,
                Int.and x (Int.repr OS_MUTEX_KEEP_LOWER_8))),
          wls))
  (H6 : RLH_ECBData_P
         (DMutex (Vint32 x) (Vptr (ptcb_addr, Int.zero)))
         (absmutexsem (Int.shru x (Int.repr 8))
            (Some
               (ptcb_addr, Int.zero,
               Int.and x (Int.repr OS_MUTEX_KEEP_LOWER_8))), wls))
  (H_ptcb : TcbMod.get tcbls (ptcb_addr, Int.zero) =
           Some (ptcb_prio, xs, xm))
  (H_ptcb_not_cur : (ptcb_addr, Int.zero) <> (cur_addr, Int.zero))
  (H_ptcb_in_left : TcbMod.get tcbls_l (ptcb_addr, Int.zero) =
                   Some (ptcb_prio, xs, xm))
  (Htcbjoin_sub_right : TcbMod.joinsig (ptcb_addr, Int.zero)
                         (ptcb_prio, xs, xm) tcbls_sub_r v'52)
  (H32 : isptr xm)
  (H45 : (Int.unsigned ptcb_prio <= 255)%Z)
  (H17 : RL_TCBblk_P
          (v'45
           :: v'43
              :: x11
                 :: xm
                    :: Vint32 i11
                       :: Vint32 i10
                          :: Vint32 ptcb_prio
                             :: Vint32 i8
                                :: Vint32 ptcb_tcby
                                   :: Vint32 ptcb_bitx
                                      :: Vint32 i2 :: nil))
  (H50 : R_TCB_Status_P
          (v'45
           :: v'43
              :: x11
                 :: xm
                    :: Vint32 i11
                       :: Vint32 i10
                          :: Vint32 ptcb_prio
                             :: Vint32 i8
                                :: Vint32 ptcb_tcby
                                   :: Vint32 ptcb_bitx
                                      :: Vint32 i2 :: nil)
          os_rdy_tbl (ptcb_prio, xs, xm))
  (Htcblist_subl : TCBList_P v'33
                    (v'34 ++
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
                                        Vint32 ptcb_tcby
                                        :: 
                                        Vint32 ptcb_bitx
                                        :: 
                                        Vint32 i2 :: nil) :: v'36)
                    os_rdy_tbl tcbls_l)
  (Hif_can_lift : ptcb_prio <> Int.shru x (Int.repr 8) /\
                 Int.ltu cur_prio
                   (Int.and x (Int.repr OS_MUTEX_KEEP_LOWER_8)) =
                 true)
  (v'31 : val)
  (H9 : array_type_vallist_match OS_TCB ∗ v'32)
  (H52 : length v'32 = 64)
  (H15 : RL_RTbl_PrioTbl_P os_rdy_tbl v'32 v'53)
  (H51 : R_PrioTbl_P v'32 tcbls v'53)
  (H_pip_is_hold : nth_val'
                    (Z.to_nat
                       (Int.unsigned (Int.shru x (Int.repr 8))))
                    v'32 = Vptr v'53)
  (H53 : array_type_vallist_match Int8u os_rdy_tbl)
  (H56 : length os_rdy_tbl = ∘ OS_RDY_TBL_SIZE)
  (H54 : rule_type_val_match Int8u v'39 = true)
  (H55 : RL_Tbl_Grp_P os_rdy_tbl v'39)
  (H57 : prio_in_tbl (Int.repr OS_IDLE_PRIO) os_rdy_tbl)
  (Hownernidle : ptcb_prio <> Int.repr OS_IDLE_PRIO)
  (Hptcbstrdy : i10 = Int.repr OS_STAT_RDY)
  (Hptcbdly0 : i11 = Int.repr 0)
  (Hgetlast : get_last_tcb_ptr v'34 v'33 =
             Some (Vptr (ptcb_addr, Int.zero)))
  (Hrange_py : (0 <= Int.unsigned ptcb_tcby <= 7)%Z)
  (v0 : int32)
  (Hif_ptcb_rdy1 : nth_val' (Z.to_nat (Int.unsigned ptcb_tcby))
                    os_rdy_tbl = Vint32 v0)
  (Hif_ptcb_rdy2 : Int.and v0 ptcb_bitx <> Int.zero)
  (Hrangev : (Int.unsigned v0 <= 255)%Z)
  (Hfx : exists x,
        nth_val' (Z.to_nat (Int.unsigned ptcb_tcby))
          (update_nth_val (Z.to_nat (Int.unsigned ptcb_tcby))
             os_rdy_tbl (Vint32 (Int.and v0 (Int.not ptcb_bitx)))) =
        Vint32 x /\ (Int.unsigned x <= 255)%Z)
  (Hif_false : val_inj
                (val_eq
                   (nth_val' (Z.to_nat (Int.unsigned ptcb_tcby))
                      (update_nth_val
                         (Z.to_nat (Int.unsigned ptcb_tcby))
                         os_rdy_tbl
                         (Vint32 (Int.and v0 (Int.not ptcb_bitx)))))
                   (Vint32 (Int.repr 0))) = 
              Vint32 Int.zero \/
              val_inj
                (val_eq
                   (nth_val' (Z.to_nat (Int.unsigned ptcb_tcby))
                      (update_nth_val
                         (Z.to_nat (Int.unsigned ptcb_tcby))
                         os_rdy_tbl
                         (Vint32 (Int.and v0 (Int.not ptcb_bitx)))))
                   (Vint32 (Int.repr 0))) = Vnull)
(* ================================= *) ,
   {|OS_spec, GetHPrio, OSLInv, I,
   fun v : option val =>
   ( <|| END v ||>  **
    p_local OSLInv (cur_addr, Int.zero) init_lg **
    ((EX v1 : val, LV timeout @ Int16u |-> v1) **
     (EX v1 : val, LV pevent @ OS_EVENT ∗ |-> v1) **
     (EX v1 : val, LV legal @ Int8u |-> v1) **
     (EX v1 : val, LV pip @ Int8u |-> v1) **
     (EX v1 : val, LV mprio @ Int8u |-> v1) **
     (EX v1 : val, LV os_code_defs.isrdy @ Int8u |-> v1) **
     (EX v1 : val, LV ptcb @ OS_TCB ∗ |-> v1) **
     (EX v1 : val, LV pevent2 @ OS_EVENT ∗ |-> v1) ** Aemp) **
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
     GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
       (update_nth_val (Z.to_nat (Int.unsigned ptcb_tcby))
          os_rdy_tbl
          (val_inj (and (Vint32 v0) (Vint32 (Int.not ptcb_bitx))))) **
     GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64)
       (update_nth_val
          (Z.to_nat (Int.unsigned (Int.shru x (Int.repr 8))))
          (update_nth_val (Z.to_nat (Int.unsigned ptcb_prio))
             v'32 (Vptr v'53)) (Vptr (ptcb_addr, Int.zero))) **
     PV v'53 @ Int8u |-> v'31 **
     Astruct (ptcb_addr, Int.zero) OS_TCB_flag
       (v'45
        :: v'43
           :: x11
              :: xm
                 :: Vint32 i11
                    :: Vint32 i10
                       :: Vint32 ptcb_prio
                          :: Vint32 i8
                             :: Vint32 ptcb_tcby
                                :: Vint32 ptcb_bitx
                                   :: Vint32 i2 :: nil) **
     tcbdllseg v'33 Vnull v'43 (Vptr (ptcb_addr, Int.zero)) v'34 **
     tcbdllseg v'45 (Vptr (ptcb_addr, Int.zero)) v'26
       (Vptr (cur_addr, Int.zero)) v'36 **
     LV ptcb @ OS_TCB ∗ |-> Vptr (ptcb_addr, Int.zero) **
     LV mprio @ Int8u
     |-> Vint32 (Int.and x (Int.repr OS_MUTEX_KEEP_LOWER_8)) **
     LV pip @ Int8u |-> Vint32 (Int.shru x (Int.repr 8)) **
     Astruct (cur_addr, Int.zero) OS_TCB_flag
       (x0
        :: v'26
           :: x12
              :: Vnull
                 :: Vint32 (Int.repr 0)
                    :: Vint32 (Int.repr OS_STAT_RDY)
                       :: Vint32 cur_prio
                          :: Vint32 i5
                             :: Vint32 i4
                                :: Vint32 i3 :: Vint32 i1 :: nil) **
     dllseg x0 (Vptr (cur_addr, Int.zero)) v'42 Vnull v'37
       OS_TCB_flag (fun vl : vallist => nth_val 1 vl)
       (fun vl : vallist => nth_val 0 vl) **
     GV OSTCBList @ OS_TCB ∗ |-> v'33 **
     GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_addr, Int.zero) **
     AEventData
       (Vint32 (Int.repr OS_EVENT_TYPE_MUTEX)
        :: Vint32 i0
           :: Vint32 x
              :: Vptr (ptcb_addr, Int.zero) :: x3 :: v'48 :: nil)
       (DMutex (Vint32 x) (Vptr (ptcb_addr, Int.zero))) **
     Astruct (pevent_addr, Int.zero) OS_EVENT
       (Vint32 (Int.repr OS_EVENT_TYPE_MUTEX)
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
       ((v'34 ++
         (v'45
          :: v'43
             :: x11
                :: xm
                   :: Vint32 i11
                      :: Vint32 i10
                         :: Vint32 ptcb_prio
                            :: Vint32 i8
                               :: Vint32 ptcb_tcby
                                  :: Vint32 ptcb_bitx
                                     :: Vint32 i2 :: nil) :: v'36) ++
        (x0
         :: v'26
            :: x12
               :: Vnull
                  :: Vint32 (Int.repr 0)
                     :: Vint32 (Int.repr OS_STAT_RDY)
                        :: Vint32 cur_prio
                           :: Vint32 i5
                              :: Vint32 i4
                                 :: Vint32 i3 :: Vint32 i1 :: nil)
        :: v'37) **
     GV OSRdyGrp @ Int8u |-> v'39 **
     G& OSPlaceHolder @ Int8u == v'53 **
     HECBList v'40 **
     HTCBList tcbls **
     HCurTCB (cur_addr, Int.zero) **
     p_local OSLInv (cur_addr, Int.zero) init_lg **
     LV legal @ Int8u |-> Vint32 (Int.repr 1) **
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
  rename i2 into ptcb_bity.
  rename Hif_false into Hif_rdytbl_tcby_neq_zero.
  simpl in Hif_rdytbl_tcby_neq_zero.

  hoare forward.
  rtmatch_solve.
  clear -H26.
  unfolds in H26.
  mytac.
  clear -H2.
  int auto.
  Open Scope Z_scope.
  Open Scope int_scope.
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
  struct_type_match_solver.
  (* { *)
  (*   rewrite postintlemma4. *)
  (*   pure_auto. *)
  (* } *)
  
  unfold AOSMapTbl.
  hoare forward.
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
    Open Scope code_scope.
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
  
  rewrite H58.

  Open Scope Z_scope.
  assert (exists vx, nth_val' (Z.to_nat
                         (Int.unsigned ((x>>ᵢ$ 8)>>ᵢ$ 3)))
                              OSMapVallist = Vint32 vx /\ Int.unsigned vx <=128).
  {
    (* ** ac: Locate osmapvallist_prop. *)
    Open Scope code_scope.
    eapply osmapvallist_prop;eauto.
    clear -H26.
    unfolds in H26.
    mytac.
    apply aux_trivial in H2;omega.
  }

  idtac.
  destruct H59.
  destruct H59.
  rewrite H59.
  hoare forward.
  simpl val_inj.
  struct_type_match_solver.
 
  hoare forward.
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

  destruct H61.
  destruct H61.
  rewrite H61.
  hoare forward.
  (* pure_auto. *)
  go.
  simpl in H54;destruct v'39;tryfalse;simpl;auto.
  (* pure_auto. *)
  
  assert (Int.ltu ($ 3) Int.iwordsize = true) as Hpred1.
  {
    clear;int auto.
  }
  rewrite Hpred1 in *.
  simpl val_inj in *.

  assert (exists xx, nth_val' (Z.to_nat (Int.unsigned ((x>>ᵢ$ 8)>>ᵢ$ 3)))
                              (update_nth_val (Z.to_nat (Int.unsigned ptcb_tcby)) os_rdy_tbl
                                              (Vint32 (v0 &ᵢInt.not ptcb_bitx))) = Vint32 xx /\ Int.unsigned xx <= 255) as Hfx1.
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
    rewrite H56.
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
  rewrite H56.
  simpl.
  clear -H26.
  unfolds in H26.
  mytac.
  apply aux_trivial in H2;auto.
  eapply array_type_vallist_match_imp_rule_type_val_match;eauto.
  simpl.
  rewrite update_nth_val_len_eq.
  rewrite H56.
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
  rewrite H56.
  simpl.
  eapply aux_trivial.
  clear -H26.
  unfolds in H26.
  mytac.

  assert (Hcur_is_rdy: st = rdy).
  {
    clear -Hcurnode H56 H53.
    unfolds in Hcurnode.
    mytac.
    eapply OSTimeDlyPure.low_stat_rdy_imp_high with (rtbl:=os_rdy_tbl);eauto.
  }
    
  hoare forward.
  hoare forward.
  rtmatch_solve.
  auto.
  transform_pre a_isr_is_prop_split ltac:(sep cancel Aisr;
                                          sep cancel Ais;
                                          sep cancel A_isr_is_prop).
  hoare_split_pure_all.
  destruct Hif_can_lift as (Hif_can_lift1 & Hif_can_lift2).
  (* ** os_eventtaskwait (pevent) *)
  unfold AEventData.
  hoare_split_pure_all.
  clear H64 H65 H66.
  Open Scope list_scope.
  assert (  RL_TCBblk_P
     (v'45
      :: v'43
         :: x11
            :: xm
               :: Vint32 i11
                  :: V$OS_STAT_MUTEX
                     :: Vint32 (x>>ᵢ$ 8)
                        :: Vint32 ((x>>ᵢ$ 8)&ᵢ$ 7)
                           :: Vint32 ((x>>ᵢ$ 8)>>ᵢ$ 3)
                           :: Vint32 x4 :: Vint32 x1 :: nil)) as Hnewrltcbblkp.
  {
    unfolds.
    do 6 eexists;splits;eauto.
    unfolds;simpl;auto.
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
      simpl in H54;tryfalse.
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

    {
      (** fix **)
      eapply OSTimeDlyPure.event_wait_rl_tbl_grp'';eauto. 
      rewrite len_lt_update_get_eq in Hif_rdytbl_tcby_neq_zero. 
      simpl in Hif_rdytbl_tcby_neq_zero.
      clear -Hif_rdytbl_tcby_neq_zero.
      destruct (Int.eq (v0 &ᵢInt.not ptcb_bitx) ($ 0));auto.
      simpl in *;destruct Hif_rdytbl_tcby_neq_zero;tryfalse.

      rewrite H56.
      simpl; omega.
    }      

    eapply idle_in_rtbl_hold';eauto.
    clear -H26.
    unfolds in H26.
    mytac.
    apply aux_trivial in H2;omega.
    rewrite update_nth_val_len_eq.
    rewrite H56.
    auto.
    eapply array_type_vallist_match_int8u_update_hold;eauto.
    clear -H17.
    unfolds in H17.
    mytac.
    simpl_vqm.
    clear -H12.
    mauto.
    
    clear -H57 H17  Hownernidle Hif_ptcb_rdy1.
    unfolds in H17.
    mytac.
    simpl_vqm.
    eapply prio_neq_in_tbl_rev;eauto.
    unfold OS_IDLE_PRIO.
    unfold OS_LOWEST_PRIO.
    int auto.
    eapply nth_val'2nth_val;eauto.
    destruct v'39;simpl in H54;simpl;auto.
    rtmatch_solve.
    apply int_unsigned_or_prop;auto.
    apply Zle_bool_imp_le.
    clear -H54.
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
    rewrite H56;auto.
    eapply array_type_vallist_match_int8u_update_hold;eauto.
    clear -H17.
    unfolds in H17.
    mytac.
    simpl_vqm.
    clear -H12.
    mauto.
    rewrite update_nth_val_len_eq.
    rewrite H56.
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
    rewrite H56.
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
  inverts H64.
  unfold V_OSTCBY,V_OSTCBBitX,V_OSTCBBitY,V_OSEventGrp in H66.
  simpl in H66.
  mytac_H.
  inverts H65.
  inverts H66; inverts H67; inverts H68; inverts H74.

  assert (Hos_grp_scope: exists os_grp, v'39 = Vint32 os_grp /\
                         Int.unsigned os_grp <= Byte.max_unsigned).
  {
    clear -H54.
    destruct v'39;tryfalse.
    eexists;simpl in H54;split;auto.
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
  
  rename H70 into Hfn.
  clear H82 H83 H84.
  mytac_H.
  inverts H63.
  inverts H71.
  unfolds in H67;simpl in H67;inverts H67.
  subst.


(**************************** simplify begin ****************************)
 
  transform_pre add_a_isr_is_prop ltac:(sep cancel Aisr;
                                        sep cancel Ais).
  assert (Hptcb_is_rdy: xs = rdy).
  {
    eapply OSTimeDlyPure.low_stat_rdy_imp_high with (rtbl:=os_rdy_tbl);eauto.
  }
  subst xs.

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
  
  hoare forward prim.
  (* cancel AECBList *)
  unfold AECBList.
  sep pauto.
  
  eapply evsllseg_compose.
  4: sep cancel evsllseg.
  4: sep cancel evsllseg.
  instantiate (1:=
                 (V$OS_EVENT_TYPE_MUTEX
                   :: Vint32 (Int.or v'68 v'65)
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


  (** sep cancel cur_right dllseg first *)
  sep lift 2%nat.
  eapply tcbdllseg_cons;eauto.
  sep cancel Astruct.
  unfold tcbdllseg.
  sep cancel 12%nat 1%nat.
  (** sep cancel cur_left dllseg has form: l1 ++ ptcb ++ l2 *)

  eapply dllseg_compose;eauto.
  unfold  V_OSTCBPrev, V_OSTCBNext.
  sep cancel 8%nat 1%nat.
  instantiate (8:=  (v'45
                       :: v'43
                       :: x11
                       :: xm
                       :: V$0
                       :: V$OS_STAT_RDY
                       :: Vint32 (x>>ᵢ$ 8)
                       :: Vint32 ((x>>ᵢ$ 8)&ᵢ$ 7)
                       :: Vint32 ((x>>ᵢ$ 8)>>ᵢ$ 3)
                       :: Vint32 x4 :: Vint32 x1 :: nil) :: v'36).
  simpl dllseg.
  unfold node.
  sep pauto.
  unfold tcbdllseg in *.
  sep cancel dllseg.
  sep cancel Astruct.
  (* 2:pure_auto. *)
  2: split; go.
  2:unfolds;simpl;auto.
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
    eapply tcbdllflag_hold_node2.
    unfolds.
    swallow; go.
    unfolds; swallow; go.
  }  

  (** OSRdyGrp need update? Yes **)
  Focus 3.
  split.
  eapply array_type_vallist_match_hold;eauto.
  eapply array_type_vallist_match_hold;eauto.
  rewrite H52.
  clear -H17.
  unfolds in H17.
  mytac.
  simpl_vqm.
  mauto.
  rewrite update_nth_val_len_eq.
  rewrite H52.
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
  clear -Hcurnode.
  unfolds in Hcurnode.
  mytac.
  unfolds in H1.
  mytac.
  simpl_vqm.
  auto.
  clear -H26.
  unfolds in H26.
  mytac;auto.
  clear -H17.
  unfolds in H17.
  mytac.
  unfolds in H1.
  mytac.
  simpl_vqm.
  auto.
  rewrite H78.
  simpl.
  eapply OSTimeDlyPure.rtbl_remove_RL_RTbl_PrioTbl_P_hold;eauto.
  instantiate (1:=cur_prio).
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
  rewrite H78 in Hfn.
  auto.

  eapply RL_RTbl_PrioTbl_P_set;eauto.
  

  clear -H26.
  unfolds in H26.
  mytac;auto.
  rewrite update_nth_val_len_eq;auto.
  rewrite update_nth_val_len_eq;auto.
  
  unfolds in H51.
  clear -H_ptcb H51.
  mytac.
  apply H0 in H_ptcb.
  destruct H_ptcb;auto.
  
  eapply RL_RTbl_PrioTbl_P_set_vhold;eauto.
  rewrite H56.
  clear -H17.
  unfolds in H17.
  mytac.
  unfolds in H1.
  mytac.
  simpl_vqm.
  unfold OS_RDY_TBL_SIZE.
  mauto.
  rewrite H78.

  instantiate (1:= TcbMod.set tcbls_r (v'38, Int.zero) (cur_prio, (wait (os_stat_mutexsem (v'46, Int.zero)) i), Vnull)).
  simpl.
  do 3 eexists;exists (cur_prio, (wait (os_stat_mutexsem (v'46, Int.zero)) i), Vnull);splits;eauto.
  unfolds;simpl;auto.

  eapply TcbMod.joinsig_set;eauto.


  lets Hx: math_mapval_core_prop H61.
  clear -H26.
  unfolds in H26.
  mytac.
  remember (x>>ᵢ$ 8) as X.
  clear HeqX.
  mauto.
  subst x4.


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
  (* ** ac: SearchAbout RL_TCBblk_P. *)
  clear - Hnewrltcbblkp.
  unfolds in Hnewrltcbblkp.
  mytac.
  simpl_vqm.
  auto.  
  
(*  unfolds in H1.
  lets Hx:H1 Hgetcur H_ptcb.
  auto.
  auto.
  clear -H26.
  unfolds in H26.
  mytac.
  auto.
 *)

  (* ** ac: Locate TCBList_P_tcb_block_hold'. *)
  eapply TCBList_P_tcb_block_hold' with (tcs':=tcbls_r) (tcs:=TcbMod.sig (v'38, Int.zero) (cur_prio, rdy, Vnull));eauto.
  instantiate (1:=cur_prio).
  clear -Hcurnode.
  unfolds in Hcurnode.
  mytac_H.
  simpl_vqm.
  unfolds in H1.
  mytac_H.
  simpl_vqm.
  split;auto.
  instantiate (3:=(v'38, Int.zero)).

  apply TcbMod.get_sig_some.
  clear -Htcbjoin_right.
  apply TcbMod.join_comm.
  unfolds in Htcbjoin_right.
  auto.

  lets Hx: math_mapval_core_prop H61.
  clear -H26.
  unfolds in H26.
  mytac.
  remember (x>>ᵢ$ 8) as X.
  clear HeqX.
  mauto.
  subst x4.
  eapply TCBList_P_rtbl_add_simpl_version;eauto.
  clear -H26.
  unfolds in H26.
  mytac.
  clear - H2.
  split; int auto.
  apply nth_val'2nth_val;auto.

  eapply vhold_not_get with (tcbls_r:=tcbls_r);eauto.
  eapply TCBList_P_tcb_block_hold' with
  (tcs:=(TcbMod.sig (ptcb_addr, Int.zero) (ptcb_prio, rdy, xm))) (tcs':=TcbMod.merge (TcbMod.sig (ptcb_addr, Int.zero) (ptcb_prio, rdy, xm)) x2);eauto.
  instantiate (1:=ptcb_prio).
  clear -H17.
  unfolds in H17.
  mytac_H.
  unfolds in H1.
  mytac_H.
  simpl_vqm.
  split;auto.
 
  rewrite TcbMod.get_sig_some;eauto.
  lets Hx: join_prop_mutexpend Htcbjoin_right  Htcbjoin_sub_right Htcbjoin_sub_whole Htcbjoin_whole.
  auto.
  clear -H17.
  unfolds in H17.
  mytac_H.
  unfolds in H1.
  mytac_H.
  simpl_vqm.
  auto.
  clear -H17.
  unfolds in H17.
  mytac_H.
  unfolds in H1.
  mytac_H.
  simpl_vqm.
  auto.
  eapply TcbMod_join_impl_prio_neq_cur_r with (tcbls:= tcbls_r).
  eapply TcbMod_join_impl_prio_neq_cur_r with (tcbls:= tcbls);eauto.
  eapply R_PrioTbl_P_impl_prio_neq_cur;eauto.
   clear -H17.
  unfolds in H17.
  mytac_H.
  unfolds in H1.
  mytac_H.
  simpl_vqm.
  auto.
  simpl in Htcbjoin_right;eauto.
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
  eapply TcbMod_join_impl_prio_neq_cur_r with (tcbls:= tcbls_r).
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
  simpl in Htcbjoin_right;eauto.
  rewrite H78 in Hfn;simpl in Hfn;auto.

  rewrite H78.
  simpl val_inj.
  instantiate (1:=TcbMod.set tcbls_l (ptcb_addr,Int.zero) ((x>>ᵢ$ 8), rdy, xm)).

  eapply TCBList_P_tcb_block_hold' with (tcs:=TcbMod.sig (v'38,Int.zero) (cur_prio,rdy,Vnull)) (tcs':=TcbMod.merge (TcbMod.sig (v'38,Int.zero) (cur_prio,rdy,Vnull)) (TcbMod.set tcbls_l (ptcb_addr, Int.zero) (x>>ᵢ$ 8, rdy, xm))).
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

  eapply join_prop_mutexpend';eauto.
  rewrite H78 in Hfn.
  simpl in Hfn.
  apply math_mapval_core_prop in H61.
  subst x4.
  apply math_mapval_core_prop in H59.
  subst x1.
  simpl in H69;inverts H69.
 
  eapply tcbls_l_mutexpend;eauto.
  clear -H26.
  unfolds in H26.
  mytac.
  auto.
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
  eapply TcbMod_join_impl_prio_neq_cur_l with (tcbls:= tcbls);eauto.
  eapply R_PrioTbl_P_impl_prio_neq_cur;eauto.
   clear -Hcurnode.
  unfolds in Hcurnode.
  mytac_H.
  simpl_vqm.
  unfolds in H1.
  mytac_H.
  simpl_vqm.
  auto.
  rewrite H78 in Hfn.
  simpl in Hfn.
  auto.

  eapply join_prop_mutexpend'';eauto.

  instantiate (1:=  Vint32 (Int.or v'68 v'65)).
  2:unfolds;simpl;auto.
  2:auto.
  inverts H69.
  (* ** ac: SearchAbout length. *)
  clear -Hcurnode H19 H18 H13 H65 H72.
  (* ** ac: Locate event_wait_rl_tbl_grp. *)
  (* ** ac: Check event_wait_rl_tbl_grp. *)
  eapply event_wait_rl_tbl_grp;eauto.
  unfolds in Hcurnode.
  mytac_H.
  eauto.
  apply nth_val_nth_val'_some_eq;auto.

  Open Scope nat_scope.
  Open Scope code_scope.
  assert (array_type_vallist_match Int8u
                                   (update_nth_val ∘(Int.unsigned v'63) v'56
                                                   (val_inj (or (nth_val' ∘(Int.unsigned v'63) v'56) (Vint32 v'64))))).
  {
    eapply array_type_vallist_match_int8u_update_hold'; auto.
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

  apply nth_val_nth_val'_some_eq in H72.
  rewrite H72 in H71;simpl in H71;auto.

  eapply ecblist_p_mutexpend_changeprio;eauto.
  rewrite TcbMod.set_a_get_a'.
  eauto.
  eapply tidspec.neq_beq_false;auto.
  (* inverts H71. *)
    (*
    assert (v'27 = nil \/ get_last_ptr v'27 = Some (Vptr (v'46, Int.zero))) as Helslink.
    clear - H58.
    assert (v'27 = nil \/ v'27 <> nil) by tauto.
    destruct H;auto.
    sep lift*)
    
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
Qed.

Close Scope code_scope.
