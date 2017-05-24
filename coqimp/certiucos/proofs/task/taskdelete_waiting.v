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
Require Import OSQPostPure.
Local Open Scope code_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.
Local Open Scope list_scope.
Lemma absimp_taskdel_cler_waitls_bit:
  forall P v3 sch tls els ct els' st wait_t msg eid ehb wl tid t,
    can_change_aop P ->
    TcbMod.get tls tid = Some (v3, wait st wait_t, msg) ->
    isWait4Ecb st eid ->
    EcbMod.get els eid = Some (ehb, wl) ->
    els' = set els eid (ehb, (remove_tid tid wl)) ->
    (* Int.lt ($ 63) v3 = false ->
     * (* OSAbstMod.get O abtcblsid = Some (abstcblist tls) -> *)
     * ~ (exists t' st msg, TcbMod.get tls t' = Some (v3, st, msg)) ->
     * (exists t', TcbMod.join tls (TcbMod.sig t' (v3, rdy, Vnull)) tls' )-> *)
    absinfer sch 
             ( <|| taskdel_clear_waitls_bit (|((Vint32 v3) :: nil)|) ;; spec_del (Vint32 v3)  ;;isched ;; END (Some (Vint32 (Int.repr NO_ERR))) ||> **  HECBList els ** HTCBList tls ** HTime t ** HCurTCB ct ** P)
             ( <|| spec_del (Vint32 v3);;  isched ;; END (Some (Vint32 (Int.repr NO_ERR))) ||> **  HECBList els' ** HTCBList tls ** HTime t ** HCurTCB ct ** P)
.
Proof.
  intros.
  infer_part1 0%nat.
  infer_part2.
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


Lemma task_deletewaiting:
  forall
(
  v' v'0 v'1 v'2 : val
)(
  v'3 v'4 v'5 : list vallist
)(
  priotbl : vallist
)(
  v'9 : val
)(
  l1 l2 : list vallist
)(
  ecbmap : EcbMod.map
)(
  tcbmap : TcbMod.map
)(
  v'18 : int32
)(
  vhold : addrval
)(
  v'20 : val
)(
  v'21 : list vallist
)(
  v'22 : val
)(
  H4 : array_type_vallist_match OS_TCB ∗ priotbl
)(
  H7 : length priotbl = 64%nat
)(
  H6 : R_PrioTbl_P priotbl tcbmap vhold
)(
  v'23 v'24 : val
)(
  v'25 v'26 : TcbMod.map
)(
  H8 : v'9 <> Vnull
)(
  H9 : join v'25 v'26 tcbmap
)(
  v'27 : val
)(
  cur_tcb_blk : block
)(
  H2 : RH_TCBList_ECBList_MUTEX_OWNER ecbmap tcbmap
)(
  H61 : forall (p : priority) (tid0 : tid) (eid : ecbid) 
          (t : int32) (msg0 : msg) (waitstat : tcbstats),
        isWait4Ecb waitstat eid ->
        get tcbmap tid0 = Some (p, wait waitstat t, msg0) ->
        exists hle wls,
        get ecbmap eid = Some (hle, wls) /\
        In tid0 wls /\ hle2wait hle eid = waitstat
)(
  H62 : poi_R_ET ecbmap tcbmap
)(
  H3 : RH_CurTCB (cur_tcb_blk, Int.zero) tcbmap
)(
  H15 : Vptr (cur_tcb_blk, Int.zero) <> Vnull
)(
  x1 x2 x3 x4 : val
)(
  x5 : int32
)(
  x6 x7 x8 x9 : val
)(
  H12 : isptr v'27
)(
  hello : taskstatus
)(
  kitty : ProtectWrapper
            (TcbMod.get tcbmap (cur_tcb_blk, Int.zero) = Some (x5, hello, x2))
)(
  H19 : RH_CurTCB (cur_tcb_blk, Int.zero) tcbmap
)(
  H17 : RH_TCBList_ECBList_P ecbmap tcbmap (cur_tcb_blk, Int.zero)
)(
  v'10 v'12 : val
)(
  H18 : v'9 <> Vnull
)(
  x0 : msg
)(
  l1' l2' : list vallist
)(
  v'13 : val
)(
  v'17 v'19 : TcbMod.map
)(
  H28 : TcbMod.join v'17 v'19 tcbmap
)(
  x17 x18 x19 x20 : val
)(
  H16 : isptr x20
)(
  H27 : isptr x19
)(
  H31 : isptr x18
)(
  H32 : isptr x17
)(
  i6 : int32
)(
  H33 : Int.unsigned i6 <= 65535
)(
  i5 : int32
)(
  H34 : Int.unsigned i5 <= 255
)(
  i4 : int32
)(
  H35 : Int.unsigned i4 <= 255
)(
  i3 : int32
)(
  H36 : Int.unsigned i3 <= 255
)(
  i2 : int32
)(
  H37 : Int.unsigned i2 <= 255
)(
  i1 : int32
)(
  H38 : Int.unsigned i1 <= 255
)(
  i0 : int32
)(
  H39 : Int.unsigned i0 <= 255
)(
  todelblock : block
)(
  H14 : (todelblock, Int.zero) <> vhold
)(
  some_pure_hyp : ~ is_some_mutex_owner (todelblock, Int.zero) ecbmap

    (* forall (eid : tidspec.A) (pr : int32) 
     *                 (tid0 : tid) (opr : int32) (wls : waitset),
     *               EcbMod.get ecbmap eid =
     *               Some (absmutexsem pr (Some (tid0, opr)), wls) ->
     *               tid0 <> (todelblock, Int.zero) *)
)(
  H40 : Vptr (todelblock, Int.zero) <> Vnull
)(
  i13 : int32
)(
  H45 : Int.unsigned i13 <= 65535
)(
  H42 : isptr v'13
)(
  x13 : TcbMod.map
)(
  H44 : isptr x0
)(
  x21 : int32
)(
  H58 : x21 = $ OS_STAT_SEM \/
        x21 = $ OS_STAT_Q \/ x21 = $ OS_STAT_MBOX \/ x21 = $ OS_STAT_MUTEX
)(
  H46 : Int.unsigned x21 <= 255
)(
  v'11 : block
)(
  v'29 : int32
)(
  v'30 : vallist
)(
  v'31 : addrval
)(
  v'32 v'33 v'34 v'35 v'36 : expr
)(
  v'40 v'41 : int32
)(
  H59 : OSRdyGrp ′
        :: OSRdyTbl ′
           :: ptcb ′ → OSTCBBitX
              :: ptcb ′ → OSTCBBitY :: ptcb ′ → OSTCBY :: nil =
        v'33 :: v'32 :: v'34 :: v'35 :: v'36 :: nil
)(
  H71 : Int.unsigned v'41 <= Byte.max_unsigned
)(
  H66 : rule_type_val_match Int8u (Vint32 v'40) = true
)(
  H21 : Int.unsigned v'29 <= 255
)(
  H5 : RL_RTbl_PrioTbl_P v'30 priotbl vhold
)(
  H10 : TCBList_P v'9 l1 v'30 v'25
)(
  H29 : TCBList_P v'9 l1' v'30 v'17
)(
  H11 : TCBList_P (Vptr (cur_tcb_blk, Int.zero))
          ((x20
            :: x19
               :: x18
                  :: x17
                     :: Vint32 i6
                        :: Vint32 i5
                           :: Vint32 i4
                              :: Vint32 i3
                                 :: Vint32 i2
                                    :: Vint32 i1 :: Vint32 i0 :: nil) :: l2)
          v'30 v'26
)(
  H20 : array_type_vallist_match Int8u v'30
)(
  H56 : length v'30 = ∘ OS_RDY_TBL_SIZE
)(
  H55 : prio_in_tbl ($ OS_IDLE_PRIO) v'30
)(
  H54 : length v'30 = ∘ OS_RDY_TBL_SIZE
)(
  H30 : RL_Tbl_Grp_P v'30 (Vint32 v'29)
)(
  bbackup : RH_TCBList_ECBList_P ecbmap tcbmap (cur_tcb_blk, Int.zero)
)(
  x : edata
)(
  x14 : list tid
)(
  H74 : In (todelblock, Int.zero) x14
)(
  v'8 : val
)(
  H76 : isptr v'8
)(
  x11 x15 : list os_inv.EventCtr
)(
  x22 : EventData
)(
  x23 x24 : list EventData
)(
  x25 x26 : EcbMod.map
)(
  H77 : join x25 x26 ecbmap
)(
  v'6 : val
)(
  H82 : isptr v'6
)(
  v'15 : block
)(
  x29 x30 : val
)(
  i7 : int32
)(
  H89 : Int.unsigned i7 <= 255
)(
  i8 : int32
)(
  H91 : Int.unsigned i8 <= 65535
)(
  H92 : isptr x29
)(
  H93 : isptr v'6
)(
  H64 : x21 = $ OS_STAT_RDY -> Vptr (v'15, Int.zero) = Vnull
)(
  H43 : isptr (Vptr (v'15, Int.zero))
)(
  H73 : get ecbmap (v'15, Int.zero) = Some (x, x14)
)(
  H72 : isWait4Ecb (hle2wait x (v'15, Int.zero)) (v'15, Int.zero)
)(
  H80 : ECBList_P v'8 (Vptr (v'15, Int.zero)) x11 x23 x25 tcbmap
)(
  H79 : isptr (Vptr (v'15, Int.zero))
)(
  v'28 : int32
)(
  v'37 : vallist
)(
  v'38 : addrval
)(
  v'39 v'42 v'44 v'45 v'46 : expr
)(
  v'50 v'51 v'53 : int32
)(
  H83 : pevent ′ → OSEventGrp
        :: pevent ′ → OSEventTbl
           :: ptcb ′ → OSTCBBitX
              :: ptcb ′ → OSTCBBitY :: ptcb ′ → OSTCBY :: nil =
        v'42 :: v'39 :: v'44 :: v'45 :: v'46 :: nil
)(
  H104 : Int.unsigned v'51 <= Byte.max_unsigned
)(
  H96 : rule_type_val_match Int8u (Vint32 v'50) = true
)(
  H90 : Int.unsigned v'28 <= 255
)(
  H84 : array_type_vallist_match Int8u v'37
)(
  H88 : length v'37 = ∘ OS_EVENT_TBL_SIZE
)(
  H87 : RL_Tbl_Grp_P v'37 (Vint32 v'28)
)(
  H75 : ECBList_P v'8 Vnull
          (x11 ++
           (Vint32 i7 :: Vint32 v'28 :: Vint32 i8 :: x29 :: x30 :: v'6 :: nil,
           v'37) :: x15) (x23 ++ x22 :: x24) ecbmap tcbmap
)(
  H81 : ECBList_P (Vptr (v'15, Int.zero)) Vnull
          ((Vint32 i7 :: Vint32 v'28 :: Vint32 i8 :: x29 :: x30 :: v'6 :: nil,
           v'37) :: x15) (x22 :: x24) x26 tcbmap
)(
  H85 : id_addrval' (Vptr (v'15, Int.zero)) OSEventTbl OS_EVENT = Some v'38
)(
  H57 : 0 <= Int.unsigned v'53
)(
  H65 : Int.unsigned v'53 < 64
)(
  H1 : Int.unsigned v'53 <= 255
)(
  H : Int.unsigned v'53 < 64
)(
  H0 : Int.unsigned v'53 <> 63
)(
  H13 : nth_val' (Z.to_nat (Int.unsigned v'53)) priotbl =
        Vptr (todelblock, Int.zero)
)(
  H47 : Int.unsigned v'53 <= 255
)(
  H49 : Int.unsigned (v'53 >>ᵢ $ 3) <= 255
)(
  H50 : Int.unsigned ($ 1<<ᵢ(v'53&ᵢ$ 7)) <= 255
)(
  H48 : Int.unsigned (v'53&ᵢ$ 7) <= 255
)(
  H51 : Int.unsigned ($ 1<<ᵢ(v'53 >>ᵢ $ 3)) <= 255
)(
  H60 : nth_val' (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'30 = Vint32 v'41
)(
  H63 : length
          (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'30
             (val_inj
                (and (Vint32 v'41) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7))))))) =
        ∘ OS_RDY_TBL_SIZE
)(
  H67 : RL_Tbl_Grp_P
          (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'30
             (val_inj
                (and (Vint32 v'41) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7)))))))
          (Vint32 v'40)
)(
  H68 : forall x : int32,
        prio_in_tbl x v'30 ->
        Int.eq x v'53 = false ->
        prio_in_tbl x
          (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'30
             (val_inj
                (and (Vint32 v'41) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7)))))))
)(
  H69 : prio_not_in_tbl v'53
          (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'30
             (val_inj
                (and (Vint32 v'41) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7)))))))
)(
  H70 : array_type_vallist_match Int8u
          (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'30
             (val_inj
                (and (Vint32 v'41) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7)))))))
)(
  H23 : TcbMod.get tcbmap (todelblock, Int.zero) =
        Some (v'53, wait (hle2wait x (v'15, Int.zero)) i13, x0)
)(
  H22 : TcbJoin (todelblock, Int.zero)
          (v'53, wait (hle2wait x (v'15, Int.zero)) i13, x0) x13 v'19
)(
  H86 : nth_val' (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'37 = Vint32 v'51
)(
  H95 : length
          (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'37
             (val_inj
                (and (Vint32 v'51) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7))))))) =
        ∘ OS_RDY_TBL_SIZE
)(
  H97 : RL_Tbl_Grp_P
          (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'37
             (val_inj
                (and (Vint32 v'51) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7)))))))
          (Vint32 v'50)
)(
  H98 : forall x : int32,
        prio_in_tbl x v'37 ->
        Int.eq x v'53 = false ->
        prio_in_tbl x
          (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'37
             (val_inj
                (and (Vint32 v'51) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7)))))))
)(
  H99 : prio_not_in_tbl v'53
          (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'37
             (val_inj
                (and (Vint32 v'51) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7)))))))
)(
  H100 : array_type_vallist_match Int8u
           (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'37
              (val_inj
                 (and (Vint32 v'51) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7)))))))
)(
  v'7 : val
)(
  H78 : array_type_vallist_match OS_TCB ∗ priotbl
)(
  H106 : length priotbl = 64%nat
)(
  H94 : RL_RTbl_PrioTbl_P v'30 priotbl vhold
)(
  H105 : R_PrioTbl_P priotbl tcbmap vhold
)(
  v'14 : val
)(
  v'16 : block
)(
  x34 x35 : val
)(
  H110 : isptr x35
)(
  H111 : isptr x34
)(
  i15 : int32
)(
  H112 : Int.unsigned i15 <= 65535
)(
  i14 : int32
)(
  H113 : Int.unsigned i14 <= 255
)(
  i12 : int32
)(
  H114 : Int.unsigned i12 <= 255
)(
  i11 : int32
)(
  H115 : Int.unsigned i11 <= 255
)(
  i10 : int32
)(
  H116 : Int.unsigned i10 <= 255
)(
  i9 : int32
)(
  H117 : Int.unsigned i9 <= 255
)(
  i : int32
)(
  H118 : Int.unsigned i <= 255
)(
  H109 : isptr (Vptr (todelblock, Int.zero))
)(
  H108 : isptr v'14
)(
  H41 : isptr (Vptr (v'16, Int.zero))
)(
  H53 : R_TCB_Status_P
          (Vptr (v'16, Int.zero)
           :: v'13
              :: Vptr (v'15, Int.zero)
                 :: x0
                    :: Vint32 i13
                       :: Vint32 x21
                          :: Vint32 v'53
                             :: Vint32 (v'53&ᵢ$ 7)
                                :: Vint32 (v'53 >>ᵢ $ 3)
                                   :: Vint32 ($ 1<<ᵢ(v'53&ᵢ$ 7))
                                      :: Vint32 ($ 1<<ᵢ(v'53 >>ᵢ $ 3)) :: nil)
          v'30 (v'53, wait (hle2wait x (v'15, Int.zero)) i13, x0)
)(
  H107 : Vptr (v'16, Int.zero) <> Vnull
)(
  H52 : TCBList_P (Vptr (v'16, Int.zero))
          ((v'14
            :: Vptr (todelblock, Int.zero)
               :: x35
                  :: x34
                     :: Vint32 i15
                        :: Vint32 i14
                           :: Vint32 i12
                              :: Vint32 i11
                                 :: Vint32 i10
                                    :: Vint32 i9 :: Vint32 i :: nil) :: l2')
          v'30 x13
)(
  H24 : ptr_in_tcbdllseg (Vptr (cur_tcb_blk, Int.zero)) v'9
          (l1' ++
           (Vptr (v'16, Int.zero)
            :: v'13
               :: Vptr (v'15, Int.zero)
                  :: x0
                     :: Vint32 i13
                        :: Vint32 x21
                           :: Vint32 v'53
                              :: Vint32 (v'53&ᵢ$ 7)
                                 :: Vint32 (v'53 >>ᵢ $ 3)
                                    :: Vint32 ($ 1<<ᵢ(v'53&ᵢ$ 7))
                                       :: Vint32 ($ 1<<ᵢ(v'53 >>ᵢ $ 3))
                                          :: nil)
           :: (v'14
               :: Vptr (todelblock, Int.zero)
                  :: x35
                     :: x34
                        :: Vint32 i15
                           :: Vint32 i14
                              :: Vint32 i12
                                 :: Vint32 i11
                                    :: Vint32 i10
                                       :: Vint32 i9 :: Vint32 i :: nil)
              :: l2')
)(
  Heqtcblst : ProtectWrapper
                (l1' ++
                 (Vptr (v'16, Int.zero)
                  :: v'13
                     :: Vptr (v'15, Int.zero)
                        :: x0
                           :: Vint32 i13
                              :: Vint32 x21
                                 :: Vint32 v'53
                                    :: Vint32 (v'53&ᵢ$ 7)
                                       :: Vint32 (v'53 >>ᵢ $ 3)
                                          :: Vint32 ($ 1<<ᵢ(v'53&ᵢ$ 7))
                                             :: Vint32 ($ 1<<ᵢ(v'53 >>ᵢ $ 3))
                                                :: nil)
                 :: (v'14
                     :: Vptr (todelblock, Int.zero)
                        :: x35
                           :: x34
                              :: Vint32 i15
                                 :: Vint32 i14
                                    :: Vint32 i12
                                       :: Vint32 i11
                                          :: Vint32 i10
                                             :: Vint32 i9 :: Vint32 i :: nil)
                    :: l2' =
                 l1 ++
                 (x20
                  :: x19
                     :: x18
                        :: x17
                           :: Vint32 i6
                              :: Vint32 i5
                                 :: Vint32 i4
                                    :: Vint32 i3
                                       :: Vint32 i2
                                          :: Vint32 i1 :: Vint32 i0 :: nil)
                 :: l2)
)(
  H26 : ptr_in_tcbdllseg (Vptr (todelblock, Int.zero)) v'9
          (l1' ++
           (Vptr (v'16, Int.zero)
            :: v'13
               :: Vptr (v'15, Int.zero)
                  :: x0
                     :: Vint32 i13
                        :: Vint32 x21
                           :: Vint32 v'53
                              :: Vint32 (v'53&ᵢ$ 7)
                                 :: Vint32 (v'53 >>ᵢ $ 3)
                                    :: Vint32 ($ 1<<ᵢ(v'53&ᵢ$ 7))
                                       :: Vint32 ($ 1<<ᵢ(v'53 >>ᵢ $ 3))
                                          :: nil)
           :: (v'14
               :: Vptr (todelblock, Int.zero)
                  :: x35
                     :: x34
                        :: Vint32 i15
                           :: Vint32 i14
                              :: Vint32 i12
                                 :: Vint32 i11
                                    :: Vint32 i10
                                       :: Vint32 i9 :: Vint32 i :: nil)
              :: l2')
)(
  H25 : TCBList_P v'9
          (l1' ++
           (Vptr (v'16, Int.zero)
            :: v'13
               :: Vptr (v'15, Int.zero)
                  :: x0
                     :: Vint32 i13
                        :: Vint32 x21
                           :: Vint32 v'53
                              :: Vint32 (v'53&ᵢ$ 7)
                                 :: Vint32 (v'53 >>ᵢ $ 3)
                                    :: Vint32 ($ 1<<ᵢ(v'53&ᵢ$ 7))
                                       :: Vint32 ($ 1<<ᵢ(v'53 >>ᵢ $ 3))
                                          :: nil)
           :: (v'14
               :: Vptr (todelblock, Int.zero)
                  :: x35
                     :: x34
                        :: Vint32 i15
                           :: Vint32 i14
                              :: Vint32 i12
                                 :: Vint32 i11
                                    :: Vint32 i10
                                       :: Vint32 i9 :: Vint32 i :: nil)
              :: l2') v'30 tcbmap
)(
  backup : TCBList_P (Vptr (todelblock, Int.zero))
             ((Vptr (v'16, Int.zero)
               :: v'13
                  :: Vptr (v'15, Int.zero)
                     :: x0
                        :: Vint32 i13
                           :: Vint32 x21
                              :: Vint32 v'53
                                 :: Vint32 (v'53&ᵢ$ 7)
                                    :: Vint32 (v'53 >>ᵢ $ 3)
                                       :: Vint32 ($ 1<<ᵢ(v'53&ᵢ$ 7))
                                          :: Vint32 ($ 1<<ᵢ(v'53 >>ᵢ $ 3))
                                             :: nil)
              :: (v'14
                  :: Vptr (todelblock, Int.zero)
                     :: x35
                        :: x34
                           :: Vint32 i15
                              :: Vint32 i14
                                 :: Vint32 i12
                                    :: Vint32 i11
                                       :: Vint32 i10
                                          :: Vint32 i9 :: Vint32 i :: nil)
                 :: l2') v'30 v'19
             ),
   {|OS_spec, GetHPrio, OSLInv, I,
   fun v : option val =>
   ( <|| END v ||>  **
    p_local OSLInv (cur_tcb_blk, Int.zero) init_lg **
    ((EX v0 : val, LV prio @ Int8u |-> v0) **
     (EX v0 : val, LV pevent @ OS_EVENT ∗ |-> v0) **
     (EX v0 : val, LV ptcb @ OS_TCB ∗ |-> v0) **
     (EX v0 : val, LV self @ Int8u |-> v0) **
     (EX v0 : val, LV os_code_defs.x @ OS_TCB ∗ |-> v0) ** Aemp) **
    Aie true ** Ais nil ** Acs nil ** Aisr empisr) **
   A_dom_lenv
     ((prio, Int8u)
      :: (pevent, OS_EVENT ∗)
         :: (ptcb, OS_TCB ∗)
            :: (self, Int8u) :: (os_code_defs.x, OS_TCB ∗) :: nil), Afalse|}
   |- (cur_tcb_blk, Int.zero)
   {{Astruct (v'16, Int.zero) OS_TCB_flag
       (v'14
        :: Vptr (todelblock, Int.zero)
           :: x35
              :: x34
                 :: Vint32 i15
                    :: Vint32 i14
                       :: Vint32 i12
                          :: Vint32 i11
                             :: Vint32 i10 :: Vint32 i9 :: Vint32 i :: nil) **
     dllseg v'14 (Vptr (v'16, Int.zero)) v'12 Vnull l2' OS_TCB_flag
       (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
       <||        taskdel_clear_waitls_bit (|Vint32 v'53 :: nil|);;
spec_del (Vint32 v'53);;
       isched;; END Some (V$ NO_ERR) ||>  **
     A_dom_lenv
       ((prio, Int8u)
        :: (pevent, OS_EVENT ∗)
           :: (ptcb, OS_TCB ∗)
              :: (self, Int8u) :: (os_code_defs.x, OS_TCB ∗) :: nil) **
     GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64)
       (update_nth_val (Z.to_nat (Int.unsigned v'53)) priotbl Vnull) **
     PV vhold @ Int8u |-> v'7 **
     LV ptcb @ OS_TCB ∗ |-> Vptr (todelblock, Int.zero) **
     Astruct (todelblock, Int.zero) OS_TCB_flag
       (Vptr (v'16, Int.zero)
        :: v'13
           :: Vptr (v'15, Int.zero)
              :: x0
                 :: V$ 0
                    :: V$ OS_STAT_RDY
                       :: Vint32 v'53
                          :: Vint32 (v'53&ᵢ$ 7)
                             :: Vint32 (v'53 >>ᵢ $ 3)
                                :: Vint32 ($ 1<<ᵢ(v'53&ᵢ$ 7))
                                   :: Vint32 ($ 1<<ᵢ(v'53 >>ᵢ $ 3)) :: nil) **
     Aarray v'38 (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
       (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'37
          (val_inj (and (Vint32 v'51) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7))))))) **
     PV (v'15, Int.zero +ᵢ  $ 1) @ Int8u |-> Vint32 v'50 **
     PV (v'15, Int.zero) @ Int8u |-> Vint32 i7 **
     PV (v'15,
        (Int.zero +ᵢ  $ Z.of_nat (typelen Int8u)) +ᵢ
        $ Z.of_nat (typelen Int8u)) @ Int16u |-> Vint32 i8 **
     PV (v'15,
        ((Int.zero +ᵢ  $ Z.of_nat (typelen Int8u)) +ᵢ
         $ Z.of_nat (typelen Int8u)) +ᵢ  $ Z.of_nat (typelen Int16u)) @
     (Void) ∗ |-> x29 **
     PV (v'15,
        ((((Int.zero +ᵢ  $ Z.of_nat (typelen Int8u)) +ᵢ
           $ Z.of_nat (typelen Int8u)) +ᵢ  $ Z.of_nat (typelen Int16u)) +ᵢ
         $ Z.of_nat (typelen (Void) ∗)) +ᵢ
        $ Z.of_nat (typelen (Tarray Int8u ∘ OS_EVENT_TBL_SIZE))) @
     STRUCT os_event ⋆ |-> v'6 **
     AEventData
       (Vint32 i7 :: Vint32 v'28 :: Vint32 i8 :: x29 :: x30 :: v'6 :: nil)
       x22 **
     evsllseg v'6 Vnull x15 x24 **
     evsllseg v'8 (Vptr (v'15, Int.zero)) x11 x23 **
     GV OSEventList @ OS_EVENT ∗ |-> v'8 **
     HECBList ecbmap **
     HTCBList tcbmap **
     HTime v'18 **
     HCurTCB (cur_tcb_blk, Int.zero) **
     LV pevent @ OS_EVENT ∗ |-> Vptr (v'15, Int.zero) **
     GV OSRdyGrp @ Int8u |-> Vint32 v'40 **
     GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
       (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'30
          (val_inj (and (Vint32 v'41) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7))))))) **
     dllseg v'9 Vnull v'13 (Vptr (todelblock, Int.zero)) l1' OS_TCB_flag
       (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
     GV OSTCBList @ OS_TCB ∗ |-> v'9 **
     GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
     Aie false **
     Ais nil **
     Acs (true :: nil) **
     Aisr empisr **
     tcbdllflag v'9
       (l1' ++
        (Vptr (v'16, Int.zero)
         :: v'13
            :: Vptr (v'15, Int.zero)
               :: x0
                  :: Vint32 i13
                     :: Vint32 x21
                        :: Vint32 v'53
                           :: Vint32 (v'53&ᵢ$ 7)
                              :: Vint32 (v'53 >>ᵢ $ 3)
                                 :: Vint32 ($ 1<<ᵢ(v'53&ᵢ$ 7))
                                    :: Vint32 ($ 1<<ᵢ(v'53 >>ᵢ $ 3)) :: nil)
        :: (v'14
            :: Vptr (todelblock, Int.zero)
               :: x35
                  :: x34
                     :: Vint32 i15
                        :: Vint32 i14
                           :: Vint32 i12
                              :: Vint32 i11
                                 :: Vint32 i10
                                    :: Vint32 i9 :: Vint32 i :: nil) :: l2') **
     G& OSPlaceHolder @ Int8u == vhold **
     A_isr_is_prop **
     p_local OSLInv (cur_tcb_blk, Int.zero) init_lg **
     LV self @ Int8u |-> (V$ 0) **
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
     LV os_code_defs.x @ OS_TCB ∗ |-> v'2 ** LV prio @ Int8u |-> Vint32 v'53}} 
ptcb ′ → OSTCBEventPtr =ₑ NULL;ₛ
   sif (ptcb ′ → OSTCBPrev ==ₑ NULL)
        (os_code_defs.x ′ =ₑ ptcb ′ → OSTCBNext;ₛ
        os_code_defs.x ′ → OSTCBPrev =ₑ NULL;ₛ
        OSTCBList ′ =ₑ os_code_defs.x ′)
       (os_code_defs.x ′ =ₑ ptcb ′ → OSTCBPrev;ₛ
            os_code_defs.x ′ → OSTCBNext =ₑ ptcb ′ → OSTCBNext;ₛ
            os_code_defs.x ′ =ₑ ptcb ′ → OSTCBNext;ₛ
            os_code_defs.x ′ → OSTCBPrev =ₑ ptcb ′ → OSTCBPrev)   ;ₛ
   ptcb ′ → OSTCBNext =ₑ OSTCBFreeList ′;ₛ
   OSTCBFreeList ′ =ₑ ptcb ′;ₛ
   os_task.STKFREE ptcb ′;ₛ
   ptcb ′ → OSTCBflag =ₑ ′ 0;ₛ

   EXIT_CRITICAL;ₛ
   OS_Sched (­);ₛ
                  RETURN ′ OS_NO_ERR {{Afalse}}.
Proof.
  intros.
  Set Printing Depth 999.
  hoare forward.

  hoare abscsq.
  apply noabs_oslinv.
  eapply absimp_taskdel_cler_waitls_bit.
  go.
  exact H23.
  go.
  go.
  go.
  
  destruct l1'.
  hoare_assert_pure (v'13 = Vnull). 
  unfold1 dllseg in H101.
  sep normal in H101.
  sep destruct H101.
  sep split in H101.
  rewrite H103; reflexivity.
  
  (* v'13 is null, deleting first tcb node *)
  {
    hoare_split_pure_all.
    subst v'13.

    hoare forward.
    (* intro; tryfalse. *)
    go.
    (* intro; tryfalse. *)

    Focus 2.
    hoare_split_pure_all; false.
    clear -H101; simpljoin.
    destruct H101; tryfalse.

    hoare unfold.
    hoare forward.
    (* intro; tryfalse. *)
    go.
    hoare forward.
    hoare forward.

    hoare forward.

    Focus 2.
    hoare_split_pure_all.
    false.
    clear -H101; destruct H101; tryfalse.


    hoare unfold.
    unfold AOSTCBFreeList.
    hoare unfold.
    hoare forward.

    eapply isptr_is_definitely_ptr.
    eapply sll_head_isptr.
    instantiate (5:=s).
    sep cancel sll.
    go.

    hoare forward.
    (* Local Open Scope list_scope. *)

    (* hoare abscsq.
     * apply noabs_oslinv.
     * eapply absimp_taskdel_succ.
     * go.
     * 2: eauto.
     * exact kitty. *)
    (*************)
    clear H101 H102 H103.
    assert (todelblock = cur_tcb_blk \/ todelblock <> cur_tcb_blk) by tauto. 
    destruct H101.
    (* delete current *)
    {
      subst todelblock.
      (* unfold get in H16; simpl in H16. *)
      rewrite H23 in kitty.
      Set Printing Depth 999.
      eapply backward_rule1.
      instantiate (1:=
                     (
                       <|| sdel (Vint32 v'53 :: nil);;
(* taskdel_clear_waitls_bit (|Vint32 v'53 :: nil|);; *)
                           isched;; END Some (V$ NO_ERR) ||>  **
                           HTCBList tcbmap **
                           HCurTCB (cur_tcb_blk, Int.zero) **
                           OS [ empisr, false, nil, (true::nil)] **
  (* <|| spec_del (Vint32 v'53);; isched;; END Some (V$ NO_ERR) ||>  ** *)
   A_dom_lenv
     ((prio, Int8u)
      :: (pevent, OS_EVENT ∗)
         :: (ptcb, OS_TCB ∗)
            :: (self, Int8u) :: (os_code_defs.x, OS_TCB ∗) :: nil) **
   GV OSTCBFreeList @ OS_TCB ∗ |-> Vptr (cur_tcb_blk, Int.zero) **
   LV ptcb @ OS_TCB ∗ |-> Vptr (cur_tcb_blk, Int.zero) **
   Astruct (cur_tcb_blk, Int.zero) OS_TCB_flag
     (v'20
      :: Vnull
         :: Vnull
            :: x0
               :: V$ 0
                  :: V$ OS_STAT_RDY
                     :: Vint32 v'53
                        :: Vint32 (v'53&ᵢ$ 7)
                           :: Vint32 (v'53 >>ᵢ $ 3)
                              :: Vint32 ($ 1<<ᵢ(v'53&ᵢ$ 7))
                                 :: Vint32 ($ 1<<ᵢ(v'53 >>ᵢ $ 3)) :: nil) **
   GV OSTCBList @ OS_TCB ∗ |-> Vptr (v'16, Int.zero) **
   LV os_code_defs.x @ OS_TCB ∗ |-> Vptr (v'16, Int.zero) **
   Astruct (v'16, Int.zero) OS_TCB_flag
     (v'14
      :: Vnull
         :: x35
            :: x34
               :: Vint32 i15
                  :: Vint32 i14
                     :: Vint32 i12
                        :: Vint32 i11
                           :: Vint32 i10 :: Vint32 i9 :: Vint32 i :: nil) **
   dllseg v'14 (Vptr (v'16, Int.zero)) v'12 Vnull l2' OS_TCB_flag
     (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
   GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64)
     (update_nth_val (Z.to_nat (Int.unsigned v'53)) priotbl Vnull) **
   PV vhold @ Int8u |-> v'7 **
   Aarray v'38 (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
     (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'37
        (val_inj (and (Vint32 v'51) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7))))))) **
   PV (v'15, Int.zero +ᵢ  $ 1) @ Int8u |-> Vint32 v'50 **
   PV (v'15, Int.zero) @ Int8u |-> Vint32 i7 **
   PV (v'15,
      (Int.zero +ᵢ  $ Z.of_nat (typelen Int8u)) +ᵢ
      $ Z.of_nat (typelen Int8u)) @ Int16u |-> Vint32 i8 **
   PV (v'15,
      ((Int.zero +ᵢ  $ Z.of_nat (typelen Int8u)) +ᵢ
       $ Z.of_nat (typelen Int8u)) +ᵢ  $ Z.of_nat (typelen Int16u)) @
   (Void) ∗ |-> x29 **
   PV (v'15,
      ((((Int.zero +ᵢ  $ Z.of_nat (typelen Int8u)) +ᵢ
         $ Z.of_nat (typelen Int8u)) +ᵢ  $ Z.of_nat (typelen Int16u)) +ᵢ
       $ Z.of_nat (typelen (Void) ∗)) +ᵢ
      $ Z.of_nat (typelen (Tarray Int8u ∘ OS_EVENT_TBL_SIZE))) @
   STRUCT os_event ⋆ |-> v'6 **
   AEventData
     (Vint32 i7 :: Vint32 v'28 :: Vint32 i8 :: x29 :: x30 :: v'6 :: nil) x22 **
   evsllseg v'6 Vnull x15 x24 **
   evsllseg v'8 (Vptr (v'15, Int.zero)) x11 x23 **
   GV OSEventList @ OS_EVENT ∗ |-> v'8 **
   HECBList
   (EcbMod.set ecbmap (v'15, Int.zero)
        (x, remove_tid (cur_tcb_blk, Int.zero) x14))
   (* ecbmap *)
   **
   (* HTCBList tcbmap ** *)
   HTime v'18 **
   (* HCurTCB (cur_tcb_blk, Int.zero) ** *)
   LV pevent @ OS_EVENT ∗ |-> Vptr (v'15, Int.zero) **
   GV OSRdyGrp @ Int8u |-> Vint32 v'40 **
   GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
     (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'30
        (val_inj (and (Vint32 v'41) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7))))))) **
   dllseg v'9 Vnull Vnull (Vptr (cur_tcb_blk, Int.zero)) nil OS_TCB_flag
     (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
   GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
   (* Aie false ** *)
   (* Ais nil ** *)
   (* Acs (true :: nil) ** *)
   (* Aisr empisr ** *)
   tcbdllflag v'9
     (nil ++
      (Vptr (v'16, Int.zero)
       :: Vnull
          :: Vptr (v'15, Int.zero)
             :: x0
                :: Vint32 i13
                   :: Vint32 x21
                      :: Vint32 v'53
                         :: Vint32 (v'53&ᵢ$ 7)
                            :: Vint32 (v'53 >>ᵢ $ 3)
                               :: Vint32 ($ 1<<ᵢ(v'53&ᵢ$ 7))
                                  :: Vint32 ($ 1<<ᵢ(v'53 >>ᵢ $ 3)) :: nil)
      :: (v'14
          :: Vptr (cur_tcb_blk, Int.zero)
             :: x35
                :: x34
                   :: Vint32 i15
                      :: Vint32 i14
                         :: Vint32 i12
                            :: Vint32 i11
                               :: Vint32 i10 :: Vint32 i9 :: Vint32 i :: nil)
         :: l2') **
   G& OSPlaceHolder @ Int8u == vhold **
   (* A_isr_is_prop ** *)
   p_local OSLInv (cur_tcb_blk, Int.zero) init_lg **
   LV self @ Int8u |-> (V$ 0) **
   AOSEventFreeList v'3 **
   AOSQFreeList v'4 **
   AOSQFreeBlk v'5 **
   AOSMapTbl **
   AOSUnMapTbl **
   AOSIntNesting **
   sll v'20 v'21 OS_TCB_flag (fun vl : vallist => nth_val 0 vl) **
   sllfreeflag v'20 v'21 **
   AOSTime (Vint32 v'18) **
   AGVars ** atoy_inv' ** LV prio @ Int8u |-> Vint32 v'53 
                           (* Aisr empisr **
                            * Aie false **
                            * Ais nil **
                            * Acs (true :: nil) ** *)
                  )).
      clear.
      intro; intros.
      sep lifts (4:: 6::nil)%nat. 
      eapply elim_a_isr_is_prop.
      sep cancel Aisr.
      sep cancel Ais.
      sep cancel Acs.
      sep cancel Aie.
      sep pauto.
      unfold os_task.STKFREE.

      assert (exists mmm, TcbJoin (cur_tcb_blk, Int.zero) (v'53, wait (hle2wait x (v'15, Int.zero)) i13 , x0) mmm tcbmap).
      apply tcb_get_join.
      unfold get, sig, join in *; simpl in *.
      unfold get, sig, join in *; simpl in *.
      go.

      destruct H101 as (tcbmap_left & tcbmapleft_join_hyp).


      eapply seq_rule.
      eapply  derive_delself_rule.

        
      apply goodlinv.
       (* goodlinv *)
      go.
      unfold AEventData.
      destruct x22; go.
      unfold p_local.
      unfold CurTid; unfold LINV.
      unfold OSLInv.
      go.

      exact tcbmapleft_join_hyp.
      intro; intros.
      split.
      sep_get_rv.
      unfold p_local in H101.
      unfold CurLINV.
      sep pauto.
      sep cancel LINV.
      simpl; auto 1.

      rewrite app_nil_l.
      unfold1 tcbdllflag.
      unfold1 dllsegflag.
      hoare unfold.
      hoare lift 4%nat pre.
      unfold p_local at 2.
      unfold OSLInv at 3.
      unfold LINV.
      unfold1 dllseg.
      hoare unfold.
      eapply backward_rule1.
      intro; intros.
      (* Print Ltac sep_combine. *)
      sep combine ( get_off_addr (cur_tcb_blk, Int.zero) ($ 24)  ) in H102.
      eauto.

      hoare lift 2%nat pre.
      eapply seq_rule.
      eapply assign_rule'.
      Focus 2.

      intro; intros.
      split.
      eapply field_asrt_impl.
      Focus 3.
      sep cancel 12%nat 1%nat.
      eauto.
      reflexivity.
      reflexivity.
      sep get rv.
      eapply eq_int; auto.

      intro; intros.
      unfold p_local, OSLInv.
      sep pauto.
      unfold LINV.
      sep pauto.
      sep cancel 49%nat 1%nat.
      simpl; auto.
      splits; eauto.
      unfolds; auto.
      

      eapply backward_rule1.
      intro; intros.
      sep lifts (7::9::nil)%nat in H102.
      eapply add_a_isr_is_prop in H102.
      eauto.
      hoare lift 4%nat pre.
      eapply seq_rule.

      eapply excrit1_rule'_ISnil_ISRemp''.
      intro.
      intros.
      sep cancel atoy_inv'.
      sep cancel Aisr.
      sep cancel Aie.
      sep cancel Ais.
      sep cancel Acs.
      unfold p_local, OSLInv.
      unfold LINV.
      sep pauto.
      sep cancel 2%nat 1%nat.
      sep cancel CurTid.
      unfold OSInv.
      sep pauto.
      sep cancel AOSEventFreeList.
      sep cancel AOSQFreeList.
      sep cancel AOSQFreeBlk.
      unfold AECBList.

      instantiate (17 := (x11 ++ (Vint32 i7 :: Vint32 v'50 :: Vint32 i8 :: x29 :: x30 :: v'6 :: nil,
                                 (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'37
                                                 (val_inj
                                                    (and (Vint32 v'51) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7)))))))
                                ) :: x15)).
      instantiate (16 :=(x23 ++ x22 :: x24) ).
      sep pauto.
      eapply evsllseg_merge.
      eapply (ecblistp_length_eq_1 _ _ _ _ _ _ H80).
      eapply (ecblistp_length_eq_1 _ _ _ _ _ _ H81).

      unfold1 evsllseg .
      sep pauto.
      unfold AEventNode.
      sep cancel evsllseg.
      sep cancel evsllseg.
      unfold AOSEvent.
      unfold node.
      unfold AOSEventTbl.
      sep pauto.
      sep cancel Aarray.
      sep lift 2%nat.
      eapply AED_changegrp.
      sep cancel AEventData.
      unfold Astruct.
      unfold OS_EVENT.
      unfold Astruct'.
      sep normal.
      sep cancel 14%nat 2%nat.
      repeat sep cancel 14%nat 1%nat.
      unfold AOSTCBPrioTbl.
      sep pauto.
      sep cancel 12%nat 1%nat.
      sep cancel 16%nat 1%nat.
      unfold AOSRdyTblGrp.
      unfold AOSRdyTbl.
      unfold AOSRdyGrp.
      sep pauto.
      unfold AOSTCBList'.
      eapply intro_or_r.
      sep pauto.
      unfold tcblist.
      instantiate ( 5 := nil).
      instantiate ( 3 := l2').
      instantiate ( 4 := (v'48
                             :: Vnull
                             :: x35
                             :: x34
                             :: Vint32 i15
                             :: Vint32 i14
                             :: Vint32 i12
                             :: Vint32 i11
                             :: Vint32 i10
                             :: Vint32 i9 :: Vint32 i :: nil)).
      (* instantiate (x1 := (nil ++ (v'48
       *                               :: Vnull
       *                               :: x35
       *                               :: x34
       *                               :: Vint32 i15
       *                               :: Vint32 i14
       *                               :: Vint32 i12
       *                               :: Vint32 i11
       *                               :: Vint32 i10
       *                               :: Vint32 i9 :: Vint32 i :: nil) :: l2')). *)
      
(* ** ac:       Print  TCB_Not_In . *)
      unfold TCB_Not_In.
      sep pauto.
      (* unfold tcbdllseg. *)
      (* SearchAbout dllseg. *)
      eapply tcbdllseg_compose.
      unfold tcbdllseg.
      unfold1 dllseg.
      unfold node.
      sep pauto.
      sep cancel 9%nat 1%nat.
      sep cancel 9%nat 1%nat.
      unfold1 tcbdllflag.
      unfold tcbdllflag in H102.
      rewrite app_nil_l.
      unfold1 dllsegflag.
      unfold1 dllsegflag in H102.
      sep normal in H102.
      sep pauto.
      (* inverts H126. *)
      sep cancel dllsegflag.
      sep cancel 2%nat 1%nat.
      (* freelist *)
      unfold AOSTCBFreeList'.
      sep pauto.
      eapply intro_or_r. 
      unfold TCBFree_Eq.
      sep pauto.
      sep cancel sll.
      sep cancel sllfreeflag.
      eauto.
      go.
      eapply isptr_is_definitely_ptr.
      eapply sll_head_isptr.
      instantiate (5:=s).
      sep cancel sll.
      go.
      unfolds.
      {
        do 6 eexists.
        splits.
        go.
        go.
        go.
        go.
        go.
        go.
        go.
        splits.
        go.
        go.
        go.
        go.
        left; auto.
      repeat tri_exists_and_solver1.
      go.
      }
      eexists; go.
           {
        unfolds in H6.
        simpljoin.
        clear -tcbmapleft_join_hyp H122.
        unfolds.
        unfolds in tcbmapleft_join_hyp.
        intro.
        simpljoin.

        unfolds in H122.
        assert (x1 <> (cur_tcb_blk, Int.zero)).
        intro.
        subst.
(* ** ac:         SearchAbout join. *)
(* ** ac:         SearchAbout TcbMod.join. *)
        eapply TcbMod.map_join_get_some .
        
        auto.
        eauto.
        2: exact H.
        (* instantiate (1:=(v'43, x, x0)). *)
        unfold get in *; simpl in *.
        unfold sig in *; simpl in *.
        eapply TcbMod.get_a_sig_a.
        go.
        unfold join, sig, get in *; simpl in *.
        assert (TcbMod.get tcbmap x1 =Some (v'53, x2, x3) ).
        go.
        assert (TcbMod.get tcbmap (cur_tcb_blk, Int.zero) =Some(v'53, wait (hle2wait x (v'15, Int.zero)) i13,
                             x0)  ).
        go.
        lets bb: H122 H0 H1 H2.
        apply bb.
        reflexivity.

      }
 
      go.
      go.
      intro;tryfalse.
      go.
      go.
      {
        split.
        rewrite ptr_in_tcblist_app.
        2: simpl; auto.
        intro.
        destruct H121.
        simpl in H121.
        exact H121.
        simpl (val_inj (get_last_tcb_ptr nil (Vptr (v'16, Int.zero)))) in H121.
        gen H121.
        eapply distinct_is_unique_second.
        3: eapply  TCBLP_imply_dictinct_list .
        2:instantiate ( 1 := (Vptr (v'16, Int.zero)
      :: Vnull
         :: Vptr (v'15, Int.zero)
            :: x0
               :: Vint32 i13
                  :: Vint32 x21
                     :: Vint32 v'53
                        :: Vint32 (v'53&ᵢ$ 7)
                           :: Vint32 (v'53 >>ᵢ $ 3)
                              :: Vint32 ($ 1<<ᵢ(v'53&ᵢ$ 7))
                              :: Vint32 ($ 1<<ᵢ(v'53 >>ᵢ $ 3)) :: nil)).
        2: go.
        instantiate (1 :=  nil).
        simpl; auto.
(* ** ac:         SearchAbout (nil ++ _). *)
        rewrite app_nil_l.

         exact backup.
         simpl.
         auto.
         eauto.
      }
       (* from tcblist_p, get they are all different? *)
      {
        rewrite app_nil_l.
        rewrite app_nil_l in H25.
(* ** ac:         Print  R_PrioTbl_P . *)
        

        eapply tcblist_p_hold_for_del_a_tcb_at_head.
        omega.
        2:go.
        2:go.
        3: exact H25.
        2: exact tcbmapleft_join_hyp.
        unfolds in H105.
        simpljoin; assumption.
      }
      split.
      assumption.
      eapply (H68 _ H55).
      clear -H0; unfold OS_IDLE_PRIO.
      csimpl OS_LOWEST_PRIO.
      int auto.

        
(* OSTimeDlyPure.update_rtbl_tcblist_hold: *)

        
        
      {
        eapply  r_priotbl_p_hold_for_del_a_tcb.
        omega.
        assumption.
        eauto 1.

        exact   tcbmapleft_join_hyp .

      }
       (* r_priotbl_p hold for deleting a tcb *)
      
{
  eapply  rtbl_remove_RL_RTbl_PrioTbl_P_hold'.
  omega.
  rewrite Int.repr_unsigned.
  reflexivity.

  rewrite Int.repr_unsigned.
  reflexivity.

  2: assumption.
  unfold nat_of_Z.
  apply nv'2nv.
  
  assumption.
  intro; tryfalse.
  
      }

       (* rl_rtbl_ptbl_p hold for deleting a tcb *)

      split.
      eapply array_type_vallist_match_hold.
      assumption.

      rewrite H7.
      clear -H; mauto.
      reflexivity.

      rewrite hoare_assign.update_nth_val_len_eq.
      assumption.
      go.
      go.
      go.
      go.
      clear -H96 H121.
      unfolds in H96.
      change Byte.max_unsigned with 255%Z in * .
      math simpl in H96.
      omega.
      go.

      {
        eapply ECBLP_hold4del_a_tcb; eauto.
        3:exact tcbmapleft_join_hyp.
        clear -H6; unfolds in H6; tauto.
        clear -H6; unfolds in H6; tauto.
      }
      
      (* admit. (* from H101 : RL_Tbl_Grp_P *)
           (update_nth_val (Z.to_nat (Int.unsigned (v'56 >>ᵢ $ 3))) v'40
              (val_inj
                 (and (Vint32 v'54) (Vint32 (Int.not ($ 1<<ᵢ(v'56&ᵢ$ 7)))))))
           (Vint32 v'53), ECBList_P holds for deleting a tcb *)

          

        
      eapply poi_is_rtep.

       

      {
        eapply poi_RHTEP_hold_for_del_a_tcb.
        assumption.
        go.
        eapply tcbmapleft_join_hyp.
        go.
        clear -H2 H61 H62; unfolds; splits; auto.
      }
        
      
       (* change to poi, *)
(* from some_pure_hyp : forall (eid : tidspec.A) (pr : int32) 
 *                     (tid0 : tid) (opr : int32) (wls : waitset),
 *                   EcbMod.get ecbmap eid =
 *                   Some (absmutexsem pr (Some (tid0, opr)), wls) ->
 *                   tid0 <> (cur_tcb_blk, Int.zero)
 * get rh_te_p hold for deleting a tcb *)
      splits; go.
      unfolds; auto.
      go.
      hoare forward.
      sep cancel Aisr.
      sep cancel Acs.
      sep cancel Ais.
      sep cancel Aie.
      sep cancel Aop.
      sep cancel p_local.
      eauto.
      unfolds; auto.
      go.
      linv_solver.
      linv_solver.

      unfold OS_SchedPost.
      unfold OS_SchedPost'.
      unfold getasrt.
      hoare forward.
      inverts H103.
      reflexivity.
    }

    (* delete some tcb other than current, at head *)
    {
      eapply backward_rule1.
      Set Printing Depth 999.
      intro; intros.
      Set Printing Depth 999.
(* ** ac:       Show. *)
      instantiate ( 1 := (
        <|| sdel (Vint32 v'53 :: nil);; isched;; END Some (V$ NO_ERR) ||>  **
                              HTCBList tcbmap **
                              HCurTCB (cur_tcb_blk, Int.zero) **
                              OS [ empisr, false, nil, (true::nil)] **

                           (* <|| spec_del (Vint32 v'53);; isched;; END Some (V$ NO_ERR) ||>  ** *)
            A_dom_lenv
              ((prio, Int8u)
               :: (pevent, OS_EVENT ∗)
                  :: (ptcb, OS_TCB ∗)
                     :: (self, Int8u) :: (os_code_defs.x, OS_TCB ∗) :: nil) **
            GV OSTCBFreeList @ OS_TCB ∗ |-> Vptr (todelblock, Int.zero) **
            LV ptcb @ OS_TCB ∗ |-> Vptr (todelblock, Int.zero) **
            Astruct (todelblock, Int.zero) OS_TCB_flag
              (v'20
               :: Vnull
                  :: Vnull
                     :: x0
                        :: V$ 0
                           :: V$ OS_STAT_RDY
                              :: Vint32 v'53
                                 :: Vint32 (v'53&ᵢ$ 7)
                                    :: Vint32 (v'53 >>ᵢ $ 3)
                                       :: Vint32 ($ 1<<ᵢ(v'53&ᵢ$ 7))
                                          :: Vint32 ($ 1<<ᵢ(v'53 >>ᵢ $ 3))
                                             :: nil) **
            GV OSTCBList @ OS_TCB ∗ |-> Vptr (v'16, Int.zero) **
            LV os_code_defs.x @ OS_TCB ∗ |-> Vptr (v'16, Int.zero) **
            Astruct (v'16, Int.zero) OS_TCB_flag
              (v'14
               :: Vnull
                  :: x35
                     :: x34
                        :: Vint32 i15
                           :: Vint32 i14
                              :: Vint32 i12
                                 :: Vint32 i11
                                    :: Vint32 i10
                                       :: Vint32 i9 :: Vint32 i :: nil) **
            dllseg v'14 (Vptr (v'16, Int.zero)) v'12 Vnull l2' OS_TCB_flag
              (fun vl : vallist => nth_val 1 vl)
              (fun vl : vallist => nth_val 0 vl) **
            GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64)
              (update_nth_val (Z.to_nat (Int.unsigned v'53)) priotbl Vnull) **
            PV vhold @ Int8u |-> v'7 **
            Aarray v'38 (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
              (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'37
                 (val_inj
                    (and (Vint32 v'51) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7))))))) **
            PV (v'15, Int.zero +ᵢ  $ 1) @ Int8u |-> Vint32 v'50 **
            PV (v'15, Int.zero) @ Int8u |-> Vint32 i7 **
            PV (v'15,
               (Int.zero +ᵢ  $ Z.of_nat (typelen Int8u)) +ᵢ
               $ Z.of_nat (typelen Int8u)) @ Int16u |-> 
            Vint32 i8 **
            PV (v'15,
               ((Int.zero +ᵢ  $ Z.of_nat (typelen Int8u)) +ᵢ
                $ Z.of_nat (typelen Int8u)) +ᵢ  $ Z.of_nat (typelen Int16u)) @
            (Void) ∗ |-> x29 **
            PV (v'15,
               ((((Int.zero +ᵢ  $ Z.of_nat (typelen Int8u)) +ᵢ
                  $ Z.of_nat (typelen Int8u)) +ᵢ  
                 $ Z.of_nat (typelen Int16u)) +ᵢ
                $ Z.of_nat (typelen (Void) ∗)) +ᵢ
               $ Z.of_nat (typelen (Tarray Int8u ∘ OS_EVENT_TBL_SIZE))) @
            STRUCT os_event ⋆ |-> v'6 **
            AEventData
              (Vint32 i7
               :: Vint32 v'28 :: Vint32 i8 :: x29 :: x30 :: v'6 :: nil) x22 **
            evsllseg v'6 Vnull x15 x24 **
            evsllseg v'8 (Vptr (v'15, Int.zero)) x11 x23 **
            GV OSEventList @ OS_EVENT ∗ |-> v'8 **
            HECBList (EcbMod.set ecbmap (v'15, Int.zero)
      (x, remove_tid (todelblock, Int.zero) x14))

            **
            (* HTCBList tcbmap ** *)
            HTime v'18 **
            (* HCurTCB (cur_tcb_blk, Int.zero) ** *)
            LV pevent @ OS_EVENT ∗ |-> Vptr (v'15, Int.zero) **
            GV OSRdyGrp @ Int8u |-> Vint32 v'40 **
            GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
              (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'30
                 (val_inj
                    (and (Vint32 v'41) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7))))))) **
            dllseg v'9 Vnull Vnull (Vptr (todelblock, Int.zero)) nil
              OS_TCB_flag (fun vl : vallist => nth_val 1 vl)
              (fun vl : vallist => nth_val 0 vl) **
            GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
            (* Aie false ** *)
            (* Ais nil ** *)
            (* Acs (true :: nil) ** *)
            (* Aisr empisr ** *)
            tcbdllflag v'9
              (nil ++
               (Vptr (v'16, Int.zero)
                :: Vnull
                   :: Vptr (v'15, Int.zero)
                      :: x0
                         :: Vint32 i13
                            :: Vint32 x21
                               :: Vint32 v'53
                                  :: Vint32 (v'53&ᵢ$ 7)
                                     :: Vint32 (v'53 >>ᵢ $ 3)
                                        :: Vint32 ($ 1<<ᵢ(v'53&ᵢ$ 7))
                                           :: Vint32 ($ 1<<ᵢ(v'53 >>ᵢ $ 3))
                                              :: nil)
               :: (v'14
                   :: Vptr (todelblock, Int.zero)
                      :: x35
                         :: x34
                            :: Vint32 i15
                               :: Vint32 i14
                                  :: Vint32 i12
                                     :: Vint32 i11
                                        :: Vint32 i10
                                           :: Vint32 i9 :: Vint32 i :: nil)
                  :: l2') **
            G& OSPlaceHolder @ Int8u == vhold **
            (* A_isr_is_prop ** *)
            p_local OSLInv (cur_tcb_blk, Int.zero) init_lg **
            LV self @ Int8u |-> (V$ 0) **
            AOSEventFreeList v'3 **
            AOSQFreeList v'4 **
            AOSQFreeBlk v'5 **
            AOSMapTbl **
            AOSUnMapTbl **
            AOSIntNesting **
            sll v'20 v'21 OS_TCB_flag (fun vl : vallist => nth_val 0 vl) **
            sllfreeflag v'20 v'21 **
            AOSTime (Vint32 v'18) **
            AGVars ** atoy_inv' ** LV prio @ Int8u |-> Vint32 v'53
                        )).
                        (*                         HECBList ecbmap **
                         *       HTime v'18 **
                         *       A_dom_lenv
                         *       ((prio, Int8u)
                         *          :: (pevent, OS_EVENT ∗)
                         *          :: (ptcb, OS_TCB ∗)
                         *          :: (self, Int8u) :: (os_code_defs.x, OS_TCB ∗) :: nil) **
                         *       GV OSTCBFreeList @ OS_TCB ∗ |-> Vptr (v'32, Int.zero) **
                         *       LV ptcb @ OS_TCB ∗ |-> Vptr (v'32, Int.zero) **
                         *       Astruct (v'32, Int.zero) OS_TCB_flag
                         *       (v'20
                         *          :: Vnull
                         *          :: Vptr (v'14, Int.zero)
                         *          :: x0
                         *          :: V$ 0
                         *          :: V$ OS_STAT_RDY
                         *          :: Vint32 v'56
                         *          :: Vint32 (v'56&ᵢ$ 7)
                         *          :: Vint32 (v'56 >>ᵢ $ 3)
                         *          :: Vint32 ($ 1<<ᵢ(v'56&ᵢ$ 7))
                         *          :: Vint32 ($ 1<<ᵢ(v'56 >>ᵢ $ 3))
                         *          :: nil) **
                         *       GV OSTCBList @ OS_TCB ∗ |-> Vptr (v'15, Int.zero) **
                         *       LV os_code_defs.x @ OS_TCB ∗ |-> Vptr (v'15, Int.zero) **
                         *       Astruct (v'15, Int.zero) OS_TCB_flag
                         *       (v'11
                         *          :: Vnull
                         *          :: x35
                         *          :: x34
                         *          :: Vint32 i16
                         *          :: Vint32 i15
                         *          :: Vint32 i14
                         *          :: Vint32 i12
                         *          :: Vint32 i11
                         *          :: Vint32 i10 :: Vint32 i7 :: nil) **
                         *       dllseg v'11 (Vptr (v'15, Int.zero)) v'29 Vnull l2' OS_TCB_flag
                         *       (fun vl : vallist => nth_val 1 vl)
                         *       (fun vl : vallist => nth_val 0 vl) **
                         *       GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64)
                         *       (update_nth_val (Z.to_nat (Int.unsigned v'56)) priotbl Vnull) **
                         *       PV vhold @ Int8u |-> v'7 **
                         *       Aarray v'41 (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
                         *       (update_nth_val (Z.to_nat (Int.unsigned (v'56 >>ᵢ $ 3))) v'40
                         *                       (val_inj
                         *                          (and (Vint32 v'54) (Vint32 (Int.not ($ 1<<ᵢ(v'56&ᵢ$ 7))))))) **
                         *       PV (v'14, Int.zero +ᵢ  $ 1) @ Int8u |-> Vint32 v'53 **
                         *       PV (v'14, Int.zero) @ Int8u |-> Vint32 i8 **
                         *       PV (v'14,
                         *           (Int.zero +ᵢ  $ Z.of_nat (typelen Int8u)) +ᵢ
                         *                                                        $ Z.of_nat (typelen Int8u)) @ Int16u |-> 
                         *       Vint32 i9 **
                         *       PV (v'14,
                         *           ((Int.zero +ᵢ  $ Z.of_nat (typelen Int8u)) +ᵢ
                         *                                                         $ Z.of_nat (typelen Int8u)) +ᵢ  $ Z.of_nat (typelen Int16u)) @
                         *       (Void) ∗ |-> x29 **
                         *       PV (v'14,
                         *           ((((Int.zero +ᵢ  $ Z.of_nat (typelen Int8u)) +ᵢ
                         *                                                           $ Z.of_nat (typelen Int8u)) +ᵢ  
                         *                                                                                          $ Z.of_nat (typelen Int16u)) +ᵢ
                         *                                                                                                                          $ Z.of_nat (typelen (Void) ∗)) +ᵢ
                         *                                                                                                                                                            $ Z.of_nat (typelen (Tarray Int8u ∘ OS_EVENT_TBL_SIZE))) @
                         *       STRUCT os_event ⋆ |-> v'6 **
                         *       AEventData
                         *       (Vint32 i8
                         *               :: Vint32 v'16 :: Vint32 i9 :: x29 :: x30 :: v'6 :: nil) x22 **
                         *       evsllseg v'6 Vnull x15 x24 **
                         *       evsllseg v'8 (Vptr (v'14, Int.zero)) x5 x23 **
                         *       GV OSEventList @ OS_EVENT ∗ |-> v'8 **
                         *       LV pevent @ OS_EVENT ∗ |-> Vptr (v'14, Int.zero) **
                         *       GV OSRdyGrp @ Int8u |-> Vint32 v'43 **
                         *       GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
                         *       (update_nth_val (Z.to_nat (Int.unsigned (v'56 >>ᵢ $ 3))) v'33
                         *                       (val_inj
                         *                          (and (Vint32 v'44) (Vint32 (Int.not ($ 1<<ᵢ(v'56&ᵢ$ 7))))))) **
                         *       dllseg v'9 Vnull Vnull (Vptr (v'32, Int.zero)) nil OS_TCB_flag
                         *       (fun vl : vallist => nth_val 1 vl)
                         *       (fun vl : vallist => nth_val 0 vl) **
                         *       GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
                         *                                         AOSEventFreeList v'3 **
                         *                                         AOSQFreeList v'4 **
                         *                                         AOSQFreeBlk v'5 **
                         *                                         AOSMapTbl **
                         *                                         AOSUnMapTbl **
                         *                                         G& OSPlaceHolder @ Int8u == vhold **
                         *                                                                           AOSIntNesting **
                         *                                                                           sll v'20 v'21 OS_TCB_flag (fun vl : vallist => nth_val 0 vl) **
                         *                                                                           sllfreeflag v'20 v'21 **
                         *                                                                           AOSTime (Vint32 v'18) **
                         *                                                                           AGVars **
                         *                                                                           (* A_isr_is_prop ** *)
                         *                                                                           tcbdllflag v'9
                         *                                                                           (nil ++
                         *                                                                                (Vptr (v'15, Int.zero)
                         *                                                                                      :: Vnull
                         *                                                                                      :: Vptr (v'14, Int.zero)
                         *                                                                                      :: x0
                         *                                                                                      :: Vint32 i13
                         *                                                                                      :: Vint32 x21
                         *                                                                                      :: Vint32 v'56
                         *                                                                                      :: Vint32 (v'56&ᵢ$ 7)
                         *                                                                                      :: Vint32 (v'56 >>ᵢ $ 3)
                         *                                                                                      :: Vint32 ($ 1<<ᵢ(v'56&ᵢ$ 7))
                         *                                                                                      :: Vint32 ($ 1<<ᵢ(v'56 >>ᵢ $ 3))
                         *                                                                                      :: nil)
                         *                                                                                :: (v'11
                         *                                                                                      :: Vptr (v'32, Int.zero)
                         *                                                                                      :: x35
                         *                                                                                      :: x34
                         *                                                                                      :: Vint32 i16
                         *                                                                                      :: Vint32 i15
                         *                                                                                      :: Vint32 i14
                         *                                                                                      :: Vint32 i12
                         *                                                                                      :: Vint32 i11
                         *                                                                                      :: Vint32 i10 :: Vint32 i7 :: nil)
                         *                                                                                :: l2') **
                         *                                                                           p_local OSLInv (cur_tcb_blk, Int.zero) init_lg **
                         *                                                                           (* Aisr empisr **
                         *                                                                            * Aie false **
                         *                                                                            * Ais nil **
                         *                                                                            * Acs (true :: nil) ** *)
                         *                                                                           atoy_inv' **
                         *                                                                           LV self @ Int8u |-> (V$ 0) ** LV prio @ Int8u |-> Vint32 v'56
                         *                                                                           
                         * )). *)
      sep lifts (4:: 6::nil)%nat. 
      eapply elim_a_isr_is_prop.
      sep cancel Aisr.
      sep cancel Ais.
      sep cancel Acs.
      sep cancel Aie.
      sep pauto.
      unfold os_task.STKFREE.

      assert (exists mmm, TcbJoin (todelblock, Int.zero) (v'53, wait (hle2wait x (v'15, Int.zero)) i13 , x0) mmm tcbmap).
      apply tcb_get_join.
      unfold get, sig, join in H22; simpl in H22.
      unfold get, sig, join in H22, H9; simpl in H22, H9.
      go.

      destruct H102 as (tcbmap_left & tcbmapleft_join_hyp).
      rename H101 into not_cur_hyp.


      eapply seq_rule.
      eapply  derive_delother_rule.
      apply goodlinv.
       (* goodlinv *)
      go.
      unfold AEventData.
      destruct x22; go.
      unfold p_local.
      unfold CurTid; unfold LINV.
      unfold OSLInv.
      go.
      exact tcbmapleft_join_hyp.
      clear -H3.
      unfolds in H3.
      unfolds.
      simpljoin; eauto.

      clear -not_cur_hyp.
      intro H; inverts H; apply not_cur_hyp; reflexivity.

      
      intro; intros.
      split.
      sep_get_rv.
      unfold p_local in H101.
      unfold CurLINV.
      sep pauto.
      sep cancel LINV.
      simpl; auto 1.

      rewrite app_nil_l.
      unfold1 tcbdllflag.
      unfold1 dllsegflag.
      hoare unfold.
      hoare lift 4%nat pre.
      unfold OSLInv at 3.
      unfold LINV.
      unfold1 dllseg.
      hoare unfold.
      eapply backward_rule1.
      intro; intros.
      (* Print Ltac sep_combine. *)
      sep combine ( get_off_addr (todelblock, Int.zero) ($ 24)  ) in H101.
      eauto.

      (* hoare lift 2%nat pre. *)
      hoare lift 4%nat pre.
      eapply seq_rule.
      eapply assign_rule'.
      Focus 2.

      intro; intros.
      split.
      eapply field_asrt_impl.
      Focus 3.
      sep cancel 12%nat 1%nat.
      eauto.
      reflexivity.
      reflexivity.
      sep get rv.
      eapply eq_int; auto.

      linv_solver.
      (* intro; intros.
       * unfold p_local, OSLInv.
       * sep pauto.
       * unfold LINV.
       * sep pauto.
       * sep cancel 49%nat 1%nat.
       * simpl; auto.
       * splits; eauto.
       * unfolds; auto. *)
      

      eapply backward_rule1.
      intro; intros.
      sep lifts (7::9::nil)%nat in H101.
      eapply add_a_isr_is_prop in H101.
      eauto.
      hoare lift 4%nat pre.
      eapply seq_rule.

      eapply excrit1_rule'_ISnil_ISRemp''.
      intro.
      intros.
      sep cancel atoy_inv'.
      sep cancel Aisr.
      sep cancel Aie.
      sep cancel Ais.
      sep cancel Acs.
      sep cancel p_local.
      eapply poi_OSINV_imply_OSInv.

      unfold poi_OSINV.
(*       try progress snormal_3.
 *       try unfold myAconj.
 *       Ltac aaa :=
 *   let H := fresh "H" in
 *   match goal with
 *     | |- _ |= EX _ , _ =>
 *       eapply aexists_prop;
 *         [intros ? H; try progress aaa; exact H | idtac]
 *     | |- _ |= _ => idtac
 *   end.
 *       aaa.
 * Ltac aaa' :=
 *   let s := fresh in
 *   let H := fresh in
 *   match goal with
 *     | |- ?s' |= ?A => 
 *           let t := toTree A in
 *           pose (ssimplI t) as H;
 *             cbv [asrtTree_to_list asrtTree_to_list' listsimpl listsimplA listsimplB
 *                  myAppAsrtTree list_to_asrtTree unTree] in H;
 *             apply H; clear H;
 *             try unfold myAconj
 *     | _ => fail
 *   end.
 * aaa'.
 * assert (   s
 *    |= EX (y y0 y1 : list vallist) (y2 : list EventData)
 *       (y3 : list os_inv.EventCtr) (y4 : vallist) (y5 : val) 
 *       (y6 : vallist) (y7 : val) (y8 : list vallist) 
 *       (y9 : EcbMod.map) (y10 : TcbMod.map) (y11 : int32) 
 *       (y12 y13 : addrval) (y14 : val) (y15 : list vallist),
 *       (AOSEventFreeList y **
 *        AOSQFreeList y0 **
 *        AOSQFreeBlk y1 **
 *        AECBList y3 y2 y9 y10 **
 *        AOSMapTbl **
 *        AOSUnMapTbl **
 *        AOSTCBPrioTbl y4 y6 y10 y13 **
 *        AOSIntNesting **
 *        poi_AOSTCBList y5 y10 y6 y12 y8 y14 **
 *        AOSTCBFreeList' y14 y15 y12 **
 *        AOSRdyTblGrp y6 y7 **
 *        AOSTime (Vint32 y11) **
 *        HECBList y9 **
 *        HTCBList y10 **
 *        HTime y11 **
 *        HCurTCB y12 **
 *        AGVars ** [|RH_TCBList_ECBList_P y9 y10 y12|] ** A_isr_is_prop) ).
 * sep normal.
 * sep eexists.
 * 
 *       ssimpl.
 *       Print OSInv.
 *       sep semiauto.
 *       sep pauto. *)
      sep pauto.
      sep cancel AOSEventFreeList.
      sep cancel AOSQFreeList.
      sep cancel AOSQFreeBlk.
      unfold AECBList.
      instantiate (14 := (x11 ++ (Vint32 i7 :: Vint32 v'50 :: Vint32 i8 :: x29 :: x30 :: v'6 :: nil,
                                 (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'37
                                                 (val_inj
                                                    (and (Vint32 v'51) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7)))))))
                                ) :: x15)).
      instantiate (13 :=(x23 ++ x22 :: x24) ).

      (* instantiate (x3 := (x5 ++ (Vint32 i8 :: Vint32 v'53 :: Vint32 i9 :: x29 :: x30 :: v'6 :: nil,
       *                            (update_nth_val (Z.to_nat (Int.unsigned (v'56 >>ᵢ $ 3))) v'40
       *                                            (val_inj
       *                                               (and (Vint32 v'54) (Vint32 (Int.not ($ 1<<ᵢ(v'56&ᵢ$ 7)))))))
       *                           ) :: x15)).
       * instantiate (x2 :=(x23 ++ x22 :: x24) ). *)
      sep pauto.
      eapply evsllseg_merge.

      eapply (ecblistp_length_eq_1 _ _ _ _ _ _ H80).
      eapply (ecblistp_length_eq_1 _ _ _ _ _ _ H81).
      unfold1 evsllseg .
      sep pauto.
(* ** ac:       Print AEventNode. *)
      unfold AEventNode.
      sep cancel evsllseg.
      sep cancel evsllseg.
      unfold AOSEvent.
      unfold node.
      unfold AOSEventTbl.
      sep pauto.
      sep cancel Aarray.
      (* Lemma AED_changegrp:
       *   forall a grp grp' b c d e f g P,
       *     AEventData (a:: grp:: b:: c:: d:: e:: f :: nil) g **P  ==>
       *                AEventData (a:: grp' :: b :: c :: d ::e ::f ::nil) g ** P. 
       * Proof.
       *   intros.
       *   unfold AEventData in *.
       *   destruct g;
       *     sep pauto.
       * Qed.
       * 
       * Show. *)
      sep lift 2%nat.
      eapply AED_changegrp.
      sep cancel AEventData.
      unfold Astruct.
      unfold OS_EVENT.
      unfold Astruct'.
      sep normal.
      sep cancel 14%nat 2%nat.
      repeat sep cancel 14%nat 1%nat.
      unfold AOSTCBPrioTbl.
      sep pauto.
      idtac.
      idtac.
      sep cancel 12%nat 1%nat.
      sep cancel 16%nat 1%nat.
      unfold AOSRdyTblGrp.
      unfold AOSRdyTbl.
      unfold AOSRdyGrp.
      sep pauto.
      unfold poi_AOSTCBList.
      
      sep pauto.
      instantiate (4 := (
                          (v'49
                             :: Vnull
                             :: x35
                             :: x34
                             :: Vint32 i15
                             :: Vint32 i14
                             :: Vint32 i12
                             :: Vint32 i11
                             :: Vint32 i10
                             :: Vint32 i9 :: Vint32 i :: nil)
                            :: l2')).
      (* unfold tcbdllflag.
       * 
       * sep cancel dllsegflag.
       * sep cancel 1%nat 1%nat.
       * SearchAbout ptr_in_tcbdllseg.
       * 
       * 
       * 
       * 
       * 
       * sep pauto.
       * unfold tcblist.
       * instantiate ( x7 := nil).
       * instantiate ( x9 := l2').
       * instantiate ( x8 := (v'50
       *                        :: Vnull
       *                        :: x35
       *                        :: x34
       *                        :: Vint32 i16
       *                        :: Vint32 i15
       *                        :: Vint32 i14
       *                        :: Vint32 i12
       *                        :: Vint32 i11
       *                        :: Vint32 i10 :: Vint32 i7 :: nil)).
       * instantiate (x1 := (nil ++ (v'50
       *                               :: Vnull
       *                               :: x35
       *                               :: x34
       *                               :: Vint32 i16
       *                               :: Vint32 i15
       *                               :: Vint32 i14
       *                               :: Vint32 i12
       *                               :: Vint32 i11
       *                               :: Vint32 i10 :: Vint32 i7 :: nil) :: l2')).
       * 
       * Print  TCB_Not_In .
       * unfold TCB_Not_In.
       * sep pauto.
       * (* unfold tcbdllseg. *)
       * (* SearchAbout dllseg. *)
       * SearchAbout tcbdllseg.
       * eapply tcbdllseg_compose. *)
      unfold tcbdllseg.
      unfold tcbdllflag.
      unfold1 dllsegflag.
      unfold1 dllseg.
      unfold node.
      sep pauto.
      sep cancel 2%nat 1%nat.
      sep cancel dllsegflag.
      sep cancel dllseg.
      sep cancel 7%nat 1%nat.
      (* sep cancel 9%nat 1%nat.
       * sep cancel 9%nat 1%nat.
       * unfold tcbdllflag in H123.
       * rewrite app_nil_l.
       * unfold1 dllsegflag in H123.
       * sep normal in H123.
       * sep pauto.
       * (* inverts H126. *)
       * sep cancel dllsegflag.
       * sep cancel 2%nat 1%nat. *)
      (* freelist *)
      unfold AOSTCBFreeList'.
      sep pauto.
      eapply intro_or_l. 
      unfold TCBFree_Not_Eq.
      sep pauto.
      instantiate (2 := (
                           (v'20
                              :: Vnull
                              :: Vnull
                              :: x0
                              :: V$ 0
                              :: V$ OS_STAT_RDY
                              :: Vint32 v'53
                              :: Vint32 (v'53&ᵢ$ 7)
                              :: Vint32 (v'53 >>ᵢ $ 3)
                              :: Vint32 ($ 1<<ᵢ(v'53&ᵢ$ 7))
                              :: Vint32 ($ 1<<ᵢ(v'53 >>ᵢ $ 3))
                              :: nil) ::v'21
                                      
                         )).
      unfold sll.
      unfold sllfreeflag.
      unfold1 sllseg.
      unfold1 sllsegfreeflag.
      unfold node.
      unfold sll in H101.
      unfold sllfreeflag in H101.
      sep pauto.
      sep cancel sllseg.
      sep cancel sllsegfreeflag.
      
      sep cancel 1%nat 1%nat.
      sep cancel Astruct.
      eauto.
      go.
      go.
      apply isptr_is_definitely_ptr.
      eapply sllseg_head_isptr.
      instantiate (5:=s).
      sep cancel sllseg.
      eauto.

      go.
      intro; tryfalse.
      go.
      go.
      go.
      intro; tryfalse.
      {

        rewrite app_nil_l in H25.
        eapply tcblist_p_hold_for_del_a_tcb_at_head.
        omega.
        2:go.
        2:go.
        3: exact H25.
        2: exact tcbmapleft_join_hyp.
        unfolds in H105.
        simpljoin; assumption.
      }
       (* tcblist_p hold for deleting a tcb *)
      {

        clear -H24 not_cur_hyp .

        eapply ptr_in_tcbdllseg_change_head.
        Focus 2.
                eapply ptr_in_tcbdllseg_not_head.
        rewrite app_nil_l in H24.
        2: eauto.
        simpl; auto.
        intro; tryfalse.
        unfold V_OSTCBNext.
        reflexivity.
      }

      
       (* from tcblist_p, get they are all different? *)
      split.
      assumption.
      eapply (H68 _ H55).
      clear -H0; unfold OS_IDLE_PRIO.
      csimpl OS_LOWEST_PRIO.
      int auto.

      {
        eapply r_priotbl_p_hold_for_del_a_tcb.
        
        omega.
        assumption.
        eauto 1.

        exact   tcbmapleft_join_hyp .
      }
       (* r_priotbl_p hold for deleting a tcb *)
      {
        eapply  rtbl_remove_RL_RTbl_PrioTbl_P_hold'.
        omega.
        rewrite Int.repr_unsigned.
        reflexivity.

        rewrite Int.repr_unsigned.
        reflexivity.

        2: assumption.
        unfold nat_of_Z.
        apply nv'2nv.
        
        assumption.
        intro; tryfalse.
      }
       (* rl_rtbl_ptbl_p hold for deleting a tcb *)

      split.

      eapply array_type_vallist_match_hold.
      assumption.

      rewrite H7.
      clear -H; mauto.
      reflexivity.

      rewrite hoare_assign.update_nth_val_len_eq.
      assumption.
      go.
      go.
      go.
      go.
      go.
      clear -H96 H103.
      unfolds in H96.
      change Byte.max_unsigned with 255%Z in * .
      math simpl in H96.
      omega.
      go.
      {

        eapply ECBLP_hold4del_a_tcb; eauto.
        3:exact tcbmapleft_join_hyp.
        clear -H6; unfolds in H6; tauto.
        clear -H6; unfolds in H6; tauto.
        
      }
       (* from H101 : RL_Tbl_Grp_P
           (update_nth_val (Z.to_nat (Int.unsigned (v'56 >>ᵢ $ 3))) v'40
              (val_inj
                 (and (Vint32 v'54) (Vint32 (Int.not ($ 1<<ᵢ(v'56&ᵢ$ 7)))))))
           (Vint32 v'53), ECBList_P holds for deleting a tcb *)
      {

      eapply poi_is_rtep.
        
        eapply poi_RHTEP_hold_for_del_a_tcb.
        assumption.
        go.
        eapply tcbmapleft_join_hyp.
        go.
        clear -H2 H61 H62; unfolds; splits; auto.
      }
       (* change to poi,
from some_pure_hyp : forall (eid : tidspec.A) (pr : int32) 
                    (tid0 : tid) (opr : int32) (wls : waitset),
                  EcbMod.get ecbmap eid =
                  Some (absmutexsem pr (Some (tid0, opr)), wls) ->
                  tid0 <> (cur_tcb_blk, Int.zero)
get rh_te_p hold for deleting a tcb
              *)
      go.
      hoare forward.
      sep cancel Aisr.
      sep cancel Acs.
      sep cancel Ais.
      sep cancel Aie.
      sep cancel Aop.
      sep cancel p_local.
      eauto.
      unfolds; auto.
      go.
      linv_solver.
      linv_solver.

      unfold OS_SchedPost.
      unfold OS_SchedPost'.
      unfold getasrt.
      hoare forward.
      inverts H102.
      reflexivity.
      
    }
    (* delete some tcb in the middle of the tcblist *)
  }
  {
    destruct H42.
    hoare_assert_pure False.
    (* hw **)
    subst v'13.

    eapply dllseg_tail_not_null.
    instantiate (10:=s0).
    sep pauto.
    sep cancel 26%nat 1%nat.
    eauto.
    hoare unfold.
    inverts H101.

    destruct H42 as (prev_tcb_ptr & eqprev); subst v'13.
    (* rename x11 into prev_tcb_ptr. *)

    eapply backward_rule1.
    intro; intros.
    sep lift 26%nat in H42.
    rewrite dllseg_split_node_tail in H42.
    
    eauto.
    unfold node.
    hoare unfold.
    rename v'48 into prev_tcb_block.
    rename v'16 into next_tcb_block.

    hoare forward.
    (* intro; tryfalse. *)
    go.
    (* intro; tryfalse. *)
    hoare unfold.
    instantiate (1:= Afalse).
    false.

    hoare unfold.
    clear H42.
    hoare forward.
    (* intro; tryfalse. *)
    go.
    hoare forward.
    (* intro; tryfalse. *)
    go.
    
    hoare forward.
    (* intro; tryfalse. *)
    go.
    
    hoare forward.
    (* intro; tryfalse. *)
    go.

    hoare forward.
    hoare unfold.
    unfold   AOSTCBFreeList.
    hoare normal pre.
    hoare forward.
    eapply isptr_match_eq_true.
    eapply sll_head_isptr.
    instantiate (5 := s).
    sep cancel sll.
    eauto.

    hoare forward.
    assert (todelblock = cur_tcb_blk \/ todelblock <> cur_tcb_blk) by tauto. 
    destruct H102.
    (* delete current *)
    {
      subst todelblock.
      (* unfold get in H16; simpl in H16. *)
      rewrite H23 in kitty.
      (* Lemma derive_delself_rule:
       *   forall pa P  prio st msg tls' tls t e tp  aop r ri sd Spec I isr ie is cs,
       *     GoodLInvAsrt pa ->
       *     GoodFrm P ->
       *     joinsig t (prio, st, msg) tls' tls  ->
       *     P ==>  Rv e @ tp == Vptr t //\\  CurLINV pa t ->
       *     InfRules Spec sd pa I r ri 
       *              (
       *                <|| spec_del  (Vint32 prio);; aop ||>  **
       *                    Aabsdata abstcblsid (abstcblist tls) **
       *                    Aabsdata curtid (oscurt t) **
       *                    OS[isr, ie, is, cs] ** P
       *              ) 
       *              (sprim (stkfree e))
       *              (
       *                <|| aop ||>  **
       *                    Aabsdata abstcblsid (abstcblist tls') ** 
       *                    Aabsdata curtid (oscurt t) **
       *                    OS[isr, ie, is, cs]  
       *                    ** P
       *              ) t.
       * Proof.
       *   intros.
       *   eapply backward_rule1.
       *   instantiate (1:= (
       *                     <|| spec_del (Vint32 prio);; aop ||> ** P**
       *                         HTCBList tls ** HCurTCB t ** OS [isr, ie, is, cs] 
       *                         
       *                   )).
       *   intro.
       *   intros.
       *   sep pauto.
       *   eapply forward_rule2.
       *   eapply delself_rule; eauto.
       *   intro.
       *   intro.
       *   sep pauto.
       * Qed. *)
      eapply backward_rule1.
      instantiate (1:=
                     (
                       <|| sdel (Vint32 v'53 :: nil);; isched;; END Some (V$ NO_ERR) ||>  **
                           HTCBList tcbmap **
                           HCurTCB (cur_tcb_blk, Int.zero) **
                           OS [ empisr, false, nil, (true::nil)] **

  (* <|| spec_del (Vint32 v'53);; isched;; END Some (V$ NO_ERR) ||>  ** *)
   A_dom_lenv
     ((prio, Int8u)
      :: (pevent, OS_EVENT ∗)
         :: (ptcb, OS_TCB ∗)
            :: (self, Int8u) :: (os_code_defs.x, OS_TCB ∗) :: nil) **
   GV OSTCBFreeList @ OS_TCB ∗ |-> Vptr (cur_tcb_blk, Int.zero) **
   LV ptcb @ OS_TCB ∗ |-> Vptr (cur_tcb_blk, Int.zero) **
   Astruct (cur_tcb_blk, Int.zero) OS_TCB_flag
     (v'20
      :: Vptr (prev_tcb_block, Int.zero)
         :: Vnull
            :: x0
               :: V$ 0
                  :: V$ OS_STAT_RDY
                     :: Vint32 v'53
                        :: Vint32 (v'53&ᵢ$ 7)
                           :: Vint32 (v'53 >>ᵢ $ 3)
                              :: Vint32 ($ 1<<ᵢ(v'53&ᵢ$ 7))
                                 :: Vint32 ($ 1<<ᵢ(v'53 >>ᵢ $ 3)) :: nil) **
   LV os_code_defs.x @ OS_TCB ∗ |-> Vptr (next_tcb_block, Int.zero) **
   Astruct (next_tcb_block, Int.zero) OS_TCB_flag
     (v'14
      :: Vptr (prev_tcb_block, Int.zero)
         :: x35
            :: x34
               :: Vint32 i15
                  :: Vint32 i14
                     :: Vint32 i12
                        :: Vint32 i11
                           :: Vint32 i10 :: Vint32 i9 :: Vint32 i :: nil) **
   Astruct (prev_tcb_block, Int.zero) OS_TCB_flag
     (Vptr (next_tcb_block, Int.zero)
      :: v'13
         :: x36
            :: x33
               :: Vint32 i22
                  :: Vint32 i21
                     :: Vint32 i20
                        :: Vint32 i19
                           :: Vint32 i18 :: Vint32 i17 :: Vint32 i16 :: nil) **
   dllseg v'9 Vnull v'13 (Vptr (prev_tcb_block, Int.zero)) v'43 OS_TCB_flag
     (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
   dllseg v'14 (Vptr (next_tcb_block, Int.zero)) v'12 Vnull l2' OS_TCB_flag
     (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
   GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64)
     (update_nth_val (Z.to_nat (Int.unsigned v'53)) priotbl Vnull) **
   PV vhold @ Int8u |-> v'7 **
   Aarray v'38 (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
     (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'37
        (val_inj (and (Vint32 v'51) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7))))))) **
   PV (v'15, Int.zero +ᵢ  $ 1) @ Int8u |-> Vint32 v'50 **
   PV (v'15, Int.zero) @ Int8u |-> Vint32 i7 **
   PV (v'15,
      (Int.zero +ᵢ  $ Z.of_nat (typelen Int8u)) +ᵢ
      $ Z.of_nat (typelen Int8u)) @ Int16u |-> Vint32 i8 **
   PV (v'15,
      ((Int.zero +ᵢ  $ Z.of_nat (typelen Int8u)) +ᵢ
       $ Z.of_nat (typelen Int8u)) +ᵢ  $ Z.of_nat (typelen Int16u)) @
   (Void) ∗ |-> x29 **
   PV (v'15,
      ((((Int.zero +ᵢ  $ Z.of_nat (typelen Int8u)) +ᵢ
         $ Z.of_nat (typelen Int8u)) +ᵢ  $ Z.of_nat (typelen Int16u)) +ᵢ
       $ Z.of_nat (typelen (Void) ∗)) +ᵢ
      $ Z.of_nat (typelen (Tarray Int8u ∘ OS_EVENT_TBL_SIZE))) @
   STRUCT os_event ⋆ |-> v'6 **
   AEventData
     (Vint32 i7 :: Vint32 v'28 :: Vint32 i8 :: x29 :: x30 :: v'6 :: nil) x22 **
   evsllseg v'6 Vnull x15 x24 **
   evsllseg v'8 (Vptr (v'15, Int.zero)) x11 x23 **
   GV OSEventList @ OS_EVENT ∗ |-> v'8 **
   (* HECBList ecbmap ** *)

   HECBList
   (EcbMod.set ecbmap (v'15, Int.zero)
        (x, remove_tid (cur_tcb_blk, Int.zero) x14)) **
   (* HTCBList tcbmap ** *)
   HTime v'18 **
   (* HCurTCB (cur_tcb_blk, Int.zero) ** *)
   LV pevent @ OS_EVENT ∗ |-> Vptr (v'15, Int.zero) **
   GV OSRdyGrp @ Int8u |-> Vint32 v'40 **
   GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
     (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'30
        (val_inj (and (Vint32 v'41) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7))))))) **
   GV OSTCBList @ OS_TCB ∗ |-> v'9 **
   GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
   (* Aie false ** *)
   (* Ais nil ** *)
   (* Acs (true :: nil) ** *)
   (* Aisr empisr ** *)
   tcbdllflag v'9
     ((v :: l1') ++
      (Vptr (next_tcb_block, Int.zero)
       :: Vptr (prev_tcb_block, Int.zero)
          :: Vptr (v'15, Int.zero)
             :: x0
                :: Vint32 i13
                   :: Vint32 x21
                      :: Vint32 v'53
                         :: Vint32 (v'53&ᵢ$ 7)
                            :: Vint32 (v'53 >>ᵢ $ 3)
                               :: Vint32 ($ 1<<ᵢ(v'53&ᵢ$ 7))
                                  :: Vint32 ($ 1<<ᵢ(v'53 >>ᵢ $ 3)) :: nil)
      :: (v'14
          :: Vptr (cur_tcb_blk, Int.zero)
             :: x35
                :: x34
                   :: Vint32 i15
                      :: Vint32 i14
                         :: Vint32 i12
                            :: Vint32 i11
                               :: Vint32 i10 :: Vint32 i9 :: Vint32 i :: nil)
         :: l2') **
   G& OSPlaceHolder @ Int8u == vhold **
   (* A_isr_is_prop ** *)
   p_local OSLInv (cur_tcb_blk, Int.zero) init_lg **
   LV self @ Int8u |-> (V$ 0) **
   AOSEventFreeList v'3 **
   AOSQFreeList v'4 **
   AOSQFreeBlk v'5 **
   AOSMapTbl **
   AOSUnMapTbl **
   AOSIntNesting **
   sll v'20 v'21 OS_TCB_flag V_OSTCBNext **
   sllfreeflag v'20 v'21 **
   AOSTime (Vint32 v'18) **
   AGVars ** atoy_inv' ** LV prio @ Int8u |-> Vint32 v'53)).
     
      (* (* Aisr empisr **
       *  * Aie false **
       *  * Ais nil **
       *  * Acs (true :: nil) ** *)
       * HECBList ecbmap **
       * HTime v'18 **
       * A_dom_lenv
       *   ((prio, Int8u)
       *    :: (pevent, OS_EVENT ∗)
       *       :: (ptcb, OS_TCB ∗)
       *          :: (self, Int8u) :: (os_code_defs.x, OS_TCB ∗) :: nil) **
       * GV OSTCBFreeList @ OS_TCB ∗ |-> Vptr (cur_tcb_blk, Int.zero) **
       * LV ptcb @ OS_TCB ∗ |-> Vptr (cur_tcb_blk, Int.zero) **
       * Astruct (cur_tcb_blk, Int.zero) OS_TCB_flag
       *   (v'20
       *    :: Vnull
       *       :: Vptr (v'14, Int.zero)
       *          :: x0
       *             :: V$ 0
       *                :: V$ OS_STAT_RDY
       *                   :: Vint32 v'56
       *                      :: Vint32 (v'56&ᵢ$ 7)
       *                         :: Vint32 (v'56 >>ᵢ $ 3)
       *                            :: Vint32 ($ 1<<ᵢ(v'56&ᵢ$ 7))
       *                               :: Vint32 ($ 1<<ᵢ(v'56 >>ᵢ $ 3)) :: nil) **
       * GV OSTCBList @ OS_TCB ∗ |-> Vptr (v'15, Int.zero) **
       * LV os_code_defs.x @ OS_TCB ∗ |-> Vptr (v'15, Int.zero) **
       * Astruct (v'15, Int.zero) OS_TCB_flag
       *   (v'11
       *    :: Vnull
       *       :: x35
       *          :: x34
       *             :: Vint32 i16
       *                :: Vint32 i15
       *                   :: Vint32 i14
       *                      :: Vint32 i12
       *                         :: Vint32 i11 :: Vint32 i10 :: Vint32 i7 :: nil) **
       * dllseg v'11 (Vptr (v'15, Int.zero)) v'29 Vnull l2' OS_TCB_flag
       *   (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
       * GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64)
       *   (update_nth_val (Z.to_nat (Int.unsigned v'56)) priotbl Vnull) **
       * Aarray v'41 (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
       *   (update_nth_val (Z.to_nat (Int.unsigned (v'56 >>ᵢ $ 3))) v'40
       *      (val_inj (and (Vint32 v'54) (Vint32 (Int.not ($ 1<<ᵢ(v'56&ᵢ$ 7))))))) **
       * PV (v'14, Int.zero +ᵢ  $ 1) @ Int8u |-> Vint32 v'53 **
       * PV (v'14, Int.zero) @ Int8u |-> Vint32 i8 **
       * PV (v'14,
       *    (Int.zero +ᵢ  $ Z.of_nat (typelen Int8u)) +ᵢ
       *    $ Z.of_nat (typelen Int8u)) @ Int16u |-> Vint32 i9 **
       * PV (v'14,
       *    ((Int.zero +ᵢ  $ Z.of_nat (typelen Int8u)) +ᵢ
       *     $ Z.of_nat (typelen Int8u)) +ᵢ  $ Z.of_nat (typelen Int16u)) @
       * (Void) ∗ |-> x29 **
       * PV (v'14,
       *    ((((Int.zero +ᵢ  $ Z.of_nat (typelen Int8u)) +ᵢ
       *       $ Z.of_nat (typelen Int8u)) +ᵢ  $ Z.of_nat (typelen Int16u)) +ᵢ
       *     $ Z.of_nat (typelen (Void) ∗)) +ᵢ
       *    $ Z.of_nat (typelen (Tarray Int8u ∘ OS_EVENT_TBL_SIZE))) @
       * STRUCT os_event ⋆ |-> v'6 **
       * AEventData
       *   (Vint32 i8 :: Vint32 v'16 :: Vint32 i9 :: x29 :: x30 :: v'6 :: nil) x22 **
       * evsllseg v'6 Vnull x15 x24 **
       * evsllseg v'8 (Vptr (v'14, Int.zero)) x5 x23 **
       * GV OSEventList @ OS_EVENT ∗ |-> v'8 **
       * LV pevent @ OS_EVENT ∗ |-> Vptr (v'14, Int.zero) **
       * GV OSRdyGrp @ Int8u |-> Vint32 v'43 **
       * GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
       *   (update_nth_val (Z.to_nat (Int.unsigned (v'56 >>ᵢ $ 3))) v'33
       *      (val_inj (and (Vint32 v'44) (Vint32 (Int.not ($ 1<<ᵢ(v'56&ᵢ$ 7))))))) **
       * dllseg v'9 Vnull Vnull (Vptr (cur_tcb_blk, Int.zero)) nil OS_TCB_flag
       *   (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
       * PV vhold @ Int8u |-> v'7 **
       * GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
       * AOSEventFreeList v'3 **
       * AOSQFreeList v'4 **
       * AOSQFreeBlk v'5 **
       * AOSMapTbl **
       * AOSUnMapTbl **
       * G& OSPlaceHolder @ Int8u == vhold **
       * AOSIntNesting **
       * sll v'20 v'21 OS_TCB_flag (fun vl : vallist => nth_val 0 vl) **
       * sllfreeflag v'20 v'21 **
       * AOSTime (Vint32 v'18) **
       * AGVars **
       * tcbdllflag v'9
       *   (nil ++
       *    (Vptr (v'15, Int.zero)
       *     :: Vnull
       *        :: Vptr (v'14, Int.zero)
       *           :: x0
       *              :: Vint32 i13
       *                 :: Vint32 x21
       *                    :: Vint32 v'56
       *                       :: Vint32 (v'56&ᵢ$ 7)
       *                          :: Vint32 (v'56 >>ᵢ $ 3)
       *                             :: Vint32 ($ 1<<ᵢ(v'56&ᵢ$ 7))
       *                                :: Vint32 ($ 1<<ᵢ(v'56 >>ᵢ $ 3)) :: nil)
       *    :: (v'11
       *        :: Vptr (cur_tcb_blk, Int.zero)
       *           :: x35
       *              :: x34
       *                 :: Vint32 i16
       *                    :: Vint32 i15
       *                       :: Vint32 i14
       *                          :: Vint32 i12
       *                             :: Vint32 i11
       *                                :: Vint32 i10 :: Vint32 i7 :: nil) :: l2') **
       * p_local OSLInv (cur_tcb_blk, Int.zero) init_lg **
       * atoy_inv' ** LV self @ Int8u |-> (V$ 0) ** LV prio @ Int8u |-> Vint32 v'56)
       * 
       *          ). *)
      clear.
      intro; intros.
      sep lifts (4:: 6::nil)%nat. 
      eapply elim_a_isr_is_prop.
      sep cancel Aisr.
      sep cancel Ais.
      sep cancel Acs.
      sep cancel Aie.
      sep pauto.

      unfold os_task.STKFREE.

      assert (exists mmm, TcbJoin (cur_tcb_blk, Int.zero) (v'53, wait (hle2wait x (v'15, Int.zero)) i13 , x0) mmm tcbmap).
      apply tcb_get_join.
      unfold get, sig, join in *; simpl in *.
      unfold get, sig, join in *; simpl in *.
      go.

      destruct H102 as (tcbmap_left & tcbmapleft_join_hyp).


      eapply seq_rule.
      eapply derive_delself_rule.
      apply goodlinv.

       (* goodlinv *)
      go.
      unfold AEventData.
      destruct x22; go.
      unfold p_local.
      unfold CurTid; unfold LINV.
      unfold OSLInv.
      go.
      exact tcbmapleft_join_hyp.
      intro; intros.
      split.
      sep_get_rv.
      unfold p_local in H102.
      unfold CurLINV.
      sep pauto.
      sep cancel LINV.
      simpl; auto 1.
(* ** ac:       Check dllsegflag_split. *)
      hoare lift 36%nat pre.
      eapply backward_rule1.
      eapply dllsegflag_split.
      hoare_split_pure_all.
      unfold dllsegflag at 2.
      fold dllsegflag .
      hoare_split_pure_all.
      inverts H130.
      inverts H103.
      inverts H131.
      inverts H103.
      rewrite H101.

      (* Lemma dllsegflag_last_next_is_endstnl:
       *   forall l head endstnl endp next s P,
       *     s |= dllsegflag head endstnl (l++ (endp :: nil)) next  ** P ->
       *     next endp = Some endstnl.
       * Proof.
       *   induction l.
       *   intros.
       *   simpl (nil ++ endp :: nil) in H.
       *   unfold dllsegflag in H.
       *   sep normal in H.
       *   sep destruct H.
       *   sep split in H.
       *   subst.
       *   auto.
       * 
       *   intros.
       *   simpl ((a ::l ) ++ endp :: nil) in H.
       *   unfold1 dllsegflag in H.
       *   
       *   sep normal in H.
       *   sep destruct H.
       *   sep split in H.
       *   sep lift 2%nat in H.
       *   eapply IHl.
       *   eauto.
       * Qed. *)

      hoare_assert_pure ( (fun vl : vallist => nth_val 0 vl) (Vptr (cur_tcb_blk, Int.zero)
                                                                   :: v'13
                                                                   :: x36
                                                                   :: x33
                                                                   :: Vint32 i22
                                                                   :: Vint32 i21
                                                                   :: Vint32 i20
                                                                   :: Vint32 i19
                                                                   :: Vint32 i18
                                                                   :: Vint32 i17 :: Vint32 i16 :: nil) = Some (Vptr v'47) ).
      eapply dllsegflag_last_next_is_endstnl.
      instantiate (4 := s0).
      sep cancel 4%nat 1%nat.
      eauto.

      hoare_split_pure_all.
      inverts H102.

      
      
      (* rewrite app_nil_l. *)
      (* hoare unfold. *)
      (* hoare lift 4%nat pre. *)
      unfold p_local at 2.
      unfold OSLInv at 3.
      unfold LINV.
      hoare_split_pure_all.
      (* unfold1 dllseg. *)
      (* hoare unfold. *)
      eapply backward_rule1.
      intro; intros.
      (* Print Ltac sep_combine. *)
      sep combine ( get_off_addr (cur_tcb_blk, Int.zero) ($ 24)  ) in H130.
      eauto.

      hoare lift 5%nat pre.
      eapply seq_rule.
      eapply assign_rule'.
      Focus 2.

      intro; intros.
      split.
      eapply field_asrt_impl.
      Focus 3.
      sep cancel 13%nat 1%nat.
      eauto.
      reflexivity.
      reflexivity.
      sep get rv.
      eapply eq_int; auto.

      intro; intros.
      unfold p_local, OSLInv.
      sep pauto.
      unfold LINV.
      sep pauto.
      sep cancel 52%nat 1%nat.
      simpl; auto.
      splits; eauto.
      unfolds; auto.
      

      eapply backward_rule1.
      intro; intros.
      sep lifts (8::10::nil)%nat in H130.
      eapply add_a_isr_is_prop in H130.
      eauto.
      hoare lift 4%nat pre.
      eapply seq_rule.

      eapply excrit1_rule'_ISnil_ISRemp''.
      intro.
      intros.
      sep cancel atoy_inv'.
      sep cancel Aisr.
      sep cancel Aie.
      sep cancel Ais.
      sep cancel Acs.
      unfold p_local, OSLInv.
      unfold LINV.
      sep pauto.
      sep cancel 2%nat 1%nat.
      sep cancel CurTid.
      unfold OSInv.
      sep pauto.
      sep cancel AOSEventFreeList.
      sep cancel AOSQFreeList.
      sep cancel AOSQFreeBlk.
      unfold AECBList.
instantiate (17 := (x11 ++ (Vint32 i7 :: Vint32 v'50 :: Vint32 i8 :: x29 :: x30 :: v'6 :: nil,
                                 (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'37
                                                 (val_inj
                                                    (and (Vint32 v'51) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7)))))))
                                ) :: x15)).
      instantiate (16 :=(x23 ++ x22 :: x24) ).

      (* instantiate (x3 := (x5 ++ (Vint32 i8 :: Vint32 v'53 :: Vint32 i9 :: x29 :: x30 :: v'6 :: nil,
       *                            (update_nth_val (Z.to_nat (Int.unsigned (v'56 >>ᵢ $ 3))) v'40
       *                                            (val_inj
       *                                               (and (Vint32 v'54) (Vint32 (Int.not ($ 1<<ᵢ(v'56&ᵢ$ 7)))))))
       *                           ) :: x15)).
       * instantiate (x2 :=(x23 ++ x22 :: x24) ). *)
      sep pauto.
      eapply evsllseg_merge.
      eapply (ecblistp_length_eq_1 _ _ _ _ _ _ H80).
      eapply (ecblistp_length_eq_1 _ _ _ _ _ _ H81).

      (* admit.
       * admit. *)
      unfold1 evsllseg .
      sep pauto.
      unfold AEventNode.
      sep cancel evsllseg.
      sep cancel evsllseg.
      unfold AOSEvent.
      unfold node.
      unfold AOSEventTbl.
      sep pauto.
      sep cancel Aarray.

      sep lift 2%nat.
      eapply AED_changegrp.
      sep cancel AEventData.
      unfold Astruct.
      unfold OS_EVENT.
      unfold Astruct'.
      sep normal.
      sep cancel 16%nat 2%nat.
      repeat sep cancel 16%nat 1%nat.
      unfold AOSTCBPrioTbl.
      sep pauto.
      sep cancel 20%nat 2%nat.
      sep cancel 14%nat 1%nat.
      unfold AOSRdyTblGrp.
      unfold AOSRdyTbl.
      unfold AOSRdyGrp.
      sep pauto.
      unfold AOSTCBList'.
      eapply intro_or_r.
      sep pauto.
      unfold tcblist.

      instantiate ( 5 :=(v'43 ++
                               (Vptr (next_tcb_block, Int.zero)
                                     :: v'13
                                     :: x36
                                     :: x33
                                     :: Vint32 i22
                                     :: Vint32 i21
                                     :: Vint32 i20
                                     :: Vint32 i19
                                     :: Vint32 i18
                                     :: Vint32 i17 :: Vint32 i16 :: nil)
                               :: nil)  ).

      instantiate ( 3 := l2').
      instantiate ( 4 :=
                      (v'52
                         :: Vptr (prev_tcb_block, Int.zero)
                         :: x35
                         :: x34
                         :: Vint32 i15
                         :: Vint32 i14
                         :: Vint32 i12
                         :: Vint32 i11
                         :: Vint32 i10
                         :: Vint32 i9 :: Vint32 i :: nil)).
      (* (Vptr (next_tcb_block, Int.zero)
       *                :: v'13
       *                   :: x36
       *                      :: x33
       *                         :: Vint32 i23
       *                            :: Vint32 i22
       *                               :: Vint32 i21
       *                                  :: Vint32 i20
       *                                     :: Vint32 i19
       *                                        :: Vint32 i18 :: Vint32 i17 :: nil) 
       *              ). *)
      (* instantiate (x1 :=
       *                ((v'46 ++
       *                       (Vptr (cur_tcb_blk, Int.zero)
       *                             :: v'13
       *                             :: x36
       *                             :: x33
       *                             :: Vint32 i23
       *                             :: Vint32 i22
       *                             :: Vint32 i21
       *                             :: Vint32 i20
       *                             :: Vint32 i19
       *                             :: Vint32 i18 :: Vint32 i17 :: nil) :: nil)
       *                   ++
       *                   (v'52
       *                      :: Vptr (prev_tcb_block, Int.zero)
       *                      :: x35
       *                      :: x34
       *                      :: Vint32 i16
       *                      :: Vint32 i15
       *                      :: Vint32 i14
       *                      :: Vint32 i12
       *                      :: Vint32 i11
       *                      :: Vint32 i10 :: Vint32 i7 :: nil) :: l2') ). *)

      unfold TCB_Not_In.
      sep pauto.
      eapply tcbdllseg_compose.
      unfold tcbdllseg.
      unfold1 dllseg.
      unfold node.
      sep pauto.
      sep cancel 10%nat 1%nat.
      sep cancel 12%nat 1%nat.
(* ** ac:       SearchAbout dllseg. *)
      (* Goal forall l head headprev tail tailnext x t fprev fnext,
       *        dllseg head headprev tail tailnext (l++x::nil) t fprev fnext <==>
       *               EX tail', dllseg head headprev tail' tail l t fprev fnext **
       *                                [| |] *)
       
      (* Fixpoint poidllseg (head  headprev tail tailnext: val) (l : list vallist) cond : asrt:=
       *   match l with
       *     | nil =>  [| head = tailnext /\ headprev = tail|]
       *        | vl :: l' =>
       *          EX  (vn : val),
       *          cond head headprev vl vn **
       *          (* scond head vl  ** *)
       *           poidllseg vn head tail tailnext l' cond 
       *   end.
       * 
       * Lemma poidllseg_is_poillseg :
       *   forall l head hp tail tn cond,
       *     poidllseg head hp tail tn l cond <==> poi_llseg (head, hp) (tn, tail) l
       *               (fun head vl head'=> let (h, hp) := head in let (h', hp') := head' in 
       *                                                           cond h hp vl h' ** [|hp' = h|]).
       * Proof.
       *   induction l.
       *   intros.
       *   split.
       *   unfold poidllseg, poi_llseg in *.
       *   intro.
       *   sep auto.
       *   simpljoin.
       *   
       *   unfold poidllseg, poi_llseg in *.
       *   intro.
       *   sep auto.
       *   simpljoin.
       *   tauto.
       *   intros.
       *   splits.
       *   intros.
       *   unfold1 poidllseg in H.
       *   sep destruct H.
       *   unfold poi_llseg.
       *   sep eexists.
       *   instantiate (x := (x, head)).
       *   simpl (let (h', hp') := (x, head) in cond head hp a h' ** [| hp' = head |]) .
       *   sep pauto.
       *   apply IHl.
       *   auto.
       *   intro.
       *   unfold poi_llseg in H.
       *   sep destruct H.
       *   destruct x.
       *   unfold1 poidllseg.
       *   sep eexists.
       *   sep cancel 1%nat 1%nat.
       *   sep split in H.
       *   apply IHl in H.
       *   subst.
       *   auto.
       * Qed. *)
        
      (* Lemma split_poidllseg :
       *   forall l1 l2 head headprev tail tailnext cond P,
       *     poidllseg head headprev tail tailnext (l1 ++ l2) cond ** P<==>
       *               EX mid midn,
       *               poidllseg head headprev mid midn l1 cond **
       *                         poidllseg midn mid tail tailnext l2 cond ** P.
       * Proof.
       *   induction l1.
       *   intros.
       *   splits.
       *   intros.
       *   simpl (nil ++ l2) in H.
       *   sep eexists.
       *   unfold1 poidllseg.
       *   sep pauto.
       *   intros.
       * 
       *   simpl (nil ++ l2) .
       *   sep pauto.
       *   unfold1 poidllseg in H.
       *   sep pauto.
       *   subst; auto.
       *   intro.
       * 
       *   split.
       *   intros.
       *   simpl  ( (a::l1) ++ l2) in H.
       *   unfold1 poidllseg in H.
       *   sep normal in H.
       *   sep destruct H.
       *   sep split in H.
       *   sep lift 2%nat in H.
       *   apply IHl1 in H.
       *   sep pauto.
       *   unfold1 poidllseg.
       *   sep pauto.
       *   sep cancel 3%nat 1%nat.
       *   sep pauto.
       *   intro.
       *   
       *   simpl  ( (a::l1) ++ l2) .
       *   unfold1 poidllseg.
       *   sep destruct H.
       *   unfold1 poidllseg in H.
       *   sep normal in H.
       *   sep destruct H.
       *   sep split in H.
       *   sep normal.
       *   sep eexists.
       *   sep split.
       *   sep lift 2%nat.
       *   rewrite IHl1.
       *   sep eexists.
       *   sep cancel 1%nat 3%nat.
       *   sep pauto.
       * Qed.
       * 
       * Show. *)
      eapply dllseg_is_poi.
      eapply split_poillseg.
      sep eexists.
      rewrite <- dllseg_is_poi.
      sep lift 2%nat.
      rewrite <- dllseg_is_poi.
      unfold1 dllseg.
      unfold node.
      sep pauto.
      sep cancel 10%nat 1%nat.
      sep cancel dllseg.


     (* Fixpoint poisllseg (head tailnext: val) (l : list vallist) cond : asrt:=
      *    match l with
      *      | nil =>  [| head = tailnext |]
      *         | vl :: l' =>
      *           EX  (vn : val),
      *           cond head vl vn **
      *           (* scond head vl  ** *)
      *            poisllseg vn tailnext l' cond 
      *    end.
      *  
      * 
      *  Lemma split_poisllseg :
      *    forall l1 l2 head tailnext cond P,
      *      poisllseg head tailnext (l1 ++ l2) cond ** P<==>
      *                EX midn,
      *                poisllseg head midn l1 cond **
      *                          poisllseg midn tailnext l2 cond ** P.
      *  Proof.
      *    induction l1.
      *    intros.
      *    splits.
      *    intros.
      *    simpl (nil ++ l2) in H.
      *    sep eexists.
      *    unfold1 poisllseg.
      *    sep pauto.
      *    intros.
      * 
      *    simpl (nil ++ l2) .
      *    sep pauto.
      *    unfold1 poisllseg in H.
      *    sep pauto.
      *    subst; auto.
      *    intro.
      * 
      *    split.
      *    intros.
      *    simpl  ( (a::l1) ++ l2) in H.
      *    unfold1 poisllseg in H.
      *    sep normal in H.
      *    sep destruct H.
      *    sep split in H.
      *    sep lift 2%nat in H.
      *    apply IHl1 in H.
      *    sep pauto.
      *    unfold1 poisllseg.
      *    sep pauto.
      *    sep cancel 3%nat 1%nat.
      *    sep pauto.
      *    intro.
      *    
      *    simpl  ( (a::l1) ++ l2) .
      *    unfold1 poisllseg.
      *    sep destruct H.
      *    unfold1 poisllseg in H.
      *    sep normal in H.
      *    sep destruct H.
      *    sep split in H.
      *    sep normal.
      *    sep eexists.
      *    sep split.
      *    sep lift 2%nat.
      *    rewrite IHl1.
      *    sep eexists.
      *    sep cancel 1%nat 3%nat.
      *    sep pauto.
      *  Qed.
      * 
      *  Show.
      * 
      *  Print tcbdllflag.
      *  Print tcbdllflag.
      *  Print dllsegflag.
      *  Print dllsegflag.
      *  Print dllsegflag.
      *  Print dllsegflag. *)
      unfold tcbdllflag.
      sep lift 4%nat in H130.
      rewrite dllsegflag_is_poi in H130.
      apply split_poillseg in H130.

      apply dllsegflag_is_poi.
      sep pauto.
      apply split_poillseg.
      sep eexists.
      apply split_poillseg.
      sep eexists.
      sep cancel 1%nat 1%nat.
      unfold1 @poi_llseg in *.
      sep pauto.
      sep lift 2%nat.
      rewrite <- dllsegflag_is_poi.
      sep cancel dllsegflag.
      instantiate (3 := x16).
      sep cancel 1%nat 2%nat.
      sep cancel 2%nat 1%nat.

      (* freelist *)
      unfold AOSTCBFreeList'.
      sep pauto.
      eapply intro_or_r. 
      unfold TCBFree_Eq.
      sep pauto.
      sep cancel sll.
      sep cancel sllfreeflag.
      eauto.
      go.
      eapply isptr_is_definitely_ptr.
      eapply sll_head_isptr.
      instantiate (5:=s).
      sep cancel sll.
      go.
      unfolds.
      {
        do 6 eexists.
        splits.
        go.
        go.
        go.
        go.
        go.
        go.
        go.
        splits.
        go.
        go.
        go.
        go.
        left; auto.
        repeat tri_exists_and_solver1.
        go.
      }
      eexists; go.
{
        unfolds in H6.
        simpljoin.
        clear -tcbmapleft_join_hyp H134.
        unfolds.
        unfolds in tcbmapleft_join_hyp.
        intro.
        simpljoin.

        unfolds in H134.
        assert (x1 <> (cur_tcb_blk, Int.zero)).
        intro.
        subst.
(* ** ac:         SearchAbout join. *)
(* ** ac:         SearchAbout TcbMod.join. *)
        eapply TcbMod.map_join_get_some .
        
        auto.
        eauto.
        2: exact H.
        (* instantiate (1:=(v'43, x, x0)). *)
        unfold get in *; simpl in *.
        unfold sig in *; simpl in *.
        eapply TcbMod.get_a_sig_a.
        go.
        unfold join, sig, get in *; simpl in *.
        assert (TcbMod.get tcbmap x1 =Some (v'53, x2, x3) ).
        go.
        assert (TcbMod.get tcbmap (cur_tcb_blk, Int.zero) =Some(v'53, wait (hle2wait x (v'15, Int.zero)) i13,
                             x0)  ).
        go.
        lets bb: H134 H0 H1 H2.
        apply bb.
        reflexivity.

      }      
      go.
      2: go.
      go.
      go.
      intro; tryfalse.
      go.
      go.
      intro; tryfalse.
      go.
      go.
      go.
      {
        splits.
assert( list_all_P (fun x10 : vallist => V_OSTCBNext x10 <> None)
   (v'43 ++
    (Vptr (cur_tcb_blk, Int.zero)
     :: v'13
        :: x36
           :: x33
              :: Vint32 i22
                 :: Vint32 i21
                    :: Vint32 i20
                       :: Vint32 i19
                          :: Vint32 i18 :: Vint32 i17 :: Vint32 i16 :: nil)
    :: nil) )as hell.

change ((fun x => list_all_P (fun x10 : vallist => V_OSTCBNext x10 <> None) x)
         (v'43 ++
      (Vptr (cur_tcb_blk, Int.zero)
       :: v'13
          :: x36
             :: x33
                :: Vint32 i22
                   :: Vint32 i21
                      :: Vint32 i20
                         :: Vint32 i19
                            :: Vint32 i18 :: Vint32 i17 :: Vint32 i16 :: nil)
      :: nil)).
 
 rewrite <- H101.

     
(* ** ac:  Show. *)
 eapply TCBLP_imply_nextnotnull_list.
 exact H29.
 
 rewrite H101.
 
         rewrite get_last_tcb_ptr_appsig.
         reflexivity.

        (* here *)
        rewrite ptr_in_tcblist_app.
        (* 2: simpl; auto. *)
        intro.
        destruct H131.
        eapply ptr_in_tcblist_last_ir in H131.
        gen H131.
        eapply distinct_is_unique_first.
instantiate ( 1 :=(Vptr (cur_tcb_blk, Int.zero)
             :: v'13
                :: x36
                   :: x33
                      :: Vint32 i22
                         :: Vint32 i21
                            :: Vint32 i20
                               :: Vint32 i19
                                  :: Vint32 i18
                                  :: Vint32 i17 :: Vint32 i16 :: nil)).

exact hell.
(* ** ac: SearchAbout get_last_tcb_ptr. *)

         eapply  TCBLP_imply_dictinct_list .
         rewrite <- H101.
         exact H25.

         rewrite get_last_tcb_ptr_appsig.
         reflexivity.

           
       
        (* simpl in H131. *)
        (* exact H131. *)
         rewrite get_last_tcb_ptr_appsig in H131.
         simpl (val_inj (Some (Vptr (next_tcb_block, Int.zero)))) in H131. 
(* ** ac:          SearchAbout ptr_in_tcblist. *)

(* ** ac:         Show. *)
        eapply ptr_in_tcblist_change_first in H131.
        gen H131.

        eapply distinct_is_unique_second.
        3: eapply  TCBLP_imply_dictinct_list .
        3: exact H25.
        2: go.
        rewrite H101.
        exact hell.
        rewrite H101.
        rewrite get_last_tcb_ptr_appsig.
        reflexivity.
        rewrite list_all_P_app.
        rewrite list_all_P_app in hell.
        simpljoin.
        splits; auto.
        simpl.
        split; auto.
         (* unfold V_OSTCBNext; simpl; intro; tryfalse. *)
        eauto.
      }
       (* from tcblist_p, get they are all different? *)
      {

(* ** ac:         SearchAbout TCBList_P. *)

         eapply TCBList_merge_prop.
         instantiate (2 := v'17).
         instantiate (1 := x13).

(* ** ac:          SearchAbout TcbMod.join. *)
         eapply some_join_lemma0; eauto.
         exact H22.
         exact tcbmapleft_join_hyp.
                  
  (* H22 : TcbJoin (cur_tcb_blk, Int.zero)
   *         (v'53, wait (hle2wait x (v'15, Int.zero)) i13, x0) x13 v'19
   * H28 : TcbMod.join v'17 v'19 tcbmap
   * tcbmapleft_join_hyp : TcbJoin (cur_tcb_blk, Int.zero)
   *                         (v'53, wait (hle2wait x (v'15, Int.zero)) i13, x0)
   *                         tcbmap_left tcbmap
   * 
   *         *)
(* ** ac:          SearchAbout last. *)
(* ** ac:          Print get_last_tcb_ptr. *)
(* ** ac:          SearchAbout last. *)
         rewrite app_last.
         simpl.
         go.
         Focus 2.

(* Lemma tcblist_p_hold_for_del_a_tcb_at_head' :
 *           forall l head hn xx x0 i13 x21 v'53 hleft hnleft v'48 tcbmap_left v'41 v'30 tcbmap  status msg prev, 
 *  0 <= Int.unsigned v'53 < 64 ->
 *             R_Prio_No_Dup tcbmap ->
 *             (forall x : int32,
 *         prio_in_tbl x v'30 ->
 *         Int.eq x v'53 = false ->
 *         prio_in_tbl x
 *           (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'30
 *              (val_inj
 *                 (and (Vint32 v'41) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7)))))))) ->
 *             nth_val' (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'30 = Vint32 v'41 ->
 *             TcbMod.join (TcbMod.sig head (v'53, status, msg)) tcbmap_left tcbmap ->
 *             TCBList_P (Vptr head)
 *                       ((hn :: prev :: xx :: x0 :: i13 :: x21 :: Vint32 v'53 :: hleft)
 *                          :: (v'48 :: Vptr head :: hnleft) :: l)
 *                       v'30 tcbmap ->
 *             TCBList_P hn
 *                       ((v'48 :: prev :: hnleft) :: l)
 *                       (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'30
 *                                       (val_inj (and (Vint32 v'41) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7)))))))
 *                       tcbmap_left.
 *         Proof.
 *           introv HHH.
 *           intros.
 * 
 * 
 *           Check OSTimeDlyPure.update_rtbl_tcblist_hold.
 *           eapply OSTimeDlyPure.update_rtbl_tcblist_hold.
 *           auto.
 *           eapply nv'2nv.
 *           exact H1.
 *           intro; tryfalse.
 *           intros.
 *           assert ( tid = head \/ tid <> head) by tauto.
 *           destruct H5.
 *           subst head.
 *           intro.
 *           assert (exists bb, TcbMod.join (sig tid (a,b,c)) bb tcbmap_left).
 *           clear -H4.
 *           SearchAbout TcbMod.get.
 *           eapply tcb_get_join.
 *           auto.
 *           simpljoin.
 *           
 * 
 *           eapply join_two_sig_is_false.
 *           exact H2.
 *           eauto.
 * 
 *           assert (TcbMod.get tcbmap head = Some (v'53, status, msg)).
 *           go.
 *           assert (TcbMod.get tcbmap tid = Some (a, b, c)).
 *           go.
 *           lets fff: H H6 H7.
 *           auto.
 *           auto.
 *           
 *           SearchAbout TCBList_P.
 *           remember ( (v'48 :: Vptr head :: hnleft) :: l).
 *           unfold1 TCBList_P in H3.
 *           simpljoin.
 *           inverts H4.
 *           inverts H3.
 * 
 *           lets bbbb: tcbjoinsig_unique H2 H5.
 *            simpljoin.
 * 
 *            eapply Tcblist_p_hold_for_change_headprev.
 *            eauto.
 *         Qed. *)


         eapply  tcblist_p_hold_for_del_a_tcb_at_head .
         omega.

        2:go.
        2:go.
        2: exact H22.
        2: exact backup.
        unfolds in H6.
        simpljoin.
        clear -H133 H28.
        eapply R_Prio_No_Dup_hold_for_subset.
        apply TcbMod.join_comm; eauto.
        eauto.

        
        eapply OSTimeDlyPure.update_rtbl_tcblist_hold.

        omega.
        unfold nat_of_Z; eapply nv'2nv.
        exact H60.
        intro; tryfalse.
        intros.

        unfolds in H6.
        simpljoin.
        clear -H28 H22 H131 H134.
(* ** ac:         Print R_Prio_No_Dup. *)
        eapply H134.
        instantiate (2 := tid).
        instantiate (1 := (cur_tcb_blk, Int.zero)).
        intro; subst tid.
(* ** ac:         SearchAbout TcbMod.join. *)
        eapply TcbMod.map_join_get_some.
        auto.
        exact H28.
        unfold TcbJoin in H22.
        unfold join,sig,get in H22; simpl in H22.
        go.
        
        unfold TcbJoin in H22.
        unfold join,sig,get in H22; simpl in H22.
        go.
        
        unfold TcbJoin in H22.
        unfold join,sig,get in H22; simpl in H22.
        unfold get; simpl.
        go.
        unfold TcbJoin in H22.
        unfold join,sig,get in H22; simpl in H22.
        unfold get; simpl.
        go.

(* ** ac:         SearchAbout TCBList_P. *)

        eapply TCBList_P_hold_for_last_change.
        rewrite H101 in H29.
        exact H29.
        
        
  (* H28 : TcbMod.join v'17 v'19 tcbmap
   * H22 : TcbJoin (cur_tcb_blk, Int.zero)
   *         (v'53, wait (hle2wait x (v'15, Int.zero)) i13, x0) x13 v'19 *)
      }
       (* tcblist_p hold for deleting a tcb *)
      split.
      assumption.
      eapply (H68 _ H55).
      clear -H0; unfold OS_IDLE_PRIO.
      csimpl OS_LOWEST_PRIO.
      int auto.
       
      {
        eapply  r_priotbl_p_hold_for_del_a_tcb.
        omega.
        assumption.
        eauto 1.

        exact   tcbmapleft_join_hyp .

      }

       (* r_priotbl_p hold for deleting a tcb *)
      
{
  eapply  rtbl_remove_RL_RTbl_PrioTbl_P_hold'.
  omega.
  rewrite Int.repr_unsigned.
  reflexivity.

  rewrite Int.repr_unsigned.
  reflexivity.

  2: assumption.
  unfold nat_of_Z.
  apply nv'2nv.
  
  assumption.
  intro; tryfalse.
  
      }

       (* rl_rtbl_ptbl_p hold for deleting a tcb *)

      split.
      eapply array_type_vallist_match_hold.
      assumption.

      rewrite H7.
      clear -H; mauto.
      reflexivity.

      rewrite hoare_assign.update_nth_val_len_eq.
      assumption.
      go.
      go.
      go.
      go.
      clear -H96 H131.
      unfolds in H96.
      change Byte.max_unsigned with 255%Z in * .
      math simpl in H96.
      omega.
      go.

      {
        eapply ECBLP_hold4del_a_tcb; eauto.
        3:exact tcbmapleft_join_hyp.
        clear -H6; unfolds in H6; tauto.
        clear -H6; unfolds in H6; tauto.
      }

       (* from H101 : RL_Tbl_Grp_P
           (update_nth_val (Z.to_nat (Int.unsigned (v'56 >>ᵢ $ 3))) v'40
              (val_inj
                 (and (Vint32 v'54) (Vint32 (Int.not ($ 1<<ᵢ(v'56&ᵢ$ 7)))))))
           (Vint32 v'53), ECBList_P holds for deleting a tcb *)

        

       

      {
      eapply poi_is_rtep.
        eapply poi_RHTEP_hold_for_del_a_tcb.
        assumption.
        go.
        eapply tcbmapleft_join_hyp.
        go.
        clear -H2 H61 H62; unfolds; splits; auto.
      }

       (* change to poi,
from some_pure_hyp : forall (eid : tidspec.A) (pr : int32) 
                    (tid0 : tid) (opr : int32) (wls : waitset),
                  EcbMod.get ecbmap eid =
                  Some (absmutexsem pr (Some (tid0, opr)), wls) ->
                  tid0 <> (cur_tcb_blk, Int.zero)
get rh_te_p hold for deleting a tcb
              *)
      splits; go.
      unfolds; auto.
      go.
      hoare forward.
      sep cancel Aisr.
      sep cancel Acs.
      sep cancel Ais.
      sep cancel Aie.
      sep cancel Aop.
      sep cancel p_local.
      eauto.
      unfolds; auto.
      go.
      linv_solver.
      linv_solver.

      unfold OS_SchedPost.
      unfold OS_SchedPost'.
      unfold getasrt.
      hoare forward.
      inverts H131.
      reflexivity.
    }

    (* delete not current *)
    {

      (* subst todelblock. *)
      (* unfold get in H16; simpl in H16. *)
      (* rewrite H23 in kitty. *)
      (* Lemma derive_delself_rule:
       *   forall pa P  prio st msg tls' tls t e tp  aop r ri sd Spec I isr ie is cs,
       *     GoodLInvAsrt pa ->
       *     GoodFrm P ->
       *     joinsig t (prio, st, msg) tls' tls  ->
       *     P ==>  Rv e @ tp == Vptr t //\\  CurLINV pa t ->
       *     InfRules Spec sd pa I r ri 
       *              (
       *                <|| spec_del  (Vint32 prio);; aop ||>  **
       *                    Aabsdata abstcblsid (abstcblist tls) **
       *                    Aabsdata curtid (oscurt t) **
       *                    OS[isr, ie, is, cs] ** P
       *              ) 
       *              (sprim (stkfree e))
       *              (
       *                <|| aop ||>  **
       *                    Aabsdata abstcblsid (abstcblist tls') ** 
       *                    Aabsdata curtid (oscurt t) **
       *                    OS[isr, ie, is, cs]  
       *                    ** P
       *              ) t.
       * Proof.
       *   intros.
       *   eapply backward_rule1.
       *   instantiate (1:= (
       *                     <|| spec_del (Vint32 prio);; aop ||> ** P**
       *                         HTCBList tls ** HCurTCB t ** OS [isr, ie, is, cs] 
       *                         
       *                   )).
       *   intro.
       *   intros.
       *   sep pauto.
       *   eapply forward_rule2.
       *   eapply delself_rule; eauto.
       *   intro.
       *   intro.
       *   sep pauto.
       * Qed. *)
      eapply backward_rule1.
      Set Printing Depth 999.
(* ** ac:       Show. *)
      instantiate (1:=
                     (
                       <|| sdel (Vint32 v'53 :: nil);; isched;; END Some (V$ NO_ERR) ||>  **
                           HTCBList tcbmap **
                           HCurTCB (cur_tcb_blk, Int.zero) **
                           OS [ empisr, false, nil, (true::nil)] **
   (* <|| spec_del (Vint32 v'53);; isched;; END Some (V$ NO_ERR) ||>  ** *)
   A_dom_lenv
     ((prio, Int8u)
      :: (pevent, OS_EVENT ∗)
         :: (ptcb, OS_TCB ∗)
            :: (self, Int8u) :: (os_code_defs.x, OS_TCB ∗) :: nil) **
   GV OSTCBFreeList @ OS_TCB ∗ |-> Vptr (todelblock, Int.zero) **
   LV ptcb @ OS_TCB ∗ |-> Vptr (todelblock, Int.zero) **
   Astruct (todelblock, Int.zero) OS_TCB_flag
     (v'20
      :: Vptr (prev_tcb_block, Int.zero)
         :: Vnull
            :: x0
               :: V$ 0
                  :: V$ OS_STAT_RDY
                     :: Vint32 v'53
                        :: Vint32 (v'53&ᵢ$ 7)
                           :: Vint32 (v'53 >>ᵢ $ 3)
                              :: Vint32 ($ 1<<ᵢ(v'53&ᵢ$ 7))
                                 :: Vint32 ($ 1<<ᵢ(v'53 >>ᵢ $ 3)) :: nil) **
   LV os_code_defs.x @ OS_TCB ∗ |-> Vptr (next_tcb_block, Int.zero) **
   Astruct (next_tcb_block, Int.zero) OS_TCB_flag
     (v'14
      :: Vptr (prev_tcb_block, Int.zero)
         :: x35
            :: x34
               :: Vint32 i15
                  :: Vint32 i14
                     :: Vint32 i12
                        :: Vint32 i11
                           :: Vint32 i10 :: Vint32 i9 :: Vint32 i :: nil) **
   Astruct (prev_tcb_block, Int.zero) OS_TCB_flag
     (Vptr (next_tcb_block, Int.zero)
      :: v'13
         :: x36
            :: x33
               :: Vint32 i22
                  :: Vint32 i21
                     :: Vint32 i20
                        :: Vint32 i19
                           :: Vint32 i18 :: Vint32 i17 :: Vint32 i16 :: nil) **
   dllseg v'9 Vnull v'13 (Vptr (prev_tcb_block, Int.zero)) v'43 OS_TCB_flag
     (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
   dllseg v'14 (Vptr (next_tcb_block, Int.zero)) v'12 Vnull l2' OS_TCB_flag
     (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
   GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64)
     (update_nth_val (Z.to_nat (Int.unsigned v'53)) priotbl Vnull) **
   PV vhold @ Int8u |-> v'7 **
   Aarray v'38 (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
     (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'37
        (val_inj (and (Vint32 v'51) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7))))))) **
   PV (v'15, Int.zero +ᵢ  $ 1) @ Int8u |-> Vint32 v'50 **
   PV (v'15, Int.zero) @ Int8u |-> Vint32 i7 **
   PV (v'15,
      (Int.zero +ᵢ  $ Z.of_nat (typelen Int8u)) +ᵢ
      $ Z.of_nat (typelen Int8u)) @ Int16u |-> Vint32 i8 **
   PV (v'15,
      ((Int.zero +ᵢ  $ Z.of_nat (typelen Int8u)) +ᵢ
       $ Z.of_nat (typelen Int8u)) +ᵢ  $ Z.of_nat (typelen Int16u)) @
   (Void) ∗ |-> x29 **
   PV (v'15,
      ((((Int.zero +ᵢ  $ Z.of_nat (typelen Int8u)) +ᵢ
         $ Z.of_nat (typelen Int8u)) +ᵢ  $ Z.of_nat (typelen Int16u)) +ᵢ
       $ Z.of_nat (typelen (Void) ∗)) +ᵢ
      $ Z.of_nat (typelen (Tarray Int8u ∘ OS_EVENT_TBL_SIZE))) @
   STRUCT os_event ⋆ |-> v'6 **
   AEventData
     (Vint32 i7 :: Vint32 v'28 :: Vint32 i8 :: x29 :: x30 :: v'6 :: nil) x22 **
   evsllseg v'6 Vnull x15 x24 **
   evsllseg v'8 (Vptr (v'15, Int.zero)) x11 x23 **
   GV OSEventList @ OS_EVENT ∗ |-> v'8 **
   (* HECBList ecbmap ** *)
   HECBList
   (EcbMod.set ecbmap (v'15, Int.zero)
        (x, remove_tid (todelblock, Int.zero) x14)) **
   (* HTCBList tcbmap ** *)
   HTime v'18 **
   (* HCurTCB (cur_tcb_blk, Int.zero) ** *)
   LV pevent @ OS_EVENT ∗ |-> Vptr (v'15, Int.zero) **
   GV OSRdyGrp @ Int8u |-> Vint32 v'40 **
   GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
     (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'30
        (val_inj (and (Vint32 v'41) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7))))))) **
   GV OSTCBList @ OS_TCB ∗ |-> v'9 **
   GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
   (* Aie false ** *)
   (* Ais nil ** *)
   (* Acs (true :: nil) ** *)
   (* Aisr empisr ** *)
   tcbdllflag v'9
     ((v :: l1') ++
      (Vptr (next_tcb_block, Int.zero)
       :: Vptr (prev_tcb_block, Int.zero)
          :: Vptr (v'15, Int.zero)
             :: x0
                :: Vint32 i13
                   :: Vint32 x21
                      :: Vint32 v'53
                         :: Vint32 (v'53&ᵢ$ 7)
                            :: Vint32 (v'53 >>ᵢ $ 3)
                               :: Vint32 ($ 1<<ᵢ(v'53&ᵢ$ 7))
                                  :: Vint32 ($ 1<<ᵢ(v'53 >>ᵢ $ 3)) :: nil)
      :: (v'14
          :: Vptr (todelblock, Int.zero)
             :: x35
                :: x34
                   :: Vint32 i15
                      :: Vint32 i14
                         :: Vint32 i12
                            :: Vint32 i11
                               :: Vint32 i10 :: Vint32 i9 :: Vint32 i :: nil)
         :: l2') **
   G& OSPlaceHolder @ Int8u == vhold **
   (* A_isr_is_prop ** *)
   p_local OSLInv (cur_tcb_blk, Int.zero) init_lg **
   LV self @ Int8u |-> (V$ 0) **
   AOSEventFreeList v'3 **
   AOSQFreeList v'4 **
   AOSQFreeBlk v'5 **
   AOSMapTbl **
   AOSUnMapTbl **
   AOSIntNesting **
   sll v'20 v'21 OS_TCB_flag V_OSTCBNext **
   sllfreeflag v'20 v'21 **
   AOSTime (Vint32 v'18) **
   AGVars ** atoy_inv' ** LV prio @ Int8u |-> Vint32 v'53 )).

      clear.
      intro; intros.
      sep lifts (4:: 6::nil)%nat. 
      eapply elim_a_isr_is_prop.
      sep cancel Aisr.
      sep cancel Ais.
      sep cancel Acs.
      sep cancel Aie.
      sep pauto.

      unfold os_task.STKFREE.

      assert (exists mmm, TcbJoin (todelblock, Int.zero) (v'53, wait (hle2wait x (v'15, Int.zero)) i13 , x0) mmm tcbmap).
      apply tcb_get_join.
      unfold get, sig, join in *; simpl in *.
      unfold get, sig, join in *; simpl in *.
      go.

      destruct H103 as (tcbmap_left & tcbmapleft_join_hyp).


      eapply seq_rule.
      eapply derive_delother_rule.
      apply goodlinv.

       (* goodlinv *)
      go.
      unfold AEventData.
      destruct x22; go.
      unfold p_local.
      unfold CurTid; unfold LINV.
      unfold OSLInv.
      go.
      exact tcbmapleft_join_hyp.
      clear -H3; unfolds in H3.
      unfolds.
      simpljoin.
      eauto.
      intro; tryfalse.
      intro; intros.
      split.
      sep_get_rv.
      unfold p_local in H103.
      unfold CurLINV.
      sep pauto.
      sep cancel LINV.
      simpl; auto 1.
      hoare lift 37%nat pre.
      eapply backward_rule1.
      eapply dllsegflag_split.
      hoare_split_pure_all.
      unfold dllsegflag at 2.
      fold dllsegflag .
      hoare_split_pure_all.
      inverts H130.
      inverts H103.
      inverts H131.
      inverts H132.
      rewrite H101.

      (* Lemma dllsegflag_last_next_is_endstnl:
       *   forall l head endstnl endp next s P,
       *     s |= dllsegflag head endstnl (l++ (endp :: nil)) next  ** P ->
       *     next endp = Some endstnl.
       * Proof.
       *   induction l.
       *   intros.
       *   simpl (nil ++ endp :: nil) in H.
       *   unfold dllsegflag in H.
       *   sep normal in H.
       *   sep destruct H.
       *   sep split in H.
       *   subst.
       *   auto.
       * 
       *   intros.
       *   simpl ((a ::l ) ++ endp :: nil) in H.
       *   unfold1 dllsegflag in H.
       *   
       *   sep normal in H.
       *   sep destruct H.
       *   sep split in H.
       *   sep lift 2%nat in H.
       *   eapply IHl.
       *   eauto.
       * Qed. *)

      hoare_assert_pure ( (fun vl : vallist => nth_val 0 vl) (Vptr (todelblock, Int.zero)
                                                                   :: v'13
                                                                   :: x36
                                                                   :: x33
                                                                   :: Vint32 i22
                                                                   :: Vint32 i21
                                                                   :: Vint32 i20
                                                                   :: Vint32 i19
                                                                   :: Vint32 i18
                                                                   :: Vint32 i17 :: Vint32 i16 :: nil) = Some (Vptr v'48) ).
      eapply dllsegflag_last_next_is_endstnl.
      instantiate (4 := s0).
      sep cancel 5%nat 1%nat.
      eauto.

      hoare_split_pure_all.
      inverts H131.

      
      
      (* rewrite app_nil_l. *)
      (* hoare unfold. *)
      (* hoare lift 4%nat pre. *)
      unfold p_local at 2.
      unfold OSLInv at 3.
      unfold LINV.
      hoare_split_pure_all.
      (* unfold1 dllseg. *)
      (* hoare unfold. *)
      eapply backward_rule1.
      intro; intros.
      (* Print Ltac sep_combine. *)
      sep combine ( get_off_addr (todelblock, Int.zero) ($ 24)  ) in H133.
      eauto.

      hoare lift 5%nat pre.
      eapply seq_rule.
      eapply assign_rule'.
      Focus 2.

      intro; intros.
      split.
      eapply field_asrt_impl.
      Focus 3.
      sep cancel 13%nat 1%nat.
      eauto.
      reflexivity.
      reflexivity.
      sep get rv.
      eapply eq_int; auto.

      intro; intros.
      unfold p_local, OSLInv.
      sep pauto.
      unfold LINV.
      sep pauto.
      sep lift 39%nat in H133.
      unfold OSLInv in H133.
      sep normal in H133.
      sep destruct H133.
      sep split in H133.
      unfold init_lg in H131; destruct H131.
      inverts H131.
      sep cancel 1%nat 1%nat.
      eauto.

      simpl; auto.
      splits; eauto.
      unfolds; auto.
      

      eapply backward_rule1.
      intro; intros.
      sep lifts (8::10::nil)%nat in H133.
      eapply add_a_isr_is_prop in H133.
      eauto.
      hoare lift 4%nat pre.
      eapply seq_rule.

      eapply excrit1_rule'_ISnil_ISRemp''.
      intro.
      intros.
      sep cancel atoy_inv'.
      sep cancel Aisr.
      sep cancel Aie.
      sep cancel Ais.
      sep cancel Acs.
      unfold p_local.
      sep pauto.
      unfold LINV.
      sep pauto.
      sep cancel OSLInv.
      eapply poi_OSINV_imply_OSInv.
      unfold poi_OSINV.
      sep pauto.
      sep cancel AOSEventFreeList.
      sep cancel AOSQFreeList.
      sep cancel AOSQFreeBlk.
      unfold AECBList.
instantiate (14 := (x11 ++ (Vint32 i7 :: Vint32 v'50 :: Vint32 i8 :: x29 :: x30 :: v'6 :: nil,
                                 (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'37
                                                 (val_inj
                                                    (and (Vint32 v'51) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7)))))))
                                ) :: x15)).
      instantiate (13 :=(x23 ++ x22 :: x24) ).


      (* instantiate (x3 := (x5 ++ (Vint32 i8 :: Vint32 v'53 :: Vint32 i9 :: x29 :: x30 :: v'6 :: nil,
       *                            (update_nth_val (Z.to_nat (Int.unsigned (v'56 >>ᵢ $ 3))) v'40
       *                                            (val_inj
       *                                               (and (Vint32 v'54) (Vint32 (Int.not ($ 1<<ᵢ(v'56&ᵢ$ 7)))))))
       *                           ) :: x15)).
       * instantiate (x2 :=(x23 ++ x22 :: x24) ). *)
      sep pauto.
      eapply evsllseg_merge.
            eapply (ecblistp_length_eq_1 _ _ _ _ _ _ H80).
      eapply (ecblistp_length_eq_1 _ _ _ _ _ _ H81).

      (* admit.
       * admit. *)
      unfold1 evsllseg .
      sep pauto.
      unfold AEventNode.
      sep cancel evsllseg.
      sep cancel evsllseg.
      unfold AOSEvent.
      unfold node.
      unfold AOSEventTbl.
      sep pauto.
      sep cancel Aarray.

      sep lift 2%nat.
      eapply AED_changegrp.
      sep cancel AEventData.
      unfold Astruct.
      unfold OS_EVENT.
      unfold Astruct'.
      sep normal.
      sep cancel 16%nat 2%nat.
      repeat sep cancel 16%nat 1%nat.
      unfold AOSTCBPrioTbl.
      sep pauto.
      sep cancel 20%nat 2%nat.
      sep cancel 14%nat 1%nat.
      unfold AOSRdyTblGrp.
      unfold AOSRdyTbl.
      unfold AOSRdyGrp.
      sep pauto.
      unfold poi_AOSTCBList.
      
      sep pauto.
      instantiate (4 := (
(v'43 ++
               (Vptr (next_tcb_block, Int.zero)
                :: v'13
                   :: x36
                      :: x33
                         :: Vint32 i22
                            :: Vint32 i21
                               :: Vint32 i20
                                  :: Vint32 i19
                                     :: Vint32 i18
                                        :: Vint32 i17 :: Vint32 i16 :: nil)
               :: nil)  ++
                         (v'54
               :: Vptr (prev_tcb_block, Int.zero)
                  :: x35
                     :: x34
                        :: Vint32 i15
                           :: Vint32 i14
                              :: Vint32 i12
                                 :: Vint32 i11
                                    :: Vint32 i10
                                       :: Vint32 i9 :: Vint32 i :: nil) 
                          
                            :: l2')).
unfold tcbdllseg.
      unfold tcbdllflag.
      unfold1 dllsegflag.
      unfold1 dllseg.
      unfold node.
      sep pauto.

      
      (* unfold TCB_Not_In.
       * sep pauto.
       * eapply tcbdllseg_compose.
       * unfold tcbdllseg.
       * unfold1 dllseg.
       * unfold node.
       * sep pauto.
       * sep cancel 10%nat 1%nat.
       * sep cancel 12%nat 1%nat. *)
      (* Goal forall l head headprev tail tailnext x t fprev fnext,
       *        dllseg head headprev tail tailnext (l++x::nil) t fprev fnext <==>
       *               EX tail', dllseg head headprev tail' tail l t fprev fnext **
       *                                [| |] *)
      eapply dllseg_is_poi.
      eapply split_poillseg.
      sep eexists.
      eapply split_poillseg.
      sep eexists.
      rewrite <- dllseg_is_poi.
      sep lift 2%nat.
      rewrite <- dllseg_is_poi.
      sep lift 3%nat.
      rewrite <- dllseg_is_poi.
      unfold1 dllseg.
      unfold node.
      sep pauto.
      sep cancel 11%nat 1%nat.
      sep cancel 10%nat 1%nat.
      sep cancel 11%nat 1%nat.
      sep cancel dllseg.

      sep lift 4%nat in H133.
      rewrite dllsegflag_is_poi in H133.
      apply split_poillseg in H133.
      sep destruct H133.
      apply dllsegflag_is_poi.
      apply split_poillseg.
      sep eexists.
      apply split_poillseg.
      sep eexists.
      sep pauto.
      sep cancel 1%nat 1%nat.
      unfold1 @poi_llseg in *.
      sep pauto.
      sep lift 2%nat.
      rewrite <- dllsegflag_is_poi.
      sep cancel dllsegflag.
      instantiate (4 := x16).
      sep cancel 1%nat 2%nat.
      sep cancel 2%nat 1%nat.

      (* freelist *)
      unfold AOSTCBFreeList'.
      sep pauto.
      eapply intro_or_l. 
      unfold TCBFree_Not_Eq.
      sep pauto.
      instantiate ( 2 := (
(v'20
               :: Vptr (prev_tcb_block, Int.zero)
                  :: Vnull
                     :: x0
                        :: V$ 0
                           :: V$ OS_STAT_RDY
                              :: Vint32 v'53
                                 :: Vint32 (v'53&ᵢ$ 7)
                                    :: Vint32 (v'53 >>ᵢ $ 3)
                                       :: Vint32 ($ 1<<ᵢ(v'53&ᵢ$ 7))
                                          :: Vint32 ($ 1<<ᵢ(v'53 >>ᵢ $ 3))
                                             :: nil) :: v'21
                            
                          )).
      unfold1 sll.
      unfold1 sllfreeflag.
      unfold1 sllseg.
      unfold1 sllsegfreeflag.
      
      sep pauto.
      unfold node.
      unfold sll, sllfreeflag in H133.
      sep pauto.
      sep cancel sllsegfreeflag.
      sep cancel sllseg.
      sep cancel Astruct.
      eauto.
      go.
      eapply isptr_is_definitely_ptr.
      eapply sll_head_isptr.
      instantiate (5:=s).
      unfold sll.
      sep cancel sllseg.
      go.
      go.
      
      go.
      intro; tryfalse.
      2:go.
      go.
      go.
      intro; tryfalse.
      intro; tryfalse.
      go.
      go.
      go.
      go.
      go.
      go.
      intro; tryfalse.
      {


         eapply TCBList_merge_prop.
         instantiate (2 := v'17).
         instantiate (1 := x13).

         eapply some_join_lemma0; eauto.
         exact H22.
         exact tcbmapleft_join_hyp.
                  
  (* H22 : TcbJoin (cur_tcb_blk, Int.zero)
   *         (v'53, wait (hle2wait x (v'15, Int.zero)) i13, x0) x13 v'19
   * H28 : TcbMod.join v'17 v'19 tcbmap
   * tcbmapleft_join_hyp : TcbJoin (cur_tcb_blk, Int.zero)
   *                         (v'53, wait (hle2wait x (v'15, Int.zero)) i13, x0)
   *                         tcbmap_left tcbmap
   * 
   *         *)
         rewrite app_last.
         simpl.
         go.
         Focus 2.

         eapply  tcblist_p_hold_for_del_a_tcb_at_head .
         omega.

        2:go.
        2:go.
        2: exact H22.
        2: exact backup.
        unfolds in H6.
        simpljoin.
        clear -H135 H28.
        eapply R_Prio_No_Dup_hold_for_subset.
        apply TcbMod.join_comm; eauto.
        eauto.

        
        eapply OSTimeDlyPure.update_rtbl_tcblist_hold.

        omega.
        unfold nat_of_Z; eapply nv'2nv.
        exact H60.
        intro; tryfalse.
        intros.

        unfolds in H6.
        simpljoin.
        clear -H28 H22 H136 H134.
        eapply H136.
        instantiate (2 := tid).
        instantiate (1 := (todelblock, Int.zero)).
        intro; subst tid.
        eapply TcbMod.map_join_get_some.
        auto.
        exact H28.
        unfold TcbJoin in H22.
        unfold join,sig,get in H22; simpl in H22.
        go.
        
        unfold TcbJoin in H22.
        unfold join,sig,get in H22; simpl in H22.
        go.
        
        unfold TcbJoin in H22.
        unfold join,sig,get in H22; simpl in H22.
        unfold get; simpl.
        go.
        unfold TcbJoin in H22.
        unfold join,sig,get in H22; simpl in H22.
        unfold get; simpl.
        go.
        eapply TCBList_P_hold_for_last_change.
        rewrite H101 in H29.
        exact H29.
        
        
  (* H28 : TcbMod.join v'17 v'19 tcbmap
   * H22 : TcbJoin (cur_tcb_blk, Int.zero)
   *         (v'53, wait (hle2wait x (v'15, Int.zero)) i13, x0) x13 v'19 *)
      }
       (* tcblist_p hold for deleting a tcb *)

      {
(* ** ac:         SearchAbout ptr_in_tcbdllseg. *)
(* ** ac:         Search ptr_in_tcbdllseg. *)
(* ** ac:         SearchAbout ptr_in_tcbdllseg. *)
        assert (list_all_P (fun x10 : vallist => V_OSTCBNext x10 <> None) (v'43 ++
         (Vptr (todelblock, Int.zero)
          :: v'13
             :: x36
                :: x33
                   :: Vint32 i22
                      :: Vint32 i21
                         :: Vint32 i20
                            :: Vint32 i19
                               :: Vint32 i18
                                  :: Vint32 i17 :: Vint32 i16 :: nil) :: nil
                                                                         )).

 eapply TCBLP_imply_nextnotnull_list.
 rewrite H101 in H29.
 exact H29.
 rewrite  get_last_tcb_ptr_appsig.
 eauto.


 
        eapply  ptr_in_tcblist_app in H24.
        destruct H24.
        apply  ptr_in_tcblist_app.

        2: left; eapply ptr_in_tcblist_last_ir.
        apply  list_all_P_app.
        apply  list_all_P_app in H134.
        simpljoin.
        splits; auto.
        simpl; go.
        (* unfold V_OSTCBNext; simpl; intro; tryfalse. *)
        rewrite H101 in H24; exact H24.

        
        apply  ptr_in_tcblist_app.

        apply  list_all_P_app.
        apply  list_all_P_app in H134.
        simpljoin.
        splits; auto.
        simpl; go.
        (* unfold V_OSTCBNext; simpl; intro; tryfalse. *)

        right.
        
        rewrite          get_last_tcb_ptr_appsig.
        rewrite H101 in H24.
        rewrite          get_last_tcb_ptr_appsig in H24.
        eapply  ptr_in_tcbdllseg_change_head.
        Focus 2.
        eapply ptr_in_tcbdllseg_not_head. 
        2: exact H24.
        reflexivity.
        simpl; intro; tryfalse.
        reflexivity.
        rewrite H101.
        exact H134.
        
      }
       (* from tcblist_p, get they are all different? *)
      split.
      assumption.
      eapply (H68 _ H55).
      clear -H0; unfold OS_IDLE_PRIO.
      csimpl OS_LOWEST_PRIO.
      int auto.
        
      {
        eapply  r_priotbl_p_hold_for_del_a_tcb.
        omega.
        assumption.
        eauto 1.

        exact   tcbmapleft_join_hyp .

      }

       (* r_priotbl_p hold for deleting a tcb *)
      
{
  eapply  rtbl_remove_RL_RTbl_PrioTbl_P_hold'.
  omega.
  rewrite Int.repr_unsigned.
  reflexivity.

  rewrite Int.repr_unsigned.
  reflexivity.

  2: assumption.
  unfold nat_of_Z.
  apply nv'2nv.
  
  assumption.
  intro; tryfalse.
  
      }

       (* rl_rtbl_ptbl_p hold for deleting a tcb *)

      split.
      eapply array_type_vallist_match_hold.
      assumption.

      rewrite H7.
      clear -H; mauto.
      reflexivity.

      rewrite hoare_assign.update_nth_val_len_eq.
      assumption.
      go.
      go.
      go.
      go.
      clear -H96 H134.
      unfolds in H96.
      change Byte.max_unsigned with 255%Z in * .
      math simpl in H96.
      omega.
      go.
      {
        eapply ECBLP_hold4del_a_tcb; eauto.
        3:exact tcbmapleft_join_hyp.
        clear -H6; unfolds in H6; tauto.
        clear -H6; unfolds in H6; tauto.
      }

       (* from H101 : RL_Tbl_Grp_P
           (update_nth_val (Z.to_nat (Int.unsigned (v'56 >>ᵢ $ 3))) v'40
              (val_inj
                 (and (Vint32 v'54) (Vint32 (Int.not ($ 1<<ᵢ(v'56&ᵢ$ 7)))))))
           (Vint32 v'53), ECBList_P holds for deleting a tcb *)

        

       

      {
      eapply poi_is_rtep.
        eapply poi_RHTEP_hold_for_del_a_tcb.
        assumption.
        go.
        eapply tcbmapleft_join_hyp.
        go.
        clear -H2 H61 H62; unfolds; splits; auto.
      }

       (* change to poi,
from some_pure_hyp : forall (eid : tidspec.A) (pr : int32) 
                    (tid0 : tid) (opr : int32) (wls : waitset),
                  EcbMod.get ecbmap eid =
                  Some (absmutexsem pr (Some (tid0, opr)), wls) ->
                  tid0 <> (cur_tcb_blk, Int.zero)
get rh_te_p hold for deleting a tcb
              *)
      go.
      hoare forward.
      sep cancel Aisr.
      sep cancel Acs.
      sep cancel Ais.
      sep cancel Aie.
      sep cancel Aop.
      sep cancel p_local.
      eauto.
      unfolds; auto.
      go.
      go.
      linv_solver.
      linv_solver.

      unfold OS_SchedPost.
      unfold OS_SchedPost'.
      unfold getasrt.
      hoare forward.
      inverts H134.
      reflexivity.
    }


    Unshelve.
    exact (Afalse).

    exact (V$0).
    exact (V$0).
    exact (V$0).
    exact (V$0).
    exact (V$0).
    exact (V$0).
    exact (V$0).
    exact (V$0).
    exact (V$0).
    exact (V$0).
    exact (V$0).
    exact (V$0).
    exact (V$0).
    exact (V$0).
    exact (V$0).
    exact (V$0).
    exact (V$0).
    exact (V$0).
    exact (V$0).
    exact (V$0).

    }


    
Qed.

