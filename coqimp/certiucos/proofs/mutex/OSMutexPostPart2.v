Require Import ucos_include.
Require Import OSMutex_common.
Require Import os_ucos_h.
Require Import mutex_absop_rules.
Require Import sep_lemmas_ext.
Require Import symbolic_lemmas.
Local Open Scope code_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.
Local Open Scope list_scope.


(* Require Import ucert.
 * Require Import ucert.
 * Require Import os_code_defs.
 * Require Import mathlib.
 * Require Import OSMutex_common.
 * Require Import lab.
 * Require Import gen_lemmas.
 * Open Scope code_scope. *)

 Theorem MutexPostPart1: (*gen_MutexPostPart1. *)
forall
  (v' v'0 v'1 v'2 : val
)(
  v'3 v'4 v'5 : list vallist
)(
  v'6 : list EventData
)(
  v'7 : list os_inv.EventCtr
)(
  v'8 : vallist
)(
  v'9 v'10 : val
)(
  v'11 : list vallist
)(
  v'12 : vallist
)(
  v'13 : list vallist
)(
  v'14 : vallist
)(
  v'15 : val
)(
  v'16 : EcbMod.map
)(
  v'17 : TcbMod.map
)(
  v'18 : int32
)(
  v'19 : addrval
)(
  v'20 : True
)(
  v'21 : val
)(
  v'22 : list vallist
)(
  v'25 v'26 : list os_inv.EventCtr
)(
  v'27 v'28 : list EventData
)(
  v'30 : vallist
)(
  v'31 : val
)(
  v'33 v'35 : list vallist
)(
  v'36 : vallist
)(
  v'38 : EcbMod.map
)(
  v'39 : TcbMod.map
)(
  v'42 : val
)(
  v'44 : vallist
)(
  v'46 : val
)(
  v'47 v'48 v'49 : EcbMod.map
)(
  w : waitset
)(
  v'51 : addrval
)(
  H3 : ECBList_P v'46 Vnull v'26 v'28 v'48 v'39
)(
  H17 : EcbMod.join v'47 v'49 v'38
)(
  H12 : length v'25 = length v'27
)(
  H16 : isptr v'46
)(
  v'23 : addrval
)(
  v'29 : block
)(
  H11 : array_type_vallist_match Int8u v'44
)(
  H19 : length v'44 = ∘ OS_EVENT_TBL_SIZE
)(
  x3 : val
)(
  i : int32
)(
  H21 : Int.unsigned i <= 255
)(
  H18 : RL_Tbl_Grp_P v'44 (Vint32 i)
)(
  H24 : isptr v'46
)(
  H2 : ECBList_P v'42 (Vptr (v'29, Int.zero)) v'25 v'27 v'47 v'39
)(
  H14 : id_addrval' (Vptr (v'29, Int.zero)) OSEventTbl OS_EVENT = Some v'23
)(
  H20 : Int.unsigned ($ OS_EVENT_TYPE_MUTEX) <= 255
)(
  x : int32
)(
  H10 : Int.unsigned x <= 65535
)(
  H15 : Int.unsigned (x >>ᵢ $ 8) < 64
)(
  H22 : Int.unsigned x <= 65535
)(
  v'24 v'40 : val
)(
  v'43 v'45 : TcbMod.map
)(
  v'50 : val
)(
  v'52 : block
)(
  H31 : v'31 <> Vnull
)(
  H32 : join v'43 v'45 v'39
)(
  H33 : TCBList_P v'31 v'33 v'36 v'43
)(
  H30 : Vptr (v'52, Int.zero) <> Vnull
)(
  x8 x9 : val
)(
  H37 : isptr x9
)(
  H38 : isptr x8
)(
  i6 : int32
)(
  H39 : Int.unsigned i6 <= 65535
)(
  i5 : int32
)(
  H40 : Int.unsigned i5 <= 255
)(
  i4 : int32
)(
  H41 : Int.unsigned i4 <= 255
)(
  i3 : int32
)(
  H42 : Int.unsigned i3 <= 255
)(
  i2 : int32
)(
  H43 : Int.unsigned i2 <= 255
)(
  i1 : int32
)(
  H44 : Int.unsigned i1 <= 255
)(
  i0 : int32
)(
  H45 : Int.unsigned i0 <= 255
)(
  H36 : isptr v'24
)(
  H27 : isptr v'50
)(
  H34 : TCBList_P (Vptr (v'52, Int.zero))
          ((v'50
            :: v'24
               :: x9
                  :: x8
                     :: Vint32 i6
                        :: Vint32 i5
                           :: Vint32 i4
                              :: Vint32 i3
                                 :: Vint32 i2
                                    :: Vint32 i1 :: Vint32 i0 :: nil) :: v'35)
          v'36 v'45
)(
  H : RH_TCBList_ECBList_P v'16 v'17 (v'52, Int.zero)
)(
  H0 : RH_CurTCB (v'52, Int.zero) v'17
)(
  H7 : RH_TCBList_ECBList_P v'38 v'39 (v'52, Int.zero)
)(
  H8 : RH_CurTCB (v'52, Int.zero) v'39
)(
  H23 : isptr (Vptr (v'52, $ 0))
)(
  H5 : R_ECB_ETbl_P (v'29, Int.zero)
         (V$ OS_EVENT_TYPE_MUTEX
          :: Vint32 i :: Vint32 x :: Vptr (v'52, $ 0) :: x3 :: v'46 :: nil,
         v'44) v'39
)(
  H1 : ECBList_P v'42 Vnull
         (v'25 ++
          ((V$ OS_EVENT_TYPE_MUTEX
            :: Vint32 i :: Vint32 x :: Vptr (v'52, $ 0) :: x3 :: v'46 :: nil,
           v'44) :: nil) ++ v'26)
         (v'27 ++ (DMutex (Vint32 x) (Vptr (v'52, $ 0)) :: nil) ++ v'28) v'38
         v'39
)(
  H28 : Int.ltu i4 (x >>ᵢ $ 8) = false
)(
  H29 : x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 = $ OS_MUTEX_AVAILABLE \/
        x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 <> $ OS_MUTEX_AVAILABLE
)(
  H35 : x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 <> $ OS_MUTEX_AVAILABLE
)(
  H47 : Int.ltu (x >>ᵢ $ 8) (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = true
)(
  H48 : Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) < 64
)(
  H6 : EcbMod.joinsig (v'29, Int.zero)
         (absmutexsem (x >>ᵢ $ 8)
            (Some (v'52, $ 0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), w) v'48 v'49
)(
  H4 : Some (v'52, $ 0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = None -> w = nil
)(
  H9 : forall (tid0 : tid) (opr : int32),
       Some (v'52, $ 0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = Some (tid0, opr) ->
       Int.ltu (x >>ᵢ $ 8) opr = true /\ Int.unsigned opr < 64
)(
  H13 : w <> nil -> Some (v'52, $ 0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) <> None
)(
  H25 : x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 = $ OS_MUTEX_AVAILABLE ->
        Some (v'52, $ 0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = None /\
        Vptr (v'52, $ 0) = Vnull
)(
  H26 : x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 <> $ OS_MUTEX_AVAILABLE ->
        exists tid,
        Vptr (v'52, $ 0) = Vptr tid /\
        Some (v'52, $ 0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) =
        Some (tid, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)
)(
  backup : RLH_ECBData_P (DMutex (Vint32 x) (Vptr (v'52, $ 0)))
             (absmutexsem (x >>ᵢ $ 8)
                (Some (v'52, $ 0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), w)
)(
  v'32 : val
)(
  H46 : array_type_vallist_match OS_TCB ∗ v'30
)(
  H51 : length v'30 = 64%nat
)(
  H49 : RL_RTbl_PrioTbl_P v'36 v'30 v'51
)(
  H50 : R_PrioTbl_P v'30 v'39 v'51
)(
  x1 : val
)(
  H52 : nth_val (Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) v'30 =
        Some x1
)(
  x0 : val
)(
  H53 : nth_val (Z.to_nat (Int.unsigned (x >>ᵢ $ 8))) v'30 = Some x0
)(
  H54 : array_type_vallist_match Int8u v'36
)(
  H58 : length v'36 = ∘ OS_RDY_TBL_SIZE
)(
  i7 : int32
)(
  H55 : Int.unsigned i7 <= 255
)(
  H57 : prio_in_tbl ($ OS_IDLE_PRIO) v'36
)(
  H56 : RL_Tbl_Grp_P v'36 (Vint32 i7)
)(
  x2 : int32
)(
  fffa : length OSUnMapVallist = 256%nat ->
         (Z.to_nat (Int.unsigned i) < 256)%nat ->
         exists x,
         Vint32 x2 = Vint32 x /\ true = rule_type_val_match Int8u (Vint32 x)
)(
  H59 : length OSUnMapVallist = 256%nat
)(
  H60 : (Z.to_nat (Int.unsigned i) < 256)%nat
)(
  H61 : nth_val' (Z.to_nat (Int.unsigned i)) OSUnMapVallist = Vint32 x2
)(
  H62 : true = rule_type_val_match Int8u (Vint32 x2)
)(
  fffbb : Int.unsigned x2 < 8
)(
  fffbb2 : (Z.to_nat (Int.unsigned x2) < length v'44)%nat
)(
  H19'' : length v'44 = Z.to_nat 8
)(
  x4 : int32
)(
  H63 : nth_val' (Z.to_nat (Int.unsigned x2)) v'44 = Vint32 x4
)(
  H64 : Int.unsigned x4 <= 255
)(
  H65 : (Z.to_nat (Int.unsigned x4) < length OSUnMapVallist)%nat
)(
  x5 : int32
)(
  H66 : nth_val' (Z.to_nat (Int.unsigned x4)) OSUnMapVallist = Vint32 x5
)(
  H67 : Int.unsigned x5 <= 255
)(
  ttfasd : Int.unsigned x5 < 8
)(
  H68 : val_inj
          (bool_and
             (val_inj
                (notint
                   (val_inj
                      (if Int.eq i ($ 0)
                       then Some (Vint32 Int.one)
                       else Some (Vint32 Int.zero)))))
             (val_inj
                (bool_or
                   (val_inj
                      (if
                        Int.ltu ((x2<<ᵢ$ 3) +ᵢ  x5)
                          (Int.modu (x >>ᵢ $ 8) ($ Byte.modulus))
                       then Some (Vint32 Int.one)
                       else Some (Vint32 Int.zero)))
                   (val_inj
                      (if
                        Int.eq ((x2<<ᵢ$ 3) +ᵢ  x5)
                          (Int.modu (x >>ᵢ $ 8) ($ Byte.modulus))
                       then Some (Vint32 Int.one)
                       else Some (Vint32 Int.zero)))))) = 
        Vint32 Int.zero \/
        val_inj
          (bool_and
             (val_inj
                (notint
                   (val_inj
                      (if Int.eq i ($ 0)
                       then Some (Vint32 Int.one)
                       else Some (Vint32 Int.zero)))))
             (val_inj
                (bool_or
                   (val_inj
                      (if
                        Int.ltu ((x2<<ᵢ$ 3) +ᵢ  x5)
                          (Int.modu (x >>ᵢ $ 8) ($ Byte.modulus))
                       then Some (Vint32 Int.one)
                       else Some (Vint32 Int.zero)))
                   (val_inj
                      (if
                        Int.eq ((x2<<ᵢ$ 3) +ᵢ  x5)
                          (Int.modu (x >>ᵢ $ 8) ($ Byte.modulus))
                       then Some (Vint32 Int.one)
                       else Some (Vint32 Int.zero)))))) = Vnull
)(
  last_condition : i5 = $ OS_STAT_RDY /\ i6 = $ 0
                                     ),
   {|OS_spec, GetHPrio, OSLInv, I,
   fun v : option val =>
   ( <|| END v ||>  **
    p_local OSLInv (v'52, Int.zero) init_lg **
    ((EX v0 : val, LV pevent @ OS_EVENT ∗ |-> v0) **
     (EX v0 : val, LV os_code_defs.x @ Int8u |-> v0) **
     (EX v0 : val, LV pip @ Int8u |-> v0) **
     (EX v0 : val, LV prio @ Int8u |-> v0) **
     (EX v0 : val, LV legal @ Int8u |-> v0) ** Aemp) **
    Aie true ** Ais nil ** Acs nil ** Aisr empisr) **
   A_dom_lenv
     ((pevent, OS_EVENT ∗)
      :: (os_code_defs.x, Int8u)
         :: (pip, Int8u) :: (prio, Int8u) :: (legal, Int8u) :: nil), Afalse|}
   |- (v'52, Int.zero)
   {{ <|| mutexpost (Vptr (v'29, Int.zero) :: nil) ||>  **
     LV os_code_defs.x @ Int8u |-> Vint32 ((x2<<ᵢ$ 3) +ᵢ  x5) **
     LV legal @ Int8u |-> Vint32 x2 **
     PV v'51 @ Int8u |-> v'32 **
     Astruct (v'52, Int.zero) OS_TCB_flag
       (v'50
        :: v'24
           :: x9
              :: x8
                 :: Vint32 i6
                    :: Vint32 i5
                       :: Vint32 i4
                          :: Vint32 i3
                             :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil) **
     dllseg v'50 (Vptr (v'52, Int.zero)) v'40 Vnull v'35 OS_TCB_flag
       (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
     GV OSTCBList @ OS_TCB ∗ |-> v'31 **
     dllseg v'31 Vnull v'24 (Vptr (v'52, Int.zero)) v'33 OS_TCB_flag
       (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
     GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (v'52, Int.zero) **
     LV prio @ Int8u
     |-> Vint32 (Int.modu (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) ($ Byte.modulus)) **
     LV pip @ Int8u |-> Vint32 (Int.modu (x >>ᵢ $ 8) ($ Byte.modulus)) **
     Astruct (v'29, Int.zero) OS_EVENT
       (V$ OS_EVENT_TYPE_MUTEX
        :: Vint32 i :: Vint32 x :: Vptr (v'52, $ 0) :: x3 :: v'46 :: nil) **
     Aarray v'23 (Tarray Int8u ∘ OS_EVENT_TBL_SIZE) v'44 **
     Aie false **
     Ais nil **
     Acs (true :: nil) **
     Aisr empisr **
     GV OSEventList @ OS_EVENT ∗ |-> v'42 **
     evsllseg v'42 (Vptr (v'29, Int.zero)) v'25 v'27 **
     evsllseg v'46 Vnull v'26 v'28 **
     A_isr_is_prop **
     tcbdllflag v'31
       (v'33 ++
        (v'50
         :: v'24
            :: x9
               :: x8
                  :: Vint32 i6
                     :: Vint32 i5
                        :: Vint32 i4
                           :: Vint32 i3
                              :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil)
        :: v'35) **
     GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE) v'36 **
     GV OSRdyGrp @ Int8u |-> Vint32 i7 **
     GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64) v'30 **
     G& OSPlaceHolder @ Int8u == v'51 **
     HECBList v'38 **
     HTCBList v'39 **
     HCurTCB (v'52, Int.zero) **
     p_local OSLInv (v'52, Int.zero) init_lg **
     AOSEventFreeList v'3 **
     AOSQFreeList v'4 **
     AOSQFreeBlk v'5 **
     AOSMapTbl **
     GAarray OSUnMapTbl (Tarray Int8u 256) OSUnMapVallist **
     AOSIntNesting **
     AOSTCBFreeList v'21 v'22 **
     AOSTime (Vint32 v'18) **
     HTime v'18 **
     AGVars **
     atoy_inv' **
     LV pevent @ OS_EVENT ∗ |-> Vptr (v'29, Int.zero) **
     A_dom_lenv
       ((pevent, OS_EVENT ∗)
        :: (os_code_defs.x, Int8u)
           :: (pip, Int8u) :: (prio, Int8u) :: (legal, Int8u) :: nil)}} 
   If(OSTCBCur ′ → OSTCBPrio ==ₑ pip ′)
        {If(OSTCBPrioTbl ′ [prio ′] !=ₑ 〈 OS_TCB ∗ 〉 os_mutex.PlaceHolder)
              {EXIT_CRITICAL;ₛ
              RETURN ′ OS_ERR_ORIGINAL_NOT_HOLDER}  ;ₛ
        OSRdyTbl ′ [OSTCBCur ′ → OSTCBY] &= ∼ OSTCBCur ′ → OSTCBBitX;ₛ
        If(OSRdyTbl ′ [OSTCBCur ′ → OSTCBY] ==ₑ ′ 0)
             {OSRdyGrp ′ &= ∼ OSTCBCur ′ → OSTCBBitY}  ;ₛ
        OSTCBCur ′ → OSTCBPrio =ₑ prio ′;ₛ
        OSTCBCur ′ → OSTCBY =ₑ prio ′ ≫ ′ 3;ₛ
        OSTCBCur ′ → OSTCBBitY =ₑ OSMapTbl ′ [OSTCBCur ′ → OSTCBY];ₛ
        OSTCBCur ′ → OSTCBX =ₑ prio ′ &ₑ ′ 7;ₛ
        OSTCBCur ′ → OSTCBBitX =ₑ OSMapTbl ′ [OSTCBCur ′ → OSTCBX];ₛ
        OSRdyGrp ′ =ₑ OSRdyGrp ′ |ₑ OSTCBCur ′ → OSTCBBitY;ₛ
        OSRdyTbl ′ [OSTCBCur ′ → OSTCBY] =ₑ
        OSRdyTbl ′ [OSTCBCur ′ → OSTCBY] |ₑ OSTCBCur ′ → OSTCBBitX;ₛ
        OSTCBPrioTbl ′ [prio ′] =ₑ 〈 OS_TCB ∗ 〉 OSTCBCur ′;ₛ
        OSTCBPrioTbl ′ [pip ′] =ₑ 〈 OS_TCB ∗ 〉 os_mutex.PlaceHolder}  ;ₛ
   If(pevent ′ → OSEventGrp !=ₑ ′ 0)
        {os_code_defs.x ′ =ₑ ′ OS_STAT_MUTEX;ₛ
        prio ′ =ᶠ OS_EventTaskRdy (·pevent ′, 〈 (Void) ∗ 〉 pevent ′,
        os_code_defs.x ′·);ₛ
        pevent ′ → OSEventCnt &= ′ OS_MUTEX_KEEP_UPPER_8;ₛ
        pevent ′ → OSEventCnt =ₑ pevent ′ → OSEventCnt |ₑ prio ′;ₛ
        pevent ′ → OSEventPtr =ₑ OSTCBPrioTbl ′ [prio ′];ₛ
        EXIT_CRITICAL;ₛ
        OS_Sched (­);ₛ
        RETURN ′ OS_NO_ERR}  ;ₛ
   pevent ′ → OSEventCnt =ₑ pevent ′ → OSEventCnt |ₑ ′ OS_MUTEX_AVAILABLE;ₛ
   pevent ′ → OSEventPtr =ₑ NULL;ₛ
   EXIT_CRITICAL;ₛ
   RETURN ′ OS_NO_ERR {{Afalse}}
                 .
Proof.
    intros.
    protect last_condition.
    unfold AOSRdyTblGrp.
    unfold AOSMapTbl.
    unfold AOSRdyTbl.
    unfold AOSRdyGrp.
    hoare_split_pure_all.

    simpljoin.


    lets backup2: H34.
    unfold1 TCBList_P in H34.
    simpljoin.
    inverts H34.
    inverts H69.
    unfolds in H71.
    simpljoin.
    destruct x11; destruct p.
    simpljoin.
    inverts H34.
    inverts H69.
    unfolds in H71.
    simpljoin.
    inverts H71; inverts H75; inverts H74; inverts H69.
    inverts H34; inverts H83; inverts H76.

    lets r1 : post_intlemma3 H15.
    lets r2 : post_intlemma4 H48.
    lets r3 : post_intlemma3 H48.
    lets r4 : post_intlemma4 H15.

    assert (array_type_vallist_match Int8u OSMapVallist).
    unfolds.
    unfold OSMapVallist.
    splits; auto; unfolds.
    assert (length OSMapVallist = 8%nat) by reflexivity.
    assert ( (Z.to_nat (Int.unsigned (Int.shru (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) ($ 3)))) < 8)%nat.
    clear -H48.
    remember (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8).
    mauto.
    lets fff: nthval'_has_value H34 H69 H71.
    simpljoin.

    assert ( (Z.to_nat (Int.unsigned (Int.and (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) ($ 7)))) < 8)%nat.
    clear -H48.
    remember (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8).
    mauto.

    lets ffff: nthval'_has_value H34 H69 H76.
    simpljoin.     assert ( (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7))) < 8)%nat.
    clear -H48.
    remember (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8).
    mauto.

    lets fff: nthval'_has_value osmapvallist_int8u osmapvallist_length8 H80.
    simpljoin.

    lets r5 : post_intlemma3 H85.
    lets r6:  post_intlemma4 H85.
    

    lets rr1: intlt2nat r1.
    lets rr2: intlt2nat r2.
    lets rr3: intlt2nat r3.
    lets rr4: intlt2nat r4.
    lets rr5: intlt2nat r5.
    lets rr6: intlt2nat r6.

    lets rrr1: intlt2intlt r1.
    lets rrr2: intlt2intlt r2.
    lets rrr3: intlt2intlt r3.
    lets rrr4: intlt2intlt r4.
    lets rrr5: intlt2intlt r5.
    lets rrr6: intlt2intlt r6.


    lets HH58 : H58.
    unfold OS_RDY_TBL_SIZE, nat_of_Z in HH58.

    
    rewrite <- HH58 in rr1, rr2, rr3, rr4, rr5, rr6,  rrr1, rrr2, rrr3, rrr4, rrr5, rrr6.

    lets aa:  array_type_vallist_match_imp_rule_type_val_match rr1 H54.
    lets aa2:  array_type_vallist_match_imp_rule_type_val_match rr3 H54.
    lets aa3:  array_type_vallist_match_imp_rule_type_val_match rr5 H54.

    simpljoin.


    lets bb: ruletypevalmatch8u aa.
    lets bb2: ruletypevalmatch8u aa2.
    lets bb3: ruletypevalmatch8u aa3.
    simpljoin.


    hoare forward.
    go.
    apply del_intlemma1.
    go.
    destruct ( Int.eq x6 (Int.modu (x >>ᵢ $ 8) ($ Byte.modulus))); simpl; intro; tryfalse.
    (* pauto. *)
    hoare forward.
    hoare_split_pure_all.
    
    eapply ift_rule''.
    unfold os_mutex.PlaceHolder.
    intro.
    intros.
    eapply uop_rv; [ idtac | simpl; auto | auto | simpl; auto ].

    eapply bop_rv; [ idtac | idtac | simpl; auto | auto | simpl; auto ].
    Focus 2.
    eapply cast_rv_tptr.
    eapply addrof_gvar_rv.
    eapply dom_lenv_imp_notin_lenv.
    instantiate (1:=       ((pevent, OS_EVENT ∗)
                              :: (os_code_defs.x, Int8u)
                              :: (pip, Int8u) :: (prio, Int8u) :: (legal, Int8u) :: nil)).

    simpl.
    auto.
    sep auto.
    auto.
    sep_get_rv.

    rewrite mutexpost_intlemma1.
    clear -H48.
    remember  (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8).
    mauto.
    auto.
    rewrite mutexpost_intlemma1.
    clear -H48.
    remember  (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8).
    mauto.
    auto.
    simpljoin.
    rewrite H51.
    rewrite mutexpost_intlemma1.
    clear -H48.
    remember  (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8).
    mauto.
    auto.
    rewrite mutexpost_intlemma1.

    apply array_type_vallist_match_imp_rule_type_val_match.
    simpljoin.
    rewrite H51.
    clear -H48.
    remember  (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8).
    mauto.
    auto.
    auto.

    

    rewrite mutexpost_intlemma1.
    rewrite (nth_val_nth_val'_some_eq _ _ H52).
    assert (rule_type_val_match (OS_TCB ∗) (nth_val' (Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) v'30) = true).
    apply array_type_vallist_match_imp_rule_type_val_match.
    rewrite H51.
    clear -H48.
    remember  (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8).
    mauto.
    auto.
    rewrite (nth_val_nth_val'_some_eq _ _ H52) in H94.
    unfolds in H94.
    clear -H94.
    destruct x1; tryfalse.
    simpl; auto.
    destruct v'51; simpl; intro; tryfalse.
    simpl.
    destruct a; destruct v'51.
    destruct (peq b b0); destruct (Int.eq i i0); simpl; intro; tryfalse.

    auto.
    auto.


    rewrite mutexpost_intlemma1.
    rewrite (nth_val_nth_val'_some_eq _ _ H52).
    assert (rule_type_val_match (OS_TCB ∗) (nth_val' (Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) v'30) = true).
    apply array_type_vallist_match_imp_rule_type_val_match.
    rewrite H51.
    clear -H48.
    remember  (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8).
    mauto.
    auto.
    rewrite (nth_val_nth_val'_some_eq _ _ H52) in H94.
    unfolds in H94.
    clear -H94.
    destruct x1; tryfalse.
    simpl; auto.
    destruct v'51; simpl; intro; tryfalse.
    simpl.
    destruct a; destruct v'51.
    destruct (peq b b0); destruct (Int.eq i i0); simpl;  intro; tryfalse.

    auto.
    eauto.
    simpl.
    eauto.

    hoare abscsq.
    apply noabs_oslinv.
    eapply absinfer_mutex_post_original_not_holder_err_return.
    go .
    hoare forward prim.
    unfold AECBList.
    unfold AOSTCBPrioTbl.
    unfold AOSTCBList.
    unfold tcbdllseg.
    unfold AEventNode.
    unfold AOSEvent.
    unfold AEventData.
    unfold node.
    unfold AOSEventTbl.
    sep pauto.
    sep cancel 3%nat 3%nat.
    sep cancel 5%nat 1%nat.
    4:eauto.
    4:eauto.
    unfold1 dllseg; sep pauto.
    unfold node; sep cancel dllseg; unfold AOSEventTbl.
    sep pauto.
    sep cancel Astruct.
    
    do 2 rewrite list_prop1.
    eapply evsllseg_merge; eauto.


    lets Heq : ecblistp_length_eq H1 H12.
    simpl; auto.
    sep cancel 7%nat 1%nat.
    unfold1 evsllseg.
    unfold AEventNode; unfold AOSEvent; unfold AEventData; unfold node; unfold AOSEventTbl.
    sep pauto.
    sep cancel Astruct.
    sep cancel Aarray.
    sep cancel evsllseg.
    unfold AOSMapTbl.
    unfold AOSRdyTblGrp.
    unfold AOSRdyTbl, AOSRdyGrp.
    unfold AOSUnMapTbl.
    sep cancel tcbdllflag.
    sep pauto.
    go. 
    math simpls.
    go.  go.  go.  go.  go.  go.  go.  go.  go.  go.  go.
    go.
    hoare forward.

    hoare forward.
    hoare unfold.

    rewrite (mutexpost_intlemma1 _ H48) in H92.
    rewrite (nth_val_nth_val'_some_eq _ _ H52) in H92.

    apply post_valinjlemma1 in H92.
    
    rewrite (mutexdel_intlemma1 _ H15).
    rewrite (mutexpost_intlemma1 _ H48).
    (* eapply seq_rule. *)

    hoare forward.
   
    (* let s:= fresh in let H:=fresh in eapply forward_rule2; [idtac| intros s H; exact H]. *)
(*     Require Import hoare_assign.
 * Require Import aux_for_hoare_lemmas. *)
(* Ltac hoare_assign_array' :=
 *   let s := fresh in
 *   let H := fresh in
 *   match goal with
 *     | |- {| _, _, _, _, _ |} |-  {{ ?P }} (sassign (earrayelem (evar ?x) _) _) {{ _ }} =>
 *       match find_lvararray P x with
 *         | some ?m =>
 *           match find_aop P with
 *             | none _ => fail 1
 *             | some ?n =>
 *               hoare lifts (n::m::nil)%list pre;
 *                 eapply assign_rule_array_aop;
 *                 [ intro s; split; intro H; exact H
 *                 | symbolic execution
 *                 | symbolic execution
 *                 | intuition auto
 *                 | idtac
 *                 | apply assign_type_match_true; simpl; auto
 *                 | idtac ]
 *           end
 *         | none _ =>
 *           match find_dom_lenv P with
 *             | (none _, _) => fail 2
 *             | (some ?m, Some ?ls) =>
 *               let ret1 := constr:(var_notin_dom x ls) in
 *               let ret2 := (eval compute in ret1) in
 *               match ret2 with
 *                 | true =>
 *                   match find_aop P with
 *                     | none _ => fail 1
 *                     | some ?n =>
 *                       match find_gvararray P x with
 *                         | none _ => fail 3
 *                         | some ?o =>
 *                           hoare lifts (n::m::o::nil)%list pre;
 *                             eapply assign_rule_array_g_aop;
 *                             [ intro s; split; intro H; exact H
 *                             | simpl; auto
 *                             | symbolic execution
 *                             | symbolic execution
 *                             | intuition auto
 *                             | idtac
 *                             | apply assign_type_match_true; simpl; auto
 *                             | idtac ]
 *                       end
 *                   end
 *                 | false => fail
 *               end
 *           end
 *       end
 *     | |- {| _, _, _, _, _ |} |-  {{ ?P }} (sassign (earrayelem _  _) _) {{ _ }} =>
 *       eapply assign_rule_ptr_array_aop;
 *         [ symbolic execution;try solve [eauto | simpl;eauto] 
 *         | intro s;split;intro H;
 *           [
 *             match goal with
 *               | H' : ?s |= ?P |- ?s |= Aarray ?l _ _ ** _ =>
 *                  match find_ptrarray P l with
 *                    | (some ?n) => sep lift n in H'; try exact H'
 *                    | _ => fail 4
 *                  end 
 *             end
 *           | match goal with 
 *               | H': ?s |= Aarray ?l _ _ ** _ |- ?s |= ?P =>
 *                 match find_ptrarray P l with
 *                   | (some ?n) => sep lift n ; try exact H'
 *                   | _ => fail 4
 *                 end
 *             end
 *           ]
 *         | symbolic execution 
 *         | symbolic execution
 *         | intuition auto
 *         | intuition auto
 *         | simpl
 *         | simpl;auto
 *         | simpl
 *         ]
 *   end. *)

    (* hoare_assign_array'. *)

    go.
    go.
    go.
    (* intro; tryfalse. *)
    rewrite H86.
    simpl.
    intro; tryfalse.
    go.
    Set Printing Depth 999.
    (* unfold OS_RDY_TBL_SIZE.
     * rewrite HH58 in rrr5; clear - rrr5.
     * exact rrr5.
     * exact rrr5. *)
    
(* (    (
 *     <|| mutexpost (Vptr (v'29, Int.zero) :: nil) ||>  **
 *    A_dom_lenv
 *      ((pevent, OS_EVENT ∗)
 *       :: (os_code_defs.x, Int8u)
 *          :: (pip, Int8u) :: (prio, Int8u) :: (legal, Int8u) :: nil) **
 *    GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64)
 *      (update_nth_val (Z.to_nat (Int.unsigned (Int.shru x ($ 8))))
 *         (update_nth_val (Z.to_nat (Int.unsigned (x&$ OS_MUTEX_KEEP_LOWER_8)))
 *            v'30 (Vptr (v'52, Int.zero))) (Vptr v'51)) **
 *    GAarray OSRdyTbl (Tarray Int8u ∘OS_RDY_TBL_SIZE)
 *      (update_nth_val
 *         (Z.to_nat (Int.unsigned (Int.shru (x&$ OS_MUTEX_KEEP_LOWER_8) ($ 3))))
 *         (update_nth_val (Z.to_nat (Int.unsigned (Int.shru x6 ($ 3)))) v'36
 *            (val_inj (and (Vint32 x12) (Vint32 (Int.not ($ 1<<(x6&$ 7)))))))
 *         (val_inj
 *            (or
 *               (nth_val'
 *                  (Z.to_nat (Int.unsigned (Int.shru (x&$ OS_MUTEX_KEEP_LOWER_8) ($ 3))))
 *                  (update_nth_val (Z.to_nat (Int.unsigned (Int.shru x6 ($ 3)))) v'36
 *                     (val_inj
 *                        (and (Vint32 x12) (Vint32 (Int.not ($ 1<<(x6&$ 7))))))))
 *               (Vint32 x11)))) **
 *    GV OSRdyGrp @ Int8u |-> Vint32 (Int.or (i7&Int.not ($ 1<<(Int.shru x6 ($ 3)))) x8) **
 *    GV OSTCBCur @ OS_TCB ∗ |-> Vptr (v'52, Int.zero) **
 *    Astruct (v'52, Int.zero) OS_TCB
 *      (x7
 *       :: v'24
 *          :: x15
 *             :: m
 *                :: Vint32 i6
 *                   :: Vint32 x14
 *                      :: Vint32 (x&$ OS_MUTEX_KEEP_LOWER_8)
 *                         :: Vint32 ((x&$ OS_MUTEX_KEEP_LOWER_8)&$ 7)
 *                            :: Vint32 (Int.shru (x&$ OS_MUTEX_KEEP_LOWER_8) ($ 3))
 *                               :: Vint32 x11 :: Vint32 x8 :: nil) **
 *    LV os_code_defs.x @ Int8u |-> Vint32 ((x2<<$ 3)+ᵢx5) **
 *    LV legal @ Int8u |-> Vint32 x2 **
 *    PV v'51 @ Int8u |-> v'32 **
 *    dllseg x7 (Vptr (v'52, Int.zero)) v'40 Vnull v'35 OS_TCB
 *      (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
 *    GV OSTCBList @ OS_TCB ∗ |-> v'31 **
 *    dllseg v'31 Vnull v'24 (Vptr (v'52, Int.zero)) v'33 OS_TCB
 *      (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
 *    LV prio @ Int8u |-> Vint32 (x&$ OS_MUTEX_KEEP_LOWER_8) **
 *    LV pip @ Int8u |-> Vint32 (Int.shru x ($ 8)) **
 *    Astruct (v'29, Int.zero) OS_EVENT
 *      (V$OS_EVENT_TYPE_MUTEX
 *       :: Vint32 i :: Vint32 x :: Vptr (v'52, $ 0) :: x3 :: v'46 :: nil) **
 *    Aarray v'23 (Tarray Int8u ∘OS_EVENT_TBL_SIZE) v'44 **
 *    Aie false **
 *    Ais nil **
 *    Acs (true :: nil) **
 *    Aisr empisr **
 *    GV OSEventList @ OS_EVENT ∗ |-> v'42 **
 *    evsllseg v'42 (Vptr (v'29, Int.zero)) v'25 v'27 **
 *    evsllseg v'46 Vnull v'26 v'28 **
 *    A_isr_is_prop **
 *    G&OSPlaceHolder @ Int8u == v'51 **
 *    HECBList v'38 **
 *    HTCBList v'39 **
 *    HCurTCB (v'52, Int.zero) **
 *    AOSEventFreeList v'3 **
 *    AOSQFreeList v'4 **
 *    AOSQFreeBlk v'5 **
 *    GAarray OSMapTbl (Tarray Int8u 8) OSMapVallist **
 *    GAarray OSUnMapTbl (Tarray Int8u 256) OSUnMapVallist **
 *    AOSIntNesting **
 *    AOSTCBFreeList v'21 v'22 **
 *    AOSTime (Vint32 v'18) **
 *    HTime v'18 **
 *    AGVars **
 *    atoy_inv' **
 *    LV pevent @ OS_EVENT ∗ |-> Vptr (v'29, Int.zero) **
 *    [|val_inj
 *        (val_eq
 *           (nth_val' (Z.to_nat (Int.unsigned (Int.shru x6 ($ 3))))
 *              (update_nth_val (Z.to_nat (Int.unsigned (Int.shru x6 ($ 3)))) v'36
 *                 (val_inj
 *                    (and (Vint32 x12) (Vint32 (Int.not ($ 1<<(x6&$ 7))))))))
 *           (V$0)) <> Vint32 Int.zero /\
 *      val_inj
 *        (val_eq
 *           (nth_val' (Z.to_nat (Int.unsigned (Int.shru x6 ($ 3))))
 *              (update_nth_val (Z.to_nat (Int.unsigned (Int.shru x6 ($ 3)))) v'36
 *                 (val_inj
 *                    (and (Vint32 x12) (Vint32 (Int.not ($ 1<<(x6&$ 7))))))))
 *           (V$0)) <> Vnull /\
 *      val_inj
 *        (val_eq
 *           (nth_val' (Z.to_nat (Int.unsigned (Int.shru x6 ($ 3))))
 *              (update_nth_val (Z.to_nat (Int.unsigned (Int.shru x6 ($ 3)))) v'36
 *                 (val_inj
 *                    (and (Vint32 x12) (Vint32 (Int.not ($ 1<<(x6&$ 7))))))))
 *           (V$0)) <> Vundef|] **
 *    [|val_inj
 *        (val_eq
 *           (nth_val' (Z.to_nat (Int.unsigned (Int.shru x6 ($ 3))))
 *              (update_nth_val (Z.to_nat (Int.unsigned (Int.shru x6 ($ 3)))) v'36
 *                 (val_inj
 *                    (and (Vint32 x12) (Vint32 (Int.not ($ 1<<(x6&$ 7))))))))
 *           (V$0)) <> Vint32 Int.zero /\
 *      val_inj
 *        (val_eq
 *           (nth_val' (Z.to_nat (Int.unsigned (Int.shru x6 ($ 3))))
 *              (update_nth_val (Z.to_nat (Int.unsigned (Int.shru x6 ($ 3)))) v'36
 *                 (val_inj
 *                    (and (Vint32 x12) (Vint32 (Int.not ($ 1<<(x6&$ 7))))))))
 *           (V$0)) <> Vnull /\
 *      val_inj
 *        (val_eq
 *           (nth_val' (Z.to_nat (Int.unsigned (Int.shru x6 ($ 3))))
 *              (update_nth_val (Z.to_nat (Int.unsigned (Int.shru x6 ($ 3)))) v'36
 *                 (val_inj
 *                    (and (Vint32 x12) (Vint32 (Int.not ($ 1<<(x6&$ 7))))))))
 *           (V$0)) <> Vundef|]
 * 	  ) **
 *           [| x1 = Vptr v'51 |]
 *           \\// (
 * 	      <|| mutexpost (Vptr (v'29, Int.zero) :: nil) ||>  **
 *    A_dom_lenv
 *      ((pevent, OS_EVENT ∗)
 *       :: (os_code_defs.x, Int8u)
 *          :: (pip, Int8u) :: (prio, Int8u) :: (legal, Int8u) :: nil) **
 *    GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64)
 *      (update_nth_val (Z.to_nat (Int.unsigned (Int.shru x ($ 8))))
 *         (update_nth_val (Z.to_nat (Int.unsigned (x&$ OS_MUTEX_KEEP_LOWER_8)))
 *            v'30 (Vptr (v'52, Int.zero))) (Vptr v'51)) **
 *    GAarray OSRdyTbl (Tarray Int8u ∘OS_RDY_TBL_SIZE)
 *      (update_nth_val
 *         (Z.to_nat (Int.unsigned (Int.shru (x&$ OS_MUTEX_KEEP_LOWER_8) ($ 3))))
 *         (update_nth_val (Z.to_nat (Int.unsigned (Int.shru x6 ($ 3)))) v'36
 *            (val_inj (and (Vint32 x12) (Vint32 (Int.not ($ 1<<(x6&$ 7)))))))
 *         (val_inj
 *            (or
 *               (nth_val'
 *                  (Z.to_nat (Int.unsigned (Int.shru (x&$ OS_MUTEX_KEEP_LOWER_8) ($ 3))))
 *                  (update_nth_val (Z.to_nat (Int.unsigned (Int.shru x6 ($ 3)))) v'36
 *                     (val_inj
 *                        (and (Vint32 x12) (Vint32 (Int.not ($ 1<<(x6&$ 7))))))))
 *               (Vint32 x11)))) **
 *    GV OSRdyGrp @ Int8u |-> Vint32 (Int.or i7 x8) **
 *    GV OSTCBCur @ OS_TCB ∗ |-> Vptr (v'52, Int.zero) **
 *    Astruct (v'52, Int.zero) OS_TCB
 *      (x7
 *       :: v'24
 *          :: x15
 *             :: m
 *                :: Vint32 i6
 *                   :: Vint32 x14
 *                      :: Vint32 (x&$ OS_MUTEX_KEEP_LOWER_8)
 *                         :: Vint32 ((x&$ OS_MUTEX_KEEP_LOWER_8)&$ 7)
 *                            :: Vint32 (Int.shru (x&$ OS_MUTEX_KEEP_LOWER_8) ($ 3))
 *                               :: Vint32 x11 :: Vint32 x8 :: nil) **
 *    LV os_code_defs.x @ Int8u |-> Vint32 ((x2<<$ 3)+ᵢx5) **
 *    LV legal @ Int8u |-> Vint32 x2 **
 *    PV v'51 @ Int8u |-> v'32 **
 *    dllseg x7 (Vptr (v'52, Int.zero)) v'40 Vnull v'35 OS_TCB
 *      (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
 *    GV OSTCBList @ OS_TCB ∗ |-> v'31 **
 *    dllseg v'31 Vnull v'24 (Vptr (v'52, Int.zero)) v'33 OS_TCB
 *      (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
 *    LV prio @ Int8u |-> Vint32 (x&$ OS_MUTEX_KEEP_LOWER_8) **
 *    LV pip @ Int8u |-> Vint32 (Int.shru x ($ 8)) **
 *    Astruct (v'29, Int.zero) OS_EVENT
 *      (V$OS_EVENT_TYPE_MUTEX
 *       :: Vint32 i :: Vint32 x :: Vptr (v'52, $ 0) :: x3 :: v'46 :: nil) **
 *    Aarray v'23 (Tarray Int8u ∘OS_EVENT_TBL_SIZE) v'44 **
 *    Aie false **
 *    Ais nil **
 *    Acs (true :: nil) **
 *    Aisr empisr **
 *    GV OSEventList @ OS_EVENT ∗ |-> v'42 **
 *    evsllseg v'42 (Vptr (v'29, Int.zero)) v'25 v'27 **
 *    evsllseg v'46 Vnull v'26 v'28 **
 *    A_isr_is_prop **
 *    G&OSPlaceHolder @ Int8u == v'51 **
 *    HECBList v'38 **
 *    HTCBList v'39 **
 *    HCurTCB (v'52, Int.zero) **
 *    AOSEventFreeList v'3 **
 *    AOSQFreeList v'4 **
 *    AOSQFreeBlk v'5 **
 *    GAarray OSMapTbl (Tarray Int8u 8) OSMapVallist **
 *    GAarray OSUnMapTbl (Tarray Int8u 256) OSUnMapVallist **
 *    AOSIntNesting **
 *    AOSTCBFreeList v'21 v'22 **
 *    AOSTime (Vint32 v'18) **
 *    HTime v'18 **
 *    AGVars **
 *    atoy_inv' **
 *    LV pevent @ OS_EVENT ∗ |-> Vptr (v'29, Int.zero) **
 *    [|val_inj
 *        (val_eq
 *           (nth_val' (Z.to_nat (Int.unsigned (Int.shru x6 ($ 3))))
 *              (update_nth_val (Z.to_nat (Int.unsigned (Int.shru x6 ($ 3)))) v'36
 *                 (val_inj
 *                    (and (Vint32 x12) (Vint32 (Int.not ($ 1<<(x6&$ 7))))))))
 *           (V$0)) = Vint32 Int.zero \/
 *      val_inj
 *        (val_eq
 *           (nth_val' (Z.to_nat (Int.unsigned (Int.shru x6 ($ 3))))
 *              (update_nth_val (Z.to_nat (Int.unsigned (Int.shru x6 ($ 3)))) v'36
 *                 (val_inj
 *                    (and (Vint32 x12) (Vint32 (Int.not ($ 1<<(x6&$ 7))))))))
 *           (V$0)) = Vnull|] **
 *           [| x1 = Vptr v'51 |]
 * 	  )
 * ) *)

    Focus 2.
    Require Import OSMutexPostPart3.
    eapply MutexPostPart3; eauto.
    
    Require Import OSMutexPostPart2_0. 
    eapply MutexPostPart10; eauto.

Qed.
(*     Require Import OSMutexPostPart3.
 *     eapply MutexPostPart3; eauto.
 * 
 * 
 * Qed. *)
(*0*)
