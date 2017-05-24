Require Import ucos_include.
Require Import OSMutex_common.
Require Import os_ucos_h.
Require Import mutex_absop_rules.
Require Import sep_lemmas_ext.
Require Import symbolic_lemmas.
Require Import OSTimeDlyPure.
Require Import OSQPostPure.
Require Import tcblist_setnode_lemmas.
Local Open Scope code_scope.
Local Open Scope nat_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.
Local Open Scope list_scope.


(* in pendpure 1 *) 
  
Lemma MutexPostPart3: (*: gen_MutexPostPart3.*)
forall
(
  v' v'0 v'1 v'2 : val
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
  i6 : int32
)(
  H39 : Int.unsigned i6 <= 65535
)(
  H36 : isptr v'24
)(
  x7 : val
)(
  x10 : TcbMod.map
)(
  t : taskstatus
)(
  m : msg
)(
  H72 : TCBList_P x7 v'35 v'36 x10
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
  H27 : isptr x7
)(
  H38 : isptr m
              )(
  x6 x14 : int32
)(
  H77 : 0 <= Int.unsigned x6
)(
  H85 : Int.unsigned x6 < 64
)(
  H82 : x14 = $ OS_STAT_RDY \/
        x14 = $ OS_STAT_SEM \/
        x14 = $ OS_STAT_Q \/ x14 = $ OS_STAT_MBOX \/ x14 = $ OS_STAT_MUTEX
)(
  x15 : val
)(
  H84 : x14 = $ OS_STAT_RDY -> x15 = Vnull
)(
  H43 : Int.unsigned (x6 >>ᵢ $ 3) <= 255
)(
  H45 : Int.unsigned ($ 1<<ᵢ(x6 >>ᵢ $ 3)) <= 255
)(
  H44 : Int.unsigned ($ 1<<ᵢ(x6&ᵢ$ 7)) <= 255
)(
  H42 : Int.unsigned (x6&ᵢ$ 7) <= 255
)(
  H70 : TcbJoin (v'52, Int.zero) (x6, t, m) x10 v'45
)(
  H41 : Int.unsigned x6 <= 255
)(
  H28 : Int.ltu x6 (x >>ᵢ $ 8) = false
)(
  H37 : isptr x15
)(
  H40 : Int.unsigned x14 <= 255
)(
  last_condition : ProtectWrapper (x14 = $ OS_STAT_RDY /\ i6 = $ 0)
)(
  H73 : R_TCB_Status_P
          (x7
           :: v'24
              :: x15
                 :: m
                    :: Vint32 i6
                       :: Vint32 x14
                          :: Vint32 x6
                             :: Vint32 (x6&ᵢ$ 7)
                                :: Vint32 (x6 >>ᵢ $ 3)
                                   :: Vint32 ($ 1<<ᵢ(x6&ᵢ$ 7))
                                      :: Vint32 ($ 1<<ᵢ(x6 >>ᵢ $ 3)) :: nil)
          v'36 (x6, t, m)
)(
  backup2 : TCBList_P (Vptr (v'52, Int.zero))
              ((x7
                :: v'24
                   :: x15
                      :: m
                         :: Vint32 i6
                            :: Vint32 x14
                               :: Vint32 x6
                                  :: Vint32 (x6&ᵢ$ 7)
                                     :: Vint32 (x6 >>ᵢ $ 3)
                                        :: Vint32 ($ 1<<ᵢ(x6&ᵢ$ 7))
                                           :: Vint32 ($ 1<<ᵢ(x6 >>ᵢ $ 3))
                                              :: nil) :: v'35) v'36 v'45
)(
  r1 : Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3) < 8
)(
  r2 : Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7) < 8
)(
  r3 : Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3) < 8
)(
  r4 : Int.unsigned ((x >>ᵢ $ 8)&ᵢ$ 7) < 8
)(
  H34 : array_type_vallist_match Int8u OSMapVallist
)(
  H69 : length OSMapVallist = 8%nat
)(
  H71 : (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)) < 8)%nat
)(
  x8 : int32
)(
  H74 : nth_val'
          (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
          OSMapVallist = Vint32 x8
)(
  H75 : true = rule_type_val_match Int8u (Vint32 x8)
)(
  H76 : (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)) < 8)%nat
)(
  x9 : int32
)(
  H78 : nth_val'
          (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)))
          OSMapVallist = Vint32 x9
)(
  H79 : true = rule_type_val_match Int8u (Vint32 x9)
)(
  H80 : (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)) < 8)%nat
)(
  x11 : int32
)(
  H81 : nth_val'
          (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)))
          OSMapVallist = Vint32 x11
)(
  H83 : true = rule_type_val_match Int8u (Vint32 x11)
)(
  r5 : Int.unsigned (x6 >>ᵢ $ 3) < 8
)(
  r6 : Int.unsigned (x6&ᵢ$ 7) < 8
)(
  rr1 : (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3)) < length v'36)%nat
)(
  rr2 : (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)) <
         length v'36)%nat
)(
  rr3 : (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)) <
         length v'36)%nat
)(
  rr4 : (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8)&ᵢ$ 7)) < length v'36)%nat
)(
  rr5 : (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3)) < length v'36)%nat
)(
  rr6 : (Z.to_nat (Int.unsigned (x6&ᵢ$ 7)) < length v'36)%nat
)(
  rrr1 : Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3) < Z.of_nat (length v'36)
)(
  rrr2 : Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7) <
         Z.of_nat (length v'36)
)(
  rrr3 : Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3) <
         Z.of_nat (length v'36)
)(
  rrr4 : Int.unsigned ((x >>ᵢ $ 8)&ᵢ$ 7) < Z.of_nat (length v'36)
)(
  rrr5 : Int.unsigned (x6 >>ᵢ $ 3) < Z.of_nat (length v'36)
)(
  rrr6 : Int.unsigned (x6&ᵢ$ 7) < Z.of_nat (length v'36)
)(
  HH58 : length v'36 = Z.to_nat 8
)(
  aa : rule_type_val_match Int8u
         (nth_val' (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3))) v'36) =
       true
)(
  aa2 : rule_type_val_match Int8u
          (nth_val'
             (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
             v'36) = true
)(
  aa3 : rule_type_val_match Int8u
          (nth_val' (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3))) v'36) = true
)(
  x16 : int32
)(
  H88 : nth_val' (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3))) v'36 =
        Vint32 x16
)(
  H91 : Int.unsigned x16 <= 255
)(
  x13 : int32
)(
  H87 : nth_val'
          (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
          v'36 = Vint32 x13
)(
  H90 : Int.unsigned x13 <= 255
)(
  x12 : int32
)(
  H86 : nth_val' (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3))) v'36 = Vint32 x12
)(
  H89 : Int.unsigned x12 <= 255
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
   {{(( <|| mutexpost (Vptr (v'29, Int.zero) :: nil) ||>  **
       A_dom_lenv
         ((pevent, OS_EVENT ∗)
          :: (os_code_defs.x, Int8u)
             :: (pip, Int8u) :: (prio, Int8u) :: (legal, Int8u) :: nil) **
       GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64)
         (update_nth_val (Z.to_nat (Int.unsigned (x >>ᵢ $ 8)))
            (update_nth_val
               (Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) v'30
               (Vptr (v'52, Int.zero))) (Vptr v'51)) **
       GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
         (update_nth_val
            (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
            (update_nth_val (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3))) v'36
               (val_inj
                  (and (Vint32 x12) (Vint32 (Int.not ($ 1<<ᵢ(x6&ᵢ$ 7)))))))
            (val_inj
               (or
                  (nth_val'
                     (Z.to_nat
                        (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
                     (update_nth_val (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3)))
                        v'36 (Vint32 (x12&ᵢInt.not ($ 1<<ᵢ(x6&ᵢ$ 7))))))
                  (Vint32 x11)))) **
       GV OSRdyGrp @ Int8u
       |-> Vint32 (Int.or (i7&ᵢInt.not ($ 1<<ᵢ(x6 >>ᵢ $ 3))) x8) **
       GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (v'52, Int.zero) **
       Astruct (v'52, Int.zero) OS_TCB_flag
         (x7
          :: v'24
             :: x15
                :: m
                   :: Vint32 i6
                      :: Vint32 x14
                         :: Vint32 (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)
                            :: Vint32 ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)
                               :: Vint32
                                    ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)
                                  :: Vint32 x11 :: Vint32 x8 :: nil) **
       LV os_code_defs.x @ Int8u |-> Vint32 ((x2<<ᵢ$ 3) +ᵢ  x5) **
       LV legal @ Int8u |-> Vint32 x2 **
       PV v'51 @ Int8u |-> v'32 **
       dllseg x7 (Vptr (v'52, Int.zero)) v'40 Vnull v'35 OS_TCB_flag
         (fun vl : vallist => nth_val 1 vl)
         (fun vl : vallist => nth_val 0 vl) **
       GV OSTCBList @ OS_TCB ∗ |-> v'31 **
       dllseg v'31 Vnull v'24 (Vptr (v'52, Int.zero)) v'33 OS_TCB_flag
         (fun vl : vallist => nth_val 1 vl)
         (fun vl : vallist => nth_val 0 vl) **
       LV prio @ Int8u |-> Vint32 (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) **
       LV pip @ Int8u |-> Vint32 (x >>ᵢ $ 8) **
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
          (x7
           :: v'24
              :: x15
                 :: m
                    :: Vint32 i6
                       :: Vint32 x14
                          :: Vint32 x6
                             :: Vint32 (x6&ᵢ$ 7)
                                :: Vint32 (x6 >>ᵢ $ 3)
                                   :: Vint32 ($ 1<<ᵢ(x6&ᵢ$ 7))
                                      :: Vint32 ($ 1<<ᵢ(x6 >>ᵢ $ 3)) :: nil)
          :: v'35) **
       G& OSPlaceHolder @ Int8u == v'51 **
       HECBList v'38 **
       HTCBList v'39 **
       HCurTCB (v'52, Int.zero) **
       p_local OSLInv (v'52, Int.zero) init_lg **
       AOSEventFreeList v'3 **
       AOSQFreeList v'4 **
       AOSQFreeBlk v'5 **
       GAarray OSMapTbl (Tarray Int8u 8) OSMapVallist **
       GAarray OSUnMapTbl (Tarray Int8u 256) OSUnMapVallist **
       (EX v : int32, GV OSIntNesting @ Int32u |-> Vint32 v) **
       AOSTCBFreeList v'21 v'22 **
       GV OSTime @ Int32u |-> Vint32 v'18 **
       HTime v'18 **
       (GV OSRunning @ Int8u |-> (V$ 1) **
        (EX v : int32,
         GV OSPrioHighRdy @ Int8u |-> Vint32 v ** [|Int.unsigned v <= 63|]) **
        (EX v : int32, GV OSCtxSwCtr @ Int32u |-> Vint32 v) **
        (EX v : addrval, GV OSTCBHighRdy @ OS_TCB ∗ |-> Vptr v) **
        (EX v : int32,
         GV OSPrioCur @ Int8u |-> Vint32 v ** [|Int.unsigned v <= 63|]) **
        (EX v : int32, GV OSIntExitY @ Int8u |-> Vint32 v)) **
       atoy_inv' **
       LV pevent @ OS_EVENT ∗ |-> Vptr (v'29, Int.zero) **
       [|val_inj
           (val_eq
              (nth_val' (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3)))
                 (update_nth_val (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3))) v'36
                    (val_inj
                       (and (Vint32 x12) (Vint32 (Int.not ($ 1<<ᵢ(x6&ᵢ$ 7))))))))
              (V$ 0)) <> Vint32 Int.zero /\
         val_inj
           (val_eq
              (nth_val' (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3)))
                 (update_nth_val (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3))) v'36
                    (val_inj
                       (and (Vint32 x12) (Vint32 (Int.not ($ 1<<ᵢ(x6&ᵢ$ 7))))))))
              (V$ 0)) <> Vnull /\
         val_inj
           (val_eq
              (nth_val' (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3)))
                 (update_nth_val (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3))) v'36
                    (val_inj
                       (and (Vint32 x12) (Vint32 (Int.not ($ 1<<ᵢ(x6&ᵢ$ 7))))))))
              (V$ 0)) <> Vundef|] **
       [|val_inj
           (val_eq
              (nth_val' (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3)))
                 (update_nth_val (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3))) v'36
                    (val_inj
                       (and (Vint32 x12) (Vint32 (Int.not ($ 1<<ᵢ(x6&ᵢ$ 7))))))))
              (V$ 0)) <> Vint32 Int.zero /\
         val_inj
           (val_eq
              (nth_val' (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3)))
                 (update_nth_val (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3))) v'36
                    (val_inj
                       (and (Vint32 x12) (Vint32 (Int.not ($ 1<<ᵢ(x6&ᵢ$ 7))))))))
              (V$ 0)) <> Vnull /\
         val_inj
           (val_eq
              (nth_val' (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3)))
                 (update_nth_val (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3))) v'36
                    (val_inj
                       (and (Vint32 x12) (Vint32 (Int.not ($ 1<<ᵢ(x6&ᵢ$ 7))))))))
              (V$ 0)) <> Vundef|]) ** [|x1 = Vptr v'51|] \\//
       <|| mutexpost (Vptr (v'29, Int.zero) :: nil) ||>  **
      A_dom_lenv
        ((pevent, OS_EVENT ∗)
         :: (os_code_defs.x, Int8u)
            :: (pip, Int8u) :: (prio, Int8u) :: (legal, Int8u) :: nil) **
      GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64)
        (update_nth_val (Z.to_nat (Int.unsigned (x >>ᵢ $ 8)))
           (update_nth_val
              (Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) v'30
              (Vptr (v'52, Int.zero))) (Vptr v'51)) **
      GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
        (update_nth_val
           (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
           (update_nth_val (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3))) v'36
              (val_inj
                 (and (Vint32 x12) (Vint32 (Int.not ($ 1<<ᵢ(x6&ᵢ$ 7)))))))
           (val_inj
              (or
                 (nth_val'
                    (Z.to_nat
                       (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
                    (update_nth_val (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3)))
                       v'36 (Vint32 (x12&ᵢInt.not ($ 1<<ᵢ(x6&ᵢ$ 7))))))
                 (Vint32 x11)))) **
      GV OSRdyGrp @ Int8u |-> Vint32 (Int.or i7 x8) **
      GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (v'52, Int.zero) **
      Astruct (v'52, Int.zero) OS_TCB_flag
        (x7
         :: v'24
            :: x15
               :: m
                  :: Vint32 i6
                     :: Vint32 x14
                        :: Vint32 (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)
                           :: Vint32 ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)
                              :: Vint32
                                   ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)
                                 :: Vint32 x11 :: Vint32 x8 :: nil) **
      LV os_code_defs.x @ Int8u |-> Vint32 ((x2<<ᵢ$ 3) +ᵢ  x5) **
      LV legal @ Int8u |-> Vint32 x2 **
      PV v'51 @ Int8u |-> v'32 **
      dllseg x7 (Vptr (v'52, Int.zero)) v'40 Vnull v'35 OS_TCB_flag
        (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
      GV OSTCBList @ OS_TCB ∗ |-> v'31 **
      dllseg v'31 Vnull v'24 (Vptr (v'52, Int.zero)) v'33 OS_TCB_flag
        (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
      LV prio @ Int8u |-> Vint32 (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) **
      LV pip @ Int8u |-> Vint32 (x >>ᵢ $ 8) **
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
         (x7
          :: v'24
             :: x15
                :: m
                   :: Vint32 i6
                      :: Vint32 x14
                         :: Vint32 x6
                            :: Vint32 (x6&ᵢ$ 7)
                               :: Vint32 (x6 >>ᵢ $ 3)
                                  :: Vint32 ($ 1<<ᵢ(x6&ᵢ$ 7))
                                     :: Vint32 ($ 1<<ᵢ(x6 >>ᵢ $ 3)) :: nil)
         :: v'35) **
      G& OSPlaceHolder @ Int8u == v'51 **
      HECBList v'38 **
      HTCBList v'39 **
      HCurTCB (v'52, Int.zero) **
      p_local OSLInv (v'52, Int.zero) init_lg **
      AOSEventFreeList v'3 **
      AOSQFreeList v'4 **
      AOSQFreeBlk v'5 **
      GAarray OSMapTbl (Tarray Int8u 8) OSMapVallist **
      GAarray OSUnMapTbl (Tarray Int8u 256) OSUnMapVallist **
      AOSIntNesting **
      AOSTCBFreeList v'21 v'22 **
      AOSTime (Vint32 v'18) **
      HTime v'18 **
      AGVars **
      atoy_inv' **
      LV pevent @ OS_EVENT ∗ |-> Vptr (v'29, Int.zero) **
      [|val_inj
          (val_eq
             (nth_val' (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3)))
                (update_nth_val (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3))) v'36
                   (val_inj
                      (and (Vint32 x12) (Vint32 (Int.not ($ 1<<ᵢ(x6&ᵢ$ 7))))))))
             (V$ 0)) = Vint32 Int.zero \/
        val_inj
          (val_eq
             (nth_val' (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3)))
                (update_nth_val (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3))) v'36
                   (val_inj
                      (and (Vint32 x12) (Vint32 (Int.not ($ 1<<ᵢ(x6&ᵢ$ 7))))))))
             (V$ 0)) = Vnull|] ** [|x1 = Vptr v'51|]) **
     [|val_inj
         (if Int.eq x6 (Int.modu (x >>ᵢ $ 8) ($ Byte.modulus))
          then Some (Vint32 Int.one)
          else Some (Vint32 Int.zero)) <> Vint32 Int.zero /\
       val_inj
         (if Int.eq x6 (Int.modu (x >>ᵢ $ 8) ($ Byte.modulus))
          then Some (Vint32 Int.one)
          else Some (Vint32 Int.zero)) <> Vnull /\
       val_inj
         (if Int.eq x6 (Int.modu (x >>ᵢ $ 8) ($ Byte.modulus))
          then Some (Vint32 Int.one)
          else Some (Vint32 Int.zero)) <> Vundef|] \\//
     ( <|| mutexpost (Vptr (v'29, Int.zero) :: nil) ||>  **
      LV os_code_defs.x @ Int8u |-> Vint32 ((x2<<ᵢ$ 3) +ᵢ  x5) **
      LV legal @ Int8u |-> Vint32 x2 **
      PV v'51 @ Int8u |-> v'32 **
      Astruct (v'52, Int.zero) OS_TCB_flag
        (x7
         :: v'24
            :: x15
               :: m
                  :: Vint32 i6
                     :: Vint32 x14
                        :: Vint32 x6
                           :: Vint32 (x6&ᵢ$ 7)
                              :: Vint32 (x6 >>ᵢ $ 3)
                                 :: Vint32 ($ 1<<ᵢ(x6&ᵢ$ 7))
                                    :: Vint32 ($ 1<<ᵢ(x6 >>ᵢ $ 3)) :: nil) **
      dllseg x7 (Vptr (v'52, Int.zero)) v'40 Vnull v'35 OS_TCB_flag
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
         (x7
          :: v'24
             :: x15
                :: m
                   :: Vint32 i6
                      :: Vint32 x14
                         :: Vint32 x6
                            :: Vint32 (x6&ᵢ$ 7)
                               :: Vint32 (x6 >>ᵢ $ 3)
                                  :: Vint32 ($ 1<<ᵢ(x6&ᵢ$ 7))
                                     :: Vint32 ($ 1<<ᵢ(x6 >>ᵢ $ 3)) :: nil)
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
      GAarray OSMapTbl (Tarray Int8u 8) OSMapVallist **
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
            :: (pip, Int8u) :: (prio, Int8u) :: (legal, Int8u) :: nil)) **
     [|val_inj
         (if Int.eq x6 (Int.modu (x >>ᵢ $ 8) ($ Byte.modulus))
          then Some (Vint32 Int.one)
          else Some (Vint32 Int.zero)) = Vint32 Int.zero \/
       val_inj
         (if Int.eq x6 (Int.modu (x >>ᵢ $ 8) ($ Byte.modulus))
          then Some (Vint32 Int.one)
          else Some (Vint32 Int.zero)) = Vnull|]}} 
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
                   RETURN ′ OS_NO_ERR {{Afalse}}.
Proof.
  intros.
  Set Printing Depth 999.
  assert ( Int.unsigned (Int.shru x ($ 8)) < Int.unsigned ($ Byte.modulus)).
  change Byte.modulus with 256.
  clear -H15.
  ur_rewriter.
  omega.
  auto.
  rewrite intlemma13 in *; auto.
  rewrite intlemma13 in *; auto.
  Focus 2.
  change Byte.modulus with 256.
  ur_rewriter.
  cut ( Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) <=255).
  intros afdaf; clear -afdaf; omega.
  apply postintlemma3.
  hoare forward.
  {
    (* priority inversion *) 
     apply  val_injsimpl in H68.
     hoare_split_pure_all.
     
     simpljoin.
     apply val_inj2 in H93.
     repeat rewrite <- H93 in *.
    assert ( array_type_vallist_match Int8u (update_nth_val (Z.to_nat (Int.unsigned (x6>>ᵢ$ 3))) v'36
                       (val_inj
                          (and (Vint32 x12)
                             (Vint32 (Int.not ($ 1<<ᵢ(x6&ᵢ$ 7)))))))).
    apply array_type_vallist_match_hold.
    auto.
    auto.
    unfolds; simpl; auto.
    Ltac mew2 := match goal with
                   | |- (if _ then true else false) = true => rewrite ifE
                   | |- (_ <=? _ = true) => apply Zle_imp_le_bool
                   | |- (_ <= _ ) => apply Zle_bool_imp_le
                 end.
    mew2; mew2.
    apply le255_and_le255.
    auto.
    assert (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)>>ᵢ$ 3)) < length (update_nth_val (Z.to_nat (Int.unsigned (x6>>ᵢ$ 3))) v'36
             (val_inj (and (Vint32 x12) (Vint32 (Int.not ($ 1<<ᵢ(x6&ᵢ$ 7))))))))%nat.
    rewrite update_nth_val_len_eq.
    auto.


    lets fdaff: array_int8u_nth_lt_len H96 H97.
    destruct fdaff as (t1 & t2 & t3).
    simpl in t2.
Ltac simplintcompute' :=
  match goal with
    | |- context[val_inj (Some ?e)] => simpl (val_inj (Some e))
    | H : context[val_inj (Some ?e)] |- _ => simpl (val_inj (Some e)) in H
    | |- context[and (Vint32 ?e1) (Vint32 ?e2)] => simpl (and (Vint32 e1) (Vint32 e2))
    | H: context[and (Vint32 ?e1) (Vint32 ?e2)] |- _ => simpl (and (Vint32 e1) (Vint32 e2)) in H
    | |- context[or (Vint32 ?e1) (Vint32 ?e2)] => simpl (or (Vint32 e1) (Vint32 e2))
    | H: context[or (Vint32 ?e1) (Vint32 ?e2)] |- _ => simpl (or (Vint32 e1) (Vint32 e2)) in H
  end.

Ltac simplintcompute := repeat simplintcompute'.
simplintcompute.


       rewrite t2 in *.
    assert (Z.to_nat (Int.unsigned (x6>>ᵢ$ 3)) < length (update_nth_val (Z.to_nat (Int.unsigned (x6>>ᵢ$ 3))) v'36

             (val_inj (and (Vint32 x12) (Vint32 (Int.not ($ 1<<ᵢ(x6&ᵢ$ 7))))))))%nat.
    rewrite update_nth_val_len_eq.
    auto.

    lets fdaff: array_int8u_nth_lt_len H96 H98.
    destruct fdaff as (t11 & t12 & t13).
simplintcompute.
    rewrite t12 in *.

    eapply conseq_rule.
    Focus 2.

    intro.
    intro.
    exact H99.
    intro.
    intros.

instantiate (1:=( EX ttt ,

 AOSRdyTblGrp  (update_nth_val
           (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)>>ᵢ$ 3)))
           (update_nth_val (Z.to_nat (Int.unsigned (x6>>ᵢ$ 3))) v'36
              (val_inj (and (Vint32 x12) (Vint32 (Int.not ($ 1<<ᵢ(x6&ᵢ$ 7)))))))
           (val_inj
              (or
                 (Vint32 t1)
                 (Vint32 x11)))) ttt **
<|| mutexpost (Vptr (v'29, Int.zero) :: nil) ||>  **
      LV os_code_defs.x @ Int8u |-> Vint32 ((x2<<ᵢ$ 3)+ᵢx5) **
      LV legal @ Int8u |-> Vint32 x2 **
      Astruct (v'52, Int.zero) OS_TCB_flag
        (x7
         :: v'24
            :: x15
               :: m
                  :: Vint32 i6
                     :: Vint32 x14
                        :: Vint32 (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)
                           :: Vint32 ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)
                              :: Vint32  ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)>>ᵢ$ 3)
                                :: Vint32 x11 :: Vint32 x8 :: nil) **
      dllseg x7 (Vptr (v'52, Int.zero)) v'40 Vnull v'35 OS_TCB_flag
        (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
      GV OSTCBList @ OS_TCB ∗ |-> v'31 **
      dllseg v'31 Vnull v'24 (Vptr (v'52, Int.zero)) v'33 OS_TCB_flag
        (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
      GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (v'52, Int.zero) **
      LV prio @ Int8u
      |-> Vint32 (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)**
      LV pip @ Int8u |-> Vint32 (x>>ᵢ$ 8)  **
      Astruct (v'29, Int.zero) OS_EVENT
        (V$OS_EVENT_TYPE_MUTEX
         :: Vint32 i :: Vint32 x :: Vptr (v'52, $ 0) :: x3 :: v'46 :: nil) **
      Aarray v'23 (Tarray Int8u ∘OS_EVENT_TBL_SIZE) v'44 **
      Aie false **
      Ais nil **
      Acs (true :: nil) **
      Aisr empisr **
      GV OSEventList @ OS_EVENT ∗ |-> v'42 **
      evsllseg v'42 (Vptr (v'29, Int.zero)) v'25 v'27 **
      evsllseg v'46 Vnull v'26 v'28 **
      A_isr_is_prop **
      HECBList v'38 **
      HTCBList v'39 **
      HCurTCB (v'52, Int.zero) **
      AOSEventFreeList v'3 **
      AOSQFreeList v'4 **
      AOSQFreeBlk v'5  **
      AOSMapTbl **
      GAarray OSUnMapTbl (Tarray Int8u 256) OSUnMapVallist **
      AOSIntNesting **
      AOSTCBFreeList v'21 v'22 **
      AOSTime (Vint32 v'18) **
      HTime v'18 **
      AGVars **
      atoy_inv' **
      LV pevent @ OS_EVENT ∗ |-> Vptr (v'29, Int.zero) **
   [|x1 = Vptr v'51|] **
      A_dom_lenv
        ((pevent, OS_EVENT ∗)
         :: (os_code_defs.x, Int8u)
            :: (pip, Int8u) :: (prio, Int8u) :: (legal, Int8u) :: nil) **
  AOSTCBPrioTbl (update_nth_val (Z.to_nat (Int.unsigned (x>>ᵢ$ 8)))
                (update_nth_val
                   (Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) v'30
                   (Vptr (v'52, Int.zero))) (Vptr v'51)) ((update_nth_val
           (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)>>ᵢ$ 3)))
           (update_nth_val (Z.to_nat (Int.unsigned (x6>>ᵢ$ 3))) v'36
              (val_inj (and (Vint32 x12) (Vint32 (Int.not ($ 1<<ᵢ(x6&ᵢ$ 7)))))))
           (val_inj
              (or
                 (nth_val'
                    (Z.to_nat
                       (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)>>ᵢ$ 3)))
                    (update_nth_val (Z.to_nat (Int.unsigned (x6>>ᵢ$ 3))) v'36
                       (val_inj
                          (and (Vint32 x12)
                             (Vint32 (Int.not ($ 1<<ᵢ(x6&ᵢ$ 7))))))))
                 (Vint32 x11))))) (TcbMod.set v'39  (v'52, Int.zero) (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8, t, m)) v'51 **
  tcbdllflag v'31
             (v'33 ++
              (x7
               :: v'24
                  :: x15
                     :: m
                        :: Vint32 i6
                           :: Vint32 x14
                              :: Vint32 x6
                                 :: Vint32 (x6&ᵢ$ 7)
                                    :: Vint32 (x6 >>ᵢ $ 3)
                                       :: Vint32 ($ 1<<ᵢ(x6&ᵢ$ 7))
                                          :: Vint32 ($ 1<<ᵢ(x6 >>ᵢ $ 3))
                                             :: nil) :: v'35) **
            p_local OSLInv (v'52, Int.zero) init_lg 
                )).
simplintcompute.
change (GV OSRunning @ Int8u |-> (V$ 1) **
             (EX v : int32,
              GV OSPrioHighRdy @ Int8u |-> Vint32 v **
              [|Int.unsigned v <= 63|]) **
             (EX v : int32, GV OSCtxSwCtr @ Int32u |-> Vint32 v) **
             (EX v : addrval,
              GV OSTCBHighRdy @ OS_TCB ∗ |-> Vptr v) **
             (EX v : int32,
              GV OSPrioCur @ Int8u |-> Vint32 v ** [|Int.unsigned v <= 63|]) **
             (EX v : int32, GV OSIntExitY @ Int8u |-> Vint32 v)) with AGVars in H99.
change ( (EX v : int32, GV OSIntNesting @ Int32u |-> Vint32 v) ) with AOSIntNesting in H99.
  rewrite t2.
  
  apply DisjPropE in H99.
  destruct H99; intros.
  unfold AOSMapTbl.
  unfold AOSRdyTblGrp.
  unfold AOSRdyGrp.
  unfold AOSRdyTbl.
  unfold AOSTCBPrioTbl.
  sep pauto.
  (* sep cancel 10%nat 2%nat. *)
 (* sep cancel Aop.
  * sep pauto.
  * sep cancel 3%nat 1%nat.
  * sep cancel A_dom_lenv.
  * sep cancel 2%nat 1%nat.
  * Print Ltac sep_auto.
  * Print Ltac scancel.
  * Print Ltac scancel'.
  * Print Ltac cancel_same.
  * sep lift 35%nat .
  * sep cancel 1%nat 1%nat.
  * sep pauto.
  * sep cancel 3%nat 1%nat.
  * sep cancel 3%nat 1%nat.
  * sep pauto.
  * (* repeat sep cancel 1%nat 1%nat.
  * *   GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64)
  * *              (update_nth_val (Z.to_nat (Int.unsigned (x >>ᵢ $ 8)))
  * *                 (update_nth_val
  * *                    (Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)))
  * *                    v'30 (Vptr (v'52, Int.zero))) (Vptr v'51)) **
  * *            GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
  * *              (update_nth_val
  * *                 (Z.to_nat
  * *                    (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
  * *                 (update_nth_val
  * *                    (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3))) v'36
  * *                    (Vint32 (x12&ᵢInt.not ($ 1<<ᵢ((x >>ᵢ $ 8)&ᵢ$ 7)))))
  * *                 (Vint32 (Int.or t1 x11))) **
  * *  
  * * sep pauto. *) *)
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aisr.
  unfold AOSTime.
  sep cancel 1%nat 1%nat.
  sep cancel 1%nat 2%nat.
  auto.
  
  (* sep cancel evsllseg.
   * sep cancel evsllseg.
   * sep cancel Astruct.
   * sep cancel Astruct.
   * sep cancel GAarray.
   * sep cancel GAarray.
   * Locate "G&".
   * sep cancel Agvarenv'.
   * sep cancel AGVars.
   * sep cancel A_isr_is_prop.
   * sep cancel 2%nat 1%nat.
   * sep cancel dllseg.
   * sep cancel 1%nat 2%nat.
   * sep cancel 1%nat 2%nat.
   * repeat sep cancel 1%nat 2%nat.
   * unfold p_local in H99.
   * unfold CurTid in H99.
   * unfold OSLInv in H99.
   * sep normal in H99.
   * sep destruct H99.
   * Locate "LINV".
   * unfold init_lg in H99.
   * sep normal in H99.
   * simpl (LINV
   *            (fun (t : tid) (lg : list logicvar) =>
   *             EX v : val,
   *             PV get_off_addr t ($ 24) @ Int8u |-r-> v **
   *             [|lg = logic_val v :: nil /\ isflag v|]) 
   *            (v'52, Int.zero) (logic_val (V$ 1) :: nil) ) in H99.
   * 
   * Locate "LINV".
   * unfold LINV in H99.
   * sep normal in H99.
   * sep destruct H99.
   * sep split in H99.
   * 
   * sep cancel 1%nat 1%nat.
   * simpl in H99.
   * sep cancel  *)


  eapply return_r_pt_p; eauto.
  
  assert ( (v'52, Int.zero) <> v'51).
  eapply intcbnotvhold.
  eauto.
  clear H99.
  unfold join in *; simpl in *.
  unfold sig in *; simpl in *.
  go.

  eapply return_rl_rt_pt_p; eauto.

  split.
  apply array_type_vallist_match_hold.
  apply array_type_vallist_match_hold.
  auto.
  2:unfolds; simpl; auto.
  rewrite H51.
  clear -H48.
  remember  (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8).
  mauto.
  rewrite update_nth_val_len_eq.
  rewrite H51.
  clear -H85.
  remember  (x>>ᵢ$ 8).
  mauto.
  unfolds; simpl; auto.
  
  rewrite update_nth_val_len_eq.

  rewrite update_nth_val_len_eq.
  auto.


  eapply return_rl_t_g_p; eauto.
  unfolds; simpl; auto.

  mew2.
  mew2.
  change Byte.max_unsigned with 255.
  apply int_unsigned_or_prop'.
  apply le255_and_le255.
  auto.
  apply int8ule255; auto.
  split.
  apply array_type_vallist_match_hold.
  apply array_type_vallist_match_hold.
  auto.
  auto.
  unfolds; simpl; auto.
  mew2; mew2.

  change Byte.max_unsigned with 255.
  apply le255_and_le255; auto.

  rewrite update_nth_val_len_eq.
  auto.
  unfolds; simpl; auto.
  mew2; mew2.
  apply int_unsigned_or_prop'.
  auto.
  apply int8ule255; auto.
  rewrite update_nth_val_len_eq.
  rewrite update_nth_val_len_eq.
  auto.

  unfold AOSMapTbl.
  unfold AOSRdyTblGrp.
  unfold AOSRdyGrp.
  unfold AOSRdyTbl.
  unfold AOSTCBPrioTbl.
  sep pauto.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aisr.
  auto.
  eapply return_r_pt_p; eauto.

  assert ( (v'52, Int.zero) <> v'51).
  eapply intcbnotvhold.
  eauto.

  clear H99.
  unfold join in *; simpl in *.
  unfold sig in *; simpl in *.
  go.
  eapply return_rl_rt_pt_p; eauto.
  split.
  apply array_type_vallist_match_hold.
  apply array_type_vallist_match_hold.
  auto.
  2:unfolds; simpl; auto.
  rewrite H51.
  clear -H48.
  remember  (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8).
  mauto.
  rewrite update_nth_val_len_eq.
  rewrite H51.
  clear -H85.
  remember  (x>>ᵢ$ 8).
  mauto.
  unfolds; simpl; auto.
  
  rewrite update_nth_val_len_eq.
  
  rewrite update_nth_val_len_eq.
  auto.

  eapply return_rl_t_g_p'; eauto.
  unfolds; simpl; auto.

  mew2.
  mew2.
  change Byte.max_unsigned with 255.
  apply int_unsigned_or_prop'.
  auto.
  apply int8ule255; auto.
  split.
  apply array_type_vallist_match_hold.
  apply array_type_vallist_match_hold.
  auto.
  auto.
  unfolds; simpl; auto.
  mew2; mew2.

  change Byte.max_unsigned with 255.
  apply le255_and_le255; auto.

  rewrite update_nth_val_len_eq.
  auto.
  unfolds; simpl; auto.
  mew2; mew2.
  apply int_unsigned_or_prop'.
  auto.
  apply int8ule255; auto.
  rewrite update_nth_val_len_eq.
  rewrite update_nth_val_len_eq.
  auto.
  simplintcompute.
  rewrite t2.
  hoare_split_pure_all.
  subst x1.
  hoare forward.
  (* intro; tryfalse. *)
  go.
  (* hoare unfold. *)

  destruct ( Int.eq i ($ 0)) ; simpl; intro; tryfalse.
  destruct ( Int.eq i ($ 0)) ; simpl; intro; tryfalse.
  hoare forward.
  hoare unfold.


  unfold AOSTCBPrioTbl.
  hoare unfold.
  hoare forward.
  unfold AEventNode.
  unfold AOSEvent.
  unfold AOSEventTbl.
  unfold node.
  unfold AEventData.
  unfold AOSTCBList.
  unfold AOSUnMapTbl.
  unfold tcbdllseg.

  instantiate (19:= (DMutex (Vint32 x) (Vptr (v'52, $ 0)))).
  sep pauto.
(* ** ac:   Show. *)
(* ** ac:   Show. *)
  sep cancel 12%nat 1%nat.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aisr.
  sep cancel Aop.
  sep cancel AOSRdyTblGrp.
  sep cancel Aarray.
  

  (* sep cancel 7%nat 2%nat.
   * sep cancel 7%nat 2%nat.
   * sep cancel 1%nat 2%nat. *)
  (* SearchAbout TCBList_P.
   * Print TCBList_P. *)
  (* Focus 14.
 * 
 *   SearchAbout TCBList_P.
 *   eapply return_tcbl_p.
 *   2: unprotect last_condition; simpljoin; exact backup2.
 * assert (t=rdy).
 * 
 *   {
 *   unfold1 TCBList_P in backup2.
 *   simpljoin.
 *   unfolds in H111.
 *   destruct x18; destruct p; simpljoin.
 *   unprotect last_condition; destruct last_condition as (ll & lll); apply eq2inteq in ll; apply eq2inteq in lll.
 * 
 *   apply (low_stat_rdy_imp_high _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H54 H58 H114 H73 ll lll).
 *   }
 *   subst t.
 * 
 * 
 *   exact H70. *)
  (* unfold1 dllseg.
   * unfold node.
   * sep pauto.
   * sep cancel Astruct.
   * sep cancel dllseg.
   * eauto. *)

  Require Import inv_prop.
Lemma dllseg_compose:
  forall (s : RstateOP) (P : asrt) (h hp t1 tn1 t2 tn2 : val)
         (l1 l2 : list vallist),
    s |= dllseg h hp t1 tn1 l1 OS_TCB_flag
      (fun vl : vallist => nth_val 1 vl)
      (fun vl : vallist => nth_val 0 vl) ** dllseg tn1 t1 t2 tn2 l2  OS_TCB_flag
      (fun vl : vallist => nth_val 1 vl)
      (fun vl : vallist => nth_val 0 vl)** P ->
    s |= dllseg h hp t2 tn2 (l1 ++ l2)  OS_TCB_flag
      (fun vl : vallist => nth_val 1 vl)
      (fun vl : vallist => nth_val 0 vl) ** P.
Proof.
  intros.
  generalize s P h hp t1 tn1 t2 tn2 l2 H.
  clear s P h hp t1 tn1 t2 tn2 l2 H.
  induction l1.
  intros.
  unfold tcbdllseg in H.
  unfold dllseg in H.
  fold dllseg in H.
  sep split in H.
  subst.
  simpl; auto.
  intros.
  simpl ( (a::l1) ++l2).

  unfold tcbdllseg in *.
  unfold dllseg in *.
  fold dllseg in *.
  sep normal.
  
  sep auto.
  apply StarEmpER.
  eapply IHl1.
  sep auto.
  auto.
Qed.

  (* Require Import OSMutexPendPure1.
   * Check dllseg_compose.
   * Lemma dllseg_compose:
   * forall (s : RstateOP) (P : asrt) (h hp t1 tn1 t2 tn2 : val)
   *        (l1 l2 : list vallist),
   *   s |= dllseg h hp t1 tn1 l1 OS_TCB_flag
   *     (fun vl : vallist => nth_val 1 vl)
   *     (fun vl : vallist => nth_val 0 vl) ** dllseg tn1 t1 t2 tn2 l2  OS_TCB_flag
   *     (fun vl : vallist => nth_val 1 vl)
   *     (fun vl : vallist => nth_val 0 vl)** P ->
   *   s |= dllseg h hp t2 tn2 (l1 ++ l2)  OS_TCB_flag
   *     (fun vl : vallist => nth_val 1 vl)
   *     (fun vl : vallist => nth_val 0 vl) ** P.
   * Admitted. *)

  eapply dllseg_compose.
  
  sep cancel 7%nat 1%nat. 
  instantiate (2:= ( 
             (x7
              :: v'24
                 :: x15
                    :: m
                       :: Vint32 i6
                          :: Vint32 x14
                             :: Vint32 (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)
                                :: Vint32 ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)
                                   :: Vint32
                                        ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)
                                        :: Vint32 x11 :: Vint32 x8 :: nil)  :: v'35)).
  unfold1 dllseg.
  unfold tcbdllseg.
  unfold dllseg;fold dllseg.
  unfold node.

  sep pauto.
  sep cancel 4%nat 1%nat.
  sep cancel 4%nat 1%nat.
  eauto.

  go.
  go.

    assert (Int.unsigned x11 <= Byte.max_unsigned).
    apply int8ule255.
    auto.
    clear -H107 H108; omega.
    assert (Int.unsigned x8 <= Byte.max_unsigned).
    apply int8ule255; auto.
    clear -H107 H108; omega.



  
  go.
  go.
  go.
  go.
  go.
  exact H14.
  go.
  go.
  go.
  clear -H99.
  remember (Int.eq i ($ 0)).
  destruct b; simpl in *.
  false; apply H99.
  int auto.
  clear -Heqb.
  intro; subst i; int auto.
  
  go.
  go.
  go.
  Focus 3.
  unfold AOSTCBPrioTbl in H93.
  sep normal in H93.
  sep destruct H93.
  sep split in H93.
  go.

  Focus 2.

  assert (t=rdy).

  {
  unfold1 TCBList_P in backup2.
  simpljoin.
  unfolds in H115.
  destruct x18; destruct p; simpljoin.
  unprotect last_condition; destruct last_condition as (ll & lll); apply eq2inteq in ll; apply eq2inteq in lll.

  apply (low_stat_rdy_imp_high _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H54 H58 H118 H73 ll lll).
  }
  subst t.

  eapply return_r_ecb_et_p.
  unfold TcbJoin in H70.
  unfold join in H70; unfold sig in H70; simpl in H70.
  unfold join in H32; simpl in H32.
  go.
  go.

  (* H32 : join v'43 v'45 v'39
   * H33 : TCBList_P v'31 v'33 v'36 v'43
   * backup2 : TCBList_P (Vptr (v'52, Int.zero))
   *             ((x7
   *               :: v'24
   *                  :: x15
   *                     :: m
   *                        :: Vint32 i6
   *                           :: Vint32 x14
   *                              :: Vint32 (x >>ᵢ $ 8)
   *                                 :: Vint32 ((x >>ᵢ $ 8)&ᵢ$ 7)
   *                                    :: Vint32 ((x >>ᵢ $ 8) >>ᵢ $ 3)
   *                                       :: Vint32 ($ 1<<ᵢ((x >>ᵢ $ 8)&ᵢ$ 7))
   *                                          :: Vint32
   *                                               ($ 1<<ᵢ((x >>ᵢ $ 8) >>ᵢ $ 3))
   *                                             :: nil) :: v'35) v'36 v'45 *)

  (* {
   *   Check return_tcbl_p.
   *   (* eapply return_tcbl_p.
   *    * 2: unprotect last_condition; simpljoin; exact backup2. *)
   *   assert (t=rdy).
   * 
   *   {
   *     unfold1 TCBList_P in backup2.
   *     simpljoin.
   *     unfolds in H111.
   *     destruct x18; destruct p; simpljoin.
   *     unprotect last_condition; destruct last_condition as (ll & lll); apply eq2inteq in ll; apply eq2inteq in lll.
   * 
   *     apply (low_stat_rdy_imp_high _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H54 H58 H114 H73 ll lll).
   *   }
   *   subst t.
   *   eapply return_tcbl_p; eauto.
   *   Print TCBList_P.
   *   Print AOSTCBPrioTbl.
   *   Print HTCBList .
   *   2: unprotect last_condition; simpljoin; exact H70.
   * } *)
  (* unfold1 dllseg.
   * unfold node.
   * sep pauto.
   * sep cancel Astruct.
   * sep cancel dllseg.
   * eauto. *)
(* ** ac:   SearchAbout TCBList_P. *)
  {
(* ** ac:     Check TCBList_P_Combine. *)
  eapply TCBList_P_Combine.
(* ** ac:   SearchAbout get_last_tcb_ptr. *)
  (* in osqpostproof1 *)
(* Lemma tcbdllseg_get_last_tcb_ptr :
 *   forall vl head headprev tail tailnext P s,
 *     s |= tcbdllseg head headprev tail tailnext vl ** P ->
 *     get_last_tcb_ptr vl head = Some tailnext.
 * Proof.
 *  
 * Admitted. *)
eapply tcbdllseg_get_last_tcb_ptr.
instantiate (5:= s).
unfold tcbdllseg.
sep auto.

  Focus 2.
  eapply return_tcbl_p'; eauto.
  instantiate (1:= (TcbMod.set v'45 (v'52, Int.zero) (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8, t, m)) ).
(* ** ac:   Check return_tcbl_p. *)
  Focus 2.
  
    assert (t=rdy).

    unfold1 TCBList_P in backup2.
    simpljoin.
    unfolds in H115.
    destruct x18; destruct p; simpljoin.
    unprotect last_condition; destruct last_condition as (ll & lll); apply eq2inteq in ll; apply eq2inteq in lll.

    apply (low_stat_rdy_imp_high _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H54 H58 H118 H73 ll lll).
    subst t.

    unprotect last_condition.
    simpljoin.
 
  eapply return_tcbl_p; eauto.
 
    apply TcbMod.join_set_r.
    auto.
    unfolds; eexists.

  unfold TcbJoin in H70.
  unfold join in H70; unfold sig in H70; simpl in H70.
  unfold join in H32; simpl in H32.

    go.
  }

  unfold AOSTCBPrioTbl in H93.
  sep normal in H93.
  sep destruct H93.
  sep split in H93.
  go.


  unfold AOSTCBPrioTbl in H93.
  sep normal in H93.
  sep destruct H93.
  sep split in H93.

  (* in osqpostproof1 *)
(* Lemma tcbdllseg_combine_ptr_in_tcblist :
 *   forall vl1 vl2 head1 headprev1 tail1 tailnext1 tail2 tailnext2 s P,
 *     s |= tcbdllseg head1 headprev1 tail1 tailnext1 vl1 ** tcbdllseg tailnext1 tail1 tail2 tailnext2 vl2 ** P ->
 *     vl2 <> nil ->
 *     ptr_in_tcblist tailnext1 head1 (vl1 ++ vl2).
 * Proof.
 * Admitted. *)
{
eapply tcbdllseg_combine_ptr_in_tcblist.
unfold tcbdllseg.

Set Printing Depth 999.
unfold1 dllseg.
unfold node.
sep normal.
sep eexists.
sep split.
instantiate (8 := s).
sep auto.
intro; tryfalse.
go. 
go. 
go. 

    assert (Int.unsigned x11 <= Byte.max_unsigned).
    apply int8ule255.
    auto.
    clear -H112 H113; omega.
    assert (Int.unsigned x8 <= Byte.max_unsigned).
    apply int8ule255; auto.
    clear -H112 H113; omega.
    intro; tryfalse.
    }

  (* go.
   * go.
   * go.
   * go.
   * apply postintlemma3.
   * apply le255_and_le255.
   * apply postintlemma3.
   * 
   * clear -H48.
   * remember (x&$ OS_MUTEX_KEEP_LOWER_8).
   * mauto.
   * 
   * apply int8ule255.
   * auto.
   * apply int8ule255.
   * auto.
   * go.
   * go.
   * go.
   * go.
   * go.  go.  go.  go.  go.
   * instantiate (1:= TcbMod.set v'45 (v'52, Int.zero) (x&$ OS_MUTEX_KEEP_LOWER_8, t, m)).
   * 
   * 
   * assert (t=rdy).
   * 
   * unfold1 TCBList_P in backup2.
   * mytac.
   * unfolds in H107.
   * destruct x18; destruct p; mytac.
   * unprotect last_condition; destruct last_condition as (ll & lll); apply eq2inteq in ll; apply eq2inteq in lll.
   * 
   * (* Require Import OSTimeDlyPure. *)
   * apply (low_stat_rdy_imp_high _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H54 H58 H110 H73 ll lll).
   * subst t.
   * unprotect last_condition; mytac.
   * 
   * eapply return_tcbl_p; eauto.
   * 
   * instantiate (1:= v'43).
   * 
   * eapply  return_tcbl_p'; eauto.
   * 
   * apply TcbMod.join_set_r.
   * auto.
   * unfolds; eexists.
   * go.
   * go.
   * 
   * 
   * apply intlemmaf; auto.
   * 
   * assert (t=rdy).
   * 
   * unfold1 TCBList_P in backup2.
   * mytac.
   * unfolds in H111.
   * destruct x18; destruct p; mytac.
   * unprotect last_condition; destruct last_condition as (ll & lll); apply eq2inteq in ll; apply eq2inteq in lll.
   * 
   * apply (low_stat_rdy_imp_high _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H54 H58 H114 H73 ll lll).
   * subst t.
   * unprotect last_condition; mytac.
   * 
   * eapply return_r_ecb_et_p; eauto.
   * go.
   * go. *)
go.
  exact retpost_eventrdy.

  intro.
  intros.
  sep normal in H105.
  sep destruct H105.
  sep eexists.
  sep cancel p_local.
  simpl; auto.
(* ** ac:   Show. *)
(* ** ac:   Show. *)
  intro.
  intros.
  sep normal in H105.
  sep destruct H105.
  sep eexists.
  sep cancel p_local.
  simpl; auto.

  instantiate (1:=Afalse).
  hoare unfold.




  
  Set Printing Depth 999.
  

  
  Focus 2.
  {
    hoare forward.
    hoare unfold.
    hoare forward.
    (* meew. *)
    go.
    (* intro; tryfalse. *)
    go.
    (* intro;tryfalse. *)
    hoare forward.
    (* meew. *)


    assert (w =nil ).
    eapply post_exwt_succ_pre_mutex' with (v'12 := i) ; eauto.
    apply val_inj_eq; auto.
    subst w.

    assert (t=rdy).

    unfold1 TCBList_P in backup2.
    simpljoin.
    unfolds in H102.
    destruct x18; destruct p; simpljoin.
    unprotect last_condition; destruct last_condition as (ll & lll); apply eq2inteq in ll; apply eq2inteq in lll.

    apply (low_stat_rdy_imp_high _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H54 H58 H105 H73 ll lll).
    subst t.
    unprotect last_condition; simpljoin.
    
    hoare abscsq.
    apply noabs_oslinv.

    eapply absinfer_mutexpost_return_nowt_succ.
    go.
    
    go.

  unfold TcbJoin in H70.
  unfold join in H70; unfold sig in H70; simpl in H70.
  unfold join in H32; simpl in H32.
    go.
    clear -H47.
    remember  (x>>ᵢ$ 8); remember (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8).
    clear Heqi; clear Heqi0 .
    int auto.
    
    hoare forward prim.
    unfold AECBList.
    unfold AOSUnMapTbl.
    unfold AOSTCBList.
    sep pauto.
    unfold tcbdllseg.
    sep pauto.
    sep cancel 7%nat 1%nat.
    unfold1 dllseg.
    sep pauto.
    sep cancel dllseg.
    unfold node.
    sep pauto.
    sep cancel 5%nat 1%nat.
    

(* ** ac:     SearchAbout tcbdllflag. *)
(* ** ac:     Print tcbdllflag. *)
(* ** ac:     Print dllsegflag. *)
    instantiate (3:= (v'25 ++
                           (( (V$OS_EVENT_TYPE_MUTEX
                                :: Vint32 i
                                :: Vint32 (Int.or x ($ OS_MUTEX_AVAILABLE))
                                :: Vnull :: x3 :: v'46 :: nil),
                              v'44) :: nil) ++ v'26)).
    instantiate (2:= (v'27 ++ (DMutex ( Vint32 (Int.or x ($ OS_MUTEX_AVAILABLE))) (Vnull) :: nil) ++ v'28)).
    
    eapply evsllseg_compose; eauto.
    go.
    
    unfold AEventNode.
    unfold AEventData.

    unfold_msg.
    sep pauto.
    
    sep cancel 2%nat 1%nat.
    sep cancel 6%nat 1%nat.
    sep cancel 6%nat 1%nat.

(* ** ac:     SearchAbout tcbdllflag. *)

    eapply tcbdllflag_hold.
    2: sep cancel tcbdllflag; eauto.
(* ** ac:     SearchAbout eq_dllflag. *)
    apply tcbdllflag_hold_middle.
    unfolds.
    simpl.
    unfold V_OSTCBNext, V_OSTCBflag; simpl.
    auto.
    
    go.
    go.  go.  go.  
    

    assert (Int.unsigned (Int.or x ($ OS_MUTEX_AVAILABLE)) < 65536).
    change 65536 with (two_power_nat 16).
    unfold Int.or.
    unfold OS_MUTEX_AVAILABLE.
    assert (Z.lor (Int.unsigned x) ( 255) < two_power_nat 16).
    apply  acpt_intlemma12.
    clear -H10 ; change (two_power_nat 16) with 65536; omega.
    clear ; change (two_power_nat 16) with 65536; omega.
    
    change (two_power_nat 16) with 65536 in *.
    clear -H102; repeat ur_rewriter; try omega.
    remember ( Z.lor (Int.unsigned x) 255 ).
    int auto.

    rewrite Heqz.
    apply Z_lor_range_lo.
    int auto.
    omega.
    clear -H101 H102.
    change Int16.max_unsigned with 65535 in H101.
    
    remember (   Int.unsigned (Int.or x ($ OS_MUTEX_AVAILABLE))) ; omega.
    go.

    assert (Int.unsigned x11 <= Byte.max_unsigned).
    apply int8ule255.
    auto.
    clear -H101 H102; omega.
    assert (Int.unsigned x8 <= Byte.max_unsigned).
    apply int8ule255; auto.
    clear -H101 H102; omega.

    (* apply postintlemma3.
     * apply le255_and_le255.
     * apply postintlemma3.
     * 
     * clear -r3; remember  ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)>>ᵢ$ 3); mauto.
     * apply int8ule255; auto.
     * apply int8ule255; auto. *)
    go. go.

    eapply return_ecbl_p .
    exact H70.
    eauto.

    eapply ecblistp_hold; eauto.


    sep lift 14%nat in H93.
    eapply evsllseg_aux.
    exact H93.
    remember (     (update_nth_val
                      (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)>>ᵢ$ 3)))
                      (update_nth_val (Z.to_nat (Int.unsigned ((x>>ᵢ$ 8)>>ᵢ$ 3))) v'36
                                      (val_inj
                                         (and (Vint32 x12) (Vint32 (Int.not ($ 1<<ᵢ((x>>ᵢ$ 8)&ᵢ$ 7)))))))
                      (val_inj (or (Vint32 t1) (Vint32 x11))))) as rdy_tbl.
    instantiate (1:=(TcbMod.set v'45 (v'52, Int.zero) (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8, rdy, m))).

    2:instantiate (1:= (v'43)).

    Focus 3.
    apply TcbMod.join_set_r.
    auto.
    unfolds.
  unfold TcbJoin in H70.
  unfold join in H70; unfold sig in H70; simpl in H70.
  unfold join in H32; simpl in H32.
    eexists; go.

    subst rdy_tbl.
(* ** ac:     Check return_tcbl_p. *)
    eapply return_tcbl_p; eauto.
    eapply  return_tcbl_p' ; eauto.


    apply return_rh_ctcb.
    eapply  return_rh_tcbl_ecbl_p ; eauto.

    eapply mutex_rh_tcblist_ecblist_p_hold; eauto.
    go.
    go.
    hoare unfold.
    hoare forward.

  }
  Unfocus.
  inverts H135.
  hoare unfold.
  hoare forward.
  (* intro; tryfalse. *)
  (* intro; tryfalse. *)



(* Lemma post3 :
 * 
 * forall (
 *   v' v'0 v'1 v'2 : val
 * )(
 *   v'3 v'4 v'5 : list vallist
 * )(
 *   v'6 : list EventData
 * )(
 *   v'7 : list os_inv.EventCtr
 * )(
 *   v'8 : vallist
 * )(
 *   v'9 v'10 : val
 * )(
 *   v'11 : list vallist
 * )(
 *   v'12 : vallist
 * )(
 *   v'13 : list vallist
 * )(
 *   v'14 : vallist
 * )(
 *   v'15 : val
 * )(
 *   v'16 : EcbMod.map
 * )(
 *   v'17 : TcbMod.map
 * )(
 *   v'18 : int32
 * )(
 *   v'19 : addrval
 * )(
 *   v'21 : val
 * )(
 *   v'22 : list vallist
 * )(
 *   v'25 v'26 : list os_inv.EventCtr
 * )(
 *   v'27 v'28 : list EventData
 * )(
 *   v'30 : vallist
 * )(
 *   v'33 v'35 : list vallist
 * )(
 *   v'36 : vallist
 * )(
 *   v'38 : EcbMod.map
 * )(
 *   v'39 : TcbMod.map
 * )(
 *   v'42 v'46 : val
 * )(
 *   v'47 v'48 v'49 : EcbMod.map
 * )(
 *   w : waitset
 * )(
 *   H3 : ECBList_P v'46 Vnull v'26 v'28 v'48 v'39
 * )(
 *   H17 : EcbMod.join v'47 v'49 v'38
 * )(
 *   H12 : length v'25 = length v'27
 * )(
 *   H16 : isptr v'46
 * )(
 *   v'23 : addrval
 * )(
 *   x3 : val
 * )(
 *   H24 : isptr v'46
 * )(
 *   H20 : Int.unsigned ($ OS_EVENT_TYPE_MUTEX) <= 255
 * )(
 *   x : int32
 * )(
 *   H10 H22 : Int.unsigned x <= 65535
 * )(
 *   v'24 : val
 * )(
 *   v'43 v'45 : TcbMod.map
 * )(
 *   v'52 : block
 * )(
 *   H32 : join v'43 v'45 v'39
 * )(
 *   H30 : Vptr (v'52, Int.zero) <> Vnull
 * )(
 *   i6 : int32
 * )(
 *   H39 : Int.unsigned i6 <= 65535
 * )(
 *   H36 : isptr v'24
 * )(
 *   x7 : val
 * )(
 *   x10 : TcbMod.map
 * )(
 *   t : taskstatus
 * )(
 *   m : msg
 * )(
 *   H72 : TCBList_P x7 v'35 v'36 x10
 * )(
 *   H : RH_TCBList_ECBList_P v'16 v'17 (v'52, Int.zero)
 * )(
 *   H0 : RH_CurTCB (v'52, Int.zero) v'17
 * )(
 *   H7 : RH_TCBList_ECBList_P v'38 v'39 (v'52, Int.zero)
 * )(
 *   H8 : RH_CurTCB (v'52, Int.zero) v'39
 * )(
 *   H23 : isptr (Vptr (v'52, $ 0))
 * )(
 *   H29 : x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 = $ OS_MUTEX_AVAILABLE \/
 *         x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 <> $ OS_MUTEX_AVAILABLE
 * )(
 *   H35 : x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 <> $ OS_MUTEX_AVAILABLE
 * )(
 *   H48 : Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) < 64
 * )(
 *   H4 : Some (v'52, $ 0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = None -> w = nil
 * )(
 *   H13 : w <> nil -> Some (v'52, $ 0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) <> None
 * )(
 *   H25 : x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 = $ OS_MUTEX_AVAILABLE ->
 *         Some (v'52, $ 0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = None /\
 *         Vptr (v'52, $ 0) = Vnull
 * )(
 *   H26 : x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 <> $ OS_MUTEX_AVAILABLE ->
 *         exists tid,
 *         Vptr (v'52, $ 0) = Vptr tid /\
 *         Some (v'52, $ 0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) =
 *         Some (tid, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)
 * )(
 *   v'32 : val
 * )(
 *   H46 : array_type_vallist_match OS_TCB ∗ v'30
 * )(
 *   H51 : length v'30 = 64%nat
 * )(
 *   x0 : val
 * )(
 *   H54 : array_type_vallist_match Int8u v'36
 * )(
 *   H58 : length v'36 = ∘ OS_RDY_TBL_SIZE
 * )(
 *   i7 : int32
 * )(
 *   H55 : Int.unsigned i7 <= 255
 * )(
 *   H57 : prio_in_tbl ($ OS_IDLE_PRIO) v'36
 * )(
 *   H56 : RL_Tbl_Grp_P v'36 (Vint32 i7)
 * )(
 *   x2 : int32
 * )(
 *   H59 : length OSUnMapVallist = 256%nat
 * )(
 *   H62 : true = rule_type_val_match Int8u (Vint32 x2)
 * )(
 *   fffbb : Int.unsigned x2 < 8
 * )(
 *   x4 : int32
 * )(
 *   H64 : Int.unsigned x4 <= 255
 * )(
 *   H65 : (Z.to_nat (Int.unsigned x4) < length OSUnMapVallist)%nat
 * )(
 *   x5 : int32
 * )(
 *   H66 : nth_val' (Z.to_nat (Int.unsigned x4)) OSUnMapVallist = Vint32 x5
 * )(
 *   H67 : Int.unsigned x5 <= 255
 * )(
 *   ttfasd : Int.unsigned x5 < 8
 * )(
 *   H27 : isptr x7
 * )(
 *   H38 : isptr m
 * )(
 *   x14 : int32
 * )(
 *   H82 : x14 = $ OS_STAT_RDY \/
 *         x14 = $ OS_STAT_SEM \/
 *         x14 = $ OS_STAT_Q \/ x14 = $ OS_STAT_MBOX \/ x14 = $ OS_STAT_MUTEX
 * )(
 *   x15 : val
 * )(
 *   H84 : x14 = $ OS_STAT_RDY -> x15 = Vnull
 * )(
 *   H37 : isptr x15
 * )(
 *   H40 : Int.unsigned x14 <= 255
 * )(
 *   last_condition : ProtectWrapper (x14 = $ OS_STAT_RDY /\ i6 = $ 0)
 * )(
 *   r2 : Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7) < 8
 * )(
 *   r3 : Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3) < 8
 * )(
 *   H34 : array_type_vallist_match Int8u OSMapVallist
 * )(
 *   H69 : length OSMapVallist = 8%nat
 * )(
 *   H71 : (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)) < 8)%nat
 * )(
 *   x8 : int32
 * )(
 *   H74 : nth_val'
 *           (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
 *           OSMapVallist = Vint32 x8
 * )(
 *   H75 : true = rule_type_val_match Int8u (Vint32 x8)
 * )(
 *   H76 : (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)) < 8)%nat
 * )(
 *   x9 : int32
 * )(
 *   H78 : nth_val'
 *           (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)))
 *           OSMapVallist = Vint32 x9
 * )(
 *   H79 : true = rule_type_val_match Int8u (Vint32 x9)
 * )(
 *   H80 : (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)) < 8)%nat
 * )(
 *   x11 : int32
 * )(
 *   H81 : nth_val'
 *           (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)))
 *           OSMapVallist = Vint32 x11
 * )(
 *   H83 : true = rule_type_val_match Int8u (Vint32 x11)
 * )(
 *   rr2 : (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)) <
 *          length v'36)%nat
 * )(
 *   rr3 : (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)) <
 *          length v'36)%nat
 * )(
 *   rrr2 : Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7) <
 *          Z.of_nat (length v'36)
 * )(
 *   rrr3 : Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3) <
 *          Z.of_nat (length v'36)
 * )(
 *   HH58 : length v'36 = Z.to_nat 8
 * )(
 *   aa2 : rule_type_val_match Int8u
 *           (nth_val'
 *              (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
 *              v'36) = true
 * )(
 *   x16 : int32
 * )(
 *   H91 : Int.unsigned x16 <= 255
 * )(
 *   x13 : int32
 * )(
 *   H87 : nth_val'
 *           (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
 *           v'36 = Vint32 x13
 * )(
 *   H90 : Int.unsigned x13 <= 255
 * )(
 *   x12 : int32
 * )(
 *   H89 : Int.unsigned x12 <= 255
 * )(
 *   t1 : int32
 * )(
 *   t3 : Int.unsigned t1 <= 255
 * )(
 *   t11 : int32
 * )(
 *   t13 : Int.unsigned t11 <= 255
 * )(
 *   H15 : Int.unsigned (x >>ᵢ $ 8) < 64
 * )(
 *   H47 : Int.ltu (x >>ᵢ $ 8) (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = true
 * )(
 *   H9 : forall (tid0 : tid) (opr : int32),
 *        Some (v'52, $ 0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = Some (tid0, opr) ->
 *        Int.ltu (x >>ᵢ $ 8) opr = true /\ Int.unsigned opr < 64
 * )(
 *   backup : RLH_ECBData_P (DMutex (Vint32 x) (Vptr (v'52, $ 0)))
 *              (absmutexsem (x >>ᵢ $ 8)
 *                 (Some (v'52, $ 0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), w)
 * )(
 *   H53 : nth_val (Z.to_nat (Int.unsigned (x >>ᵢ $ 8))) v'30 = Some x0
 * )(
 *   H77 : 0 <= Int.unsigned (x >>ᵢ $ 8)
 * )(
 *   H85 : Int.unsigned (x >>ᵢ $ 8) < 64
 * )(
 *   H43 : Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3) <= 255
 * )(
 *   H45 : Int.unsigned ($ 1<<ᵢ((x >>ᵢ $ 8) >>ᵢ $ 3)) <= 255
 * )(
 *   H44 : Int.unsigned ($ 1<<ᵢ((x >>ᵢ $ 8)&ᵢ$ 7)) <= 255
 * )(
 *   H42 : Int.unsigned ((x >>ᵢ $ 8)&ᵢ$ 7) <= 255
 * )(
 *   H70 : TcbJoin (v'52, Int.zero) (x >>ᵢ $ 8, t, m) x10 v'45
 * )(
 *   H41 : Int.unsigned (x >>ᵢ $ 8) <= 255
 * )(
 *   H28 : Int.ltu (x >>ᵢ $ 8) (x >>ᵢ $ 8) = false
 * )(
 *   H73 : R_TCB_Status_P
 *           (x7
 *            :: v'24
 *               :: x15
 *                  :: m
 *                     :: Vint32 i6
 *                        :: Vint32 x14
 *                           :: Vint32 (x >>ᵢ $ 8)
 *                              :: Vint32 ((x >>ᵢ $ 8)&ᵢ$ 7)
 *                                 :: Vint32 ((x >>ᵢ $ 8) >>ᵢ $ 3)
 *                                    :: Vint32 ($ 1<<ᵢ((x >>ᵢ $ 8)&ᵢ$ 7))
 *                                       :: Vint32 ($ 1<<ᵢ((x >>ᵢ $ 8) >>ᵢ $ 3))
 *                                          :: nil) v'36 
 *           (x >>ᵢ $ 8, t, m)
 * )(
 *   backup2 : TCBList_P (Vptr (v'52, Int.zero))
 *               ((x7
 *                 :: v'24
 *                    :: x15
 *                       :: m
 *                          :: Vint32 i6
 *                             :: Vint32 x14
 *                                :: Vint32 (x >>ᵢ $ 8)
 *                                   :: Vint32 ((x >>ᵢ $ 8)&ᵢ$ 7)
 *                                      :: Vint32 ((x >>ᵢ $ 8) >>ᵢ $ 3)
 *                                         :: Vint32 ($ 1<<ᵢ((x >>ᵢ $ 8)&ᵢ$ 7))
 *                                            :: Vint32
 *                                                 ($ 1<<ᵢ((x >>ᵢ $ 8) >>ᵢ $ 3))
 *                                               :: nil) :: v'35) v'36 v'45
 * )(
 *   r1 : Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3) < 8
 * )(
 *   r4 : Int.unsigned ((x >>ᵢ $ 8)&ᵢ$ 7) < 8
 * )(
 *   r5 : Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3) < 8
 * )(
 *   r6 : Int.unsigned ((x >>ᵢ $ 8)&ᵢ$ 7) < 8
 * )(
 *   rr1 : (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3)) < length v'36)%nat
 * )(
 *   rr4 : (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8)&ᵢ$ 7)) < length v'36)%nat
 * )(
 *   rr5 : (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3)) < length v'36)%nat
 * )(
 *   rr6 : (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8)&ᵢ$ 7)) < length v'36)%nat
 * )(
 *   rrr1 : Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3) < Z.of_nat (length v'36)
 * )(
 *   rrr4 : Int.unsigned ((x >>ᵢ $ 8)&ᵢ$ 7) < Z.of_nat (length v'36)
 * )(
 *   rrr5 : Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3) < Z.of_nat (length v'36)
 * )(
 *   rrr6 : Int.unsigned ((x >>ᵢ $ 8)&ᵢ$ 7) < Z.of_nat (length v'36)
 * )(
 *   aa aa3 : rule_type_val_match Int8u
 *           (nth_val' (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3))) v'36) =
 *         true
 * )(
 *   H88 : nth_val' (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3))) v'36 =
 *         Vint32 x16
 * )(
 *   H86 : nth_val' (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3))) v'36 =
 *         Vint32 x12
 * )(
 *   H92 : Int.unsigned (x >>ᵢ $ 8) < Int.unsigned ($ Byte.modulus)
 * )(
 *   H94 : val_inj
 *           (if Int.eq (x >>ᵢ $ 8) (x >>ᵢ $ 8)
 *            then Some (Vint32 Int.one)
 *            else Some (Vint32 Int.zero)) <> Vnull
 * )(
 *   H95 : val_inj
 *           (if Int.eq (x >>ᵢ $ 8) (x >>ᵢ $ 8)
 *            then Some (Vint32 Int.one)
 *            else Some (Vint32 Int.zero)) <> Vundef
 * )(
 *   H96 : array_type_vallist_match Int8u
 *           (update_nth_val (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3)))
 *              v'36 (Vint32 (x12&ᵢInt.not ($ 1<<ᵢ((x >>ᵢ $ 8)&ᵢ$ 7)))))
 * )(
 *   H97 : (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)) <
 *          length
 *            (update_nth_val (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3)))
 *               v'36 (Vint32 (x12&ᵢInt.not ($ 1<<ᵢ((x >>ᵢ $ 8)&ᵢ$ 7))))))%nat
 * )(
 *   t2 : nth_val'
 *          (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
 *          (update_nth_val (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3))) v'36
 *             (Vint32 (x12&ᵢInt.not ($ 1<<ᵢ((x >>ᵢ $ 8)&ᵢ$ 7))))) = 
 *        Vint32 t1
 * )(
 *   H98 : (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3)) <
 *          length
 *            (update_nth_val (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3)))
 *               v'36 (Vint32 (x12&ᵢInt.not ($ 1<<ᵢ((x >>ᵢ $ 8)&ᵢ$ 7))))))%nat
 * )(
 *   t12 : nth_val' (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3)))
 *           (update_nth_val (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3)))
 *              v'36 (Vint32 (x12&ᵢInt.not ($ 1<<ᵢ((x >>ᵢ $ 8)&ᵢ$ 7))))) =
 *         Vint32 t11
 * )(
 *   v'34 : val
 * )(
 *   v'41 : addrval
 * )(
 *   v'59 : val
 * )(
 *   v'60 v'61 : int32
 * )(
 *   v'62 : vallist
 * )(
 *   v'69 v'71 : val
 * )(
 *   v'75 v'76 v'77 v'78 v'79 : int32
 * )(
 *   v'82 v'83 v'84 v'85 v'86 : val
 * )(
 *   v'87 : int32
 * )(
 *   v'88 v'89 v'90 v'91 v'92 : val
 * )(
 *   v'93 : block
 * )(
 *   v'94 : int32
 * )(
 *   H146 : (v'93, Int.zero) <> v'41
 * )(
 *   H113 : nth_val' (Z.to_nat (Int.unsigned v'60)) OSUnMapVallist = Vint32 v'76
 * )(
 *   H114 : nth_val' (Z.to_nat (Int.unsigned v'76)) v'62 = Vint32 v'77
 * )(
 *   H115 : nth_val' (Z.to_nat (Int.unsigned v'77)) OSUnMapVallist = Vint32 v'75
 * )(
 *   H116 : nth_val' (Z.to_nat (Int.unsigned v'76)) OSMapVallist = Vint32 v'79
 * )(
 *   H117 : nth_val' (Z.to_nat (Int.unsigned v'75)) OSMapVallist = Vint32 v'78
 * )(
 *   i0 : int32
 * )(
 *   H123 : Int.unsigned i0 <= 255
 * )(
 *   H124 : RL_Tbl_Grp_P v'62 (Vint32 v'60)
 * )(
 *   H125 : array_type_vallist_match Int8u v'62
 * )(
 *   v'95 : addrval
 * )(
 *   v'97 : block
 * )(
 *   H137 : array_type_vallist_match Int8u
 *            (update_nth_val (Z.to_nat (Int.unsigned v'76)) v'62
 *               (Vint32 (v'77&ᵢInt.not v'78)))
 * )(
 *   H141 : length
 *            (update_nth_val (Z.to_nat (Int.unsigned v'76)) v'62
 *               (Vint32 (v'77&ᵢInt.not v'78))) = ∘ OS_EVENT_TBL_SIZE
 * )(
 *   H2 : ECBList_P v'42 (Vptr (v'97, Int.zero)) v'25 v'27 v'47 v'39
 * )(
 *   H14 : id_addrval' (Vptr (v'97, Int.zero)) OSEventTbl OS_EVENT = Some v'23
 * )(
 *   H6 : EcbMod.joinsig (v'97, Int.zero)
 *          (absmutexsem (x >>ᵢ $ 8)
 *             (Some (v'52, $ 0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), w) v'48 v'49
 * )(
 *   H138 : id_addrval' (Vptr (v'97, Int.zero)) OSEventTbl OS_EVENT = Some v'95
 * )(
 *   H49 : RL_RTbl_PrioTbl_P v'36 v'30 v'41
 * )(
 *   H50 : R_PrioTbl_P v'30 v'39 v'41
 * )(
 *   H52 : nth_val (Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) v'30 =
 *         Some (Vptr v'41)
 * )(
 *   H93 : array_type_vallist_match OS_TCB ∗
 *           (update_nth_val (Z.to_nat (Int.unsigned (x >>ᵢ $ 8)))
 *              (update_nth_val
 *                 (Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) v'30
 *                 (Vptr (v'52, Int.zero))) (Vptr v'41))
 * )(
 *   H104 : length
 *            (update_nth_val (Z.to_nat (Int.unsigned (x >>ᵢ $ 8)))
 *               (update_nth_val
 *                  (Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) v'30
 *                  (Vptr (v'52, Int.zero))) (Vptr v'41)) = 64%nat
 * )(
 *   H102 : RL_RTbl_PrioTbl_P
 *            (update_nth_val
 *               (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
 *               (update_nth_val (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3)))
 *                  v'36 (Vint32 (x12&ᵢInt.not ($ 1<<ᵢ((x >>ᵢ $ 8)&ᵢ$ 7)))))
 *               (val_inj (or (Vint32 t1) (Vint32 x11))))
 *            (update_nth_val (Z.to_nat (Int.unsigned (x >>ᵢ $ 8)))
 *               (update_nth_val
 *                  (Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) v'30
 *                  (Vptr (v'52, Int.zero))) (Vptr v'41)) v'41
 * )(
 *   H103 : R_PrioTbl_P
 *            (update_nth_val (Z.to_nat (Int.unsigned (x >>ᵢ $ 8)))
 *               (update_nth_val
 *                  (Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) v'30
 *                  (Vptr (v'52, Int.zero))) (Vptr v'41))
 *            (TcbMod.set v'39 (v'52, Int.zero)
 *               (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8, t, m)) v'41
 * )(
 *   H31 : v'69 <> Vnull
 * )(
 *   H33 : TCBList_P v'69 v'33 v'36 v'43
 * )(
 *   H107 : nth_val' (Z.to_nat (Int.unsigned ((v'76<<ᵢ$ 3) +ᵢ  v'75)))
 *            (update_nth_val (Z.to_nat (Int.unsigned (x >>ᵢ $ 8)))
 *               (update_nth_val
 *                  (Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) v'30
 *                  (Vptr (v'52, Int.zero))) (Vptr v'41)) =
 *          Vptr (v'93, Int.zero)
 * )(
 *   H130 : array_type_vallist_match OS_TCB ∗
 *            (update_nth_val (Z.to_nat (Int.unsigned (x >>ᵢ $ 8)))
 *               (update_nth_val
 *                  (Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) v'30
 *                  (Vptr (v'52, Int.zero))) (Vptr v'41))
 * )(
 *   H143 : length
 *            (update_nth_val (Z.to_nat (Int.unsigned (x >>ᵢ $ 8)))
 *               (update_nth_val
 *                  (Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) v'30
 *                  (Vptr (v'52, Int.zero))) (Vptr v'41)) = 64%nat
 * )(
 *   H105 : nth_val' (Z.to_nat (Int.unsigned v'76))
 *            (update_nth_val
 *               (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
 *               (update_nth_val (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3)))
 *                  v'36 (Vint32 (x12&ᵢInt.not ($ 1<<ᵢ((x >>ᵢ $ 8)&ᵢ$ 7)))))
 *               (Vint32 (Int.or t1 x11))) = Vint32 v'94
 * )(
 *   H145 : prio_in_tbl ($ OS_IDLE_PRIO)
 *            (update_nth_val
 *               (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
 *               (update_nth_val (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3)))
 *                  v'36 (Vint32 (x12&ᵢInt.not ($ 1<<ᵢ((x >>ᵢ $ 8)&ᵢ$ 7)))))
 *               (Vint32 (Int.or t1 x11)))
 * )(
 *   H122 : array_type_vallist_match Int8u
 *            (update_nth_val
 *               (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
 *               (update_nth_val (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3)))
 *                  v'36 (Vint32 (x12&ᵢInt.not ($ 1<<ᵢ((x >>ᵢ $ 8)&ᵢ$ 7)))))
 *               (Vint32 (Int.or t1 x11)))
 * )(
 *   H144 : length
 *            (update_nth_val
 *               (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
 *               (update_nth_val (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3)))
 *                  v'36 (Vint32 (x12&ᵢInt.not ($ 1<<ᵢ((x >>ᵢ $ 8)&ᵢ$ 7)))))
 *               (Vint32 (Int.or t1 x11))) = ∘ OS_RDY_TBL_SIZE
 * )(
 *   H121 : RL_Tbl_Grp_P
 *            (update_nth_val
 *               (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
 *               (update_nth_val (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3)))
 *                  v'36 (Vint32 (x12&ᵢInt.not ($ 1<<ᵢ((x >>ᵢ $ 8)&ᵢ$ 7)))))
 *               (Vint32 (Int.or t1 x11))) (Vint32 i0)
 * )(
 *   H131 : RL_RTbl_PrioTbl_P
 *            (update_nth_val (Z.to_nat (Int.unsigned v'76))
 *               (update_nth_val
 *                  (Z.to_nat
 *                     (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
 *                  (update_nth_val
 *                     (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3))) v'36
 *                     (Vint32 (x12&ᵢInt.not ($ 1<<ᵢ((x >>ᵢ $ 8)&ᵢ$ 7)))))
 *                  (Vint32 (Int.or t1 x11))) (Vint32 (Int.or v'94 v'78)))
 *            (update_nth_val (Z.to_nat (Int.unsigned (x >>ᵢ $ 8)))
 *               (update_nth_val
 *                  (Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) v'30
 *                  (Vptr (v'52, Int.zero))) (Vptr v'41)) v'41
 * )(
 *   H11 : array_type_vallist_match Int8u v'62
 * )(
 *   H19 : length v'62 = ∘ OS_EVENT_TBL_SIZE
 * )(
 *   fffbb2 : (Z.to_nat (Int.unsigned x2) < length v'62)%nat
 * )(
 *   H19'' : length v'62 = Z.to_nat 8
 * )(
 *   H63 : nth_val' (Z.to_nat (Int.unsigned x2)) v'62 = Vint32 x4
 * )(
 *   H112 : rel_edata_tcbstat (DMutex (Vint32 x) (Vptr (v'52, $ 0))) v'87
 * )(
 *   H132 : R_PrioTbl_P
 *            (update_nth_val (Z.to_nat (Int.unsigned (x >>ᵢ $ 8)))
 *               (update_nth_val
 *                  (Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) v'30
 *                  (Vptr (v'52, Int.zero))) (Vptr v'41))
 *            (TcbMod.set v'39 (v'52, Int.zero)
 *               (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8, t, m)) v'41
 * )(
 *   H108 : tcblist_get (Vptr (v'93, Int.zero)) v'69
 *            (v'33 ++
 *             (x7
 *              :: v'24
 *                 :: x15
 *                    :: m
 *                       :: Vint32 i6
 *                          :: Vint32 x14
 *                             :: Vint32 (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)
 *                                :: Vint32 ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)
 *                                   :: Vint32
 *                                        ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)
 *                                      :: Vint32 x11 :: Vint32 x8 :: nil)
 *             :: v'35) =
 *          Some
 *            (v'82
 *             :: v'83
 *                :: v'84
 *                   :: v'85
 *                      :: v'86
 *                         :: Vint32 v'87
 *                            :: v'88 :: v'89 :: v'90 :: v'91 :: v'92 :: nil)
 * )(
 *   H129 : ptr_in_tcblist (Vptr (v'52, Int.zero)) v'69
 *            (set_node (Vptr (v'93, Int.zero))
 *               (v'82
 *                :: v'83
 *                   :: Vnull
 *                      :: Vptr (v'97, Int.zero)
 *                         :: Vint32 Int.zero
 *                            :: Vint32 (v'87&ᵢInt.not ($ OS_STAT_MUTEX))
 *                               :: v'88 :: v'89 :: v'90 :: v'91 :: v'92 :: nil)
 *               v'69
 *               (v'33 ++
 *                (x7
 *                 :: v'24
 *                    :: x15
 *                       :: m
 *                          :: Vint32 i6
 *                             :: Vint32 x14
 *                                :: Vint32 (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)
 *                                   :: Vint32
 *                                        ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)
 *                                      :: Vint32
 *                                           ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ
 *                                            $ 3)
 *                                         :: Vint32 x11 :: Vint32 x8 :: nil)
 *                :: v'35))
 * )(
 *   H134 : TCBList_P v'69
 *            (v'33 ++
 *             (x7
 *              :: v'24
 *                 :: x15
 *                    :: m
 *                       :: Vint32 i6
 *                          :: Vint32 x14
 *                             :: Vint32 (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)
 *                                :: Vint32 ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)
 *                                   :: Vint32
 *                                        ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)
 *                                      :: Vint32 x11 :: Vint32 x8 :: nil)
 *             :: v'35)
 *            (update_nth_val
 *               (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
 *               (update_nth_val (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3)))
 *                  v'36 (Vint32 (x12&ᵢInt.not ($ 1<<ᵢ((x >>ᵢ $ 8)&ᵢ$ 7)))))
 *               (Vint32 (Int.or t1 x11)))
 *            (TcbMod.set v'39 (v'52, Int.zero)
 *               (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8, t, m))
 * )(
 *   H21 : Int.unsigned v'60 <= 255
 * )(
 *   fffa : length OSUnMapVallist = 256%nat ->
 *          (Z.to_nat (Int.unsigned v'60) < 256)%nat ->
 *          exists x,
 *          Vint32 x2 = Vint32 x /\ true = rule_type_val_match Int8u (Vint32 x)
 * )(
 *   H60 : (Z.to_nat (Int.unsigned v'60) < 256)%nat
 * )(
 *   H61 : nth_val' (Z.to_nat (Int.unsigned v'60)) OSUnMapVallist = Vint32 x2
 * )(
 *   H99 : val_inj
 *           (notint
 *              (val_inj
 *                 (if Int.eq v'60 ($ 0)
 *                  then Some (Vint32 Int.one)
 *                  else Some (Vint32 Int.zero)))) <> 
 *         Vint32 Int.zero
 * )(
 *   H100 : val_inj
 *            (notint
 *               (val_inj
 *                  (if Int.eq v'60 ($ 0)
 *                   then Some (Vint32 Int.one)
 *                   else Some (Vint32 Int.zero)))) <> Vnull
 * )(
 *   H101 : val_inj
 *            (notint
 *               (val_inj
 *                  (if Int.eq v'60 ($ 0)
 *                   then Some (Vint32 Int.one)
 *                   else Some (Vint32 Int.zero)))) <> Vundef
 * )(
 *   H68 : v'60 = $ 0 \/
 *         Int.ltu ((x2<<ᵢ$ 3) +ᵢ  x5) (x >>ᵢ $ 8) = false /\
 *         (x2<<ᵢ$ 3) +ᵢ  x5 <> x >>ᵢ $ 8
 * )(
 *   H142 : struct_type_vallist_match OS_EVENT
 *            (update_nth_val 1
 *               (V$ OS_EVENT_TYPE_MUTEX
 *                :: Vint32 v'60
 *                   :: Vint32 x :: Vptr (v'52, $ 0) :: x3 :: v'46 :: nil)
 *               (Vint32 v'61))
 * )(
 *   H18 : RL_Tbl_Grp_P v'62 (Vint32 v'60)
 * )(
 *   H1 : ECBList_P v'42 Vnull
 *          (v'25 ++
 *           ((V$ OS_EVENT_TYPE_MUTEX
 *             :: Vint32 v'60
 *                :: Vint32 x :: Vptr (v'52, $ 0) :: x3 :: v'46 :: nil, v'62)
 *            :: nil) ++ v'26)
 *          (v'27 ++ (DMutex (Vint32 x) (Vptr (v'52, $ 0)) :: nil) ++ v'28) v'38
 *          v'39
 * )(
 *   H5 : R_ECB_ETbl_P (v'97, Int.zero)
 *          (V$ OS_EVENT_TYPE_MUTEX
 *           :: Vint32 v'60 :: Vint32 x :: Vptr (v'52, $ 0) :: x3 :: v'46 :: nil,
 *          v'62) v'39
 * )(
 *   H133 : R_ECB_ETbl_P (v'97, Int.zero)
 *            (V$ OS_EVENT_TYPE_MUTEX
 *             :: Vint32 v'60
 *                :: Vint32 x :: Vptr (v'52, $ 0) :: x3 :: v'46 :: nil, v'62)
 *            (TcbMod.set v'39 (v'52, Int.zero)
 *               (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8, t, m))
 * )(
 *   H140 : RL_Tbl_Grp_P
 *            (update_nth_val (Z.to_nat (Int.unsigned v'76)) v'62
 *               (Vint32 (v'77&ᵢInt.not v'78))) (Vint32 v'61)
 *        )
 * (struct_type_vallist_match_condition : struct_type_vallist_match OS_TCB_flag
 *            (v'82
 *             :: v'83
 *                :: v'84
 *                   :: v'85
 *                      :: v'86
 *                         :: Vint32 v'87
 *                            :: v'88 :: v'89 :: v'90 :: v'91 :: v'92 :: nil))
 * ,
 *    {|OS_spec, GetHPrio, OSLInv, I,
 *    fun v : option val =>
 *    ( <|| END v ||>  **
 *     p_local OSLInv (v'52, Int.zero) init_lg **
 *     ((EX v0 : val, LV pevent @ OS_EVENT ∗ |-> v0) **
 *      (EX v0 : val, LV os_code_defs.x @ Int8u |-> v0) **
 *      (EX v0 : val, LV pip @ Int8u |-> v0) **
 *      (EX v0 : val, LV prio @ Int8u |-> v0) **
 *      (EX v0 : val, LV legal @ Int8u |-> v0) ** Aemp) **
 *     Aie true ** Ais nil ** Acs nil ** Aisr empisr) **
 *    A_dom_lenv
 *      ((pevent, OS_EVENT ∗)
 *       :: (os_code_defs.x, Int8u)
 *          :: (pip, Int8u) :: (prio, Int8u) :: (legal, Int8u) :: nil), Afalse|}
 *    |- (v'52, Int.zero)
 *    {{ <|| mutexpost (Vptr (v'97, Int.zero) :: nil) ||>  **
 *      LV pevent @ OS_EVENT ∗ |-> Vptr (v'97, Int.zero) **
 *      Astruct (v'97, Int.zero) OS_EVENT
 *        (V$ OS_EVENT_TYPE_MUTEX
 *         :: Vint32 v'61
 *            :: Vint32 (x&ᵢ$ OS_MUTEX_KEEP_UPPER_8)
 *               :: Vptr (v'52, $ 0) :: x3 :: v'46 :: nil) **
 *      Aarray v'95 (Tarray Int8u ∘ OS_EVENT_TBL_SIZE)
 *        (update_nth_val (Z.to_nat (Int.unsigned v'76)) v'62
 *           (Vint32 (v'77&ᵢInt.not v'78))) **
 *      p_local OSLInv (v'52, Int.zero) init_lg **
 *      Aie false **
 *      Ais nil **
 *      Acs (true :: nil) **
 *      Aisr empisr **
 *      A_isr_is_prop **
 *      AEventData
 *        (update_nth_val 1
 *           (V$ OS_EVENT_TYPE_MUTEX
 *            :: Vint32 v'60
 *               :: Vint32 x :: Vptr (v'52, $ 0) :: x3 :: v'46 :: nil)
 *           (Vint32 v'61)) (DMutex (Vint32 x) (Vptr (v'52, $ 0))) **
 *      AOSUnMapTbl **
 *      AOSMapTbl **
 *      AOSRdyTblGrp
 *        (update_nth_val (Z.to_nat (Int.unsigned v'76))
 *           (update_nth_val
 *              (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
 *              (update_nth_val (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3)))
 *                 v'36 (Vint32 (x12&ᵢInt.not ($ 1<<ᵢ((x >>ᵢ $ 8)&ᵢ$ 7)))))
 *              (Vint32 (Int.or t1 x11))) (Vint32 (Int.or v'94 v'78))) v'59 **
 *      GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64)
 *        (update_nth_val (Z.to_nat (Int.unsigned (x >>ᵢ $ 8)))
 *           (update_nth_val
 *              (Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) v'30
 *              (Vptr (v'52, Int.zero))) (Vptr v'41)) **
 *      tcbdllseg v'69 Vnull v'71 Vnull
 *        (set_node (Vptr (v'93, Int.zero))
 *           (v'82
 *            :: v'83
 *               :: Vnull
 *                  :: Vptr (v'97, Int.zero)
 *                     :: Vint32 Int.zero
 *                        :: Vint32 (v'87&ᵢInt.not ($ OS_STAT_MUTEX))
 *                           :: v'88 :: v'89 :: v'90 :: v'91 :: v'92 :: nil)
 *           v'69
 *           (v'33 ++
 *            (x7
 *             :: v'24
 *                :: x15
 *                   :: m
 *                      :: Vint32 i6
 *                         :: Vint32 x14
 *                            :: Vint32 (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)
 *                               :: Vint32 ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)
 *                                  :: Vint32
 *                                       ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)
 *                                     :: Vint32 x11 :: Vint32 x8 :: nil)
 *            :: v'35)) **
 *      LV prio @ Int8u |-> Vint32 ((v'76<<ᵢ$ 3) +ᵢ  v'75) **
 *      PV v'41 @ Int8u |-> v'34 **
 *      LV os_code_defs.x @ Int8u |-> (V$ OS_STAT_MUTEX) **
 *      LV legal @ Int8u |-> Vint32 x2 **
 *      GV OSTCBList @ OS_TCB ∗ |-> v'69 **
 *      GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (v'52, Int.zero) **
 *      LV pip @ Int8u |-> Vint32 (x >>ᵢ $ 8) **
 *      GV OSEventList @ OS_EVENT ∗ |-> v'42 **
 *      evsllseg v'42 (Vptr (v'97, Int.zero)) v'25 v'27 **
 *      evsllseg v'46 Vnull v'26 v'28 **
 *      HECBList v'38 **
 *      HTCBList v'39 **
 *      HCurTCB (v'52, Int.zero) **
 *      AOSEventFreeList v'3 **
 *      AOSQFreeList v'4 **
 *      AOSQFreeBlk v'5 **
 *      AOSIntNesting **
 *      AOSTCBFreeList v'21 v'22 **
 *      AOSTime (Vint32 v'18) **
 *      HTime v'18 **
 *      AGVars **
 *      atoy_inv' **
 *      A_dom_lenv
 *        ((pevent, OS_EVENT ∗)
 *         :: (os_code_defs.x, Int8u)
 *            :: (pip, Int8u) :: (prio, Int8u) :: (legal, Int8u) :: nil) **
 *      G& OSPlaceHolder @ Int8u == v'41 **
 *      tcbdllflag v'69
 *        (v'33 ++
 *         (x7
 *          :: v'24
 *             :: x15
 *                :: m
 *                   :: Vint32 i6
 *                      :: Vint32 x14
 *                         :: Vint32 (x >>ᵢ $ 8)
 *                            :: Vint32 ((x >>ᵢ $ 8)&ᵢ$ 7)
 *                               :: Vint32 ((x >>ᵢ $ 8) >>ᵢ $ 3)
 *                                  :: Vint32 ($ 1<<ᵢ((x >>ᵢ $ 8)&ᵢ$ 7))
 *                                     :: Vint32 ($ 1<<ᵢ((x >>ᵢ $ 8) >>ᵢ $ 3))
 *                                        :: nil) :: v'35)}} 
 *    pevent ′ → OSEventCnt =ₑ pevent ′ → OSEventCnt |ₑ prio ′;ₛ
 *    pevent ′ → OSEventPtr =ₑ OSTCBPrioTbl ′ [prio ′];ₛ
 *    EXIT_CRITICAL;ₛ
 *    OS_Sched (­);ₛ
 *                   RETURN ′ OS_NO_ERR {{Afalse}}.
 * Admitted. *)
(* eapply post3. *)


  Require Import OSMutexPostPart30.
eapply (post3 v' v'0 v'1 v'2 
  v'3 v'4 v'5 
  v'6 
  v'7 
  v'8 
  v'9 v'10 
  v'11 
  v'12 
  v'13 
  v'14 
  v'15
  v'16 
  v'17 
  v'18 
  v'19 
  v'21 
  v'22 
  v'25 v'26 
  v'27 v'28 
  v'30 
  v'33 v'35 
  v'36 
  v'38 
  v'39 
  v'42 v'46 
  v'47 v'48 v'49 
  w
  H3 
  H17 
  H12 
  H16 
  v'23 
  x3 
  H24 
  H20 
  x 
  H10 H22 
  v'24 
  v'43 v'45 
  v'52 
  H32 
  H30 
  i6 
  H39 
  H36 
  x7 
  x10 
  t 
  m 
  H72 
  H 
  H0 
  H7 
  H8 
  H23 
  H29 
  H35 
  H48 
  H4 
  H13 
  H25 
  H26 
  v'32 
  H46 
  H51 
  x0 
  H54 
  H58 
  i7 
  H55 
  H57 
  H56 
  x2 
  H59 
  H62 
  fffbb 
  x4 
  H64 
  H65 
  x5 
  H66 
  H67 
  ttfasd 
  H27 
  H38 
  x14 
  H82 
  x15 
  H84 
  H37 
  H40 
  last_condition 
  r2 
  r3 
  H34 
  H69 
  H71 
  x8 
  H74 
  H75 
  H76 
  x9 
  H78 
  H79 
  H80 
  x11 
  H81 
  H83 
  rr2 
  rr3 
  rrr2 
  rrr3 
  HH58 
  aa2 
  x16
  H91 
  x13 
  H87 
  H90 
  x12 
  H89 
  t1 
  t3 
  t11 
  t13 
  H15 
  H47 
  H9 
  backup 
  H53 
  H77 
  H85 
  H43 
  H45 
  H44 
  H42 
  H70 
  H41 
  H28 
  H73 
  backup2 
  r1 
  r4 
  r5 
  r6 
  rr1 
  rr4 
  rr5 
  rr6 
  rrr1 
  rrr4 
  rrr5 
  rrr6 
  aa
  aa3 
  H88 
  H86 
  H92 
  H94 
  H95 
  H96 
  H97 
  t2 
  H98 
  t12 
  v'34 
  v'41 
  v'59 
  v'60 v'61 
  v'62 
  v'69 v'71 
  v'75 v'76 v'77 v'78 v'79 
  v'82 v'83 v'84 v'85 v'86 
  v'87 
  v'88 v'89 v'90 v'91 v'92 
  v'93 
  v'94 
  H147 
  H113 
  H114 
  H115 
       ) with (i0 := i0); eauto.
  }

                    assert (t = rdy).
                    {
                      unfold1 TCBList_P in backup2.
                      simpljoin.
                      unfolds in H96.
                      destruct x20; destruct p; simpljoin.
                      unprotect last_condition; destruct last_condition as (ll & lll); apply eq2inteq in ll; apply eq2inteq in lll.

                      apply (low_stat_rdy_imp_high _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H54 H58 H99 H73 ll lll).
                    }
                    subst t.

                    unprotect last_condition.
                    destruct last_condition.
                    subst x14; subst i6.

                    Set Printing Depth 999.
(* ** ac:                     Show. *)
                    

                    Require Import OSMutexPost_tozh.
  eapply MutexPostNoUnliftSuccReturn; eauto.
  
Qed.
(*0*)
