Require Import ucos_include.
Require Import OSMutex_common.
Require Import os_ucos_h.
Require Import mutex_absop_rules.
Require Import sep_lemmas_ext.
Require Import symbolic_lemmas.
Require Import OSTimeDlyPure.

Require Import OSMutexPostPure.

Require Import OSQPostPure.

Require Import tcblist_setnode_lemmas.
Local Open Scope code_scope.
Local Open Scope nat_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.
Local Open Scope list_scope.



Lemma post3 :

forall (
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
  v'33 v'35 : list vallist
)(
  v'36 : vallist
)(
  v'38 : EcbMod.map
)(
  v'39 : TcbMod.map
)(
  v'42 v'46 : val
)(
  v'47 v'48 v'49 : EcbMod.map
)(
  w : waitset
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
  x3 : val
)(
  H24 : isptr v'46
)(
  H20 : Int.unsigned ($ OS_EVENT_TYPE_MUTEX) <= 255
)(
  x : int32
)(
  H10 H22 : Int.unsigned x <= 65535
)(
  v'24 : val
)(
  v'43 v'45 : TcbMod.map
)(
  v'52 : block
)(
  H32 : join v'43 v'45 v'39
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
  H29 : x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 = $ OS_MUTEX_AVAILABLE \/
        x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 <> $ OS_MUTEX_AVAILABLE
)(
  H35 : x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 <> $ OS_MUTEX_AVAILABLE
)(
  H48 : Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) < 64
)(
  H4 : Some (v'52, $ 0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = None -> w = nil
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
  v'32 : val
)(
  H46 : array_type_vallist_match OS_TCB ∗ v'30
)(
  H51 : length v'30 = 64%nat
)(
  x0 : val
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
  H59 : length OSUnMapVallist = 256%nat
)(
  H62 : true = rule_type_val_match Int8u (Vint32 x2)
)(
  fffbb : Int.unsigned x2 < 8
)(
  x4 : int32
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
  H27 : isptr x7
)(
  H38 : isptr m
)(
  x14 : int32
)(
  H82 : x14 = $ OS_STAT_RDY \/
        x14 = $ OS_STAT_SEM \/
        x14 = $ OS_STAT_Q \/ x14 = $ OS_STAT_MBOX \/ x14 = $ OS_STAT_MUTEX
)(
  x15 : val
)(
  H84 : x14 = $ OS_STAT_RDY -> x15 = Vnull
)(
  H37 : isptr x15
)(
  H40 : Int.unsigned x14 <= 255
)(
  last_condition : ProtectWrapper (x14 = $ OS_STAT_RDY /\ i6 = $ 0)
)(
  r2 : Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7) < 8
)(
  r3 : Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3) < 8
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
  rr2 : (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)) <
         length v'36)%nat
)(
  rr3 : (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)) <
         length v'36)%nat
)(
  rrr2 : Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7) <
         Z.of_nat (length v'36)
)(
  rrr3 : Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3) <
         Z.of_nat (length v'36)
)(
  HH58 : length v'36 = Z.to_nat 8
)(
  aa2 : rule_type_val_match Int8u
          (nth_val'
             (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
             v'36) = true
)(
  x16 : int32
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
  H89 : Int.unsigned x12 <= 255
)(
  t1 : int32
)(
  t3 : Int.unsigned t1 <= 255
)(
  t11 : int32
)(
  t13 : Int.unsigned t11 <= 255
)(
  H15 : Int.unsigned (x >>ᵢ $ 8) < 64
)(
  H47 : Int.ltu (x >>ᵢ $ 8) (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = true
)(
  H9 : forall (tid0 : tid) (opr : int32),
       Some (v'52, $ 0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = Some (tid0, opr) ->
       Int.ltu (x >>ᵢ $ 8) opr = true /\ Int.unsigned opr < 64
)(
  backup : RLH_ECBData_P (DMutex (Vint32 x) (Vptr (v'52, $ 0)))
             (absmutexsem (x >>ᵢ $ 8)
                (Some (v'52, $ 0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), w)
)(
  H53 : nth_val (Z.to_nat (Int.unsigned (x >>ᵢ $ 8))) v'30 = Some x0
)(
  H77 : 0 <= Int.unsigned (x >>ᵢ $ 8)
)(
  H85 : Int.unsigned (x >>ᵢ $ 8) < 64
)(
  H43 : Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3) <= 255
)(
  H45 : Int.unsigned ($ 1<<ᵢ((x >>ᵢ $ 8) >>ᵢ $ 3)) <= 255
)(
  H44 : Int.unsigned ($ 1<<ᵢ((x >>ᵢ $ 8)&ᵢ$ 7)) <= 255
)(
  H42 : Int.unsigned ((x >>ᵢ $ 8)&ᵢ$ 7) <= 255
)(
  H70 : TcbJoin (v'52, Int.zero) (x >>ᵢ $ 8, t, m) x10 v'45
)(
  H41 : Int.unsigned (x >>ᵢ $ 8) <= 255
)(
  H28 : Int.ltu (x >>ᵢ $ 8) (x >>ᵢ $ 8) = false
)(
  H73 : R_TCB_Status_P
          (x7
           :: v'24
              :: x15
                 :: m
                    :: Vint32 i6
                       :: Vint32 x14
                          :: Vint32 (x >>ᵢ $ 8)
                             :: Vint32 ((x >>ᵢ $ 8)&ᵢ$ 7)
                                :: Vint32 ((x >>ᵢ $ 8) >>ᵢ $ 3)
                                   :: Vint32 ($ 1<<ᵢ((x >>ᵢ $ 8)&ᵢ$ 7))
                                      :: Vint32 ($ 1<<ᵢ((x >>ᵢ $ 8) >>ᵢ $ 3))
                                         :: nil) v'36 
          (x >>ᵢ $ 8, t, m)
)(
  backup2 : TCBList_P (Vptr (v'52, Int.zero))
              ((x7
                :: v'24
                   :: x15
                      :: m
                         :: Vint32 i6
                            :: Vint32 x14
                               :: Vint32 (x >>ᵢ $ 8)
                                  :: Vint32 ((x >>ᵢ $ 8)&ᵢ$ 7)
                                     :: Vint32 ((x >>ᵢ $ 8) >>ᵢ $ 3)
                                        :: Vint32 ($ 1<<ᵢ((x >>ᵢ $ 8)&ᵢ$ 7))
                                           :: Vint32
                                                ($ 1<<ᵢ((x >>ᵢ $ 8) >>ᵢ $ 3))
                                              :: nil) :: v'35) v'36 v'45
)(
  r1 : Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3) < 8
)(
  r4 : Int.unsigned ((x >>ᵢ $ 8)&ᵢ$ 7) < 8
)(
  r5 : Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3) < 8
)(
  r6 : Int.unsigned ((x >>ᵢ $ 8)&ᵢ$ 7) < 8
)(
  rr1 : (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3)) < length v'36)%nat
)(
  rr4 : (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8)&ᵢ$ 7)) < length v'36)%nat
)(
  rr5 : (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3)) < length v'36)%nat
)(
  rr6 : (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8)&ᵢ$ 7)) < length v'36)%nat
)(
  rrr1 : Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3) < Z.of_nat (length v'36)
)(
  rrr4 : Int.unsigned ((x >>ᵢ $ 8)&ᵢ$ 7) < Z.of_nat (length v'36)
)(
  rrr5 : Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3) < Z.of_nat (length v'36)
)(
  rrr6 : Int.unsigned ((x >>ᵢ $ 8)&ᵢ$ 7) < Z.of_nat (length v'36)
)(
  aa aa3 : rule_type_val_match Int8u
          (nth_val' (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3))) v'36) =
        true
)(
  H88 : nth_val' (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3))) v'36 =
        Vint32 x16
)(
  H86 : nth_val' (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3))) v'36 =
        Vint32 x12
)(
  H92 : Int.unsigned (x >>ᵢ $ 8) < Int.unsigned ($ Byte.modulus)
)(
  H94 : val_inj
          (if Int.eq (x >>ᵢ $ 8) (x >>ᵢ $ 8)
           then Some (Vint32 Int.one)
           else Some (Vint32 Int.zero)) <> Vnull
)(
  H95 : val_inj
          (if Int.eq (x >>ᵢ $ 8) (x >>ᵢ $ 8)
           then Some (Vint32 Int.one)
           else Some (Vint32 Int.zero)) <> Vundef
)(
  H96 : array_type_vallist_match Int8u
          (update_nth_val (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3)))
             v'36 (Vint32 (x12&ᵢInt.not ($ 1<<ᵢ((x >>ᵢ $ 8)&ᵢ$ 7)))))
)(
  H97 : (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)) <
         length
           (update_nth_val (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3)))
              v'36 (Vint32 (x12&ᵢInt.not ($ 1<<ᵢ((x >>ᵢ $ 8)&ᵢ$ 7))))))%nat
)(
  t2 : nth_val'
         (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
         (update_nth_val (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3))) v'36
            (Vint32 (x12&ᵢInt.not ($ 1<<ᵢ((x >>ᵢ $ 8)&ᵢ$ 7))))) = 
       Vint32 t1
)(
  H98 : (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3)) <
         length
           (update_nth_val (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3)))
              v'36 (Vint32 (x12&ᵢInt.not ($ 1<<ᵢ((x >>ᵢ $ 8)&ᵢ$ 7))))))%nat
)(
  t12 : nth_val' (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3)))
          (update_nth_val (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3)))
             v'36 (Vint32 (x12&ᵢInt.not ($ 1<<ᵢ((x >>ᵢ $ 8)&ᵢ$ 7))))) =
        Vint32 t11
)(
  v'34 : val
)(
  v'41 : addrval
)(
  v'59 : val
)(
  v'60 v'61 : int32
)(
  v'62 : vallist
)(
  v'69 v'71 : val
)(
  v'75 v'76 v'77 v'78 v'79 : int32
)(
  v'82 v'83 v'84 v'85 v'86 : val
)(
  v'87 : int32
)(
  v'88 v'89 v'90 v'91 v'92 : val
)(
  v'93 : block
)(
  v'94 : int32
)(
  H146 : (v'93, Int.zero) <> v'41
)(
  H113 : nth_val' (Z.to_nat (Int.unsigned v'60)) OSUnMapVallist = Vint32 v'76
)(
  H114 : nth_val' (Z.to_nat (Int.unsigned v'76)) v'62 = Vint32 v'77
)(
  H115 : nth_val' (Z.to_nat (Int.unsigned v'77)) OSUnMapVallist = Vint32 v'75
)(
  H116 : nth_val' (Z.to_nat (Int.unsigned v'76)) OSMapVallist = Vint32 v'79
)(
  H117 : nth_val' (Z.to_nat (Int.unsigned v'75)) OSMapVallist = Vint32 v'78
)(
  i0 : int32
)(
  H123 : Int.unsigned i0 <= 255
)(
  H124 : RL_Tbl_Grp_P v'62 (Vint32 v'60)
)(
  H125 : array_type_vallist_match Int8u v'62
)(
  v'95 : addrval
)(
  v'97 : block
)(
  H137 : array_type_vallist_match Int8u
           (update_nth_val (Z.to_nat (Int.unsigned v'76)) v'62
              (Vint32 (v'77&ᵢInt.not v'78)))
)(
  H141 : length
           (update_nth_val (Z.to_nat (Int.unsigned v'76)) v'62
              (Vint32 (v'77&ᵢInt.not v'78))) = ∘ OS_EVENT_TBL_SIZE
)(
  H2 : ECBList_P v'42 (Vptr (v'97, Int.zero)) v'25 v'27 v'47 v'39
)(
  H14 : id_addrval' (Vptr (v'97, Int.zero)) OSEventTbl OS_EVENT = Some v'23
)(
  H6 : EcbMod.joinsig (v'97, Int.zero)
         (absmutexsem (x >>ᵢ $ 8)
            (Some (v'52, $ 0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), w) v'48 v'49
)(
  H138 : id_addrval' (Vptr (v'97, Int.zero)) OSEventTbl OS_EVENT = Some v'95
)(
  H49 : RL_RTbl_PrioTbl_P v'36 v'30 v'41
)(
  H50 : R_PrioTbl_P v'30 v'39 v'41
)(
  H52 : nth_val (Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) v'30 =
        Some (Vptr v'41)
)(
  H93 : array_type_vallist_match OS_TCB ∗
          (update_nth_val (Z.to_nat (Int.unsigned (x >>ᵢ $ 8)))
             (update_nth_val
                (Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) v'30
                (Vptr (v'52, Int.zero))) (Vptr v'41))
)(
  H104 : length
           (update_nth_val (Z.to_nat (Int.unsigned (x >>ᵢ $ 8)))
              (update_nth_val
                 (Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) v'30
                 (Vptr (v'52, Int.zero))) (Vptr v'41)) = 64%nat
)(
  H102 : RL_RTbl_PrioTbl_P
           (update_nth_val
              (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
              (update_nth_val (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3)))
                 v'36 (Vint32 (x12&ᵢInt.not ($ 1<<ᵢ((x >>ᵢ $ 8)&ᵢ$ 7)))))
              (val_inj (or (Vint32 t1) (Vint32 x11))))
           (update_nth_val (Z.to_nat (Int.unsigned (x >>ᵢ $ 8)))
              (update_nth_val
                 (Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) v'30
                 (Vptr (v'52, Int.zero))) (Vptr v'41)) v'41
)(
  H103 : R_PrioTbl_P
           (update_nth_val (Z.to_nat (Int.unsigned (x >>ᵢ $ 8)))
              (update_nth_val
                 (Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) v'30
                 (Vptr (v'52, Int.zero))) (Vptr v'41))
           (TcbMod.set v'39 (v'52, Int.zero)
              (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8, t, m)) v'41
)(
  H31 : v'69 <> Vnull
)(
  H33 : TCBList_P v'69 v'33 v'36 v'43
)(
  H107 : nth_val' (Z.to_nat (Int.unsigned ((v'76<<ᵢ$ 3) +ᵢ  v'75)))
           (update_nth_val (Z.to_nat (Int.unsigned (x >>ᵢ $ 8)))
              (update_nth_val
                 (Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) v'30
                 (Vptr (v'52, Int.zero))) (Vptr v'41)) =
         Vptr (v'93, Int.zero)
)(
  H130 : array_type_vallist_match OS_TCB ∗
           (update_nth_val (Z.to_nat (Int.unsigned (x >>ᵢ $ 8)))
              (update_nth_val
                 (Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) v'30
                 (Vptr (v'52, Int.zero))) (Vptr v'41))
)(
  H143 : length
           (update_nth_val (Z.to_nat (Int.unsigned (x >>ᵢ $ 8)))
              (update_nth_val
                 (Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) v'30
                 (Vptr (v'52, Int.zero))) (Vptr v'41)) = 64%nat
)(
  H105 : nth_val' (Z.to_nat (Int.unsigned v'76))
           (update_nth_val
              (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
              (update_nth_val (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3)))
                 v'36 (Vint32 (x12&ᵢInt.not ($ 1<<ᵢ((x >>ᵢ $ 8)&ᵢ$ 7)))))
              (Vint32 (Int.or t1 x11))) = Vint32 v'94
)(
  H145 : prio_in_tbl ($ OS_IDLE_PRIO)
           (update_nth_val
              (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
              (update_nth_val (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3)))
                 v'36 (Vint32 (x12&ᵢInt.not ($ 1<<ᵢ((x >>ᵢ $ 8)&ᵢ$ 7)))))
              (Vint32 (Int.or t1 x11)))
)(
  H122 : array_type_vallist_match Int8u
           (update_nth_val
              (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
              (update_nth_val (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3)))
                 v'36 (Vint32 (x12&ᵢInt.not ($ 1<<ᵢ((x >>ᵢ $ 8)&ᵢ$ 7)))))
              (Vint32 (Int.or t1 x11)))
)(
  H144 : length
           (update_nth_val
              (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
              (update_nth_val (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3)))
                 v'36 (Vint32 (x12&ᵢInt.not ($ 1<<ᵢ((x >>ᵢ $ 8)&ᵢ$ 7)))))
              (Vint32 (Int.or t1 x11))) = ∘ OS_RDY_TBL_SIZE
)(
  H121 : RL_Tbl_Grp_P
           (update_nth_val
              (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
              (update_nth_val (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3)))
                 v'36 (Vint32 (x12&ᵢInt.not ($ 1<<ᵢ((x >>ᵢ $ 8)&ᵢ$ 7)))))
              (Vint32 (Int.or t1 x11))) (Vint32 i0)
)(
  H131 : RL_RTbl_PrioTbl_P
           (update_nth_val (Z.to_nat (Int.unsigned v'76))
              (update_nth_val
                 (Z.to_nat
                    (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
                 (update_nth_val
                    (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3))) v'36
                    (Vint32 (x12&ᵢInt.not ($ 1<<ᵢ((x >>ᵢ $ 8)&ᵢ$ 7)))))
                 (Vint32 (Int.or t1 x11))) (Vint32 (Int.or v'94 v'78)))
           (update_nth_val (Z.to_nat (Int.unsigned (x >>ᵢ $ 8)))
              (update_nth_val
                 (Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) v'30
                 (Vptr (v'52, Int.zero))) (Vptr v'41)) v'41
)(
  H11 : array_type_vallist_match Int8u v'62
)(
  H19 : length v'62 = ∘ OS_EVENT_TBL_SIZE
)(
  fffbb2 : (Z.to_nat (Int.unsigned x2) < length v'62)%nat
)(
  H19'' : length v'62 = Z.to_nat 8
)(
  H63 : nth_val' (Z.to_nat (Int.unsigned x2)) v'62 = Vint32 x4
)(
  H112 : rel_edata_tcbstat (DMutex (Vint32 x) (Vptr (v'52, $ 0))) v'87
)(
  H132 : R_PrioTbl_P
           (update_nth_val (Z.to_nat (Int.unsigned (x >>ᵢ $ 8)))
              (update_nth_val
                 (Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) v'30
                 (Vptr (v'52, Int.zero))) (Vptr v'41))
           (TcbMod.set v'39 (v'52, Int.zero)
              (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8, t, m)) v'41
)(
  H108 : tcblist_get (Vptr (v'93, Int.zero)) v'69
           (v'33 ++
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
                                     :: Vint32 x11 :: Vint32 x8 :: nil)
            :: v'35) =
         Some
           (v'82
            :: v'83
               :: v'84
                  :: v'85
                     :: v'86
                        :: Vint32 v'87
                           :: v'88 :: v'89 :: v'90 :: v'91 :: v'92 :: nil)
)(
  H129 : ptr_in_tcblist (Vptr (v'52, Int.zero)) v'69
           (set_node (Vptr (v'93, Int.zero))
              (v'82
               :: v'83
                  :: Vnull
                     :: Vptr (v'97, Int.zero)
                        :: Vint32 Int.zero
                           :: Vint32 (v'87&ᵢInt.not ($ OS_STAT_MUTEX))
                              :: v'88 :: v'89 :: v'90 :: v'91 :: v'92 :: nil)
              v'69
              (v'33 ++
               (x7
                :: v'24
                   :: x15
                      :: m
                         :: Vint32 i6
                            :: Vint32 x14
                               :: Vint32 (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)
                                  :: Vint32
                                       ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)
                                     :: Vint32
                                          ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ
                                           $ 3)
                                        :: Vint32 x11 :: Vint32 x8 :: nil)
               :: v'35))
)(
  H134 : TCBList_P v'69
           (v'33 ++
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
                                     :: Vint32 x11 :: Vint32 x8 :: nil)
            :: v'35)
           (update_nth_val
              (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
              (update_nth_val (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3)))
                 v'36 (Vint32 (x12&ᵢInt.not ($ 1<<ᵢ((x >>ᵢ $ 8)&ᵢ$ 7)))))
              (Vint32 (Int.or t1 x11)))
           (TcbMod.set v'39 (v'52, Int.zero)
              (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8, t, m))
)(
  H21 : Int.unsigned v'60 <= 255
)(
  fffa : length OSUnMapVallist = 256%nat ->
         (Z.to_nat (Int.unsigned v'60) < 256)%nat ->
         exists x,
         Vint32 x2 = Vint32 x /\ true = rule_type_val_match Int8u (Vint32 x)
)(
  H60 : (Z.to_nat (Int.unsigned v'60) < 256)%nat
)(
  H61 : nth_val' (Z.to_nat (Int.unsigned v'60)) OSUnMapVallist = Vint32 x2
)(
  H99 : val_inj
          (notint
             (val_inj
                (if Int.eq v'60 ($ 0)
                 then Some (Vint32 Int.one)
                 else Some (Vint32 Int.zero)))) <> 
        Vint32 Int.zero
)(
  H100 : val_inj
           (notint
              (val_inj
                 (if Int.eq v'60 ($ 0)
                  then Some (Vint32 Int.one)
                  else Some (Vint32 Int.zero)))) <> Vnull
)(
  H101 : val_inj
           (notint
              (val_inj
                 (if Int.eq v'60 ($ 0)
                  then Some (Vint32 Int.one)
                  else Some (Vint32 Int.zero)))) <> Vundef
)(
  H68 : v'60 = $ 0 \/
        Int.ltu ((x2<<ᵢ$ 3) +ᵢ  x5) (x >>ᵢ $ 8) = false /\
        (x2<<ᵢ$ 3) +ᵢ  x5 <> x >>ᵢ $ 8
)(
  H142 : struct_type_vallist_match OS_EVENT
           (update_nth_val 1
              (V$ OS_EVENT_TYPE_MUTEX
               :: Vint32 v'60
                  :: Vint32 x :: Vptr (v'52, $ 0) :: x3 :: v'46 :: nil)
              (Vint32 v'61))
)(
  H18 : RL_Tbl_Grp_P v'62 (Vint32 v'60)
)(
  H1 : ECBList_P v'42 Vnull
         (v'25 ++
          ((V$ OS_EVENT_TYPE_MUTEX
            :: Vint32 v'60
               :: Vint32 x :: Vptr (v'52, $ 0) :: x3 :: v'46 :: nil, v'62)
           :: nil) ++ v'26)
         (v'27 ++ (DMutex (Vint32 x) (Vptr (v'52, $ 0)) :: nil) ++ v'28) v'38
         v'39
)(
  H5 : R_ECB_ETbl_P (v'97, Int.zero)
         (V$ OS_EVENT_TYPE_MUTEX
          :: Vint32 v'60 :: Vint32 x :: Vptr (v'52, $ 0) :: x3 :: v'46 :: nil,
         v'62) v'39
)(
  H133 : R_ECB_ETbl_P (v'97, Int.zero)
           (V$ OS_EVENT_TYPE_MUTEX
            :: Vint32 v'60
               :: Vint32 x :: Vptr (v'52, $ 0) :: x3 :: v'46 :: nil, v'62)
           (TcbMod.set v'39 (v'52, Int.zero)
              (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8, t, m))
)(
  H140 : RL_Tbl_Grp_P
           (update_nth_val (Z.to_nat (Int.unsigned v'76)) v'62
              (Vint32 (v'77&ᵢInt.not v'78))) (Vint32 v'61)
       )
(struct_type_vallist_match_condition : struct_type_vallist_match OS_TCB_flag
           (v'82
            :: v'83
               :: v'84
                  :: v'85
                     :: v'86
                        :: Vint32 v'87
                           :: v'88 :: v'89 :: v'90 :: v'91 :: v'92 :: nil))
,
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
   {{ <|| mutexpost (Vptr (v'97, Int.zero) :: nil) ||>  **
     LV pevent @ OS_EVENT ∗ |-> Vptr (v'97, Int.zero) **
     Astruct (v'97, Int.zero) OS_EVENT
       (V$ OS_EVENT_TYPE_MUTEX
        :: Vint32 v'61
           :: Vint32 (x&ᵢ$ OS_MUTEX_KEEP_UPPER_8)
              :: Vptr (v'52, $ 0) :: x3 :: v'46 :: nil) **
     Aarray v'95 (Tarray Int8u ∘ OS_EVENT_TBL_SIZE)
       (update_nth_val (Z.to_nat (Int.unsigned v'76)) v'62
          (Vint32 (v'77&ᵢInt.not v'78))) **
     p_local OSLInv (v'52, Int.zero) init_lg **
     Aie false **
     Ais nil **
     Acs (true :: nil) **
     Aisr empisr **
     A_isr_is_prop **
     AEventData
       (update_nth_val 1
          (V$ OS_EVENT_TYPE_MUTEX
           :: Vint32 v'60
              :: Vint32 x :: Vptr (v'52, $ 0) :: x3 :: v'46 :: nil)
          (Vint32 v'61)) (DMutex (Vint32 x) (Vptr (v'52, $ 0))) **
     AOSUnMapTbl **
     AOSMapTbl **
     AOSRdyTblGrp
       (update_nth_val (Z.to_nat (Int.unsigned v'76))
          (update_nth_val
             (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
             (update_nth_val (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3)))
                v'36 (Vint32 (x12&ᵢInt.not ($ 1<<ᵢ((x >>ᵢ $ 8)&ᵢ$ 7)))))
             (Vint32 (Int.or t1 x11))) (Vint32 (Int.or v'94 v'78))) v'59 **
     GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64)
       (update_nth_val (Z.to_nat (Int.unsigned (x >>ᵢ $ 8)))
          (update_nth_val
             (Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) v'30
             (Vptr (v'52, Int.zero))) (Vptr v'41)) **
     tcbdllseg v'69 Vnull v'71 Vnull
       (set_node (Vptr (v'93, Int.zero))
          (v'82
           :: v'83
              :: Vnull
                 :: Vptr (v'97, Int.zero)
                    :: Vint32 Int.zero
                       :: Vint32 (v'87&ᵢInt.not ($ OS_STAT_MUTEX))
                          :: v'88 :: v'89 :: v'90 :: v'91 :: v'92 :: nil)
          v'69
          (v'33 ++
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
                                    :: Vint32 x11 :: Vint32 x8 :: nil)
           :: v'35)) **
     LV prio @ Int8u |-> Vint32 ((v'76<<ᵢ$ 3) +ᵢ  v'75) **
     PV v'41 @ Int8u |-> v'34 **
     LV os_code_defs.x @ Int8u |-> (V$ OS_STAT_MUTEX) **
     LV legal @ Int8u |-> Vint32 x2 **
     GV OSTCBList @ OS_TCB ∗ |-> v'69 **
     GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (v'52, Int.zero) **
     LV pip @ Int8u |-> Vint32 (x >>ᵢ $ 8) **
     GV OSEventList @ OS_EVENT ∗ |-> v'42 **
     evsllseg v'42 (Vptr (v'97, Int.zero)) v'25 v'27 **
     evsllseg v'46 Vnull v'26 v'28 **
     HECBList v'38 **
     HTCBList v'39 **
     HCurTCB (v'52, Int.zero) **
     AOSEventFreeList v'3 **
     AOSQFreeList v'4 **
     AOSQFreeBlk v'5 **
     AOSIntNesting **
     AOSTCBFreeList v'21 v'22 **
     AOSTime (Vint32 v'18) **
     HTime v'18 **
     AGVars **
     atoy_inv' **
     A_dom_lenv
       ((pevent, OS_EVENT ∗)
        :: (os_code_defs.x, Int8u)
           :: (pip, Int8u) :: (prio, Int8u) :: (legal, Int8u) :: nil) **
     G& OSPlaceHolder @ Int8u == v'41 **
     tcbdllflag v'69
       (v'33 ++
        (x7
         :: v'24
            :: x15
               :: m
                  :: Vint32 i6
                     :: Vint32 x14
                        :: Vint32 (x >>ᵢ $ 8)
                           :: Vint32 ((x >>ᵢ $ 8)&ᵢ$ 7)
                              :: Vint32 ((x >>ᵢ $ 8) >>ᵢ $ 3)
                                 :: Vint32 ($ 1<<ᵢ((x >>ᵢ $ 8)&ᵢ$ 7))
                                    :: Vint32 ($ 1<<ᵢ((x >>ᵢ $ 8) >>ᵢ $ 3))
                                       :: nil) :: v'35)}} 
   pevent ′ → OSEventCnt =ₑ pevent ′ → OSEventCnt |ₑ prio ′;ₛ
   pevent ′ → OSEventPtr =ₑ OSTCBPrioTbl ′ [prio ′];ₛ
   EXIT_CRITICAL;ₛ
   OS_Sched (­);ₛ
                  RETURN ′ OS_NO_ERR {{Afalse}}.
  
Proof.
  intros.
  rewrite H113 in H61.
  inversion H61.
  subst v'76.
  rewrite H114 in H63.
  inversion H63.
  subst v'77.
  rewrite H115 in H66.
  inversion H66.
  subst v'75.


  
  simpl ((update_nth_val 1
              (V$ OS_EVENT_TYPE_MUTEX
               :: Vint32 v'60
                  :: Vint32 x :: Vptr (v'52, $ 0) :: x3 :: v'46 :: nil)
              (Vint32 v'61))) in H142.
  
  hoare forward.
  (* intro; tryfalse. *)

  clear -H142; unfold OS_EVENT in *; simpl in *.
  simpljoin; splits; auto.
  math simpls.
  eapply acpt_int_lemma0.
  math simpl in H1.
  exact H1.

  math simpls.
  clear -fffbb ttfasd; mauto.
  try intro; tryfalse.

  hoare forward.

  clear -fffbb ttfasd; mauto.
  clear -fffbb ttfasd; mauto.

  rewrite update_nth_val_len_eq.
  rewrite update_nth_val_len_eq.
  rewrite H51.

  clear -fffbb ttfasd; mauto.
  
  
  
  unfolds; simpl; auto.
  rewrite H107.
  reflexivity.

  
  assert (exists vvv, v'88 = Vint32 vvv).
  {
    clear -struct_type_vallist_match_condition.
    unfolds in struct_type_vallist_match_condition.
    unfold OS_TCB_flag in struct_type_vallist_match_condition.
    simpl in struct_type_vallist_match_condition; simpljoin.
    clear -H5; destruct v'88; tryfalse; eauto.
    
  }
  simpljoin.
  lets newtmp: tcblist_get_TCBList_P_get  H134.
  eauto.
  go.
  simpljoin.

  rename x1 into newowner_prio.
  rename x6 into newowner_st.
  rename x17 into newowner_msg.


Lemma post_exwt_succ_pre_mutex_new
     : forall (v'36 v'13 : vallist) (v'12 : int32) 
         (v'32 : block) (v'15 : int32) (v'24 : block) 
         (v'35 v'0 : val) (v'8 : tid) (v'9 v'11 : EcbMod.map)
         (x : val) (x0 : maxlen) (x1 : waitset)
         (v'6 v'10 : EcbMod.map) (v'38 v'69 v'39 : int32) 
         (v'58 : block) (b : taskstatus) 
         (c :msg) (v'62 v'7 : TcbMod.map) 
         (vhold : addrval) pr o a ,
       v'12 <> Int.zero ->
       R_PrioTbl_P v'36 v'7 vhold ->
       RL_Tbl_Grp_P v'13 (Vint32 v'12) ->
       R_ECB_ETbl_P (v'32, Int.zero)
         (V$OS_EVENT_TYPE_MUTEX
          :: Vint32 v'12
             :: Vint32 v'15 :: Vptr (v'24, Int.zero) :: v'35 :: v'0 :: nil,
         v'13) v'7 ->
       RH_TCBList_ECBList_P v'11 v'7 v'8 ->
       EcbMod.join v'9 v'10 v'11 ->
       EcbMod.joinsig (v'32, Int.zero) (absmutexsem pr o , x1) v'6 v'10 ->
       Int.unsigned v'12 <= 255 ->
       array_type_vallist_match Int8u v'13 ->
       length v'13 = ∘OS_EVENT_TBL_SIZE ->
       nth_val' (Z.to_nat (Int.unsigned v'12)) OSUnMapVallist = Vint32 v'38 ->
       Int.unsigned v'38 <= 7 ->
       nth_val' (Z.to_nat (Int.unsigned v'38)) v'13 = Vint32 v'69 ->
       Int.unsigned v'69 <= 255 ->
       nth_val' (Z.to_nat (Int.unsigned v'69)) OSUnMapVallist = Vint32 v'39 ->
       Int.unsigned v'39 <= 7 ->
       nth_val' (Z.to_nat (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39))) v'36 =
       Vptr (v'58, Int.zero) ->
       TcbJoin (v'58, Int.zero) (a, b, c) v'62 v'7 ->
       a = (v'38<<ᵢ$ 3)+ᵢv'39/\ x1 <> nil /\
       (exists  b'', b = (wait (os_stat_mutexsem (v'32, Int.zero)) b'')) /\
       GetHWait v'7 x1 (v'58, Int.zero) /\
       TcbMod.get v'7 (v'58, Int.zero) = Some (a, b, c)
.
Proof.
  intros.
  lets Hs :  tcbjoin_get_a  H16.
  unfolds in H3.
  unfolds in H1.
  unfolds in H0.
  unfolds in H2.
  destruct H2.
  destruct H17 as (H17&Htype).
  unfolds in H2.
  unfolds in H17.
  lets Hg : EcbMod.join_joinsig_get H4 H5.
  clear H4 H5.
  clear H16.
  assert ( Int.unsigned v'38 < 8) as Hx by omega.
  assert (Int.unsigned v'39 < 8) as Hy by omega.
  clear H10 H12.
  lets Hrs : math_xy_prio_cons Hx Hy.
  unfold nat_of_Z in H0.
  destruct H0 as (Hpr1 & Hpr2).
  assert ((v'58, Int.zero) <> vhold) as Hnvhold.
  destruct Hpr2.
  apply H0 in Hs.
  destruct Hs;auto.
  lets Hnth : nth_val'_imp_nth_val_vptr H15.
  lets Hsd : Hpr1 Hrs Hnth.
  destruct Hsd as (st & m & Hst);auto.
  unfold get in *;simpl in *.
  rewrite Hs in Hst.
  inverts Hst.
  split.
  auto.
  assert (Int.shru ((v'38<<ᵢ$ 3)+ᵢv'39) ($ 3)= v'38).
  eapply math_shrl_3_eq; eauto.
  eapply nat_8_range_conver; eauto.
  assert ( (Z.to_nat (Int.unsigned v'38))  < length v'13)%nat.
  rewrite H8.
  simpl.
  unfold Pos.to_nat; simpl.
  clear - Hx.
  mauto.
  lets Has : array_int8u_nth_lt_len H7 H4.
  destruct Has as (i & Hnthz & Hinsa).
  rewrite H11 in Hnthz.
  inverts Hnthz.
  assert ((((v'38<<ᵢ$ 3)+ᵢv'39)&ᵢ$ 7) = v'39).
  eapply math_8range_eqy; eauto.
  eapply  nat_8_range_conver; eauto.
  apply nth_val'_imp_nth_val_int in H11.
  assert ( Vint32 v'12 = Vint32 v'12) by auto.
  lets Hzs : H1 H11 H10.
  eapply  nat_8_range_conver; eauto.
  destruct Hzs.
  lets Has : math_8_255_eq H6 H9 H.
  assert (i <> $ 0).
  assert ($ 1<<ᵢ$ Z.of_nat ∘(Int.unsigned v'38) = $ 1<<ᵢv'38).
  clear -Hx.
  mauto.
  rewrite H18 in H16.
  apply H16 in Has.
  apply ltu_eq_false in Has.
  pose (Int.eq_spec i ($0)).
  rewrite Has in y.
  auto.
  assert (PrioWaitInQ (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39)) v'13).
  unfolds.
  rewrite Int.repr_unsigned in *.
  exists ( ((v'38<<ᵢ$ 3)+ᵢv'39)&ᵢ$ 7 ).
  exists (Int.shru ((v'38<<ᵢ$ 3)+ᵢv'39) ($ 3) ).
  rewrite H0 in *.
  exists i.
  splits; eauto.
  rewrite H5.
  eapply math_8_255_eq; eauto.
  destruct H2 as (H2'&H2''&Hres&H2).
  lets Hes : H2 H19.
  unfold V_OSEventType in Hes.
  simpl nth_val in Hes.
  assert (Some (V$OS_EVENT_TYPE_MUTEX) = Some (V$OS_EVENT_TYPE_MUTEX)) by auto.
  apply Hes in H20.
  clear Hes.
  rename H20 into Hes.
  destruct Hes as (td & nn &mm & Hge).
  destruct Hpr2 as (Hpr2 & Hpr3).
  unfolds in Hpr3.
  assert (td = (v'58, Int.zero)  \/ td <> (v'58, Int.zero) ) by tauto.
  destruct H20.
  Focus 2.
  lets Hass : Hpr3 H20 Hge Hs.
  rewrite Int.repr_unsigned in *.
  tryfalse.
  rewrite Int.repr_unsigned in *.
  subst td.
    unfold get in *; simpl in *.

  rewrite Hs in Hge.
  inverts Hge.
  destruct H3 as (H3'&H3''&Hres'&H3).
  destruct H3 as (Heg1 & Heg2 & Heg3).
  lets Hrgs : Heg2 Hs.
  destruct Hrgs as (xx & z &  qw & Hem & Hin).
  unfold get in *; simpl in *.

  rewrite Hg in Hem.
  inverts Hem.



  assert (qw = nil \/ qw <> nil) by tauto.
  destruct H3.
  subst qw.
  simpl in Hin; tryfalse.
  splits; auto.
  eauto.
  unfolds.
  splits; auto.
  do 3 eexists; splits; eauto.
  intros.
  assert (EcbMod.get v'11 (v'32, Int.zero) = Some (absmutexsem xx z, qw) /\ In t' qw) .
  splits; auto.
  lets Habs : Heg1 H22.
  destruct Habs as (prio' & m' & n' & Hbs).
  do 3 eexists; splits; eauto.
  destruct H17 as (H17'&H17''&Hres''&H17).
  lets Hpro : H17 Hbs.
  destruct Hpro as (Hpro&Hss).
  clear Hss.
  unfolds in Hpro.
  destruct Hpro as (xa & xb & zz & Hran & Hxx & Hyy & Hnths & Hzz).
  subst xa xb.
  rewrite Int.repr_unsigned in *.
  lets Hat : math_highest_prio_select H13 H9 H11 Hnths  Hzz;
    try eapply int_usigned_tcb_range; try omega;
    eauto.
  assert (Vint32 v'12 = Vint32 v'12) by auto.
  lets Hzs : H1 Hnths H23.
  eapply nat_8_range_conver; eauto.
  try eapply int_usigned_tcb_range; eauto.  
  destruct Hzs.
  assert (zz = $ 0 \/ zz <> $ 0) by tauto.
  destruct H26.
  subst zz.
  rewrite Int.and_commut in Hzz.
  rewrite Int.and_zero in Hzz.
  unfold Int.one in *.
  unfold Int.zero in *.
  assert ($ 1<<ᵢ(prio'&ᵢ$ 7) <> $ 0 ).
  eapply math_prop_neq_zero2; eauto.
  tryfalse.
  assert (Int.ltu ($ 0) zz = true).
  clear - H26.
  int auto.
  assert (0<=Int.unsigned zz ).
  int auto.
  assert (Int.unsigned zz = 0).
  omega.
  rewrite <- H0 in H26.
  rewrite Int.repr_unsigned in *.
  tryfalse.
  apply H25 in H27.
  assert ($ Z.of_nat ∘(Int.unsigned (Int.shru prio' ($ 3))) = (Int.shru prio' ($ 3))).
  clear -Hran.
  mauto.
  rewrite H28 in *.
  auto.
  lets Hasss : Hpr3 H20 Hs Hbs; eauto.
  unfolds.
  rewrite zlt_true; auto.
  assert (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39) < Int.unsigned prio' \/
          Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39) = Int.unsigned prio').
  omega.
  destruct H23; auto; tryfalse.
  false.
  apply Hasss.
  apply unsigned_inj; eauto.
Qed.



assert ( newowner_prio = ((x2<<ᵢ$ 3)+ᵢx5) /\
           w<>nil /\
           (exists  b'', newowner_st = (wait (os_stat_mutexsem (v'97, Int.zero)) b'')) /\
           GetHWait (TcbMod.set v'39 (v'52, Int.zero) (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8, t, m)) w (v'93,Int.zero) /\
           TcbMod.get (TcbMod.set v'39 (v'52, Int.zero) (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8, t, m)) (v'93,Int.zero) = Some (newowner_prio,newowner_st,newowner_msg)).

lets wzsrlgl: H61.
apply get_join in wzsrlgl.
destruct wzsrlgl as (wzs & rlgl).
  {
  eapply  post_exwt_succ_pre_mutex_new.
  eauto.
  eauto.
  eauto.
  4:exact H133.
  10: assumption.
  10: clear -fffbb; omega.
  10: eauto.
  3:go.
  7:assumption.
  7:assumption.
  7:assumption.
  7:assumption.
  6:assumption.
  6: clear -ttfasd; omega.
  6:exact H107.
  2:go.
  4: exact H6.

  Focus 2.
  instantiate ( 1:=  (v'52, Int.zero)).
  unfold1 TCBList_P in backup2.
  simpljoin.
  unfolds in t0.
  destruct x18; destruct p; simpljoin.
  unprotect last_condition; destruct last_condition as (ll & lll); apply eq2inteq in ll; apply eq2inteq in lll.
  assert (t=rdy).
  apply (low_stat_rdy_imp_high _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H54 H58 r H73 ll lll).
  subst t.
  eapply return_rh_tcbl_ecbl_p; eauto.
  2:eauto.
  {
    clear -H99.
    remember (Int.eq v'60 ($ 0)) as b; destruct b; intro; subst; int auto.
   }

  exact rlgl.

  }
  

  hoare abscsq.
  apply noabs_oslinv.

  (* mutex absop rules *)

  eapply absinfer_mutexpost_return_exwt_succ. 
  go.
  unfold get; simpl.
  go.
  simpljoin; go.

  assert (t=rdy).
  unprotect last_condition; destruct last_condition as (ll & lll); apply eq2inteq in ll; apply eq2inteq in lll.

  unfold1 TCBList_P in backup2.
  simpljoin.
  unfolds in H120.

  destruct x18; destruct p; simpljoin.
  apply (OSTimeDlyPure.low_stat_rdy_imp_high _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H54 H58 H120 H73 ll lll).
  subst t.


  eapply  return_gethwait; eauto.
  instantiate (3 := v'97).

  go.


  unfold join in H32; simpl in H32.
  unfold TcbJoin in H70; unfold join in H70; unfold sig in H70; simpl in H70.
  
  go.
  simpljoin; eauto 1.
  (*
 TcbMod.get
          (TcbMod.set v'39 (v'52, Int.zero)
             (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8, rdy, m)) 
          (v'93, Int.zero) = Some (newowner_prio, newowner_st, newowner_msg)
 (exists b' b'', newowner_st = wait (os_stat_mutexsem b') b'') 
  they cannot be same
   *)
  simpljoin.
  clear -H61.
  intro H; rewrite H in H61.
  unfold get in H61; simpl in H61.
  rewrite TcbMod.set_a_get_a in H61; tryfalse.
  go.


  unfold get ; simpl.
  unfold join in H32; simpl in H32.
  unfold TcbJoin in H70; unfold join in H70; unfold sig in H70; simpl in H70.
  
  go.

 
  unfold get ; simpl.
  unfold join in H32; simpl in H32.
  unfold TcbJoin in H70; unfold join in H70; unfold sig in H70; simpl in H70.
  
  simpljoin.
 
  rewrite TcbMod.set_a_get_a' in e1.
  go.
  (* same as before *)
  (* clear -H147; go. *)

  assert ( (v'52 , Int.zero) <> (v'93, Int.zero)).
  unfold1 TCBList_P in backup2.
  simpljoin.
  unfolds in H109.
  destruct x19; destruct p; simpljoin.
  unprotect last_condition; destruct last_condition as (ll & lll); apply eq2inteq in ll; apply eq2inteq in lll.
  assert (t=rdy).
  apply (low_stat_rdy_imp_high _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H54 H58 H118 H73 ll lll).
  subst t.

  simpljoin.
  clear -H61.
  intro H; rewrite H in H61.
  unfold get in H61; simpl in H61.
  rewrite TcbMod.set_a_get_a in H61; tryfalse.
  go.
  clear -H63.

  go.

  remember (update_nth_val (Z.to_nat (Int.unsigned x2))
          (update_nth_val
             (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
             (update_nth_val (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3)))
                v'36 (Vint32 (x12&ᵢInt.not ($ 1<<ᵢ((x >>ᵢ $ 8)&ᵢ$ 7)))))
             (Vint32 (Int.or t1 x11))) (Vint32 (Int.or v'94 v'78)))  as rdy_tbl.
  remember       (update_nth_val (Z.to_nat (Int.unsigned (x >>ᵢ $ 8)))
          (update_nth_val
             (Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) v'30
             (Vptr (v'52, Int.zero))) (Vptr v'41))(*       (update_nth_val (Z.to_nat (Int.unsigned (v'55>>ᵢ$ 8)))
                                       * (update_nth_val
                                       *    (Z.to_nat (Int.unsigned (v'55&$ OS_MUTEX_KEEP_LOWER_8)))
                                       *    v'30 (Vptr (v'52, Int.zero))) (Vptr v'51)) *) as prio_tbl.

  (* assert ( (Z.to_nat (Int.unsigned v'63)) < length rdy_tbl)%nat as fa.
   * rewrite H152.
   * clear -fffbb.
   * mauto.
   * lets aaa: array_int8u_nth_lt_len H151 fa.
   * destruct aaa as (a1 & a2 & a3). *)
  hoare lift 20%nat pre.
  simpljoin.
  lets bbb: TCBList_P_tcblist_get_TCBNode_P H108 H61.
  eauto.

  eapply backward_rule1.
  intro.
  
  eapply set_node_elim.
  2:eauto.
  2:eauto.
  2:  eauto.
  5: compute; auto.
  exact H129.
  {
    instantiate (3:=(update_nth_val (Z.to_nat (Int.unsigned x2))
              (update_nth_val
                 (Z.to_nat
                    (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
                 (update_nth_val
                    (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3))) v'36
                    (Vint32 (x12&ᵢInt.not ($ 1<<ᵢ((x >>ᵢ $ 8)&ᵢ$ 7)))))
                 (Vint32 (Int.or t1 x11))) (Vint32 (Int.or v'94 v'78)))).
   instantiate (1 := Vptr (v'97, Int.zero)).
   instantiate (1 := rdy ).

    eapply  TCBNode_P_set_rdy ; try assumption.
    clear -fffbb ttfasd; mauto.
    apply nth_val'2nth_val.
    rewrite math_shrl_3_eq.
    exact H105.
    clear -ttfasd; mauto.
    clear -fffbb; mauto.
    assert ( rule_type_val_match Int8u (nth_val' (Z.to_nat (Int.unsigned x2))
           (update_nth_val
              (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
              (update_nth_val (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3)))
                 v'36 (Vint32 (x12&ᵢInt.not ($ 1<<ᵢ((x >>ᵢ $ 8)&ᵢ$ 7)))))
              (Vint32 (Int.or t1 x11)))) = true).
    apply array_type_vallist_match_imp_rule_type_val_match.
    rewrite H144.
    clear -fffbb; mauto.
    assumption.
    rewrite H105 in H63.
    clear -H63.
    unfolds in H63.
    math simpl in H63.
    auto.
    4:exact bbb.
    unfolds in H112; subst v'87; clear.
    apply Int.and_not_self.
    rewrite math_shrl_3_eq.
    auto.
    clear -ttfasd; mauto.
    clear -fffbb; mauto.
 
    rewrite math_8range_eqy.
    2: clear -fffbb; mauto.
    2: clear -ttfasd; mauto.


    cut (Vint32 v'78 = Vint32 ($1 <<ᵢ x5)).
    clear; intro H; inverts H.
    reflexivity.
    rewrite <- H117.
    apply xmapis1shlx.
    clear -ttfasd; mauto.

    (**************************TODO************************)
    (* Lemma tcbnode_p_hold:
     *   forall v'82 v'83 v'84 v'85 v'86 v'87 x2 x5 v'89 v'90 v'91 v'92 vl  x1 x6 newowner_msg new_msg,
     *    TCBNode_P
     *       (v'82
     *        :: v'83
     *           :: v'84
     *              :: v'85
     *                 :: v'86
     *                    :: Vint32 v'87
     *                       :: Vint32 ((x2<<ᵢ$ 3) +ᵢ  x5)
     *                          :: v'89 :: v'90 :: v'91 :: v'92 :: nil)
     *       vl
     *       ((x2<<ᵢ$ 3) +ᵢ  x5, wait (os_stat_mutexsem x1) x6, newowner_msg)
     *    ->
     *     TCBNode_P
     *  (v'82
     *   :: v'83
     *      :: Vnull
     *         :: new_msg
     *            :: Vint32 Int.zero
     *               :: V$ OS_STAT_RDY
     *                  :: Vint32 ((x2<<ᵢ$ 3) +ᵢ  x5)
     *                     :: v'89 :: v'90 :: v'91 :: v'92 :: nil)
     * vl ((x2<<ᵢ$ 3) +ᵢ  x5, rdy, new_msg).
     * Proof.
     *   SearchAbout TCBNode_P.
     *   intros.
     *   unfold TCBNode_P in *.
     *   simpljoin.
     *   splits.
     *   Check set_node_elim_hoare.
     *   unfolds; simpl; auto.
     *   go.
     *   clear -H1.
     *   unfold RL_TCBblk_P in *.
     *   simpljoin.
     *   do 6 eexists.
     *   splits.
     *   go.
     *   eauto.
     *   eauto.
     *   eauto.
     *   eauto.
     *   unfolds.
     *   simpl.
     *   go.
     *   inverts H.
     *   auto.
     *   inverts H.
     *   splits; auto.
     *   eexists.
     *   splits.
     *   go.
     *   intro; auto.
     *   clear -H2.
     *   unfold R_TCB_Status_P in *.
     *   simpljoin; splits;
     *   match goal with
     *     | H: ?f _ _ _ |- ?f _ _ _ => clear -H; unfold f in *
     *   end.
     *   intros.
     *   apply H in H0.
     *   simpljoin; splits;
     *   match goal with
     *     | H: ?f _ _ _ |- ?f _ _ _ => clear -H; unfold f in *
     *   end.
     *   intros.
     *   inverts H.
     *   splits;  auto.
     *   splits;  auto.
     *   admit.
     * 
     *   simpljoin; splits;
     *   match goal with
     *     | H: ?f _ _ _ |- ?f _ _ _ => clear -H; unfold f in *
     *   end.
     *   intros.
     *   unfolds in H0.
     *   apply H in H0.
     *   inverts H.
     *   splits;  auto.
     *   splits;  auto.
     *   admit.
     * 
     * 
     *   
     *   
     * Admitted.
     * Show.
     * eapply tcbnode_p_hold; auto.
     * unfolds in H112.
     * 
     * exact bbb. *)
  
  }


  remember ((update_nth_val
        (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
        (update_nth_val (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3))) v'36
           (Vint32 (x12&ᵢInt.not ($ 1<<ᵢ((x >>ᵢ $ 8)&ᵢ$ 7)))))
        (Vint32 (Int.or t1 x11)))) as rtbl.
  {
    unfolds.
    assert((((x2<<ᵢ$ 3) +ᵢ  x5) >>ᵢ $ 3) = x2) as eq1.
    clear -fffbb ttfasd; mauto.
    rewrite eq1.
    assert((((x2<<ᵢ$ 3) +ᵢ  x5)&ᵢ$ 7) = x5) as eq2.
    clear -fffbb ttfasd; mauto.
    rewrite eq2.
    do 3 eexists.
    clear - fffbb ttfasd.
    mauto.
    splits; eauto.

                                                                     
  }

  {
    Lemma mutex_post_nodup:
      forall v'30 v'39 v'41 prio' t m v'52,
        R_PrioTbl_P v'30 v'39 v'41 ->
        nth_val (Z.to_nat (Int.unsigned prio')) v'30 = Some (Vptr v'41) ->
        R_Prio_No_Dup (TcbMod.set v'39 (v'52, Int.zero) (prio', t, m)).
    Proof.
      intros.
      unfolds in H.
      simpljoin.
      unfolds.
      intros.
      assert ( tid = (v'52, Int.zero) \/ tid <> (v'52, Int.zero)) by tauto.
      destruct H6; intros.
      subst tid.
      unfold get in *; simpl in *.
      rewrite TcbMod.set_a_get_a in H4.
      inverts H4.
      2:go.
      rewrite TcbMod.set_a_get_a' in H5.
      2:go.
      lets ff: H1 H5.
      simpljoin.
      intro.
      subst prio.
      unfold nat_of_Z in H4.
      rewrite H0 in H4.
      inverts H4.
      apply H6; auto.

      rewrite TcbMod.set_a_get_a' in H4.
      2:go.
      assert ( tid' = (v'52, Int.zero) \/ tid' <> (v'52, Int.zero)) by tauto.

      destruct H7; intros.
      subst tid'.

      unfold get in *; simpl in *.
      rewrite TcbMod.set_a_get_a in H5.
      2:go.
      inverts H5.

      lets bb: H1 H4.
      simpljoin.
      intro; subst.
      unfold nat_of_Z in H5.
      rewrite H5 in H0.
      inverts H0.
      apply H7; auto.

      unfold get in H5.
      simpl in H5.
      rewrite TcbMod.set_a_get_a' in H5; go.
      unfolds in H2.
      eapply H2.
      2:eauto.
      2:eauto.
      auto.
    Qed.

    eapply mutex_post_nodup; eauto.
    }

      
  hoare forward prim.
  unfold AECBList.
  unfold AOSMapTbl.
  unfold AOSUnMapTbl.
  unfold AOSTCBPrioTbl.
  unfold AOSTCBList.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  unfold AOSRdyGrp.
  sep pauto.


  sep cancel 1%nat 1%nat.
  sep cancel 1%nat 1%nat.
  sep cancel 6%nat 1%nat.
  sep cancel 12%nat 2%nat.
  (* sep lift 3%nat. *)
  eapply evsllseg_compose with
  (qptrl1:= v'25)
    (qptrl2:=v'26)
    (l:= (V$ OS_EVENT_TYPE_MUTEX
              :: Vint32 v'61
                 :: Vint32
                      (Int.or (x&ᵢ$ OS_MUTEX_KEEP_UPPER_8)
                         ((x2<<ᵢ$ 3) +ᵢ  x5))
                    :: nth_val' (Z.to_nat (Int.unsigned ((x2<<ᵢ$ 3) +ᵢ  x5)))
                         (update_nth_val
                            (Z.to_nat (Int.unsigned (x >>ᵢ $ 8)))
                            (update_nth_val
                               (Z.to_nat
                                  (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)))
                               v'30 (Vptr (v'52, Int.zero))) 
                            (Vptr v'41)) :: x3 :: v'46 :: nil))
       (* (V$OS_EVENT_TYPE_MUTEX
        *     ::  Vint32 (v'58&ᵢInt.not v'67)
        *     :: Vint32 (Int.or (v'55&ᵢ$ OS_MUTEX_KEEP_UPPER_8)
        *                       ((v'63<<ᵢ$ 3)+ᵢv'65))
        *     ::  nth_val'
        *     (Z.to_nat (Int.unsigned ((v'63<<ᵢ$ 3)+ᵢv'65)))
        *     (update_nth_val
        *        (Z.to_nat (Int.unsigned (v'55>>ᵢ$ 8)))
        *        (update_nth_val
        *           (Z.to_nat
        *              (Int.unsigned
        *                 (v'55&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) v'30
        *           (Vptr (v'52, Int.zero))) 
        *        (Vptr v'51)) :: v'61 :: v'57 :: nil)) *)
    (msgqls1:=v'27)
    (msgqls2 := v'28)
    (tl:=(Vptr (v'97, Int.zero)))
    (x:=(* (update_nth_val
         *       (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
         *       (update_nth_val (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3)))
         *          v'36 (Vint32 (x12&ᵢInt.not ($ 1<<ᵢ((x >>ᵢ $ 8)&ᵢ$ 7)))))
         *       (val_inj (or (Vint32 t1) (Vint32 x11)))) *)

       (update_nth_val (Z.to_nat (Int.unsigned x2)) v'62
                (Vint32 (x4&ᵢInt.not v'78))) )
    (msgq:=DMutex (Vint32 (Int.or (x &ᵢ$ OS_MUTEX_KEEP_UPPER_8)
                                  ((x2<<ᵢ$ 3)+ᵢx5)))
                  ( nth_val' (Z.to_nat (Int.unsigned ((x2<<ᵢ$ 3)+ᵢx5)))
                             (update_nth_val (Z.to_nat (Int.unsigned (x>>ᵢ$ 8)))
                                             (update_nth_val (Z.to_nat
                                                                (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) v'30
                                                             (Vptr (v'52, Int.zero))) 
                                             (Vptr v'41))) );
    auto.
  go.

  unfold AEventNode.
  unfold AEventData.

  unfold_msg.
  sep pauto.

  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  rewrite <- H106.
  (* instantiate (x7 := v'33).
   * instantiate (x9 := v'35).
   * instantiate (x8 := (x7
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
   *                                         :: Vint32 x11 :: Vint32 x8 :: nil)).
   * sep lift 3%nat. *)
  eapply tcbdllflag_hold.

  2: sep cancel tcbdllflag.
  Lemma set_node_eq_dllflag :
    forall tcbl ptr  v'82 v'83 v'84 v'85 v'86 v'87 v'88 v'89 v'90 v'91 v'92 v'83' v'84' v'85' v'86' v'87' v'88' v'89' v'90' v'91' head,
           tcblist_get ptr head tcbl = 
           Some
             (v'82 :: v'83 :: v'84 :: v'85 :: v'86 :: v'87 :: v'88
                   :: v'89 :: v'90 :: v'91 :: v'92 :: nil) ->
           eq_dllflag tcbl (set_node ptr (v'82 :: v'83' :: v'84' :: v'85' :: v'86' :: v'87' :: v'88'
                                           :: v'89' :: v'90' :: v'91' :: v'92 :: nil) head tcbl).
  Proof.
    induction tcbl.
    intros.
    simpl.
    auto.
    intros.
    simpl.
    remember (beq_val ptr head).
    destruct b.
    unfold tcblist_get in H.
    rewrite <- Heqb in H.
    simpl in H.
    inverts H.
    splits; auto.
    Focus 2.
    splits; auto.
    eapply IHtcbl.
    unfolds in H.
    rewrite <- Heqb in H.
    destruct a.
    simpl in H.
    inversion H.
    simpl in H.
    fold tcblist_get in H.
    exact H.

    apply eq_dllflag_refl.
  Qed.


  Lemma eq_dllflag_trans :
    forall l1 l2 l3,
      eq_dllflag l1 l2 ->
      eq_dllflag l2 l3 ->
      eq_dllflag l1 l3.
  Proof.
    induction l1.
    intros.
    simpl in H.
    destruct l2; tryfalse.

    simpl in H0.
    destruct l3; tryfalse.
    auto.
    intros.
    simpl in H.
    destruct l2; tryfalse.
    simpl in H0.
    destruct l3; tryfalse.
    simpl.
    simpljoin.
    splits.
    rewrite H.
    auto.
    rewrite H3.
    auto.
    eapply IHl1.
    eauto.
    eauto.
  Qed.

  eapply eq_dllflag_trans.
  2: eapply  set_node_eq_dllflag .
  eapply tcbdllflag_hold_middle.
  unfolds ; auto.
  eauto.
  eauto.

  go.
  go.
  exact H138.
  go.
  
  go.

  clear -H142 H126.

  unfolds in H142; unfold OS_EVENT in H142; simpl in H142; simpljoin.
  math simpl in H0; clear -H0 H126; omega.

  assert (Int.unsigned
            (Int.or (x&ᵢ$ OS_MUTEX_KEEP_UPPER_8) ((x2<<ᵢ$ 3) +ᵢ  x5)) <= 65535).
  apply acpt_intlemma6.

  clear -fffbb ttfasd; mauto.

  change Int16.max_unsigned with 65535 in H126.
  clear -H126 H127; omega.

  rewrite H107.
  auto.

  eapply r_priotbl_p_set_hold;eauto.

{
Lemma rl_rtbl_priotbl_p_hold''
     : forall (v'36 : vallist) (v'12 : int32) (v'13 : vallist)
         (v'38 v'69 v'39 : int32) (v'58 : block) (v'40 v'41 v'57 : int32)
         (v'37 : vallist) (vhold : block * int32) vvv,
       (v'58, Int.zero) <> vhold ->
       RL_RTbl_PrioTbl_P v'37 v'36 vhold ->
       v'12 <> Int.zero ->
       Int.unsigned v'12 <= 255 ->
       array_type_vallist_match Int8u v'13 ->
       length v'13 = ∘ OS_EVENT_TBL_SIZE ->
       array_type_vallist_match Int8u v'37 ->
       length v'37 = ∘ OS_EVENT_TBL_SIZE ->
       nth_val' (Z.to_nat (Int.unsigned v'12)) OSUnMapVallist = Vint32 v'38 ->
       Int.unsigned v'38 <= 7 ->
       nth_val' (Z.to_nat (Int.unsigned v'38)) v'13 = Vint32 v'69 ->
       Int.unsigned v'69 <= 255 ->
       nth_val' (Z.to_nat (Int.unsigned v'69)) OSUnMapVallist = Vint32 v'39 ->
       Int.unsigned v'39 <= 7 ->
       nth_val' (Z.to_nat (Int.unsigned ((v'38<<ᵢ$ 3) +ᵢ  v'39))) v'36 =
       Vptr (v'58, Int.zero) ->
       nth_val' (Z.to_nat (Int.unsigned v'39)) OSMapVallist = Vint32 v'40 ->
       Int.unsigned v'40 <= 128 ->
       nth_val' (Z.to_nat (Int.unsigned v'38)) OSMapVallist = Vint32 v'41 ->
       Int.unsigned v'41 <= 128 ->
       RL_Tbl_Grp_P v'13 (Vint32 v'12) ->
       RL_Tbl_Grp_P v'37 (Vint32 v'57) ->
       Int.unsigned v'57 <= 255 ->
       array_type_vallist_match Int8u v'37 ->
       length v'37 = ∘ OS_RDY_TBL_SIZE ->
       (nth_val' (Z.to_nat (Int.unsigned v'38)) v'37) = Vint32 vvv ->
       RL_RTbl_PrioTbl_P
         (update_nth_val (Z.to_nat (Int.unsigned v'38)) v'37
            (val_inj
               (or (Vint32 vvv)
                   (Vint32 v'40)))) v'36 vhold.
Proof.
  intros.
  
  rewrite <- H23.
  eapply rl_rtbl_priotbl_p_hold; try assumption.
  12: eauto.
  12: eauto.
  11: eauto.
  9: eauto.
  6: eauto.
  6: eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
Qed.
eapply rl_rtbl_priotbl_p_hold''; try assumption.
6: eauto 1.
7: eauto 1.
8: eauto 1.
9: eauto 1.
9: eauto 1.
10: eauto 1.
assumption.
clear -H99.
intro; subst v'60; change (Int.eq  (Int.zero)  ($ 0)) with true in H99; apply H99; auto.
assumption.
assumption.
assumption.
clear -fffbb ; mauto.
assumption.
clear -ttfasd; mauto.
3: assumption.
idtac.
3: exact H121.
3: assumption.
Lemma osmapvalle128:
  forall x y,
    nth_val' (Z.to_nat (Int.unsigned x)) OSMapVallist = Vint32 y ->
    Int.unsigned y <= 128.
Proof.
  intros.
  unfold OSMapVallist in H.
  assert (Int.unsigned x<8 \/ Int.unsigned x > 7).
  omega.
  elim H0; intros.
  mauto_dbg.
  destruct H1; [rewrite H1 in *; simpl in H; inverts H; ur_rewriter; omega| ..].
  destruct H1; [rewrite H1 in *; simpl in H; inverts H; ur_rewriter; omega| ..].
  destruct H1; [rewrite H1 in *; simpl in H; inverts H; ur_rewriter; omega| ..].
  destruct H1; [rewrite H1 in *; simpl in H; inverts H; ur_rewriter; omega| ..].
  destruct H1; [rewrite H1 in *; simpl in H; inverts H; ur_rewriter; omega| ..].
  destruct H1; [rewrite H1 in *; simpl in H; inverts H; ur_rewriter; omega| ..].
  destruct H1; [rewrite H1 in *; simpl in H; inverts H; ur_rewriter; omega| ..].
  rewrite H1 in *; simpl in H; inverts H; ur_rewriter; omega.
  remember (Int.unsigned x).
  assert ( 7 < z) by omega.
  apply Z2Nat.inj_lt in H2.
  remember (Z.to_nat z).
  change (Z.to_nat 7) with 7%nat in H2.
  destruct n; try omega.
  destruct n; try omega.
  destruct n; try omega.
  destruct n; try omega.
  destruct n; try omega.
  destruct n; try omega.
  destruct n; try omega.
  destruct n; try omega.
  induction n.
  simpl in H.
  inverts H.
  simpl in H.
  inverts H.
  omega.
  rewrite Heqz.
  int auto.
Qed.

eapply osmapvalle128; eauto.
eapply osmapvalle128; eauto.
                                                               
}


rewrite H107.
  (* H146 : struct_type_vallist_match OS_TCB_flag
   *          (v'82
   *           :: v'83
   *              :: v'84
   *                 :: v'85
   *                    :: v'86
   *                       :: Vint32 v'87
   *                          :: v'88 :: v'89 :: v'90 :: v'91 :: v'92 :: nil) *)
{

  assert (v'60 <> $ 0).
{
  clear -H99.
  intro; subst v'60; change (Int.eq  (Int.zero)  ($ 0)) with true in H99; apply H99; auto.
}

{

lets wzsrlgl: H61.
apply get_join in wzsrlgl.
destruct wzsrlgl as (wzs & rlgl).
 
eapply ecblist_p_post_exwt_hold_mutex_new; eauto.
elim H68; intros; try solve [ clear -H127 H126; subst; tryfalse].
clear -H127; simpljoin.
apply int_ltu_prop; auto.

clear -fffbb; mauto.
clear -ttfasd; mauto.
eapply osmapvalle128; eauto.


 unfold1 TCBList_P in backup2.
  simpljoin.
  unfolds in H136.
  destruct x19; destruct p; simpljoin.
  unprotect last_condition; destruct last_condition as (ll & lll); apply eq2inteq in ll; apply eq2inteq in lll.
  assert (t=rdy).
  apply (low_stat_rdy_imp_high _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H54 H58 H148 H73 ll lll).
  subst t.

  eapply return_ecbl_p; eauto.

 unfold1 TCBList_P in backup2.
  simpljoin.
  unfolds in H136.
  destruct x19; destruct p; simpljoin.
  unprotect last_condition; destruct last_condition as (ll & lll); apply eq2inteq in ll; apply eq2inteq in lll.
  assert (t=rdy).
  apply (low_stat_rdy_imp_high _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H54 H58 H148 H73 ll lll).
  subst t.

  eapply return_ecbl_p; eauto.

  }




 }
exact H119.
exact H118.
exact H111.
apply rh_curtcb_set_nct;auto.
unfolds.
do 3 eexists.
unfold get; simpl.
apply TcbMod.set_a_get_a.
go.
intro HHH; inverts HHH.

 unfold1 TCBList_P in backup2.
  simpljoin.
  idtac.
  idtac.
  unfolds in H148.
  destruct x19; destruct p; simpljoin.
  unprotect last_condition; destruct last_condition as (ll & lll); apply eq2inteq in ll; apply eq2inteq in lll.
  assert (t=rdy).
  apply (low_stat_rdy_imp_high _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H54 H58 H151 H73 ll lll).
  subst t.

  rewrite TcbMod.set_a_get_a in H110; [inverts H110| go].


  eapply rh_tcblist_ecblist_p_post_exwt_mutex ; eauto.
  
  unfold1 TCBList_P in backup2.
  simpljoin.
  unfolds in H148.
  destruct x19; destruct p; simpljoin.
  unprotect last_condition; destruct last_condition as (ll & lll); apply eq2inteq in ll; apply eq2inteq in lll.
  assert (t=rdy).
  apply (low_stat_rdy_imp_high _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H54 H58 H151 H73 ll lll).
  subst t.

  eapply return_rh_tcbl_ecbl_p; eauto.
  unfolds in H109.
  destruct H109; exact H109.

  unfold AEventData; go.
  hoare forward.
  sep cancel p_local.
  sep cancel 1%nat 5%nat.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aisr.
  eauto.

  unfolds; auto.
  go.
  unfold AEventData.
  go.


  intro; intros.
  sep normal in H63.
  sep destruct H63.
  sep eexists.
  sep cancel p_local.
  simpl; auto.

  intro; intros.
  sep normal in H63.
  sep destruct H63.
  sep eexists.
  sep cancel p_local.
  simpl; auto.

  
  unfold AEventData.
  hoare unfold.
  hoare forward.
  inverts H63; reflexivity.
Qed.
