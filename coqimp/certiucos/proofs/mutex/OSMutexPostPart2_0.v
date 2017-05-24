Require Import ucos_include.
Require Import OSMutex_common.
Require Import os_ucos_h.
Require Import mutex_absop_rules.
Require Import sep_lemmas_ext.
Require Import symbolic_lemmas.
Local Open Scope code_scope.
Local Open Scope int_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.



(* Require Import ucert.
 * Require Import os_code_defs.
 * Require Import mathlib.
 * Require Import OSMutex_common.
 * Require Import lab.
 * Open Scope code_scope. *)
(* Require Import OSMutexPostPart2_1. *)
Lemma MutexPostPart10:
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
  H21 : (Int.unsigned i <= 255)%Z
)(
  H18 : RL_Tbl_Grp_P v'44 (Vint32 i)
)(
  H24 : isptr v'46
)(
  H2 : ECBList_P v'42 (Vptr (v'29, Int.zero)) v'25 v'27 v'47 v'39
)(
  H14 : id_addrval' (Vptr (v'29, Int.zero)) OSEventTbl OS_EVENT = Some v'23
)(
  H20 : (Int.unsigned ($ OS_EVENT_TYPE_MUTEX) <= 255)%Z
)(
  x : int32
)(
  H10 : (Int.unsigned x <= 65535)%Z
)(
  H15 : (Int.unsigned (x >>ᵢ $ 8) < 64)%Z
)(
  H22 : (Int.unsigned x <= 65535)%Z
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
  H39 : (Int.unsigned i6 <= 65535)%Z
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
  H48 : (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) < 64)%Z
)(
  H6 : EcbMod.joinsig (v'29, Int.zero)
         (absmutexsem (x >>ᵢ $ 8)
            (Some (v'52, $ 0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), w) v'48 v'49
)(
  H4 : Some (v'52, $ 0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = None -> w = nil
)(
  H9 : forall (tid0 : tid) (opr : int32),
       Some (v'52, $ 0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = Some (tid0, opr) ->
       Int.ltu (x >>ᵢ $ 8) opr = true /\ (Int.unsigned opr < 64)%Z
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
  H55 : (Int.unsigned i7 <= 255)%Z
)(
  H57 : prio_in_tbl ($ OS_IDLE_PRIO) v'36
)(
  H56 : RL_Tbl_Grp_P v'36 (Vint32 i7)
)(
  x2 : int32
)(
  fffa : length OSUnMapVallist = 256%nat ->
         Z.to_nat (Int.unsigned i) < 256%nat ->
         exists x,
         Vint32 x2 = Vint32 x /\ true = rule_type_val_match Int8u (Vint32 x)
)(
  H59 : length OSUnMapVallist = 256
)(
  H60 : Z.to_nat (Int.unsigned i) < 256
)(
  H61 : nth_val' (Z.to_nat (Int.unsigned i)) OSUnMapVallist = Vint32 x2
)(
  H62 : true = rule_type_val_match Int8u (Vint32 x2)
)(
  fffbb : (Int.unsigned x2 < 8)%Z
)(
  fffbb2 : Z.to_nat (Int.unsigned x2) < length v'44
)(
  H19'' : length v'44 = Z.to_nat 8
)(
  x4 : int32
)(
  H63 : nth_val' (Z.to_nat (Int.unsigned x2)) v'44 = Vint32 x4
)(
  H64 : (Int.unsigned x4 <= 255)%Z
)(
  H65 : Z.to_nat (Int.unsigned x4) < length OSUnMapVallist
)(
  x5 : int32
)(
  H66 : nth_val' (Z.to_nat (Int.unsigned x4)) OSUnMapVallist = Vint32 x5
)(
  H67 : (Int.unsigned x5 <= 255)%Z
)(
  ttfasd : (Int.unsigned x5 < 8)%Z
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
  H77 : (0 <= Int.unsigned x6)%Z
)(
  H85 : (Int.unsigned x6 < 64)%Z
)(
  H82 : x14 = $ OS_STAT_RDY \/
        x14 = $ OS_STAT_SEM \/
        x14 = $ OS_STAT_Q \/ x14 = $ OS_STAT_MBOX \/ x14 = $ OS_STAT_MUTEX
)(
  x15 : val
)(
  H84 : x14 = $ OS_STAT_RDY -> x15 = Vnull
)(
  H43 : (Int.unsigned (x6 >>ᵢ $ 3) <= 255)%Z
)(
  H45 : (Int.unsigned ($ 1<<ᵢ(x6 >>ᵢ $ 3)) <= 255)%Z
)(
  H44 : (Int.unsigned ($ 1<<ᵢ(x6&ᵢ$ 7)) <= 255)%Z
)(
  H42 : (Int.unsigned (x6&ᵢ$ 7) <= 255)%Z
)(
  H70 : TcbJoin (v'52, Int.zero) (x6, t, m) x10 v'45
)(
  H41 : (Int.unsigned x6 <= 255)%Z
)(
  H28 : Int.ltu x6 (x >>ᵢ $ 8) = false
)(
  H37 : isptr x15
)(
  H40 : (Int.unsigned x14 <= 255)%Z
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
  r1 : (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3) < 8)%Z
)(
  r2 : (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7) < 8)%Z
)(
  r3 : (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3) < 8)%Z
)(
  r4 : (Int.unsigned ((x >>ᵢ $ 8)&ᵢ$ 7) < 8)%Z
)(
  H34 : array_type_vallist_match Int8u OSMapVallist
)(
  H69 : length OSMapVallist = 8
)(
  H71 : Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)) < 8
)(
  x8 : int32
)(
  H74 : nth_val'
          (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
          OSMapVallist = Vint32 x8
)(
  H75 : true = rule_type_val_match Int8u (Vint32 x8)
)(
  H76 : Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)) < 8
)(
  x9 : int32
)(
  H78 : nth_val'
          (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)))
          OSMapVallist = Vint32 x9
)(
  H79 : true = rule_type_val_match Int8u (Vint32 x9)
)(
  H80 : Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)) < 8
)(
  x11 : int32
)(
  H81 : nth_val'
          (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)))
          OSMapVallist = Vint32 x11
)(
  H83 : true = rule_type_val_match Int8u (Vint32 x11)
)(
  r5 : (Int.unsigned (x6 >>ᵢ $ 3) < 8)%Z
)(
  r6 : (Int.unsigned (x6&ᵢ$ 7) < 8)%Z
)(
  rr1 : Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3)) < length v'36
)(
  rr2 : Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)) <
        length v'36
)(
  rr3 : Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)) <
        length v'36
)(
  rr4 : Z.to_nat (Int.unsigned ((x >>ᵢ $ 8)&ᵢ$ 7)) < length v'36
)(
  rr5 : Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3)) < length v'36
)(
  rr6 : Z.to_nat (Int.unsigned (x6&ᵢ$ 7)) < length v'36
)(
  rrr1 : (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3) < Z.of_nat (length v'36))%Z
)(
  rrr2 : (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7) <
          Z.of_nat (length v'36))%Z
)(
  rrr3 : (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3) <
          Z.of_nat (length v'36))%Z
)(
  rrr4 : (Int.unsigned ((x >>ᵢ $ 8)&ᵢ$ 7) < Z.of_nat (length v'36))%Z
)(
  rrr5 : (Int.unsigned (x6 >>ᵢ $ 3) < Z.of_nat (length v'36))%Z
)(
  rrr6 : (Int.unsigned (x6&ᵢ$ 7) < Z.of_nat (length v'36))%Z
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
  H91 : (Int.unsigned x16 <= 255)%Z
)(
  x13 : int32
)(
  H87 : nth_val'
          (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
          v'36 = Vint32 x13
)(
  H90 : (Int.unsigned x13 <= 255)%Z
)(
  x12 : int32
)(
  H86 : nth_val' (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3))) v'36 = Vint32 x12
)(
  H89 : (Int.unsigned x12 <= 255)%Z
)(
  H92 : x1 = Vptr v'51
                  )
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
   {{ <|| mutexpost (Vptr (v'29, Int.zero) :: nil) ||>  **
     A_dom_lenv
       ((pevent, OS_EVENT ∗)
        :: (os_code_defs.x, Int8u)
           :: (pip, Int8u) :: (prio, Int8u) :: (legal, Int8u) :: nil) **
     GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
       (update_nth_val (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3))) v'36
          (val_inj
             (and (nth_val' (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3))) v'36)
                (Vint32 (Int.not ($ 1<<ᵢ(x6&ᵢ$ 7))))))) **
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
     AGVars ** atoy_inv' ** LV pevent @ OS_EVENT ∗ |-> Vptr (v'29, Int.zero)}} 
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
OSTCBPrioTbl ′ [pip ′] =ₑ 〈 OS_TCB ∗ 〉 os_mutex.PlaceHolder
                          {{
(
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
           (val_inj (and (Vint32 x12) (Vint32 (Int.not ($ 1<<ᵢ(x6&ᵢ$ 7)))))))
        (val_inj
           (or
              (nth_val'
                 (Z.to_nat
                    (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
                 (update_nth_val (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3))) v'36
                    (Vint32 (x12&ᵢInt.not ($ 1<<ᵢ(x6&ᵢ$ 7)))))) 
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
                           :: Vint32 ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)
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
          (V$ 0)) <> Vundef|] )%Z **
            [| x1 = Vptr v'51 |]
\\//(<|| mutexpost (Vptr (v'29, Int.zero) :: nil) ||>  **
           A_dom_lenv
             ((pevent, OS_EVENT ∗)
              :: (os_code_defs.x, Int8u)
                 :: (pip, Int8u) :: (prio, Int8u) :: (legal, Int8u) :: nil) **
           GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64)
             (update_nth_val (Z.to_nat (Int.unsigned (x >>ᵢ $ 8)))
                (update_nth_val
                   (Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)))
                   v'30 (Vptr (v'52, Int.zero))) (Vptr v'51)) **
           GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
             (update_nth_val
                (Z.to_nat
                   (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
                (update_nth_val (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3))) v'36
                   (val_inj
                      (and (Vint32 x12) (Vint32 (Int.not ($ 1<<ᵢ(x6&ᵢ$ 7)))))))
                (val_inj
                   (or
                      (nth_val'
                         (Z.to_nat
                            (Int.unsigned
                               ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
                         (update_nth_val
                            (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3))) v'36
                            (Vint32 (x12&ᵢInt.not ($ 1<<ᵢ(x6&ᵢ$ 7))))))
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
              :: Vint32 i
                 :: Vint32 x :: Vptr (v'52, $ 0) :: x3 :: v'46 :: nil) **
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
                                          :: Vint32 ($ 1<<ᵢ(x6 >>ᵢ $ 3))
                                             :: nil) :: v'35) **
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
                     (update_nth_val (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3)))
                        v'36
                        (val_inj
                           (and (Vint32 x12)
                              (Vint32 (Int.not ($ 1<<ᵢ(x6&ᵢ$ 7)))))))) 
                  (V$ 0)) = Vint32 Int.zero \/
             val_inj
               (val_eq
                  (nth_val' (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3)))
                     (update_nth_val (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3)))
                        v'36
                        (val_inj
                           (and (Vint32 x12)
                              (Vint32 (Int.not ($ 1<<ᵢ(x6&ᵢ$ 7)))))))) 
                  (V$ 0)) = Vnull|] **
            [| x1 = Vptr v'51 |]


           )

                           }}
                                                              .

(*   forall (
 *   v' : val
 * )(
 *   v'0 : val
 * )(
 *   v'1 : val
 * )(
 *   v'2 : val
 * )(
 *   v'3 : list vallist
 * )(
 *   v'4 : list vallist
 * )(
 *   v'5 : list vallist
 * )(
 *   v'6 : list EventData
 * )(
 *   v'7 : list EventCtr
 * )(
 *   v'8 : vallist
 * )(
 *   v'9 : val
 * )(
 *   v'10 : val
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
 *   v'18 : Int.int
 * )(
 *   v'19 : addrval
 * )(
 *   v'20 : addrval
 * )(
 *   v'21 : val
 * )(
 *   v'22 : list vallist
 * )(
 *   H : RH_TCBList_ECBList_P v'16 v'17 v'19
 * )(
 *   H0 : RH_CurTCB v'19 v'17
 * )(
 *   v'25 : list EventCtr
 * )(
 *   v'26 : list EventCtr
 * )(
 *   v'27 : list EventData
 * )(
 *   v'28 : list EventData
 * )(
 *   v'30 : vallist
 * )(
 *   v'31 : val
 * )(
 *   v'33 : list vallist
 * )(
 *   v'35 : list vallist
 * )(
 *   v'36 : vallist
 * )(
 *   v'38 : EcbMod.map
 * )(
 *   v'39 : TcbMod.map
 * )(
 *   v'42 : val
 * )(
 *   v'44 : vallist
 * )(
 *   v'46 : val
 * )(
 *   v'47 : EcbMod.map
 * )(
 *   v'48 : EcbMod.map
 * )(
 *   v'49 : EcbMod.map
 * )(
 *   w : waitset
 * )(
 *   v'51 : addrval
 * )(
 *   H3 : ECBList_P v'46 Vnull v'26 v'28 v'48 v'39
 * )(
 *   H17 : EcbMod.join v'47 v'49 v'38
 * )(
 *   H12 : @eq nat (@length EventCtr v'25) (@length EventData v'27)
 * )(
 *   H16 : isptr v'46
 * )(
 *   v'23 : addrval
 * )(
 *   v'29 : block
 * )(
 *   H11 : array_type_vallist_match Tint8 v'44
 * )(
 *   H19 : @eq nat (@length val v'44) (nat_of_Z OS_EVENT_TBL_SIZE)
 * )(
 *   x3 : val
 * )(
 *   i : Int.int
 * )(
 *   H21 : Z.le (Int.unsigned i) (Zpos (xI (xI (xI (xI (xI (xI (xI xH))))))))
 * )(
 *   H18 : RL_Tbl_Grp_P v'44 (Vint32 i)
 * )(
 *   H24 : isptr v'46
 * )(
 *   H2 : ECBList_P v'42 (Vptr (@pair block Int.int v'29 Int.zero)) v'25 v'27
 *          v'47 v'39
 * )(
 *   H14 : @eq (option (prod block Int.int))
 *           (id_addrval' (Vptr (@pair block Int.int v'29 Int.zero)) OSEventTbl
 *              OS_EVENT) (@Some addrval v'23)
 * )(
 *   H20 : Z.le (Int.unsigned (Int.repr OS_EVENT_TYPE_MUTEX))
 *           (Zpos (xI (xI (xI (xI (xI (xI (xI xH))))))))
 * )(
 *   x : Int.int
 * )(
 *   H10 : Z.le (Int.unsigned x)
 *           (Zpos
 *              (xI
 *                 (xI
 *                    (xI
 *                       (xI
 *                          (xI
 *                             (xI
 *                                (xI (xI (xI (xI (xI (xI (xI (xI (xI xH))))))))))))))))
 * )(
 *   H15 : Z.lt (Int.unsigned (Int.shru x (Int.repr (Zpos (xO (xO (xO xH)))))))
 *           (Zpos (xO (xO (xO (xO (xO (xO xH)))))))
 * )(
 *   H22 : Z.le (Int.unsigned x)
 *           (Zpos
 *              (xI
 *                 (xI
 *                    (xI
 *                       (xI
 *                          (xI
 *                             (xI
 *                                (xI (xI (xI (xI (xI (xI (xI (xI (xI xH))))))))))))))))
 * )(
 *   v'24 : val
 * )(
 *   v'40 : val
 * )(
 *   v'43 : TcbMod.map
 * )(
 *   v'45 : TcbMod.map
 * )(
 *   v'52 : block
 * )(
 *   H31 : not (@eq val v'31 Vnull)
 * )(
 *   H32 : TcbMod.join v'43 v'45 v'39
 * )(
 *   H33 : TCBList_P v'31 v'33 v'36 v'43
 * )(
 *   H30 : not (@eq val (Vptr (@pair block Int.int v'52 Int.zero)) Vnull)
 * )(
 *   i6 : Int.int
 * )(
 *   H39 : Z.le (Int.unsigned i6)
 *           (Zpos
 *              (xI
 *                 (xI
 *                    (xI
 *                       (xI
 *                          (xI
 *                             (xI
 *                                (xI (xI (xI (xI (xI (xI (xI (xI (xI xH))))))))))))))))
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
 *   H7 : RH_TCBList_ECBList_P v'38 v'39 (@pair block Int.int v'52 Int.zero)
 * )(
 *   H8 : RH_CurTCB (@pair block Int.int v'52 Int.zero) v'39
 * )(
 *   H23 : isptr (Vptr (@pair block Int.int v'52 (Int.repr Z0)))
 * )(
 *   H5 : R_ECB_ETbl_P (@pair block Int.int v'29 Int.zero)
 *          (@pair (list val) vallist
 *             (@cons val (Vint32 (Int.repr OS_EVENT_TYPE_MUTEX))
 *                (@cons val (Vint32 i)
 *                   (@cons val (Vint32 x)
 *                      (@cons val
 *                         (Vptr (@pair block Int.int v'52 (Int.repr Z0)))
 *                         (@cons val x3 (@cons val v'46 (@nil val))))))) v'44)
 *          v'39
 * )(
 *   H1 : ECBList_P v'42 Vnull
 *          (@app EventCtr v'25
 *             (@app (prod (list val) vallist)
 *                (@cons (prod (list val) vallist)
 *                   (@pair (list val) vallist
 *                      (@cons val (Vint32 (Int.repr OS_EVENT_TYPE_MUTEX))
 *                         (@cons val (Vint32 i)
 *                            (@cons val (Vint32 x)
 *                               (@cons val
 *                                  (Vptr
 *                                     (@pair block Int.int v'52 (Int.repr Z0)))
 *                                  (@cons val x3 (@cons val v'46 (@nil val)))))))
 *                      v'44) (@nil (prod (list val) vallist))) v'26))
 *          (@app EventData v'27
 *             (@app EventData
 *                (@cons EventData
 *                   (DMutex (Vint32 x)
 *                      (Vptr (@pair block Int.int v'52 (Int.repr Z0))))
 *                   (@nil EventData)) v'28)) v'38 v'39
 * )(
 *   H29 : Logic.or
 *           (@eq Int.int (Int.and x (Int.repr OS_MUTEX_KEEP_LOWER_8))
 *              (Int.repr OS_MUTEX_AVAILABLE))
 *           (not
 *              (@eq Int.int (Int.and x (Int.repr OS_MUTEX_KEEP_LOWER_8))
 *                 (Int.repr OS_MUTEX_AVAILABLE)))
 * )(
 *   H35 : not
 *           (@eq Int.int (Int.and x (Int.repr OS_MUTEX_KEEP_LOWER_8))
 *              (Int.repr OS_MUTEX_AVAILABLE))
 * )(
 *   H47 : @eq bool
 *           (Int.ltu (Int.shru x (Int.repr (Zpos (xO (xO (xO xH))))))
 *              (Int.and x (Int.repr OS_MUTEX_KEEP_LOWER_8))) true
 * )(
 *   H48 : Z.lt (Int.unsigned (Int.and x (Int.repr OS_MUTEX_KEEP_LOWER_8)))
 *           (Zpos (xO (xO (xO (xO (xO (xO xH)))))))
 * )(
 *   H6 : EcbMod.joinsig (@pair block Int.int v'29 Int.zero)
 *          (@pair edata waitset
 *             (absmutexsem (Int.shru x (Int.repr (Zpos (xO (xO (xO xH))))))
 *                (@Some (prod (prod block Int.int) Int.int)
 *                   (@pair (prod block Int.int) Int.int
 *                      (@pair block Int.int v'52 (Int.repr Z0))
 *                      (Int.and x (Int.repr OS_MUTEX_KEEP_LOWER_8))))) w) v'48
 *          v'49
 * )(
 *   H4 : @eq (option (prod (prod block Int.int) Int.int))
 *          (@Some (prod (prod block Int.int) Int.int)
 *             (@pair (prod block Int.int) Int.int
 *                (@pair block Int.int v'52 (Int.repr Z0))
 *                (Int.and x (Int.repr OS_MUTEX_KEEP_LOWER_8))))
 *          (@None (prod (prod block Int.int) Int.int)) ->
 *        @eq waitset w (@nil tid)
 * )(
 *   H9 : forall (tid : tid) (opr : Int.int),
 *        @eq (option (prod (prod block Int.int) Int.int))
 *          (@Some (prod (prod block Int.int) Int.int)
 *             (@pair (prod block Int.int) Int.int
 *                (@pair block Int.int v'52 (Int.repr Z0))
 *                (Int.and x (Int.repr OS_MUTEX_KEEP_LOWER_8))))
 *          (@Some (prod language.tid Int.int)
 *             (@pair language.tid Int.int tid opr)) ->
 *        Logic.and
 *          (@eq bool
 *             (Int.ltu (Int.shru x (Int.repr (Zpos (xO (xO (xO xH)))))) opr)
 *             true)
 *          (Z.lt (Int.unsigned opr) (Zpos (xO (xO (xO (xO (xO (xO xH))))))))
 * )(
 *   H13 : not (@eq waitset w (@nil tid)) ->
 *         not
 *           (@eq (option (prod (prod block Int.int) Int.int))
 *              (@Some (prod (prod block Int.int) Int.int)
 *                 (@pair (prod block Int.int) Int.int
 *                    (@pair block Int.int v'52 (Int.repr Z0))
 *                    (Int.and x (Int.repr OS_MUTEX_KEEP_LOWER_8))))
 *              (@None (prod (prod block Int.int) Int.int)))
 * )(
 *   H25 : @eq Int.int (Int.and x (Int.repr OS_MUTEX_KEEP_LOWER_8))
 *           (Int.repr OS_MUTEX_AVAILABLE) ->
 *         Logic.and
 *           (@eq (option (prod (prod block Int.int) Int.int))
 *              (@Some (prod (prod block Int.int) Int.int)
 *                 (@pair (prod block Int.int) Int.int
 *                    (@pair block Int.int v'52 (Int.repr Z0))
 *                    (Int.and x (Int.repr OS_MUTEX_KEEP_LOWER_8))))
 *              (@None (prod (prod block Int.int) Int.int)))
 *           (@eq val (Vptr (@pair block Int.int v'52 (Int.repr Z0))) Vnull)
 * )(
 *   H26 : not
 *           (@eq Int.int (Int.and x (Int.repr OS_MUTEX_KEEP_LOWER_8))
 *              (Int.repr OS_MUTEX_AVAILABLE)) ->
 *         @ex addrval
 *           (fun tid : addrval =>
 *            Logic.and
 *              (@eq val (Vptr (@pair block Int.int v'52 (Int.repr Z0)))
 *                 (Vptr tid))
 *              (@eq (option (prod (prod block Int.int) Int.int))
 *                 (@Some (prod (prod block Int.int) Int.int)
 *                    (@pair (prod block Int.int) Int.int
 *                       (@pair block Int.int v'52 (Int.repr Z0))
 *                       (Int.and x (Int.repr OS_MUTEX_KEEP_LOWER_8))))
 *                 (@Some (prod addrval Int.int)
 *                    (@pair addrval Int.int tid
 *                       (Int.and x (Int.repr OS_MUTEX_KEEP_LOWER_8))))))
 * )(
 *   backup : RLH_ECBData_P
 *              (DMutex (Vint32 x)
 *                 (Vptr (@pair block Int.int v'52 (Int.repr Z0))))
 *              (@pair edata waitset
 *                 (absmutexsem (Int.shru x (Int.repr (Zpos (xO (xO (xO xH))))))
 *                    (@Some (prod (prod block Int.int) Int.int)
 *                       (@pair (prod block Int.int) Int.int
 *                          (@pair block Int.int v'52 (Int.repr Z0))
 *                          (Int.and x (Int.repr OS_MUTEX_KEEP_LOWER_8))))) w)
 * )(
 *   v'32 : val
 * )(
 *   H46 : array_type_vallist_match (Tptr OS_TCB) v'30
 * )(
 *   H51 : @eq nat (@length val v'30)
 *           64%nat
 * )(
 *   H49 : RL_RTbl_PrioTbl_P v'36 v'30 v'51
 * )(
 *   H50 : R_PrioTbl_P v'30 v'39 v'51
 * )(
 *   x1 : val
 * )(
 *   H52 : @eq (option val)
 *           (nth_val
 *              (Z.to_nat
 *                 (Int.unsigned (Int.and x (Int.repr OS_MUTEX_KEEP_LOWER_8))))
 *              v'30) (@Some val x1)
 * )(
 *   x0 : val
 * )(
 *   H53 : @eq (option val)
 *           (nth_val
 *              (Z.to_nat
 *                 (Int.unsigned
 *                    (Int.shru x (Int.repr (Zpos (xO (xO (xO xH)))))))) v'30)
 *           (@Some val x0)
 * )(
 *   H54 : array_type_vallist_match Tint8 v'36
 * )(
 *   H58 : @eq nat (@length val v'36) (nat_of_Z OS_RDY_TBL_SIZE)
 * )(
 *   i7 : Int.int
 * )(
 *   H55 : Z.le (Int.unsigned i7) (Zpos (xI (xI (xI (xI (xI (xI (xI xH))))))))
 * )(
 *   H57 : prio_in_tbl (Int.repr OS_IDLE_PRIO) v'36
 * )(
 *   H56 : RL_Tbl_Grp_P v'36 (Vint32 i7)
 * )(
 *   x2 : Int.int
 * )(
 *   fffa : @eq nat (@length val OSUnMapVallist)
 *           256%nat ->
 *          lt (Z.to_nat (Int.unsigned i))
 *            256%nat ->
 *          @ex Int.int
 *            (fun x4 : Int.int =>
 *             Logic.and (@eq val (Vint32 x2) (Vint32 x4))
 *               (@eq bool true (rule_type_val_match Tint8 (Vint32 x4))))
 * )(
 *   H59 : @eq nat (@length val OSUnMapVallist)
 *          256%nat
 * )(
 *   H60 : lt (Z.to_nat (Int.unsigned i))
 *           256%nat
 * )(
 *   H61 : @eq val (nth_val' (Z.to_nat (Int.unsigned i)) OSUnMapVallist)
 *           (Vint32 x2)
 * )(
 *   H62 : @eq bool true (rule_type_val_match Tint8 (Vint32 x2))
 * )(
 *   fffbb : Z.lt (Int.unsigned x2) (Zpos (xO (xO (xO xH))))
 * )(
 *   fffbb2 : lt (Z.to_nat (Int.unsigned x2)) (@length val v'44)
 * )(
 *   H19'' : @eq nat (@length val v'44) (Z.to_nat (Zpos (xO (xO (xO xH)))))
 * )(
 *   x4 : Int.int
 * )(
 *   H63 : @eq val (nth_val' (Z.to_nat (Int.unsigned x2)) v'44) (Vint32 x4)
 * )(
 *   H64 : Z.le (Int.unsigned x4) (Zpos (xI (xI (xI (xI (xI (xI (xI xH))))))))
 * )(
 *   H65 : lt (Z.to_nat (Int.unsigned x4)) (@length val OSUnMapVallist)
 * )(
 *   x5 : Int.int
 * )(
 *   H66 : @eq val (nth_val' (Z.to_nat (Int.unsigned x4)) OSUnMapVallist)
 *           (Vint32 x5)
 * )(
 *   H67 : Z.le (Int.unsigned x5) (Zpos (xI (xI (xI (xI (xI (xI (xI xH))))))))
 * )(
 *   ttfasd : Z.lt (Int.unsigned x5) (Zpos (xO (xO (xO xH))))
 * )(
 *   H68 :  val_inj
 *           (bool_and
 *              (val_inj
 *                 (notint
 *                    (val_inj
 *                       (if Int.eq i ($ 0)
 *                        then Some (Vint32 Int.one)
 *                        else Some (Vint32 Int.zero)))))
 *              (val_inj
 *                 (bool_or
 *                    (val_inj
 *                       (if Int.ltu ((x2<<$ 3)+ᵢx5)
 *                             (Int.modu (Int.shru x ($ 8)) ($ Byte.modulus))
 *                        then Some (Vint32 Int.one)
 *                        else Some (Vint32 Int.zero)))
 *                    (val_inj
 *                       (if Int.eq ((x2<<$ 3)+ᵢx5)
 *                             (Int.modu (Int.shru x ($ 8)) ($ Byte.modulus))
 *                        then Some (Vint32 Int.one)
 *                        else Some (Vint32 Int.zero)))))) = 
 *         Vint32 Int.zero \/
 *         val_inj
 *           (bool_and
 *              (val_inj
 *                 (notint
 *                    (val_inj
 *                       (if Int.eq i ($ 0)
 *                        then Some (Vint32 Int.one)
 *                        else Some (Vint32 Int.zero)))))
 *              (val_inj
 *                 (bool_or
 *                    (val_inj
 *                       (if Int.ltu ((x2<<$ 3)+ᵢx5)
 *                             (Int.modu (Int.shru x ($ 8)) ($ Byte.modulus))
 *                        then Some (Vint32 Int.one)
 *                        else Some (Vint32 Int.zero)))
 *                    (val_inj
 *                       (if Int.eq ((x2<<$ 3)+ᵢx5)
 *                             (Int.modu (Int.shru x ($ 8)) ($ Byte.modulus))
 *                        then Some (Vint32 Int.one)
 *                        else Some (Vint32 Int.zero)))))) = Vnull
 * )(
 *   H27 : isptr x7
 * )(
 *   H38 : isptr m
 * )(
 *   x6 : Int.int
 * )(
 *   x14 : Int.int
 * )(
 *   H77 : Z.le Z0 (Int.unsigned x6)
 * )(
 *   H85 : Z.lt (Int.unsigned x6) (Zpos (xO (xO (xO (xO (xO (xO xH)))))))
 * )(
 *   H82 : Logic.or (@eq Int.int x14 (Int.repr OS_STAT_RDY))
 *           (Logic.or (@eq Int.int x14 (Int.repr OS_STAT_SEM))
 *              (Logic.or (@eq Int.int x14 (Int.repr OS_STAT_Q))
 *                 (Logic.or (@eq Int.int x14 (Int.repr OS_STAT_MBOX))
 *                    (@eq Int.int x14 (Int.repr OS_STAT_MUTEX)))))
 * )(
 *   x15 : val
 * )(
 *   H84 : @eq Int.int x14 (Int.repr OS_STAT_RDY) -> @eq val x15 Vnull
 * )(
 *   H43 : Z.le (Int.unsigned (Int.shru x6 (Int.repr (Zpos (xI xH)))))
 *           (Zpos (xI (xI (xI (xI (xI (xI (xI xH))))))))
 * )(
 *   H45 : Z.le
 *           (Int.unsigned
 *              (Int.shl (Int.repr (Zpos xH))
 *                 (Int.shru x6 (Int.repr (Zpos (xI xH))))))
 *           (Zpos (xI (xI (xI (xI (xI (xI (xI xH))))))))
 * )(
 *   H44 : Z.le
 *           (Int.unsigned
 *              (Int.shl (Int.repr (Zpos xH))
 *                 (Int.and x6 (Int.repr (Zpos (xI (xI xH)))))))
 *           (Zpos (xI (xI (xI (xI (xI (xI (xI xH))))))))
 * )(
 *   H42 : Z.le (Int.unsigned (Int.and x6 (Int.repr (Zpos (xI (xI xH))))))
 *           (Zpos (xI (xI (xI (xI (xI (xI (xI xH))))))))
 * )(
 *   H70 : TcbJoin (@pair block Int.int v'52 Int.zero)
 *           (@pair (prod priority taskstatus) msg
 *              (@pair priority taskstatus x6 t) m) x10 v'45
 * )(
 *   H41 : Z.le (Int.unsigned x6) (Zpos (xI (xI (xI (xI (xI (xI (xI xH))))))))
 * )(
 *   H28 : @eq bool
 *           (Int.ltu x6 (Int.shru x (Int.repr (Zpos (xO (xO (xO xH))))))) false
 * )(
 *   H37 : isptr x15
 * )(
 *   H40 : Z.le (Int.unsigned x14) (Zpos (xI (xI (xI (xI (xI (xI (xI xH))))))))
 * )(
 *   H73 : R_TCB_Status_P
 *           (@cons val x7
 *              (@cons val v'24
 *                 (@cons val x15
 *                    (@cons val m
 *                       (@cons val (Vint32 i6)
 *                          (@cons val (Vint32 x14)
 *                             (@cons val (Vint32 x6)
 *                                (@cons val
 *                                   (Vint32
 *                                      (Int.and x6
 *                                         (Int.repr (Zpos (xI (xI xH))))))
 *                                   (@cons val
 *                                      (Vint32
 *                                         (Int.shru x6
 *                                            (Int.repr (Zpos (xI xH)))))
 *                                      (@cons val
 *                                         (Vint32
 *                                            (Int.shl 
 *                                               (Int.repr (Zpos xH))
 *                                               (Int.and x6
 *                                                  (Int.repr
 *                                                   (Zpos (xI (xI xH)))))))
 *                                         (@cons val
 *                                            (Vint32
 *                                               (Int.shl 
 *                                                  (Int.repr (Zpos xH))
 *                                                  (Int.shru x6
 *                                                   (Int.repr (Zpos (xI xH))))))
 *                                            (@nil val)))))))))))) v'36
 *           (@pair (prod priority taskstatus) msg
 *              (@pair priority taskstatus x6 t) m)
 * )(
 *   backup2 : TCBList_P (Vptr (@pair block Int.int v'52 Int.zero))
 *               (@cons (list val)
 *                  (@cons val x7
 *                     (@cons val v'24
 *                        (@cons val x15
 *                           (@cons val m
 *                              (@cons val (Vint32 i6)
 *                                 (@cons val (Vint32 x14)
 *                                    (@cons val (Vint32 x6)
 *                                       (@cons val
 *                                          (Vint32
 *                                             (Int.and x6
 *                                                (Int.repr (Zpos (xI (xI xH))))))
 *                                          (@cons val
 *                                             (Vint32
 *                                                (Int.shru x6
 *                                                   (Int.repr (Zpos (xI xH)))))
 *                                             (@cons val
 *                                                (Vint32
 *                                                   (Int.shl
 *                                                   (Int.repr (Zpos xH))
 *                                                   (Int.and x6
 *                                                   (Int.repr
 *                                                   (Zpos (xI (xI xH)))))))
 *                                                (@cons val
 *                                                   (Vint32
 *                                                   (Int.shl
 *                                                   (Int.repr (Zpos xH))
 *                                                   (Int.shru x6
 *                                                   (Int.repr (Zpos (xI xH))))))
 *                                                   (@nil val)))))))))))) v'35)
 *               v'36 v'45
 * )(
 *   r1 : Z.lt
 *          (Int.unsigned
 *             (Int.shru (Int.shru x (Int.repr (Zpos (xO (xO (xO xH))))))
 *                (Int.repr (Zpos (xI xH))))) (Zpos (xO (xO (xO xH))))
 * )(
 *   r2 : Z.lt
 *          (Int.unsigned
 *             (Int.and (Int.and x (Int.repr OS_MUTEX_KEEP_LOWER_8))
 *                (Int.repr (Zpos (xI (xI xH)))))) (Zpos (xO (xO (xO xH))))
 * )(
 *   r3 : Z.lt
 *          (Int.unsigned
 *             (Int.shru (Int.and x (Int.repr OS_MUTEX_KEEP_LOWER_8))
 *                (Int.repr (Zpos (xI xH))))) (Zpos (xO (xO (xO xH))))
 * )(
 *   r4 : Z.lt
 *          (Int.unsigned
 *             (Int.and (Int.shru x (Int.repr (Zpos (xO (xO (xO xH))))))
 *                (Int.repr (Zpos (xI (xI xH)))))) (Zpos (xO (xO (xO xH))))
 * )(
 *   H34 : array_type_vallist_match Tint8 OSMapVallist
 * )(
 *   H69 : @eq nat (@length val OSMapVallist) (S (S (S (S (S (S (S (S O))))))))
 * )(
 *   H71 : lt
 *           (Z.to_nat
 *              (Int.unsigned
 *                 (Int.shru (Int.and x (Int.repr OS_MUTEX_KEEP_LOWER_8))
 *                    (Int.repr (Zpos (xI xH))))))
 *           (S (S (S (S (S (S (S (S O))))))))
 * )(
 *   x8 : Int.int
 * )(
 *   H74 : @eq val
 *           (nth_val'
 *              (Z.to_nat
 *                 (Int.unsigned
 *                    (Int.shru (Int.and x (Int.repr OS_MUTEX_KEEP_LOWER_8))
 *                       (Int.repr (Zpos (xI xH)))))) OSMapVallist) 
 *           (Vint32 x8)
 * )(
 *   H75 : @eq bool true (rule_type_val_match Tint8 (Vint32 x8))
 * )(
 *   H76 : lt
 *           (Z.to_nat
 *              (Int.unsigned
 *                 (Int.and (Int.and x (Int.repr OS_MUTEX_KEEP_LOWER_8))
 *                    (Int.repr (Zpos (xI (xI xH)))))))
 *           (S (S (S (S (S (S (S (S O))))))))
 * )(
 *   x9 : Int.int
 * )(
 *   H78 : @eq val
 *           (nth_val'
 *              (Z.to_nat
 *                 (Int.unsigned
 *                    (Int.and (Int.and x (Int.repr OS_MUTEX_KEEP_LOWER_8))
 *                       (Int.repr (Zpos (xI (xI xH))))))) OSMapVallist)
 *           (Vint32 x9)
 * )(
 *   H79 : @eq bool true (rule_type_val_match Tint8 (Vint32 x9))
 * )(
 *   H80 : lt
 *           (Z.to_nat
 *              (Int.unsigned
 *                 (Int.and (Int.and x (Int.repr OS_MUTEX_KEEP_LOWER_8))
 *                    (Int.repr (Zpos (xI (xI xH)))))))
 *           (S (S (S (S (S (S (S (S O))))))))
 * )(
 *   x11 : Int.int
 * )(
 *   H81 : @eq val
 *           (nth_val'
 *              (Z.to_nat
 *                 (Int.unsigned
 *                    (Int.and (Int.and x (Int.repr OS_MUTEX_KEEP_LOWER_8))
 *                       (Int.repr (Zpos (xI (xI xH))))))) OSMapVallist)
 *           (Vint32 x11)
 * )(
 *   H83 : @eq bool true (rule_type_val_match Tint8 (Vint32 x11))
 * )(
 *   r5 : Z.lt (Int.unsigned (Int.shru x6 (Int.repr (Zpos (xI xH)))))
 *          (Zpos (xO (xO (xO xH))))
 * )(
 *   r6 : Z.lt (Int.unsigned (Int.and x6 (Int.repr (Zpos (xI (xI xH))))))
 *          (Zpos (xO (xO (xO xH))))
 * )(
 *   rr1 : lt
 *           (Z.to_nat
 *              (Int.unsigned
 *                 (Int.shru (Int.shru x (Int.repr (Zpos (xO (xO (xO xH))))))
 *                    (Int.repr (Zpos (xI xH)))))) (@length val v'36)
 * )(
 *   rr2 : lt
 *           (Z.to_nat
 *              (Int.unsigned
 *                 (Int.and (Int.and x (Int.repr OS_MUTEX_KEEP_LOWER_8))
 *                    (Int.repr (Zpos (xI (xI xH))))))) 
 *           (@length val v'36)
 * )(
 *   rr3 : lt
 *           (Z.to_nat
 *              (Int.unsigned
 *                 (Int.shru (Int.and x (Int.repr OS_MUTEX_KEEP_LOWER_8))
 *                    (Int.repr (Zpos (xI xH)))))) (@length val v'36)
 * )(
 *   rr4 : lt
 *           (Z.to_nat
 *              (Int.unsigned
 *                 (Int.and (Int.shru x (Int.repr (Zpos (xO (xO (xO xH))))))
 *                    (Int.repr (Zpos (xI (xI xH))))))) 
 *           (@length val v'36)
 * )(
 *   rr5 : lt (Z.to_nat (Int.unsigned (Int.shru x6 (Int.repr (Zpos (xI xH))))))
 *           (@length val v'36)
 * )(
 *   rr6 : lt
 *           (Z.to_nat
 *              (Int.unsigned (Int.and x6 (Int.repr (Zpos (xI (xI xH)))))))
 *           (@length val v'36)
 * )(
 *   rrr1 : Z.lt
 *            (Int.unsigned
 *               (Int.shru (Int.shru x (Int.repr (Zpos (xO (xO (xO xH))))))
 *                  (Int.repr (Zpos (xI xH))))) (Z.of_nat (@length val v'36))
 * )(
 *   rrr2 : Z.lt
 *            (Int.unsigned
 *               (Int.and (Int.and x (Int.repr OS_MUTEX_KEEP_LOWER_8))
 *                  (Int.repr (Zpos (xI (xI xH))))))
 *            (Z.of_nat (@length val v'36))
 * )(
 *   rrr3 : Z.lt
 *            (Int.unsigned
 *               (Int.shru (Int.and x (Int.repr OS_MUTEX_KEEP_LOWER_8))
 *                  (Int.repr (Zpos (xI xH))))) (Z.of_nat (@length val v'36))
 * )(
 *   rrr4 : Z.lt
 *            (Int.unsigned
 *               (Int.and (Int.shru x (Int.repr (Zpos (xO (xO (xO xH))))))
 *                  (Int.repr (Zpos (xI (xI xH))))))
 *            (Z.of_nat (@length val v'36))
 * )(
 *   rrr5 : Z.lt (Int.unsigned (Int.shru x6 (Int.repr (Zpos (xI xH)))))
 *            (Z.of_nat (@length val v'36))
 * )(
 *   rrr6 : Z.lt (Int.unsigned (Int.and x6 (Int.repr (Zpos (xI (xI xH))))))
 *            (Z.of_nat (@length val v'36))
 * )(
 *   HH58 : @eq nat (@length val v'36) (Z.to_nat (Zpos (xO (xO (xO xH)))))
 * )(
 *   aa : @eq bool
 *          (rule_type_val_match Tint8
 *             (nth_val'
 *                (Z.to_nat
 *                   (Int.unsigned
 *                      (Int.shru
 *                         (Int.shru x (Int.repr (Zpos (xO (xO (xO xH))))))
 *                         (Int.repr (Zpos (xI xH)))))) v'36)) true
 * )(
 *   aa2 : @eq bool
 *           (rule_type_val_match Tint8
 *              (nth_val'
 *                 (Z.to_nat
 *                    (Int.unsigned
 *                       (Int.shru (Int.and x (Int.repr OS_MUTEX_KEEP_LOWER_8))
 *                          (Int.repr (Zpos (xI xH)))))) v'36)) true
 * )(
 *   aa3 : @eq bool
 *           (rule_type_val_match Tint8
 *              (nth_val'
 *                 (Z.to_nat
 *                    (Int.unsigned (Int.shru x6 (Int.repr (Zpos (xI xH))))))
 *                 v'36)) true
 * )(
 *   x16 : Int.int
 * )(
 *   H88 : @eq val
 *           (nth_val'
 *              (Z.to_nat
 *                 (Int.unsigned
 *                    (Int.shru (Int.shru x (Int.repr (Zpos (xO (xO (xO xH))))))
 *                       (Int.repr (Zpos (xI xH)))))) v'36) 
 *           (Vint32 x16)
 * )(
 *   H91 : Z.le (Int.unsigned x16) (Zpos (xI (xI (xI (xI (xI (xI (xI xH))))))))
 * )(
 *   x13 : Int.int
 * )(
 *   H87 : @eq val
 *           (nth_val'
 *              (Z.to_nat
 *                 (Int.unsigned
 *                    (Int.shru (Int.and x (Int.repr OS_MUTEX_KEEP_LOWER_8))
 *                       (Int.repr (Zpos (xI xH)))))) v'36) 
 *           (Vint32 x13)
 * )(
 *   H90 : Z.le (Int.unsigned x13) (Zpos (xI (xI (xI (xI (xI (xI (xI xH))))))))
 * )(
 *   x12 : Int.int
 * )(
 *   H86 : @eq val
 *           (nth_val'
 *              (Z.to_nat (Int.unsigned (Int.shru x6 (Int.repr (Zpos (xI xH))))))
 *              v'36) (Vint32 x12)
 * )(
 *   H89 : Z.le (Int.unsigned x12) (Zpos (xI (xI (xI (xI (xI (xI (xI xH))))))))
 * )(
 *   H92 : @eq val x1 (Vptr v'51)
 * ),
 *    InfRules OSQ_spec GetHPrio I
 *      (fun v : option val =>
 *       Astar
 *         (Astar
 *            (Astar
 *               (Astar
 *                  (@Aexists val
 *                     (fun v0 : val => Alvarmapsto pevent (Tptr OS_EVENT) v0))
 *                  (Astar
 *                     (@Aexists val
 *                        (fun v0 : val => Alvarmapsto os_code_defs.x Tint8 v0))
 *                     (Astar
 *                        (@Aexists val
 *                           (fun v0 : val => Alvarmapsto pip Tint8 v0))
 *                        (Astar
 *                           (@Aexists val
 *                              (fun v0 : val => Alvarmapsto prio Tint8 v0))
 *                           (Astar
 *                              (@Aexists val
 *                                 (fun v0 : val => Alvarmapsto legal Tint8 v0))
 *                              Aemp)))))
 *               (Astar (Aie true)
 *                  (Astar (Ais (@nil hid))
 *                     (Astar (Acs (@nil ie)) (Aisr empisr)))))
 *            (A_dom_lenv
 *               (@cons (prod ident type)
 *                  (@pair ident type pevent (Tptr OS_EVENT))
 *                  (@cons (prod ident type)
 *                     (@pair ident type os_code_defs.x Tint8)
 *                     (@cons (prod ident type) (@pair ident type pip Tint8)
 *                        (@cons (prod ident type) (@pair ident type prio Tint8)
 *                           (@cons (prod ident type)
 *                              (@pair ident type legal Tint8)
 *                              (@nil (prod ident type)))))))))
 *         (Aop' (spec_done v))) Afalse
 *      (Astar
 *         (Aop'
 *            (mutexpost
 *               (@cons val (Vptr (@pair block Int.int v'29 Int.zero))
 *                  (@nil val))))
 *         (Astar
 *            (A_dom_lenv
 *               (@cons (prod ident type)
 *                  (@pair ident type pevent (Tptr OS_EVENT))
 *                  (@cons (prod ident type)
 *                     (@pair ident type os_code_defs.x Tint8)
 *                     (@cons (prod ident type) (@pair ident type pip Tint8)
 *                        (@cons (prod ident type) (@pair ident type prio Tint8)
 *                           (@cons (prod ident type)
 *                              (@pair ident type legal Tint8)
 *                              (@nil (prod ident type))))))))
 *            (Astar
 *               (GAarray OSRdyTbl (Tarray Tint8 (nat_of_Z OS_RDY_TBL_SIZE))
 *                  (update_nth_val
 *                     (Z.to_nat
 *                        (Int.unsigned (Int.shru x6 (Int.repr (Zpos (xI xH))))))
 *                     v'36
 *                     (val_inj
 *                        (and
 *                           (nth_val'
 *                              (Z.to_nat
 *                                 (Int.unsigned
 *                                    (Int.shru x6 (Int.repr (Zpos (xI xH))))))
 *                              v'36)
 *                           (Vint32
 *                              (Int.not
 *                                 (Int.shl (Int.repr (Zpos xH))
 *                                    (Int.and x6 (Int.repr (Zpos (xI (xI xH))))))))))))
 *               (Astar
 *                  (Alvarmapsto os_code_defs.x Tint8
 *                     (Vint32
 *                        (Int.add (Int.shl x2 (Int.repr (Zpos (xI xH)))) x5)))
 *                  (Astar (Alvarmapsto legal Tint8 (Vint32 x2))
 *                     (Astar (Aptrmapsto v'51 Tint8 v'32)
 *                        (Astar
 *                           (Astruct (@pair block Int.int v'52 Int.zero) OS_TCB
 *                              (@cons val x7
 *                                 (@cons val v'24
 *                                    (@cons val x15
 *                                       (@cons val m
 *                                          (@cons val 
 *                                             (Vint32 i6)
 *                                             (@cons val 
 *                                                (Vint32 x14)
 *                                                (@cons val 
 *                                                   (Vint32 x6)
 *                                                   (@cons val
 *                                                   (Vint32
 *                                                   (Int.and x6
 *                                                   (Int.repr
 *                                                   (Zpos (xI (xI xH))))))
 *                                                   (@cons val
 *                                                   (Vint32
 *                                                   (Int.shru x6
 *                                                   (Int.repr (Zpos (xI xH)))))
 *                                                   (@cons val
 *                                                   (Vint32
 *                                                   (Int.shl
 *                                                   (Int.repr (Zpos xH))
 *                                                   (Int.and x6
 *                                                   (Int.repr
 *                                                   (Zpos (xI (xI xH)))))))
 *                                                   (@cons val
 *                                                   (Vint32
 *                                                   (Int.shl
 *                                                   (Int.repr (Zpos xH))
 *                                                   (Int.shru x6
 *                                                   (Int.repr (Zpos (xI xH))))))
 *                                                   (@nil val)))))))))))))
 *                           (Astar
 *                              (dllseg x7
 *                                 (Vptr (@pair block Int.int v'52 Int.zero))
 *                                 v'40 Vnull v'35 OS_TCB
 *                                 (fun vl : vallist => nth_val (S O) vl)
 *                                 (fun vl : vallist => nth_val O vl))
 *                              (Astar
 *                                 (Agvarmapsto OSTCBList (Tptr OS_TCB) v'31)
 *                                 (Astar
 *                                    (dllseg v'31 Vnull v'24
 *                                       (Vptr
 *                                          (@pair block Int.int v'52 Int.zero))
 *                                       v'33 OS_TCB
 *                                       (fun vl : vallist => nth_val (S O) vl)
 *                                       (fun vl : vallist => nth_val O vl))
 *                                    (Astar
 *                                       (Agvarmapsto OSTCBCur 
 *                                          (Tptr OS_TCB)
 *                                          (Vptr
 *                                             (@pair block Int.int v'52
 *                                                Int.zero)))
 *                                       (Astar
 *                                          (Alvarmapsto prio Tint8
 *                                             (Vint32
 *                                                (Int.and x
 *                                                   (Int.repr
 *                                                   OS_MUTEX_KEEP_LOWER_8))))
 *                                          (Astar
 *                                             (Alvarmapsto pip Tint8
 *                                                (Vint32
 *                                                   (Int.shru x
 *                                                   (Int.repr
 *                                                   (Zpos (xO (xO (xO xH))))))))
 *                                             (Astar
 *                                                (Astruct
 *                                                   (@pair block Int.int v'29
 *                                                   Int.zero) OS_EVENT
 *                                                   (@cons val
 *                                                   (Vint32
 *                                                   (Int.repr
 *                                                   OS_EVENT_TYPE_MUTEX))
 *                                                   (@cons val 
 *                                                   (Vint32 i)
 *                                                   (@cons val 
 *                                                   (Vint32 x)
 *                                                   (@cons val
 *                                                   (Vptr
 *                                                   (@pair block Int.int v'52
 *                                                   (Int.repr Z0)))
 *                                                   (@cons val x3
 *                                                   (@cons val v'46 (@nil val))))))))
 *                                                (Astar
 *                                                   (Aarray v'23
 *                                                   (Tarray Tint8
 *                                                   (nat_of_Z OS_EVENT_TBL_SIZE))
 *                                                   v'44)
 *                                                   (Astar 
 *                                                   (Aie false)
 *                                                   (Astar 
 *                                                   (Ais (@nil hid))
 *                                                   (Astar
 *                                                   (Acs
 *                                                   (@cons bool true
 *                                                   (@nil bool)))
 *                                                   (Astar 
 *                                                   (Aisr empisr)
 *                                                   (Astar
 *                                                   (Agvarmapsto OSEventList
 *                                                   (Tptr OS_EVENT) v'42)
 *                                                   (Astar
 *                                                   (evsllseg v'42
 *                                                   (Vptr
 *                                                   (@pair block Int.int v'29
 *                                                   Int.zero)) v'25 v'27)
 *                                                   (Astar
 *                                                   (evsllseg v'46 Vnull v'26
 *                                                   v'28)
 *                                                   (Astar A_isr_is_prop
 *                                                   (Astar
 *                                                   (Agvarmapsto OSRdyGrp Tint8
 *                                                   (Vint32 i7))
 *                                                   (Astar
 *                                                   (GAarray OSTCBPrioTbl
 *                                                   (Tarray 
 *                                                   (Tptr OS_TCB)
 *                                                   64)
 *                                                   v'30)
 *                                                   (Astar
 *                                                   (Agvarenv' OSPlaceHolder
 *                                                   Tint8 v'51)
 *                                                   (Astar
 *                                                   (Aabsdata absecblsid
 *                                                   (absecblist v'38))
 *                                                   (Astar
 *                                                   (Aabsdata abstcblsid
 *                                                   (abstcblist v'39))
 *                                                   (Astar
 *                                                   (Aabsdata curtid
 *                                                   (oscurt
 *                                                   (@pair block Int.int v'52
 *                                                   Int.zero)))
 *                                                   (Astar
 *                                                   (AOSEventFreeList v'3)
 *                                                   (Astar 
 *                                                   (AOSQFreeList v'4)
 *                                                   (Astar 
 *                                                   (AOSQFreeBlk v'5)
 *                                                   (Astar
 *                                                   (GAarray OSMapTbl
 *                                                   (Tarray Tint8
 *                                                   (S
 *                                                   (S
 *                                                   (S (S (S (S (S (S O)))))))))
 *                                                   OSMapVallist)
 *                                                   (Astar
 *                                                   (GAarray OSUnMapTbl
 *                                                   (Tarray Tint8
 *                                                 256)
 *                                                   OSUnMapVallist)
 *                                                   (Astar AOSIntNesting
 *                                                   (Astar
 *                                                   (AOSTCBFreeList v'21 v'22)
 *                                                   (Astar
 *                                                   (AOSTime (Vint32 v'18))
 *                                                   (Astar
 *                                                   (Aabsdata ostmid
 *                                                   (ostm v'18))
 *                                                   (Astar AGVars
 *                                                   (Astar atoy_inv'
 *                                                   (Alvarmapsto pevent
 *                                                   (Tptr OS_EVENT)
 *                                                   (Vptr
 *                                                   (@pair block Int.int v'29
 *                                                   Int.zero)))))))))))))))))))))))))))))))))))))))))))
 *      (sseq
 *         (sifthen
 *            (ebinop oeq
 *               (earrayelem (evar OSRdyTbl)
 *                  (efield (ederef (evar OSTCBCur)) OSTCBY))
 *               (econst32 (Int.repr Z0)))
 *            (sassign (evar OSRdyGrp)
 *               (ebinop obitand (evar OSRdyGrp)
 *                  (eunop negation (efield (ederef (evar OSTCBCur)) OSTCBBitY)))))
 *         (sseq
 *            (sassign (efield (ederef (evar OSTCBCur)) OSTCBPrio) (evar prio))
 *            (sseq
 *               (sassign (efield (ederef (evar OSTCBCur)) OSTCBY)
 *                  (ebinop orshift (evar prio)
 *                     (econst32 (Int.repr (Zpos (xI xH))))))
 *               (sseq
 *                  (sassign (efield (ederef (evar OSTCBCur)) OSTCBBitY)
 *                     (earrayelem (evar OSMapTbl)
 *                        (efield (ederef (evar OSTCBCur)) OSTCBY)))
 *                  (sseq
 *                     (sassign (efield (ederef (evar OSTCBCur)) OSTCBX)
 *                        (ebinop obitand (evar prio)
 *                           (econst32 (Int.repr (Zpos (xI (xI xH)))))))
 *                     (sseq
 *                        (sassign (efield (ederef (evar OSTCBCur)) OSTCBBitX)
 *                           (earrayelem (evar OSMapTbl)
 *                              (efield (ederef (evar OSTCBCur)) OSTCBX)))
 *                        (sseq
 *                           (sassign (evar OSRdyGrp)
 *                              (ebinop obitor (evar OSRdyGrp)
 *                                 (efield (ederef (evar OSTCBCur)) OSTCBBitY)))
 *                           (sseq
 *                              (sassign
 *                                 (earrayelem (evar OSRdyTbl)
 *                                    (efield (ederef (evar OSTCBCur)) OSTCBY))
 *                                 (ebinop obitor
 *                                    (earrayelem (evar OSRdyTbl)
 *                                       (efield (ederef (evar OSTCBCur)) OSTCBY))
 *                                    (efield (ederef (evar OSTCBCur)) OSTCBBitX)))
 *                              (sseq
 *                                 (sassign
 *                                    (earrayelem (evar OSTCBPrioTbl)
 *                                       (evar prio))
 *                                    (ecast (evar OSTCBCur) (Tptr OS_TCB)))
 *                                 (sassign
 *                                    (earrayelem (evar OSTCBPrioTbl) (evar pip))
 *                                    (ecast os_mutex.PlaceHolder (Tptr OS_TCB))))))))))))
 *      (    (
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
 * ). *)
Proof.
  intros.
  rewrite intlemma13 in H68.
  hoare forward.
  go.


  rewrite update_nth_val_len_eq.
  auto.

  rewrite len_lt_update_get_eq.
  simpljoin.
  rewrite H86.
  simpl.
  Local Open Scope Z_scope.
  assert (Int.unsigned (x12&ᵢInt.not (Int.shl ($ 1) (x6&ᵢ$ 7))) <=? Byte.max_unsigned = true).

  apply Zle_imp_le_bool.

  change (Byte.max_unsigned) with 255.

  apply le255_and_le255.
  auto.

  rewrite H92.
  auto.
  auto.

  rewrite H86.
  rewrite len_lt_update_get_eq.
  simpl; auto.
  destruct  (Int.eq (x12&ᵢInt.not (Int.shl ($ 1) (x6&ᵢ$ 7))) ($ 0)).
  simpl; intro; tryfalse.
  simpl; intro; tryfalse.
  auto.

  hoare forward.

  (* Ltac mew2 := match goal with
   *                | |- (if _ then true else false) = true => rewrite ifE
   *                | |- (_ <=? _ = true) => apply Zle_imp_le_bool
   *                | |- (_ <= _ ) => apply Zle_bool_imp_le
   *              end. *)
  math simpls.
  
  go.
  (* intro; tryfalse. *)
  (* intro; tryfalse. *)
  (* go. *)
  hoare forward.
  Focus 3.
  clear -H15.
  change Byte.modulus with 256.
  remember (Int.shru x ($ 8)).
  clear Heqi.
  int auto.


  (* start from here *) 
  hoare forward.

  math simpls.

  change Byte.max_unsigned with 255.
  apply postintlemma3.

  hoare forward.
  math simpls.
  change Byte.max_unsigned with 255.
  apply postintlemma3.

  (* rewrite postintlemma4. *)
  (* simpl; intro; tryfalse. *)

  rewrite postintlemma4.
  hoare forward.

  go.

  rewrite H74.
  unfolds; simpl.
  math simpls.
  apply int8ule255.
  auto.
  
  hoare forward.
  math simpls.
  change Byte.max_unsigned with 255.
  apply postintlemma3.
  (* intro; tryfalse. *)

  rewrite H86.
  rewrite H74.
  hoare forward.
  go.
(* ** ac:   Show. *)
  go.
  assert (Int.unsigned x8 <= Byte.max_unsigned).
  apply int8ule255.
  auto.
  clear -H96 H97; omega.
  rewrite H81.
  auto.

  rewrite H81.
  
  hoare forward.

  math simpls.
  apply le255_and_le255.
  auto.
  go.


  assert (Int.unsigned x11 <= Byte.max_unsigned).
  apply int8ule255.
  auto.
  clear -H96 H97; omega.
  assert (Int.unsigned x8 <= Byte.max_unsigned).
  apply int8ule255; auto.
  clear -H96 H97; omega.
  (* intro; tryfalse. *)
  hoare forward.

  go.
  assert (Int.unsigned x11 <= Byte.max_unsigned).
  apply int8ule255; auto.
  clear -H96 H97; omega.

  assert (Int.unsigned x8 <= Byte.max_unsigned).
  apply int8ule255; auto.
  clear -H96 H97; omega.

  rewrite update_nth_val_len_eq.
  auto.
  apply array_type_vallist_match_imp_rule_type_val_match.
  rewrite update_nth_val_len_eq.
  auto.
  apply array_type_vallist_match_hold.
  auto.
  auto.
  unfolds; simpl.
  math simpls.
  apply le255_and_le255; auto.

  go.
  assert (Int.unsigned x11 <= Byte.max_unsigned)%Z.
  apply int8ule255; auto.
  clear -H96 H97; omega.
  assert (Int.unsigned x8 <= Byte.max_unsigned)%Z.
  apply int8ule255; auto.
  clear -H96 H97; omega.

  assert  (length  (update_nth_val (Z.to_nat (Int.unsigned (Int.shru x6 ($ 3)))) v'36
                                   (val_inj (and (Vint32 x12) (Vint32 (Int.not ($ 1<<ᵢ(x6&ᵢ$ 7))))))) = Z.to_nat 8).
  rewrite update_nth_val_len_eq.
  auto.
  
  assert ((Z.to_nat (Int.unsigned (Int.shru (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) ($ 3)))) < length  (update_nth_val (Z.to_nat (Int.unsigned (Int.shru x6 ($ 3)))) v'36
                                                                                                           (val_inj (and (Vint32 x12) (Vint32 (Int.not ($ 1<<ᵢ(x6&ᵢ$ 7))))))))%nat.
  rewrite H92.
  clear -H48.

  remember (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8).
  mauto.

  assert (   array_type_vallist_match Int8u  (update_nth_val (Z.to_nat (Int.unsigned (Int.shru x6 ($ 3)))) v'36
                                                             (val_inj (and (Vint32 x12) (Vint32 (Int.not ($ 1<<ᵢ(x6&ᵢ$ 7))))))) ).
  apply array_type_vallist_match_hold.
  auto.
  auto.
  Local Open Scope Z_scope.
  unfolds; simpl.
Ltac mew2 := match goal with
                 | |- (if _ then true else false) = true => rewrite ifE
                 | |- (_ <=? _ = true) => apply Zle_imp_le_bool
                 | |- (_ <= _ ) => apply Zle_bool_imp_le
               end.

  (* math simpls. *)
  mew2.
  mew2.
  change Byte.max_unsigned with 255.
  apply le255_and_le255.
  auto.
  lets aabb:  array_type_vallist_match_imp_rule_type_val_match H96 H97.
  lets bbaa: ruletypevalmatch8u aabb.
  simpljoin.
  simpl in H98.
  rewrite H98.
  simpl;let H := fresh in  intro H;clear -H;  tryfalse.

  go.

  assert (Int.unsigned x11 <= Byte.max_unsigned)%Z.
  apply int8ule255; auto.
  clear -H96 H97; omega.
  assert (Int.unsigned x8 <= Byte.max_unsigned)%Z.
  apply int8ule255; auto.
  clear -H96 H97; omega.

  (* apply postintlemma3.
   * clear -H48.
   * remember (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8).
   * mauto.
   * 
   * clear -H48.
   * remember (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8).
   * mauto. *)
  (* apply int8ule255.
   * auto.
   * 
   * apply int8ule255.
   * auto. *)
  rewrite update_nth_val_len_eq.
  auto.

  hoare forward.
  mew2; mew2.
  apply postintlemma3.
  clear -H48.
  remember (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8).
  mauto.

  hoare forward.
  eapply forward_rule2.
Local Open Scope list_scope.
  let s := fresh in
  let H := fresh in
  match goal with
    | |- {|_ , _, _,_, _, _|}|- _ {{?P}}?x ′ [_] =ₑ _ {{_}} =>
      match find_lvararray P x with
        | some ?m => idtac
        | none _ =>          
          match find_dom_lenv P with
            | (none _, _) => fail 2
            | (some ?m, Some ?ls) =>
              let ret1 := constr:(var_notin_dom x ls) in
              let ret2 := eval compute in ret1 in
                  match ret2 with
                    | true =>
                      match find_aop P with
                        | none _ => fail 1
                        | some ?n =>
                          match find_gvararray P x with
                            | none _ => fail 3
                            | some ?o =>
                              hoare lifts (n :: m :: o :: nil) pre
                          end
                      end
                    | false => fail
                  end
          end
      end
  end.


  eapply assign_rule_array_g_aop.
  intro.

  split.
  intro.

  exact H93.
  intro.
  exact H93.

  simpl; auto.

  2:symbolic execution.
  intros.
  sep normal; sep eexists.  eapply cast_rv_tptr.
  eapply addrof_gvar_rv.
  apply  astar_l_anotinlenv_intro.
  sep cancel Agvarenv'.
  eauto.

  intro.

  apply astar_l_adomlenv_elim in H93.
  destruct H93.
  clear -H93 H94.
  unfolds in H93.
  unfolds in H94.
  simpljoin.
  destruct x.
  lets adfsadf: H93 OSPlaceHolder t.
  elim adfsadf; intros.
  assert (   ListSet.set_In (OSPlaceHolder, t)
                            ((pevent, OS_EVENT ∗)
                               :: (os_code_defs.x, Int8u)
                               :: (pip, Int8u) :: (prio, Int8u) :: (legal, Int8u):: nil)).
  apply H1.
  eexists; eauto.
  unfolds in H2.
  simpl in H2.
  destruct H2; intros; tryfalse.
  destruct H2; intros; tryfalse.
  destruct H2; intros; tryfalse.
  destruct H2; intros; tryfalse.
  destruct H2; intros; tryfalse.

  unfolds; simpl.
  auto.
  mew2.
  mew2.
  
  change Byte.modulus with 256.
  clear -H15.
  change Byte.max_unsigned with 255.
  remember (Int.shru x ($ 8)).
  omega.

  tauto.
  exact H15.
  constructor.
  do 2 eexists; split; eauto.

  rewrite update_nth_val_len_eq.
  rewrite H51.

  exact H15.
  intro; intros.
  sep eexists.
  sep cancel p_local.
  simpl; auto.

  eapply seporI2.
  intro.
  intros.
  sep auto.
  Set Printing Depth 999.
  (*
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
           (val_inj (and (Vint32 x12) (Vint32 (Int.not ($ 1<<ᵢ(x6&ᵢ$ 7)))))))
        (val_inj
           (or
              (nth_val'
                 (Z.to_nat
                    (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
                 (update_nth_val (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3))) v'36
                    (Vint32 (x12&ᵢInt.not ($ 1<<ᵢ(x6&ᵢ$ 7)))))) 
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
                           :: Vint32 ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)
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
   (EX v : int32, GV OSIntNesting @ Int32u |-> Vint32 v) **
   AOSTCBFreeList v'21 v'22 **
   GV OSTime @ Int32u |-> Vint32 v'18 **
   HTime v'18 **
   (GV OSRunning @ Int8u |-> (V$ 1) **
    (EX v : int32,
     GV OSPrioHighRdy @ Int8u |-> Vint32 v ** [|Int.unsigned v <= 63|]) **
    (EX v : int32, GV OSCtxSwCtr @ Int32u |-> Vint32 v) **
    (EX v : addrval, GV os_code_defs.OSTCBHighRdy @ OS_TCB ∗ |-> Vptr v) **
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
          (V$ 0)) <> Vundef|] 

   *)
  eapply forward_rule2.



(* Lemma MutexPostPIRdyTable2:
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
 *   v'31 : val
 * )(
 *   v'33 v'35 : list vallist
 * )(
 *   v'36 : vallist
 * )(
 *   v'38 : EcbMod.map
 * )(
 *   v'39 : TcbMod.map
 * )(
 *   v'42 : val
 * )(
 *   v'44 : vallist
 * )(
 *   v'46 : val
 * )(
 *   v'47 v'48 v'49 : EcbMod.map
 * )(
 *   w : waitset
 * )(
 *   v'51 : addrval
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
 *   v'29 : block
 * )(
 *   H11 : array_type_vallist_match Int8u v'44
 * )(
 *   H19 : length v'44 = ∘ OS_EVENT_TBL_SIZE
 * )(
 *   x3 : val
 * )(
 *   i : int32
 * )(
 *   H21 : Int.unsigned i <= 255
 * )(
 *   H18 : RL_Tbl_Grp_P v'44 (Vint32 i)
 * )(
 *   H24 : isptr v'46
 * )(
 *   H2 : ECBList_P v'42 (Vptr (v'29, Int.zero)) v'25 v'27 v'47 v'39
 * )(
 *   H14 : id_addrval' (Vptr (v'29, Int.zero)) OSEventTbl OS_EVENT = Some v'23
 * )(
 *   H20 : Int.unsigned ($ OS_EVENT_TYPE_MUTEX) <= 255
 * )(
 *   x : int32
 * )(
 *   H10 : Int.unsigned x <= 65535
 * )(
 *   H15 : Int.unsigned (x >>ᵢ $ 8) < 64
 * )(
 *   H22 : Int.unsigned x <= 65535
 * )(
 *   v'24 v'40 : val
 * )(
 *   v'43 v'45 : TcbMod.map
 * )(
 *   v'52 : block
 * )(
 *   H31 : v'31 <> Vnull
 * )(
 *   H32 : join v'43 v'45 v'39
 * )(
 *   H33 : TCBList_P v'31 v'33 v'36 v'43
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
 *   H5 : R_ECB_ETbl_P (v'29, Int.zero)
 *          (V$ OS_EVENT_TYPE_MUTEX
 *           :: Vint32 i :: Vint32 x :: Vptr (v'52, $ 0) :: x3 :: v'46 :: nil,
 *          v'44) v'39
 * )(
 *   H1 : ECBList_P v'42 Vnull
 *          (v'25 ++
 *           ((V$ OS_EVENT_TYPE_MUTEX
 *             :: Vint32 i :: Vint32 x :: Vptr (v'52, $ 0) :: x3 :: v'46 :: nil,
 *            v'44) :: nil) ++ v'26)
 *          (v'27 ++ (DMutex (Vint32 x) (Vptr (v'52, $ 0)) :: nil) ++ v'28) v'38
 *          v'39
 * )(
 *   H29 : x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 = $ OS_MUTEX_AVAILABLE \/
 *         x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 <> $ OS_MUTEX_AVAILABLE
 * )(
 *   H35 : x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 <> $ OS_MUTEX_AVAILABLE
 * )(
 *   H47 : Int.ltu (x >>ᵢ $ 8) (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = true
 * )(
 *   H48 : Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) < 64
 * )(
 *   H6 : EcbMod.joinsig (v'29, Int.zero)
 *          (absmutexsem (x >>ᵢ $ 8)
 *             (Some (v'52, $ 0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), w) v'48 v'49
 * )(
 *   H4 : Some (v'52, $ 0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = None -> w = nil
 * )(
 *   H9 : forall (tid0 : tid) (opr : int32),
 *        Some (v'52, $ 0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = Some (tid0, opr) ->
 *        Int.ltu (x >>ᵢ $ 8) opr = true /\ Int.unsigned opr < 64
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
 *   backup : RLH_ECBData_P (DMutex (Vint32 x) (Vptr (v'52, $ 0)))
 *              (absmutexsem (x >>ᵢ $ 8)
 *                 (Some (v'52, $ 0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), w)
 * )(
 *   v'32 : val
 * )(
 *   H46 : array_type_vallist_match OS_TCB ∗ v'30
 * )(
 *   H51 : length v'30 = 64%nat
 * )(
 *   H49 : RL_RTbl_PrioTbl_P v'36 v'30 v'51
 * )(
 *   H50 : R_PrioTbl_P v'30 v'39 v'51
 * )(
 *   x1 : val
 * )(
 *   H52 : nth_val (Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) v'30 =
 *         Some x1
 * )(
 *   x0 : val
 * )(
 *   H53 : nth_val (Z.to_nat (Int.unsigned (x >>ᵢ $ 8))) v'30 = Some x0
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
 *   fffa : length OSUnMapVallist = 256%nat ->
 *          (Z.to_nat (Int.unsigned i) < 256)%nat ->
 *          exists x,
 *          Vint32 x2 = Vint32 x /\ true = rule_type_val_match Int8u (Vint32 x)
 * )(
 *   H59 : length OSUnMapVallist = 256%nat
 * )(
 *   H60 : (Z.to_nat (Int.unsigned i) < 256)%nat
 * )(
 *   H61 : nth_val' (Z.to_nat (Int.unsigned i)) OSUnMapVallist = Vint32 x2
 * )(
 *   H62 : true = rule_type_val_match Int8u (Vint32 x2)
 * )(
 *   fffbb : Int.unsigned x2 < 8
 * )(
 *   fffbb2 : (Z.to_nat (Int.unsigned x2) < length v'44)%nat
 * )(
 *   H19'' : length v'44 = Z.to_nat 8
 * )(
 *   x4 : int32
 * )(
 *   H63 : nth_val' (Z.to_nat (Int.unsigned x2)) v'44 = Vint32 x4
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
 *   H68 : val_inj
 *           (bool_and
 *              (val_inj
 *                 (notint
 *                    (val_inj
 *                       (if Int.eq i ($ 0)
 *                        then Some (Vint32 Int.one)
 *                        else Some (Vint32 Int.zero)))))
 *              (val_inj
 *                 (bool_or
 *                    (val_inj
 *                       (if Int.ltu ((x2<<ᵢ$ 3) +ᵢ  x5) (x >>ᵢ $ 8)
 *                        then Some (Vint32 Int.one)
 *                        else Some (Vint32 Int.zero)))
 *                    (val_inj
 *                       (if Int.eq ((x2<<ᵢ$ 3) +ᵢ  x5) (x >>ᵢ $ 8)
 *                        then Some (Vint32 Int.one)
 *                        else Some (Vint32 Int.zero)))))) = 
 *         Vint32 Int.zero \/
 *         val_inj
 *           (bool_and
 *              (val_inj
 *                 (notint
 *                    (val_inj
 *                       (if Int.eq i ($ 0)
 *                        then Some (Vint32 Int.one)
 *                        else Some (Vint32 Int.zero)))))
 *              (val_inj
 *                 (bool_or
 *                    (val_inj
 *                       (if Int.ltu ((x2<<ᵢ$ 3) +ᵢ  x5) (x >>ᵢ $ 8)
 *                        then Some (Vint32 Int.one)
 *                        else Some (Vint32 Int.zero)))
 *                    (val_inj
 *                       (if Int.eq ((x2<<ᵢ$ 3) +ᵢ  x5) (x >>ᵢ $ 8)
 *                        then Some (Vint32 Int.one)
 *                        else Some (Vint32 Int.zero)))))) = Vnull
 * )(
 *   H27 : isptr x7
 * )(
 *   H38 : isptr m
 * )(
 *   x6 x14 : int32
 * )(
 *   H77 : 0 <= Int.unsigned x6
 * )(
 *   H85 : Int.unsigned x6 < 64
 * )(
 *   H82 : x14 = $ OS_STAT_RDY \/
 *         x14 = $ OS_STAT_SEM \/
 *         x14 = $ OS_STAT_Q \/ x14 = $ OS_STAT_MBOX \/ x14 = $ OS_STAT_MUTEX
 * )(
 *   x15 : val
 * )(
 *   H84 : x14 = $ OS_STAT_RDY -> x15 = Vnull
 * )(
 *   H43 : Int.unsigned (x6 >>ᵢ $ 3) <= 255
 * )(
 *   H45 : Int.unsigned ($ 1<<ᵢ(x6 >>ᵢ $ 3)) <= 255
 * )(
 *   H44 : Int.unsigned ($ 1<<ᵢ(x6&ᵢ$ 7)) <= 255
 * )(
 *   H42 : Int.unsigned (x6&ᵢ$ 7) <= 255
 * )(
 *   H70 : TcbJoin (v'52, Int.zero) (x6, t, m) x10 v'45
 * )(
 *   H41 : Int.unsigned x6 <= 255
 * )(
 *   H28 : Int.ltu x6 (x >>ᵢ $ 8) = false
 * )(
 *   H37 : isptr x15
 * )(
 *   H40 : Int.unsigned x14 <= 255
 * )(
 *   last_condition : ProtectWrapper (x14 = $ OS_STAT_RDY /\ i6 = $ 0)
 * )(
 *   H73 : R_TCB_Status_P
 *           (x7
 *            :: v'24
 *               :: x15
 *                  :: m
 *                     :: Vint32 i6
 *                        :: Vint32 x14
 *                           :: Vint32 x6
 *                              :: Vint32 (x6&ᵢ$ 7)
 *                                 :: Vint32 (x6 >>ᵢ $ 3)
 *                                    :: Vint32 ($ 1<<ᵢ(x6&ᵢ$ 7))
 *                                       :: Vint32 ($ 1<<ᵢ(x6 >>ᵢ $ 3)) :: nil)
 *           v'36 (x6, t, m)
 * )(
 *   backup2 : TCBList_P (Vptr (v'52, Int.zero))
 *               ((x7
 *                 :: v'24
 *                    :: x15
 *                       :: m
 *                          :: Vint32 i6
 *                             :: Vint32 x14
 *                                :: Vint32 x6
 *                                   :: Vint32 (x6&ᵢ$ 7)
 *                                      :: Vint32 (x6 >>ᵢ $ 3)
 *                                         :: Vint32 ($ 1<<ᵢ(x6&ᵢ$ 7))
 *                                            :: Vint32 ($ 1<<ᵢ(x6 >>ᵢ $ 3))
 *                                               :: nil) :: v'35) v'36 v'45
 * )(
 *   r1 : Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3) < 8
 * )(
 *   r2 : Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7) < 8
 * )(
 *   r3 : Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3) < 8
 * )(
 *   r4 : Int.unsigned ((x >>ᵢ $ 8)&ᵢ$ 7) < 8
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
 *   r5 : Int.unsigned (x6 >>ᵢ $ 3) < 8
 * )(
 *   r6 : Int.unsigned (x6&ᵢ$ 7) < 8
 * )(
 *   rr1 : (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3)) < length v'36)%nat
 * )(
 *   rr2 : (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)) <
 *          length v'36)%nat
 * )(
 *   rr3 : (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)) <
 *          length v'36)%nat
 * )(
 *   rr4 : (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8)&ᵢ$ 7)) < length v'36)%nat
 * )(
 *   rr5 : (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3)) < length v'36)%nat
 * )(
 *   rr6 : (Z.to_nat (Int.unsigned (x6&ᵢ$ 7)) < length v'36)%nat
 * )(
 *   rrr1 : Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3) < Z.of_nat (length v'36)
 * )(
 *   rrr2 : Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7) <
 *          Z.of_nat (length v'36)
 * )(
 *   rrr3 : Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3) <
 *          Z.of_nat (length v'36)
 * )(
 *   rrr4 : Int.unsigned ((x >>ᵢ $ 8)&ᵢ$ 7) < Z.of_nat (length v'36)
 * )(
 *   rrr5 : Int.unsigned (x6 >>ᵢ $ 3) < Z.of_nat (length v'36)
 * )(
 *   rrr6 : Int.unsigned (x6&ᵢ$ 7) < Z.of_nat (length v'36)
 * )(
 *   HH58 : length v'36 = Z.to_nat 8
 * )(
 *   aa : rule_type_val_match Int8u
 *          (nth_val' (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3))) v'36) =
 *        true
 * )(
 *   aa2 : rule_type_val_match Int8u
 *           (nth_val'
 *              (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
 *              v'36) = true
 * )(
 *   aa3 : rule_type_val_match Int8u
 *           (nth_val' (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3))) v'36) = true
 * )(
 *   x16 : int32
 * )(
 *   H88 : nth_val' (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3))) v'36 =
 *         Vint32 x16
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
 *   H86 : nth_val' (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3))) v'36 = Vint32 x12
 * )(
 *   H89 : Int.unsigned x12 <= 255
 * )(
 *   H92 : x1 = Vptr v'51
 * ),
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
 *    {{( <|| mutexpost (Vptr (v'29, Int.zero) :: nil) ||>  **
 *       A_dom_lenv
 *         ((pevent, OS_EVENT ∗)
 *          :: (os_code_defs.x, Int8u)
 *             :: (pip, Int8u) :: (prio, Int8u) :: (legal, Int8u) :: nil) **
 *       GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
 *         (update_nth_val (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3))) v'36
 *            (val_inj
 *               (and (nth_val' (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3))) v'36)
 *                  (Vint32 (Int.not ($ 1<<ᵢ(x6&ᵢ$ 7))))))) **
 *       LV os_code_defs.x @ Int8u |-> Vint32 ((x2<<ᵢ$ 3) +ᵢ  x5) **
 *       LV legal @ Int8u |-> Vint32 x2 **
 *       PV v'51 @ Int8u |-> v'32 **
 *       Astruct (v'52, Int.zero) OS_TCB_flag
 *         (x7
 *          :: v'24
 *             :: x15
 *                :: m
 *                   :: Vint32 i6
 *                      :: Vint32 x14
 *                         :: Vint32 x6
 *                            :: Vint32 (x6&ᵢ$ 7)
 *                               :: Vint32 (x6 >>ᵢ $ 3)
 *                                  :: Vint32 ($ 1<<ᵢ(x6&ᵢ$ 7))
 *                                     :: Vint32 ($ 1<<ᵢ(x6 >>ᵢ $ 3)) :: nil) **
 *       dllseg x7 (Vptr (v'52, Int.zero)) v'40 Vnull v'35 OS_TCB_flag
 *         (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
 *       GV OSTCBList @ OS_TCB ∗ |-> v'31 **
 *       dllseg v'31 Vnull v'24 (Vptr (v'52, Int.zero)) v'33 OS_TCB_flag
 *         (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
 *       GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (v'52, Int.zero) **
 *       LV prio @ Int8u |-> Vint32 (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) **
 *       LV pip @ Int8u |-> Vint32 (x >>ᵢ $ 8) **
 *       Astruct (v'29, Int.zero) OS_EVENT
 *         (V$ OS_EVENT_TYPE_MUTEX
 *          :: Vint32 i :: Vint32 x :: Vptr (v'52, $ 0) :: x3 :: v'46 :: nil) **
 *       Aarray v'23 (Tarray Int8u ∘ OS_EVENT_TBL_SIZE) v'44 **
 *       Aie false **
 *       Ais nil **
 *       Acs (true :: nil) **
 *       Aisr empisr **
 *       GV OSEventList @ OS_EVENT ∗ |-> v'42 **
 *       evsllseg v'42 (Vptr (v'29, Int.zero)) v'25 v'27 **
 *       evsllseg v'46 Vnull v'26 v'28 **
 *       A_isr_is_prop **
 *       tcbdllflag v'31
 *         (v'33 ++
 *          (x7
 *           :: v'24
 *              :: x15
 *                 :: m
 *                    :: Vint32 i6
 *                       :: Vint32 x14
 *                          :: Vint32 x6
 *                             :: Vint32 (x6&ᵢ$ 7)
 *                                :: Vint32 (x6 >>ᵢ $ 3)
 *                                   :: Vint32 ($ 1<<ᵢ(x6&ᵢ$ 7))
 *                                      :: Vint32 ($ 1<<ᵢ(x6 >>ᵢ $ 3)) :: nil)
 *          :: v'35) **
 *       GV OSRdyGrp @ Int8u |-> Vint32 i7 **
 *       GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64) v'30 **
 *       G& OSPlaceHolder @ Int8u == v'51 **
 *       HECBList v'38 **
 *       HTCBList v'39 **
 *       HCurTCB (v'52, Int.zero) **
 *       p_local OSLInv (v'52, Int.zero) init_lg **
 *       AOSEventFreeList v'3 **
 *       AOSQFreeList v'4 **
 *       AOSQFreeBlk v'5 **
 *       GAarray OSMapTbl (Tarray Int8u 8) OSMapVallist **
 *       GAarray OSUnMapTbl (Tarray Int8u 256) OSUnMapVallist **
 *       AOSIntNesting **
 *       AOSTCBFreeList v'21 v'22 **
 *       AOSTime (Vint32 v'18) **
 *       HTime v'18 **
 *       AGVars ** atoy_inv' ** LV pevent @ OS_EVENT ∗ |-> Vptr (v'29, Int.zero)) **
 *      [|val_inj
 *          (val_eq
 *             (nth_val' (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3)))
 *                (update_nth_val (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3))) v'36
 *                   (val_inj
 *                      (and
 *                         (nth_val' (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3))) v'36)
 *                         (Vint32 (Int.not ($ 1<<ᵢ(x6&ᵢ$ 7)))))))) 
 *             (V$ 0)) = Vint32 Int.zero \/
 *        val_inj
 *          (val_eq
 *             (nth_val' (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3)))
 *                (update_nth_val (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3))) v'36
 *                   (val_inj
 *                      (and
 *                         (nth_val' (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3))) v'36)
 *                         (Vint32 (Int.not ($ 1<<ᵢ(x6&ᵢ$ 7)))))))) 
 *             (V$ 0)) = Vnull|]}} OSTCBCur ′ → OSTCBPrio =ₑ prio ′;ₛ
 *    OSTCBCur ′ → OSTCBY =ₑ prio ′ ≫ ′ 3;ₛ
 *    OSTCBCur ′ → OSTCBBitY =ₑ OSMapTbl ′ [OSTCBCur ′ → OSTCBY];ₛ
 *    OSTCBCur ′ → OSTCBX =ₑ prio ′ &ₑ ′ 7;ₛ
 *    OSTCBCur ′ → OSTCBBitX =ₑ OSMapTbl ′ [OSTCBCur ′ → OSTCBX];ₛ
 *    OSRdyGrp ′ =ₑ OSRdyGrp ′ |ₑ OSTCBCur ′ → OSTCBBitY;ₛ
 *    OSRdyTbl ′ [OSTCBCur ′ → OSTCBY] =ₑ
 *    OSRdyTbl ′ [OSTCBCur ′ → OSTCBY] |ₑ OSTCBCur ′ → OSTCBBitX;ₛ
 *    OSTCBPrioTbl ′ [prio ′] =ₑ 〈 OS_TCB ∗ 〉 OSTCBCur ′;ₛ
 *    OSTCBPrioTbl ′ [pip ′] =ₑ 〈 OS_TCB ∗ 〉 os_mutex.PlaceHolder {{
 *    Afalse}}.
 * Admitted. *)

  Require Import OSMutexPostPart2_1.

  
  eapply MutexPostPIRdyTable2; eauto.
(* ** ac:   Show. *)
  
  (* rewrite intlemma13 .
   * exact H68.
   * clear -H15.
   * change Byte.modulus with 256. *)
  (* ur_rewriter. *)
  (* omega. *)
  eapply seporI2'.
  intro.
  intros.
  sep auto.

Qed.
