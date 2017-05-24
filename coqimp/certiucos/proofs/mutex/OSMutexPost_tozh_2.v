Require Import ucos_include.
Require Import OSMutex_common.
Require Import os_ucos_h.
Require Import mutex_absop_rules.
Require Import sep_lemmas_ext.
Require Import symbolic_lemmas.
Require Import OSTimeDlyPure.
Require Import OSQPostPure.
Require Import tcblist_setnode_lemmas.
Require Import OSMutexPostPure.

Local Open Scope code_scope.
Local Open Scope nat_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.
Local Open Scope list_scope.

Lemma mutex_post_no_pi_part2 :
  forall
(  v'  v'0  v'1  v'2 : val )
(  v'3  v'4  v'5 : list vallist )
(  v'6 : list EventData )
(  v'7 : list os_inv.EventCtr )
(  v'8 : vallist )
(  v'9  v'10 : val )
(  v'11 : list vallist )
(  v'12 : vallist )
(  v'13 : list vallist )
(  v'14 : vallist )
(  v'15 : val )
(  v'16 : EcbMod.map )
(  v'17 : TcbMod.map )
(  v'18 : int32 )
(  v'19 : addrval )
(  v'21 : val )
(  v'22 : list vallist )
(  v'25  v'26 : list os_inv.EventCtr )
(  v'27  v'28 : list EventData )
(  v'30 : vallist )
(  v'31 : val )
(  v'33  v'35 : list vallist )
(  v'36 : vallist )
(  v'38 : EcbMod.map )
(  v'39 : TcbMod.map )
(  v'42 : val )
(  v'44 : vallist )
(  v'46 : val )
(  v'47  v'48  v'49 : EcbMod.map )
(  w : waitset )
(  v'51 : addrval )
(  H3 : ECBList_P v'46 Vnull v'26 v'28 v'48 v'39 )
(  H17 : EcbMod.join v'47 v'49 v'38 )
(  H12 : length v'25 = length v'27 )
(  H16 : isptr v'46 )
(  v'23 : addrval )
(  v'29 : block )
(  H11 : array_type_vallist_match Int8u v'44 )
(  H19 : length v'44 = ∘ OS_EVENT_TBL_SIZE )
(  x3 : val )
(  i : int32 )
(  H21 : Int.unsigned i <= 255 )
(  H18 : RL_Tbl_Grp_P v'44 (Vint32 i) )
(  H24 : isptr v'46 )
(  H2 : ECBList_P v'42 (Vptr (v'29, Int.zero)) v'25 v'27 v'47 v'39 )
(  H14 : id_addrval' (Vptr (v'29, Int.zero)) OSEventTbl OS_EVENT = Some v'23 )
(  H20 : Int.unsigned ($ OS_EVENT_TYPE_MUTEX) <= 255 )
(  x : int32 )
(  H10 : Int.unsigned x <= 65535 )
(  H15 : Int.unsigned (x >>ᵢ $ 8) < 64 )
(  H22 : Int.unsigned x <= 65535 )
(  v'24  v'40 : val )
(  v'43  v'45 : TcbMod.map )
(  v'52 : block )
(  H31 : v'31 <> Vnull )
(  H32 : join v'43 v'45 v'39 )
(  H33 : TCBList_P v'31 v'33 v'36 v'43 )
(  H30 : Vptr (v'52, Int.zero) <> Vnull )
(  H36 : isptr v'24 )
(  x7 : val )
(  x10 : TcbMod.map )
(  m : msg )
(  H72 : TCBList_P x7 v'35 v'36 x10 )
(  H : RH_TCBList_ECBList_P v'16 v'17 (v'52, Int.zero) )
(  H0 : RH_CurTCB (v'52, Int.zero) v'17 )
(  H7 : RH_TCBList_ECBList_P v'38 v'39 (v'52, Int.zero) )
(  H8 : RH_CurTCB (v'52, Int.zero) v'39 )
(  H23 : isptr (Vptr (v'52, $ 0)) )
(  H5 : R_ECB_ETbl_P (v'29, Int.zero)
         (V$ OS_EVENT_TYPE_MUTEX
          :: Vint32 i :: Vint32 x :: Vptr (v'52, $ 0) :: x3 :: v'46 :: nil, v'44) v'39 )
(  H1 : ECBList_P v'42 Vnull
         (v'25 ++
          ((V$ OS_EVENT_TYPE_MUTEX
            :: Vint32 i :: Vint32 x :: Vptr (v'52, $ 0) :: x3 :: v'46 :: nil, v'44)
           :: nil) ++ v'26)
         (v'27 ++ (DMutex (Vint32 x) (Vptr (v'52, $ 0)) :: nil) ++ v'28) v'38 v'39 )
(  H29 : x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 = $ OS_MUTEX_AVAILABLE \/
        x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 <> $ OS_MUTEX_AVAILABLE )
(  H35 : x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 <> $ OS_MUTEX_AVAILABLE )
(  H47 : Int.ltu (x >>ᵢ $ 8) (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = true )
(  H48 : Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) < 64 )
(  H6 : EcbMod.joinsig (v'29, Int.zero)
         (absmutexsem (x >>ᵢ $ 8) (Some (v'52, $ 0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), w)
         v'48 v'49 )
(  H4 : Some (v'52, $ 0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = None -> w = nil )
(  H9 : forall (tid0 : tid) (opr : int32),
       Some (v'52, $ 0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = Some (tid0, opr) ->
       Int.ltu (x >>ᵢ $ 8) opr = true /\ Int.unsigned opr < 64 )
(  H13 : w <> nil -> Some (v'52, $ 0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) <> None )
(  H25 : x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 = $ OS_MUTEX_AVAILABLE ->
        Some (v'52, $ 0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = None /\
        Vptr (v'52, $ 0) = Vnull )
(  H26 : x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 <> $ OS_MUTEX_AVAILABLE ->
        exists tid,
        Vptr (v'52, $ 0) = Vptr tid /\
        Some (v'52, $ 0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) =
        Some (tid, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) )
(  backup : RLH_ECBData_P (DMutex (Vint32 x) (Vptr (v'52, $ 0)))
             (absmutexsem (x >>ᵢ $ 8) (Some (v'52, $ 0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)),
             w) )
(  v'32 : val )
(  H46 : array_type_vallist_match OS_TCB ∗ v'30 )
(  H51 : length v'30 = 64%nat )
(  H49 : RL_RTbl_PrioTbl_P v'36 v'30 v'51 )
(  H50 : R_PrioTbl_P v'30 v'39 v'51 )
(  x1 : val )
(  H52 : nth_val (Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) v'30 = Some x1 )
(  x0 : val )
(  H53 : nth_val (Z.to_nat (Int.unsigned (x >>ᵢ $ 8))) v'30 = Some x0 )
(  H54 : array_type_vallist_match Int8u v'36 )
(  H58 : length v'36 = ∘ OS_RDY_TBL_SIZE )
(  i7 : int32 )
(  H55 : Int.unsigned i7 <= 255 )
(  H57 : prio_in_tbl ($ OS_IDLE_PRIO) v'36 )
(  H56 : RL_Tbl_Grp_P v'36 (Vint32 i7) )
(  x2 : int32 )
(  fffa : length OSUnMapVallist = 256%nat ->
         (Z.to_nat (Int.unsigned i) < 256)%nat ->
         exists x, Vint32 x2 = Vint32 x /\ true = rule_type_val_match Int8u (Vint32 x) )
(  H59 : length OSUnMapVallist = 256%nat )
(  H60 : (Z.to_nat (Int.unsigned i) < 256)%nat )
(  H61 : nth_val' (Z.to_nat (Int.unsigned i)) OSUnMapVallist = Vint32 x2 )
(  H62 : true = rule_type_val_match Int8u (Vint32 x2) )
(  fffbb : Int.unsigned x2 < 8 )
(  fffbb2 : (Z.to_nat (Int.unsigned x2) < length v'44)%nat )
(  H19'' : length v'44 = Z.to_nat 8 )
(  x4 : int32 )
(  H63 : nth_val' (Z.to_nat (Int.unsigned x2)) v'44 = Vint32 x4 )
(  H64 : Int.unsigned x4 <= 255 )
(  H65 : (Z.to_nat (Int.unsigned x4) < length OSUnMapVallist)%nat )
(  x5 : int32 )
(  H66 : nth_val' (Z.to_nat (Int.unsigned x4)) OSUnMapVallist = Vint32 x5 )
(  H67 : Int.unsigned x5 <= 255 )
(  ttfasd : Int.unsigned x5 < 8 )
(  H68 : val_inj
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
                      (if Int.ltu ((x2<<ᵢ$ 3) +ᵢ  x5) (x >>ᵢ $ 8)
                       then Some (Vint32 Int.one)
                       else Some (Vint32 Int.zero)))
                   (val_inj
                      (if Int.eq ((x2<<ᵢ$ 3) +ᵢ  x5) (x >>ᵢ $ 8)
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
                      (if Int.ltu ((x2<<ᵢ$ 3) +ᵢ  x5) (x >>ᵢ $ 8)
                       then Some (Vint32 Int.one)
                       else Some (Vint32 Int.zero)))
                   (val_inj
                      (if Int.eq ((x2<<ᵢ$ 3) +ᵢ  x5) (x >>ᵢ $ 8)
                       then Some (Vint32 Int.one)
                       else Some (Vint32 Int.zero)))))) = Vnull )
(  H27 : isptr x7 )
(  H38 : isptr m )
(  x6 : int32 )
(  H77 : 0 <= Int.unsigned x6 )
(  H85 : Int.unsigned x6 < 64 )
(  x15 : val )
(  H43 : Int.unsigned (x6 >>ᵢ $ 3) <= 255 )
(  H45 : Int.unsigned ($ 1<<ᵢ(x6 >>ᵢ $ 3)) <= 255 )
(  H44 : Int.unsigned ($ 1<<ᵢ(x6&ᵢ$ 7)) <= 255 )
(  H42 : Int.unsigned (x6&ᵢ$ 7) <= 255 )
(  H41 : Int.unsigned x6 <= 255 )
(  H28 : Int.ltu x6 (x >>ᵢ $ 8) = false )
(  H37 : isptr x15 )
(  r1 : Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3) < 8 )
(  r2 : Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7) < 8 )
(  r3 : Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3) < 8 )
(  r4 : Int.unsigned ((x >>ᵢ $ 8)&ᵢ$ 7) < 8 )
(  H34 : array_type_vallist_match Int8u OSMapVallist )
(  H69 : length OSMapVallist = 8%nat )
(  H71 : (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)) < 8)%nat )
(  x8 : int32 )
(  H74 : nth_val' (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
          OSMapVallist = Vint32 x8 )
(  H75 : true = rule_type_val_match Int8u (Vint32 x8) )
(  H76 : (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)) < 8)%nat )
(  x9 : int32 )
(  H78 : nth_val' (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)))
          OSMapVallist = Vint32 x9 )
(  H79 : true = rule_type_val_match Int8u (Vint32 x9) )
(  H80 : (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)) < 8)%nat )
(  x11 : int32 )
(  H81 : nth_val' (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)))
          OSMapVallist = Vint32 x11 )
(  H83 : true = rule_type_val_match Int8u (Vint32 x11) )
(  r5 : Int.unsigned (x6 >>ᵢ $ 3) < 8 )
(  r6 : Int.unsigned (x6&ᵢ$ 7) < 8 )
(  rr1 : (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3)) < length v'36)%nat )
(  rr2 : (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)) < length v'36)%nat )
(  rr3 : (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)) < length v'36)%nat )
(  rr4 : (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8)&ᵢ$ 7)) < length v'36)%nat )
(  rr5 : (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3)) < length v'36)%nat )
(  rr6 : (Z.to_nat (Int.unsigned (x6&ᵢ$ 7)) < length v'36)%nat )
(  rrr1 : Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3) < Z.of_nat (length v'36) )
(  rrr2 : Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7) < Z.of_nat (length v'36) )
(  rrr3 : Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3) < Z.of_nat (length v'36) )
(  rrr4 : Int.unsigned ((x >>ᵢ $ 8)&ᵢ$ 7) < Z.of_nat (length v'36) )
(  rrr5 : Int.unsigned (x6 >>ᵢ $ 3) < Z.of_nat (length v'36) )
(  rrr6 : Int.unsigned (x6&ᵢ$ 7) < Z.of_nat (length v'36) )
(  HH58 : length v'36 = Z.to_nat 8 )
(  aa : rule_type_val_match Int8u 
         (nth_val' (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3))) v'36) = true )
(  aa2 : rule_type_val_match Int8u
          (nth_val' (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
             v'36) = true )
(  aa3 : rule_type_val_match Int8u
          (nth_val' (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3))) v'36) = true )
(  x16 : int32 )
(  H88 : nth_val' (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3))) v'36 = Vint32 x16 )
(  H91 : Int.unsigned x16 <= 255 )
(  x13 : int32 )
(  H87 : nth_val' (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3))) v'36 =
        Vint32 x13 )
(  H90 : Int.unsigned x13 <= 255 )
(  x12 : int32 )
(  H86 : nth_val' (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3))) v'36 = Vint32 x12 )
(  H89 : Int.unsigned x12 <= 255 )
(  H92 : Int.unsigned (x >>ᵢ $ 8) < Int.unsigned ($ Byte.modulus) )
(  H70 : TcbJoin (v'52, Int.zero) (x6, rdy, m) x10 v'45 )
(  H82 : $ OS_STAT_RDY = $ OS_STAT_RDY \/
        $ OS_STAT_RDY = $ OS_STAT_SEM \/
        $ OS_STAT_RDY = $ OS_STAT_Q \/
        $ OS_STAT_RDY = $ OS_STAT_MBOX \/ $ OS_STAT_RDY = $ OS_STAT_MUTEX )
(  H84 : $ OS_STAT_RDY = $ OS_STAT_RDY -> x15 = Vnull )
(  H40 : Int.unsigned ($ OS_STAT_RDY) <= 255 )
(  H39 : Int.unsigned ($ 0) <= 65535 )
(  backup2 : TCBList_P (Vptr (v'52, Int.zero))
              ((x7
                :: v'24
                   :: x15
                      :: m
                         :: V$ 0
                            :: V$ OS_STAT_RDY
                               :: Vint32 x6
                                  :: Vint32 (x6&ᵢ$ 7)
                                     :: Vint32 (x6 >>ᵢ $ 3)
                                        :: Vint32 ($ 1<<ᵢ(x6&ᵢ$ 7))
                                           :: Vint32 ($ 1<<ᵢ(x6 >>ᵢ $ 3)) :: nil)
               :: v'35) v'36 v'45 )
(  H73 : R_TCB_Status_P
          (x7
           :: v'24
              :: x15
                 :: m
                    :: V$ 0
                       :: V$ OS_STAT_RDY
                          :: Vint32 x6
                             :: Vint32 (x6&ᵢ$ 7)
                                :: Vint32 (x6 >>ᵢ $ 3)
                                   :: Vint32 ($ 1<<ᵢ(x6&ᵢ$ 7))
                                      :: Vint32 ($ 1<<ᵢ(x6 >>ᵢ $ 3)) :: nil) v'36
          (x6, rdy, m) ),
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
   {{Afalse **
     [|val_inj
         (notint
            (val_inj
               (if Int.eq i ($ 0)
                then Some (Vint32 Int.one)
                else Some (Vint32 Int.zero)))) <> Vint32 Int.zero /\
       val_inj
         (notint
            (val_inj
               (if Int.eq i ($ 0)
                then Some (Vint32 Int.one)
                else Some (Vint32 Int.zero)))) <> Vnull /\
       val_inj
         (notint
            (val_inj
               (if Int.eq i ($ 0)
                then Some (Vint32 Int.one)
                else Some (Vint32 Int.zero)))) <> Vundef|] \\//
     ( <|| mutexpost (Vptr (v'29, Int.zero) :: nil) ||>  **
      LV os_code_defs.x @ Int8u |-> Vint32 ((x2<<ᵢ$ 3) +ᵢ  x5) **
      LV legal @ Int8u |-> Vint32 x2 **
      PV v'51 @ Int8u |-> v'32 **
      Astruct (v'52, Int.zero) OS_TCB_flag
        (x7
         :: v'24
            :: x15
               :: m
                  :: V$ 0
                     :: V$ OS_STAT_RDY
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
                   :: V$ 0
                      :: V$ OS_STAT_RDY
                         :: Vint32 x6
                            :: Vint32 (x6&ᵢ$ 7)
                               :: Vint32 (x6 >>ᵢ $ 3)
                                  :: Vint32 ($ 1<<ᵢ(x6&ᵢ$ 7))
                                     :: Vint32 ($ 1<<ᵢ(x6 >>ᵢ $ 3)) :: nil) :: v'35) **
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
            :: (pip, Int8u) :: (prio, Int8u) :: (legal, Int8u) :: nil) **
      [|val_inj
          (if Int.eq x6 (x >>ᵢ $ 8)
           then Some (Vint32 Int.one)
           else Some (Vint32 Int.zero)) = Vint32 Int.zero \/
        val_inj
          (if Int.eq x6 (x >>ᵢ $ 8)
           then Some (Vint32 Int.one)
           else Some (Vint32 Int.zero)) = Vnull|]) **
     [|val_inj
         (notint
            (val_inj
               (if Int.eq i ($ 0)
                then Some (Vint32 Int.one)
                else Some (Vint32 Int.zero)))) = Vint32 Int.zero \/
       val_inj
         (notint
            (val_inj
               (if Int.eq i ($ 0)
                then Some (Vint32 Int.one)
                else Some (Vint32 Int.zero)))) = Vnull|]}} 
   pevent ′ → OSEventCnt =ₑ pevent ′ → OSEventCnt |ₑ ′ OS_MUTEX_AVAILABLE;ₛ
   pevent ′ → OSEventPtr =ₑ NULL;ₛ
   EXIT_CRITICAL;ₛ
   RETURN ′ OS_NO_ERR {{Afalse}}.
Proof.
  intros.
  Set Printing Depth 999.
  hoare forward.

  
  (*pevent ′ → OSEventCnt =ₑ pevent ′ → OSEventCnt |ₑ ′ OS_MUTEX_AVAILABLE;ₛ*)
  hoare forward.
  go.

  (*pevent ′ → OSEventPtr =ₑ NULL;ₛ*)
  hoare forward.

  (*high level step*)
  hoare_split_pure_all.
  assert (i = ($ 0)).
  clear - H94.
  destruct H94;
    destruct (Int.eq i ($ 0)) eqn : eq1; simpl; tryfalse.
  eapply inteqeq; auto.
  lets Hx: post_exwt_succ_pre_mutex' H95 H50 H18 H5 H7; auto.
  lets Hx1: Hx H17 H6; clear Hx.
  assert (Int.eq x6 (x >>ᵢ $ 8) = false).
  clear - H93.
  destruct H93;
    destruct (Int.eq x6 (x >>ᵢ $ 8)) eqn : eq1; simpl; tryfalse.
  auto.
  substs.
  
  hoare abscsq.
  apply noabs_oslinv.
  eapply absinfer_mutexpost_nowt_no_return_prio_succ.
  go.
  eapply EcbMod.join_get_r; eauto.
  unfold EcbMod.joinsig in H6.
  eapply EcbMod.join_get_l; eauto.
  eapply EcbMod.get_sig_some.
  
  eapply TcbMod.join_get_r; eauto.
  unfold TcbJoin in H70.
  eapply TcbMod.join_get_l; eauto.
  eapply TcbMod.get_sig_some.
  auto.
  eauto.

  (*EXIT_CRITICAL;ₛ*)
(*  lets Hx: ecblist_ecbmod_get_mutex' H12 H10 H11 H8 H19 H7 H18 H1. *)
  hoare forward prim.
  unfold AECBList.
  unfold AOSMapTbl.
  unfold AOSUnMapTbl.
  unfold AOSTCBPrioTbl.
  unfold AOSTCBList.
  unfold AOSRdyTbl.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  unfold AOSRdyGrp.
  sep normal.
  do 6 eexists.
  sep cancel OSTCBList.
  sep cancel OSTCBCur.
  sep cancel OSEventList.
  sep cancel OSMapTbl.
  sep cancel OSUnMapTbl.
  sep cancel OSTCBPrioTbl.
  sep cancel OSPlaceHolder.
  sep cancel OSRdyGrp.
  sep cancel OSRdyTbl.
  sep cancel 5%nat 7%nat.
  instantiate (6
               :=
                 (v'25 ++
                       ((V$ OS_EVENT_TYPE_MUTEX
              :: V$ 0 :: Vint32 (Int.or x ($ OS_MUTEX_AVAILABLE)) :: Vnull :: x3 :: v'46 :: nil,
           v'44) :: nil) ++ v'26)
              ).
  sep split; eauto.
  unfold tcbdllseg.
  sep cancel 7%nat 1%nat.
  unfold dllseg; fold dllseg.
  unfold node.
  sep normal.
  do 2 eexists.
  sep split; eauto.
  do 2 sep cancel 5%nat 1%nat.
  eapply evsllseg_compose; eauto.
  unfolds; simpl; eauto.
  instantiate (5 := DMutex (Vint32 (Int.or x ($ OS_MUTEX_AVAILABLE))) Vnull).
  unfold AEventNode.
  unfold AOSEvent.
  unfold AEventData.
  unfold AOSEventTbl.
  unfold node.
  sep normal.
  do 3 eexists.
  sep split; eauto.
  sep cancel 2%nat 1%nat.
  do 3 sep cancel 6%nat 1%nat.
  sep lift 6%nat in H93.
  eapply tcbdllflag_hold.
  eapply tcbdllflag_hold_middle.
  instantiate (1 :=(x7
               :: v'24
                  :: x15
                     :: m
                        :: V$ 0
                           :: V$ OS_STAT_RDY
                              :: Vint32 x6
                                 :: Vint32 (x6&ᵢ$ 7)
                                    :: Vint32 (x6 >>ᵢ $ 3)
                                       :: Vint32 ($ 1<<ᵢ(x6&ᵢ$ 7))
                                          :: Vint32 ($ 1<<ᵢ(x6 >>ᵢ $ 3)) :: nil) ).
  unfolds; simpl.
  unfold V_OSTCBNext, V_OSTCBflag; simpl.
  auto.
  sep cancel tcbdllflag.
  exact H95.
  split; auto.
  simpl.
  splits; eauto.
  clear - H22.
  rewrite Zle_imp_le_bool; auto.
  eapply int_auxxx; eauto.
  eapply isptr_zh; auto.
  unfolds; simpl; auto.
  split; auto.
  go.
  clear - H55.
  simpl.
  rewrite Zle_imp_le_bool; auto.
  eapply ecblistp_hold; eauto.
  sep lift 11%nat in H95.
  eapply evsllseg_aux; eauto.
  eapply mutex_rh_tcblist_ecblist_p_hold; eauto.
  eapply EcbMod.join_get_r; eauto.
  unfold EcbMod.joinsig in H6.
  eapply EcbMod.join_get_l; eauto.
  eapply EcbMod.get_sig_some.
  go.

  (*RETURN ′ OS_NO_ERR*)
  hoare forward.
Qed.
