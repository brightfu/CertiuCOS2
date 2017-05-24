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

Lemma tcbjoin_get_exists :
  forall (tcbls:TcbMod.map) a x,
    get tcbls a = Some x ->
    exists tcbls',
      TcbJoin a x tcbls' tcbls.
Proof.
  intros.
  unfold TcbJoin.
  exists (minus tcbls (sig a x)).
  unfold join, minus, sig; simpl.
  unfold get in H; simpl in H.
  unfold TcbMod.join; intro.
  destruct (tidspec.beq a a0) eqn : eq1.
  lets Hx: tidspec.beq_true_eq eq1; substs.
  rewrite TcbMod.get_sig_some.
  rewrite TcbMod.minus_sem.
  rewrite TcbMod.get_sig_some.
  rewrite H; auto.
  lets Hx: tidspec.beq_false_neq eq1.
  rewrite TcbMod.minus_sem.
  rewrite TcbMod.get_sig_none; auto.
  destruct (TcbMod.get tcbls a0); auto.
Qed.

Lemma OSMapVallist_bound :
  forall n (i:int32),
    (n < 8)%nat -> exists i, nth_val' n OSMapVallist = Vint32 i /\ (Int.unsigned i) <= 128. 
Proof.
  intros.
  destruct n.
  simpl; exists ($1); split; mauto.
  destruct n.
  simpl; exists ($2); split; mauto.
  destruct n.
  simpl; exists ($4); split; mauto.
  destruct n.
  simpl; exists ($8); split; mauto.
  destruct n.
  simpl; exists ($16); split; mauto.
  destruct n.
  simpl; exists ($32); split; mauto.
  destruct n.
  simpl; exists ($64); split; mauto.
  destruct n.
  simpl; exists ($128); split; mauto.
  omega.
Qed.


Lemma mutex_post_no_pi_part1 :
  forall 
   ( v'  v'0  v'1  v'2 : val)
(v'3  v'4  v'5 : list vallist )
(  v'6 : list EventData)
(  v'7 : list os_inv.EventCtr)
(  v'8 : vallist)
(  v'9  v'10 : val)
(  v'11 : list vallist)
(  v'12 : vallist)
(  v'13 : list vallist)
(  v'14 : vallist)
(  v'15 : val)
(  v'16 : EcbMod.map)
(  v'17 : TcbMod.map)
(  v'18 : int32)
(  v'19 : addrval)
(  v'21 : val)
(  v'22 : list vallist)
(  v'25  v'26 : list os_inv.EventCtr)
(  v'27  v'28 : list EventData)
(  v'33  v'35 : list vallist)
(  v'38 : EcbMod.map)
(  v'42  v'46 : val)
(  v'47  v'48  v'49 : EcbMod.map)
(  w : waitset)
(  H17 : EcbMod.join v'47 v'49 v'38)
(  H12 : length v'25 = length v'27)
(  H16 : isptr v'46)
(  v'23 : addrval)
(  x3 : val)
(  H24 : isptr v'46)
(  H20 : Int.unsigned ($ OS_EVENT_TYPE_MUTEX) <= 255)
(  x : int32)
(  H10 : Int.unsigned x <= 65535)
(  H15 : Int.unsigned (x >>ᵢ $ 8) < 64)
(  H22 : Int.unsigned x <= 65535)
(  v'24 : val)
(  v'43  v'45 : TcbMod.map)
(  v'52 : block)
(  H30 : Vptr (v'52, Int.zero) <> Vnull)
(  H36 : isptr v'24)
(  x7 : val)
(  x10 : TcbMod.map)
(  m : msg)
(  H : RH_TCBList_ECBList_P v'16 v'17 (v'52, Int.zero))
(  H0 : RH_CurTCB (v'52, Int.zero) v'17)
(  H23 : isptr (Vptr (v'52, $ 0)))
(  H29 : x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 = $ OS_MUTEX_AVAILABLE \/
        x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 <> $ OS_MUTEX_AVAILABLE ) 
(  H35 : x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 <> $ OS_MUTEX_AVAILABLE)
(  H47 : Int.ltu (x >>ᵢ $ 8) (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = true)
(  H48 : Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) < 64)
(  H4 : Some (v'52, $ 0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = None -> w = nil)
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
             (absmutexsem (x >>ᵢ $ 8)
                (Some (v'52, $ 0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), w) )
(  v'32  x1  x0 : val )
(  i7 : int32)
(  H55 : Int.unsigned i7 <= 255)
(  x2 : int32)
(  H59 : length OSUnMapVallist = 256%nat)
(  H62 : true = rule_type_val_match Int8u (Vint32 x2))
(  fffbb : Int.unsigned x2 < 8)
(  x4 : int32)
(  H64 : Int.unsigned x4 <= 255)
(  H65 : (Z.to_nat (Int.unsigned x4) < length OSUnMapVallist)%nat)
(  x5 : int32)
(  H66 : nth_val' (Z.to_nat (Int.unsigned x4)) OSUnMapVallist = Vint32 x5)
(  H67 : Int.unsigned x5 <= 255)
(  ttfasd : Int.unsigned x5 < 8)
(  H27 : isptr x7)
(  H38 : isptr m)
(  x6 : int32)
(  H77 : 0 <= Int.unsigned x6)
(  H85 : Int.unsigned x6 < 64)
(  x15 : val)
(  H43 : Int.unsigned (x6 >>ᵢ $ 3) <= 255)
(  H45 : Int.unsigned ($ 1<<ᵢ(x6 >>ᵢ $ 3)) <= 255)
(  H44 : Int.unsigned ($ 1<<ᵢ(x6&ᵢ$ 7)) <= 255)
(  H42 : Int.unsigned (x6&ᵢ$ 7) <= 255)
(  H41 : Int.unsigned x6 <= 255)
(  H28 : Int.ltu x6 (x >>ᵢ $ 8) = false)
(  H37 : isptr x15)
(  r1 : Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3) < 8)
(  r2 : Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7) < 8)
(  r3 : Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3) < 8)
(  r4 : Int.unsigned ((x >>ᵢ $ 8)&ᵢ$ 7) < 8)
(  H34 : array_type_vallist_match Int8u OSMapVallist)
(  H69 : length OSMapVallist = 8%nat)
(  H71 : (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)) <
         8)%nat )
(  x8 : int32 )
(  H74 : nth_val'
          (Z.to_nat
             (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
          OSMapVallist = Vint32 x8 )
(  H75 : true = rule_type_val_match Int8u (Vint32 x8))
(  H76 : (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)) < 8)%nat)
(  x9 : int32)
(  H78 : nth_val'
          (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)))
          OSMapVallist = Vint32 x9 )
(  H79 : true = rule_type_val_match Int8u (Vint32 x9))
(  H80 : (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)) < 8)%nat)
(  x11 : int32)
(  H81 : nth_val'
          (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)))
          OSMapVallist = Vint32 x11)
(  H83 : true = rule_type_val_match Int8u (Vint32 x11))
(  r5 : Int.unsigned (x6 >>ᵢ $ 3) < 8)
(  r6 : Int.unsigned (x6&ᵢ$ 7) < 8)
(  x16 : int32)
(  H91 : Int.unsigned x16 <= 255)
(  x13 : int32)
(  H90 : Int.unsigned x13 <= 255)
(  x12 : int32)
(  H89 : Int.unsigned x12 <= 255)
(  H92 : Int.unsigned (x >>ᵢ $ 8) < Int.unsigned ($ Byte.modulus))
(  H70 : TcbJoin (v'52, Int.zero) (x6, rdy, m) x10 v'45)
(  H82 : $ OS_STAT_RDY = $ OS_STAT_RDY \/
        $ OS_STAT_RDY = $ OS_STAT_SEM \/
        $ OS_STAT_RDY = $ OS_STAT_Q \/
        $ OS_STAT_RDY = $ OS_STAT_MBOX \/
        $ OS_STAT_RDY = $ OS_STAT_MUTEX )
(  H84 : $ OS_STAT_RDY = $ OS_STAT_RDY -> x15 = Vnull)
(  H40 : Int.unsigned ($ OS_STAT_RDY) <= 255)
(  H39 : Int.unsigned ($ 0) <= 65535)
(  H93 : val_inj
          (if Int.eq x6 (x >>ᵢ $ 8)
           then Some (Vint32 Int.one)
           else Some (Vint32 Int.zero)) = Vint32 Int.zero \/
        val_inj
          (if Int.eq x6 (x >>ᵢ $ 8)
           then Some (Vint32 Int.one)
           else Some (Vint32 Int.zero)) = Vnull )
(  v'34 : addrval)
(  v'37 : TcbMod.map)
(  v'53 : list val)
(  v'54 : vallist)
(  v'57 : val)
(  v'58  v'59 : int32)
(  v'60 : vallist)
(  v'67  v'69 : val)
(  v'73  v'74  v'75  v'76  v'77 : int32)
(  v'80  v'81  v'82  v'83  v'84 : val)
(  v'85 : int32)
(  v'86  v'87  v'88  v'89  v'90 : val)
(  v'91 : block)
(  v'92 : int32)
(  H95 : nth_val' (Z.to_nat (Int.unsigned v'74)) v'54 = Vint32 v'92)
(  H97 : nth_val' (Z.to_nat (Int.unsigned ((v'74<<ᵢ$ 3) +ᵢ  v'73))) v'53 =
        Vptr (v'91, Int.zero) /\ (v'91, Int.zero) <> v'34 )
(  H103 : nth_val' (Z.to_nat (Int.unsigned v'58)) OSUnMapVallist =
         Vint32 v'74 )
(  H104 : nth_val' (Z.to_nat (Int.unsigned v'74)) v'60 = Vint32 v'75 )
(  H105 : nth_val' (Z.to_nat (Int.unsigned v'75)) OSUnMapVallist =
         Vint32 v'73 )
(  H106 : nth_val' (Z.to_nat (Int.unsigned v'74)) OSMapVallist =
         Vint32 v'77 )
(  H107 : nth_val' (Z.to_nat (Int.unsigned v'73)) OSMapVallist =
         Vint32 v'76 )
(  H112 : array_type_vallist_match Int8u v'54 /\
         length v'54 = ∘ OS_RDY_TBL_SIZE )
(  H114 : RL_Tbl_Grp_P v'60 (Vint32 v'58))
(  H115 : array_type_vallist_match Int8u v'60)
(  H120 : array_type_vallist_match OS_TCB ∗ v'53 /\ length v'53 = 64%nat)
(  H122 : R_PrioTbl_P v'53 v'37 v'34)
(  H31 : v'67 <> Vnull)
(  H46 : array_type_vallist_match OS_TCB ∗ v'53)
(  H51 : length v'53 = 64%nat)
(  H52 : nth_val (Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)))
          v'53 = Some x1 )
(  H53 : nth_val (Z.to_nat (Int.unsigned (x >>ᵢ $ 8))) v'53 = Some x0)
(  H72 : TCBList_P x7 v'35 v'54 x10)
(  H54 : array_type_vallist_match Int8u v'54)
(  H58 : length v'54 = ∘ OS_RDY_TBL_SIZE)
(  H57 : prio_in_tbl ($ OS_IDLE_PRIO) v'54)
(  H56 : RL_Tbl_Grp_P v'54 (Vint32 i7))
(  rr1 : (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3)) < length v'54)%nat)
(  rr2 : (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)) <
         length v'54)%nat )
(  rr3 : (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)) <
         length v'54)%nat )
(  rr4 : (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8)&ᵢ$ 7)) < length v'54)%nat)
(  rr5 : (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3)) < length v'54)%nat)
(  rr6 : (Z.to_nat (Int.unsigned (x6&ᵢ$ 7)) < length v'54)%nat)
(  rrr1 : Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3) < Z.of_nat (length v'54))
(  rrr2 : Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7) <
         Z.of_nat (length v'54) )
(  rrr3 : Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3) <
         Z.of_nat (length v'54) )
(  rrr4 : Int.unsigned ((x >>ᵢ $ 8)&ᵢ$ 7) < Z.of_nat (length v'54))
(  rrr5 : Int.unsigned (x6 >>ᵢ $ 3) < Z.of_nat (length v'54))
(  rrr6 : Int.unsigned (x6&ᵢ$ 7) < Z.of_nat (length v'54))
(  HH58 : length v'54 = Z.to_nat 8)
(  aa : rule_type_val_match Int8u
         (nth_val' (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3))) v'54) =
       true )
(  aa2 : rule_type_val_match Int8u
          (nth_val'
             (Z.to_nat
                (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
             v'54) = true )
(  aa3 : rule_type_val_match Int8u
          (nth_val' (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3))) v'54) = true )
(  H88 : nth_val' (Z.to_nat (Int.unsigned ((x >>ᵢ $ 8) >>ᵢ $ 3))) v'54 =
        Vint32 x16 )
(  H87 : nth_val'
          (Z.to_nat
             (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3))) v'54 =
        Vint32 x13 )
(  H86 : nth_val' (Z.to_nat (Int.unsigned (x6 >>ᵢ $ 3))) v'54 =
        Vint32 x12 )
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
                                           :: Vint32
                                              ($ 1<<ᵢ(x6 >>ᵢ $ 3))
                                              :: nil) :: v'35) v'54 v'45 )
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
                                      :: Vint32 ($ 1<<ᵢ(x6 >>ᵢ $ 3))
                                         :: nil) v'54 
          (x6, rdy, m) )
(  H33 : TCBList_P v'67 v'33 v'54 v'43)
(  H49 : RL_RTbl_PrioTbl_P v'54 v'53 v'34)
(  H111 : RL_Tbl_Grp_P v'54 (Vint32 i7) /\
         prio_in_tbl ($ OS_IDLE_PRIO) v'54 )
(  H113 : rule_type_val_match Int8u (Vint32 i7) = true)
(  H11 : array_type_vallist_match Int8u v'60)
(  H19 : length v'60 = ∘ OS_EVENT_TBL_SIZE)
(  fffbb2 : (Z.to_nat (Int.unsigned x2) < length v'60)%nat)
(  H19'' : length v'60 = Z.to_nat 8)
(  H63 : nth_val' (Z.to_nat (Int.unsigned x2)) v'60 = Vint32 x4)
(  H102 : rel_edata_tcbstat (DMutex (Vint32 x) (Vptr (v'52, $ 0))) v'85)
(  H3 : ECBList_P v'46 Vnull v'26 v'28 v'48 v'37)
(  H32 : join v'43 v'45 v'37)
(  H7 : RH_TCBList_ECBList_P v'38 v'37 (v'52, Int.zero))
(  H8 : RH_CurTCB (v'52, Int.zero) v'37)
(  H50 : R_PrioTbl_P v'53 v'37 v'34)
(  H124 : TCBList_P v'67
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
                                        :: Vint32 ($ 1<<ᵢ(x6 >>ᵢ $ 3))
                                           :: nil) :: v'35) v'54 v'37 )
(  H21 : Int.unsigned v'58 <= 255 )
(  fffa : length OSUnMapVallist = 256%nat ->
         (Z.to_nat (Int.unsigned v'58) < 256)%nat ->
         exists x,
         Vint32 x2 = Vint32 x /\
         true = rule_type_val_match Int8u (Vint32 x) )
(  H60 : (Z.to_nat (Int.unsigned v'58) < 256)%nat )
(  H61 : nth_val' (Z.to_nat (Int.unsigned v'58)) OSUnMapVallist =
        Vint32 x2 )
(  H68 : val_inj
          (bool_and
             (val_inj
                (notint
                   (val_inj
                      (if Int.eq v'58 ($ 0)
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
                      (if Int.eq v'58 ($ 0)
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
(  H94 : val_inj
          (notint
             (val_inj
                (if Int.eq v'58 ($ 0)
                 then Some (Vint32 Int.one)
                 else Some (Vint32 Int.zero)))) <> 
        Vint32 Int.zero /\
        val_inj
          (notint
             (val_inj
                (if Int.eq v'58 ($ 0)
                 then Some (Vint32 Int.one)
                 else Some (Vint32 Int.zero)))) <> Vnull /\
        val_inj
          (notint
             (val_inj
                (if Int.eq v'58 ($ 0)
                 then Some (Vint32 Int.one)
                 else Some (Vint32 Int.zero)))) <> Vundef )
(  i_neq_zero : v'58 <> Int.zero )
(  H18 : RL_Tbl_Grp_P v'60 (Vint32 v'58) )
(  H1 : ECBList_P v'42 Vnull
         (v'25 ++
          ((V$ OS_EVENT_TYPE_MUTEX
            :: Vint32 v'58
               :: Vint32 x :: Vptr (v'52, $ 0) :: x3 :: v'46 :: nil,
           v'60) :: nil) ++ v'26)
         (v'27 ++ (DMutex (Vint32 x) (Vptr (v'52, $ 0)) :: nil) ++ v'28)
         v'38 v'37 )
(  H98 : tcblist_get (Vptr (v'91, Int.zero)) v'67
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
                                       :: Vint32 ($ 1<<ᵢ(x6 >>ᵢ $ 3))
                                          :: nil) :: v'35) =
        Some
          (v'80
           :: v'81
              :: v'82
                 :: v'83
                    :: v'84
                       :: Vint32 v'85
                          :: v'86 :: v'87 :: v'88 :: v'89 :: v'90 :: nil) /\
        struct_type_vallist_match OS_TCB_flag
          (v'80
           :: v'81
              :: v'82
                 :: v'83
                    :: v'84
                       :: Vint32 v'85
                          :: v'86 :: v'87 :: v'88 :: v'89 :: v'90 :: nil) )
(  H121 : RL_RTbl_PrioTbl_P
           (update_nth_val (Z.to_nat (Int.unsigned v'74)) v'54
              (Vint32 (Int.or v'92 v'76))) v'53 v'34 )
(  v'30 : addrval)
(  v'31 : val)
(  v'36 : block)
(  H118 : struct_type_vallist_match OS_EVENT
           (V$ OS_EVENT_TYPE_MUTEX
            :: Vint32 v'59
               :: Vint32 x :: Vptr (v'52, $ 0) :: x3 :: v'46 :: nil) )
(  H99 : array_type_vallist_match Int8u
          (update_nth_val (Z.to_nat (Int.unsigned v'74)) v'60
             (Vint32 (v'75&ᵢInt.not v'76))) )
(  H101 : Some (Vint32 v'59) = Some v'31 )
(  H108 : RL_Tbl_Grp_P
           (update_nth_val (Z.to_nat (Int.unsigned v'74)) v'60
              (Vint32 (v'75&ᵢInt.not v'76))) v'31)
(  H109 : Some (V$ OS_EVENT_TYPE_MUTEX) = Some (V$ OS_EVENT_TYPE_MUTEX))
(  H116 : Some (Vint32 x) = Some (Vint32 x))
(  H117 : Some (Vptr (v'52, $ 0)) = Some (Vptr (v'52, $ 0)))
(  H14 : id_addrval' (Vptr (v'36, Int.zero)) OSEventTbl OS_EVENT =
        Some v'23 )
(  H6 : EcbMod.joinsig (v'36, Int.zero)
         (absmutexsem (x >>ᵢ $ 8)
            (Some (v'52, $ 0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), w) v'48 v'49 )
(  H2 : ECBList_P v'42 (Vptr (v'36, Int.zero)) v'25 v'27 v'47 v'37 )
(  H5 : R_ECB_ETbl_P (v'36, Int.zero)
         (V$ OS_EVENT_TYPE_MUTEX
          :: Vint32 v'58
             :: Vint32 x :: Vptr (v'52, $ 0) :: x3 :: v'46 :: nil, v'60)
         v'37 )
(  H123 : R_ECB_ETbl_P (v'36, Int.zero)
           (V$ OS_EVENT_TYPE_MUTEX
            :: Vint32 v'58
               :: Vint32 x :: Vptr (v'52, $ 0) :: x3 :: v'46 :: nil,
           v'60) v'37 )
(  H119 : ptr_in_tcblist (Vptr (v'52, Int.zero)) v'67
           (set_node (Vptr (v'91, Int.zero))
              (v'80
               :: v'81
                  :: Vnull
                     :: Vptr (v'36, Int.zero)
                        :: Vint32 Int.zero
                           :: Vint32 (v'85&ᵢInt.not ($ OS_STAT_MUTEX))
                              :: v'86
                                 :: v'87 :: v'88 :: v'89 :: v'90 :: nil)
              v'67
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
                                           :: Vint32
                                              ($ 1<<ᵢ(x6 >>ᵢ $ 3))
                                              :: nil) :: v'35)) )
(  H100 : id_addrval' (Vptr (v'36, Int.zero)) OSEventTbl OS_EVENT =
         Some v'30 )
(  H_rgrp_le7 : Int.unsigned v'74 <= 7)
( H_row_le7 : Int.unsigned v'73 <= 7 ),
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
         :: (pip, Int8u) :: (prio, Int8u) :: (legal, Int8u) :: nil),
   Afalse|}|- (v'52, Int.zero)
   {{ <|| mutexpost (Vptr (v'36, Int.zero) :: nil) ||>  **
     LV pevent @ OS_EVENT ∗ |-> Vptr (v'36, Int.zero) **
     Astruct (v'36, Int.zero) OS_EVENT
       (V$ OS_EVENT_TYPE_MUTEX
        :: Vint32 v'59
           :: Vint32
                (Int.or (x&ᵢ$ OS_MUTEX_KEEP_UPPER_8) ((v'74<<ᵢ$ 3) +ᵢ  v'73))
              :: nth_val' (Z.to_nat (Int.unsigned ((v'74<<ᵢ$ 3) +ᵢ  v'73)))
                   v'53 :: x3 :: v'46 :: nil) **
     Aarray v'30 (Tarray Int8u ∘ OS_EVENT_TBL_SIZE)
       (update_nth_val (Z.to_nat (Int.unsigned v'74)) v'60
          (Vint32 (v'75&ᵢInt.not v'76))) **
     p_local OSLInv (v'52, Int.zero) init_lg **
     Aie false **
     Ais nil **
     Acs (true :: nil) **
     Aisr empisr **
     A_isr_is_prop **
     AOSUnMapTbl **
     AOSMapTbl **
     AOSRdyTblGrp
       (update_nth_val (Z.to_nat (Int.unsigned v'74)) v'54
          (Vint32 (Int.or v'92 v'76))) v'57 **
     GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64) v'53 **
     tcbdllseg v'67 Vnull v'69 Vnull
       (set_node (Vptr (v'91, Int.zero))
          (v'80
           :: v'81
              :: Vnull
                 :: Vptr (v'36, Int.zero)
                    :: Vint32 Int.zero
                       :: Vint32 (v'85&ᵢInt.not ($ OS_STAT_MUTEX))
                          :: v'86 :: v'87 :: v'88 :: v'89 :: v'90 :: nil)
          v'67
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
                                       :: Vint32 ($ 1<<ᵢ(x6 >>ᵢ $ 3)) :: nil)
           :: v'35)) **
     LV prio @ Int8u |-> Vint32 ((v'74<<ᵢ$ 3) +ᵢ  v'73) **
     LV os_code_defs.x @ Int8u |-> (V$ OS_STAT_MUTEX) **
     LV legal @ Int8u |-> Vint32 x2 **
     PV v'34 @ Int8u |-> v'32 **
     GV OSTCBList @ OS_TCB ∗ |-> v'67 **
     GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (v'52, Int.zero) **
     LV pip @ Int8u |-> Vint32 (x >>ᵢ $ 8) **
     GV OSEventList @ OS_EVENT ∗ |-> v'42 **
     evsllseg v'42 (Vptr (v'36, Int.zero)) v'25 v'27 **
     evsllseg v'46 Vnull v'26 v'28 **
     tcbdllflag v'67
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
                                    :: Vint32 ($ 1<<ᵢ(x6 >>ᵢ $ 3)) :: nil)
        :: v'35) **
     G& OSPlaceHolder @ Int8u == v'34 **
     HECBList v'38 **
     HTCBList v'37 **
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
           :: (pip, Int8u) :: (prio, Int8u) :: (legal, Int8u) :: nil)}} 
   EXIT_CRITICAL;ₛ
   OS_Sched (­);ₛ
  RETURN ′ OS_NO_ERR {{Afalse}}.
Proof.
  Set Printing Depth 999.
  intros.

  (*high level step*)
  destruct H97.
  unfolds in H50.
  destruct H50.
  assert (0 <= Int.unsigned ((v'74<<ᵢ$ 3) +ᵢ  v'73) < 64) as H_prio_range.
  clear - H_rgrp_le7 H_row_le7.
  mauto.

  assert (nth_val ∘ (Int.unsigned ((v'74<<ᵢ$ 3) +ᵢ  v'73)) v'53 = Some (Vptr (v'91, Int.zero))).
  eapply oscore_common.nth_val'2nth_val'; auto.

  lets Hx: H50 H_prio_range H125 H97.
  destruct Hx.
  destruct H126.

  lets Hx: tcbjoin_get_exists H126; destruct Hx.
  lets Hx: post_exwt_succ_pre_mutex'' i_neq_zero H103 H104 H105 H96; eauto.
  clear - H104 H115 H_rgrp_le7 H19.
  assert (Z.to_nat (Int.unsigned v'74) < length v'60)%nat.
  rewrite H19.
  unfold OS_EVENT_TBL_SIZE.
  mauto.
  lets Hx: array_int8u_nth_lt_len H115 H; simpljoin1.
  rewrite H104 in H0; inverts H0; auto.
  lets Hx1: Hx H127; clear Hx.
  simpljoin1.

  assert (Int.eq x6 (x >>ᵢ $ 8) = false).
  clear - H93.
  destruct H93.
  destruct (Int.eq x6 (x >>ᵢ $ 8)) eqn : eq1; tryfalse; auto.
  destruct (Int.eq x6 (x >>ᵢ $ 8)) eqn : eq1; tryfalse; auto.
  
  hoare abscsq.
  apply noabs_oslinv.
  eapply absinfer_mutexpost_noreturn_exwt_succ; eauto.
  go.
  eapply EcbMod.join_get_r; eauto.
  eapply EcbMod.join_get_l; eauto.
  eapply EcbMod.get_sig_some.

  eapply join_get_r.
  auto.
  eapply H32.
  unfold TcbJoin in H70.
  eapply join_get_l; eauto.
  eapply get_sig_some.

(*change the tcbdllseg in the post cond of OS_EventTaskRdy *)
  assert ((((v'74<<ᵢ$ 3) +ᵢ  v'73) >>ᵢ $ 3) = v'74) as H_prio_shr3.
  clear - H_rgrp_le7 H_row_le7.
  mauto.
  assert ((((v'74<<ᵢ$ 3) +ᵢ  v'73) &ᵢ$ 7) = v'73) as H_prio_and7.
  clear - H_rgrp_le7 H_row_le7.
  mauto.
  assert (v'76 = ($ 1<<ᵢv'73)) as H_bitx_prop.
  clear - H107 H_row_le7.
  eapply math_mapval_core_prop; auto.
  mauto.

  hoare lift 19%nat pre.
  eapply set_node_elim_hoare; eauto.
  eapply TCBNode_P_set_rdy with (row := v'92); eauto.
  rewrite H_prio_shr3.
  eapply nth_val'2nth_val; eauto.
  3: eapply TCBList_P_tcblist_get_TCBNode_P; eauto. 
  clear - H95 H112 H_rgrp_le7 H141.
  assert (Z.to_nat (Int.unsigned v'74) < length v'54)%nat.
  rewrite H141.
  unfold OS_RDY_TBL_SIZE.
  mauto.
  lets Hx: array_int8u_nth_lt_len H112 H; simpljoin1.
  rewrite H95 in H0; inverts H0; auto.

  clear - H102.
  simpl in H102; substs.
  unfold OS_STAT_MUTEX, OS_STAT_MUTEX.
  apply Int.and_not_self.
  unfolds.
  rewrite H_prio_shr3; rewrite H_prio_and7.
  do 2 eexists.
  splits; eauto.
  rewrite H_bitx_prop; auto.
  unfolds; simpl; auto.
  (**)

  (*EXIT_CRITICAL;ₛ*)
  hoare forward prim.
  remember (A_dom_lenv
              ((pevent, OS_EVENT ∗)
               :: (os_code_defs.x, Int8u) :: (pip, Int8u) :: (prio, Int8u) :: (legal, Int8u) :: nil)) in H116.
  sep split in H116.
  unfold AOSTCBList.
  sep normal.
  do 23 eexists.
  sep cancel 1%nat 2%nat.
  sep cancel 1%nat 3%nat.
  do 2 sep cancel 18%nat 1%nat.
  sep split.
  6: eapply H128.
  sep cancel AOSEventFreeList.
  do 2 sep cancel 24%nat 1%nat.
  sep cancel AOSMapTbl; sep cancel AOSUnMapTbl; sep cancel AOSIntNesting.
  sep cancel AOSTCBFreeList; sep cancel AOSRdyTblGrp.
  sep cancel AOSTime.
  do 2 sep cancel 3%nat 5%nat.
  sep cancel AGVars.
  sep cancel p_local.
  sep cancel A_isr_is_prop.
  sep cancel atoy_inv'.
  do 2 sep cancel 1%nat 3%nat.
  unfold AOSTCBPrioTbl.
  sep split; eauto.
  sep cancel OSTCBPrioTbl.
  sep cancel OSPlaceHolder.
  sep normal.
  eexists.
  sep cancel 7%nat 1%nat.
  sep lift 11%nat in H116.
  sep lift 2%nat.
  eapply tcbdllflag_set_node; eauto.
  sep cancel 1%nat 1%nat.
  unfold AECBList.
  sep normal.
  eexists.
  sep cancel OSEventList.
  sep split; eauto.
  eapply evsllseg_compose; eauto.
  instantiate (2 :=
                 (V$ OS_EVENT_TYPE_MUTEX
                   :: Vint32 v'59
                   :: Vint32 (Int.or (x&ᵢ$ OS_MUTEX_KEEP_UPPER_8) ((v'74<<ᵢ$ 3) +ᵢ  v'73))
                   :: nth_val' (Z.to_nat (Int.unsigned ((v'74<<ᵢ$ 3) +ᵢ  v'73))) v'53
                   :: x3 :: v'46 :: nil)).
  unfold V_OSEventListPtr; simpl; eauto.
  sep cancel 8%nat 2%nat.
  sep cancel 8%nat 2%nat.
  instantiate (2 := DMutex (Vint32 (Int.or (x&ᵢ$ OS_MUTEX_KEEP_UPPER_8) ((v'74<<ᵢ$ 3) +ᵢ  v'73))) (Vptr (v'91, Int.zero)) ).
  unfold AEventNode; unfold AOSEvent; unfold AEventData; unfold AOSEventTbl.
  unfold node.
  sep normal.
  do 3 eexists.
  sep split; eauto.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  rewrite Heqa in H116.
  exact H116.
  unfolds; simpl.
  rewrite H96; auto.
  split; auto.
  rewrite H96.
  clear - H118 H_rgrp_le7 H_row_le7 H133 H134 H10.
  simpl in H118.
  simpl.
  simpljoin1; splits; auto.
  remember ((v'74<<ᵢ$ 3) +ᵢ  v'73).
  clear Heqi.
  clear - H134 H10.
  lets Hx: mund_int_c1 H134 H10.
  rewrite Zle_imp_le_bool; auto.

  rewrite H96.
  eapply ecblist_p_post_exwt_hold_mutex_new; eauto.
  rewrite H61 in H103.
  inverts H103.
  rewrite H63 in H104.
  inverts H104.
  rewrite H66 in H105.
  inverts H105.
  eapply zh_asdf.
  clear - H68 i_neq_zero.
  assert (Int.eq v'58 ($ 0) = false).
  eapply Int.eq_false; auto.
  rewrite H in H68.
  auto.
  clear - H104 H115 H_rgrp_le7 H19.
  assert (Z.to_nat (Int.unsigned v'74) < length v'60)%nat.
  rewrite H19.
  unfold OS_EVENT_TBL_SIZE.
  mauto.
  lets Hx: array_int8u_nth_lt_len H115 H; simpljoin1.
  rewrite H104 in H0; inverts H0; auto.

  clear - H107 H_row_le7.
  assert (Z.to_nat (Int.unsigned v'73) < 8)%nat.
  mauto.
  lets Hx: OSMapVallist_bound H; auto.
  simpljoin1.
  rewrite H107 in H0; inverts H0; auto.
  unfolds; simpl; auto.
  clear - H50 H96 H97 H122 H133 H134.
  assert (nth_val (Z.to_nat (Int.unsigned ((v'74<<ᵢ$ 3) +ᵢ  v'73))) v'53 = Some (Vptr (v'91, Int.zero))).
  eapply oscore_common.nth_val'2nth_val'; auto.
  apply H50 in H; auto.
  do 2 destruct H.
  eapply r_priotbl_p_set_hold; eauto.
  lets Hx: Pos.eq_dec v'52 v'91.
  destruct Hx.
  substs.
  eapply OSMutex_common.return_rh_ctcb.
  eapply rh_curtcb_set_nct; auto.
  intro; apply n; inverts H144; auto.
  unfolds in H131; simpljoin1.
  lets Hx: rh_tcblist_ecblist_p_post_exwt_aux_mbox H7 H17 H6 H131 H126.
  auto.
  destruct Hx; substs.
  eapply rh_tcblist_ecblist_p_post_exwt_mutex; eauto.
  rewrite H_prio_shr3 in H143.
  rewrite H_prio_and7 in H143.
  rewrite H_bitx_prop.
  auto.
  rewrite H_prio_shr3 in H142.
  rewrite H_prio_and7 in H142.
  rewrite H_bitx_prop.
  auto.
  auto.
  go.

  (*OS_Sched (­);ₛ*)
  hoare forward.
  sep normal.
  do 2 eexists.
  remember (A_dom_lenv
              ((pevent, OS_EVENT ∗)
               :: (os_code_defs.x, Int8u) :: (pip, Int8u) :: (prio, Int8u) :: (legal, Int8u) :: nil)) in H116.
  sep split in H116.
  sep split; eauto.
  sep cancel p_local.
  rewrite Heqa in H116.
  exact H116.
  unfolds; auto.
  go.
  intros.
  do 2 destruct H116.
  exists init_lg.
  sep cancel p_local.
  sep auto.
  intros.
  do 2 destruct H116.
  exists (logic_val x20 :: nil).
  sep cancel p_local.
  sep auto.

  (*RETURN ′ OS_NO_ERR*)
  unfold OS_SchedPost.
  simpl getasrt.
  unfold OS_SchedPost'.
  hoare forward.
  sep normal.
  do 5 eexists.
  sep split in H116.
  sep split; eauto.
  sep cancel pevent.
  sep cancel p_local.
  sep cancel legal.
  sep cancel prio.
  sep cancel pip.
  eapply H116.
  inverts H117.
  auto.
Qed.
