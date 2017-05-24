(**************************  uc/OS-II  ******************************)
(*************************** OS_MUTEX.C *****************************)
(******Proof of API Fucntion:  int8u OSMutexPost(OS_EVENT* pevent) **)
(***************************** Code: ********************************)
(**
Int8u ·OSMutexPost·(⌞pevent @ OS_EVENT∗ ⌟)··{
        ⌞
         x @ Int8u;
         pip @ Int8u;
         prio  @ Int8u;
         legal @ Int8u
        ⌟;
        
1       If (pevent′ ==ₑ NULL)
        {
2          RETURN ′OS_ERR_PEVENT_NULL
        };ₛ
3       ENTER_CRITICAL;ₛ
4       legal′ =ᶠ OS_EventSearch(·pevent′·);ₛ
5       If (legal′ ==ₑ ′0)
        {
6           EXIT_CRITICAL;ₛ
7           RETURN ′OS_ERR_PEVENT_NO_EX
        };ₛ
8       If (pevent′→OSEventType !=ₑ ′OS_EVENT_TYPE_MUTEX)
        {
9           EXIT_CRITICAL;ₛ
10          RETURN ′OS_ERR_EVENT_TYPE
        };ₛ
        
11      pip′  =ₑ 〈Int8u〉(pevent′→OSEventCnt ≫ ′8);ₛ
12      prio′ =ₑ 〈Int8u〉(pevent′→OSEventCnt &ₑ ′OS_MUTEX_KEEP_LOWER_8);ₛ    
13      If (OSTCBCur′ !=ₑ pevent′→OSEventPtr)
        {   (* See if posting task owns the MUTEX*)
14          EXIT_CRITICAL;ₛ
15          RETURN ′OS_ERR_NOT_MUTEX_OWNER
        };ₛ                                                                     
16      If (OSTCBCur′→OSTCBPrio <ₑ pip′)
        {
17          EXIT_CRITICAL;ₛ
18          RETURN ′OS_ERR_MUTEX_PRIO
        };ₛ
19      If (OSTCBCur′→OSTCBPrio ==ₑ pip′)
        {
          (* Did we have to raise current task's priority? *)
          (* Yes, Return to original priority              *)
          (*      Remove owner from ready list at 'pip'    *)
20          If ( OSTCBPrioTbl′[prio′]  !=ₑ 〈OS_TCB ∗〉 PlaceHolder)
            {
21              EXIT_CRITICAL;ₛ
22              RETURN ′OS_ERR_ORIGINAL_NOT_HOLDER
            };ₛ
23          OSRdyTbl′[OSTCBCur′→OSTCBY] =ₑ OSRdyTbl′[OSTCBCur′→OSTCBY] &ₑ (∼OSTCBCur′→OSTCBBitX);ₛ
24          If ( OSRdyTbl′[OSTCBCur′→OSTCBY] ==ₑ ′0)
            {
25              OSRdyGrp′ =ₑ OSRdyGrp′ &ₑ ∼OSTCBCur′→OSTCBBitY
            };ₛ
26          OSTCBCur′→OSTCBPrio         =ₑ prio′;ₛ
27          OSTCBCur′→OSTCBY            =ₑ prio′ ≫  ′3;ₛ
28          OSTCBCur′→OSTCBBitY         =ₑ OSMapTbl′[OSTCBCur′→OSTCBY];ₛ
29          OSTCBCur′→OSTCBX            =ₑ prio′ &ₑ ′7;ₛ
30          OSTCBCur′→OSTCBBitX         =ₑ OSMapTbl′[OSTCBCur′→OSTCBX];ₛ
31          OSRdyGrp′                    =ₑ OSRdyGrp′ |ₑ OSTCBCur′→OSTCBBitY;ₛ
32          OSRdyTbl′[OSTCBCur′→OSTCBY] =ₑ OSRdyTbl′[OSTCBCur′→OSTCBY] |ₑ OSTCBCur′→OSTCBBitX;ₛ
33          OSTCBPrioTbl′[prio′]         =ₑ 〈OS_TCB ∗〉 OSTCBCur′;ₛ
34          OSTCBPrioTbl′[pip′]          =ₑ 〈OS_TCB ∗〉 PlaceHolder
        };ₛ
        (*OSTCBPrioTbl′[prio′] =ₑ 〈OS_TCB ∗〉 PlaceHolder;ₛ*)
35      If (pevent′→OSEventGrp !=ₑ ′0)
        {
36          x′ =ₑ ′OS_STAT_MUTEX;ₛ 
37          prio′ =ᶠ OS_EventTaskRdy(·pevent′, pevent′, x′·);ₛ
38          pevent′→OSEventCnt =ₑ pevent′→OSEventCnt &ₑ ′OS_MUTEX_KEEP_UPPER_8;ₛ  (*Save priority of mutex's new owner *)
39          pevent′→OSEventCnt =ₑ pevent′→OSEventCnt |ₑ prio′;ₛ
40          pevent′→OSEventPtr =ₑ OSTCBPrioTbl′[prio′];ₛ     (*Link to mutex owner's OS_TCB*)
            (*(OSTCBPrioTbl′[prio′])→OSTCBMutexOwn =ₑ pevent′;ₛ *)
41          EXIT_CRITICAL;ₛ
42          OS_Sched(­);ₛ
43          RETURN ′OS_NO_ERR 
        };ₛ
44      pevent′→OSEventCnt =ₑ pevent′→OSEventCnt |ₑ ′OS_MUTEX_AVAILABLE;ₛ (* No,  Mutex is now available   *)
45      pevent′→OSEventPtr =ₑ NULL;ₛ
        (*OSTCBCur′→OSTCBMutexOwn =ₑ NULL;ₛ*)
46      EXIT_CRITICAL;ₛ
47      RETURN ′OS_NO_ERR 
*)
Require Import ucos_include.
Require Import OSMutex_common.
Require Import os_ucos_h.
Require Import mutex_absop_rules.
Require Import sep_lemmas_ext.
Local Open Scope code_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.

(* Goal forall
 *   (v' v'0 v'1 v'2 : val
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
 *   v'20 : True
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
 *   v'50 : val
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
 *   x8 x9 : val
 * )(
 *   H37 : isptr x9
 * )(
 *   H38 : isptr x8
 * )(
 *   i6 : int32
 * )(
 *   H39 : Int.unsigned i6 <= 65535
 * )(
 *   i5 : int32
 * )(
 *   H40 : Int.unsigned i5 <= 255
 * )(
 *   i4 : int32
 * )(
 *   H41 : Int.unsigned i4 <= 255
 * )(
 *   i3 : int32
 * )(
 *   H42 : Int.unsigned i3 <= 255
 * )(
 *   i2 : int32
 * )(
 *   H43 : Int.unsigned i2 <= 255
 * )(
 *   i1 : int32
 * )(
 *   H44 : Int.unsigned i1 <= 255
 * )(
 *   i0 : int32
 * )(
 *   H45 : Int.unsigned i0 <= 255
 * )(
 *   H36 : isptr v'24
 * )(
 *   H27 : isptr v'50
 * )(
 *   H34 : TCBList_P (Vptr (v'52, Int.zero))
 *           ((v'50
 *             :: v'24
 *                :: x9
 *                   :: x8
 *                      :: Vint32 i6
 *                         :: Vint32 i5
 *                            :: Vint32 i4
 *                               :: Vint32 i3
 *                                  :: Vint32 i2
 *                                     :: Vint32 i1 :: Vint32 i0 :: nil) :: v'35)
 *           v'36 v'45
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
 *   H28 : Int.ltu i4 (x >>ᵢ $ 8) = false
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
 *                       (if
 *                         Int.ltu ((x2<<ᵢ$ 3) +ᵢ  x5)
 *                           (Int.modu (x >>ᵢ $ 8) ($ Byte.modulus))
 *                        then Some (Vint32 Int.one)
 *                        else Some (Vint32 Int.zero)))
 *                    (val_inj
 *                       (if
 *                         Int.eq ((x2<<ᵢ$ 3) +ᵢ  x5)
 *                           (Int.modu (x >>ᵢ $ 8) ($ Byte.modulus))
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
 *                       (if
 *                         Int.ltu ((x2<<ᵢ$ 3) +ᵢ  x5)
 *                           (Int.modu (x >>ᵢ $ 8) ($ Byte.modulus))
 *                        then Some (Vint32 Int.one)
 *                        else Some (Vint32 Int.zero)))
 *                    (val_inj
 *                       (if
 *                         Int.eq ((x2<<ᵢ$ 3) +ᵢ  x5)
 *                           (Int.modu (x >>ᵢ $ 8) ($ Byte.modulus))
 *                        then Some (Vint32 Int.one)
 *                        else Some (Vint32 Int.zero)))))) = Vnull
 * )(
 *   H69 : i5 = $ OS_STAT_RDY /\ i6 = $ 0
 *                                      ),
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
 *    {{ <|| mutexpost (Vptr (v'29, Int.zero) :: nil) ||>  **
 *      LV os_code_defs.x @ Int8u |-> Vint32 ((x2<<ᵢ$ 3) +ᵢ  x5) **
 *      LV legal @ Int8u |-> Vint32 x2 **
 *      PV v'51 @ Int8u |-> v'32 **
 *      Astruct (v'52, Int.zero) OS_TCB_flag
 *        (v'50
 *         :: v'24
 *            :: x9
 *               :: x8
 *                  :: Vint32 i6
 *                     :: Vint32 i5
 *                        :: Vint32 i4
 *                           :: Vint32 i3
 *                              :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil) **
 *      dllseg v'50 (Vptr (v'52, Int.zero)) v'40 Vnull v'35 OS_TCB_flag
 *        (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
 *      GV OSTCBList @ OS_TCB ∗ |-> v'31 **
 *      dllseg v'31 Vnull v'24 (Vptr (v'52, Int.zero)) v'33 OS_TCB_flag
 *        (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
 *      GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (v'52, Int.zero) **
 *      LV prio @ Int8u
 *      |-> Vint32 (Int.modu (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) ($ Byte.modulus)) **
 *      LV pip @ Int8u |-> Vint32 (Int.modu (x >>ᵢ $ 8) ($ Byte.modulus)) **
 *      Astruct (v'29, Int.zero) OS_EVENT
 *        (V$ OS_EVENT_TYPE_MUTEX
 *         :: Vint32 i :: Vint32 x :: Vptr (v'52, $ 0) :: x3 :: v'46 :: nil) **
 *      Aarray v'23 (Tarray Int8u ∘ OS_EVENT_TBL_SIZE) v'44 **
 *      Aie false **
 *      Ais nil **
 *      Acs (true :: nil) **
 *      Aisr empisr **
 *      GV OSEventList @ OS_EVENT ∗ |-> v'42 **
 *      evsllseg v'42 (Vptr (v'29, Int.zero)) v'25 v'27 **
 *      evsllseg v'46 Vnull v'26 v'28 **
 *      A_isr_is_prop **
 *      tcbdllflag v'31
 *        (v'33 ++
 *         (v'50
 *          :: v'24
 *             :: x9
 *                :: x8
 *                   :: Vint32 i6
 *                      :: Vint32 i5
 *                         :: Vint32 i4
 *                            :: Vint32 i3
 *                               :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil)
 *         :: v'35) **
 *      GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE) v'36 **
 *      GV OSRdyGrp @ Int8u |-> Vint32 i7 **
 *      GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64) v'30 **
 *      G& OSPlaceHolder @ Int8u == v'51 **
 *      HECBList v'38 **
 *      HTCBList v'39 **
 *      HCurTCB (v'52, Int.zero) **
 *      p_local OSLInv (v'52, Int.zero) init_lg **
 *      AOSEventFreeList v'3 **
 *      AOSQFreeList v'4 **
 *      AOSQFreeBlk v'5 **
 *      AOSMapTbl **
 *      GAarray OSUnMapTbl (Tarray Int8u 256) OSUnMapVallist **
 *      AOSIntNesting **
 *      AOSTCBFreeList v'21 v'22 **
 *      AOSTime (Vint32 v'18) **
 *      HTime v'18 **
 *      AGVars **
 *      atoy_inv' **
 *      LV pevent @ OS_EVENT ∗ |-> Vptr (v'29, Int.zero) **
 *      A_dom_lenv
 *        ((pevent, OS_EVENT ∗)
 *         :: (os_code_defs.x, Int8u)
 *            :: (pip, Int8u) :: (prio, Int8u) :: (legal, Int8u) :: nil)}} 
 *    If(OSTCBCur ′ → OSTCBPrio ==ₑ pip ′)
 *         {If(OSTCBPrioTbl ′ [prio ′] !=ₑ 〈 OS_TCB ∗ 〉 os_mutex.PlaceHolder)
 *               {EXIT_CRITICAL;ₛ
 *               RETURN ′ OS_ERR_ORIGINAL_NOT_HOLDER}  ;ₛ
 *         OSRdyTbl ′ [OSTCBCur ′ → OSTCBY] &= ∼ OSTCBCur ′ → OSTCBBitX;ₛ
 *         If(OSRdyTbl ′ [OSTCBCur ′ → OSTCBY] ==ₑ ′ 0)
 *              {OSRdyGrp ′ &= ∼ OSTCBCur ′ → OSTCBBitY}  ;ₛ
 *         OSTCBCur ′ → OSTCBPrio =ₑ prio ′;ₛ
 *         OSTCBCur ′ → OSTCBY =ₑ prio ′ ≫ ′ 3;ₛ
 *         OSTCBCur ′ → OSTCBBitY =ₑ OSMapTbl ′ [OSTCBCur ′ → OSTCBY];ₛ
 *         OSTCBCur ′ → OSTCBX =ₑ prio ′ &ₑ ′ 7;ₛ
 *         OSTCBCur ′ → OSTCBBitX =ₑ OSMapTbl ′ [OSTCBCur ′ → OSTCBX];ₛ
 *         OSRdyGrp ′ =ₑ OSRdyGrp ′ |ₑ OSTCBCur ′ → OSTCBBitY;ₛ
 *         OSRdyTbl ′ [OSTCBCur ′ → OSTCBY] =ₑ
 *         OSRdyTbl ′ [OSTCBCur ′ → OSTCBY] |ₑ OSTCBCur ′ → OSTCBBitX;ₛ
 *         OSTCBPrioTbl ′ [prio ′] =ₑ 〈 OS_TCB ∗ 〉 OSTCBCur ′;ₛ
 *         OSTCBPrioTbl ′ [pip ′] =ₑ 〈 OS_TCB ∗ 〉 os_mutex.PlaceHolder}  ;ₛ
 *    If(pevent ′ → OSEventGrp !=ₑ ′ 0)
 *         {os_code_defs.x ′ =ₑ ′ OS_STAT_MUTEX;ₛ
 *         prio ′ =ᶠ OS_EventTaskRdy (·pevent ′, 〈 (Void) ∗ 〉 pevent ′,
 *         os_code_defs.x ′·);ₛ
 *         pevent ′ → OSEventCnt &= ′ OS_MUTEX_KEEP_UPPER_8;ₛ
 *         pevent ′ → OSEventCnt =ₑ pevent ′ → OSEventCnt |ₑ prio ′;ₛ
 *         pevent ′ → OSEventPtr =ₑ OSTCBPrioTbl ′ [prio ′];ₛ
 *         EXIT_CRITICAL;ₛ
 *         OS_Sched (­);ₛ
 *         RETURN ′ OS_NO_ERR}  ;ₛ
 *    pevent ′ → OSEventCnt =ₑ pevent ′ → OSEventCnt |ₑ ′ OS_MUTEX_AVAILABLE;ₛ
 *    pevent ′ → OSEventPtr =ₑ NULL;ₛ
 *    EXIT_CRITICAL;ₛ
 *    RETURN ′ OS_NO_ERR {{Afalse}}
 *                  .
 * Admitted. *)




Theorem OSMutexPostRight: 
  forall vl p r tid,
    Some p = BuildPreA' os_api OSMutexPost mutexpostapi vl OSLInv tid init_lg ->
    Some r = BuildRetA' os_api OSMutexPost mutexpostapi vl OSLInv tid init_lg ->
    exists t d1 d2 s ,
      os_api OSMutexPost = Some (t, d1, d2, s) /\ {| OS_spec, GetHPrio, OSLInv, I, r, Afalse |} |- tid {{ p }} s {{ Afalse }}.
Proof.
  init_spec.
  destruct x;
  try solve [unfolds in H1; destruct H1; intros; simpljoin; tryfalse].
  hoare forward.
  (* intro; tryfalse. *)
  hoare unfold.
  hoare abscsq.
  apply noabs_oslinv.

  eapply  absinfer_mutex_post_null_return .
  go.
  hoare forward.
  hoare forward.
  hoare unfold.
  false.
  elim H; intros; tryfalse.

  hoare unfold.
  hoare forward.
  destruct a.
  simpl.
  intro; tryfalse.
  hoare unfold.
  false.
  destruct a.
  simpl in H; apply H; auto.
  instantiate (1:=Afalse).
  hoare forward.
  hoare unfold.
  clear H.
  clear H1.
  hoare unfold.
  hoare forward prim.
  hoare unfold.
  hoare forward.
  sep cancel tcbdllflag.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aisr.
  sep cancel AECBList.
  sep cancel AOSTCBList.
  sep cancel AOSRdyTblGrp.
  sep cancel AOSTCBPrioTbl.
  sep cancel 1%nat 1%nat.
  eauto.
  simpl; eauto 1.
  go.
  exact retpost_osev.
  Require Import linv_solver.
  linv solver.
  linv solver.
  (* sep cancel p_local.
   * simpl; auto. *)
  hoare unfold.
  eapply backward_rule1.
  intros;eapply disj_star_elim.
  eauto.
  hoare forward. 
  Focus 2.
  hoare unfold.
  hoare forward.
  change (Int.eq ($ 0) ($ 0)) with true.
  (* simpl; intro; tryfalse. *)
  hoare_split_pure_all.
  inverts H5.
  hoare abscsq.
  apply noabs_oslinv.
  eapply  absinfer_mutex_post_p_not_legal_return.
  go.
  go.
  hoare forward prim.
  go.
  go.
  hoare forward.
  hoare forward.
  hoare unfold.
  false.
  assert (Int.eq ($ 0) ($ 0) = true).
  int auto.
  rewrite H4 in H3.
  simpl in H3.
  elim H3; intros; tryfalse.

  (* legal =1 *)
  hoare unfold.
  inverts H15.
  hoare forward.
  change (Int.eq ($ 1) ($ 0)) with false.
  (* simpl; intro; tryfalse. *)
  hoare unfold.
  instantiate (1:=Afalse).
  false.
  clear -H9.
  (* assert (Int.eq ($ 1) ($ 0 ) = false). *)
  int auto.
  (* rewrite H in H9. *)
  (* simpl in H9; apply H9; auto. *)
  hoare forward.

  (* legal = 1 *)
  hoare unfold.
  
  hoare forward.
  (* intro; tryfalse. *)
  go.
  destruct ( Int.eq i0 ($ OS_EVENT_TYPE_MUTEX)); simpl; intro; tryfalse. 
  destruct ( Int.eq i0 ($ OS_EVENT_TYPE_MUTEX)); simpl; intro; tryfalse. 
  
  hoare unfold.
  assert (Int.eq i0 ($ OS_EVENT_TYPE_MUTEX) = false \/ Int.eq i0 ($ OS_EVENT_TYPE_MUTEX) = true).
  clear.
  destruct (   Int.eq i0 ($ OS_EVENT_TYPE_MUTEX)).
  right; auto.
  left; auto.
  elim H25; intros.

    eapply backward_rule1.
  intros.
  sep lift 8%nat in H27.
  eapply eventtype_neq_mutex;
  eauto.
  hoare unfold.

  hoare abscsq.
  apply noabs_oslinv.
  eapply absinfer_mutex_post_wrong_type_return.
  go.
  eexists.
  split.
  go.
  intro.
  apply H27.
  simpljoin.
  do 3 eexists.
  go.
  hoare forward prim.
  unfold AECBList.
  sep pauto.
  2:eauto.
  rewrite list_prop1.
  rewrite list_prop1.
  eapply evsllseg_merge; eauto.

  lets Heq : ecblistp_length_eq H1 H12.
  simpl; auto.

  sep cancel 4%nat 1%nat.  
  unfold evsllseg; fold evsllseg.
  unfold AEventNode.
  unfold AOSEvent.
  unfold node.
  unfold AOSEventTbl.
  sep pauto.
  go.
  go.
  go.
  go.
  hoare forward.
  false.
  rewrite H26 in H10.
  simpl in H10.
  apply H10; auto.
  hoare forward.
  hoare unfold.
  apply  val_inj_eq in H10.
  subst i0.
  unfold AEventData.
  destruct v'43; hoare_split_pure_all.
  inverts H13.
  inverts H10.
  inverts H10.
  inverts H15.
  inverts H13.
  clear H10.
  clear H9.
  lets backup : H4.
  unfolds in H4.
  destruct v'48.
  destruct e; tryfalse.
  simpljoin.
  unfolds in H4.
  simpljoin.
  inverts H4.
  unfolds in H9.
  simpljoin.
  
  hoare unfold.
  hoare forward.
  (* intro; tryfalse. *)
  go.
  change (Int.ltu ($ 8) Int.iwordsize ) with true. 
  simpl; eauto.
  (* intro; tryfalse. *)

  hoare unfold.
  hoare forward.
  (* intro; tryfalse. *)
  go.
  (* intro; tryfalse. *)

  hoare unfold.
  hoare forward.
  (* intro; tryfalse. *)
  go.
  clear -H23.
  destruct v0;
  unfolds in H23;
  elim H23; intros; simpljoin; tryfalse.
  simpl; intro; tryfalse.
  inverts H.
  destruct x.
  destruct ( peq v'50 b); destruct (Int.eq Int.zero i); simpl; intro; tryfalse. 
clear -H23.
  destruct v0;
  unfolds in H23;
  elim H23; intros; simpljoin; tryfalse.
  simpl; intro; tryfalse.
  inverts H.
  destruct x.
  destruct ( peq v'50 b); destruct (Int.eq Int.zero i); simpl; intro; tryfalse. 

    hoare unfold.
  


  apply  valinj_lemma1 in H28.
  hoare abscsq.
  apply noabs_oslinv.
  eapply  absinfer_mutex_post_no_owner_return.
  go.
  go.
  intro.
  simpljoin.
  lets fff: H9 (eq_refl ( Some (v'50, Int.zero, x0))).
  assert (  x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 = $ OS_MUTEX_AVAILABLE \/  x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 <> $ OS_MUTEX_AVAILABLE) by tauto.
  elim H46; intros.
  lets ffff: H25 H47.
  simpljoin.
  tryfalse.
  lets ffff: H26 H47.
  simpljoin.
  elim H28; intros.
  tryfalse.
  simpljoin.
  inverts H48.
  inverts H49.
  elim H52.
  clear; intro; int auto.
  clear; intro; auto.
  hoare forward prim.
  unfold AECBList; unfold AOSTCBList.
  sep pauto.
  2:eauto.
  rewrite list_prop1.
  rewrite list_prop1.
  unfold tcbdllseg.
  sep pauto.
  sep cancel 3%nat 1%nat.
  unfold1 dllseg.
  unfold node.
  sep pauto.
  sep cancel 1%nat 1%nat.
  sep cancel 1%nat 1%nat.
  eapply evsllseg_merge; eauto.


  lets Heq : ecblistp_length_eq H1 H12.
  simpl; auto.

  sep cancel 5%nat 1%nat.  
  unfold evsllseg; fold evsllseg.
  unfold AEventNode.
  unfold AOSEvent.
  unfold node.
  unfold AOSEventTbl.
  unfold AEventData.
  sep pauto.
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel evsllseg.
  eauto.

  go.
  go.
  go.
  go.
  go.
  go.
  go.
  go.
  go.
  go.
  go.
  go.
  hoare forward.
  auto.
  hoare forward.

  hoare unfold.
  apply valinj_lemma2 in H28.
  subst v0.

  (* assert tcbcur has mutex *)

  hoare forward.
  go.
  apply del_intlemma1.
  auto.
  destruct ( Int.ltu i4 (Int.modu (x >>ᵢ $ 8) ($ Byte.modulus))); simpl; intro; tryfalse.

  hoare unfold.
  apply post_intlemma1 in H28.
  

  
  lets backup2: H34.

  unfold1 TCBList_P in H34.
  simpljoin.
  inverts H46.
  inverts H34.
  unfolds in H48.
  simpljoin.
  destruct x4.
  destruct p.
  simpljoin.
  inverts H34.
  inverts H46.

  hoare abscsq.

  apply noabs_oslinv.
  eapply absinfer_mutex_post_prio_err_return.
  
  go.
  go.
  unfold TcbJoin in *.
  unfold join in *; simpl in *.
  unfold sig in *; simpl in *.
  go.
  go.


  hoare forward prim.
  unfold AECBList.
  unfold AOSTCBList.
  unfold tcbdllseg.
  sep pauto.
  sep cancel 3%nat 1%nat.
  3:eauto.
  unfold1 dllseg.
  sep pauto.
  unfold node.
  3:eauto.
  sep pauto.
  sep cancel 1%nat 1%nat.
  sep cancel 1%nat 1%nat.
  do 2 rewrite list_prop1.
  eapply evsllseg_merge; eauto.


  lets Heq : ecblistp_length_eq H1 H12.
  simpl; auto.
  sep cancel 5%nat 1%nat.
  unfold1 evsllseg.
  unfold AEventNode.
  unfold AOSEvent.
  unfold AEventData.
  unfold node.
  sep pauto.
  sep cancel Astruct.
  unfold AOSEventTbl.
  sep cancel Aarray.
  sep cancel evsllseg.
  sep pauto.
  go.
  go.
  go.
  go.
  go.  go.  go.  go.  go.  go.  go.
  hoare forward.
  go.
  hoare forward.
  hoare unfold.
  apply post_intlemma2 in H28.

  2:auto.


  assert ( x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 = $ OS_MUTEX_AVAILABLE \/  x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 <> $ OS_MUTEX_AVAILABLE).
  tauto.
  elim H29; intros.
  false.

  lets fff: H25 H35.
  clear -fff.
  simpljoin; tryfalse.

  lets fff: H26 H35.
  simpljoin.

  lets fff: H9 (eq_refl (Some (x0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8))).
  simpljoin.

  hoare unfold.
  unfold AOSTCBPrioTbl.
  hoare_split_pure_all.

  destruct H46.

  assert ( exists t, nth_val (Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) v'29 = Some t).

  apply ls_has_nth_val.
  rewrite H51.
  clear -H48.
  remember (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) .
  mauto.

  assert ( exists t, nth_val (Z.to_nat (Int.unsigned (Int.shru x ($ 8)))) v'29 = Some t).

  apply ls_has_nth_val.
  rewrite H51.
  clear -H15.
  remember (Int.shru x ($ 8)) .
  mauto.

  simpljoin.
  Open Scope code_scope.
  unfold AOSUnMapTbl.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl, AOSRdyGrp.
  hoare_split_pure_all.
  hoare forward.
  (* intro; tryfalse. *)
  go.
  Require Import symbolic_lemmas.
  apply array_type_vallist_match_imp_rule_type_val_match.
  clear -H21.
  unfold OSUnMapVallist.
  simpl.
  mauto.

  exact unMapvallistint8u.

  hoare unfold.
  lets fffa: nthval'_has_value  OSUnMapVallist_type_vallist_match.
  assert (length OSUnMapVallist = 256)%nat by auto.
  assert (Z.to_nat (Int.unsigned i) < 256)%nat.
  clear -H21.
  mauto.
  lets fffaa :fffa H59 H60.
  simpljoin.
  rewrite H61 in *.
  lets fffbb: math_unmap_get_y H21 H61.
  Hint Resolve OS_EVENT_TBL_SIZE : tlib.
  Hint Resolve intlt2nat : tlib.
  Hint Resolve int8ule255 : tlib.
  Hint Resolve array_type_vallist_match_imp_rule_type_val_match : tlib.
  lets fffbb2 : intlt2nat fffbb.
  lets H19'' : H19.
  unfold OS_EVENT_TBL_SIZE in H19''.
  unfold nat_of_Z in H19''.
  rewrite <- H19'' in fffbb2.

  lets bbbff:array_int8u_nth_lt_len H11 fffbb2.
  simpljoin.
  assert (Z.to_nat (Int.unsigned x4) < length OSUnMapVallist)%nat.
  clear -H64.
  mauto.
  lets bbfa: array_int8u_nth_lt_len OSUnMapVallist_type_vallist_match H65.
  simpljoin.

  hoare forward.
  (* change ( Int.ltu ($ 3) Int.iwordsize ) with true; simpl; intro ; tryfalse. *)
  rewrite H19.
  auto with tlib.
  rewrite H63.
  unfolds; auto.

  
  Local Open Scope Z_scope.
  math simpls.
  Ltac mew2 := match goal with
                 | |- (if _ then true else false) = true => rewrite ifE
                 | |- (_ <=? _ = true) => apply Zle_imp_le_bool
                 | |- (_ <= _ ) => apply Zle_bool_imp_le
               end.
  Hint Resolve ifE : tlib.
  Hint Resolve Zle_imp_le_bool : tlib.
  eauto.
  clear -H64; omega.
  clear -H64; omega.

  apply array_type_vallist_match_imp_rule_type_val_match.
  unfold OSUnMapVallist.
  simpl.
  clear -H64; mauto.
  exact OSUnMapVallist_type_vallist_match.
  Hint Resolve OSUnMapVallist_type_vallist_match: tlib.
  rewrite postintlemma4.
  rewrite H66.
  simpl; intro; tryfalse.
  rewrite postintlemma4.
  rewrite H66.
  simpl add.
  simpl val_inj.


  lets ttfasd: math_unmap_get_y H64 H66.
  hoare forward.
  (* intro; tryfalse. *)
  go.
  destruct (Int.eq i ($ 0)); simpl;intro; tryfalse.
  destruct (Int.eq i ($ 0)); simpl; intro; tryfalse.

  math simpls.
  clear -fffbb ttfasd.
  mauto.


  apply postintlemma1.
  destruct ( Int.ltu ((x2<<ᵢ$ 3)+ᵢx5) (Int.modu (Int.shru x ($ 8)) ($ Byte.modulus))).
  simpl; intro; tryfalse.
  simpl; intro; tryfalse.
  clear -fffbb ttfasd.
  mauto.
  apply postintlemma1.

  destruct ( Int.eq ((x2<<ᵢ$ 3)+ᵢx5) (Int.modu (Int.shru x ($ 8)) ($ Byte.modulus))); simpl; intro; tryfalse.
  destruct (Int.eq i ($ 0)); 
    destruct ( Int.ltu ((x2<<ᵢ$ 3)+ᵢx5) (Int.modu (Int.shru x ($ 8)) ($ Byte.modulus)));    destruct ( Int.eq ((x2<<ᵢ$ 3)+ᵢx5) (Int.modu (Int.shru x ($ 8)) ($ Byte.modulus))); simpl; intro; tryfalse.
  destruct (Int.eq i ($ 0)); 
    destruct ( Int.ltu ((x2<<ᵢ$ 3)+ᵢx5) (Int.modu (Int.shru x ($ 8)) ($ Byte.modulus)));    destruct ( Int.eq ((x2<<ᵢ$ 3)+ᵢx5) (Int.modu (Int.shru x ($ 8)) ($ Byte.modulus))); simpl; intro; tryfalse.

  hoare unfold.

  instantiate (1:=Afalse).


  (* to zhang hui *)
  
  rename v'42 into evnt_tbl.
  Ltac copy H1 H2 :=
    match type of H1 with
      | ?T =>
        assert(T) as H2 by (apply H1)
    end.
  copy H5 Hx.
  unfolds in Hx. 
  destruct Hx as (Hx & _ & _).
  unfolds in Hx.
  destruct Hx as (_&_&_&Hx).
  unfolds in Hx.
  unfold V_OSEventType in Hx.
  simpl nth_val in Hx.
  assert(PrioWaitInQ (Int.unsigned ((x2<<ᵢ$ 3)+ᵢx5)) evnt_tbl).

  pose proof prio_from_grp_tbl_PrioWaitInQ i evnt_tbl x2 x4 x5.
  eapply H71; eauto.
  clear - H68 H69 H70.
  destruct (Int.eq i ($ 0)) eqn : eq1.

  destruct (Int.ltu ((x2<<ᵢ$ 3)+ᵢx5) (Int.modu (Int.shru x ($ 8)) ($ Byte.modulus)));
    destruct (Int.eq ((x2<<ᵢ$ 3)+ᵢx5) (Int.modu (Int.shru x ($ 8)) ($ Byte.modulus)));
    simpl in *; try (rewrite int_ltu_zero_one_true in *); try (rewrite int_ltu_zero_notbool_one_false in *); try (rewrite int_ltu_zero_zero_false in *); simpl in *; tryfalse.

  clear - eq1.
  intro; substs.
  rewrite Int.eq_true in eq1.
  inversion eq1.
  
  apply Hx in H71; auto.
  do 3 destruct H71.
  copy H7 Hx1.
  unfolds in Hx1.
  destruct Hx1 as (_&_&_&Hx1).
  unfolds in Hx1.
  destruct Hx1 as (_&Hx1).
  copy H71 Hx2.
  apply Hx1 in H71.
  clear Hx1.
  simpljoin. 
  unfold get in H71, Hx2; simpl in H71, Hx2.
  assert(EcbMod.get v'37 (v'28, Int.zero) = Some (absmutexsem (Int.shru x ($ 8)) (Some (v'50, $ 0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), w)).
  clear - H17 H6.
  pose proof H6 (v'28, Int.zero).
  rewrite EcbMod.get_sig_some in H.
  destruct (EcbMod.get v'46 (v'28, Int.zero)); tryfalse.
  destruct (EcbMod.get v'47 (v'28, Int.zero)) eqn : eq1; tryfalse.
  pose proof H17 (v'28, Int.zero).
  rewrite eq1 in H0.
  destruct (EcbMod.get v'45 (v'28, Int.zero)); tryfalse.
  destruct (EcbMod.get v'37 (v'28, Int.zero)); tryfalse.
  substs; auto.
  
  rewrite H71 in H73; inverts H73.

  hoare abscsq.

  apply noabs_oslinv.
  eapply absinfer_mutex_post_wl_highest_prio_err_return; eauto.
  go.
  go.
  
  apply zlt_false.  
  assert(Int.modu (Int.shru x ($ 8)) ($ Byte.modulus) = (Int.shru x ($ 8))).
  clear - H15.
  apply mutexdel_intlemma1; auto.   
  clear - H68 H69 H70 H73.
  rewrite H73 in *.
  destruct (Int.ltu ((Int.shl x2 ($ 3))+ᵢx5) (Int.shru x ($ 8))) eqn : eq1.
  rewrite Int.repr_unsigned.
  apply Int.ltu_inv in eq1.
  clear - eq1.
  apply Znot_lt_ge. 
  apply Zle_not_lt.
  destruct eq1. 
  apply Z.lt_le_incl; auto.
  destruct(Int.eq ((Int.shl x2 ($ 3))+ᵢx5) (Int.shru x ($ 8))) eqn : eq2;
    destruct(Int.eq i ($ 0)); simpl in *; try (rewrite int_ltu_zero_notbool_one_false in *); try (rewrite int_ltu_zero_zero_false in *); try (rewrite int_ltu_zero_one_true in *); try (rewrite int_ltu_zero_notbool_zero_true in *); simpl in *; tryfalse.
  rewrite Int.repr_unsigned.
  unfold Int.eq in eq2.
  destruct (zeq (Int.unsigned ((Int.shl x2 ($ 3))+ᵢx5)) (Int.unsigned (Int.shru x ($ 8)))) eqn : eq3.
  rewrite e.
  omega.
  inversion eq2.
  rewrite int_ltu_zero_zero_false in H68.
  simpl in H68.
  tryfalse.
  
  hoare forward prim.
  unfold AOSUnMapTbl.
  unfold AOSTCBPrioTbl.
  unfold AOSRdyTblGrp.
  unfold AOSTCBList.
  unfold AOSRdyTbl.
  unfold AOSRdyGrp.
  unfold tcbdllseg.
  unfold dllseg; fold dllseg.
  unfold  V_OSTCBPrev; unfold V_OSTCBNext.

  sep pauto; eauto.
  sep cancel tcbdllflag.
  sep cancel 5%nat 2%nat.
  sep cancel 5%nat 2%nat.
  sep cancel 3%nat 2%nat.
  sep cancel 11%nat 3%nat.
  unfold node.
  sep pauto.
  sep cancel 3%nat 1%nat.
  Local Open Scope list_scope.
  instantiate (3:=(v'24 ++
                        ((V$OS_EVENT_TYPE_MUTEX
                           :: Vint32 i :: Vint32 x :: Vptr (v'50, $ 0) :: x3 :: v'44 :: nil,
                          evnt_tbl) :: nil) ++ v'25)).
  instantiate (2:=(v'26 ++ (DMutex (Vint32 x) (Vptr (v'50, $ 0)) :: nil) ++ v'27)).
  unfold AECBList.
  sep pauto.
  eapply evsllseg_compose; eauto.
  unfolds; simpl; eauto.
  unfold AEventNode.
  unfold AOSEvent.
  unfold AEventData.
  unfold node.
  unfold AOSEventTbl.
  sep pauto; eauto.
  do 3 (sep cancel 5%nat 1%nat).
  exact H73.
  split; auto.
  go.
  split; auto.
  go.
  unfolds.
  lets Hx1: leb_bytemax_true_intro H55.
  rewrite Hx1.
  auto.
  go.
  go.
  go.

  hoare forward.
  (*to zhanghui end*)
  

  hoare forward.
  hoare unfold.

  hoare forward.
  
  go.

  destruct (Int.eq i5 ($ OS_STAT_RDY)); simpl; intro; tryfalse.
  destruct (Int.eq i5 ($ OS_STAT_RDY)); simpl; intro; tryfalse.

  go.

  destruct (Int.eq i6 ($ 0)); simpl; intro; tryfalse.
  destruct (Int.eq i6 ($ 0)); simpl; intro; tryfalse.
  destruct (Int.eq i6 ($ 0));
    destruct (Int.eq i5 ($ OS_STAT_RDY)); simpl; intro; tryfalse.

  instantiate (1:=Afalse).

  hoare abscsq.
  apply noabs_oslinv.
  eapply absinfer_mutex_post_original_not_holder_err_return .
  go.
  hoare forward prim.
  unfold AOSUnMapTbl.
  unfold AOSTCBPrioTbl.
  unfold AOSRdyTblGrp.
  unfold AOSTCBList.
  unfold AOSRdyTbl.
  unfold AOSRdyGrp.
  unfold tcbdllseg.
  unfold dllseg; fold dllseg.
  unfold node.
  sep pauto.
  sep cancel tcbdllflag.

  sep cancel 4%nat 1%nat.
  sep cancel 4%nat 1%nat.
  sep cancel 4%nat 1%nat.
  sep cancel 3%nat 1%nat.
  sep cancel 10%nat 2%nat.
  instantiate (3:=(v'24 ++
                        ((V$OS_EVENT_TYPE_MUTEX
                           :: Vint32 i :: Vint32 x :: Vptr (v'50, $ 0) :: x3 :: v'44 :: nil,
                          v'42) :: nil) ++ v'25)).
  instantiate (2:=(v'26 ++ (DMutex (Vint32 x) (Vptr (v'50, $ 0)) :: nil) ++ v'27)).

  (* instantiate (3 := ((v'25 ++
   *                          ((V$OS_EVENT_TYPE_MUTEX
   *                             :: Vint32 i :: Vint32 x :: Vptr (v'52, $ 0) :: x3 :: v'46 :: nil,
   *                            v'44) :: nil) ++ v'26))).
   * instantiate (2 := (  (v'27 ++ (DMutex (Vint32 x) (Vptr (v'52, $ 0)) :: nil) ++ v'28))). *)
  unfold AECBList.
  sep pauto.
  eapply evsllseg_compose; eauto.
  go.
  unfold AEventNode.
  unfold AEventData; unfold AOSEvent.
  unfold node.
  unfold AOSEventTbl.
  sep pauto.
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel evsllseg.
  eauto.
  go.   go.   go.   go.   go.   go.   
  mew2; mew2.
  exact H55.
  go.   go.   go.
  go.   go.   go. 
  go.   go. 
  go.
  hoare forward.

  hoare forward.
  hoare unfold.

  apply simpl_valinj in H69.


  
  Require Import OSMutexPostPart2.

  eapply MutexPostPart1; eauto.

Qed.
