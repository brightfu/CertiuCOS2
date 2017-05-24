Require Import include_frm.
Require Import math_auto.
Require Import ucos_include.
Require Import os_ucos_h.
Require Import OSTimeDlyPure.
Local Open Scope code_scope.


Definition ProtectWrapper (a:Type) : Type :=a.
Lemma MakeProtectWrapper : forall H, H -> ProtectWrapper H.
Proof.
  auto.
Qed.
Ltac protect H := let H' := fresh in rename H into H'; lets H : MakeProtectWrapper H'; clear H'.
Ltac unprotect H := unfold ProtectWrapper in H.

Local Open Scope int_scope.
Local Open Scope Z_scope.


Lemma Zland_le_l: forall a b, 0<=a -> Z.land a b <= a.
Proof.
  intros.
  apply Byte.Ztestbit_le.
  auto.
  intros.
  rewrite Z.land_spec in H1.
  rewrite andb_true_iff in H1.
  tauto.
Qed.

Lemma Zland_le_r: forall a b, 0<=b -> Z.land a b <= b.
Proof.
  intros a b.
  rewrite Z.land_comm.
  apply Zland_le_l.
Qed.

Lemma tblemma1 : forall i, 0<=i<8 -> Z.testbit 255 i = true.
Proof.
  intros.
  mauto.
Qed.


Lemma tblemma2 : forall i, 0<=i<8 -> Z.testbit 65280 i = false.
Proof.
  intros.
  mauto.
Qed.

Lemma tblemma4 : forall i x, 0<=x -> Z.testbit x i = true -> 2^i <= x.
Proof.
  intros.

  apply Byte.Ztestbit_le.
  auto.
  intros.
  assert (i=i0 \/ i <> i0).
  tauto.
  elim H3; intros.
  subst i.
  auto.
  false.
  lets aaa: Z.pow2_bits_false H4.
  rewrite aaa in H2.
  inversion H2.
Qed.

Lemma tblemma3 : forall i x, 0<=x<=255 -> i>=8 -> Z.testbit x i = false.
Proof.
  intros.
  remember (Z.testbit x i).
  destruct b.
  assert (Z.testbit x i = true) by auto.
  assert (0<=x) by omega.
  lets aaa: tblemma4 H2 H1.
  rewrite <- two_p_equiv  in aaa.
  assert (two_p 8 <= two_p i).
  apply two_p_monotone.
  omega.
  simpl in H3.
  unfold two_power_pos in H3.
  unfold shift_pos in H3.
  simpl in H3.
  omega.
  auto.
Qed.


Lemma int_auxxx:
  forall x0,
    Int.unsigned x0 <= 65535 ->
    Int.unsigned (Int.or x0 ($ OS_MUTEX_AVAILABLE)) <= 65535.
Proof.
  intros.
  assert ( Int.unsigned (Int.or x0 ($ OS_MUTEX_AVAILABLE)) < two_p (Z.max (Int.size x0) (Int.size ($ OS_MUTEX_AVAILABLE)))).
  apply  Int.or_interval.
  unfold OS_MUTEX_AVAILABLE in H0.
  assert (two_p 16 -1  = 65535).
  unfolds.
  unfolds.
  unfold shift_pos.
  simpl.
  auto.
  rewrite <- H1 in H.
  assert (Int.unsigned x0 < two_p 16 ) by omega.
  assert (0<=Int.unsigned x0 < two_p 16).
  split;auto.
  clear.
  int auto.
  lets Hx : Int.size_interval_2 16  H3.
  omega.
  assert (Int.size ($ 255) = 8).
  unfolds.
  unfolds.
  rewrite Int.unsigned_repr.
  simpl; auto.
  clear.
  int auto.
  rewrite H4 in H0.
  pose  (Zmax_spec  (Int.size x0) 8) as Hpos.
  destruct Hpos.
  destruct H5.
  rewrite <- H6 in Hx.
  assert (two_p (Z.max (Int.size x0) 8) <= two_p 16 ). 
  eapply two_p_monotone.
  omega.
  rewrite <- H1.
  unfold OS_MUTEX_AVAILABLE.
  omega.
  destruct H5.
  rewrite H6 in H0.
  unfold two_p in H0.
  unfold two_power_pos in H0.
  unfold shift_pos in H0.
  simpl in H0.
  unfold OS_MUTEX_AVAILABLE.
  omega.
Qed.

Lemma acpt_intlemma8: forall x, Int.or x ($ 0) = x.
Proof.
  intros.
  unfold Int.or.
  ur_rewriter.
  rewrite Z.lor_0_r.
  apply Int.repr_unsigned.
Qed.

Lemma int_aux':
  forall x0,
    Int.unsigned x0 <= 65535 ->
    x0>>ᵢ$ 8 = (Int.or x0 ($ OS_MUTEX_AVAILABLE))>>ᵢ$ 8.
Proof.
  intros.
  rewrite <- Int.or_shru.
  change ($ OS_MUTEX_AVAILABLE>>ᵢ$ 8) with ($0).
  rewrite acpt_intlemma8.
  auto.
Qed.

Lemma intandcomm : forall x y, Int.and x y = Int.and y x.
Proof.
  intros.
  unfold Int.and.
  rewrite Z.land_comm.
  auto.
Qed.

Lemma intorcomm : forall x y, Int.or x y = Int.or y x.
Proof.
  intros.
  unfold Int.or.
  rewrite Z.lor_comm.
  auto.
Qed.

Lemma int_aux'':
  forall x0,
    Int.unsigned x0 <= 65535 ->
    Int.or x0 ($ OS_MUTEX_AVAILABLE)&ᵢ$ OS_MUTEX_KEEP_LOWER_8 =
    $ OS_MUTEX_AVAILABLE.
Proof.
  intros.
  change  OS_MUTEX_AVAILABLE with 255.
  change  OS_MUTEX_KEEP_LOWER_8 with 255.
  rewrite intandcomm.
  rewrite intorcomm.
  apply Int.and_or_absorb.
Qed.


Lemma RLH_ECBData_P_or_available :
  forall x,
    Int.unsigned x <= 65535 ->
    Int.unsigned (x>>ᵢ$ 8) < 64 ->
    RLH_ECBData_P (DMutex (Vint32 (Int.or x ($ OS_MUTEX_AVAILABLE))) Vnull)
                  (absmutexsem (x>>ᵢ$ 8) None, nil).
Proof.
  intros.
  rename H0 into Hx.
  unfolds.
  simpl; splits; auto.
  unfolds.
  do 2 eexists ;splits; eauto.
  eapply  int_auxxx; eauto.
  eapply int_aux'; eauto.
  intros.
  false.
  apply H0.
  apply int_aux''; auto.
  intros.
  tryfalse.
Qed.



Lemma del_intlemma1 :forall x, Int.unsigned (Int.shru x  ($ 8)) < 64-> (if Int.unsigned (Int.modu (Int.shru x  ($ 8)) ($ Byte.modulus)) <=?
                                                                           Byte.max_unsigned
                                                                        then true
                                                                        else false) = true.
Proof.
  intros.
  remember ( (Int.shru x ($ 8))).
  clear Heqi.
  unfold Int.modu.
  unfold Byte.max_unsigned.
  unfold Byte.modulus.
  unfold Byte.wordsize.
  unfold Wordsize_8.wordsize.
  unfold two_power_nat.
  unfold shift_nat.
  simpl.
  repeat ur_rewriter.
  mauto.
  rewrite max_unsigned_val.
  assert (0<= Int.unsigned i mod 256<256).
  apply Z_mod_lt.
  omega.
  omega.
Qed.

Lemma del_intlemma2: forall x, Int.unsigned (Int.shru x  ($ 8)) < 64 ->   Int.unsigned (Int.modu (Int.shru x  ($ 8)) ($ Byte.modulus)) < Z.of_nat 64.
Proof.
  intros.
  remember ( (Int.shru x ($ 8))).
  clear Heqi.
  unfold Int.modu.
  unfold Byte.max_unsigned.
  unfold Byte.modulus.
  unfold Byte.wordsize.
  unfold Wordsize_8.wordsize.
  unfold two_power_nat.
  unfold shift_nat.
  simpl.
  repeat ur_rewriter.
  mauto.
  rewrite max_unsigned_val.
  assert (0<= Int.unsigned i mod 256<256).
  apply Z_mod_lt.
  omega.
  omega.
Qed.

Lemma mutexdel_intlemma1: forall x, Int.unsigned (Int.shru x ($ 8)) < 64 ->  (Int.modu (Int.shru x ($ 8)) ($ Byte.modulus)) = Int.shru x ($ 8).
Proof.
  intros.
  remember ( (Int.shru x ($ 8))).
  clear Heqi.
  unfold Int.modu.
  unfold Byte.max_unsigned.
  unfold Byte.modulus.
  unfold Byte.wordsize.
  unfold Wordsize_8.wordsize.
  unfold two_power_nat.
  unfold shift_nat.
  simpl.
  repeat ur_rewriter.
  mauto.
Qed.


Lemma ecbmod_get_or : forall ma a, EcbMod.get ma a = None \/ exists b, EcbMod.get ma a = Some b.
  intros.
  destruct (EcbMod.get ma a).
  right; eauto.
  left; auto.
Qed.

Lemma ecbmod_indom_eq_join_eq: forall ma mb ma' mb' mab, (forall a, EcbMod.indom ma a <-> EcbMod.indom ma' a) -> EcbMod.join ma mb mab -> EcbMod.join ma' mb' mab -> ma = ma'.

  intros.
  apply EcbMod.extensionality.
  intros.

  lets cond1 : @ecbmod_get_or ma a.
  destruct cond1; intros.
  unfold TcbMod.indom in H.
  set (H a).
  elim i; intros.
  rewrite H2 in *.
  
  lets cond2 : @ecbmod_get_or ma' a.
  destruct cond2; intros.
  rewrite H5.
  auto.
  set (H4 H5).
  inversion i0.
  rewrite H2 in H6.
  inversion H6.

  unfold EcbMod.indom in H.
  set (H a).
  copy H2.
  rewrite i in H3.
  clear H i.
  simpljoin.

  eapply EcbMod.join_get_get_l in H0.
  Focus 2.
  exact H2.
  eapply EcbMod.join_get_get_l in H1.
  Focus 2.
  exact H.
  rewrite H2, H.
  rewrite H0 in H1.
  auto.
Qed.

Lemma indom_join_a2b:
  forall ma ma' mb mb' mc,
    EcbMod.join ma mb mc ->
    EcbMod.join ma' mb' mc ->
    (forall a, EcbMod.indom mb a <-> EcbMod.indom mb' a) ->
    (forall a, EcbMod.indom ma a <-> EcbMod.indom ma' a).
Proof.
  intros.
  gen a.
  apply EcbMod.join_comm in H. 
  apply EcbMod.join_comm in H0.
  
  assert (mb = mb').
  eapply ecbmod_indom_eq_join_eq; eauto.
  subst mb'.
  assert (ma = ma').
  eapply EcbMod.join_unique_r; eauto.
  subst ma'.
  tauto.
Qed.

Lemma sig_indom_eq': forall key val val' a, EcbMod.indom (EcbMod.sig key val) a -> EcbMod.indom (EcbMod.sig key val') a.
Proof.
  intros.
  unfold EcbMod.indom in *.
  assert (a = key \/ a <> key).
  tauto.
  elim H0; intros.
  subst a.
  rewrite EcbMod.get_a_sig_a.
  eauto.
  go.
  false.
  simpljoin.
  assert (EcbMod.get (EcbMod.sig key val) a = None).
  apply EcbMod.get_a_sig_a'.
  go.
  rewrite H2 in H.
  tryfalse.
Qed.

Lemma sig_indom_eq: forall key val val' a, EcbMod.indom (EcbMod.sig key val) a <-> EcbMod.indom (EcbMod.sig key val') a.
Proof.
  intros.
  split; intros; eapply sig_indom_eq'; eauto.
Qed.

Lemma ecb_join_sig_eq: forall x x' key val val' y, EcbMod.join x (EcbMod.sig key val) y -> EcbMod.join x' (EcbMod.sig key val') y -> x' = x.
Proof.
  intros.
  eapply  ecbmod_indom_eq_join_eq; eauto.
  intros.
  eapply indom_join_a2b; eauto.
  apply sig_indom_eq.
Qed.

Lemma del_ecbmod_join_lemma0 : forall ma mb mc md me key val val', EcbMod.join ma (EcbMod.sig key val) me -> EcbMod.join mb (EcbMod.sig key val') mc -> EcbMod.join mc md me -> EcbMod.join mb md ma.
Proof.
  intros.
  assert (EcbMod.get me key = Some val).
  clear H1.
  eapply EcbMod.join_get_r; eauto.
  eapply EcbMod.get_a_sig_a; eauto.
  go.
  assert (EcbMod.get me key = Some val').
  eapply EcbMod.join_get_l; eauto.
  eapply EcbMod.join_get_r; eauto.
  eapply EcbMod.get_a_sig_a; eauto.
  go.
  rewrite H2 in H3.
  inverts H3.
  remember (EcbMod.sig key val') as mk.
  clear -H0 H H1.
  apply EcbMod.join_comm in H0.
  lets ttt: EcbMod.join_join_join3 H0 H1.


  eapply EcbMod.join3_join_join.
  eauto.
  apply EcbMod.join_comm in H.
  auto.
Qed.

Lemma mutex_no_owner_nil_wls : forall x e w0,  RLH_ECBData_P (DMutex (Vint32 x) Vnull) (e, w0) -> w0=nil.
Proof.
  intros.
  
  unfolds in H.
  destruct e; tryfalse.
  unfold MatchMutexSem in H; simpljoin.
  unfolds in H0; simpljoin.
  assert ( x0&ᵢ$ OS_MUTEX_KEEP_LOWER_8 <> $ OS_MUTEX_AVAILABLE \/ x0&ᵢ$ OS_MUTEX_KEEP_LOWER_8 = $ OS_MUTEX_AVAILABLE) by tauto.
  elim H7; intros.
  apply H5 in H8.
  simpljoin.
  inversion H8.
  apply H4 in H8.
  simpljoin.
  apply H0; auto.
Qed.


Lemma mutex_no_owner_nil_wls': forall x w,  RH_ECB_P (absmutexsem x None, w) -> w=nil.
Proof.
  intros.
  unfolds in H.
  simpljoin.
  apply H; auto.
Qed.
Local Open Scope list_scope.

Lemma  R_ECB_ETbl_P_high_ecb_mutex_acpt_hold :
  forall x9 i x x3 v'44 v'42 v'37 i6 v'50,
    R_ECB_ETbl_P x9
                 (V$OS_EVENT_TYPE_MUTEX
                   :: Vint32 i :: Vint32 x :: Vnull :: x3 :: v'44 :: nil, v'42) v'37 ->
    R_ECB_ETbl_P x9
                 (V$OS_EVENT_TYPE_MUTEX
                   :: Vint32 i
                   :: Vint32 (Int.or (x&ᵢ$ OS_MUTEX_KEEP_UPPER_8) i6)
                   :: Vptr (v'50, Int.zero) :: x3 :: v'44 :: nil, v'42) v'37.
Proof.
  intros.
  splits.
  unfolds in H.
  simpljoin.
  unfolds in H.
  simpljoin.
  unfolds .
  splits;  unfolds; auto.
  unfolds in H.
  simpljoin.
  clear -H0.
  unfolds in H0.
  simpljoin.
  unfolds.
  splits; unfolds; auto.
  unfolds in H.
  simpljoin.
  clear -H1.
  unfolds in H1.
  unfolds.
  auto.
Qed.

Lemma ecb_sig_join_sig'_set : forall a b c d b', EcbMod.joinsig a b c d -> EcbMod.joinsig a b' c (EcbMod.set d a b').
  intros.
  unfolds.
  unfolds in H.
  unfolds.
  intros.
  unfolds in H.
  lets aaa : H a0.
  assert (a = a0 \/ a<> a0) by tauto.
  elim H0; intros.
  subst.
  rewrite EcbMod.get_a_sig_a.
  rewrite EcbMod.get_a_sig_a in aaa.
  rewrite EcbMod.set_a_get_a.
  destruct (EcbMod.get c a0).
  inversion aaa.
  auto.
  apply CltEnvMod.beq_refl.
  apply CltEnvMod.beq_refl.
  apply CltEnvMod.beq_refl.
  
  rewrite EcbMod.get_a_sig_a'.
  rewrite EcbMod.get_a_sig_a' in aaa.
  rewrite EcbMod.set_a_get_a'.
  destruct (EcbMod.get c a0).
  destruct (EcbMod.get d a0).
  auto.
  auto.
  auto.
  apply tidspec.neq_beq_false; auto.
  apply tidspec.neq_beq_false; auto.
  apply tidspec.neq_beq_false; auto.
Qed.
(*
    Lemma RH_TCBList_ECBList_MUTEX_NODUP_ecbset_hold : forall v'34 v'35 a w v,(~exists x y, a=absmutexsem x y)->  RH_TCBList_ECBList_MUTEX_NODUP v'34 v'35 ->  RH_TCBList_ECBList_MUTEX_NODUP (EcbMod.set v'34 v (a, w)) v'35.
    Proof.
      intros.
      unfold RH_TCBList_ECBList_MUTEX_NODUP in *.
      intros.
      assert ( v = eid \/ v <> eid).
      tauto.
      elim H3; intros.
      subst eid.
      rewrite EcbMod.set_a_get_a in H2.
      intro.
      subst prio.
      apply H.
      inversion H2.
      eauto.
      apply CltEnvMod.beq_refl.
      rewrite EcbMod.set_a_get_a' in H2.
      eapply H0; eauto.
      apply tidspec.neq_beq_false; auto.
    Qed.

    Lemma RH_TCBList_ECBList_MUTEX_NODUP_ecbset_hold' :forall vv v'37 x v o1 o2,  RH_TCBList_ECBList_MUTEX_NODUP vv v'37 ->  EcbMod.get vv v = Some (absmutexsem x o1, nil) ->   RH_TCBList_ECBList_MUTEX_NODUP
                                                                                                                                                                                   (EcbMod.set vv v (absmutexsem x o2, nil))
                                                                                                                                                                                   v'37.
    Proof.
      intros.
      unfold RH_TCBList_ECBList_MUTEX_NODUP in *.
      intros.
      assert ( v = eid \/ v <> eid).
      tauto.
      elim H3; intros.
      subst v.
      rewrite EcbMod.set_a_get_a in H2.
      inverts H2.
      lets aaa: H H1 H0. 
      auto.
      go.
      rewrite EcbMod.set_a_get_a' in H2.
      lets aaa: H H1 H2.
      auto.
      go.
    Qed.
 *)
Lemma val_inj_eq
: forall i0 a: int32,
    val_inj
      (notint
         (val_inj
            (if Int.eq i0  a
             then Some (Vint32 Int.one)
             else Some (Vint32 Int.zero)))) = Vint32 Int.zero \/
    val_inj
      (notint
         (val_inj
            (if Int.eq i0  a
             then Some (Vint32 Int.one)
             else Some (Vint32 Int.zero)))) = Vnull ->
    i0 = a.
Proof.
  intros.
  destruct H; intros.
  int auto.
  apply unsigned_inj; auto.
  int auto.
Qed.


Lemma or_true_ltrue_rtrue: forall x y, val_inj (bool_or (val_inj (Some x)) (val_inj (Some y))) <> Vint32 Int.zero -> x <> Vint32 Int.zero \/  y <> Vint32 Int.zero.
Proof.
  intros.
  unfold bool_or in H.
  destruct x; destruct y; tryfalse;
  simpl in H;try solve[left; intro; tryfalse].
  right; intro; tryfalse.
  right; intro; tryfalse.
  unfold Int.ltu in H.
  2: right; intro; tryfalse.
  destruct ( zlt (Int.unsigned Int.zero) (Int.unsigned i)).
  left.
  intro.
  inverts H0.
  tryfalse.
  destruct ( zlt (Int.unsigned Int.zero) (Int.unsigned i0)).
  right; intro.
  inverts H0.
  try false.
  simpl in H.
  tryfalse.
Qed.

Lemma val_inj_or : forall (a b: bool),  
                     val_inj
                       (if b
                        then Some (Vint32 Int.one)
                        else Some (Vint32 Int.zero)) <> Vint32 Int.zero \/
                     val_inj
                       (if a
                        then Some (Vint32 Int.one)
                        else Some (Vint32 Int.zero)) <> Vint32 Int.zero ->
                     a = true \/ b= true.
Proof.                                                  
  intros.
  elim H; intros.
  pauto.
  pauto.
Qed.


Lemma le65535shr8mod255self:forall i1, Int.unsigned i1 <= 65535 ->  (Int.modu (Int.shru i1 ($ 8)) ($ Byte.modulus)) = (Int.shru i1 ($ 8)).
Proof. 
  intros.

  unfold Int.modu.
  unfold Int.shru.
  unfold Byte.max_unsigned.
  unfold Byte.modulus.
  unfold Byte.wordsize.
  unfold Wordsize_8.wordsize.
  unfold two_power_nat.

  repeat ur_rewriter; simpl.
  Focus 2.
  unfold shift_nat.
  simpl.
  int auto.
  Focus 2.
  rewrite Byte.Zshiftr_div_two_p.
  simpl.
  unfold two_power_pos.
  unfold shift_pos.
  simpl.
  apply Zdiv_interval_2.
  int auto.
  omega.
  int auto.
  omega.
  omega.
  unfold shift_nat.
  simpl.

  rewrite Coqlib.Zmod_small.
  auto.
  rewrite Byte.Zshiftr_div_two_p.
  simpl.
  unfold two_power_pos.
  unfold shift_pos.
  simpl.
  apply Zdiv_interval_1.
  omega.
  omega.
  omega.
  simpl.
  int auto.
  omega.
Qed.

Lemma acpt_int_lemma00 : forall i1,  Int.unsigned (i1 &ᵢ $ OS_MUTEX_KEEP_UPPER_8) <= 65535.
  intros.
  unfold OS_MUTEX_KEEP_UPPER_8.
  rewrite Int.and_commut.
  eapply Zle_trans.
  eapply Int.and_le.
  ur_rewriter.
  omega.
Qed.


Lemma acpt_int_lemma0 : forall i1,  Int.unsigned i1 <= 65535 ->   Int.unsigned (i1 &ᵢ $ OS_MUTEX_KEEP_UPPER_8) <= 65535.
Proof fun x y => acpt_int_lemma00 x.

  Lemma acpt_intlemma1 : forall i1,  Int.unsigned i1 <= 65535 ->  Int.unsigned (Int.modu (Int.shru i1 ($ 8)) ($ Byte.modulus)) <= Byte.max_unsigned.
  Proof.
    introv HHH.
    unfold Int.modu.
    unfold Int.shru.
    unfold Byte.max_unsigned.
    unfold Byte.modulus.
    unfold Byte.wordsize.
    unfold Wordsize_8.wordsize.
    unfold two_power_nat.
    assert ( Z.pos (shift_nat 8 1) = 256).
    simpl; auto.
    rewrite H.
    simpl.
    clear H.
    assert (Int.unsigned i1 >= 0) by int auto.
    remember (Int.unsigned i1).
    assert (0<=   Z.shiftr z 8 mod 256 < 256).
    apply Z_mod_lt.
    omega.
    assert (0<=z<=65535) by omega.
    clear Heqz.
    assert ( 0 <= Z.shiftr z 8 <= Int.max_unsigned).

    rewrite Z.shiftr_div_pow2.
    simpl.
    unfold Z.pow_pos.
    simpl.
    apply Zdiv_interval_2.
    int auto.
    omega.
    int auto.
    omega.
    omega.
    repeat ur_rewriter. 
    omega.
    auto.
    int auto.
    auto.
  Qed.

  Lemma acpt_intlemma2: forall i1,  val_inj
                                      (if Int.eq (i1&ᵢ$ OS_MUTEX_KEEP_LOWER_8) ($ OS_MUTEX_AVAILABLE)
                                       then Some (Vint32 Int.one)
                                       else Some (Vint32 Int.zero)) <> Vint32 Int.zero ->  i1 &ᵢ$ OS_MUTEX_KEEP_LOWER_8 = $ OS_MUTEX_AVAILABLE.
  Proof.
    intros.
    remember (Int.eq (i1&ᵢ$ OS_MUTEX_KEEP_LOWER_8) ($ OS_MUTEX_AVAILABLE)) as h.
    destruct h.
    Focus 2.
    simpl in H.
    tryfalse.
    clear H.
    lets aa: Int.eq_spec (   i1&ᵢ$ OS_MUTEX_KEEP_LOWER_8) ($ OS_MUTEX_AVAILABLE) .
    rewrite <- Heqh in aa.
    auto.
  Qed.



  Lemma acpt_intlemma3: forall x y,Int.unsigned x<64 ->  Int.or (y&ᵢ$ OS_MUTEX_KEEP_UPPER_8) x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 = x.
  Proof.
    intros.
    unfold Int.and.
    unfold Int.or.
    unfold OS_MUTEX_KEEP_UPPER_8.
    unfold OS_MUTEX_KEEP_LOWER_8.
    repeat ur_rewriter.
    apply unsigned_inj.
    ur_rewriter.
    apply Byte.equal_same_bits.
    intros.
    rewrite Z.land_spec.
    rewrite Z.lor_spec.
    rewrite Z.land_spec.
    assert (0<=i<8 \/ i>=8).
    omega.
    elim H1; intros.
    rewrite tblemma1; auto.
    rewrite tblemma2; auto.
    rewrite andb_true_r.
    rewrite andb_false_intro2; auto.
    rewrite (tblemma3 i 255); auto.
    rewrite andb_false_intro2; auto.
    cut ( Z.testbit (Int.unsigned x) i = false).
    auto.
    apply tblemma3.
    int auto.
    auto.
    omega.
    assert (0<= Z.land (Z.lor (Z.land (Int.unsigned y) 65280) (Int.unsigned x)) 255 <=255).
    split.
    apply Z_land_range_lo_r.
    omega.      
    apply Zland_le_r.
    omega.
    int auto.
    assert (0<=  Z.land  (Int.unsigned y)  65280 <= 65280).
    split.
    apply Z_land_range_lo_r.
    omega.      
    apply Zland_le_r.
    omega.
    int auto.
    Focus 2.
    assert (0<=  Z.land  (Int.unsigned y)  65280 <= 65280).
    split.
    apply Z_land_range_lo_r.
    omega.      
    apply Zland_le_r.
    omega.
    int auto.
    
    split.
    apply Z_lor_range_lo.
    apply Z_land_range_lo_r.
    omega.      
    int auto.

    apply Z_lor_range_hi.
    split.
    apply Z_land_range_lo_r.
    omega.
    assert (  Z.land  (Int.unsigned y)  65280 <= 65280).
    apply Zland_le_r.
    omega.
    int auto.
    int auto.
  Qed.

  Lemma acpt_intlemma7: forall y, Int.unsigned y < 64 -> Int.shru y ($ 8) = $0.
  Proof.
    intros.
    mauto.
  Qed.


  Lemma acpt_intlemma9: forall i6 x, Int.unsigned i6 < 64->   Int.ltu (Int.shru x ($ 8)) i6 = true-> Int.unsigned x <= 65535.
  Proof.
    intros.
    int auto.
    assert  (Int.unsigned (Int.shru x ($ 8)) < 64).
    omega.
    clear -H2.
    unfold Int.shru in H2.
    repeat ur_rewriter_in H2.
    rewrite Int.Zshiftr_div_two_p in H2.
    unfold two_p in H2.
    unfold two_power_pos in H2.
    unfold shift_pos in H2.
    simpl in H2.
    change 64 with (64 * 256 / 256) in H2.
    eapply div_lt_lt in H2.
    simpl in H2.
    omega.
    omega.
    omega.
    ur_rewriter.
    rewrite Z.shiftr_div_pow2.
    simpl.
    unfold Z.pow_pos.
    simpl.
    apply div_in_intrange.
    int auto.
    omega.
    omega.
  Qed.
  
  Lemma acpt_intlemma10: forall x ,Int.unsigned x <= 65535 -> Int.unsigned (Int.shru x ($ 8)) <= 255.
  Proof.
    intros.
    assert (Int.unsigned x <= 65279 \/ Int.unsigned x > 65279) by omega.
    elim H0; intros.
    Focus 2.
    assert ( 65279 < Int.unsigned x <= 65535) by omega.
    clear -H2.
    mauto.
    clear -H1.
    unfold Int.shru.
    repeat ur_rewriter.

    rewrite Int.Zshiftr_div_two_p.
    unfold two_p.
    unfold two_power_pos.
    unfold shift_pos.
    simpl.
    apply Z.div_le_upper_bound.
    omega.
    omega.
    omega.
    rewrite Int.Zshiftr_div_two_p.
    unfold two_p.
    unfold two_power_pos.
    unfold shift_pos.
    simpl.
    apply  div_in_intrange.
    int auto.
    omega.
    omega.

  Qed.


  Lemma acpt_intlemma4: forall x y,Int.unsigned x <= 65535 -> Int.unsigned y <64 ->(Int.shru  (Int.or (x&ᵢ$ OS_MUTEX_KEEP_UPPER_8) y) ($ 8)) = Int.shru x ($ 8).
  Proof.
    intros.

    rewrite <- Int.or_shru.
    rewrite (acpt_intlemma7 y); auto.
    rewrite acpt_intlemma8.
    rewrite <- Int.and_shru.
    unfold OS_MUTEX_KEEP_UPPER_8.
    unfold Int.shru at 2.
    do 2 ur_rewriter.
    unfold Z.shiftr.
    unfold Z.shiftl.
    simpl.
    lets aaa:  acpt_intlemma10 H.
    remember (Int.shru x ($ 8)).
    clear -aaa.
    mauto.
  Qed.


  Lemma acpt_intlemma5 : forall x i6, Int.unsigned i6 <64 ->  Int.or (x&ᵢ$ OS_MUTEX_KEEP_UPPER_8) i6&ᵢ$ OS_MUTEX_KEEP_LOWER_8 = $ 255 -> False.
  Proof.
    intros.
    rewrite  acpt_intlemma3 in H0; auto.
    rewrite H0 in H.
    int auto.
  Qed.

  Lemma acpt_intlemma15: forall n, Z.log2 (two_power_nat n) = Z_of_nat n.
  Proof.
    intros.
    rewrite two_power_nat_equiv.
    apply Z.log2_bits_unique.
    apply Z.pow2_bits_true.
    apply Zle_0_nat.
    intros.
    apply Z.pow2_bits_false.
    omega.
  Qed.
  Lemma acpt_intlemma14: forall a n,a>0 ->( a< two_power_nat n <-> (forall x, x >= Z_of_nat n -> Z.testbit a x = false)).
  Proof.
    intros.
    split.
    intros.
    eapply Int.Ztestbit_above.
    instantiate (1:=n).
    omega.
    omega.
    intros.
    assert (0<a) by omega.
    lets aaa : Z.bit_log2 H1.
    apply Z.log2_lt_cancel.

    rewrite acpt_intlemma15.
    
    assert (Z.log2 a < Z.of_nat n \/ Z.log2 a >= Z.of_nat n).
    omega.
    elim H2; intros.
    auto.
    false.
    simpl.
    lets aa: H0 H3.
    rewrite aa in aaa.
    inversion aaa.
  Qed.


  Lemma acpt_intlemma12 : forall a b n, a < two_power_nat n -> b < two_power_nat n -> Z.lor a b < two_power_nat n.
  Proof.
    intros.
    unfold two_p.

    assert (a<0 \/ a>=0).
    omega.
    elim H1; intros.
    lets aaa: two_power_nat_pos n.
    assert (Z.lor a b <0).
    rewrite Z.lor_neg.
    left; auto.
    omega.
    assert (b<0 \/ b>=0).
    omega.
    elim H3; intros.
    lets aaa: two_power_nat_pos n.
    assert (Z.lor a b <0).
    rewrite Z.lor_neg.
    right; auto.
    clear -H5 aaa.
    omega.
    clear H1 H3.

    assert (Z.lor a b >=0 \/ Z.lor a b <0).
    omega.
    elim H1; intros.
    Focus 2.
    rewrite Z.lor_neg in H3.
    elim H3; intros.
    omega.
    omega.

    assert ( a= 0 \/ a>0) .
    omega.
    elim H5; intros.
    subst.
    rewrite Z.lor_0_l.
    auto.

    assert ( b= 0 \/ b>0) .
    omega.
    elim H7; intros.
    subst.
    rewrite Z.lor_0_r.
    auto.


    assert (  Z.lor a b= 0 \/  Z.lor a b>0) .
    omega.
    elim H9; intros.
    subst.
    rewrite Z.lor_eq_0_iff in H10.
    elim H10; intros; omega.

    lets aaa: acpt_intlemma14 H6.
    lets aab: acpt_intlemma14 H8.
    lets aac: acpt_intlemma14 H10.
    
    rewrite aac.
    rewrite aaa in H.
    rewrite aab in H0.
    intros.
    rewrite Z.lor_spec.
    apply orb_false_iff.
    split.
    apply H.
    auto.
    apply H0.
    auto.
  Qed.
  Lemma acpt_intlemma6: forall x p, Int.unsigned p<=65535 -> Int.unsigned (Int.or (x&ᵢ$ OS_MUTEX_KEEP_UPPER_8) p) <= 65535.
  Proof.
    intros.
    cut (  Int.unsigned (Int.or (x&ᵢ$ OS_MUTEX_KEEP_UPPER_8) p) < 65536).
    intros; omega.
    
    unfold Int.or.
    unfold Int.and.
    unfold OS_MUTEX_KEEP_UPPER_8.
    repeat ur_rewriter.
    change 65536 with (two_power_nat 16).
    apply acpt_intlemma12.
    assert (  Z.land (Int.unsigned x) 65280 <= 65280).
    apply  Zland_le_r.
    omega.
    change (two_power_nat 16) with 65536.
    remember ( Z.land (Int.unsigned x) 65280 ).
    int auto.
    change (two_power_nat 16) with 65536.
    omega.
    assert (  Z.land (Int.unsigned x) 65280 <= 65280).
    apply  Zland_le_r.
    omega.
    apply Z_land_range.
    int auto.

    int auto.
    apply Z_lor_range.
    apply Z_land_range.
    int auto.

    int auto.
    int auto.
    apply Z_land_range.
    int auto.
    int auto.
  Qed.

  Lemma intlemma13 : forall x y, Int.unsigned x < Int.unsigned y -> Int.modu x y = x.
  Proof.
    intros.
    unfold Int.modu.
    rewrite Coqlib.Zmod_small.
    
    int auto.
    int auto.
  Qed.

  Lemma intlemma11:forall x x0, val_inj
                                  (bool_or
                                     (val_inj
                                        (if Int.ltu x0 x
                                         then Some (Vint32 Int.one)
                                         else Some (Vint32 Int.zero)))
                                     (val_inj
                                        (if Int.eq x0 x
                                         then Some (Vint32 Int.one)
                                         else Some (Vint32 Int.zero)))) = Vint32 Int.zero \/
                                val_inj
                                  (bool_or
                                     (val_inj
                                        (if Int.ltu x0 x
                                         then Some (Vint32 Int.one)
                                         else Some (Vint32 Int.zero)))
                                     (val_inj
                                        (if Int.eq x0 x
                                         then Some (Vint32 Int.one)
                                         else Some (Vint32 Int.zero)))) = Vnull ->   Int.ltu (x) x0 = true.
  Proof.
    intros.
    apply val_inj_i1_i2_lt.
    rewrite Int.eq_sym.
    exact H.
  Qed.
  
  Lemma eventtype_neq_mutex:
    forall v'38 v'21 i1 i0 i2 x2 x3 v'42 v'40 v'22 v'23 v'41 v'24 v'34 v'35 v'49 s P v'43 v'45 v'44 v'46,
      length v'21 = length v'23-> 
      ECBList_P v'38 Vnull
                (v'21 ++
                      ((Vint32 i1 :: Vint32 i0 :: Vint32 i2 :: x2 :: x3 :: v'42 :: nil,
                        v'40) :: nil) ++ v'22) (v'23 ++ (v'41 :: nil) ++ v'24) v'34 v'35 ->
      ECBList_P v'38 (Vptr (v'49, Int.zero)) v'21 v'23 v'43 v'35 ->
      EcbMod.join v'43 v'45 v'34 ->
      EcbMod.joinsig (v'49, Int.zero) v'46 v'44 v'45 ->
      false = Int.eq i1 ($  OS_EVENT_TYPE_MUTEX) ->
      s|= AEventData
       (Vint32 i1 :: Vint32 i0 :: Vint32 i2 :: x2 :: x3 :: v'42 :: nil) v'41 ** P ->
      s |= AEventData
        (Vint32 i1 :: Vint32 i0 :: Vint32 i2 :: x2 :: x3 :: v'42 :: nil) v'41 **
        [|~ exists x y z, EcbMod.get v'34 (v'49,Int.zero) = Some (absmutexsem x y, z) |] ** P.
  Proof.
    intros.

    apply ecblist_p_decompose in H0;auto.
    simpljoin.
    
    assert (x1 = Vptr (v'49, Int.zero) /\ x = v'43).
    eapply ecblist_p_eqh;eauto.
    instantiate (1:=v'34).
    eapply EcbMod.join_sub_l;eauto.
    eapply EcbMod.join_sub_l;eauto.
    destruct H8;subst.
    destruct v'41.
    Focus 4.
    {
      unfold AEventData in *.
      sep normal in H5.
      sep split in H5.
      unfolds in H8;simpl in H8.
      inverts H8.
      rewrite Int.eq_true in H4;tryfalse.
    }
    Unfocus.
    {
      sep auto.
      simpl in H6.
      simpljoin.
      destruct x1.
      destruct e;tryfalse.
      simpljoin.
      intro.
      simpljoin.
      inverts H6.
      lets Hx:EcbMod.join_joinsig_get H7 H10.
      rewrite H16 in Hx.
      tryfalse.
    }
    {
      sep auto.
      simpl in H6.
      simpljoin.
      destruct x1.
      destruct e;tryfalse.
      simpljoin.
      intro.
      simpljoin.
      inverts H6.
      lets Hx:EcbMod.join_joinsig_get H7 H10.
      rewrite H11 in Hx.
      tryfalse.
    }
    {
      sep auto.
      simpl in H6.
      simpljoin.
      destruct x1.
      destruct e;tryfalse.

      simpljoin.
      intro.
      simpljoin.
      inverts H6.
      lets Hx:EcbMod.join_joinsig_get H7 H10.
      rewrite H11 in Hx.
      tryfalse.
    }
  Qed.

  Lemma Mutex_owner_set' : forall x y z w u ,
                             RH_TCBList_ECBList_MUTEX_OWNER x y ->
                             RH_TCBList_ECBList_MUTEX_OWNER (EcbMod.set x z (absmutexsem w None, u)) y.
  Proof.
    intros.
    unfold RH_TCBList_ECBList_MUTEX_OWNER in *.
    intros.
    assert  ( z = eid \/ z<> eid) by tauto.
    elim H1; intros.
    subst eid.
    rewrite EcbMod.set_a_get_a in H0.
    inverts H0.
    go.
    rewrite EcbMod.set_a_get_a' in H0.
    eapply H; eauto.
    go.
  Qed.

  Lemma mutex_ex_wt_ex_owner :forall i0 o x4 x5,  RH_ECB_P (absmutexsem i0 o, x4 :: x5) -> exists yy, o= Some yy.
  Proof.
    intros.
    unfolds in H.
    simpljoin.
    destruct o.
    eauto.
    false.
    apply H1.
    intro; tryfalse.
    auto.
  Qed.
  Goal  forall x,  val_inj
                     (if Int.ltu ($ 8) Int.iwordsize then Some (Vint32 x) else None) =
                   Vint32 x.
  intros.
  unfold Int.iwordsize.
  unfold Int.zwordsize.
  unfold Int.wordsize.
  unfold Wordsize_32.wordsize.
  int auto.
  simpl.
  omega.
Save intlemma0.
Goal forall x, Int.ltu Int.zero x = false -> x= Int.zero.
Proof.
  intros.
  int auto.
  lets xxx: Int.unsigned_range x.
  assert (Int.unsigned x = 0).
  omega.
  apply unsigned_inj.
  auto.
Save int_ltu_zero_false_is_zero.
Goal forall x y , val_inj  (bool_or x y ) =Vint32 Int.zero \/ val_inj (bool_or x y) = Vnull ->
                  x = Vint32 Int.zero /\ y = Vint32 Int.zero.
Proof.
  intros.
  elim H; intros.
  unfold bool_or in H0.
  destruct x; tryfalse.
  destruct y; tryfalse.

  remember (Int.ltu Int.zero i || Int.ltu Int.zero i0 ).
  destruct b;
    simpl in H0.
  inversion H0.
  apply eq_sym in Heqb.
  apply orb_false_iff in Heqb.
  elim Heqb; intros.
  apply int_ltu_zero_false_is_zero in H1.
  apply int_ltu_zero_false_is_zero in H2.
  subst i.
  subst i0.
  tauto.

  unfold bool_or in H0.
  destruct x; tryfalse.
  destruct y; tryfalse.
  destruct ( Int.ltu Int.zero i || Int.ltu Int.zero i0); simpl in H0; tryfalse.
Save val_inj_bool_or_lemma0.
Goal forall x y, 
       val_inj
         (notint
            (val_inj
               (if Int.eq x y
                then Some (Vint32 Int.one)
                else Some (Vint32 Int.zero)))) = Vint32 Int.zero ->   x= y.
Proof.
  intros.
  remember (Int.eq x y).
  destruct b.
  lets ttt: Int.eq_spec x y. 
  rewrite <- Heqb in ttt.
  auto.
  simpl in H.
  unfold Int.notbool in H.
  rewrite eq_zero_zero in H.
  inversion H.
Save val_inj_not_eq.
Goal forall ls x, (x< length ls)%nat -> exists t, nth_val x ls = Some t.
Proof.
  intro.
  induction ls.
  intros.
  inversion H.
  intro.
  induction x.
  intros.
  simpl.
  eauto.
  intros.
  simpl.
  apply IHls.
  simpl in H.
  omega.
Save ls_has_nth_val.

Lemma post_intlemma3 : forall x1, Int.unsigned x1 < 64 -> Int.unsigned (Int.shru x1 ($ 3)) < 8.
Proof.
  intros.
  mauto.
Qed.
Lemma post_intlemma4 : forall x1, Int.unsigned x1 < 64 -> Int.unsigned (Int.and x1 ($ 7)) < 8.
Proof.
  intros.
  mauto.
Qed.

Lemma postintlemma1 : forall x,  (if Int.unsigned (Int.modu x ($ Byte.modulus)) <=?
                                     Byte.max_unsigned
                                  then true
                                  else false) = true.
Proof.
  intros.
  assert ( Int.unsigned (Int.modu x ($ Byte.modulus)) <=? Byte.max_unsigned = true).
  unfold Int.modu.
  unfold Byte.max_unsigned.
  change Byte.modulus with 256.
  repeat ur_rewriter.
  apply Zle_imp_le_bool.
  simpl.
  lets bb: @Z_mod_lt (Int.unsigned x) 256.
  omega.
  lets bb: @Z_mod_lt (Int.unsigned x) 256.
  change Int.max_unsigned with (65536*65536-1).
  omega.
  rewrite H.
  auto.
Qed.

Lemma postintlemma2 : forall x,  Int.unsigned (Int.modu x ($ Byte.modulus)) <=?
                                 Byte.max_unsigned =true.
Proof.
  intro.
  lets fff : postintlemma1 x.
  destruct ( Int.unsigned
               (Int.modu x ($ Byte.modulus)) <=?
             Byte.max_unsigned).
  auto.
  auto.
Qed.

Lemma postintlemma3 : forall x,  Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) <= 255.
Proof.
  intros.
  rewrite Int.and_commut.
  apply le255_and_le255.
  unfold OS_MUTEX_KEEP_LOWER_8.
  ur_rewriter.
  omega.      
Qed.

Lemma postintlemma4 :  Int.ltu ($ 3) Int.iwordsize = true.
Proof.
  auto.
Qed.



Lemma osmapvallist_int8u : (array_type_vallist_match Int8u OSMapVallist).
Proof.
  unfolds.
  unfold OSMapVallist.
  splits; auto; unfolds.
Qed.
Lemma osmapvallist_length8 : length OSMapVallist = 8%nat.
Proof.
  reflexivity.
Qed.


Lemma intlt2nat: forall x y, Int.unsigned x < y -> (Z.to_nat (Int.unsigned x) < Z.to_nat y)%nat.
Proof.
  intros.
  assert (y=y-1+1).
  omega.
  rewrite H0.
  apply int_unsigned_le_z2nat_lt.
  omega.
Qed.

Lemma intlt2intlt: forall x y, Int.unsigned x < y -> Int.unsigned x < Z.of_nat (Z.to_nat y).
Proof.
  intros.
  assert (y >= 0).
  assert (Int.unsigned x >= 0).
  int auto.
  omega.
  assert (Z.of_nat (Z.to_nat y) = y).
  lets fff: Coqlib.nat_of_Z_eq H0.
  unfold nat_of_Z in fff.
  auto.
  rewrite H1.
  auto.
Qed.

Lemma ruletypevalmatch8u : forall x, rule_type_val_match Int8u x = true ->exists tt,  x = Vint32 tt /\ Int.unsigned tt <= 255.
Proof.
  intros.
  unfolds in H.
  destruct x; tryfalse.
  change Byte.max_unsigned with 255 in H.
  eexists; eauto.
  split; eauto.
  apply Zle_bool_imp_le.
  destruct ( Int.unsigned i <=? 255).
  auto.
  auto.
Qed.

Lemma mutexpost_intlemma1: forall x, Int.unsigned x < 64 ->  (Int.modu x ($ Byte.modulus)) = x.
Proof.
  intros.
  unfold Int.modu.
  unfold Byte.max_unsigned.
  unfold Byte.modulus.
  unfold Byte.wordsize.
  unfold Wordsize_8.wordsize.
  unfold two_power_nat.
  unfold shift_nat.
  simpl.
  repeat ur_rewriter.
  mauto.
Qed.


Lemma int8ule255: forall x2, true = rule_type_val_match Int8u (Vint32 x2) ->  Int.unsigned x2 <=255.
Proof.
  intros.
  unfold rule_type_val_match in H.

  remember ( Int.unsigned x2 <=?  Byte.max_unsigned).
  destruct b; tryfalse.
  apply leb_bytemax_true_elim.
  auto.
Qed.


Lemma postintlemma2' : forall x,  Int.unsigned (Int.modu x ($ Byte.modulus)) <=255.

Proof.
  intros.

  unfold Int.modu.
  unfold Byte.max_unsigned.
  change Byte.modulus with 256.
  repeat ur_rewriter.
  lets bb: @Z_mod_lt (Int.unsigned x) 256.
  omega.
  lets bb: @Z_mod_lt (Int.unsigned x) 256.
  change Int.max_unsigned with (65536*65536-1).
  omega.
Qed.
Lemma ifE : forall e:bool, (if e then true else false) = true <-> e = true.
  intros.
  split; intros; destruct e; auto; tryfalse.
Qed.

Lemma seporI : forall  P Q, P ==>  P\\//Q.
Proof.
  intros.
  eapply adisj_mono.
  intro.
  intros.
  sep auto.
  instantiate (1:=Afalse).
  intro.
  intro.
  simpl in H0.
  tryfalse.
  simpl.
  left; auto.
Qed.

Lemma seporI' : forall  P Q, Q ==>  P\\//Q.
Proof.
  intros.
  eapply adisj_mono.
  instantiate (1:=Afalse).
  intro.
  intros.
  simpl in H0.
  inversion H0.
  intro.
  intros.
  sep auto.
  simpl.
  right.
  auto.
Qed.

Lemma RH_TL_EL_MUTEX_OWNER_hold: forall tls tid els eid prio st msg o1 pp w1 w2 pr, TcbMod.get tls tid = Some (prio, st, msg) -> EcbMod.get els eid = Some (absmutexsem pr o1, w1) -> RH_TCBList_ECBList_MUTEX_OWNER els tls -> RH_TCBList_ECBList_MUTEX_OWNER (EcbMod.set els eid (absmutexsem pr (Some (tid, pp)), w2)) tls.
Proof.
  intros.
  unfold RH_TCBList_ECBList_MUTEX_OWNER in *.
  intros.
  assert ( eid0 = eid \/ eid0<> eid) by tauto.
  elim H3; intros.
  subst eid0.
  
  rewrite EcbMod.set_a_get_a in H2.
  inverts H2.
  eauto.
  go.
  
  rewrite EcbMod.set_a_get_a' in H2.
  eapply H1; eauto.
  go.
Qed.


Lemma post_exwt_succ_pre_mutex
: forall (v'36 v'13 : vallist) (v'12 : int32) 
         (v'32 : block) (v'15 : int32) (v'24 : block) 
         (v'35 v'0 : val) (v'8 : tid) (v'9 v'11 : EcbMod.map)
         (x : val) (x0 : maxlen) (x1 : waitset)
         (v'6 v'10 : EcbMod.map) (v'38 v'69 v'39 : int32) 
         (v'58 : block) (b : taskstatus) 
         (c :msg) (v'62 v'7 : TcbMod.map) 
         (vhold : addrval) pr o a,
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
    GetHWait v'7 x1 (v'58, Int.zero) /\
    TcbMod.get v'7 (v'58, Int.zero) = Some (a, b, c)
.
Proof.
  (*  eapply post_exwt_succ_pre_mutex; eauto.
  rewrite H126 in H61.
  inverts H61.
  rewrite H128 in H63.
  inverts H61.
  H128 : nth_val' (Z.to_nat (Int.unsigned x2)) v'50 = Vint32 v'63
  H134 : nth_val' (Z.to_nat (Int.unsigned x2)) OSMapVallist = Vint32 v'66
  H128 : nth_val' (Z.to_nat (Int.unsigned v'62)) v'50 = Vint32 v'63
 nth_val' (Z.to_nat (Int.unsigned v'57)) OSUnMapVallist = Vint32 x2
 nth_val' (Z.to_nat (Int.unsigned v'57)) OSUnMapVallist = Vint32 v'62
 nth_val' (Z.to_nat (Int.unsigned x2)) v'50 = Vint32 x4
 nth_val' (Z.to_nat (Int.unsigned x4)) OSUnMapVallist = Vint32 x5
   *)
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
  unfold get in *; simpl in *.
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

(* TODO no omega hoare_assign_struct' *)

(* Ltac hoare_assign_struct' :=
 *   let s := fresh in
 *   let H := fresh in
 *   match goal with
 *     | |- {|_ , _, _, _, _, _|}|- _ {{?P}}?x ′ → _ =ₑ _ {{_}} =>
 *       match find_lvarmapsto P x with
 *         | some ?m =>
 *           match find_aop P with
 *             | none _ => fail 1
 *             | some ?n =>
 *               hoare lifts (n :: m :: nil) pre;
 *                 match goal with
 *                   | |-
 *                     {|_ , _, _, _, _, _|}|- _
 *                     {{ <|| _ ||>  ** LV x @ _ ∗ |-> Vptr ?l ** ?P'}}_ {{_}} =>
 *                     match find_ptrstruct P' l with
 *                       | none _ => fail 2
 *                       | some ?o =>
 *                         hoare lifts (1%nat :: 2%nat :: S (S o) :: nil)
 *                               pre; eapply assign_rule_struct_aop;
 *                         [ intro s; split; intro H; exact H
 *                         | match goal with
 *                             | |- ?tp = STRUCT _ ­{ _ }­ => try unfold tp
 *                           end; auto
 *                         | simpl; auto
 *                         | unfold id_nth; simpl; auto
 *                         | simpl; auto
 *                         | intros; auto
 *                         | intros; auto
 *                         | symbolic
 *                             execution
 *                         | apply
 *                             assign_type_match_true;
 *                           simpl; auto
 *                         | simpl
 *                         | simpl; auto ]
 *                     end
 *                 end
 *           end
 *         | none _ =>
 *           match find_dom_lenv P with
 *             | (none _, _) => fail 3
 *             | (some ?m, Some ?ls) =>
 *               let ret1 := constr:(var_notin_dom x ls) in
 *               let ret2 := eval compute in ret1 in
 *                   match ret2 with
 *                     | true =>
 *                       match find_aop P with
 *                         | none _ => fail 1
 *                         | some ?n =>
 *                           match find_gvarmapsto P x with
 *                             | none _ => fail 4
 *                             | some ?o =>
 *                               hoare lifts (n :: m :: o :: nil) pre;
 *                                 match goal with
 *                                   | |-
 *                                     {|_ , _, _, _, _, _|}|- _
 *                                     {{ <|| _ ||>  **
 *                                            A_dom_lenv _ **
 *                                            GV x @ _ ∗ |-> Vptr ?l ** ?P'}}_ {{_}} =>
 *                                     match find_ptrstruct P' l with
 *                                       | none _ => fail 5
 *                                       | some ?p =>
 *                                         hoare lifts
 *                                               (1%nat
 *                                                 :: 2%nat
 *                                                 :: 3%nat :: S (S (S p)) :: nil)
 *                                               pre; eapply assign_rule_struct_g_aop;
 *                                         [ intro s; split; intro H; exact H
 *                                         | simpl; auto
 *                                         | match goal with
 *                                             | |- ?tp = STRUCT _ ­{ _ }­ =>
 *                                               try unfold tp
 *                                           end; auto
 *                                         | simpl; auto
 *                                         | unfold id_nth; simpl; auto
 *                                         | simpl; auto
 *                                         | intros; auto
 *                                         | intros; auto
 *                                         | symbolic
 *                                             execution
 *                                         | apply
 *                                             assign_type_match_true;
 *                                           simpl; auto
 *                                         | simpl
 *                                         | simpl; auto ]
 *                                     end
 *                                 end
 *                           end
 *                       end
 *                     | false => fail 6
 *                   end
 *           end
 *       end
 *   end.
 * Ltac meew :=  eapply seq_rule;[ let s:= fresh in let H:= fresh in eapply forward_rule2; [hoare_assign_struct' | intros s H; exact H]| idtac]. *)


Lemma val_injsimpl :forall i x2 x5 x, val_inj
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
                                                    (if Int.ltu ((x2<<ᵢ$ 3)+ᵢx5) (x>>ᵢ$ 8)
                                                     then Some (Vint32 Int.one)
                                                     else Some (Vint32 Int.zero)))
                                                 (val_inj
                                                    (if Int.eq ((x2<<ᵢ$ 3)+ᵢx5) (x>>ᵢ$ 8)
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
                                                    (if Int.ltu ((x2<<ᵢ$ 3)+ᵢx5) (x>>ᵢ$ 8)
                                                     then Some (Vint32 Int.one)
                                                     else Some (Vint32 Int.zero)))
                                                 (val_inj
                                                    (if Int.eq ((x2<<ᵢ$ 3)+ᵢx5) (x>>ᵢ$ 8)
                                                     then Some (Vint32 Int.one)
                                                     else Some (Vint32 Int.zero)))))) = Vnull -> 
                                      i = $0 \/  (Int.ltu ((x2<<ᵢ$ 3)+ᵢx5) (x>>ᵢ$ 8) = false /\ ((x2<<ᵢ$ 3)+ᵢx5) <> (x>>ᵢ$ 8)).
Proof.
  intros.
  elim H; intros.
  remember (Int.eq i ($ 0)).
  remember (Int.ltu ((x2<<ᵢ$ 3)+ᵢx5) (x>>ᵢ$ 8)).
  remember (Int.eq ((x2<<ᵢ$ 3)+ᵢx5) (x>>ᵢ$ 8)).
  destruct b.
  simpl in H0.
  clear -Heqb.
  left.
  int auto.
  apply unsigned_inj.
  auto.
  Focus 2.
  destruct ( Int.eq i ($ 0)); destruct ( Int.ltu ((x2<<ᵢ$ 3)+ᵢx5) (x>>ᵢ$ 8)); destruct ( Int.eq ((x2<<ᵢ$ 3)+ᵢx5) (x>>ᵢ$ 8)); tryfalse.
  right.
  destruct b0; destruct b1;
  simpl in H0.
  change (Int.ltu Int.zero Int.one) with true in H0.
  simpl in H0.
  change (Int.notbool Int.zero) with Int.one in H0.
  change (Int.ltu Int.zero Int.one) with true in H0.
  simpl in H0.
  tryfalse.
  change (Int.ltu Int.zero Int.one) with true in H0.
  simpl in H0.
  change (Int.notbool Int.zero) with Int.one in H0.
  change (Int.ltu Int.zero Int.one) with true in H0.
  simpl in H0.
  tryfalse.
  change (Int.ltu Int.zero Int.zero) with false in H0.
  simpl in H0.

  change (Int.ltu Int.zero Int.one) with true in H0.
  simpl in H0.

  change (Int.notbool Int.zero) with Int.one in H0.

  change (Int.ltu Int.zero Int.one) with true in H0.

  simpl in H0.
  tryfalse.

  clear -Heqb0 Heqb1.
  splits.
  simpljoin.
  intro.
  rewrite H in Heqb1.
  clear -Heqb1.
  int auto.
Qed.

Lemma neq_imp_neqq :
  forall x y,
    x <> y  -> 
    Z.to_nat (Int.unsigned x) <>  (Z.to_nat (Int.unsigned y)).
Proof.
  intros.
  introv Hf.
  apply H.
  lets Heqx :  Z2Nat.inj Hf;
    try
      eapply Int.unsigned_range; eauto.
  eapply unsigned_inj; auto.
Qed.

Lemma tcbjoin_mod:
  forall x y ma mb mc  m,
    TcbJoin x y ma mb ->
    TcbMod.join mc mb m ->
    TcbMod.get m x = Some y.
Proof.
  intros.
  unfold TcbJoin in H.
  unfold join in *; simpl in *.
  unfold sig in *; simpl in *.

  go.
Qed.

(**)

Lemma return_r_pt_p :
  forall v'52 x t m x10 v'45 v'43 v'39 v'30 v'51,
    array_type_vallist_match OS_TCB ∗ v'30 ->
    length v'30 = 64%nat ->
    Int.unsigned ((x>>ᵢ$ 8)>>ᵢ$ 3) < 8 ->
    Int.unsigned ((x>>ᵢ$ 8)&ᵢ$ 7) < 8 ->
    Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7) < 8 ->
    Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)>>ᵢ$ 3) < 8 ->
    Int.unsigned (x>>ᵢ$ 8) < 64 ->
    Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) < 64 ->
    TcbJoin (v'52, Int.zero) ((x>>ᵢ$ 8), t, m) x10 v'45 ->
    TcbMod.join v'43 v'45 v'39 ->
    Int.ltu (x>>ᵢ$ 8) (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = true ->
    nth_val((Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8))))   v'30 = Some (Vptr v'51) ->
    R_PrioTbl_P v'30 v'39 v'51 ->
    R_PrioTbl_P
      (update_nth_val (Z.to_nat (Int.unsigned (x>>ᵢ$ 8)))
                      (update_nth_val (Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)))
                                      v'30 (Vptr (v'52, Int.zero))) (Vptr v'51))
      (TcbMod.set v'39 (v'52, Int.zero) (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8, t, m))
      v'51.
Proof.
  introv Har Hlen Hi1 Hi2 Hi3 Hi4 Hi5 Hi6 Hjo1.
  introv Hjo2 Hnneq Hntss  Hrp.
  unfolds.
  splits.
  introv Hp Hnth Hneq.
  unfolds in Hrp.
  destruct Hrp as (Hrp1 & Hrp2 & Hrp3).
  remember ( ∘(Int.unsigned prio)) as pm.
  remember ( (Z.to_nat (Int.unsigned (x>>ᵢ$ 8)))) as pn.
  remember ((Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)))) as px.
  assert (pm <> pn \/ pm = pn) as Hart by tauto.
  destruct Hart as [Hart1 | Hart2].
  lets Hres : nth_upd_neq  Hart1 Hnth.
  assert (pm <> px \/ pm = px) as Harst by tauto.
  destruct Harst as [Harst1 | Harst2].
  lets Hres2 : nth_upd_neq  Harst1 Hres.
  lets Hasb : Hrp1 Hneq; eauto.
  rewrite <- Heqpm; auto. 
  unfolds in Hrp3.
  assert ( tcbid =  (v'52, Int.zero) \/ tcbid <>  (v'52, Int.zero)) by tauto.
  destruct H.
  subst tcbid.

  lets Hsa : tcbjoin_mod Hjo1 Hjo2.
  destruct Hasb as (sst & m11 & Hgs).
  unfold get in *; simpl in *.
  rewrite Hgs in Hsa.
  inverts Hsa.
  rewrite Heqpn in Hart1.
  rewrite Heqpm in Hart1.
  clear - Hart1.
  unfold nat_of_Z in Hart1.
  tryfalse.
  destruct Hasb as (sst & m11 & Hgs).
  exists sst m11.
  rewrite TcbMod.set_sem.
  erewrite tidspec.neq_beq_false; eauto.
  rewrite Harst2 in Hres.
  lets Heqs: nth_upd_eq  Hres.
  inverts Heqs.
  exists t m.
  rewrite Heqpm in Harst2 .
  rewrite Heqpx in Harst2.
  assert (prio =x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 ).
  clear - Harst2 Hi6 Hp.
  remember (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) as xx.
  clear Heqxx.
  unfold nat_of_Z in Harst2.
  lets Has : Z2Nat.inj Harst2.  
  clear.
  int auto.
  clear .
  int auto.
  eapply unsigned_inj; eauto.
  rewrite H.
  rewrite TcbMod.set_sem.
  erewrite tidspec.eq_beq_true; eauto.
  rewrite Hart2 in Hnth.
  lets Heqs: nth_upd_eq  Hnth.
  inverts Heqs.
  tryfalse.

  introv Hgets .
  destruct Hrp as (Hrp1 & Hrp2 & Hrp3).
  assert ( tcbid =  (v'52, Int.zero) \/ tcbid <>  (v'52, Int.zero)) by tauto.
  destruct H.
  subst tcbid.
  rewrite TcbMod.set_sem in Hgets.
  erewrite tidspec.eq_beq_true in Hgets; eauto.
  inverts Hgets.
  unfold nat_of_Z.
  remember ( (Z.to_nat (Int.unsigned (x>>ᵢ$ 8)))) as pn.
  remember ((Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)))) as px.
  assert (px = pn \/ px <> pn) as Hasrt by tauto.
  lets Hsa : tcbjoin_mod Hjo1 Hjo2.
  lets Hasc : Hrp2 Hsa.
  destruct Hasc.
  split; auto.
  destruct Hasrt.
  apply Int.ltu_inv in Hnneq.
  rewrite Heqpn in H1.
  rewrite Heqpx in H1.
  clear -Hnneq H1.
  lets Heqx :  Z2Nat.inj H1;
    try
      eapply Int.unsigned_range; eauto.
  omega.
  eapply nth_upd_neqrev; eauto.
  assert (px < length v'30)%nat.
  clear - Hlen Heqpx Hi6.
  rewrite Hlen.
  remember (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) as Hk.
  rewrite Heqpx.
  clear Heqpx  HeqHk Hlen.
  mauto.
  lets Hass : ls_has_nth_val  H2.
  destruct Hass.
  eapply update_nth.
  eauto.
  rewrite TcbMod.set_sem in Hgets.
  erewrite tidspec.neq_beq_false in Hgets; eauto.
  lets Hress : Hrp2 Hgets.
  destruct Hress.
  split; auto.
  lets Hsa : tcbjoin_mod Hjo1 Hjo2.
  lets Hesx : Hrp3 H Hgets Hsa.

  
  eapply nth_upd_neqrev; eauto.
  unfold nat_of_Z.
  eapply  neq_imp_neqq ; eauto.
  remember  ∘(Int.unsigned prio) as px.
  remember  (Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) as py.

  assert (px <> py \/ px = py) as Hasss by tauto.
  destruct Hasss.
  eapply nth_upd_neqrev; eauto.
  rewrite H2 in *.
  rewrite H0 in Hntss.
  inverts Hntss.
  tryfalse.

  unfolds.
  intros.
  unfolds in Hrp.
  destruct Hrp as (Hpr1 & Hpr2 & Hpr3).
  unfolds in Hpr3.
  assert ( (v'52, Int.zero) <> tid \/  (v'52, Int.zero) = tid ) by tauto.
  destruct H2.
  rewrite TcbMod.set_sem in H0.
  rewrite tidspec.neq_beq_false in H0; eauto.
  assert ( (v'52, Int.zero) <> tid' \/  (v'52, Int.zero) = tid' ) by tauto.
  destruct H3.
  rewrite TcbMod.set_sem in H1.
  rewrite tidspec.neq_beq_false in H1; eauto.
  rewrite TcbMod.set_sem in H1.
  rewrite tidspec.eq_beq_true in H1; eauto.
  inverts H1.
  assert (  prio <> x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 \/   prio = x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) by tauto.
  destruct H1; auto.
  subst prio.
  lets Hasds : Hpr2 H0.
  destruct Hasds.
  unfold nat_of_Z in H1.
  rewrite Hntss in H1.
  inverts H1.
  tryfalse.
  subst tid.
  rewrite TcbMod.set_sem in H1.
  rewrite tidspec.neq_beq_false in H1; eauto.
  rewrite TcbMod.set_sem in H0.
  rewrite tidspec.eq_beq_true in H0; eauto.
  inverts H0.
  assert (  prio' <> x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 \/   prio' = x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) by tauto.
  destruct H0; auto.
  lets Hasds : Hpr2 H1.
  destruct Hasds.
  unfold nat_of_Z in H2.
  subst prio'.
  rewrite Hntss in H2.
  inverts H2.
  tryfalse.
Qed.




Lemma rtbl_remove_RL_RTbl_PrioTbl_P_hold':
  forall (prio : Z) (y bitx : int32) (rtbl : vallist) 
         (ry : int32) (ptbl : vallist) (av : addrval),
    0 <= prio < 64 ->
    y = $ prio>>ᵢ$ 3 ->
    bitx = $ 1<<ᵢ($ prio&ᵢ$ 7) ->
    nth_val ∘(Int.unsigned y) rtbl = Some (Vint32 ry) ->
    RL_RTbl_PrioTbl_P rtbl ptbl av ->
    RL_RTbl_PrioTbl_P
      (update_nth_val ∘(Int.unsigned y) rtbl (Vint32 (ry&ᵢInt.not bitx)))
      (update_nth_val  (∘prio)  ptbl (Vptr av))
      av.
Proof.
  introv Hpr Hy Hb Hnth Hrl.
  unfolds in Hrl.
  unfolds.
  introv Hp Hpro.
  subst .
  remember ($ prio) as pri.
  assert ( 0 <= Int.unsigned pri < 64).
  clear -Hpr Heqpri.
  subst.
  int auto.
  assert (p = pri \/ p <> pri) by tauto.
  destruct H0.
  subst p.
  eapply  prio_update_self_not_in in Hpro; eauto.
  tryfalse.
  lets Hxs : prio_neq_in_tbl H0 Hnth Hpro; eauto.
  lets Has : Hrl Hxs; eauto.
  simpljoin.
  exists x.
  splits; auto.
  assert ((Z.to_nat (Int.unsigned p)) <> ∘prio).
  unfold nat_of_Z.
  introv Hf.
  apply H0.
  lets Hsas : Z2Nat.inj Hf; eauto.
  rewrite <- Hsas.
  clear - H5.
  int auto.
  eapply nth_upd_neqrev; eauto.
Qed.

Lemma nth_val_upd_ex :
  forall x y vl v,  
    (x < length vl)%nat ->
    exists t, nth_val x (update_nth_val y vl v) = Some t.
Proof.
  inductions x; destruct vl.
  simpl in *.
  intros.
  omega.
  intros.
  simpl.
  destruct y.
  simpl.
  eauto.
  simpl in H.
  simpl.
  eauto.
  intros.
  simpl in H.
  omega.
  intros.
  simpl in *.
  assert (x < length vl)%nat.
  omega.
  destruct y.
  simpl.
  lets Hxas :  IHx O vl v  H0.
  simpljoin.
  destruct vl.
  simpl in H1.
  tryfalse.
  simpl in H1.
  simpl.
  destruct x.
  eauto.
  eauto.
  simpl.
  eapply IHx; eauto.
Qed.

Lemma nth_val_exx:
  forall x vl,
    (x < length vl)%nat ->
    exists v, nth_val x vl = Some v.
Proof.
  inductions x.
  destruct vl.
  intros.
  simpl in H.
  omega.
  simpl.
  eauto.
  destruct vl.
  simpl.
  intros.
  omega.
  simpl.
  intros.
  eapply IHx.
  omega.
Qed.

Lemma RL_RTbl_PrioTbl_P_set:
  forall x vhold rtbl ptbl x4 x5 ptcb_addr,
    Int.unsigned x < 64 ->
    (length rtbl = 8)%nat ->
    (length ptbl = 64)%nat ->
    (ptcb_addr, Int.zero) <> vhold -> 
    nth_val' (Z.to_nat (Int.unsigned (x&ᵢ$ 7))) OSMapVallist =
    Vint32 x4 ->
    nth_val' (Z.to_nat (Int.unsigned (x>>ᵢ$ 3)))
             rtbl = Vint32 x5 ->
    RL_RTbl_PrioTbl_P rtbl ptbl vhold ->
    RL_RTbl_PrioTbl_P
      (update_nth_val (Z.to_nat (Int.unsigned (x>>ᵢ$ 3)))
                      rtbl (Vint32 (Int.or x5 x4)))
      (update_nth_val (Z.to_nat (Int.unsigned x))
                      ptbl
                      (Vptr (ptcb_addr, Int.zero))) vhold.
Proof.
  introv Hx Hlen Hlen2 Hneq Hnth1 Hnth2 Hrl.
  lets Hxa : math_mapval_core_prop Hnth1.
  clear - Hx.
  mauto.
  rewrite Hxa.
  unfolds.
  introv Hp Hprio.
  unfolds in Hrl.
  assert (p <> x \/ p = x) by tauto.
  destruct H.
  assert (  prio_in_tbl p rtbl).
  Require Import OSQPostPure.
  eapply prio_set_rdy_in_tbl_rev with (prio0:=p)(prio:=x); eauto.
  clear -Hx.
  split; auto.
  clear.
  int auto.
  apply   nth_val'_imply_nth_val.
  rewrite Hlen.
  clear - Hx.
  mauto.
  unfold nat_of_Z.
  auto.
  lets Hxas : Hrl Hp H0.
  destruct Hxas as (tid & Hnt & Hne).
  exists tid.
  split; auto.
  eapply nth_upd_neqrev; eauto.
  introv Hf.
  apply H.
  lets Has : Z2Nat.inj Hf.  
  clear .
  int auto.
  clear.
  int auto.
  eapply unsigned_inj; eauto.
  exists  (ptcb_addr, Int.zero).
  split; auto.
  rewrite H.
  assert ( (Z.to_nat (Int.unsigned x)) < length ptbl)%nat.
  rewrite Hlen2.
  clear - Hx.
  mauto.
  lets Hxs: nth_val_exx H0.
  simpljoin.
  eapply update_nth; eauto.
Qed.


Lemma nth_val_le_len_is_none: forall x ls, (x >= length ls)%nat -> nth_val x ls = None.
Proof.
  intros x ls.
  gen x.
  induction ls.
  intros.
  auto.
  induction x.
  intros.
  simpl in H.
  omega.
  intros.
  simpl.
  apply IHls.
  simpl in H.
  omega.
Qed.

Lemma double_update_exchange :forall a b c d ls, a<>b -> (a<length ls)%nat -> (b<length ls)%nat  ->(forall x, nth_val x (update_nth_val a (update_nth_val b ls d) c) =nth_val x ( update_nth_val b (update_nth_val a ls c) d)).
Proof.
  intros.
  assert (a < length (update_nth_val b ls d))%nat.
  erewrite <- update_nth_val_length_eq.
  auto.
  assert (b < length (update_nth_val a ls c))%nat.
  erewrite <- update_nth_val_length_eq.
  auto.

  lets aa: ls_has_nth_val H0.
  lets bb: ls_has_nth_val H1.
  lets cc: ls_has_nth_val H2.
  lets dd: ls_has_nth_val H3.
  assert ( x < length ls \/ x >= length ls)%nat as strange_name by omega.
  simpljoin.
  assert ( x = a \/ x <> a) by tauto.
  destruct H8; intros.
  subst x.

  erewrite (@nth_upd_neqrev _ _ _ _ _ H).
  erewrite update_nth.
  eauto.
  2:erewrite update_nth.
  2:eauto.
  eauto.
  eauto.


  assert ( x = b \/ x <> b) by tauto.
  destruct H9; intros.
  subst x.

  assert (b<>a) by auto.
  erewrite (nth_upd_neqrev _ _ H9).
  erewrite update_nth.
  eauto.
  eauto.
  erewrite update_nth.
  eauto.
  eauto.

  destruct strange_name; intros.
  lets ee:  ls_has_nth_val H10.
  simpljoin.

  erewrite (nth_upd_neqrev _ _ H9).
  erewrite (nth_upd_neqrev _ _ H8).
  Focus 2.
  erewrite (nth_upd_neqrev _ _ H9).
  2:eauto.
  eauto.
  eauto.
  erewrite (nth_upd_neqrev _ _ H8).
  eauto.
  eauto.

  rewrite nth_val_le_len_is_none.
  rewrite nth_val_le_len_is_none.
  auto.

  erewrite <- update_nth_val_length_eq.
  erewrite <- update_nth_val_length_eq.
  auto.
  erewrite <- update_nth_val_length_eq.
  erewrite <- update_nth_val_length_eq.
  auto.
Qed.


Lemma double_update_exchangable4rlrt_pt_p : forall a b c d l1 l2 vh, a<>b -> (a<length l2)%nat -> (b<length l2)%nat -> RL_RTbl_PrioTbl_P l1 (update_nth_val a (update_nth_val b l2 c) d) vh ->  RL_RTbl_PrioTbl_P l1 (update_nth_val b (update_nth_val a l2 d) c) vh  . 
Proof.
  intros.
  unfolds.
  intros.
  rewrite double_update_exchange; auto.
Qed.


Lemma return_rl_rt_pt_p : forall x  v'52 v'39 v'36 v'30 v'51 x11 x12 t1,
                            (v'52, Int.zero) <> v'51 ->
                            Int.ltu (x>>ᵢ$ 8) (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = true ->
                            array_type_vallist_match OS_TCB ∗ v'30 ->
                            length v'30 = 64%nat ->
                            array_type_vallist_match Int8u v'36 ->
                            length v'36 = ∘OS_RDY_TBL_SIZE ->
                            Int.unsigned ((x>>ᵢ$ 8)>>ᵢ$ 3) < 8 ->
                            Int.unsigned ((x>>ᵢ$ 8)&ᵢ$ 7) < 8 ->
                            Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7) < 8 ->
                            Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)>>ᵢ$ 3) < 8 ->
                            Int.unsigned (x>>ᵢ$ 8) < 64 ->
                            Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) < 64 ->
                            nth_val' (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)))
                                     OSMapVallist = Vint32 x11 ->
                            true = rule_type_val_match Int8u (Vint32 x11) ->
                            Int.unsigned x12 <= 255 ->
                            nth_val' (Z.to_nat (Int.unsigned ((x>>ᵢ$ 8)>>ᵢ$ 3))) v'36 =
                            Vint32 x12 ->
                            nth_val' (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)>>ᵢ$ 3)))
                                     (update_nth_val (Z.to_nat (Int.unsigned ((x>>ᵢ$ 8)>>ᵢ$ 3))) v'36
                                                     (val_inj
                                                        (and (Vint32 x12) (Vint32 (Int.not ($ 1<<ᵢ((x>>ᵢ$ 8)&ᵢ$ 7))))))) =
                            Vint32 t1 ->
                            Int.unsigned t1 <= 255 ->
                            RL_RTbl_PrioTbl_P v'36 v'30 v'51 ->  RH_CurTCB (v'52, Int.zero) v'39 ->
                            RL_RTbl_PrioTbl_P
                              (update_nth_val
                                 (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)>>ᵢ$ 3)))
                                 (update_nth_val (Z.to_nat (Int.unsigned ((x>>ᵢ$ 8)>>ᵢ$ 3))) v'36
                                                 (val_inj
                                                    (and (Vint32 x12) (Vint32 (Int.not ($ 1<<ᵢ((x>>ᵢ$ 8)&ᵢ$ 7)))))))
                                 (val_inj
                                    (or
                                       (Vint32 t1)
                                       (Vint32 x11))))
                              (update_nth_val (Z.to_nat (Int.unsigned (x>>ᵢ$ 8)))
                                              (update_nth_val (Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)))
                                                              v'30 (Vptr (v'52, Int.zero))) (Vptr v'51)) v'51.
Proof.
  introv aaaaaa.
  intros.


  apply  double_update_exchangable4rlrt_pt_p.

  intro.
  Focus 4.
  rename x into tag.
  lets pr_eq : math_prio_eq H8.
  lets prio_eq : math_prio_eq H9.

  remember ((tag>>ᵢ$ 8)>>ᵢ$ 3) as pr_y.
  remember ((tag>>ᵢ$ 8)&ᵢ$ 7) as pr_x.
  remember  ((tag&ᵢ$ OS_MUTEX_KEEP_LOWER_8)>>ᵢ$ 3) as prio_y.
  remember  ((tag&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7) as prio_x.


  rewrite pr_eq, prio_eq in *.
  rewrite <- H14.



  Lemma rl_rtbl_priotbl_p_hold':
    forall (v'36 : vallist) (v'12 : int32) (v'13 : vallist)
           (v'38 v'69 v'39 : int32) (v'58 : block) (v'40 v'41 v'57 : int32)
           (v'37 : vallist) (vhold : block * int32),
      (v'58, Int.zero) <> vhold ->
      RL_RTbl_PrioTbl_P v'37 v'36 vhold ->
      True ->
      Int.unsigned v'12 <= 255 ->
      array_type_vallist_match Int8u v'13 ->
      length v'13 = ∘OS_EVENT_TBL_SIZE ->
      array_type_vallist_match Int8u v'37 ->
      length v'37 = ∘OS_EVENT_TBL_SIZE ->
      nth_val' (Z.to_nat (Int.unsigned v'12)) OSUnMapVallist = Vint32 v'38 ->
      Int.unsigned v'38 <= 7 ->
      nth_val' (Z.to_nat (Int.unsigned v'38)) v'13 = Vint32 v'69 ->
      Int.unsigned v'69 <= 255 ->
      True ->
      Int.unsigned v'39 <= 7 ->
      (*nth_val' (Z.to_nat (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39))) v'36 =
  Vptr (v'58, Int.zero) *)
      length v'36 = 64%nat ->
      nth_val' (Z.to_nat (Int.unsigned v'39)) OSMapVallist = Vint32 v'40 ->
      Int.unsigned v'40 <= 128 ->
      nth_val' (Z.to_nat (Int.unsigned v'38)) OSMapVallist = Vint32 v'41 ->
      Int.unsigned v'41 <= 128 ->
      True ->
      True ->
      Int.unsigned v'57 <= 255 ->
      array_type_vallist_match Int8u v'37 ->
      length v'37 = ∘OS_RDY_TBL_SIZE ->
      RL_RTbl_PrioTbl_P
        (update_nth_val (Z.to_nat (Int.unsigned v'38)) v'37
                        (val_inj
                           (or (nth_val' (Z.to_nat (Int.unsigned v'38)) v'37) (Vint32 v'40))))
        (update_nth_val (Z.to_nat (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39)))  v'36  (Vptr (v'58, Int.zero)) ) vhold.
  Proof.
    introv Hnvhold.
    intros.
    unfold  RL_RTbl_PrioTbl_P  in *.
    auto.
    (*  unfolds in H17.
  unfolds in H18.*)
    intros.
    unfolds in H23.
    assert (  p&ᵢ$ 7  = p&ᵢ$ 7 ) by auto.
    assert (Int.shru p ($ 3) = Int.shru p ($ 3)) by auto.
    assert ( ∘(Int.unsigned (Int.shru p ($ 3))) <> Z.to_nat (Int.unsigned v'38) \/
             ∘(Int.unsigned (Int.shru p ($ 3))) = (Z.to_nat (Int.unsigned v'38)))%nat.
    tauto.

    lets Hy : math_unmap_get_y H1 H6.
    assert ( ∘(Int.unsigned (Int.shru p ($ 3))) <∘OS_EVENT_TBL_SIZE)%nat.
    clear -H22.
    mauto.
    lets Ha : nthval'_has_value H4  H27; eauto.
    destruct Ha as (x&Hnth & Htru).
    lets Hnt : nth_val'_imp_nth_val_int Hnth.
    destruct H26.
    assert ( nth_val ∘(Int.unsigned (Int.shru p ($ 3)))
                     (update_nth_val (Z.to_nat (Int.unsigned v'38)) v'37
                                     (val_inj
                                        (or (nth_val' (Z.to_nat (Int.unsigned v'38)) v'37)
                                            (Vint32 v'40)))) = Some (Vint32 x)).
    eapply nth_upd_neqrev; eauto.
    lets Hb : H23 H24 H25 H28 .
    assert (Int.unsigned (Int.shru p ($ 3))<8). 
    clear - H22.
    mauto.
    remember (Int.shru p ($3)) as px. 
    assert ($ Z.of_nat ∘(Int.unsigned px) = px).
    clear - H29.
    mauto.
    assert (prio_in_tbl p v'37 ).
    unfolds.
    intros.
    subst.
    rewrite H33 in Hnt.
    inverts Hnt.
    auto.
    lets Hsas : H H31; eauto.
    destruct Hsas as (tid1 & Has1 & Hnq).
    assert ((Z.to_nat (Int.unsigned p) = (Z.to_nat (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39)))
             \/ (Z.to_nat (Int.unsigned p)<> (Z.to_nat (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39)))))).
    tauto.
    destruct H32.
    rewrite H32 in *.
    exists ( (v'58, Int.zero)).
    splits; auto.
    eapply update_nth; eauto.
    exists tid1.
    split; auto.
    eapply nth_upd_neqrev; eauto.

    assert (  p&ᵢ$ 7 = v'39 \/  p&ᵢ$ 7 <> v'39).
    tauto.
    destruct H28.
    subst v'39.
    lets Hzzp : int_usigned_tcb_range H22.
    destruct Hzzp.
    remember (Int.shru p ($3)) as px.
    assert (px = v'38).
    clear - Hy  H29 H26.
    gen H26.
    mauto.
    subst v'38.
    subst px.
    assert ( (((Int.shru p ($ 3))<<ᵢ$ 3)+ᵢ(p&ᵢ$ 7)) = p).
    clear -H22.
    mauto.
    (*
  rewrite H30 in H12.
  apply nth_val'_imp_nth_val_vptr in H12.
     *)
    assert (Z.to_nat (Int.unsigned p) < length v'36)%nat.
    clear - H22 H12.
    rewrite H12.
    simpl.
    clear H12.
    unfold Pos.to_nat.
    simpl.
    mauto.
    lets Hass : ls_has_nth_val  H31.
    destruct Hass.
    rewrite  H30.
    exists  (v'58, Int.zero).
    splits; auto.
    eapply update_nth; eauto.
    
    assert ( prio_in_tbl p v'37).
    unfolds.
    intros.
    lets Hzzp : int_usigned_tcb_range H22.
    destruct Hzzp.
    remember (Int.shru p ($3)) as px.
    remember (p&ᵢ$ 7) as py.
    assert ( px = v'38).
    clear -Hy H33 H26.
    gen H26.
    mauto.
    subst v'38.
    rewrite H30 in H31.
    rewrite Hnt in H31.
    inverts H31.
    remember ((val_inj
                 (or (nth_val' (Z.to_nat (Int.unsigned px)) v'37)
                     (Vint32 v'40)))) as v.
    unfold val_inj in Heqv.
    rewrite H26 in Hnth.
    rewrite Hnth in Heqv.
    unfold or in Heqv.
    subst v.
    assert ( nth_val ∘(Int.unsigned (px))
                     (update_nth_val (Z.to_nat (Int.unsigned px)) v'37
                                     (Vint32 (Int.or z v'40))) =Some (Vint32 (Int.or z v'40))).
    rewrite <- H26.
    eapply update_nth; eauto.
    lets Hd : H23 H31; eauto.
    rewrite Int.and_commut in Hd.
    rewrite Int.and_or_distrib in Hd.
    lets Hzzps :  math_nth_8_eq_zero'  H13   H28; eauto; try omega.
    rewrite Int.and_commut in Hzzps.
    rewrite H29 in Hd.
    rewrite Hzzps in Hd.
    rewrite Int.or_zero in Hd.
    rewrite Int.and_commut in Hd.
    rewrite H29.
    auto.
    lets Hasas : H H29; eauto.
    destruct Hasas as (tiss & Ha1 & aas).
    assert ((Z.to_nat (Int.unsigned p) = (Z.to_nat (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39)))
             \/ (Z.to_nat (Int.unsigned p)<> (Z.to_nat (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39)))))).
    tauto.
    destruct H30.
    rewrite H30 in *.
    exists ( (v'58, Int.zero)).
    splits; auto.
    eapply update_nth; eauto.
    exists tiss.
    split; auto.
    eapply nth_upd_neqrev; eauto.
  Qed.


  Lemma unsignedsimpllemma : forall x y, y < 8 -> Int.unsigned x = y -> x = Int.repr y.
  Proof.
    intros.
    rewrite <- (Int.unsigned_repr y) in H0.
    apply unsigned_inj in H0.
    auto.
    change Int.max_unsigned with (65536 * 65536-1).
    simpl.
    rewrite <- H0 in *.
    int auto.
  Qed.

  Lemma exists_some_unmap_is_x : forall x, Int.unsigned x < 8 -> nth_val' (Z.to_nat (Int.unsigned ($ 1 <<ᵢ x))) OSUnMapVallist = Vint32 x /\ Int.unsigned ($ 1 <<ᵢ x) <= 128.
  Proof.
    intros.
    mauto_dbg.
    destruct H.
    unfold Int.shl.
    rewrite H.
    apply unsignedsimpllemma in H ; [subst | omega].
    repeat ur_rewriter.
    split; simpl; auto; try omega.
    simpl; int auto.
    
    destruct H.
    unfold Int.shl.
    rewrite H.
    apply unsignedsimpllemma in H ; [subst | omega].
    repeat ur_rewriter.
    split; simpl; auto; try omega.
    simpl; int auto.
    destruct H.
    unfold Int.shl.
    rewrite H.
    apply unsignedsimpllemma in H ; [subst | omega].
    repeat ur_rewriter.
    split; simpl; auto; try omega.
    simpl; int auto.
    destruct H.
    unfold Int.shl.
    rewrite H.
    apply unsignedsimpllemma in H ; [subst | omega].
    repeat ur_rewriter.
    split; simpl; auto; try omega.
    simpl; int auto.
    destruct H.
    unfold Int.shl.
    rewrite H.
    apply unsignedsimpllemma in H ; [subst | omega].
    repeat ur_rewriter.
    split; simpl; auto; try omega.
    simpl; int auto.

    destruct H.
    unfold Int.shl.
    rewrite H.
    apply unsignedsimpllemma in H ; [subst | omega].
    repeat ur_rewriter.
    split; simpl; auto; try omega.
    simpl; int auto.
    destruct H.
    unfold Int.shl.
    rewrite H.
    apply unsignedsimpllemma in H ; [subst | omega].
    repeat ur_rewriter.
    split; simpl; auto; try omega.
    simpl; int auto.
    unfold Int.shl.
    rewrite H.
    apply unsignedsimpllemma in H ; [subst | omega].
    repeat ur_rewriter.
    split; simpl; auto; try omega.
    simpl; int auto.


  Qed.

  lets aaa :  exists_some_unmap_is_x H4.
  lets aaa5 :  exists_some_unmap_is_x H5.
  lets aaa6 :  exists_some_unmap_is_x H6.
  lets aaa7 :  exists_some_unmap_is_x H7.
  simpljoin.

  assert ((Z.to_nat (Int.unsigned prio_y)) <  ∘OS_RDY_TBL_SIZE)%nat.
  unfold OS_RDY_TBL_SIZE.
  clear -H7; mauto.
  lets ffff:nthval'_has_value H2 H3 H26.
  simpljoin.

  eapply rl_rtbl_priotbl_p_hold'.
  auto.
  
  
  eapply  rtbl_remove_RL_RTbl_PrioTbl_P_hold'; eauto.
  clear -H4 H5; mauto.
  clear -H4 H5; mauto.
  clear -H4 H5; mauto.

  apply nth_val'_imp_nth_val_int.
  auto.

  auto.
  6:exact H18.
  omega.
  go.
  go.
  6: auto.
  8:auto.

  apply array_type_vallist_match_int8u_update_hold_255.
  auto.
  omega.
  omega.
  clear -H5.
  mauto.
  auto.
  rewrite update_nth_val_len_eq.
  auto.
  omega.
  eauto.
  apply int8ule255.
  auto.
  omega.
  rewrite update_nth_val_len_eq.
  auto.
  clear -H10 H6.
  mautoext.
  Lemma xmapis1shlx : forall x, Int.unsigned x < 8 -> nth_val' (Z.to_nat (Int.unsigned x)) OSMapVallist = Vint32 ($ 1 <<ᵢ x).
  Proof.
    intros.
    mauto.
  Qed.
  apply xmapis1shlx.
  omega.
  clear -H7.
  mauto.
  trivial.
  auto.
  apply int8ule255.
  eauto.
  apply array_type_vallist_match_int8u_update_hold_255.
  go.
  omega.
  go.
  clear -H5; mauto.
  go.
  rewrite update_nth_val_len_eq.
  auto.
  apply Z2Nat.inj in H18.
  apply unsigned_inj in H18.
  rewrite H18 in H.
  remember  (x>>ᵢ$ 8).
  clear -H.
  int auto.
  remember  (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8).
  clear;
    int auto.
  remember  (x>>ᵢ$ 8).
  clear;
    int auto.

  rewrite H1; clear -H9; remember  (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8);  mauto.
  rewrite H1; clear -H8; remember  (x>>ᵢ$ 8);  mauto.
Qed.

Lemma return_rl_t_g_p :
  forall v'36 i7 x v'52 w x8 x11 x12 t1 t11,
    array_type_vallist_match Int8u v'36 ->
    length v'36 = ∘OS_RDY_TBL_SIZE ->
    Int.unsigned i7 <= 255 ->
    Int.unsigned ((x>>ᵢ$ 8)>>ᵢ$ 3) < 8 ->
    Int.unsigned ((x>>ᵢ$ 8)&ᵢ$ 7) < 8 ->
    Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7) < 8 ->
    Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)>>ᵢ$ 3) < 8 ->
    Int.unsigned (x>>ᵢ$ 8) < 64 ->
    Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) < 64 ->
    val_inj (val_eq (Vint32 t11) (V$0)) <> Vint32 Int.zero ->
    nth_val' (Z.to_nat (Int.unsigned ((x>>ᵢ$ 8)>>ᵢ$ 3)))
             (update_nth_val (Z.to_nat (Int.unsigned ((x>>ᵢ$ 8)>>ᵢ$ 3))) v'36
                             (val_inj
                                (and (Vint32 x12) (Vint32 (Int.not ($ 1<<ᵢ((x>>ᵢ$ 8)&ᵢ$ 7))))))) =
    Vint32 t11 -> 
    nth_val'
      (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)>>ᵢ$ 3)))
      OSMapVallist = Vint32 x8 ->
    true = rule_type_val_match Int8u (Vint32 x8) ->
    nth_val' (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)))
             OSMapVallist = Vint32 x11 ->
    true = rule_type_val_match Int8u (Vint32 x11) ->
    Int.unsigned x12 <= 255 ->
    nth_val' (Z.to_nat (Int.unsigned ((x>>ᵢ$ 8)>>ᵢ$ 3))) v'36 =
    Vint32 x12 ->
    nth_val' (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)>>ᵢ$ 3)))
             (update_nth_val (Z.to_nat (Int.unsigned ((x>>ᵢ$ 8)>>ᵢ$ 3))) v'36
                             (val_inj
                                (and (Vint32 x12) (Vint32 (Int.not ($ 1<<ᵢ((x>>ᵢ$ 8)&ᵢ$ 7))))))) =
    Vint32 t1 ->
    Int.unsigned t1 <= 255 ->
    RL_Tbl_Grp_P v'36 (Vint32 i7) -> 
    prio_in_tbl ($ OS_IDLE_PRIO) v'36 ->
    RLH_ECBData_P (DMutex (Vint32 x) (Vptr (v'52, $ 0)))
                  (absmutexsem (x>>ᵢ$ 8)
                               (Some (v'52, $ 0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), w) ->
    RL_Tbl_Grp_P
      (update_nth_val
         (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)>>ᵢ$ 3)))
         (update_nth_val (Z.to_nat (Int.unsigned ((x>>ᵢ$ 8)>>ᵢ$ 3))) v'36
                         (val_inj
                            (and (Vint32 x12) (Vint32 (Int.not ($ 1<<ᵢ((x>>ᵢ$ 8)&ᵢ$ 7)))))))
         (val_inj
            (or
               (Vint32 t1)
               (Vint32 x11))))
      (Vint32 (Int.or (i7&ᵢInt.not ($ 1<<ᵢ((x>>ᵢ$ 8)>>ᵢ$ 3))) x8)) /\
    prio_in_tbl ($ OS_IDLE_PRIO)
                (update_nth_val
                   (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)>>ᵢ$ 3)))
                   (update_nth_val (Z.to_nat (Int.unsigned ((x>>ᵢ$ 8)>>ᵢ$ 3))) v'36
                                   (val_inj
                                      (and (Vint32 x12) (Vint32 (Int.not ($ 1<<ᵢ((x>>ᵢ$ 8)&ᵢ$ 7)))))))
                   (val_inj
                      (or
                         (Vint32 t1)
                         (Vint32 x11)))).
Proof.
  intros.
  split.
  eapply event_wait_rl_tbl_grp;eauto.
  instantiate (8:=Vnull).
  instantiate (7:=Vnull).
  instantiate (6:=Vnull).
  instantiate (5:=Vnull).
  instantiate (4:=(Int.repr 0)).
  instantiate (3:= Int.repr OS_STAT_RDY).
  instantiate (2:=(x &ᵢ $ OS_MUTEX_KEEP_LOWER_8)).
  unfolds.
  do 6 eexists;splits;eauto.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  split;auto.
  clear.
  remember (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) as X.
  destruct HeqX.
  int auto.
  splits;eauto.
  symmetry.
  eapply math_mapval_core_prop;eauto.
  symmetry.
  eapply math_mapval_core_prop;eauto.
  eexists.
  split.
  unfolds;simpl;auto.
  intros;auto.
  eapply array_type_vallist_match_int8u_update_hold;eauto.
  clear -H2.
  omega.
  clear -H3.
  remember ((x>>ᵢ$ 8)&ᵢ$ 7) as X.
  clear HeqX.
  mauto.
  eapply event_wait_rl_tbl_grp';eauto.
  instantiate (8:=Vnull).
  instantiate (7:=Vnull).
  instantiate (6:=Vnull).
  instantiate (5:=Vnull).
  instantiate (4:=(Int.repr 0)).
  instantiate (3:= Int.repr OS_STAT_RDY).
  instantiate (2:=(x>>ᵢ$ 8)).
  unfolds.
  do 6 eexists;splits;eauto.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  split;auto.
  clear.
  remember (x>>ᵢ$ 8) as X.
  destruct HeqX.
  int auto.
  splits;eauto.
  eexists;split.
  unfolds;simpl;auto.
  intros;auto.
  rewrite len_lt_update_get_eq in H9.
  clear -H9 H8.
  simpl in H8.
  remember (Int.eq t11 ($ 0)) as X.
  destruct X;simpl in H8;tryfalse.
  simpl in H9.
  assert (t11 =($ 0)).
  lets Hx: Int.eq_spec t11 ($ 0).
  rewrite <- HeqX in Hx.
  auto.
  subst.
  assert (forall x y,Vint32 x = Vint32 y -> x = y).
  intros.
  inverts H;auto.
  apply H in H9.
  rewrite H9.
  clear;int auto.
  rewrite H0.
  simpl.
  auto.

  rewrite <- H16.
  eapply idle_in_rtbl_hold';eauto.
  clear -H5;omega.
  rewrite update_nth_val_len_eq.
  rewrite H0.
  auto.
  eapply array_type_vallist_match_int8u_update_hold;eauto.
  omega.
  clear -H3.
  remember (((x>>ᵢ$ 8)&ᵢ$ 7)) as X.
  destruct HeqX.
  mauto.
  eapply prio_neq_in_tbl_rev;eauto.
  unfold OS_IDLE_PRIO.
  unfold OS_LOWEST_PRIO.
  clear;int auto.
  split;auto.
  clear;int auto.
  2:  eapply nth_val'2nth_val;eauto.
  unfolds in H20.
  simpljoin.
  unfolds in H20.
  unfolds in H21.
  simpljoin.
  assert ( Some (v'52, $ 0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = Some (v'52, $ 0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)) by auto.
  apply H22 in H27.
  simpljoin.
  clear -H27 H30.
  remember (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) as X.
  clear HeqX.
  remember (x>>ᵢ$ 8) as Y.
  clear HeqY.
  intro.
  subst Y.
  unfold OS_IDLE_PRIO in H27.
  unfold OS_LOWEST_PRIO in H27.
  int auto.
Qed.


Lemma return_rl_t_g_p' :
  forall v'36 i7 x v'52 w x8 x11 x12 t1 t11,
    array_type_vallist_match Int8u v'36 ->
    length v'36 = ∘OS_RDY_TBL_SIZE ->
    Int.unsigned i7 <= 255 ->
    Int.unsigned ((x>>ᵢ$ 8)>>ᵢ$ 3) < 8 ->
    Int.unsigned ((x>>ᵢ$ 8)&ᵢ$ 7) < 8 ->
    Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7) < 8 ->
    Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)>>ᵢ$ 3) < 8 ->
    Int.unsigned (x>>ᵢ$ 8) < 64 ->
    Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) < 64 ->
    val_inj (val_eq (Vint32 t11) (V$0)) = Vint32 Int.zero \/
    val_inj (val_eq (Vint32 t11) (V$0)) = Vnull ->
    nth_val' (Z.to_nat (Int.unsigned ((x>>ᵢ$ 8)>>ᵢ$ 3)))
             (update_nth_val (Z.to_nat (Int.unsigned ((x>>ᵢ$ 8)>>ᵢ$ 3))) v'36
                             (val_inj
                                (and (Vint32 x12) (Vint32 (Int.not ($ 1<<ᵢ((x>>ᵢ$ 8)&ᵢ$ 7))))))) =
    Vint32 t11 -> 
    nth_val'
      (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)>>ᵢ$ 3)))
      OSMapVallist = Vint32 x8 ->
    true = rule_type_val_match Int8u (Vint32 x8) ->
    nth_val' (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)))
             OSMapVallist = Vint32 x11 ->
    true = rule_type_val_match Int8u (Vint32 x11) ->
    Int.unsigned x12 <= 255 ->
    nth_val' (Z.to_nat (Int.unsigned ((x>>ᵢ$ 8)>>ᵢ$ 3))) v'36 =
    Vint32 x12 ->
    nth_val' (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)>>ᵢ$ 3)))
             (update_nth_val (Z.to_nat (Int.unsigned ((x>>ᵢ$ 8)>>ᵢ$ 3))) v'36
                             (val_inj
                                (and (Vint32 x12) (Vint32 (Int.not ($ 1<<ᵢ((x>>ᵢ$ 8)&ᵢ$ 7))))))) =
    Vint32 t1 ->
    Int.unsigned t1 <= 255 ->
    RL_Tbl_Grp_P v'36 (Vint32 i7) ->  
    prio_in_tbl ($ OS_IDLE_PRIO) v'36 -> 
    RLH_ECBData_P (DMutex (Vint32 x) (Vptr (v'52, $ 0)))
                  (absmutexsem (x>>ᵢ$ 8)
                               (Some (v'52, $ 0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), w) ->
    RL_Tbl_Grp_P
      (update_nth_val
         (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)>>ᵢ$ 3)))
         (update_nth_val (Z.to_nat (Int.unsigned ((x>>ᵢ$ 8)>>ᵢ$ 3))) v'36
                         (val_inj
                            (and (Vint32 x12) (Vint32 (Int.not ($ 1<<ᵢ((x>>ᵢ$ 8)&ᵢ$ 7)))))))
         (val_inj (or (Vint32 t1) (Vint32 x11)))) (Vint32 (Int.or i7 x8)) /\
    prio_in_tbl ($ OS_IDLE_PRIO)
                (update_nth_val
                   (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)>>ᵢ$ 3)))
                   (update_nth_val (Z.to_nat (Int.unsigned ((x>>ᵢ$ 8)>>ᵢ$ 3))) v'36
                                   (val_inj
                                      (and (Vint32 x12) (Vint32 (Int.not ($ 1<<ᵢ((x>>ᵢ$ 8)&ᵢ$ 7)))))))
                   (val_inj (or (Vint32 t1) (Vint32 x11)))).
Proof.
  intros.
  split.
  eapply event_wait_rl_tbl_grp;eauto.
  instantiate (8:=Vnull).
  instantiate (7:=Vnull).
  instantiate (6:=Vnull).
  instantiate (5:=Vnull).
  instantiate (4:=(Int.repr 0)).
  instantiate (3:= Int.repr OS_STAT_RDY).
  instantiate (2:=(x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)).
  unfolds.
  do 6 eexists;splits;eauto.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  split;auto.
  clear.
  remember (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) as X.
  destruct HeqX.
  int auto.
  splits;eauto.
  symmetry.
  eapply math_mapval_core_prop;eauto.
  symmetry.
  eapply math_mapval_core_prop;eauto.
  eexists.
  split.
  unfolds;simpl;auto.
  intros;auto.
  eapply array_type_vallist_match_int8u_update_hold;eauto.
  clear -H2.
  omega.
  clear -H3.
  remember ((x>>ᵢ$ 8)&ᵢ$ 7) as X.
  clear HeqX.
  mauto.

  eapply event_wait_rl_tbl_grp'';eauto.
  instantiate (9:=Vnull).
  instantiate (8:=Vnull).
  instantiate (7:=Vnull).
  instantiate (6:=Vnull).
  instantiate (5:=(Int.repr 0)).
  instantiate (4:= Int.repr OS_STAT_RDY).
  instantiate (3:=(x>>ᵢ$ 8)).
  unfolds.
  do 6 eexists;splits;eauto.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  split;auto.
  clear.
  remember (x>>ᵢ$ 8) as X.
  destruct HeqX.
  int auto.
  splits;eauto.
  eexists;split.
  unfolds;simpl;auto.
  intros;auto.
  rewrite len_lt_update_get_eq in H9.
  simpl in H9.
  inverts H9.
  destruct H8.
  simpl in H8.
  destruct (Int.eq (x12&ᵢInt.not ($ 1<<ᵢ((x>>ᵢ$ 8)&ᵢ$ 7))) ($ 0));auto;tryfalse.
  simpl in H8.
  destruct (Int.eq (x12&ᵢInt.not ($ 1<<ᵢ((x>>ᵢ$ 8)&ᵢ$ 7))) ($ 0));auto;tryfalse.
  rewrite H0.
  simpl.
  omega.
  rewrite <- H16.
  eapply idle_in_rtbl_hold';eauto.
  omega.
  rewrite update_nth_val_len_eq.
  auto.
  eapply array_type_vallist_match_int8u_update_hold;eauto.
  omega.
  clear -H3.
  remember (((x>>ᵢ$ 8)&ᵢ$ 7)) as X.
  destruct HeqX.
  mauto.
  eapply prio_neq_in_tbl_rev;eauto.
  unfold OS_IDLE_PRIO.
  unfold OS_LOWEST_PRIO.
  clear;int auto.
  split;auto.
  clear;int auto.
  2:  eapply nth_val'2nth_val;eauto.
  unfolds in H20.
  simpljoin.
  unfolds in H20.
  unfolds in H21.
  simpljoin.
  assert ( Some (v'52, $ 0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = Some (v'52, $ 0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)) by auto.
  apply H22 in H27.
  simpljoin.
  clear -H27 H30.
  remember (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) as X.
  clear HeqX.
  remember (x>>ᵢ$ 8) as Y.
  clear HeqY.
  intro.
  subst Y.
  unfold OS_IDLE_PRIO in H27.
  unfold OS_LOWEST_PRIO in H27.
  int auto.
Qed.


Lemma return_gethwait :
  forall v'38 v'39 v'52 v'55 w prio m v'87 v'59,
    (* need 2 premises
     1: (v'52,Int.zero) should in v'39
     2: (v'52,Int.zero) not in w \/ v'55&ᵢ$ OS_MUTEX_KEEP_LOWER_8 is higher that the original priority of (v'52,Int.zero)
     *)
    (*   TcbMod.get v'39 (v'52, Int.zero) = Some (p, rdy, m) ->
    GetHWait
      (TcbMod.set v'39 (v'52, Int.zero)
                  (v'55&ᵢ$ OS_MUTEX_KEEP_LOWER_8, rdy, m)) w 
      (v'87, Int.zero) ->  (v'52, Int.zero) <> (v'87, Int.zero) ->   GetHWait v'39 w (v'87, Int.zero).*)

    RH_TCBList_ECBList_P v'38 v'39 (v'52, Int.zero) -> 
    EcbMod.get v'38 (v'59, Int.zero) =  Some (absmutexsem (v'55>>ᵢ$ 8)
                                                          (Some (v'52, $ 0, v'55&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), w) ->
    TcbMod.get v'39 (v'52, Int.zero) = Some (prio, rdy, m) ->
    GetHWait
      (TcbMod.set v'39 (v'52, Int.zero)
                  (v'55&ᵢ$ OS_MUTEX_KEEP_LOWER_8, rdy, m)) w 
      (v'87, Int.zero) -> 
    (v'52, Int.zero) <> (v'87, Int.zero) ->
    GetHWait v'39 w (v'87, Int.zero).
Proof.
  introv Hrh Heget Htget.
  intros.
  unfolds in H.
  simpljoin.
  unfolds.
  simpljoin;splits; auto.
  rewrite TcbMod.set_a_get_a' in H1.
  do 3 eexists.
  splits;eauto.
  intros.
  apply H2 in H3;eauto.
  simpljoin.
  assert (t' = (v'52, Int.zero) \/ t' <> (v'52, Int.zero)) by tauto.
  destruct H6;subst.
  rewrite TcbMod.set_a_get_a in H3.
  inverts H3.
  do 3 eexists;split;eauto.
  unfolds in Hrh.
  simpljoin.
  unfolds in H8.
  simpljoin.
  assert (EcbMod.get v'38 (v'59,Int.zero) =  Some (absmutexsem (v'55>>ᵢ$ 8)
                                                               (Some (v'52, $ 0, v'55&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), w)  /\ In (v'52,Int.zero) w) by (split;auto).
  apply H8 in H11.
  simpljoin.
  unfold get in *; simpl in*.
  rewrite Htget in H11;inverts H11.
  rewrite tidspec.eq_beq_true;auto.
  rewrite TcbMod.set_a_get_a' in H3.
  do 3 eexists;splits;eauto.
  rewrite tidspec.neq_beq_false;auto.
  rewrite tidspec.neq_beq_false;auto.
Qed.


Lemma vhold_not_get:
  forall tcbls_l tcbls_r tcbls ct cur_prio x2 v'32 v'53 phold,
    TcbMod.join tcbls_l tcbls_r tcbls ->
    TcbJoin ct (cur_prio, rdy, Vnull) x2 tcbls_r -> 
    R_PrioTbl_P v'32 tcbls v'53 ->
    nth_val' (Z.to_nat (Int.unsigned phold)) v'32 =
    Vptr v'53 ->
    forall (tid : tidspec.A) (p : priority) (s0 : taskstatus) (m : msg),
      TcbMod.get x2 tid = Some (p, s0, m) -> p <> phold.
Proof.
  intros.
  unfolds in H1.
  destructs H1.
  unfolds in H5.
  assert (TcbMod.get tcbls tid = Some (p,s0,m)).
  eapply TcbMod.join_get_r;eauto.
  eapply tcbjoin_get_get_my;eauto.
  clear H3.
  intro.
  subst p.
  lets Hx:H4 H6.
  destruct Hx.
  apply nth_val_nth_val'_some_eq in H3;auto.
  unfold nat_of_Z in H3.
  rewrite H3 in H2.
  inverts H2.
  tryfalse.
Qed.




Lemma vhold_not_get'
: forall (tcbls_l tcbls_r tcbls : TcbMod.map) 
         (v'32 : vallist) (v'53 : addrval) (phold : int32),
    TcbMod.join tcbls_l tcbls_r tcbls ->
    R_PrioTbl_P v'32 tcbls v'53 ->
    nth_val' (Z.to_nat (Int.unsigned phold)) v'32 = Vptr v'53 ->
    forall (tid : tidspec.A) (p : priority) (s0 : taskstatus) (m : msg),
      TcbMod.get tcbls_l tid = Some (p, s0, m) -> p <> phold.
Proof.
  intros.
  unfolds in H0.
  simpljoin.
  assert (TcbMod.get tcbls tid = Some (p,s0,m)).
  eapply TcbMod.join_get_l;eauto.
  clear H2.
  intro.
  subst p.
  apply H3 in H5.
  destruct H5.
  unfold nat_of_Z in H2.
  apply nth_val_nth_val'_some_eq in H2;auto.
  rewrite H1 in H2;inverts H2.
  tryfalse.
Qed.


(* ?
Require Import sem_common. *)

Ltac simpl_vqm :=
  repeat
    match goal with
      | H: ?f _ = Some _ |- _ => simpl in H;inverts H
      | _ => idtac
    end.

Lemma tcbls_l_mutexpend:
  forall prio_lift  ptcb_prio v'33 v'34 v'45 v'43 x11 xm i8 ptcb_tcby ptcb_bitx ptcb_bity v'36 os_rdy_tbl tcbls_l v'32 tcbls_r tcbls ptcb_addr v0 x5 vhold,
    
    get_last_tcb_ptr v'34 v'33 = Some (Vptr (ptcb_addr,Int.zero)) -> (*added*)
    nth_val' (Z.to_nat (Int.unsigned prio_lift)) v'32 =
    Vptr vhold -> (*added*)
    TcbMod.join tcbls_l tcbls_r tcbls ->
    R_PrioTbl_P v'32 tcbls vhold ->
    Int.unsigned prio_lift < 64 -> 
    ptcb_prio <>  prio_lift->
    TcbMod.get tcbls_l (ptcb_addr, Int.zero) =
    Some (ptcb_prio, rdy, xm) ->
    nth_val' (Z.to_nat (Int.unsigned ptcb_tcby)) os_rdy_tbl =
    Vint32 v0 ->
    nth_val' (Z.to_nat (Int.unsigned (prio_lift>>ᵢ$ 3)))
             (update_nth_val (Z.to_nat (Int.unsigned ptcb_tcby)) os_rdy_tbl
                             (Vint32 (v0&ᵢInt.not ptcb_bitx))) = Vint32 x5 ->
    TCBList_P v'33
              (v'34 ++
                    (v'45
                       :: v'43
                       :: x11
                       :: xm
                       :: V$0
                       :: V$OS_STAT_RDY
                       :: Vint32 ptcb_prio
                       :: Vint32 i8
                       :: Vint32 ptcb_tcby
                       :: Vint32 ptcb_bitx
                       :: 
                       Vint32 ptcb_bity :: nil)
                    :: v'36) os_rdy_tbl tcbls_l ->
    TCBList_P v'33
              (v'34 ++
                    (v'45
                       :: v'43
                       :: x11
                       :: xm
                       :: V$0
                       :: V$OS_STAT_RDY
                       :: Vint32 prio_lift
                       :: Vint32 (prio_lift&ᵢ$ 7)
                       :: Vint32 (prio_lift>>ᵢ$ 3)
                       :: Vint32 ($ 1<<ᵢ(prio_lift&ᵢ$ 7)) :: Vint32 ($ 1<<ᵢ(prio_lift>>ᵢ$ 3)) :: nil) :: v'36)
              (update_nth_val (Z.to_nat (Int.unsigned (prio_lift>>ᵢ$ 3)))
                              (update_nth_val (Z.to_nat (Int.unsigned ptcb_tcby)) os_rdy_tbl
                                              (Vint32 (v0&ᵢInt.not ptcb_bitx)))
                              (Vint32 (Int.or x5 ($ 1<<ᵢ(prio_lift&ᵢ$ 7)))))
              (TcbMod.set tcbls_l (ptcb_addr, Int.zero) (prio_lift, rdy, xm)).
Proof.
  introv Hlast Hhold.
  intros.
  apply TCBList_P_Split in H6.
  simpljoin.
  simpl in H9.
  simpljoin.
  unfolds in H10;simpl in H10;inverts H10.
  eapply TCBList_P_Combine;eauto.
  instantiate (1:= TcbMod.set x1 (ptcb_addr, Int.zero) (prio_lift, rdy, xm)).
  eapply TcbMod.join_set_r;eauto.
  unfolds.
  rewrite Hlast in H6;inverts H6.
  exists x6.
  eapply tcbjoin_get_a_my;eauto.
  eapply TCBList_P_rtbl_add_simpl_version;eauto.
  split;auto.
  clear;int auto.
  apply nth_val'2nth_val;auto.
  assert (forall (tid : tidspec.A) (p : priority) (s : taskstatus) (m : msg),
            TcbMod.get tcbls_l tid = Some (p, s, m) -> p <> prio_lift).
  eapply vhold_not_get';eauto.
  intros.
  eapply H9;eauto.
  eapply TcbMod.join_get_l;eauto.
  destruct x6.
  destruct p as (p&st).
  Require Import Mbox_common.
  eapply TCBList_P_tcb_block_hold' with (tcs:= x1) (tcs':=tcbls_l) (prio:=p);eauto.
  clear -H12.
  unfolds in H12.


  simpljoin.
  unfolds in H1.
  simpljoin.
  simpl_vqm.
  auto.
  eapply tcbjoin_get_a_my;eauto.
  clear -H12.
  unfolds in H12.
  simpljoin.
  unfolds in H1.
  simpljoin.
  simpl_vqm.
  auto.
  clear -H12.
  unfolds in H12.
  simpljoin.
  unfolds in H1.
  simpljoin.
  simpl_vqm.
  auto.
  unfolds in H12.
  simpljoin.
  unfolds in H12.
  simpljoin.
  symmetry in H6.
  symmetry in Hlast.
  symmetry in H3.
  simpl_vqm.
  eapply TcbMod_join_impl_prio_neq_cur_l;eauto.
  eapply TcbMod_join_impl_prio_neq_cur_l;eauto.
  eapply R_PrioTbl_P_impl_prio_neq_cur;eauto.
  eapply TcbMod.join_get_l;eauto.
  eapply TcbMod.join_get_r;eauto.
  eapply tcbjoin_get_a_my;eauto.
  clear -H12 H4.
  unfolds in H12.
  Import DeprecatedTactic.
  mytac.
  unfolds in H1.
  mytac.
  simpl_vqm.
  apply nth_val'2nth_val;auto.
  simpl.
  rewrite Hlast in H6;inverts H6.
  do 4 eexists;splits;eauto.
  unfolds;simpl;eauto.
  instantiate (1:= x4).
  instantiate (1:= (prio_lift, rdy, xm)).
  eapply tcbjoin_set_my;eauto.
  destruct x6.
  destruct p.
  unfolds in H12.
  mytac.
  unfolds in H10.
  mytac.
  symmetry in Hlast.
  symmetry in H3.
  simpl_vqm.
  unfolds.
  mytac.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  unfolds.
  do 6 eexists;splits.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  split;auto.
  clear;int auto.
  splits;auto.
  eexists;split.
  unfolds;simpl;auto.
  intros.
  apply H26;auto.
  unfolds in H12.
  mytac.
  unfolds.
  splits;unfolds;intros.
  unfolds in H14.
  simpljoin.
  simpl_vqm.
  splits.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  eexists;auto.
  inverts H14.
  splits.
  2:unfolds;simpl;auto.
  2:unfolds;simpl;auto.
  unfolds.
  splits.
  unfolds;simpl;auto.
  eapply prio_in_tbl_orself;eauto.
  splits;unfolds;intros.
  unfolds in H14.
  simpljoin.
  simpl_vqm.
  assert (~prio_not_in_tbl prio
           (update_nth_val (Z.to_nat (Int.unsigned (prio>>ᵢ$ 3)))
                           (update_nth_val (Z.to_nat (Int.unsigned (p>>ᵢ$ 3))) os_rdy_tbl
                                           (Vint32 (v0&ᵢInt.not ($ 1<<ᵢ(p&ᵢ$ 7)))))
                           (Vint32 (Int.or x5 ($ 1<<ᵢ(prio&ᵢ$ 7)))))).
  eapply prio_notin_tbl_orself;eauto.
  apply nth_val'2nth_val;auto.
  false.
  simpl_vqm;false.
  simpl_vqm;false.
  simpl_vqm;false.
  simpl_vqm;false.
  splits;unfolds;intros.
  inverts H14.
  inverts H14.
  inverts H14.
  inverts H14.
  inverts H14.

  eapply TCBList_P_rtbl_add_simpl_version;eauto.
  split;auto.
  clear;int auto.
  apply nth_val'2nth_val;auto.
  assert (forall (tid : tidspec.A) (p : priority) (s : taskstatus) (m : msg),
            TcbMod.get tcbls_l tid = Some (p, s, m) -> p <> prio_lift).
  eapply vhold_not_get';eauto.
  intros.
  destruct x6.
  destruct p0.
  eapply H6;eauto.
  eapply TcbMod.join_get_r;eauto.
  eapply tcbjoin_get_get;eauto.
  destruct x6.
  destruct p.
  unfolds in H12.
  simpljoin.
  unfolds in H1.
  simpljoin.
  symmetry in Hlast.
  symmetry in H3.
  simpl_vqm.
  eapply TCBList_P_tcb_block_hold' with (tcs:= TcbMod.sig (ptcb_addr, Int.zero) (p, t, m)) (tcs':=x1) (prio:=p);eauto.
  clear -H10.
  unfolds in H10.
  simpljoin.
  simpl_vqm.
  auto.
  rewrite TcbMod.sig_sem.
  rewrite tidspec.eq_beq_true;eauto.
  unfolds in H11.
  apply TcbMod.join_comm;auto.
  clear -H10.
  unfolds in H10.
  simpljoin.
  simpl_vqm.
  auto.
  clear -H10.
  unfolds in H10.
  simpljoin.
  simpl_vqm.
  auto.
  eapply TcbMod_join_impl_prio_neq_cur_r;eauto.
  eapply TcbMod_join_impl_prio_neq_cur_r;eauto.
  eapply TcbMod_join_impl_prio_neq_cur_l;eauto.
  eapply R_PrioTbl_P_impl_prio_neq_cur;eauto.
  clear -H10.
  unfolds in H10.
  simpljoin.
  simpl_vqm.
  auto.
  eapply tcbjoin_get_a_my in H11;eauto.
  eapply TcbMod.join_get_l;eauto.
  apply nth_val'2nth_val;auto.
Qed.

Lemma return_tcbl_p: forall  m x x11 x8 v'35 v'36 x12 t1  v'52 v'45 v'24 x15 x7 v'51 v'39 v'30 x10 v'43,
                       nth_val'
                         (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)>>ᵢ$ 3)))
                         OSMapVallist = Vint32 x8 ->
                       
                       true = rule_type_val_match Int8u (Vint32 x8) ->
                       Int.ltu (x>>ᵢ$ 8) (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = true->
                       array_type_vallist_match Int8u v'36 ->
                       length v'36 = ∘OS_RDY_TBL_SIZE ->
                       Int.unsigned ((x>>ᵢ$ 8)>>ᵢ$ 3) < 8 ->
                       Int.unsigned ((x>>ᵢ$ 8)&ᵢ$ 7) < 8 ->
                       Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7) < 8 ->
                       Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)>>ᵢ$ 3) < 8 ->
                       Int.unsigned (x>>ᵢ$ 8) < 64 ->
                       Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) < 64 ->
                       nth_val' (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)))
                                OSMapVallist = Vint32 x11 ->
                       true = rule_type_val_match Int8u (Vint32 x11) ->
                       Int.unsigned x12 <= 255 ->
                       nth_val' (Z.to_nat (Int.unsigned ((x>>ᵢ$ 8)>>ᵢ$ 3))) v'36 =
                       Vint32 x12 ->
                       nth_val' (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)>>ᵢ$ 3)))
                                (update_nth_val (Z.to_nat (Int.unsigned ((x>>ᵢ$ 8)>>ᵢ$ 3))) v'36
                                                (val_inj
                                                   (and (Vint32 x12) (Vint32 (Int.not ($ 1<<ᵢ((x>>ᵢ$ 8)&ᵢ$ 7))))))) =
                       Vint32 t1 ->
                       Int.unsigned t1 <= 255 ->
                       TcbMod.join v'43 v'45 v'39 ->
                       TcbJoin (v'52, Int.zero) (x>>ᵢ$ 8, rdy, m) x10 v'45 ->
                       nth_val (Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) v'30 =
                       Some (Vptr v'51) ->
                       R_PrioTbl_P v'30 v'39 v'51 ->
                       TCBList_P (Vptr (v'52, Int.zero))
                                 ((x7
                                     :: v'24
                                     :: x15
                                     :: m
                                     :: V$0
                                     :: V$OS_STAT_RDY
                                     :: Vint32 (x>>ᵢ$ 8)
                                     :: Vint32 ((x>>ᵢ$ 8)&ᵢ$ 7)
                                     :: Vint32 ((x>>ᵢ$ 8)>>ᵢ$ 3)
                                     :: Vint32 ($ 1<<ᵢ((x>>ᵢ$ 8)&ᵢ$ 7))
                                     :: Vint32 ($ 1<<ᵢ((x>>ᵢ$ 8)>>ᵢ$ 3))
                                     :: nil) :: v'35) v'36 v'45 ->
                       TCBList_P (Vptr (v'52, Int.zero))
                                 ((x7
                                     :: v'24
                                     :: x15
                                     :: m
                                     :: V$0
                                     :: V$OS_STAT_RDY
                                     :: Vint32 (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)
                                     :: Vint32 ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)
                                     :: Vint32 ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)>>ᵢ$ 3)
                                     :: Vint32 x11 :: Vint32 x8 :: nil) :: v'35)
                                 (update_nth_val
                                    (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)>>ᵢ$ 3)))
                                    (update_nth_val (Z.to_nat (Int.unsigned ((x>>ᵢ$ 8)>>ᵢ$ 3))) v'36
                                                    (val_inj
                                                       (and (Vint32 x12) (Vint32 (Int.not ($ 1<<ᵢ((x>>ᵢ$ 8)&ᵢ$ 7)))))))
                                    (val_inj (or (Vint32 t1) (Vint32 x11))))
                                 (TcbMod.set v'45 (v'52, Int.zero) (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8, rdy, m)).
Proof.
  introv Hadd1 Hadd2.
  intros.
  simpl val_inj in *.
  assert (nil++ (x7
                   :: v'24
                   :: x15
                   :: m
                   :: V$0
                   :: V$OS_STAT_RDY
                   :: Vint32 (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)
                   :: Vint32 ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)
                   :: Vint32 ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)>>ᵢ$ 3)
                   :: Vint32 x11 :: Vint32 x8 :: nil) :: v'35 =(x7
                                                                  :: v'24
                                                                  :: x15
                                                                  :: m
                                                                  :: V$0
                                                                  :: V$OS_STAT_RDY
                                                                  :: Vint32 (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)
                                                                  :: Vint32 ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)
                                                                  :: Vint32 ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)>>ᵢ$ 3)
                                                                  :: Vint32 x11 :: Vint32 x8 :: nil) :: v'35).
  simpl;auto.
  rewrite <- H19.
  clear H19.
  eapply math_mapval_core_prop in H8;eauto.
  subst x11.
  eapply math_mapval_core_prop in Hadd1;eauto.
  subst x8.
  eapply tcbls_l_mutexpend;eauto.  
  eapply nth_val_nth_val'_some_eq;eauto.
  eapply TcbMod.join_comm;eauto.
  clear -H.
  intro.
  rewrite H0 in H;clear -H.
  remember (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) as X.
  clear HeqX.
  int auto.
  eapply tcbjoin_get_a_my;eauto.
Qed.



Lemma return_tcbl_p' :forall v'31 v'33 v'36 v'43 x x11 t1 x12 v'51 v'39 v'30 v'45 x10 t m v'52,
                        array_type_vallist_match Int8u v'36 ->
                        length v'36 = ∘OS_RDY_TBL_SIZE ->
                        Int.unsigned ((x>>ᵢ$ 8)>>ᵢ$ 3) < 8 ->
                        Int.unsigned ((x>>ᵢ$ 8)&ᵢ$ 7) < 8 ->
                        Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7) < 8 ->
                        Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)>>ᵢ$ 3) < 8 ->
                        Int.unsigned (x>>ᵢ$ 8) < 64 ->
                        Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) < 64 ->
                        nth_val' (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)))
                                 OSMapVallist = Vint32 x11 ->
                        true = rule_type_val_match Int8u (Vint32 x11) ->
                        Int.unsigned x12 <= 255 ->
                        nth_val' (Z.to_nat (Int.unsigned ((x>>ᵢ$ 8)>>ᵢ$ 3))) v'36 =
                        Vint32 x12 ->
                        nth_val' (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)>>ᵢ$ 3)))
                                 (update_nth_val (Z.to_nat (Int.unsigned ((x>>ᵢ$ 8)>>ᵢ$ 3))) v'36
                                                 (val_inj
                                                    (and (Vint32 x12) (Vint32 (Int.not ($ 1<<ᵢ((x>>ᵢ$ 8)&ᵢ$ 7))))))) =
                        Vint32 t1 ->
                        Int.unsigned t1 <= 255 ->
                        TcbMod.join v'43 v'45 v'39 ->
                        TcbJoin (v'52, Int.zero) (x>>ᵢ$ 8, t, m) x10 v'45 ->
                        nth_val (Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) v'30 =
                        Some (Vptr v'51) ->
                        R_PrioTbl_P v'30 v'39 v'51 ->
                        TCBList_P v'31 v'33 v'36 v'43 ->
                        TCBList_P v'31 v'33
                                  (update_nth_val
                                     (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)>>ᵢ$ 3)))
                                     (update_nth_val (Z.to_nat (Int.unsigned ((x>>ᵢ$ 8)>>ᵢ$ 3))) v'36
                                                     (val_inj
                                                        (and (Vint32 x12) (Vint32 (Int.not ($ 1<<ᵢ((x>>ᵢ$ 8)&ᵢ$ 7)))))))
                                     (val_inj (or (Vint32 t1) (Vint32 x11)))) v'43
.
Proof.
  intros.
  simpl val_inj in *.
  apply math_mapval_core_prop in H7;auto.
  subst x11.
  eapply TCBList_P_rtbl_add_simpl_version;eauto.
  split;auto.
  remember ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)) as X;clear HeqX.
  clear;int auto.
  eapply nth_val'2nth_val;eauto.
  eapply vhold_not_get';eauto.
  eapply nth_val_nth_val'_some_eq;eauto.
  eapply TCBList_P_tcb_block_hold';eauto.
  split;auto.
  remember (x>>ᵢ$ 8) as X;clear HeqX.
  clear;int auto.
  eapply tcbjoin_get_a_my;eauto.
  eapply TcbMod_join_impl_prio_neq_cur_l;eauto.
  eapply R_PrioTbl_P_impl_prio_neq_cur;eauto.
  split;auto.
  remember (x>>ᵢ$ 8) as X.
  clear;int auto.
  eapply TcbMod.join_get_r;eauto.
  eapply tcbjoin_get_a_my;eauto.
  eapply nth_val'2nth_val;eauto.
Qed.


Lemma int_ltu_prop:
  forall x y, Int.ltu x y = false ->
              x <> y ->
              Int.ltu y x = true.
Proof.
  intros.
  int auto.
  false.
  apply H0.
  assert (Int.unsigned x = Int.unsigned y) by omega.
  eapply unsigned_inj; eauto.
Qed.

Lemma intlemmag :
  forall x2 x x5, Int.ltu ((x2<<ᵢ$ 3)+ᵢx5) (x>>ᵢ$ 8) = false
                  /\ (x2<<ᵢ$ 3)+ᵢx5 <> x>>ᵢ$ 8 ->
                  Int.ltu  (x>>ᵢ$ 8) ((x2<<ᵢ$ 3)+ᵢx5) = true.
Proof.  
  introv Hf.
  destruct Hf as (Hf1 & Hf2).
  eapply  int_ltu_prop; eauto.
Qed.

Lemma ltu_false_eq_false_ltu_true :
  forall i1 i2,
    Int.ltu i1 i2 = false ->
    Int.eq i1 i2 = false ->
    Int.ltu i2 i1 = true.
Proof.
  intros.
  apply int_ltu_prop.
  auto.
  intro.
  subst i1.
  clear -H0.
  int auto.
Qed.
Lemma return_r_ecb_et_p :
  forall  i  v'52 x3 v'46 v'44 v'39 v'29 x p m,
    TcbMod.get v'39 (v'52, Int.zero) = Some (p,rdy,m) ->
    R_ECB_ETbl_P (v'29, Int.zero)
                 (V$OS_EVENT_TYPE_MUTEX
                   :: Vint32 i :: Vint32 x :: Vptr (v'52, $ 0) :: x3 :: v'46 :: nil,
                  v'44) v'39 ->
    R_ECB_ETbl_P (v'29, Int.zero)
                 (V$OS_EVENT_TYPE_MUTEX
                   :: Vint32 i :: Vint32 x :: Vptr (v'52, $ 0) :: x3 :: v'46 :: nil, v'44)
                 (TcbMod.set v'39 (v'52, Int.zero) (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8, rdy, m)).
Proof.
  introv Htget.
  intros.
  unfolds in H.
  mytac.
  unfolds.
  mytac;auto.
  unfolds in H.
  unfolds.
  splits;unfolds;intros.
  unfolds in H3;simpl in H3;inverts H3.
  unfolds in H3;simpl in H3;inverts H3.
  unfolds in H3;simpl in H3;inverts H3.
  mytac.
  unfolds in H6.
  lets Hx:H6 H2 H3.
  mytac.
  assert (x0 <> (v'52,Int.zero)).
  intro.
  subst.
  unfold get in *; simpl in *.
  rewrite Htget in H7.
  inverts H7.
  exists x0.
  do 2 eexists.
  rewrite TcbMod.set_a_get_a';eauto.
  apply tidspec.neq_beq_false;auto.
  unfolds.
  unfolds in H0.
  mytac.
  unfolds.
  intros.
  assert ((v'52,Int.zero) = tid \/ (v'52,Int.zero) <> tid) by tauto.
  destruct H6.
  subst.
  rewrite TcbMod.set_a_get_a in H5.
  inverts H5.
  rewrite tidspec.eq_beq_true;auto.
  rewrite TcbMod.set_a_get_a' in H5.
  unfolds in H0.
  apply H0 in H5;auto.
  rewrite tidspec.neq_beq_false;auto.
  
  unfolds.
  intros.
  assert ((v'52,Int.zero) = tid \/ (v'52,Int.zero) <> tid) by tauto.
  destruct H6.
  subst.
  rewrite TcbMod.set_a_get_a in H5.
  inverts H5.
  rewrite tidspec.eq_beq_true;auto.
  rewrite TcbMod.set_a_get_a' in H5.
  unfolds in H2.
  apply H2 in H5;auto.
  rewrite tidspec.neq_beq_false;auto.
  
  unfolds.
  intros.
  assert ((v'52,Int.zero) = tid \/ (v'52,Int.zero) <> tid) by tauto.
  destruct H6.
  subst.
  rewrite TcbMod.set_a_get_a in H5.
  inverts H5.
  rewrite tidspec.eq_beq_true;auto.
  rewrite TcbMod.set_a_get_a' in H5.
  unfolds in H3.
  apply H3 in H5;auto.
  rewrite tidspec.neq_beq_false;auto.
  unfolds.
  intros.
  assert ((v'52,Int.zero) = tid \/ (v'52,Int.zero) <> tid) by tauto.
  destruct H6.
  subst.
  rewrite TcbMod.set_a_get_a in H5.
  inverts H5.
  rewrite tidspec.eq_beq_true;auto.
  rewrite TcbMod.set_a_get_a' in H5.
  unfolds in H4.
  apply H4 in H5;auto.
  rewrite tidspec.neq_beq_false;auto.
Qed.



Lemma ecblist_p_mutexpend_changeprio:
  forall ectl tcbls v'44  edatal ecbls ptcb_addr ptcb_prio xm prio_lift tl,
    TcbMod.get tcbls (ptcb_addr, Int.zero) = Some (ptcb_prio, rdy, xm) -> 
    ECBList_P v'44 tl ectl edatal ecbls tcbls ->
    ECBList_P v'44 tl ectl edatal ecbls (TcbMod.set tcbls (ptcb_addr, Int.zero) (prio_lift, rdy, xm)).
Proof.
  inductions ectl;intros.
  simpl in H0.
  mytac.
  simpl;auto.
  simpl in H0.
  mytac.
  simpl.
  destruct edatal.
  false.
  destruct a.
  mytac.
  eexists;split;eauto.
  split.
  2:do 3 eexists;splits;eauto.
  unfolds in H1.
  mytac.
  unfolds.
  splits;auto.
  unfolds.
  unfolds in H1.
  mytac.
  unfolds in H1.
  unfolds.
  intros.
  lets Hx:H1 H10 H11.
  mytac.
  assert (x3 = (ptcb_addr, Int.zero) \/ x3 <> (ptcb_addr, Int.zero)) by tauto.
  destruct H13.
  subst.
  unfold get in *; simpl in *.
  rewrite H in H12;inverts H12.
  do 3 eexists.
  rewrite TcbMod.set_a_get_a';eauto.
  eapply tidspec.neq_beq_false;eauto.
  unfolds in H7.
  unfolds.
  intros.
  lets Hx:H7 H10 H11.
  mytac.
  assert (x3 = (ptcb_addr, Int.zero) \/ x3 <> (ptcb_addr, Int.zero)) by tauto.
  destruct H13.
  subst.
  unfold get in *; simpl in *.
  rewrite H in H12;inverts H12.
  do 3 eexists.
  rewrite TcbMod.set_a_get_a';eauto.
  eapply tidspec.neq_beq_false;eauto.  
  unfolds in H8.
  unfolds.
  intros.
  lets Hx:H8 H10 H11.
  mytac.
  assert (x3 = (ptcb_addr, Int.zero) \/ x3 <> (ptcb_addr, Int.zero)) by tauto.
  destruct H13.
  subst.
  unfold get in *; simpl in *.
  rewrite H in H12;inverts H12.
  do 3 eexists.
  rewrite TcbMod.set_a_get_a';eauto.
  eapply tidspec.neq_beq_false;eauto.
  unfolds in H9.
  unfolds.
  intros.
  lets Hx:H9 H10 H11.
  mytac.
  assert (x3 = (ptcb_addr, Int.zero) \/ x3 <> (ptcb_addr, Int.zero)) by tauto.
  destruct H13.
  subst.
  unfold get in *; simpl in *.
  rewrite H in H12;inverts H12.
  do 3 eexists.
  rewrite TcbMod.set_a_get_a';eauto.
  eapply tidspec.neq_beq_false;eauto.
  
  unfolds.
  unfolds in H5.
  mytac.
  unfolds;intros.
  unfolds in H5.
  assert (tid = (ptcb_addr, Int.zero) \/ tid <> (ptcb_addr, Int.zero)) by tauto.
  destruct H11.
  subst tid.
  unfold get in *; simpl in *.
  rewrite TcbMod.set_a_get_a in H10.
  inverts H10.
  apply tidspec.eq_beq_true;auto.
  rewrite TcbMod.set_a_get_a' in H10.
  eapply H5;eauto.
  apply tidspec.neq_beq_false;auto.

  unfolds;intros.
  unfolds in H7.
  assert (tid = (ptcb_addr, Int.zero) \/ tid <> (ptcb_addr, Int.zero)) by tauto.
  destruct H11.
  subst tid.
  rewrite TcbMod.set_a_get_a in H10.
  inverts H10.
  apply tidspec.eq_beq_true;auto.
  rewrite TcbMod.set_a_get_a' in H10.
  eapply H7;eauto.
  apply tidspec.neq_beq_false;auto.

  unfolds;intros.
  unfolds in H8.
  assert (tid = (ptcb_addr, Int.zero) \/ tid <> (ptcb_addr, Int.zero)) by tauto.
  destruct H11.
  subst tid.
  rewrite TcbMod.set_a_get_a in H10.
  inverts H10.
  apply tidspec.eq_beq_true;auto.
  rewrite TcbMod.set_a_get_a' in H10.
  eapply H8;eauto.
  apply tidspec.neq_beq_false;auto.

  unfolds;intros.
  unfolds in H9.
  assert (tid = (ptcb_addr, Int.zero) \/ tid <> (ptcb_addr, Int.zero)) by tauto.
  destruct H11.
  subst tid.
  rewrite TcbMod.set_a_get_a in H10.
  inverts H10.
  apply tidspec.eq_beq_true;auto.
  rewrite TcbMod.set_a_get_a' in H10.
  eapply H9;eauto.
  apply tidspec.neq_beq_false;auto.
Qed.




Lemma RH_TCBList_ECBList_P_changeprio:
  forall ptcb_prio tid tcbls ecbls pcur xm p',
    TcbMod.get tcbls tid = Some (ptcb_prio, rdy, xm)->
    RH_TCBList_ECBList_P ecbls tcbls pcur ->
    RH_TCBList_ECBList_P ecbls (TcbMod.set tcbls tid (p',rdy,xm)) pcur.
Proof.
  introv Ht Hrh.
  unfolds in Hrh.
  destruct Hrh as (Hrh1 & Hrh2 & Hrh3 & Hrh4).
  unfolds.
  split.
  unfolds.
  split.
  intros.
  apply Hrh1 in H.
  mytac.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H0.
  subst.
  unfold get in *; simpl in *.
  rewrite H in Ht; inverts Ht.
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false ; eauto.
  intros.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H0.
  subst.
  rewrite  TcbMod.set_sem  in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false  in H; auto.
  eapply Hrh1 in H.
  eauto.

  split.
  unfolds.
  split.
  intros.
  apply Hrh2 in H.
  mytac.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H0.
  subst.
  unfold get in *; simpl in *.
  rewrite H in Ht; inverts Ht.
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false ; eauto.
  intros.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H0.
  subst.
  rewrite  TcbMod.set_sem  in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false  in H; auto.
  eapply Hrh2 in H.
  eauto.

  split.
  unfolds.
  split.
  intros.
  apply Hrh3 in H.
  mytac.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H0.
  subst.
  unfold get in *; simpl in *.
  rewrite H in Ht; inverts Ht.
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false ; eauto.
  intros.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H0.
  subst.
  rewrite  TcbMod.set_sem  in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false  in H; auto.
  eapply Hrh3 in H.
  eauto.


  split.
  intros.
  apply Hrh4 in H.
  mytac.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H0.
  subst.
  unfold get in *; simpl in *.
  rewrite H in Ht; inverts Ht.
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false ; eauto.
  split.
  intros.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H0.
  subst.
  rewrite  TcbMod.set_sem  in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false  in H; auto.
  eapply Hrh4 in H.
  eauto.

  unfolds.
  destruct Hrh4.
  destruct H0.
  unfolds in H1.
  intros.
  apply H1 in H2.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H3.
  subst.
  rewrite  TcbMod.set_sem .
  rewrite tidspec.eq_beq_true ; eauto.
  rewrite  TcbMod.set_sem .
  rewrite tidspec.neq_beq_false ; eauto.
Qed.


Lemma return_ecbl_p : forall v'57 v'26 v'28 v'48 v'39 v'52 v'55 m x10 tl v'45 v'43,
                        TcbJoin (v'52, Int.zero) (v'55>>ᵢ$ 8, rdy, m) x10 v'45 ->
                        TcbMod.join v'43 v'45 v'39 ->
                        ECBList_P v'57 tl v'26 v'28 v'48 v'39 ->
                        ECBList_P v'57 tl v'26 v'28 v'48 
                                  (TcbMod.set v'39 (v'52, Int.zero) (v'55&ᵢ$ OS_MUTEX_KEEP_LOWER_8, rdy, m)).
Proof.
  intros.
  eapply ecblist_p_mutexpend_changeprio;eauto.
  eapply TcbMod.join_get_r;eauto.
  eapply tcbjoin_get_a;eauto.
Qed.



Lemma return_rh_tcbl_ecbl_p : forall v'38 v'39 v'52 v'55 m x10 v'45 v'43,
                                TcbJoin (v'52, Int.zero) (v'55>>ᵢ$ 8, rdy, m) x10 v'45 ->
                                TcbMod.join v'43 v'45 v'39 ->
                                RH_TCBList_ECBList_P v'38 v'39 (v'52, Int.zero) ->
                                RH_TCBList_ECBList_P v'38
                                                     (TcbMod.set v'39 (v'52, Int.zero) (v'55&ᵢ$ OS_MUTEX_KEEP_LOWER_8, rdy, m))
                                                     (v'52, Int.zero).
Proof.
  intros.
  eapply RH_TCBList_ECBList_P_changeprio;eauto.
  eapply TcbMod.join_get_r;eauto.
  eapply tcbjoin_get_a;eauto.
Qed.

Lemma eq2inteq: forall x y, x=y -> Int.eq x y = true.
Proof.  
  intros.
  int auto.
Qed.

Lemma tcbset_indom_eq: forall tls a c ,TcbMod.indom tls a-> (forall tid, TcbMod.indom tls tid <-> TcbMod.indom (TcbMod.set tls a c) tid).
Proof.
  intros.
  split; intros.
  assert (tid = a \/ tid <> a).
  tauto.
  elim H1; intros.
  subst tid.
  unfolds.
  rewrite TcbMod.set_a_get_a.
  eauto.
  go.
  unfolds.
  rewrite TcbMod.set_a_get_a'.
  exact H0.
  go.

  assert (tid = a \/ tid <> a).
  tauto.
  elim H1;intros.
  subst tid.
  auto.
  unfolds.
  unfolds in H0.
  rewrite TcbMod.set_a_get_a' in H0.
  auto.
  go.
Qed.

Lemma ecblistp_hold :
  forall v'42 v'25 i x v'52 x3 v'46 v'44 v'26 v'27 v'28 v'38 v'39 v'29 v'48 v'49 v'47,
    ((v'42 =  Vptr (v'29, Int.zero) /\ v'25 = nil)\/ get_last_ptr v'25 = Some (Vptr (v'29, Int.zero))) /\ (length v'25 = length v'27)-> (*added*)
    EcbMod.joinsig (v'29, Int.zero)
                   (absmutexsem (x>>ᵢ$ 8) (Some (v'52, $ 0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), 
                    nil) v'48 v'49 ->
    EcbMod.join v'47 v'49 v'38 ->
    ECBList_P v'42 Vnull
              (v'25 ++
                    ((V$OS_EVENT_TYPE_MUTEX
                       :: Vint32 i :: Vint32 x :: Vptr (v'52, $ 0) :: x3 :: v'46 :: nil,
                      v'44) :: nil) ++ v'26)
              (v'27 ++ (DMutex (Vint32 x) (Vptr (v'52, $ 0)) :: nil) ++ v'28) v'38 v'39 -> 
    R_ECB_ETbl_P (v'29, Int.zero)
                 (V$OS_EVENT_TYPE_MUTEX
                   :: Vint32 i :: Vint32 x :: Vptr (v'52, $ 0) :: x3 :: v'46 :: nil,
                  v'44) v'39 ->
    ECBList_P v'42 Vnull
              (v'25 ++
                    ((V$OS_EVENT_TYPE_MUTEX
                       :: Vint32 i
                       :: Vint32 (Int.or x ($ OS_MUTEX_AVAILABLE))
                       :: Vnull :: x3 :: v'46 :: nil, v'44) :: nil) ++ v'26)
              (v'27 ++
                    (DMutex (Vint32 (Int.or x ($ OS_MUTEX_AVAILABLE))) Vnull :: nil) ++
                    v'28)
              (EcbMod.set v'38 (v'29, Int.zero) (absmutexsem (x>>ᵢ$ 8) None, nil))
              v'39.
Proof.
  introv Hlink.
  destruct Hlink as (Hlink&Hleneq).
  intros.
  assert (EcbMod.get v'38 (v'29, Int.zero) = Some 
                                               (absmutexsem (x>>ᵢ$ 8) (Some (v'52, $ 0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)),
                                                nil)) as Hget.
  apply ecbmod_joinsig_get in H.
  eapply EcbMod.join_get_r;eauto.
  clear H H0.
  lets Hx:Mbox_common.ecblist_p_decompose Hleneq H1.
  mytac.
  clear H1.
  assert ( x0 = Vptr (v'29, Int.zero)).
  clear -H4 Hlink H.
  destruct v'25.
  simpl in H.
  mytac;auto.
  destruct Hlink;mytac;auto.
  unfolds in H.
  tryfalse.
  apply ECBList_last_val in H;auto.
  mytac.
  destruct H4;destruct Hlink.
  destruct H2;tryfalse.
  unfolds in H1.
  rewrite H in H1.
  unfolds in H1.
  false.
  destruct H2;false.
  rewrite H2 in H1;inverts H1.
  auto.
(*  intro; tryfalse. *)
  subst x0.
  
  simpl in H0.
  mytac.
  inverts H0.
  destruct x4;tryfalse.
  destruct e;tryfalse.
  unfolds in H5;simpl in H5;inverts H5.
  assert ((absmutexsem i0 o, w) = (absmutexsem (x>>ᵢ$ 8) (Some (v'52, $ 0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)),
                                   nil)).
  apply ecbmod_joinsig_get in H6.
  eapply EcbMod.join_get_r in H6;eauto.
  rewrite Hget in H6;inverts H6;auto.
  inverts H0.
  eapply ecblist_p_compose;eauto.
  eapply EcbMod.join_set_r;eauto.
  unfolds.
  eexists.
  eapply ecbmod_joinsig_get;eauto.
  simpl.
  eexists;splits;eauto.
  do 3 eexists.
  splits.
  unfolds;simpl;auto.
  eapply EcbMod.joinsig_set;eauto.
  simpl.
  2:auto.
  mytac.
  unfolds.
  unfolds in H0.
  mytac.
  inverts H0.
  do 2 eexists.
  splits;auto.

  
  eapply int_auxxx;eauto.

  apply int_aux';auto.

  intros.
  destruct H0.

  apply int_aux'';auto.
  
  auto.
  intros.
  false.
  intros;auto.
  unfolds in H5.
  mytac.
  assert ( Some (v'52, $ 0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = Some (v'52, $ 0, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)) by auto.
  apply H7 in H11.
  mytac.
  clear -H11 H12.
  remember ((x>>ᵢ$ 8)) as X.
  remember (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)  as Y.
  clear HeqX HeqY.
  int auto.
Qed.

Lemma retpost_eventrdy :  retpost OS_EventTaskRdyPost.
Proof.
  unfolds.
  intros.
  unfold getasrt in H.
  unfold  OS_EventTaskRdyPost in H.
  unfold  OS_EventTaskRdyPost' in H.
  (* unfold OS_EventTaskRdyPost_fold' in H. *)
  unfold A_isr_is_prop in H.
  sep normal in H.
  sep destruct H.
  sep split in H.
  repeat
    progress
    match goal with
      | H : _ |=?p _ _  _ \\// _ |- _ => 
        let x:= fresh  in
        (destruct H as [x  | ] ;
         [unfold p in x;
           sep destruct x;
           sep split in x;
           subst; auto | idtac])
    end.
  (* unfold event_rdy_post6' in H. *)
  sep destruct H.
  sep split in H.
  subst v.
  intro; tryfalse. 
Qed.



Lemma  Mutex_owner_set_true:
  forall tcbls tid p st msg t pr opr wls eid ecbls,
    TcbMod.get tcbls tid = Some (p, st, msg) ->  
    t = (absmutexsem pr (Some (tid, opr)), wls) ->
    RH_TCBList_ECBList_MUTEX_OWNER ecbls tcbls ->
    RH_TCBList_ECBList_MUTEX_OWNER (EcbMod.set ecbls eid t) tcbls.
Proof.
  intros.
  unfold RH_TCBList_ECBList_MUTEX_OWNER in *.
  intros.

  assert ( eid = eid0 \/ eid <> eid0).
  tauto.
  destruct H3.
  subst.
  rewrite EcbMod.set_a_get_a in H2.
  inverts H2.
  eauto.
  go.

  eapply H1.
  rewrite EcbMod.set_a_get_a' in H2.
  eauto.
  go.
Qed.  

Lemma mutex_acpt_rh_tcblist_ecblist_p_hold: 
  forall v v'37 v'50 x vv x0 x1 x2, 
    TcbMod.get v'37 (v'50, Int.zero) = Some (x0, x1, x2) ->
    EcbMod.get vv  v  = Some  (absmutexsem (Int.shru x ($ 8)) None, nil) ->
    RH_TCBList_ECBList_P vv v'37 (v'50, Int.zero) ->
    RH_TCBList_ECBList_P
      (EcbMod.set vv v
                  (absmutexsem (Int.shru x ($ 8)) (Some (v'50, Int.zero, x0)), nil)) v'37
      (v'50, Int.zero).
Proof.
  introv HHH.
  intros.
  unfolds in H0.
  mytac.
  unfolds.

  mytac; [clear - HHH H H0 |
          clear -HHH H H1; rename H1 into H0 |
          clear -HHH H H2; rename H2 into H0 |
          clear -HHH H H3; rename H3 into H0 ];
  unfolds; unfolds in H0; mytac; intros; unfold get in *; simpl in *; 
  try solve [eapply H0;
              mytac; eauto;
              assert ( eid = v \/ eid <> v)  as aa by tauto;
              destruct aa;
              [subst; rewrite EcbMod.set_a_get_a in e;
               [ inversion e
               | apply CltEnvMod.beq_refl] 
              | rewrite EcbMod.set_a_get_a' in e;
                [ eauto
                 |apply tidspec.neq_beq_false]; auto]]
  ;try solve
       [ lets aaa : H1 H2;
         mytac;
         assert ( eid = v \/ eid <> v)  as aa by tauto;
         destruct aa;
         [ subst eid;rewrite H in H3;inversion H3
         | rewrite EcbMod.set_a_get_a';
           [ rewrite H3; eauto
           | apply tidspec.neq_beq_false; auto]]
       ].

 
  assert (eid = v \/ eid <> v) as aa by tauto; destruct aa; [subst eid; rewrite EcbMod.set_a_get_a in H3
                                                            |idtac].
  elim H3; intros.

  inversion H4.
  subst.
  eapply H0.
  splits; eauto.
  apply CltEnvMod.beq_refl.
  eapply H0.
  rewrite EcbMod.set_a_get_a' in H3.
  eauto.
  apply tidspec.neq_beq_false; auto.

  assert (eid = v \/ eid <> v) as aa by tauto; destruct aa. 
  subst.
  rewrite EcbMod.set_a_get_a.
  repeat eexists.
  lets aaa : H1 H3.
  mytac; auto.
  rewrite H in H4.
  inversion H4.
  subst.
  auto.
  apply CltEnvMod.beq_refl.

  rewrite EcbMod.set_a_get_a'.
  eapply H1.
  eauto.
  apply tidspec.neq_beq_false; auto.


  eapply Mutex_owner_set_true; eauto.
Qed.

Lemma mund_int_c1:
  forall i x,
    Int.unsigned i < 64 ->
    Int.unsigned x <= 65535 ->
    Int.unsigned (Int.or (x&ᵢ$ OS_MUTEX_KEEP_UPPER_8) i) <= 65535.
  intros.
  apply acpt_intlemma6.
  omega.
Qed.

Lemma mutex_pend_inv_update1:
  forall i2 i6 s low med high P low' med' high' i0 x3 v'48 x1 x2 x0 v'54 v'41,
    s |= AEventData low med ** P ->
    RLH_ECBData_P med high ->
    low = (V$OS_EVENT_TYPE_MUTEX
            :: Vint32 i0 :: Vint32 i2 :: x2 :: x3 :: v'48 :: nil) ->
    med = DMutex (Vint32 i2) x2 ->
    high = (absmutexsem (Int.shru i2 ($ 8)) x0, x1) ->
    RH_CurTCB (v'54, Int.zero) v'41 ->
    Int.unsigned i6 < 64 ->
    Int.unsigned i2 <= 65535 ->
    Int.ltu (Int.shru i2 ($ 8)) i6 = true ->
    i2&ᵢ ($ OS_MUTEX_KEEP_LOWER_8) = ($ OS_MUTEX_AVAILABLE) ->
    low' = (V$OS_EVENT_TYPE_MUTEX
             :: Vint32 i0
             :: Vint32 (Int.or (i2&ᵢ$ OS_MUTEX_KEEP_UPPER_8) i6)
             :: Vptr (v'54, Int.zero) :: x3 :: v'48 :: nil) ->
    med' = DMutex (Vint32 (Int.or (i2&ᵢ$ OS_MUTEX_KEEP_UPPER_8) i6))
                  (Vptr (v'54, Int.zero)) ->
    high' = (absmutexsem (Int.shru i2 ($ 8)) (Some ((v'54, Int.zero), i6)), x1) ->
    s |= AEventData low' med' **
      [| RLH_ECBData_P med' high' |] ** P.
Proof.
  intros.
  unfold AEventData in *.
  sep pauto.
  - sep pauto.
  - unfold RLH_ECBData_P in *.
    mytac.
    clear H1 H2 H3.
    + unfold MatchMutexSem in *.
      mytac.
      inverts H0.
      clear H2.
      do 2 eexists.
      mytac; eauto.
      * clear -H1 H5.
        apply mund_int_c1; auto.
      * symmetry.
        apply acpt_intlemma4.
        auto.
        auto.
      * intros.
        rewrite acpt_intlemma3 in H0.
        unfold OS_MUTEX_AVAILABLE in *.
        clear -H5 H0.
        subst.
        tryfalse.
        auto.
      * assert ((Int.or (x&ᵢ$ OS_MUTEX_KEEP_UPPER_8) i6) &ᵢ ($ OS_MUTEX_KEEP_LOWER_8) = i6).  
        apply acpt_intlemma3.
        auto.
        rewrite H0.
        intros.
        exists (v'54, Int.zero).
        split; auto.
    + unfold RH_ECB_P in *.
      mytac.
      intros; tryfalse.
      intros.
      match goal with
        | H: Some _ = Some _ |- _ => inverts H
      end.
      split; auto.
      intros.
      intro; tryfalse.
      auto.
Qed.

(*
TODO

Lemma TCBList_P_split_by_tcbls_verbose :
  forall l tls tid htcb s head hprev tail tnext rtbl P,
    TcbMod.get tls tid = Some htcb ->
    TCBList_P head l rtbl tls ->
    s |= tcbdllseg head hprev tail tnext l ** P ->
    exists l1 tcbnode l2 tls1 tls2 tail1,
      s |= tcbdllseg head hprev tail1 (Vptr tid) l1 **
        tcbdllseg (Vptr tid) tail1 tail tnext (tcbnode :: l2) ** P /\
      TCBList_P head l1 rtbl tls1 /\
      TCBList_P (Vptr tid) (tcbnode :: l2) rtbl tls2 /\
      TcbMod.join tls1 tls2 tls /\
      l = l1 ++ (tcbnode :: l2) /\
      get_last_tcb_ptr l1 head = Some (Vptr tid). 
Proof.
  inductions l; intros.
  simpl in H0; substs.
  rewrite TcbMod.emp_sem in H; tryfalse.

  simpl in H0; mytac.
  destruct (tidspec.beq tid x) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  exists (nil(A:=vallist)) a l TcbMod.emp tls hprev.
  mytac.
  sep auto.
  destruct_s s.
  simpl in H1; mytac.
  simpl.
  do 6 eexists; repeat (split; eauto).
  unfolds.
  simpl.
  intro; auto.
  rewrite HalfPermMap.map_merge_emp.
  auto.
  join auto.
  simpl; auto.
  simpl.
  do 4 eexists; repeat (split; eauto).
  apply TcbMod.join_emp; auto.
  {
    auto.
  }
  {
    unfold get_last_tcb_ptr.
    auto.
  }
  
  unfold tcbdllseg in H1.
  unfold dllseg in H1; fold dllseg in H1.
  destruct_s s.
  sep split in H1.
  simpl_sat H1; mytac.

  assert((e, e0, (MemMod.merge x23 x4), i, (i0, i1, c), (OSAbstMod.merge x26 x7), a0)
           |= dllseg x9 (Vptr x) tail tnext l os_ucos_h.OS_TCB V_OSTCBPrev
           V_OSTCBNext ** P).
  simpl_sat_goal.
  exists x23 x4; eexists.
  exists x26 x7; eexists.
  repeat (split; eauto).
  clear - H6 H21.
  unfolds; intro.
  pose proof H6 a; pose proof H21 a.
  rewrite MemMod.merge_sem.
  destruct(MemMod.get x3 a);
    destruct(MemMod.get x4 a);
    destruct(MemMod.get m a);
    destruct(MemMod.get x22 a);
    destruct(MemMod.get x23 a);
    tryfalse; auto.
  clear - H8 H23.
  unfolds; intro.
  pose proof H8 a; pose proof H23 a.
  rewrite OSAbstMod.merge_sem.
  destruct(OSAbstMod.get x6 a);
    destruct(OSAbstMod.get x7 a);
    destruct(OSAbstMod.get o a);
    destruct(OSAbstMod.get x25 a);
    destruct(OSAbstMod.get x26 a);
    tryfalse; auto.
  
  assert(TcbMod.get x1 tid = Some htcb).
  clear - H H3 eq1.
  unfolds in H3.
  pose proof H3 tid.
  rewrite TcbMod.get_sig_none in H0.
  rewrite H in H0.
  destruct(TcbMod.get x1 tid); tryfalse; auto.
  substs; auto.
  pose proof tidspec.beq_false_neq eq1.
  auto.

  rewrite H2 in H14; inverts H14.
  unfold tcbdllseg at 1 in IHl.
  lets Hx: IHl H7 H5 H1.
  mytac.
  (** I plus this *) rename H15 into Fzero.
  
  exists (a::x0) x5 x8 (TcbMod.merge (TcbMod.sig x x2) x10) x11 x12.
  mytac; auto.
  simpl_sat H9; mytac.
  simpl_sat_goal.
  exists (MemMod.merge x22 x13) x14 m (OSAbstMod.merge x25 x16) x17 o.
  repeat (split; eauto).
  clear - H14 H6 H21.
  unfolds; intro.
  rewrite MemMod.merge_sem.
  pose proof H6 a.
  pose proof H21 a.
  pose proof H14 a.
  rewrite MemMod.merge_sem in H1.
  destruct(MemMod.get x3 a);
    destruct(MemMod.get x4 a);
    destruct(MemMod.get m a);
    destruct(MemMod.get x22 a);
    destruct(MemMod.get x23 a);
    destruct(MemMod.get x14 a);
    destruct(MemMod.get x13 a); tryfalse; substs; auto.

  clear - H16 H8 H23.
  unfolds; intro.
  rewrite OSAbstMod.merge_sem.
  pose proof H8 a.
  pose proof H23 a.
  pose proof H16 a.
  rewrite OSAbstMod.merge_sem in H1.
  destruct(OSAbstMod.get x6 a);
    destruct(OSAbstMod.get x7 a);
    destruct(OSAbstMod.get o a);
    destruct(OSAbstMod.get x25 a);
    destruct(OSAbstMod.get x26 a);
    destruct(OSAbstMod.get x17 a);
    destruct(OSAbstMod.get x16 a);
    tryfalse; substs; auto.
  
  unfold tcbdllseg; unfold dllseg; fold dllseg.
  sep split; auto.
  exists x9.
  sep split; auto.
  simpl_sat_goal.
  exists x22 x13; eexists.
  exists x25 x16; eexists.
  repeat (split; eauto).
  clear - H6 H21 H14.
  eapply MemMod.join_merge_disj.
  unfolds; intro.
  pose proof H6 a; pose proof H21 a; pose proof H14 a.
  rewrite MemMod.merge_sem in H1.
  destruct (MemMod.get x3 a);
    destruct (MemMod.get x4 a);
    destruct (MemMod.get m a);
    destruct (MemMod.get x22 a);
    destruct (MemMod.get x23 a);
    destruct (MemMod.get x13 a);
    destruct (MemMod.get x14 a);
    tryfalse; auto.
  
  clear - H8 H23 H16.
  eapply OSAbstMod.join_merge_disj.
  unfolds; intros.
  pose proof H8 a; pose proof H23 a; pose proof H16 a.
  rewrite OSAbstMod.merge_sem in H1.
  destruct (OSAbstMod.get x6 a);
    destruct (OSAbstMod.get x7 a);
    destruct (OSAbstMod.get o a);
    destruct (OSAbstMod.get x25 a);
    destruct (OSAbstMod.get x26 a);
    destruct (OSAbstMod.get x16 a);
    destruct (OSAbstMod.get x17 a);
    tryfalse; auto.

  exists x19 x20 x14 x24 x27 x17.
  repeat (split; eauto).

  simpl; do 4 eexists; repeat (split; eauto).
  clear - H3 H13.
  unfold TcbJoin in *.
  unfolds; intros.
  pose proof H3 a; pose proof H13 a.
  rewrite TcbMod.merge_sem.
  destruct(TcbMod.get (TcbMod.sig x x2) a);
    destruct (TcbMod.get x1 a);
    destruct (TcbMod.get tls a);
    destruct (TcbMod.get x10 a);
    destruct (TcbMod.get x11 a); tryfalse; auto.
  
  clear - H3 H13.
  unfold TcbJoin in *.
  unfolds; intros.
  pose proof H3 a; pose proof H13 a.
  rewrite TcbMod.merge_sem.
  destruct(TcbMod.get (TcbMod.sig x x2) a);
    destruct (TcbMod.get x1 a);
    destruct (TcbMod.get tls a);
    destruct (TcbMod.get x10 a);
    destruct (TcbMod.get x11 a); tryfalse; substs; auto.

  {
    eapply get_last_tcb_ptr_prop.
    eauto.
    auto.
  }
Qed.

Lemma lzh_tcb_list_split:
  forall s P head headpre tail tailnext l tid abstcb tcbls rtbl,
    s |= tcbdllseg head headpre tail tailnext l ** P ->
    TcbMod.get tcbls tid = Some abstcb ->
    TCBList_P head l rtbl tcbls ->
    s |= EX ltcb l1 l2 p p_pre p_next tcbls1 tcbls2' tcbls2,
  [| p = Vptr tid |] **
                     tcbdllseg head headpre p_pre p l1 **
                     node p ltcb OS_TCB **
                     [| V_OSTCBNext ltcb = Some p_next |] **
                     [| get_last_tcb_ptr l1 head = Some p |] **
                     [| V_OSTCBPrev ltcb = Some p_pre |] **
                     tcbdllseg p_next p tail tailnext l2 **
                     [| l = l1 ++ ltcb :: l2 |] **
                     [| TcbMod.join tcbls1 tcbls2' tcbls |] **
                     [| TcbMod.joinsig tid abstcb tcbls2 tcbls2' |] **
                     [| TCBNode_P ltcb rtbl abstcb |] **
                     [| TCBList_P head l1 rtbl tcbls1 |] **
                     [| TCBList_P p_next l2 rtbl tcbls2 |] ** P.
  intros.
  lets F1: TCBList_P_split_by_tcbls_verbose H0 H1 H.
  simpljoin.
  rename H7 into Fzero.
  unfold TCBList_P in H4.
  fold TCBList_P in H4.
  simpljoin.
  inverts H4.
  assert (abstcb = x8).
  {
    unfold TcbJoin in *.
    assert (Htmp: TcbMod.get tcbls x5 = Some x8).
    {
      eapply TcbMod.join_get_get_r.
      eapply H5.
      eapply TcbMod.join_sig_get.
      eauto.
    }
    rewrite Htmp in H0.
    inverts H0.
    auto.
  }
  subst x8.
  sep pauto.
  sep cancel tcbdllseg.
  2: eauto.
  2: eauto.
  2: eauto.
  2: eauto.
  2: eauto.
  3: eauto.
  3: eauto.
  unfold tcbdllseg in *.
  unfold dllseg in H2.
  fold dllseg in H2.
  sep pauto.
  rewrite H6 in H10.
  inverts H10.
  auto.
  {
    unfold tcbdllseg in *.
    unfold dllseg in *.
    fold dllseg in *.
    sep pauto.
  }
Qed.

Lemma mund_int_a1:
  forall i,
    Int.unsigned i <= 65535 ->
    Int.unsigned (i>>ᵢ$ 8) <= 255.
  apply acpt_intlemma10.
Qed.  


Lemma mund_int_a2:
  forall i,
    Int.unsigned i <= 255 ->
    (if Int.unsigned i <=? Byte.max_unsigned then true else false) = true.
  intros.
  apply leb_bytemax_true_intro in H.
  rewrite H.
  auto.
Qed.


Lemma mund_val_inj_a0:
  forall (b:bool),
    val_inj
      (if b
       then Some (Vint32 Int.one)
       else Some (Vint32 Int.zero)) <> Vundef.
  intros; pauto.
Qed.


Lemma mund_val_inj_a1:
  forall (b1 b2:bool),
    val_inj
      (bool_or
         (val_inj
            (if b1
             then Some (Vint32 Int.one)
             else Some (Vint32 Int.zero)))
         (val_inj
            (if b2
             then Some (Vint32 Int.one)
             else Some (Vint32 Int.zero)))) <> Vundef.
  intros; pauto.
Qed.


Lemma mund_int_ltu_revers:
  forall x y,
    Int.ltu x y = true \/ Int.eq x y = true ->
    Int.ltu y x = false.
  intros.
  destruct H.
  unfold Int.ltu in *.
  destruct (zlt (Int.unsigned x) (Int.unsigned y)).
  destruct (zlt (Int.unsigned y) (Int.unsigned x)).
  omega.
  auto.
  tryfalse.
  lzh_simpl_int_eq.
  subst.
  unfold Int.ltu in *.
  destruct (zlt (Int.unsigned y) (Int.unsigned y)).
  omega.
  auto.
Qed.


Lemma absinfer_mutex_pend_cur_prio_higher:
  forall P ecbls tcbls t ct v prio st msg pr owner wls eid,
    Int.unsigned v <= 65535 ->
    TcbMod.get tcbls ct = Some (prio, st, msg) ->
    EcbMod.get ecbls eid = Some (absmutexsem pr owner, wls) ->
    Int.ltu pr prio = false ->
    can_change_aop P ->
    absinfer
      (<|| mutexpend (Vptr eid :: Vint32 v :: nil) ||> **
           HECBList ecbls **
           HTCBList tcbls **
           HTime t **
           HCurTCB ct ** P)
      (<|| END (Some (Vint32 (Int.repr OS_ERR_MUTEX_PRIO)))||> **
           HECBList ecbls **
           HTCBList tcbls **
           HTime t **
           HCurTCB ct ** P).
  infer_solver 5%nat.
  (*  repeat tri_exists_and_solver1. *)
Qed.


Lemma mund_int_a3:
  forall i,
    Int.unsigned i <= 65535 ->
    Int.unsigned (i&ᵢ$ OS_MUTEX_KEEP_LOWER_8) <= 255.
  intros.
  apply postintlemma3.
Qed.


Lemma mund_int_byte_modulus:
  Byte.modulus = 256.
  unfold Byte.modulus.
  unfold Byte.wordsize.
  unfold Wordsize_8.wordsize.
  unfold two_power_nat.
  int auto.
Qed.  


Lemma mund_int_mod:
  forall i,
    Int.unsigned i <= 255 ->
    $ Int.unsigned i mod 256 = i.
  intros.
  rewrite Coqlib.Zmod_small.
  apply Int.repr_unsigned.
  int auto.
Qed.


(* Lemma absinfer_mutex_pend_available_return:
 *   forall P v sid prio m pr els tls t ct,
 *     can_change_aop P ->
 *     Int.unsigned v <= 65535 ->
 *     TcbMod.get tls ct = Some (prio, rdy, m) ->
 *     EcbMod.get els sid = Some (absmutexsem pr None, nil) ->
 *     Int.ltu pr prio = true ->
 *     absinfer
 *       ( <|| mutexpend (Vptr sid :: Vint32 v :: nil) ||> **
 *             HECBList els **
 *             HTCBList tls **
 *             HTime t **
 *             HCurTCB ct ** P)
 *       ( <|| END (Some (Vint32 (Int.repr NO_ERR))) ||> **
 *             HECBList (EcbMod.set els sid (absmutexsem pr (Some (ct, prio)), nil)) **
 *             HTCBList tls **
 *             HTime t **
 *             HCurTCB ct ** P).
 *   infer_solver 6%nat.
 * Qed. *)



Lemma lzh_ecb_join_set_one:
  forall ml a b ml1 ml2 ml1' med b',
    RLH_ECBData_P med b' ->
    EcbMod.get ml a = Some b -> 
    EcbMod.joinsig a
                   b ml1' ml1 ->
    EcbMod.join ml2 ml1 ml -> 
    exists ml1n, EcbMod.joinsig a b' ml1' ml1n /\ EcbMod.join ml2 ml1n (EcbMod.set ml a b'). 
Proof.
  intros.
  exists (EcbMod.set ml1 a b').
  split.
  eapply EcbMod.joinsig_set; eauto.
  eapply EcbMod.joinsig_set_set; eauto.
Qed.


Lemma TCBList_get_head:
  forall tcbls tid abstcb vl l rtbl,
    TCBList_P (Vptr tid) (vl :: l) rtbl tcbls ->
    TcbMod.get tcbls tid = Some abstcb ->
    TCBNode_P vl rtbl abstcb.
Proof.
  intros.
  unfolds in H.
  mytac.
  clear H4.
  inverts H.
  unfolds in H2.
  assert (Hget: TcbMod.get tcbls x = Some x2).
  eapply TcbMod.join_get_l.
  eauto.
  go.
  rewrite tidspec.eq_beq_true.
  auto.
  auto.
  rewrite Hget in H0.
  inverts H0.
  auto.
Qed.


Lemma mund_ltu_a1:
  Int.ltu Int.zero Int.zero = false.
  int auto.
Qed.

Lemma mund_ltu_a2:
  Int.ltu Int.zero Int.one = true.
  int auto.
Qed.  


Lemma mund_int_byte_max_unsigned:
  Byte.max_unsigned = 255.
  unfold Byte.max_unsigned.
  rewrite mund_int_byte_modulus.
  simpl.
  auto.
Qed.


Lemma mund_to_nat_a1:
  forall i,
    Int.unsigned i < 64 ->
    (Z.to_nat (Int.unsigned i) < 64)%nat.
  intros.
  apply intlt2nat in H.
  int auto.
Qed.

Lemma mund_nth_val_a1:
  forall i v'32,
    Int.unsigned i < 64 ->
    array_type_vallist_match OS_TCB ∗ v'32 ->
    length v'32 = 64%nat ->
    (exists v, (nth_val' (Z.to_nat (Int.unsigned i)) v'32) = Vptr v) \/
    (nth_val' (Z.to_nat (Int.unsigned i)) v'32) = Vnull.
Proof.
  intros.
  lets F: array_type_vallist_match_imp_rule_type_val_match H0.
  rewrite H1.
  instantiate (1:=(Z.to_nat (Int.unsigned i))).
  apply mund_to_nat_a1.
  auto.
  lets F': rule_type_val_match_ptr_elim F.
  unfold isptr in F'.
  destruct F'; auto.
Qed.

(* absinfer lemma *)
(* Lemma absinfer_mutex_pend_null_return:
 *   forall P x, 
 *     can_change_aop P ->
 *     tl_vl_match  (Tint16 :: nil) x = true ->
 *     absinfer
 *       (<|| mutexpend (Vnull :: x) ||> ** P)
 *       (<|| END (Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL))) ||> ** P).
 * Proof.
 *   infer_solver 0%nat.
 * Qed.
 * 
 * 
 * Lemma absinfer_mbox_pend_p_not_legal_return :
 *   forall x a P b v'33 v'16 v'35, 
 *     can_change_aop P ->
 *     Int.unsigned b<=65535 ->
 *     EcbMod.get x a = None ->
 *     absinfer
 *       (<|| mutexpend (Vptr a ::Vint32 b:: nil) ||> **
 *            HECBList x **
 *            HTCBList v'33 **
 *            HTime v'16 **
 *            HCurTCB v'35 ** P)
 *       (<|| END (Some  (V$ OS_ERR_PEVENT_NO_EX)) ||> **
 *            HECBList x **
 *            HTCBList v'33 **
 *            HTime v'16 **
 *            HCurTCB v'35 ** P).
 * Proof.
 *   infer_solver 1%nat.
 * Qed. *)


Lemma mutex_eventtype_neq_mutex:
  forall s P a msgq mq t,
    s |= AEventData a msgq ** P ->
    RLH_ECBData_P msgq mq ->
    V_OSEventType a = Some (Vint32 t) ->
    t <> ($ OS_EVENT_TYPE_MUTEX) ->
    s |= AEventData a msgq **
      [| (~ exists pr owner wls, mq = (absmutexsem pr owner, wls)) |] ** P.
Proof.
  intros.

  unfold AEventData in *.
  destruct msgq eqn:Hmsgq.
  sep split in H.
  sep auto.
  unfold RLH_ECBData_P in H0.
  destruct mq; destruct e eqn:Hmq; tryfalse.
  unfold not; intros; mytac; tryfalse.
  
  sep split in H.
  sep auto.
  unfold RLH_ECBData_P in H0.
  destruct mq; destruct e eqn:Hmq; tryfalse.
  unfold not; intros; mytac; tryfalse.

  sep split in H.
  sep auto.
  unfold RLH_ECBData_P in H0.
  destruct mq; destruct e eqn:Hmq; tryfalse.
  unfold not; intros; mytac; tryfalse.

  sep split in H.
  rewrite H3 in H1.
  inverts H1.
  tryfalse.
Qed.


(* Lemma absinfer_mutex_pend_wrong_type_return :
 *   forall x a b P v'33 v'16 v'35, 
 *     can_change_aop P ->
 *     Int.unsigned b <= 65535 ->
 *     (exists d,
 *        EcbMod.get x a = Some d /\ ~ (exists x y wls, d = (absmutexsem x y, wls))) ->
 *     absinfer
 *       (<|| mutexpend (Vptr a :: Vint32 b :: nil) ||> **
 *            HECBList x **
 *            HTCBList v'33 **
 *            HTime v'16 **
 *            HCurTCB v'35 ** P)
 *       (<|| END (Some  (V$ OS_ERR_EVENT_TYPE)) ||> **
 *            HECBList x **
 *            HTCBList v'33 **
 *            HTime v'16 **
 *            HCurTCB v'35 ** P).
 * Proof.
 *   infer_solver 2%nat.
 * Qed.   *)


Lemma mutex_triangle:
  (* 3种表示方式的关系 *)
  forall s P a x y msgq mq,
    s |= AEventData a msgq ** P ->
    RLH_ECBData_P msgq mq ->
    V_OSEventType a = Some (V$OS_EVENT_TYPE_MUTEX) ->
    V_OSEventCnt a = Some x ->
    V_OSEventPtr a = Some y ->
    s |= AEventData a msgq ** 
      [| exists pr own wls, msgq = DMutex x y
                            /\ mq = (absmutexsem pr own, wls)
                            /\ MatchMutexSem x y pr own
                            /\ RH_ECB_P mq|] ** P.
  intros.
  sep pauto.
  unfold AEventData in *.
  destruct msgq eqn:Hmsgq; sep split in H. 
  - rewrite H1 in H5; tryfalse.
  - rewrite H1 in H4; tryfalse.
  - rewrite H1 in H4; tryfalse. 
  - unfold RLH_ECBData_P in H0.
    rewrite H2 in *.
    rewrite H3 in *.
    inverts H5; inverts H6.
    clear H4 H2 H3.
    destruct mq; destruct e eqn:Hmq; tryfalse.
    exists i o w.
    mytac.
    auto.
    auto.
Qed.  


Lemma TCBList_imp_TCBNode:
  forall v v'52 v'26 x12 x11 i8 i7 i6 i5 i4 i3 i1 v'37 v'38 v'47,
    TCBList_P (Vptr v)
              ((v'52
                  :: v'26
                  :: x12
                  :: x11
                  :: Vint32 i8
                  :: Vint32 i7
                  :: Vint32 i6
                  :: Vint32 i5
                  :: Vint32 i4
                  :: Vint32 i3 :: Vint32 i1 :: nil) :: v'37)
              v'38 v'47 ->
    exists abstcb,
      TCBNode_P 
        (v'52
           :: v'26
           :: x12
           :: x11
           :: Vint32 i8
           :: Vint32 i7
           :: Vint32 i6
           :: Vint32 i5
           :: Vint32 i4 :: Vint32 i3 :: Vint32 i1 :: nil)
        v'38 abstcb /\
      TcbMod.get v'47 v = Some abstcb /\
      exists st, abstcb = (i6, st, x11).
Proof.
  intros.
  unfolds in H.
  simpljoin.
  exists x2.
  fold TCBList_P in H3.
  split.
  auto.
  unfold TCBNode_P in H2.
  destruct x2; destruct p.
  simpljoin.
  inverts H; inverts H2; inverts H4.
  split.
  eapply TcbMod.join_get_l.
  eauto.
  eapply TcbMod.get_a_sig_a.
  eapply CltEnvMod.beq_refl.
  exists t.
  auto.
Qed.  


(* Lemma absinfer_mutex_pend_from_idle_return :
 *   forall x a b P y t ct, 
 *     can_change_aop P ->
 *     Int.unsigned b <= 65535 ->
 *     (exists st msg, TcbMod.get y ct = Some (Int.repr OS_IDLE_PRIO, st, msg)) ->
 *     absinfer
 *       (<|| mutexpend (Vptr a :: Vint32 b :: nil) ||> **
 *            HECBList x **
 *            HTCBList y **
 *            HTime t **
 *            HCurTCB ct ** P)
 *       ( <|| END (Some  (V$ OS_ERR_IDLE)) ||> **
 *             HECBList x **
 *             HTCBList y **
 *             HTime t **
 *             HCurTCB ct ** P).
 * Proof.
 *   infer_solver 3%nat.
 * Qed.  
 * 
 * 
 * Lemma absinfer_mutex_pend_not_ready_return :
 *   forall P ecbls tcbls t ct st msg v x prio,
 *     Int.unsigned v <= 65535 ->
 *     TcbMod.get tcbls ct = Some (prio, st, msg) ->
 *     ~ st = rdy ->
 *     can_change_aop P ->
 *     absinfer
 *       (<|| mutexpend (Vptr x :: Vint32 v :: nil) ||> **
 *            HECBList ecbls **
 *            HTCBList tcbls **
 *            HTime t **
 *            HCurTCB ct ** P)
 *       (<|| END (Some (Vint32 (Int.repr OS_ERR_STAT)))||> **
 *            HECBList ecbls **
 *            HTCBList tcbls **
 *            HTime t **
 *            HCurTCB ct ** P).
 * Proof.
 *   infer_solver 4%nat.
 * Qed.  
 * 
 * 
 * Lemma absinfer_mutex_pend_msg_not_null_return :
 *   forall P ecbls tcbls t ct st msg v x prio,
 *     Int.unsigned v <= 65535 ->
 *     TcbMod.get tcbls ct = Some (prio, st, msg) ->
 *     ~ msg = Vnull ->
 *     can_change_aop P ->
 *     absinfer
 *       (<|| mutexpend (Vptr x :: Vint32 v :: nil) ||> **
 *            HECBList ecbls **
 *            HTCBList tcbls **
 *            HTime t **
 *            HCurTCB ct ** P)
 *       (<|| END (Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL)))||> **
 *            HECBList ecbls **
 *            HTCBList tcbls **
 *            HTime t **
 *            HCurTCB ct ** P).
 * Proof.
 *   infer_solver 11%nat.
 * Qed.  
 * 
 * 
 * 
 * Lemma absinfer_mutex_post_null_return : forall P, 
 *                                           can_change_aop P ->
 *                                           absinfer (<|| mutexpost (Vnull :: nil) ||> ** P) ( <|| END (Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL))) ||> ** P).
 * Proof.
 *   infer_solver 0%nat.
 * Qed.
 * 
 * Lemma absinfer_mutex_post_p_not_legal_return : forall x a P tcbls t ct, 
 *                                                  can_change_aop P ->
 *                                                  EcbMod.get x a = None ->
 *                                                  absinfer (<|| mutexpost (Vptr a :: nil) ||> ** HECBList x** HTCBList tcbls ** HTime t ** HCurTCB ct  **
 *                                                                P) ( <|| END (Some  (V$ OS_ERR_PEVENT_NO_EX)) ||> ** HECBList x ** HTCBList tcbls ** HTime t ** HCurTCB ct  ** P).
 * Proof.
 *   infer_solver 1%nat.
 * Qed.
 * 
 * Lemma absinfer_mutex_post_wrong_type_return : forall x a P tcbls t ct, 
 *                                                 can_change_aop P ->
 *                                                 (exists d,
 *                                                    EcbMod.get x a = Some d /\ ~ (exists x y wls, d = (absmutexsem x y, wls))) ->
 *                                                 absinfer (<|| mutexpost (Vptr a :: nil) ||> ** HECBList x ** HTCBList tcbls ** HTime t ** HCurTCB ct **
 *                                                               P) ( <|| END (Some  (V$OS_ERR_EVENT_TYPE)) ||> ** HECBList x ** HTCBList tcbls ** HTime t ** HCurTCB ct ** P).
 * Proof.
 *   infer_solver 2%nat.
 * Qed.
 * 
 * Lemma absinfer_mutex_post_no_owner_return : forall x a P tcbls t ct y y0 wl, 
 *                                               can_change_aop P ->
 *                                               EcbMod.get x a = Some (absmutexsem y0 y, wl) ->
 *                                               (~ exists p, y =Some  (ct,p))  ->
 *                                               absinfer (<|| mutexpost (Vptr a :: nil) ||> ** HECBList x ** HTCBList tcbls ** HTime t ** HCurTCB ct **
 *                                                             P) ( <|| END (Some  (V$OS_ERR_NOT_MUTEX_OWNER)) ||> ** HECBList x ** HTCBList tcbls ** HTime t ** HCurTCB ct ** P).
 * Proof.
 *   infer_solver 3%nat.
 * Qed. *)

*)

Lemma  valinj_lemma1 :
  forall v0 v'52,
    isptr v0 ->val_inj
                 (notint
                    (val_inj
                       match v0 with
                         | Vundef => None
                         | Vnull => Some (Vint32 Int.zero)
                         | Vint32 _ => None
                         | Vptr (b2, ofs2) =>
                           if peq v'52 b2
                           then
                             if Int.eq Int.zero ofs2
                             then Some (Vint32 Int.one)
                             else Some (Vint32 Int.zero)
                           else Some (Vint32 Int.zero)
                       end)) <> Vint32 Int.zero -> v0 = Vnull \/( exists b2 ofs2, v0= Vptr (b2, ofs2) /\ (Int.eq Int.zero ofs2 = false \/ v'52 <> b2)).
Proof.
  intros.
  destruct v0;
    unfolds in H; elim H; intros; mytac; tryfalse.
  left; auto.
  right.
  destruct a.
  do 2 tri_exists_and_solver1.
  split.
  eauto.
  assert (v'52 <> b \/ v'52 = b) by tauto.
  elim H2; intros.
  right ; auto.
  subst v'52.
  rewrite peq_true in H0.
  left.
  remember (Int.eq Int.zero i).
  destruct b0.
  simpl in H0.
  unfold Int.notbool in H0.
  int auto.
  auto.
Qed.

Lemma  valinj_lemma2:forall v0 v'52, val_inj
                                       (notint
                                          (val_inj
                                             match v0 with
                                               | Vundef => None
                                               | Vnull => Some (Vint32 Int.zero)
                                               | Vint32 _ => None
                                               | Vptr (b2, ofs2) =>
                                                 if peq v'52 b2
                                                 then
                                                   if Int.eq Int.zero ofs2
                                                   then Some (Vint32 Int.one)
                                                   else Some (Vint32 Int.zero)
                                                 else Some (Vint32 Int.zero)
                                             end)) = Vint32 Int.zero \/
                                     val_inj
                                       (notint
                                          (val_inj
                                             match v0 with
                                               | Vundef => None
                                               | Vnull => Some (Vint32 Int.zero)
                                               | Vint32 _ => None
                                               | Vptr (b2, ofs2) =>
                                                 if peq v'52 b2
                                                 then
                                                   if Int.eq Int.zero ofs2
                                                   then Some (Vint32 Int.one)
                                                   else Some (Vint32 Int.zero)
                                                 else Some (Vint32 Int.zero)
                                             end)) = Vnull -> v0=Vptr (v'52, $0).
Proof.
  intros.
  elim H; intros.
  destruct v0; simpl in H0; tryfalse.
  destruct a; simpl in H0.
  assert (v'52 = b \/ v'52 <> b) by tauto.
  elim H1; intros.
  subst v'52.
  rewrite peq_true in *.
  assert (i=Int.zero \/ i <> Int.zero).
  tauto.
  elim H2; intros.
  subst i.
  auto.
  rewrite Int.eq_false in H0.
  simpl in H0.
  clear -H0.
  false.
  int auto.

  rewrite peq_false in H0.
  simpl in H0.
  false; clear -H0; int auto.
  auto.

  destruct v0.
  tryfalse.
  tryfalse.
  tryfalse.
  destruct a.
  destruct (Int.eq Int.zero i);
    destruct (peq v'52 b);
    tryfalse.
Qed.


Lemma post_intlemma1 : forall i4 x, Int.unsigned (Int.shru x ($ 8))<64 -> val_inj
                                                                            (if Int.ltu i4 (Int.modu (Int.shru x ($ 8)) ($ Byte.modulus))
                                                                             then Some (Vint32 Int.one)
                                                                             else Some (Vint32 Int.zero)) <> Vint32 Int.zero ->  Int.ltu i4  (Int.shru x ($ 8)) = true.
Proof.
  intros.
  rewrite  mutexdel_intlemma1 in H0.
  destruct ( Int.ltu i4 (Int.shru x ($ 8))).
  auto.
  int auto.
  auto.
Qed.

Lemma unMapvallistint8u :    array_type_vallist_match Int8u OSUnMapVallist.
Proof.
  unfold OSUnMapVallist.
  simpl.
  change Byte.max_unsigned with 255.
  repeat ur_rewriter.
  compute.
  tauto.
Qed.


(* Lemma absinfer_mutex_post_prio_err_return : forall x a P tcbls t ct p stp wl prio st msg,
 *                                               can_change_aop P ->
 *                                               EcbMod.get x a = Some (absmutexsem p stp,wl) ->
 *                                               TcbMod.get tcbls ct = Some (prio,st,msg) ->
 *                                               Int.ltu prio p = true ->
 *                                               absinfer (<|| mutexpost (Vptr a :: nil) ||> ** HECBList x ** HTCBList tcbls ** HTime t ** HCurTCB ct **
 *                                                             P) ( <|| END (Some  (V$OS_ERR_MUTEX_PRIO)) ||> ** HECBList x ** HTCBList tcbls ** HTime t ** HCurTCB ct ** P).
 * Proof.
 *   infer_solver 8%nat.
 * Qed. *)




Lemma post_intlemma2 :forall x i4 , Int.unsigned (Int.shru x ($ 8)) < 64 ->
                                    val_inj (if Int.ltu i4 (Int.modu (Int.shru x ($ 8)) ($ Byte.modulus))
                                             then Some (Vint32 Int.one)
                                             else Some (Vint32 Int.zero)) = Vint32 Int.zero \/
                                    val_inj
                                      (if Int.ltu i4 (Int.modu (Int.shru x ($ 8)) ($ Byte.modulus))
                                       then Some (Vint32 Int.one)
                                       else Some (Vint32 Int.zero)) = Vnull ->  Int.ltu i4  (Int.shru x ($ 8)) = false.
Proof.
  introv HHHH.
  intros.
  elim H; intros.

  rewrite  mutexdel_intlemma1 in H0.
  destruct ( Int.ltu i4 (Int.shru x ($ 8))).
  clear -H0.
  int auto.
  auto.
  auto.
  rewrite  mutexdel_intlemma1 in H0.
  destruct ( Int.ltu i4 (Int.shru x ($ 8))); simpl in H0; tryfalse.
  auto.
Qed.


Lemma Bmax_unsigned : Byte.max_unsigned = 255.
Proof.
  auto.
Qed.

Lemma Bmodulus : Byte.modulus = 256.
Proof.
  auto.
Qed.



(* Lemma absinfer_mutex_post_wl_highest_prio_err_return : forall x a P tcbls t ct pr opr wl sometid somepr somest somemsg, 
 *                                                          can_change_aop P ->
 *                                                          EcbMod.get x a = Some (absmutexsem pr opr, wl) ->
 *                                                          In sometid wl ->
 *                                                          TcbMod.get tcbls sometid = Some (somepr, somest, somemsg) ->
 *                                                          Int.ltu pr somepr = false -> 
 *                                                          absinfer (<|| mutexpost (Vptr a :: nil) ||> ** HECBList x ** HTCBList tcbls ** HTime t ** HCurTCB ct **
 *                                                                        P) ( <|| END (Some  (V$OS_ERR_MUTEX_WL_HIGHEST_PRIO)) ||> ** HECBList x ** HTCBList tcbls ** HTime t ** HCurTCB ct ** P).
 * Proof.
 *   infer_solver 9%nat.
 * Qed.
 * 
 * Lemma absinfer_mutex_post_original_not_holder_err_return : forall x a P tcbls t ct,
 *                                                              can_change_aop P ->
 *                                                              absinfer (<|| mutexpost (Vptr a :: nil) ||> ** HECBList x ** HTCBList tcbls ** HTime t ** HCurTCB ct **
 *                                                                            P) ( <|| END (Some  (V$OS_ERR_ORIGINAL_NOT_HOLDER)) ||> ** HECBList x ** HTCBList tcbls ** HTime t ** HCurTCB ct ** P).
 * Proof.
 *   infer_solver 7%nat.
 * Qed. *)

Lemma simpl_valinj : forall i5 i6 a b, val_inj
                                         (bool_or
                                            (val_inj
                                               (notint
                                                  (val_inj
                                                     (if Int.eq i5 a
                                                      then Some (Vint32 Int.one)
                                                      else Some (Vint32 Int.zero)))))
                                            (val_inj
                                               (notint
                                                  (val_inj
                                                     (if Int.eq i6 b
                                                      then Some (Vint32 Int.one)
                                                      else Some (Vint32 Int.zero)))))) = 
                                       Vint32 Int.zero \/
                                       val_inj
                                         (bool_or
                                            (val_inj
                                               (notint
                                                  (val_inj
                                                     (if Int.eq i5 a
                                                      then Some (Vint32 Int.one)
                                                      else Some (Vint32 Int.zero)))))
                                            (val_inj
                                               (notint
                                                  (val_inj
                                                     (if Int.eq i6 b
                                                      then Some (Vint32 Int.one)
                                                      else Some (Vint32 Int.zero)))))) = Vnull -> i5 =a /\ i6 = b.
Proof.
  intros.
  elim H; intros.
  Focus 2.
  destruct (Int.eq i5 a); destruct (Int.eq i6 b); clear -H0; simpl in H0; tryfalse.
  remember (Int.eq i5 a); remember (Int.eq i6 b).
  destruct b0; destruct b1; simpl in H0;
  change (Int.notbool Int.one) with Int.zero in *;
  change (Int.notbool Int.zero) with Int.one in *;
  change (Int.ltu Int.zero Int.one) with true in *;
  change (Int.ltu Int.one Int.zero) with false in *;
  change (Int.ltu Int.zero Int.zero) with false in *;
  change (Int.ltu Int.one Int.one) with false in *; simpl in H0; tryfalse.
  clear H H0.
  split; int auto.
  apply unsigned_inj; auto.
  apply unsigned_inj; auto.
Qed.
(*lemmas*)
Lemma prio_from_grp_tbl_PrioWaitInQ :
  forall grp evnt_rdy_tbl x1 x2 x3,
    length evnt_rdy_tbl = ∘OS_EVENT_TBL_SIZE ->
    RL_Tbl_Grp_P evnt_rdy_tbl (Vint32 grp) ->
    Int.unsigned x2 <= 255 ->
    Int.unsigned grp <= 255 ->
    grp <> $ 0 ->
    nth_val' (Z.to_nat (Int.unsigned grp)) OSUnMapVallist = Vint32 x1 ->
    nth_val' (Z.to_nat (Int.unsigned x1)) evnt_rdy_tbl = Vint32 x2 ->
    nth_val' (Z.to_nat (Int.unsigned x2)) OSUnMapVallist = Vint32 x3 ->
    PrioWaitInQ (Int.unsigned ((x1<<ᵢ$ 3)+ᵢx3)) evnt_rdy_tbl.
Proof.
  intros.
  unfold PrioWaitInQ.
  exists x3 x1 x2.
  assert(0<= Int.unsigned x1 < 8).

Local Ltac mytac_1' :=
  match goal with
    | H:exists _, _ |- _ => destruct H; mytac_1'
    | H:_ /\ _ |- _ => destruct H; mytac_1'
    |  _ => try (progress subst; mytac_1')
  end.

Local Ltac mytac' := repeat progress mytac_1'.


  lets Hx: osunmapvallist_prop H2; mytac'.
  rewrite H4 in H7; inverts H7.
  apply Zle_bool_imp_le in H8.
  int auto.

  assert(0<= Int.unsigned x3 < 8).
  lets Hx: osunmapvallist_prop H1; mytac'.
  rewrite H6 in H8; inverts H8.
  apply Zle_bool_imp_le in H9.
  int auto.
  splits.
  eapply math_88_prio_range.
  int auto.
  int auto.
  lets Hx: intlt2nat H10.
  int auto.
  symmetry.
  rewrite Int.repr_unsigned.
  eapply math_8range_eqy.
  int auto.
  lets Hx: intlt2nat H10.
  int auto.
  int auto.

  symmetry.
  rewrite Int.repr_unsigned.
  eapply math_shrl_3_eq; int auto.
  lets Hx: intlt2nat H10.
  int auto.
  apply nth_val'_imply_nth_val; auto.
  rewrite H.
  unfold OS_EVENT_TBL_SIZE.
  apply Z_le_nat; auto.
  apply math_8_255_eq; auto.
  unfolds in H0.
  assert(0<= Z.to_nat (Int.unsigned x1) < 8)%nat.
  mytac.
  int auto.
  lets Hx: intlt2nat H10.
  int auto.
  assert (nth_val (Z.to_nat (Int.unsigned x1)) evnt_rdy_tbl = Some (Vint32 x2)).
  apply nth_val'_imply_nth_val; auto.
  rewrite H.
  unfold OS_EVENT_TBL_SIZE.
  replace (∘8) with 8%nat.
  int auto.
  int auto.
  assert (Vint32 grp = Vint32 grp) by auto.
  lets Hx: H0 H9 H10 H11.
  mytac.
  destruct H13.
  clear H12 H13.
  assert(grp&ᵢ($ 1<<ᵢ$ Z.of_nat (Z.to_nat (Int.unsigned x1))) =
         $ 1<<ᵢ$ Z.of_nat (Z.to_nat (Int.unsigned x1))).
  eapply math_8_255_eq; auto.
  rewrite nat_elim; auto.
  apply H11 in H12.
  intro; substs.
  unfolds in H12.
  rewrite zlt_false in H12.
  inverts H12.
  rewrite Int.unsigned_repr.
  omega.
  split.
  omega.
  unfold Int.max_unsigned.
  simpl.
  omega.
Qed.

Lemma int_ltu_zero_one_true : Int.ltu Int.zero Int.one = true.
Proof.
  unfold Int.ltu.
  rewrite Int.unsigned_zero.
  rewrite Int.unsigned_one.
  apply zlt_true.
  omega.
Qed.
Lemma int_ltu_zero_notbool_one_false : Int.ltu Int.zero (Int.notbool Int.one) = false.
Proof.
  unfold Int.notbool.
  rewrite Int.eq_false.
  unfold Int.ltu.
  rewrite zlt_false.
  auto.
  rewrite Int.unsigned_zero.
  omega.
  intro.
  inversion H.
Qed.
Lemma int_ltu_zero_zero_false : Int.ltu Int.zero Int.zero = false.
Proof.
  unfold Int.ltu.
  rewrite Int.unsigned_zero.
  rewrite zlt_false.
  auto.
  omega.
Qed.

Lemma int_ltu_zero_notbool_zero_true : Int.ltu Int.zero (Int.notbool Int.zero) = true.
Proof.
  unfold Int.notbool.
  rewrite Int.eq_true.
  unfold Int.ltu.
  rewrite zlt_true.
  auto. 
  rewrite Int.unsigned_zero; rewrite Int.unsigned_one.
  omega.
Qed.

(*end of lemmas*)


(* Lemma mutexacc_null_absinfer:forall P, can_change_aop P -> absinfer
 *                                                              ( <|| mutexacc (Vnull :: nil) ||>  **
 *                                                                    P) (<|| END (Some (V$0)) ||>  **
 *                                                                            P).
 * Proof.
 *   infer_solver 0%nat.
 * Qed.
 * 
 * 
 * Lemma mutexacc_no_mutex_err_absinfer:
 *   forall P mqls x v1 v3 ct,
 *     can_change_aop P ->
 *     (~ exists a b wl,EcbMod.get mqls x = Some (absmutexsem a b,wl)) ->
 *     absinfer
 *       ( <|| mutexacc  (Vptr x :: nil) ||>  ** HECBList mqls **  HTCBList v1 **
 *             HTime v3 **
 *             HCurTCB ct **
 *             P)
 *       (<|| END (Some (V$0)) ||>  ** HECBList mqls **  HTCBList v1 **
 *            HTime v3 **
 *            HCurTCB ct **
 *            P).
 * Proof.
 *   infer_solver 1%nat.
 * Qed.
 * 
 * Lemma mutexacc_no_available_absinfer:
 *   forall P mqls x wl p o v1 v3 ct,  
 *     can_change_aop P ->  
 *     EcbMod.get mqls x = Some (absmutexsem p (Some o),wl)-> 
 *     absinfer
 *       ( <|| mutexacc (Vptr x :: nil) ||>  ** 
 *             HECBList mqls **  HTCBList v1 **
 *             HTime v3 **
 *             HCurTCB ct ** P) 
 *       (<|| END (Some (V$0)) ||>  ** HECBList mqls **  HTCBList v1 **
 *            HTime v3 **
 *            HCurTCB ct **
 *            P).
 * Proof.
 *   infer_solver 2%nat.
 * Qed.
 * 
 * 
 * Lemma  mutexacc_prio_err_absinfer:
 *   forall P mqls x wl p v1 v3 ct pt st m owner,  
 *     can_change_aop P ->  
 *     EcbMod.get mqls x = Some (absmutexsem p owner,wl)-> TcbMod.get v1 ct = Some (pt,st,m) -> 
 *     Int.ltu p pt = false ->
 *     absinfer
 *       ( <|| mutexacc (Vptr x :: nil) ||>  ** 
 *             HECBList mqls **  HTCBList v1 **
 *             HTime v3 **
 *             HCurTCB ct ** P) 
 *       (<|| END (Some (V$0)) ||>  ** HECBList mqls **  HTCBList v1 **
 *            HTime v3 **
 *            HCurTCB ct **
 *            P).
 * Proof.
 *   infer_solver 3%nat.
 * Qed.
 * 
 * 
 * Lemma mutexacc_succ_absinfer:
 *   forall P mqls x wl v1 v3 ct p pt st m, 
 *     can_change_aop P ->  
 *     EcbMod.get mqls x = Some (absmutexsem p None,wl) ->
 *     TcbMod.get v1 ct = Some (pt,st,m) ->
 *     Int.ltu p pt = true->
 *     absinfer
 *       ( <|| mutexacc (Vptr x :: nil) ||>  ** 
 *             HECBList mqls **  HTCBList v1 **
 *             HTime v3 **
 *             HCurTCB ct **
 *             P) 
 *       (<|| END (Some (V$1)) ||>  ** HECBList (EcbMod.set mqls x (absmutexsem p (Some (ct,pt)),wl)) **  HTCBList v1 **
 *            HTime v3 **
 *            HCurTCB ct **
 *            P).
 * Proof.
 *   infer_solver 4%nat.
 * Qed. *)
(*
Lemma mutexacc_idle_err_absinfer:
  forall P mqls x v1 v3 ct st m, 
    can_change_aop P ->  
    TcbMod.get v1 ct = Some (Int.repr OS_IDLE_PRIO, st, m) ->
    absinfer
      ( <|| mutexacc (Vptr x :: nil) ||>  ** 
            HECBList mqls **  HTCBList v1 **
      HTime v3 **
      HCurTCB ct **
       P) 
      (<|| END (Some (V$0)) ||>  ** HECBList mqls **  HTCBList v1 **
      HTime v3 **
      HCurTCB ct **
                    P).
Proof.
  infer_solver 5%nat.
Qed.
 *)  





Lemma RLH_ECBData_p_high_mbox_acpt_hold:forall x e w0 i6 v'50, Int.unsigned i6 < 64->   Int.ltu (Int.shru x ($ 8)) i6 = true-> RLH_ECBData_P (DMutex (Vint32 x) Vnull) (e, w0) ->  RLH_ECBData_P
                                                                                                                                                                                     (DMutex (Vint32 (Int.or (x&ᵢ$ OS_MUTEX_KEEP_UPPER_8) i6))
                                                                                                                                                                                             (Vptr (v'50, Int.zero))) (absmutexsem (Int.shru ( Int.or (x &ᵢ $ OS_MUTEX_KEEP_UPPER_8) i6) ($ 8)) ( Some
                                                                                                                                                                                                                                                                                                   (v'50, Int.zero, i6)), w0)
.
Proof.
  introv HHH HHHH.
  intros.
  unfolds in H.
  destruct e; tryfalse.
  unfolds.
  mytac.
  unfolds in H.
  unfolds in H0.
  mytac.
  unfolds.
  do 2 eexists.
  splits.
  eauto.
  apply acpt_intlemma6.
  omega.

  auto.
  eauto.
  unfold OS_MUTEX_AVAILABLE. (* i6 <> 63 *)  

  intro.
  false.

  eapply acpt_intlemma5.
  exact HHH.
  exact H5.
  intro.
  eexists.
  split.
  eauto.

  rewrite acpt_intlemma3.
  auto.
  omega.
  unfolds.
  splits.
  intro.
  inversion H1.
  intros.
  inverts H1.
  splits.
  lets aaaa: acpt_intlemma9 HHH HHHH.
  rewrite acpt_intlemma4.
  auto.
  auto.
  auto.
  auto.
  intro.
  intro; tryfalse.
  rewrite acpt_intlemma4.
  clear -HHH HHHH.
  int auto.
  lets aaaa: acpt_intlemma9 HHH HHHH.
  auto.
  omega.
Qed.
Lemma l2 : forall T  b (a:T), (a::nil) ++ b = a :: b.
  intros.
  simpl.
  auto.
Qed.





(* Lemma mutexcre_error_absinfer :
 *   forall P i, 
 *     can_change_aop P -> 
 *     (Int.unsigned i <=? 255 = true) -> 
 *     absinfer ( <|| mutexcre (Vint32 i :: nil) ||> ** P)
 *              ( <|| END (Some Vnull) ||> ** P).
 * Proof.
 *   infer_solver 0%nat.
 * Qed.
 * 
 * Lemma mutexcre_succ_absinfer :
 *   forall P i qid  qls  tcbls curtid tm,
 *     can_change_aop P ->
 *     (Int.unsigned i <=? 255 = true) -> 
 *     prio_available i tcbls ->
 *     Int.ltu i (Int.repr OS_LOWEST_PRIO)= true ->
 *     EcbMod.get qls qid = None  ->
 *     absinfer ( <|| mutexcre (Vint32 i :: nil) ||>
 *                    **HECBList qls **   HTCBList tcbls ** HTime tm **  HCurTCB curtid ** P)
 *              ( <|| END (Some (Vptr qid)) ||> **                                                                                                                 
 *                    HECBList (EcbMod.set qls qid (absmutexsem i
 *                                                              None,
 *                                                  nil:list tid)) **HTCBList tcbls **  HTime tm **
 *                    HCurTCB curtid **P).
 * Proof.
 *   infer_solver 1%nat.
 * Qed. *)
Lemma intlemma1 :forall v'19 v'21,  id_addrval' (Vptr (v'21, Int.zero)) OSEventTbl OS_EVENT = Some v'19 -> (v'21, Int.zero+ᵢ($ 4+ᵢ($ 2+ᵢ($ 1+ᵢ($ 1+ᵢInt.zero))))) = v'19.
  intros.
  unfold id_addrval' in *.
  unfold id_addrval in *.
  simpl in H.
  inversion H.
  auto.
Qed.


Lemma val_inj_eq'
: forall a ,
    val_inj
      (notint
         (val_inj
            a)) = Vint32 Int.zero \/
    val_inj
      (notint
         (val_inj
            a)) = Vnull ->
    (exists v, a= Some (Vint32 v)) /\a <> Some (Vint32 Int.zero).
Proof.
  intros.
  elim H; intros.
  unfold val_inj in H0.
  unfold notint in H0.
  destruct a;tryfalse.  
  destruct v; tryfalse.
  splits.
  eauto.
  unfold Int.notbool in H0.
  int auto.
  intro.
  inversion H1.
  rewrite H3 in n.
  unfold Int.zero in n.
  ur_rewriter_in n.
  tryfalse.
  destruct a; tryfalse.
  destruct v; tryfalse.
Qed.
Lemma val_eq_some_not_zero : forall xx xxx x,
                               val_eq xx xxx = Some (Vint32 x) ->
                               val_eq xx xxx <> Some (Vint32 Int.zero) ->
                               xx= xxx.
Proof.
  intros.
  unfold val_eq in *.
  destruct xx; destruct xxx; tryfalse; auto.
  destruct a.
  tryfalse.
  remember (Int.eq i i0).
  destruct b.
  int auto.
  apply unsigned_inj in e.
  rewrite e .
  auto.
  tryfalse.
  destruct a; tryfalse.
  destruct a; tryfalse.
  destruct a; tryfalse.
  destruct a; tryfalse.
  destruct a0; tryfalse.
  remember (peq b b0).
  destruct s.
  remember (Int.eq i i0).
  destruct b1.
  rewrite e; auto.
  int auto.
  apply unsigned_inj in e0.
  rewrite e0.
  auto.
  tryfalse.
  tryfalse.
Qed.
Lemma R_PrioTbl_P_update_vhold : forall i v'5 v'14 v'17,  Int.unsigned i < 63->R_PrioTbl_P v'5 v'14 v'17 -> nth_val' (Z.to_nat (Int.unsigned i)) v'5 = Vnull -> R_PrioTbl_P (update_nth_val (Z.to_nat (Int.unsigned i)) v'5 (Vptr v'17)) v'14 v'17.
Proof.
  intros.
  unfold R_PrioTbl_P in *.
  mytac.


  intros.

  assert ((Z.to_nat (Int.unsigned i)) =  ∘(Int.unsigned prio) \/ (Z.to_nat (Int.unsigned i)) <>  ∘(Int.unsigned prio)) by tauto.

  elim H7; intros.
  rewrite H8 in H5.
  eapply nth_upd_eq in H5.
  tryfalse.


  apply H0; auto.   
  eapply nth_upd_neq in H5; eauto.
  intros.
  
  lets aaa: H2 H4.
  mytac; auto.
  
  assert ((Z.to_nat (Int.unsigned i)) =  ∘(Int.unsigned prio) \/ (Z.to_nat (Int.unsigned i)) <>  ∘(Int.unsigned prio)) by tauto.
  elim H7; intros.
  rewrite H8 in H1.
  apply nth_val_nth_val'_some_eq in H5.
  rewrite H1 in H5.
  inversion H5.
  eapply nth_upd_neqrev.
  eauto.
  eauto.
  auto.
Qed.

Lemma RL_RTbl_PrioTbl_P_update_vhold : forall i v'5 v'11 v'17,  Int.unsigned i < 63-> RL_RTbl_PrioTbl_P v'11 v'5 v'17 -> nth_val' (Z.to_nat (Int.unsigned i)) v'5 = Vnull ->   RL_RTbl_PrioTbl_P v'11
                                                                                                                                                                                                 (update_nth_val (Z.to_nat (Int.unsigned i)) v'5 (Vptr v'17)) v'17.
Proof.
  intros.
  unfold RL_RTbl_PrioTbl_P in *.
  intros.

  lets aa : H0 H2 H3.
  mytac.
  eexists; splits; eauto.
  assert ((Z.to_nat (Int.unsigned i)) =  ∘(Int.unsigned p) \/ (Z.to_nat (Int.unsigned i)) <>  ∘(Int.unsigned p)) by tauto.
  elim H7; intros.
  rewrite H8 in H1.
  apply nth_val_nth_val'_some_eq in H4.
  unfold nat_of_Z in H1.
  rewrite H1 in H4.
  inversion H4.

  eapply nth_upd_neqrev.
  eauto.
  eauto.
Qed.



Lemma ECBList_Mutex_Create_prop :
  forall v'41 v'50 v'22 v'28 v'40
         v'37 v'38 v'27 x i,

    Int.unsigned i < 63 ->
    RH_TCBList_ECBList_P v'37 v'38 v'40 ->
    EcbMod.get v'37 (v'41, Int.zero) = None ->
    ECBList_P v'22 Vnull v'28 v'27 v'37 v'38->
    ECBList_P (Vptr (v'41, Int.zero)) Vnull
              
              ((V$OS_EVENT_TYPE_MUTEX   :: Vint32 Int.zero ::  val_inj
                 (or
                    (val_inj
                       (if Int.ltu ($ 8) Int.iwordsize
                        then Some (Vint32 (i<<ᵢ$ 8))
                        else None)) (V$OS_MUTEX_AVAILABLE)) :: x :: v'50 :: v'22 :: nil, INIT_EVENT_TBL) :: v'28)
              (DMutex  (val_inj
                          (or
                             (val_inj
                                (if Int.ltu ($ 8) Int.iwordsize
                                 then Some (Vint32 (i<<ᵢ$ 8))
                                 else None)) (V$OS_MUTEX_AVAILABLE))) Vnull :: v'27)
              (EcbMod.set v'37 (v'41, Int.zero) (absmutexsem i None, nil))
              v'38.
Proof.
  introv HHHHH.
  intros.
  unfolds.
  fold ECBList_P.
  eexists.
  split; eauto.
  split.
  unfolds.
  split.
  unfolds.
  destruct H as (Ha1 & Ha2 & Ha3 & Ha4).
  splits;
    unfolds;
    intros;
    try solve [usimpl H2].
  unfolds in H.
  mytac.
  simpl in H5.
  lets Hres : prio_prop  H H7; eauto.
  assert (nat_of_Z (Int.unsigned (Int.shru ($ prio) ($ 3))) < 8)%nat.
  eapply Z_le_nat; eauto.
  split; auto.
  apply Int.unsigned_range_2.
  remember (nat_of_Z (Int.unsigned (Int.shru ($ prio) ($ 3)))) as  Heq.
  assert (x2=Int.zero) by (eapply nat8_des;eauto).
  subst x2.
  apply int_land_zero in H6; tryfalse.

  destruct H as (Ha1 & Ha2 & Ha3 & Ha4).
  split.
  unfolds.
  splits.
  unfolds.
  intros.
  destruct Ha1 as (Hab & Hac).
  lets Hre : Hac H.
  destruct Hre as (xx & yy & wt & Hec & Hin).
  unfold get in *; simpl in *.
  tryfalse.
  unfolds.
  intros.
  destruct Ha2 as (Hab & Hac).
  lets Hre : Hac H.
  destruct Hre as (xx  & wt & Hec & Hin).
  unfold get in *; simpl in *.
  tryfalse.
  unfolds.
  intros.
  destruct Ha3 as (Hab & Hac).
  lets Hre : Hac H.
  destruct Hre as (xx  & wt & Hec & Hin).
  unfold get in *; simpl in *.
  tryfalse.
  unfolds.
  intros.
  destruct Ha4 as (Hab & Hac & Had).
  lets Hre : Hac H.
  destruct Hre as (xx  & wt & Hec & Hin & Hd).
  unfold get in *; simpl in *.
  tryfalse.
  unfolds.
  branch 4.
  simpl;auto.
  do 3 eexists.
  unfold V_OSEventListPtr.
  simpl nth_val .
  splits; eauto.
  instantiate (1:= (absmutexsem i None, nil)).
  eapply ecbmod_get_sig_set; eauto.
  unfolds.
  splits.
  auto.
  unfolds.
  do 2 eexists.
  splits.
  unfold OS_MUTEX_AVAILABLE.
  int auto.
  clear -HHHHH; mauto.
  clear -HHHHH; mauto.
  eauto.
  intros; tauto.
  intros.
  unfold OS_MUTEX_KEEP_LOWER_8 in H2.
  unfold OS_MUTEX_AVAILABLE in H2.
  false.
  apply H2.
  clear -HHHHH; mauto.
  unfolds.
  splits; auto.
  intros.
  inversion H2.
  omega.
Qed.

Lemma create_val_inj_lemma0: forall i v'5, val_inj
                                             (notint
                                                (val_inj
                                                   (val_eq (nth_val' (Z.to_nat (Int.unsigned i)) v'5) Vnull))) =
                                           Vint32 Int.zero \/
                                           val_inj
                                             (notint
                                                (val_inj
                                                   (val_eq (nth_val' (Z.to_nat (Int.unsigned i)) v'5) Vnull))) =
                                           Vnull ->(nth_val' (Z.to_nat (Int.unsigned i)) v'5) = Vnull.
Proof.
  intros i v'5.
  remember (nth_val' (Z.to_nat (Int.unsigned i)) v'5).
  intros.
  elim H;intros.
  destruct v; simpl in H0; tryfalse.
  auto.
  destruct a.
  int auto.
  destruct v; simpl in H0; tryfalse.
  destruct a.
  int auto.
Qed.
Lemma priotbl_null_no_tcb :forall v'5 v'14 v'17 i, R_PrioTbl_P v'5 v'14 v'17 ->   nth_val (Z.to_nat (Int.unsigned i)) v'5 = Some Vnull -> (~ exists x st msg, TcbMod.get v'14 x = Some ( i, st, msg)).
Proof.
  intros.
  unfolds in H.
  destruct H as (H & H' & H'').
  intro.
  mytac.
  lets aaa: H' H1.
  mytac.
  unfold nat_of_Z in H2.
  rewrite H0 in H2.
  tryfalse.
Qed.



Lemma Mutex_Create_TCB_prop :
  forall v'37  x  i v'38 v'40,
    ~ (exists x st msg, TcbMod.get v'38 x = Some (i, st, msg)) ->
    EcbMod.get v'37 x = None ->
    RH_TCBList_ECBList_P v'37 v'38 v'40 ->
    RH_TCBList_ECBList_P
      (EcbMod.set v'37 x (absmutexsem i None, nil))
      v'38 v'40.
Proof.
  introv HHHHH.
  intros.
  unfolds.
  unfolds in H0.
  destruct H0 as (Ha1 & Ha2 & Ha3 & Ha4).
  split.

  destruct Ha1.
  unfolds.
  split.
  intros.
  rewrite EcbMod.set_sem in H2.
  destruct (tidspec.beq x eid).
  destruct H2.
  inverts H2.
  lets Hres : H0 H2.
  eauto.
  intros.
  lets Hres : H1 H2.
  mytac.
  assert (eid = x \/ eid <> x) by tauto.
  destruct H5.
  subst.
  unfold get in *; simpl in *.
  tryfalse.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  eapply H1; eauto.

  split.

  destruct Ha2.
  unfolds.
  split.
  intros.
  rewrite EcbMod.set_sem in H2.
  destruct (tidspec.beq x eid).
  destruct H2.
  inverts H2.
  lets Hres : H0 H2.
  eauto.
  intros.
  lets Hres : H1 H2.
  mytac.
  assert (eid = x \/ eid <> x) by tauto.
  destruct H5.
  subst.
  unfold get in *; simpl in *.
  tryfalse.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  eapply H1; eauto.

  split.
  Focus 2.
  destruct Ha4.
  unfolds.
  split.
  intros.
  rewrite EcbMod.set_sem in H2.
  destruct (tidspec.beq x eid).
  destruct H2.
  inverts H2.
  simpl in H3; tryfalse.
  eapply H0; eauto.
  split.
  intros.
  rewrite EcbMod.set_sem.
  destruct H1 as (H1 & HHH).
  lets Hres : H1 H2.
  destruct Hres as (x1&qw& Hec & Hin).
  remember (tidspec.beq x eid) as Hbool.
  destruct Hbool.
  apply eq_sym in HeqHbool.
  apply tidspec.beq_true_eq in HeqHbool.
  subst x.
  unfold get in *; simpl in *.
  rewrite H in Hin.
  elim Hin; intros.
  tryfalse.
  mytac.
  do 3 eexists; splits; eauto.
  apply Mutex_owner_set'.
  destruct H1; auto.
  (*
  unfolds.
  intros.
  destruct H1.
  unfolds in H4.
  assert ( x <> eid \/ x = eid) by tauto.
  elim H5; intros.
  rewrite EcbMod.set_a_get_a' in H3.
  eapply H4; eauto.
  apply tidspec.neq_beq_false; auto.
  subst eid.
  intro.
  apply HHHHH.
  rewrite EcbMod.set_a_get_a in H3.
  inversion H3.
  mytac.
  eauto.
  apply CltEnvMod.beq_refl.
   *) 

  destruct Ha3.
  unfolds.
  split.
  intros.
  rewrite EcbMod.set_sem in H2.
  destruct (tidspec.beq x eid).
  destruct H2.
  inverts H2.
  lets Hres : H0 H2.
  eauto.
  intros.
  lets Hres : H1 H2.
  mytac.
  assert (eid = x \/ eid <> x) by tauto.
  destruct H5.
  subst.
  unfold get in *; simpl in *.
  tryfalse.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  eapply H1; eauto.
Qed.

Lemma mutex_createpure : forall v'5 v'14 v'17 i,  R_PrioTbl_P v'5 v'14 v'17 ->  nth_val' (Z.to_nat (Int.unsigned i)) v'5 = Vnull ->   prio_available i v'14.
Proof.
  intros.
  unfolds.
  intros.
  unfolds in H.
  mytac.
  assert (i=p \/ i<> p).
  tauto.
  elim H4; intros.
  subst p.
  lets bb: H2 H1.
  mytac.
  unfold nat_of_Z in H5.
  rewrite (nth_val_nth_val'_some_eq _ _ H5 ) in H0.
  inversion H0.
  clear -H5.
  int auto.
  false.
  apply H5.
  apply unsigned_inj.
  auto.
Qed.







(* Lemma mutexdel_null_absinfer:
 *   forall P , 
 *     can_change_aop P ->
 *     absinfer (<|| mutexdel (Vnull :: nil) ||> ** P)
 *              ( <|| END (Some  (V$ OS_ERR_PEVENT_NULL)) ||> ** P).
 * Proof.
 *   infer_solver 0%nat.
 * Qed.
 * 
 * Lemma mutexdel_no_mutex_err_absinfer:
 *   forall x a P tcbls tm curtid, 
 *     can_change_aop P ->
 *     EcbMod.get x a = None ->
 *     absinfer (<|| mutexdel (Vptr a :: nil) ||>  ** HECBList x ** HTCBList tcbls ** HTime tm **  HCurTCB curtid ** P)
 *              ( <|| END (Some  (V$ OS_ERR_PEVENT_NO_EX)) ||>  ** HECBList x ** HTCBList tcbls ** HTime tm **  HCurTCB curtid ** P).
 * Proof.
 *   infer_solver 1%nat.
 * Qed.
 * 
 * Lemma mutexdel_type_err_absinfer:
 *   forall ecbls a P X tcbls tm curtid, 
 *     can_change_aop P ->
 *     EcbMod.get ecbls a = Some X ->
 *     (~ exists x y wl, X = (absmutexsem x y, wl))->
 *     absinfer (<|| mutexdel (Vptr a :: nil) ||> ** HECBList ecbls ** HTCBList tcbls ** HTime tm **  HCurTCB curtid ** P)
 *              ( <|| END (Some  (V$OS_ERR_EVENT_TYPE)) ||> ** HECBList ecbls ** HTCBList tcbls ** HTime tm **  HCurTCB curtid ** P).
 * Proof.
 *   infer_solver 2%nat.
 * Qed.
 * 
 * 
 * Lemma mutexdel_ex_wt_err_absinfer:
 *   forall x a P p o tl tcbls tm curtid ,
 *     can_change_aop P ->
 *     EcbMod.get x a = Some (absmutexsem p (Some o), tl)->
 *     absinfer (<|| mutexdel (Vptr a :: nil) ||> ** HECBList x  ** HTCBList tcbls ** HTime tm **  HCurTCB curtid ** P)
 *              ( <|| END (Some  (V$ OS_ERR_TASK_WAITING)) ||> ** HECBList x  ** HTCBList tcbls ** HTime tm **  HCurTCB curtid ** P).
 * Proof.
 *   infer_solver 3%nat.
 * Qed. *)



(* Lemma mutexdel_succ_absinfer:
 *   forall x a P z  x' tid t tcbls , 
 *     can_change_aop P ->
 *     EcbMod.get x a = Some (absmutexsem z None, nil) ->
 *     EcbMod.join x' (EcbMod.sig a (absmutexsem z None, nil)) x ->
 *     absinfer (<|| mutexdel (Vptr a :: nil) ||> **
 *                   HECBList x ** HTCBList tcbls ** HTime t **  HCurTCB tid  ** P)
 *              ( <|| END (Some  (V$ NO_ERR)) ||> ** HECBList x' ** HTCBList tcbls **
 *                    HTime t **  HCurTCB tid  ** P).
 * Proof.
 *   infer_solver 4%nat.
 * Qed.
 * 
 * Lemma mutexdel_pr_not_holder_err_absinfer:
 *   forall P tcbls x curtid tm a,
 *     can_change_aop P ->
 *     absinfer (<|| mutexdel (Vptr a ::nil)||>  ** HECBList x  ** HTCBList tcbls ** HTime tm **  HCurTCB curtid ** P) ( <|| END (Some (V$ OS_ERR_MUTEXPR_NOT_HOLDER))||>  ** HECBList x  ** HTCBList tcbls ** HTime tm **  HCurTCB curtid ** P).
 * Proof.
 *   infer_solver 5%nat.
 * Qed. *)


Lemma  ecb_wt_ex_prop_mutex :
  forall
    v'43  v'34 v'38 x v'21 tid
    v'23 v'35 i i3 x2 x3 v'42 v'40,
    Int.eq i ($ 0) = false ->
    Int.unsigned i <= 255 ->
    array_type_vallist_match Int8u v'40 ->
    length v'40 = ∘OS_EVENT_TBL_SIZE ->
    RL_Tbl_Grp_P v'40 (Vint32 i) -> 
    ECBList_P v'38 (Vptr x)  v'21 v'23 v'43 v'35->
    R_ECB_ETbl_P x
                 (V$OS_EVENT_TYPE_MUTEX
                   :: Vint32 i
                   :: Vint32 i3 :: x2 :: x3 :: v'42 :: nil,
                  v'40) v'35 ->
    RH_TCBList_ECBList_P v'34 v'35 tid ->
    exists z zz t' tl,
      EcbMod.get v'34 x = Some (absmutexsem z zz, t' :: tl).
Proof.
  introv Hinteq Hiu Harr Hlen  Hrl Hep Hrp Hz.
  unfolds in Hrp.
  unfolds in Hrl.
  lets Hex : int8_neq0_ex Hiu Hinteq.
  destruct Hex as (n & Hn1 & Hn2).
  lets Heu :  n07_arr_len_ex Hn1 Harr Hlen.
  destruct Heu as (vv & Hnth & Hint).
  assert ( Vint32 i = Vint32 i) by auto.
  lets Hed : Hrl Hn1 Hnth H.
  destruct Hed as (Hed1 & Hed2).
  destruct Hed2.
  lets Hed22 : H0 Hn2.
  destruct Hrp as (Hrp1 & Hrp2).
  unfold PrioWaitInQ in Hrp1.
  lets Hexx : prio_inq Hn1 Hed22 Hint Hnth.
  destruct Hexx as (prio & Hpro).
  unfolds in Hrp1.
  destruct Hrp1 as (Hrpa & Hrpb & Hrpc & Hrp1).
  lets Hxq : Hrp1 Hpro.
  destruct Hxq as (tid' & n0 & m & Hte).
  unfolds; simpl; auto.
  unfolds in Hz.
  destruct Hz as (Hz1 & Hz2 & Hz3 & Hz4).
  destruct Hz4.
  destruct H3.
  lets Hea : H3 Hte.
  mytac.
  apply  inlist_ex in H6.
  mytac.
  do 3 eexists.
  eauto.
Qed.


Lemma inteq_has_value: forall a b, (exists x,  (notint
                                                  (val_inj
                                                     (if Int.eq a b
                                                      then Some (Vint32 Int.one)
                                                      else Some (Vint32 Int.zero))) = Some x)).
Proof.
  intros.
  unfold notint.
  destruct (Int.eq a b).
  simpl.
  eauto.
  simpl.
  eauto.
Qed.



Lemma upd_last_prop:
  forall v g x vl z ,
    V_OSEventListPtr v = Some x ->
    vl = upd_last_ectrls ((v, g) :: nil) z ->
    exists v', vl = ((v', g) ::nil) /\ V_OSEventListPtr v' = Some z.
Proof.
  intros.
  unfolds in H.
  destruct v;simpl in H; tryfalse.
  destruct v0; simpl in H; tryfalse.
  destruct v1; simpl in H; tryfalse.
  destruct v2; simpl in H; tryfalse.
  destruct v3; simpl in H; tryfalse.
  destruct v4; simpl in H; tryfalse.
  inverts H.
  unfold upd_last_ectrls in H0.
  simpl in H0.
  eexists; splits; eauto.
Qed.


Lemma nth_val_upd_prop:
  forall vl n m v x,
    (n<>m)%nat ->
    (nth_val n (ifun_spec.update_nth val m vl v) = Some x  <->
     nth_val n vl  = Some x).
Proof.
  inductions vl.
  intros.
  simpl.
  split;
    intros; tryfalse.
  intros.
  simpl.
  destruct n.
  destruct m.
  tryfalse.
  simpl.
  intros; split; auto.
  destruct m.
  simpl.
  split; auto.
  assert (n <> m) by omega.
  simpl.
  eapply IHvl.
  eauto.
Qed.

Lemma R_ECB_upd_hold :
  forall x1 v v0 v'36 x8,
    R_ECB_ETbl_P x1 (v, v0) v'36 ->
    R_ECB_ETbl_P x1 (ifun_spec.update_nth val 5 v x8, v0) v'36.
Proof.
  introv Hr.
  unfolds in Hr.
  destruct Hr.
  unfolds.
  splits.
  destruct H as (Hr1 & Hr2 & Hr3 & Hr4).
  unfolds in Hr1.
  splits.
  unfolds.
  intros.
  unfolds in H1.
  eapply Hr1; eauto.
  unfolds.
  assert (0<>5)%nat by omega.
  eapply nth_val_upd_prop; eauto.
  unfolds in Hr2.
  unfolds.
  intros.
  eapply Hr2; eauto.
  assert (0<>5)%nat by omega.
  eapply nth_val_upd_prop; eauto.
  unfolds in Hr3.
  unfolds.
  intros.
  eapply Hr3; eauto.
  assert (0<>5)%nat by omega.
  eapply nth_val_upd_prop; eauto.
  unfolds in Hr4.
  unfolds.
  intros.
  eapply Hr4; eauto.
  assert (0<>5)%nat by omega.
  eapply nth_val_upd_prop; eauto.
  destruct H0 as (H0 & _).
  destruct H0 as (Hr1 & Hr2 & Hr3 & Hr4).
  unfolds.
  splits.
  unfolds in Hr1.
  unfolds.
  intros.
  apply Hr1 in H0.
  destruct H0.
  split; eauto.
  assert (0<>5)%nat by omega.
  eapply nth_val_upd_prop; eauto.
  unfolds in Hr2.
  unfolds.
  intros.
  apply Hr2 in H0.
  destruct H0.
  split; eauto.
  assert (0<>5)%nat by omega.
  eapply nth_val_upd_prop; eauto.
  unfolds in Hr3.
  unfolds.
  intros.
  apply Hr3 in H0.
  destruct H0.
  split; eauto.
  assert (0<>5)%nat by omega.
  eapply nth_val_upd_prop; eauto.
  unfolds in Hr4.
  unfolds.
  intros.
  apply Hr4 in H0.
  destruct H0.
  split; eauto.
  assert (0<>5)%nat by omega.
  eapply nth_val_upd_prop; eauto.
  destruct H0.
  unfolds in H1.
  unfolds.
  simpl in *.
  unfold V_OSEventType in *.
  destruct H1.
  left.
  eapply nth_val_upd_prop; eauto.
  destruct H1.
  branch 2.
  eapply nth_val_upd_prop; eauto.
  destruct H1.
  branch 3.
  eapply nth_val_upd_prop; eauto.
  branch 4.
  eapply nth_val_upd_prop; eauto.
Qed.

Lemma ecb_list_join_join :
  forall v'40  v'52 v'61 v'21 x x2  v'36 x8 v'42 v'37 x0 v'51,
    v'40 <> nil ->
    ECBList_P v'52 (Vptr (v'61, Int.zero)) v'40 v'21 x v'36 ->
    ECBList_P x8 Vnull v'42 v'37 x0 v'36 ->
    v'51 = upd_last_ectrls v'40 x8 -> 
    EcbMod.join x0 x x2 -> 
    ECBList_P v'52 Vnull (v'51 ++ v'42) (v'21 ++ v'37) x2 v'36.
Proof.
  inductions v'40.
  simpl.
  intros.
  mytac.
  unfold upd_last_ectrls in H.
  simpl in H.
  tryfalse.
  introv Hneq Hep Hepp Hsom Hj.
  assert (v'40 = nil \/ v'40 <> nil) by tauto.
  destruct H.
  subst v'40.
  destruct v'21.
  simpl in Hep.
  mytac; tryfalse.
  simpl in Hep.
  mytac.
  destruct a.
  mytac.
  remember (upd_last_ectrls ((v, v0) :: nil) x8) as vl.
  lets Hx : upd_last_prop  H Heqvl.
  mytac.
  unfolds in H3.
  simpl in H3.
  inverts H3.
  unfolds upd_last_ectrls.
  simpl.
  eexists; splits; eauto.

  eapply R_ECB_upd_hold; eauto.
  do 2 eexists.
  exists x8.
  split; auto.
  split.
  eapply ecbmod_join_sigg; eauto.
  split; eauto.
  destruct a.
  lets Hzz :  upd_last_prop' Hsom;auto.
  destruct Hzz as (vll & Hv1 & Hv2).
  rewrite Hv1.
  destruct v'21.
  simpl in Hep; mytac; tryfalse.
  simpl.
  simpl in Hep.
  destruct Hep as (qid & Heq & Hr &Hex).
  destruct Hex as (abs & mqls & vv & Heaq & Hjoin & Hrl & Hepc ).
  lets Hxz : joinsig_join_sig2 Hjoin Hj.
  destruct Hxz as (x6 & Hj1 & Hj2).
  subst v'52.
  eexists.
  split; eauto.
  split; auto.
  do 2 eexists.
  exists vv.
  splits; eauto.
Qed.


Lemma ecblist_ecbmod_get_aux_mutex :
  forall v'61 i6  x4 x8 v'58 v'42  
         v'63 x20 v'37 v'35 v'36 v'38 x21,
    array_type_vallist_match Int8u v'58->
    RH_CurTCB v'38 v'36 ->
    length v'58 = ∘OS_EVENT_TBL_SIZE ->
    RH_TCBList_ECBList_P v'35 v'36 v'38 ->
    RL_Tbl_Grp_P v'58 (V$0) ->
    ECBList_P (Vptr (v'61, Int.zero)) Vnull
              (
                ((V$OS_EVENT_TYPE_MUTEX
                   :: V$0 :: Vint32 i6 :: v'63 :: x4 :: x8 :: nil,
                  v'58) :: nil) ++ v'42)
              ((DMutex x20 x21 :: nil) ++ v'37) v'35 v'36 ->
    exists msgls xx,
      EcbMod.get v'35 (v'61, Int.zero) = Some (absmutexsem msgls xx, nil)
      /\ exists vv,  EcbMod.join vv  (EcbMod.sig (v'61, Int.zero) (absmutexsem msgls xx, nil)) v'35 /\ECBList_P x8 Vnull v'42 v'37  vv  v'36.
Proof.
  introv  Harr Hcur Hrl Htcb Hre Hep.
  unfolds in Hre.
  assert (forall n, (0 <= n < 8)%nat  ->  nth_val n v'58 = Some (Vint32 ($ 0))).
  intros.
  lets Hex : n07_arr_len_ex H  Harr Hrl.
  destruct Hex as (vh & Hnth & Hneq).
  assert (V$0 = V$0) as Hasrt by auto.
  lets Hres : Hre H Hnth Hasrt.
  destruct Hres as (Hrs1 & Hrs2).
  destruct Hrs1 as (Hrs11 & Hrs22).
  rewrite Int.and_zero_l in Hrs11.
  assert (vh = $ 0) .
  apply Hrs11.
  auto.
  subst vh.
  auto.
  simpl in Hep.
  destruct Hep as (qid & Heq & Heb & Hex).
  destruct Hex as (absmq & mqls' & v' & Hv & Hej & Hmt & Hlp).
  destruct absmq.
  destruct e; tryfalse.
  usimpl Hv.
  inverts Heq.
  destruct Hmt as (Hm1 & Hm2 ). (* & Hm3 & Hm4). *)  
  mytac.
  exists i o .
  assert (w = nil \/ w <> nil) by tauto.
  destruct H0 as [Hnil | Hnnil].
  Focus 2.
  unfolds in Hcur.
  unfolds in Htcb.
  destruct Htcb as (Htcb1&Htcb2&Htcb3&Htcb4).
  lets Hj : ecbmod_joinsig_get Hej.
  lets Hea : qwaitset_notnil_ex Hnnil.
  destruct Hea as (tid & Hin).
  assert ( EcbMod.get v'35 (v'61, Int.zero) = Some (absmutexsem i o, w) /\ In tid w) by (split; auto).
  destruct Htcb4 as (Htb & Htb2).
  lets Hjj : Htb H0.
  destruct Hjj as (prio & m0 & n & Htcg).
  unfolds in Heb.
  destruct Heb as (Heb1 & Heb2 & _).
  unfolds  in Heb2.
  destruct Heb2 as (Heba & Hebb & Hebd & Hebc).
  lets Hebs : Hebc Htcg.
  lets Hbb : prioinq_exists Hebs.
  destruct Hbb as (n0 & Hnn & Hnth).
  lets Hfs : H Hnn.
  tryfalse.
  subst w.
  split.
  
  eapply ecbmod_joinsig_get; eauto.
  eexists; splits; eauto.
  
  eapply  ecbmod_joinsig_sig; eauto.
Qed.


Lemma ecblist_ecbmod_get_mutex :
  forall v'61 i6  x4 x8 v'58 v'42 v'21 v'63 x20 v'37 v'35 v'36 v'38 x21,
    length v'21 = O  ->
    array_type_vallist_match Int8u v'58->
    RH_CurTCB v'38 v'36 ->
    length v'58 = ∘OS_EVENT_TBL_SIZE ->
    RH_TCBList_ECBList_P v'35 v'36 v'38 ->
    RL_Tbl_Grp_P v'58 (V$0) ->
    ECBList_P (Vptr (v'61, Int.zero)) Vnull
              (nil ++
                   ((V$OS_EVENT_TYPE_MUTEX
                      :: V$0 :: Vint32 i6 :: v'63 :: x4 :: x8 :: nil,
                     v'58) :: nil) ++ v'42)
              (v'21 ++
                    (DMutex x20 x21 :: nil) ++ v'37) v'35 v'36 ->
    exists msgls xx,
      EcbMod.get v'35 (v'61, Int.zero) = Some (absmutexsem msgls xx, nil)
      /\ exists vv,  EcbMod.join vv  (EcbMod.sig (v'61, Int.zero) (absmutexsem msgls xx, nil)) v'35 /\ECBList_P x8 Vnull v'42 v'37  vv  v'36.
Proof.
  introv Hlen Harr Hcur Hrl Htcb Hre Hep.
  destruct v'21.
  2 : simpl in Hlen; tryfalse.
  rewrite app_nil_l in Hep.
  rewrite app_nil_l in Hep.
  eapply ecblist_ecbmod_get_aux_mutex;eauto.
Qed.
Goal forall i0,val_inj
                 (notint
                    (val_inj
                       (if Int.eq i0 ($ 0)
                        then Some (Vint32 Int.one)
                        else Some (Vint32 Int.zero)))) = Vint32 Int.zero -> i0 = $0.
Proof.
  intros.
  assert (i0 = $0 \/ i0<>$0) by tauto.
  elim H0; intros; auto.
  int auto.
  clear -e.
  unfold Int.zero.
  apply unsigned_inj; auto.
Save del_val_inj_lemma0.

Lemma get_last_prop:
  forall (l : list EventCtr)  x v y,
    l <> nil -> 
    (get_last_ptr ((x, v) :: l)  =   y <->
     get_last_ptr  l =  y).
Proof.
  destruct l.
  intros.
  tryfalse.
  intros.
  unfolds get_last_ptr.
  simpl.
  destruct l; splits;auto.
Qed.


Lemma ecblist_p_decompose :
  forall  y1 z1  x y2 z2 t z ,
    length y1 = length y2 ->
    ECBList_P x Vnull (y1++z1) (y2++z2) t z ->
    exists x1 t1 t2,
      ECBList_P x x1 y1 y2 t1 z /\ ECBList_P x1 Vnull z1 z2 t2 z /\
      EcbMod.join t1 t2 t /\  (get_last_ptr y1 = None \/ get_last_ptr y1  = Some x1).
Proof.
  inductions y1; inductions y2.
  simpl.
  intros.
  do 3 eexists; splits; eauto.
  eapply EcbMod.join_emp; eauto.
  intros.
  simpl in H.
  tryfalse.
  intros.
  simpl in H; tryfalse.
  intros.
  simpl in H.
  inverts H.
  simpl in H0.
  mytac.
  destruct a.
  mytac.
  lets Hx : IHy1 H2 H4.
  mytac.
  lets Hex : joinsig_join_ex H1 H7.
  mytac.
  do 3 eexists.
  splits.
  simpl.
  eexists; splits; eauto.
  do 3 eexists; splits.
  eauto.
  2: eauto.
  3: eauto.
  2 : eauto.
  eauto.
  eauto.
  assert (y1 = nil \/ y1 <> nil) by tauto.
  destruct H11.
  subst y1.  
  right.
  simpl in H2.
  apply eq_sym in H2.
  apply length_zero_nil in H2.
  subst y2.
  simpl in H5.
  mytac.
  unfolds.
  simpl.
  auto.
  destruct H8.
  left.
  eapply  get_last_prop in H11.
  eapply H11; eauto.
  eapply  get_last_prop in H11.
  right.
  eapply H11; eauto.
Qed.  

Lemma ecblist_ecbmod_get_mutex' :
  forall v'40 v'52 v'61 i6  x4 x8 v'58 v'42 v'21 xx
         v'63 x20 i5 v'37 v'35 v'36 v'38 x21,
    Some (Vptr (v'61, Int.zero)) = get_last_ptr v'40 ->
    length v'40 = length v'21 ->
    Int.unsigned i5 <= 65535 -> 
    array_type_vallist_match Int8u v'58->
    RH_CurTCB v'38 v'36 ->
    length v'58 = ∘OS_EVENT_TBL_SIZE ->
    RH_TCBList_ECBList_P v'35 v'36 v'38 ->
    RL_Tbl_Grp_P v'58 (V$0) ->
    ECBList_P v'52 Vnull
              (v'40 ++
                    ((V$OS_EVENT_TYPE_MUTEX
                       :: xx :: Vint32 i6 :: v'63 :: x4 :: x8 :: nil,
                      v'58) :: nil) ++ v'42)
              (v'21 ++
                    (DMutex x20 x21 :: nil) ++ v'37) v'35 v'36 ->
    
    exists msgls  xx,
      EcbMod.get v'35 (v'61, Int.zero) = Some (absmutexsem msgls xx, nil)
      /\ exists vg vv vx,
           ECBList_P v'52 (Vptr (v'61, Int.zero)) v'40 v'21 vg v'36 /\
           EcbMod.join vg vx v'35/\
           EcbMod.join vv  (EcbMod.sig (v'61, Int.zero) (absmutexsem msgls xx, nil)) vx/\
           ECBList_P x8 Vnull v'42 v'37  vv  v'36.
Proof.
  introv Hsom Hlen Hi Harr Hcur Hrl Htcb Hre Hep.
  lets Hex : ecblist_p_decompose Hlen Hep.


  mytac.
  destruct H2.
  rewrite H2 in Hsom; tryfalse.
  rewrite H2 in Hsom ; inverts Hsom.
  unfolds in Hre.
  assert (forall n, (0 <= n < 8)%nat  ->  nth_val n v'58 = Some (Vint32 ($ 0))).
  intros.
  lets Hex : n07_arr_len_ex H3  Harr Hrl.
  destruct Hex as (vh & Hnth & Hneq).
  assert (V$0 = V$0) as Hasrt by auto.
  lets Hres : Hre H3 Hnth Hasrt.
  destruct Hres as (Hrs1 & Hrs2).
  destruct Hrs1 as (Hrs11 & Hrs22).
  rewrite Int.and_zero_l in Hrs11.
  assert (vh = $ 0) .
  apply Hrs11.
  auto.
  subst vh.
  auto.
  simpl in H0.
  destruct H0 as (qid & Heq & Heb & Hex).
  destruct Hex as (absmq & mqls' & v' & Hv & Hej & Hmt & Hlp).
  destruct absmq.
  destruct e; tryfalse.
  usimpl Hv.
  inverts Heq.
  destruct Hmt as (Hm1 & Hm2). (* & Hm3 & Hm4). *)  
  assert (w = nil \/ w <> nil) by tauto.
  destruct H0 as [Hnil | Hnnil].
  Focus 2.
  unfolds in Hcur.
  unfolds in Htcb.
  destruct Htcb as (Htcb1&Htcb2&Htcb3&Htcb4).
  lets Hj : ecbmod_joinsig_get Hej.
  lets Hea : qwaitset_notnil_ex Hnnil.
  destruct Hea as (tid & Hin).
  assert ( EcbMod.get x1 (v'61, Int.zero) = Some (absmutexsem i o, w) /\ In tid w) by (split; auto).
  lets Has : EcbMod.join_get_get_r H1 H0.
  assert ( EcbMod.get v'35 (v'61, Int.zero) = Some (absmutexsem i o, w) /\ In tid w) by (split; auto).
  destruct Htcb4 as (Htc & Htc').
  lets Hjj : Htc H4.
  destruct Hjj as (prio & m0 & n & Htcg).
  unfolds in Heb.
  destruct Heb as (Heb1 & Heb2 &  Heb3).
  unfolds  in Heb1.
  unfolds in Heb2.
  destruct Heb2 as (Hebbb & Heb2 & Heb4 & Hebb).
  lets Hebs : Hebb Htcg.
  lets Hbb : prioinq_exists Hebs.
  destruct Hbb as (n0 & Hnn & Hnth).
  lets Hfs : H3 Hnn.
  tryfalse.
  subst w.
  exists i o.
  split.
  assert (EcbMod.get x1 (v'61, Int.zero) = Some (absmutexsem i o, nil)).
  eapply ecbmod_joinsig_get; eauto.
  eapply EcbMod.join_get_get_r;eauto.
  do 3 eexists; splits; eauto.
  eapply ecbmod_joinsig_sig.
  eauto.
Qed.

Lemma R_Prio_Tbl_P_hold_for_del :
  forall v'29 v'38 v'50 v'37 v'40 x x0 v'66,
    nth_val (Z.to_nat (Int.unsigned x)) v'29 =Some (Vptr v'50)-> 
    EcbMod.join x0 (EcbMod.sig (v'66, Int.zero) (absmutexsem x None, nil)) v'37 ->
    0<= Int.unsigned x <64 -> 
    length v'29 = 64%nat ->  
    R_PrioTbl_P v'29 v'38 v'50 ->
    RH_TCBList_ECBList_P v'37 v'38 v'40 -> 
    R_PrioTbl_P (update_nth_val (Z.to_nat (Int.unsigned x)) v'29 Vnull) v'38 v'50.
Proof.
  introv HHH.
  intros.
  unfold R_PrioTbl_P in *.
  assert (Z.to_nat (Int.unsigned x) < length v'29)%nat.
  clear H2 H3.
  rewrite H1.
  mauto.
  split; intros; elim H2; intros.
  apply H8; auto.
  unfold nat_of_Z in *.
  assert (Z.to_nat (Int.unsigned prio) = Z.to_nat (Int.unsigned x) \/ Z.to_nat (Int.unsigned prio) <> Z.to_nat (Int.unsigned x)).
  tauto.
  elim H10; intros.
  rewrite H11 in H6.
  lets xxx: ls_has_nth_val H4.
  mytac.

  erewrite  update_nth in H6.
  inversion H6.
  eauto.
  eapply nth_upd_neq.
  eauto.
  eauto.

  split.
  intros.
  assert (Z.to_nat (Int.unsigned prio) = Z.to_nat (Int.unsigned x) \/ Z.to_nat (Int.unsigned prio) <> Z.to_nat (Int.unsigned x)).
  tauto.
  elim H8; intros.
  Focus 2.
  split.
  elim H6; intros.
  lets fff: H10 H7.
  mytac.

  apply  nth_upd_neqrev.
  auto.
  auto.

  elim H6; intros.
  lets fff: H10 H7.
  mytac.
  auto.
  destruct H3.
  mytac.
  destruct H13.
  assert (EcbMod.get v'37 (v'66, Int.zero) = Some (absmutexsem x None, nil)).
  eapply EcbMod.join_get_r; eauto.
  apply EcbMod.get_a_sig_a.
  go.
  lets aa: H14 H7.
  apply Z2Nat.inj in H9.
  apply unsigned_inj in H9.
  mytac.
  unfold nat_of_Z in H19.
  rewrite H19 in HHH.
  inverts HHH.

  tryfalse.
  int auto.
  int auto.
  lets fffff: H14 H7.
  mytac.
  auto.
  
  elim H6; intros.
  auto.
Qed.
Lemma val_eq_lemma001 :forall x0 v'50,  val_inj (notint (val_inj (val_eq x0 (Vptr v'50)))) = Vint32 Int.zero \/
                                        val_inj (notint (val_inj (val_eq x0 (Vptr v'50)))) = Vnull -> x0= Vptr v'50.
Proof.
  intros.
  destruct x0;
    simpl in H;
    elim H; intros; tryfalse.
  destruct v'50.
  simpl in H0.
  unfold Int.notbool in H0.
  int auto.
  destruct v'50.
  int auto.
  destruct a.
  destruct v'50.
  assert (b = b0 \/ b <> b0).
  tauto.
  elim H1; intros.
  subst b0.
  rewrite peq_true in H0.
  assert ( i = i0 \/ i <> i0) by tauto.
  elim H2; intros.
  subst i0.
  auto.
  rewrite Int.eq_false in H0.
  simpl in H0.
  int auto.
  auto.
  rewrite peq_false in H0.
  int auto.
  auto.
  destruct a.
  destruct v'50.
  assert (b = b0 \/ b <> b0).
  tauto.
  elim H1; intros.
  subst b0.
  rewrite peq_true in H0.
  assert ( i = i0 \/ i <> i0) by tauto.
  elim H2; intros.
  subst i0.
  auto.
  rewrite Int.eq_false in H0.
  simpl in H0.
  int auto.
  auto.
  rewrite peq_false in H0.
  int auto.
  auto.
Qed.


Lemma RL_RTbl_PrioTbl_P_hold_for_del: forall v'29 v'38 v'50 v'37 v'40 x x0 v'66 v'35,
                                        nth_val (Z.to_nat (Int.unsigned x)) v'29 =Some (Vptr v'50)->  EcbMod.join x0
                                                                                                                  (EcbMod.sig (v'66, Int.zero) (absmutexsem x None, nil)) v'37 -> 0<= Int.unsigned x <64 ->  length v'29 = 64%nat ->  R_PrioTbl_P v'29 v'38 v'50 ->  RH_TCBList_ECBList_P v'37 v'38 v'40 ->  RL_RTbl_PrioTbl_P v'35 v'29 v'50->   RL_RTbl_PrioTbl_P v'35
                                                                                                                                                                                                                                                                                                                                                                    (update_nth_val
                                                                                                                                                                                                                                                                                                                                                                       (Z.to_nat (Int.unsigned x )) v'29
                                                                                                                                                                                                                                                                                                                                                                       Vnull) v'50.
Proof.
  introv HHH.
  intros.
  unfold RL_RTbl_PrioTbl_P in *.
  intros.
  assert (Z.to_nat (Int.unsigned p) = Z.to_nat (Int.unsigned x) \/ Z.to_nat (Int.unsigned p) <> Z.to_nat (Int.unsigned x)).
  tauto.
  elim H7; intros.
  Focus 2.
  lets aa: H4 H5 H6.
  mytac.
  eexists.
  splits; eauto.
  
  apply  nth_upd_neqrev.
  auto.
  auto.

  lets bb: H4 H5 H6.
  false.
  mytac.
  unfolds in H3.
  mytac.
  destruct H15.
  destruct H16.
  unfolds in H17.
  unfolds in H2.
  mytac.
  lets fff: H2 H9 H10.
  omega.
  mytac.
  apply Z2Nat.inj in H8.
  apply unsigned_inj in H8.

  subst p.
  2:omega.
  2:omega.
  assert (EcbMod.get v'37 (v'66, Int.zero) = Some (absmutexsem x None, nil)).
  eapply EcbMod.join_get_r; eauto.
  apply EcbMod.get_a_sig_a.
  go.
  rewrite HHH in H9.
  inverts H9.
  tryfalse.
Qed.
Goal forall v'35 v'36 x y , RH_TCBList_ECBList_MUTEX_OWNER v'35 v'36 ->  EcbMod.join x y v'35 ->  RH_TCBList_ECBList_MUTEX_OWNER x v'36.
Proof.
  intros.
  unfolds.
  intros.
  unfolds in H.
  unfold get in *; simpl in *.
  assert (EcbMod.get v'35 eid  = Some (absmutexsem pr (Some (tid, opr)), wls)).
  go.
  lets fff: H H2.
  auto.
Save MOWNER_IN_TCB_join_part_hold.
Lemma ecb_del_prop_RHhold:
  forall v'35 v'36 v'38 x y absmg,
    RH_TCBList_ECBList_P v'35 v'36 v'38 ->
    EcbMod.join x (EcbMod.sig y (absmg, nil))
                v'35 ->  RH_TCBList_ECBList_P x v'36 v'38 .
Proof.
  introv Hrh Hjo.
  unfolds in Hrh.
  destruct Hrh as (Hrh1&Hrh2&Hrh3&Hrh4).
  unfolds.
  splits.
  destruct Hrh1.
  splits.
  intros.
  mytac.
  lets Hg : EcbMod.join_get_get_l Hjo H1.
  eapply H.
  eauto.
  intros.
  assert (eid = y \/ eid <>y) by tauto.
  apply H0 in H1.
  mytac.
  destruct H2.
  subst y.
  apply EcbMod.join_comm in Hjo.
  eapply EcbMod.join_sig_get in Hjo.
  unfold get in *; simpl in *.
  rewrite H1 in Hjo.
  inverts Hjo.
  simpl in H3.
  tryfalse.
  do 3 eexists; split; try eapply ecbmod_get_join_get; eauto.
  destruct Hrh2.
  splits.
  intros.
  mytac.
  lets Hg : EcbMod.join_get_get_l Hjo H1.
  eapply H.
  eauto.
  intros.
  assert (eid = y \/ eid <>y) by tauto.
  apply H0 in H1.
  mytac.
  destruct H2.
  subst y.
  apply EcbMod.join_comm in Hjo.
  eapply EcbMod.join_sig_get in Hjo.
  unfold get in *; simpl in *.
  rewrite H1 in Hjo.
  inverts Hjo.
  simpl in H3.
  tryfalse.
  do 2 eexists; split; try eapply ecbmod_get_join_get; eauto.
  destruct Hrh3.
  splits.
  intros.
  mytac.
  lets Hg : EcbMod.join_get_get_l Hjo H1.
  eapply H.
  eauto.
  intros.
  assert (eid = y \/ eid <>y) by tauto.
  apply H0 in H1.
  mytac.
  destruct H2.
  subst y.
  apply EcbMod.join_comm in Hjo.
  eapply EcbMod.join_sig_get in Hjo.
  unfold get in *; simpl in *.
  rewrite H1 in Hjo.
  inverts Hjo.
  simpl in H3.
  tryfalse.
  do 2 eexists; split; try eapply ecbmod_get_join_get; eauto.
  destruct Hrh4.
  splits.
  intros.
  mytac.
  lets Hg : EcbMod.join_get_get_l Hjo H1.
  eapply H.
  eauto.
  intros.
  assert (eid = y \/ eid <>y) by tauto.
  apply H0 in H1.
  mytac.
  destruct H2.
  subst y.
  apply EcbMod.join_comm in Hjo.
  eapply EcbMod.join_sig_get in Hjo.
  unfold get in *; simpl in *.
  rewrite H1 in Hjo.
  inverts Hjo.
  simpl in H3.
  tryfalse.
  do 3 eexists; split; try eapply ecbmod_get_join_get; eauto.
  mytac.
  eapply  MOWNER_IN_TCB_join_part_hold; eauto.
Qed. 


Lemma ltu_eq_false_ltu':
  forall a b,
    Int.ltu a b = false ->
    Int.eq a b = false ->
    Int.ltu b a = true.
Proof.
  intros.
  int auto.
Qed.


Lemma AOSRdyTblGrp_fold:
  forall s P v'38 v'39,
    s |= GAarray OSRdyTbl (Tarray Int8u ∘OS_RDY_TBL_SIZE) v'38 **
      AOSRdyGrp v'39 ** P ->
    array_type_vallist_match Int8u v'38 /\ length v'38 = ∘OS_RDY_TBL_SIZE ->
    RL_Tbl_Grp_P v'38 v'39 /\ prio_in_tbl ($ OS_IDLE_PRIO) v'38 ->
    s |= AOSRdyTblGrp v'38 v'39 ** P.
Proof.
  intros.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  sep pauto.
Qed.


Lemma mutexpend_TCBNode_P_in_tcb_rdy:
  forall v'51 v'22  xs x9 x8 i9 i8 i6 i5 i4 i3 xx rtbl,
    array_type_vallist_match Int8u rtbl ->
    length rtbl = ∘OS_RDY_TBL_SIZE ->
    TCBNode_P (v'51
                 :: v'22
                 :: x9
                 :: x8
                 :: Vint32 i9
                 :: Vint32 i8
                 :: Vint32 xx
                 :: Vint32 i6
                 :: Vint32 i5
                 :: Vint32 i4 :: Vint32 i3 :: nil)
              rtbl (xx, xs, x8) ->
    i9 = $ 0 ->
    i8 = $ OS_STAT_RDY ->
    xs = rdy.
Proof.
  intros.
  unfolds in H1.
  mytac.
  inverts H1; inverts H4.
  lets F: low_stat_rdy_imp_high H H0 H5 H6.
  apply F.
  rewrite Int.eq_true; auto.
  rewrite Int.eq_true; auto.
Qed.  

(* Lemma absinfer_mutex_pend_ptcb_is_cur:
 *   forall P ecbls tcbls t ct v pr wls eid p' ptcb,
 *     Int.unsigned v <= 65535 ->
 *     EcbMod.get ecbls eid = Some (absmutexsem pr (Some (ptcb, p')), wls) ->
 *     ptcb = ct ->                                                                   
 *     can_change_aop P ->
 *     absinfer
 *       (<|| mutexpend (Vptr eid :: Vint32 v :: nil) ||> **
 *            HECBList ecbls **
 *            HTCBList tcbls **
 *            HTime t **
 *            HCurTCB ct ** P)
 *       (<|| END (Some (Vint32 (Int.repr OS_ERR_MUTEX_DEADLOCK)))||> **
 *            HECBList ecbls **
 *            HTCBList tcbls **
 *            HTime t **
 *            HCurTCB ct ** P).
 *   infer_solver 10%nat.
 * Qed. *)


(* Lemma absinfer_mutex_pend_ptcb_is_idle:
 *   forall P ecbls tcbls t ct v pr wls eid p' ptcb st msg,
 *     Int.unsigned v <= 65535 ->
 *     EcbMod.get ecbls eid = Some (absmutexsem pr (Some (ptcb, p')), wls) ->
 *     TcbMod.get tcbls ptcb = Some (Int.repr OS_IDLE_PRIO,st,msg) ->
 *     can_change_aop P ->
 *     absinfer
 *       (<|| mutexpend (Vptr eid :: Vint32 v :: nil) ||> **
 *            HECBList ecbls **
 *            HTCBList tcbls **
 *            HTime t **
 *            HCurTCB ct ** P)
 *       (<|| END (Some (Vint32 (Int.repr OS_ERR_MUTEX_IDLE)))||> **
 *            HECBList ecbls **
 *            HTCBList tcbls **
 *            HTime t **
 *            HCurTCB ct ** P).
 *   infer_solver 13%nat.
 * Qed. *)


(* Lemma absinfer_mutex_pend_ptcb_is_not_rdy:
 *   forall P ecbls tcbls t ct v pr wls eid p' ptcb st msg ptcb_prio cur_prio m,
 *     Int.unsigned v <= 65535 ->
 *     EcbMod.get ecbls eid = Some (absmutexsem pr (Some (ptcb, p')), wls) ->
 *     TcbMod.get tcbls ptcb = Some (ptcb_prio ,st,msg) ->
 *     TcbMod.get tcbls ct = Some (cur_prio,rdy,m) ->
 *     ~ st = rdy -> 
 *     can_change_aop P ->
 *     absinfer
 *       (<|| mutexpend (Vptr eid :: Vint32 v :: nil) ||> **
 *            HECBList ecbls **
 *            HTCBList tcbls **
 *            HTime t **
 *            HCurTCB ct ** P)
 *       (<|| END (Some (Vint32 (Int.repr OS_ERR_NEST)))||> **
 *            HECBList ecbls **
 *            HTCBList tcbls **
 *            HTime t **
 *            HCurTCB ct ** P).
 *   infer_solver 9%nat.
 * Qed. *)




(* Lemma absinfer_mutex_pend_cur_prio_eql_mprio:
 *   forall P ecbls tcbls t ct v pr wls eid p' ptcb st msg cur_prio,
 *     Int.unsigned v <= 65535 ->
 *     EcbMod.get ecbls eid = Some (absmutexsem pr (Some (ptcb, p')), wls) ->
 *     TcbMod.get tcbls ct = Some (cur_prio ,st,msg) ->
 *     p' = cur_prio -> 
 *     can_change_aop P ->
 *     absinfer
 *       (<|| mutexpend (Vptr eid :: Vint32 v :: nil) ||> **
 *            HECBList ecbls **
 *            HTCBList tcbls **
 *            HTime t **
 *            HCurTCB ct ** P)
 *       (<|| END (Some (Vint32 (Int.repr OS_ERR_MUTEX_DEADLOCK)))||> **
 *            HECBList ecbls **
 *            HTCBList tcbls **
 *            HTime t **
 *            HCurTCB ct ** P).
 *   infer_solver 12%nat.
 * Qed. *)



(* Lemma absinfer_mutex_pend_pip_is_not_hold:
 *   forall P ecbls tcbls t ct v eid,
 *     Int.unsigned v <= 65535 ->
 *     can_change_aop P ->
 *     absinfer
 *       (<|| mutexpend (Vptr eid :: Vint32 v :: nil) ||> **
 *            HECBList ecbls **
 *            HTCBList tcbls **
 *            HTime t **
 *            HCurTCB ct ** P)
 *       (<|| END (Some (Vint32 (Int.repr OS_ERR_MUTEXPR_NOT_HOLDER)))||> **
 *            HECBList ecbls **
 *            HTCBList tcbls **
 *            HTime t **
 *            HCurTCB ct ** P).
 *   infer_solver 8%nat.
 * Qed. *)


Lemma seporI2 : forall p q p', (p' ==> p) -> p' ==> p \\// q.
  intros.
  apply seporI.
  sep auto.
Qed.
Lemma seporI2' : forall p q p', (p' ==> p) -> p' ==> q \\// p.
  intros.
  apply seporI'.
  sep auto.
Qed.





Lemma post_valinjlemma1 : forall v0 v'51,  val_inj (notint (val_inj (val_eq v0 (Vptr v'51)))) = Vint32 Int.zero \/
                                           val_inj (notint (val_inj (val_eq v0 (Vptr v'51)))) = Vnull -> v0 = (Vptr v'51).
Proof.
  intros.
  elim H; intros.
  destruct v0; simpl in H0; tryfalse.
  destruct v'51; simpl in H0.
  int auto.
  destruct a; destruct v'51.
  assert (b = b0 \/ b <> b0) by tauto.
  elim H1; intros.
  subst b.
  rewrite peq_true in *.
  assert (i=i0 \/ i <> i0).
  tauto.
  elim H2; intros.
  subst i.
  auto.
  rewrite Int.eq_false in H0.
  simpl in H0.
  clear -H0.
  false.
  int auto.

  rewrite peq_false in H0.
  simpl in H0.
  false; clear -H0; int auto.
  auto.
  destruct v0; int auto.
  simpl in H0.
  destruct v'51.
  int auto.
  
  destruct a.
  destruct v'51.
  simpl in H0.
  destruct (peq b b0);
    tryfalse.
  destruct (Int.eq i i0); tryfalse.
Qed.



(* absinfer lemma *)
(* Lemma absinfer_mutexpost_return_exwt_succ: 
 *   forall P mqls x wl tls t ct st m m' st'  t' p' pr op, 
 *     can_change_aop P ->  
 *     EcbMod.get mqls x = Some (absmutexsem pr (Some (ct, op)) ,wl) ->
 *     ~ wl=nil ->
 *     GetHWait tls wl t' ->
 *     TcbMod.get tls ct= Some (pr,  st,  m)  ->
 *     TcbMod.get tls t' = Some (p', st', m') ->
 *     absinfer
 *       ( <|| mutexpost (Vptr x :: nil) ||>  ** 
 *             HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P) 
 *       (<|| isched;;END (Some (Vint32 (Int.repr NO_ERR))) ||>  ** HECBList (EcbMod.set mqls x (absmutexsem pr (Some (t', p')), (remove_tid t' wl))) ** HTCBList (TcbMod.set (TcbMod.set tls ct (op, st, m)) t' (p', rdy, (Vptr x)) ) ** HTime t ** HCurTCB ct ** P).
 * Proof.
 *   try match goal with
 *         | |- context [ <|| ?x _ ||> ] => unfold x
 *       end; intros.
 *   infer_branch 6%nat.
 * 
 *   multi_step_handler. 
 *   infer_branch 0%nat.
 *   tri_infer_prim.
 *   infer_part2.
 *   eapply ruleLib.eqdomO_trans.
 *   2: eapply abst_get_set_eqdom; [ absdata_solver | idtac ].
 *   eqdomO_solver.
 *   unfolds.
 *   unfolds.
 *   intros.
 *   split; intros.
 *   rewrite <- tcbset_indom_eq.
 *   rewrite <- tcbset_indom_eq.
 *   auto.
 *   unfolds.
 *   eauto.
 *   assert (ct = t' \/ ct <> t') by tauto.
 *   elim H7; intros.
 *   subst t'.
 *   unfolds.
 *   rewrite TcbMod.set_a_get_a.
 *   eauto.
 *   go.
 *   unfolds.
 *   rewrite TcbMod.set_a_get_a'.
 *   eauto.
 *   go.
 * 
 *   rewrite <- tcbset_indom_eq in H6.
 *   rewrite <- tcbset_indom_eq in H6.
 *   auto.
 *   unfolds.
 *   eauto.
 * 
 *   rewrite <- tcbset_indom_eq.
 *   unfolds.
 *   eauto.
 *   unfolds; eauto.
 * Qed. *)

(* Lemma absinfer_mutexpost_noreturn_exwt_succ: 
 *   forall P mqls x wl tls t ct st m m' st'  t' p' pr op p, 
 *     can_change_aop P ->  
 *     EcbMod.get mqls x = Some (absmutexsem pr (Some (ct, op)) ,wl) ->
 *     Int.eq p pr = false /\
 *     ~ wl=nil ->
 *     GetHWait tls wl t' ->
 *     TcbMod.get tls ct= Some (p,  st,  m)  ->
 *     TcbMod.get tls t' = Some (p', st', m') ->
 *     absinfer
 *       ( <|| mutexpost (Vptr x :: nil) ||>  ** 
 *             HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P) 
 *       (<|| isched;;END (Some (Vint32 (Int.repr NO_ERR))) ||>  ** HECBList (EcbMod.set mqls x (absmutexsem pr (Some (t', p')), (remove_tid t' wl))) ** HTCBList (TcbMod.set  tls  t' (p', rdy, (Vptr x)) ) ** HTime t ** HCurTCB ct ** P).
 * Proof.
 *   try match goal with
 *         | |- context [ <|| ?x _ ||> ] => unfold x
 *       end; intros.
 *   infer_branch 6%nat.
 * 
 *   multi_step_handler. 
 *   infer_branch 1%nat.
 *   tri_infer_prim.
 *   infer_part2.
 * Qed. *)
Goal forall x y, Int.eq x y = true  -> x=y.
intros.
int auto.
apply unsigned_inj.
auto.
Save inteqeq.


Lemma Astruct_PV_neq1 :
  forall s p1 p2 v2  h vl P,
    s |= Astruct p1 OS_TCB (h::vl) ** PV p2 @ Int8u |-> v2 ** P ->
    p1 <> p2.
Proof.
  intros.
  intro; substs.
  destruct_s s.
  simpl in H.
  destruct p2.
  mytac.
  simpl in H3; mytac.
  clear H7.
  clear H9.
  simpl in H8.
  unfold mapstoval in *.
  mytac.
  assert((b, Int.unsigned i2) <> (b, Int.unsigned i2)).
  eapply ptomval_nnil_neq with (x1:=x5) (x2:=x1); eauto.
  eapply type_encode_nnil; eauto.
  unfolds.
  intro.
  unfolds in H.
  destruct H; mytac; tryfalse.
  destruct H; mytac; tryfalse.

  eapply type_encode_nnil; eauto.
  unfolds.
  intro.
  unfolds in H.
  destruct H; mytac; tryfalse.
  destruct H; mytac; tryfalse.
  instantiate (1:= merge x5 x1).
  clear - H5 H0 H1.

  apply map_join_merge.
  join auto.
  (* unfolds; intros.
   * rewrite merge_sem.
   * pose proof H5 a; pose proof H0 a; pose proof H1 a.
   * destruct (MemMod.get x5 a);
   *   destruct (MemMod.get x6 a);
   *   destruct (MemMod.get x0 a);
   *   destruct (MemMod.get x a);
   *   destruct (MemMod.get m a);
   *   destruct (MemMod.get x1 a);
   *   destruct (MemMod.get x4 a);
   *   tryfalse; substs; auto. *)

  tryfalse.
Qed.

(* Lemma absinfer_mutexpost_exwt_no_return_prio_succ :
 *   forall qls qls' qid p p' p''  t t' pt wl tls tls' st st' m m' tm P,
 *     can_change_aop P ->
 *     EcbMod.get qls qid = Some (absmutexsem p (Some (t, pt)), wl) ->
 *     wl <> nil ->
 *     GetHWait tls wl t' ->
 *     Int.eq p'' p = false ->
 *     TcbMod.get tls t = Some (p'', st, m) ->
 *     TcbMod.get tls t' = Some (p', st', m') ->
 *     tls' = TcbMod.set tls t' (p', rdy, Vptr qid) ->
 *     qls' = EcbMod.set qls qid (absmutexsem p (Some (t', p')), remove_tid t' wl) ->
 *     absinfer
 *       (<|| mutexpost (Vptr qid :: nil) ||> **
 *            HECBList qls ** HTCBList tls ** HTime tm ** HCurTCB t ** P)
 *       (<|| isched;; END Some (V$NO_ERR) ||> **
 *            HECBList qls' ** HTCBList tls' ** HTime tm ** HCurTCB t ** P).
 * Proof.
 *   intros.
 *   unfold mutexpost.
 *   infer_branch 6%nat.
 *   eapply absinfer_trans.
 *   eapply absinfer_seq with (q:=(HECBList qls' ** HTCBList tls' ** HTime tm ** HCurTCB t ** P)); can_change_aop_solver.
 *   2: eapply absinfer_seq_end; can_change_aop_solver.
 *   substs.
 *   infer_solver 1%nat.
 * Qed. *)

Lemma zh_asdf1 :
  forall
    (v'79 : int32)
    (H137 : Int.unsigned v'79 <= 255)
    (H125 : Int.eq (v'79&ᵢInt.not ($ OS_STAT_MUTEX)) ($ OS_STAT_RDY) = true),
    $ OS_STAT_RDY = v'79&ᵢInt.not ($ OS_STAT_MUTEX).
Proof.
  intros.
  unfold Int.eq in H125.
  destruct (zeq (Int.unsigned (v'79&ᵢInt.not ($ OS_STAT_MUTEX)))
                (Int.unsigned ($ OS_STAT_RDY))) eqn : eq1; tryfalse.
  clear eq1.
  unfold Int.and in *.
  rewrite Int.unsigned_repr in e.
  rewrite Int.unsigned_repr in e.
  rewrite e; auto.
  unfold OS_STAT_RDY.
  unfold Int.max_unsigned.
  simpl.
  omega.
  unfold Int.not.
  unfold Int.xor.
  rewrite Int.unsigned_repr.
  rewrite Int.unsigned_repr.
  unfold OS_STAT_MUTEX.
  rewrite Int.unsigned_mone.
  simpl.
  unfold Int.max_unsigned; simpl.
  apply Z_land_range.
  unfold Int.max_unsigned; simpl.
  split.
  pose proof Int.unsigned_range v'79; destruct H; auto.
  omega.
  unfold Int.max_unsigned; simpl.
  omega.
  unfold OS_STAT_MUTEX; unfold Int.max_unsigned; simpl.
  omega.
  unfold OS_STAT_MUTEX.
  rewrite Int.unsigned_mone.
  simpl.
  unfold Int.max_unsigned; simpl.
  rewrite Int.unsigned_repr.
  simpl; omega.
  unfold Int.max_unsigned; simpl.
  omega.
Qed.

Lemma nth_val'_length :
  forall l n,
    nth_val' n l <> Vundef ->
    (n < length l)%nat.
Proof.
  inductions l; intros.
  destruct n; simpl in H; tryfalse.
  destruct n.
  simpl; omega.
  simpl in H.
  simpl.
  eapply IHl in H.
  omega.
Qed.

Lemma zh_asdf:
  forall (v'54 : int32)
         (v'62 : int32)
         (v'64 : int32),
    val_inj
      (bool_and (val_inj (notint (val_inj (Some (Vint32 Int.zero)))))
                (val_inj
                   (bool_or
                      (val_inj
                         (if Int.ltu ((v'62<<ᵢ$ 3)+ᵢv'64) (v'54>>ᵢ$ 8)
                          then Some (Vint32 Int.one)
                          else Some (Vint32 Int.zero)))
                      (val_inj
                         (if Int.eq ((v'62<<ᵢ$ 3)+ᵢv'64) (v'54>>ᵢ$ 8)
                          then Some (Vint32 Int.one)
                          else Some (Vint32 Int.zero)))))) = 
    Vint32 Int.zero \/
    val_inj
      (bool_and (val_inj (notint (val_inj (Some (Vint32 Int.zero)))))
                (val_inj
                   (bool_or
                      (val_inj
                         (if Int.ltu ((v'62<<ᵢ$ 3)+ᵢv'64) (v'54>>ᵢ$ 8)
                          then Some (Vint32 Int.one)
                          else Some (Vint32 Int.zero)))
                      (val_inj
                         (if Int.eq ((v'62<<ᵢ$ 3)+ᵢv'64) (v'54>>ᵢ$ 8)
                          then Some (Vint32 Int.one)
                          else Some (Vint32 Int.zero)))))) = Vnull
    ->                                                            
    Int.ltu (v'54>>ᵢ$ 8) ((v'62<<ᵢ$ 3)+ᵢv'64) = true.
Proof.
  intros.

  
  simpl in H.
  rewrite int_ltu_zero_notbool_zero_true in H.
  destruct (Int.ltu ((v'62<<ᵢ$ 3)+ᵢv'64) (v'54>>ᵢ$ 8)) eqn : eq1;
    destruct (Int.eq ((v'62<<ᵢ$ 3)+ᵢv'64) (v'54>>ᵢ$ 8)) eqn : eq2; simpl in H;
    try (rewrite int_ltu_zero_one_true in H);
    try (rewrite int_ltu_zero_zero_false in H);
    try (rewrite int_ltu_zero_notbool_zero_true in H); simpl in H; destruct H;
    tryfalse.

  eapply ltu_false_eq_false_ltu_true; eauto.
Qed.

Lemma GetHWait_In :
  forall w v'61 v'86,
    GetHWait v'61 w (v'86, Int.zero) -> In (v'86, Int.zero) w.
Proof.
  intros.
  unfolds in H; mytac; auto.
Qed.

Lemma tcb_join_join_merge :
  forall m1 m2 m3 m4 m5,
    TcbMod.join m1 m2 m3 ->
    TcbMod.join m4 m5 m2 ->
    TcbMod.join m4 (TcbMod.merge m1 m5) m3.
Proof.
  intros.
  unfolds; intros.
  pose proof H a; pose proof H0 a.
  rewrite TcbMod.merge_sem.
  destruct(TcbMod.get m1 a);
    destruct(TcbMod.get m2 a);
    destruct(TcbMod.get m3 a);
    destruct(TcbMod.get m4 a);
    destruct(TcbMod.get m5 a);
    tryfalse; substs ;auto.
Qed.




Lemma or_OS_MUTEX_AVAILABLE_le_65535 :
  forall x, Int.unsigned x <= 65535 ->
            Int.unsigned (Int.or x ($ OS_MUTEX_AVAILABLE)) <= 65535.
Proof.
  apply int_auxxx.
Qed.

(* Lemma absinfer_mutexpost_nowt_no_return_prio_succ :
 *   forall qls qls' qid p p' p'' t tm tls st m P,
 *     can_change_aop P -> 
 *     EcbMod.get qls qid = Some (absmutexsem p (Some (t, p')), nil) ->
 *     TcbMod.get tls t = Some (p'', st, m) ->
 *     Int.eq p'' p = false ->
 *     qls' = EcbMod.set qls qid (absmutexsem p None, nil) ->
 *     absinfer
 *       (<|| mutexpost (Vptr qid :: nil) ||> **
 *            HECBList qls ** HTCBList tls ** HTime tm ** HCurTCB t ** P)
 *       (<|| END Some (V$NO_ERR) ||> **
 *            HECBList qls' ** HTCBList tls ** HTime tm ** HCurTCB t ** P).
 * Proof.
 *   intros.
 *   substs.
 *   infer_solver 5%nat.
 * Qed. *)

Lemma isptr_zh :
  forall x, isptr x ->
            match x with
              | Vundef => false
              | Vnull => true
              | Vint32 _ => false
              | Vptr _ => true
            end = true.
Proof.
  intros.
  unfolds in H; destruct H.
  substs; auto.
  destruct H; substs; auto.
Qed.

Lemma evsllseg_aux:
  forall l1 s a b l2 P,
    s |= evsllseg a b l1 l2 ** P ->
    (a = b /\ l1 = nil \/ get_last_ptr l1 = Some b) /\ length l1 = length l2.
Proof.
  inductions l1.
  intros.
  simpl in H.
  mytac.
  left.
  auto.
  auto.
  intros.
  unfold evsllseg in H.
  fold evsllseg in H.
  destruct l3.
  simpl in H.
  mytac; tryfalse.
  destruct a.
  sep normal in H.
  sep destruct H.
  sep lift 3%nat in H.
  lets Hxax: IHl1 H.
  mytac.
  2: simpl; auto.
  destruct H0.
  mytac.
  right.
  unfolds.
  simpl.
  sep split in H.
  auto.
  right.
  unfolds.
  simpl.
  destruct l1.
  unfolds in H0.
  simpl in H0.
  unfolds in H0.
  unfold nth_val in H0.
  tryfalse.
  simpl.
  auto.
Qed.
Lemma mutex_rh_tcblist_ecblist_p_hold: forall v'34 v'35 v'37 v w m  y, EcbMod.get v'34 v = Some (absmutexsem m y, w) ->RH_TCBList_ECBList_P v'34 v'35 v'37 ->
                                                                       RH_TCBList_ECBList_P
                                                                         (EcbMod.set v'34 v (absmutexsem m None, w)) v'35 v'37.
Proof.
  intros.
  unfolds in H0.
  mytac.
  unfolds.
  mytac; [clear -H H0| clear -H H1; rename H1 into H0|clear -H H2; rename H2 into H0| clear -H H3; rename H3 into H0]; unfolds; unfolds in H0; mytac; intros; unfold get in *; simpl in *;
  try solve [eapply H0;
              mytac; eauto;
              assert ( eid = v \/ eid <> v)  as aa by tauto; destruct aa;[subst;
                                                                           rewrite EcbMod.set_a_get_a in e;[
                                                                             inversion e|
                                                                             apply CltEnvMod.beq_refl] 
                                                                         |
                                                                         rewrite EcbMod.set_a_get_a' in e;[
                                                                             eauto|
                                                                             apply tidspec.neq_beq_false];
                                                                         auto]]
  ;try solve[
         lets aaa : H1 H2;
         mytac;
         assert ( eid = v \/ eid <> v)  as aa by tauto; destruct aa;[subst eid;rewrite H in H3;inversion H3|
                                                                     rewrite EcbMod.set_a_get_a';[
                                                                         rewrite H3;
                                                                         eauto|
                                                                         apply tidspec.neq_beq_false;
                                                                           auto]]
       ]
  .

  assert (eid = v \/ eid <> v) as aa by tauto; destruct aa.
  subst eid.
  
  rewrite EcbMod.set_a_get_a in H3.
  mytac.
  inverts H3.
  eapply H0.
  mytac; eauto.
  go.
  rewrite EcbMod.set_a_get_a' in H3.
  lets fff: H0 H3.
  auto.
  go.

  assert (eid = v \/ eid <> v) as aa by tauto; destruct aa.
  subst eid.
  lets fff: H1 H3.
  mytac.
  rewrite EcbMod.set_a_get_a.
  repeat tri_exists_and_solver1.
  rewrite H in H4.
  inverts H4.
  auto.
  go.
  rewrite EcbMod.set_a_get_a'.
  eapply H1; eauto.
  go.

  unfolds.
  intros.

  assert (eid = v \/ eid <> v) as aa by tauto; destruct aa.
  rewrite EcbMod.set_a_get_a in H3.
  inverts H3.
  subst eid.
  go.
  
  rewrite EcbMod.set_a_get_a' in H3.
  unfolds in H2.
  eapply H2; eauto.
  go.
Qed.



Lemma intlemmaf: forall i,  val_inj
                              (notint
                                 (val_inj
                                    (if Int.eq i ($ 0)
                                     then Some (Vint32 Int.one)
                                     else Some (Vint32 Int.zero)))) <> 
                            Vint32 Int.zero -> i <> Int.zero.
Proof.
  intros.
  remember (Int.eq i ($ 0)).
  destruct b.
  simpl in H.
  change (Int.notbool Int.one) with Int.zero in H.
  tryfalse.
  intro.
  rewrite H0 in Heqb.
  clear -Heqb.
  int auto.
Qed.



Lemma return_rh_ctcb :forall v'52 v'39 a b c, RH_CurTCB (v'52, Int.zero) (TcbMod.set v'39 (v'52, Int.zero) (a, b, c)).
Proof.
  intros.
  unfold RH_CurTCB in *.
  rewrite TcbMod.set_a_get_a.
  eauto.
  go.
Qed.

Lemma rg1 :  forall x2 x6 ,  0 <= Int.unsigned x2 < 64->
                             x6 = $ Int.unsigned x2&ᵢ$ 7 ->
                             0<= Int.unsigned x6 < 8.
Proof.
  intros.
  subst x6.
  mauto.
Qed.

Lemma rg2 :  forall x2 x7 ,  0 <= Int.unsigned x2 < 64->
                             x7 = Int.shru ($ Int.unsigned x2) ($ 3) ->
                             0<= Int.unsigned x7 < 8.
Proof.
  intros.
  subst x7.
  mauto.
Qed.


Lemma something_in_not_nil : forall (T:Type) (y: @list T), y<>nil -> exists x, In x y.
Proof.
  intros T y.
  elim y.
  intro; tryfalse.
  intros.
  exists a.
  simpl.
  left; auto.
Qed.

Lemma post_exwt_succ_pre_mutex'
: forall (v'36 v'13 : vallist) (v'12 : int32) 
         (v'32 : block) (v'15 : int32) (v'24 : val) 
         (v'35 v'0 : val) (v'8 : tid) (v'9 v'11 : EcbMod.map)
         x  (x1 : waitset)
         (v'6 v'10 : EcbMod.map) (v'38 v'69 v'39 : int32) 
         (v'58 : block) (a : priority)
         (c : msg) (v'62 v'7 : TcbMod.map) 
         (vhold : addrval) y,
    v'12 = Int.zero ->
    R_PrioTbl_P v'36 v'7 vhold ->
    RL_Tbl_Grp_P v'13 (Vint32 v'12) ->
    R_ECB_ETbl_P (v'32, Int.zero)
                 (V$OS_EVENT_TYPE_MUTEX
                   :: Vint32 v'12
                   :: Vint32 v'15 :: v'24 :: v'35 :: v'0 :: nil,
                  v'13) v'7 ->
    RH_TCBList_ECBList_P v'11 v'7 v'8 ->
    EcbMod.join v'9 v'10 v'11 ->
    EcbMod.joinsig (v'32, Int.zero) (absmutexsem x y , x1) v'6 v'10 ->
    x1 = nil
.
Proof.
  intros.
  unfolds in H2.
  destruct H2 as (H2 & H2' & _).
  destruct H2 as (_ & _ & _ & H2).
  destruct H2' as (_ & _ & _ & H2').
  unfolds in H2.
  unfolds in H2'.
  

  unfolds in H3.
  unfolds in H1.
  unfolds in H0.
  destruct H3 as (_ & _ & _ & H3).
  unfolds in H3.
  destruct H3 as (H3 & H3').

  lets Hg : EcbMod.join_joinsig_get H4 H5.
  clear H4 H5.
  assert ( x1 = nil \/ x1 <> nil) by tauto.
  destruct H4; intros; auto.

  idtac.
  apply something_in_not_nil in H4.
  inversion H4.
  assert (EcbMod.get v'11 (v'32, Int.zero) = Some (absmutexsem x y, x1) /\ In x0 x1) by tauto.
  lets aadf : H3 H6.
  mytac.
  lets bbdf : H2' H7.
  destruct bbdf.
  unfolds in H.
  do 3 destruct H.
  destruct H as (Ha & Hb & Hc & Hd& He).
  cut ( 0<=(∘(Int.unsigned x7)) <8)%nat.
  intro.
  assert (V$0 = V$0) by auto.
  lets adfafd : H1 H Hd H14.
  destruct adfafd.
  destruct H13.
  destruct H14.
  cut ( $ 0&ᵢ($ 1<<ᵢ$ Z.of_nat ∘(Int.unsigned x7)) = $ 0).
  intro.
  apply H15 in H13.
  subst x8.

  lets rg : rg1 Ha Hb.
  clear -He rg.
  false.
  gen He.
  mauto.

  lets rg : rg2 Ha Hc.
  clear -rg.
  mauto.

  lets rg : rg2 Ha Hc.
  clear -rg.
  mauto.
Qed.

(* Lemma absinfer_mutexpost_return_nowt_succ: 
 *   forall P mqls x tls t ct st m pr op, 
 *     can_change_aop P ->  
 *     EcbMod.get mqls x = Some (absmutexsem pr (Some (ct, op)) ,nil) ->
 *     TcbMod.get tls ct= Some (pr,  st,  m)  ->
 *     Int.eq pr op = false -> 
 *     absinfer
 *       ( <|| mutexpost (Vptr x :: nil) ||>  ** 
 *             HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P) 
 *       (<|| END (Some (Vint32 (Int.repr NO_ERR))) ||>  ** HECBList (EcbMod.set mqls x (absmutexsem pr None, nil)) ** HTCBList (TcbMod.set tls ct (op, st, m))  ** HTime t ** HCurTCB ct ** P).
 * Proof.
 *   intros.
 *   infer_solver 4%nat.
 * Qed. *)

Lemma intcbnotvhold :forall ptbl tcbls vhold tcbptr p s m,  R_PrioTbl_P ptbl tcbls vhold -> TcbMod.get tcbls tcbptr = Some (p, s, m) -> tcbptr <> vhold.
Proof.
  intros.
  unfolds in H.
  mytac.
  lets fff: H1 H0.
  mytac.
  auto.
Qed.

Lemma valinjlemma1: forall a b,  val_inj
                                   (if Int.eq a b
                                    then Some (Vint32 Int.one)
                                    else Some (Vint32 Int.zero)) <> Vint32 Int.zero -> a= b.
Proof.
  intros.
  remember (Int.eq a b).
  destruct b0.
  change (if true then a=b else a<>b).
  rewrite Heqb0.
  apply Int.eq_spec.
  simpl in H.
  tryfalse.
Qed.
Lemma val_inj2 : forall x x6,  val_inj
                                 (if Int.eq x6 x
                                  then Some (Vint32 Int.one)
                                  else Some (Vint32 Int.zero)) <> Vint32 Int.zero -> x6 = x.
Proof.
  intros.
  remember (Int.eq x6 x).
  destruct b; tryfalse.
  
  int auto.
  apply unsigned_inj.
  auto.
  simpl in H.
  tryfalse.
Qed.
