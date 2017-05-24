Require Import include_frm.
Require Import int_auto.
Require Import sep_auto.
Require Import math_sol.
Require Import os_code_defs.
Require Import os_inv.
Require Import pure_lib.
Require Import cancel_abs.
Require Import ucos_bitsmap.

Set Implicit Arguments.

Open Scope int_scope.
Open Scope code_scope.
Open Scope Z_scope.

Lemma val_eq_vundef:
  forall i0,
    val_inj
      (if Int.eq i0 ($ OS_EVENT_TYPE_Q)
       then Some (Vint32 Int.one)
       else Some (Vint32 Int.zero)) <> Vundef.
Proof.
  intros.
  destruct (Int.eq i0 ($ OS_EVENT_TYPE_Q)).
  simpl.
  introv Hf.
  inverts Hf.
  simpl.
  introv Hf.
  inverts Hf.
Qed.

Lemma val_eq_vundef':
  forall i0,
    val_inj
      (notint
         (val_inj
            (if Int.eq i0 ($ OS_EVENT_TYPE_Q)
             then Some (Vint32 Int.one)
             else Some (Vint32 Int.zero)))) <> Vundef.
Proof.
  intros.
  destruct (Int.eq i0 ($ OS_EVENT_TYPE_Q)).
  simpl.
  introv Hf.
  inverts Hf.
  simpl.
  introv Hf.
  inverts Hf.
Qed.


Lemma val_inj_eq_q:
  forall i0,
    val_inj
      (notint
         (val_inj
            (if Int.eq i0 ($ OS_EVENT_TYPE_Q)
             then Some (Vint32 Int.one)
             else Some (Vint32 Int.zero)))) = Vint32 Int.zero \/
    val_inj
      (notint
         (val_inj
            (if Int.eq i0 ($ OS_EVENT_TYPE_Q)
             then Some (Vint32 Int.one)
             else Some (Vint32 Int.zero)))) = Vnull ->
    i0 = ($ OS_EVENT_TYPE_Q).
Proof.
  intros.
  destruct H.
  remember (Int.eq i0 ($ OS_EVENT_TYPE_Q)) as Hr.
  destruct Hr.
  pose (Int.eq_spec i0 ($ OS_EVENT_TYPE_Q)) as Hp.
  rewrite <-HeqHr in Hp.
  auto.
  simpl in H.
  unfold Int.notbool in H.
  rewrite Int.eq_true in H.
  tryfalse.
  destruct ( Int.eq i0 ($ OS_EVENT_TYPE_Q)).
  simpl in H.
  unfold Int.notbool in H.
  rewrite Int.eq_false in H.
  tryfalse.
  intros Hf.
  tryfalse.
  simpl in H.
  unfold Int.notbool in H.
  rewrite Int.eq_true in H.
  tryfalse.
Qed.

(*
Lemma ecbmod_get_sig_set:
  forall v x y,
    EcbMod.get v x = None -> 
    EcbMod.joinsig x y v (EcbMod.set v x y).
Proof.
  intros.
  unfold EcbMod.joinsig.
  unfold EcbMod.join.
  intro.
  ecbspec_dec v x a.
  rewrite H; auto.
  destruct (EcbMod.get v a); auto.
Qed.
*)



Lemma math_prop_l1: 
  val_inj
    (notint
       (val_inj
          (if Int.eq ($ OS_EVENT_TYPE_Q) ($ OS_EVENT_TYPE_Q)
           then Some (Vint32 Int.one)
                             else Some (Vint32 Int.zero)))) = Vint32 Int.zero.
Proof.
  int auto.
Qed.

Lemma length8_ex:
  forall v'40 :vallist,
    length v'40 = ∘OS_EVENT_TBL_SIZE ->
    exists v1 v2 v3 v4 v5 v6 v7 v8,
      v'40 = v1::v2::v3::v4::v5::v6::v7::v8::nil.
Proof.
  introv Hlen.
  try do 8  (destruct v'40; simpl in Hlen; tryfalse).
  do 8 eexists; eauto.
  assert (length v'40 = 0)%nat.
  unfold Pos.to_nat in Hlen.
  simpl in Hlen.
  inverts Hlen.
  auto.
  assert (v'40 = nil).
  destruct v'40.
  auto.
  simpl in H; tryfalse.
  subst.
  eauto.
Qed.

Lemma n07_arr_len_ex:
  forall n v'40,
    (0 <= n < 8)%nat ->
    array_type_vallist_match Int8u v'40 ->
    length v'40 = ∘OS_EVENT_TBL_SIZE ->
    exists v, nth_val n v'40 = Some (Vint32 v) /\ Int.unsigned v <= 255.
Proof.
  introv Hn Hqr Hlen.
  apply length8_ex in Hlen.
  simp join.
  simpl in Hqr.
  simp join.
  repeat
    match goal  with
      | x : val |- _  => destruct x; simp join; tryfalse
    end.

  repeat match goal with
           | H : context [if _ then _ else _] |- _ =>
             apply int_true_le255 in H
         end.
  assert (n = 0 \/ n =1 \/ n=2 \/ n=3 \/ n=4 \/ n=5\/ n=6 \/ n = 7) %nat by omega.
  do 8 solve_disj.
Qed.

Lemma prio_inq:
  forall vv n v'40,
    (0 <= n < 8)%nat ->
    Int.ltu ($ 0) vv = true -> 
    Int.unsigned vv <= 255 ->
    nth_val n v'40 = Some (Vint32 vv) ->
    exists prio, 
      PrioWaitInQ prio v'40.
Proof.
  introv Hn Hun Hnth Hvneq.
  unfold PrioWaitInQ.
  lets Hex : ltu_ex_and Hun Hnth.
  destruct Hex as (xx & Heee & Hd).
  lets Hk :  math_des88 Hn Hd.
  destruct Hk as (yy & Hy1 & Hy2 & Hy3).
  eexists.
  eexists xx.
  exists (Int.repr (Z.of_nat n)).
  eexists vv.
  splits; eauto.
  clear -Hvneq Hn.
  int auto.
  rewrite nat_of_Z_of_nat .
  auto.
Qed.


Lemma  ecblistp_length_eq_1 :
  forall x y l1 l2 t1 t2,
    ECBList_P  x y l1 l2 t1 t2 -> length l1 = length l2.
Proof.
  intros.
  gen l1 x y t1 t2.
  inductions l2; intros; simpl.
  destruct l1.
  simpl; auto.
  simpl in H.
  simp join; tryfalse.
  destruct l1.
  simpl in H; simp join; tryfalse.
  simpl.
  simpl in H.
  simp join.
  destruct e.
  simp join.
  apply IHl2 in H3.
  omega.
Qed.

Lemma ecblistp_length_eq : forall x l1 z l2 l1' z' l2' t1 t2,
                             ECBList_P  x Vnull (l1 ++ (z::nil) ++ l2) (l1' ++ (z'::nil) ++ l2') t1 t2-> length l1 = length l1' -> length l2 = length l2'.
Proof.
  intros.
  rewrite list_prop1 in *.
  rewrite list_prop1 in *.

  apply ecblistp_length_eq_1 in H.
  rewrite app_length in H.
  rewrite app_length in H.
  simpl in H.
  omega.
Qed.


Lemma ECBList_last_val :
  forall x y v1 v2 v3 v4,
    v1 <> nil ->
    ECBList_P x y v1 v2 v3 v4 ->
    exists a b, last v1 (nil,nil) = (a,b)
                /\  nth_val 5 a = Some y.
Proof.
  intros.
  gen x y v2 v3 v4.
  inductions v1.
  tryfalse.
  intros.
  simpl in H0.
  simp join.
  destruct v2.
  tryfalse.
  destruct a.
  simp join.
  assert (v1 = nil \/ v1 <> nil) by tauto.
  destruct H5.
  subst.
  simpl.
  do 2 eexists.
  splits; eauto.
  unfolds in H0.
  simpl in H4.
  simp  join.
  auto.
  lets Hre : IHv1 H5; eauto.
  simpl.
  destruct v1.
  tryfalse.
  apply Hre in H4.
  simp join.
  do 2 eexists.
  splits; eauto.
Qed.

Require Import ifun_spec.

Lemma get_eidls_inlist: forall x ls,
                          In x (get_eidls x ls).
Proof.
  intros.
  unfold get_eidls.
  simpl.
  left.
  auto.
Qed.



Inductive listsub (T : Type) : list T -> list T -> Prop :=
| listsub1:forall x,  listsub nil x
| listsubrec: forall x y lsx lsy,  x = y ->
                                   listsub lsx lsy ->
                                   listsub (x :: lsx) (y :: lsy).

(* in mathlib.v *)
Lemma list_sub_prop1 :
  forall v1 (z:EventCtr) v1',   listsub (v1++(z::nil)) (v1 ++(z::v1')).
Proof.
  inductions v1.
  simpl.
  intros.
  constructors; auto.
  constructors.
  simpl.
  intros.
  constructors.
  auto.
  eapply IHv1.
Qed.


Lemma list_sub_prop2 :
  forall x y, listsub x y -> listsub (get_eid_ecbls x) (get_eid_ecbls y).
Proof.
  intros.
  inductions H.
  simpl.
  constructors.
  unfold get_eid_ecbls; fold get_eid_ecbls.
  destruct x.
  destruct y.
  inverts H.
  constructors.
  auto.
  auto.
Qed.

Require Import List.
Lemma removelast_prop:
  forall (t: Type) (a : t)  x , x <> nil -> removelast (a::x) = a :: removelast x.
Proof.
  inductions x.
  simpl.
  intros.
  tryfalse.
  intros.
  simpl.
  destruct x.
  auto.
  simpl in IHx.
  destruct x.
  auto.
  auto.
Qed.


Lemma list_sub_prop3 :
  forall (x : val) y z ,  listsub y z ->  In x y -> In x z.
Proof.
  intros.
  inductions H gen x.
  simpl in H0; tryfalse.
  simpl in H1.
  simpl.
  destruct H1; subst.
  left ; auto.
  right.
  eauto.
Qed.

(* in mathlib.v *)
Lemma  list_sub_prop4 :
  forall (x :vallist)  y, listsub x y -> listsub (removelast x) (removelast y).
  intros.
  inductions H.
  simpl.
  constructors.
  subst.
  simpl.
  destruct lsx; destruct lsy; try constructors; eauto.
  inverts H0.
Qed.


Lemma nil_get_eid_nil:
  forall x,  x <> nil -> get_eid_ecbls x <> nil.
Proof.
  inductions x.
  intros; tryfalse.
  intros.
  simpl.
  destruct a.
  intros Hf.
  tryfalse.
Qed.


Lemma in_get_eidls :
  forall v1  y x  z vl',
    In y (get_eidls x (v1 ++ (z :: nil)))
    ->In y (get_eidls x (v1 ++ (z :: vl'))).
Proof.
  unfold get_eidls in *.
  intros.
  eapply list_sub_prop3.
  eapply listsubrec.
  eauto.
  eapply list_sub_prop4.
  eapply list_sub_prop2.
  eapply list_sub_prop1.
  auto.
Qed.

(* in mathlib.v *)
Lemma get_remove_exchange:
  forall x,   removelast (get_eid_ecbls x) = get_eid_ecbls (removelast x).
  inductions x.
  simpl.
  auto.
  unfold get_eid_ecbls; fold get_eid_ecbls.
  destruct a.
  assert (x = nil \/ x <> nil) by tauto.
  destruct H.
  subst x.
  simpl.
  auto.
  assert (x <> nil) as Hasrt by auto.
  eapply removelast_prop with (a:= (v, v0)) in H.
  rewrite H.
  apply nil_get_eid_nil in Hasrt.
  lets Hzz :  removelast_prop (nth_val' 5 v) Hasrt.
  rewrite Hzz.
  unfold get_eid_ecbls; fold get_eid_ecbls.
  rewrite IHx.
  auto.
Qed.



Lemma  qwaitset_notnil_ex:
  forall qwaitset : waitset ,
    qwaitset <> nil ->
    exists tid, In tid qwaitset.
Proof.
  inductions qwaitset.
  intros; tryfalse.
  intros.
  eexists.
  simpl.
  left; eauto.
Qed.


Lemma prioinq_exists:
  forall prio v'58,
    PrioWaitInQ prio v'58 ->
    exists n,
      (0 <= n < 8)%nat /\ nth_val n v'58 <> Some (V$0).
Proof.
  intros.
  unfolds in H.
  simp join.
  assert (x1 = $0 \/ x1 <> $0) by tauto.
  destruct H0.
  subst x1.
  rewrite Int.and_zero_l in H3.
  assert (0<=prio<64) by omega.
  false.
  clear -H0 H3.
  mauto_dbg.
  destruct H0; subst.
  inverts H3.

  repeat (destruct H;[ subst;  inverts H3|idtac]).
  subst prio; inverts H3.

  exists ( ∘(Int.unsigned (Int.shru ($ prio) ($ 3)))).
  split.
  Focus 2.
  rewrite H2; intro Hf.
  inverts Hf.
  tryfalse.

  assert (0<=prio<64) by omega.
  apply prio_destruct in H1.
  mauto.
Qed.



Lemma ecbjoin_sig_join :
		forall x x1 v'35 x0 v'61 v3 i5,
            	               EcbMod.join x x1 v'35 ->
        	                   EcbMod.join x0
                                       (EcbMod.sig (v'61, Int.zero) (absmsgq v3 i5, nil))
                                       x1 ->  exists y, EcbMod.join x0 x y /\ EcbMod.join y
                                                                                          (EcbMod.sig (v'61, Int.zero) (absmsgq v3 i5, nil)) v'35.
Proof.
  intros.
  set ( EcbMod.join_assoc_r H0 H).
  simp join.
  exists x2.
  split; auto.
  apply EcbMod.join_comm in H1.
  auto.
Qed.

Require Import os_ucos_h.
Lemma qacc_dl_vl_match:
  forall vl, true = dl_vl_match ((dcons pevent  (Tptr OS_EVENT) ) dnil) (rev vl) -> (exists v,vl = (Vptr v)::nil\/ vl =Vnull::nil) .
Proof.
  intros.
  simpl in H.
  remember (rev vl) as X.
  destruct X;tryfalse.
  destruct v;tryfalse.
  destruct X;tryfalse.
  assert (length (Vnull :: nil) = length (rev vl)).
  rewrite HeqX;auto.
  simpl in H0.
  destruct vl;simpl in H0;tryfalse.
  rewrite app_length in H0.
  simpl in H0.
  assert (length (rev vl) = 0%nat).
  omega.
  rewrite  rev_length in H1.
  destruct vl;simpl in H1;tryfalse.
  simpl in HeqX.
  rewrite <- HeqX.
  exists (xH,Int.zero).
  right;auto.

  destruct X;tryfalse.
  assert (length (Vptr a :: nil) = length (rev vl)).
  rewrite HeqX;auto.
  simpl in H0.
  destruct vl;simpl in H0;tryfalse.
  rewrite app_length in H0.
  simpl in H0.
  assert (length (rev vl) = 0%nat).
  omega.
  rewrite  rev_length in H1.
  destruct vl;simpl in H1;tryfalse.
  simpl in HeqX.
  rewrite <- HeqX.
  exists a.
  left;auto.
Qed.


Lemma ecb_get_set_join_join:
  forall ml a b ml1 ml2 ml1' b',
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

Open Scope code_scope.

Lemma array_type_vallist_match_int8u_update_hold:
  forall v'38 v'69 v'40 v'13,
    length v'13 = ∘OS_EVENT_TBL_SIZE ->
    Int.unsigned v'38 <= 7 ->
    Int.unsigned v'69 <= 255 ->
    Int.unsigned v'40 <= 128 ->
    array_type_vallist_match Int8u v'13 ->
    array_type_vallist_match Int8u
                             (update_nth_val (Z.to_nat (Int.unsigned v'38)) v'13
                                             (Vint32 (v'69&ᵢInt.not v'40))).
Proof.
  intros.
  rewrite array_type_vallist_match_is_all_elem_p.
  apply all_elem_hold_for_upd.
  rewrite array_type_vallist_match_is_all_elem_p in H3.
  auto.

  simpl.
  unfold Byte.max_unsigned.
  unfold Byte.modulus.
  simpl.
  remember not_and_p.
  cut (Int.unsigned (v'69&ᵢInt.not v'40) <=? 255 = true).
  intro.
  rewrite H4.
  reflexivity.
  rewrite <- Zle_is_le_bool.
  apply not_and_p; auto.
Qed.

Lemma array_type_vallist_match_int8u_update_hold_255:
  forall v'38 v'69 v'40 v'13,
    length v'13 = ∘OS_EVENT_TBL_SIZE ->
    Int.unsigned v'38 <= 7 ->
    Int.unsigned v'69 <= 255 ->
    Int.unsigned v'40 <= 255 ->
    array_type_vallist_match Int8u v'13 ->
    array_type_vallist_match Int8u
                             (update_nth_val (Z.to_nat (Int.unsigned v'38)) v'13
                                             (Vint32 (v'69&ᵢInt.not v'40))).
Proof.
  intros.
  rewrite array_type_vallist_match_is_all_elem_p.
  apply all_elem_hold_for_upd.
  rewrite array_type_vallist_match_is_all_elem_p in H3.
  auto.

  simpl.
  unfold Byte.max_unsigned.
  unfold Byte.modulus.
  simpl.
  remember not_and_p.
  cut (Int.unsigned (v'69&ᵢInt.not v'40) <=? 255 = true).
  intro.
  rewrite H4.
  reflexivity.

  rewrite <- Zle_is_le_bool.
  apply not_and_p'; auto.
Qed.


Lemma  array_type_vallist_match_int8u_update_hold':
  forall v'37 ( v'38 v'40 : int32) (v'13 : list val),
    length v'37 = nat_of_Z OS_RDY_TBL_SIZE ->
    array_type_vallist_match Tint8 v'37 ->
    length v'13 = nat_of_Z OS_EVENT_TBL_SIZE ->
    Int.unsigned v'38 <= 7 ->
    Int.unsigned v'40 <= 128 ->
    array_type_vallist_match Tint8 v'13 ->
    array_type_vallist_match Tint8
                             (update_nth_val (Z.to_nat (Int.unsigned v'38)) v'13
                                             (val_inj
                                                (or (nth_val' (Z.to_nat (Int.unsigned v'38)) v'37) (Vint32 v'40)))).
Proof.
  intros.
  rewrite  array_type_vallist_match_is_all_elem_p.
  rewrite array_type_vallist_match_is_all_elem_p in *.
  apply all_elem_hold_for_upd.
  auto.
  simpl.
  assert (Z.to_nat (Int.unsigned v'38) < 8)%nat.
  handle_z2n_lt_nat.
  rewrite <- array_type_vallist_match_is_all_elem_p in H0.
  remember (nthval'_has_value v'37 H0 H H5).
  inversion e.
  inversion H6.
  rewrite H7.
  simpl.
  simpl in H8.

  symmetry in H8.
  bfunction_invert.
  rewrite <- Zle_is_le_bool in H9.

  idtac.
  rewrite if_eq_true_cond_is_true.
  rewrite <- Zle_is_le_bool.
  apply  int_unsigned_or_prop; auto.
Qed.

Lemma length_n_change:
  forall v'38 v'37 v'40,
    length v'37 = nat_of_Z OS_RDY_TBL_SIZE ->
    Int.unsigned v'38 <= 7 ->
    length
      (update_nth_val (Z.to_nat (Int.unsigned v'38)) v'37
                      (val_inj
                         (or (nth_val' (Z.to_nat (Int.unsigned v'38)) v'37) (Vint32 v'40)))) =
    nat_of_Z OS_RDY_TBL_SIZE.
Proof.
  intros.
  rewrite <- H.
  apply update_nth_val_len_eq.
Qed.


Lemma math_le_xyz:
  forall sin out start size,
    start = $ 4 ->
    Int.unsigned size <= OS_MAX_Q_SIZE ->
    Int.ltu out start = false ->
    Int.modu (out-ᵢstart) ($ 4) = $ 0 ->
    Int.ltu sin start = false ->
    Int.modu (sin-ᵢstart) ($ 4) = $ 0 ->
    (∘(Int.unsigned (Int.divu (sin-ᵢstart) ($ 4))) <  ∘(Int.unsigned size))%nat ->
    (∘(Int.unsigned (Int.divu (out-ᵢ$ 4) ($ 4))) <  ∘(Int.unsigned ($ Int.unsigned size)))%nat ->
    ∘(Int.unsigned (Int.divu ((out+ᵢ$ 4)-ᵢstart) ($ 4))) = ∘(Int.unsigned size) ->
    Int.unsigned (Int.divu (sin-ᵢstart) ($ 4)) <= Int.unsigned (Int.divu (out-ᵢstart) ($ 4))/\
    (S ∘(Int.unsigned (Int.divu (out-ᵢstart) ($ 4))) =  ∘(Int.unsigned size))%nat  /\
    ∘(Int.unsigned (Int.divu (out-ᵢstart) ($ 4))) =
    (Z.to_nat ((Int.unsigned out - Int.unsigned start) / 4)).
Proof.
  intros.
  rewrite H in *.
  apply (int_minus4_mod4 H1) in H2.
  apply (int_minus4_mod4 H3) in H4.
  copy H2.
  copy H4.
  rewrite Zminus_mod in H9, H8.
  rewrite Z_mod_same_full in H9, H8.
  rewrite <- Zminus_0_l_reverse in H9, H8.
  rewrite <- Zmod_div_mod in H9;[ idtac| omega.. | try (apply Zdivide_intro with 1; auto)].
  rewrite <- Zmod_div_mod in H8;[ idtac| omega.. | try (apply Zdivide_intro with 1; auto)].

  unfold nat_of_Z in *.
  unfold Int.ltu in H1, H3.
  bfunc_invert' H3.
  bfunc_invert' H1.
  ur_rewriter_in g0.
  ur_rewriter_in g.

  unfold Int.divu, Int.sub, Int.add in *.
  repeat (ur_rewriter_in H5).
  unfold OS_MAX_Q_SIZE in H0.
  repeat ur_rewriter.
  rewrite <- Z2Nat.inj_lt in H5.
  set (Z.lt_le_trans _ _ _ H5 H0).

  Focus 2.
  apply Z.div_le_lower_bound; omega.
  Focus 2.
  intrange size omega.

  rewrite (Z.mul_lt_mono_pos_r 4) in l; [idtac | omega].
  rewrite (Z.add_lt_mono_r _ _ 4) in l.
  assert ((Int.unsigned sin - 4) / 4 * 4 + 4 >= Int.unsigned sin - 4).
  apply (@a_div_b_multi_b_plus_b_ge_a (Int.unsigned sin -4) 4); omega.
  revs' H10.
  set (Z.le_lt_trans _ _ _ H11 l).
  simpl in l0.
  repeat (ur_rewriter_in H6).
  rewrite <- Z2Nat.inj_lt in H6.
  set (Z.lt_le_trans _ _ _ H6 H0).

  Focus 2.
  apply Z.div_le_lower_bound; omega.
  Focus 2.
  intrange size omega.

  rewrite (Z.mul_lt_mono_pos_r 4) in l1; [idtac | omega].
  rewrite (Z.add_lt_mono_r _ _ 4) in l1.
  assert ((Int.unsigned out - 4) / 4 * 4 + 4 >= Int.unsigned out - 4).
  apply (@a_div_b_multi_b_plus_b_ge_a (Int.unsigned out -4) 4); omega.
  revs' H12.
  set (Z.le_lt_trans _ _ _ H13 l1).
  simpl in l2.

  repeat (ur_rewriter_in H7).

  rewrite Z2Nat.inj_iff in H7.

  Focus 2.
  apply Z.div_le_lower_bound; omega.
  Focus 2.
  intrange size omega.


  (* proof start *)
  split.
  rewrite <- H7 in H5.
  apply Zlt_le_succ in H5.
  unfold Z.succ in H5.
  assert (Int.unsigned out + 4 -4 = Int.unsigned out -4 + 1*4) by omega.
  rewrite H14 in H5.
  rewrite Z_div_plus_full in H5.
  omega.
  omega.

  split.
  rewrite <- H7.
  assert (Int.unsigned out + 4 -4 = Int.unsigned out -4 + 1*4) by omega.
  rewrite H14.
  rewrite  Z_div_plus_full.
  rewrite <- Z2Nat.inj_succ.
  auto.
  revs.
  apply Z_div_ge0.
  omega.
  omega.
  omega.

  auto.
Qed.


Lemma vallist_seg_eqnil :
  forall n vl,
    vallist_seg n n vl = nil.
Proof.
  inductions n.
  intros.
  unfolds.
  simpl.
  auto.
  intros.
  unfolds.
  simpl.
  destruct vl; auto.
  eapply IHn.
Qed.



Lemma vallist_seg_Sn :
  forall n vl,
    (S n <= length vl)%nat ->
    vallist_seg n (S n) vl =  nth_val' n vl :: nil.
Proof.
  inductions n.
  intros; unfolds; simpl.
  destruct vl.
  simpl in H; omega.
  auto.
  intros.
  unfolds.
  destruct vl.
  simpl.
  simpl in H.
  omega.
  simpl in H.
  simpl.
  eapply IHn.
  omega.
Qed.


Lemma vallistseg_n_m_split:
  forall n m vl vl',
    (n >= m) %nat ->
    (n <= length vl)%nat ->
    vallist_seg m n vl = nth_val' m vl :: vl' ->
    vallist_seg (S m) n vl = vl'.
Proof.
  inductions n; inductions m; intros; simpl in *; 
  destruct vl; unfold vallist_seg in *; simpl in *; tryfalse; auto.
  inverts H1.
  auto.
  eapply IHn.
  omega.
  omega.
  auto.
Qed.


Lemma vallist_seg_prop:
  forall m size vl,
    (m < size)%nat ->
    (size <= length vl) %nat ->
    vallist_seg m size vl <> nil.
Proof.
  inductions m; inductions size; simpl; unfold vallist_seg in *; simpl in *; intuition (try omega).
  destruct vl.
  simpl in H0 ; omega.
  inverts H1.
  destruct vl.
  simpl in H0.
  omega.
  simpl in H0.
  assert (m < size)%nat by omega.
  assert (size <= length vl)%nat by omega.
  eapply IHm; eauto.
Qed.

Lemma  vallist_seg_n_m_split' :
  forall  m size vl vl' ,
    (m < size)%nat ->
    (size <= length vl) %nat ->
    vallist_seg m size vl  =  nth_val' m vl :: vl' ->
    vallist_seg (S m) size vl  = vl'.
Proof.
  inductions m; inductions size; intros; simpl in *;  
  destruct vl; unfold vallist_seg in *; simpl in *; tryfalse; try omega; auto.
  inverts H1.
  auto.
  eapply IHm; eauto; try omega.
Qed.


Lemma vallist_seg_ltunm_prop:
  forall  m size vl vl' x,
    (m < size)%nat ->
    (size <= length vl) %nat ->
    vallist_seg m size vl ++ x  =  nth_val' m vl :: vl' ->
    vallist_seg (S m) size vl ++ x  = vl'.
Proof.
  intros.
  lets Hex : vallist_seg_prop H H0.
  lets Hez : list_append_split Hex H1.
  simp join.
  lets Hsaa : vallist_seg_n_m_split' H H0 H2.
  rewrite Hsaa.
  auto.
Qed.


Lemma math_xyz_prop2 :
  forall out start sin hsize,
    start = $ 4 ->
    Int.ltu out start = false ->
    Int.ltu sin start = false ->
    Int.modu (out-ᵢstart) ($ 4) = $ 0 ->
    Int.modu (sin-ᵢstart) ($ 4) = $ 0 ->
    (∘(Int.unsigned (Int.divu (sin-ᵢstart) ($ 4))) <
     ∘(Int.unsigned ($ Int.unsigned hsize)))%nat ->
    (∘(Int.unsigned (Int.divu (out-ᵢstart) ($ 4))) <
     ∘(Int.unsigned ($ Int.unsigned hsize)))%nat ->
    Int.unsigned ($ Int.unsigned hsize) <= OS_MAX_Q_SIZE ->
    Int.unsigned (Int.divu (sin-ᵢstart) ($ 4)) >=
    Int.unsigned (Int.divu ((out+ᵢ$ 4)-ᵢstart) ($ 4)) ->
    Int.unsigned (Int.divu (sin-ᵢstart) ($ 4)) >=
    Int.unsigned (Int.divu (out-ᵢstart) ($ 4))/\
    (S ∘(Int.unsigned (Int.divu (out-ᵢstart) ($ 4))) =
     ∘(Int.unsigned (Int.divu ((out+ᵢ$ 4)-ᵢstart) ($ 4))))%nat  /\
    ∘(Int.unsigned (Int.divu (out-ᵢstart) ($ 4))) =
    (Z.to_nat ((Int.unsigned out - Int.unsigned start) / 4)).
Proof.
  intros.
  repeat rewrite Int.repr_unsigned in *.

  rewrite H in *.
  apply (int_minus4_mod4 H0) in H2.
  apply (int_minus4_mod4 H1) in H3.
  copy H2.
  copy H3.
  rewrite Zminus_mod in H9, H8.
  rewrite Z_mod_same_full in H9, H8.
  rewrite <- Zminus_0_l_reverse in H9, H8.
  rewrite <- Zmod_div_mod in H9;[ idtac| omega.. | try (apply Zdivide_intro with 1; auto)].
  rewrite <- Zmod_div_mod in H8;[ idtac| omega.. | try (apply Zdivide_intro with 1; auto)].

  unfold nat_of_Z in *.
  unfold Int.ltu in H1, H0.
  bfunc_invert' H0.
  bfunc_invert' H1.
  ur_rewriter_in g0.
  ur_rewriter_in g.

  unfold Int.divu, Int.sub, Int.add in *.
  repeat (ur_rewriter_in H5).
  repeat (ur_rewriter_in H4).



  unfold OS_MAX_Q_SIZE in H6.
  rewrite <- Z2Nat.inj_lt in H5, H4.
  set (Z.lt_le_trans _ _ _ H5 H6).
  set (Z.lt_le_trans _ _ _ H4 H6).


  rewrite (Z.mul_lt_mono_pos_r 4) in l; [idtac | omega].
  rewrite (Z.add_lt_mono_r _ _ 4) in l.
  assert ((Int.unsigned out - 4) / 4 * 4 + 4 >= Int.unsigned out - 4).
  apply (@a_div_b_multi_b_plus_b_ge_a (Int.unsigned out -4) 4); omega.
  revs' H10.
  set (Z.le_lt_trans _ _ _ H11 l).
  simpl in l1.

  rewrite (Z.mul_lt_mono_pos_r 4) in l0; [idtac | omega].
  rewrite (Z.add_lt_mono_r _ _ 4) in l0.
  assert ((Int.unsigned sin - 4) / 4 * 4 + 4 >= Int.unsigned sin - 4).
  apply (@a_div_b_multi_b_plus_b_ge_a (Int.unsigned sin -4) 4); omega.
  revs' H12.
  set (Z.le_lt_trans _ _ _ H13 l0).
  simpl in l2.
  repeat ur_rewriter.

  Focus 2.
  apply Z.div_le_lower_bound; omega.
  Focus 2.
  intrange hsize omega.
  Focus 2.
  apply Z.div_le_lower_bound; omega.
  Focus 2.
  intrange hsize omega.

  repeat (ur_rewriter_in H7).

  (* proof start *)
  split.
  assert (Int.unsigned out +4 -4  =Int.unsigned out) by omega.
  assert (Int.unsigned out -4 = Int.unsigned out + -(1) * 4) by omega.
  rewrite H15.
  rewrite H14 in H7.
  rewrite Z_div_plus_full.
  omega.
  omega.

  split.
  rewrite <- Z2Nat.inj_succ.
  assert (Int.unsigned out +4 -4 = Int.unsigned out -4 + 1*4) by omega.
  rewrite H14.
  rewrite Z_div_plus_full.
  unfold Z.succ.
  auto.
  omega.
  revs.
  apply Z_div_ge0.
  omega.
  omega.
  auto.
Qed.


Lemma math_xyz_prop3 :
  forall out start sin hsize,
    start = $ 4 -> 
    Int.ltu out start = false ->
    Int.ltu sin start = false ->
    Int.modu (out-ᵢstart) ($ 4) = $ 0 ->
    Int.modu (sin-ᵢstart) ($ 4) = $ 0 ->
    (∘(Int.unsigned (Int.divu (sin-ᵢstart) ($ 4))) <
     ∘(Int.unsigned ($ Int.unsigned hsize)))%nat ->
    (∘(Int.unsigned (Int.divu (out-ᵢstart) ($ 4))) <
     ∘(Int.unsigned ($ Int.unsigned hsize)))%nat ->
    Int.unsigned ($ Int.unsigned hsize) <= OS_MAX_Q_SIZE ->
    Int.unsigned (Int.divu (sin-ᵢstart) ($ 4)) <
    Int.unsigned (Int.divu ((out+ᵢ$ 4)-ᵢstart) ($ 4)) ->
    (Int.unsigned (Int.divu (sin-ᵢstart) ($ 4)) <
     Int.unsigned (Int.divu (out-ᵢstart) ($ 4)) \/
     Int.unsigned (Int.divu (sin-ᵢstart) ($ 4)) =
     Int.unsigned (Int.divu (out-ᵢstart) ($ 4)))/\
    (S ∘(Int.unsigned (Int.divu (out-ᵢstart) ($ 4))) =
     ∘(Int.unsigned (Int.divu ((out+ᵢ$ 4)-ᵢstart) ($ 4))))%nat  /\
    ∘(Int.unsigned (Int.divu (out-ᵢstart) ($ 4))) =
    (Z.to_nat ((Int.unsigned out - Int.unsigned start) / 4)).
Proof.
  intros.
  rewrite H in *.
  repeat rewrite Int.repr_unsigned in *.

  apply (int_minus4_mod4 H0) in H2.
  apply (int_minus4_mod4 H1) in H3.
  copy H2.
  copy H3.
  rewrite Zminus_mod in H9, H8.
  rewrite Z_mod_same_full in H9, H8.
  rewrite <- Zminus_0_l_reverse in H9, H8.
  rewrite <- Zmod_div_mod in H9;[ idtac| omega.. | try (apply Zdivide_intro with 1; auto)].
  rewrite <- Zmod_div_mod in H8;[ idtac| omega.. | try (apply Zdivide_intro with 1; auto)].

  unfold nat_of_Z in *.
  unfold Int.ltu in H1, H0.
  bfunc_invert' H0.
  bfunc_invert' H1.
  ur_rewriter_in g0.
  ur_rewriter_in g.

  unfold Int.divu, Int.sub, Int.add in *.
  repeat (ur_rewriter_in H5).
  repeat (ur_rewriter_in H4).



  unfold OS_MAX_Q_SIZE in H6.
  rewrite <- Z2Nat.inj_lt in H5, H4.
  set (Z.lt_le_trans _ _ _ H5 H6).
  set (Z.lt_le_trans _ _ _ H4 H6).


  rewrite (Z.mul_lt_mono_pos_r 4) in l; [idtac | omega].
  rewrite (Z.add_lt_mono_r _ _ 4) in l.
  assert ((Int.unsigned out - 4) / 4 * 4 + 4 >= Int.unsigned out - 4).
  apply (@a_div_b_multi_b_plus_b_ge_a (Int.unsigned out -4) 4); omega.
  revs' H10.
  set (Z.le_lt_trans _ _ _ H11 l).
  simpl in l1.

  rewrite (Z.mul_lt_mono_pos_r 4) in l0; [idtac | omega].
  rewrite (Z.add_lt_mono_r _ _ 4) in l0.
  assert ((Int.unsigned sin - 4) / 4 * 4 + 4 >= Int.unsigned sin - 4).
  apply (@a_div_b_multi_b_plus_b_ge_a (Int.unsigned sin -4) 4); omega.
  revs' H12.
  set (Z.le_lt_trans _ _ _ H13 l0).
  simpl in l2.
  repeat ur_rewriter.

  Focus 2.
  apply Z.div_le_lower_bound; omega.
  Focus 2.
  intrange hsize omega.
  Focus 2.
  apply Z.div_le_lower_bound; omega.
  Focus 2.
  intrange hsize omega.

  repeat (ur_rewriter_in H7).

  (* proof start *)
  split.
  assert (Int.unsigned out +4 -4  =Int.unsigned out) by omega.
  assert (Int.unsigned out -4 = Int.unsigned out + -(1) * 4) by omega.
  rewrite H15.
  rewrite H14 in H7.
  rewrite Z_div_plus_full.
  omega.
  omega.

  split.
  rewrite <- Z2Nat.inj_succ.
  assert (Int.unsigned out +4 -4 = Int.unsigned out -4 + 1*4) by omega.
  rewrite H14.
  rewrite Z_div_plus_full.
  unfold Z.succ.
  auto.
  omega.
  revs.
  apply Z_div_ge0.
  omega.
  omega.
  auto.
Qed.

Lemma vallist_destru: 
  forall vl:vallist , 
    length vl = ∘OS_EVENT_TBL_SIZE -> 
    exists v1 v2 v3 v4,
      exists v5 v6 v7 v8,
        vl = v1 ::v2 ::v3 ::v4 ::v5 ::v6::v7::v8 :: nil.
Proof.
  introv H.

  destruct vl;simpl in H; tryfalse.
  inverts H.

  destruct vl;simpl in H1; tryfalse.
  inverts H1.

  destruct vl;simpl in H0; tryfalse.
  inverts H0.

  destruct vl;simpl in H1; tryfalse.
  inverts H1.
  destruct vl;simpl in H0; tryfalse.
  inverts H0.
  destruct vl;simpl in H1; tryfalse.
  inverts H1.

  destruct vl;simpl in H0; tryfalse.
  inverts H0.

  destruct vl;simpl in H1; tryfalse.
  inverts H1.
  destruct vl.
  do 8 eexists; eauto.
  simpl in H0; tryfalse.
Qed.

Lemma prio_in_rtbl_has_tid:
  forall rtbl ptbl p vhold,
    0 <= Int.unsigned p < 64 ->
    RL_RTbl_PrioTbl_P rtbl ptbl vhold->
    prio_in_tbl p rtbl ->
    exists x, nth_val' (Z.to_nat (Int.unsigned p)) ptbl = Vptr x.
Proof.
  intros rtbl ptbl p Hpr.
  intros.
  unfold RL_RTbl_PrioTbl_P in *.
  lets Hf : H0  H H1; auto.
  simp join ;eexists;eauto.
  rewrite -> nth_val'_and_nth_val.
  rewrite H2.
  simpl.
  trivial.
Qed.

Lemma update_nth_aux:
  forall vl x a n,
    update_nth_ectrls (x :: vl) (S n) a =
    x :: (update_nth_ectrls vl n a).
Proof.
  inductions vl.
  simpl.
  auto.
  simpl.
  auto.
Qed.

Lemma  upd_last_prop':
  forall v'40 v'51 v v0 x8,
    v'40 <> nil ->
    v'51 = upd_last_ectrls ((v, v0) :: v'40) x8 ->
    exists vl,  v'51 = ((v,v0) :: vl) /\
                vl = upd_last_ectrls v'40 x8.
Proof.
  introv Hneq Hv .
  unfolds in Hv.
  simpl length in Hv.
  assert (update_nth_ectrls ((v, v0) :: v'40) (S (length v'40 -1) ) x8 =
          (v,v0) :: (update_nth_ectrls v'40 (length v'40-1) x8)).
  apply update_nth_aux.
  assert (S (length v'40 - 1) =  S (length v'40) - 1 )%nat.
  destruct v'40.
  tryfalse.
  simpl.
  omega.
  rewrite H0 in H.
  unfold upd_last_ectrls.
  exists ( update_nth_ectrls v'40 (length v'40 - 1) x8).
  splits; eauto.
  rewrite <- H .
  auto.
Qed.


Lemma R_Prio_NoChange_Prio_hold:
  forall tcb tid st msg prio st' msg',
    R_Prio_No_Dup tcb ->
    TcbMod.get tcb tid = Some (prio, st, msg) ->
    R_Prio_No_Dup (TcbMod.set tcb tid (prio, st', msg')).
Proof.
  introv Hrp Htcb.
  unfolds.
  unfolds in Hrp.
  intros.
  assert (tid' = tid \/ tid' <> tid) by tauto.
  destruct H2.
  subst.
  rewrite TcbMod.set_sem in H1.
  remember (tidspec.beq tid tid) as bool; destruct bool.
  inverts H1.
  symmetry in Heqbool; apply tidspec.beq_true_eq in Heqbool.
  lets Hba :  tcbmod_neq_set_get tid0 tid  (prio', st'0, m')  tcb H.
  unfold get in *. simpl in *.
  rewrite H0 in Hba.
  apply eq_sym in Hba.
  eapply Hrp; eauto.
  symmetry in Heqbool; apply tidspec.beq_false_neq in Heqbool.
  tryfalse.
  lets Hba :  tcbmod_neq_set_get tid' tid (prio, st', msg') tcb H2.
  unfold get in *. simpl in *.
  rewrite H1 in Hba.
  apply eq_sym in Hba.
  assert (tid0 = tid \/ tid0 <> tid) by tauto.
  destruct H3.
  subst.
  rewrite TcbMod.set_sem in H0.
  rewrite tidspec.eq_beq_true in H0; auto.
  inverts H0.
  lets Hdas : Hrp Htcb Hba; eauto.
  lets Hbba :  tcbmod_neq_set_get tid0 tid (prio, st', msg') tcb H3.
  rewrite H0 in Hbba.
  apply eq_sym in  Hbba.
  lets Hrsss : Hrp Hbba Hba; eauto.
Qed.

Lemma prio_rtbl_dec:
  forall x rtbl,
    0 <= Int.unsigned x < 64 ->
    array_type_vallist_match Int8u rtbl ->
    length rtbl = ∘OS_RDY_TBL_SIZE ->
    prio_in_tbl  x rtbl  \/  prio_not_in_tbl  x rtbl.
Proof.
  introv Hr Harr Hlen.
  unfold prio_in_tbl.
  unfold prio_not_in_tbl.
  lets Hex :   int_usigned_tcb_range Hr.
  destruct Hex as (He1 & He2).
  simpl in Hlen.
  unfold Pos.to_nat in Hlen.
  simpl in Hlen.
  assert ( 0<=Z.to_nat(Int.unsigned (Int.shru x ($ 3))) <8)%nat.
  eapply int8_range_nat; auto.
  lets Hes : n07_arr_len_ex H Harr Hlen.
  destruct Hes as (v & Hes & Hneq).
  assert ( 0 <=Int.unsigned v <256).
  clear -Hneq.
  int auto.
  lets Hea: prio_int_disj H0 He1.
  destruct Hea.
  left.
  intros.
  subst.
  unfold nat_of_Z in H4.
  rewrite Hes in H4.
  inverts H4.
  auto.
  branch 2.
  intros.
  subst.
  unfold nat_of_Z in H4.
  rewrite Hes in H4.
  inverts H4; auto.
Qed.


Definition prio_neq_cur tcbls curtid curprio :=
  forall tid prio st m, 
    tid <> curtid -> 
    TcbMod.get tcbls tid = Some (prio, st, m) ->
    prio <> curprio.



Lemma prio_neq_in_tbl:
  forall prio0 prio rtbl grp,
    0 <= Int.unsigned prio0 < 64 ->
    0 <= Int.unsigned prio < 64 ->
    prio0 <> prio ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    prio_in_tbl prio0
                (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                                (Vint32 (grp&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))))) ->
    prio_in_tbl prio0 rtbl.
Proof.
  introv Hr1 Hr2 Hneq Hnth Hprt.
  unfolds in Hprt.
  unfolds.
  intros.
  assert ( ∘(Int.unsigned (Int.shru prio ($ 3))) =  ∘(Int.unsigned (Int.shru prio0 ($ 3))) \/
           ∘(Int.unsigned (Int.shru prio ($ 3))) <>  ∘(Int.unsigned (Int.shru prio0 ($ 3)))) by tauto.
  destruct H2.
  assert (nth_val ∘(Int.unsigned  (Int.shru prio ($ 3)))
                  (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                                  (Vint32 (grp&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))))) = 
          Some (Vint32  (grp&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))))).

  eapply pure_lib.update_nth; eauto.
  lets Hzz : Hprt H3; eauto.
  eapply nat_of_Z_eq; eauto.
  subst.
  rewrite <- H2 in H1.
  rewrite Hnth in H1.
  inverts H1.
  rewrite Int.and_assoc in Hzz.
  erewrite prio_neq_grpeq_prop in Hzz; eauto.
  subst.
  assert (nth_val ∘(Int.unsigned  (Int.shru prio0 ($ 3)))
                  (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                                  (Vint32 (grp&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))))) = 
          Some (Vint32 z)).
  eapply nth_upd_neqrev; eauto.
  lets Hzzz : Hprt  H; eauto.
Qed.

Lemma prio_neq_in_tbl_rev:
  forall prio0 prio rtbl grp,
    0 <= Int.unsigned prio0 < 64 ->
    0 <= Int.unsigned prio < 64 ->
    prio0 <> prio ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    prio_in_tbl prio0 rtbl ->
    prio_in_tbl prio0
                (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                                (Vint32 (grp&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))))) .

Proof.
  introv Hr1 Hr2 Hneq Hnth Hprt.
  unfolds in Hprt.
  unfolds.
  intros.
  assert ( ∘(Int.unsigned (Int.shru prio0 ($ 3))) =  ∘(Int.unsigned (Int.shru prio ($ 3))) \/
           ∘(Int.unsigned (Int.shru prio0 ($ 3))) <>  ∘(Int.unsigned (Int.shru prio ($ 3)))) by tauto.
  destruct H2.
  assert (nth_val ∘(Int.unsigned  (Int.shru prio ($ 3)))
                  (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                                  (Vint32 (grp&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))))) = 
          Some (Vint32  (grp&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))))).
  eapply pure_lib.update_nth; eauto.
  rewrite <- H2 in Hnth.
  lets Hzz : Hprt Hnth; eauto.
  subst.
  rewrite  H2 in H1.
  rewrite H3 in H1.
  inverts H1.
  rewrite Int.and_assoc.
  erewrite prio_neq_grpeq_prop ; eauto.
  subst.
  lets Hss : nth_upd_neq H2 H1.
  eapply Hprt; eauto.
Qed.


Lemma prio_neq_not_in_tbl:
  forall prio0 prio rtbl grp,
    0 <= Int.unsigned prio0 < 64 ->
    0 <= Int.unsigned prio < 64 ->
    prio0 <> prio ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    prio_not_in_tbl prio0
                    (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                                    (Vint32 (grp&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))))) ->
    prio_not_in_tbl prio0 rtbl.
Proof.
  introv Hr1 Hr2 Hneq Hnth Hprt.
  unfolds in Hprt.
  unfolds.
  intros.
  assert ( ∘(Int.unsigned (Int.shru prio ($ 3))) =  ∘(Int.unsigned (Int.shru prio0 ($ 3))) \/
           ∘(Int.unsigned (Int.shru prio ($ 3))) <>  ∘(Int.unsigned (Int.shru prio0 ($ 3)))) by tauto.
  destruct H2.
  assert (nth_val ∘(Int.unsigned  (Int.shru prio ($ 3)))
                  (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                                  (Vint32 (grp&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))))) = 
          Some (Vint32  (grp&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))))).
  eapply pure_lib.update_nth; eauto.
  lets Hzz : Hprt H3; eauto.
  eapply nat_of_Z_eq; eauto.
  subst.
  rewrite <- H2 in H1.
  rewrite Hnth in H1.
  inverts H1.
  rewrite Int.and_assoc in Hzz.
  erewrite prio_neq_grpeq_prop in Hzz; eauto.
  subst.
  assert (nth_val ∘(Int.unsigned  (Int.shru prio0 ($ 3)))
                  (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                                  (Vint32 (grp&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))))) = 
          Some (Vint32 z)).
  eapply nth_upd_neqrev; eauto.
  lets Hzzz : Hprt  H; eauto.
Qed.

Lemma prio_neq_not_in_tbl_rev:
  forall prio0 prio rtbl grp,
    0 <= Int.unsigned prio0 < 64 ->
    0 <= Int.unsigned prio < 64 ->
    prio0 <> prio ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    prio_not_in_tbl prio0 rtbl ->
    prio_not_in_tbl prio0
                    (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                                    (Vint32 (grp&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))))) .

Proof.
  introv Hr1 Hr2 Hneq Hnth Hprt.
  unfolds in Hprt.
  unfolds.
  intros.
  assert ( ∘(Int.unsigned (Int.shru prio0 ($ 3))) =  ∘(Int.unsigned (Int.shru prio ($ 3))) \/
           ∘(Int.unsigned (Int.shru prio0 ($ 3))) <>  ∘(Int.unsigned (Int.shru prio ($ 3)))) by tauto.
  destruct H2.
  assert (nth_val ∘(Int.unsigned  (Int.shru prio ($ 3)))
                  (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                                  (Vint32 (grp&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))))) = 
          Some (Vint32  (grp&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))))).

  eapply pure_lib.update_nth; eauto.
  rewrite <- H2 in Hnth.
  lets Hzz : Hprt Hnth; eauto.
  subst.
  rewrite  H2 in H1.
  rewrite H3 in H1.
  inverts H1.
  rewrite Int.and_assoc.
  erewrite prio_neq_grpeq_prop ; eauto.
  subst.
  lets Hss : nth_upd_neq H2 H1.
  eapply Hprt; eauto.
Qed.

Lemma TcbMod_join_impl_prio_neq_cur_l :
  forall tcbls1 tcbls2 tcbls curtid curprio,
    prio_neq_cur tcbls curtid curprio ->
    TcbMod.join tcbls1 tcbls2 tcbls ->
    prio_neq_cur tcbls1 curtid curprio.
Proof.
  introv Hpr Htcv.
  unfolds in Hpr.
  unfolds.
  intros.
  lets Hlk : TcbMod.join_get_get_l Htcv H0.
  eapply Hpr; eauto.
Qed.

Lemma TcbMod_join_impl_prio_neq_cur_r :
  forall tcbls1 tcbls2 tcbls curtid curprio,
    prio_neq_cur tcbls curtid curprio ->
    TcbMod.join tcbls1 tcbls2 tcbls ->
    prio_neq_cur tcbls2 curtid curprio.
Proof.
  introv Hpr Htc.
  apply TcbMod.join_comm in Htc.
  eapply TcbMod_join_impl_prio_neq_cur_l;eauto.
Qed.

Lemma R_PrioTbl_P_impl_prio_neq_cur :
  forall ptbl tcbls curtid curprio st m vhold,
    0 <= Int.unsigned curprio < 64 ->
    R_PrioTbl_P ptbl tcbls vhold ->
    TcbMod.get tcbls curtid = Some (curprio, st, m) ->
    prio_neq_cur tcbls curtid curprio.
Proof.
  introv Hran Hrp Htc.
  unfolds in Hrp.
  destruct Hrp.
  apply H0 in Htc.
  destruct H0.
  unfolds in H1.
  unfolds.
  intros.
  lets Hrs : H Hran Htc.
  destruct Htc.
  apply Hrs in H5.
  simp join.
  eapply H1; eauto.
Qed.



Lemma idle_in_rtbl_hold:
  forall v'10  p x2 x0 v'16 x7 m i6 i5 i3 i2 i1 i0,
    array_type_vallist_match Int8u v'10 ->
    prio_in_tbl ($ OS_IDLE_PRIO) v'10 ->
    Int.eq p ($ OS_IDLE_PRIO) = false ->
    nth_val' (Z.to_nat (Int.unsigned i2)) v'10 = Vint32 x2 ->
    Int.unsigned x2 <= 255 ->
    RL_TCBblk_P
      (x0
         :: v'16
         :: x7
         :: m
         :: Vint32 i6
         :: Vint32 i5
         :: Vint32 p
         :: Vint32 i3
         :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil) ->
    prio_in_tbl ($ OS_IDLE_PRIO)
                (update_nth_val (Z.to_nat (Int.unsigned i2)) v'10
                                (Vint32 (x2&ᵢInt.not i1))).
Proof.
  intros.
  funfold H4.
  eapply prio_neq_in_tbl_rev;eauto.
  rewrite Int.unsigned_repr.
  unfold OS_IDLE_PRIO.
  unfold OS_LOWEST_PRIO.
  omega.
  unfold OS_IDLE_PRIO.
  unfold OS_LOWEST_PRIO.
  clear.
  int auto.
  lets Hx:Int.eq_spec  x ($ OS_IDLE_PRIO).
  rewrite H1 in Hx.
  auto.
  eapply nth_val'_imp_nth_val_int;eauto.
Qed.


Lemma vallist_seg_prop_eq :
  forall n m vl x ll,
    vallist_seg n m vl = x :: ll ->
    x = nth_val' n vl.
Proof.
  inductions n; inductions m;    destruct vl ; intros;
  try   unfold vallist_seg in *; try simpl in *; tryfalse; auto.
  inverts H;auto.
  eapply IHn; eauto.
Qed.


Lemma math_out_start_eq:
  forall out m,
    Int.ltu out ($ 4) = false ->
    Int.modu (out-ᵢ$4) ($ 4) = $ 0 ->
    (∘(Int.unsigned (Int.divu (out-ᵢ$ 4) ($ 4))) <
     ∘(Int.unsigned ($ Int.unsigned m)))%nat ->
    Int.unsigned ($ Int.unsigned m) <= OS_MAX_Q_SIZE ->
    ∘(Int.unsigned (Int.divu (out-ᵢ$4) ($ 4))) =
    (Z.to_nat ((Int.unsigned out - Int.unsigned ($ 4)) / 4)).
Proof.
  intros.
  unfold Int.ltu in H.


  bfunc_invert' H.
  rewrite Int.unsigned_repr in g.
  int auto.
  split.
  omega.
  intrange out omega.
  split.
  repeat rewrite Int.unsigned_repr.
  cut ((Int.unsigned out -4)/ 4 >=0).
  intros.
  omega.
  apply Z_div_ge0.
  omega.
  omega.

  get_int_max; omega.
  get_int_max; split.
  omega.
  intrange out omega.

  repeat rewrite Int.unsigned_repr.
  rewrite <- (Z_div_mult_full  4294967295 4) .
  apply Z_div_le.
  omega.
  intrange out omega.
  omega.

  get_int_max; omega.
  split.
  omega.
  get_int_max; intrange out omega.

  split.
  omega.
  get_int_max; intrange out omega.
  split.
  omega.
  get_int_max; intrange out omega.

  repeat rewrite Int.unsigned_repr.
  split.
  cut ((Int.unsigned out -4)/ 4 >=0).
  intros.
  omega.
  apply Z_div_ge0.
  omega.
  omega.

  rewrite <- (Z_div_mult_full  4294967295 4) .
  apply Z_div_le.
  omega.
  intrange out omega.
  omega.

  get_int_max; omega.
  get_int_max; split.
  omega.
  intrange out omega.
  get_int_max; omega.
Qed.

Lemma math_lt_mod_lt :
  forall i i0 x4,
    Int.ltu i ($ 4) = false ->
    Int.ltu i0 ($ 4) = false ->
    Int.modu (i-ᵢ$ 4) ($ 4) = $ 0 ->
    Int.modu (i0-ᵢ$ 4) ($ 4) = $ 0 ->
    i0 <> i+ᵢ$ 4 ->
     ∘(Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4))) = ∘(Int.unsigned x4) ->
    (∘(Int.unsigned (Int.divu (i-ᵢ$ 4) ($ 4))) < ∘(Int.unsigned x4))%nat ->
    Int.unsigned x4 <= OS_MAX_Q_SIZE ->
    Int.ltu (i+ᵢ$ 4) ($ 4) = false /\ Int.modu ((i+ᵢ$ 4)-ᵢ$ 4) ($ 4) = $ 0 /\
    (∘(Int.unsigned (Int.divu ((i+ᵢ$ 4)-ᵢ$ 4) ($ 4))) < ∘(Int.unsigned x4))%nat.
Proof.
  intros.
  unfold Int.ltu in H.
  bfunc_invert' H.
  rewrite_un_repr_in g.

  unfold Int.ltu in H0.
  bfunc_invert' H0.
  rewrite_un_repr_in g0.

  unfold Int.modu, Int.sub in H1, H2.
  rewrite Int.unsigned_repr in H1, H2.
  rewrite_un_repr_in H1.
  rewrite_un_repr_in H2.
  Focus 2.


  solve_int_range i0.
  Focus 2.
  solve_int_range i.

  simpl_int_repr H1.
  simpl_int_repr H2.

  Focus 2.

  get_int_max.
  solve_mod_range omega.
  Focus 2.
  get_int_max.
  solve_mod_range omega.

  copy H7.
  copy H8.

  rewrite Zminus_mod in H7, H8.
  rewrite Z_mod_same_full in H7, H8.
  rewrite <- Zminus_0_l_reverse in H7, H8.
  rewrite <- Zmod_div_mod in H7;[ idtac| omega.. | try (apply Zdivide_intro with 1; auto)].
  rewrite <- Zmod_div_mod in H8;[ idtac| omega.. | try (apply Zdivide_intro with 1; auto)].



  unfold nat_of_Z in *.
  (* handle div range *)
  unfold Int.divu in H5.
  rewrite Int.unsigned_repr in H5.
  Focus 2.

  unfold Int.sub.
  rewrite Int.unsigned_repr;  solve_int_range i.
  revs.
  apply Z_div_ge0.
  omega.
  omega.

  apply Z.div_le_upper_bound.
  omega.
  intrange i omega.
  (** end of handling div range *)

  (** handle sub range *)
  unfold Int.sub in H5.
  rewrite -> Int.unsigned_repr in H5; [idtac | try solve_int_range i].
  rewrite_un_repr_in H5.
  (* end of handling sub *)

  rewrite <- Z2Nat.inj_lt in H5.
  set (Z.lt_le_trans _ _ _ H5 H6).

  Focus 2.
  apply Z.div_le_lower_bound; omega.
  Focus 2.
  intrange x4 omega.

  (* from (Int.unsigned i - 4) / 4 < ... get a sup of i*)
  rewrite (Z.mul_lt_mono_pos_r 4) in l; [idtac | omega].
  rewrite (Z.add_lt_mono_r _ _ 4) in l.
  assert ((Int.unsigned i - 4) / 4 * 4 + 4 >= Int.unsigned i - 4).
  apply (@a_div_b_multi_b_plus_b_ge_a (Int.unsigned i -4) 4); omega.
  revs' H11.
  set (Z.le_lt_trans _ _ _ H12 l).
  unfold OS_MAX_Q_SIZE in l0.
  simpl in l0.
  (* got *)

  split.
  unfold Int.ltu.
  destruct ( zlt (Int.unsigned (i+ᵢ$ 4)) (Int.unsigned ($ 4))).

  rewrite_un_repr_in l1.

  (* handling add *)
  unfold Int.add in l1.
  rewrite Int.unsigned_repr in l1.
  rewrite_un_repr_in l1.
  Focus 2.
  solve_int_range i.
  (*end of plus *)
  omega.
  trivial.

  (* before this *)
  split.
  clear H3.
  (* int auto bug*)
  clear g0.
  clear H4.
  int auto;try rewrite Z.add_simpl_r.
  rewrite H7.
  auto.
  (* and  this part *)
  unfold Int.sub in H4.
  rewrite Int.unsigned_repr in H4; [idtac | solve_int_range i0].

  unfold Int.divu in H4.
  rewrite Int.unsigned_repr in H4.
  Focus 2.
  rewrite Int.unsigned_repr;  solve_int_range i.
  (* div handler*)
  revs.
  apply Z_div_ge0.
  omega.
  omega.

  apply Z.div_le_upper_bound.
  omega.
  (**)
  intrange i0 omega.
  intrange i0 omega.
  unfold Int.modu in H2.
  (*rewrite_un_repr_in H2.
  simpl_int_repr H2;[idtac|  get_int_max;  solve_mod_range omega].*)
  rewrite Int.unsigned_repr in H4.
  rewrite_un_repr_in H4.
  Focus 2.
  get_int_max.
  solve_int_range omega.
  intrange i0 omega.

  apply Z2Nat.inj_iff in H4.

  rewrite <- H4 in H5.
  int auto.
  apply Z2Nat.inj_lt.
  (* div handler *)
  revs.
  apply Z_div_ge0.
  omega.
  omega.
  omega.

  apply Z.div_lt_upper_bound.
  omega.
  (**)
  rewrite <- H4.
  rewrite Z.add_simpl_r.
  rewrite <- Z_div_exact_full_2.

  apply (@div_lt_lt _ _ 4);[omega|idtac].
  apply Zlt_le_succ in H5.

  unfold Z.succ in H5.
  assert ((Int.unsigned i - 4) = Int.unsigned i+ -(1) * 4 ).
  omega.
  rewrite H13 in H5.
  rewrite Z_div_plus_full in H5;[idtac| omega].
  apply Zle_lt_or_eq in H5.
  destruct H5.

  omega.
  assert ((Int.unsigned i0 - 4) = Int.unsigned i0+ -(1) * 4 ).
  omega.
  rewrite H14 in H5.
  rewrite Z_div_plus_full in H5;[idtac|omega].
  assert (Int.unsigned i/4 + -(1) +1 = Int.unsigned i /4 + 1 + -(1)) by omega.
  rewrite H15 in H5.
  rewrite <- Z_div_plus_full in H5.

  simpl in H5.
  assert ((Int.unsigned i +4) /4 = Int.unsigned i0 /4) by omega.

  idtac.
  apply mod_0_div_eq_eq in H16.
  rewrite H16 in H3.
  rewrite Int.repr_unsigned in H3.
  tryfalse.
  omega.
  rewrite H8.
  assert (4 = 1*4) by omega.
  rewrite H17 at 1.
  rewrite Z_mod_plus_full.
  auto.
  omega.
  omega.

  set (@Z_mod_plus (Int.unsigned i0) (Z.neg 1) 4).
  assert (Int.unsigned i0 - 4 = Int.unsigned i0 + -1 *4).
  omega.
  rewrite H13.
  rewrite e.
  auto.
  omega.

  repeat rewrite_un_repr.
  solve_int_range i.
  (* div handler *)
  revs.
  apply Z_div_ge0.
  omega.
  omega.

  apply Z.div_le_upper_bound.
  omega.
  (**)

  intrange i omega.

  (* half div handler*)
  revs.
  apply Z_div_ge0; omega.
  (**)
  omega.
Qed.

Lemma join_prop1_my:
  forall ma mb mab x1 v1 v2 mc' mc md,
    TcbMod.join ma mb mab ->
    TcbJoin x1 v1 mc' mc ->
    TcbMod.join md mc ma ->
    TcbMod.join (TcbMod.set ma x1 v2) mb
                (TcbMod.set mab x1 v2).
Proof.
  intros.
  apply TcbMod.join_comm.
  eapply TcbMod.my_join_sig_abc.
  eapply H1.
  apply TcbMod.join_comm; trivial.
  eapply H0.
Qed.

Lemma join_prop1:
  forall v'44 v'43 v'7 v'58 prio st msg v'59 v'49 v'47 x00,
    TcbMod.join v'44 v'43 v'7 ->
    TcbJoin (v'58, Int.zero) (prio, st, msg) v'59 v'49 ->
    TcbMod.join v'47 v'49 v'44 ->
    TcbMod.join
      (TcbMod.set v'44 (v'58, Int.zero)
                  (prio, rdy , Vptr x00)) v'43
      (TcbMod.set v'7 (v'58, Int.zero)
                  (prio, rdy , Vptr x00)).
Proof.
  intros.
  eapply join_prop1_my.
  trivial.
  eapply H0.
  eapply H1.
Qed.
(* lzh-begin: Tcb join and set *)


(* mainly owe to joinsig_set_set *)


Lemma join_prop2_my:
  forall m1 m2 m12 b1 prio st msg m3 ma3 m4 p1,
    TcbMod.join m1 m2 m12 ->
    TcbJoin (b1, Int.zero) (prio, st, msg) m3 ma3 ->
    TcbMod.join m4 ma3 m2 ->
    TcbMod.join m1 
                (TcbMod.set m2 (b1, Int.zero) (prio, rdy, Vptr p1))
                (TcbMod.set m12 (b1, Int.zero) (prio, rdy, Vptr p1)).
Proof.
  unfold TcbJoin.
  intros.
  eapply TcbMod.my_join_sig_abc.
  eapply H1.
  trivial.
  unfold TcbMod.joinsig.
  eapply H0.
Qed.

Lemma join_prop2: forall v'44 v'43 v'7 v'57 prio st msg v'58 v'48 v'46 x00,
                    TcbMod.join v'44 v'43 v'7 ->
                    TcbJoin (v'57, Int.zero) (prio, st, msg) v'58 v'48 ->
                    TcbMod.join v'46 v'48 v'43->
                    TcbMod.join v'44
                                (TcbMod.set v'43 (v'57, Int.zero)
                                            (prio, rdy, Vptr x00))
                                (TcbMod.set v'7 (v'57, Int.zero)
                                            (prio, rdy , Vptr x00)).
Proof.
  apply join_prop2_my.
Qed.


(**** lzh-end *)



(**** lzh-begin: join *)

Lemma joinsig_join_ex_my:
  forall x1 v1 ma mb mab m,
    EcbMod.joinsig x1 v1 mab m ->
    EcbMod.join ma mb mab ->
    exists mm, EcbMod.joinsig x1 v1 ma mm /\ EcbMod.join mm mb m.
Proof.
  intros x1 v1 ma mb mab m.
  unfold EcbMod.joinsig.
  intros F1 F2.
  apply EcbMod.join_assoc_spec_1 with (mab:=mab); trivial.
Qed.

Lemma joinsig_join_ex:
  forall x0 x x1 t x4 x5,
    EcbMod.joinsig x0 x x1 t ->
    EcbMod.join x4 x5 x1 ->
    exists y,  EcbMod.joinsig x0 x x4 y /\  EcbMod.join y x5 t.
Proof.
  intros x0 x x1 t x4 x5.
  apply joinsig_join_ex_my with (mab:=x1).
Qed.
(**** lzh-end *)

(**** lzh-begin: join *)
Lemma ecbmod_join_sigg_my:
  forall m1 m2 m3 x1 v1,
    EcbMod.join m1 m2 m3 ->
    EcbMod.joinsig x1 v1 EcbMod.emp m2 ->
    EcbMod.joinsig x1 v1 m1 m3.
Proof.
  intros m1 m2 m3 x1 v1.
  unfold EcbMod.joinsig.
  intros F1 F2.
  assert (A1: EcbMod.meq (EcbMod.sig x1 v1) m2).
  apply EcbMod.join_meq.
  apply EcbMod.join_comm.
  trivial.
  apply EcbMod.join_meq_sub_1st with (m1:=m2).
  apply EcbMod.join_comm; trivial.
  apply EcbMod.meq_sym; trivial.
Qed.

Lemma ecbmod_join_sigg:
  forall x0 x2 x1 x3 x,
    EcbMod.join x0 x x2 ->
    EcbMod.joinsig x1 x3 EcbMod.emp x ->
    EcbMod.joinsig x1 x3 x0 x2.
Proof.
  intros x0 x2 x1 x3 x.
  apply ecbmod_join_sigg_my.
Qed.
(**** lzh-end *)

(**** lzh-begin: join *)

(* tidspec.A := tid *)
(* abstcb.B := (priority * taskstatus * msg) *)
(* EcbMod.map is a ordering list of (tidspec.A, abstcb.B) *)
(* EcbMod.join m1 m2 m: merge m1 and m2 to m *)
(* EcbMod.sig a b: cons a b to a EcbMod.map, for EcbMod.map = EcbMod.listset *)


(** 
Use '+' indicate the operation EcbMod.join 
Then, this lemma means: 
(x1,v1) + m1 = m2 ->
mm1 + m2 = mm2 ->
exists me = mm1 + m1, (x1,v1) + me = mm2

The proof is obvious:
(x1,v1) + me = (x1,v1) + mm1 + m1 = (x1,v1) + m1 + mm1 = m2 + mm1 = mm1 + m2 = mm2
*)


Lemma joinsig_join_sig2_my:
  forall x1 v1 m1 m2 mm1 mm2,
    EcbMod.joinsig x1 v1 m1 m2 ->
    EcbMod.join mm1 m2 mm2 ->
    exists me, EcbMod.joinsig x1 v1 me mm2 /\ EcbMod.join mm1 m1 me.
Proof.
  intros x1 v1 m1 m2 mm1 mm2.
  unfold EcbMod.joinsig.
  intros H1 H2.
  set (F1:=EcbMod.join_disj_meq H1).
  set (F2:=EcbMod.join_disj_meq H2).
  inversion F1 as [F11 F12].
  clear F1.
  inversion F2 as [F21 F22].
  clear F2.
  exists (EcbMod.merge mm1 m1).
  assert (H3:EcbMod.join mm1 m1 (EcbMod.merge mm1 m1)).
  apply EcbMod.join_merge_disj.
  unfold EcbMod.meq in F12.
  apply EcbMod.disj_trans_sub with (m2:=m2).
  apply EcbMod.join_sub_r with (m1:=EcbMod.sig x1 v1).
  assumption.
  assumption.
  split.
  apply EcbMod.join_assoc with (mb:=m1)(mc:=mm1)(mab:=m2).
  trivial.
  apply EcbMod.join_comm; trivial.
  apply EcbMod.join_comm; trivial.
  trivial.
Qed.

Lemma joinsig_join_sig2:
  forall x1 x3 x4 x x0 x2,
    EcbMod.joinsig x1 x3 x4 x ->
    EcbMod.join x0 x x2 ->
    exists x5,  EcbMod.joinsig x1 x3 x5 x2 /\ EcbMod.join x0 x4 x5.
Proof.
  apply joinsig_join_sig2_my.
Qed.

(**** lzh-end *)

Lemma tcbjoin_set_my:
  forall x1 v1 v2 m' m,
    TcbJoin x1 v1 m' m ->
    TcbJoin x1 v2 m' (TcbMod.set m x1 v2).
Proof.
  unfold TcbJoin.
  apply TcbMod.my_joinsig_set.
Qed.

Lemma tcbjoin_set:
  forall x  y x2 x1 tcbls,
    TcbJoin x x2 x1 tcbls ->
    TcbJoin x y x1 (TcbMod.set tcbls x y).
Proof.
  intros x y x2 x1 tcbls.
  apply tcbjoin_set_my.
Qed.

Lemma tcbjoin_get_my:
  forall x1 v1 m' m v2,
    TcbJoin x1 v1 m' m ->
    TcbMod.get m x1 = Some v2 -> v1 = v2.
Proof.
  unfold TcbJoin.
  intros.
  apply TcbMod.join_sig_get in H.
  rewrite H in H0.
  inversion H0.
  trivial.
Qed.

Lemma tcbjoin_get:
  forall x a x1 tcbls a',
    TcbJoin x a  x1 tcbls ->
    TcbMod.get tcbls x = Some a' -> a = a'.
Proof.
  intros x a x1 tcbls a'.
  apply tcbjoin_get_my.
Qed.


Lemma tcbjoin_get_get_my:
  forall x1 v1 m' m x2 v2,
    TcbJoin x1 v1 m' m ->
    TcbMod.get m' x2 = Some v2 ->
    TcbMod.get m x2 = Some v2.
Proof.
  intros x1 v1 m' m x2 v2 F1 F2.
  eapply TcbMod.get_sub_get.
  eapply F2.
  unfold TcbJoin in *.
  eapply TcbMod.join_sub_r.
  eapply F1.
Qed.

Lemma tcbjoin_get_get:
  forall x x2 x1 tcbls v tid ,
    TcbJoin x x2 x1 tcbls ->
    TcbMod.get x1 tid = Some v->
    TcbMod.get tcbls tid = Some v.
Proof.
  intros x x2 x1 tcbls v tid.
  apply tcbjoin_get_get_my.
Qed.

Lemma tcbjoin_get_a_my:
  forall x v m' m,
    TcbJoin x v m' m ->
    TcbMod.get m x = Some v.
Proof.
  intros x v m' m.
  eapply TcbMod.join_sig_get.
Qed.

Lemma tcbjoin_get_a :
  forall x a x1 tcbls,
    TcbJoin x a  x1 tcbls ->
    TcbMod.get tcbls x = Some a.
Proof.
  intros x a x1 tcbls.
  apply tcbjoin_get_a_my.
Qed.


Lemma not_eq_comm:
  forall T (x y:T),
    x <> y -> y <> x.
Proof.
  intros T x y F1.
  intuition.
Qed.

Lemma tcbjoin_get_getneq_my:
  forall x1 v1 x2 v2 m' m,
    TcbJoin x1 v1 m' m ->
    TcbMod.get m' x2 = Some v2 ->
    TcbMod.get m x2 = Some v2 /\ x2 <> x1.
Proof.
  intros x1 v1 x2 v2 m' m.
  unfold TcbJoin.
  unfold join in *.
  unfold sig in *.
  simpl in *.  
  intros F1 F2.
  split.
  TcbMod.solve_map.
  apply not_eq_comm.
  eapply TcbMod.join_get_get_neq.
  eapply F1.
  TcbMod.solve_map.
  TcbMod.solve_map.
Qed.

Lemma tcbjoin_get_getneq:
  forall x a x1 tcbls tid b,
    TcbJoin x a  x1 tcbls ->
    TcbMod.get x1 tid = Some b ->
    TcbMod.get tcbls tid = Some b /\ tid <> x.
Proof.
  intros x a x1 tcbls tid b.
  apply tcbjoin_get_getneq_my.
Qed.

Lemma tcbjoin_join_get_neq_my:
  forall x1 v1 x2 v2 ma mb' mb mab,
    TcbJoin x1 v1 mb' mb ->
    TcbMod.join ma mb mab ->
    TcbMod.get ma x2 = Some v2 ->
    x2 <> x1 /\ TcbMod.get mab x2 = Some v2.
Proof.
  intros x1 v1 x2 v2 ma mb' mb mab.
  unfold TcbJoin.
  unfold join in *.
  unfold sig in *.
  simpl in *.  
  intros F1 F2 F3.
  split.
  eapply TcbMod.join_get_get_neq.
  eapply F2.
  TcbMod.solve_map.
  TcbMod.solve_map.
  TcbMod.solve_map.
Qed.

Lemma  tcbjoin_join_get_neq:
  forall ptcb a x1 tid tcs tcbls tcs' b,
    TcbJoin ptcb a x1 tcs ->
    TcbMod.join tcbls tcs tcs' ->
    TcbMod.get tcbls tid = Some b ->
    tid <> ptcb /\  TcbMod.get tcs' tid = Some b.
Proof.
  intros ptcb a x1 tid tcs tcbls tcs' b.
  eapply tcbjoin_join_get_neq_my.
Qed.


Lemma tcbjoin_join_ex2_main:
  forall x v ma' ma mb mab,
    TcbJoin x v ma' ma ->
    TcbMod.join ma mb mab ->
    exists mab', TcbMod.join ma' mb mab' /\ TcbJoin x v mab' mab.
Proof.
  introv Fjs Fj.
  unfold TcbJoin in *.
  exists (TcbMod.merge ma' mb).
  assert (Hy: TcbMod.join ma' mb (TcbMod.merge ma' mb)).
  eapply TcbMod.join_whole2part; eauto.
  split; eauto.
  eapply TcbMod.join_assoc; eauto.
Qed.

Lemma  tcbjoin_join_ex2 :
  forall x x4 x3 a0 b c,
    TcbJoin x x4 x3 a0 ->
    TcbMod.join a0 b c ->
    exists z, TcbMod.join x3 b z /\ TcbJoin x x4 z c.
Proof.
  introv F1 F2.
  eapply tcbjoin_join_ex2_main; eauto.
Qed.

Lemma tcbjoin_set_ex_main:
  forall x v ma' ma mb mab v',
    TcbJoin x v ma' ma ->
    TcbMod.join mb ma mab ->
    exists ma'',
      TcbJoin x v' ma' ma'' /\
      TcbMod.join mb ma'' (TcbMod.set mab x v').
Proof.
  introv Fj1 Fj2.
  unfold TcbJoin in *.
  exists (TcbMod.set ma x v').
  assert (Fj3: TcbJoin x v' ma' (TcbMod.set ma x v')).
  eapply TcbMod.joinsig_set; eauto.
  split; eauto.
  eapply TcbMod.my_joinsig_join_set; eauto.
Qed.

Lemma tcbjoin_set_ex :
  forall  ptr st st' x y z a ,
    TcbJoin ptr st  x y ->
    TcbMod.join z y a  ->
    exists b,
      TcbJoin ptr st' x b /\
      TcbMod.join z b (TcbMod.set a ptr st').
Proof.
  introv F1 F2.
  eapply tcbjoin_set_ex_main; eauto.
Qed.


Lemma ecblist_p_compose:
  forall qptrl1 p q  msgqls1 mqls1 tcbls qptrl2 msgqls2 mqls2 mqls,
    EcbMod.join mqls1 mqls2 mqls -> 
    ECBList_P p q  qptrl1 msgqls1 mqls1 tcbls ->
    ECBList_P q Vnull qptrl2 msgqls2 mqls2 tcbls ->
    ECBList_P p Vnull (qptrl1 ++ qptrl2) (msgqls1 ++ msgqls2) mqls tcbls.
Proof.
  inductions qptrl1.
  introv Hecb Hp1 Hp2.
  simpl in Hp1.
  simp join.
  simpl.
  apply EcbMod.join_emp_eq in Hecb.
  subst.
  auto.
  introv Hecb Hp1 Hp2.
  unfold ECBList_P in Hp1; fold ECBList_P in Hp1.
  simp join.
  destruct msgqls1 ; tryfalse.
  destruct a.
  simp join.
  simpl.
  eexists.
  splits; eauto.
  apply EcbMod.join_comm in Hecb.
  lets Hrs : joinsig_join_sig2 H1 Hecb.
  simp join.
  do 3 eexists; splits; eauto.
  apply EcbMod.join_comm in H5.
  eapply IHqptrl1; eauto.
Qed.


Lemma prio_in_tbl_rgrp_neq_zero:
  forall p rtbl rgrp,
    0<= Int.unsigned p < 64 ->
    array_type_vallist_match Int8u rtbl ->
    length rtbl = ∘OS_RDY_TBL_SIZE->
    prio_in_tbl p rtbl ->
    RL_Tbl_Grp_P rtbl (Vint32 rgrp) ->
    rgrp <> $ 0.
Proof.
  introv Hran Harr  Hlen Hpro Hrl.
  unfolds in Hpro.
  unfolds in Hrl.
  introv Hf.
  subst.
  assert ( 0<= ∘(Int.unsigned (Int.shru p ($ 3))) < 8)%nat.
  splits; try omega.
  unfold nat_of_Z.
  assert (Z.to_nat 8 = 8)%nat by (simpl; auto).
  rewrite <- H.
  eapply Z2Nat.inj_lt.
  apply Int.unsigned_range.
  omega.
  apply shru_3_lt_8.
  omega.
  assert ( p&ᵢ$ 7  =  p&ᵢ$ 7) by auto.
  assert (Int.shru p ($ 3) = Int.shru p ($ 3)) by auto.
  lets Hex : n07_arr_len_ex H Harr Hlen.
  destruct Hex as (v & Hex1 & Hex2).
  lets Hesa : Hpro H0 H1 Hex1.
  assert ( V$0 = V$0) by auto.
  lets Hds : Hrl H Hex1 H2.
  simp join.
  rewrite Int.and_commut in *.
  rewrite Int.and_zero in *.
  unfold Int.zero in *.
  assert ($ 0 = $ 0) by auto.
  apply H3 in H0.
  subst v.
  rewrite Int.and_zero in Hesa.
  unfold Int.zero.
  assert (0 <= Int.unsigned p < 64) by omega.
  lets Hf : math_prop_neq_zero2 H0.
  unfold Int.zero in Hesa.
  tryfalse.
Qed.


Lemma unmap_inrtbl': 
  forall x y i i0 rtbl,
    prio_in_tbl ($ OS_IDLE_PRIO) rtbl -> 
    array_type_vallist_match Int8u rtbl ->
    length rtbl = ∘OS_RDY_TBL_SIZE->
    RL_Tbl_Grp_P rtbl (Vint32 i) ->
    (Int.unsigned i <= 255) ->
    nth_val' (Z.to_nat (Int.unsigned i)) OSUnMapVallist = Vint32 x ->
    nth_val' (Z.to_nat (Int.unsigned x)) rtbl = Vint32 i0 ->
    nth_val' (Z.to_nat (Int.unsigned i0)) OSUnMapVallist = Vint32 y ->
    Int.unsigned ((x<<ᵢ$ 3) +ᵢ y) < 64 /\ 
    prio_in_tbl ((x<<ᵢ$ 3) +ᵢ y) rtbl.
Proof.
  introv Hpro Harr Hlen Hrl Hrg Hnth1 Hnth2 Hnth3.
  lets Hneq : prio_in_tbl_rgrp_neq_zero Hpro Hrl; try omega; eauto.
  unfold OS_IDLE_PRIO.
  unfold OS_LOWEST_PRIO.
  clear -x.
  int auto.
  unfolds in Hrl.
  lets Hrs : math_unmap_range Hrg Hnth1.
  simpl in Hlen.
  unfold Pos.to_nat in Hlen.
  simpl in Hlen.
  rewrite <- Hlen in Hrs.
  assert (Z.to_nat (Int.unsigned x) < length rtbl)%nat by omega.
  lets Hz :  nth_val'_imply_nth_val H Hnth2.
  rewrite Hlen in Hrs.
  assert ( Vint32 i = Vint32 i) by auto.
  lets Hex : Hrl Hrs Hz H0.
  destruct Hex as (Hes1 & Hes2).
  assert (i0 = $ 0 \/   Int.ltu ($ 0) i0 = true ).
  assert (i0 = $ 0 \/ i0 <>$ 0) by tauto.
  destruct H1; auto.
  right.
  eapply int_eq_false_ltu.
  eapply Int.eq_false.
  auto.
  destruct H1.
  subst i0.
  assert (  $ 0 = $ 0) by auto.
  apply Hes1 in H1.
  unfolds in Hpro.
  clear Hes1.
  clear Hes2.
  rewrite Int.unsigned_repr in Hnth3.
  simpl in Hnth3.
  inverts Hnth3.
  splits.
  eapply   nat_x_prop_range; auto.
  unfolds.
  intros.
  subst.
  rewrite shrl_eq in Hz; auto.
  rewrite Hz in H4.
  inverts H4.
  rewrite Int.and_commut.
  rewrite Int.and_zero.
  replace ($ 0) with (Int.zero) by auto.
  rewrite  Int.add_zero.

  eapply math_prop_int_zero_eq; eauto.
  assert ($ Z.of_nat (Z.to_nat (Int.unsigned x)) = x).
  clear -Hrs.
  apply nat_8_range_conver in Hrs.
  mauto.
  rewrite H2 in H1.
  auto.
  clear -x.
  int auto.

  assert (i0 <> $ 0).
  assert (   i0 <> $ 0 \/    i0 = $ 0) by tauto.
  destruct H2; auto.
  subst i0.
  unfolds in H1.
  rewrite zlt_false in H1.
  inverts H1.
  clear -x.
  int auto.
  apply Hes2 in H1.
  clear Hes1 Hes2.
  lets Hex : n07_arr_len_ex  Hrs  Harr Hlen.
  destruct Hex as (v & Hex1 & Hex2).
  lets Hzd :  nth_val'_imply_nth_val H Hnth2.
  rewrite Hzd in Hex1.
  inverts Hex1.
  lets Hrzd : math_unmap_get_y Hex2 Hnth3.
  splits.
  eapply math_88_prio_range; eauto.
  unfolds.
  introv Hx Hy.
  subst.
  introv Hnv.
  lets Heq : math_shrl_3_eq  Hrzd Hrs.
  rewrite Heq in *.
  unfold nat_of_Z in *.
  erewrite Hnv in Hzd.
  inverts Hzd.
  lets Htra : Hrl Hrs Hnv H0.
  destruct Htra.
  lets Hda : math_8range_eqy Hrs Hrzd.
  rewrite Hda.
  eapply math_8_255_eq; eauto.
Qed.



Lemma unmap_inrtbl: 
  forall x y i i0 rtbl,
   prio_in_tbl ($ OS_IDLE_PRIO) rtbl -> 
    array_type_vallist_match Int8u rtbl ->
    length rtbl = ∘OS_RDY_TBL_SIZE->
    RL_Tbl_Grp_P rtbl (Vint32 i) ->
    (Int.unsigned i <= 255) ->
    nth_val' (Z.to_nat (Int.unsigned i)) OSUnMapVallist = Vint32 x ->
    nth_val' (Z.to_nat (Int.unsigned x)) rtbl = Vint32 i0 ->
    nth_val' (Z.to_nat (Int.unsigned i0)) OSUnMapVallist = Vint32 y ->
    prio_in_tbl (Int.repr (Int.unsigned ((x<<ᵢ$ 3) +ᵢ y))) rtbl.
Proof.
  intros.
  lets Hss  : unmap_inrtbl' H4 H5 H6; eauto.
  destruct Hss.
  rewrite Int.repr_unsigned.
  auto.
Qed.


Lemma tcbjoin_get_get2:
  forall x t x3 x2 x1 z,
    x <> t ->
    TcbJoin x x3 x2 x1 ->
    TcbMod.get x1 t = Some z ->
    TcbMod.get x2 t = Some z.
Proof.
  intros.
  unfold TcbJoin in H0.
  eapply TcbMod.join_get_or in H0.
  elim H0.
  intros.
  Focus 2.
  intro.
  exact H2.
  rewrite TcbMod.get_sig_none in H2.
  inversion H2.
  auto.
  auto.
Qed.


Lemma  TCBList_P_tcbmod_get:
  forall l1 x1 t z p1 rtbl ,
    TcbMod.get x1 t = Some z ->
    TCBList_P p1 l1 rtbl x1 ->
    (Vptr t = p1 /\ l1 <> nil) \/ 
    (exists ll1 ll2 vl, l1 = ll1 ++ (vl :: ll2) /\ ll2 <> nil /\  V_OSTCBNext vl = Some (Vptr t)).
Proof.
  inductions l1.
  intros.
  simpl in H0.
  subst x1.
  rewrite TcbMod.emp_sem in H.
  tryfalse.
  intros.
  simpl in H0.
  simp join.
  assert (x = t \/ x <> t) by tauto.
  destruct H0.
  left; subst; auto.
  
(*  split. 
  auto. 
  introv Hf; tryfalse. *)
  right.
  lets Hs : tcbjoin_get_get2 H; eauto.
  lets Hx : IHl1 Hs H4.
  destruct Hx.
  simp join.
  eexists (nil :list vallist).
  exists l1.
  exists a.
  splits; eauto.
  destruct H5 as (la1 & la2 & vla & Hle & Hll2 & Hv).
  subst l1.
  exists (a::la1).
  exists la2.
  exists vla.
  splits; simpl; eauto.
Qed.


Lemma tcbjoin_join_ex:
  forall x x3  x1 x4 x5 x2,
    TcbJoin x x3 x2 x1 ->
    TcbMod.join x4 x5 x2 ->
    exists x',  TcbJoin x x3  x4 x' /\ TcbMod.join x' x5 x1.
Proof.
  intros.
  unfold TcbJoin in *.
  eapply TcbMod.join_assoc_r.
  exact H0.
  auto.
Qed.


Lemma TCBList_P_decompose:
  forall l1 l2 p1  rtbl x1 a vp, 
    TCBList_P p1 ((l1++(a::nil))++l2) rtbl x1 ->
    V_OSTCBNext a = Some vp ->
    exists x y ,TCBList_P p1 (l1++(a::nil)) rtbl x /\ 
                TCBList_P vp l2 rtbl y /\ TcbMod.join x y x1.
Proof.
  inductions l1.
  intros.
  simpl in H.
  simpl.
  simp join.
  exists (TcbMod.sig x x3).
  exists x2.
  rewrite H1 in H0.
  inverts H0.
  splits; eauto.
  do 4 eexists; splits; eauto.
  unfolds.
  eapply TcbMod.join_emp; eauto.
  intros.
  simpl in H.
  simp join.
  eapply IHl1 in H4; eauto.
  simp join.
  lets Hsz : tcbjoin_join_ex H2 H5.
  simp join.
  exists x6.
  exists x5.
  splits; eauto.
  simpl.
  do 4 eexists; splits; eauto.
  unfold TcbJoin in *.
  unfold join, sig in *; simpl in *.
  auto.
Qed.


Lemma TCBList_get_TCBNode_P:
  forall tcbls p1 p2 rtbl t x1 x x2 l1 l2 ,
    TcbMod.get tcbls t = Some x ->
    TcbMod.join x1 x2 tcbls ->
    TCBList_P p1 l1 rtbl x1 ->
    TCBList_P p2 l2 rtbl x2 ->
    exists vl, TCBNode_P vl rtbl x.
Proof.
  intros.
  lets Hrs : TcbMod.join_get_or H0 H.
  destruct Hrs.
  lets Has :  TCBList_P_tcbmod_get H3 H1.
  destruct Has.
  simp join.
  destruct l1; tryfalse.
  simpl in H1.
  simp join.
  inverts H1.
  apply tcbjoin_get_a_my in H6.
  rewrite H6 in H3.
  inverts H3.
  eauto.
  simp join.
  rewrite list_cons_assoc in H1.
  lets Hzs : TCBList_P_decompose H1 H6.
  simp join.
  destruct x3; tryfalse.
  simpl in H7.
  simp join.
  inverts H7.
  apply tcbjoin_get_a_my in H10.
  lets Hasb : TcbMod.join_get_get_r H8 H10.
  rewrite H3 in Hasb.
  inverts Hasb.
  eauto.
  lets Has :  TCBList_P_tcbmod_get H3 H2.
  destruct Has.
  simp join.
  destruct l2; tryfalse.
  simpl in H2.
  simp join.
  inverts H2.
  apply tcbjoin_get_a_my in H6.
  rewrite H6 in H3.
  inverts H3.
  eauto.
  simp join.
  rewrite list_cons_assoc in H2.
  lets Hzs : TCBList_P_decompose H2 H6.
  simp join.
  destruct x3; tryfalse.
  simpl in H7.
  simp join.
  inverts H7.
  apply tcbjoin_get_a_my in H10.
  lets Hasb : TcbMod.join_get_get_r H8 H10.
  rewrite H3 in Hasb.
  inverts Hasb.
  eauto.
Qed.


Lemma prio_wt_inq_keep:
  forall prio prio0  etbl ey,
    Int.unsigned prio < 64 ->
    prio <> $ prio0 ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) etbl = Some (Vint32 ey) ->
    (PrioWaitInQ prio0
                 (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) etbl
                                 (Vint32 (Int.or ey ($ 1<<ᵢ(prio&ᵢ$ 7))))) <->
     PrioWaitInQ prio0 etbl).
Proof.
  introv Hran  Hneq Hnth .
  split.
  intros.
  unfolds.
  unfolds in H.
  simp join.
  remember ($ prio0) as pri.
  assert (0 <=Int.unsigned pri < 64).

  clear - H H4 Heqpri.
  int auto.
  subst .
  int auto.

  exists ( pri&ᵢ$ 7).
  exists (Int.shru ( pri) ($ 3)).
  assert ( ∘(Int.unsigned (Int.shru pri ($ 3))) <> ∘(Int.unsigned (Int.shru prio ($ 3)))
           \/ ∘(Int.unsigned (Int.shru pri ($ 3))) = ∘(Int.unsigned (Int.shru prio ($ 3)))) by tauto.
  destruct H1.
  exists x1.
  splits; eauto.
  eapply nth_upd_neq with (m :=∘(Int.unsigned (Int.shru prio ($ 3)))); eauto.
  rewrite H1 in H2.
  apply nth_upd_eq in H2.
  inverts H2.
  rewrite H1.
  exists ey.
  splits; eauto.
  rewrite Int.and_commut in H3.
  rewrite Int.and_or_distrib in H3.

  lets Heq : math_prio_neq_zero H0 H1; eauto.
  clear - Hran.
  int auto.
  unfold Int.one in *.
  rewrite Heq in H3.
  rewrite Int.or_zero in H3.
  rewrite Int.and_commut in H3.
  auto.
  intro Hpr.
  unfolds in Hpr.
  simp join.
  unfolds.
  remember ($ prio0) as pri.
  assert (0 <=Int.unsigned pri < 64).

  clear - H H4 Heqpri.
  int auto.
  subst .
  int auto.

  exists ( pri&ᵢ$ 7).
  exists (Int.shru ( pri) ($ 3)).
  assert ( ∘(Int.unsigned (Int.shru pri ($ 3))) <> ∘(Int.unsigned (Int.shru prio ($ 3)))
           \/ ∘(Int.unsigned (Int.shru pri ($ 3))) = ∘(Int.unsigned (Int.shru prio ($ 3)))) by tauto.
  destruct H1.
  exists x1.
  splits; eauto.
  eapply nth_upd_neqrev with (m :=∘(Int.unsigned (Int.shru prio ($ 3)))); eauto.
  rewrite H1 in *.
  exists ( (Int.or ey ($ 1<<ᵢ(prio&ᵢ$ 7)))).
  splits; eauto.
  eapply pure_lib.update_nth; eauto.
  rewrite Int.and_commut.
  rewrite Int.and_or_distrib.
  rewrite Hnth in H2.
  inverts H2.
  lets Heq : math_prio_neq_zero H0 H1; eauto.
  clear  - Hran.
  int auto.
  rewrite Heq.
  rewrite Int.or_zero.
  rewrite Int.and_commut.
  auto.
Qed.


Lemma ecbmod_joinsig_get_none:
  forall x x0 x1 ecbls qid,
    EcbMod.joinsig x x0 x1 ecbls ->
    EcbMod.get ecbls qid = None ->
    EcbMod.get x1 qid = None.
Proof.
  intros.
  unfold EcbMod.joinsig in H.
  unfold EcbMod.join in H.
  set (H qid).
  rewrite H0 in y.
  destruct (EcbMod.get x1 qid).
  destruct (EcbMod.get (EcbMod.sig x x0) qid); inversion y.
  auto.
Qed.

Lemma prio_update_self_not_in :
  forall pri rtbl ry,
    0 <= Int.unsigned pri < 64 ->
    nth_val ∘(Int.unsigned (Int.shru pri ($ 3))) rtbl = Some (Vint32 ry) ->
    ~ prio_in_tbl pri
      (update_nth_val ∘(Int.unsigned (Int.shru pri ($ 3))) rtbl
                      (Vint32 (ry&ᵢInt.not ($ 1<<ᵢ(pri&ᵢ$ 7))))).
Proof.
  introv Hin Hnth Hf.
  unfolds in  Hf.
  assert (nth_val ∘(Int.unsigned (Int.shru pri ($ 3)))
                  (update_nth_val ∘(Int.unsigned (Int.shru pri ($ 3))) rtbl
                                  (Vint32 (ry&ᵢInt.not ($ 1<<ᵢ(pri&ᵢ$ 7))))) = Some (Vint32  (ry&ᵢInt.not ($ 1<<ᵢ(pri&ᵢ$ 7))))).
  eapply pure_lib.update_nth; eauto.
  lets Hs : Hf H; eauto.
  rewrite Int.and_assoc in Hs.
  assert (Int.not ($ 1<<ᵢ(pri&ᵢ$ 7))&ᵢ($ 1<<ᵢ(pri&ᵢ$ 7)) = Int.zero).
  rewrite Int.and_commut.
  apply  Int.and_not_self.
  rewrite H0 in Hs.
  rewrite Int.and_zero in Hs.
  lets Hx : math_prop_neq_zero2 Hin.
  unfold Int.zero in *.
  rewrite <- Hs in Hx.
  tryfalse.
Qed.


Lemma math_xyz_prop2'
: forall out start sin hsize : int32,
    start = $ 4 ->
    Int.ltu out start = false ->
    Int.ltu sin start = false ->
    Int.modu (out-ᵢstart) ($ 4) = $ 0 ->
    Int.modu (sin-ᵢstart) ($ 4) = $ 0 ->
    (∘(Int.unsigned (Int.divu (sin-ᵢstart) ($ 4))) <
     ∘(Int.unsigned hsize))%nat ->
    (∘(Int.unsigned (Int.divu (out-ᵢstart) ($ 4))) <
     ∘(Int.unsigned hsize))%nat ->
    Int.unsigned hsize <= OS_MAX_Q_SIZE ->
    Int.unsigned (Int.divu (sin-ᵢstart) ($ 4)) >
    Int.unsigned (Int.divu ((out+ᵢ$ 4)-ᵢstart) ($ 4)) ->
    Int.unsigned (Int.divu (sin-ᵢstart) ($ 4)) >
    Int.unsigned (Int.divu (out-ᵢstart) ($ 4)) /\
    S ∘(Int.unsigned (Int.divu (out-ᵢstart) ($ 4))) =
    ∘(Int.unsigned (Int.divu ((out+ᵢ$ 4)-ᵢstart) ($ 4))) /\
    ∘(Int.unsigned (Int.divu (out-ᵢstart) ($ 4))) =
    Z.to_nat ((Int.unsigned out - Int.unsigned start) / 4).
Proof.
  intros.
  repeat rewrite Int.repr_unsigned in *.

  rewrite H in *.
  apply (int_minus4_mod4 H0) in H2.
  apply (int_minus4_mod4 H1) in H3.
  copy H2.
  copy H3.
  rewrite Zminus_mod in H9, H8.
  rewrite Z_mod_same_full in H9, H8.
  rewrite <- Zminus_0_l_reverse in H9, H8.
  rewrite <- Zmod_div_mod in H9;[ idtac| omega.. | try (apply Zdivide_intro with 1; auto)].
  rewrite <- Zmod_div_mod in H8;[ idtac| omega.. | try (apply Zdivide_intro with 1; auto)].

  unfold nat_of_Z in *.
  unfold Int.ltu in H1, H0.
  bfunc_invert' H0.
  bfunc_invert' H1.
  ur_rewriter_in g0.
  ur_rewriter_in g.

  unfold Int.divu, Int.sub, Int.add in *.
  repeat (ur_rewriter_in H5).
  repeat (ur_rewriter_in H4).



  unfold OS_MAX_Q_SIZE in H6.
  rewrite <- Z2Nat.inj_lt in H5, H4.
  set (Z.lt_le_trans _ _ _ H5 H6).
  set (Z.lt_le_trans _ _ _ H4 H6).


  rewrite (Z.mul_lt_mono_pos_r 4) in l; [idtac | omega].
  rewrite (Z.add_lt_mono_r _ _ 4) in l.
  assert ((Int.unsigned out - 4) / 4 * 4 + 4 >= Int.unsigned out - 4).
  apply (@a_div_b_multi_b_plus_b_ge_a (Int.unsigned out -4) 4); omega.
  revs' H10.
  set (Z.le_lt_trans _ _ _ H11 l).
  simpl in l1.

  rewrite (Z.mul_lt_mono_pos_r 4) in l0; [idtac | omega].
  rewrite (Z.add_lt_mono_r _ _ 4) in l0.
  assert ((Int.unsigned sin - 4) / 4 * 4 + 4 >= Int.unsigned sin - 4).
  apply (@a_div_b_multi_b_plus_b_ge_a (Int.unsigned sin -4) 4); omega.
  revs' H12.
  set (Z.le_lt_trans _ _ _ H13 l0).
  simpl in l2.
  repeat ur_rewriter.

  Focus 2.
  apply Z.div_le_lower_bound; omega.
  Focus 2.
  intrange hsize omega.
  Focus 2.
  apply Z.div_le_lower_bound; omega.
  Focus 2.
  intrange hsize omega.

  repeat (ur_rewriter_in H7).

  (* proof start *)
  split.
  assert (Int.unsigned out +4 -4  =Int.unsigned out) by omega.
  assert (Int.unsigned out -4 = Int.unsigned out + -(1) * 4) by omega.
  rewrite H15.
  rewrite H14 in H7.
  rewrite Z_div_plus_full.
  omega.
  omega.

  split.
  rewrite <- Z2Nat.inj_succ.
  assert (Int.unsigned out +4 -4 = Int.unsigned out -4 + 1*4) by omega.
  rewrite H14.
  rewrite Z_div_plus_full.
  unfold Z.succ.
  auto.
  omega.
  revs.
  apply Z_div_ge0.
  omega.
  omega.
  auto.
Qed.

Lemma math_xyz_prop3'
: forall out start sin hsize : int32,
    start = $ 4 ->
    Int.ltu out start = false ->
    Int.ltu sin start = false ->
    Int.modu (out-ᵢstart) ($ 4) = $ 0 ->
    Int.modu (sin-ᵢstart) ($ 4) = $ 0 ->
    (∘(Int.unsigned (Int.divu (sin-ᵢstart) ($ 4))) <
     ∘(Int.unsigned hsize))%nat ->
    (∘(Int.unsigned (Int.divu (out-ᵢstart) ($ 4))) <
     ∘(Int.unsigned hsize))%nat ->
    Int.unsigned hsize <= OS_MAX_Q_SIZE ->
    Int.unsigned (Int.divu (sin-ᵢstart) ($ 4)) <
    Int.unsigned (Int.divu ((out+ᵢ$ 4)-ᵢstart) ($ 4)) ->
    (Int.unsigned (Int.divu (sin-ᵢstart) ($ 4)) <
     Int.unsigned (Int.divu (out-ᵢstart) ($ 4)) \/
     Int.unsigned (Int.divu (sin-ᵢstart) ($ 4)) =
     Int.unsigned (Int.divu (out-ᵢstart) ($ 4))) /\
    S ∘(Int.unsigned (Int.divu (out-ᵢstart) ($ 4))) =
    ∘(Int.unsigned (Int.divu ((out+ᵢ$ 4)-ᵢstart) ($ 4))) /\
    ∘(Int.unsigned (Int.divu (out-ᵢstart) ($ 4))) =
    Z.to_nat ((Int.unsigned out - Int.unsigned start) / 4).
Proof.
  intros.
  repeat rewrite Int.repr_unsigned in *.

  rewrite H in *.
  apply (int_minus4_mod4 H0) in H2.
  apply (int_minus4_mod4 H1) in H3.
  copy H2.
  copy H3.
  rewrite Zminus_mod in H9, H8.
  rewrite Z_mod_same_full in H9, H8.
  rewrite <- Zminus_0_l_reverse in H9, H8.
  rewrite <- Zmod_div_mod in H9;[ idtac| omega.. | try (apply Zdivide_intro with 1; auto)].
  rewrite <- Zmod_div_mod in H8;[ idtac| omega.. | try (apply Zdivide_intro with 1; auto)].

  unfold nat_of_Z in *.
  unfold Int.ltu in H1, H0.
  bfunc_invert' H0.
  bfunc_invert' H1.
  ur_rewriter_in g0.
  ur_rewriter_in g.

  unfold Int.divu, Int.sub, Int.add in *.
  repeat (ur_rewriter_in H5).
  repeat (ur_rewriter_in H4).



  unfold OS_MAX_Q_SIZE in H6.
  rewrite <- Z2Nat.inj_lt in H5, H4.
  set (Z.lt_le_trans _ _ _ H5 H6).
  set (Z.lt_le_trans _ _ _ H4 H6).


  rewrite (Z.mul_lt_mono_pos_r 4) in l; [idtac | omega].
  rewrite (Z.add_lt_mono_r _ _ 4) in l.
  assert ((Int.unsigned out - 4) / 4 * 4 + 4 >= Int.unsigned out - 4).
  apply (@a_div_b_multi_b_plus_b_ge_a (Int.unsigned out -4) 4); omega.
  revs' H10.
  set (Z.le_lt_trans _ _ _ H11 l).
  simpl in l1.

  rewrite (Z.mul_lt_mono_pos_r 4) in l0; [idtac | omega].
  rewrite (Z.add_lt_mono_r _ _ 4) in l0.
  assert ((Int.unsigned sin - 4) / 4 * 4 + 4 >= Int.unsigned sin - 4).
  apply (@a_div_b_multi_b_plus_b_ge_a (Int.unsigned sin -4) 4); omega.
  revs' H12.
  set (Z.le_lt_trans _ _ _ H13 l0).
  simpl in l2.
  repeat ur_rewriter.

  Focus 2.
  apply Z.div_le_lower_bound; omega.
  Focus 2.
  intrange hsize omega.
  Focus 2.
  apply Z.div_le_lower_bound; omega.
  Focus 2.
  intrange hsize omega.

  repeat (ur_rewriter_in H7).

  (* proof start *)
  split.
  assert (Int.unsigned out +4 -4  =Int.unsigned out) by omega.
  assert (Int.unsigned out -4 = Int.unsigned out + -(1) * 4) by omega.
  rewrite H15.
  rewrite H14 in H7.
  rewrite Z_div_plus_full.
  omega.
  omega.

  split.
  rewrite <- Z2Nat.inj_succ.
  assert (Int.unsigned out +4 -4 = Int.unsigned out -4 + 1*4) by omega.
  rewrite H14.
  rewrite Z_div_plus_full.
  unfold Z.succ.
  auto.
  omega.
  revs.
  apply Z_div_ge0.
  omega.
  omega.
  auto.
Qed.


Lemma list_maxsize_le:
  forall (ml : list val) hsize,
    (length ml = ∘OS_MAX_Q_SIZE)%nat ->
    Int.unsigned hsize <= OS_MAX_Q_SIZE ->
    (∘(Int.unsigned hsize) <= length ml)%nat.
Proof.
  intros.
  unfold nat_of_Z in *.
  rewrite H in *.
  apply Zle_natle.
  auto.
Qed.

Lemma math_xyz_prop4'
: forall out start sin hsize : int32,
    start = $ 4 ->
    Int.ltu out start = false ->
    Int.ltu sin start = false ->
    Int.modu (out-ᵢstart) ($ 4) = $ 0 ->
    Int.modu (sin-ᵢstart) ($ 4) = $ 0 ->
    (∘(Int.unsigned (Int.divu (sin-ᵢstart) ($ 4))) <
     ∘(Int.unsigned hsize))%nat ->
    (∘(Int.unsigned (Int.divu (out-ᵢstart) ($ 4))) <
     ∘(Int.unsigned hsize))%nat ->
    Int.unsigned hsize <= OS_MAX_Q_SIZE ->
    Int.unsigned (Int.divu (sin-ᵢstart) ($ 4)) =
    Int.unsigned (Int.divu ((out+ᵢ$ 4)-ᵢstart) ($ 4)) ->
    (Int.unsigned (Int.divu (sin-ᵢstart) ($ 4)) >
     Int.unsigned (Int.divu (out-ᵢstart) ($ 4)) ) /\
    S ∘(Int.unsigned (Int.divu (out-ᵢstart) ($ 4))) =
    ∘(Int.unsigned (Int.divu ((out+ᵢ$ 4)-ᵢstart) ($ 4))) /\
    ∘(Int.unsigned (Int.divu (out-ᵢstart) ($ 4))) =
    Z.to_nat ((Int.unsigned out - Int.unsigned start) / 4).
Proof.
  intros.
  repeat rewrite Int.repr_unsigned in *.

  rewrite H in *.
  apply (int_minus4_mod4 H0) in H2.
  apply (int_minus4_mod4 H1) in H3.
  copy H2.
  copy H3.
  rewrite Zminus_mod in H9, H8.
  rewrite Z_mod_same_full in H9, H8.
  rewrite <- Zminus_0_l_reverse in H9, H8.
  rewrite <- Zmod_div_mod in H9;[ idtac| omega.. | try (apply Zdivide_intro with 1; auto)].
  rewrite <- Zmod_div_mod in H8;[ idtac| omega.. | try (apply Zdivide_intro with 1; auto)].

  unfold nat_of_Z in *.
  unfold Int.ltu in H1, H0.
  bfunc_invert' H0.
  bfunc_invert' H1.
  ur_rewriter_in g0.
  ur_rewriter_in g.

  unfold Int.divu, Int.sub, Int.add in *.
  repeat (ur_rewriter_in H5).
  repeat (ur_rewriter_in H4).



  unfold OS_MAX_Q_SIZE in H6.
  rewrite <- Z2Nat.inj_lt in H5, H4.
  set (Z.lt_le_trans _ _ _ H5 H6).
  set (Z.lt_le_trans _ _ _ H4 H6).


  rewrite (Z.mul_lt_mono_pos_r 4) in l; [idtac | omega].
  rewrite (Z.add_lt_mono_r _ _ 4) in l.
  assert ((Int.unsigned out - 4) / 4 * 4 + 4 >= Int.unsigned out - 4).
  apply (@a_div_b_multi_b_plus_b_ge_a (Int.unsigned out -4) 4); omega.
  revs' H10.
  set (Z.le_lt_trans _ _ _ H11 l).
  simpl in l1.

  rewrite (Z.mul_lt_mono_pos_r 4) in l0; [idtac | omega].
  rewrite (Z.add_lt_mono_r _ _ 4) in l0.
  assert ((Int.unsigned sin - 4) / 4 * 4 + 4 >= Int.unsigned sin - 4).
  apply (@a_div_b_multi_b_plus_b_ge_a (Int.unsigned sin -4) 4); omega.
  revs' H12.
  set (Z.le_lt_trans _ _ _ H13 l0).
  simpl in l2.
  repeat ur_rewriter.

  Focus 2.
  apply Z.div_le_lower_bound; omega.
  Focus 2.
  intrange hsize omega.
  Focus 2.
  apply Z.div_le_lower_bound; omega.
  Focus 2.
  intrange hsize omega.

  repeat (ur_rewriter_in H7).

  (* proof start *)
  split.
  assert (Int.unsigned out +4 -4  =Int.unsigned out) by omega.
  assert (Int.unsigned out -4 = Int.unsigned out + -(1) * 4) by omega.
  rewrite H15.
  rewrite H14 in H7.
  rewrite Z_div_plus_full.
  omega.
  omega.

  split.
  rewrite <- Z2Nat.inj_succ.
  assert (Int.unsigned out +4 -4 = Int.unsigned out -4 + 1*4) by omega.
  rewrite H14.
  rewrite Z_div_plus_full.
  unfold Z.succ.
  auto.
  omega.
  revs.
  apply Z_div_ge0.
  omega.
  omega.
  auto.
Qed.

Lemma math_out_start_eq'
: forall out m : int32,
    Int.ltu out ($ 4) = false ->
    Int.modu (out-ᵢ$ 4) ($ 4) = $ 0 ->
    (∘(Int.unsigned (Int.divu (out-ᵢ$ 4) ($ 4))) <
     ∘(Int.unsigned m))%nat ->
    Int.unsigned m <= OS_MAX_Q_SIZE ->
    ∘(Int.unsigned (Int.divu (out-ᵢ$ 4) ($ 4))) =
    Z.to_nat ((Int.unsigned out - Int.unsigned ($ 4)) / 4).
Proof.
  intros.
  Iltu_simplerH H.
  unfold Int.divu, Int.sub .
  repeat ur_rewriter.
  auto.
Qed.


Lemma array_type_match_get_value:
  forall rtbl Zpy,
    0<=Zpy <= 7 ->
    array_type_vallist_match Int8u rtbl ->
    length rtbl = ∘OS_RDY_TBL_SIZE ->
    (exists v, nth_val (Z.to_nat Zpy) rtbl = Some (Vint32 v)).
Proof.
  intros.
  assert ( (exists v, nth_val (Z.to_nat Zpy) rtbl = Some (Vint32 v) /\ Int.unsigned v <=255)).
  eapply n07_arr_len_ex; eauto.
  clear -H.
  mauto.
  simp join.
  eexists; eauto.
Qed.

Lemma tcbjoin_tid_neq :
  forall tid  x y z tid0 a,
    TcbJoin tid x y z ->
    TcbMod.get y tid0 = Some a -> tid0  <> tid.
Proof.
  intros.
  unfold TcbJoin in H.
  unfold TcbMod.join in H.
  set (H tid0).
  rewrite H0 in y0.
  assert (tid0<> tid \/ tid0 = tid) by tauto.
  elim H1; intros.
  auto.
  rewrite H2 in y0.
  rewrite TcbMod.get_sig_some in y0.
  inversion y0.
Qed.


Lemma  joinsig_join_getnone:
  forall x y v1 v2 v3 v4,
    EcbMod.joinsig x y v4 v2 ->
    EcbMod.join v1 v2 v3 -> 
    EcbMod.get v1 x = None.
Proof.
  intros.

  assert ( EcbMod.get v2 x = Some y).
  eapply ecbmod_joinsig_get.
  exact H.
  unfold EcbMod.join in H0.
  set (H0 x).
  rewrite H1 in y0.
  destruct (EcbMod.get v1 x).
  inversion y0.
  auto.
Qed.

Lemma joinsig_get_none:
  forall x y v4 v2,
    EcbMod.joinsig x y v4 v2  ->
    EcbMod.get v4 x = None.
Proof.
  intros.
  unfold EcbMod.joinsig, EcbMod.join in H.
  set (H x).
  rewrite (EcbMod.get_sig_some) in y0.

  destruct (EcbMod.get v4 x).
  inversion y0.
  auto.
Qed.


Lemma ecb_set_join_join:
  forall (ml : EcbMod.map) (a : tidspec.A) (b : absecb.B)
         (ml1 ml2 ml1' : EcbMod.map) (b' : absecb.B),
    EcbMod.joinsig a b ml1' ml1 ->
    EcbMod.join ml2 ml1 ml ->
    exists ml1n,
      EcbMod.joinsig a b' ml1' ml1n /\ EcbMod.join ml2 ml1n (EcbMod.set ml a b').
Proof.
  intros.
  exists (EcbMod.set ml1 a b').
  split.
  unfold EcbMod.joinsig in *.
  clear -H.
  unfold EcbMod.join in *.
  intros.
  set (H a0).
  assert (a=a0 \/ a<> a0) by tauto.
  elim H0; intros.
  subst.
  rewrite EcbMod.get_a_sig_a in *.
  destruct (EcbMod.get ml1' a0).
  inversion y.
  rewrite EcbMod.set_a_get_a.
  auto.
  rewrite CltEnvMod.beq_refl.
  auto.
  rewrite CltEnvMod.beq_refl.
  auto.
  rewrite CltEnvMod.beq_refl.
  auto.
  rewrite CltEnvMod.beq_refl.
  auto.


  rewrite EcbMod.get_a_sig_a' in *;[idtac| rewrite tidspec.neq_beq_false; auto..].
  rewrite EcbMod.set_a_get_a' in *;[idtac| rewrite tidspec.neq_beq_false; auto..].
  destruct (EcbMod.get ml1' a0).
  destruct (EcbMod.get ml1 a0).
  auto.
  auto.
  destruct (EcbMod.get ml1 a0).
  auto.
  auto.


  eapply EcbMod.joinsig_set_set.
  exact H.
  auto.
Qed.


Lemma math_le_max_q :
   forall x N M, 
     x <= OS_MAX_Q_SIZE ->
     (M < ∘x)%nat ->
     (S N = ∘x)%nat ->
     (N < ∘OS_MAX_Q_SIZE)%nat /\  (N >= M)%nat.
Proof.
  intros.
  unfold nat_of_Z in *.

  split.
  unfold OS_MAX_Q_SIZE in *.
  compute.
  rewrite H1.
  assert (20%nat = ( Z.to_nat 20)).
  auto.
  rewrite H2.


  apply Zle_natle.
  auto.
  rewrite <- H1 in H0.
  omega.
Qed.



(* need *)
Lemma math_len_le_and:
  forall v2 a N M y,
    length v2 = ∘OS_MAX_Q_SIZE ->
    a  <= OS_MAX_Q_SIZE ->
    (M < ∘a)%nat -> 
    (S N = ∘ a)%nat ->
    (M <= S N)%nat /\  (S N <= length (update_nth_val N v2 y))%nat.
Proof.
  intros.
  unfold nat_of_Z in *.
  split.
  omega.
  rewrite H2.
  rewrite update_nth_val_len_eq.
  rewrite H.
  rewrite <- Z2Nat.inj_le.
  auto.
  assert ( 0<=a \/ a<0) by omega.
  elim H3.
  auto.
  intros.
  destruct a.
  omega.
  inversion H4.
  simpl in H2.
  inversion H2.
  unfold OS_MAX_Q_SIZE.
  omega.
Qed.


Lemma math_max_le_q:
 forall x M,
   x <= OS_MAX_Q_SIZE ->
   (M < ∘(x))%nat ->
   (S M <= ∘OS_MAX_Q_SIZE)%nat.
Proof.
  intros.
  unfold nat_of_Z in *.
  assert (Z.to_nat x <= Z.to_nat OS_MAX_Q_SIZE) %nat.
  apply Zle_natle.
  auto.
  omega.
Qed.



Lemma math_inc_eq_ltu:
  forall x2 x3 (x1 : list msg),
    Int.unsigned x2 <= OS_MAX_Q_SIZE ->
    Int.ltu x3 x2 = true -> 
    Int.unsigned x3 = Z.of_nat (length x1) ->
    Int.unsigned (x3+ᵢ$ 1) = Z.of_nat (length x1 + 1) .
Proof.
  intros.
  int auto.
  rewrite H1.
  rewrite Z.add_1_r.
  rewrite <- Nat2Z.inj_succ.
  assert (S (length x1) = (length x1) +1)%nat by omega.
  rewrite H2.
  reflexivity.
  unfold OS_MAX_Q_SIZE in *.
  destruct (zlt (Int.unsigned x3) (Int.unsigned x2)).
  assert (Int.unsigned x3 <= 20) by omega.
  int auto.
  inversion H0.
Qed.


Lemma math_int_lt_eq_split:
  forall x i0 M N x2,
    Int.ltu x ($ 4) = false ->
    Int.ltu i0 ($ 4) = false ->
    Int.modu (x-ᵢ$ 4) ($ 4) = $ 0 ->
    Int.modu (i0-ᵢ$ 4) ($ 4) = $ 0 ->
    (∘M < ∘(Int.unsigned x2))%nat ->
    (∘N < ∘(Int.unsigned x2))%nat ->
    Int.unsigned x2 <= OS_MAX_Q_SIZE ->
    M = Int.unsigned (Int.divu (x-ᵢ$ 4) ($ 4)) ->
    N = Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4)) ->
    Int.unsigned (Int.divu ((x+ᵢ$ 4)-ᵢ$ 4) ($ 4)) > N ->
    (∘(Int.unsigned (Int.divu ((x+ᵢ$ 4)-ᵢ$ 4) ($ 4)))  = S (∘M))%nat /\
    (M > N \/ M = N)/\((Z.to_nat ((Int.unsigned x - 4) / 4)) = ∘M)%nat
    /\  (∘M < ∘OS_MAX_Q_SIZE /\∘M>= ∘N )%nat  .
Proof.
  intros.
  Iltu_simplerH H.
  Iltu_simplerH H0.

  Imod_simplerH H1.
  Imod_simplerH H2.

  unfold Int.sub, Int.divu,Int.add in *.

  repeat ur_rewriter_in H1.
  repeat ur_rewriter_in H2.
  repeat ur_rewriter_in H7.
  repeat ur_rewriter_in H6.
  unfold OS_MAX_Q_SIZE in H5.

  subst.


  rewrite <- Z2Nat.inj_lt in H4, H3; [idtac | try le0_solver..].

  set (Z.lt_le_trans _ _ _ H3 H5).
  set (Z.lt_le_trans _ _ _ H4 H5).


  Zdivsup_simplerH l.
  Zdivsup_simplerH l0.

  repeat ur_rewriter_in H8.
  repeat ur_rewriter.

  unfold nat_of_Z in *.
  splits.
  rewrite Zplus_minus.
  rewrite <-Z2Nat.inj_succ.
  assert (Int.unsigned x -4 = Int.unsigned x + - (1) * 4) by omega.
  rewrite H6.
  rewrite Z_div_plus_full.
  unfold Z.succ.
  assert (Int.unsigned x /4 + -(1) +1 = Int.unsigned x /4) by omega.
  rewrite H10.
  auto.
  omega.
  le0_solver.
  rewrite Zplus_minus in H8.
  revsH H8.
  apply Z.lt_le_pred in H8.

  unfold Z.pred in H8.
  rewrite <- Z_div_plus_full in H8.
  assert (Int.unsigned x + -1 * 4 = Int.unsigned x -4 ) by omega.
  rewrite H6 in H8.
  apply Zle_lt_or_eq in H8.
  elim H8; intros;
  clear -H10; [left|right]; omega.
  omega.
  auto.
  unfold OS_MAX_Q_SIZE.
  rewrite <- Z2Nat.inj_lt.

  set (Z.lt_le_trans _ _ _ H3 H5).
  auto.
  le0_solver.
  omega.


  kzrevs.
  rewrite <- Z2Nat.inj_le;[ idtac| le0_solver..].
  rewrite Zplus_minus in H8.
  revsH H8.

  apply Z.lt_le_pred in H8.

  unfold Z.pred in H8.
  rewrite <- Z_div_plus_full in H8.
  assert (Int.unsigned x + -1 * 4 = Int.unsigned x -4 ) by omega.
  rewrite H6 in H8.
  auto.
  omega.
Qed.

Lemma math_int_lt_eq_split':
  forall x i0 M N x2,
    Int.ltu x ($ 4) = false ->
    Int.ltu i0 ($ 4) = false ->
    Int.modu (x-ᵢ$ 4) ($ 4) = $ 0 ->
    Int.modu (i0-ᵢ$ 4) ($ 4) = $ 0 ->
    (∘M < ∘(Int.unsigned x2))%nat ->
    (∘N < ∘(Int.unsigned x2))%nat ->
    Int.unsigned x2 <= OS_MAX_Q_SIZE ->
    M = Int.unsigned (Int.divu (x-ᵢ$ 4) ($ 4)) ->
    N = Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4)) ->
    Int.unsigned (Int.divu ((x+ᵢ$ 4)-ᵢ$ 4) ($ 4)) < N ->
    (∘(Int.unsigned (Int.divu ((x+ᵢ$ 4)-ᵢ$ 4) ($ 4)))  = S (∘M))%nat /\
    (M < N)/\((Z.to_nat ((Int.unsigned x - 4) / 4)) = ∘M)%nat
    /\  (∘N < ∘OS_MAX_Q_SIZE /\∘M< ∘N /\ (∘(Int.unsigned x2) <= ∘OS_MAX_Q_SIZE ))%nat  .
Proof.
  intros.
  Iltu_simplerH H.
  Iltu_simplerH H0.
  Imod_simplerH H1.
  Imod_simplerH H2.


  unfold Int.sub, Int.divu,Int.add in *.

  repeat ur_rewriter_in H1.
  repeat ur_rewriter_in H2.
  repeat ur_rewriter_in H7.
  repeat ur_rewriter_in H6.
  unfold OS_MAX_Q_SIZE in H5.

  subst.


  rewrite <- Z2Nat.inj_lt in H4, H3; [idtac | try le0_solver..].

  set (Z.lt_le_trans _ _ _ H3 H5).
  set (Z.lt_le_trans _ _ _ H4 H5).


  Zdivsup_simplerH l.
  Zdivsup_simplerH l0.

  repeat ur_rewriter_in H8.
  repeat ur_rewriter.

  unfold nat_of_Z in *.
  splits.
  rewrite Zplus_minus.
  rewrite <-Z2Nat.inj_succ.
  assert (Int.unsigned x -4 = Int.unsigned x + - (1) * 4) by omega.
  rewrite H6.
  rewrite Z_div_plus_full.
  unfold Z.succ.
  assert (Int.unsigned x /4 + -(1) +1 = Int.unsigned x /4) by omega.
  rewrite H10.
  auto.
  omega.
  le0_solver.
  rewrite Zplus_minus in H8.

  assert (Int.unsigned x + -1 * 4 = Int.unsigned x -4 ) by omega.
  rewrite <- H6 .
  rewrite Z_div_plus_full.
  assert (Int.unsigned x / 4 + -1 < Int.unsigned x /4) by omega.
  omega.
  omega.
  auto.

  unfold OS_MAX_Q_SIZE.
  rewrite <- Z2Nat.inj_lt.

  set (Z.lt_le_trans _ _ _ H4 H5).
  auto.
  le0_solver.
  omega.


  rewrite <- Z2Nat.inj_lt;[ idtac| le0_solver..].
  rewrite Zplus_minus in H8.
  revsH H8.

  assert (Int.unsigned x + -1 * 4 = Int.unsigned x -4 ) by omega.
  rewrite <- H6 .
  rewrite Z_div_plus_full.
  assert (Int.unsigned x / 4 + -1 < Int.unsigned x /4) by omega.
  omega.
  omega.

  unfold OS_MAX_Q_SIZE.
  rewrite <- Z2Nat.inj_le;[ idtac| le0_solver..].
  auto.
Qed.

Lemma math_int_lt_eq_split'':
  forall x i0 M N x2,
    Int.ltu x ($ 4) = false ->
    Int.ltu i0 ($ 4) = false ->
    Int.modu (x-ᵢ$ 4) ($ 4) = $ 0 ->
    Int.modu (i0-ᵢ$ 4) ($ 4) = $ 0 ->
    (∘M < ∘(Int.unsigned x2))%nat ->
    (∘N < ∘(Int.unsigned x2))%nat ->
    Int.unsigned x2 <= OS_MAX_Q_SIZE ->
    M = Int.unsigned (Int.divu (x-ᵢ$ 4) ($ 4)) ->
    N = Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4)) ->
    Int.unsigned (Int.divu ((x+ᵢ$ 4)-ᵢ$ 4) ($ 4)) = N ->
    (∘(Int.unsigned (Int.divu ((x+ᵢ$ 4)-ᵢ$ 4) ($ 4)))  = S (∘M))%nat /\
    (M + 1 =  N /\ M < N)/\((Z.to_nat ((Int.unsigned x - 4) / 4)) = ∘M)%nat
    /\  (∘N < ∘OS_MAX_Q_SIZE /\S ∘(M)= ∘N /\ (∘(Int.unsigned x2) <= ∘OS_MAX_Q_SIZE ))%nat  .
Proof.
  intros.
  Iltu_simplerH H.
  Iltu_simplerH H0.
  Imod_simplerH H1.
  Imod_simplerH H2.


  unfold Int.sub, Int.divu,Int.add in *.

  repeat ur_rewriter_in H1.
  repeat ur_rewriter_in H2.
  repeat ur_rewriter_in H7.
  repeat ur_rewriter_in H6.
  unfold OS_MAX_Q_SIZE in H5.

  subst.


  rewrite <- Z2Nat.inj_lt in H4, H3; [idtac | try le0_solver..].

  set (Z.lt_le_trans _ _ _ H3 H5).
  set (Z.lt_le_trans _ _ _ H4 H5).


  Zdivsup_simplerH l.
  Zdivsup_simplerH l0.

  repeat ur_rewriter_in H8.
  repeat ur_rewriter.

  unfold nat_of_Z in *.
  splits.
  rewrite Zplus_minus.
  rewrite <-Z2Nat.inj_succ.
  assert (Int.unsigned x -4 = Int.unsigned x + - (1) * 4) by omega.
  rewrite H6.
  rewrite Z_div_plus_full.
  unfold Z.succ.
  assert (Int.unsigned x /4 + -(1) +1 = Int.unsigned x /4) by omega.
  rewrite H10.
  auto.
  omega.
  le0_solver.
  rewrite Zplus_minus in H8.

  assert (Int.unsigned x + -1 * 4 = Int.unsigned x -4 ) by omega.
  rewrite <- H6 .
  rewrite Z_div_plus_full.
  assert (Int.unsigned x / 4 + -1 < Int.unsigned x /4) by omega.
  omega.
  omega.
  auto.

  unfold OS_MAX_Q_SIZE.
  rewrite <- Z2Nat.inj_lt.

  set (Z.lt_le_trans _ _ _ H4 H5).
  auto.


  le0_solver.
  omega.
  rewrite <-Z2Nat.inj_succ; [idtac| le0_solver].
  unfold Z.succ.

  rewrite <- Z_div_plus_full.
  rewrite  Z2Nat.inj_iff.
  assert ( Int.unsigned x -4 + 1*4 = Int.unsigned x +4-4) by omega.
  rewrite H6.
  auto.

  le0_solver.
  le0_solver.
  omega.
  unfold OS_MAX_Q_SIZE.

  rewrite <- Z2Nat.inj_le.
  auto.

  le0_solver.
  le0_solver.
Qed.


Lemma math_ltu_false_false:
  forall x x4,
    0 < Int.unsigned x4 ->
    Int.unsigned x4 <= OS_MAX_Q_SIZE ->
    Int.ltu x ($ 4) = false ->
    (∘(Int.unsigned (Int.divu (x-ᵢ$ 4) ($ 4))) < ∘(Int.unsigned x4))%nat ->
    Int.modu (x-ᵢ$ 4) ($ 4) = $ 0 ->
    Int.ltu (x+ᵢ$ 4) ($ 4) = false /\ Int.modu ((x+ᵢ$ 4)-ᵢ$ 4) ($ 4) = $ 0.
Proof.
  intros.

  Iltu_simplerH H1.
  Imod_simplerH H3.
  unfold OS_MAX_Q_SIZE in *.

  unfold Int.divu, Int.sub in H2.
  repeat ur_rewriter_in H2.

  unfold nat_of_Z in H2.

  rewrite <- Z2Nat.inj_lt in H2; [idtac | le0_solver..].

  set (Z.lt_le_trans _ _ _ H2 H0).

  Zdivsup_simplerH l.


  split.
  int auto.
  ur_rewriter.
  omega.
  ur_rewriter.
  omega.


  unfold Int.modu, Int.add, Int.sub in *.
  repeat ur_rewriter_in H3.
  repeat ur_rewriter.

  Zmod_simplerH H3 1 (Int.unsigned x +4 -4).
  rewrite H3.
  auto.
Qed.



Lemma tcblist_p_indom_eq :
 forall v x y l1 l2, TCBList_P v x y l1 -> TCBList_P v x y l2 -> 
(forall a, TcbMod.indom l1 a <-> TcbMod.indom l2 a).
Proof.
  intros v x.
  gen v.
  induction x.
  intros.
  simpl in H.
  simpl in H0.
  subst.
  tauto.
  intros v y l1.
  intros.
  unfold TCBList_P in H; fold TCBList_P in H.
  simp join.
  unfold TCBList_P in H0; fold TCBList_P in H0.
  simp join.
  inverts H.
  rewrite H1 in H0.
  inverts H0.
  lets ab: IHx H7 H4.

  split.
  intro.
  assert ( a0 = x4 \/ a0 <> x4) by tauto.
  elim H0; intros.
  subst.
  unfold TcbMod.indom.
  eexists.

  eapply tcbjoin_get_a.
  exact H5.

  eapply join_indom_r.
  exact H5.
  apply ab.

  eapply join_indom_or in H2.
  Focus 2.
  exact H.

  elim H2.
  intros.
  unfold TcbMod.indom in H9.
  simp join.
  assert (x4 <> a0) by auto.
  eapply TcbMod.get_sig_none in H10.
  rewrite H10 in H9.
  inversion H9.
  tauto.

  intro.
  assert ( a0 = x4 \/ a0 <> x4) by tauto.
  elim H0; intros.
  subst.
  unfold TcbMod.indom.
  eexists.

  eapply tcbjoin_get_a.
  exact H2.

  eapply join_indom_r.
  exact H2.
  apply ab.

  eapply join_indom_or in H5.
  Focus 2.
  exact H.

  elim H5.
  intros.
  unfold TcbMod.indom in H9.
  simp join.
  assert (x4 <> a0) by auto.
  eapply TcbMod.get_sig_none in H10.
  rewrite H10 in H9.
  inversion H9.
  tauto.
Qed.


Lemma tcblist_p_sub_eq:
  forall l l1 l2 l1' l2' v x y,
    TcbMod.join l1 l2 l -> 
    TCBList_P v x y l1  ->
    TcbMod.join l1' l2' l ->
    TCBList_P v x y l1'->
    l2 = l2'.
Proof.
  intros.
  lets cond : tcblist_p_indom_eq H0 H2.
  assert (l1 = l1').
  eapply indom_eq_join_eq.
  auto.
  exact H.
  exact H1.
  subst.
  eapply TcbMod.join_unique_r.
  eauto.
  eauto.
Qed.

Lemma  math_le_int16:
  forall x0 (l:list msg)  m,
    Int.unsigned x0 = Z.of_nat (length l) ->
    (length l < ∘(Int.unsigned m))%nat ->
    Int.unsigned m <= OS_MAX_Q_SIZE ->
    Int.unsigned (x0+ᵢ$ 1) <= Int16.max_unsigned.
Proof.
  intros.
  unfold nat_of_Z in *.

  assert (Z.to_nat (Z.of_nat (length l)) = (length l))%nat  by (apply Nat2Z.id).
  rewrite <- H2 in H0.

  rewrite <- Z2Nat.inj_lt in H0.
  rewrite <- H in H0.

  set (Z.lt_le_trans _ _ _ H0 H1).

  unfold OS_MAX_Q_SIZE in *.

  int auto.
  unfold Int16.max_unsigned.
  unfold Int16.modulus.
  unfold Int16.wordsize.
  simpl.
  int auto.
  ur_rewriter.
  omega.
  le0_solver.
  le0_solver.
Qed.

Lemma  math_MN_max_prop:
  forall M N m, 
    M < N ->
    (∘M < ∘(Int.unsigned m))%nat ->
    (∘N < ∘(Int.unsigned m))%nat ->
    Int.unsigned m <= OS_MAX_Q_SIZE -> 
    (∘M <= ∘OS_MAX_Q_SIZE)%nat /\
    (∘N <= ∘(Int.unsigned m))%nat/\(∘(Int.unsigned m) <= ∘OS_MAX_Q_SIZE)%nat.
Proof.
  intros.
  unfold OS_MAX_Q_SIZE in *.
  unfold nat_of_Z in *.

  rewrite Z2Nat.inj_le in H2.
  split.
  omega.
  omega.
  le0_solver.
  omega.
Qed.



Lemma  math_MN_le_int16:
  forall M N m x0,
    M > N ->
    (∘M < ∘(Int.unsigned m))%nat ->
    (∘N < ∘(Int.unsigned m))%nat ->
    Int.unsigned m <= OS_MAX_Q_SIZE ->
    Int.unsigned x0 = Z.of_nat (∘M - ∘N) ->
    Int.unsigned (x0+ᵢ$ 1) <= Int16.max_unsigned  .
Proof.
  intros.
  unfold nat_of_Z in *.
  unfold Int16.max_unsigned.
  unfold Int16.modulus.
  unfold Int16.wordsize.
  simpl.
  unfold OS_MAX_Q_SIZE in *.

  unfold Int.add.
  repeat ur_rewriter.
  rewrite H3.

  rewrite Z2Nat.inj_le in H2; [idtac | le0_solver..].
  assert (Z.of_nat (Z.to_nat M - Z.to_nat N) <= Z.of_nat (Z.to_nat M)).
  apply Nat2Z.inj_le.

  apply NPeano.Nat.le_sub_l.

  rewrite Nat2Z.inj_lt in H0.
  rewrite Nat2Z.inj_le in H2.
  simpl in H2.

  omega.
  split.
  le0_solver.

  rewrite max_unsigned_val.
  rewrite H3.

  rewrite Z2Nat.inj_le in H2; [idtac | le0_solver..].
  assert (Z.of_nat (Z.to_nat M - Z.to_nat N) <= Z.of_nat (Z.to_nat M)).
  apply Nat2Z.inj_le.

  apply NPeano.Nat.le_sub_l.

  rewrite Nat2Z.inj_lt in H0.
  rewrite Nat2Z.inj_le in H2.
  simpl in H2.

  omega.
Qed.


Lemma math_MN_le_max:
  forall M N m ,
    M > N ->
    (∘M < ∘(Int.unsigned m))%nat ->
    (∘N < ∘(Int.unsigned m))%nat ->
    Int.unsigned m <= OS_MAX_Q_SIZE ->
    (∘N <= ∘M)%nat /\ (∘M <= ∘ OS_MAX_Q_SIZE )%nat/\(∘N <= ∘(Int.unsigned m))%nat  .
Proof.
  intros.
  unfold nat_of_Z, OS_MAX_Q_SIZE in *.
  rewrite Z2Nat.inj_le in H2; [idtac| le0_solver..].
  split; try omega.


  assert (N<=M) by omega.
  apply Zle_natle.
  auto.
Qed.


Lemma isptr_list_tail_add:
  forall x1 x0,
    isptr_list x1 ->
    isptr_list (x1 ++ Vptr x0 :: nil).
Proof.
  inductions x1.
  simpl.
  intros; splits; auto.
  unfolds.
  right; eauto.
  intros.
  simpl in H.
  destruct H as (His & Hip).
  apply IHx1 with x0 in Hip.
  simpl.
  split; auto.
Qed.


Lemma vallist_seg_upd_prop:
  forall  N M v2 x1 y,
    (N < length v2)%nat ->
    (N >= M)%nat ->
    vallist_seg M N v2 = x1 ->
    vallist_seg M (S N) (update_nth_val N v2 y ) =  x1 ++ (y :: nil).
Proof.
  inductions N.
  intros.
  assert (M=0)%nat.
  omega.
  subst M.
  unfolds in H1.
  simpl in H1.
  subst.
  simpl.
  unfolds.
  simpl.
  lets Hexs : list_gt_0_ex H.
  simp join.
  simpl.
  auto.
  intros.
  destruct M.
  unfolds in H1.
  simpl in H1.
  unfolds.
  simpl.
  destruct v2.
  simpl in H.
  omega.
  simpl in H.
  simpl.
  assert (N < length v2)%nat by omega.
  destruct x1.
  tryfalse.
  assert (vallist_seg 0 N v2 =x1).
  unfolds.
  simpl.
  inverts H1; auto.
  lets Heq : IHN y H2  H3.
  omega.
  unfolds in Heq.
  simpl in Heq.
  rewrite Heq.
  simpl.
  inverts H1.
  auto.
  destruct v2.
  simpl in H.
  omega.
  simpl in H.
  assert (N < length v2)%nat by omega.
  assert (N >= M )%nat by omega.
  unfolds in H1.
  simpl in H1.
  assert ( vallist_seg M N v2 = x1 ) by auto.
  lets Heqs : IHN y H2 H3 H4.
  auto.
Qed.

Lemma  vallist_pre_size_eq:
  forall size v2 x,
    (size <= length v2)%nat ->
    vallist_pre size v2 = x ->
    (length x = size).
Proof.
  inductions size.
  destruct v2.
  intros.
  simpl in H0.
  subst.
  simpl; auto.
  simpl.
  intros.
  subst.
  simpl; auto.
  intros.
  destruct v2.
  simpl in H.
  omega.
  simpl in H.
  assert (size <= length v2)%nat by omega.
  simpl in H0.
  destruct x.
  tryfalse.
  simpl.
  assert (vallist_pre size v2 = x).
  inverts H0; auto.
  eapply IHsize in H1; eauto.
Qed.


Lemma vallist_seg_length_prop:
  forall x y v2 ls,
    (x <= y)%nat ->
    (y <= length v2)%nat ->
    vallist_seg x y v2 = ls ->
    (length ls = y - x)%nat.
Proof.
  inductions x.
  intros.
  unfolds in H1.
  simpl in H1.

  lets Hz : vallist_pre_size_eq H1; eauto.
  rewrite Hz.
  omega.
  intros.
  destruct y.
  omega.
  destruct v2.
  simpl in H0.
  omega.
  assert (x <= y)%nat by omega.
  simpl in H0.
  assert (y <= length v2)%nat by omega.
  unfolds in H1.
  simpl in H1.
  lets Hsas : IHx H2 H3 H1.
  rewrite Hsas.
  omega.
Qed.

Lemma vallist_seg_length :
    forall N v2 x1 size,
      (S N  < size) %nat ->
      (size <= length v2) %nat ->
  vallist_seg (S N) size v2 ++ vallist_seg 0 N v2 = x1 ->
  (length x1 = size -1)%nat.
Proof.
  intros.
  remember (vallist_seg (S N) size v2) as ls1.
  remember ( vallist_seg 0 N v2 ) as ls2.
  rewrite <-H1.
  apply eq_sym in Heqls1.
  apply eq_sym in Heqls2.
  assert (S N <= size)%nat by omega.
  lets Hle :  vallist_seg_length_prop H2 H0 Heqls1.
  assert (0 <= N)%nat by omega.
  assert (N <= length v2)%nat by omega.
  lets Hle1 : vallist_seg_length_prop H3 H4 Heqls2.
  rewrite app_length.
  rewrite Hle.
  rewrite Hle1.
  omega.
Qed.



Lemma vallist_seg_upd_SM:
  forall M v2 y,
    (S M <= length v2)%nat ->
    vallist_seg M (S M) (update_nth_val M v2 y) = y::nil.
Proof.
  inductions M.
  destruct v2.
  simpl.
  intros; omega.
  intros.
  unfold vallist_seg.
  simpl.
  auto.
  destruct v2.
  intros.
  simpl in H.
  omega.
  intros.
  simpl in H.
  assert ( (S M) <= length v2)%nat.
  omega.
  lets Hk : IHM y H0.
  unfold vallist_seg.
  simpl.
  auto.
Qed.

Lemma vallist_seg_upd_irr:
 forall  N M  size v2 y,
   (M < N)%nat ->
   (N < size)%nat ->
   (size <= length v2)%nat ->
   vallist_seg N size v2 =
   vallist_seg N size (update_nth_val M v2 y).
Proof.
  inductions N.
  intros;
    destruct M;
    destruct size;try omega.
  intros.
  destruct M.
  destruct size; try omega.
  destruct v2.
  simpl in H1; try omega.
  simpl in H1.
  assert (N = 0 \/ 0 < N)%nat by omega.
  destruct H2.
  subst N.
  simpl.
  unfolds.
  simpl; auto.
  assert (N < size)%nat by omega.
  assert (size <= length v2)%nat by omega.
  lets Hres : IHN H2 H3 H4.
  unfolds.
  simpl.
  auto.
  destruct v2.
  simpl in H1.
  omega.
  destruct size.
  omega.
  simpl in H1.
  assert (M < N)%nat by omega.
  assert (N < size)%nat by omega.
  assert (size <= length v2)%nat  by omega.
  lets Heq : IHN y H2 H3 H4.
  unfolds.
  simpl.
  auto.
  Grab Existential Variables.
  exact y.
Qed.


Lemma math_prop_ltu_20:
  forall x x4,
    Int.unsigned x4 <= OS_MAX_Q_SIZE ->
    Int.ltu x ($ 4) = false ->
    Int.modu (x-ᵢ$ 4) ($ 4) = $ 0 ->
    (∘(Int.unsigned (Int.divu (x-ᵢ$ 4) ($ 4))) < ∘(Int.unsigned x4))%nat ->
    (Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4 < 20.
Proof.
  intros.

  int auto.
  unfold OS_MAX_Q_SIZE in H.
  simpl.
  unfold nat_of_Z in H2.
  rewrite <-  Z2Nat.inj_lt in H2.
  set (Z.lt_le_trans _ _ _ H2 H).
  auto.
  assert (4>0) by omega.

  cut ((Int.unsigned x -4)/ 4 >=0).
  intros.
  omega.
  apply Z_div_ge0.
  auto.
  int auto.
  int auto.
  int auto.
  int auto.
  int auto.
  destruct (zlt (Int.unsigned x) 4).
  inversion H0.
  split.
  omega.

  intrange x omega.

  destruct (zlt (Int.unsigned x) 4).
  inversion H0.
  split.
  omega.

  intrange x omega.

  rewrite Int.unsigned_repr.
  rewrite Int.unsigned_repr.
  split.

  destruct (zlt (Int.unsigned x) 4).
  inversion H0.
  cut ((Int.unsigned x -4)/ 4 >=0).
  intros.
  omega.
  apply Z_div_ge0.
  omega.
  omega.

  cut (Int.unsigned x -4 <= 4294967295).
  intro.
  rewrite <- (Z_div_mult_full  4294967295 4) .
  apply Z_div_le.
  omega.
  omega.
  omega.
  intrange x omega.
  unfold Int.max_unsigned, Int.modulus; simpl.
  omega.
  split.
  destruct (zlt (Int.unsigned x) 4).
  inversion H0.
  omega.
  unfold Int.max_unsigned, Int.modulus; simpl.
  intrange x omega.
Qed.


Lemma math_prop_divu_zle:
  forall x3 i,
    Int.unsigned x3 <= OS_MAX_Q_SIZE ->
    Int.ltu i ($ 4) = false ->
    (∘(Int.unsigned (Int.divu (i-ᵢ$ 4) ($ 4))) < ∘(Int.unsigned x3))%nat ->
    (Int.unsigned i - 4) / 4 < OS_MAX_Q_SIZE.
Proof.
  intros.
  unfold OS_MAX_Q_SIZE in *.
  unfold Int.ltu in H0.
  bfunc_invert' H0.
  ur_rewriter_in g.
  unfold nat_of_Z in *.
  unfold Int.divu, Int.sub in H1.
  repeat ur_rewriter_in H1.
  rewrite <- Z2Nat.inj_lt in H1.
  omega.
  revs.
  apply Z_div_ge0.
  omega.
  omega.
  intrange x3 omega.
Qed.


Lemma math_prop_divu_ltmod:
  forall x3 i2,
    0 < Int.unsigned x3 ->
    Int.unsigned x3 <= OS_MAX_Q_SIZE ->
    ∘(Int.unsigned (Int.divu (i2-ᵢ$ 4) ($ 4))) = ∘(Int.unsigned x3) ->
    Int.ltu i2 ($ 4) = false ->
    Int.modu (i2-ᵢ$ 4) ($ 4) = $ 0 -> 
    i2 =  Int.mul x3 ($ 4)+ᵢ$ 4.
Proof.
  intros.
  apply (int_minus4_mod4 H2) in H3.
  unfold Int.ltu in H2.
  bfunc_invert' H2.
  ur_rewriter_in g.
  unfold nat_of_Z in H1.
  apply Z2Nat.inj_iff in H1.
  unfold Int.divu, Int.sub in H1.
  unfold OS_MAX_Q_SIZE in H0.
  repeat ur_rewriter_in H1.
  unfold Int.mul, Int.add.
  repeat ur_rewriter.
  rewrite <- H1.
  rewrite Z.mul_comm.
  rewrite <- Z_div_exact_full_2.
  assert ( Int.unsigned i2 -4 +4 = Int.unsigned i2) by omega.
  rewrite H4.
  symmetry.
  apply Int.repr_unsigned.
  omega.
  auto.
  auto.
  unfold Int.divu, Int.sub.
  repeat ur_rewriter.
  revs.
  apply Z_div_ge0; omega.
  omega.
Qed.

Lemma TCBList_merge_prop:
  forall y1 x1 a b c z x2 y2,
    TcbMod.join a b c ->
    V_OSTCBNext (last y1 nil) = Some x2 ->
    TCBList_P x1 y1 z a  ->
    TCBList_P  x2 y2 z b ->
    TCBList_P x1 (y1++y2) z c .
Proof.
  inductions y1.
  intros.
  simpl in *.
  unfolds in H0; simpl in H0;inverts H0.
  intros.
  assert (y1 = nil \/ y1 <> nil).
  tauto.
  destruct H3.
  subst.
  simpl.
  simpl in H0.
  simpl in H1.
  simp join.
  rewrite H0 in H3.
  inverts H3.
  do 4 eexists; splits; eauto.
  unfolds in H4.
  apply TcbMod.join_comm in H4.
  apply TcbMod.join_emp_eq in H4.
  subst a0.
  auto.
  simpl.
  simpl in H1.
  simp join.
  rewrite last_remain in H0; auto.
  lets Hex : tcbjoin_join_ex2 H5 H.
  simp join.
  lets Hsz :  IHy1  H1 H0  H2; eauto.
  do 4 eexists; splits; eauto.
  unfold TcbJoin in *.
  unfold join, sig in *; simpl in *; auto.
Qed.

Require Import Coq.Logic.FunctionalExtensionality.

Lemma isr_is_prop_emp:
  forall i ir, isr_is_prop (isrupd ir i false) (i :: nil) -> (isrupd ir i false) = empisr.
Proof.
  intros.
  unfold isr_is_prop in H.
  simpl in H.
  apply functional_extensionality.
  intros.
  unfold empisr.
  assert (i=x\/i<>x) by tauto.
  destruct H0.
  unfold isrupd.
  rewrite <- beq_nat_true_iff in H0.
  rewrite H0.
  auto.
  apply H.
  intro.
  destruct H1.
  tryfalse.
  false.
Qed.

Lemma a_isr_is_prop_split:
  forall s P isr is, s |= Aisr isr ** Ais is ** A_isr_is_prop ** P -> s |= Aisr isr ** Ais is ** P ** [| isr_is_prop isr is |].
Proof.
  introv Hsat.
  unfold A_isr_is_prop in Hsat.
  destruct_s s.
  sep normal in Hsat.
  sep auto.
Qed.

Lemma retpost_osev :  retpost OS_EventSearchPost.
Proof.
  unfolds.
  intros.
  unfold OS_EventSearchPost in H.
  unfold OS_EventSearchPost' in H.
  unfold getasrt in H.
  destruct H.
  sep destroy H.
  subst.
  intro Hf;  false.
  sep destroy H.
  simp join.
  intro Hf; false.
Qed.
(*
Definition prio_neq_cur tcbls curtid curprio :=
  forall tid prio st m, 
    tid <> curtid -> 
    TcbMod.get tcbls tid = Some (prio, st, m) ->
    prio <> curprio.
*)


Lemma abst_disj_merge_set_eqq : forall (x y : absdatastru.B) (id : absdataidspec.A)
         (O Of : OSAbstMod.map),
    disjoint O Of ->
    get O id = Some x ->
    merge Of (set O id y)  =
    set (merge Of O) id y.
Proof.
  intros.
  rewrite disjoint_merge_sym.
  assert (merge Of O =merge O Of).
  apply disjoint_merge_sym.
  apply disjoint_sym.
  auto.
  rewrite H1.
  destruct H.
  eapply  join_merge_set_eq;eauto.
  unfolds; simpl; auto.
  apply disjoint_sym.
  eapply abst_get_set_disj; eauto.
Qed.

Definition array_struct t :=
  (exists t1 n, t = Tarray t1 n) \/ (exists id dl, t = Tstruct id dl) \/ ( t = Tvoid).

Lemma  tarray_tvoid :
  forall t , ~array_struct t  -> typelen t <> 0%nat.
Proof.
  inductions t; introv Hs Hf; simpl in *; tryfalse.
  unfold array_struct in Hs.
  apply Classical_Prop.not_or_and  in Hs.
  destruct Hs.
  apply Classical_Prop.not_or_and  in H0.
  destruct H0.
  tryfalse.
  apply Hs.
  unfolds.
  branch 1.
  do 2 eexists; eauto.
  apply Hs.
  branch 2.
  do 2 eexists; eauto.
Qed.

Lemma type_encode_nnil :
  forall t v,  ~array_struct t  -> encode_val t v <> nil.
Proof.
  inductions t; unfold encode_val in *;
  try solve [destruct v; simpl in *; intuition (try destruct a; tryfalse)].
  intros.
  false.
  apply H.
  branch 3; eauto.
  intros.
  false.
  apply H.
  branch 1; 
    do 2 eexists; eauto.
  intros.
  false.
  apply H.
  branch 2; 
    do 2 eexists; eauto.
Qed.

Require Import join_lib.
Lemma ptomval_nnil_neq_auto :
  forall (A B T : Type) (MC : PermMap A B T) x1 x2 m b1 b2 a1 a2 x4 x0,
    usePerm = true ->
    join x1 x2 m ->
    isRw b1 = true ->
    isRw b2 = true ->
    join (sig a1 b1) x4 x1 ->
    join (sig a2 b2) x0 x2 ->
    a1 <> a2.
  intros.
  let l := calc_ins in
  infer' l a1; crush.
Qed.


Lemma ptomval_nnil_neq:
  forall v1 v2 x y  x1 x2 m,
    v1 <> nil ->
    v2 <> nil ->
    join x1 x2 m ->
    ptomvallist x true v1 x1 ->
    ptomvallist y true v2 x2 ->
    x <> y.
Proof.
  introv Hn1 Hn2 Hj  Hpto1 Hpto2.
  destruct v1; destruct v2; tryfalse.
  unfolds in Hpto1.
  unfolds in Hpto2.
  destruct x.
  destruct y.
  simp join.
  unfold ptomval in *.
  subst.
  eapply ptomval_nnil_neq_auto with (b1 := (true, m0)) (b2 := (true, m1)); auto.
  exact Hj.
  eauto.
  eauto.
Qed.  
(*
  apply MemMod.join_sub_l in H.
  apply MemMod.join_sub_l in H0.
  subst x3.
  subst x.
  eapply join_sub_sub_sig_neq; eauto.
Qed.
*)

Lemma pv_false :
  forall s x y t1 t2 v1 v2 P,
   ~array_struct t1 ->
      ~ array_struct t2 ->
    s  |= PV  x @ t1 |-> v1 ** PV y  @ t2 |-> v2 ** P-> x <> y.
Proof.
  introv Ht1 Ht2 H.
  sep lift 3%nat in H.
  assert (x = y \/ x <> y) by tauto.
  destruct H0; auto; subst y.
  remember ( PV x @ t1 |-> v1 ** PV x @ t2 |-> v2) as Hs.
  sep destroy H.
  subst.
  destruct_s x1.
  simpl in H1.
  simp join.
  unfolds in H4.
  unfolds in H5.
  simp join.
  remember (addrval_to_addr x)  as xx.
  lets Hneq1 : type_encode_nnil v1 Ht1.
  lets Hneq2 : type_encode_nnil v2 Ht2.
  lets Hz :  ptomval_nnil_neq H5 H4; eauto.
Qed.

Lemma astruct_neq_ptr : forall s x id1 t1 d1 id2 t2 d2 v1 y  v2 P a b,
                          ~array_struct t1 ->
                          ~ array_struct t2 ->
                          s |= Astruct x (STRUCT id1 ­{ dcons a t1 d1 }­) v1
                            ** Astruct y (STRUCT id2 ­{ dcons b t2 d2 }­) v2 ** P -> x <> y .
Proof.
  intros.
  unfold Astruct in H1.
  sep lift 3%nat in H1.
  remember ( Astruct' x (dcons a t1 d1) v1 ** Astruct' y (dcons b t2 d2) v2) as Hr.
  sep destroy H1.
  subst Hr.
  destruct v1; destruct v2; simp join;          
  try solve [simpl in H3; simp join; tryfalse].
  unfold Astruct' in H3; fold Astruct' in H3.
  destruct t1; destruct  x ; destruct t2; destruct y;
  sep lower 2%nat in H3; try solve [eapply pv_false in H3  ;eauto;tryfalse];
  try solve [false; apply H0; branch 1; do 2 eexists; eauto];
  try solve [false; apply H0; branch 2;  do 2 eexists; eauto];
  try solve [false; apply H0; branch 3; eauto];
  try solve [false; apply H; branch 1; do 2 eexists; eauto];
  try solve [false; apply H; branch 2;  do 2 eexists; eauto];
  try solve [false; apply H; branch 3; eauto].
Qed.

Lemma ecbf_sllseg_isptr : forall s P v1 v2 t f, s |= ecbf_sllseg v1 Vnull
                                                  v2 t  f ** P -> isptr v1.
Proof.
  intros.
  gen v1 t f P.
  inductions v2.
  unfold ecbf_sllseg.
  intros.
  sep split in H.
  subst v1.
  unfolds; auto.
  intros.
  unfold  ecbf_sllseg in H.
  fold ecbf_sllseg in H.
  sep destruct  H.
  unfold node in H.
  sep destroy H.
  destruct H0.
  subst v1.
  unfolds;  eauto.
Qed.

Lemma evsllseg_get_last_eq :
  forall ls1 head tail ls2 s,  ls1 <> nil ->
                               s |= evsllseg head tail ls1 ls2 -> get_last_ptr ls1 = Some tail.
Proof.
  inductions ls1.
  simpl.
  intros.
  tryfalse.
  intros.
  destruct a.
  unfold get_last_ptr.
  simpl.
  destruct ls1.
  simpl in H0.
  destruct ls2.
  simpl in H0.
  tryfalse.
  simpl in H0.
  simp join.
  auto.
  remember (e::ls1) as Ht.
  unfold  evsllseg in H0 at 1.
  fold evsllseg in H0.
  subst Ht.
  destruct ls2.
  simpl in H0.
  tryfalse.
  sep destroy H0.
  eapply IHls1.
  introv Hf.
  tryfalse.
  eauto.
Qed.

Lemma evsllseg_merge :
  forall l1 l1' l2 l2' x1  x2 y s P,
    length l1 = length l1' ->
    length l2 = length l2' -> 
    s |= evsllseg x1 y l1 l1' ** evsllseg y x2 l2 l2' ** P->
    s |= evsllseg x1 x2 (l1++l2) (l1'++l2') **P.
Proof.
  inductions l1.
  intros.
  destruct l1'.
  simpl evsllseg in *.
  sep split in H1.
  simp join.
  auto.
  simpl in H.
  omega.
  intros.
  destruct l1'.
  simpl in H; omega.
  simpl in H.
  inverts H.
  rewrite <- app_comm_cons.
  rewrite <-  app_comm_cons.
  unfold evsllseg in *; fold evsllseg in *.
  destruct a.
  sep normal.
  sep normal in H1.
  destruct H1.
  exists x.
  sep lower 1%nat.
  sep lower 1%nat.
  eapply IHl1; eauto.
  sep auto.
Qed.

Lemma Aarray_vl_len_eq: 
  forall vl s n t P l, 
    s |=  Aarray l (Tarray t n) vl ** P -> length vl = n.
Proof.
  unfold Aarray.
  induction vl;intros.
  destruct n.
  auto.
  unfold Aarray' in H;fold Aarray' in H.
  simpl in H;simp join;false.
  destruct n.
  unfold Aarray' in H;fold Aarray' in H.
  simpl in H;simp join;false.
  simpl.
  assert (length vl = n).
  unfold Aarray' in H;fold Aarray' in H.
  destruct l.
  assert ( s
             |= (
               Aarray' (b, i +ᵢ $ Z.of_nat (typelen t)) n t vl) ** P ** PV (b, i) @ t |-> a ).
  sep auto.
  eapply IHvl;eauto.
  auto.
Qed.

Lemma Aarray_vl_len_eq': 
  forall vl s n t P l, 
    s |=  Aarray l (Tarray t n) vl ** P -> s|= Aarray l (Tarray t n) vl ** P **[|length vl = n|].
Proof.
  intros.
  sep auto.
  eapply Aarray_vl_len_eq;eauto.
Qed.

Lemma sep_pure_split:forall s P A, s|=[|P|]**A -> (P /\ s|=A).
Proof.
  intros.
  split;sep_auto.
  simpl in H.
  do 6 destruct H.
  destructs H.
  destruct H3.
  auto.
Qed.

Lemma sep_pure_get:forall s P A, s|=[|P|]**A -> (P /\ s|= [|P|] ** A).
Proof.
  intros.
  split;sep_auto.
  simpl in H.
  do 6 destruct H.
  destructs H.
  destruct H3.
  auto.
Qed.


Lemma absimp_pre_compose: forall p1 p2 q x,
                            absinfer x p1 q -> absinfer  x p2 q -> absinfer x (p1\\//p2) q.
Proof.
  intros.
  eapply absinfer_conseq with (q := (q \\//q)) (p :=p1 \\// p2 ).
  intros.
  destruct H1; auto.
  eapply absinfer_disj; auto.
  auto.
Qed.

Lemma absimp_conseq_pre: forall p q p' x,
	 absinfer x p q -> p'==>p -> absinfer x  p' q.
Proof.
  intros.
  eapply absinfer_conseq with (p:=p) (q:=q); auto.
Qed.

Lemma absimp_conseq_post: 
	forall p q q' x, absinfer x p q -> q ==> q' -> absinfer x p q'.
Proof.
  intros.
  eapply absinfer_conseq with (p:=p) (q:=q); auto.
Qed.

Lemma absimp_pre_post_compose: 
	forall p1 p2 q1 q2 x,
                            absinfer x p1 q1 -> absinfer x p2 q2 -> absinfer x (p1\\//p2) (q1\\//q2).
Proof.
  intros.
  eapply absinfer_disj; auto.
Qed.

Lemma absimp_ex_intro:
  forall  (tp:Type) (p:tp->asrt) q xx, 
  	(forall x,absinfer xx (p x) q) -> absinfer xx  (EX x:tp,p x) q.
Proof.
  intros.
  eapply absinfer_ex ; eauto.
Qed.


Lemma evsllseg_add_head: forall head tailnext vl ecbl s P tl l x msgq, V_OSEventListPtr l = Some head -> s|= AEventNode tl l x msgq ** evsllseg head tailnext vl ecbl ** P -> s|= evsllseg tl tailnext ((l, x) :: vl) (msgq ::ecbl) ** P.
  intros.
  unfold evsllseg in *.
  sep auto.
Qed.


Lemma evsllseg_app: 
forall head mid vl0 ecbl0 tail vl1 ecbl1 P s,
	 s|= evsllseg head mid vl0 ecbl0 ** evsllseg mid tail vl1 ecbl1 ** P -> s|= evsllseg head tail (vl0++vl1) (ecbl0++ecbl1) ** P.
Proof.
  intros h m vl.
  generalize h.
  clear h.
  induction vl.
  intros.
  destruct ecbl0.
  sep auto.
  simpl.
  unfold evsllseg in *.
  sep auto.
  inversion H0.
  subst.
  sep auto.
  sep destroy H.
  simpl in H0.
  inversion H0.
  inversion H1.
  inversion H5.

  intros.
  induction ecbl0.
  sep destroy H.
  unfold evsllseg in H0.
  inversion H0.
  unfold evsllseg in *.
  simpl ( (fix evsllseg (head tailnext : val) (vl0 : list EventCtr)
                  (ecbls : list EventData) {struct vl0} : asrt :=
       match vl0 with
       | nil => [|head = tailnext /\ ecbls = nil|]
       | l :: vl' =>
           match ecbls with
           | nil => Afalse
           | enode :: ecbls' =>
               let (osevent, etbl) := l in
               EX vn : val,
               [|V_OSEventListPtr osevent = Some vn|] **
               AEventNode head osevent etbl enode **
               evsllseg vn tailnext vl' ecbls'
           end
       end) h tail ((a :: vl) ++ vl1) ((a0 :: ecbl0) ++ ecbl1) ** P) .
  fold evsllseg in *.
  destruct a.
  sep normal.
  sep auto.
  apply astar_r_aemp_intro  in H.
  sep normal in H.
  lets Has : IHvl H.
  sep auto.
  auto.
Qed.

Lemma evsllseg_compose:
  forall s P (qptrl:list EventCtr) l x p msgqls tail vn qptrl1 qptrl2 msgqls1 msgqls2 tl msgq, 

    V_OSEventListPtr l = Some vn ->
    qptrl = qptrl1 ++ ((l,x)::nil) ++ qptrl2  ->
    msgqls = msgqls1 ++ (msgq::nil) ++msgqls2 ->
    s |= AEventNode tl l x msgq **
      evsllseg p tl qptrl1 msgqls1 **
      evsllseg vn tail qptrl2 msgqls2 ** P ->
    s |= evsllseg p tail qptrl msgqls ** P.
Proof.
  intros.
  idtac.
  sep lifts (1::3::nil)%nat in H2.
  apply evsllseg_add_head in H2.
  sep lifts (2::1::nil)%nat in H2.
  subst.
  eapply evsllseg_app.
  sep auto.
  auto.
Qed.

Lemma elim_a_isr_is_prop:
  forall P, Aisr empisr ** Ais nil ** A_isr_is_prop ** P ==> Aisr empisr ** Ais nil ** P.
Proof.
  intros.
  sep auto.
  simpl.
  unfold A_isr_is_prop in H.
  sep auto.
Qed.

Lemma add_a_isr_is_prop:
  forall P, Aisr empisr ** Ais nil ** P ==> Aisr empisr ** Ais nil ** A_isr_is_prop ** P.
Proof.
  intros.
  unfold A_isr_is_prop.
  sep normal.
  sep auto.
  rewrite H0.
  rewrite H1.
  unfolds.
  intros.
  auto.
Qed.

Lemma tcbdllseg_compose:
  forall s P h hp t1 tn1 t2 tn2 l1 l2,
    s |= tcbdllseg h hp t1 tn1 l1 ** tcbdllseg tn1 t1 t2 tn2 l2 ** P->
    s |= tcbdllseg h hp t2 tn2 (l1++l2) ** P.
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
  apply astar_r_aemp_elim.
  eapply IHl1.
  sep auto.
  auto.
Qed.

Lemma evsllseg_isptr : forall {p1 l1 l2 s P},
                            s |= evsllseg p1 Vnull l1 l2 ** P -> isptr p1.
Proof.
  intros.
  destruct_s s.
  simpl in H; simp join.
  destruct l1; simpl in H3; simp join.
  unfolds; auto.
  destruct l2; tryfalse.
  unfold AEventNode in H3.
  destruct e1.
  unfold AOSEvent in H3.
  unfold node in H3.
  sep normal in H3.
  sep destruct H3.
  sep split in H3.
  simp join.
  unfold isptr; simpl.
  right; eauto.
Qed.

(** astruct_neq_ptr **)
Lemma sep_ptr_neq_OS_EVENT : forall p1 vl1 p2 vl2 s P,
  s |= Astruct p1 OS_EVENT vl1 ** Astruct p2 OS_EVENT vl2 ** P ->
  p1 <> p2.
Proof.
  intros.
  unfold OS_EVENT in H.
  eapply astruct_neq_ptr.
  Focus 3.
  eauto.
  unfold not; intros.
  unfold array_struct in H0.
  destruct H0 as [? | [? | ?]]; heat; tryfalse.
  unfold array_struct; intros.
  unfold not.
  intros.
  destruct H0 as [? | [? | ?]]; heat; tryfalse.
Qed.                           

Lemma evsllseg_list_len_eq : forall l1 l2 p1 p2 s P,
  s |= evsllseg p1 p2 l1 l2 ** P -> length l1 = length l2.
Proof.
  intro.
  inductions l1; intros.
  simpl in H; simp join.
  simpl; auto.
  destruct l2.
  simpl in H; simp join; tryfalse.
  simpl.
  simpl evsllseg in H.
  destruct a.
  sep pure.
  sep remember (1::nil)%nat in H.
  destruct_s s; simpl in H; simp join.
  assert(length l1 = length l2).
  eapply IHl1; eauto.
  auto.
Qed.

Require Import derived_rules.
Lemma disj_conj_distrib_pre : forall (P Q R S: asrt) s a b c d sc x tid, 
                  {|a, b, c, d, sc, x|} |-tid {{(P//\\R)\\//(Q//\\R)}} s {{S}} ->
                  {|a, b, c, d, sc,x|} |-tid {{(P\\//Q)//\\R}} s {{S}}.
Proof.
  intros.
  eapply backward_rule1 with (p := ((P //\\ R) \\// (Q //\\ R))).
  intros.
  destruct H0.
  destruct H0.
  left; split; auto.
  right; split; auto.
  auto.
Qed.

Lemma topis_0_imp:
  forall s x si P,
    s|=ATopis x **  Ais (0%nat::si) **  P ->
    x =0%nat.
Proof.
  intros.
  destruct_s s.
  simpl in *;simp join.
  simpl.
  auto.
Qed.

Lemma isrclr_imp :
  forall P,
    isrclr ** P ==> Aisr empisr ** P.
Proof.
  intros.
  sep auto.
  simpl in H.
  simp join.
  simpl;auto.
  destruct_s s.
  simpl in H.
  simp join.
  simpl.
  unfold empisr.
  apply functional_extensionality_dep.
  auto.
Qed.

Lemma imp_isrclr:
  forall P,
    Aisr empisr ** P ==>  isrclr ** P.
Proof.
  intros.
  destruct_s s.
  simpl in *.
  simp join.
  exists empmem m m empabst o o.
  splits;simp join.
  exists (empisr).
  splits;simp join.
  splits; auto.
  unfolds.
  auto.
  intros.
  unfold empisr;auto.
  unfolds; auto.
  simp join.
  unfolds in H6.
  subst.
  join auto.  
Qed.

Lemma topis_nil:forall s x P ,s |= ATopis x **  Ais nil ** P -> x = INUM.
Proof.
  intros.
  destruct_s s;simpl in *;simp join.
  simpl.
  auto.
Qed.

Lemma atopis_pure:forall s P x, s|= ATopis x ** P -> s|= P.
Proof.
  intros.
  sep auto.
Qed.

Lemma tcbblk_prio_range:
  forall a p,
    RL_TCBblk_P a ->
    V_OSTCBPrio a = Some (Vint32 p) ->
    0<= Int.unsigned p < 64.
Proof.
  intros.
  unfolds in H.
  simp join.
  rewrite H in H0.
  inverts H0.
  auto.
 Qed.

Fixpoint get_eid_list' (vll:list EventCtr):=
  match vll with
    | nil => nil
    | (vl,x)::vll' => (nth_val' 5%nat vl) :: (get_eid_list' vll')
  end.

Definition get_eid_list (head:val) (vll:list EventCtr):=
  head:: (List.removelast (get_eid_list' vll)).

Definition vl_elem_neq (l:vallist):= forall n m vn vm,nth_val n l = Some vn -> nth_val m l = Some vm -> n <> m -> vn <> vm.


Lemma nth_val_nth_val'_some_eq : forall n vl x,
  nth_val n vl = Some x -> nth_val' n vl = x.
Proof.
  inductions n; intros.
  destruct vl; simpl in H; tryfalse.
  unfolds; simpl; inverts H; auto.

  simpl.
  destruct vl; simpl in H; tryfalse.
  apply IHn in H; auto.
Qed.


(*
move to join_lib
Lemma join_merge : forall {m1 m2 m3:mem}, join m1 m2 m3 -> m3 = merge m1 m2.
Proof.
(* Admitted. *)
*)
(*
  intros.
  apply extensionality.
  intros.
  rewrite merge_sem.
  unfold join in H; pose proof H a; clear H.
  destruct (get m1 a);
  destruct (get m2 a);
  destruct (get m3 a);
  subst; auto;
  inversion H0.
Qed.
*)
 
 (*
Lemma disj_join_disj : forall {m1 m2 m3 m4 m5 m6:mem},
  join m1 m2 m3 -> join m4 m5 m6 -> disj m3 m6 ->
  disj m1 m4.
Proof.
  intros.
  pose proof join_merge H.
  pose proof join_merge H0.
  subst.
  pose proof disj_merge_elim_lr H1.
  destruct H2.
  destruct H2.
  apply disj_sym.
  auto.
Qed.
*)

Lemma length_encode_val : 
	forall t v, (typelen t > 0)%nat -> (length (encode_val t v) > 0)%nat.
Proof.
  intros.
  destruct t; destruct v;
  try solve [simpl; try (destruct a); auto];
  try solve [simpl in H; simpl; try (destruct a); destruct (typelen t * n)%nat; [omega | simpl; omega]];
  try solve [simpl in H; simpl; try (destruct a); destruct (szstruct d); [omega | simpl; omega]].
Qed.


Lemma length_exists: 
	forall {A:Type} (l: list A), (length l > 0)%nat -> exists h t, l = h :: t.
Proof.
  intros.
  destruct l.
  simpl in H; omega.
  eauto.
Qed.

(*
Lemma mapstoval_disj_false : 
	forall a t v1 v2 m1 m2,
  (typelen t > 0)%nat -> 
  	mapstoval a t v1 m1 -> 
   	mapstoval a t v2 m2 ->
    	 MemMod.disj m1 m2 ->
  False.
Proof.
  intros.
  unfold mapstoval in *; simp join.



  intros.
  pose proof length_encode_val v1 H.
  pose proof length_encode_val v2 H.


  pose proof length_exists H1.
  pose proof length_exists H0.
  simp join.
  rewrite H5 in H3.
  rewrite H6 in H4.
  simpl in H3; destruct a.
  simpl in H4.
  simp join.
  unfolds in H9.
  unfolds in H7.
  substs.
  unfolds in H2.
  pose proof H2 (b, o); clear H2.
  unfolds in H4; pose proof H4 (b, o); clear H4.
  unfolds in H3; pose proof H3 (b, o); clear H3.
  rewrite MemMod.get_sig_some in *.
  destruct (MemMod.get m1 (b, o));
  destruct (MemMod.get m2 (b, o));
  destruct (MemMod.get x4 (b, o));
  destruct (MemMod.get x6 (b, o));
  tryfalse.
Qed.
*)


Lemma Astruct_sll_OS_TCB_dup_false:
  forall (p : addrval) a1 a2 (P : asrt) (s : RstateOP),
    s |= Astruct p OS_TCB_flag a1** sll (Vptr p) a2 OS_TCB_flag V_OSTCBNext** P -> False.
Proof.
  intros.
  destruct a2.
  unfold sll in H.
  simpl sllseg in H.
  sep split in H.
  tryfalse.

  unfold sll in *.
  unfold1 sllseg in H.
  unfold node in H.
  sep normal in H.
  sep destruct H.
  sep split in H.
  sep lifts (1::3::nil)%nat in H. 
  heat.
  inverts H0.

  eapply inv_prop.struct_type_vallist_match_os_tcb_flag in H3.
  heat.
  sep lift 2%nat in H.
  unfold Astruct in H.
  unfold OS_TCB_flag in H.
  unfold Astruct' in H.
  destruct a1.
  (* ** ac: SearchAbout (_ |= Afalse ** _). *)
  eapply astar_l_afalse_elim in H.
  simpl in H; auto.

  destruct a1.
  sep normal in H.
  sep lift 2%nat in H.
  eapply astar_l_afalse_elim in H.
  simpl in H; auto.

  destruct a1.
  sep normal in H.
  sep lift 3%nat in H.
  eapply astar_l_afalse_elim in H.
  simpl in H; auto.

  destruct a1.
  sep normal in H.
  sep lift 4%nat in H.
  eapply astar_l_afalse_elim in H.
  simpl in H; auto.

  destruct a1.
  sep normal in H.
  sep lift 5%nat in H.
  eapply astar_l_afalse_elim in H.
  simpl in H; auto.

  sep normal in H.
  sep lift 5%nat in H.
  sep lift 11%nat in H.

  (* ** ac: Check pv_false. *)
  remember (x0,
            (((Int.zero +ᵢ  $ Z.of_nat (typelen STRUCT os_tcb ⋆))
              +ᵢ  $ Z.of_nat (typelen STRUCT os_tcb ⋆)) +ᵢ
             $ Z.of_nat (typelen OS_EVENT ∗)) +ᵢ
            $ Z.of_nat (typelen (Void) ∗)) as xx.
  assert (xx <> xx).
  {
    eapply pv_false.
    3: eauto.
    unfold not.
    intros.
    unfold array_struct in H0.
    destruct H0 as [? | [? | ?]]; heat; inverts H0.
    
    unfold not.
    intros.
    unfold array_struct in H0.
    destruct H0 as [? | [? | ?]]; heat; inverts H0.
  }
  tryfalse.
Qed.

Lemma Astruct_osevent_dup_false :
  forall p v1 v1' s,
    s |= Astruct p OS_EVENT v1 ** Astruct p OS_EVENT v1' -> False.
Proof.
  intros.
  eapply sep_lemmas_ext.StarEmpIR in H.
  assert (p <> p).
  {
    eapply sep_ptr_neq_OS_EVENT.
    sep normal in H.
    eauto.
  }
  tryfalse.
Qed.


Lemma Astruct_osevent_dup_false' :
  forall p v1 v1' s P,
    s |= Astruct p OS_EVENT v1 ** Astruct p OS_EVENT v1' ** P -> False.
Proof.
  intros.
  destruct_s s.
  sep remember (3::nil)%nat in H.
  simpl in H; simp  join.
  eapply Astruct_osevent_dup_false; eauto.
Qed.

Lemma AEventNode_dup_false :
  forall p v1 v2 v3 v4 e1 e2 P s,
    s |= AEventNode p v1 v2 e1 ** AEventNode p v3 v4 e2 ** P ->
    False.
Proof.
  intros.
  unfold AEventNode in H.
  unfold AOSEvent in H.
  unfold node in H.
  sep pure; simp join; substs.
  inverts H4.
  sep lift 3%nat in H.
  eapply Astruct_osevent_dup_false'; eauto.
Qed.

Lemma aeventnode_evsllseg_get_neq : forall ectrl edatal head head' n v v0 e x tail s P,
  s |= AEventNode head v v0 e ** evsllseg head' tail ectrl edatal ** P-> ectrl <> nil ->
  nth_val n (get_eid_list head' ectrl) = Some x -> head <> x.
Proof.
  intros.
  destruct ectrl; tryfalse.

  clear H0.
  gen e0 edatal head head' n v v0 e x tail.
  gen s P.
  inductions ectrl; intros.
  simpl in H1.
  destruct n.
  inverts H1.
  unfold evsllseg in H.
  destruct e0.
  destruct edatal.
  simpl in H; simp join; tryfalse.
  sep pure.
  destruct H1; substs.
  intro; substs.
  eapply AEventNode_dup_false; eauto.
  destruct e0.
  simpl in H1; tryfalse.
  destruct n.
  simpl in H1; inverts H1.
  destruct edatal.
  unfold evsllseg in H; simpl in H; simp join; tryfalse.
  unfold evsllseg in H; fold evsllseg in H.
  destruct e0.
  destruct edatal.
  sep pure; simpl in H; simp join; tryfalse.
  destruct a; sep pure.
  intro; substs.
  sep lifts (3::4::nil)%nat in H.
  eapply AEventNode_dup_false; eauto.
  destruct edatal.
  unfold evsllseg in H; simpl in H; simp join; tryfalse.
  unfold evsllseg in H; fold evsllseg in H.
  destruct e0.
  destruct edatal.
  sep pure; simpl in H; simp join; tryfalse.
  sep pure.
  destruct a.
  sep pure.
  pose proof IHectrl s (AEventNode head' v1 v2 e1 ** P) (v3, v4) (e0:: edatal) head  x0 n v v0 e x; clear IHectrl.
  simpl in H1.
  unfolds in H0.
  destruct v1; simpl in H0; tryfalse.
  destruct v5; simpl in H0; tryfalse.
  destruct v3; simpl in H0; tryfalse.
  destruct v6; simpl in H0; tryfalse.
  destruct v8; simpl in H0; tryfalse.
  destruct v9; simpl in H0; tryfalse.
  destruct v10; simpl in H0; tryfalse.
  simpl nth_val in H3.
  inverts H0.
  pose proof H3 H1 tail; clear H3.
  apply H0; clear H0.
  unfold evsllseg; fold evsllseg.
  sep auto.
Qed.

Lemma aeventnode_evsllseg_get_neq' : forall ectrl edatal head head' n v v0 e x tail s,
  s |= AEventNode head v v0 e ** evsllseg head' tail ectrl edatal -> ectrl <> nil ->
  nth_val n (get_eid_list head' ectrl) = Some x -> head <> x.
Proof.
  intros.
  assert (s |= AEventNode head v v0 e ** evsllseg head' tail ectrl edatal ** Aemp).
  sep auto.
  clear H.
  eapply aeventnode_evsllseg_get_neq; eauto.
Qed.


(*end of the candidate lemmas*)
Lemma evsllseg_eid_neq:
  forall ectrl edatal head tail s P, s |= evsllseg head tail ectrl edatal ** P -> vl_elem_neq (get_eid_list head ectrl).
Proof.
   inductions ectrl; intros.
  simpl in H; simp join.
  unfolds; intros.
  unfold get_eid_list in H.
  unfold get_eid_list' in H.
  simpl in H.
  destruct n; tryfalse.
  unfold get_eid_list in H1.
  unfold get_eid_list' in H1.
  simpl in H1.
  destruct m; tryfalse.
  destruct edatal.
  simpl in H.
   simp join.  
   tryfalse.
  unfold evsllseg in H; fold evsllseg in H.
  destruct a. 
  sep pure.
  unfolds in H0.
  destruct v; simpl in H0; tryfalse.
  destruct v1; simpl in H0; tryfalse.
  destruct v2; simpl in H0; tryfalse.
  destruct v3; simpl in H0; tryfalse.
  destruct v4; simpl in H0; tryfalse.
  destruct v5; simpl in H0; tryfalse.
  inverts H0.
  unfolds.
  intros.
  destruct ectrl.
  simpl in H0.
  destruct n; inverts H0.
  simpl in H1.
  destruct m; tryfalse.
  destruct n; destruct m; tryfalse.
  simpl in H0; inverts H0.
  apply aeventnode_evsllseg_get_neq  with (n := m) (x:=vm) in H; auto.

(*  introv Hf; tryfalse. *)
  simpl.
  simpl in H1.
  destruct e0.
  simpl.
  destruct m.
  simpl in H1; auto.
  auto.
  simpl in H1; inverts H1.
  apply aeventnode_evsllseg_get_neq  with (n := n) (x:=vn) in H; auto.

(*  introv Hf; tryfalse. *)
  simpl.
  simpl in H0.
  destruct e0.
  simpl.
  destruct n.
  simpl in H0; auto.
  auto.
  sep lift 2%nat in H.
  apply IHectrl in H.
  unfolds in H.
  apply (H n m vn vm).
  simpl in H0.
  destruct e0.
  simpl; auto.
  simpl in H1; destruct e0.
  simpl; auto.
  auto.
  Qed.

Lemma  ecb_joinsig_ex_split:
  forall x x0 x1 ecbls x3 x4,
    EcbMod.joinsig x x0 x1 ecbls ->
    EcbMod.join x3 x4 x1 ->
    exists y, EcbMod.joinsig x x0 x3 y /\ EcbMod.join y x4 ecbls.
Proof.
  intros.
  exists (EcbMod.minus ecbls x4).
  split.
  unfolds; intro.
  pose proof H a.
  pose proof H0 a.
  destruct(tidspec.beq x a) eqn:eq1.
 lets Hkk: tidspec.beq_true_eq eq1; substs.
  rewrite EcbMod.get_sig_some.
  rewrite EcbMod.get_sig_some in H1.
  rewrite EcbMod.minus_sem.
  destruct( EcbMod.get x3 a);
  destruct( EcbMod.get x4 a);
  destruct( EcbMod.get x1 a);
  destruct( EcbMod.get ecbls a);
  tryfalse; substs; auto.
  apply tidspec.beq_false_neq in eq1.
  rewrite EcbMod.get_sig_none; auto.
  rewrite EcbMod.get_sig_none in H1; auto.
  rewrite EcbMod.minus_sem.
  destruct( EcbMod.get x3 a);
  destruct( EcbMod.get x4 a);
  destruct( EcbMod.get x1 a);
  destruct( EcbMod.get ecbls a);
  tryfalse; substs; auto.

  intro.
  pose proof H a.
  pose proof H0 a.
  rewrite EcbMod.minus_sem.
  destruct(tidspec.beq x a) eqn:eq1.
  lets Hkk: tidspec.beq_true_eq eq1; substs.
  rewrite EcbMod.get_sig_some in H1.
  destruct( EcbMod.get x3 a);
  destruct( EcbMod.get x4 a);
  destruct( EcbMod.get x1 a);
  destruct( EcbMod.get ecbls a);
  tryfalse; substs; auto.

  apply tidspec.beq_false_neq in eq1.
  rewrite EcbMod.get_sig_none in H1; auto.
  destruct( EcbMod.get x3 a);
  destruct( EcbMod.get x4 a);
  destruct( EcbMod.get x1 a);
  destruct( EcbMod.get ecbls a);
  tryfalse; substs; auto.
Qed.


Lemma ecblist_p_decompose:
  forall l1 ll1 l2 ll2 head ecbls tcbls,
    length l1 = length ll1 ->
    ECBList_P head Vnull
              (l1++
                 l2) (ll1 ++ ll2) ecbls tcbls ->
    exists ecbls1 ecbls2 x,
      ECBList_P head x l1 ll1 ecbls1 tcbls /\
      ECBList_P x Vnull l2 ll2 ecbls2 tcbls /\
      EcbMod.join ecbls1 ecbls2 ecbls.
Proof.
  inductions l1.
  simpl.
  intros.
  destruct ll1.
  simpl in H0.
  do 3 eexists;splits; eauto.
  eapply EcbMod.join_emp; auto.
  simpl in H.
  tryfalse.
  intros.
  destruct ll1.
  simpl in H.
  tryfalse.
  simpl in H.
  assert (length l1 = length ll1) by omega.
  simpl in H0.
simp join.
	  destruct a.
  simp join.
  lets Hxs : IHl1 H1 H5.
  simp join.
  lets Hsx :     ecb_joinsig_ex_split H3 H8.
  simp join.
  exists x6 x4 x5.
  simpl.
  splits.
  eexists.
  splits; eauto.
  do 3 eexists.
  splits; eauto.
  auto.
  auto.
Qed.

Lemma ecb_sub_eq:
  forall h ecbls h' x x4 x5 x1 x2,
    EcbMod.sub h ecbls ->
    EcbMod.sub h' ecbls -> 
    EcbMod.joinsig x x4 x5 h ->
    EcbMod.joinsig x x1 x2 h'->
    x5 = x2 ->
    h = h'.
Proof.
  intros.
  substs.
  apply EcbMod.extensionality.
  intro.
  pose proof H a.
  pose proof H0 a.
  pose proof H2 a.
  pose proof H1 a.
  unfold EcbMod.lookup in *.
  destruct (tidspec.beq x a) eqn : eq1.
  lets Hak : tidspec.beq_true_eq eq1; substs.
  rewrite EcbMod.get_sig_some in H6.
  rewrite EcbMod.get_sig_some in H5.
  destruct (EcbMod.get x2 a); tryfalse.
  destruct (EcbMod.get h' a) eqn: eq2;
  destruct (EcbMod.get h a) eqn: eq3;
  tryfalse.
  assert (Some b0 = Some b0) by auto.
  pose proof H3 b0 H7.
  assert (Some b = Some b) by auto.
  pose proof H4 b H9.
  rewrite H8 in H10; inverts H10; auto.

  apply tidspec.beq_false_neq in eq1.
  rewrite EcbMod.get_sig_none in H6; auto.
  rewrite EcbMod.get_sig_none in H5; auto.
  destruct (EcbMod.get x2 a).
  destruct (EcbMod.get h' a) eqn: eq2;
  destruct (EcbMod.get h a) eqn: eq3;
  tryfalse; substs; auto.
  destruct (EcbMod.get h' a) eqn: eq2;
  destruct (EcbMod.get h a) eqn: eq3;
  tryfalse; substs; auto.
Qed.


Lemma ecblist_p_eqh:
  forall l  h h' ecbls head tail1 tail2  ll tcbls,
    EcbMod.sub h ecbls ->
    EcbMod.sub h' ecbls ->
    ECBList_P head tail1 l ll h tcbls ->
    ECBList_P head tail2 l ll h' tcbls ->
    tail1 = tail2 /\ h = h'.
Proof.
  inductions l.
  simpl.
  intros.
  simp join. 
  split; auto.
  intros.
  simpl in *.
  simp join.
  destruct ll; tryfalse.
  destruct a.
  simp join.
  inverts H2.
  rewrite H4 in H1.
  inverts H1.
  lets Hzz : IHl H11 H8.
  apply EcbMod.join_sub_r in H9.
  lets Hs : EcbMod.sub_trans H9 H.
  eapply Hs.
  apply EcbMod.join_sub_r in H6.
  lets Hss : EcbMod.sub_trans H6 H0.
  eapply Hss.
  destruct Hzz.
  split.
  auto.
  eapply ecb_sub_eq ; eauto.
Qed.


Lemma eventtype_neq_q:
  forall v'38 v'21 i1 i0 i2 x2 x3 v'42 v'40 v'22 v'23 v'41 v'24 v'34 v'35 v'49 s P v'43 v'45 v'44 v'46,
    length v'21 = length v'23-> 
    ECBList_P v'38 Vnull
              (v'21 ++
                    ((Vint32 i1 :: Vint32 i0 :: Vint32 i2 :: x2 :: x3 :: v'42 :: nil,
                      v'40) :: nil) ++ v'22) (v'23 ++ (v'41 :: nil) ++ v'24) v'34 v'35 ->
    ECBList_P v'38 (Vptr (v'49, Int.zero)) v'21 v'23 v'43 v'35 ->
    EcbMod.join v'43 v'45 v'34 ->
    EcbMod.joinsig (v'49, Int.zero) v'46 v'44 v'45 ->
    Int.eq i1 ($ OS_EVENT_TYPE_Q) = false ->
    s|= AEventData
     (Vint32 i1 :: Vint32 i0 :: Vint32 i2 :: x2 :: x3 :: v'42 :: nil) v'41 ** P ->
    s |= AEventData
      (Vint32 i1 :: Vint32 i0 :: Vint32 i2 :: x2 :: x3 :: v'42 :: nil) v'41 **
      [|~ exists x y z, EcbMod.get v'34 (v'49,Int.zero) = Some (absmsgq x y, z) |] ** P.
Proof.
  intros.

  apply ecblist_p_decompose in H0;auto.
  simp join.

  assert (x1 = Vptr (v'49, Int.zero) /\ x = v'43).
  eapply ecblist_p_eqh;eauto.
  instantiate (1:=v'34).
  eapply EcbMod.join_sub_l;eauto.
  eapply EcbMod.join_sub_l;eauto.
  destruct H8;subst.
  destruct v'41.
  unfold AEventData in *.
  sep normal in H5.
  sep split in H5.
  unfolds in H9;simpl in H9.
  inverts H9.
  rewrite Int.eq_true in H4;tryfalse.
  sep auto.
  simpl in H6.
  simp join.
  destruct x1.
  destruct e;tryfalse.
  simp join.
  intro.
simp join.
  inverts H6.
  lets Hx:EcbMod.join_joinsig_get H7 H10.
  rewrite H11 in Hx.
  tryfalse.
  sep auto.
  simpl in H6.
  simp join.
  destruct x1.
  destruct e;tryfalse.
  simp join.
  intro.
  simp join.
  inverts H6.
  lets Hx:EcbMod.join_joinsig_get H7 H10.
  rewrite H11 in Hx.
  tryfalse.
  sep auto.
  simpl in H6.
  simp join.
  destruct x1.
  destruct e;tryfalse.
  simp join.
  intro.
  simp join.
  inverts H6.
  lets Hx:EcbMod.join_joinsig_get H7 H10.
  rewrite H14 in Hx.
  tryfalse.
Qed.


Fixpoint RL_PrioTbl_P (ptbl : vallist) (tcbls : list vallist) (vhold:addrval) {struct tcbls}:=
  match tcbls with
    | nil => True
    | l::tcbls' =>
      match
        V_OSTCBPrio l with
        | Some (Vint32 prio) =>
          (exists x,nth_val (nat_of_Z (Int.unsigned prio)) ptbl = Some (Vptr x)  /\ x <> vhold ) /\ RL_PrioTbl_P ptbl tcbls' vhold
        | _ => False
      end
  end.


Fixpoint RL_TCBListblk_P l :=
  match l with
    | nil => True
    | a::l' => RL_TCBblk_P a /\ RL_TCBListblk_P l'
  end.

Lemma imp_rl_priotbl_p:
  forall  ltls  ptbl htls p rtbl vhold,
    R_PrioTbl_P ptbl htls vhold->
    TCBList_P p ltls rtbl htls ->
    RL_PrioTbl_P ptbl ltls vhold.
Proof.
  intros.
  unfolds in H.
  destruct H.
  destruct H1.
  clear H H2.
  gen H0 H1 .
  inductions ltls.
  intros.
  simpl in H0.
  subst.
  simpl.
  auto.
  intros.
  simpl in H0.
  simp join.
  simpl.
  unfolds in H3.
  destruct x2.
  destruct p.
  simp join.
  rewrite H3.
  splits.
  unfolds in H2.
  apply TcbMod.join_sig_get in H2.
  apply H1 in H2.
  simp join.
  eauto.
  eapply IHltls; eauto.
  intros.
  eapply H1.
  eapply TcbMod.join_get_r;eauto.
Qed.




Lemma tcbdllseg_split:
  forall x1 s P v'23 v'32 x2 x3 xx,
    s |= tcbdllseg (Vptr v'23) xx v'32 Vnull (x1 ++ x2 :: x3) ** P ->
    s |= EX x v'15,
  tcbdllseg (Vptr v'23) xx x (Vptr v'15) x1 **
            tcbdllseg (Vptr v'15) x v'32 Vnull (x2 :: x3)** [|x1<>nil /\ nth_val 0 (last x1 nil) = Some (Vptr v'15) \/ x1 = nil /\ Vptr v'15 = Vptr v'23 |] ** P.
Proof.
  induction x1.
  intros.
  simpl List.app in H.
  unfold tcbdllseg at 1.
  simpl dllseg at 1.
  sep auto.
  unfold tcbdllseg in *.
  intros.
  rewrite <- List.app_comm_cons in H.
  unfold1 dllseg in H.
  sep normal in H.
  sep destruct H.
  sep split in H.
  sep lift 2%nat in H.
  remember (node (Vptr v'23) a OS_TCB ** P) as X.
  lets Hx:dllseg_head_isptr H.
  unfolds in Hx.
  destruct Hx.
  subst.
  remember (x1 ++ x2 :: x3 ) as X.
  destruct X.
  destruct x1;simpl in HeqX;tryfalse.
  unfold1 dllseg in H.
  sep split in H.
  tryfalse.
  destruct H3.
  subst.
  eapply IHx1 in H.
  unfold dllseg at 1.
  fold dllseg.
  sep auto.
  left.
  split;auto.
  (*introv Hf; tryfalse.*)
  destruct H3.
  simp join.
  simpl.
  destruct x1.
  simpl in H4;tryfalse.
  auto.
  destruct H3.
  subst;inverts H4.
  simpl.
  unfolds in H0;auto.
Qed.

Close Scope code_scope.
Close Scope int_scope.
Close Scope Z_scope.
