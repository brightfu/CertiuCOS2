Require Import include_frm.
Require Export math_sol.
Require Export tv_match.
Require Export int_auto.
Require Export pure_lib.
Require Import os_inv.

Open Scope Z_scope.
Open Scope int_scope.

Module _mathsolver_ext.
  Close Scope nat_scope.
  Open Scope Z_scope.
  Definition deref_Vint32_unsafe (x:val): int32 :=
    match x with
      | Vint32 x => x
      | _ => (Int.repr 0)
    end.

  Lemma OSUnMapVallist_safe_deVint32 :
    forall z y, 0<=z<=255 ->
                nth_val' (Z.to_nat z) OSUnMapVallist = Vint32 y ->
                y = deref_Vint32_unsafe ( nth_val' (Z.to_nat z) OSUnMapVallist).
  Proof.
    intros.
    _mathsolver.pre.
    repeat (destruct H; [rewrite H in *; simpl in H0; inversion H0; auto| idtac]).
    rewrite H in *; simpl in H0; inversion H0; auto.
  Qed.

  Lemma OSMapVallist_safe_deVint32 :
    forall z y, 0<=z<=7 ->
                nth_val' (Z.to_nat z) OSMapVallist = Vint32 y ->
                y = deref_Vint32_unsafe ( nth_val' (Z.to_nat z) OSMapVallist).
  Proof.
    intros.
    _mathsolver.pre.
    repeat (destruct H; [rewrite H in *; simpl in H0; inversion H0; auto| idtac]).
    rewrite H in *; simpl in H0; inversion H0; auto.
  Qed.
  
  Ltac deref_vint32_for_array :=
    match goal with 
      | H : nth_val' (Z.to_nat (Int.unsigned ?a) ) OSUnMapVallist = Vint32 _ |- _=>
        apply OSUnMapVallist_safe_deVint32 in H;
          [unfold deref_Vint32_unsafe in H;
            try rewrite H in *;
            clear H |set (@Int.unsigned_range_2 a);
             try omega]
      | H : nth_val' (Z.to_nat (Int.unsigned ?a) ) OSMapVallist = Vint32 _ |- _ =>
        apply OSMapVallist_safe_deVint32 in H;
          [unfold deref_Vint32_unsafe in H;
            try rewrite H in *; clear H | set (@Int.unsigned_range_2 a);
             try omega]
      | H : nth_val' (Z.to_nat _ ) OSUnMapVallist = Vint32 _ |- _=>
        apply OSUnMapVallist_safe_deVint32 in H;
          [unfold deref_Vint32_unsafe in H;
            try rewrite H in *; clear H |
           try omega]
      | H : nth_val' (Z.to_nat _ ) OSMapVallist = Vint32 _ |- _ =>
        apply OSMapVallist_safe_deVint32 in H;
          [unfold deref_Vint32_unsafe in H;
            try rewrite H in *; clear H |
           try omega]
    end.
End _mathsolver_ext.

Ltac mautoext :=
  repeat _mathsolver_ext.deref_vint32_for_array; _mathsolver.new_mathsolver.

Ltac mautoext_noto :=
  repeat _mathsolver_ext.deref_vint32_for_array; _mathsolver.new_mathsolver_noto.

Lemma OSUnMapVallist_type_vallist_match:
  array_type_vallist_match Tint8 OSUnMapVallist.
Proof.
  unfold OSUnMapVallist.
  simpl.
  repeat (splits; 
          try solve [apply true_if_else_true;
                      apply Zle_is_le_bool;
                      rewrite Int.unsigned_repr;
                      try solve [unfold Byte.max_unsigned; simpl; omega | int auto]]).
  auto.
Qed.

Lemma osunmapvallist_prop:
  forall i, (Int.unsigned i <= 255) ->
            exists x, nth_val' (Z.to_nat (Int.unsigned i)) OSUnMapVallist = Vint32 x
                      /\ Int.unsigned x <=?7 = true.
Proof.
  intros.
  lets Hx:Int.unsigned_range i.
  destruct Hx.
  clear H1.
  remember (Int.unsigned i) as z.
  clear Heqz.
  lets Hx:pos_to_nat_range_0_255 H0 H;eauto.
  destruct Hx.
  clear H H0.
  remember (Z.to_nat z) as n.
  clear Heqn.
  do 255 ( destruct n;[
             simpl;
             eexists;split;eauto | 
             apply sn_le_n_le_minus1 in H2;simpl in H2]).
  simpl;auto.
  destruct n.
  eexists;simpl;auto.
  omega.
Qed.

Lemma math_unmap_range:
  forall x y,
    Int.unsigned x <= 255 ->
    nth_val' (Z.to_nat (Int.unsigned x)) OSUnMapVallist = Vint32 y ->
    (0<= Z.to_nat (Int.unsigned y) <8)%nat.
Proof.
  introv H Hl.
  mautoext.
Qed.

Lemma math_8_255_eq:
  forall y v,
    Int.unsigned v <= 255 ->
    nth_val' (Z.to_nat (Int.unsigned v)) OSUnMapVallist = Vint32 y ->
    v <> $ 0 ->
    v&ᵢ($ 1<<ᵢ  y) = $ 1<<ᵢ y.
Proof.
  introv Hi Hj.
  mautoext.
Qed.


Lemma math_prop_int_zero_eq :
  forall rgrp x,
    Int.unsigned rgrp <= 255->
    nth_val' (Z.to_nat (Int.unsigned rgrp)) OSUnMapVallist = Vint32 x ->
    rgrp <> $ 0 -> 
    rgrp&ᵢ($ 1<<ᵢ x)  = $ 0 ->
    Int.zero =  $ 1<<ᵢ(((x<<ᵢ$ 3))&ᵢ$ 7).
Proof.
  introv Hx Hy Hc.
  lets Hz : math_8_255_eq Hx Hy Hc.
  rewrite Hz.
  clear Hc Hz.
  intros.
  false.
  gen H.
  mautoext.
Qed.

Lemma math_unmap_get_y :
  forall v y,
    Int.unsigned v <= 255 ->
    nth_val' (Z.to_nat (Int.unsigned v)) OSUnMapVallist = Vint32 y ->
    Int.unsigned y < 8.
Proof.
  introv Hv Hs.
  eapply nat_8_range_conver.
  eapply math_unmap_range; eauto.
Qed.

Lemma math_unmap_core_prop:
  forall rgrp x y,
    Int.unsigned rgrp <=255 ->
    nth_val' (Z.to_nat (Int.unsigned rgrp)) OSUnMapVallist = Vint32 x ->
    Int.unsigned y < 8 ->
    rgrp <> $ 0  ->
    rgrp&ᵢ($ 1<<ᵢ y) = $ 1<<ᵢ y ->
    Int.unsigned x <= Int.unsigned y.
Proof.
  introv Hx Hk Hz.
  mautoext.
Qed.

Lemma math_highest_prio_select :
  forall x y xv rgrp prio' rtbl vy,
    Int.unsigned x < 8 ->
    Int.unsigned y < 8 ->
    Int.unsigned (prio'&ᵢ$ 7) < 8 ->
    Int.unsigned prio' < 64 ->
    Int.unsigned (Int.shru prio' ($ 3)) < 8 -> 
    Int.unsigned rgrp <=255 ->
    Int.unsigned xv <=255 ->
    nth_val' (Z.to_nat (Int.unsigned xv)) OSUnMapVallist = Vint32 y ->
    nth_val' (Z.to_nat (Int.unsigned rgrp)) OSUnMapVallist = Vint32 x ->
    nth_val (Z.to_nat (Int.unsigned x)) rtbl = Some (Vint32 xv) ->
    nth_val (Z.to_nat (Int.unsigned (Int.shru prio' ($ 3)))) rtbl = Some (Vint32 vy) ->
    rgrp <> $ 0 ->
    xv <> $ 0 ->
    rgrp&ᵢ($ 1<<ᵢ(Int.shru prio' ($ 3))) = $ 1<<ᵢ(Int.shru prio' ($ 3)) ->
    vy&ᵢ($ 1<<ᵢ(prio'&ᵢ$ 7)) = $ 1<<ᵢ(prio'&ᵢ$ 7) ->
    Int.unsigned ((x<<ᵢ$ 3)+ᵢy) <= Int.unsigned prio'.
Proof.    
  introv Hi1 Hp1 Hpp Hpx Hp2 Hp3  Hx1 Hnth1 Hnth2 Hnth3.
  introv Hnth4 Hneq1 Hneq2 Hrgrp Hvx.
  lets Hn1 :  math_unmap_core_prop Hp3 Hnth2 Hp2 Hrgrp; auto.
  assert (Int.unsigned x < Int.unsigned (Int.shru prio' ($ 3))
          \/ Int.unsigned x = Int.unsigned (Int.shru prio'($ 3))).
  omega.
  destruct H.
  lets Hle :  int_ltu_shru_ltu H ; eauto.
  lets Hls : int_add_lt_max Hi1 Hp1.
  omega.
  rewrite H in Hnth3.
  rewrite Hnth3 in Hnth4.
  inverts Hnth4.
  lets Has : math_unmap_core_prop  Hx1 Hnth1  Hneq2 Hvx; auto.
  apply unsigned_inj in H.
  subst x.
  eapply math_prio_8_lt; eauto.
Qed.

Lemma math_nth_8_neq_not:
  forall x y n,
    Int.unsigned x < 8 ->
    nth_val' (Z.to_nat (Int.unsigned x)) OSMapVallist = Vint32 y ->
    (0 <= n < 8)%nat ->
    n <> Z.to_nat (Int.unsigned x) ->
    Int.not y &ᵢ($ 1<<ᵢ$ Z.of_nat n) = $ 1<<ᵢ$ Z.of_nat n.
Proof.
  introv Hx Hy Hz.
  mautoext.
Qed.

Lemma math_nth_8_neq_zero :
  forall x y ,
    Int.unsigned x < 8 ->
    nth_val' (Z.to_nat (Int.unsigned x)) OSMapVallist = Vint32 y ->
    ($ 1<<ᵢx)&ᵢy <> $ 0.
Proof.
  introv Hx Hy.
  mautoext.
Qed.

Lemma math_nth_8_neq_zero' :
  forall x y ,
    Int.unsigned x < 8 ->
    nth_val' (Z.to_nat (Int.unsigned x)) OSMapVallist = Vint32 y ->
    y <> $ 0 .
Proof.
  introv Hx Hy.
  mautoext.
Qed.

Lemma math_nth_8_gt_zero :
  forall v'39 v'40 ,
    Int.unsigned v'39 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned v'39)) OSMapVallist = Vint32 v'40 ->
    0 < Int.unsigned  v'40.
Proof.
  introv Hx Hy.
  mautoext.
Qed.


Lemma math_nth_8_eq_shl :
  forall x y ,
    Int.unsigned x < 8 ->
    nth_val' (Z.to_nat (Int.unsigned x)) OSMapVallist = Vint32 y ->
    ($ 1<<ᵢx)&ᵢy =  ($ 1<<ᵢx).
Proof.
  introv Hx Hy.
  mautoext.
Qed.


Lemma  math_nth_8_eq_zero:
  forall x y n,
    Int.unsigned x <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned x)) OSMapVallist = Vint32 y ->
    (0 <= n < 8)%nat ->
    n <> Z.to_nat (Int.unsigned x) ->
    y&ᵢ($ 1<<ᵢ$ Z.of_nat n) = Int.zero.
Proof.
  introv Hx Hy Hz.
  mautoext.
Qed.

Lemma math_nth_8_eq_zero2:
  forall (x y z: int32) ,
    Int.unsigned x <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned x)) OSMapVallist = Vint32 y ->
    Int.unsigned z < 8  ->
    z <> x -> Int.not y &ᵢ($ 1<<ᵢ z) = ($ 1<<ᵢ z).
Proof.
  introv Hx Hy Hz.
  mautoext.
Qed.

Lemma math_nth_8_eq_zero':
  forall (x y z: int32) ,
    Int.unsigned x <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned x)) OSMapVallist = Vint32 y ->
    Int.unsigned z < 8  ->
    z <> x -> y&ᵢ($ 1<<ᵢ z) = $ 0.
Proof.
  introv Hx Hy Hz.
  mautoext.
Qed.

Lemma math_mapval_core_prop:
  forall x y : int32,
    Int.unsigned x < 8 ->
    nth_val' (Z.to_nat (Int.unsigned x)) OSMapVallist = Vint32 y ->
    y = $ 1<<ᵢx.
Proof.
  intros.
  mautoext.
Qed.

Close Scope int_scope.
Close Scope Z_scope.
