Require Import include_frm.
Require Import int_auto.
Require Import sep_auto.
Require Import math_sol.
Require Import code_notations.

Set Implicit Arguments.

Open Scope code_scope.
Open Scope Z_scope.
Open Scope int_scope.

Lemma le255_and_le255 :
  forall x v'37,
    Int.unsigned x<=255 ->
    Int.unsigned (x&ᵢv'37) <= 255.
Proof.
  intros.
  set (Int.and_le x v'37).
  omega.
Qed.

Lemma ptr_isptr :
  forall x, isptr (Vptr x).
  intros.
  unfolds.
  right; eexists; eauto.
Qed.

Lemma Vnull_is_ptr :
  isptr Vnull.
Proof.
  unfolds; auto.
Qed.


Ltac desifthen :=
  match goal with 
      |  H: context[if ?x then _ else _ ] |- _ => 
        destruct x; simpl;
        intuition auto; tryfalse
      | |- context[if ?x then _ else _ ] => 
        destruct x; simpl;
        intuition auto; tryfalse
end.

Lemma isptr2_bool_not_vundef :
  forall v1 v2,
    isptr v1 ->
    isptr v2 ->
    val_inj
      (bool_and (val_inj (notint (val_inj (val_eq v1 Vnull))))
                (val_inj (notint (val_inj (val_eq v2 Vnull))))) <> Vundef.
Proof.
  introv Hisptr1 Hisptr2.
  unfold isptr in *.
  destruct Hisptr1; destruct Hisptr2; 
  simp join. 
  simpl; desifthen.
  simpl; destruct x.
  simpl; desifthen.
  simpl; destruct x.
  simpl; desifthen.
  simpl; destruct x0.
  destruct x.
  simpl; desifthen.
Qed.


Lemma isptr2_bool_and :
  forall v1 v2 , 
    isptr v1 ->
    isptr v2 -> 
    val_inj
      (bool_and (val_inj (notint (val_inj (val_eq v1 Vnull))))
                (val_inj (notint (val_inj (val_eq v2 Vnull))))) <>
    Vint32 Int.zero -> 
    exists x y, v1 = Vptr x /\ v2 = Vptr y.
Proof.
  introv Hisptr1 Hisptr2 Hnot.
  unfold isptr in *.
  destruct Hisptr1; destruct Hisptr2; simpl join.
  subst.
  simpl in Hnot.
  int auto.
  simpl in Hnot; tryfalse.
  subst.
  destruct H0.
  subst.
  simpl in Hnot.
  destruct x.
  simpl in Hnot.
  int auto.
  simpl in Hnot.
  tryfalse.
  simpl in Hnot; tryfalse.
  simp join.
  simpl in Hnot.    
  destruct x.
  simpl in Hnot.
  int auto.
  simpl in Hnot.  
  tryfalse.
  simpl in Hnot; tryfalse.
  simp join.
  eauto.
Qed.


Lemma isptr_neq_vundef : 
  forall v, isptr v ->
            val_inj (val_eq v Vnull) <> Vundef.  
Proof.
  introv His; unfolds in His.
  destruct His;subst; simpl. 
  introv Hf; inverts Hf.
  simp join.
  introv Hf.
  simpl in Hf.
  destruct x.
  simpl in Hf.
  inverts Hf.
Qed.


Lemma isptr_neq_notint_vundef : 
  forall v, isptr v ->
            val_inj (notint (val_inj (val_eq v Vnull))) <> Vundef.  
Proof.
  introv His; unfolds in His.
  destruct His;subst; simpl. 
  introv Hf; inverts Hf.
  simp join.
  introv Hf.
  simpl in Hf.
  destruct x.
  simpl in Hf.
  inverts Hf.
Qed.



Lemma isptr_match_eq_true : 
  forall x, isptr x -> 
            match x with
              | Vundef => false
              | Vnull => true
              | Vint32 _ => false
              | Vptr _ => true
            end = true.
Proof.
  intros.
  destruct H.
  subst; auto.
  destruct H; subst; auto.
Qed.


Lemma ptr_neq_null :  
  forall x, isptr x -> 
            val_inj (val_eq x Vnull) <> Vint32 Int.zero 
            -> x = Vnull.
Proof.
  introv Hp Hv.
  destruct Hp; subst; auto.
  simp join.
  simpl in Hv.
  destruct x0.
  simpl in Hv.
  tryfalse.
Qed. 


Lemma isptr_pointer_intro : 
  forall x , isptr x -> 
             ((val_inj (val_eq x Vnull) = Vint32 Int.zero \/
               val_inj (val_eq x Vnull) = Vnull)) -> exists v, x = Vptr v.
Proof.
  intros.
  destruct x; unfolds in H;  destruct H; simp join; tryfalse.
  destruct H0.
  simpl in H; tryfalse.
  simpl in H; tryfalse.
  eauto.
Qed.


Lemma int32_inj_neq_Vundef: 
  forall x y,   
    val_inj (val_eq (Vint32  (Int.repr x) ) (Vint32 (Int.repr y))) <> Vundef.
Proof.
  intros.
  unfolds.
  intros.
  unfolds in H.
  remember (val_eq (Vint32  (Int.repr x) ) (Vint32 (Int.repr y))) as Hr.
  unfolds in HeqHr.
  destruct Hr; desifthen.
Qed.


Lemma vptr_inj_neq_Vundef: 
  forall x y,  isptr x ->
               isptr y ->
               val_inj (val_eq x y ) <> Vundef.
Proof.
    intros.
    unfolds.
    intros.
    unfolds in H.
    unfolds in H0.
    destruct H; destruct H0 ; simp join ;  simpl in H1; tryfalse.
    destruct x0; simpl in H1; tryfalse.
    destruct x0; simpl in H1; tryfalse.
    destruct x1; destruct x0; simpl in H1.
    destruct (peq b b0) ; destruct (Int.eq i i0) ; tryfalse.
Qed.



Lemma ltu_zero_false_imp_eq_zero :
  forall i,
    Int.ltu Int.zero i = false ->
    i = Int.zero.
Proof.
  intros.
  unfold Int.ltu in *.
  rewrite Int.unsigned_zero in *.
  remember (zlt 0 (Int.unsigned i)) as bool; destruct bool.
  tryfalse.
  assert (Int.unsigned i >= 0 )%Z  by int auto.
  assert (Int.unsigned i = 0)%Z.
  omega.
  clear - H1.
  eapply Int.unsigned_eq_zero.
  auto.
Qed.



Lemma shru_3_lt_8 :
  forall i,
    Int.unsigned i < 64 ->
    Int.unsigned (Int.shru i ($ 3)) < 8.
Proof.
  intros.
  mauto.
Qed.





Lemma val_inj_impl_eq :
  forall x y,
    val_inj (val_eq x y) <> Vint32 Int.zero /\
    val_inj (val_eq x y) <> Vnull /\
    val_inj (val_eq x y) <> Vundef ->
    x = y.
Proof.   
  intros.
  destruct x.
  destruct y; auto; simpl in H; simp join; tryfalse.  
  destruct y; auto; simpl in H; simp join; tryfalse.
  destruct a; simpl in *; tryfalse.
  destruct y; auto; simpl in H; simp join; tryfalse.
  remember (Int.eq i i0) as b.    
  destruct b; simpl in *; tryfalse.
  symmetry in Heqb.
  lets H100: Int.eq_spec i i0.
  rewrite Heqb in H100.
  subst i; eauto.
  destruct a.
  destruct y; auto; simpl in H; simp join; tryfalse.
  destruct a; simpl in *; tryfalse.
  remember (Int.eq i i0) as bb.
  destruct (peq b b0), bb; simpl in *; tryfalse.
  subst b.     
  symmetry in Heqbb.
  lets H100: Int.eq_spec i i0.
  rewrite Heqbb in H100.
  subst i; auto.
Qed.

Lemma val_inj_impl_Vnull :
  forall x,
    val_inj (val_eq x Vnull) <> Vint32 Int.zero /\
    val_inj (val_eq x Vnull) <> Vnull /\
    val_inj (val_eq x Vnull) <> Vundef ->
    x = Vnull.
Proof.   
  intros.
  destruct x; simpl in *; simp join; tryfalse; auto.  
  destruct a; simpl in *; tryfalse.  
Qed.

Lemma val_inj_impl_Vptr :
  forall x,
    val_inj (val_eq x Vnull) = Vint32 Int.zero \/
    val_inj (val_eq x Vnull) = Vnull ->
    exists a, x = Vptr a.
Proof.
  intros.
  destruct x; simpl in H; (destruct H; tryfalse).
  eexists; auto.
  eexists; auto.
Qed.


Lemma bool_type_val_match :
  forall v, 
    Some v = Some (V$ 1) \/ Some v = Some (V$ 0) ->
    type_val_match Tint8 v = true.
Proof.
  intros.
  destruct H; inverts H; eauto.
Qed.  

Lemma val_inj_not_Vundef_2 :
  forall v,
    Some v = Some (V$ 1) \/ Some v = Some (V$ 0) ->
    val_inj (val_eq v (V$ 0)) <> Vundef.
Proof.
  intros.
  destruct H; inverts H; auto.
  simpl.
  int auto.
  simpl; intuition auto; tryfalse.
  simpl.
  int auto.
  simpl.
  introv Hf; tryfalse.
Qed.


Lemma Int_i2_i_1 : 
  forall i2  i,
    (Int.unsigned i2 <=? 65535) = true -> 
    true = Int.ltu ($ 0) i2 ->
    (Int.unsigned i <=? 255) = true ->
    (Int.unsigned (i2 -ᵢ $ 1) <=? 65535) = true.
Proof.
  intros.
  apply Zle_bool_imp_le in H.
  apply Zle_bool_imp_le in H1.
  apply Zle_imp_le_bool.
  int auto.
  int auto.
Qed.

Lemma  Int_i2_i_1_iftrue: 
  forall i2  i,
    (Int.unsigned i2 <=? 65535) = true -> 
    true = Int.ltu ($ 0) i2 ->
    (Int.unsigned i <=? 255) = true ->
    (if Int.unsigned (i2-ᵢ$ 1) <=? Int16.max_unsigned then true else false) =
    true.
Proof.
  intros.
  unfold Int16.max_unsigned.
  simpl.
  erewrite   Int_i2_i_1 ; eauto.
Qed.



Lemma isptr_val_inj_neqvundef : forall x b ofs,
  isptr x ->  val_inj
     match x with
     | Vundef => None
     | Vnull => Some (Vint32 Int.zero)
     | Vint32 _ => None
     | Vptr (b2, ofs2) =>
         if peq b b2
         then
          if Int.eq ofs ofs2
          then Some (Vint32 Int.one)
          else Some (Vint32 Int.zero)
         else Some (Vint32 Int.zero)
     end <> Vundef.
Proof.
  intros.
  unfolds in H.
  destruct H; subst; simpl; intuition auto; tryfalse.
  simp join.
  destruct x0.
  destruct (peq b b0); destruct (Int.eq ofs i); simpl in * ; tryfalse ;  auto.
Qed.


Hint Resolve   isptr2_bool_and: pauto_lemmas.
Hint Resolve  isptr2_bool_not_vundef : pauto_lemmas.
Hint Resolve isptr_val_inj_neqvundef: pauto_lemmas.
Hint Resolve  Int_i2_i_1 Int_i2_i_1_iftrue : pauto_lemmas.
Hint Resolve  isptr_neq_vundef : pauto_lemmas.
Hint Resolve  isptr_neq_notint_vundef  : pauto_lemmas.
Hint Resolve   isptr_match_eq_true  : pauto_lemmas.
Hint Resolve   ptr_neq_null   : pauto_lemmas.
Hint Resolve   isptr_pointer_intro  : pauto_lemmas.
Hint Resolve  int32_inj_neq_Vundef  : pauto_lemmas.
Hint Resolve vptr_inj_neq_Vundef  : pauto_lemmas.
Hint Resolve  ltu_zero_false_imp_eq_zero : pauto_lemmas.
Hint Resolve shru_3_lt_8  : pauto_lemmas.
Hint Resolve val_inj_impl_eq  : pauto_lemmas.
Hint Resolve bool_type_val_match  : pauto_lemmas.
Hint Resolve val_inj_not_Vundef_2 : pauto_lemmas.
Hint Resolve val_inj_impl_Vptr : pauto_lemmas.
(*Hint Resolve  val_inj_not_Vundef_1   : pauto_lemmas.*)
Hint Resolve val_inj_impl_Vnull : pauto_lemmas.
Hint Resolve  val_inj_impl_eq : pauto_lemmas.


 Lemma a_div_b_multi_b_plus_b_ge_a: forall a b, 0<=a -> 0<b -> a/b*b +b >= a.
   intros.
   rewrite (Z_div_mod_eq a b) at 2.

   rewrite Z.mul_comm.
   assert (b>= a mod b).
   set (Z_mod_lt a b).
   omega.
   omega.
   omega.
 Qed.

 Ltac revs := 
   match goal with 
     |  |- ?a < ?b => cut (b > a); [intro; omega| idtac]
     |  |- ?a > ?b => cut (b < a); [intro; omega| idtac]
     |  |- ?a >= ?b => cut (b <= a); [intro; omega| idtac]
     |  |- ?a <= ?b => cut (b >= a); [intro; omega| idtac]
   end.

 Ltac revs' H := 
   match type of H with 
     |  ?a < ?b => assert (b > a) by omega
     |  ?a > ?b => assert (b < a) by omega
     |  ?a >= ?b => assert (b <= a) by omega
     |  ?a <= ?b => assert (b >= a) by omega
   end.

 Lemma div_lt_lt: forall a b c, c > 0 -> a/c < b/c -> a<b.
   intros.
   set (@Z_mod_lt a c H).
   set (@Z_mod_lt b c H).
   rewrite (Z_div_mod_eq a c).
   rewrite (Z_div_mod_eq b c).
   apply (@Zlt_le_trans _ (c*(a/c) +c)).
   inversion a0.
   omega.
   apply (@Zle_trans _ (c*(b/c))).
   Focus 2.
   inversion a1.
   omega.
   rewrite Zmult_succ_r_reverse.
   unfold Z.succ.
   apply Zmult_le_compat_l.
   omega.
   omega.
   omega.
   omega.
 Qed.

 Ltac bfunc_invert' H :=
   match type of H with 
     | (if ?e then true else false) = false => destruct (e); [inversion H|idtac]
   end.

 Ltac get_int_max :=  unfold Int.max_unsigned, Int.modulus; simpl.
 Ltac rewrite_un_repr := rewrite Int.unsigned_repr;[ idtac| get_int_max; omega].
 Ltac rewrite_un_repr_in l := rewrite Int.unsigned_repr in l;[ idtac| get_int_max; omega].

 Ltac intrange x tac :=
   let xval := fresh in let xrange := fresh in 
                        destruct x as [xval xrange]; unfold Int.modulus, 
                                                     two_power_nat, shift_nat in xrange; simpl in xrange; simpl; tac.

 Ltac handle_z2n_compare_nat rel z2nat_rule :=
   let H0 := fresh in 
   match goal with 
     | |- rel ( Z.to_nat _  ) ?x => 
       assert (Z.to_nat (Z.of_nat x) = x)%nat as H0 by
                                                  (apply Nat2Z.id);rewrite <- H0; rewrite <- z2nat_rule;simpl; int auto
   end.

 Ltac handle_z2n_lt_nat := handle_z2n_compare_nat lt Z2Nat.inj_lt.

 Ltac get_unsigned_sup_pow x p := 
   let H := fresh in assert (Int.unsigned x < (two_p p)) by 
                      (unfold two_p; unfold two_power_pos; unfold shift_pos;  simpl;  omega).

 Ltac get_unsigned_sz_sup' x p := 
   let H:= fresh in let H0 := fresh in 
                    let H1 := fresh in 
                    assert (0<=p) as H1 by omega; assert (0<=Int.unsigned x < two_p p ) as
                                                    H by (split; [int auto| auto]); set (Int.size_interval_2 x _ H1 H) as H0.

 Ltac get_unsigned_sz_sup x p:= get_unsigned_sup_pow x p; get_unsigned_sz_sup' x p.

 Ltac get_unsigned_sz_inf x := let H := fresh in  assert (0<= Int.size x) by (set (Int.size_range x) as H; inversion H;auto).

 Lemma int_not_0_sz_not_0 : 
   forall n, Int.unsigned n = 0 <-> Int.size n = 0.
   intros.
   split.
   intros.
   get_unsigned_sz_sup n 0.
   get_unsigned_sz_inf n.
   omega.
   intros.
   set (Int.size_interval_1 n).
   rewrite H in a.
   simpl in a.
   omega.
 Qed.

 Lemma and_xy_x: 
   forall x y, (forall n, 0<=n -> Z.testbit x n = true -> Z.testbit y n = true) -> Z.land x y = x.
 Proof.
   intros.
   apply Int.equal_same_bits.
   intros.
   rewrite Z.land_spec.
   remember (H i H0).
   clear Heqe.
   destruct (Z.testbit x i).
   rewrite e; auto.
   auto.
 Qed.

 Lemma lt_imply_le : 
   forall n m: Z, n<m -> n<=m.
 Proof.
   intros.
   omega.
 Qed.
 
 Lemma lt_is_gt : forall n m: Z, n<m <-> m>n.
 Proof.
   intros; split; omega.
 Qed.

 Lemma le_is_ge : forall n m:Z, n<=m <-> m>=n.
 Proof.
   intros; split; omega.
 Qed.

 Ltac bfunction_invert :=
   let H := fresh in 
   match goal with 
     | Htmp: (if ?e then true else false) = true|-_ => 
       assert (e = true) by (apply Classical_Prop.NNPP; intros H;
                             apply not_true_is_false in H; 
                             rewrite H in Htmp; inversion Htmp)
   end.

 Lemma if_eq_true_cond_is_true: 
   forall x:bool, (if x then true else false) = true <-> x =true.
   intros.
   split.
   intro.
   bfunction_invert;auto.
   intro.
   rewrite H; auto.
 Qed.


  Ltac tidspec_dec_true := try (rewrite TcbMod.set_a_get_a in *; [idtac | apply tidspec.eq_beq_true; auto]).
  Ltac tidspec_dec_false := try (rewrite TcbMod.set_a_get_a' in *; [idtac | apply tidspec.neq_beq_false; auto]).

  
  Ltac tidspec_dec x y :=let t := fresh
                                  with t1 := fresh
                                             with t2 := fresh
                                                       in remember (Classical_Prop.classic (x=y)) as t; 
                                                       destruct t as [t1| t2];  [rewrite t1 in * ; 
                                                                                  tidspec_dec_true | tidspec_dec_false].

 Ltac ecbspec_dec_true x := 
   let H := fresh in let H0 := fresh in 
                     remember (EcbMod.beq_refl x) as H eqn: H0; 
                       clear H0; try rewrite (EcbMod.get_a_sig_a _ H); 
                       try rewrite H; try rewrite EcbMod.set_a_get_a; auto.

Ltac ecbspec_dec_false v Hneq := 
  let H := fresh in let H0 := fresh in
                    remember (tidspec.neq_beq_false Hneq) as H eqn:H0; 
                      clear H0; try rewrite (EcbMod.get_a_sig_a' _ H); 
                      rewrite (EcbMod.set_a_get_a' v _ H).

Ltac ecbspec_dec v x a := 
  let H0 := fresh in let H0' := fresh in 
                     remember (Classical_Prop.classic (x=a)) as H0 eqn: H0'; 
                       clear H0'; destruct H0;[ rewrite -> H0 in *; 
                                                ecbspec_dec_true a | ecbspec_dec_false v H0].
                                  
Lemma nthval'_has_value : 
  forall l len n, array_type_vallist_match Tint8 l ->
                  length l = len -> 
                  (n < len)%nat ->
                  exists x, nth_val' n l = Vint32 x /\ true = rule_type_val_match Tint8 (Vint32 x).
Proof.
  intro.
  induction l.
  intros.
  simpl in H0.
  rewrite <- H0 in H1.
  inversion H1.

  intros.
  induction n.
  inversion H.
  simpl in H2.
  destruct a; try inversion H2.
  exists i.
  split ; auto.

  simpl nth_val'.
  apply (IHl (pred len)).
  inversion H;  auto.
  simpl in H0.
  omega.
  omega.
Qed.


Lemma mod_0_div_eq_eq: 
  forall a b c, c>0 -> a mod c =  b mod c  -> a / c = b / c -> a =b.
  intros.
  rewrite (Z_div_mod_eq b c).
  rewrite (Z_div_mod_eq a c).
  rewrite H1; rewrite H0.
  auto.
  omega.
  omega.
Qed.

Ltac solve_int_range i:= 
  repeat rewrite_un_repr; split; 
  [try omega| get_int_max;
              try intrange i omega; try omega]; 
  try intrange i omega.

Ltac simpl_int_repr H :=
  match type of (H) with 
    |  $ (?x) = $ (?y) =>
       let H' := fresh in 
       assert ( Int.unsigned ($ x) =Int.unsigned ($ y)) as H' by (rewrite H; trivial);
         try  rewrite Int.unsigned_repr in H'; 
         repeat rewrite_un_repr_in H'
  end.

Ltac solve_mod_range tac :=
  match goal with 
    |  |- _ <= ?a mod ?x <= _ => 
       let H:= fresh in  assert (0<x) as H by omega;
                       set (Z.mod_pos_bound a x H); tac; clear H
  end.

Ltac copy H := 
  let copy_of_H := fresh in 
  let e:= fresh in  remember H as copy_of_H eqn: e; clear e.

Ltac simpl_mod_in H := 
  try rewrite Zminus_mod in H;
  try rewrite Z_mod_same_full in H;
  try rewrite <- Zminus_0_l_reverse in H;
  try rewrite <- Zmod_div_mod in H;
  [idtac| try omega ..| try (apply Zdivide_intro with 1; auto)].


Ltac clear_useless_int32 :=
  match goal with
    | a : int32 |- _ => clear dependent a
  end.

Ltac clear_all_useless_int32 := repeat clear_useless_int32.

Lemma a_mult_b_ge_b : forall a b, 0<a -> 0<=b -> a*b >= b.
Proof.  
  intros.
  apply Zle_lt_or_eq in H0.
  elim H0; intros.
  apply Zlt_le_succ in H.
  simpl in H.
  assert (a = Z.succ (Z.pred a)) by omega.
  rewrite H2 at 1.
  rewrite <- Zmult_succ_l_reverse.
  assert (Z.pred a * b >=0).
  revs.
  apply Zmult_gt_0_le_0_compat.
  omega.
  omega.
  omega.
  rewrite <- H1.
  rewrite <- Zmult_0_r_reverse.
  omega.
Qed.


Lemma div_in_intrange: 
  forall x a mx, 0<=x <=mx -> a>0 -> 0<=x/a<=mx.
Proof.
  intros.
  split.
  revs.
  apply Z_div_ge0.
  omega.
  omega.
  apply Z.div_le_upper_bound.
  omega.
  elim H; intros.
  eapply Zle_trans.
  exact H2.
  revs.
  apply a_mult_b_ge_b; omega.
Qed.


Ltac solve_int_range' := 
  match goal with 
    | i : int32 |- _ =>
      let xval := fresh in 
      let xrange := fresh in destruct i as [xval xrange]; 
                            unfold Int.modulus, two_power_nat, shift_nat in xrange; 
                            simpl in xrange; simpl in *;  
                            solve_int_range'
    | _ => subst; 
          try rewrite max_unsigned_val; solve [ omega | apply div_in_intrange; omega ]
  end.


Ltac rangesolver :=
  clear_all_useless_int32; 
  try solve_int_range';
  repeat (rewrite Int.unsigned_repr; try solve_int_range').

Ltac ur_rewriter := 
  rewrite Int.unsigned_repr; [idtac| try solve[rangesolver] ].

Ltac ur_rewriter_in H := 
  rewrite Int.unsigned_repr in H; [idtac|clear H; try solve[rangesolver] ].

Ltac trivial_ur_rewriterH H :=
  repeat (rewrite Int.unsigned_repr in H; [idtac |solve [split;[omega| rewrite max_unsigned_val; omega]]]).


Ltac bfunc_invertH H :=
  let HH := fresh in 
  match type of H with 
    | (if ?e then true else false) = false => 
      rename H into HH; destruct e as [H|H]; [inversion HH|idtac]; clear HH
    | (if ?e then true else false) = true  => 
      rename H into HH; destruct e as [H|H]; [idtac| inversion HH]; clear HH
  end.

Ltac Iltu_simplerH H := 
  unfold Int.ltu in H; bfunc_invertH H; try trivial_ur_rewriterH H.

Ltac Irepr_simplerH H :=  
  match type of (H) with 
    |  $ (?x) = $ (?y) => 
       let H' := fresh in rename H into H'; 
                         assert ( Int.unsigned ($ x) =Int.unsigned ($ y)) as H by (rewrite H'; trivial);
                         try rewrite Int.unsigned_repr in H; 
                         repeat rewrite_un_repr_in H;clear H'
  end.

Ltac trivial_mod_range :=
  match goal with 
    |  |- _ <= ?a mod ?x <= _ => 
       let H:= fresh in  assert (0<x) as H by omega;
                       set (Z.mod_pos_bound a x H); omega; clear H
  end.

Ltac Imod_simplerH H :=
  let H' := fresh in unfold Int.modu in H; 
                    repeat trivial_ur_rewriterH H; 
                    try (Irepr_simplerH H;[idtac| rewrite max_unsigned_val; trivial_mod_range]).

Ltac Zmod_simplerH H k newval := 
  match type of H with
    | ?a mod ?n = ?b =>
      let H' := fresh in 
      rewrite <- (Z_mod_plus _ k) in H;
        [idtac|omega]; assert ( a + k * n = newval) as H' by omega ; 
        rewrite H' in H; clear H'
  end.


Lemma unsigned_ge0 : 
  forall x, Int.unsigned x >=0.
Proof.
  intros.
  destruct x.
  simpl; omega.
Qed.

Lemma Zplus_minus : 
  forall z x, z+x-x=z. 
Proof.
  intros;omega.
Qed.


Ltac ge0_solver := 
  solve [omega| apply unsigned_ge0|  apply Z_div_ge0; [omega| ge0_solver] ].

Ltac le0_solver := revs; ge0_solver.

Ltac revsH H :=
  let H' := fresh in 
  match type of H with 
    |  ?a < ?b => assert (a < b -> b > a) as H' by omega; apply H' in H; clear H'
    |  ?a > ?b => assert (a > b -> b < a) as H'  by omega; apply H' in H; clear H'
    |  ?a >= ?b => assert (a>=b -> b <= a) as H' by omega; apply H' in H; clear H'
    |  ?a <= ?b => assert (a<=b -> b >= a) as H' by omega; apply H' in H; clear H'
  end.

Ltac Zdivsup_simplerH H := 
  match type of H with 
    | ?a / ?b < ?c =>
      let H'' := fresh in 
      let H' := fresh  in 
      let e := fresh in 
      rewrite (Z.mul_lt_mono_pos_r b) in H; 
        [idtac | omega]; rewrite (Z.add_lt_mono_r _ _ b ) in H; 
        assert ( a / b * b + b >= a ) as H'' by (apply (@a_div_b_multi_b_plus_b_ge_a a b); omega); 
        revsH H''; remember (Z.le_lt_trans _ _ _ H'' H) as H' eqn: e; 
        simpl in H'; clear e; clear H''
  end.

Ltac kzrevs := 
  match goal with 
    |  |- ?a < ?b => cut (b > a); [intro; omega| idtac]
    |  |- ?a > ?b => cut (b < a); [intro; omega| idtac]
    |  |- ?a >= ?b => cut (b <= a); [intro; omega| idtac]
    |  |- ?a <= ?b => cut (b >= a); [intro; omega| idtac]
    |  |- (?a < ?b)%nat => cut (b > a)%nat; [intro; omega| idtac]
    |  |- (?a > ?b)%nat => cut (b < a)%nat; [intro; omega| idtac]
    |  |- (?a >= ?b)%nat => cut (b <= a)%nat; [intro; omega| idtac]
    |  |- (?a <= ?b)%nat => cut (b >= a)%nat; [intro; omega| idtac]
  end.

Lemma int_not_leq : forall i j, i>=0 -> j >=0 ->  ~i + j < i. 
  intros.
  apply Zle_not_lt.
  omega.
Qed.

Lemma Z_prop : forall x y  a,  0<a -> (x + a * y - x) / a = y.
Proof.
  intros.
  assert (x + a * y -x = a * y) by omega. 
  rewrite H0.
  eapply Coqlib.Zdiv_unique with 0. 
  assert ((y * a) +0 = y*a) by omega.
  rewrite H1.
  apply Z.mul_comm.
  omega.
Qed.

Lemma prio_destruct1 :
  forall x,  0 <= x < 17 <->
             x = 0 \/ x = 1 \/  x = 2  \/ x = 3 \/ x = 4 \/ x = 5 \/ x = 6 \/ x = 7 \/ 
             x = 8 \/ x = 9 \/  x = 10  \/ x = 11 \/ x = 12 \/ x = 13  \/ x = 14 \/ x = 15 \/
             x = 16.
Proof.
  split.
  intros; omega.
  intros.
  repeat progress (destruct H; subst ; split; try omega).
Qed.

Lemma int_aux :
  Int.unsigned ($ (0 + (4 + 0) - (0 + (4 + 0)))) / Int.unsigned ($ 4) =0.
Proof.
  int auto.
Qed.


Lemma prio_destruct2 :
  forall x,  17 <= x < 32 <->
             x = 17 \/  x = 18  \/ x = 19\/ x = 20 \/ x = 21  \/ x = 22 \/ x = 23 \/
             x = 24 \/ x = 25 \/  x = 26  \/ x = 27 \/ x = 28 \/ x = 29  \/ x = 30 \/ x = 31.
Proof.
  split.
  intros; omega.
  intros.
  repeat progress (destruct H; subst ; split; try omega).
Qed.


Lemma prio_destruct3 :
  forall x,  32 <= x < 48 <->
             x = 32 \/ x = 33 \/  x = 34  \/ x = 35 \/ x = 36 \/ x = 37  \/ x = 38 \/ x = 39 \/
             x = 40 \/ x = 41 \/  x = 42  \/ x = 43 \/ x = 44 \/ x = 45  \/ x = 46 \/ x = 47.
Proof.
  split.
  intros; omega.
  intros.
  repeat progress (destruct H; subst ; split; try omega).
Qed.


Lemma prio_destruct4 :
  forall x,  48 <= x < 64 <->
             x = 48 \/ x = 49 \/  x = 50  \/ x = 51 \/ x = 52 \/ x = 53  \/ x = 54 \/ x = 55 \/
             x = 56 \/ x = 57 \/  x = 58  \/ x = 59 \/ x = 60 \/ x = 61  \/ x = 62 \/ x = 63.
Proof.
  split.
  intros; omega.
  intros.
  repeat progress (destruct H; subst ; split; try omega).
Qed.


Lemma prio_range_com :
  forall x,  0 <= x < 17 \/ 17 <= x < 32 \/  32 <= x < 48 \/  48 <= x < 64  <->
             0 <= x < 64.
Proof.
  split; intros;  omega.
Qed.

Lemma prio_destruct :
  forall x,  0 <= x < 64 <->
             x = 0 \/ x = 1 \/  x = 2  \/ x = 3 \/ x = 4 \/ x = 5 \/ x = 6 \/ x = 7 \/ 
             x = 8 \/ x = 9 \/  x = 10  \/ x = 11 \/ x = 12 \/ x = 13  \/ x = 14 \/ x = 15 \/
             x = 16 \/ x = 17 \/  x = 18  \/ x = 19 \/ x = 20 \/ x = 21  \/ x = 22 \/ x = 23 \/
             x = 24 \/ x = 25 \/  x = 26  \/ x = 27 \/ x = 28 \/ x = 29  \/ x = 30 \/ x = 31 \/
             x = 32 \/ x = 33 \/  x = 34  \/ x = 35 \/ x = 36 \/ x = 37  \/ x = 38 \/ x = 39 \/
             x = 40 \/ x = 41 \/  x = 42  \/ x = 43 \/ x = 44 \/ x = 45  \/ x = 46 \/ x = 47 \/
             x = 48 \/ x = 49 \/  x = 50  \/ x = 51 \/ x = 52 \/ x = 53  \/ x = 54 \/ x = 55 \/
             x = 56 \/ x = 57 \/  x = 58  \/ x = 59 \/ x = 60 \/ x = 61  \/ x = 62 \/ x = 63.
Proof.
  split;intros.
  apply prio_range_com in H.
  destruct H.
  apply prio_destruct1 in H.
  omega.
  destruct H.
  apply prio_destruct2 in H.
  omega.
  destruct H.
  apply prio_destruct3 in H.
  omega.
  apply prio_destruct4 in H.
  omega.
  omega.
Qed.

Lemma prio_prop :
  forall prio,
    0 <= prio ->
    prio < 64 ->
    Int.unsigned (Int.shru ($ prio) ($ 3)) < 8.
Proof.
  intros.
  eapply shru_3_lt_8.
  int auto.
Qed.

Lemma Z_le_nat :
  forall x, (0<= x < 8)%Z-> ( ∘x < 8) %nat.
Proof.
  intros.
  destruct H.
  remember ( ∘x) as  m.
  assert (Z.of_nat m <8).
  subst.
  rewrite nat_of_Z_max.
  assert (Z.max x 0 = x).
  eapply Zmax_left. omega.
  rewrite H1.
  auto.
  omega.
Qed.

Lemma val_inj_1 :
  val_inj
    (if Int.ltu Int.zero (Int.notbool Int.one) &&Int.ltu Int.zero (Int.notbool Int.one)
     then Some (Vint32 Int.one)
     else Some (Vint32 Int.zero)) = Vint32 Int.zero.
Proof.
  int auto.
Qed.

Lemma isptr_vundef2:
  forall x,
    isptr x -> val_inj
                 (bool_and (val_inj (notint (val_inj (val_eq x Vnull))))
                           (Vint32 (Int.notbool Int.one))) <> Vundef.
Proof.
  introv Histpr.
  destruct x; unfolds in Histpr; destruct Histpr; simp join;  tryfalse.
  simpl.
  int auto.
  simpl.
  introv Hf.
  inverts Hf.
  simpl.
  inverts H.
  destruct x.
  simpl.
  int auto.
  simpl. 
  introv hf; tryfalse.
Qed.

Lemma val_inj_12 :
  forall x , val_inj
               (bool_and
                  (val_inj
                     (notint (val_inj (val_eq (Vptr (x, Int.zero)) Vnull))))
                  (Vint32 (Int.notbool Int.one))) = Vint32 Int.zero.
Proof.
  int auto.
Qed.


Lemma val_inj_12' :
  forall x , isptr x -> val_inj
                          (bool_and
                             (val_inj
                                (notint (val_inj (val_eq x  Vnull))))
                             (Vint32 (Int.notbool Int.one))) = Vint32 Int.zero.
Proof.
  intros.
  unfolds in H.
  destruct H; simp join; int auto.
  simpl.
  destruct x0.
  int auto.
Qed.

Lemma isptr_vundef_not :
  forall x,  isptr x -> 
             val_inj
               match val_inj (notint (val_inj (val_eq x Vnull))) with
                 | Vundef => None
                 | Vnull => None
                 | Vint32 n2 =>
                              if Int.ltu Int.zero (Int.notbool Int.one) && Int.ltu Int.zero n2
                              then Some (Vint32 Int.one)
                              else Some (Vint32 Int.zero)
                 | Vptr _ => None
               end <> Vundef.
Proof.  
  intros.
  destruct H; simp join.
  simpl.
  int auto.
  simpl.
  introv Hf.
  tryfalse.
  destruct x0.
  simpl.
  int auto.
  simpl.
  introv Hf; tryfalse.
Qed.


Lemma val_inj_122 :
  forall x ,  isptr x ->
              val_inj
                match val_inj (notint (val_inj (val_eq x Vnull))) with
                  | Vundef => None
                  | Vnull => None
                  | Vint32 n2 =>
                    if Int.ltu Int.zero (Int.notbool Int.one) &&
                               Int.ltu Int.zero n2
                              then Some (Vint32 Int.one)
                    else Some (Vint32 Int.zero)
                  | Vptr _ => None
                end = Vint32 Int.zero.
Proof.
  intros.
  destruct H; simp join; simpl; int auto.
  destruct x0.
  int auto.
Qed.


Lemma int_land_zero:
  forall x,  Int.zero&ᵢ(Int.one<<ᵢ(x &ᵢ$ 7)) <> Int.one<<ᵢ(x &ᵢ$ 7).
Proof.
  introv Hf.
  rewrite Int.and_zero_l in Hf.
  rewrite Int.shl_mul_two_p in Hf.
  rewrite Int.mul_commut in Hf.
  rewrite Int.mul_one in Hf.
  rewrite <- repr_zero in Hf.
  assert (Int.unsigned (x &ᵢ ($7)) <= 7) as Hasrt.  
  rewrite Int.and_commut.
  eapply Int.and_le; eauto.
  assert (0 <=Int.unsigned ( x &ᵢ$ 7)).
  apply Int.unsigned_range_2.
  remember ( Int.unsigned (x &ᵢ$ 7)) as y.
  assert (two_p 0  <=two_p y <= two_p 7).
  split;eapply two_p_monotone; omega.
  simpl in H0.
  unfold  two_power_pos in H0.
  unfold shift_pos in H0.
  simpl in H0.
  remember (two_p y) as py.
  assert (Int.ltu ($ 0) ($ py) = true).
  clear Heqy Heqpy.
  int auto.
  rewrite <- Hf in H1.
  clear Heqy.
  clear Heqpy.
  int auto.
Qed.

Lemma nat8_des:
  forall x2 Heq ,
    (Heq < 8) %nat ->
    match Heq with
      | 0%nat => Some (Vint32 Int.zero)
      | 1%nat => Some (Vint32 Int.zero)
      | 2%nat => Some (Vint32 Int.zero)
      | 3%nat => Some (Vint32 Int.zero)
      | 4%nat => Some (Vint32 Int.zero)
      | 5%nat => Some (Vint32 Int.zero)
      | 6%nat => Some (Vint32 Int.zero)
      | 7%nat => Some (Vint32 Int.zero)
      | S (S (S (S (S (S (S (S _))))))) => None
    end = Some (Vint32 x2) -> x2 = Int.zero.
Proof.
  do 8 ( destruct Heq;
         try solve [introv H Heq; inverts Heq; auto]).
  intros.
  inverts H0.
Qed.


Lemma leftmoven:
  forall n,
    (0 <= n < 8)%nat ->
    $ 1<<ᵢ$ Z.of_nat n <> $ 0.
Proof.
  intros.
  do 8 (destruct n ;[ 
          simpl;
          unfolds;
          intros;
          int auto | idtac ]).
  omega.
Qed.



Lemma math_prop_l2 : 
  val_inj
             (if Int.eq ($ 1) ($ 0)
              then Some (Vint32 Int.one)
              else Some (Vint32 Int.zero)) = Vint32 Int.zero.
Proof.
  int auto.
Qed.

Lemma math_prop_l3 : val_inj
             (notint
                (val_inj
                   (if Int.eq ($1) ($ 0)
                    then Some (Vint32 Int.one)
                    else Some (Vint32 Int.zero)))) <>  Vint32 Int.zero.
Proof.
  int auto.
  simpl.
  introv Hf.
  inverts Hf.
Qed.

Ltac solve_disj:=
  match goal with
    | H : _ \/ _ |- _  =>
      let Hx := fresh in
      let Hy := fresh in
      (destruct H as [Hx | Hy]; [subst; eexists; simpl; splits; eauto| idtac])
    | _ => try (subst; eexists; simpl; splits; eauto)
  end.


Lemma int8_neq0_ex:
  forall i ,
    Int.unsigned i <= 255 ->
    Int.eq i ($ 0) = false ->
    exists n,  (0 <= n < 8)%nat /\ i &ᵢ($ 1<<ᵢ$ Z.of_nat n) = $ 1<<ᵢ$ Z.of_nat n.
Proof.
  intros.
  unfold Int.eq in H0.
  destruct (zeq (Int.unsigned i) (Int.unsigned ($ 0))).
  inversion H0.
  get_unsigned_sz_sup i 8.
  set (Int.bits_size_1 i).
  inversion o.
  rewrite H5 in n.
  int auto.
  exists (Z.to_nat (Z.pred (Int.size i))).
  rewrite int_not_0_sz_not_0 in n.
  split.
  split.
  omega.
  handle_z2n_lt_nat.
  get_unsigned_sz_inf i.
  omega.
  rewrite (Z2Nat.id (Z.pred (Int.size i))).
  int auto.
  rewrite Z.land_comm.
  apply and_xy_x.
  intros.
  destruct (Z.eq_dec n0 (Z.pred (Int.size i))).
  subst.
  exact H5.
  rewrite Z.shiftl_mul_pow2 in H6.
  rewrite Z.mul_1_l in H6.
  rewrite Z.pow2_bits_false in H6.
  inversion H6.
  auto.
  get_unsigned_sz_inf i.
  omega.
  get_unsigned_sz_inf i.
  omega.
  get_unsigned_sz_inf i.
  rewrite Int.Zshiftl_mul_two_p.
  rewrite Z.mul_1_l.
  split.
  int auto.
  apply lt_imply_le.
  rewrite lt_is_gt.
  apply two_p_gt_ZERO.
  omega.
  int auto.
  rewrite<- le_is_ge in H3.
  rewrite Z.pred_le_mono in H3.
  eapply Zle_trans.
  int auto.
  apply two_p_monotone.
  split.
  int auto.
  exact H3.
  simpl.
  unfold two_power_pos.
  unfold shift_pos.
  simpl.
  omega.
  int auto.
  get_unsigned_sz_inf i.
  int auto.
Qed.



Lemma int_true_le255:
  forall x,
    (if Int.unsigned x <=? Byte.max_unsigned then true else false) = true ->
    Int.unsigned x <= 255.
Proof.
  introv Hin.
  remember (Int.unsigned x <=? Byte.max_unsigned) as Hbool.
  destruct Hbool.
  unfold Byte.max_unsigned in HeqHbool.
  simpl in HeqHbool.
  apply eq_sym in HeqHbool.
  eapply Zle_bool_imp_le; eauto.
  tryfalse.
Qed.


Lemma nat8_ex_shift3:
  forall n,
    (0 <= n < 8) %nat ->
    exists y, $ Z.of_nat n = Int.shru ($ y) ( $ 3) /\ 0  <= y < 64.
Proof.
  intros.
  assert (n = 0 \/ n =1 \/ n=2 \/ n=3 \/ n=4 \/ n=5\/ n=6 \/ n = 7) %nat by omega.
  destruct H0.
  subst.
  simpl.
  exists 4.
  split; try omega.
  unfolds.
  int_auto_simpl.
  destruct H0.
  subst.
  simpl.
  exists 8.
  split; try omega.
  unfolds.
  int_auto_simpl.
  destruct H0.
  subst.
  simpl.
  exists 16.
  split; try omega.
  unfolds.
  int_auto_simpl.
  unfold Z.shiftr.
  simpl.
  auto.
  destruct H0.
  subst.
  simpl.
  exists 24.
  split; try omega.
  unfolds.
  int_auto_simpl.
  unfold Z.shiftr.
  simpl.
  auto.
  destruct H0.
  subst.
  simpl.
  exists 32.
  split; try omega.
  unfolds.
  int_auto_simpl.
  int auto.
  destruct H0.
  subst.
  simpl.
  exists 40.
  split; try omega.
  unfolds.
  int_auto_simpl.
  int auto.
  destruct H0.
  subst.
  simpl.
  exists 48.
  split; try omega.
  unfolds.
  int_auto_simpl.
  int auto.
  subst.
  simpl.
  exists 56.
  split; try omega.
  unfolds.
  int_auto_simpl.
  int auto.
Qed.

Lemma math_des88:
  forall n xx, 
    (0 <= n < 8)%nat ->
    (xx = $ 0 \/
     xx = $ 1 \/
     xx = $ 2 \/ xx = $ 3 \/ xx = $ 4 \/ xx = $ 5 \/ xx = $ 6 \/ xx = $ 7) ->
    exists y, 0 <= y < 64 /\ xx = $ y &ᵢ $ 7 /\ ($ Z.of_nat n = Int.shru ($ y) ( $ 3)).
Proof.
  intros.
  assert (n = 0 \/ n =1 \/ n=2 \/ n=3 \/ n=4 \/ n=5\/ n=6 \/ n = 7) %nat by omega.
  destruct H0.
  destruct H1; [subst; exists 0; int auto | idtac..].
  destruct H1; [subst; exists 8; int auto | idtac..].
  destruct H1; [subst; exists 16; int auto | idtac..].
  destruct H1; [subst; exists 24; int auto | idtac..].
  destruct H1; [subst; exists 32; int auto | idtac..].
  destruct H1; [subst; exists 40; int auto | idtac..].
  destruct H1; [subst; exists 48; int auto | idtac..].
  subst; exists 56; int auto.
  destruct H0.
  destruct H1; [subst; exists 1; int auto | idtac..].
  destruct H1; [subst; exists 9; int auto | idtac..].
  destruct H1; [subst; exists 17; int auto | idtac..].
  destruct H1; [subst; exists 25; int auto | idtac..].
  destruct H1; [subst; exists 33; int auto | idtac..].
  destruct H1; [subst; exists 41; int auto | idtac..].
  destruct H1; [subst; exists 49; int auto | idtac..].
  subst; exists 57; int auto.
  
  destruct H0.
  destruct H1; [subst; exists 2; int auto | idtac..].
  destruct H1; [subst; exists 10; int auto | idtac..].
  destruct H1; [subst; exists 18; int auto | idtac..].
  destruct H1; [subst; exists 26; int auto | idtac..].
  destruct H1; [subst; exists 34; int auto | idtac..].
  destruct H1; [subst; exists 42; int auto | idtac..].
  destruct H1; [subst; exists 50; int auto | idtac..].
  subst; exists 58; int auto.
  
  destruct H0.
  destruct H1; [subst; exists 3; int auto | idtac..].
  destruct H1; [subst; exists 11; int auto | idtac..].
  destruct H1; [subst; exists 19; int auto | idtac..].
  destruct H1; [subst; exists 27; int auto | idtac..].
  destruct H1; [subst; exists 35; int auto | idtac..].
  destruct H1; [subst; exists 43; int auto | idtac..].
  destruct H1; [subst; exists 51; int auto | idtac..].
  subst; exists 59; int auto.

  destruct H0.
  destruct H1; [subst; exists 4; int auto | idtac..].
  destruct H1; [subst; exists 12; int auto | idtac..].
  destruct H1; [subst; exists 20; int auto | idtac..].
  destruct H1; [subst; exists 28; int auto | idtac..].
  destruct H1; [subst; exists 36; int auto | idtac..].
  destruct H1; [subst; exists 44; int auto | idtac..].
  destruct H1; [subst; exists 52; int auto | idtac..].
  subst; exists 60; int auto.

  destruct H0.
  destruct H1; [subst; exists 5; int auto | idtac..].
  destruct H1; [subst; exists 13; int auto | idtac..].
  destruct H1; [subst; exists 21; int auto | idtac..].
  destruct H1; [subst; exists 29; int auto | idtac..].
  destruct H1; [subst; exists 37; int auto | idtac..].
  destruct H1; [subst; exists 45; int auto | idtac..].
  destruct H1; [subst; exists 53; int auto | idtac..].
  subst; exists 61; int auto.

  destruct H0.
  destruct H1; [subst; exists 6; int auto | idtac..].
  destruct H1; [subst; exists 14; int auto | idtac..].
  destruct H1; [subst; exists 22; int auto | idtac..].
  destruct H1; [subst; exists 30; int auto | idtac..].
  destruct H1; [subst; exists 38; int auto | idtac..].
  destruct H1; [subst; exists 46; int auto | idtac..].
  destruct H1; [subst; exists 54; int auto | idtac..].
  subst; exists 62; int auto.

  subst.
  destruct H1; [subst; exists 7; int auto | idtac..].
  destruct H0; [subst; exists 15; int auto | idtac..].
  destruct H0; [subst; exists 23; int auto | idtac..].
  destruct H0; [subst; exists 31; int auto | idtac..].
  destruct H0; [subst; exists 39; int auto | idtac..].
  destruct H0; [subst; exists 47; int auto | idtac..].
  destruct H0; [subst; exists 55; int auto | idtac..].
  subst; exists 63; int auto.
Qed.

 
Lemma eight_destruct: 
  forall x, 0<=x<8 <-> x=0 \/ x=1 \/ x=2\/x=3\/x=4\/x=5\/x=6\/x=7.
Proof.
  intro.
  split;
    intro;
    omega.
Qed.

Lemma ltu_ex_and :
  forall vv,
    Int.ltu ($ 0) vv = true->
    Int.unsigned vv <= 255 ->
    exists x,
      vv&ᵢ(Int.one<<ᵢ x) = Int.one<<ᵢ x /\
         (x = $0 \/ x = $1 \/ x = $2 \/ x = $3 \/
          x = $4 \/ x = $5 \/ x = $6 \/ x = $7).
Proof.      
  intros.
  assert (Int.eq vv ($0) = false).
  unfold Int.eq.
  destruct (zeq (Int.unsigned vv) (Int.unsigned ($0))).
  unfold Int.ltu in H.
  rewrite e in H.
  tryfalse.
  auto.
  lets Hxa :  int8_neq0_ex H0 H1; eauto.
  destruct Hxa.
  eexists ($ (Z.of_nat x)).
  split.
  elim H2; intros.
  exact H4.
   elim H2; intros.
  assert (0<= (Z.of_nat x) < 8) by  omega.
  rewrite eight_destruct in H5.
  repeat (elim H5; clear H5; intro H5;[rewrite H5; auto 8| idtac]).
  repeat right; rewrite H5;  auto.
Qed.


Lemma inlist_ex :
  forall x4 (x:tidspec.A),
    In x x4 -> exists y z,  x4 = y :: z.   
Proof.
  inductions x4.
  intros.
  simpl in H.
  tryfalse.
  intros.
  simpl in H.
  destruct H.
  subst.
  do 2 eexists; eauto.
  eapply IHx4 in H.
  simp join.
  do 2 eexists; eauto.
Qed.

Lemma l4 :  
  forall i, val_inj
              (notint
                 (val_inj
                    (if Int.eq i ($ 0)
                     then Some (Vint32 Int.one)
                               else Some (Vint32 Int.zero)))) <> 
            Vint32 Int.zero ->   Int.eq i ($ 0) = false.
Proof.
  intros.
  assert (Int.eq i ($ 0) = true \/ Int.eq i ($ 0) = false).
  destruct (Int.eq i ($ 0)); auto.
  destruct H0; auto.
  rewrite H0 in H.
  simpl in H.
  unfold Int.notbool in H.
  rewrite eq_one_zero in H.
  false.
Qed.

Lemma list_prop1 : 
  forall (t: Type) (a:t) (l1 l2: list t), l1 ++ ((a::nil) ++ l2) = l1 ++ (a::l2).
Proof.
  intros.
  rewrite <- app_comm_cons.
  rewrite app_nil_l.    
  auto.
Qed.


Lemma  l5 : 
  forall i , val_inj
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
                      else Some (Vint32 Int.zero)))) = Vnull -> i = $ 0.
Proof.
  intros.
  assert (Int.eq i ($ 0) = true \/ Int.eq i ($ 0) = false).
  destruct (Int.eq i ($ 0)); auto.
  destruct H0.
  assert (if Int.eq i ($ 0) then i = $ 0 else i <> $ 0) by (apply Int.eq_spec).
  rewrite H0 in H1.
  auto.
  rewrite H0 in H.
  destruct H.
  simpl in H.
  unfold Int.notbool in H.
  rewrite Int.eq_true in H.
  inverts H.   
  simpl in H.
  unfold Int.notbool in H.
  rewrite Int.eq_true in H.
  inverts H.
Qed.




Ltac usimpl H := unfolds in H; simpl in H; inverts H.


Lemma int_usign_eq :
  forall m,
    0 <= m -> m <= Int.max_unsigned ->
    (Int.unsigned ($ m)) = m.
Proof.
  int auto.
  int auto.
Qed.




Lemma length_zero_nil : 
  forall (t : Type) (x : list t), length x = 0%nat -> x = nil.
Proof.
  intros.
  destruct x.
  auto.
  simpl in H.
  inverts H.
Qed.

Lemma nil_simp : 
  forall  (t : Type) (x : list t), nil ++ x = x.
Proof.
  simpl.
  auto.
Qed.


Lemma ge_0_minus_1_in_range: 
  forall i2,
    Int.unsigned i2 <= 65535 -> 
    Int.ltu ($ 0) i2 = true -> 
    Int.unsigned (i2 -ᵢ $ 1) <=? Int16.max_unsigned = true.
Proof.
  intros.
  unfold Int.ltu in H0.
  rewrite <- Zle_is_le_bool.
  unfold Int16.max_unsigned.
  unfold Int16.modulus.
  unfold two_power_nat.
  unfold Int16.wordsize.
  unfold Wordsize_16.wordsize.
  simpl.
  int auto.
  int auto.
Qed.



Lemma notint_neq_zero_eq: 
  forall x y,
    val_inj
      (notint
         (val_inj
            (if Int.eq x y
             then Some (Vint32 Int.one)
             else Some (Vint32 Int.zero)))) <> 
    Vint32 Int.zero -> Int.eq x y = false.
Proof.
  intros.
  unfold val_inj in H.
  destruct (Int.eq x y).
  unfold notint in H.
  unfolds in H.
  unfold Int.notbool in H.
  rewrite eq_one_zero in H.
  tryfalse.
  auto.
Qed.



Fixpoint all_elem_p {X:Type} p (l: @list X) := 
  match l with
    | nil => True
    | h :: t => p h = true /\ all_elem_p p t
  end.

Lemma array_type_vallist_match_is_all_elem_p:
  forall t l, array_type_vallist_match t l <-> all_elem_p (rule_type_val_match t) l.
Proof.
  intros.
  split.
  intro.
  induction l.
  auto.
  simpl.
  simpl in H.
  inversion H.
  auto.
  intro.
  induction l; auto.
  simpl in *; auto.
  inversion H; auto.
Qed.

Lemma all_elem_hold_for_upd: 
  forall n x l p, 
    all_elem_p p l -> 
    p x = true -> 
    all_elem_p p (update_nth_val n l x).
Proof.
  intro.
  induction n.
  intros.
  induction l.
  auto.
  simpl.
  inversion H; auto.

  intros.
  induction l.
  auto.
  simpl.
  inversion H.
  split; auto.
Qed.

Lemma not_and_p: 
  forall v'41 v'12, Int.unsigned v'12 <= 255 ->
                    Int.unsigned v'41 <= 128 -> 
                    Int.unsigned (v'12&ᵢInt.not v'41) <= 255.
Proof.
  intros.
  get_unsigned_sz_sup v'12 8.
  remember (Int.and_interval v'12 (Int.not v'41)).
  assert  (0<=Z.min (Int.size v'12) (Int.size (Int.not v'41)) <= 8).
  split.
  rewrite Z.min_glb_iff.
  split;[get_unsigned_sz_inf v'12; auto| get_unsigned_sz_inf (Int.not v'41); auto].
  rewrite -> Z.min_le_iff.
  left; omega.
  apply two_p_monotone in H5.
  inversion a.
  apply Zlt_succ_le; simpl.
  eapply Zlt_le_trans.
  exact H7.
  auto.
Qed.

Lemma not_and_p':
  forall v'41 v'12, Int.unsigned v'12 <= 255 ->
                    Int.unsigned v'41 <= 255 -> 
                    Int.unsigned (v'12&ᵢInt.not v'41) <= 255.
Proof.
  intros.
  get_unsigned_sz_sup v'12 8.
  remember (Int.and_interval v'12 (Int.not v'41)).
  assert  (0<=Z.min (Int.size v'12) (Int.size (Int.not v'41)) <= 8).
  split.
  rewrite Z.min_glb_iff.
  split;[get_unsigned_sz_inf v'12; auto| get_unsigned_sz_inf (Int.not v'41); auto].
  rewrite -> Z.min_le_iff.
  left; omega.
  apply two_p_monotone in H5.
  inversion a.
  apply Zlt_succ_le; simpl.
  eapply Zlt_le_trans.
  exact H7.
  auto.
Qed.



Lemma int_unsigned_or_prop:
  forall v'57 v'41, 
    Int.unsigned v'57 <= 255 ->
    Int.unsigned v'41 <= 128 ->
    Int.unsigned (Int.or v'57 v'41) <= 255.
Proof.
  intros.
  get_unsigned_sz_sup v'57 8.
  get_unsigned_sz_sup v'41 8.
  set (Int.or_interval v'57 v'41).
  assert (0<=Z.max (Int.size v'57) (Int.size v'41) <= 8).
  split.
  rewrite Z.max_le_iff.
  left.
  get_unsigned_sz_inf v'57.
  auto.
  apply Z.max_lub; omega.
  apply two_p_monotone in H9.
  apply Zlt_succ_le; simpl.
  inversion a.
  eapply Zlt_le_trans.
  exact H11.
  auto.
Qed.





Lemma ltu_eq_false:
  forall i1 i2, Int.ltu i2 i1 = true -> Int.eq i1 i2 = false.
Proof.
  intros.
  unfold Int.ltu in H.
  assert ( (Int.unsigned i2) < (Int.unsigned i1)).
  unfold zlt in H.
  destruct ( Z_lt_dec (Int.unsigned i2) (Int.unsigned i1)).
  auto.
  inversion H.
  unfold Int.eq.
  unfold zeq.
  destruct (Z.eq_dec (Int.unsigned i1) (Int.unsigned i2)).
  rewrite e in H0.
  omega.
  auto.
Qed.

Lemma val_inj_i1_i2_lt:
  forall i1 i2,
    val_inj
      (bool_or
         (val_inj
            (if Int.ltu i2 i1
             then Some (Vint32 Int.one)
             else Some (Vint32 Int.zero)))
         (val_inj
            (if Int.eq i1 i2
             then Some (Vint32 Int.one)
             else Some (Vint32 Int.zero)))) = Vint32 Int.zero \/
    val_inj
      (bool_or
         (val_inj
            (if Int.ltu i2 i1
             then Some (Vint32 Int.one)
             else Some (Vint32 Int.zero)))
         (val_inj
            (if Int.eq i1 i2
             then Some (Vint32 Int.one)
             else Some (Vint32 Int.zero)))) = Vnull ->  Int.ltu i1 i2 = true.
Proof.
  intros.
  unfold val_inj in H.
  int auto;
    elim H;  intros;  int auto.
Qed.

Lemma val_inj_eq_p:
  forall x6 v'49 x,
    isptr x6 ->
    val_inj
      match x6 with
        | Vundef => None
        | Vnull => Some (Vint32 Int.zero)
        | Vint32 _ => None
        | Vptr (b2, ofs2) =>
          if peq v'49 b2
          then
            if Int.eq (x+ᵢInt.mul ($ 1) ($ 4)) ofs2
            then Some (Vint32 Int.one)
            else Some (Vint32 Int.zero)
          else Some (Vint32 Int.zero)
      end <> Vint32 Int.zero -> x6 = Vptr (v'49, (x+ᵢInt.mul ($ 1) ($ 4)) ).
Proof.
  intros.
  unfolds in H.
  destruct H.
  subst.
  simpl in H0;tryfalse.
  destruct H.
  subst.
  destruct x0.
  remember (peq v'49 b) as X.
  destruct X.
  subst.
  remember (Int.eq (x+ᵢInt.mul ($ 1) ($ 4)) i) as Y.
  destruct Y.
  simpl in H0; tryfalse.
  symmetry in HeqY.
  lets Hx: Int.eq_spec (x+ᵢInt.mul ($ 1) ($ 4)) i.
  rewrite HeqY in Hx.
  subst;auto.
  simpl in H0;tryfalse.
  simpl in H0;tryfalse.
Qed.

Lemma val_inj_eq_elim:
  forall x6 v'49 x,
    val_inj
      match x6 with
        | Vundef => None
        | Vnull => Some (Vint32 Int.zero)
        | Vint32 _ => None
        | Vptr (b2, ofs2) =>
          if peq v'49 b2
          then
            if Int.eq (x+ᵢInt.mul ($ 1) ($ 4)) ofs2
            then Some (Vint32 Int.one)
            else Some (Vint32 Int.zero)
          else Some (Vint32 Int.zero)
      end = Vint32 Int.zero \/
    val_inj
      match x6 with
        | Vundef => None
        | Vnull => Some (Vint32 Int.zero)
        | Vint32 _ => None
        | Vptr (b2, ofs2) =>
          if peq v'49 b2
          then
            if Int.eq (x+ᵢInt.mul ($ 1) ($ 4)) ofs2
            then Some (Vint32 Int.one)
            else Some (Vint32 Int.zero)
          else Some (Vint32 Int.zero)
      end = Vnull -> x6 <> Vptr (v'49,  (x+ᵢInt.mul ($ 1) ($ 4))).
Proof.
  intros.
  destruct H;destruct x6;tryfalse.
  introv hf; tryfalse.
  destruct a.
  destruct (peq v'49 b).
  subst.
  remember ( Int.eq (x+ᵢInt.mul ($ 1) ($ 4)) i ) as X.
  destruct X;simpl in H;tryfalse.
  intro.
  symmetry in HeqX.
  lets Hx: Int.eq_spec (x+ᵢInt.mul ($ 1) ($ 4)) i.
  rewrite HeqX in Hx.
  inverts H0.
  tryfalse.
  intro.
  inverts H0;tryfalse.
  destruct a.
   destruct (peq v'49 b).
  subst.
  remember ( Int.eq (x+ᵢInt.mul ($ 1) ($ 4)) i ) as X.
  destruct X;simpl in H;tryfalse.
  intro.
  inverts H0;tryfalse.
Qed.


Lemma isptr_val_inj_false: 
  forall x0, isptr x0 -> val_inj (val_eq x0 Vnull) = Vnull -> False.
Proof.
  intros.
  destruct x0;tryfalse.
  simpl in H0.
  simpl in H0.
  destruct a;
    tryfalse.
Qed.

Lemma array_int8u_nth_lt_len :
  forall vl m,
    array_type_vallist_match Int8u vl ->
    (m < length vl)%nat ->
    exists i, nth_val' m vl = Vint32 i /\ Int.unsigned i <= 255.
Proof.
  induction vl, m; intros; simpl in *.
  omega.
  omega.
  destruct a; simpl in *; destruct H; tryfalse.
  eexists; intuition eauto.
  clear - H.
  remember (Int.unsigned i <=? Byte.max_unsigned) as bool; destruct bool; tryfalse.
  eapply int_true_le255.
  rewrite <- Heqbool.
  auto.
  apply IHvl.
  intuition auto.
  omega.
Qed.

Lemma int_lemma1:
  forall i1 i2,
    Int.unsigned i1 <= 255 ->
    Int.unsigned i2 <= 255 ->
    Int.unsigned (i1 &ᵢ Int.not i2) <= 255.
Proof. 
  intros.
  get_unsigned_sz_sup i1 8.
  remember (Int.and_interval i1 (Int.not i2)).
  assert (0<=Z.min (Int.size i1) (Int.size (Int.not i2)) <= 8).
  split.
  rewrite Z.min_glb_iff.
  split.
  get_unsigned_sz_inf i1; auto.
  get_unsigned_sz_inf (Int.not i2); auto.

  rewrite -> Z.min_le_iff.
  left.
  omega.
  apply two_p_monotone in H5.
  inversion a.
  apply Zlt_succ_le; simpl.
  eapply Zlt_le_trans.
  exact H7.
  auto.
Qed.

Lemma array_type_vallist_match_hold :
  forall vl n t v,
    array_type_vallist_match t vl ->
    (n < length vl)%nat ->
    rule_type_val_match t v = true ->
    array_type_vallist_match t (update_nth_val n vl v).
Proof.
  induction vl, n; intros; simpl in *; intuition auto.
  apply IHvl; auto.
  omega.
Qed.

(*move to join_lib*)
Lemma tcbmod_neq_set_get:
  forall x y b tcbls,
    x <> y ->
    TcbMod.get (TcbMod.set tcbls y b) x =  TcbMod.get tcbls x.
Proof.
  intros.
  rewrite TcbMod.set_sem.
  remember (tidspec.beq y x ) as Hbol.
  destruct Hbol; auto.
  apply eq_sym in HeqHbol.
  apply tidspec.beq_true_eq in HeqHbol; tryfalse.
Qed.
 
Lemma ltu_zero_eq_zero:
  forall i, Int.unsigned i <= 65535 -> false = Int.ltu ($ 0) i -> i = Int.zero.
Proof.
  introv Hi Hj.
  int auto.
  assert (Int.unsigned i >= 0).
  int auto.
  assert (Int.unsigned i= 0) by omega.
  clear - H0.
  rewrite <- unsigned_zero in H0.
  apply unsigned_inj in H0.
  auto.
Qed.

Lemma bool_and_true_1 :
  forall {v1 v2 x},
    istrue x = Some true -> bool_and v1 v2 = Some x ->
    exists n1, v1 = Vint32 n1 /\ Int.ltu Int.zero n1 = true.
Proof.
  intros.
  unfolds in H0.
  destruct v1; tryfalse.
  destruct v2; tryfalse.
  destruct (Int.ltu Int.zero i && Int.ltu Int.zero i0) eqn : eq1.
  rewrite andb_true_iff in eq1; destruct eq1.
  eexists; split; eauto.
  inversion H0.
  unfolds in H.
  destruct x; tryfalse.
  inverts H0.
  rewrite Int.eq_true in H.
  inversion H.
Qed.

Lemma ltu_zero_notbool_true : 
  forall {i2},
    Int.ltu Int.zero (Int.notbool i2) = true -> Int.eq i2 Int.zero = true.
Proof.
  intros.
  unfold Int.notbool in H.
  destruct (Int.eq i2 Int.zero) eqn : eq1; auto.
Qed.

Lemma val_eq_zero_neq : 
  forall {v1 v2 i},
    val_eq v1 v2 = Some (Vint32 i) -> 
    Int.eq i Int.zero = true -> v1 <> v2.
Proof.
  intros.
  intro.
  substs.
  unfolds in H.
  destruct v2; tryfalse.
  inverts H.
  unfolds in H0.
  destruct (zeq (Int.unsigned Int.one) (Int.unsigned Int.zero)) eqn : eq1.
  inversion e.
  tryfalse.
  rewrite Int.eq_true in H.
  inverts H.
  unfolds in H0.
  destruct (zeq (Int.unsigned Int.one) (Int.unsigned Int.zero)) eqn : eq1; tryfalse.
  destruct a.
  rewrite peq_true in H.
  rewrite Int.eq_true in H.
  inverts H.
  unfolds in H0.
  destruct (zeq (Int.unsigned Int.one) (Int.unsigned Int.zero)) eqn : eq1; tryfalse.
Qed.


Lemma bool_and_true_gt: 
  forall {v1 v2 x},
    bool_and v1 v2 = Some x -> istrue x = Some true ->
    exists n1 n2, v1 = Vint32 n1 /\ 
                  v2 = Vint32 n2 /\ 
                  Int.ltu Int.zero n1 = true /\ Int.ltu Int.zero n2 = true.
Proof.
  intros.
  unfolds in H.
  destruct v1; tryfalse.
  destruct v2; tryfalse.
  destruct (Int.ltu Int.zero i && Int.ltu Int.zero i0) eqn : eq1.
  apply andb_true_iff in eq1.
  destruct eq1.
  do 2 eexists.
  eauto.
  inverts H.
  simpl in H0.
  rewrite Int.eq_true in H0.
  tryfalse.
Qed.


Lemma list_cons_assoc :
  forall {A} l1 l2 (n:A),
    l1 ++ n :: l2 = (l1 ++ n::nil) ++ l2.
Proof.
  intro. intro.
  inductions l1; intros.
  simpl; auto.
  rewrite <- app_comm_cons.
  rewrite IHl1.
  rewrite app_comm_cons.
  auto.
Qed.


Lemma upd_vallist_eq_length: 
  forall  vl n v',
    length vl = length (update_nth_val n vl v').
Proof.
  inductions vl.
  simpl. intros; auto.
  introv.
  simpl.
  destruct n.
  simpl. auto.
  simpl.
  erewrite IHvl.
  eauto.
Qed.



Lemma eq_1 :Int.zero+ᵢ($ 4+ᵢ($ 2+ᵢ($ 1+ᵢ$ 1))) = $ 8.
Proof.
  repeat int auto.
Qed.

Lemma eq_2 :  $ 8+ᵢ ($ 1) = $ 9.
Proof.
  repeat int auto.
Qed.

Lemma eq_3 :  $ 9+ᵢ ($ 1) = $10.
Proof.
  repeat int auto.
Qed.

Lemma eq_4  : $ 10+ᵢ($ 1) = $11.
Proof.
  repeat int auto.
Qed.

Lemma eq_5 :  $11+ᵢ ($ 1) = $ 12.
Proof.
  repeat int auto.
Qed.

Lemma eq_6 :  $ 12+ᵢ ($ 1) = $ 13.
Proof.
  repeat int auto.
Qed.

Lemma eq_7 :  $ 13+ᵢ($ 1) = $ 14.
Proof.
  repeat int auto.
Qed.

Lemma eq_8 :  $ 14+ᵢ ($ 1) = $ 15.
Proof.
  repeat int auto.
Qed.

Lemma eq_9 : $0+ᵢ$ 1 = $1.
Proof.
  rewrite <- Int.add_zero.
  int auto.
Qed.

Lemma eq_10 :$1+ᵢ$ 1 = $2.
Proof.
  int auto.
Qed.

Lemma eq_11 :$2+ᵢ$2 = $4.
Proof.
  int auto.
Qed.

Lemma eq_12 :$4+ᵢ$4 = $8.
Proof.
  int auto.
Qed.

Lemma eq_13 :$8+ᵢ$8 = $16.
Proof.
  int auto.
Qed.


Lemma is_length_neq_zero_elim:
  forall v'1, val_inj (val_eq (is_length (0%nat :: v'1)) (V$1)) <> Vint32 Int.zero -> v'1=nil.
Proof.
  intros.
  unfold val_inj in *.
  unfold is_length in *.
  destruct v'1;simpl in H;auto.
  assert (Int.eq Int.zero ($ 1) =false) by int_auto.
  rewrite H0 in H.
  tryfalse.
Qed.


Lemma z_le_7_imp_n: 
  forall x, Int.unsigned x <= 7  -> (Z.to_nat (Int.unsigned x) < 8)%nat.
Proof.
  intros.
  handle_z2n_lt_nat.
Qed.

Lemma z_le_255_imp_n: 
  forall x, Int.unsigned x <= 255 -> (Z.to_nat (Int.unsigned x) < 256)%nat.
Proof.
  intros.
  handle_z2n_lt_nat.
Qed.



Lemma pos_to_nat_range_0_255:
  forall z, 0<=z -> z<=255 -> (0<=Z.to_nat z<=255)%nat.
Proof.
  intros.
  split.
  induction (Z.to_nat z); auto.
  unfold Z.to_nat.
  induction z; try  omega.
  assert (255%nat = Pos.to_nat ( Pos.of_nat 255)).
  simpl.
  unfold Pos.to_nat.
  int auto.
  rewrite H1.
  apply Pos2Nat.inj_le.
  int auto.
Qed.


Lemma sn_le_n_le_minus1:
  forall (n x:nat), (S n <= x -> n <= x-1)%nat. 
Proof.
  intros.
  omega.
Qed.


Lemma int_iwordsize_gt_3:
  Int.ltu ($ 3) Int.iwordsize = true.
Proof.
  int auto.
Qed.

Lemma shl3_add_range:
  forall x x0, 
    (Int.unsigned x <=? 7) = true -> 
    (Int.unsigned x0 <=? 7) = true ->
    Int.unsigned ((x<<ᵢ$ 3) +ᵢ x0) <=? 63 =true.
Proof.
  intros.
  rewrite <- Zle_is_le_bool in *.
  Ltac auto_shiftl := unfold Z.shiftl; unfold Pos.iter; int auto.
  auto_shiftl.
  auto_shiftl.
  int auto; auto_shiftl.
  int auto; auto_shiftl.
Qed.


Lemma int_unsigned_le_z2nat_lt:
  forall x z,Int.unsigned x <= z ->
             (Z.to_nat (Int.unsigned x) < Z.to_nat (z+1))%nat.
Proof.
  intros.
  remember (Int.unsigned_range x).
  clear Heqa.
  elim a.
  intros.
  assert (z>=0).
  omega.
  apply Z2Nat.inj_lt.
  auto.
  omega.
  int auto.
Qed.


Fixpoint my_nth_val' (n:nat)(vl:list val){struct vl} : val :=
  match vl with
    | nil => Vundef
    | v :: vl' => match n with
                    | 0%nat => v
                    | S n' => my_nth_val' n' vl'
                  end
  end.

Lemma my_nth_val'_eql_yours:
  forall n vl,
    nth_val' n vl = my_nth_val' n vl.
Proof.
  induction n; induction vl.
  unfold nth_val', my_nth_val'; trivial.
  unfold nth_val', my_nth_val'; trivial.
  unfold nth_val', my_nth_val'; trivial.
  unfold nth_val'; fold nth_val'.
  unfold my_nth_val'; fold my_nth_val'.
  apply IHn.
Qed.

Definition get_option_value (v : option val) : val :=
  match v with
    | None => Vundef
    | Some v' => v'
  end.

Lemma my_nth_val'_and_nth_val:
  forall n vl,
    my_nth_val' n vl = get_option_value (nth_val n vl).
Proof.
  unfold get_option_value.
  induction n; induction vl.
  unfold my_nth_val', nth_val; trivial.
  unfold my_nth_val', nth_val; trivial.
  unfold my_nth_val', nth_val'; trivial.
  unfold my_nth_val'; fold my_nth_val'.
  unfold nth_val; fold nth_val.
  apply IHn.
Qed.    

Lemma nth_val'_and_nth_val:
  forall n vl,
    nth_val' n vl = get_option_value (nth_val n vl).
Proof.
  intros n vl.
  rewrite <- my_nth_val'_and_nth_val.
  apply my_nth_val'_eql_yours.
Qed.




Lemma update_nth_val_length_eq:
  forall n vl v, length vl = length (update_nth_val n vl v).
Proof.
  intros n vl.
  exact (upd_vallist_eq_length vl n).
Qed.



Lemma int_unsigned_or_prop'
: forall v'57 v'41 : int32,
    Int.unsigned v'57 <= 255 ->
    Int.unsigned v'41 <= 255 ->
    Int.unsigned (Int.or v'57 v'41) <= 255.
Proof.
  intros.
  get_unsigned_sz_sup v'57 8.
  get_unsigned_sz_sup v'41 8.
  set (Int.or_interval v'57 v'41).
  assert (0<=Z.max (Int.size v'57) (Int.size v'41) <= 8).
  split.
  rewrite Z.max_le_iff.
  left.
  get_unsigned_sz_inf v'57.
  auto.
  apply Z.max_lub; omega.
  apply two_p_monotone in H9.
  apply Zlt_succ_le; simpl.
  inversion a.
  eapply Zlt_le_trans.
  exact H11.
  auto.
Qed.

Lemma nth_val'_imp_nth_val_int:
  forall z vl v,
    nth_val' (Z.to_nat z) vl = Vint32 v -> 
    nth_val ∘z vl = Some (Vint32 v).
Proof.
  unfold Coqlib.nat_of_Z.
  intro.
  induction (Z.to_nat z).
  intros.
  induction vl.
  simpl in H; inversion H.
  simpl in H; simpl; rewrite H; auto.
  intros.
  induction vl.
  inversion H.
  simpl.
  simpl in H.
  apply IHn; auto.
Qed.

Lemma unsigned_to_z_eq: 
  forall i,  nat_of_Z (Int.unsigned i) =Z.to_nat (Int.unsigned i) .
Proof.
  intros.
  int auto.
Qed.




Lemma Int_eq_false_Vptr_neq :
  forall i1 i2 b,
    Int.eq i1 i2 = false ->
    Vptr (b, i1) <> Vptr (b, i2).
Proof.
  intros.
  red.
  intros.
  inverts H0.
  rewrite Int.eq_true in H.
  tryfalse.
Qed.

Lemma qentries_eq_zero :
  forall (i:int32),
    (val_inj
       (if Int.ltu ($ 0) i
        then Some (Vint32 Int.one)
        else Some (Vint32 Int.zero)) = Vint32 Int.zero \/
     val_inj
       (if Int.ltu ($ 0) i
        then Some (Vint32 Int.one)
        else Some (Vint32 Int.zero)) = Vnull) ->
    i = Int.zero.
Proof. 
  intro i.
  remember (Int.ltu ($ 0) i) as b.
  destruct b.
  simpl. intros.
  destruct H; tryfalse.
  simpl. intros.
  destruct H; tryfalse.
  unfold Int.ltu in Heqb.
  rewrite Int.unsigned_repr in Heqb.
  assert (0>(Int.unsigned i) \/0<=(Int.unsigned i)).
  omega.
  destruct H0.
  rewrite zlt_true in Heqb.
  tryfalse.
  int auto.
  assert (0<Int.unsigned i \/ 0 = Int.unsigned i).
  omega.
  destruct H1.
  rewrite zlt_true in Heqb.
  tryfalse.  
  auto.
  unfold Int.zero.
  rewrite H1.
  rewrite Int.repr_unsigned.
  auto.
  int auto.
Qed.




Lemma math_prop_and:
  forall x0 n,
    0 <= Int.unsigned x0 < 64 ->
    (0 <= n < 8)%nat ->
    n <> Z.to_nat (Int.unsigned (Int.shru x0 ($ 3))) ->
    (Int.not ($ 1<<ᵢ(Int.shru x0 ($ 3)))&ᵢ($ 1<<ᵢ$ Z.of_nat n)) = ($ 1<<ᵢ$ Z.of_nat n).
Proof.
  introv Hin Hn.
  mauto.
Qed. 


Lemma math_prop_eq0:
  forall x0,
    0 <= Int.unsigned x0 < 64 ->
    Int.not ($ 1<<ᵢ(Int.shru x0 ($ 3)))&ᵢ
    ($ 1<<ᵢ$ Z.of_nat (Z.to_nat (Int.unsigned (Int.shru x0 ($ 3)
                                             )))) = $ 0.
Proof.
  intros;mauto.
Qed.


Lemma math_and_zero:
  forall n x ,
    0 <= Int.unsigned x < 64 ->
    (0 <= n < 8)%nat -> 
    n <> Z.to_nat (Int.unsigned (Int.shru x ($ 3))) ->
    ($ 1<<ᵢ$ Z.of_nat n)&ᵢ($ 1<<ᵢ(Int.shru x ($ 3))) = $ 0.
Proof.
  introv Hin Hn;mauto.
Qed.


Lemma  math_prop_neq_zero:
  forall  x,
    0 <= Int.unsigned x < 64 ->
    ($ 1<<ᵢ$ Z.of_nat (Z.to_nat (Int.unsigned (Int.shru x ($ 3)))))&ᵢ($ 1<<ᵢ(Int.shru x ($ 3))) <>
                                                                   $ 0.
Proof.
   intros;mauto.
Qed.

Lemma int_usigned_tcb_range:
  forall x,
    0 <= Int.unsigned x < 64 ->
    0 <=Int.unsigned (x&ᵢ$ 7) < 8 /\
    0 <= Int.unsigned (Int.shru  x ($ 3)) < 8.
Proof.
  intros;mauto.
Qed.


Lemma  prio_int_disj:
  forall x y,
    0 <= Int.unsigned x < 256 ->
    0 <= Int.unsigned y < 8 ->
    (x &ᵢ($ 1<<ᵢy) = $ 1<<ᵢy) \/ (x&ᵢ($ 1<<ᵢy) = $ 0).
Proof.
  intros;mauto_noto.
Qed.


Lemma nat_int64_range_eq:
  forall x,
    (0 <= Int.unsigned x < 64)  ->
    (0<=∘ (Int.unsigned x) < 64)% nat.
Proof.
  intros;mauto_noto.
Qed.


Lemma prio_neq_grpeq_prop :
  forall prio0 prio,
    0 <= Int.unsigned prio0 < 64 ->
    0 <= Int.unsigned prio < 64 ->
    prio0 <> prio -> 
    ∘(Int.unsigned (Int.shru prio0 ($ 3))) =  ∘(Int.unsigned (Int.shru prio ($ 3)))->
    (Int.not ($ 1<<ᵢ(prio&ᵢ$ 7))&ᵢ($ 1<<ᵢ(prio0&ᵢ$ 7))) =
    $ 1<<ᵢ(prio0&ᵢ$ 7).
Proof.
  introv H1 H2;mauto_noto.
Qed.


Lemma math_lshift_neq_zero:
  forall x0,
    0 <= Int.unsigned x0 < 64 ->
    Int.zero <> $ 1<<ᵢ$ Z.of_nat (Z.to_nat (Int.unsigned (Int.shru x0 ($ 3)))).
Proof.
  intros; mauto.
Qed.


Ltac simpl_hyp :=
  repeat progress
         match goal with
           | H : ?f _ = Some _ |- _  => unfold f in H; simpl in H; inverts H
         end.

Ltac funfold H:=
  match type of H with
    |  ?f _  =>
       unfold f in H  ;simp join; simpl_hyp
    |  ?f _ _  =>
       unfold f in H  ;simp join; simpl_hyp
    |  ?f _ _ _  =>
       unfold f in H  ;simp join; simpl_hyp
    |  ?f _ _ _ _ =>
       unfold f in H  ;simp join; simpl_hyp
    |  ?f _ _ _ _ _ =>
       unfold f in H  ;simp join; simpl_hyp
    | _ => idtac
  end.


Lemma nth_upd_neq :
  forall vl n m x y,
    n <> m ->
    nth_val n (update_nth_val m vl x) = Some y ->
    nth_val n vl = Some y.
Proof.
  inductions vl.
  intros;simpl.
  simpl in H0.
  auto.
  intros.
  simpl in H0.
  simpl.
  destruct n.
  destruct m.
  tryfalse.
  simpl in H0.
  auto.
  destruct m.
  simpl in H0.
  auto.
  simpl in H0.
  assert (n <> m) by omega.
  eapply IHvl; eauto.
Qed.     

Lemma nth_upd_eq :
  forall  vl n x y,
    nth_val n (update_nth_val n vl x) = Some y ->
    x = y.
Proof.
  inductions vl.
  simpl.
  intros; tryfalse.
  intros.
  simpl in H.
  destruct n.
  simpl in H.
  inverts H; auto.
  simpl in H.
  eapply IHvl; eauto.
Qed.

Lemma int_unsigned_inj:
  forall x,
    0 <= x <= Int.max_unsigned ->  $ x  = $ 0 ->  x = 0.
  intros.
  assert (Int.unsigned ($ x) = Int.unsigned ($ 0)).
  rewrite H0.
  auto.
  rewrite Int.unsigned_repr in H1.
  rewrite Int.unsigned_repr  in H1.
  auto.
  int auto.
  auto.
Qed. 

Lemma int_or_zero_split:
  forall x y,
    Int.or x y = $ 0 -> x = $0 /\ y = $ 0.
  introv Hi.
  unfolds in Hi.
  eapply int_unsigned_inj in Hi.
  apply Z.lor_eq_0_iff in Hi.
  simp join.
  rewrite <- unsigned_zero in H.
  apply unsigned_inj in H.
  auto.
  rewrite <- unsigned_zero in H0.
  apply unsigned_inj in H0.
  auto.
  assert (0 <= Int.unsigned x <= Int.max_unsigned ).
  apply Int.unsigned_range_2; auto.
  assert (0 <= Int.unsigned y <= Int.max_unsigned ).
  apply Int.unsigned_range_2; auto.
  apply Z_lor_range; auto.
Qed.



Lemma  math_prop_neq_zero2:
  forall  x,
    0 <= Int.unsigned x < 64 ->
    $ 1<<ᵢ(x&ᵢ$ 7) <>
    $ 0.
Proof.
  intros;mauto.
Qed.



Lemma int_eq_false_ltu : 
  forall x,
    Int.eq x ($ 0) = false -> 
    Int.ltu ($ 0) x = true.
Proof.
  int auto.
  assert ( 0<= Int.unsigned x) .
  clear  n H g.
  int auto.
  omega.
Qed.




Lemma  int_ltu_true:
  forall x x0,
    0 <= Int.unsigned x < 64  -> 
    Int.ltu ($ 0) (Int.or x0 ($ 1<<ᵢ(x&ᵢ$ 7))) = true.
Proof.
  intros.
  apply int_eq_false_ltu.
  apply Int.eq_false.
  assert (Int.or x0 ($ 1<<ᵢ(x&ᵢ$ 7)) <> $ 0 \/ Int.or x0 ($ 1<<ᵢ(x&ᵢ$ 7)) = $ 0) by
      tauto.
  destruct H0; auto.
  apply int_or_zero_split in H0.
  destruct H0.
  assert ( $ 1<<ᵢ(x&ᵢ$ 7)  <> $ 0).
  clear -H.
  mauto.
  tryfalse.
Qed.


Lemma math_prop_eq:
  forall x ,
    0 <= Int.unsigned x < 64  ->
    ($ 1<<ᵢ$ Z.of_nat (Z.to_nat (Int.unsigned (Int.shru x ($ 3))))) =
    $ 1<<ᵢ(Int.shru x ($ 3)).
Proof.
  intros;mauto.
Qed.


Lemma int8_range_nat:
  forall z,
    0 <= Int.unsigned z < 8 ->
    (0<=Z.to_nat (Int.unsigned z) <8)%nat.
Proof.
  intros;mauto.
Qed.



Lemma nat_of_Z_eq:
  forall x y,
    nat_of_Z (Int.unsigned x) = nat_of_Z (Int.unsigned y) ->
    x = y.
Proof.
  intros.
  eapply unsigned_inj.
  unfold nat_of_Z in H.
  eapply Z2Nat.inj; eauto.
  int auto.
  int auto.
Qed.



Lemma nth_upd_neqrev:
  forall (vl : vallist) (n m : nat) (x y : val),
    n <> m ->
    nth_val n vl = Some y ->
    nth_val n (update_nth_val m vl x) = Some y.
Proof.
  inductions vl.
  intros.
  simpl in *.
  auto.
  intros; simpl in *.
  destruct n.
  simpl.
  destruct m.
  tryfalse.
  simpl ; auto.
  destruct m.
  simpl.
  auto.
  eapply IHvl.
  omega.
  auto.
Qed.




Ltac invertsall :=
  repeat progress match goal with
                    | H : Some _ = Some _ |-
                      _=> inverts H
                  end.

Lemma int_ltu_false_eq0:
  forall x3,
    Int.ltu ($ 0) x3 = false ->
    Int.unsigned x3 = 0.
  intros.
  int auto.
  assert ( 0<= Int.unsigned x3).
  clear -x3.
  int auto.
  omega.
Qed.


Lemma zof_nat_eq_zero_zero:
  forall x ,  Z.of_nat x = 0 -> (x = 0)%nat.
Proof.
  intros.
  destruct x.
  auto.
  inversion H.
Qed.

Lemma  sub_zero_eq_rev:
  forall i1 i2 : int32,
    i1 = i2 -> i1-ᵢi2 = Int.zero. 
Proof.
  intros.
  subst.
  int auto.
Qed.

Lemma int_divu_zero:
  forall x,  Int.divu Int.zero x = Int.zero.
Proof.
  intros.
  int auto.
Qed.

Lemma z_split:
  forall x y,
    x <= y -> x = y \/  x < y.
Proof.
  intros.
  omega.
Qed.


Lemma int_minus4_mod4 : 
  forall x, Int.ltu x ($ 4) = false -> Int.modu (Int.sub x ($ 4)) ($ 4) = $ 0 ->(Int.unsigned x - 4) mod 4 = 0.
Proof.
  intros.
  unfold Int.ltu in H.
  bfunc_invert' H.
  rewrite_un_repr_in g.
  unfold Int.modu, Int.sub in H0.
  rewrite Int.unsigned_repr in H0.
  rewrite_un_repr_in H0.
  simpl_int_repr H0.
  auto.
  rewrite max_unsigned_val.
  solve_mod_range omega.
  rewrite_un_repr.
  rewrite max_unsigned_val.  
  split.
  omega.
  intrange x omega.
Qed.



Lemma isptr_length_nth:
  forall n vl,
    isptr (nth_val' n vl) -> (S n <= length vl)%nat. 
Proof.
  inductions n.
  simpl.
  destruct vl.
  intros.
  unfolds in H.
  destruct H; simp join; tryfalse.
  intros.
  simpl.
  omega.
  intros.
  simpl in H.
  destruct vl.
  unfolds in H.
  destruct H; simp join; tryfalse.
  apply IHn in H.
  simpl.
  omega.
Qed.




Lemma int_list_length_dec:
  forall (hml : list val) x1,
    Int.unsigned x1 = Z.pos (Pos.of_succ_nat (length hml)) ->
    Int.unsigned (x1-ᵢ$ 1) = Z.of_nat (length hml).
Proof.
  intros hml x1.
  intros.
  rewrite Zpos_P_of_succ_nat in H.
  int auto.
  int auto.
Qed.



Lemma list_append_split:
  forall (ls1 ls2 : list val) x vl,
    ls1 <> nil ->
    ls1 ++ ls2 = x :: vl ->
    exists l', ls1 = x::l' /\ vl = l' ++ ls2.
Proof.
  induction ls1;intros;tryfalse.
  simpl in H0.
  inversion H0.
  eexists;
  splits; auto.
Qed.



Lemma le_change: 
  forall a b, (a <= b -> b >=a)%nat.
Proof.
  intros.
  omega.
Qed.



Lemma int_nat_ltu_lt:
  forall x1 x,
    Int.unsigned x1 = Z.of_nat x ->
    Int.ltu ($ 0) x1 = true ->
    (0 < x) %nat.
Proof.
  intros.
  int auto.
Qed.



Lemma list_length_lt:
  forall l :  list msg ,  (0 < length l)%nat
                          -> exists x l',  l = x ::l'.
Proof.  
  inductions l.
  intros;simpl in *; omega.
  simpl.
  intros.
  do 2 eexists; eauto.
Qed.



Lemma math_prop_int_modu:
  forall x,
    Int.ltu x ($ 4) = false ->
    Int.modu (x-ᵢ$ 4) ($ 4) = $ 0 ->
    (Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) mod 4 = 0.
Proof.
  intros.
  int auto.
  simpl.
  apply int_unsigned_inj.
  assert (4>0) by omega.
  set (@Z_mod_lt (Int.unsigned x -4) 4 H1).
  int auto.
  auto.
  int auto.
  int auto.
  int auto.
  split.
  set (Ztrichotomy 0 (Int.unsigned x -4)).
  destruct (zlt (Int.unsigned x) 4).
  inversion H.
  omega.
  destruct x.
  simpl.
  unfold Int.modulus in intrange; unfold two_power_nat in intrange; unfold shift_nat in intrange;simpl in intrange.
  omega.
Qed.




Lemma nat_8_range_conver:
  forall x, (0 <= Z.to_nat (Int.unsigned x) < 8)%nat <->
            (Int.unsigned x < 8).
Proof. 
  intros.
  splits.
  intros.
  eapply Z2Nat.inj_lt. 
  clear -x.
  int auto.
  omega.
  simpl.
  unfold Pos.to_nat;simpl; omega.
  intros.
  mauto.
Qed.



Lemma nth_val'_imply_nth_val:
  forall n vl v,
    (n < length vl)%nat ->
    nth_val' n vl  = v ->
    nth_val n vl = Some v.
Proof.
  inductions n; inductions vl; simpl; intros; try omega; subst; auto.
  eapply IHn; try omega.
  auto.
Qed.


Lemma shrl_eq :
  forall x,
    (0 <= Z.to_nat (Int.unsigned x) < 8)%nat ->
    (Z.to_nat (Int.unsigned x)) =
    ∘(Int.unsigned (Int.shru ((x<<ᵢ$ 3)+ᵢ$ 0) ($ 3))).
Proof.
  introv Hn.
  apply nat_8_range_conver in Hn.
  mauto.
Qed.


Lemma math_64_le_8 :
  forall y,
    Int.unsigned y < 64 ->
    Int.unsigned (Int.shru y ($ 3)) <8.
Proof.
  introv H.
  mauto_noto.
Qed.


Lemma nat_x_prop_range:
  forall x ,
    (0 <= Z.to_nat (Int.unsigned x) < 8)%nat ->
    0 <= Int.unsigned ((x<<ᵢ$ 3)+ᵢ$ 0) < 64. 
Proof.
  introv Hr.
  apply nat_8_range_conver in Hr.
  mauto.
Qed.


Lemma math_8range_eqy:
  forall x y,
    (0 <= Z.to_nat (Int.unsigned x) < 8)%nat ->
    Int.unsigned y < 8 ->
    (((x<<ᵢ$ 3)+ᵢy)&ᵢ$ 7) = y.
Proof.
  introv Hx  Hr.
  apply nat_8_range_conver in Hx.
  mauto.
Qed. 

Lemma math_shrl_3_eq :
  forall x y,
    Int.unsigned y < 8 ->
    (0 <= Z.to_nat (Int.unsigned x) < 8)%nat ->
    (Int.shru ((x<<ᵢ$ 3)+ᵢy) ($ 3)) = x.
Proof.
  introv Hy Hx.
  apply nat_8_range_conver in Hx.
   mauto.
Qed.


Lemma math_88_prio_range:
  forall x y,
    Int.unsigned y < 8 ->
    (0 <= Z.to_nat (Int.unsigned x) < 8)%nat ->
    0 <= Int.unsigned ((x<<ᵢ$ 3)+ᵢy) < 64.
Proof.    
  introv Hy Hx.
  apply nat_8_range_conver in Hx.
  mauto.
Qed. 





Lemma math_and_shf_ltu_true:
  forall v x,
    Int.unsigned x < 64 ->
    v&ᵢ($ 1<<ᵢ(x&ᵢ$ 7)) = $ 1<<ᵢ(x&ᵢ$ 7) ->
    Int.ltu ($ 0) v = true.
Proof.
  introv Hi.
  assert (v = $0 \/ v<> $ 0) by tauto.
  destruct H.
  subst v.
  intros.
  rewrite Int.and_commut in H.
  rewrite Int.and_zero in H.
  assert ( 0<=Int.unsigned x < 64).
  clear H.
  int auto.
  lets Hsrs: math_prop_neq_zero2 H0 .
  unfold Int.zero in H.
  tryfalse.
  intros.
  eapply int_eq_false_ltu.
  eapply Int.eq_false; eauto.
Qed.


Lemma  nat_elim:
  forall x,
    Int.unsigned x < 8 ->
    $ Z.of_nat (Z.to_nat (Int.unsigned x)) = x.
Proof.
  introv Hi.
  mauto.
Qed.

Lemma int_ltu_shru_ltu:
  forall x  prio',
    Int.unsigned x < 8 ->
    Int.unsigned prio' < 64 ->
    Int.unsigned x < Int.unsigned (Int.shru prio' ($ 3)) ->
    Int.unsigned ((x<<ᵢ$ 3)+ᵢ$7) < Int.unsigned prio'.                      
Proof.
  introv Hx Hy .
  mauto_noto.
Qed.


Lemma int_add_lt_max :
  forall x y,
    Int.unsigned x < 8 ->
    Int.unsigned y < 8 ->
    Int.unsigned ((x<<ᵢ$ 3)+ᵢy)   <= Int.unsigned ((x<<ᵢ$ 3)+ᵢ$7).
Proof.
  introv Hx Hy.
  mauto.
Qed.

Lemma math_prio_8_lt:
  forall y prio',
    Int.unsigned y < 8 ->
    Int.unsigned prio' < 64 -> 
    Int.unsigned y <= Int.unsigned (prio'&ᵢ$ 7) ->
    Int.unsigned (((Int.shru prio' ($ 3))<<ᵢ$ 3)+ᵢy) <= Int.unsigned prio'.
Proof.  
  introv Hx Hp.
  mauto_noto.
Qed.




Ltac sifthen :=
  repeat progress
         match goal with
           | H : exists _, _ |- _ => destruct H
           | H : _ /\ _ |- _ => destruct H
           | H : context[if ?b then _ else _] |- _ =>
             let x := fresh "B" in (remember b as x);
               destruct x;         
               [match goal with
                  | H1 : true = (_ =? _)%positive  |- _ => 
                    rewrite Pos2Z.inj_eqb in H1;
                      apply eq_sym in H1;
                      apply Z.eqb_eq in H1;
                      inverts H1
                end | tryfalse]
         end.

Ltac fsimpl :=
  repeat progress
         match goal with
           | H : context[let (_, _) := ?x in _] |- _ => destruct x
           | _ => idtac
         end; sifthen;invertsall.


(*move to join_lib.*)
Lemma tcb_get_join:
  forall tcs ptcb prio t m,
    TcbMod.get tcs ptcb = Some (prio, t, m) ->
    exists tcs',
      TcbMod.join (TcbMod.sig ptcb (prio, t, m)) tcs' tcs.
Proof.
  intros.
  apply TcbMod.sub_exists_join.
  unfold TcbMod.sub.
  intros.
  unfold TcbMod.lookup in *.
  rewrite TcbMod.sig_sem in H0.
  assert ( ptcb = a \/ ptcb <> a ) by tauto.
  elim H1; intros.
  rewrite H2 in *.
  rewrite tidspec.eq_beq_true in H0.
  rewrite <- H0.
  auto.
  auto.
  rewrite tidspec.neq_beq_false in H0.
  inversion H0.
  auto.
Qed.



Lemma math_prop_ltu_mod:
  forall i,
    Int.ltu i ($ 4) = false ->
    Int.modu (i-ᵢ$ 4) ($ 4) = $ 0 ->
    4 * ((Int.unsigned i - 4) / 4) = Int.unsigned i - 4.
Proof.
  intros.
  apply (int_minus4_mod4 H) in H0.
  rewrite <- Z_div_exact_full_2; auto.
  introv Hf; tryfalse.
Qed.



Lemma math_prio_neq_zero:
  forall prio pri,
    0<=Int.unsigned prio < 64 ->
    0<=Int.unsigned pri < 64 ->
    prio <> pri ->
    ∘(Int.unsigned (Int.shru pri ($ 3))) = ∘(Int.unsigned (Int.shru prio ($ 3))) ->
    (Int.one<<ᵢ(pri&ᵢ$ 7))&ᵢ($ 1<<ᵢ(prio&ᵢ$ 7)) = $ 0.
Proof.
  introv Hr Hk Hj Hl.
  apply eq_sym in Hl.
  lets Hsa :   prio_neq_grpeq_prop  Hr Hk Hj Hl. 
  rewrite <- Hsa.
  rewrite <- Int.and_assoc.
  rewrite   Int.and_not_self.
  rewrite Int.and_commut.
  rewrite Int.and_zero.
  auto.
Qed.




Lemma math_xy_prio_cons:
  forall x y,
    Int.unsigned x < 8 ->
    Int.unsigned y < 8 ->
    0<= (Int.unsigned ((x<<ᵢ$ 3)+ᵢy)) < 64.
Proof.
  intros.
  mauto.
Qed.

Lemma nth_val'_imp_nth_val_vptr:
  forall  n (vl : list val) v,
    nth_val' n  vl = Vptr v -> nth_val n vl = Some (Vptr v).
Proof.
  inductions n; destruct vl; intros; simpl in *; tryfalse; auto.
  subst.
  auto.
Qed.



Lemma last_remain :
  forall  (y1 : list vallist) a,  
    y1 <> nil -> 
    last (a :: y1) nil = last y1 nil.
Proof.
  inductions y1.
  intros; tryfalse.
  intros.
  simpl.
  destruct y1; auto.
Qed.


Lemma  int_ltu_eq_false:
  forall x1,
    Int.ltu ($ 0) x1 = true ->
    Int.eq x1  Int.zero  = false.
Proof.
  intros.
  int auto.
Qed.

Lemma Z2Nat_0: forall a, a<=0 -> Z.to_nat a =0%nat.
  intros.
  destruct a;  simpl;  auto.
  set (Pos2Z.is_pos p).
  omega.
Qed.


Lemma Zle_natle : forall a b, a<=b -> (Z.to_nat a <= Z.to_nat b)%nat.
  intros.
  assert (a<=0 \/ a>0) by tauto.
  elim H0; intros.
  rewrite Z2Nat_0.
  omega.
  auto.

  assert (b<=0 \/ b>0) by tauto.
  elim H2.
  intros.
  omega.
  intros.

  rewrite <-  Z2Nat.inj_le; auto.
  omega.
  omega.
Qed.

Lemma math_le_trans:
  forall x y n,
    y <= Z.of_nat n ->
    (∘x < ∘y)%nat ->
    (∘x  <= n)%nat.
Proof.
  intros.
  unfold nat_of_Z in *.
  int auto.
  assert (Z.to_nat y <= n)%nat.

  rewrite <- (Nat2Z.id n).
  apply Zle_natle.
  auto.
  omega.
Qed.



Lemma prio_bit_and_zero:
  forall prio prio0,
    0 <= Int.unsigned prio0 < 64 ->
    0 <= Int.unsigned prio < 64 ->
    prio0 <> prio ->
    Z.to_nat (Int.unsigned (Int.shru prio ($ 3))) = Z.to_nat (Int.unsigned (Int.shru prio0 ($ 3))) ->
    ($ 1<<ᵢ(prio&ᵢ$ 7))&ᵢ($ 1<<ᵢ(prio0&ᵢ$ 7)) = Int.zero.
Proof.
  introv H H'.
  mauto_noto.
Qed.

Lemma or_and_combine:
  forall x y z, 
    x &ᵢ z = z ->
    y &ᵢ z = Int.zero ->
    (Int.or x y) &ᵢ z = z.
Proof.
  intros.
  rewrite Int.and_or_distrib_l.
  rewrite H0.
  rewrite H.
  apply Int.or_zero.
Qed.

Lemma or_and_distrib:
  forall x y z,
    (Int.or z x) &ᵢ y = y ->
    x &ᵢ y = Int.zero ->
    z &ᵢ y = y.
Proof.
  intros.
  rewrite Int.and_or_distrib_l in H.
  rewrite H0 in H.
  rewrite Int.or_zero in H.
  auto.
Qed.

Lemma or_and_distrib_zero:
  forall x y z,
    (Int.or z y) &ᵢ x = Int.zero ->
    y &ᵢ x = Int.zero ->
    z &ᵢ x = Int.zero.
Proof.
  intros.
  rewrite Int.and_or_distrib_l in H.
  rewrite H0 in H.
  rewrite Int.or_zero in H.
  auto.
Qed.
  

Lemma or_and_combine_zero:
  forall x y z,
    z &ᵢ x = Int.zero ->
    y &ᵢ x = Int.zero ->
    (Int.or z y) &ᵢ x = Int.zero.
Proof.
  intros.
   rewrite Int.and_or_distrib_l.
   rewrite H.
   rewrite H0.
   rewrite Int.or_zero.
   auto.
Qed.

Lemma neq_comm:
  forall T (a b:T),
    a <> b ->
    b <> a.
Proof.
  auto.
Qed.



Lemma math_pry_neq_prio_neq:
  forall x y z,
    Int.unsigned x <= 7 ->
    Int.unsigned y <= 7 ->
    0 <= z < 64 -> 
    Int.shru ($ z) ($ 3) <> x ->
    $ z <> (x<<ᵢ$ 3)+ᵢy .
Proof.
  introv Hx Hy Hz.
  mauto.
Qed.


Lemma int_ltu_neq_zero:
  forall x,
    Int.ltu ($ 0) x = true -> x <> $ 0.
Proof.
  intros.
  assert (x= $ 0 \/ x <> $0) by tauto.
  destruct H0; auto.
  subst x.
  unfolds in H.
  rewrite zlt_false in H.
  inverts H.
  clear H.
  int auto.
Qed.


Lemma int_not_shrl_and :
  forall x y,
    Int.unsigned x < 8 ->
    Int.unsigned y < 8 ->
    x <> y ->
    (Int.not ($ 1 <<ᵢ x)) &ᵢ  ($1 <<ᵢ y) = $ 1 <<ᵢ y.
Proof.
  introv Hx Hy.
  mauto.
Qed.

Lemma  math_prio_eq:
  forall prio  ,
    Int.unsigned prio < 64 ->
    prio = Int.add (Int.shru prio ($ 3) <<ᵢ $ 3) (prio &ᵢ $ 7).
Proof.
  introv Hx.
   mauto.
Qed.



 
 Lemma  math_length_int_eq:
   forall x3 (x1 : list msg ) N x2,
     Int.unsigned x3 = Z.of_nat (length x1) ->
     ((length x1 + 1)%nat = S N) %nat ->
     S N = ∘(Int.unsigned x2) ->
     Int.eq (x3+ᵢ$ 1) x2 = true.
 Proof.
   intros.
   unfold nat_of_Z in *.
   unfold Int.add.
   ur_rewriter.
   rewrite H.
   rewrite Z.add_1_r.
   rewrite <- Nat2Z.inj_succ.
   assert (length x1 = N) by omega.
   rewrite H2.
   rewrite H1.
   rewrite Z2Nat.id.
   rewrite Int.repr_unsigned.
   rewrite Int.eq_true.
   auto.
   int auto.
Qed.



 Lemma math_int_eq_len:
  forall x3 (x1:list msg)  x2,
    (0 < Int.unsigned x2) ->
    Int.unsigned x3 = Z.of_nat (length x1) ->
    length x1 = (∘(Int.unsigned x2) - 1)%nat ->
    Int.eq (x3+ᵢ$ 1) x2 = true.
Proof.
  intros.
  unfold nat_of_Z in *.
  unfold Int.add.
  ur_rewriter.
  rewrite H1 in H0.
  rewrite H0.
  rewrite <- pred_of_minus.
  rewrite <- Z2Nat.inj_pred.
  rewrite Z2Nat.id.
  rewrite Z.add_1_r.
  rewrite <-Zsucc_pred.
  rewrite Int.repr_unsigned.
  apply Int.eq_true.
  omega.
Qed.  


(* move to join_lib*)
Lemma join_indom_r : 
  forall ma mb mab x, TcbMod.join ma mb mab -> TcbMod.indom mb x ->TcbMod.indom mab x.
  intros.
  unfold TcbMod.indom in *.
  inversion H0.
  exists x0.
  eapply TcbMod.join_get_get_r.
  exact H.
  auto.
Qed.
  
  Lemma join_indom_or :
 forall ma mb mab x, TcbMod.join ma mb mab -> TcbMod.indom mab x -> TcbMod.indom ma x \/ TcbMod.indom mb x.
    intros.
    unfold TcbMod.indom in *.
    inversion H0.
    eapply (TcbMod.join_get_or) in H1.
    elim H1; intros.
    Focus 3.
    exact H.
    left.
    eauto.
    right.
    eauto.
  Qed.



Lemma tcbmod_get_or : forall ma a, TcbMod.get ma a = None \/ exists b, TcbMod.get ma a = Some b.
  intros.
  destruct (TcbMod.get ma a).
  right; eauto.
  left; auto.
Qed.

Lemma indom_eq_join_eq:
 forall ma mb ma' mb' mab,
 (forall a, TcbMod.indom ma a <-> TcbMod.indom ma' a) -> 
TcbMod.join ma mb mab ->
TcbMod.join ma' mb' mab -> ma = ma'.
Proof.
  intros.
  apply TcbMod.extensionality.
  intros.

  lets cond1 : @tcbmod_get_or ma a.
  destruct cond1; intros.
  unfold TcbMod.indom in H.
  set (H a).
  elim i; intros.
  rewrite H2 in *.
  
  lets cond2 : @tcbmod_get_or ma' a.
  destruct cond2; intros.
  rewrite H5.
  auto.
  set (H4 H5).
  inversion e.
  inversion H6.

  unfold TcbMod.indom in H.
  set (H a).
  copy H2.
  rewrite i in H3.
  clear H i.
  simp join.
  eapply TcbMod.join_get_get_l in H0.
  Focus 2.
  exact H2.
  eapply TcbMod.join_get_get_l in H1.
  Focus 2.
  exact H.
  rewrite H2, H.
  rewrite H0 in H1.
  auto.
Qed.



Lemma list_gt_0_ex:
  forall v2 : list val, 
    (0 < length v2)%nat ->
    exists x y, v2 = x :: y. 
Proof.
  inductions v2; intros; simpl in *; try omega.
  eauto.
Qed.






Lemma update_nth_val_len_eq: forall vl v x, length (update_nth_val x vl v) = length vl.
Proof.
  induction vl;  intros.
  simpl;auto.
  simpl.
  destruct x.
  simpl;auto.
  simpl.
  assert(length (update_nth_val x vl v)=length vl).
  auto.
  omega.
Qed.

Lemma update_nth:
 forall vl n v vi, nth_val n vl = Some vi -> nth_val n (update_nth_val n vl v) = Some v.
Proof.
  intros.
  generalize dependent n.
  generalize dependent v.
  generalize dependent vi.
  induction vl.
  intros.
  destruct n;tryfalse.
  intros.
  destruct n;tryfalse.
  simpl in H.
  inverts H.
  simpl.
  auto.
  simpl in H.
  simpl.
  eapply IHvl;eauto.
Qed.

Require Import join_lib.

Lemma ecbmod_get_sig_set_auto:
  forall (A B T : Type) (MC : PermMap A B T) v x y,
    usePerm = false ->
    get v x = None ->
    join (sig x y) v (set v x y).
  hy.
Qed.  

Lemma ecbmod_get_sig_set:
  forall v x y,
    EcbMod.get v x = None -> 
    EcbMod.joinsig x y v (EcbMod.set v x y).
Proof.
  intros.
  assert (get v x = None).
  {
    unfold get.
    simpl.
    auto.
  }
  assert (join (sig x y) v (set v x y)).
  {
    eapply ecbmod_get_sig_set_auto; auto.
  }
  auto.
Qed.

Lemma ecbmod_joinsig_get :
  forall x y mqls mqls',
    EcbMod.joinsig x y mqls mqls' ->
    EcbMod.get  mqls' x = Some y.
Proof.
  intros.
  unfold EcbMod.joinsig in H.
  eapply EcbMod.join_get_get_l.
  exact H.
  apply EcbMod.get_sig_some.
Qed.

Lemma ecbmod_joinsig_sig:
  forall x y mqls mqls',
    EcbMod.joinsig x y mqls mqls' ->
    EcbMod.join mqls (EcbMod.sig x y) mqls'.
Proof.
  intros.
  apply EcbMod.join_comm.
  exact H.
Qed.


Lemma  ecbmod_get_join_get:
  forall eid y m x z t,
    eid <> y ->
    EcbMod.get m eid = Some t ->
    EcbMod.join x (EcbMod.sig y z) m ->
    EcbMod.get x eid = Some t.
Proof.
  intros.

  set (EcbMod.join_get_or H1 H0).
  elim o; intros.
  auto.
  rewrite EcbMod.get_a_sig_a' in H2.
  inversion H2.
  EcbMod.beq_simpl_tac.
Qed.



Close Scope int_scope.
Close Scope Z_scope.
Close Scope code_scope.

