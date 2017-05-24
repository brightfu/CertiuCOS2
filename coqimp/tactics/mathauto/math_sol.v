Set Implicit Arguments.
Unset Strict Implicit.

Require Import Integers.
Require Import Coq.Setoids.Setoid.
Require Import ZArith.
Require Import Arith.
Require Import LibTactics.
Require Import int_auto.
(*Require Import bits_map.*)

Module _mathsolver.

Fixpoint _iter {T:Type} (f:T->T) (base : T) (n: nat) : T :=
  match n with 
      | O => base
      | S n' => _iter f (f base) n'
 end.
Module Type has_le.
  Parameter A: Type.
  Parameter le : A->A->Prop.

  Axiom le_refl : forall x:A, le x x.
  Axiom le_antisymm : forall a b:A, le a b -> le b a -> a=b.
  Axiom le_trans : forall a b c:A, le a b -> le b c -> le a c. 
End has_le.

Module Type has_next (LE: has_le).
  Import LE.
  Parameter next : A->A.
  Axiom next_is_smallest : forall (x n:A), le x n <-> n =  x \/ le (next x) n.
End has_next.

Module Type has_dist (Import LE: has_le) (Import HN:has_next LE).
  Parameter dist : A->A->nat.
  Axiom dist_a : forall a b,le a b-> _iter next a (dist a b) = b.
End has_dist.

Module Range (Import LE: has_le) (Import HN : has_next LE) (Import HD: has_dist LE HN).
  Definition range (b:A)(l:nat)(x:A) := le b x /\ le x (_iter next b l).

  Lemma x_le_next: forall x :A , le x (next x).
    intros.
    rewrite next_is_smallest.
    right.
    apply le_refl.
  Qed.

  Lemma x_le_iter_next : forall (x :A) (n:nat), le x (_iter next x n).
    intros.
    generalize x; clear x.
    induction n.
    simpl.
    apply le_refl.
    simpl.
    intros.
    eapply (@le_trans _  (next x)).
    apply x_le_next.
    apply IHn.
  Qed.

  Lemma range_l_r: forall (l r x:A) , le l r -> (le l x /\ le x r <-> range l (dist l r) x).
    intros.
    split;
    intro;
    unfold range in *;
    rewrite dist_a in *;auto.
  Qed.

  Lemma range_split_first' : forall (b:A) (l:nat) (x:A), x=b \/ range (next b) l x -> range b (S l) x.
    intros b l.
    generalize b; clear b.
    induction l.
    intros.
    elim H; intros.
    unfold range.
    simpl.
    rewrite H0.
    split.
    apply le_refl.
    
    apply x_le_next.

    unfold range.
    unfold range in H0.
    unfold _iter in H0.
    unfold _iter.
    elim H0; intros.
    set (@le_antisymm x (next b) H2 H1 ).
    rewrite e.
    split.
    apply x_le_next.
    apply le_refl.

    intros.

    elim H; intros.
    rewrite H0; split; intros.
    apply le_refl.
    simpl.

    eapply (@le_trans _  (next (next b))).
    eapply (@le_trans _ (next b)).
    apply (x_le_next).
    apply x_le_next.
    apply x_le_iter_next.

    unfold range in *.
    elim H0; intros.
    split.
    eapply le_trans.
    Focus 2.
    exact H1.
    apply x_le_next.
    simpl.
    simpl in H2.
    exact H2.
  Qed.

  Lemma range_split_first'' : forall (b:A) (l:nat) (x:A), range b (S l) x -> x=b \/ range (next b) l x.
    intros.
    set (next_is_smallest b x).
    elim i; intros o o'.
    unfold range in H.
    inversion H.
    set (o H0).
    elim o0; intros.
    left; auto.
    right; unfold range.
    split; auto.
  Qed.

  Lemma range_split_first : forall (b:A) (l:nat) (x:A), range b (S l) x <-> x=b \/ range (next b) l x.
    split.
    apply range_split_first''.
    apply range_split_first'.
  Qed.

  Lemma range_eq : forall (l x:A), range l O x <-> x=l.
    split;intros.
    unfold range in H.
    elim H; intros.
    apply le_antisymm; auto.
    unfold range; rewrite H; split;apply le_refl.
  Qed.

  (* good *)
  Fixpoint gen_prop (b:A) (len:nat) (x:A) {struct len} := 
    match len with
      | O => x=b
      | S n => x = b \/ gen_prop (next b) n x
    end.

  (* bad *)
  Fixpoint gen_prop' (b:A) (len:nat) (x:A) {struct len} :=
    match len with 
      | O => x=b
      | S n => gen_prop' b n x \/ x= _iter next b len
    end.

  Lemma range_fin_elem: forall b l x, range b l x <-> gen_prop b l x.
    intros b l.
    generalize b; clear b.
    induction l.
    intros; split; simpl;
    apply range_eq.

    intros; split; simpl; intros.
    apply range_split_first in H.
    elim H; intros.
    left; auto.
    right.
    apply IHl.
    auto.
    
    apply range_split_first.
    elim H; intros.
    left; auto.
    right; apply IHl.
    auto.
  Qed.
  Lemma range_l_r_fin_elem: forall (l r x:A) , le l r -> (le l x /\ le x r <-> gen_prop l (dist l r) x).
    intros.
    split.
    intro.
    rewrite range_l_r in H0.
    rewrite range_fin_elem in H0.
    auto.
    auto.
    intro.
    rewrite range_l_r; auto.
    rewrite range_fin_elem; auto.
  Qed.

  Lemma range_split_last'' : forall (b:A) (l:nat) (x:A), range b (S l) x -> range b l x \/ x= _iter next b (S l).
    intros b l.
    generalize b; clear b.
    induction l.
    intros.
    simpl.
    rewrite range_fin_elem in *.
    simpl in *.  
    auto.
    intros.

    apply range_split_first in H.
    elim H; intros.
    left; rewrite H0.
    unfold range.
    split; auto.
    apply le_refl.
    apply x_le_iter_next.
    apply IHl in H0.
    elim H0; intros.
    left.


    unfold range.
    unfold range in H1.
    elim H1; intros.
    split.
    eapply le_trans.
    Focus 2.
    exact H2.
    apply x_le_next.
    simpl.
    exact H3.

    right.
    auto.
  Qed.

  Lemma range_split_last' : forall (b:A) (l:nat) (x:A), range b l x \/ x = _iter next b (S l) -> range b (S l) x.
    intros b l.
    generalize b; clear b.
    induction l.
    intros.
    rewrite range_fin_elem in *.
    simpl in *.
    auto.

    intros.
    elim H; intros.
    unfold range in H0.
    unfold range.
    elim H0; intros; split; auto.
    eapply le_trans.
    exact H2.
    Lemma iter_n_lt_lt: forall n b, le (_iter next b n) (_iter next b (S n)).
      intro.
      induction n.
      intros.
      simpl.
      apply x_le_next.

      intros.
      assert (forall k, _iter next b (S k) = _iter next (next b) k).
      auto.
      rewrite H.
      rewrite H.
      apply IHn.
    Qed.
    apply iter_n_lt_lt.
    unfold range.
    split.
    rewrite H0.
    apply x_le_iter_next.
    rewrite H0.
    apply le_refl.
  Qed.

  Lemma range_split_last : forall (b:A) (l:nat) (x:A), range b l x \/ x = _iter next b (S l) <-> range b (S l) x.
    intros.
    split.
    apply range_split_last'.
    apply range_split_last''.
  Qed.

  Lemma range_fin_elem2' : forall b len x, range b len x -> gen_prop' b len x.
    intros b l.
    generalize b; clear b.
    induction l.
    intros.
    simpl in *.
    apply range_eq.
    auto.

    intros.
    simpl.
    rewrite <- range_split_last in H.
    elim H; intros.
    left.
    apply IHl.
    auto.
    right.
    simpl in H0; auto.
  Qed.

  Lemma range_fin_elem2'': forall b len x, gen_prop' b len x -> range b len x.
    intros b l.
    generalize b; clear b.
    induction l;intros.
    simpl in H; apply range_eq.
    auto.

    rewrite<- range_split_last. 
    simpl in H.
    elim H; intros.
    left; apply IHl; auto.
    right; simpl; auto.
  Qed.

  Lemma range_fin_elem2 : forall b len x, gen_prop' b len x <-> range b len x.
    intros.
    split.
    apply range_fin_elem2''.
    apply range_fin_elem2'.
  Qed.
End Range.

(* Z has le next and dist *)
Module Z_has_le <: has_le.
  Definition A := Z.
  Definition le := Zle.

  Definition le_refl:=Z.le_refl.
  Definition le_antisymm :=Z.le_antisymm.
  Definition le_trans := Z.le_trans.
End Z_has_le.

Module Z_has_next <: has_next Z_has_le.
  Definition next := fun x:Z => (1+ x)%Z.
  Lemma next_is_smallest: forall (x a:Z), Zle x a <-> a = x \/ Zle (next x) a.
    intros.
    split; intros.
    apply Z.le_lteq in H.
    elim H; intros.
    right.
    unfold next.
    omega.
    left ; auto.
    
    rewrite Z.le_lteq.
    elim H; intros.
    right; auto.
    left; unfold next in H0; omega.
  Qed.
End Z_has_next.

Module Z_has_dist <: has_dist Z_has_le Z_has_next.
  Import Z_has_le.
  Import Z_has_next.
  Definition dist := fun a b:Z => Z.to_nat (b-a).
    Lemma dist_a': forall n a, _iter next a n = (a+ Z.of_nat n)%Z.
       intro.
       induction n.
       intros.
       simpl.
       omega.
       
       intros.
       rewrite Nat2Z.inj_succ.
       simpl.
       rewrite IHn.
       unfold next.
       omega.
    Qed.

  Lemma dist_a : forall a b, le a b -> _iter next a (dist a b)  =b.
    intros a b.
    intro.
    assert (b = a + Z.of_nat (dist a b))%Z.
    unfold dist.
    rewrite Z2Nat.id.
    omega.
    unfold le in H; omega.
    rewrite H0 at 2.
    apply dist_a'.
  Qed.
End Z_has_dist.

(* nat has le next and dist *)

Module nat_has_le <: has_le.
  Definition A := nat.
  Definition le := le.

  Definition le_refl:=le_refl.
  Definition le_antisymm :=le_antisym.
  Definition le_trans := le_trans.
End nat_has_le.

Module nat_has_next <: has_next nat_has_le.
  Definition next := fun x => (S x).
  Lemma next_is_smallest: forall (x a:nat), le x a <-> a = x \/ le (next x) a.
    intros.
    split; intros.
    apply le_lt_or_eq_iff in H.
    elim H; intros.
    right.
    unfold next.
    omega.
    left ; auto.
    rewrite le_lt_or_eq_iff.
    elim H; intros.
    right; auto.
    left; unfold next in H0; omega.
  Qed.
End nat_has_next.

Module nat_has_dist <: has_dist nat_has_le nat_has_next.
  Import nat_has_le.
  Import nat_has_next.
  Definition dist := fun a b: nat => (b-a)%nat.
    Lemma dist_a': forall n a, _iter next a n = (a+n)%nat.
       intro.
       induction n.
       intros.
       simpl.
       omega.
       
       intros.
       simpl.
       rewrite IHn.
       unfold next.
       omega.
    Qed.

  Lemma dist_a : forall a b, le a b -> _iter next a (dist a b)  =b.
    intros a b.
    intro.
    assert (b = a + (dist a b))%nat.
    unfold dist.
    unfold le in H.
    omega.
    rewrite H0 at 2.
    apply dist_a'.
  Qed.
End nat_has_dist.

Module Z_range := Range Z_has_le Z_has_next Z_has_dist.

Module nat_range := Range nat_has_le nat_has_next nat_has_dist.

Ltac nat_range_unfold_all H:=try unfold nat_range.gen_prop in H;try unfold nat_has_next.next in H;try unfold nat_has_dist.dist in H;try unfold nat_has_le.A in H.

Ltac Z_range_unfold_all H:=try unfold Z_range.gen_prop in H;try unfold Z_has_next.next in H;try unfold Z_has_dist.dist in H;try unfold Z_has_le.A in H.

Ltac stdrange_fin_elem :=
  repeat progress
  match goal with 
      | H : ( _ <= ?a (?b _) <= _)%nat |- _ => apply nat_range.range_l_r_fin_elem in H;[cbv beta delta -[a b] iota in H| unfold nat_has_le.le; omega]
      | H : ( _ <= ?a _ _ <= _)%nat |- _ => apply nat_range.range_l_r_fin_elem in H;[cbv beta delta -[a] iota in H| unfold nat_has_le.le; omega]
      | H : ( _ <= ?a _ <= _)%nat |- _ => apply nat_range.range_l_r_fin_elem in H;[cbv beta delta -[a] iota in H| unfold nat_has_le.le; omega]
      | H : ( _ <= _ <= _)%nat |- _ => apply nat_range.range_l_r_fin_elem in H;[cbv beta delta iota in H| unfold nat_has_le.le; omega]
      | H : ( _ <= ?a (?b _) <= _)%Z |- _ => apply Z_range.range_l_r_fin_elem in H;[cbv beta delta -[a b] iota in H| unfold Z_has_le.le; omega]
      | H : ( _ <= ?a _ _ <= _)%Z |- _ => apply Z_range.range_l_r_fin_elem in H;[cbv beta delta -[a] iota in H| unfold Z_has_le.le; omega]
      | H : ( _ <= ?a _ <= _)%Z |- _ => apply Z_range.range_l_r_fin_elem in H;[cbv beta delta -[a] iota in H| unfold Z_has_le.le; omega]
      | H : ( _ <= _ <= _ )%Z   |- _ => apply Z_range.range_l_r_fin_elem  in H;[cbv beta delta iota in H| unfold Z_has_le.le; omega]
      | _ => fail
  end.

(* range split part end *)

Open Scope nat_scope.
  Lemma nat_lt2stdrange : forall x b:nat, x<b -> 0<=x<=(pred b).
    intros;set (le_0_n x); split; auto.
    omega.
  Qed.

  Lemma nat_le2stdrange : forall x b:nat,  x<=b -> 0<=x<=b.
    intros; set (le_0_n x);split; auto.
  Qed.

  Lemma nat_gt2stdrange : forall x b:nat, b>x -> 0<=x<=(pred b).
    intros; set (le_0_n x); split; auto.
    omega.
  Qed.
  Lemma nat_ge2stdrange: forall x b, b>=x -> 0<=x<=b.
    intros; set (le_0_n x); split; auto.
  Qed.
Close Scope nat_scope.

(*******************************)

Open Scope Z_scope.
  Lemma unsigned_lt2stdrange : forall x b, Int.unsigned x< b -> 0<=Int.unsigned x <= (Z.pred b).
    intros;split;[set (Int.unsigned_range x); tauto| omega].
  Qed.
  
  Lemma unsigned_le2stdrange : forall x b, Int.unsigned x<=b -> 0<=Int.unsigned x<=b.
    intros;split;[set (Int.unsigned_range x); tauto| omega].
  Qed.

  Lemma unsigned_gt2stdrange : forall x b,  b > Int.unsigned x -> 0<=Int.unsigned x <= (Z.pred b).
    intros;split;[set (Int.unsigned_range x); tauto| omega].
  Qed.
  
  Lemma unsigned_ge2stdrange : forall x b, b >= Int.unsigned x -> 0<=Int.unsigned x<=b.
    intros;split;[set (Int.unsigned_range x); tauto| omega].
  Qed.

  Lemma repr_unsigned : forall x n, Int.unsigned x = n -> x= Int.repr n.
    intros.
    rewrite <- H.
    rewrite Int.repr_unsigned.
    reflexivity.
  Qed.

  (* TODO: change this function *)
  Ltac pre' :=
    match goal with 
       | H : (?x <  ?b)%nat |- _                => apply nat_lt2stdrange in H
       | H : (?x <= ?b)%nat |- _                => apply nat_le2stdrange in H
       | H : (?b >  ?x)%nat |- _                => apply nat_gt2stdrange in H
       | H : (?b >= ?x)%nat |- _                => apply nat_ge2stdrange in H
       | H : (Int.unsigned ?x <  ?b)     |- _   => apply unsigned_lt2stdrange in H
       | H : (Int.unsigned ?x <= ?b)     |- _   => apply unsigned_le2stdrange in H
       | H : (?b >  Int.unsigned ?x )    |- _   => apply unsigned_gt2stdrange in H
       | H : (?b >= Int.unsigned ?x)     |- _   => apply unsigned_ge2stdrange in H
       | H : (?a < ?x < ?b)%nat |- _            => let H' := fresh in rename H into H'; assert ( (S a) <= x <= (pred b))%nat as H by omega; clear H'
       | H : (?a <= ?x < ?b)%nat |- _           => let H' := fresh in rename H into H'; assert ( (a) <= x <= (pred b))%nat as H by omega; clear H'
       | H : (?a < ?x <= ?b)%nat |- _           => let H' := fresh in rename H into H'; assert ( (S a) <= x <= ( b))%nat as H by omega; clear H'
       | H : (?a < ?x < ?b) |- _                => let H' := fresh in rename H into H'; assert ( (1+ a) <= x <= (Z.pred b)) as H by omega; clear H'
       | H : (?a <= ?x < ?b) |- _               => let H' := fresh in rename H into H'; assert ( (a) <= x <= (Z.pred b)) as H by omega; clear H'
       | H : (?a < ?x <= ?b) |- _               => let H' := fresh in rename H into H'; assert ( (1+ a) <= x <= ( b)) as H by omega; clear H'
    end.
  
  Ltac pre := repeat pre';repeat ((* handle even not a real range, 1<=x<=0 for example*)try omega; timeout 8 stdrange_fin_elem).
  Ltac pre_noto := repeat pre';repeat ((* handle even not a real range, 1<=x<=0 for example*)try omega; stdrange_fin_elem).


  (* do NOT use this *)
  (* use a tactic as a param in another tactic is VERY slow*)
  Ltac brute_force tac:=
    match goal with 
        | H : _ \/ _ |- _ => destruct H; brute_force tac
        | _               => tac
    end.

  Lemma sample'' : forall n , (0< n<63)%nat ->True.
    intros.
    pre.
    auto.
  Qed.

  Lemma sample0: forall n m :int32,  Int.unsigned m < 64 -> 64 > Int.unsigned n ->  True.
    intros.
    pre.
    auto.
  Qed.

  Lemma sample1: forall n:nat, (n<25)%nat-> True.
    intros.
    pre.
    auto.
  Qed.

  Lemma sample2: forall n:nat, (25>n)%nat-> True.
    intros.
    pre.
    auto.
  Qed.

  Ltac math_solver_pre :=
    match goal with 
        | H : Int.unsigned _ = _ |- _ => apply repr_unsigned in H
        | _  => idtac
    end.

  (* can use compute -[Int.unsigned Int.mone] instead *)
  Ltac munfold :=try unfold Int.shru; try unfold Int.shl; try unfold Int.not; try unfold Z.shiftr; try unfold Int.xor; try unfold Int.and; try unfold Z.to_nat; try unfold Pos.to_nat; try unfold Int.or; try unfold Z.lor; try unfold Int.divu; try unfold Int.add; try unfold Int.mul; try unfold Int.sub; try unfold Int.ltu; try unfold Int.zero; try unfold Int.one; try unfold Int.eq.

  Ltac mycompute := compute -[Int.unsigned].


(*
Lemma div_in_intrange: forall x a mx:Z, (0<=x <=mx -> a>0 -> 0<= Z.div x a <=mx)%Z.
  intros.
  split.
  ht.revs.
  apply Z_div_ge0.
  omega.
  omega.
  apply Z.div_le_upper_bound.
  omega.
  elim H; intros.
  eapply Zle_trans.
  exact H2.
  ht.revs.
  apply a_mult_b_ge_b; omega.
Qed.
  Ltac solve_int_range := 
match goal with 
    | i : int32 |- _ => let xval := fresh in let xrange := fresh in destruct i as [xval xrange]; unfold Int.modulus, two_power_nat, shift_nat in xrange; simpl in xrange; simpl in *;  solve_int_range
    | _ => subst; try rewrite max_unsigned_val; solve [ omega | apply div_in_intrange; omega ]
end.
  Ltac rangesolver :=try solve_int_range; repeat (rewrite Int.unsigned_repr; try solve_int_range).
  Ltac ur_rewriter := rewrite Int.unsigned_repr; [idtac| rangesolver].
  Ltac ur_rewriter_in H := rewrite Int.unsigned_repr in H; [idtac| rangesolver].
 *)
  Ltac trivial_ur_rewriter := rewrite Int.unsigned_repr;[idtac| rewrite max_unsigned_val; omega].

  Ltac subst_all := subst.



(* not so basic *)
  Ltac basic_solver := match goal with 
| H : Int.unsigned ?a = ?b |- _  => rewrite H in *; apply repr_unsigned in H; basic_solver
| _  => subst_all; simpl; repeat trivial_ur_rewriter; simpl; solve [auto| omega |  timeout 2 mycompute; intros; try split; tryfalse; try omega; auto]
end.
  Ltac basic_solver_noto := match goal with 
| H : Int.unsigned ?a = ?b |- _  => rewrite H in *; apply repr_unsigned in H; basic_solver
| _  => subst_all; simpl; repeat trivial_ur_rewriter; simpl; solve [auto| omega |  mycompute; intros; try split; tryfalse; try omega; auto]
end.
  

  Ltac bf_basic_solver :=
    repeat progress
           match goal with
             | H : _ \/ _ |- _  => destruct H;
                                  [match goal with
                                     |  H' : _\/_ |- _ => destruct H';
                                                         [match goal with
                                                            |  H'' : _\/_ |- _ => destruct H''; [basic_solver | idtac]
                                                            |  _ => basic_solver
                                                          end | idtac ]
                                     |  _ => basic_solver
                                   end | idtac ]
             | _ => basic_solver
           end.

  Ltac bf_basic_solver_noto :=
    repeat progress
           match goal with
             | H : _ \/ _ |- _  => destruct H;
                                  [match goal with
                                     |  H' : _\/_ |- _ => destruct H';
                                                         [match goal with
                                                            |  H'' : _\/_ |- _ => destruct H''; [basic_solver_noto | idtac]
                                                            |  _ => basic_solver_noto
                                                          end | idtac ]
                                     |  _ => basic_solver_noto
                                   end | idtac ]
             | _ => basic_solver_noto
           end.


  Ltac basic_solver_safe := match goal with 
| H : Int.unsigned ?a = ?b |- _  => rewrite H; apply repr_unsigned in H; basic_solver_safe
| _  => subst_all; simpl;  split; try omega
end.

Ltac bf1_basic_solver :=
   match goal with
     | H : _ \/ _ |- _  => solve[clear -H; repeat (destruct H as [H | H] ;[basic_solver_safe| idtac] ) ; basic_solver_safe]
   end.

Ltac clear_useless_or :=
  match goal with
      | H : _ ?a = _ \/ _ |- _ => clear dependent a
      | H : ?a = _ \/ _   |- _ => clear dependent a
end.

Ltac clear_all_useless_or := repeat clear_useless_or.

Ltac mrewrite := repeat rewrite unsigned_mone_val; repeat rewrite Int.unsigned_repr; try rewrite max_unsigned_val; [idtac|solve [clear; omega |  clear_all_useless_or;  bf_basic_solver] .. ].
Ltac mrewrite_noto := repeat rewrite unsigned_mone_val; repeat rewrite Int.unsigned_repr; try rewrite max_unsigned_val; [idtac|solve [clear; omega |  clear_all_useless_or;  bf_basic_solver_noto] .. ].

  Ltac new_mathsolver:= munfold; pre; mrewrite; bf_basic_solver.
  Ltac new_mathsolver_noto := munfold; pre_noto; mrewrite_noto; bf_basic_solver_noto.
  (* old version *)
  Ltac math_rewrite :=
    repeat progress (
             try rewrite Int.unsigned_repr in *;
             try rewrite max_unsigned_val in *;
             try omega ;
             try rewrite unsigned_mone_val in *;
             try omega; auto).


  Ltac math_solver:=
    math_solver_pre;
    subst;
    try simpl in *;
    try unfold Int.shru in *;
    try unfold Int.shl in *;
    try unfold Int.not in *;
    try unfold Z.shiftr in *;
    try unfold Int.xor in *;
    try unfold Int.and in *;
    try unfold Z.to_nat in *;
    try unfold Pos.to_nat in *;
    try unfold Int.or in *;
    try unfold Z.lor in *;
    try unfold Int.divu in *;
    try unfold Int.add in *;
    try unfold Int.mul in *;
    try unfold Int.sub in *;
    try unfold Int.ltu in *;
    try unfold Int.zero in *;
    try unfold Int.one in *;
    try unfold Int.eq in *;
    match goal with
      | H : ?f  _  =  _ |- _ => simpl f in H;  inverts H
      | _ => idtac
    end;
    math_rewrite;
    try simpl in *;
    math_rewrite;
    intuition tryfalse;
    try (simpl; omega).

  Ltac mathsolver' :=
    repeat progress
           match goal with
             | H : False |- _ => inversion H
             | H : _ \/ _ |- _  => destruct H;
                                  [match goal with
                                     |  H' : _\/_ |- _ => destruct H';
                                                         [match goal with
                                                            |  H'' : _\/_ |- _ => destruct H''; [math_solver | idtac]
                                                            |  _ => math_solver
                                                          end | idtac ]
                                     |  _ => math_solver
                                   end | idtac ]
             | _ => math_solver
           end.
  
  Ltac mathsolver:= pre; mathsolver'.

End _mathsolver.
(*
Require Import memory. (* for Vint32 *)
Require Import OSTCBInvDef. (* for OSUnMapVallist *)
Require Import BaseAsrtDef. (* for nth_val' *)

Module _mathsolver_ext.
  Close Scope nat_scope.
  Open Scope Z_scope.
  Definition deref_Vint32_unsafe (x:val): int32 :=
    match x with
        | Vint32 x => x
        | _ => (Int.repr 0)
    end.

  Lemma OSUnMapVallist_safe_deVint32 : forall z y, 0<=z<=255 -> nth_val' (Z.to_nat z) OSUnMapVallist = Vint32 y -> y = deref_Vint32_unsafe ( nth_val' (Z.to_nat z) OSUnMapVallist).
Proof.
  intros.
  _mathsolver.pre.
  repeat (destruct H; [rewrite H in *; simpl in H0; inversion H0; auto| idtac]).
  rewrite H in *; simpl in H0; inversion H0; auto.
Qed.
 
  Lemma OSMapVallist_safe_deVint32 : forall z y, 0<=z<=7 -> nth_val' (Z.to_nat z) OSMapVallist = Vint32 y -> y = deref_Vint32_unsafe ( nth_val' (Z.to_nat z) OSMapVallist).
    intros.
    _mathsolver.pre.
    repeat (destruct H; [rewrite H in *; simpl in H0; inversion H0; auto| idtac]).
    rewrite H in *; simpl in H0; inversion H0; auto.
  Qed.
  
  Ltac deref_vint32_for_array := match goal with 
                                 | H : nth_val' (Z.to_nat (Int.unsigned ?a) ) OSUnMapVallist = Vint32 _ |- _=> apply OSUnMapVallist_safe_deVint32 in H;[unfold deref_Vint32_unsafe in H; try rewrite H in *; clear H |set (@Int.unsigned_range_2 a); try omega]
                                 | H : nth_val' (Z.to_nat (Int.unsigned ?a) ) OSMapVallist = Vint32 _ |- _ => apply OSMapVallist_safe_deVint32 in H; [unfold deref_Vint32_unsafe in H; try rewrite H in *; clear H | set (@Int.unsigned_range_2 a);  try omega]
                                 | H : nth_val' (Z.to_nat _ ) OSUnMapVallist = Vint32 _ |- _=> apply OSUnMapVallist_safe_deVint32 in H;[unfold deref_Vint32_unsafe in H; try rewrite H in *; clear H | try omega]
                                 | H : nth_val' (Z.to_nat _ ) OSMapVallist = Vint32 _ |- _ => apply OSMapVallist_safe_deVint32 in H; [unfold deref_Vint32_unsafe in H; try rewrite H in *; clear H | try omega]
                                 end.
End _mathsolver_ext.
*)

Ltac mauto := (*repeat _mathsolver_ext.deref_vint32_for_array; *)_mathsolver.new_mathsolver.
Ltac mauto_noto := (*repeat _mathsolver_ext.deref_vint32_for_array;*) _mathsolver.new_mathsolver_noto.
Ltac mauto_old := _mathsolver.mathsolver.
Ltac mauto_dbg := _mathsolver.pre.
