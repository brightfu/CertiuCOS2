Require Import Coqlib.
Require Import Integers.
Require Import ZArith.
Require Import LibTactics.
Require Import Classical.

Definition ident := Z.
Definition block := positive.
Definition addrval :=  (block * int32)%type.
Definition tid := addrval.

Fixpoint blt_pos (p q : positive) {struct p} : bool :=
  match (Pcompare p q Eq) with
    | Lt => true 
    | _  => false
  end.

Fixpoint beq_pos (p p' : positive) {struct p} : bool :=
  match p, p' with
    | x~0, x'~0 => andb true (beq_pos x x')
    | p~1, p'~1 => andb true (beq_pos p p')
    | 1, 1 => true 
    | _, _ => false
  end %positive.

Definition beq_tid (n m : tid) :  bool := 
  match n, m with
   |  (b, i), (b', i') => andb (beq_pos b b') (Int.eq i i') 
 end.

Definition blt_tid (n m : tid) : bool :=
 match n, m with
   |  (b, i), (b', i') => if blt_pos b b'
                          then true
                          else if beq_pos b b' 
                               then Int.lt i i'
                               else false
 end.

Lemma beq_pos_Pos_eqb_eq :
  forall b1 b2,
    beq_pos b1 b2 = Pos.eqb b1 b2.
Proof.
  induction b1; induction b2; intros; simpl in *; auto.
Qed.

Lemma blt_pos_Pos_ltb_eq :
  forall b1 b2,
    blt_pos b1 b2 = Pos.ltb b1 b2.
Proof.
  induction b1; induction b2; intros; simpl in *; auto.
Qed.


Module tidspec.

  Definition A := tid.

  Definition B := tid.
  
  Definition beq : A -> A -> bool := beq_tid.
  
  Definition blt : A -> A -> bool := blt_tid.
  
  Lemma beq_true_eq : forall a a' : A,
    beq a a' = true -> a = a'.
  Proof.
    introv Heq.
    unfolds in Heq.
    unfolds in Heq.
    destruct a ; destruct a'.
    apply andb_true_iff in Heq.
    destruct Heq.

    rewrite beq_pos_Pos_eqb_eq in H.      
    apply Pos.eqb_eq in H.
    assert (if Int.eq i i0 then i = i0 else i <> i0) as Hasrt.
    eapply Int.eq_spec with (x:=i) (y:= i0).
    rewrite H0 in Hasrt.
    subst.
    auto.
  Qed.


  Lemma beq_false_neq : forall a a' : A,
    beq a a' = false -> a <> a'.
  Proof.
   introv Heq.
   unfolds in Heq.
   unfolds in Heq.
   destruct a; destruct a'.
   apply andb_false_iff in Heq.
   destruct Heq.
     rewrite beq_pos_Pos_eqb_eq in H.
   apply Pos.eqb_neq in H.
   introv Heq.
   inverts Heq.
   tryfalse.
     assert (if Int.eq i i0 then i = i0 else i <> i0) as Hasrt.
    eapply Int.eq_spec with (x:=i) (y:= i0).
   rewrite H in Hasrt.
   introv Heq.
   inverts Heq; tryfalse.
Qed.


  Lemma eq_beq_true : forall a a' : A,
    a = a' -> beq a a' = true.
  Proof.
    introv Heq.
    unfolds.
    unfolds.
    destruct a; destruct a'.
    apply andb_true_iff .
    splits.
    inverts Heq.
    rewrite beq_pos_Pos_eqb_eq.
    apply Pos.eqb_refl.
    inverts Heq.
    apply Int.eq_true.
Qed.

  Lemma neq_beq_false : forall a a' : A,
    a <> a' -> beq a a' = false.
  Proof.
    introv Heq.
        unfolds.
    unfolds.
    destruct a; destruct a'.
    apply andb_false_iff .
    assert (~ (b = b0 /\ i = i0)). 
    introv  Hf.
    apply Heq.
    destruct Hf.
    subst.
    auto.

    apply Classical_Prop.not_and_or in H.
    destruct H.
    left.
    rewrite beq_pos_Pos_eqb_eq.
    apply Pos.eqb_neq ; auto.
    right.
    apply Int.eq_false; auto.   
  Qed.


  Lemma blt_trans : forall a a' a'' : A,
                      blt a a' = true -> blt a' a'' = true -> blt a a'' = true.
  Proof.
    introv Hb1 Hb2.
    unfolds in Hb1.
    unfolds in Hb2.
    unfolds in Hb1.
    unfolds in Hb2.
    unfolds; unfolds.
    destruct a; destruct a'; destruct a''.
    rewrite blt_pos_Pos_ltb_eq in *.
    rewrite beq_pos_Pos_eqb_eq in *.    
    remember (Pos.ltb b b0) as bool1;
      remember (Pos.ltb b0 b1) as bool2;
      remember (Pos.eqb b b0) as bool3;
      remember (Pos.eqb b0 b1) as bool4;
      remember (Int.lt i i0) as bool5;
      remember (Int.lt i0 i1) as bool6.
    destruct bool1; destruct bool2; tryfalse.
    symmetry in Heqbool1; apply Pos.ltb_lt in Heqbool1.
    symmetry in Heqbool2; apply Pos.ltb_lt in Heqbool2.
    assert (Pos.ltb b b1 = true) as H100.
    apply Pos.ltb_lt.
    eapply Pos.lt_trans; eauto.
    rewrite H100; auto.
    destruct bool4; tryfalse.
    symmetry in Heqbool4; apply Pos.eqb_eq in Heqbool4; subst.
    rewrite <- Heqbool1; auto.    
    destruct bool3; tryfalse.
    symmetry in Heqbool3; apply Pos.eqb_eq in Heqbool3; subst.
    rewrite <- Heqbool2; auto.
    destruct bool3; destruct bool4; tryfalse.
    symmetry in Heqbool3; apply Pos.eqb_eq in Heqbool3; subst.
    symmetry in Heqbool4; apply Pos.eqb_eq in Heqbool4; subst.
    rewrite Pos.ltb_irrefl.
    rewrite Pos.eqb_refl.
    unfold Int.lt in *.
    remember (zlt (Int.signed i0) (Int.signed i1)) as Hbb.
    remember (zlt (Int.signed i) (Int.signed i0)) as Hbb'.
    destruct Hbb; destruct Hbb';tryfalse.
    lets Hre : ReflOmegaCore.Z_as_Int.lt_trans l0 l.
    remember (zlt (Int.signed i) (Int.signed i1)) as Hres.
    destruct Hres; auto.
  Qed.

  Lemma blt_irrefl : forall a : A,
                       blt a a = false.
  Proof.
    intros; unfolds; unfolds; destruct a.
    assert (blt_pos b b = false).
    rewrite blt_pos_Pos_ltb_eq.
    apply Pos.ltb_irrefl.
    rewrite H.
    assert (beq_pos b b = true) as Htr.
    rewrite beq_pos_Pos_eqb_eq.
    apply Pos.eqb_eq; auto.
    rewrite Htr.
    unfolds.
    unfold zlt.
    destruct (Z_lt_dec (Int.signed i) (Int.signed i) ); auto.
    apply Z.lt_irrefl in l; tryfalse.
  Qed.


  Lemma blt_asym :  forall a b : A, 
    blt a b = true -> blt b a = false.
   Proof.
    intros.
    unfold blt in *.
    unfold blt_tid in *.
    destruct a; destruct b.
    rewrite blt_pos_Pos_ltb_eq in *.
    rewrite beq_pos_Pos_eqb_eq in *.
    remember (Pos.ltb b0 b) as bool1; destruct bool1.
    symmetry in Heqbool1; apply Pos.ltb_lt in Heqbool1.
    assert (Pos.ltb b b0 = false) as H100.
    apply Pos.ltb_ge.
    apply Pos.lt_le_incl; auto.
    rewrite H100; clear H100.
    remember (Pos.eqb b b0) as bool2; destruct bool2.
    symmetry in Heqbool2; apply Peqb_true_eq in Heqbool2; subst b.
    pose (Pos.ltb_irrefl b0) as H200; apply Pos.ltb_nlt in H200; tryfalse.
    auto.
        symmetry in Heqbool1; apply Pos.ltb_ge in Heqbool1.
    apply Pos.lt_eq_cases in Heqbool1; destruct Heqbool1 as [ H100 | H100 ].
    assert (Pos.eqb b0 b = false) as H200.
    apply Pos.eqb_neq.
    red; intros; subst b.
    pose (Pos.ltb_irrefl b0) as H300; apply Pos.ltb_nlt in H300; tryfalse.
    rewrite H200 in H; tryfalse.
    subst b.
    rewrite Pos.eqb_refl in *.
    rewrite Pos.ltb_irrefl.
    unfolds Int.lt.
    remember ( zlt (Int.signed i) (Int.signed i0)) as Hbb1.
    remember (zlt (Int.signed i0) (Int.signed i)) as Hbb2.
    destruct Hbb1; destruct Hbb2; tryfalse; auto.
    assert ( (Int.signed i <= Int.signed i0)%Z) .
    omega.
    apply ReflOmegaCore.Z_as_Int.le_lt_iff in H0; tryfalse.
  Qed.


   Lemma blt_beq_dec : forall a b : A,
                         {blt a b = true} + {beq a b = true} + {blt b a = true}.
   Proof.
     intros.
     unfold blt.
     unfold blt_tid.
     unfold beq.
     unfold beq_tid.
     destruct a; destruct b.
     repeat progress rewrite blt_pos_Pos_ltb_eq.
     repeat progress rewrite beq_pos_Pos_eqb_eq.
     remember (Pos.ltb b0 b) as bool1; destruct bool1.
     left; left; auto.
     remember (Pos.eqb b0 b) as bool2; destruct bool2.
     symmetry in Heqbool2; apply Pos.eqb_eq in Heqbool2; subst.
     rewrite <- Heqbool1.
     assert ((b =? b)%positive = true).
     inductions b; simpl; auto.
     rewrite H.
     simpl.
     unfold Int.lt.
     unfolds Int.eq.
     remember ( zlt (Int.signed i) (Int.signed i0)) as H1.
     remember ( zeq (Int.unsigned i) (Int.unsigned i0)) as H2.
     remember ( zlt (Int.signed i0) (Int.signed i)) as H3.
     destruct H1; destruct H2; destruct H3; auto.
     unfold Int.unsigned in *.
     simpl in *.
     unfold Int.signed in *.
     unfold Int.unsigned in *.
     destruct i ; destruct i0.
     simpl in *.
     remember (zlt intval Int.half_modulus) as Hz1.
     remember (zlt intval0 Int.half_modulus ) as Hz2.
     destruct Hz1; destruct Hz2; tryfalse.
     omega.   
     omega.
     omega.
     omega.
     right.
     assert ((b <? b0)%positive = true).  

     apply Pos.ltb_lt.
     apply eq_sym in Heqbool1.
     apply eq_sym in Heqbool2.
     apply Pos.eqb_neq in Heqbool2.
     apply Pos.ltb_nlt in Heqbool1.
     apply Pos.le_nlt in Heqbool1.
     apply Pos.lt_eq_cases in Heqbool1.
     destruct Heqbool1; tryfalse; auto.
     rewrite H.
     auto.
   Qed.  
End tidspec.


Module identspec.
  Definition A := ident.
  Definition beq := Zeq_bool.
  Definition blt := Zlt_bool.
  Lemma beq_true_eq : 
    forall a a' : A,
      beq a a' = true -> a = a'.
  Proof.
    apply Zeq_bool_eq.
  Qed.    
  Lemma beq_false_neq : 
    forall a a' : A,
      beq a a' = false -> a <> a'.
  Proof. 
    apply Zeq_bool_neq.
  Qed.  

  Lemma eq_beq_true :
    forall a a' : A,
      a = a' -> beq a a' = true.
  Proof.
    apply Zeq_is_eq_bool.
  Qed.

  Lemma neq_beq_false : 
    forall a a' : A,
      a <> a' -> beq a a' = false.
  Proof.
    intros.
    simpl in H.
    case_eq (beq a a').
    intros.
    apply Zeq_bool_eq in H0.
    destruct H.
    auto.
    auto.
  Qed.

  Lemma blt_trans : 
    forall a a' a'' : A,
      blt a a' = true -> blt a' a'' = true -> blt a a'' = true.
  Proof.
    unfold blt; intros.
    apply Z.ltb_lt in H.
    apply Z.ltb_lt in H0.
    apply Z.ltb_lt.
    omega.
  Qed.

  Lemma blt_irrefl :
    forall a : A,
      blt a a = false.
  Proof.  
    unfold blt; intros.
    apply Z.ltb_irrefl.
  Qed.

  Lemma blt_asym : 
    forall a b : A, 
      blt a b = true -> blt b a = false.
  Proof.  
    unfold blt; intros.
    apply Z.ltb_ge.
    apply Z.ltb_lt in H.
    omega.
  Qed.

  Lemma blt_beq_dec :
    forall a b : A,
      {blt a b = true} + {beq a b = true} + {blt b a = true}.
  Proof.
    unfold blt; unfold beq; intros.
    remember (Z.ltb a b) as bool1; destruct bool1.
    left; left; auto.
    remember (Zeq_bool a b) as bool2; destruct bool2.
    left; right; auto.

    symmetry in Heqbool1; apply Z.ltb_ge in Heqbool1.
    symmetry in Heqbool2; apply Zeq_bool_neq in Heqbool2.
    assert (b < a)%Z as H100 by omega.
    apply Z.ltb_lt in H100.
    right; auto.
  Qed.  

End identspec.




