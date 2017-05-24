Require Export Coqlib.
Require Export Integers.
Require Export ZArith.
Require Export List.
Require Export MapLib.
Require Export Modules.
Require Export Maps.
Require Export LibTactics.
Require Export map_tactics.
(* Import old. (** map_tactics is moduled to old **) *)
Require Import Coq.Logic.FunctionalExtensionality.
Set Implicit Arguments.
Unset Strict Implicit.
Open Local Scope Z_scope.

(**Definition of the physical memory model**)
Definition offset := Z.
Definition  addr : Set := prod block offset.
Definition addrlist : Set := list addr.

Definition get_off_addr (t : tid) off:=  (fst t, Int.add (snd t) off).

Lemma addr_eq_dec : forall a b : addr, {a = b} + {a <> b}.
Proof.
  introv.
  destruct a. destruct b.
  assert ({o = o0} + {o <> o0}).
  apply Z_eq_dec.
  assert({b=b0}+{b<>b0}).
  apply positive_eq_dec.
  inverts H; inverts H0; try auto; right;
  introv Hfalse;
  inverts Hfalse; false.
Qed.

Inductive memval : Set :=
| Undef : memval
| Byte : byte -> memval
| Pointer : block -> int32 -> nat -> memval
| MNull :memval.

Definition mvallist: Type := list memval.

Lemma memval_eq_dec : forall a b : memval, {a = b} + {a <> b}.
Proof.
  intros.
  destruct a, b; auto;
  try solve [right;
  intro Hf; false].
  assert ({i=i0} + {i <> i0}).
  apply Byte.eq_dec.
  destruct H.
  left.
  subst.
  auto.
  right.
  introv Hf.
  apply n.
  inverts Hf.
  auto.
  assert ({b0 = b} + {b0<>b}).
  apply Pos.eq_dec.
  assert ({i=i0}+{i<>i0}).
  apply Int.eq_dec.
  assert  ({n=n0}+{n<>n0}).
  apply eq_nat_dec.
  destruct H, H0, H1; [subst; left; auto|   (right; introv Hf; inverts Hf; tryfalse)..].
Qed.

(* ** ac: Print memval. *)
(* ** ac: Print block. *)
(* ** ac: SearchAbout positive. *) (** beq_pos **)
(* ** ac: Check beq_pos. *) (** beq block **)
(* ** ac: Print int32. *)
(* ** ac: SearchAbout int. *)
(* ** ac: Check Int.eq. *) (** beq int32 **)
(* ** ac: SearchAbout nat. *)
(* ** ac: Check Nat.eqb. *) (** beq nat **)

(* ** ac: SearchAbout byte. *)
(* ** ac: Print Byte.eq. *) (** beq int8 **)

(* ** ac: Print memval. *)

Definition beq_memval (a b: memval) : bool :=
  match a, b return bool with
    | Undef, Undef => true
    | Byte i1, Byte i2 => Byte.eq i1 i2
    | Pointer b1 i1 n1, Pointer b2 i2 n2 =>
      (beq_pos b1 b2) && (Int.eq i1 i2) && (Nat.eqb n1 n2) 
    | MNull, MNull => true
    | _, _ => false
  end.

Lemma beq_memval_to_dec:
  forall a b,
    beq_memval a b = true ->
    a = b.
Proof.
  intros.
  unfold beq_memval in *.
  destruct a,b;
  simpl in H; tryfalse; auto.  
  (* ** ac: SearchAbout Byte.eq. *)
  generalize (Byte.eq_spec i i0); intros.
  rewrite H in H0.
  subst; auto.

  destruct (beq_pos b0 b) eqn:F1;
  destruct (Int.eq i i0) eqn:F2;
  destruct (Nat.eqb n n0) eqn:F3;
  simpl in H; tryfalse.
  clear H.

  (* ** ac: SearchAbout beq_pos. *)
  rewrite beq_pos_Pos_eqb_eq in F1.
  (* ** ac: SearchAbout Int.eq. *)
  generalize (Int.eq_spec i i0); intros.
  rewrite F2 in H.
  (* ** ac: SearchAbout Nat.eqb. *)
  apply beq_nat_true in F3.
  (* ** ac: Locate "=?". *)
  (* ** ac: SearchAbout Pos.eqb. *)
  apply Peqb_true_eq in F1.
  subst; auto.
Qed.  

Lemma beq_memval_to_dec':
  forall a b,
    a = b ->
    beq_memval a b = true.
Proof.
  intros.
  subst.
  unfold beq_memval; destruct b; auto.
  (* ** ac: SearchAbout Byte.eq. *)
  apply Byte.eq_true; auto.
  (* ** ac: SearchAbout beq_pos. *)
  rewrite beq_pos_Pos_eqb_eq.
  (* ** ac: SearchAbout Pos.eqb. *)
  rewrite Pos.eqb_refl.
  (* ** ac: SearchAbout Int.eq. *)
  rewrite Int.eq_true.
  (* ** ac: SearchAbout Nat.eqb. *)
  rewrite <- beq_nat_refl.
  auto.
Qed.  

Lemma beq_memval_to_dec'':
  forall a b,
    beq_memval a b = false ->
    a <> b.
Proof.
  intros.
  destruct (memval_eq_dec a b).
  apply beq_memval_to_dec' in e.
  tryfalse.
  auto.
Qed.  

Lemma beq_memval_to_dec''':
  forall a b,
    a <> b ->
    beq_memval a b = false.
Proof.
  intros.
  destruct (beq_memval a b) eqn:F.
  apply beq_memval_to_dec in F.
  tryfalse.
  auto.
Qed.  

(**We only support half permissions here, **)
(**true represents the full permission "1" while **)
(**false represents the half permission "1/2" ,  false + false = true**)

Module HalfPermMap.
  Ltac meauto := eauto 3 with mdb.
  
  Definition A := addr.
  Definition C := memval.

  Definition dec_A := addr_eq_dec.
  Definition dec_C := memval_eq_dec.
  Definition beq_C := beq_memval.
  
  Hint Resolve dec_A : mdb.
  Hint Resolve dec_C : mdb.
  Hint Resolve beq_memval_to_dec beq_memval_to_dec' : mdb.
  Hint Resolve beq_memval_to_dec'' beq_memval_to_dec''' : mdb.
  (** instant begin **)
  (** permition using bool to indicate **)
  Definition B := (bool * C)%type.

  (* partial map *)
  Definition Map := A -> option B.

  Hint Resolve bool_dec : mdb.
  
  Lemma dec_B : forall (x y:B), {x = y} + {x <> y}.
  Proof.
    intros.
    destruct x; destruct y.
    assert ({b = b0} + {b <> b0}) by meauto.
    assert ({c = c0} + {c <> c0}) by meauto.
    destruct H; destruct H0; subst.
    left; auto.
    right.
    unfold not.
    intros.
    inversion H.
    tauto.
    right; unfold not; intro.
    inversion H; tauto.
    right.
    unfold not; intro.
    inversion H; tauto.
  Qed.    

  Definition same (b1 b2:B) : bool :=
    match b1, b2 with
      | (p1, v1), (p2, v2) =>
        (eqb p1 p2) && (beq_C v1 v2)
    end.

  (*
  Lemma dec_map': forall (x y:Map) t, {x t = y t} + {x t <> y t}.
  Proof.
    intros.
    destruct (x t); destruct (y t).
    assert (Htmp: {b = b0} + {b <> b0}) by meauto; destruct Htmp.
    left. subst. auto.
    right; unfold not; intro Htmp; inversion Htmp; tauto.
    right; unfold not; intro Htmp; inversion Htmp; tauto.
    right; unfold not; intro Htmp; inversion Htmp; tauto.
    left; auto.
  Qed.

  (* ** ac: SearchAbout (_ \/ not _). *)
  (* ** ac: SearchAbout sumbool. *)
  
  Lemma dec_map'': forall (x y:Map), {forall t, x t = y t} + {not (forall t, x t = y t)}.
  Proof.    
    intros.
    eapply reflect_dec.
    constructor.
    intros.
    (* ** ac: Print reflect. *)
    (* ** ac: SearchAbout "dec". *)
    (* ** ac: Print Decidable.decidable. *)
    (* ** ac: Check reflect_dec. *)
    (* ** ac: Print reflect. *)
    generalize (dec_map' x y); intros.
    
    
  Lemma dec_map: forall (x y:Map), {x = y} + {x <> y}.
  Proof.
    intros.
    assert (forall t, {x t = y 
  *)

  Definition usePerm := true.

  Lemma map_same:
    forall (v1 v2: B),
      usePerm = true ->
      same v1 v2 = true ->
      v1 = v2.
  Proof.
    intros.
    unfold same in *.
    destruct v1, v2;
    simpl in *; auto.
    destruct b, b0;
    (destruct (dec_C c c0);
     [ (** c = c0 **)
       subst c0;
       assert (Ht:beq_C c c = true) by meauto;
       rewrite Ht in H0;
       tryfalse;
       auto
     | assert (Ht:beq_C c c0 = false) by meauto;
       rewrite Ht in H0;
       tryfalse ]).
  Qed.    

  Lemma map_same':
    forall (v1 v2: B),
      usePerm = true ->
      same v1 v2 = false ->
      v1 <> v2.
  Proof.
    intros.
    unfold same in *.
    destruct v1, v2.
    destruct b, b0;
    try (unfold not; intros; tryfalse);
    (destruct (dec_C c c0);
     [ subst c0;
       assert (Ht: beq_C c c = true) by meauto;
       rewrite Ht in H0;
       tryfalse
     | unfold not; intros; tryfalse]).
  Qed.                             
  
  Definition isRw (v:B) := 
    (fst v).

  Definition flip (b: B) : B :=
    (negb (fst b), snd b).

  Definition sameV (b1 b2 : B) : Prop :=
    (snd b1) = (snd b2).

  Lemma map_sv_ref:
    forall v, usePerm = true -> sameV v v.
  Proof.    
    intros.
    unfold sameV.
    auto.
  Qed.    

  Lemma map_sv_comm:
    forall v v',
      usePerm = true ->
      sameV v v' ->
      sameV v' v.
  Proof.
    intros.
    unfold sameV in *.
    auto.
  Qed.    

  Lemma map_sv_assoc:
    forall v1 v2 v3,
      usePerm = true ->
      sameV v1 v2 ->
      sameV v2 v3 ->
      sameV v1 v3.
  Proof.    
    intros.
    unfold sameV in *.
    unfold snd in *.
    destruct v1; destruct v2; destruct v3; subst; auto.
  Qed.    

  Lemma map_perm_eql:
    forall v1 v2,
      usePerm = true ->
      sameV v1 v2 ->
      isRw v1 = isRw v2 ->
      v1 = v2.
  Proof.
    unfold sameV.
    unfold snd.
    unfold isRw.
    unfold fst.
    intros.
    destruct v1; destruct v2; subst; auto.
  Qed.
    
  Lemma map_flip_isRw:
    forall v,
      usePerm = true ->
      isRw (flip v) = negb (isRw v).
  Proof.
    unfold isRw.
    unfold flip.
    unfold fst.
    intros.
    destruct v; subst; auto.
  Qed.    
    
  Lemma map_flip_sv:
    forall v,
      usePerm = true ->
      sameV v (flip v).
  Proof.
    unfold sameV; unfold flip; unfold fst; unfold snd.
    intros.
    destruct v; subst; auto.
  Qed.    

  Lemma extensionality : forall (A : Type) (B : Type) (f g : A -> B), (forall x : A, f x = g x) -> f = g.
  Proof.
    intros.
    eapply  functional_extensionality; eauto.
  Qed.

  Lemma extensionality_rev :
    forall (A : Type) (B: Type) (f g: A -> B),
      f = g ->
      (forall x, f x = g x).
  Proof.
    intros.
    eapply equal_f.
    auto.
  Qed.

  Lemma extensionality_not:
    forall (A : Type) (B: Type) (f g: A -> B),
      f <> g ->
      (exists x, f x <> g x).
  Proof.
    intros.
    cut (not (forall x, f x = g x)).
    Focus 2.
    unfold not.
    intros.
    apply extensionality in H0.
    tauto.
    intros.
    apply Classical_Pred_Type.not_all_ex_not.
    auto.
  Qed.
    
  Definition disjoint (m1 m2:Map)  :=
    forall (x : A),
      match m1 x, m2 x with
      |  Some  (false, x1), Some (false, x2) => x1 = x2
      |  Some _, None => True
      |  None , Some  _ => True
      |  None, None => True
      |  _, _ => False
      end.

  Definition emp:Map := fun (a:A) => None.

  Definition get := fun (m:Map) x =>  m x.

  Definition set (m:Map) (a:A) (b:B) :=
    (fun x =>  if (dec_A x a) then (Some b) else m x).

  Definition sig := fun a b => set emp a b.

  Goal (Some 1 = None -> False).
    intros.
    inversion H.
    Abort.

   
  Ltac crush :=
    repeat
      match goal with
        | |- context [let (_, _) := ?b in _] =>
          destruct b
        | |- context [if ?b then _ else _] =>
          destruct b
        | H: context [let (_, _) := ?b in _] |- _ =>
          destruct b
        | H: context [if ?b then _ else _] |- _ =>
          destruct b
        | H: Some _ = Some _ |- _ =>
          inversion H; clear H; subst
        | H: Some _ = None |- _ =>
          inversion H 
        | H: None = Some _ |- _ =>
          inversion H
        | H: true = false |- _ =>
          inversion H
        | H: false = true |- _ =>
          inversion H
      end;
    meauto.

  Lemma map_disjoint_comm:
    forall x y,
      disjoint x y ->
      disjoint y x.
  Proof.    
    unfold disjoint.
    intros.
    generalize (H x0); clear H; intro.
    destruct (x x0); destruct (y x0); crush.
  Qed.

  Hint Resolve map_disjoint_comm: mdb.

  
  Lemma map_disjoint_getp1:
    forall x y t v,
      usePerm = true ->
      disjoint x y ->
      get x t = Some v ->
      isRw v = true ->
      get y t = None.
  Proof.
    unfold disjoint.
    unfold get.
    unfold isRw; unfold fst.
    intros.
    instant H0 t.
    destruct (x t); destruct (y t); crush; first [tauto | auto].
  Qed.

  Hint Resolve map_disjoint_getp1 : mdb.

  Lemma map_disjoint_emp:
    forall x,
      disjoint x emp.
  Proof.    
    unfold disjoint.
    unfold emp.
    intros.
    destruct (x x0); crush.
  Qed.

  Hint Resolve map_disjoint_emp: mdb.

  Lemma map_disjoint_getp2:
    forall x y t v v',
      usePerm = true ->
      disjoint x y ->
      get x t = Some v ->
      get y t = Some v' ->
      v' = v /\ isRw v = false.
  Proof.
    unfold disjoint; unfold get; unfold isRw; unfold fst.
    intros.
    instant H0 t.
    destruct (x t); destruct (y t); crush; first [tauto | auto].
  Qed.

  Hint Resolve map_disjoint_getp2 : mdb.
  
  Definition rjoin (b1 b2 : B) :=
    match b1, b2 with
    | (false, x),  (false, y) =>
      if (dec_C x y) then Some (true, x) else Some b1
    | _, _  => Some b1
    end.

  Lemma rjoin_neq_none :
    forall b1 b2,  rjoin b1 b2 <> None.
  Proof.
    intros.
    intro H.
    unfold rjoin in H.
    destruct b1, b2.
    destruct b, b0; inversion H.
    destruct (dec_C  c c0); inversion H.
  Qed.
  Hint Resolve rjoin_neq_none : mdb.
  
  Definition merge (m1 m2:Map)   :=
    fun x => match m1 x with
             | None => m2 x
             | Some b1 =>  match m2 x with
                           | None  => m1 x
                           | Some b2  =>  rjoin b1 b2
                           end
             end.

  Lemma map_merge_emp:
    forall x, merge x emp = x.
  Proof.  
    unfold merge; unfold rjoin.
    intros.
    apply extensionality.
    intros.
    destruct (x x0); crush.
  Qed.
  Hint Resolve map_merge_emp : mdb.

  Lemma map_merge_emp':
    forall x y,
      merge x y = emp ->
      x = emp /\ y = emp.
  Proof.
    unfold merge.
    intros.
    assert (F1:x = emp \/ x <> emp) by tauto.
    assert (F2:y = emp \/ y <> emp) by tauto.
    destruct F1; destruct F2; subst; auto .
    generalize (extensionality_rev H); clear H; intro H.
    unfold emp in *.
    apply extensionality_not in H0.
    destruct H0.
    instant H x0.
    destruct (x x0); crush.
    tauto.
    apply extensionality_not in H0.
    destruct H0.
    unfold emp in *.
    generalize (extensionality_rev H); clear H; intro H.
    instant H x0.
    destruct (x x0); crush.
    destruct (y x0); crush.
    assert (rjoin b b0 <> None) by crush.
    rewrite H in H2.
    tauto.
    tauto.
  Qed.
  Hint Resolve map_merge_emp' : mdb.
  
  Definition join := fun m' m'' m => disjoint m' m'' /\ (m = merge m' m'').

  Lemma map_join_merge:
    forall x y,
      (exists z, join x y z) ->
      join x y (merge x y).
  Proof.
    intros.
    destruct H.
    unfold join in *.
    destruct H.
    split; auto.
  Qed.

  Hint Resolve map_join_merge : mdb.
  
  Lemma map_disjoint_merge_comm:
    forall x y,
      disjoint x y ->
      merge x y = merge y x.
  Proof.
    unfold disjoint; unfold merge; unfold rjoin.
    intros.
    apply extensionality.
    intros.
    instant H x0.
    destruct (x x0); destruct (y x0); crush; try tauto.
    rewrite H in *.
    auto.
    subst.
    tauto.
  Qed.    
  Hint Resolve map_disjoint_merge_comm: mdb.
  
  Lemma map_merge_comm:
    forall x y,
      (exists z, join x y z) ->
      merge x y = merge y x.
  Proof.
    intros.
    destruct H.
    unfold join in H.
    destruct H.
    crush.
  Qed.    
  Hint Resolve map_merge_comm: mdb.
  
  Definition del := fun (m:Map) a => fun x => if (dec_A x a) then None else m x.

  Definition rminus (b1 b2:B) : option B :=
  match b1, b2 with
    | (true, v1), (false, v2) =>
      if (dec_C v1 v2) then Some (false, v1) else None
    | _, _ => None
  end.

  Definition minus (m1 m2:Map) :=
    fun x =>
      match (m1 x) with
        | None => None
        | Some b =>
          match (m2 x) with
            | None => Some b
            | Some b' => rminus b b'
          end
      end.

  Lemma map_join_minus:
    forall z x,
      (exists y, join x y z) ->
      join x (minus z x) z.
  Proof.
    intros.
    destruct H.
    unfolds in H.
    destruct H.
    subst.
    unfolds.
    splits.
    unfold disjoint in *.
    intros.
    lets Hx : H x1.
    clear H.
    remember (x x1) as Hxx.
    destruct Hxx.
    destruct b.
    destruct b.
    remember (x0 x1) as xa.
    destruct xa; tryfalse.
    unfold minus.
    unfold merge.
    rewrite <- HeqHxx.
    rewrite <- Heqxa.
    simpl; auto.
    remember (x0 x1) as xa.
    destruct xa; tryfalse.
    destruct b.
    destruct b; tryfalse.
     unfold minus.
    unfold merge.
    rewrite <- HeqHxx.
    rewrite <- Heqxa.
    subst c.
    simpl.
    induction (dec_C c0 c0); tryfalse.
    simpl.
    induction (dec_C c0 c0); tryfalse.
    auto.
      unfold minus.
    unfold merge.
    rewrite <- HeqHxx.
    rewrite <- Heqxa.
    auto.
      unfold minus.
    unfold merge.
    rewrite <- HeqHxx.
    destruct (x0 x1) ; auto.
    apply extensionality.
    intros.
    unfold merge.
    unfold disjoint in H.
    lets Hx : H x1.
    clear H.
    remember (x x1) as Ha.
    destruct Ha.
    destruct b.
    destruct b.
    remember (x0 x1) as Hf.
    destruct Hf; tryfalse.
    unfold minus.
    rewrite <- HeqHa.
    rewrite <- HeqHf.
    simpl; auto.
     remember (x0 x1) as Hf.
    destruct Hf; tryfalse.
    destruct b.
    destruct b; tryfalse.
    subst c.
    simpl.
    induction (dec_C c0 c0); auto.
    unfold minus.
    rewrite <- HeqHa.
    rewrite <- HeqHf.
    simpl.
    induction (dec_C c0 c0);tryfalse;  auto.
    simpl;auto.
    induction (dec_C c0 c0); tryfalse; auto.
     induction (dec_C c0 c0); tryfalse; auto.
     tryfalse.
     unfold minus.
     rewrite <- HeqHa.
     rewrite <- HeqHf.
     simpl.
     auto.
     unfold minus.
     rewrite <- HeqHa.
     destruct (x0 x1) ; auto.
  Qed.

  Lemma map_join_emp: forall x, join x emp  x.
  Proof.
    unfold join.
    intros.
    split; crush.
  Qed.

  Lemma map_join_pos:
    forall x y,
      join x y emp ->
      x = emp /\ y = emp.
  Proof.
    unfold join.
    intros.
    destruct H.
    assert (F1:x = emp \/ x <> emp) by tauto.
    assert (F2:y = emp \/ y <> emp) by tauto.
    destruct F1; destruct F2; subst; auto .
    assert (merge x emp = x) by crush.
    rewrite H2 in H0.
    subst; auto.
    crush.
  Qed.

  Lemma  map_join_comm:
    forall x y z,
      join x y z ->
      join y x z.
  Proof.
    unfold join.
    intros.
    destruct H.
    assert (disjoint y x) by crush.
    assert (merge x y = merge y x) by crush.
    rewrite H2 in H0.
    auto.
  Qed.    

  Lemma map_join_assoc:
    forall a b mab c mabc,
      join a b mab ->
      join mab c mabc ->
      exists mbc,
        join a mbc mabc /\
        join b c mbc.
  Proof.
    intros.
    unfold join in *.
    exists (merge b c).
    split.
    destruct H0.
    subst.
    destruct H.
    subst.
    split.
    unfold disjoint in *.
    intros.
    generalize (H x) as Hxz.
    clear H.
    intros.
    generalize (H0 x) as Hxzz.
    clear H0.
    intros.
    remember (a x) as Ha.
    remember (merge a b  x) as Hb.
    remember (merge b c x) as Hc.
    destruct Ha, Hb, Hc; auto.
    destruct b0, b1; auto.
    destruct b0, b1; auto.
    remember (b x)  as Hxx.
    remember (c x) as Hcxx.
    destruct Hxx, Hcxx; auto.
    unfold merge in HeqHc.
    rewrite <- HeqHcxx in HeqHc.
    rewrite  <-  HeqHxx in HeqHc.
    inversion HeqHc.
    remember (b x)  as Hxx.
    remember (c x) as Hcxx.
    destruct Hxx, Hcxx; auto.
    destruct b0.
    destruct b0; inversion Hxzz.
    subst.
    unfold merge in *.
    rewrite <- HeqHxx in *.
    rewrite <- HeqHa in *.
    inversion HeqHb.
    unfold merge in *.
    rewrite <- HeqHxx in *.
    rewrite <- HeqHa in *.
    rewrite <- HeqHcxx in HeqHc.
    inversion HeqHc.
    remember (b x)  as Hxx.
    remember (c x) as Hcxx.
    destruct Hxx, Hcxx; auto.
    destruct b0.
    destruct b0; inversion Hxz.
    subst.
    inversion Hxzz.
    destruct b0.
    destruct b0; inversion Hxz.
    subst.
    unfold merge in *.
    rewrite <- HeqHcxx in *.
    rewrite  <-  HeqHxx in *.
    rewrite <- HeqHa in *.
    inversion HeqHc. auto.
    unfold merge in *.
    rewrite <- HeqHcxx in *.
    rewrite  <-  HeqHxx in *.
    rewrite <- HeqHa in *.
    inversion HeqHb.
    unfold merge in *.
    rewrite <- HeqHcxx in *.
    rewrite  <-  HeqHxx in *.
    rewrite <- HeqHa in *.
    inversion HeqHb.
    remember (b x)  as Hxx.
    remember (c x) as Hcxx.
    destruct Hxx, Hcxx; auto.
    destruct b0.
    destruct b0; inversion Hxz.
    destruct b1.
    destruct b0; inversion Hxzz.
    subst.
    unfold merge in *.
    rewrite <- HeqHxx in *.
    rewrite <- HeqHa in *.
    inversion HeqHb.
    simpl in HeqHb.
    induction (dec_C c2 c2); auto.
    inversion H2.
    contradiction.
    destruct b0.
    destruct b0; inversion Hxz.
    subst.
    unfold merge in *.
    rewrite <- HeqHxx in *.
    rewrite <- HeqHa in *.
    rewrite <- HeqHcxx in HeqHc.
    inversion HeqHc. auto.
    destruct b0.
    destruct b0; inversion Hxzz.
    subst.
    unfold merge in *.
    rewrite <- HeqHcxx in *.
    rewrite  <-  HeqHxx in *.
    rewrite <- HeqHa in *.
    inversion HeqHc.
    subst.
    inversion HeqHb.
    auto.
    unfold merge in *.
    rewrite <- HeqHcxx in *.
    rewrite  <-  HeqHxx in *.
    rewrite <- HeqHa in *.
    inversion HeqHb.
    subst.
    inversion HeqHc.
    destruct b0.
    destruct b1.
    destruct b0; auto.
    remember (b x)  as Hxx.
    remember (c x) as Hcxx.
    destruct Hxx, Hcxx; auto.
    destruct b0.
    destruct b2.
    destruct b0, b2; inversion Hxz.
    subst.
    unfold merge in *.
    rewrite <- HeqHxx in *.
    rewrite <- HeqHa in *.
    rewrite <- HeqHcxx in *.
    simpl in HeqHb.
    induction (dec_C c1 c1); auto.
    inversion HeqHb.
    contradiction.
    destruct b0.
    destruct b2.
    destruct b0, b2; inversion Hxz.
    unfold merge in *.
    rewrite <- HeqHcxx in *.
    rewrite  <-  HeqHxx in *.
    rewrite <- HeqHa in *.
    subst.
    simpl in HeqHb.
    induction (dec_C c1 c1); auto.
    inversion HeqHb.
    contradiction.
    destruct b0.
    unfold merge in *.
    rewrite <- HeqHxx in *.
    rewrite <- HeqHa in *.
    rewrite <- HeqHcxx in *.
    inversion HeqHb.
    unfold merge in *.
    rewrite <- HeqHxx in *.
    rewrite <- HeqHa in *.
    rewrite <- HeqHcxx in *.
    inversion HeqHc.
    destruct b0.
    destruct b0; auto.
    eapply extensionality.
    intros.
    unfold merge in *.
    unfold disjoint in *.
    generalize (H x) as Hxx.
    generalize (H0 x) as Hyhy.
    clear H H0.
    intros.
    remember (a x) as Ha.
    remember (b x) as Hb.
    remember (c x) as Hc.
    destruct Ha, Hb, Hc; auto.
    destruct b0.
    destruct b1.
    destruct b0, b1; inversion Hxx.
    subst.
    simpl in *.
    destruct b2.
    induction (dec_C c1 c1); auto.
    inversion Hyhy.
    contradiction.
    destruct b0.
    destruct b1.
    destruct b0, b1; inversion Hxx.
    subst.
    simpl in *.
    induction (dec_C c1 c1); auto.
    destruct H.
    destruct H0.
    subst.
    split.
    unfold disjoint in *.
    unfold merge in H0.
    intros.
    generalize (H x) as Hxx.
    generalize (H0 x) as Hyhy.
    clear H H0.
    intros.
    remember (a x) as Ha.
    remember (b x) as Hb.
    remember (c x) as Hc.
    destruct Ha, Hb, Hc; auto.
    destruct b0.
    destruct b1.
    destruct b0, b1; inversion Hxx.
    subst.
    simpl in *.
    induction (dec_C c1 c1); auto.
    inversion Hyhy.
    destruct b0.
    destruct b1.
    destruct b1; auto.
    eapply extensionality.
    intros.
    unfold merge in *.
    unfold disjoint in *.
    generalize (H x) as Hxx.
    generalize (H0 x) as Hyhy.
    clear H H0.
    intros.
    remember (a x) as Ha.
    remember (b x) as Hb.
    remember (c x) as Hc.
    destruct Ha, Hb, Hc; auto.
  Qed.

  Lemma  map_join_cancel:
    forall a b b' c,
      join a b c ->
      join a b' c ->
      b = b'.
  Proof.
    intros.
    unfold join in *.
    destruct H.
    destruct H0.
    rewrite H1 in H2.
    eapply extensionality.
    intros.
    unfold disjoint in *.
    generalize (H x) as Hx.
    generalize (H0 x) as Hy.
    clear H H0.
    intros.
    remember (a x)  as Ha.
    remember (b x) as Hb.
    destruct Ha, Hb; auto.
    destruct b0, b1.
    destruct b0, b1; inversion Hx.
    assert (merge a b x  = merge a b' x).
    rewrite H2.
    auto.
    unfold merge in *.
    rewrite <- HeqHa, HeqHb in *.
    subst.
    rewrite <- HeqHb in H0.
    remember (b' x) as Hbx.
    destruct Hbx.
    destruct b0.
    destruct b0; inversion Hy.
    subst.
    auto.
    simpl in H0.
    induction (dec_C c1 c1); auto.
    inversion H0.
    contradiction.
    destruct b0.
    assert (merge a b x  = merge a b' x).
    rewrite H2.
    auto.
    unfold merge in *.
    rewrite <- HeqHa, HeqHb in *.
    rewrite <- HeqHb in H.
    remember (b' x) as Hbx.
    destruct Hbx.
    destruct b0.
    inversion Hy.
    destruct b1.
    destruct b0; inversion Hy.
    subst.
    simpl in H.
    induction (dec_C c1 c1); auto.
    inversion H.
    contradiction.
    auto.
    assert (merge a b x  = merge a b' x).
    rewrite H2.
    auto.
    unfold merge in *.
    rewrite <- HeqHa, HeqHb in *.
    auto.
    assert (merge a b x  = merge a b' x).
    rewrite H2.
    auto.
    unfold merge in *.
    rewrite <- HeqHa, HeqHb in *.
    auto.
  Qed.

  Lemma  map_join_deter:
    forall a b c c',
      join a b c ->
      join a b c' ->
      c = c'.
  Proof.
    intros.
    unfold join in *.
    destruct H.
    destruct H0.
    subst.
    auto.
  Qed.

  Lemma map_emp_get:
    forall t, get emp t = None.
  Proof.
    intros.
    unfold emp.
    unfold get.
    auto.
  Qed.

  Lemma map_eql:
    forall x y,
      (forall t, get x t = get y t) ->
      x = y.
  Proof.
    eapply extensionality.
  Qed.

  Lemma map_disjoint':
    forall x y,
      (forall t, get x t = None \/
            get y t = None \/
            (exists v,
                usePerm = true /\
                get x t = Some v /\
                get y t = Some v /\
                isRw v = false)) ->
      disjoint x y.
  Proof.
    intros.
    unfold disjoint.
    intro t.
    instant H t.
    destruct H.
    unfold get in H.
    rewrite H.
    crush.
    destruct H.
    unfold get in H.
    rewrite H.
    destruct (x t); crush.
    heat.
    unfold get in *.
    rewrite H0.
    rewrite H1.
    crush.
    unfold isRw in *.
    unfold fst in *.
    eat_false.
  Qed.
    
  Lemma map_disjoint:
    forall x y,
      (forall t, get x t = None \/
            get y t = None \/
            (exists v,
                usePerm = true /\
                get x t = Some v /\
                get y t = Some v /\
                isRw v = false)) ->
      exists z, join x y z.
  Proof.
    intros.
    assert (disjoint x y) by auto using map_disjoint'.
    exists (merge x y).
    unfold join.
    auto.
  Qed.
      
  Lemma map_get_unique:
      forall x t v v',
        get x t = Some v ->
        get x t = Some v' ->
        v = v'.
  Proof.
    unfold get.
    intros.
    rewrite H in H0.
    inversion H0; auto.
  Qed.    
    
  Lemma map_get_sig:
    forall t v,
      get (sig t v) t = Some v.
  Proof.    
    unfold get; unfold sig; unfold set.
    intros.
    destruct (dec_A t t).
    auto.
    tauto.
  Qed.
    
  Lemma map_get_sig':
    forall t t' v,
      t <> t' ->
      get (sig t v) t' = None.
  Proof.
    unfold get; unfold sig; unfold set.
    intros.
    destruct (dec_A t' t).
    subst; tauto.
    unfold emp.
    auto.
  Qed.    
    
  Lemma map_get_set:
    forall x t v,
      get (set x t v) t = Some v.
  Proof.
    unfold get; unfold set.
    intros.
    destruct (dec_A t t); auto.
    tauto.
  Qed.    

  Lemma map_get_set':
    forall x t t' v,
      t <> t' ->
      get (set x t v) t' = get x t'.
  Proof.    
    unfold get; unfold set.
    intros.
    destruct (dec_A t' t); auto.
    subst; auto.
    tauto.
  Qed.    

  Lemma map_merge_get_none:
    forall x y t,
      disjoint x y ->
      get x t = None ->
      get (merge x y ) t = get y t.
  Proof.
    unfold merge; unfold disjoint; unfold get.
    intros.
    rewrite H0 in *.
    auto.
  Qed.
  Hint Resolve map_merge_get_none : mdb.
  
  Lemma map_join_get_none:
    forall x y z t,
      join x y z ->
      get x t = None ->
      get z t = get y t.
  Proof.    
    intros.
    unfold join in *.
    destruct H.
    rewrite H1 in *.
    crush.
  Qed.
    
  (** ** no permission **)
  Lemma map_join_get_some:
    forall x y z t v1 v2,
      usePerm = false ->
      join x y z ->
      get x t = Some v1 ->
      get y t = Some v2 ->
      False.
  Proof.
    intros.
    unfold usePerm in *.
    inversion H.
  Qed.    
      
  (** ** use permission **)
  Lemma map_join_getp_some:
    forall x y z t v1 v2 v',
      usePerm = true ->
      join x y z ->
      get x t = Some v1 ->
      get y t = Some v2 ->
      v' = flip v1 ->
      v1 = v2 /\ isRw v1 = false /\ get z t = Some v'.
  Proof.
    unfold join; unfold disjoint; unfold merge; unfold get; unfold flip.
    intros.
    destruct H0.
    destruct v1; destruct v2.
    generalize (extensionality_rev H4); clear H4; intro H4.
    instant H4 t.
    instant H0 t.
    rewrite H1 in *.
    rewrite H2 in *.
    clear H1 H2.
    crush.
    inversion H0.
    inversion H0.
    unfold rjoin in *.
    unfold isRw.
    unfold negb.
    unfold fst.
    unfold snd.
    crush.
    subst.
    tauto.
    subst; tauto.
  Qed.
  (** BUG:indentation dely **)

  (** * set **)
  (** ** general **)
  Lemma map_set_emp:
    forall t v,
      set emp t v = sig t v.
  Proof.
    unfold sig; unfold set; unfold emp.
    intros.
    apply extensionality.
    intros.
    crush.
  Qed.
    
  Lemma map_set_sig:
    forall t v v',
      set (sig t v) t v' = sig t v'.
  Proof.
    unfold sig; unfold set; unfold emp.
    intros.
    apply extensionality.
    intros.
    crush.
  Qed.   

  Ltac crush' :=
    repeat
      match goal with
        | |- context [let (_, _) := ?b in _] => destruct b
        | |- context [if ?b then _ else _] => destruct b
        | H:context [let (_, _) := ?b in _] |- _ => destruct b
        | H:context [if ?b then _ else _] |- _ => destruct b
        | H:Some _ = Some _ |- _ => inversion H; clear H; subst
        | H:Some _ = None |- _ => inversion H
        | H:None = Some _ |- _ => inversion H
        | H:true = false |- _ => inversion H
        | H:false = true |- _ => inversion H
      end; meauto.
  
  Lemma map_disjoint_set:
    forall x y t v,
      disjoint x y ->
      get x t = None ->
      disjoint x (set y t v).
  Proof.    
    unfold disjoint.
    intros.
    rename x0 into t'.
    assert (F1: (t = t') \/ (t <> t')) by tauto.
    destruct F1.
    subst.
    unfold get in *.
    rewrite H0 in *.
    unfold set.
    crush.

    instant H t'.
    destruct (x t').
    unfold set.
    destruct b.
    destruct b.
    destruct (y t').
    destruct (dec_A t' t).
    subst; tauto.
    auto.
    destruct (dec_A t' t).
    subst; tauto.
    auto.
    crush.
    subst; tauto.
    crush.
  Qed.
    
  Lemma map_join_set_none:
    forall x y z t v',
      join x y z ->
      get y t = None ->
      join (set x t v') y (set z t v').
  Proof.
    unfold join.
    intros.
    destruct H.
    split.
    assert (disjoint y x) by meauto.
    apply map_disjoint_comm.
    apply map_disjoint_set; meauto.

    apply extensionality.
    intros.
    rewrite H1 in *.
    clear H1.
    unfold merge; unfold set; unfold get in *.
    destruct (dec_A x0 t). subst.
    destruct (y t). crush. auto.
    unfold disjoint in *. 
    instant H x0.
    destruct (x x0); crush.
  Qed.
    
  Lemma map_join_set_perm:
      forall x y z t v v',
        usePerm = true ->
        join x y z ->
        get x t = None ->
        get y t = Some v ->
        isRw v = false ->
        v' = flip v ->
        join (set x t v) y (set z t v').
  Proof.    
    intros.
    unfold join in *.
    destruct H0.
    split.
    unfold disjoint in *; unfold get in *; unfold isRw in *; unfold fst in *.
    intros.
    unfold set.     
    destruct (dec_A x0 t); subst.
    destruct (y t); crush.
    instant H0 x0.
    destruct v.
    destruct (x x0).
    destruct b0. destruct b0.
    auto.
    auto.
    auto.

    apply extensionality.
    intros.
    unfold disjoint in *; unfold merge in *; unfold get in *; unfold isRw in *; unfold flip in *;
    unfold fst in *; unfold snd in *; unfold negb in *; unfold set in *.
    destruct v.
    destruct b.
    destruct (dec_A x0 t).
    subst.
    instant H0 t.
    crush.

    subst.
    crush.
    subst.
    destruct (dec_A x0 t).
    subst.
    instant H0 t.
    destruct (y t).
    rewrite H1 in *.
    unfold rjoin.
    destruct b.
    destruct b.
    inversion H2.
    destruct (dec_C c c0); subst; crush.
    tauto.
    crush.

    instant H0 x0.
    destruct (x x0).
    destruct (y x0).
    destruct b.
    destruct b; auto.
    auto.
    auto.
  Qed.    
    
  Lemma map_join_get_sig:
      forall x t v,
        get x t = Some v ->
        exists x', join (sig t v) x' x.
  Proof.
    intros.
    exists (del x t).
    unfold get, join, sig in *.
    unfold disjoint, set, emp, del, merge.
    split.
    intros.
    induction (dec_A x0 t).
    destruct v; auto.
    destruct b; auto.
    destruct (x x0); auto.
    eapply extensionality.
    intros.
    induction (dec_A x0 t).
    subst; auto.
    auto.
  Qed.
  
  Lemma map_join_get_sig_perm:
    forall x t v v',
      usePerm = true ->
      get x t = Some v ->
      isRw v = true ->
      v' = flip v ->
      exists x1 x2, join (sig t v') x1 x /\ join (sig t v') x2 x1.
  Proof.
    unfold get; unfold isRw; unfold fst; unfold flip; unfold snd.
    unfold negb.
    unfold fst.
    intros.
    exists (set x t v').
    exists (del x t).
    destruct v.
    unfold set; unfold del.
    unfold sig.
    unfold set; unfold emp.
    subst.

    split.
    unfold join; split.
    unfold disjoint.
    intros.
    destruct (dec_A x0 t); subst; crush.

    unfold merge.
    apply extensionality.
    intros.
    destruct (dec_A x0 t); subst; crush.
    rewrite H0.
    unfold rjoin; crush.
    tauto.

    unfold join; split.
    unfold disjoint.
    intros.
    destruct (dec_A x0 t); subst; crush.

    unfold merge.
    apply extensionality.
    intros.
    destruct (dec_A x0 t); subst; crush.
  Qed.

  (** aux essential lemmas **)
  Hint Resolve map_same map_same' : mdb.

  Ltac same_to_dec :=
    repeat match goal with
             | H: same ?v1 ?v2 = true |- _ =>
               assert (v1 = v2) by meauto;
               try (rewrite H in *);
               clear H
             | H: same ?v1 ?v2 = false |- _ =>
               assert (v1 <> v2) by meauto;
               try (rewrite H in *);
               clear H
           end.
  
  Ltac crush2 :=
    repeat match goal with
             | m: Map, t: A |- _ =>
               match goal with
                 | |- context [m t] =>
                   let F := fresh in
                   destruct (m t) eqn:F
               end
             | H:Some _ = Some _ |- _ => inversion H; clear H; try (subst)
             | |- context [dec_A ?x ?y] =>
               destruct (dec_A x y); try (subst); tryfalse
             | |- context [same ?x ?y] =>
               let Hb := fresh in
               destruct (same x y) eqn:Hb;
               same_to_dec;
               try (subst); tryfalse
             | |- context [dec_C ?x ?y] =>
               destruct (dec_C x y); try (subst); tryfalse
             | H: context [dec_A ?x ?y] |- _ =>
               destruct (dec_A x y); try (subst); tryfalse
             | H: context [same ?x ?y] |- _ =>
               let Hn := fresh in 
               destruct (same x y) eqn:Hn;
               same_to_dec;
               try (subst); tryfalse
             | H: context [dec_C ?x ?y] |- _ =>
               destruct (dec_C x y); try (subst); tryfalse
             | H: (_, _) = (_, _) |- _ =>
               inverts H
             | b : B |- _ =>
               destruct b
             | b : bool |- _ =>
               destruct b
             | H: _ /\ _ |- _ =>
               destruct H
           end;
    try subst; simpl in *; tryfalse; meauto.

  Ltac crush ::= crush2.

  (* Ltac crush1 := *)
  (*   repeat match goal with *)
  (*            | H:Some _ = Some _ |- _ => inversion H; clear H; try (subst) *)
  (*            | |- context [dec_A ?x ?y] => *)
  (*              destruct (dec_A x y); try (subst); tryfalse *)
  (*            | |- context [dec_B ?x ?y] => *)
  (*              destruct (dec_B x y); try (subst); tryfalse *)
  (*            | |- context [dec_C ?x ?y] => *)
  (*              destruct (dec_C x y); try (subst); tryfalse *)
  (*            | H: context [dec_A ?x ?y] |- _ => *)
  (*              destruct (dec_A x y); try (subst); tryfalse *)
  (*            | H: context [dec_B ?x ?y] |- _ => *)
  (*              destruct (dec_B x y); try (subst); tryfalse *)
  (*            | H: context [dec_C ?x ?y] |- _ => *)
  (*              destruct (dec_C x y); try (subst); tryfalse *)
  (*            | b : B |- _ => *)
  (*              destruct b *)
  (*            | b : bool |- _ => *)
  (*              destruct b *)
  (*          end; *)
  (*   tryfalse; meauto. *)

  (* Ltac crush ::= crush1. *)

  Ltac junfold :=
    try (unfold join);
    try (unfold disjoint);
    try (unfold merge);
    try (unfold minus);
    try (unfold del);
    try (unfold get);
    try (unfold set);
    try (unfold sig);
    try (unfold rjoin);
    try (unfold rminus);
    try (unfold isRw);
    try (unfold flip).
  
  Lemma map_merge_semp:
      (** def2 **)
      forall m1 m2 a,
        usePerm = true ->
        get (merge m1 m2) a
        = match (get m1 a, get m2 a) with
            | (Some b1, Some b2) => 
              match (same b1 b2) return (option B) with
                | true => match (isRw b1) with
                             | true => Some b1
                             | false => Some (flip b1)
                           end
                | false => Some b1
              end
            | (None, Some b2) => Some b2
            | (Some b1, None) => Some b1
            | (None, None) => None
          end.
  Proof.
    intros.
    junfold.
    destruct (m1 a) eqn:F1;
    destruct (m2 a) eqn:F2;
    crush.
  Qed.    

  
  Lemma map_disjoint_semp:
    forall m1 m2,
      usePerm = true ->
      (forall t,
          match (get m1 t, get m2 t) with
            | (Some b0, Some b1) => b0 = b1 /\ isRw b0 = false
            | (Some b0, None) => True
            | (None, Some b1) => True
            | (None, None) => True
          end) ->
      (exists m, join m1 m2 m).
  Proof.
    intros.
    eexists.
    unfold join.
    split; eauto.
    generalize H0; clear H0.
    junfold.
    intros.
    instant H0 x.
    crush.
  Qed.
    
  Lemma map_disjoint_semp':
    forall m1 m2,
      usePerm = true ->
      (exists m, join m1 m2 m) ->
      (forall t,
          match (get m1 t, get m2 t) with
            | (Some b0, Some b1) => b0 = b1 /\ isRw b0 = false
            | (Some b0, None) => True
            | (None, Some b1) => True
            | (None, None) => True
          end).
  Proof.
    intros.
    destruct H0.
    unfold join in H0.
    destruct H0.
    clear x H1.

    generalize H0; clear H0;
    junfold.
    intros.
    instant H0 t.
    crush.
  Qed.

  
  Lemma map_minus_semp:
    (** def2 **)
    forall m1 m a,
      usePerm = true ->
      get (minus m m1) a
      = match (get m a, get m1 a) with
          | (Some b, Some b1) =>
            match (same b (flip b1)) return (option B) with
              | true => match (isRw b) with
                           | true => Some b1
                           | false => None
                         end
              | false => None
            end
          | (Some b, None) => Some b
          | (None, Some b1) => None
          | (None, None) => None
        end.
  Proof.
    intros.
    junfold.
    crush.
  Qed.

  Lemma map_del_sem:
    forall m a t,
      get (del m a) t
      = match (dec_A a t) with
          | left _ => None
          | right _ => get m t
        end.
  Proof.
    intros.
    junfold.
    crush.
  Qed.
    
End HalfPermMap.


(*The memory is defined as a partial function from addresses to memory values with permissions*)
Definition mem := HalfPermMap.Map.

Instance memMap: PermMap addr (bool * memval) mem :=
  {
    usePerm := HalfPermMap.usePerm;
    isRw := HalfPermMap.isRw;
    flip := HalfPermMap.flip;
    sameV := HalfPermMap.sameV;
    same := HalfPermMap.same;
    emp :=HalfPermMap.emp;
    get :=HalfPermMap.get;
    set := HalfPermMap.set;
    del := HalfPermMap.del;
    sig := HalfPermMap.sig;
    join := HalfPermMap.join;
    merge := HalfPermMap.merge;
    minus := HalfPermMap.minus
}.
Proof.
  exact HalfPermMap.dec_A.
  exact HalfPermMap.map_same.
  exact HalfPermMap.map_same'.
  exact HalfPermMap.map_join_emp.
  exact HalfPermMap.map_join_pos.
  exact HalfPermMap.map_join_comm.
  exact HalfPermMap.map_join_assoc.
  exact HalfPermMap.map_join_cancel.
  exact HalfPermMap.map_join_deter.
  exact HalfPermMap.map_sv_ref.
  exact HalfPermMap.map_sv_comm.
  exact HalfPermMap.map_sv_assoc.
  exact HalfPermMap.map_perm_eql.
  exact HalfPermMap.map_flip_isRw.
  exact HalfPermMap.map_flip_sv.
  exact HalfPermMap.map_emp_get.
  exact HalfPermMap.map_eql.
  exact HalfPermMap.map_disjoint.
  exact HalfPermMap.map_get_unique.
  exact HalfPermMap.map_get_sig.
  exact HalfPermMap.map_get_sig'.
  exact HalfPermMap.map_get_set.
  exact HalfPermMap.map_get_set'.
  exact HalfPermMap.map_join_get_none.
  exact HalfPermMap.map_join_get_some.
  exact HalfPermMap.map_join_getp_some.
  exact HalfPermMap.map_set_emp.
  exact HalfPermMap.map_set_sig.
  exact HalfPermMap.map_join_set_none.
  exact HalfPermMap.map_join_set_perm.
  exact HalfPermMap.map_join_get_sig.
  exact HalfPermMap.map_join_get_sig_perm.
  intros; tryfalse.
  exact HalfPermMap.map_merge_semp.
  exact HalfPermMap.map_join_merge.
  exact HalfPermMap.map_merge_comm.
  exact HalfPermMap.map_disjoint_semp.
  exact HalfPermMap.map_disjoint_semp'.
  intros; tryfalse.
  exact HalfPermMap.map_minus_semp.
  exact HalfPermMap.map_join_minus.
  exact HalfPermMap.map_del_sem.
Defined.

(*
Goal forall (x y:mem) t, indom x t -> sub x y.
Proof.
  intros.
  unfold indom in *.
  unfold sub.
 *)

(**We define the operations over the physical memory model as bellow **)
(*fresh is a predicate to specify a fresh memory block b*)
Definition fresh (m : mem) (b : block) : Prop :=
  forall l i, l = (b, i) -> ~ indom m l.

Fixpoint allocb (m : mem) (b: block) (i : offset)  (n : nat) {struct n} :  mem :=
  match n  with
    | O =>  m
    | S n' => set (allocb m b (i+1) n') (b, i) (true,Undef)
  end.

Fixpoint freeb (m : mem) (b: block) (i : Z)  (n : nat) {struct n} : option mem :=
  match n  with
    | O =>  Some m
    | S n' => match get m (b, i), freeb m b (i+1) n'  with
                | Some (true,v), Some m' =>  Some (del m' (b, i))
                | _, _ => None
              end
  end.

Fixpoint storebytes (m : mem) (l : addr) (bl :list memval) {struct bl}: option mem :=
  match bl with
    | nil => Some m
    | u :: bl' => match l with
                      (b , i) =>
                      match get m l, storebytes m (b, (i+1)) bl' with
                        | Some (true,_), Some m' => Some (set m' l (true,u))
                        | _, _ => None
                      end
                  end
  end.

Fixpoint loadbytes (m : mem) (l : addr) (n : nat) {struct n}: option (list memval) :=
  match n with
    | O => Some nil
    | S n' => match l with
                  (b , i) =>
                  match get m l, loadbytes m (b, (i+1)) n' with
                    | Some (_,u), Some bl => Some (u :: bl)
                    | _, _ => None
                  end
              end
  end.

Definition FullMemory m := forall b, exists i, indom m (b,i).

(*To make the memory allocation never fail, we introduce the following axiom,
which assumes that we have infinite memory space *)
Axiom MemoryNotFull : forall m, ~FullMemory m.


(********************************************************************)
(********************************************************************)

(**Definition of values and types, operations over values**)

Inductive val: Set :=
| Vundef: val
| Vnull : val
| Vint32  : int -> val
| Vptr  : addrval -> val.

Definition val_inj (v : option val) : val :=
  match v with
    | Some v' => v'
    | None => Vundef
  end.

Definition vallist : Set := list val.

Definition ident := Z.
Inductive type : Set :=
| Tnull
| Tvoid
| Tint8
| Tint16
| Tint32
| Tptr : type -> type
| Tcom_ptr : ident -> type
| Tarray : type -> nat -> type
| Tstruct : ident -> decllist -> type
with
decllist : Set:=
| dnil : decllist
| dcons : ident -> type -> decllist -> decllist.

Fixpoint type_eq (t1 t2:type):=
  match t1,t2 with
    | Tvoid, Tvoid => true
    | Tnull, Tnull => true
    | Tint8, Tint8 =>true
    | Tint16, Tint16 => true
    | Tint32, Tint32 =>true
    | Tptr t1', Tptr t2' => type_eq t1' t2'
    | Tstruct id dl,Tstruct id' dl' => andb ( Zeq_bool  id id') (dl_eq dl dl')
    | Tarray t n,Tarray t' n' =>andb( type_eq t t') (beq_nat n  n')
    | Tcom_ptr x1 , Tcom_ptr x2 => Zeq_bool x1 x2    
    | _, _ => false
  end
with dl_eq (d1 d2:decllist):=
       match d1 with
         | dnil => match d2 with
                     |dnil =>true
                     |_ => false
                   end
         | dcons a b d1'=> match d2 with
                             |  dnil =>false
                             |  dcons a' b' d2' => 
                                andb (andb ( Zeq_bool  a a') (type_eq b b')) (dl_eq d1' d2') 
                           end
       end.

Scheme type_ind2 := Induction for type Sort Prop with decllist_ind2 := Induction for decllist Sort Prop. 
Lemma type_eq_true_eq : forall t1 t2, type_eq t1 t2 = true -> t1 = t2.
Proof.
  intro.
  elim t1 using type_ind2 with (P0 := fun d1 : decllist => forall d2, dl_eq d1 d2 = true -> d1 = d2); intros;
  try solve [simpl in H; destruct t2; tryfalse; auto];
  try solve [simpl in H0; destruct t2; tryfalse; apply H in H0; substs; auto];
  try (simpl in H0; destruct t2; tryfalse; apply andb_true_iff in H0; destruct H0).
  simpl in H.
  destruct t2; tryfalse.
  apply Zeq_bool_eq in H.
  subst; auto.
  apply beq_nat_true in H1; substs.
  apply H in H0; substs; auto.
  apply Zeq_bool_eq in H0; substs.
  apply H in H1; substs; auto.
  simpl in H; destruct d2; tryfalse; auto.
  simpl in H1; destruct d2; tryfalse.
  apply andb_true_iff in H1.
  destruct H1.
  apply andb_true_iff in H1; destruct H1.
  apply Zeq_bool_eq in H1; substs.
  apply H in H3; substs.
  apply H0 in H2; substs.
  auto.
Qed.


Definition typelist : Set := list type.
Definition freelist : Set:= list (prod block type).

Fixpoint typelen (t : type) : nat :=
  match t with
    | Tnull => 4 %nat
    | Tvoid => 0 % nat
    | Tint8 => 1 % nat
    | Tint16 => 2 % nat
    | Tint32 => 4  % nat
    | Tptr _ => 4 % nat
    | Tcom_ptr  _ => 4 % nat
    | Tarray t' n => mult (typelen t') n
    | Tstruct _ dls  => szstruct dls
  end
with szstruct (dls : decllist) {struct dls} : nat :=
       match dls with
         | dnil => O
         | dcons _ t1 dls' => plus (typelen t1) (szstruct dls')
       end.

Definition rule_type_val_match (t:type) (v:val) :=
  match t,v with
    | Tnull, Vnull  => true
    | Tint8,Vint32 v => (*if v is in the range of Tint8 return True, if not return False*)
      match (Int.unsigned v) <=? Byte.max_unsigned with
        | true => true
        | false => false
      end
    | Tint16,Vint32 v => (*if v is in the range of Tint16 return True, if not return False*)
      match (Int.unsigned v) <=? Int16.max_unsigned with
        | true => true
        | false => false
      end
    | Tint32,Vint32 v =>true
    | Tptr t,Vptr l => true
    | Tcom_ptr i,Vptr l => true
    | Tptr t ,Vnull => true
    | Tcom_ptr i,Vnull => true
    | _,_=> false
  end.

Inductive uop :=
 | oppsite
 | negation.

Inductive bop:=
 | oplus
 | ominus
 | omulti
 | odiv
 | olshift
 | orshift
 | oand
 | oor
 | obitand
 | obitor
 | oeq
 | olt.

(* uop *)
Definition notint (v: val) : option val :=
  match v with
    | Vint32 n => Some (Vint32 (Int.notbool n))
    | _ => None
  end.

Definition negint (v: val) : option val :=
  match v with
    | Vint32 n => Some (Vint32 (Int.not n))
    | _ => None
  end.


Definition uop_eval (v:val) (op1:uop):=
  match op1 with
    | oppsite => notint v
    | negation => negint v
  end.

Definition uop_type (t : type) (op1 : uop):=
  match t with
    | Tint8 => Some Tint8
    | Tint16=> Some Tint16
    | Tint32=> Some Tint32
    | _ =>None
  end.


Definition sub (v1 v2: val) (t1:type): option val :=
  match v1, v2 with
    | Vint32 n1, Vint32 n2 => Some (Vint32(Int.sub n1 n2))
    | Vptr (b1, ofs1), Vint32 n2 => match t1 with
                                      | Tptr t => Some( Vptr (b1, (Int.sub ofs1 (Int.mul n2 (Int.repr (Z_of_nat (typelen t)))))))
                                      | _ => None
                                    end
    | _, _ => None
  end.


Definition add (v1 v2: val) (t1 t2:type): option val :=
  match v1, v2 with
    | Vint32 n1, Vint32 n2 =>Some( Vint32(Int.add n1 n2))
    | Vptr (b1, ofs1), Vint32 n2 =>match t1 with
                                     | Tptr t => Some( Vptr (b1, (Int.add ofs1 (Int.mul n2 (Int.repr (Z_of_nat (typelen t)))))))
                                     | _ => None
                                   end
    | Vint32 n1, Vptr (b2, ofs2) =>match t2 with
                                     | Tptr t => Some( Vptr (b2, (Int.add ofs2 (Int.mul n1 (Int.repr (Z_of_nat (typelen t)))))))
                                     | _ => None
                                   end
    | _, _ => None
  end.

Definition mul (v1 v2: val): option val :=
  match v1, v2 with
    | Vint32 n1, Vint32 n2 => Some (Vint32(Int.mul n1 n2))
    | _, _ => None
  end.

Definition divs (v1 v2: val): option val :=
  match v1, v2 with
    | Vint32 n1, Vint32 n2 =>
      if Int.eq n2 Int.zero
                || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone
      then None
      else Some(Vint32(Int.divs n1 n2))
    | _, _ => None
  end.


Definition and (v1 v2: val): option val :=
  match v1, v2 with
    | Vint32 n1, Vint32 n2 => Some (Vint32(Int.and n1 n2))
    | _, _ => None
  end.

Definition or (v1 v2: val): option val :=
  match v1, v2 with
    | Vint32 n1, Vint32 n2 =>Some ( Vint32(Int.or n1 n2))
    | _, _ => None
  end.


Definition shl (v1 v2: val):option val :=
  match v1, v2 with
    | Vint32 n1, Vint32 n2 =>
      if Int.ltu n2 Int.iwordsize
      then Some(Vint32(Int.shl n1 n2))
      else None
    | _, _ => None
  end.

Definition shr (v1 v2: val):option val :=
  match v1, v2 with
    | Vint32 n1, Vint32 n2 =>
      if Int.ltu n2 Int.iwordsize
      then Some(Vint32(Int.shru n1 n2))
      else None
    | _, _ => None
  end.

Definition val_eq (v1 v2:val):option val :=
  match v1, v2 with
    | Vint32 n1, Vint32 n2 => if (Int.eq n1 n2)
                              then Some(Vint32 (Int.one))
                              else Some(Vint32 (Int.zero))
    | Vptr (b1, ofs1), Vptr (b2, ofs2) =>
      if peq b1 b2 then (if (Int.eq ofs1 ofs2)
                         then Some(Vint32 (Int.one))
                         else Some(Vint32 (Int.zero)))
      else Some(Vint32 (Int.zero))
    | Vnull, Vptr (b,ofs) => Some (Vint32 (Int.zero))
    | Vptr (b,ofs), Vnull => Some (Vint32 (Int.zero))
    | Vnull, Vnull => Some (Vint32 (Int.one))
    | _, _ => None
  end.

Definition cmpu :=
  fun (c : comparison) (x y : int32) =>
    match c with
      | Ceq => Int.eq x y
      | Cne => negb (Int.eq x y)
      | Clt => Int.ltu x y
      | Cle => negb (Int.ltu y x)
      | Cgt => Int.ltu y x
      | Cge => negb (Int.ltu x y)
    end.

Definition cmp_val (c: comparison) (v1 v2: val): option val :=
  match v1, v2 with
    | Vint32 n1, Vint32 n2 => if (cmpu c n1 n2)
                              then Some(Vint32 (Int.one))
                              else Some(Vint32 (Int.zero))
    | _, _ => None
  end.

Definition bool_and (v1 v2:val) : option val:=
  match v1,v2 with
    |Vint32 n1,Vint32 n2=> if Int.ltu Int.zero n1 && Int.ltu Int.zero n2
                           then Some(Vint32 Int.one)
                           else Some(Vint32 Int.zero)
    |_, _ =>None
  end.

Definition bool_or (v1 v2:val) : option val:=
  match v1,v2 with
    |Vint32 n1,Vint32 n2=> if Int.ltu Int.zero n1 || Int.ltu Int.zero n2
                           then Some(Vint32 Int.one)
                           else Some(Vint32 Int.zero)
    |_, _ =>None
  end.

Definition bop_eval (v1 v2:val) (t1 t2:type) (op1:bop) :=
  match op1 with
    | oplus => add v1 v2 t1 t2
    | ominus => sub v1 v2 t1
    | omulti => mul v1 v2
    | odiv => divs v1 v2
    | olshift => shl v1 v2
    | orshift => shr v1 v2
    | oand => bool_and v1 v2
    | oor => bool_or v1 v2
    | obitand => and v1 v2
    | obitor => or v1 v2
    | oeq => val_eq v1 v2
    | olt => cmp_val Clt v1 v2
  end.

Definition bop_int_type (t1 t2:type):=
  match t1,t2 with
    | Tint8, Tint8 => Some Tint8
    | Tint8, Tint16 => Some Tint16
    | Tint8, Tint32 => Some Tint32
    | Tint16, Tint8 => Some Tint16
    | Tint16, Tint16 => Some Tint16
    | Tint16, Tint32 => Some Tint32
    | Tint32, Tint8 => Some Tint32
    | Tint32, Tint16 => Some Tint32
    | Tint32, Tint32 => Some Tint32
    | _, _ =>None
  end.

Definition cmp_int_type (t1 t2:type):=
  match t1,t2 with
    | Tint8, Tint8 => Some Tint32
    | Tint8, Tint16 => Some Tint32
    | Tint8, Tint32 => Some Tint32
    | Tint16, Tint8 => Some Tint32
    | Tint16, Tint16 => Some Tint32
    | Tint16, Tint32 => Some Tint32
    | Tint32, Tint8 => Some Tint32
    | Tint32, Tint16 => Some Tint32
    | Tint32, Tint32 => Some Tint32
    | _, _ =>None
  end.

Definition bop_type (t1 t2:type) (op1:bop):=
  match op1 with
    | oplus => match t1 with
                 | Tptr t => match t2 with
                               | Tint8 => Some (Tptr t)
                               | Tint16 => Some (Tptr t)
                               | Tint32 => Some (Tptr t)
                               | _ => None
                             end
                 | Tint8 => match t2 with
                              |Tptr t => Some (Tptr t)
                              | _ => bop_int_type t1 t2
                            end
                 | Tint16 => match t2 with
                               |Tptr t => Some (Tptr t)
                               | _ => bop_int_type t1 t2
                             end
                 | Tint32 => match t2 with
                               |Tptr t => Some (Tptr t)
                               | _ => bop_int_type t1 t2
                             end
                 | _ => None
               end
    | ominus => match t1 with
                  | Tptr t => match t2 with
                                | Tint8 => Some (Tptr t)
                                | Tint16 => Some (Tptr t)
                                | Tint32 => Some (Tptr t)
                                | _ => None
                              end
                  | _ => bop_int_type t1 t2
                end
    | omulti => bop_int_type t1 t2
    | odiv => bop_int_type t1 t2
    | olshift => bop_int_type t1 t2
    | orshift => bop_int_type t1 t2
    | oand => bop_int_type t1 t2
    | oor => bop_int_type t1 t2
    | obitand => bop_int_type t1 t2
    | obitor => bop_int_type t1 t2
    | oeq => match t1 with
               | Tptr t => match t2 with
                             | Tptr t' => Some Tint32
                             | Tnull => Some Tint32
                             | Tcom_ptr x => Some Tint32
                             | _ => None
                           end
               | Tcom_ptr x => match t2 with
                                 | Tptr t' => Some Tint32
                                 | Tnull => Some Tint32
                                 | Tcom_ptr x' => Some Tint32
                                 | _ => None
                               end
               | Tnull => match t2 with
                            | Tptr t' => Some Tint32
                            | Tcom_ptr x => Some Tint32
                            | Tnull => Some Tint32
                            | _ => None
                          end
               | _ => cmp_int_type t1 t2
             end
    | olt =>cmp_int_type t1 t2
  end.

(********************************************************************)
(********************************************************************)

(**Encoding and decoding for values**)
Fixpoint encode_int (n: nat) (x: Z) {struct n}: list byte :=
  match n with
    | O => nil
    | S m => Byte.repr x :: encode_int m (x / 256)
  end.

Fixpoint decode_int (l: list byte): Z :=
  match l with
    | nil => 0
    | b :: l' => Byte.unsigned b + decode_int l' * 256
  end.

Lemma encode_int_length:
  forall sz x, length(encode_int sz x) = sz.
Proof.
  induction sz; simpl; intros. auto. decEq. auto.
Qed.

Definition inj_bytes (bl: list byte) : list memval :=
  List.map Byte bl.

Fixpoint proj_bytes (vl: list memval) : option (list byte) :=
  match vl with
    | nil => Some nil
    | Byte b :: vl' =>
      match proj_bytes vl' with None => None | Some bl => Some(b :: bl) end
    | _ => None
  end.

Lemma length_inj_bytes:
  forall bl, length (inj_bytes bl) = length bl.
Proof.
  intros. apply List.map_length.
Qed.

Lemma proj_inj_bytes:
  forall bl, proj_bytes (inj_bytes bl) = Some bl.
Proof.
  induction bl; simpl. auto. rewrite IHbl. auto.
Qed.

Lemma inj_proj_bytes:
  forall cl bl, proj_bytes cl = Some bl -> cl = inj_bytes bl.
Proof.
  induction cl; simpl; intros.
  inv H; auto.
  destruct a; try congruence. destruct (proj_bytes cl); inv H.
  simpl. decEq. auto.
Qed.

Fixpoint inj_pointer (n: nat) (b: block) (ofs: int32) {struct n}: list memval :=
  match n with
    | O => nil
    | S m => Pointer b ofs m :: inj_pointer m b ofs
  end.

Fixpoint check_pointer (n: nat) (b: block) (ofs: int32) (vl: list memval)
         {struct n} : bool :=
  match n, vl with
    | O, nil => true
    | S m, Pointer b' ofs' m' :: vl' =>
      peq b b' && Int.eq_dec ofs ofs' && beq_nat m m' && check_pointer m b ofs vl'
    | _, _ => false
  end.


Definition proj_pointer (vl: list memval) : val :=
  match vl with
    | Pointer b ofs n :: vl' =>
      if check_pointer 4%nat b ofs vl then Vptr (b, ofs) else Vundef
    | _ => Vundef
  end.

Definition encode_val (t: type) (v: val) : list memval :=
  match v, t with
  | Vint32  n, Tint8  => inj_bytes (encode_int 1%nat (Int.unsigned n))
  | Vint32  n, Tint16 => inj_bytes (encode_int 2%nat (Int.unsigned n))
  | Vint32  n, Tint32 => inj_bytes (encode_int 4%nat (Int.unsigned n))
  | Vptr (b, ofs), Tptr _ => inj_pointer 4%nat b (ofs)
  | Vptr (b, ofs), Tcom_ptr _ => inj_pointer 4%nat b (ofs)
  | Vnull, Tnull => list_repeat 4 MNull
  | Vnull, Tptr _ => list_repeat 4 MNull
  | Vnull, Tcom_ptr _ => list_repeat 4 MNull
  | _, _ => list_repeat (typelen t) Undef
  end.

Definition decode_val (t: type) (vl: list memval) : val :=
  match proj_bytes vl with
  | Some bl =>
      match t with
      | Tint8  => Vint32(Int.zero_ext 8 (Int.repr (decode_int bl)))
      | Tint16 => Vint32(Int.zero_ext 16 (Int.repr (decode_int bl)))
      | Tint32 => Vint32(Int.repr(decode_int bl))
      | _ => Vundef
      end
  | None =>
    match vl with
      | MNull :: MNull ::MNull :: MNull :: nil=> match t with
                                 | Tnull => Vnull
                                 | Tptr _ => Vnull
                                 | Tcom_ptr _ => Vnull
                                 | _ => Vundef
                               end
      | _ =>
        match t with
          | Tptr _ => proj_pointer vl
          | Tcom_ptr _ => proj_pointer vl
          | _ => Vundef
        end
    end
  end.


Lemma encode_val_length:
  forall t v, length(encode_val t v) = typelen t.
Proof.
  intros. destruct v; simpl; destruct t;
          try solve [ reflexivity
                    | apply length_list_repeat
                    | rewrite length_inj_bytes; apply encode_int_length ].
  destruct a. apply length_list_repeat.
  destruct a. apply length_list_repeat.
  destruct a. apply length_list_repeat.
  destruct a. apply length_list_repeat.
  destruct a. simpl. auto.
  destruct a. simpl. auto.
  destruct a. simpl. auto.
  destruct a. simpl. auto.
  apply length_list_repeat.
  destruct a. simpl. apply length_list_repeat.
Qed.


Fixpoint ftype (id : ident) (dls :  decllist) : option type :=
 match dls with
  | dnil => None
  | dcons id' t dls' => if Zeq_bool id id' then Some t else ftype id dls'
 end.

(* ** ac: Print addr. *)
(* ** ac: Print offset. *)

Module addrtypespec.
  Definition B:=prod addr type.
  Definition holder := ((1%positive,1%Z), Tint8).
End addrtypespec.

Module blocktypespec.
  Definition B:=prod block type.
  Definition holder := (1%positive, Tint8).
End blocktypespec.

Module EnvMod := MapLib.MapFun identspec blocktypespec.

Definition env := EnvMod.map.

Definition var := Z.

(* Definition envdel := fun (e:env) a => EnvMod.minus e (EnvMod.sig a (1%positive,Tint8)). *)

Instance EnvMap: PermMap ident (block * type) EnvMod.map :=
  {
    usePerm := EnvMod.usePerm;
    isRw := EnvMod.isRw;
    flip := EnvMod.flip;
    sameV := EnvMod.sameV;
    same := EnvMod.same;
    emp := EnvMod.emp;
    join := EnvMod.join;
    del := EnvMod.del;
    get := EnvMod.get;
    set := EnvMod.set;
    sig := EnvMod.sig;
    merge := EnvMod.merge;
    minus := EnvMod.minus
}.
Proof.
  exact EnvMod.map_dec_a.
  intros; tryfalse.
  intros; tryfalse.
  exact EnvMod.map_join_emp.
  exact EnvMod.map_join_pos.
  exact EnvMod.map_join_comm.
  exact EnvMod.map_join_assoc.
  exact EnvMod.map_join_cancel.
  exact EnvMod.map_join_deter.
  exact EnvMod.map_sv_ref.
  exact EnvMod.map_sv_comm.
  exact EnvMod.map_sv_assoc.
  exact EnvMod.map_perm_eql.
  exact EnvMod.map_flip_isRw.
  exact EnvMod.map_flip_sv.
  exact EnvMod.map_emp_get.
  exact EnvMod.map_eql.
  exact EnvMod.map_disjoint.
  exact EnvMod.map_get_unique.
  exact EnvMod.map_get_sig.
  exact EnvMod.map_get_sig'.
  exact EnvMod.map_get_set.
  exact EnvMod.map_get_set'.
  exact EnvMod.map_join_get_none.
  exact EnvMod.map_join_get_some.
  exact EnvMod.map_join_getp_some.
  exact EnvMod.map_set_emp.
  exact EnvMod.map_set_sig.
  exact EnvMod.map_join_set_none.
  exact EnvMod.map_join_set_perm.
  exact EnvMod.map_join_get_sig.
  exact EnvMod.map_join_get_sig_perm.
  exact EnvMod.map_merge_sem.
  intros; tryfalse.
  exact EnvMod.map_join_merge.
  exact EnvMod.map_merge_comm.
  intros; tryfalse.
  intros; tryfalse.
  exact EnvMod.map_minus_sem.
  intros; tryfalse.
  exact EnvMod.map_join_minus.
  exact EnvMod.map_del_sem.
Defined.

Definition alloc (x : var) (t : type) (e : env)
           (m : mem) (e' : env) (m':mem) : Prop :=
  exists b, fresh m b /\   m' = allocb m b 0 (typelen t) /\
            ~ indom e x /\ e' = set e x (b, t).

Definition  free (t : type) (b : block) (m : mem) := freeb m b 0 (typelen t).

Definition store (t : type) (m : mem) (l : addr) (v : val) : option mem :=
  match l with
      (b, i) => storebytes m l (encode_val t v)
  end.

Definition loadm (t : type) (m : mem) (l : addr) : option val :=
  match l with
      (b, i) => match loadbytes m l (typelen t) with
                  | Some bls => Some (decode_val t bls)
                  | _  => None
                end
  end.

Notation "V$ n" := (Vint32 (Int.repr n)) (at level 41):int_scope.
