Require Export List.
Require Export Maps.

Set Implicit Arguments.
Unset Strict Implicit.


(** * join axiom **)
(* Axiom map_join_emp: *)
(*   forall x, join x emp x. *)

(* ** ac: Check map_join_emp. *)
(* ** ac: Check @map_join_emp. *)
(* ** ac: Check join. *)
(* ** ac: Check @join. *)

Create HintDb jdb.

Module general.
  Ltac jauto := auto with jdb.
  Ltac jeauto := eauto with jdb.
  Ltac jeauto2 := eauto 2 with jdb.
End general.

Import general.

Hint Resolve @map_join_emp : jdb.
(** must add @, because type class may find instant automatically,
      then map_join_emp becomes a specific lemma ....
 **)

(* ** ac: Print HintDb jdb. *)
(* Axiom map_join_pos: *)
(*   forall x y, *)
(*     join x y emp -> *)
(*     x = emp /\ y = emp. *)

(* Axiom map_join_comm: *)
(*   forall x y z, *)
(*     join x y z -> *)
(*     join y x z. *)

(* Axiom map_join_assoc: *)
(*   forall a b mab c mabc, *)
(*     join a b mab -> *)
(*     join mab c mabc -> *)
(*     exists mbc, *)
(*       join a mbc mabc /\ *)
(*       join b c mbc. *)

(* Axiom map_join_cancel: *)
(*   forall a b b' c, *)
(*     join a b c -> *)
(*     join a b' c -> *)
(*     b = b'. *)

(* Axiom map_join_deter: *)
(*   forall a b c c', *)
(*     join a b c -> *)
(*     join a b c' -> *)
(*     c = c'. *)

Hint Immediate @map_join_comm : jdb.

Hint Resolve @map_join_cancel @map_join_deter : jdb.

(* ** ac: Check map_join_assoc. *)

Lemma map_join_assoc':
  forall {A B T:Type} {MC:PermMap A B T} a b mab c mabc,
    join a b mab ->
    join mab c mabc ->
    exists mbc,
      join a mbc mabc.
Proof.
  intros.
  remember (map_join_assoc H H0).
  destruct e as (mbc & F1 & F2).
  exists mbc.
  auto.
Qed.

(* ** ac: Check map_join_assoc'. *)
(* ** ac: Check @map_join_assoc'. *)
Lemma map_join_assoc'':
  forall {A B T:Type} {MC:PermMap A B T} a b mab c mabc,
    join a b mab ->
    join mab c mabc ->
    exists mbc,
      join mbc a mabc.
Proof.
  intros.
  remember (map_join_assoc H H0).
  destruct e as (mbc & F1 & F2).
  exists mbc.
  auto with jdb.
Qed.


Hint Resolve @map_join_assoc' @map_join_assoc'' : jdb.

(* ** ac: Print HintDb jdb. *)

Example test_1:
  forall {A B T:Type} {MC:PermMap A B T} a b mab c mabc,
    join a b mab ->
    join c mab mabc ->
    exists mbc,
      join mbc a mabc.
Proof.
  intros.
  jeauto.
Qed.

Lemma map_join_emp':
  forall {A B T:Type} {MC:PermMap A B T} x z,
    join x emp z ->
    x = z.
  intros; jeauto.
Qed.

Lemma map_join_emp'':
  forall {A B T:Type} {MC:PermMap A B T} x z,
    join emp x z ->
    x = z.
  intros; jeauto.
Qed.

Hint Resolve @map_join_emp' @map_join_emp'' : jdb.

Lemma map_join_pos':
  forall {A B T:Type} {MC:PermMap A B T} x y,
    join x y emp ->
    x = emp.
Proof.
  intros; apply map_join_pos in H; tauto.
Qed.

Lemma map_join_pos'':
  forall {A B T:Type} {MC:PermMap A B T} x y,
    join x y emp ->
    y = emp.
Proof.
  intros; apply map_join_pos in H; tauto.
Qed.

Hint Resolve @map_join_pos' @map_join_pos'' : jdb.

(** * Axiom : set , get and sig **)

(** ** get general **)
Hint Resolve @map_get_unique : jdb.
Hint Resolve @map_get_sig @map_get_sig' @map_get_set @map_get_set' : jdb.

Hint Resolve @map_dec_a : jdb.
Lemma map_get_sig'_l:
  forall {A B T:Type} {MC:PermMap A B T} t t' v v',
    get (sig t v) t' = Some v' ->
    t = t'.
Proof.
  intros.
  generalize (@map_dec_a _ _ _ _ t t'); intro.
  destruct H0.
  auto.
  assert (get (sig t v) t' = None) by jeauto.
  rewrite H in H0.
  inversion H0.
Qed.  

Lemma map_get_sig'_r:
  forall {A B T:Type} {MC:PermMap A B T} t t' v v',
    get (sig t v) t' = Some v' ->
    v = v'.
Proof.
  intros.
  generalize (@map_dec_a _ _ _ _ t t'); intro.
  destruct H0.
  subst.
  assert (get (sig t' v) t' = Some v) by jeauto.
  rewrite H0 in H.
  inversion H; subst; auto.
  assert (get (sig t v) t' = None) by jeauto.
  rewrite H in H0.
  inversion H0.
Qed.

Hint Resolve @map_get_sig'_l @map_get_sig'_r : jdb.

Hint Resolve @map_join_get_some @map_join_get_some @map_join_getp_some : jdb.
Hint Resolve @map_set_emp @map_set_sig @map_join_set_none map_join_set_perm : jdb.
Hint Resolve @map_join_get_sig @map_join_get_sig_perm : jdb.


(** * operator: merge **)
(* Parameter merge: T -> T -> T. *)

(* Axiom map_join_merge: *)
(*   (** the scope of exists is very large, using parenthesis **) *)
(*   forall x y, *)
(*     (exists z, join x y z) -> *)
(*     join x y (merge x y). *)

Hint Resolve @map_join_merge : jdb.

Lemma map_join_merge':
  forall {A B T:Type} {MC:PermMap A B T} x y z,
    join x y z ->
    z = merge x y.
Proof.
  intros.
  assert (join x y (merge x y)).
  apply map_join_merge.
  exists z; auto.
  eauto 2 with jdb.
Qed.

Hint Resolve @map_join_merge' : jdb.

(* Axiom map_merge_comm: *)
(*   forall x y, *)
(*     merge x y = merge y x. *)

(******************************* join_list *******************************)
Inductive join_list {A B T:Type} {MC:PermMap A B T}: list T -> T -> Prop :=
| jl_nil: join_list nil emp
| jl_cons:
    forall h ls z' z ,
      join_list ls z' ->
      join h z' z ->
      join_list (h::ls) z.

Hint Resolve @jl_nil @jl_cons : jdb.

Lemma jl_ref:
  forall {A B T:Type} {MC:PermMap A B T} x,
    join_list (x::nil) x.
Proof.
  intros.
  eapply jl_cons with (z':=emp); jauto.
Qed.

Hint Resolve @jl_ref : jdb.

Lemma jl_join_to_jl:
  forall {A B T:Type} {MC:PermMap A B T} x y z,
    join x y z ->
    join_list (x::y::nil) z.
Proof.
  intros; jeauto.
Qed.

Hint Resolve @jl_join_to_jl : jdb.

Lemma jl_elim_nil:
  forall {A B T:Type} {MC:PermMap A B T} x lx',
    join_list (emp :: lx') x ->
    join_list lx' x.
Proof.
  intros.
  inversion H; subst; clear H.
  assert (z' = x) by jeauto; subst.
  auto.
Qed.

Hint Resolve @jl_elim_nil : jdb.

Lemma jl_emp:
  forall {A B T:Type} {MC:PermMap A B T},
    join_list nil emp.
Proof.
  jauto.
Qed.

Hint Resolve @jl_emp : jdb.

Lemma jl_emp':
  forall {A B T:Type} {MC:PermMap A B T} x,
    join_list nil x -> x = emp.
Proof.
  intros.
  inversion H.
  jauto.
Qed.

Hint Resolve @jl_emp' : jdb.

(** * main lemma: jl_sub **)
(** ** TODO: simpl **)
Lemma jl_sub:
  forall {A B T:Type} {MC:PermMap A B T} x lx lz',
    join_list lx x ->
    forall z,
      join_list (x::lz') z ->
      join_list (lx ++ lz') z.
Proof.
  induction 1.
  (** trivial start **)
  intros.
  simpl.
  apply jl_elim_nil in H.
  auto.
  (** complex induction **)
  rename ls into lx'.
  rename z' into x'.
  rename h into hx.
  rename H into Hjl_x.
  rename H0 into Hjop_x.
  rename z into x.
  intros z Hjl_z.
  simpl.
  (** generate some facts **)
  inversion Hjl_z.
  subst.
  rename H1 into Hjl_z'.
  rename H3 into Hjop_z.
  remember (map_join_assoc Hjop_x Hjop_z).
  clear Heqe.
  rename e into Hmz.
  destruct Hmz as (mz & Hjop_mz_new & Hjop_mz).
  (** deal with goal **)
  eapply jl_cons.
  eapply IHjoin_list.
  eapply jl_cons.
  eauto.
  instantiate (1:=mz).
  eauto.
  auto.
Qed.


(** * main lemma: jl_deter **)
Lemma jl_deter:
  forall {A B T:Type} {MC:PermMap A B T} l x x',
    join_list l x ->
    join_list l x' ->
    x = x'.
Proof.
  induction l.
  intros.
  assert (x = emp) by jeauto.
  assert (x' = emp) by jeauto.
  subst.
  auto.

  intros x x' Hjl_x Hjl_x'.
  inversion Hjl_x.
  subst.
  rename z' into nx.
  inversion Hjl_x'.
  subst.
  rename z' into nx'.
  clear Hjl_x Hjl_x'.
  rename H1 into Hjl_nx.
  rename H2 into Hjl_nx'.
  rename H3 into Hjop_x.
  rename H5 into Hjop_x'.
  assert (nx = nx') by jeauto2.
  subst.
  jeauto2.
Qed.

Hint Resolve @jl_deter : jdb.

(** * main lemma: jl_split **)
Lemma jl_split:
  forall {A B T:Type} {MC:PermMap A B T} l1 l2 z,
    join_list (l1 ++ l2) z ->
    exists x y,
      join_list l1 x /\
      join_list l2 y /\
      join x y z.
Proof.
  induction l1; jeauto.
  intros l2 z Hjl_z.
  simpl in Hjl_z.
  inversion Hjl_z; subst; clear Hjl_z.
  apply IHl1 in H1.
  destruct H1 as (x' & y & Hjl_x' & Hjl_y & Hjop_z').
  clear IHl1.
  rename H3 into Hjop_z.
  apply map_join_comm in Hjop_z'.
  apply map_join_comm in Hjop_z.
  remember (map_join_assoc Hjop_z' Hjop_z).
  clear Heqe.
  destruct e as (x & Hjop_z1 & Hjop_x).
  exists x.
  exists y.
  split; jeauto.
Qed.

Ltac join_assoc_tac H1 H2 :=
  let f := fresh "tac_H" in
  let f1 := fresh "tac_Hjop1" in
  let f2 := fresh "tac_Hjop2" in
  let mbc := fresh "mbc" in
  first [ remember (map_join_assoc H1 H2) as f
        | apply map_join_comm in H2;
          remember (map_join_assoc H1 H2) as f];
  destruct f as (mbc & f1 & f2).

(** * main lemma: jl_merge_op **)
Lemma jl_merge_op:
  forall {A B T:Type} {MC:PermMap A B T} l1 l2 x y z,
    join_list l1 x ->
    join_list l2 y ->
    join x y z ->
    join_list (l1 ++ l2) z.
Proof.
  induction l1.
  (** base case **)
  intros.
  simpl.
  assert (x = emp) by jauto.
  subst.
  assert (y = z) by jeauto2.
  subst.
  auto.
  (** induction case **)
  intros.
  simpl.
  inversion H.
  subst.
  clear H.
  rename H4 into Hjl_l1.
  rename H6 into Hjl_a_l1.
  rename z' into ml1.
  rename x into ma_l1.
  join_assoc_tac Hjl_a_l1 H1; jeauto.
Qed.

Hint Resolve @jl_merge_op : jdb.

Lemma jl_swap:
  forall {A B T:Type} {MC:PermMap A B T} l1 l2 z,
    join_list (l1 ++ l2) z ->
    join_list (l2 ++ l1) z.
Proof.
  intros.
  apply jl_split in H.
  destruct H as (x & y & Hjl_x & Hjl_y & Hjop_z).
  jeauto.
Qed.

(** * main lemma: jl_lift **)
Lemma jl_lift:
  forall {A B T:Type} {MC:PermMap A B T} h l1 l2 z,
    join_list (l1 ++ h :: l2) z ->
    join_list (h :: l1 ++ l2) z.
Proof.
  intros.
  apply jl_swap in H.
  simpl in H.
  inversion H.
  clear H.
  subst.
  apply jl_swap in H2.
  jeauto.
Qed.

Lemma jl_ref_eql:
  forall {A B T:Type} {MC:PermMap A B T} x y,
    join_list (x :: nil) y ->
    x = y.
Proof.
  intros.
  assert (join_list (x :: nil) x) by jauto.
  jeauto2.
Qed.

Hint Resolve @jl_ref_eql : jdb.

Lemma jl_list_to_op:
  forall {A B T:Type} {MC:PermMap A B T} x y z,
    join_list (x :: y :: nil) z ->
    join x y z.
Proof.
  intros.
  inversion H.
  subst.
  assert (y = z') by jeauto.
  subst z'.
  auto.
Qed.

Hint Resolve @jl_list_to_op : jdb.

Lemma jl_intro_op:
  forall {A B T:Type} {MC:PermMap A B T} l1 l2 x y z,
    join_list l1 x ->
    join_list l2 y ->
    join_list (l1 ++ l2) z ->
    join x y z.
Proof.
  intros.
  apply jl_split in H1.
  destruct H1 as (x0 & y0 & H2 & H3 & H4).
  assert (x = x0) by jeauto2.
  assert (y = y0) by jeauto2.
  subst x0 y0.
  auto.
Qed.

Hint Resolve @jl_intro_op : jdb.

Lemma jl_intro_ex_jop:
  forall {A B T:Type} {MC:PermMap A B T} m l1 l2 l' x y,
    join_list (l1 ++ (l2 ++ l')) m ->
    join_list l1 x ->
    join_list l2 y ->
    (exists z, join x y z).
Proof.
  intros.
  rewrite app_assoc in H.
  apply jl_split in H.
  destruct H as (x0 & y0 & F1 & F2 & F3).
  exists x0.
  jeauto.
Qed.

Hint Resolve @jl_intro_ex_jop.

Lemma jl_intro_merge:
  forall {A B T:Type} {MC:PermMap A B T} m l1 l2 l' x y,
    join_list (l1 ++ (l2 ++ l')) m ->
    join_list l1 x ->
    join_list l2 y ->
    join x y (merge x y).
Proof.
  intros.
  apply map_join_merge.
  jeauto.
Qed.

Lemma jl_intro_jl_of_merge:
  forall {A B T:Type} {MC:PermMap A B T} l1 l2 x y,
    join_list l1 x ->
    join_list l2 y ->
    join x y (merge x y) ->
    join_list (l1 ++ l2) (merge x y).
Proof.
  intros.
  jeauto.
Qed.

Fixpoint merge_list {A B T:Type} {MC:PermMap A B T} (l: list T) : T :=
  match l with
    | x :: l' =>
      merge x (merge_list l')
    | nil => emp
  end.

Lemma jl_merge_list:
  (** wonderful lemma !!! **)
  forall {A B T:Type} {MC:PermMap A B T} l m,
    join_list l m ->
    join_list l (merge_list l).
Proof.
  induction 1.
  jeauto.
  simpl.
  eapply jl_cons.
  exact IHjoin_list.
  assert (merge_list ls = z') by jeauto.
  rewrite H1 in *.
  clear H1.
  jeauto.
Qed.

Hint Resolve @jl_merge_list : jdb.

Lemma jl_intro_merge_list_sub:
  forall {A B T:Type} {MC:PermMap A B T} lx ly m,
    join_list (lx ++ ly) m ->
    join_list lx (merge_list lx).
Proof.
  intros.
  apply jl_split in H.
  destruct H as (? & ? & ? & ? & ?).
  jeauto.
Qed.

Lemma jl_merge_list_merge:
  forall {A B T:Type} {MC:PermMap A B T} l1 l2 x y,
    join_list l1 x ->
    join_list l2 y ->
    join x y (merge x y) ->
    join_list (l1 ++ l2) (merge_list (l1 ++ l2)).
Proof.
  intros.
  assert (join_list (l1 ++ l2) (merge x y)) by jeauto.
  jeauto.
Qed.

Lemma jl_merge_list_subtract:
  forall {A B T:Type} {MC:PermMap A B T} l1 x,
    join_list l1 x ->
    forall l2 z,
      join_list (l1 ++ l2) z ->
      join_list l2 (merge_list l2).
Proof.
  (* ** ac: Check jl_split. *)
  intros.
  apply jl_split in H0.
  destruct H0 as (x0 & y & F1 & F2 & F3).
  jeauto.
Qed.

Lemma jl_merge_emp:
  forall {A B T:Type} {MC:PermMap A B T} x,
    merge x emp = x.
Proof.
  intros.
  apply eq_sym.
  apply map_join_merge'.
  jeauto.
Qed.

Lemma jl_merge_emp':
  forall {A B T:Type} {MC:PermMap A B T} x,
    merge emp x = x.
Proof.
  intros.
  apply eq_sym.
  apply map_join_merge'.
  jeauto.
Qed.

(***************************** list tactics *****************************)
Require Import NPeano.

Ltac slice l n m :=
  (** l: list ?T (?T can be everything), n m: nat **)
  (** get slice [n:m] of list l, count from 0
        for example, slice (1::2::3::4::5::nil) 0 2 = (1::2::nil)
        so be careful that m is exclusive !!!
   **)
  match type of l with
    | list ?T =>
      let rec slice' l n m :=
          match m with
            | O => constr:(@nil T)
            | S ?m' =>
              match l with
                | nil => constr:(@nil T)
                | ?h :: ?l' =>
                  match n with
                    | O =>
                      let l1 := slice' l' n m' in
                      constr:(h :: l1)
                    | S ?n' =>
                      let l1 := slice' l' n' m' in
                      constr:(l1)
                  end
              end
          end in
      slice' l n m
  end.

Goal forall {A B T:Type} {MC:PermMap A B T} (x y z: T) (t:A) (v:B), False.
intros.
let y := slice ((sig t v)::x::y::z::nil) 0 2 in
pose y.
Abort.

Ltac length l :=
  (** l: list A **)
  (** return the length of list l **)
  match l with
    | nil => constr:(O)
    | _ :: ?ls =>
      let n := length ls in
      constr:(S n)
  end.

Goal forall {A B T:Type} {MC:PermMap A B T} (x y z:T), False.
intros.
let y := length (x::y::z::nil) in
pose y.
Abort.

Ltac nth l n :=
  (** l: list ?T, n: nat **)
  (** nth element of list l, number from 0
        for example, nth_general (x::y::nil) 0 = x **)
  let l' := slice l n (S n) in
  match l' with
    | ?h :: nil => h
  end.

Goal forall {A B T:Type} {MC:PermMap A B T} (x y z:T), False.
intros.
let y := nth (x::y::z::nil) 1 in
pose y.
Abort.

Ltac map T f ls :=
  (** T: Type, f: A -> T(but f is a tactic function), ls: list A **)
  (** classical functional programming function: map **)
  let rec map' ls :=
      match ls with
        | nil => constr:(@nil T)
        | ?x :: ?ls' =>
          let x' := f x in
          let ls'' := map' ls' in
          constr:(x'::ls'')
      end in
  map' ls.


(** PS: how to use condition in tactic? see below ~
    Ltac find l x :=
      match l with
        | ?h :: ?ls =>
          let cond1 := constr:(eq_refl x: x = h) in (** if x = h **)
            constr:(O)
        | ?h :: ?ls =>
          let n := find ls x in (** if x <> h **)
            constr:(S n)
      end. **)

Ltac find l x :=
  (** l: list A, x: A **)
  (** find the subscript of x in l
        for example l=(m1::m2::nil) x=m2, then (find l x) = 1 **)
  match l with
    | x :: ?ls =>
      constr:(O)
    | _ :: ?ls =>
      let n := find ls x in
      constr:(S n)
  end.

Goal forall {A B T:Type} {MC:PermMap A B T} (x1 x2 x3 x4:T) (t:A) (v:B), False.
intros.
let y := find (x2::(sig t v)::x3::x4::nil) (sig t v) in
pose y.
let y := find (x2::x1::(sig t v)::x3::x4::nil) (sig t v) in
pose y.
Abort.

Ltac find_all l lx :=
  (** l: list A, lx: list A **)
  (** find all element of lx in l, return a [list nat] **)
  map nat ltac:(fun x => find l x) lx.

Goal forall {A B T:Type} {MC:PermMap A B T} (x1 x2 x3 x4 x5:T) t v, join (sig t v) x1 x2.
intros.
let ls := find_all (x1::x2::(sig t v)::x4::nil) ((sig t v)::x4::nil) in
pose ls.
Abort.

Ltac lifts_order ln :=
  (** ln: list nat **)
  (** if we want transform a list to let the (2th, 3th, 4th) be the first three element, we then perform 4th-to-head, then the 4th of new list to head, then the 4th of new list to head, so the lift number list is (4th, 4th, 4th).
        this tactic perform this transform **)
  let rec lifts_order_inc b l :=
      (** forall x in l, if x < b, then inc x **)
      match l with
        | nil => constr:(@nil nat)
        | ?h :: ?l' =>
          let l0 := lifts_order_inc b l' in
          let x := constr:(Nat.ltb h b) in
          match (eval compute in x) with
            | true => constr:((S h) :: l0)(** if h < b, then inc h **)
            | false => constr:(h :: l0)
          end
      end in
  let rec lifts_order' l :=
      match l with
        | nil => constr:(@nil nat)
        | ?h :: ?l' =>
          let l0 := lifts_order_inc h l' in
          let l1 := lifts_order' l0 in
          constr:(h :: l1)
      end in
  let l1 := constr:(rev ln) in
  let l2 := (eval compute in l1) in
  lifts_order' l2.

Goal forall {A B T:Type} {MC:PermMap A B T} (x:list nat), x = x.
intros.
let y := lifts_order (2::3::nil) in
assert (x = y).
 (** test the result of lifts_trans_list **)
Abort.

Ltac slice_tail l n :=
  (** tail of l from n, inclusive **)
  let len := length l in
  slice l n (S len).

Ltac lift_nat l n :=
  (** l: list T, n: nat **)
  (** return a list, which equal to lift nth element of l to the head **)
  let l1 := slice l 0 n in
  let x := nth l n in
  let l2 := slice_tail l (S n) in
  let l' := constr:(x :: l1 ++ l2) in
  let l'' := (eval simpl in l') in
  constr:(l'').

Goal forall {A B T:Type} {MC:PermMap A B T} (x y z:T), False.
intros.
let n := lift_nat (x::y::z::nil) 2 in
pose n.
let n := slice_tail (x::y::z::nil) 1 in
pose n.
Abort.

Ltac lift l x :=
  (** l: list T, x: T **)
  let n := find l x in
  lift_nat l n.

Goal forall {A B T:Type} {MC:PermMap A B T} (x y z:T), False.
intros.
let n := lift (x::y::z::nil) z in
pose n.
Abort.

(* ** ac: Check rev. *)
(**
     useing constr:(rev) in TypeClass will cause some problem, see below example.
     eval compute unfold something in TypeClass **)

Goal forall {A B T:Type} {MC:PermMap A B T} (x1 x2 x3 x4 x5:T) t v,
    join (sig t v) x1 x2 ->
    (sig t v :: nil) ++ (x2 :: nil) = (sig t v :: x2 :: nil) ->
    (sig t v :: nil) ++ (x1 :: nil) = (sig t v :: x1 :: nil).
intros.
simpl in H0.
let l1 := constr:(rev (x1::(sig t v)::nil)) in
let l2 := (eval simpl in l1) in
pose l2.
let l1 := constr:(rev (x1::(sig t v)::nil)) in
let l2 := (eval simpl in l1) in
pose l2.
 (** aaaaaaaaaa!!!!!! simpl will unfold sig to sigx ... How to fix it? **)
(**
     β (reduction of functional application),
     δ (unfolding of transparent constants, see 6.11.2),
     ι (reduction of pattern-matching over a constructed term, and unfolding of fix and cofix expressions)
     ζ (contraction of local definitions)
     the flag are either beta, delta, iota or zeta
 **)
let l1 := constr:(rev (x1::(sig t v)::nil)) in
let l2 := (eval compute -[sig] in l1) in
pose l2.
let l1 := constr:(rev (x1::(merge x2 x3)::nil)) in
let l2 := (eval compute -[sig] in l1) in
pose l2.

let l1 := constr:(rev (x1::(merge x2 x3)::nil)) in
let l2 := (eval compute -[merge] in l1) in
pose l2.

let l1 := constr:(rev (x1::(merge x2 x3)::(sig t v)::nil)) in
let l2 := (eval compute -[sig get set join emp merge] in l1) in
pose l2.
(* simpl. *)
simpl.
let l1 := constr:(rev (x1::(merge x2 x3)::(sig t v)::nil)) in
let l2 := eval simpl in l1 in
    pose l2.
Abort.

Ltac lifts l lx :=
  (** l: list T, lx: list T **)
  (** lift all the ident in lx, among l **)
  let rec lifts' l lx :=
      match lx with
        | ?x :: ?lx' =>
          let l' := lift l x in
          lifts' l' lx'
        | nil => constr:(l)
      end in
  let lx' := constr:(rev lx) in
  let lx'' := (eval simpl in lx') in
  lifts' l lx''.

Goal forall {A B T:Type} {MC:PermMap A B T} (x1 x2 x3 x4 x5:T) t v, join (sig t v) x1 x2.
intros.
let l1 := constr:(rev (x1::(sig t v)::nil)) in
let n := lifts (x1::x2::x3::(sig t v)::nil) (x2::x1::x3::nil) in
pose n.
let n := lifts (x1::x2::(sig t v)::x3::x4::x5::nil) (x2::(sig t v)::x3::nil) in
pose n.
Abort.

Ltac extract l lx :=
  (** l: list T, lx: list T **)
  (** perform [lifts l lx], and get the tail part of l out of lx **)
  let l' := lifts l lx in
  let n := length lx in
  let l'' := slice_tail l' n in
  constr:(l'').

Goal forall {A B T:Type} {MC:PermMap A B T} (x1 x2 x3 x4 x5:T), False.
intros.
let n := extract (x1::x2::x3::x4::x5::nil) (x3::x1::x2::nil) in
pose n.
Abort.

Ltac truncate l lx :=
  (** l: list ?T, lx: list ?T **)
  (** n = length lx, then get (slice_tail l n) **)
  (** this should be put in list tactics **)
  let n := length lx in
  slice_tail l n.

(* ** ac: Check Nat.ltb. *)
Ltac subp_list l1 l2 :=
  (** l1 l2: list ?T **)
  (** predicate whether l2 if the sub set of l1, return tactic value **)
  let l' := extract l1 l2  in
  (** not fail, means l2 is subset of l1 **)
  idtac.

Goal forall {A B T:Type} {MC:PermMap A B T} (x1 x2 x3 x4 x5:T), False.
intros.
subp_list (x1::x2::x3::nil) (x1::x3::nil).
subp_list (x1::x2::x3::nil) (x1::x3::x2::nil).
let n := extract (x1::x2::x3::x4::x5::nil) (x3::x1::x2::nil) in
pose n.
Abort.

Ltac same_list l1 l2 :=
  (** l1 l2: list ?T **)
  (** predicate of that l1 and l2 is the same set, return true or false **)
  (** this should be move to list tactic part **)
  let n1 := length l1 in
  let n2 := length l2 in
  let dummy1 := constr:(eq_refl n1: n1 = n2) in (** n1 = n2 ? **)
  let l' := extract l1 l2 in (** l' = nil if l1 and l2 are same set **)
  match l' with
    | nil => constr:(true)
    | _ => constr:(false)
  end.

Ltac same_list' l1 l2 :=
  (** the same as same_list, but return tactic. **)
  let b := same_list l1 l2 in
  match b with
    | true => idtac
    | false => fail
  end.

Goal forall {A B T:Type} {MC:PermMap A B T} (x y z i:T), join_list (x::y::z::nil) i -> False.
intros.
let n := same_list (x::y::z::nil) (y::z::x::nil) in pose n.
let n := same_list (@nil T) (@nil T) in pose n.
Abort.

(** * tactic about Hypothesis and goals **)

Ltac liftH_nat H n :=
  (** H: hypo ident, n: nat **)
  (** H must has type [join_list ?l ?ml], then transform H to let nth element of l at the head of l **)
  match type of H with
    | join_list ?l ?ml =>
      let l1 := slice l 0 n in
      let l2 := slice_tail l (S n) in
      let x := nth l n in
      let tmp := fresh in
      assert (tmp: l = (l1 ++ x :: l2)) by auto;
      rewrite tmp in H;
      clear tmp;
      apply jl_lift in H;
      simpl in H
  end.

Goal forall {A B T:Type} {MC:PermMap A B T} (x y z ml:T) t v,
    join_list (x::y::z::(sig t v)::nil) ml -> False.
intros.
liftH_nat H 3.
Abort.

Goal forall {A B T:Type} {MC:PermMap A B T} (a1 a2 x1' x2' x1 x2 x3 x4 x12 x34 x1234:T) (x:A) (v:B),
    join_list (x1::x2::(sig x v)::nil) x12 ->
    join_list (a1::a2::nil) x2' ->
    join_list (x1'::x2'::nil) x3 ->
    join_list (x12::x3::x4::nil) x1234 -> False.
intros.
liftH_nat H2 1.
Abort.

Ltac liftH H x :=
  (** H: hypo ident, x: T **)
  (** similar to liftH_nat, except x is the ident, not number **)
  match type of H with
    | join_list ?l ?ml =>
      let n := find l x in
      liftH_nat H n
  end.

Goal forall {A B T:Type} {MC:PermMap A B T} (x y z ml:T) t v,
    join_list (x::y::z::(sig t v)::nil) ml -> False.
intros.
liftH H (sig t v).
liftH H y.
Abort.

Ltac liftsH H lx :=
  (** H: hypo ident, lx: list T **)
  (** lifts all element of lx in H **)
  let rec liftsH' lx :=
      match lx with
        | ?x :: ?lx' =>
          liftH H x;
          liftsH' lx'
        | nil => idtac
      end in
  let lx' := constr:(rev lx) in
  let lx'' := (eval simpl in lx') in
  liftsH' lx''.

Goal forall {A B T:Type} {MC:PermMap A B T} (x1 x2 x3 x4 x5 ml:T) t v,
    usePerm = false ->
    join_list (x1::x2::x3::x4::x5::(sig t v)::nil) ml -> False.
intros.
liftsH H0 ((sig t v) :: nil).
liftsH H0 (x2::x4::x1::nil).
Abort.

Ltac in_hyp l :=
  (** l : list T **)
  (** predicate of the existence [H: join_list l _ ], return true/false **)
  match goal with
    | H : join_list ?ll ?x |- _ =>
      same_list l ll
    | _ => constr:(false)
  end.

Ltac in_hyp' l :=
  (** the same as in_hyp, but return tactic. **)
  let b := in_hyp l in
  match b with
    | true => idtac
    | false => fail
  end.

Goal forall {A B T:Type} {MC:PermMap A B T} (x y z i:T),
    join_list (x::y::z::nil) i ->
    join_list (x::y::nil) z ->
    join_list nil emp -> False.
intros.
let n := in_hyp (x::nil) in pose n.
let n := in_hyp (@nil T) in pose n.
in_hyp' (x::y::nil).
Abort.

Ltac search_x x :=
  (** x: T **)
  (** find the hypo [H: join_list ?lx x], return H if find, else fail **)
  match goal with
    | H: join_list ?lx x |- _ =>
      constr:(H)
  end.

Goal forall {A B T:Type} {MC:PermMap A B T} (x1 x2 x3 x4 x5:T) t v,
    join_list (x1::x2::nil) x3 ->
    get x1 t = Some v -> False.
intros.
let n:= search_x x3 in pose n.
Abort.

Ltac in_hyp_x x :=
  (** x: T **)
  (** whether [join_list lx x] is in hypo, return true/false **)
  match goal with
    | H: join_list ?lx x |- _ =>
      constr:(true)
    | |- _ => constr:(false)
  end.

Ltac in_hyp_x' x :=
  (** x: T **)
  (** whether [join_list lx x] is in hypo, return tactic value **)
  match goal with
    | H: join_list ?lx x |- _ => idtac
  end.

Goal forall {A B T:Type} {MC:PermMap A B T} (x1 x2 x3 x4 x5:T) t v,
    join_list (x1::x2::nil) x3 ->
    join_list nil emp ->
    get x1 t = Some v -> False.
intros.
let n:= search_x x3 in pose n.
let n:= in_hyp_x emp in pose n.
Abort.

Definition done (T : Type) (x : T) :=
  (** I learn this tricky method in CPDT. *)
  (** While we proof the goal, hypo place can be used to keep accumulated information.
        This function acts as the sign of such information.
   **)
  True.
(* ** ac: Check done. *)
(* ** ac: Check done (1 = 1). *)

Goal forall {A B T:Type} {MC:PermMap A B T} (x1 x2 x3 y z : T),
    False.
intros.
assert (done (x1 = x2)) by constructor.
assert (done x1) by constructor.
Abort.

Ltac place_done T :=
  (** T: Type **)
  (** intro [done T] **)
  assert (done T) by constructor.

Ltac check_done T :=
  (** T: Type **)
  (** if [done T] is in context, return true, else return false **)
  match goal with
    | H: done T |- _ =>
      constr:(true)
    | _ => constr:(false)
  end.

Ltac check_done' T :=
  (** T: Type **)
  (** if [done T] is in context, succeed, else fail **)
  let b := check_done T in
  match b with
    | true => idtac
    | false => fail
  end.

Ltac clear_done :=
  (** clear all form [done _] in context **)
  repeat match goal with
           | H: done _ |- _ =>
             clear H
         end.

Goal forall {A B T:Type} {MC:PermMap A B T} (x1 x2 x3 y z : T),
    False.
intros.
place_done (x1 = x2).
place_done x1.
place_done A.
(* ** ac: check_done' A. *)
let x := check_done (x1=x2) in pose x.
clear_done.
Abort.

Lemma jl_split_left:
  forall {A B T:Type} {MC:PermMap A B T} l1 l2 z,
    join_list (l1 ++ l2) z ->
    exists x,
      join_list l1 x.
Proof.
  intros.
  apply jl_split in H.
  destruct H as (x & y & H1 & H2 & H3).
  eauto.
Qed.


Lemma map_join_get_none':
  forall {A B T:Type} {MC:PermMap A B T} x y z t,
    join x y z ->
    get y t = None ->
    get z t = get x t.
Proof.
  intros.
  apply map_join_comm in H.
  eapply map_join_get_none; eauto.
Qed.  

Hint Resolve map_join_get_none' : jdb.

Lemma map_join_get_no_perm:
  forall {A B T:Type} {MC:PermMap A B T} x y z t v,
    usePerm = false ->
    join x y z ->
    get x t = Some v ->
    get y t = None /\ get z t = Some v.
Proof.
  intros.
  destruct (get y t) eqn:F1; destruct (get z t) eqn:F2.
  assert (Hf: False) by jeauto2; inversion Hf.
  assert (Hf: False) by jeauto2; inversion Hf.
  assert (Hf: get z t = get x t) by jeauto2.
  rewrite H1 in *.
  rewrite F2 in *.
  inversion Hf.
  subst.
  auto.
  assert (Hf: get z t = get x t) by jeauto2.
  rewrite H1 in *.
  rewrite F2 in *.
  inversion Hf.
Qed.

Lemma map_join_get_no_perm1:
  forall {A B T:Type} {MC:PermMap A B T} x y z t v,
    usePerm = false ->
    join x y z ->
    get x t = Some v ->
    get y t = None.
Proof.
  intros.
  generalize (@map_join_get_no_perm _ _ _ _ _ _ _ _ _ H H0 H1); intro. 
  destruct H2; auto.
Qed.  

Lemma map_join_get_no_perm2:
  forall {A B T:Type} {MC:PermMap A B T} x y z t v,
    usePerm = false ->
    join x y z ->
    get x t = Some v ->
    get z t = Some v.
Proof.
  intros.
  generalize (@map_join_get_no_perm _ _ _ _ _ _ _ _ _ H H0 H1); intro. 
  destruct H2; auto.
Qed.  

Hint Resolve @map_join_get_no_perm1 @map_join_get_no_perm2 : jdb.

Lemma jl_intro_set_noPerm:
  forall {A B T:Type} {MC:PermMap A B T} lx' x t v,
    usePerm = false ->
    join_list ((sig t v)::lx') x ->
    forall v', join_list ((sig t v')::lx') (set x t v').
Proof.
  intros.
  inversion H0; clear H0; subst.
  eapply jl_cons.
  jeauto.
  erewrite <- map_set_sig.
  assert (get z' t = None) by jeauto2.
  jeauto2.
Qed.

Lemma jl_intro_get_noPerm:
  forall {A B T:Type} {MC:PermMap A B T} lx' x t v,
    usePerm = false ->
    join_list ((sig t v)::lx') x ->
    get x t = Some v.
Proof.
  intros.
  inversion H0; clear H0; subst.
  jeauto2.
Qed.

Ltac simpl_map :=
  match goal with
    | H : exists _, _ |- _ => destruct H; simpl_map
    | H : (_ /\ _) |- _ => destruct H; simpl_map
    (*
    | |- _ /\ _ => split; simpljoin'
      | H : emposabst _ |- _ =>
      unfold emposabst in H; subst; mytac_1
    *) 
    | H :  join emp _ _ |- _ =>
      apply  map_join_emp' in H; subst;simpl_map

    | H :  join _ emp _ |- _ =>
      apply  map_join_comm in H; apply map_join_emp' in H; subst;simpl_map

    | |-  join emp _ _ => 
      apply  map_join_comm;apply  map_join_emp;simpl_map
    | |-  join _ emp _ =>
       apply  map_join_emp; simpl_map

    | H : join ?a ?b ?ab |- join ?b ?a ?ab =>
      apply map_join_comm; auto

    | H : (_, _) = (_, _) |- _ => inversion H; clear H; simpl_map
    | H : ?x = ?x |- _ => clear H; simpl_map
    | |- ?x = ?x => reflexivity

    | |-  join _ ?a ?a => apply  map_join_comm;simpl_map
    | |-  join ?a _ ?a => apply  map_join_emp;simpl_map

    | |- emp = _ => reflexivity;simpl_map
    | |- _ = emp => reflexivity; simpl_map
(*    | |- emposabst _ => unfold emposabst; reflexivity; mytac_1
    | |- empabst = _ => reflexivity; mytac_1
    | |- _ = empabst => reflexivity; mytac_1

    | |- empisr = _ => reflexivity; mytac_1
    | |- _ = empisr => reflexivity; mytac_1
 *)
    | H : True |- _ => clear H; simpl_map
    | |- True => auto
    | _ => try (progress subst; simpl_map)
  end.

Ltac simpljoin := repeat progress simpl_map.

Tactic Notation "simp" "join" := simpljoin.
