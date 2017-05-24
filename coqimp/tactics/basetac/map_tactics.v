(** Comment:
 **   main tactic:
 **       In most situation, you only need tactic [geat]. 
 **       cook: deal with context, prepare to solve
 **       jeat: [join] goal solver, but need using [cook] for prepare.
 **       heat: clear context (destruct [and] and [exist] hypothesis)
 **       geat: general eat, combine all above three primitive, you can use it everywhere.
 **)

Require Export join_general.

Set Implicit Arguments.
Unset Strict Implicit.

Module old.
(******************************************************************************)
(** * Wash: extract information in context **)

Create HintDb jdb0.
  
Ltac jauto := auto with jdb jdb0.
Ltac jeauto := eauto with jdb jdb0.
Ltac jeauto2 := eauto 2 with jdb jdb0.
   
Ltac wash_join :=
  (** chang [H: join x y z] to [H: join_list (x::y::nil) z] **)
  match goal with
    | H: join ?x ?y ?z |- _ =>
      apply jl_join_to_jl in H
  end.

Ltac wash_joins :=
  repeat wash_join.

(* Ltac wash_get := *)
(*   (** change [H: get x t = Some v] to [H: exists x', join (sig t v) x' x], and destruct it, *)
 (*       then transform it to [H: join_list ((sig t v)::x'::nil) x].  *)
 (*       Attention: *)
 (*         To release the pain, I want to clear all redundant or malicious form about get. *)
 (*         This wash of get will perform on `Choping' process. *)
 (*    **) *)
(*   match goal with *)
(*     | H: get ?x ?t = Some ?v |- _ => *)
(*       apply map_get_join_sig in H; *)
(*       destruct H; *)

(*   end. *)

(* ** ac: Check map_join_emp'. *)
(* ** ac: Check map_join_emp''. *)
(* ** ac: Check map_join_pos. *)

Ltac wash_emp :=
  (** deal with [join x y z], which there is emp in (x, y, z).
      extract subtle equation about x y z, and then do subst. 
   **)
  match goal with
    | H: join emp ?y ?z |- _ =>
      (** y = z **)
      apply map_join_emp'' in H;
      subst z
    | H: join ?x emp ?z |- _ =>
      (** x = z **)
      apply map_join_emp' in H;
      subst z
    | H: join ?x ?y emp |- _ =>
      (** x = y = emp **)
      apply map_join_pos in H;
      destruct H;
      subst x y
  end.

Ltac wash_emps :=
  repeat wash_emp.

Goal forall {A B T:Type} {MC:PermMap A B T} (x1 x2 x3 x4 x5:T) t v,
    join x1 x2 emp->
    join_list (x1 :: x2 :: nil) x3 ->
    get x2 t = Some v -> False.
intros.
wash_emps.
Abort.

Ltac wash_get :=
  (** transform [get x t = Some v] to [join (sig x t) x' x] **)
  match goal with
    | H: get ?x ?t = Some ?v |- _ =>
      apply map_join_get_sig in H;
      destruct H
  end.

Ltac wash_gets :=
  repeat wash_get.

Goal forall {A B T:Type} {MC:PermMap A B T} (x1 x2 x3 x4 x5:T) t v,
    get x1 t = Some v ->
    get x2 t = Some v ->
    False.
intros.
wash_gets.
Abort.

Ltac intro_jl_nil :=
  (** [join_list nil emp] is alwasy true, intro it to context if it doesn't in **)
  match goal with
    | H: join_list nil emp |- _ => idtac
    | |- _ =>
      generalize jl_emp; intro
  end.

Ltac wash :=
  wash_gets;
  wash_emps;
  wash_joins;
  intro_jl_nil.

Goal forall {A B T:Type} {MC:PermMap A B T} (x1 x2 x3 x4 x5:T) t v,
    join x1 x2 x3 ->
    get x1 t = Some v -> False.
intros.
wash.
wash.
Abort.

(******************************************************************************)
(** * Pick: clear redundant hypo in context **)

Ltac pick_jl_x' x :=
  (** x: B **)
  (** forall [H:join_list _ x], if there is no [done H], then clear it **)
  repeat match goal with
           | H: join_list _ x |- _ =>
             let b := check_done H in
             match b with
               | false => clear H
             end
         end.

Goal forall {A B T:Type} {MC:PermMap A B T} (x1 x2 x3 x4 x5:T),
    join x1 x2 x5 ->
    join x3 x4 x5 ->
    False.
intros.
wash_joins.
place_done H0.
pick_jl_x' x5.
Abort.


Ltac pick_jl_x x :=
  (** x: B **)
  (** If there is several hypo of type [join_list _ x],
      then keep the freshest one (nearest to bottom, named H, the first match succeed), clear others.
      Finally palce [done H] to indicate we have done pick_join_x for x.
   **)
  match goal with
    | H: join_list _ x |- _ =>
      let b := check_done H in
      match b with
        | true => idtac
        | false =>
          place_done H;
          pick_jl_x' x
      end
  end.

Goal forall {A B T:Type} {MC:PermMap A B T} (x1' x2' x3' x4' x5' x1 x2 x3 x4 x5:T),
    join x1 x2 x5 ->
    join x3 x4 x5 ->
    join x1' x2' x5 ->
    join x3' x4' x3 ->
    join x1' x2' x3 ->
    False.
intros.
wash.
pick_jl_x x5.
pick_jl_x x3.
Abort.

Ltac pick_jl :=
  (** clear context, ensure:
      forall x, there is only one [H: join_list _ x] in context.
      if there are many, keep the freshest one (nearest to bottom). 
   **)
  repeat match goal with
           | H: join_list _ ?x |- _ =>
             let b := check_done H in
             match b with
               | true => (** already do pick_join_one for x **)
                 fail 1
               | false => pick_jl_x x
             end
         end;
  clear_done.

Goal forall {A B T:Type} {MC:PermMap A B T} (x1' x2' x3' x4' x5' x1 x2 x3 x4 x5:T),
    join x1 x2 x5 ->
    join x3 x4 x5 ->
    join x1' x2' x5 ->
    join x3' x4' x3 ->
    join x1' x2' x3 ->
    False.
intros.
wash.
pick_jl.
pick_jl.
Abort.

Ltac pick := pick_jl.

(******************************************************************************)
(** * Chop: transform all [H: join_list lx x] to more primitive form **)

Ltac chop_join H :=
  (** H: hypo ident **)
  (** H has the form [H: join_list lz z], calculate the most primitive representation of z.
   **)
  let rec chop_join' l :=
      match l with
        | nil => idtac
        | ?x :: ?l' =>
          match goal with
            | H': join_list ?lx x |- _ =>
              chop_join H'; (** make H' to be the most primitive form **)
              liftH H x; 
              generalize (@jl_sub _ _ _ _ _ _ _ H' _ H); (** subst x with lx' in H' **)
              clear H; intro H; (simpl in H);
              chop_join' l'
            | _ => chop_join' l'
          end
      end in
  match type of H with
    | join_list ?lx ?x =>
      let b := check_done x in
      match b with
        | true => idtac 
        | false =>
          place_done x;
          let l1 := constr:(rev lx) in
          let l2 := (eval simpl in l1) in
          chop_join' l2
      end
  end.

Goal forall {A B T:Type} {MC:PermMap A B T} (a1 a2 x1' x2' x1 x2 x3 x4 x12 x34 x1234:T) (x:A) (v:B),
    join_list (x1::x2::(sig x v)::nil) x12 ->
    join a1 a2 x2' ->
    join x1' x2' x3 ->
    join_list (x12::x3::x4::nil) x1234 -> False.
intros;
wash;
liftH H2 x3.
chop_join H2.
liftH H2 x4.
Abort.

Ltac chop :=
  repeat match goal with
           | H: join_list ?lx ?x |- _ =>
             progress (chop_join H)
         end;
  clear_done.

Goal forall {A B T:Type} {MC:PermMap A B T} (a1 a2 x1' x2' x1 x2 x3 x4 x12 x34 x1234:T) (t1 t2:A) (v1 v2:B),
    join_list (x1::x2::(sig t1 v1)::nil) x12 ->
    join a1 a2 x2' ->
    join x1' x2' x3 ->
    get x4 t2 = Some v2 ->
    join_list (x12::x3::x4::nil) x1234 -> False.
intros.
wash; pick.
chop.
chop.
Abort.

Goal forall {A B T:Type} {MC:PermMap A B T} (a1 a2 x1' x2' x1 x2 x3 x4 x5 x12 x34 x1234:T) (x:A) (v:B),
    join_list (x1::x2::(sig x v)::nil) x12 ->
    join a1 a2 x2' ->
    join x1' x2' x3 ->
    join x5 emp x1' ->
    join_list (x12::x3::x4::nil) x1234 -> False.
intros.
wash; pick.
chop.
Abort.

(******************************************************************************)
(** * Dish: intro primitive elements of join_list **)

Ltac jsplit H lx :=
 (** H: hypo, lx: list T **)
  (** If we have [H: join_list lz z] and lx is subset of lz,
      then intro [H': join_list lx x].
      Use lemma jl_split_left.
   **)
  let H' := fresh in
  generalize H; intro H'; 
  liftsH H' lx; 
  match type of H' with
    | join_list ?l ?m =>
      let ly := truncate l lx in
      let tmp := fresh in
      assert (tmp: l = lx ++ ly) by auto;
      rewrite tmp in H'; clear tmp; 
      apply jl_split_left in H'; 
      destruct H'
  end.

Goal forall {A B T:Type} {MC:PermMap A B T} (x y z i:T),
    join_list (x::y::z::nil) i ->
    join_list (x::y::nil) z -> False.
intros.
jsplit H (y::z::nil).
let n := truncate (x::y::z::nil) (x::y::nil) in pose n.
jsplit H (x::z::nil).
Abort.

Ltac dish_jlH H :=
  (** H: hypo ident **)
  (** H has type [H: join_list l m],
      for every element x in l, generate [H': join_list (x::nil) x],
      if x doesn't have join_list form in context.
   **)
  let rec dish_jlH' l :=
      (** l: list T **)
      match l with
        | nil => idtac
        | ?x :: ?l' =>
          first [ in_hyp_x' x (** x is already in context **)
                | generalize (@jl_ref _ _ _ _ x); intro (** x is not in context, intro [join_list (x::nil) x] **)
                ];
          dish_jlH' l'
      end in
  match type of H with
    | join_list ?l ?m =>
      dish_jlH' l
  end.

Ltac dish_jl :=
  (** do dish_jlH for a hypo [H: join_list _ _], which not do dish_jlH for it before **)
  match goal with
    | H: join_list ?l ?m |- _ =>
      match l with
        | m :: nil => fail 1
        (** H has type [join_list (m::nil) m], no use for dish_one **)
        | _ =>
          let dummy := check_done H in
          match dummy with
            | false =>
              (** not do [dish_jl H] yet **)
              place_done H;
              dish_jlH H
          end
      end
  end.

Ltac dish_jls :=
  repeat dish_jl;
  clear_done.

Goal forall {A B T:Type} {MC:PermMap A B T} (t1 t2:A) (v1 v2:B) (x1 x2 x3 x4 x5 y z:T),
    join_list (x1::x2::x3::nil) y ->
    join_list (x1::nil) x1 ->
    join_list (y :: z:: (sig t1 v1) :: (sig t2 v2):: nil) x1 ->
    join_list (x1::x2::x3::x4::x5::nil) z ->
    False.
intros.
dish_jls.
dish_jls.
dish_jls.
Abort.

Ltac dish :=
  dish_jls.


Goal forall {A B T:Type} {MC:PermMap A B T} (x1 x2 x3 x4 x5 y z:T),
    join_list (x1::x2::x3::nil) y ->
    join_list (x1::nil) x1 ->
    join_list (y :: z:: nil) x1 ->
    join_list (x1::x2::x3::x4::x5::nil) z ->
    False.
intros.
dish.
Abort.

Goal forall {A B T:Type} {MC:PermMap A B T} (x1 x2 x3 x4 x5 y z:T),
    join_list (x1::x2::x3::nil) y ->
    join_list (x1::nil) x1 ->
    join_list (x1::x2::x3::x4::emp::emp::x5::nil) z ->
    False.
intros.
wash; pick.
dish.
Abort.

Example test_2:
  forall {A B T:Type} {MC:PermMap A B T} a b c d mab mabc mabcd,
    join a b mab ->
    join mab c mabc ->
    join mabc d mabcd ->
    exists mbcd mbc,
      join a mbcd mabcd /\
      join b c mbc /\
      join mbc d mbcd.
Proof.
  intros.
  wash.
  chop.
  dish.
  do 2 eexists.
  instantiate (1:= merge_list (b::c::d::nil)).
  instantiate (1:= merge_list (b::c::nil)).
Abort.

Example test_2':
  forall {A B T:Type} {MC:PermMap A B T} a b c d a' mab mabc mabcd,
    join a' emp a ->
    join a b mab ->
    join mab c mabc ->
    join mabc d mabcd ->
    exists mbcd mbc,
      join a mbcd mabcd /\
      join b c mbc /\
      join mbc d mbcd.
Proof.
  intros.
  wash; pick.
  chop.
  dish.
  do 2 eexists.
  instantiate (1:= merge_list (b::c::d::nil)).
  instantiate (1:= merge_list (b::c::nil)).
Abort.

(******************************************************************************)
(** * taste_join and eat_join **)

Ltac equate x y :=
  (** A: Type, x y: A **)
  (** I learn this trick from CPDT, it can instant existential variables, when x or y are evar! **)
  let dummy := constr:(eq_refl x : x = y) in idtac.

Ltac search_l lx :=
  (** lx: list T **)
  (** find [H: join_list lx x], return H **)
  match goal with
    | H: join_list ?lm ?m |- _ =>
      let b := same_list lm lx in
      match b with
        | true => constr:(H)
        | false => fail
      end
  end.

Ltac complement_x x :=
  (** x: T **)
  (** return lx of [H: join_list ?lx x] in context **)
  let H := search_x x in
  match type of H with
    | join_list ?lx _ =>
      constr:(lx)
  end.

Ltac complement_l lx :=
  (** lx: list T **)
  (** return x of [H: join_list lx ?x] in context **)
  let H := search_l lx in
  match type of H with
    | join_list _ ?x =>
      constr:(x)
  end.

Goal forall {A B T:Type} {MC:PermMap A B T} (x1 x2 x3 x4 x5 y z:T),
    join_list (x1::x2::x3::nil) y ->
    join_list (x1::x2::x3::x4::x5::nil) z ->
    False.
intros.
let n := complement_l (x2::x1::x3::x4::x5::nil) in pose n.
Abort.


(*
  Definition is_evar (T : Type) (x : T) :=
    (** intro in hypo to indicate the x is a evar **)
    True.

  Ltac is_evarb x :=
    (** A: Type, x: A **)
    (**  **)

  Failed: the gap between ltac and contr !
 *)

Ltac all_not_evar l :=
  (** l: list ?T **)
  (** predicate about whether all element in l are not evars, return tactic value **)
  match l with
    | nil => idtac
    | ?x :: ?l' =>
      (** x is evar, fail this function **)
      is_evar x; fail 1
    | ?x :: ?l' =>
      (** x is not evar, continue check l' **)
      all_not_evar l'
  end.

Goal forall {A B T:Type} {MC:PermMap A B T} (x1 x2:T), exists x, join x1 x2 x.
intros.
eexists.
all_not_evar (x1::nil).
match goal with
  | |- join ?x ?y ?z =>
    is_evar z; all_not_evar (x::y::nil)
end.
Abort.

Goal forall {A B T:Type} {MC:PermMap A B T} (x1 x2 x3 x4 x5 m: T), join_list (x1::x2::x3::x4::x5::nil) m -> False.
intros.
let n := extract (x1::x2::x3::x4::x5::nil) (x3::x2::x1::nil) in pose n.
liftsH H (x3::x2::x1::nil).
(** whether lx ++ (extract lz lx) eql to the lz of (liftsH Hz lx) ? So proof is very useful in this situation! **)
Abort.

Ltac jrewrite H lx ly :=
  (** H:hypo ident, lx ly: list T **)
  (** [H: join_list lz z], rewrite H to [H: join_list (lx ++ ly) z] **)
  let lz':= (eval simpl in (lx ++ ly)) in
  liftsH H lz';
  let tmp:= fresh in
  assert (tmp: lz' = lx ++ ly) by auto;
  rewrite tmp in H; clear tmp.

Goal forall {A B T:Type} {MC:PermMap A B T} (x1 x2 x3 x4 x5 m: T), join_list (x1::x2::x3::x4::x5::nil) m -> False.
intros.
jrewrite H (x2::x4::nil) (x3::x5::x1::nil).
Abort.

(* ** ac: Check @jl_intro_op. *)

Ltac intro_jop x y z :=
  (** x y z: T **)
  (** intro hypo [join x y z],
      if we have [Hx: join_list lx x, Hy: join_list ly y, Hz: join_list lz z],
      and (lx ++ ly) is the same set as lz.
      Using lemma jl_intro_op.
   **)
  let Hx := search_x x in
  let Hy := search_x y in
  let Hz := search_x z in
  let H' := fresh in
  generalize Hz; intro H';
  let lx := complement_x x in
  let ly := complement_x y in
  jrewrite H' lx ly; (** rewrite H' to suit jl_intro_op **)
  generalize (@jl_intro_op _ _ _ _ _ _ _ _ _ Hx Hy H'); intro;
  clear H'.

Goal forall {A B T:Type} {MC:PermMap A B T} (x1 x2 x3 x4 x5 x y z: T),
    join_list (x1::x2::x3::nil) x ->
    join_list (x4::x5::nil) y ->
    join x y z -> False.
intros.
wash;pick; chop.
liftsH H1 (x2::x1::x3::nil).
intro_jop x y z.
assert (join_list (x1::nil) x1) by jeauto.
intro_jop emp x1 x1.
intro_jop x1 emp x1.
intro_jop emp emp emp.
Abort.

(* ** ac: Check jl_merge_list_subtract. *)

Ltac subtract z x evar_y:=
  (** z x evar_y: T, evar_y is evar **)
  (** From [join_list lx x] and [join_list lz z], calculate and instant evar_y, which ensure [join x y z].
        using [merge_list ly] to instant evar_y, avoid the trick of instant evar, and intro [join_list ly (merge_list ly)].
        main lemma: jl_merge_list_subtract.
        Limits: [join_list ly _] must not already in context.
        PS: using @ to explicit give arguments to lemma, the implicit type inference rule is not adequate.
            Pay attention to implicit arguments of type class!
   **)
  let lz := complement_x z in
  let lx := complement_x x in
  let ly := extract lz lx in
  equate evar_y (merge_list ly); (** instant evar_y with y **)
  let Hx := search_x x in
  let Hz := search_x z in
  let Hz' := fresh in
  generalize Hz; intro Hz';
  jrewrite Hz' lx ly; (** rewrite Hz' to [join_list (lx ++ ly) z] **)
  generalize (@jl_merge_list_subtract _ _ _ _ _ _ Hx _ _ Hz'); intro; (** intro [join_list ly (merge_list ly)] **)
  clear Hz'.

(* ** ac: Check jl_merge_list_subtract. *)
(* ** ac: Check @jl_merge_list_subtract. *)

Goal forall {A B T:Type} {MC:PermMap A B T} (x1 x2 x3 x4 x5 x y z: T),
    join_list (x1::x2::x3::nil) x ->
    join_list (x4::x5::nil) y ->
    join x y z ->
    exists y', join x y' z.
intros.
wash; chop.
eexists.
match goal with
  | |- join ?x ?y ?z =>
    subtract z x y
end.
match goal with
  | |- join ?x ?y ?z =>
    intro_jop x y z
end.
Abort.

(* ** ac: Check jl_merge_list_merge. *)
(* ** ac: Check jl_intro_merge. *)

Ltac intro_merge' H x y :=
  (** H: hypo ident, x y: T **)
  (** H has the type [H: join_list lm m], and we has [join_list lx x], [join_list ly y] in context,
        if lm can be rewrited to (lx ++ ly ++ l'), then we can use jl_intro_merge to intro [join x y (merge x y)].
        This function can split to disj and intro, to achieve more primitive.
   **)
  let H' := fresh in
  generalize H; intro H';
  let lx := complement_x x in
  let ly := complement_x y in
  let lxy := (eval simpl in (lx ++ ly)) in
  liftsH H' lxy; (** lifts (lx ++ ly) in H' **)
  match type of H' with
    | join_list ?l ?m =>
      let l' := extract l lxy in
      let Hx := search_x x in
      let Hy := search_x y in
      let tmp := fresh in
      assert (tmp: l = lx ++ ly ++ l') by auto;
      rewrite tmp in H'; clear tmp;
      generalize (@jl_intro_merge _ _ _ _ _ _ _ _ _ _ H' Hx Hy);
      intro;
      clear H'
  end.

Ltac intro_merge x y :=
  (** x y: T **)
  (** try to find H for intro_merge' **)
  match goal with
    | H: join_list ?l ?m |- _ =>
      intro_merge' H x y
  end.

Goal forall {A B T:Type} {MC:PermMap A B T} (x1 x2 x3 x4 x5 x y z: T),
    join_list (x1::x2::x3::nil) x ->
    join_list (x4::x5::nil) y ->
    join x y z ->
    exists z', join x y z'.
intros.
wash; chop.
intro_merge x y.
Abort.

(* ** ac: Check @jl_intro_merge_list_sub. *)

Ltac intro_merge_list' H lx :=
  (** H: hypo, lx: list T **)
  (** [H:join_list lm m], lx is subset of lm.
      intro [join_list lx (merge_list lx)].
   **)
  match type of H with
    | join_list ?lm ?m =>
      let ly := extract lm lx in
      let H' := fresh in
      generalize H; intro H';
      jrewrite H' lx ly; (** rewrite lm with lx ++ ly **)
      apply jl_intro_merge_list_sub in H'
  end.

Ltac intro_merge_list lx :=
  (** try to find H for intro_merge_list' **)
  match goal with
    | H: join_list _ _ |- _ =>
      intro_merge_list' H lx
  end.

Goal forall {A B T:Type} {MC:PermMap A B T} (x1 x2 x3 x4 x5 x y z: T),
    join_list (x1::x2::x3::nil) x ->
    join_list (x4::x5::nil) y ->
    join x y z ->
    exists z', join x y z'.
intros.
intro_merge_list (x1::x3::nil).
Abort.

Ltac union x y evar_z:=
  (** x y evar_z:T, evar_z is evar **)
  (** We have [join_list lx x], [join_list ly y], x y is disjoint, 
      then we can calculate and instant evar_z = (merge_list (l1 ++ l2)).
      At the same time, intro [join_list (l1 ++ l2) (merge_list (l1 ++ l2))], and perform simpl on it.
   **)
  let lx := complement_x x in
  let ly := complement_x y in
  let lz := (eval simpl in (lx ++ ly)) in
  equate evar_z (merge_list lz); (** instant evar_z with (merge_list lz) **)
  let Hx := search_x x in
  let Hy := search_x y in
  intro_merge x y; (** intro [join x y (merge x y)] to indicate x y are disjoint **)
  let H' := fresh in
  match goal with
    | H: join x y (merge x y) |- _ =>
      generalize (@jl_merge_list_merge _ _ _ _ _ _ _ _ Hx Hy H);
      intro H';
      clear H; (** clear [join x y (merge x y)] **)
      let tmp := fresh in
      assert (tmp: lx ++ ly = lz) by auto;
      rewrite tmp in H'; (** rewrite lx ++ ly to lz **)
      clear tmp
  end.


Goal forall {A B T:Type} {MC:PermMap A B T} (x1 x2 x3 x4 x5 x y z: T),
    join_list (x1::x2::x3::nil) x ->
    join_list (x4::x5::nil) y ->
    join x y z ->
    exists z', join x y z'.
intros.
wash; pick; chop.
eexists.
match goal with
  | |- join ?x ?y ?z =>
    union x y z
end.
Abort.

Ltac swallow_ex :=
  (** elimite a exist **)
  match goal with
    | |- ex _ =>
      eexists
  end.

Ltac swallow_exs :=
  repeat swallow_ex.

Ltac taste_join :=
  (** Prepare for solving goals only involve [join].
        Instant existential variables.
        For example:
          exists mbcd mbc : T,
            join a mbcd mabcd /\ join b c mbc /\ join mbc d mbcd.
        Method:
             find term [join x y z], which (x y z) only has one evar,
             if [is_evar x], then ly and lz in hypo, then lx = lz - ly, according this, I can instant x.
             if [is_evar y], the same.
             if [is_evar z], find lx and ly, then lz = lx ++ ly, according this, I can instant z.
   **)
  match goal with
    | |- ?t =>
      match t with
        | context f [join ?x ?y ?z] =>
          (** search all sub term of t which has form [join x y z] **)
          first [ (** case 1: only x is evar **)
              is_evar x; all_not_evar (y::z::nil);
              subtract z y x
            | (** case 2: only y is evar **)
            is_evar y; all_not_evar (x::z::nil);
            subtract z x y
            | (** case 3: only z is evar **)
            is_evar z; all_not_evar (x::y::nil);
            union x y z ]
        | _ => idtac
      end
  end.

Example test_13':
  forall {A B T:Type} {MC:PermMap A B T} a b c d mab mabc mabcd,
    join a b mab ->
    join mab c mabc ->
    join mabc d mabcd ->
    exists mab mcd,
      join a b mab /\
      join c d mcd /\
      join mab mcd mabcd.
Proof.
  intros.
  wash; pick; chop; dish.
  swallow_exs.
  repeat taste_join.
Abort.


(* ** ac: Check @jl_ref. *)
Ltac intro_join_list x :=
  (** x: T **)
  (** if there is no [join_list _ x], then intro [join_list lx x].
        Two situations:
          1. x is a primitive element, lx = (x::nil)
          2. x is [merge_list l], then lx = l
   **)
  match goal with
    | H: join_list _ x |- _ => idtac
    | _ =>
      match x with
        | merge_list ?lx =>
          intro_merge_list lx
        | _ => generalize (@jl_ref _ _ _ _ x); intro
      end
  end.

Example test_14':
  forall {A B T:Type} {MC:PermMap A B T} a b c d mab mabc mabcd,
    join a b mab ->
    join mab c mabc ->
    join mabc d mabcd ->
    exists mab mcd,
      join a b mab /\
      join c d mcd /\
      join mab mcd mabcd.
Proof.
  intros.
  wash; pick; chop; dish.
  intro_merge_list (a::b::c::nil).
  intro_join_list (merge_list (a::b::c::nil)).
  intro_join_list (merge_list (a::c::d::nil)).
  intro_join_list (merge_list (a::nil)).
  intro_join_list a.
  intro_join_list emp.
  clear H4.
  intro_join_list a.
Abort.

Ltac eat_join :=
  (** solve(eat ^_^) the goal about [join x y z].
        method:
          1. perform taste_join first, try to instant existential variables
          2. if there is no existential variables, then
             1. the goal is [join x y z], to make sure [join_list _ x],
                [join_list _ y], [join_list _ z] are all in context,
                perform intro_join_list on them.
             2. using join_list form of x y z, intro [join x y z].
   **)
  taste_join;
  match goal with
    | |- join ?x ?y ?z =>
      intro_join_list x;
      intro_join_list y;
      intro_join_list z;
      intro_jop x y z; (** intro [join x y z] **)
      trivial
    | |- _ => idtac
  end.

Example test_15':
  forall {A B T:Type} {MC:PermMap A B T} a ,
    join a emp a.
Proof.
  intros.
  wash.
  eat_join.
Abort.

Example test_16':
  forall {A B T:Type} {MC:PermMap A B T} a b c d mab mabc mabcd,
    join a b mab ->
    join mab c mabc ->
    join mabc d mabcd ->
    exists mab mcd,
      join a b mab /\
      join c d mcd /\
      join mab mcd mabcd.
Proof.
  intros.
  wash; pick; chop; dish.
  swallow_exs.
  repeat split.
  eat_join.
  eat_join.
  eat_join.
Qed.

(******************************************************************************)
(** * taste_set **)
Ltac liftH_set H t :=
  (** H: hypo ident, t: A **)
  (** lift (sig t _) in H **)
  let rec findt l t :=
      (** find (sig t _) in l, return nat **)
      match l with
        | (sig t ?v) :: ?l' => constr:(O)
        | _ :: ?l' =>
          let n := findt l' t in
          constr:(S n)
      end in 
  match type of H with
    | join_list ?lx ?x =>
      let n := findt lx t in
      liftH_nat H n
  end.

Goal forall {A B T:Type} {MC:PermMap A B T} (x x1 x2 x3 x4:T) t v t' v',
    join_list (x1::x2::(sig t' v')::x3::(sig t v)::x4::nil) x -> False.
  intros.
  liftH_set H t.
Abort.

Ltac taste_set_noPerm :=
  (** usePerm = false:
      if there is subterm [set x t v] in goal,
        intro hypo [join_list lx' (set x t v)] and the new primitive element of it,
        if the join_list form of (sig t v') is not appear in context.  
        We need it when solving [join _ _ _] and [get _ _ = Some _].
   **)
  match goal with
    | Hn: usePerm = false |- context [set ?x ?t ?v] =>
      first [ in_hyp_x' (set x t v); fail 1 (** is (set x t v) already in hypo ?  **)
            | let H := search_x x in
              let H' := fresh "H" in
              generalize H; intro H';
              liftH_set H' t; (** lift (sig t _) in H **)
              generalize (@jl_intro_set_noPerm _ _ _ _ _ _ _ _ Hn H' v); clear H'; intro H';
              dish_jlH H' (** intro maybe new primitive element **)
            ]
    | |- _ => idtac
  end.

Example test:
  forall {A B T:Type} {MC:PermMap A B T} x y t v v',
    usePerm = false ->
    join x (sig t v) y ->
    get (set y t v') t = Some v'.
Proof.  
  intros; wash; chop; dish.
  taste_set_noPerm.
Abort.

Example test:
  (** from mutexPendPure1 **)
  (** TODO: (sig x y) is not appear in context, it is (set (sig x y') x y) **)
  forall {A B T:Type} {MC:PermMap A B T} x y x1 y1 y1' y' l1 l2 l3 L L',
    usePerm = false ->
    join (sig x y') L' L ->
    join l3 l2 L' ->
    join (sig x1 y1') l1 l2 ->
    join (sig x y) (set L' x1 y1)
         (set (set L x y) x1 y1).
Proof.
  intros; wash; chop; dish.
  taste_set_noPerm.
  taste_set_noPerm.
  taste_set_noPerm.
  eat_join.
Abort.

Ltac taste_set := taste_set_noPerm.

(******************************************************************************)
(** * eat_get **)
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

Ltac eat_get_noPerm := 
  (** solve(eat) goal has form [get x t = Some v], using lemma jl_intro_get **)
  match goal with
    | Hn: usePerm = false |- get ?x ?t = Some ?v =>
      let H := search_x x in
      liftsH H ((sig t v)::nil);
      generalize (@jl_intro_get_noPerm _ _ _ _ _ _ _ _ Hn H); intro;
      trivial
    | |- _ => idtac
  end.

Example test:
  forall {A B T:Type} {MC:PermMap A B T} x y z m t v,
    usePerm = false ->
    join x (sig t v) y ->
    join y z m ->
    get m t = Some v.
Proof.
  intros; wash; chop; dish.
  eat_get_noPerm.
Abort.

Ltac eat_get := eat_get_noPerm.

(******************************************************************************)
(** * taste and eat **)
Ltac taste_one :=
  taste_set; taste_join.

Ltac taste :=
  repeat taste_one.

Ltac eat_one :=
  eat_get; eat_join.

Ltac eat :=
  repeat eat_one.

(******************************************************************************)
(** * sum up **)
(** main tactic:
        cook: deal with context, prepare to solve
        jeat: compound join solver, but need using [cook] for prepare.
        heat: clear context (destruct and and exist hypothesis)
        geat: general eat, combine all up three primitive.
 **)
(** TODO: heat and eats can move to a seperated file, which perform general simplification on hypothesis and goals **)

Ltac cook :=
  (** transform all information to [join_list _ _] form, prepare for later solve **)
  wash; pick; chop; dish.

Ltac swallow_and :=
  match goal with
    | |- _ /\ _ =>
      split
  end.

Ltac swallow :=
  (** splits goals to several single goals **)
  repeat (first [swallow_ex | swallow_and]).

Ltac swallow_andH :=
  match goal with
    | H: (_ /\ _) |- _ => destruct H
  end.

Ltac swallow_exH :=
  match goal with
    | H: exists _, _ |- _ => destruct H
  end.

Ltac swallowH :=
  (** Simplifying context.
      for example, eliminate [and] and [exists] in context.  **)
  repeat (first [swallow_andH | swallow_exH | subst]).

Ltac jeat :=
  (** solve goals include (join x y z) **)
  swallow; eauto 2;
  taste; eat;
  jeauto2.

Goal forall (A B T : Type) (MC : PermMap A B T)
       x,
    join emp x x.
  intros.
  cook.
  jeat.
Qed.  
  
Ltac heat :=
  (** alias of eatsH **)
  swallowH.

Ltac geat :=
  (** general automatical tactic for solve [join] goal, can use everywhere you like **)
  heat; cook; jeat.

Example test_13'':
  forall {A B T:Type} {MC:PermMap A B T} a b c d mab mabc mabcd,
    join a b mab ->
    (exists heh, join mab c heh /\ join mab c mabc) ->
    join mabc d mabcd ->
    exists mab mcd,
      join a b mab /\
      join c d mcd /\
      join mab mcd mabcd.
Proof.
  intros.
  geat.
Qed.

Example test_13''':
  forall {A B T:Type} {MC:PermMap A B T} a b c d mab mabc mabcd,
    join a b mab ->
    join mab c mabc ->
    join mabc d mabcd ->
    join a b mab.
Proof.
  intros.
  geat.
Qed.

End old.

Export old.


(******************************************************************************)
(**Lib for  maps added by ming*)
Lemma abst_get_set_disj:
  forall  (A B T : Type) (MC: PermMap A B T)   O id Of x y,
    usePerm = false ->
    get O id = Some x -> 
    disjoint O Of -> 
    disjoint (set O id y) Of.
Proof.
  intros.
  unfold disjoint in *.
  simp join.
  exists (set x0 id y).
  eapply map_join_set_none; eauto.
  eapply map_join_get_no_perm1; eauto.
Qed.


Lemma join_sig_get_disj:
  forall  (A B T : Type) (MC: PermMap A B T)  O O' x y,
    usePerm = false ->
    join (sig x y) O O'-> 
    get O' x = Some y /\ get O x = None/\ Maps.sub O O'.
Proof.
  intros.
  split.
  eapply map_join_get_no_perm2; eauto.
  apply map_get_sig.
  split.
  eapply map_join_get_no_perm1; eauto.
  apply map_get_sig.
  unfold sub.
  eexists.
  apply map_join_comm.
  eauto.
Qed.


Lemma sub_get_get :
  forall  (A B T : Type) (MC: PermMap A B T)  O O' x y,
    usePerm = false ->
    Maps.sub O O' ->
    get O x =  Some y ->
    get O' x = Some y.
Proof.
  intros.
  unfold sub in H0.
  destruct H0.
  eapply  map_join_get_no_perm2; eauto.
Qed.


Lemma sig_set_emp :
  forall  (A B T : Type) (MC: PermMap A B T)  x y ,
    sig x y  = set emp x y.
Proof.
  intros.
  apply eq_sym.
  apply map_set_emp.
Qed.


Lemma sig_set_sig :
  forall  (A B T : Type) (MC: PermMap A B T)  x y y',
    sig x y  = set (sig x y')  x y.
Proof.
  intros.
  apply eq_sym.
  apply map_set_sig.
Qed.

Lemma get_set_neq :
   forall  (A B T : Type) (MC: PermMap A B T)   O x x' y y',
     x <> x' ->
     get O x =  y ->
     get (set O x' y') x =  y.
Proof.
  intros.
  rewrite map_get_set'; auto.
Qed.


Lemma  disj_get_merge_get :
  forall  (A B T : Type) (MC: PermMap A B T)   O O' x y,
    usePerm = false ->
    disjoint O O' ->
    get O x  = Some y ->
    get  (merge O O') x = Some y.
Proof.
  intros.
  unfold disjoint in H0.
  apply map_join_merge in H0.
  eapply map_join_get_no_perm2; eauto.
Qed.

Lemma join_set_set :
forall  (A B T : Type) (MC: PermMap A B T)   O O' O'' id x y,
  usePerm = false ->
  join O O' O'' -> 
  get O id = Some x  ->
  join (set O id y) O'  (set O'' id y).
Proof.
  intros.
  eapply map_join_set_none; eauto.
  eapply map_join_get_no_perm1; eauto.
Qed.

Lemma get_join_sig_set:
forall  (A B T : Type) (MC: PermMap A B T)   qls qid a,  
  get qls qid = None ->
  join (sig qid a) qls (set qls qid a).
Proof.
  intros.
  assert (sig qid a = set emp qid a).
  apply eq_sym.
  apply map_set_emp.
  rewrite H0.
  eapply map_join_set_none; eauto.
  geat.
Qed.


Lemma get_set_eq :
  forall  (A B T : Type) (MC: PermMap A B T)   O x  y,
    get (set O x y)  x = Some y.
Proof.
  intros.
  apply map_get_set.
Qed.

Lemma  join_merge_set_eq:
  forall (A B T : Type) (MC: PermMap A B T)   O Of x id  y O',
    usePerm = false ->
    join  O Of O' ->
    get O id = Some x ->
    merge (set O id y)  Of = set (merge O Of) id y.
Proof.
  intros.
  assert (join (set O id y) Of  (set O' id y)).
  eapply join_set_set; eauto.
  apply map_join_merge' in H2.
  apply map_join_merge' in H0.
  subst O'.
  auto.
Qed.


Lemma disjoint_merge_sym :
  forall  (A B T : Type) (MC: PermMap A B T)  O O',
    disjoint O O' ->
    merge O  O'  = merge O' O.
Proof.
  intros.
  eapply map_merge_comm.
  eauto.
Qed.

Lemma disjoint_sym:
  forall  (A B T : Type) (MC: PermMap A B T)  O O',
    disjoint O O' ->
    disjoint O' O.
Proof.
  intros.
  unfold disjoint in *.
  destruct H.
  exists x.
  apply map_join_comm.
  auto.
Qed.

Lemma join_sig_set: 
  forall  (A B T : Type) (MC: PermMap A B T)   id a O1 O b, 
    usePerm = false ->
    join (sig id a) O1 O -> join (sig id b) O1 (set O id b).
Proof.
  intros.
  assert (set (sig id a)  id b  =  sig id b).
  apply map_set_sig.
  rewrite <- H1.
  eapply join_set_set; eauto.
  jeauto2.
Qed.

Lemma get_join_sig_set_rev:
  forall  (A B T : Type) (MC: PermMap A B T)  x  qls qid qls',  
    usePerm = false ->
    joinsig qid x qls qls' -> 
    qls'= (set qls qid x).
Proof.
  intros.
  unfold joinsig in H0.
  assert (join (sig qid x) qls (set qls qid x)).
  assert (set emp qid x  = sig qid x).
  apply map_set_emp.
  rewrite <- H1.
  eapply map_join_set_none; eauto.
  geat.
  eapply map_join_get_no_perm1; eauto.
  jeauto2.
  eapply map_join_deter; eauto.
Qed.


Lemma disjoint_emp_r:
  forall {A B T:Type} {MC:PermMap A B T} x,
    disjoint emp x .
Proof.
  intros.
  unfold disjoint.
  exists x.
  eapply map_join_comm.
  eapply map_join_emp.
Qed.

Lemma disjoint_emp_l:
  forall {A B T:Type} {MC:PermMap A B T} x,
    disjoint  x emp .
Proof.
  intros.
  unfold join.
  exists x.
  eapply map_join_emp.
Qed.

(*
Lemma minus_disj :
	 forall  (A B T : Type) (MC: PermMap A B T)  M m,
  	 disjoint  (minus M m) m.
Proof. 
  (*
  introv.
  unfolds.t
  rewrite  HalfPermMap.minus_sem.
  remember (MemMod.get M a ) as Hm1.
  remember (MemMod.get m a ) as Hm2.
  destruct Hm1;destruct Hm2; auto.
  Qed.*)
(* Admitted. *)
*)

Lemma get_joinsig_rw:
  forall  (A B T : Type) (MC: PermMap A B T)  v x y,
    usePerm = false ->
    get v x = None -> 
    joinsig x y v (set v x y).
Proof.
  intros.
  unfold joinsig.
  assert (set emp x y  = sig x y).
  apply map_set_emp.
  rewrite <- H1.
  eapply map_join_set_none; eauto.
  geat.
Qed.

(*Lemma join_minus_r : 
  forall  (A B T : Type) (MC: PermMap A B T)  m1 m2 m3 M,
    join m1 m2 (minus M m3) ->
    exists mx, join m2 m3 mx.
Proof.
  (*
  introv Hjm.
  cut (HalfPermMap.disjoint m2 m3).
  introv Hdisj.
  apply join_merge_disj in Hdisj.
  eexists; eauto.
  apply join_disj_meq in Hjm. 
  destruct Hjm.
  apply MemMod.meq_eq in H0.
  assert (HalfPermMap.disjoint (HalfPermMap.minus M m3) m3) by apply Mem_minus_disj.
  rewrite <- H0 in H1.
  apply HalfPermMap.disjoint_merge_elim_l in H1. 
  destruct H1; auto.
  Qed.*)
(* Admitted. *)
*)

Lemma join_in_r : 
  forall  (A B T : Type) (MC: PermMap A B T)  ma mb mab x, 
  join ma mb mab -> indom mb x -> indom mab x.
Proof.
  intros.
  apply map_join_comm in H.
  unfold indom in *.
  simp join.
  assert (exists b, usePerm = b).
  eauto.
  destruct H1.
  destruct x1.
  assert (exists y , get ma x  = y) by eauto.
  destruct H2.
  destruct x1.
  eexists.
  eapply map_join_getp_some;eauto.
  eexists.
  apply map_join_comm in H.
  erewrite <- H0.
  eapply map_join_get_none; eauto.
  eexists.
  eapply map_join_get_no_perm; eauto.
Qed.

Lemma join_in_or :
  forall  (A B T : Type) (MC: PermMap A B T)  ma mb mab x, 
    join ma mb mab ->  indom mab x -> indom ma x \/  indom mb x.
Proof.
  intros.
  unfold indom in H0.
  destruct H0.
  assert (exists b, usePerm = b) by eauto.
  destruct H1.
  destruct x1.
  assert (exists yy, get ma x = yy) by eauto.
  destruct H2.
  destruct x1.
  left; eauto.
  unfold indom.
  eauto.
  right.
  unfold indom.
  eexists.
  rewrite <- H0.
  apply eq_sym.
  eapply map_join_get_none'; jeauto2.
  assert (exists yy, get ma x = yy) by eauto.
  destruct H2.
  destruct x1.
  left; eauto.
  unfold indom.
  eauto.
  right.
  unfold indom.
  eexists.
  rewrite <- H0.
  apply eq_sym.
  eapply map_join_get_none'; jeauto2.
Qed.

Lemma  get_or : 
forall  (A B T : Type) (MC: PermMap A B T)   ma a, 
   get ma a = None \/ exists b,  get ma a = Some b.
Proof.
  intros.
  assert (exists b, get ma a =  b) by eauto.
  destruct H.
  destruct x.
  right; eauto.
  left; eauto.
Qed.

(*
Lemma indom_join_eq:
 forall (A B T : Type) (MC: PermMap A B T)  ma mb ma' mb' mab,
 (forall a,  indom ma a <->  indom ma' a) -> 
  join ma mb mab ->
 join ma' mb' mab -> ma = ma'.
Proof.
  intros.
  unfold indom in *.
  eapply map_join_cancel.
  apply map_join_comm.
  eauto.
  apply map_join_comm.
  
(* ** ac: SearchAbout join. *)
  apply 
  assert (ma = ma' \/ ma <> ma') by tauto.
(* Admitted. *)
*)

Lemma  neq_set_get:
  forall (A B T : Type) (MC: PermMap A B T) x y b tcbls,
    x <> y ->
     get (set tcbls y b) x =  get tcbls x.
Proof.
  intros.
  jeauto2.
Qed.

Lemma  get_join:
  forall (A B T : Type) (MC: PermMap A B T) tcs ptcb m,
    get tcs ptcb = Some m->
    exists tcs',
       join (sig ptcb m) tcs' tcs.
Proof.
  intros.
  jeauto2.
Qed.


Lemma join_merge : 
	forall (A B T : Type) (MC: PermMap A B T) {m1 m2 m3}, 
 	join m1 m2 m3 -> m3 = merge m1 m2.
Proof.
  intros.
  apply map_join_merge'; auto.
Qed.

Lemma disj_join_disj : 
	forall   (A B T : Type) (MC: PermMap A B T)  {m1 m2 m3 m4 m5 m6},
  join m1 m2 m3 ->
  	 join m4 m5 m6 ->
    	 disjoint m3 m6 ->
  		disjoint m1 m4.
Proof.
  intros.
  unfold disjoint in *.
  geat.
Qed.


Lemma join_disj : 
	forall   (A B T : Type) (MC: PermMap A B T)  M1 M2 M,
 	 join M1 M2 M -> 
 	disjoint M1 M2.
Proof.
  intros.
  unfold disjoint.
  geat.
Qed.

Lemma join_sub_sub_sig_neq:
  forall 
  	  (A B T : Type) (MC: PermMap A B T) 	
    x1 x2 m a b m1 m2,
    usePerm = false ->
    join x1 x2 m ->
    sub (sig a m1) x1 ->
    sub (sig b m2) x2 ->
    a <> b.
Proof.
  intros.
  unfold sub in *.
  simp join.
  intro Hf.
  subst.
  assert (get x2 b = Some m2)  by jeauto2.
  assert (get x1 b = Some m1) by jeauto2.
  clear - H0 H3 H4 H.
  eapply map_join_get_some; eauto.
Qed.

Lemma map_join_getp_one:
  forall (A B T : Type) (MC: PermMap A B T)
    t v x y z,
    usePerm = true ->
    join x y z ->
    get x t = Some v ->
    (get y t = None /\ get z t = Some v) \/
    (isRw v = false /\ get y t = Some v /\ get z t = Some (flip v)).
Proof.
  intros.
  destruct (get y t) eqn:Hy.
  rename H1 into Hx.
  assert (v = b /\ isRw v = false /\ get z t = Some (flip v)) by jeauto2.
  right. 
  intuition.
  subst; auto.
  assert (get z t = get x t) by jeauto2.
  rewrite H1 in *.
  left.
  auto.
Qed.

Hint Resolve @map_emp_get @map_eql : jdb0.

Ltac eat_false :=
  match goal with
    | H: ?a = ?b |- _ =>
      try subst; solve [inversion H]
    | H: ?a <> ?b |- _ =>
      try subst; solve [clear -H; tauto]
    | H: False |- _ =>
      inversion H
    | _ => idtac
  end.

Ltac instant H x :=
  generalize (H x); clear H; intro H.

Lemma map_emp_get':
  forall (A B T : Type) (MC: PermMap A B T) x,
    (forall t, get x t = None) ->
    x = emp.
Proof.
  intros.
  generalize (@map_emp_get _ _ _ MC); intro.
  eapply map_eql.
  intros.
  instant H t.
  instant H0 t.
  rewrite H.
  rewrite H0.
  auto.
Qed.  

Hint Resolve @map_emp_get' : jdb0.

Lemma map_join_getp_sig:
  forall (A B T : Type) (MC: PermMap A B T)
    t v1 v2 z,
    usePerm = true ->
    join (sig t v1) (sig t v2) z ->
    v1 = v2 /\ isRw v1 = false /\ get z t = Some (flip v1).
Proof.
  intros.
  assert (Hx: (get (sig t v1) t = Some v1)) by jeauto2.
  assert (Hy: (get (sig t v2) t = Some v2)) by jeauto2.
  jeauto2.
Qed.

Lemma map_join_sig_mergep:
  forall (A B T : Type) (MC: PermMap A B T)
    t v z,
    usePerm = true ->
    isRw v = false ->
    join (sig t v) (sig t v) z ->
    z = sig t (flip v).
Proof.
  intros.
  eapply map_eql.
  intro t'.
  destruct (map_dec_a t t').
  subst.
  generalize (@map_join_getp_sig _ _ _ _ _ _ _ _ H H1); intro.
  heat.
  clear H2 H3.
  rewrite H4.
  rewrite map_get_sig.
  trivial.
  rewrite map_get_sig'.
  assert (get (sig t v) t' = None) by jeauto2.
  assert (get z t' = get (sig t v) t').
    eapply map_join_get_none; eauto.
  rewrite map_get_sig' in H3.
  auto.
  auto.
  auto.
Qed.  

Hint Resolve @map_join_sig_mergep : jdb0.

Lemma map_sig_disjointp:
  forall (A B T : Type) (MC: PermMap A B T)
    t v,
    usePerm = true ->
    isRw v = false ->
    exists z, join (sig t v) (sig t v) z.
Proof.
  intros.
  apply map_disjoint.
  intros.
  destruct (map_dec_a t t0); subst.
  right; right.
  exists v.
  swallow; jeauto2.
  left.
  jeauto2.
Qed.  

Hint Resolve map_sig_disjointp : jdb0.

Lemma map_join_sig_mergep':
  forall (A B T : Type) (MC : PermMap A B T)
    t v,
    usePerm = true ->
    isRw v = false ->
    join (sig t v) (sig t v) (sig t (flip v)).
Proof.
  intros.
  generalize (@map_sig_disjointp _ _ _ _ t v H H0); intro.
  destruct H1.
  assert (x = sig t (flip v)).
    eapply map_join_sig_mergep; auto.
  subst.
  auto.
Qed.  

Hint Resolve map_join_sig_mergep' : jdb0.

Open Scope list_scope.

Lemma jl_perm_sig_merge1:
  forall (A B T : Type) (MC: PermMap A B T)
    t v1 v2 z,
    usePerm = true ->
    join_list ((sig t v1)::(sig t v2)::nil) z ->
    v1 = v2 /\ isRw v1 = false /\ get z t = Some (flip v1).
Proof.
  intros.
  cook.
  assert (join (sig t v1) (sig t v2) z) by jeauto2.
  eapply map_join_getp_sig; eauto.
Qed.  

Lemma jl_perm_sig_merge2:
  forall (A B T : Type) (MC: PermMap A B T)
    t v1 v2 z,
    usePerm = true ->
    join_list ((sig t v1)::(sig t v2)::nil) z ->
    v1 = v2 /\ isRw v1 = false /\ join_list ((sig t (flip v1))::nil) z.
Proof.
  intros.
  generalize (jl_perm_sig_merge1 H H0); intro.
  heat.
  swallow; auto.
  generalize (@map_join_sig_mergep' _ _ _ _ t v2 H H2); intro.
  apply jl_list_to_op in H0.
  assert (sig t (flip v2) = z) by jeauto2.
  subst.
  jeauto2.
Qed.


Lemma jl_perm_merge:
  forall (A B T : Type) (MC: PermMap A B T)
    t a b l' m,
    usePerm = true ->
    join_list ((sig t a)::(sig t b)::l') m ->
    a = b /\ isRw a = false /\ join_list ((sig t (flip a))::l') m.
Proof.
  intros.
  assert (tmp: (sig t a :: sig t b :: l') = (sig t a :: sig t b :: nil) ++ l') by auto.
  rewrite tmp in H0; clear tmp.
  apply jl_split in H0.
  heat.
  generalize (@jl_perm_sig_merge2 _ _ _ _ _ _ _ _ H H0); intro.
  heat.
  swallow; auto.
  assert (join_list ((sig t (flip b) :: nil) ++ l') m) by jeauto2.
  simpl in H3.
  auto.
Qed.  
  
Lemma join_sig_eq_p :
  forall  (A B T : Type) (MC: PermMap A B T) 	
          l a b m1 m2 m3 x1 x2,
    usePerm = true ->
    isRw a = false ->
    isRw b = false ->
    join (sig l a) x1 m1 ->
    join (sig l b) x2 m2 ->
    join m1 m2 m3 ->
    a = b.
Proof.
  intros.
  geat.
  liftH H4 (sig l b).
  generalize (@jl_perm_merge _ _ _ _ _ _ _ _ _ H H4); intro.
  heat.
  auto.
Qed.

Hint Resolve join_sig_eq_p : jdb0.

Lemma map_flip_true:
  forall (A B T : Type) (MC : PermMap A B T) v v',
    usePerm = true ->
    isRw v = true ->
    v' = flip v ->
    isRw v' = false.
Proof.
  intros.
  assert (isRw (flip v) = negb (isRw v)).
    apply map_flip_isRw; auto.  
  rewrite H0 in H2.
  simpl in H2.
  subst.
  auto.
Qed.

Hint Resolve map_flip_true : jdb0.

Lemma map_flip_false:
  forall (A B T : Type) (MC : PermMap A B T) v v',
    usePerm = true ->
    isRw v = false ->
    v' = flip v ->
    isRw (flip v) = true.
Proof.
  intros.
  assert (isRw (flip v) = negb (isRw v)).
    apply map_flip_isRw; auto.  
  rewrite H0 in H2.
  simpl in H2.
  subst.
  auto.
Qed.

Hint Resolve @map_flip_true @map_flip_false : jdb0.

Lemma map_join_sig_mergep'':
  forall (A B T : Type) (MC : PermMap A B T)
    t v a b,
    usePerm = true ->
    isRw v = false ->
    a = sig t v ->
    b = sig t (flip v) ->
    join a a b.
Proof.
  intros.
  generalize (@map_join_sig_mergep' _ _ _ _ t v H H0); intro.
  subst.
  auto.
Qed.

Lemma map_flip_sv':
  forall (A B T : Type) (MC : PermMap A B T) v v',
    usePerm = true ->
    v' = flip v ->
    sameV v v'.
Proof.
  intros.
  assert (sameV v (flip v)).
    apply map_flip_sv; auto.
  subst.
  auto.
Qed.

Hint Resolve @map_flip_sv' : jdb0.
Hint Resolve @map_sv_comm @map_sv_ref @map_sv_assoc: jdb0.
Hint Resolve @map_flip_isRw @map_flip_sv : jdb0.

Lemma map_flip_inv:
  forall (A B T : Type) (MC : PermMap A B T) v,
    usePerm = true ->
    (flip (flip v)) = v.
Proof.
  intros.
  assert (sameV v (flip v)) by jeauto2.
  assert (sameV (flip v) (flip (flip v))) by jeauto2.
  assert (isRw (flip v) = negb (isRw v)) by jeauto2.
  assert (isRw (flip (flip v)) = negb (isRw (flip v))) by jeauto2.
  rewrite H2 in H3.
  rewrite Bool.negb_involutive in H3.
  apply map_perm_eql.
  auto.
  jeauto.
  jeauto.
Qed.

Hint Resolve @map_flip_inv : jdb0.

Lemma join_sig_false_true :
  forall  (A B T : Type) (MC: PermMap A B T)  l a b,
    usePerm = true ->
    isRw b = true ->
    a = flip b -> 
    join (sig l a) (sig l a) (sig l b).
Proof.
  intros.
  assert (isRw a = false) by jeauto2.
  clear H0.
  eapply map_join_sig_mergep''; auto.
  auto.
  rewrite H1.
  rewrite map_flip_inv.
  auto.
  auto.
Qed.  

Lemma join_split :
  forall  (A B T : Type) (MC: PermMap A B T) 
     m1 m2 m m11 m12 m21 m22,
    join m1 m2 m ->
    join m11 m12 m1 ->
    join m21 m22 m2 ->
    exists mx1 mx2, join m11 m21 mx1 /\ join m12 m22 mx2 /\ join mx1 mx2 m.
Proof.
  intros.
  geat.
Qed.  
