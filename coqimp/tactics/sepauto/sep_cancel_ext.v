Require Import include_frm.
Require Import sep_combine.
Require Import seplog_lemmas.
Require Import seplog_tactics.

Ltac star_emp_if_ness :=
  match goal with
    | H : ?s |= _ ** _ |- ?s |= _ ** _ =>
      idtac
    | H : ?s |= _ |- ?s |= _ ** _ =>
      apply seplog_lemmas.astar_r_aemp_intro in H
    | H : ?s |= _ |- ?s |= _ =>
      apply seplog_lemmas.astar_r_aemp_elim; star_emp_if_ness
  end.

Ltac separate_if_ness :=
  match goal with
    | H : ?s |= LV ?l @ ?t |-> ?v ** _ |- ?s |= LV ?l @ ?t |-r-> _ ** _ =>
      separate_val_in_H H
    | H : ?s |= GV ?l @ ?t |-> ?v ** _ |- ?s |= GV ?l @ ?t |-r-> _ ** _ =>
      separate_val_in_H H
    | H : ?s |= PV ?l @ ?t |-> ?v ** _ |- ?s |= PV ?l @ ?t |-r-> _ ** _ =>
      separate_val_in_H H
    | H : ?s |= LV ?l @ ?t |-r-> ?v ** _ |- ?s |= LV ?l @ ?t |-> _ ** _ =>
      sep separate 
    | H : ?s |= GV ?l @ ?t |-r-> ?v ** _ |- ?s |= GV ?l @ ?t |-> _ ** _ =>
      sep separate
    | H : ?s |= PV ?l @ ?t |-r-> ?v ** _ |- ?s |= PV ?l @ ?t |-> _ ** _ =>
      sep separate
    | _ => idtac
  end.

Ltac sep_cancel_ext m n :=
  let s':= fresh in
  match goal with
    | H: ?s |= _ |- ?s |= _ =>
      sep lift m in H;
        sep lift n;
        star_emp_if_ness;
        separate_if_ness;
        sep lift 1%nat in H; (* to ensure generalize will generate A -> B version not forall a, B *)
        match goal with
          | H : ?s |= ?A ** ?B |- ?s |= ?C ** ?D =>
            generalize dependent H; apply astar_mono; 
            [ intros s' H; exact H | first [ clear s; intros s H | intros s' H ] ]
          | H : ?s |= ?A ** ?B |- ?s |= ?C =>
            apply astar_r_aemp_elim;
              generalize dependent H; apply astar_mono; 
              [ intros s' H; exact H | first [ clear s; intros s H | intros s' H ] ]
          | H : ?s |= ?A |- ?s |= ?C ** ?D =>
            apply astar_r_aemp_intro in H;
              generalize dependent H; apply astar_mono; 
              [ intros s' H; exact H | first [ clear s; intros s H | intros s' H ] ]
          | H : ?s |= ?A |- ?s |= ?C =>
            exact H
        end
  end.

Tactic Notation "sep" "cancel" constr(m) constr(n) :=
  sep_cancel_ext m n.
