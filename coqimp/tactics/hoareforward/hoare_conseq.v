Require Import include_frm.
Require Import sep_auto.
Require Import derived_rules.
(** use consequence rule to change pre condition in a hoare triple *)

Tactic Notation "hoare" "normal" "pre" :=
  match goal with
    | |-  ({| _, _, _, _, _, _|} |- _ {{ _ //\\ _ }} _ {{ _ //\\ _ }}) =>
      let s := fresh in
      let H := fresh in
      eapply backward_rule3;
        [ intros s H; sep normal in H; exact H | idtac ]
    | |-  ({| _, _, _, _, _, _ |} |- _ {{ _ }} _ {{ _ }}) =>
      let s := fresh in
      let H := fresh in
      eapply backward_rule1;
        [ intros s H; sep normal in H; exact H | idtac ]
  end.

Tactic Notation "hoare" "lift" constr(n) "pre" :=
  match goal with
    | |-  {| _, _, _, _, _, _ |} |- _ {{ _ //\\ _ }} _ {{ _ //\\ _ }} => 
      let s := fresh in
      let H := fresh in
      eapply backward_rule3;
       [ intros s H; sep lift n in H; exact H | idtac ]
    | |-  {| _, _, _, _, _, _ |} |- _ {{ _ }} _ {{ _ }} => 
      let s := fresh in
      let H := fresh in
      eapply backward_rule1;
       [ intros s H; sep lift n in H; exact H | idtac ]
  end.

Tactic Notation "hoare" "lifts" constr(l) "pre" :=
  match goal with
    | |-  {| _, _, _, _, _, _ |} |- _  {{ _ //\\ _ }} _ {{ _ //\\ _ }} => 
      let s := fresh in
      let H := fresh in
      eapply backward_rule3;
       [ intros s H; sep lifts l in H; exact H | idtac ]
    | |-  {| _, _, _, _, _,_ |} |- _ {{ _ }} _ {{ _ }} => 
      let s := fresh in
      let H := fresh in
      eapply backward_rule1;
       [ intros s H; sep lifts l in H; exact H | idtac ]
  end.

Tactic Notation "hoare" "lower" constr(n) "pre" :=
  match goal with
    | |-  {| _, _, _, _, _, _ |} |- _ {{ _ //\\ _ }} _ {{ _ //\\ _ }} => 
      let s := fresh in
      let H := fresh in
      eapply backward_rule3;
       [intros s H; sep lower n in H; exact H | idtac ]
    | |-  {| _, _, _, _, _, _ |} |- _ {{ _ }} _ {{ _ }} => 
      let s := fresh in
      let H := fresh in
      eapply backward_rule1;
       [intros s H; sep lower n in H; exact H | idtac ]
  end.

Tactic Notation "hoare" "rearr" "pre" "with" constr (l) :=
  match goal with
    | |-  {| _, _, _, _, _, _ |} |- _ {{ _ //\\ _ }} _ {{ _ //\\ _ }} => 
      let s := fresh in
      let H := fresh in
      eapply backward_rule3;
       [ intros s H; sep rearr in H with l; exact H | idtac ]
    | |-  {| _, _, _, _, _, _ |} |- _ {{ _ }} _ {{ _ }} => 
      let s := fresh in
      let H := fresh in
      eapply backward_rule1;
       [ intros s H; sep rearr in H with l; exact H | idtac ]
  end.

Ltac hoare_remember_pre l :=
  hoare lifts l pre;
  let x := constr:(length l) in
  let y := (eval compute in x) in
  let a := fresh in
  match goal with
    | |-  {| _, _, _, _, _, _ |} |- _ {{ ?P //\\ _ }} _ {{ _ //\\ _ }} =>
      match asrt_get_after_n P y with
        | @None => fail 1
        | Some ?P' => remember P' as a
      end      
    | |-  {| _, _, _, _, _, _ |} |- _ {{ ?P }} _ {{ _ }} => 
      match asrt_get_after_n P y with
        | @None => fail 1
        | Some ?P' => remember P' as a
      end   
  end.

Tactic Notation "hoare" "remember" constr(l) "pre" :=
  hoare_remember_pre l.

(** use consequence rule to change the post condition of a hoare triple *)

Tactic Notation "hoare" "normal" "post" :=
  match goal with
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ //\\ _ }} _ {{ _ //\\ _ }} =>
      let s := fresh in
      let H := fresh in
      eapply forward_rule3;
        [ intros s H; sep normal; exact H | idtac ]
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ }} _ {{ _ }} =>
      let s := fresh in
      let H := fresh in
      eapply forward_rule1;
        [ intros s H; sep normal; exact H | idtac ]
  end.

Tactic Notation "hoare" "lift" constr (n) "post" :=
  match goal with
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ //\\ _ }} _ {{ _ //\\ _ }} => 
      let s := fresh in
      let H := fresh in
      eapply forward_rule3;
       [ intros s H; sep lift n; exact H | idtac]
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ }} _ {{ _ }} => 
      let s := fresh in
      let H := fresh in
      eapply forward_rule1;
       [ intros s H; sep lift n; exact H | idtac]
  end.

Tactic Notation "hoare" "lifts" constr (l) "post" :=
  match goal with
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ //\\ _ }} _ {{ _ //\\ _ }} => 
      let s := fresh in
      let H := fresh in
      eapply forward_rule3;
       [ intros s H; sep lifts l; exact H | idtac]
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ }} _ {{ _ }} => 
      let s := fresh in
      let H := fresh in
      eapply forward_rule1;
       [ intros s H; sep lifts l; exact H | idtac]
  end.

Tactic Notation "hoare" "lower" constr (n) "post" :=
  match goal with
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ //\\ _ }} _ {{ _ //\\ _ }} => 
      let s := fresh in
      let H := fresh in
      eapply forward_rule3;
       [ intros s H; sep lower n; exact H | idtac]
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ }} _ {{ _ }} => 
      let s := fresh in
      let H := fresh in
      eapply forward_rule1;
       [ intros s H; sep lower n; exact H | idtac]
  end.

Tactic Notation "hoare" "rearr" "post" "with" constr (l):=
  match goal with
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ //\\ _ }} _ {{ _ //\\ _ }} => 
      let s := fresh in
      let H := fresh in
      eapply forward_rule3;
       [ intros s H; sep rearr with l; exact H | idtac]
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ }} _ {{ _ }} => 
      let s := fresh in
      let H := fresh in
      eapply forward_rule1;
       [ intros s H; sep rearr with l; exact H | idtac]
  end.

Ltac hoare_remember_post l :=
  hoare lifts l post;
  let x := constr:(length l) in
  let y := (eval compute in x) in
  let a := fresh in
  match goal with
    | |-  {| _, _, _, _, _, _ |} |- _ {{ _ //\\ _ }} _ {{ ?P //\\ _ }} =>
      match asrt_get_after_n P y with
        | @None => fail 1
        | Some ?P' => remember P' as a
      end      
    | |-  {| _, _, _, _, _, _ |} |- _ {{ _ }} _ {{ ?P }} => 
      match asrt_get_after_n P y with
        | @None => fail 1
        | Some ?P' => remember P' as a
      end   
  end.

Tactic Notation "hoare" "remember" constr (l) "post" :=
  hoare_remember_post l.
