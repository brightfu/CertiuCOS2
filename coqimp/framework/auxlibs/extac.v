(***************************************************************)
(* Coq code for PCAP                                           *)
(*                                                             *)
(* Tactics                                                     *)
(*                                                             *)
(*                                                             *)
(***************************************************************)

(* $Id: extac.v 21 2012-08-16 14:14:35Z guoyu $ *)

Tactic Notation "substH" hyp (H) :=
  match goal with
    | |- ?a -> ?b => clear H; intro H
    | |- _ => fail 1 "goal must be 'A -> B'."
  end.

Tactic Notation "substH" hyp (H) "with" constr (t) := 
  generalize t; clear H; intro H.

Tactic Notation "substH" hyp (H) "with" constr (t) "into" ident (Hn) := 
  generalize t; clear H; intro Hn.


Tactic Notation "destructH" hyp (H) "with" constr (t) :=
  destruct t; clear H.

Tactic Notation "destructH" hyp (H) "with" constr (t)
  "as" simple_intropattern (p) :=
  destruct t as p; clear H.

Tactic Notation "discri" :=
  match goal with
    | H : ?a <> ?a |- _ => 
      elimtype False; apply H; reflexivity
    | |- _ -> _ => intros; discriminate
    | H : False |- _ => destruct H
    | _ => discriminate
  end.

Tactic Notation "gen_clear" hyp (H) :=
  generalize H; clear H.

Tactic Notation "gen_clear" hyp (H1) hyp (H2) :=
  generalize H1 H2; clear H1 H2.

Tactic Notation "gen_clear" 
  hyp (H1) hyp (H2) hyp (H3) :=
  generalize H1 H2 H3; clear H1 H2 H3.

Tactic Notation "gen_clear" 
  hyp (H1) hyp (H2) hyp (H3) hyp (H4) :=
  generalize H1 H2 H3 H4; 
    clear H1 H2 H3 H4.

Tactic Notation "gen_clear" 
  hyp (H1) hyp (H2) hyp (H3) 
  hyp (H4) hyp (H5):=
  generalize H1 H2 H3 H4 H5; 
    clear H1 H2 H3 H4 H5.

Tactic Notation "gen_clear" 
  hyp (H1) hyp (H2) hyp (H3) 
  hyp (H4) hyp (H5) hyp (H6):=
  generalize H1 H2 H3 H4 H5 H6; 
    clear H1 H2 H3 H4 H5 H6.

Tactic Notation "split_l" :=
  split; [trivial | idtac].

Tactic Notation "split_r" :=
  split; [idtac | trivial ].

Tactic Notation "split_lr" :=
  split; [trivial | trivial ].

Tactic Notation "split_l" "with" constr (t) :=
  split; [apply t | idtac].

Tactic Notation "split_r" "with" constr (t) :=
  split; [idtac | apply t ].

Tactic Notation "split_l" "by" tactic (tac) :=
  split; [tac | idtac ].

Tactic Notation "split_r" "by" tactic (tac) :=
  split; [idtac | tac ].

Tactic Notation "split_l_clear" "with" hyp (H) :=
  split; [apply H | clear H].

Tactic Notation "split_r_clear" "with" hyp (H) :=
  split; [clear H | apply H ].

Tactic Notation "inj_hyp" hyp (H) :=
  injection H; clear H; intro H.

Tactic Notation "rew_clear" hyp (H) :=
  rewrite H; clear H.

Tactic Notation "injection" hyp (H) :=
  injection H.

Tactic Notation "injection" hyp (H) "as" 
  simple_intropattern (pat) :=
  injection H; intros pat.

