Require Import include_frm.
Require Import sep_auto.
Require Import hoare_conseq.
Require Import derived_rules.
Require Import symbolic_execution.
Require Import hoare_assign.

Set Implicit Arguments.


Lemma rvl_elim:forall s e el v vl t tl, 
        s |= Rv e @ t == v -> s|= Rvl el @ tl == vl ->
        s |= Rvl (e::el) @ (t::tl) == (v::vl).
Proof.
  intros.
  simpl in *.
  simpljoin;auto.
Qed.

 
Lemma rvl_nil: forall s,   s |= Rvl nil @ nil == nil.
  simpl.
  intros. auto.
Qed.


Ltac unfold_spec:=
  match goal with
    | H :_ |- ?s |= PRE 
               [?t,_,_,_] ** _ => unfold getasrt;unfold t
    | _ => idtac
  end;
  match goal with
    | H : _ |- ?s |= (?t _ _ _) ** _ => unfold t
    | _ => idtac
  end.

Ltac sep_unfold_funpre:=
  match goal with
    | H :_ |-  PRE 
               [?t,_,_,_] ==> _  => unfold getasrt;unfold t
    | _ => idtac
  end;
  match goal with
    | H : _ |-  (?t _ _ _) ==> _   => unfold t
    | _ => idtac
  end.



Ltac sep_unfold_funpost:=
  match goal with
    | |- EX _, POST [ ?x, _, _, _, _]  ==> _ =>
      unfold getasrt; unfold x;
      match goal with
        | |- EX _, ?t' _ _ _ _ ==> _ => unfold t'
      end
  end.

Ltac hoare_calle_lvar :=
  match goal with
    | |- {| _, _, ?li, _, _, _ |} |-?ct {{ ?P }} scalle (evar ?x) _ ?el {{ _ }} =>
      match find_aop P with 
        | some ?n =>  
          hoare lifts (n::nil)%nat pre; 
            eapply calle_rule_lvar'; 
            [ intuition eauto  | 
              intros; do 5 try 
                         (apply rvl_elim;[ symbolic_execution | ]);
              first [apply rvl_nil | simpl;auto] | 
              intros;  unfold_spec;sep pauto |
              idtac |
              idtac |
              simpl;eauto | 
              sep_unfold_funpost |
              sep_unfold_funpre 
              ]
        | none _ => idtac
      end
  end.


Ltac hoare_call :=
  match goal with
    | |- {| _, _, ?li, _, _, _ |} |- ?ct {{ ?P }} scall _ ?el {{ _ }} =>
      match find_aop P with 
        | some ?n =>  
              hoare lifts (n::nil)%nat pre; 
                eapply call_rule';
                [intuition eauto | 
                 intros; 
                    do 5 try (apply rvl_elim;[ symbolic_execution | ]);
                     first [apply rvl_nil | simpl;auto] |
                 intros;unfold_spec;sep pauto |
                 idtac |
                 sep_unfold_funpost |
                 sep_unfold_funpre |
                 simpl;eauto
                ] 
        | none _ => idtac
      end
  end.
