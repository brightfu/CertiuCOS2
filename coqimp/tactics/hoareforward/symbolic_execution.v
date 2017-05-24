Require Import include_frm.
Require Import symbolic_lemmas.
Require Import sep_auto.

Ltac find_dom_lenv' Hp :=
  match Hp with
    | ?A ** ?B =>
      match find_dom_lenv' A with
        | (some ?a, Some ?l) => constr:(some a, Some l)
        | (none ?a, _) =>
          match find_dom_lenv' B with
            | (some ?b, Some ?l) => constr:(some (a + b)%nat, Some l)
            | (none ?b, _) => constr:(none (a + b)%nat, @None)
          end
      end
    | A_dom_lenv ?l => constr:(some 1%nat, Some l)
    | _ => constr:(none 1%nat, @None)
  end.

Ltac find_dom_lenv Hp :=
  let x := find_dom_lenv' Hp in
  eval compute in x.


Ltac find_ptrarray_by_block' Hp b :=
  match Hp with
    | ?A ** ?B =>
      match find_ptrarray_by_block' A b with
        | (some ?m) => constr:(some m)
        | (none ?m) =>
          match find_ptrarray_by_block' B b with
            | (some ?n) => constr:(some (m + n)%nat)
            | (none ?n) => constr:(none (m + n)%nat)
          end
      end
    | Aarray (b, _) _ _ => constr:(some 1%nat)
    | _ => constr:(none 1%nat)
  end.

Ltac find_ptrarray_by_block Hp b :=
  let x := find_ptrarray_by_block' Hp b in
  eval compute in x.


Import DeprecatedTactic.
Ltac sep_get_rv :=
  match goal with
    | |- _ |= Rv (ebinop ?bop ?e1 ?e2) @ _ == _ =>
      eapply bop_rv;
        [ sep_get_rv
        | sep_get_rv
        | simpl; auto
        | auto
        | simpl; auto ]

    | |- _ |= Rv (eunop ?uop ?e) @ _ == _ =>
      eapply uop_rv;
        [ sep_get_rv
        | simpl; auto
        | auto
        | simpl; auto ]

    | |- _ |= Rv (ecast _ (Tptr _)) @ _ == _ =>
      eapply cast_rv_ptr ; [sep_get_rv| simpl; eauto; tryfalse| intuition (try eexists; auto 1) ..]
      (* first [ eapply cast_rv_tptr ; [ sep_get_rv | simpl;eauto;tryfalse ]
       *       | eapply cast_rv_tnull; [ sep_get_rv | simpl;eauto;tryfalse ]
       *       | eapply cast_rv_struct_tptr; [ sep_get_rv | simpl;eauto;tryfalse ] ] *)
            
    | |- _ |= Rv (ecast _ (Tint8)) @ _ == _ =>
      eapply cast_rv_tint32_tint8 ; [ sep_get_rv | simpl;auto ]
                                      
    | |- _ |= Rv (ecast _ (Tint16)) @ _ == _ =>
              eapply cast_rv_tint8_tint16 ; [ sep_get_rv | simpl;auto ]

    | |- _ |= Rv (ederef _) @ _ == _ =>
      first [ eapply deref_rv;
              [ sep_get_rv
              | match goal with
                  | H : ?s |= ?P |- ?s |= PV ?l @ _ |=> _  @ _ ** _ =>
                    match find_ptrmapsto P l with
                      | (some ?n) => sep lift n in H; try exact H
                    end
                end 
              | simpl; auto ]
            | eapply deref_ptr_of_array_member_rv;
              [ sep_get_rv
              | match goal with
                  | H : ?s |= ?P |- ?s |= Aarray (?b, _) _ _ ** _ =>
                    match find_ptrarray_by_block P b with
                      | some ?n => sep lift n in H; try exact H
                    end
                end
              | match goal with |- ?t = Tarray _ _ => try unfold t; simpl; auto end
              | simpl; try omega
              | simpl; try omega
              | simpl; try omega
              | try omega
              | (*unfold Z.div; simpl;*) try (simpl typelen;simpl Z.of_nat); auto
              | try (simpl typelen;simpl Z.of_nat);try omega
              | simpl;try omega
              | try omega
              | auto
              | simpl; auto ] ]

    | H: ?s |= ?P |- ?s |= Rv (evar ?x) @ _ == _ =>
      match find_lvarmapsto P x with
        | some ?m =>
          eapply lvar_rv;
            [ sep lift m in H; exact H
            (*| auto*)
            | simpl; auto ]
        | none _ =>
          match find_dom_lenv P with
            | (none _, _) => fail 1
            | (some ?m, Some ?l) =>
              let ret1 := constr:(var_notin_dom x l) in
              let ret2 := (eval compute in ret1) in
              match ret2 with
                | true =>
                  match find_gvarmapsto P x with
                    | none _ => fail 2
                    | some ?n =>
                      eapply gvar_rv;
                        [ sep lifts (m::n::nil)%list in H; exact H
                        | simpl; auto
                        (*| auto*)
                        | simpl; auto ]
                  end
                | false => fail 3
              end
          end
      end
        
    | H: ?s |= ?P |- ?s |= Rv (efield (ederef (evar ?x)) _) @ _ == _ =>
      match find_lvarmapsto P x with
        | some ?m =>
          sep lift m in H;
            match type of H with
              | _ |= LV x @ Tptr _ |=> Vptr ?l @ _ ** ?P' =>
                match find_ptrstruct P' l with
                  | none _ => fail 1
                  | some ?n =>
                    sep lifts (1::(S n)::nil)%list in H;
                      eapply struct_member_rv_general_typeneq;
                      [ exact H
                      | (match goal with|- ?t' = Tstruct _ _ => try unfold t' end); auto
                      | (match goal with|- ?t' = Tstruct _ _ => try unfold t' end); auto
                      | simpl; auto
                      | simpl; auto
                      | simpl; auto
                      | unfold isarray_type;intros;mytac;
                        tryfalse;eexists;splits;auto
                      | unfold isarray_type;
                        let X:=fresh in intro X;
                                       try solve [ (destruct X;do 2 eexists;eauto) ]; 
                                       try
                                         (  
                                           eexists;splits;
                                           [ intros;auto 
                                           | unfold id_nth; simpl; auto 
                                           | simpl; try omega 
                                           | auto 
                                           | simpl;auto]
                                         )
                      ]
                end
            end
        | none _ =>
          match find_dom_lenv P with
            | (none _, _) => fail 2
            | (some ?m, Some ?ls) =>
              let ret1 := constr:(var_notin_dom x ls) in
              let ret2 := (eval compute in ret1) in
              match ret2 with
                | true =>
                  match find_gvarmapsto P x with
                    | none _ => fail 3
                    | some ?n =>
                      sep lifts (m::n::nil)%list in H;
                        match type of H with
                          | _ |= A_dom_lenv _ ** GV x @ Tptr _ |=> Vptr ?l @ _ ** ?P' =>
                            match find_ptrstruct P' l with
                              | none _ => fail 4
                              | some ?o =>
                                sep lifts (1::2::(S (S o))::nil)%list in H;
                                  eapply struct_member_rv_g_general_typeneq;
                                  [ exact H
                                  | simpl; auto
                                  | match goal with
                                    | |- ?t' = Tstruct _ _ =>
                                          try unfold t'
                                    end; eauto
                                  | match goal with
                                    | |- ?t' = Tstruct _ _  =>
                                          try unfold t'
                                    end; eauto
                                  | simpl; auto
                                  | simpl; auto
                                  | simpl; auto
                                  | unfold symbolic_lemmas.isarray_type;
                                     intros; DeprecatedTactic.mytac; tryfalse;
                                     eexists; splits; 
                                     auto
                                  | unfold symbolic_lemmas.isarray_type;
                                     (let X := fresh in
                                      intro X;
                                       try (solve
                                        [ destruct X; do 2 eexists; eauto   ]);
                                       try
                                        (eexists; splits;
                                         [ let Hx:=fresh in introv Hx; inversion Hx
                                          | unfold id_nth; simpl; auto
                                          | simpl; try omega
                                          | idtac  
                                          | simpl; auto ]))
                                  ]
                            end
                        end
                  end
                | false => fail 5
              end
          end
      end

    | H: ?s |= ?P |- ?s |= Rv (earrayelem (evar ?x) _) @ _ == _ =>
      match find_lvararray P x with
        | some ?m =>
          sep lift m in H;
            eapply array_member_rv;
            [ exact H
            | auto
            | sep_get_rv
            | intuition auto
            | simpl; try omega
            | simpl; try omega
            | simpl; try omega
            | auto
            | simpl; auto ]
        | none _ =>
          match find_dom_lenv P with
            | (none _, _) => fail 1
            | (some ?m, Some ?ls) =>
              let ret1 := constr:(var_notin_dom x ls) in
              let ret2 := (eval compute in ret1) in
              match ret2 with
                | true =>
                  match find_gvararray P x with
                    | none _ => fail 2
                    | some ?n =>
                      sep lifts (m::n::nil)%list in H;
                        eapply array_member_rv_g;
                        [ exact H
                        | simpl; auto
                        | auto
                        | sep_get_rv
                        | intuition auto
                        | intuition auto
                        | simpl; try omega
                        | simpl; try omega
                        | simpl; try omega
                        | auto
                        | simpl; auto ]
                  end
                | false => fail 3
              end
          end
      end

    | |- _ |= Rv (earrayelem _ _) @ _ == _ =>
            eapply expr_array_member_rv;
            [ 
              sep_get_rv;try solve [eauto;simpl;auto]
            | match goal with
                  | H : ?s |= ?P |- ?s |= Aarray ?l _ _ ** _ =>
                    match find_ptrarray P l with
                      | (some ?n) => sep lift n in H; try exact H
                      | _ => fail 4
                    end
                end 
            | sep_get_rv
            | intuition auto
            | intuition auto
            | simpl; try omega
            | simpl; try omega
            | simpl; try omega
            | auto
            | simpl; auto ]
              
    | |- _ |= Rv (eaddrof (ederef ?e)) @ _ == _ =>
      eapply addrof_deref_rv; sep_get_rv

    | |- _ |= Rv (eaddrof (earrayelem ?e1 ?e2)) @ _ == _ =>
      eapply addrof_array_elem_rv; 
        [ sep_get_rv 
        | sep_get_rv 
        | intuition auto 
        | intuition auto ]
    | |- _ |= Rv enull @ _ == _ =>
      apply null_rv
    | |- _ |= Rv econst32 _ @ _ == _ =>
      apply const_rv
 end.

Ltac sep_get_rv_in H :=
  let H' := fresh in
  let Hp := type of H in
  assert Hp as H' by exact H; clear H; rename H' into H;
  sep_get_rv.

Tactic Notation "sep" "get" "rv" := sep_get_rv.
Tactic Notation "sep" "get" "rv" "in" hyp (H) := sep_get_rv_in H.
 
Ltac symbolic_execution :=
  intros;
  match goal with
    |  H : ?s |= _ |- ?s  |= Rv enull @ _ == _ =>
       apply null_rv
    |  H : ?s |= _ |- ?s  |= Rv econst32 _ @ _ == _ =>
       apply const_rv
    | H : ?s |= _ |- ?s |= _ =>
      sep normal in H;
        sep destruct H;
        ssplit_apure_in H;
        subst;
        sep normal;
        sep eexists;
        sep get rv
    | |- ?s |= Rv _ @ _ == _ =>
      sep normal; sep eexists; sep get rv
  end.


Tactic Notation "symbolic" "execution" := symbolic_execution.

