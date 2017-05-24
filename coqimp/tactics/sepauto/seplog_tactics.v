Require Import include_frm.
Require Import seplog_lemmas.
Require Export frmaop_sol.

Set Asymmetric Patterns.
Set Implicit Arguments.

Open Scope nat_scope.
(** unfold x *)

Tactic Notation "unfold1" constr (x) :=
  unfold x; fold x.
Tactic Notation "unfold1" constr (x) "in" hyp (Hp) :=
  unfold x in Hp; fold x in Hp.
Tactic Notation "unfold1" constr (x) "in" "*" :=
  unfold x in *; fold x in *.

(** * simpl sep lift, never fail *)

Ltac sassocr_in H :=
  match type of H with
    | _ |= (_ ** _) ** _ => apply astar_assoc_elim in H; sassocr_in H
    | _ => idtac
  end.
Ltac sassocl_in H :=
  match type of H with
    | _ |= _ ** (_ ** _) => apply astar_assoc_intro in H; sassocr_in H
    | _ => idtac
  end.
Ltac sassocr :=
  match goal with
    | |- _ |= (_ ** _) ** _ => apply astar_assoc_intro; sassocr
    | _ => idtac
  end.
Ltac sassocl :=
  match goal with
    | |- _ |= _ ** (_ ** _) => apply astar_assoc_elim; sassocl
    | _ => idtac
  end.
Ltac scomm_in H :=
  match type of H with
    | _ |= _ ** _ => apply astar_comm in H
    | _ => idtac
  end.
Ltac scomm :=
  match goal with
    | |- _ |= _ ** _ => apply astar_comm
    | _ => idtac
  end.

Tactic Notation "sep" "assocr" "in" hyp (H) :=
  sassocr_in H.
Tactic Notation "sep" "assocl" "in" hyp (H) :=
  sassocl_in H.
Tactic Notation "sep" "assocr" :=
  sassocr.
Tactic Notation "sep" "assocl" :=
  sassocl.
Tactic Notation "sep" "comm" "in" hyp (H) :=
  scomm_in H.
Tactic Notation "sep" "comm" :=
  scomm.

Ltac sliftn n :=
  match eval compute in n with
    | 0%nat => idtac
    | 1%nat => sep assocr
    | S ?n' => sep assocr; sep comm; sliftn n'
  end.
Ltac sliftn_in H n :=
  match eval compute in n with
    | 0%nat => idtac
    | 1%nat => sep assocr in H
    | S ?n' => sep assocr in H; sep comm in H; sliftn_in H n'
  end.


(** * find : Apure Aconj Aexist Assn *)

Inductive find {t:Type} : Type :=
| some : t -> find
| none : t -> find.

Definition myAconj := Aconj.

Inductive pattern : Type :=
| pattern_apure : pattern
| pattern_pure : pattern
| pattern_aconj : pattern
| pattern_adisj : pattern
| pattern_atrue : pattern
| pattern_aemp : pattern
| pattern_aexists : pattern
| pattern_ptrmapsto : pattern
| pattern_lvarmapsto : pattern
| pattern_gvarmapsto : pattern
                         (*
| pattern_ptrmapstor : pattern
| pattern_lvarmapstor : pattern
| pattern_gvarmapstor : pattern
| pattern_ptrmapstop : pattern
| pattern_lvarmapstop : pattern
| pattern_gvarmapstop : pattern*)
                         
| pattern_ptrstruct : pattern
| pattern_ptrarray : pattern
| pattern_lvararray : pattern
| pattern_gvararray : pattern
| pattern_aarray : pattern
| pattern_default : pattern
| pattern_absdata : pattern.


Ltac asrt_to_pattern Hp :=
  match Hp with
    | [| _ |] => constr:(pattern_apure)
    | Aie _ => constr:(pattern_pure)
    | Ais _ => constr:(pattern_pure)
    | ATopis _ => constr:(pattern_pure)
    | Aisr _ => constr:(pattern_pure)
    | Acs _ => constr:(pattern_pure)
    | A_dom_lenv _ => constr:(pattern_pure)
    | A_notin_lenv _ => constr:(pattern_pure)
    | Alvarenv _ _ _ => constr:(pattern_pure)
    | Agvarenv _ _ _ => constr:(pattern_pure)
    | <|| _ ||> => constr:(pattern_pure)
    | _ //\\ _ => constr:(pattern_aconj)
    | _ \\// _ => constr:(pattern_adisj)
    | Aemp => constr:(pattern_aemp)
    | Atrue => constr:(pattern_atrue)
    | Aexists _ => constr:(pattern_aexists)
(*    | PV ?l @ _ |-> _ => constr:(pattern_ptrmapsto, l)
    | LV ?x @ _ |-> _ => constr:(pattern_lvarmapsto, x)
    | GV ?x @ _ |-> _ => constr:(pattern_gvarmapsto, x)
    | PV ?l @ _ |-r-> _ => constr:(pattern_ptrmapstor, l)
    | LV ?x @ _ |-r-> _ => constr:(pattern_lvarmapstor, x)
    | GV ?x @ _ |-r-> _ => constr:(pattern_gvarmapstor, x) *)
    | PV ?l @ _ |=> _ @ _ => constr:(pattern_ptrmapsto, l)
    | LV ?x @ _ |=> _ @ _=> constr:(pattern_lvarmapsto, x)
    | GV ?x @ _ |=> _ @ _=> constr:(pattern_gvarmapsto, x)
    | Astruct ?l _ _ => constr:(pattern_ptrstruct, l)
    | Aarray ?l _ _ => constr:(pattern_ptrarray, l)
    | LAarray ?x _ _ => constr:(pattern_lvararray, x)
    | GAarray ?x _ _ => constr:(pattern_gvararray, x)
    | Aabsdata ?absid _ => constr:(pattern_absdata, absid)
    | _ => constr:(pattern_default, Hp)
  end.

Ltac find_match' Hp x :=
  match Hp with
    | ?A ** ?B => match find_match' A x with
                    | some ?a => constr:(some a)
                    | none ?a => match find_match' B x with
                                   | some ?b => constr:(some (a + b)%nat)
                                   | none ?b => constr:(none (a + b)%nat)
                                 end
                  end
    | ?A => match asrt_to_pattern A with
              | x => let b :=  asrt_to_pattern A in
                         match x with
                       | b => constr:(some 1%nat)
                       | _ => constr:(none 1%nat)
                     end
              | _ => constr:(none 1%nat)
            end
  end. 
Ltac find_match Hp x :=
  let y := find_match' Hp x in
  eval compute in y.

Ltac find_match_all Hp A :=
  let x := asrt_to_pattern A in
  find_match Hp x.

Ltac find_apure Hp := find_match Hp pattern_apure.

Ltac find_pure Hp := find_match Hp pattern_pure.

Ltac find_aconj Hp := find_match Hp pattern_aconj.

Ltac find_aemp Hp := find_match Hp pattern_aemp.

Ltac find_aexists Hp := find_match Hp pattern_aexists.

Ltac find_ptrmapsto Hp l := find_match Hp (pattern_ptrmapsto, l).

Ltac find_lvarmapsto Hp x := find_match Hp (pattern_lvarmapsto, x).

Ltac find_gvarmapsto Hp x := find_match Hp (pattern_gvarmapsto, x).
(*
Ltac find_ptrmapstor Hp l := find_match Hp (pattern_ptrmapstor, l).

Ltac find_lvarmapstor Hp x := find_match Hp (pattern_lvarmapstor, x).

Ltac find_gvarmapstor Hp x := find_match Hp (pattern_gvarmapstor, x).

Ltac find_ptrmapstop Hp l := find_match Hp (pattern_ptrmapstop, l).

Ltac find_lvarmapstop Hp x := find_match Hp (pattern_lvarmapstop, x).

Ltac find_gvarmapstop Hp x := find_match Hp (pattern_gvarmapstop, x).
*)
Ltac find_ptrstruct Hp l := find_match Hp (pattern_ptrstruct, l).

Ltac find_ptrarray Hp l := find_match Hp (pattern_ptrarray, l).

Ltac find_lvararray Hp x := find_match Hp (pattern_lvararray, x).

Ltac find_gvararray Hp x := find_match Hp (pattern_gvararray, x).




(** * scancel *)

Inductive asrtTree : Type :=
| empTree : asrtTree
| trueTree : asrtTree
| starTree : asrtTree -> asrtTree -> asrtTree
| pureTree : Prop -> asrtTree
| baseTree : asrt -> asrtTree.

Ltac toTree Hp :=
  match Hp with
    | ?A ** ?B => let tA := toTree A in
                  let tB := toTree B in
                  constr:(starTree tA tB)
    | Aemp => constr:(empTree)
    | Atrue => constr:(trueTree)
    | [| ?P |] => constr:(pureTree P)
    | _ => constr:(baseTree Hp)
  end.

Fixpoint unTree (t:asrtTree) : asrt :=
  match t with
    | empTree => Aemp
    | trueTree => Atrue
    | starTree A B => unTree A ** unTree B
    | pureTree P => [| P |]
    | baseTree A => A
  end.

Fixpoint asrtTree_to_list' (Hp:asrtTree) (l:list asrtTree) : list asrtTree :=
  match Hp with
    | starTree A B => asrtTree_to_list' A (asrtTree_to_list' B l)
    | _ => Hp::l
  end.
Definition asrtTree_to_list (Hp:asrtTree) : list asrtTree :=
  asrtTree_to_list' Hp nil.

Ltac asrt_to_list' Hp l :=
  match Hp with
    | ?A ** ?B => let rl := asrt_to_list' B l in
                  asrt_to_list' A rl
    | ?A => constr:(A :: l)
  end.
Ltac asrt_to_list Hp := asrt_to_list' Hp (@nil asrt).

Ltac search_match' lg Hp n :=
  match lg with
    | nil => constr:(@None)
    | ?a :: ?lg' => 
      match asrt_to_pattern a with
        | pattern_apure => search_match' lg' Hp (S n)
        | pattern_pure => search_match' lg' Hp (S n)
        | _ => match find_match_all Hp a with
                 | some ?m => constr:(Some (m,n))
                 | _ => search_match' lg' Hp (S n)
               end
      end
  end.
Ltac search_match G Hp :=
  let lg := asrt_to_list G in
  let x := search_match' lg Hp 1 in
  eval compute in x.


Ltac scancel' :=
  sliftn 1;
  let s' := fresh in
  let H' := fresh in
  match goal with
    | H : ?s |= ?X |- ?s |= ?Y =>
      try solve [ exact H | apply atrue_intro ];
      match X with
        | ?A ** ?B =>
          match Y with
            | A ** ?D =>
              apply astar_mono with (P:=A) (Q:=B);
                [intros s' H'; exact H' | idtac | exact H];
                first [ clear s H; intros s H 
                      | clear H; first [intros s' H | intros H]];
                sliftn_in H 1; scancel'
            | ?C ** ?D =>
              match find_match_all B C with
                | some ?n => sliftn_in H (S n); scancel'
                | none _ => match search_match D (A ** B) with
                              | Some (_, ?m) => sliftn (S m); scancel'
                              | @None => idtac
                            end
              end
            | A => apply astar_r_aemp_elim; scancel'
            | ?C => match find_match_all B C with
                      | some ?n => sliftn_in H (S n); scancel'
                      | none _ => idtac
                    end
          end
        | ?A =>
          match Y with
            | A ** ?C => apply astar_r_aemp_intro in H; scancel'
            | ?B ** ?C => match find_match_all C A with
                           | some ?n => sliftn (S n); scancel'
                           | _ => idtac
                         end
            | ?B => idtac
          end
      end
    | H : (_,_,?m,_,_,?O,_) |= ?X |- (_,_,?m,_,_,?O,_) |= ?Y =>
      try solve [ exact H | apply atrue_intro ];
      match X with
        | ?A ** ?B =>
          match Y with
            | A ** ?D =>
              generalize dependent H;
                apply cancellation_rule;
                [ sliftn_in H 1; scancel'
                | simpl; auto ]
            | ?C ** ?D =>
              match find_match_all B C with
                | some ?n => sliftn_in H (S n); scancel'
                | none _ => match search_match D (A ** B) with
                              | Some (_, ?m) => sliftn (S m); scancel'
                              | @None => idtac
                            end
              end
            | A => apply astar_r_aemp_elim; scancel'
            | ?C => match find_match_all B C with
                      | some ?n => sliftn_in H (S n); scancel'
                      | none _ => idtac
                    end
          end
        | ?A =>
          match Y with
            | A ** ?C => apply astar_r_aemp_intro in H; scancel'
            | ?B ** ?C => match find_match_all C A with
                           | some ?n => sliftn (S n); scancel'
                           | _ => idtac
                         end
            | ?B => idtac
          end
      end
    | _ => fail
  end.

Ltac sclearemp_in H :=
  match type of H with
    | _ |= ?A => match find_aemp A with
                    | some ?n => sliftn_in H n;
                                match type of H with
                                  | Aemp ** _ =>
                                    apply astar_l_aemp_elim in H; sclearemp_in H
                                  | Aemp => idtac
                                end
                    | _ => idtac
                  end
    | _ => fail
  end.

Ltac sclearemp :=
  match goal with
    | |- _ |= ?A => match find_aemp A with
                       | some ?n => sliftn n;
                                   match goal with
                                     | |- _ |= Aemp **_ =>
                                       apply astar_l_aemp_intro; sclearemp
                                     | |- _ |= Aemp => idtac
                                   end
                       | _ => idtac
                     end
    | _ => fail
  end.

Ltac scancel :=
  match goal with
    | H : ?s |= _ |- ?s |= _ =>
      sliftn_in H 1; scancel';
      match goal with
        | |- _ |= _ => sclearemp_in H; sclearemp
        | _ => idtac
      end
    | H : (_,_,?m,_,_,?O,_) |= _ |- (_,_,?m,_,_,?O,_) |= _ =>
      sliftn_in H 1; scancel';
      match goal with
        | |- _ |= _ => sclearemp_in H; sclearemp
        | _ => idtac
      end
    | _ => idtac
  end.

Ltac scancel_with H :=
  let H' := fresh in
  let typeH := type of H in
  assert typeH as H' by exact H; clear H;
  rename H' into H; scancel.


(** * sep simpl && sep lift *)

Fixpoint myAppAsrtTree (l m : list asrtTree) : list asrtTree :=
  match l with
    | nil => m
    | a :: l' => a :: (myAppAsrtTree l' m)
  end.


Fixpoint list_to_asrtTree (l:list asrtTree) : asrtTree :=
  match l with
    | nil => empTree
    | A::nil => A
    | empTree::l' => list_to_asrtTree l'
    | A::l' => starTree A (list_to_asrtTree l')
  end.

Fixpoint list_to_asrtTree_simpl (l:list asrtTree) : asrtTree :=
  match l with
    | nil => empTree
    | A::nil => A
    | A::l' => starTree A (list_to_asrtTree_simpl l')
  end.

Ltac list_to_asrt l :=
  match l with
    | nil => fail 1 "in list_to_asrt l, l should not be nil"
    | ?A :: nil => constr:(A)
    | Aemp :: ?l' => list_to_asrt l'
    | ?A :: ?l' => let ar := list_to_asrt l' in
                   constr:(A ** ar)
  end.

Ltac list_to_asrt_simpl l :=
  match l with
    | nil => fail 1 "in list_to_asrt l, l should not be nil"
    | ?A :: nil => constr:(A)
    | ?A :: ?l' => let ar := list_to_asrt_simpl l' in
                   constr:(A ** ar)
  end.

Fixpoint listsimplA (l:list asrtTree) (b:bool) : list asrtTree * bool :=
  match l with
    | nil => (nil, b)
    | h::t => match h with
                | trueTree => listsimplA t true
                | _ => let (l',b') := listsimplA t b in
                       (h::l',b')
              end
  end.

Definition listsimplB (lb : list asrtTree * bool) : list asrtTree :=
  let (l,b) := lb in
  if b then myAppAsrtTree l (trueTree::nil) else l.

Definition listsimpl (l:list asrtTree) : list asrtTree :=
  listsimplB (listsimplA l false).

Lemma myAppAsrtTree_nil_r :
  forall l : list asrtTree,
    myAppAsrtTree l nil = l.
Proof.
  induction l; intros; simpl.
  auto.
  rewrite IHl; auto.
Qed.

Lemma myAppAsrtTree_assoc :
  forall (l m n : list asrtTree),
    myAppAsrtTree l (myAppAsrtTree m n) = myAppAsrtTree (myAppAsrtTree l m) n. 
Proof.
  induction l; intros; simpl.
  auto.
  rewrite IHl; auto.
Qed.

Lemma asrtTree_to_list_prop1 :
  forall t l,
    myAppAsrtTree (asrtTree_to_list' t nil) l = asrtTree_to_list' t l.
Proof.
  induction t; induction l; intros;
  try solve [simpl asrtTree_to_list' in *; simpl myAppAsrtTree in *; auto].
  rewrite myAppAsrtTree_nil_r; auto.
  unfold asrtTree_to_list' at 2; fold asrtTree_to_list'.
  rewrite <- IHt2.
  rewrite <- IHt1.
  unfold asrtTree_to_list' at 1; fold asrtTree_to_list'.
  rewrite <- IHt1.
  rewrite myAppAsrtTree_assoc; auto.
Qed.

Lemma asrtTree_to_list_prop2 :
  forall t1 t2,
    myAppAsrtTree (asrtTree_to_list' t1 nil) (asrtTree_to_list' t2 nil) = asrtTree_to_list' t1 (asrtTree_to_list' t2 nil). 
Proof.
  induction t1; induction t2; intros;
  try solve [ simpl asrtTree_to_list' in *; simpl myAppAsrtTree in *; auto
            | rewrite asrtTree_to_list_prop1; auto].
Qed.

Lemma list_to_asrtTree_prop1 :
  forall a l,
    unTree a ** unTree (list_to_asrtTree l) <==> unTree (list_to_asrtTree (a::l)).
Proof.
  split; intros;
  induction a; induction l;
  simpl list_to_asrtTree in *; simpl unTree in *; try solve [scancel].
Qed.

Lemma list_to_asrtTree_simpl_prop1 :
  forall a l,
    unTree a ** unTree (list_to_asrtTree_simpl l) <==> unTree (list_to_asrtTree_simpl (a::l)).
Proof.
  split; intros;
  induction a; induction l;
  simpl list_to_asrtTree_simpl in *; simpl unTree in *; try solve [scancel].
Qed.

Lemma list_to_asrtTree_prop2 :
  forall l1 l2,
    unTree (list_to_asrtTree l1) ** unTree (list_to_asrtTree l2) <==> unTree (list_to_asrtTree (myAppAsrtTree l1 l2)).
Proof.
  induction l1; induction l2; split; intros; simpl myAppAsrtTree in *.
  simpl list_to_asrtTree in *; simpl unTree in *.
  scancel.
  simpl list_to_asrtTree in *; simpl unTree in *.
  scancel.  
  unfold list_to_asrtTree in H at 1; simpl unTree in H at 1.
  scancel.
  unfold list_to_asrtTree at 1; simpl unTree at 1.
  scancel.
  rewrite myAppAsrtTree_nil_r; unfold list_to_asrtTree in H at 2; simpl unTree in H at 2.
  scancel.
  rewrite myAppAsrtTree_nil_r in H; unfold list_to_asrtTree at 2; simpl unTree at 2.
  scancel.
  eapply astar_mono in H.
  2 : apply list_to_asrtTree_prop1.
  2 : let H' := fresh in intros ? H'; apply H'.
  apply list_to_asrtTree_prop1.
  scancel.
  apply IHl1; auto.
  eapply astar_mono.
  apply list_to_asrtTree_prop1.
  let H' := fresh in intros ? H'; apply H'.
  apply list_to_asrtTree_prop1 in H.
  scancel.
  apply IHl1; auto.
Qed.

Lemma list_to_asrtTree_simpl_prop2 :
  forall l1 l2,
    unTree (list_to_asrtTree_simpl l1) ** unTree (list_to_asrtTree_simpl l2) <==> unTree (list_to_asrtTree_simpl (myAppAsrtTree l1 l2)).
Proof.
  induction l1; induction l2; split; intros; simpl myAppAsrtTree in *.
  simpl list_to_asrtTree_simpl in *; simpl unTree in *.
  scancel.
  simpl list_to_asrtTree_simpl in *; simpl unTree in *.
  scancel.  
  unfold list_to_asrtTree_simpl in H at 1; simpl unTree in H at 1.
  scancel.
  unfold list_to_asrtTree_simpl at 1; simpl unTree at 1.
  scancel.
  rewrite myAppAsrtTree_nil_r; unfold list_to_asrtTree_simpl in H at 2; simpl unTree in H at 2.
  scancel.
  rewrite myAppAsrtTree_nil_r in H; unfold list_to_asrtTree_simpl at 2; simpl unTree at 2.
  scancel.
  eapply astar_mono in H.
  2 : apply list_to_asrtTree_simpl_prop1.
  2 : let H' := fresh in intros ? H'; apply H'.
  apply list_to_asrtTree_simpl_prop1.
  scancel.
  apply IHl1; auto.
  eapply astar_mono.
  apply list_to_asrtTree_simpl_prop1.
  let H' := fresh in intros ? H'; apply H'.
  apply list_to_asrtTree_simpl_prop1 in H.
  scancel.
  apply IHl1; auto.
Qed.

Lemma myAppAsrtTree_true_r :
  forall l : list asrtTree,
    unTree (list_to_asrtTree (myAppAsrtTree l (trueTree::nil))) 
    <==>
    unTree (list_to_asrtTree l) ** Atrue.
Proof.
  split; intros.
  generalize dependent s.
  induction  l; intros.
  simpl myAppAsrtTree in H.
  simpl list_to_asrtTree in *.
  simpl unTree in *.
  scancel.
  simpl myAppAsrtTree in H.
  apply list_to_asrtTree_prop1 in H.
  eapply astar_mono in H.
  2 : intros ? H'; exact H'.
  2 : apply IHl.
  eapply astar_mono.
  apply list_to_asrtTree_prop1.
  intros ? H'; exact H'.
  scancel.
  generalize dependent s.
  induction l; intros.
  simpl myAppAsrtTree.
  simpl list_to_asrtTree in *.
  simpl unTree in *.
  scancel.
  simpl myAppAsrtTree.
  apply list_to_asrtTree_prop1.
  eapply astar_mono.
  intros ? H'; exact H'.
  apply IHl.
  eapply astar_mono in H.
  2 : apply list_to_asrtTree_prop1.
  2 : intros ? H'; exact H'.
  scancel.
Qed.

Theorem ssimplE' :
  forall t:asrtTree,
    unTree t ==> unTree (list_to_asrtTree (asrtTree_to_list t)).
Proof.
  induction t; intros; try solve [simpl in *; intuition].
  unfold1 unTree in H.
  eapply astar_mono in H; [idtac | apply IHt1 | apply IHt2].
  unfold asrtTree_to_list in *.
  unfold1 asrtTree_to_list'.
  rewrite <- asrtTree_to_list_prop2.
  apply list_to_asrtTree_prop2; auto.
Qed.

Theorem ssimplI' :
  forall t:asrtTree,
    unTree (list_to_asrtTree (asrtTree_to_list t)) ==> unTree t.
Proof.
  induction t; intros; try solve [simpl in *; intuition].
  unfold1 unTree.
  eapply astar_mono; [apply IHt1 | apply IHt2 | idtac].
  unfold asrtTree_to_list in *.
  unfold1 asrtTree_to_list' in H.
  rewrite <- asrtTree_to_list_prop2 in H.
  apply list_to_asrtTree_prop2; auto.
Qed.

Theorem ssimplE_simpl :
  forall t:asrtTree,
    unTree t ==> unTree (list_to_asrtTree_simpl (asrtTree_to_list t)).
Proof.
  induction t; intros; try solve [simpl in *; intuition].
  unfold1 unTree in H.
  eapply astar_mono in H; [idtac | apply IHt1 | apply IHt2].
  unfold asrtTree_to_list in *.
  unfold1 asrtTree_to_list'.
  rewrite <- asrtTree_to_list_prop2.
  apply list_to_asrtTree_simpl_prop2; auto.
Qed.

Theorem ssimplI_simpl :
  forall t:asrtTree,
    unTree (list_to_asrtTree_simpl (asrtTree_to_list t)) ==> unTree t.
Proof.
  induction t; intros; try solve [simpl in *; intuition].
  unfold1 unTree.
  eapply astar_mono; [apply IHt1 | apply IHt2 | idtac].
  unfold asrtTree_to_list in *.
  unfold1 asrtTree_to_list' in H.
  rewrite <- asrtTree_to_list_prop2 in H.
  apply list_to_asrtTree_simpl_prop2; auto.
Qed.

Lemma listsimplA_prop :
  forall l,
    listsimplA l true = let (l',_) := listsimplA l false in
                        (l',true).
Proof.
  induction l; intros.
  simpl; auto.
  destruct a;
    simpl; rewrite IHl;
    destruct (listsimplA l false); auto.
Qed.

Lemma list_to_asrtTree_listsimpl :
  forall a l,
    unTree (list_to_asrtTree (listsimpl (a::l)))
    <==>
    unTree a ** unTree (list_to_asrtTree (listsimpl l)).
Proof.
  intros.
  destruct a;
    unfold listsimpl;
    simpl listsimplA.
  
  destruct (listsimplA l false);
    simpl listsimplB.
  destruct b;
    simpl list_to_asrtTree.
  destruct (myAppAsrtTree l0 (trueTree::nil)).
  simpl list_to_asrtTree; simpl unTree; split; intros; scancel.
  simpl unTree at 2; split; intros; scancel.
  destruct l0.
  simpl list_to_asrtTree; simpl unTree; split; intros; scancel.
  simpl unTree at 2; split; intros; scancel.
  
  rewrite listsimplA_prop.
  destruct (listsimplA l false).
  simpl listsimplB.
  destruct b.
  split; intros.
  apply myAppAsrtTree_true_r in H.
  eapply astar_mono.
  intros ? H'; exact H'.
  apply myAppAsrtTree_true_r.
  simpl unTree at 1.
  sliftn 2.
  eapply astar_mono.
  intros ? H'; exact H'.
  apply astar_2atrue_intro.
  scancel.
  apply myAppAsrtTree_true_r.
  eapply astar_mono in H.
  2 : intros ? H'; exact H'.
  2 : apply myAppAsrtTree_true_r.
  simpl unTree at 1 in H.
  sliftn_in H 2.
  eapply astar_mono in H.
  2 : intros ? H'; exact H'.
  2 : apply astar_2atrue_elim.
  scancel.
  split; intros.
  apply myAppAsrtTree_true_r in H.
  simpl unTree at 1.
  scancel.
  apply myAppAsrtTree_true_r.
  simpl unTree at 1 in H.
  scancel.

  destruct (listsimplA l false);
    simpl listsimplB.
  destruct b;
    simpl list_to_asrtTree.
  destruct (myAppAsrtTree l0 (trueTree::nil)).
  simpl list_to_asrtTree;
    simpl unTree at 3.
  split; intros; scancel.
  unfold1 unTree.
  split; intros; scancel.
  destruct l0.
  simpl list_to_asrtTree;
    simpl unTree at 3.
  split; intros; scancel.
  unfold1 unTree.
  split; intros; scancel.

  destruct (listsimplA l false);
    simpl listsimplB.
  destruct b;
    simpl list_to_asrtTree.
  destruct (myAppAsrtTree l0 (trueTree::nil)).
  simpl list_to_asrtTree;
    simpl unTree at 3.
  split; intros; scancel.
  unfold1 unTree.
  split; intros; scancel.
  destruct l0.
  simpl list_to_asrtTree;
    simpl unTree at 3.
  split; intros; scancel.
  unfold1 unTree.
  split; intros; scancel.

  destruct (listsimplA l false);
    simpl listsimplB.
  destruct b;
    simpl list_to_asrtTree.
  destruct (myAppAsrtTree l0 (trueTree::nil)).
  simpl list_to_asrtTree;
    simpl unTree at 3.
  split; intros; scancel.
  unfold1 unTree.
  split; intros; scancel.
  destruct l0.
  simpl list_to_asrtTree;
    simpl unTree at 3.
  split; intros; scancel.
  unfold1 unTree.
  split; intros; scancel.
Qed.

Theorem listsimpl_prop :
  forall l,
    unTree (list_to_asrtTree l) <==> unTree (list_to_asrtTree (listsimpl l)).
Proof.
  split; intros.
  generalize dependent s.
  induction l; intros.
  unfold listsimpl in *; simpl listsimplA in *; simpl listsimplB in *.
  auto.
  apply list_to_asrtTree_prop1 in H.
  eapply astar_mono in H.
  2 : intros ? H'; exact H'.
  2 : apply IHl.
  apply list_to_asrtTree_listsimpl.
  scancel.
  generalize dependent s.
  induction l; intros.
  unfold listsimpl in *; simpl listsimplA in *; simpl listsimplB in *.
  auto.
  apply list_to_asrtTree_prop1.
  eapply astar_mono.
  intros ? H'; exact H'.
  apply IHl.
  apply list_to_asrtTree_listsimpl.
  auto.
Qed.

Theorem ssimplE :
  forall t : asrtTree,
    unTree t ==> unTree (list_to_asrtTree (listsimpl (asrtTree_to_list t))).
Proof.
  intros.
  apply ssimplE' in H.
  apply listsimpl_prop in H.
  auto.
Qed.

Theorem ssimplI :
  forall t : asrtTree,
    unTree (list_to_asrtTree (listsimpl (asrtTree_to_list t))) ==> unTree t.
Proof.
  intros.
  apply ssimplI'.
  apply listsimpl_prop. 
  auto.
Qed.

(** * sep lift *)

Fixpoint listliftn' (ll rl:list asrtTree) (n:nat) :=
  match rl with
    | nil => ll
    | a::rl' => match n with
                  | 0%nat => a::(myAppAsrtTree ll rl')
                  | S n' => listliftn' (myAppAsrtTree ll (a::nil)) rl' n'
              end
  end.

Definition listliftn l n := listliftn' nil l n. 

Fixpoint list_insert (l:list asrtTree) (a:asrtTree) (n:nat) : list asrtTree :=
  match l with
    | nil => a::nil
    | b::l' => match n with
                 | 0%nat => a::b::l'
                 | S n' => b::(list_insert l' a n')
               end
  end. 

Inductive listeq : list asrtTree -> list asrtTree -> Prop :=
| emptylisteq : listeq nil nil
| nonemptylisteq : forall l1 l2 a m n,
                     listeq l1 l2 -> listeq (list_insert l1 a m) (list_insert l2 a n). 


Lemma unTree_prop1 :
  forall a l n,
    unTree (list_to_asrtTree_simpl (a::l)) <==> unTree (list_to_asrtTree_simpl (list_insert l a n)).
Proof.
  induction l; induction n; intros;
  try solve [split; induction a; simpl; auto].
  split; intros.
  unfold1 list_insert.
  apply list_to_asrtTree_simpl_prop1 in H.
  apply list_to_asrtTree_simpl_prop1.
  eapply astar_mono in H.
  2 : let H' := fresh in intros ? H'; apply H'.
  2 : apply list_to_asrtTree_simpl_prop1.
  scancel.
  sep comm in H.
  apply list_to_asrtTree_simpl_prop1 in H.
  apply IHl; auto.
  unfold1 list_insert in H.
  apply list_to_asrtTree_simpl_prop1.
  apply list_to_asrtTree_simpl_prop1 in H.
  eapply astar_mono.
  let H' := fresh in intros ? H'; apply H'.
  apply list_to_asrtTree_simpl_prop1.
  scancel.
  sep comm.
  apply list_to_asrtTree_simpl_prop1.
  apply IHl in H; auto.
Qed.

Theorem unTree_prop2 :
  forall l1 l2,
    listeq l1 l2 -> unTree (list_to_asrtTree_simpl l1) <==> unTree (list_to_asrtTree_simpl l2).
Proof.
  intros.
  generalize dependent s.
  induction H; intros.
  split; auto.
  split; intros.
  apply unTree_prop1 in H0.
  apply list_to_asrtTree_simpl_prop1 in H0.
  apply unTree_prop1.
  apply list_to_asrtTree_simpl_prop1.
  scancel.
  apply IHlisteq; auto.
  apply unTree_prop1 in H0.
  apply list_to_asrtTree_simpl_prop1 in H0.
  apply unTree_prop1.
  apply list_to_asrtTree_simpl_prop1.
  scancel.
  apply IHlisteq; auto.
Qed.

Lemma list_insert_prop1 :
  forall l a, list_insert l a 0 = a::l.
Proof.
  induction l; intros;
  simpl; auto.
Qed.

Lemma listeq_prop1 :
  forall l, listeq l l.
Proof.
  induction l; intros.
  constructor.
  apply nonemptylisteq with (a:=a) (m:=0) (n:=0) in IHl.
  rewrite list_insert_prop1 in IHl; auto.
Qed.

Lemma list_liftn_prop1 :
  forall l1 l2 a n,
    exists m, list_insert (listliftn' l1 l2 n) a m = listliftn' (a::l1) l2 n.
Proof.  
  intros l1 l2.
  generalize dependent l1.
  induction l2; intros.
  simpl.
  exists 0; rewrite list_insert_prop1; auto.
  destruct n.
  simpl listliftn' at 2.
  exists 1.
  simpl.
  rewrite list_insert_prop1; auto.
  simpl.
  apply IHl2.
Qed.

Lemma listeq_liftn :
  forall l n,
    listeq (listliftn l n) l.
Proof.
  unfold listliftn; induction l; intros.
  simpl.
  constructor.
  induction n.
  simpl.
  apply listeq_prop1.
  simpl.
  replace (a::l) with (list_insert l a 0).
  2 : apply list_insert_prop1.
  pose (list_liftn_prop1 nil l a n).
  destruct e.
  rewrite <- H.
  constructor.
  apply IHl.
Qed.

Lemma listeq_comm :
  forall l1 l2,
    listeq l1 l2 -> listeq l2 l1.
Proof.
  intros.
  induction H; constructor.
  auto.
Qed.

Theorem slift :
  forall l n,
    unTree (list_to_asrtTree_simpl l) <==> unTree (list_to_asrtTree_simpl (listliftn l n)).
Proof.
  intros.
  symmetry.
  apply unTree_prop2.
  apply listeq_liftn.
Qed.

Theorem sliftE :
  forall t n,
    unTree t ==> unTree (list_to_asrtTree_simpl (listliftn (asrtTree_to_list t) n)).
Proof.
  intros.
  apply slift.
  apply ssimplE_simpl.
  auto.
Qed.

Theorem sliftI :
  forall t n,
    unTree (list_to_asrtTree_simpl (listliftn (asrtTree_to_list t) n)) ==> unTree t.
Proof.
  intros.
  apply ssimplI_simpl.
  eapply slift.
  eauto.
Qed.

Theorem sliftE' :
  forall t n P,
    unTree t //\\ P ==> unTree (list_to_asrtTree_simpl (listliftn (asrtTree_to_list t) n)) //\\ P.
Proof.
  intros t n P.
  apply aconj_mono; [ apply sliftE | auto ].
Qed.

Theorem sliftI' :
  forall t n P,
    unTree (list_to_asrtTree_simpl (listliftn (asrtTree_to_list t) n)) //\\ P ==> unTree t //\\ P.
Proof.
  intros t n P.
  apply aconj_mono; [ apply sliftI | auto ].
Qed.

Ltac sepliftn_in' H n :=
  match n with
    | 0%nat => idtac 1 "n starts from 1, not 0"; fail 1
    | S ?n' =>
      let H' := fresh in
      match type of H with
        | _ |= ?A //\\ _ => 
          let t := toTree A in
          pose (H' := sliftE' t n');
            cbv [asrtTree_to_list asrtTree_to_list' listliftn listliftn'
                 myAppAsrtTree list_to_asrtTree_simpl unTree] in H';
            apply H' in H; clear H'
        | _ |= ?A => 
          let t := toTree A in
          pose (H' := sliftE t n');
            cbv [asrtTree_to_list asrtTree_to_list' listliftn listliftn'
                 myAppAsrtTree list_to_asrtTree_simpl unTree] in H';
            apply H' in H; clear H'
      end
    | _ => idtac 2 "type of n should be nat"; fail 2
  end.

Ltac sepliftn_in'' H n :=
  let H' := fresh in
  match type of H with
    | _ |= EX _, _ =>
      eapply aexists_prop in H;
        [idtac | intros ? H'; try progress sepliftn_in'' H' n; exact H']
    | _ |= _ => try progress sepliftn_in' H n
  end.

Ltac sepliftn_in H n :=
  try progress sepliftn_in'' H n; cbv beta in H.

Ltac sepliftn' n :=
  match n with
    | 0%nat => fail 1 "n starts from 1, not 0"; fail 1
    | S ?n' =>
      let H := fresh in
      match goal with
        | |- _ |= ?A //\\ _ =>
          let t := toTree A in
          pose (H := sliftI' t n');
            cbv [asrtTree_to_list asrtTree_to_list' listliftn listliftn' myAppAsrtTree list_to_asrtTree_simpl unTree] in H;
            apply H; clear H
        | |- _ |= ?A =>
          let t := toTree A in
          pose (H := sliftI t n');
            cbv [asrtTree_to_list asrtTree_to_list' listliftn listliftn' myAppAsrtTree list_to_asrtTree_simpl unTree] in H;
            apply H; clear H
      end
    | _ => fail 2 "type of n should be nat"; fail 2
  end.

Ltac sepliftn'' n :=
  let H := fresh in
  match goal with
    | |- _ |= EX _ , _ =>
      eapply aexists_prop;
        [intros ? H; try progress sepliftn'' n; exact H | idtac]
    | |- _ |= _ => try progress sepliftn' n
    | _ => fail
  end.

Ltac sepliftn n :=
  try progress sepliftn'' n; cbv beta.

Ltac sclearemp_in H ::=
  match type of H with
    | _ |= Aemp ** _ => apply astar_l_aemp_elim in H; sclearemp_in H
    | _ |= Aemp => idtac
    | _ |= ?A => match find_aemp A with
                    | some ?n => sepliftn_in H n;
                                 sclearemp_in H
                    | _ => idtac
                  end
  end.

Ltac sclearemp ::=
  match goal with
    | |- _ |= Aemp ** _ => apply astar_l_aemp_intro; sclearemp
    | |- _ |= Aemp => idtac
    | |- _ |= ?A => match find_aemp A with
                       | some ?n => sepliftn n;
                                   sclearemp
                       | _ => idtac
                     end
  end.

Ltac ssimpl_in' H :=
  let s' := fresh in
  let H' := fresh in
  match type of H with
    | _ |= Aemp //\\ Aemp => 
      apply aconj_2aemp_elim in H  
    | _ |= _ //\\ _ => 
      eapply aconj_mono in H;
        [ idtac
        | intros s' H'; try progress ssimpl_in' H'; exact H'
        | intros s' H'; try progress ssimpl_in' H'; exact H'];
        cbv beta in H
    | _ |= ?A => 
      match find_aconj A with
        | some ?n =>
          sepliftn_in H n; eapply astar_mono in H;
          [idtac 
          | intros s' H'; try progress ssimpl_in' H'; fold myAconj in H'; exact H'
          | intros s' H'; exact H'];
          cbv beta in H; try progress ssimpl_in' H
        | _ =>
          let t := toTree A in
          pose (ssimplE t) as H';
            cbv [asrtTree_to_list asrtTree_to_list' listsimpl listsimplA listsimplB
                 myAppAsrtTree list_to_asrtTree unTree] in H';
            apply H' in H; clear H';
            try unfold myAconj in H
      end
    | _ => fail
  end.

Ltac ssimpl_in'' H :=
  let H' := fresh in
  match type of H with
    | _ |= EX _ , _ => eapply aexists_prop in H; [idtac | intros ? H'; try progress ssimpl_in'' H'; exact H']
    | _ |= _ => try progress ssimpl_in' H
    | _ => fail
  end.

Ltac ssimpl_in H :=
  try progress ssimpl_in'' H; cbv beta in H.


Ltac ssimpl' :=
  let s := fresh in
  let H := fresh in
  match goal with
    | |- _ |= Aemp //\\ Aemp => 
      apply aconj_2aemp_intro
    | |- _ |= _ //\\ _ =>
      eapply aconj_mono; 
        [ intros s H; try progress ssimpl'; exact H
        | intros s H; try progress ssimpl'; exact H
        | idtac];
        cbv beta
    | |- ?s' |= ?A => 
      match find_aconj A with
        | some ?n => sepliftn n; eapply astar_mono;
                     [ intros s H; try progress ssimpl'; fold myAconj; exact H
                     | intros s H; exact H
                     | idtac];
                     cbv beta; try progress ssimpl'
        | _ =>
          let t := toTree A in
          pose (ssimplI t) as H;
            cbv [asrtTree_to_list asrtTree_to_list' listsimpl listsimplA listsimplB
                 myAppAsrtTree list_to_asrtTree unTree] in H;
            apply H; clear H;
            try unfold myAconj
      end
    | _ => fail
  end.

Ltac ssimpl'' :=
  let H := fresh "H" in
  match goal with
    | |- _ |= EX _ , _ =>
      eapply aexists_prop;
        [intros ? H; try progress ssimpl''; exact H | idtac]
    | |- _ |= _ => try progress ssimpl'
  end.

Ltac ssimpl :=
  try progress ssimpl''; cbv beta.


(** * snormal *)

Ltac snormal_in_1 H :=
  let H' := fresh "H" in
  match type of H with
    | _ |= EX _ , _ =>
      eapply aexists_prop in H;
        [idtac | intros ? H'; try progress snormal_in_1 H'; exact H']
    | _ |= (EX _ , _) //\\ _ => apply aconj_l_aexists_elim in H; snormal_in_1 H
    | _ |= _ //\\ EX _ , _ => apply aconj_r_aexists_elim in H; snormal_in_1 H
    | _ |= _ => idtac
    | _ => fail
  end.
Ltac snormal_in_2 H :=
  try progress snormal_in_1 H; cbv beta in H.
Ltac snormal_in_3 H :=
  let s' := fresh in
  let H' := fresh "H" in
  match type of H with
    | _ |= EX _ , _ =>
      eapply aexists_prop in H;
        [idtac | intros ? H'; try progress snormal_in_3 H'; exact H']
    | _ |= _ //\\ _ =>
      eapply aconj_mono in H;
        [ idtac
        | intros s' H'; try progress snormal_in_3 H'; exact H'
        | intros s' H'; try progress snormal_in_3 H'; exact H'];
        cbv beta in H; try progress snormal_in_2 H
    | _ |= ?A => 
      match find_aexists A with
        | some ?n => sepliftn_in H n; apply astar_l_aexists_elim in H; try progress snormal_in_3 H
        | _ => match find_aconj A with
                 | some ?m => 
                   sepliftn_in H m; eapply astar_mono in H;
                   [idtac 
                   | intros s' H'; try progress snormal_in_3 H'; fold myAconj in H'; exact H'
                   | intros s' H'; exact H'];
                   cbv beta in H; try progress snormal_in_3 H
                 | _ => idtac
               end
      end
    | _ => fail
  end. 
Ltac snormal_in H :=
  try progress snormal_in_3 H; try unfold myAconj in H; ssimpl_in H; cbv beta in H.


Ltac snormal_1 :=
  let H := fresh in
  match goal with
    | |- _ |= EX _ , _ =>
      eapply aexists_prop;
        [intros ? H; try progress snormal_1; exact H | idtac]
    | |- _ |= (EX _ , _) //\\ _ => apply aconj_l_aexists_intro; snormal_1
    | |- _ |= _ //\\ EX _ , _ => apply aconj_r_aexists_intro; snormal_1
    | |- _ |= (EX _ , _) \\// _ => apply adisj_l_aexists_intro; snormal_1
    | |- _ |= _ \\// EX _ , _ => apply adisj_r_aexists_intro; snormal_1
    | |- _ |= _ => idtac
    | _ => fail
  end.
Ltac snormal_2 :=
  try progress snormal_1; cbv beta.
Ltac snormal_3 :=
  let s := fresh in
  let H := fresh in
  match goal with
    | |- _ |= EX _ , _ =>
      eapply aexists_prop;
        [intros ? H; try progress snormal_3; exact H | idtac]
    | |- _ |= _ //\\ _ => 
      eapply aconj_mono; 
        [ intros s H; try progress snormal_3; exact H
        | intros s H; try progress snormal_3; exact H
        | idtac];
        cbv beta; try progress snormal_2
    | |- _ |= ?A => 
      match find_aexists A with
        | some ?n => sepliftn n; apply astar_l_aexists_intro; try progress snormal_3
        | _ => match find_aconj A with
                 | some ?m => sepliftn m; eapply astar_mono;
                              [ intros s H; try progress snormal_3; fold myAconj; exact H
                              | intros s H; exact H
                              | idtac];
                              cbv beta; try progress snormal_3
                 | _ => idtac
               end
      end
    | _ => fail
  end.
Ltac snormal :=
  try progress snormal_3; try unfold myAconj; ssimpl; cbv beta.

(** * sep split *)

Ltac ssplit_apure_in H :=
  let H' := fresh in
  match type of H with
    | _ |= ?A =>
      match find_apure A with
        | some ?n =>
          sepliftn_in H n;
            match type of H with
              | _ |= _ ** _ =>
                apply astar_l_apure_elim in H;
                  destruct H as [ H' H ];
                  ssplit_apure_in H
              | _ |= _ =>
                apply apure_elim in H;
                  destruct H as [ H' H ]
            end
        | _ => idtac
      end
    | _ => fail
  end.

Ltac ssplit_pure_in H :=
  let H' := fresh in
  match type of H with
    | _ |= ?A =>
      match find_pure A with
        | some ?n =>
          sepliftn_in H n;
            match type of H with
              | _ |= _ ** _ =>
                first [ apply astar_l_aie_elim in H
                      | apply astar_l_ais_elim in H
                      | apply astar_l_atopis_elim in H
                      | apply astar_l_aisr_elim in H
                      | apply astar_l_acs_elim in H
                      | apply astar_l_adomlenv_elim in H
                      | apply astar_l_anotinlenv_elim in H
                      | apply astar_l_alvarenv_elim in H
                      | apply astar_l_agvarenv_elim in H
                      | apply astar_l_aop'_elim in H ];
                  destruct H as [ H' H ];
                  ssplit_pure_in H
              | _ |= _ =>
                first [ apply aie_elim in H
                      | apply ais_elim in H
                      | apply atopis_elim in H
                      | apply aisr_elim in H
                      | apply acs_elim in H
                      | apply adomlenv_elim in H
                      | apply anotinlenv_elim in H
                      | apply alvarenv_elim in H
                      | apply agvarenv_elim in H
                      | apply aop'_elim in H ];
                  destruct H as [ H' H ]
            end
        | _ => idtac
      end
    | _ => fail
  end.

Ltac ssplit_apure :=
  let s := fresh in
  let H := fresh in
  match goal with
    | |- _ |= ?A =>
      match find_apure A with
        | some ?n => 
          sepliftn n;
            match goal with
              | |- _ |= _ ** _ =>
                 apply astar_l_apure_intro;
                  [ ssplit_apure | idtac ]
              | |- _ |= _ =>
                apply apure_intro
            end
        | _ => idtac
      end
    | _ => fail
  end.


Ltac ssplit_pure :=
  let s := fresh in
  let H := fresh in
  match goal with
    | |- _ |= ?A =>
      match find_pure A with
        | some ?n => 
          sepliftn n;
            match goal with
              | |- _ |= _ ** _ =>
                first [apply astar_l_aie_intro
                      | apply astar_l_ais_intro
                      | apply astar_l_atopis_intro
                      | apply astar_l_aisr_intro
                      | apply astar_l_acs_intro
                      | apply astar_l_adomlenv_intro
                      | apply astar_l_anotinlenv_intro
                      | apply astar_l_alvarenv_intro
                      | apply astar_l_agvarenv_intro
                      | apply astar_l_aop'_intro ];
                  [ ssplit_pure | idtac ]
              | |- _ |= _ =>
                first [ apply aie_intro
                      | apply ais_intro
                      | apply atopis_intro
                      | apply aisr_intro
                      | apply acs_intro
                      | apply adomlenv_intro
                      | apply anotinlenv_intro
                      | apply alvarenv_intro
                      | apply agvarenv_intro
                      | apply aop'_intro ]
            end
        | _ => idtac
      end
    | _ => fail
  end.

(** * sep lower *)

Fixpoint listlowern (l: list asrtTree) (n:nat) : list asrtTree :=
  match l with
    | nil => l
    | a::l' => match n with
                 | 0%nat => myAppAsrtTree l' (a::nil)
                 | S n' => a::(listlowern l' n')
               end
  end.

Lemma listeq_prop2 :
  forall l a, listeq (myAppAsrtTree l (a::nil)) (a::l).
Proof.
  intros.
  replace (myAppAsrtTree l (a::nil)) with (list_insert l a (length l)).
  induction l.
  simpl.
  apply listeq_prop1.
  simpl.
  replace (a0 :: list_insert l a (length l))
          with (list_insert (list_insert l a (length l)) a0 0).
  replace (a::a0::l) with (list_insert (a::l) a0 1).
  constructor.
  auto.
  simpl.
  rewrite list_insert_prop1; auto.
  apply list_insert_prop1. 
  induction l; simpl; auto.
  rewrite IHl.
  auto.
Qed.

Lemma listeq_lowern : 
  forall l n, listeq (listlowern l n) l.
Proof.
  induction l; intros.
  simpl.
  constructor.
  induction n.
  simpl.
  apply listeq_prop2.
  simpl.
  rewrite <- list_insert_prop1.
  rewrite <- list_insert_prop1.
  constructor.
  auto.
Qed.

Theorem slower :
  forall l n,
    unTree (list_to_asrtTree_simpl l) <==> unTree (list_to_asrtTree_simpl (listlowern l n)).
Proof.
  intros.
  symmetry.
  apply unTree_prop2.
  apply listeq_lowern.
Qed.

Theorem slowerE :
  forall t n,
    unTree t ==> unTree (list_to_asrtTree_simpl (listlowern (asrtTree_to_list t) n)).
Proof.
  intros.
  apply slower.
  apply ssimplE_simpl.
  auto.
Qed.

Theorem slowerI :
  forall t n,
    unTree (list_to_asrtTree_simpl (listlowern (asrtTree_to_list t) n)) ==> unTree t.
Proof.
  intros.
  apply ssimplI_simpl.
  eapply slower.
  eauto.
Qed.

Theorem slowerE' :
  forall t n P,
    unTree t //\\ P ==> unTree (list_to_asrtTree_simpl (listlowern (asrtTree_to_list t) n)) //\\ P.
Proof.
  intros t n P.
  apply aconj_mono; [ apply slowerE | auto ].
Qed.

Theorem slowerI' :
  forall t n P,
    unTree (list_to_asrtTree_simpl (listlowern (asrtTree_to_list t) n)) //\\ P ==> unTree t //\\ P.
Proof.
  intros t n P.
  apply aconj_mono; [ apply slowerI | auto ].
Qed.

Ltac slowern_in' H n :=
  match n with
    | 0%nat => fail
    | S ?n' =>
      let H' := fresh in
      match type of H with
        | _ |= ?A //\\ _ =>
          let t := toTree A in
          pose (H' := slowerE' t n');
            cbv [asrtTree_to_list asrtTree_to_list' listlowern myAppAsrtTree list_to_asrtTree_simpl unTree] in H';
            apply H' in H; clear H'
        | _ |= ?A =>
          let t := toTree A in
          pose (H' := slowerE t n');
            cbv [asrtTree_to_list asrtTree_to_list' listlowern myAppAsrtTree list_to_asrtTree_simpl unTree] in H';
            apply H' in H; clear H'
      end
  end.

Ltac slowern_in'' H n :=
  let H' := fresh "H" in
  match type of H with
    | _ |= EX _ , _ =>
      eapply aexists_prop in H;
        [idtac | intros ? H'; try progress slowern_in'' H' n; exact H']
    | _ |= _ => try progress slowern_in' H n
  end.

Ltac slowern_in H n :=
  try progress slowern_in'' H n; cbv beta in H.

Ltac slowern' n :=
  match n with
    | 0%nat => fail
    | S ?n' =>
      let H := fresh in
      match goal with
        | |- _ |= ?A //\\ _ =>
          let t := toTree A in
          pose (H := slowerI' t n');
            cbv [asrtTree_to_list asrtTree_to_list' listlowern myAppAsrtTree list_to_asrtTree_simpl unTree] in H;
            apply H; clear H
        | |- _ |= ?A =>
          let t := toTree A in
          pose (H := slowerI t n');
            cbv [asrtTree_to_list asrtTree_to_list' listlowern myAppAsrtTree list_to_asrtTree_simpl unTree] in H;
            apply H; clear H
      end
  end.

Ltac slowern'' n :=
  let H := fresh "H" in
  match goal with
    | |- _ |= EX _ , _ =>
      eapply aexists_prop;
        [intros ? H; try progress slowern'' n; exact H | idtac]
    | |- _ |= _ => try progress slowern' n
  end.

Ltac slowern n :=
  try progress slowern'' n; cbv beta.

(** * sep rearrange *)

Fixpoint list_getn (l: list asrtTree) (n:nat) : asrtTree :=
  match l with
    | nil => empTree (* failure case *)
    | a::l' => match n with
                 | 0%nat => a
                 | S n' => list_getn l' n'
               end
  end.

Fixpoint list_getl (l: list asrtTree) (l0: list nat) : list asrtTree :=
  match l0 with
    | nil => nil
    | a::l0' => (list_getn l a)::(list_getl l l0')
  end.

Fixpoint baseList (m n:nat) : list nat :=
  match n with
    | 0%nat => nil
    | S n' => m::baseList (S m) n'
  end.

Fixpoint list_dropn (l: list asrtTree) (n:nat) : list asrtTree :=
  match l with
    | nil => nil
    | a::l' => match n with
                 | 0%nat => l
                 | S n' => list_dropn l' n'
               end
  end.

Fixpoint natlist_insert (l: list nat) (x:nat) : list nat :=
  match l with
    | nil => x::nil
    | a::l' => if NPeano.Nat.leb x a
               then x::a::l'
               else a::(natlist_insert l' x)
  end.

Fixpoint natlist_sort (l: list nat) : list nat :=
  match l with
    | nil => nil
    | a::l' => natlist_insert (natlist_sort l') a
  end.

Lemma list_dropn_prop1 :
  forall l, list_dropn l (length l) = nil.
Proof.
  induction l; intros; auto.
Qed.

Lemma list_dropn_prop2 :
  forall l, list_dropn l 0 = l.
Proof.
  induction l; auto.
Qed.

Lemma list_dropn_prop3 :
  forall l n,
    length l > n ->
    list_dropn l n = list_getn l n :: list_dropn l (S n).
Proof.
  induction l; intros; simpl in *.
  inversion H.
  induction n.
  rewrite list_dropn_prop2; auto.
  assert (length l > n) by omega; clear H.
  apply IHl in H0.
  auto.
Qed.

Lemma list_dropn_prop4 :
  forall l n,
    length l >= n ->
    list_dropn l (length l - n) = list_getl l (baseList (length l - n) n).
Proof.
  induction n; intros.
  simpl.
  replace (length l - 0) with (length l) by omega.
  apply list_dropn_prop1.
  simpl.
  rewrite list_dropn_prop3.
  2 : omega.
  replace (S (length l - S n)) with (length l - n) by omega.
  rewrite IHn.
  2 : omega.
  auto.
Qed.

Lemma list_getl_prop1:
  forall l l0 a, exists n,
    list_getl l (natlist_insert l0 a) = list_insert (list_getl l l0) (list_getn l a) n.
Proof.
  intros l l0.
  generalize dependent l.
  induction l0; intros.
  simpl.
  exists 0; auto.
  simpl.
  destruct (NPeano.Nat.leb a0 a); simpl in *.
  exists 0.
  auto.
  pose (IHl0 l a0) as H100; destruct H100 as [n H100];
  rewrite H100; clear H100.
  exists (S n); auto.
Qed.

Lemma listeq_getl_sort :
  forall l l0,
    listeq (list_getl l l0) (list_getl l (natlist_sort l0)).
Proof.
  intros l l0; generalize dependent l.
  induction l0; intros; simpl in *.
  constructor.
  simpl.
  pose (list_getl_prop1 l (natlist_sort l0) a) as H100;
    destruct H100 as [n H100].
  rewrite H100; clear H100.
  rewrite <- list_insert_prop1.
  constructor.
  auto.
Qed.

Lemma listeq_getl :
  forall l l0,
    natlist_sort l0 = baseList 0 (length l) ->
    listeq (list_getl l l0) l.
Proof.
  intros.
  assert (l = list_dropn l (length l -length l)) 
    as H100 by (replace (length l - length l) with 0 by omega; induction l; auto);
    rewrite H100 at 2; clear H100.
  rewrite list_dropn_prop4.
  2 : omega.
  replace (length l - length l) with 0 by omega.
  rewrite <- H.
  apply listeq_getl_sort.
Qed.

Theorem srearr :
  forall l l0,
    natlist_sort l0 = baseList 0 (length l) ->
    unTree (list_to_asrtTree_simpl l) <==> unTree (list_to_asrtTree_simpl (list_getl l l0)).
Proof.
  intros.
  symmetry.
  eapply unTree_prop2.
  apply listeq_getl; auto.
Qed.

Theorem srearrE :
  forall t l0,
    natlist_sort l0 = baseList 0 (length (asrtTree_to_list t)) ->
    unTree t ==> unTree (list_to_asrtTree_simpl (list_getl (asrtTree_to_list t) l0)).
Proof.
  intros.
  apply srearr.
  auto.
  apply ssimplE_simpl.
  auto.
Qed.

Theorem srearrI :
  forall t l0,
    natlist_sort l0 = baseList 0 (length (asrtTree_to_list t)) ->
    unTree (list_to_asrtTree_simpl (list_getl (asrtTree_to_list t) l0)) ==> unTree t.
Proof.
  intros.
  apply ssimplI_simpl.
  eapply srearr.
  2 : eauto.
  auto.
Qed.

Theorem srearrE' :
  forall t l0 P,
    natlist_sort l0 = baseList 0 (length (asrtTree_to_list t)) ->
    unTree t //\\ P ==> unTree (list_to_asrtTree_simpl (list_getl (asrtTree_to_list t) l0)) //\\ P.
Proof.
  intros t l0 P H.
  apply aconj_mono; [ apply srearrE; auto | auto ].
Qed.

Theorem srearrI' :
  forall t l0 P,
    natlist_sort l0 = baseList 0 (length (asrtTree_to_list t)) ->
    unTree (list_to_asrtTree_simpl (list_getl (asrtTree_to_list t) l0)) //\\ P ==> unTree t //\\ P.
Proof.
  intros t l0 P H.
  apply aconj_mono; [ apply srearrI; auto | auto ].
Qed.

Ltac list_filter_minus1 l :=
  match l with
    | nil => constr:(@nil nat)
    | ?a::?l' => match a with
                   | 0%nat => fail
                   | S ?a' => let l'' := list_filter_minus1 l' in
                              constr:(a'::l'')
                 end
  end.


Ltac srearr_in' H lorder :=
  let H' := fresh in
  let l := list_filter_minus1 lorder in
  match type of H with
    | _ |= ?A //\\ _ =>
      let t := toTree A in
      pose (srearrE' t l) as H';
        cbv [asrtTree_to_list asrtTree_to_list' natlist_sort length baseList] in H';
        cbv [natlist_insert NPeano.Nat.leb ] in H';
        cbv [list_getl list_getn list_to_asrtTree_simpl unTree] in H';
        apply H' in H; [clear H' | auto]
    | _ |= ?A =>
      let t := toTree A in
      pose (srearrE t l) as H';
        cbv [asrtTree_to_list asrtTree_to_list' natlist_sort length baseList] in H';
        cbv [natlist_insert NPeano.Nat.leb ] in H';
        cbv [list_getl list_getn list_to_asrtTree_simpl unTree] in H';
        apply H' in H; [clear H' | auto]
  end.

Ltac srearr_in'' H lorder :=
  let H' := fresh in
  match type of H with
    | _ |= EX _ , _ =>
      eapply aexists_prop in H; [idtac | intros ? H'; try progress srearr_in'' H' lorder; exact H']
    | _ |= _ => try progress srearr_in' H lorder
  end.

Ltac srearr_in H lorder :=
  try progress srearr_in'' H lorder; cbv beta in H.

Ltac srearr' lorder :=
  let H := fresh in
  let l := list_filter_minus1 lorder in
  match goal with
    | |- _ |= ?A //\\ _ =>
      let t := toTree A in
      pose (srearrI' t l) as H;
        cbv [asrtTree_to_list asrtTree_to_list' natlist_sort length baseList] in H;
        cbv [natlist_insert NPeano.Nat.leb ] in H;
        cbv [list_getl list_getn list_to_asrtTree_simpl unTree] in H;
        apply H; [auto | clear H]
    | |- _ |= ?A =>
      let t := toTree A in
      pose (srearrI t l) as H;
        cbv [asrtTree_to_list asrtTree_to_list' natlist_sort length baseList] in H;
        cbv [natlist_insert NPeano.Nat.leb ] in H;
        cbv [list_getl list_getn list_to_asrtTree_simpl unTree] in H;
        apply H; [auto | clear H]
  end.

Ltac srearr'' lorder :=
  let H := fresh "H" in
  match goal with
    | |- _ |= EX _ , _ =>
      eapply aexists_prop;
        [intros ? H; try progress srearr'' lorder; exact H | idtac]
    | |- _ |= _ => try progress srearr' lorder
  end.

Ltac srearr lorder :=
  try progress srearr'' lorder; cbv beta.

(** * Tactic Notation *)

Tactic Notation "sep" "split" "in" hyp (H) :=
   try progress ssplit_apure_in H; try progress ssplit_pure_in H. 
Tactic Notation "sep" "split"  :=
  try progress ssplit_apure; try progress ssplit_pure.

Tactic Notation "sep" "normal" "in" hyp (H) :=
  try progress (snormal_in H; cbv beta in H).
Tactic Notation "sep" "normal" :=
  try progress (snormal; cbv beta).

Tactic Notation "sep" "lift" constr (n) "in" hyp (H) :=
  try progress (sepliftn_in H n; cbv beta in H).
Tactic Notation "sep" "lift" constr (n) :=
  try progress (sepliftn n; cbv beta).


Tactic Notation "sep" "lower" constr (n) "in" hyp (H) :=
  try progress (slowern_in H n; cbv beta in H).
Tactic Notation "sep" "lower" constr (n) :=
  try progress (slowern n; cbv beta).


Tactic Notation "sep" "rearr" "in" hyp (H) "with" constr (order) :=
  try progress (srearr_in H order; cbv beta in H).
Tactic Notation "sep" "rearr" "with" constr (order) :=
  try progress (srearr order; cbv beta).

(** * Unification *)

Ltac asrtlength' Hp :=
  match Hp with
    | ?A ** ?B => let l := asrtlength' A in
                  let r := asrtlength' B in
                  constr:(l + r)
    | _ => constr:1
  end.
Ltac asrtlength Hp :=
  let x := asrtlength' Hp in
  eval compute in x.

Ltac ge_nat x y :=
  match y with
    | 0%nat => constr:true
    | S ?y' => match x with
                 | 0%nat => constr:false
                 | S ?x' => ge_nat x' y'
               end
  end.

Ltac sunify' lh lg m :=
  let s' := fresh in
  let H' := fresh in
  match goal with
    | H : ?s |= ?A ** ?B |- ?s |= ?C ** ?D =>
      try solve [ exact H ];
      try solve [ apply astar_mono with (P:=A) (Q:=B);
                  [ intros s' H'; exact H'
                  | intros s' H'; ssimpl_in H; ssimpl;
                    match lh with
                      | 0%nat => fail
                      | S ?x => match lg with
                                  | 0%nat => fail
                                  | S ?y => sunify' x y x
                                end
                    end
                  | exact H]];
        match m with
          | 0%nat => idtac
          | S ?m' => sep lower 1 in H; sunify' lh lg m'
        end
    | H : ?s |= _ |- ?s |= _ => first [ exact H | apply atrue_intro ]
    | _ => fail
  end.

Ltac sunify'' lh lg n :=
  try solve [sunify' lh lg lh];
  match n with
    | 0%nat => idtac
    | S ?n' => try solve [sep lower 1; sunify'' lh lg n']
  end.

Ltac sunify :=
   match goal with
    | H : ?s |= ?A |- ?s |= ?B =>
      try solve [ exact H | apply atrue_intro ];
      let x := asrtlength A in
      let y := asrtlength B in
      match ge_nat x y with
        | true => try solve [ssimpl_in H; ssimpl; sunify'' x y y]
        | false => idtac
      end
    | _ => fail
  end.


Tactic Notation "sep" "unify" :=
  sunify.

Tactic Notation "sep" "unify" "with" hyp (H) :=
  let H' := fresh in
  let Hp := type of H in
  assert Hp as H' by exact H;
  clear H; rename H' into H;
  sep unify.


(** sep auto *)

Ltac sep_destruct H :=
  repeat match type of H with
           | _ |= EX _, _ => destruct H as [ ? H ]
         end.

Tactic Notation "sep" "destruct" hyp(H) := sep_destruct H.

Ltac sep_eexists :=
  repeat match goal with
           | |- _ |= EX _, _ => eexists
         end.

Tactic Notation "sep" "eexists" := sep_eexists.

Ltac sep_pure := 
  match goal with
    | |- _ |= _ => idtac
    | H : _ |= _ |- _ =>
      sep normal in H;
        sep destruct H;
        sep split in H;
        subst
    | _ => idtac
  end;
  [auto..].

Tactic Notation "sep" "pure" := sep_pure.

(*Ltac can_change_aop_solver := idtac.*)

Ltac sep_auto :=
  intros;
  match goal with
    | H : ?s |= _ |- ?s |= _ =>
      try solve [ exact H | apply atrue_intro ];
        sep normal in H;
        sep destruct H;
        sep split in H; subst;
        (let Hp := type of H in
         let H' := fresh in
         assert Hp as H' by exact H; clear H; rename H' into H); 
        sep normal;
        sep eexists;
        sep split;
        match goal with
          | |- _ |= _ => scancel; sep unify
          | _ => sep_pure
        end
    | H : (?o,?O,?op) |= _ |- (?o,?O,?op') |= _ =>
      try solve [ apply atrue_intro ];
        sep normal in H;
        sep destruct H;
        sep split in H; subst;
        (let Hp := type of H in
         let H' := fresh in
         assert Hp as H' by exact H; clear H; rename H' into H); 
        sep normal;
        sep eexists;
        sep split;
        match goal with
          | |- _ |= _ =>
            apply change_aop_rule with (aop := op);
              [ scancel; sep unify
              | can_change_aop_solver ]
          | _ => sep_pure
        end
    | _ => idtac
  end.

Ltac sep_semiauto :=
    intros;
    match goal with
      | H:?s |= _
        |- ?s |= _ =>
        try (solve [ exact H | apply atrue_intro ]); sep normal in H; sep
                                                                        destruct H; sep split in H; subst;
        repeat match goal with
                 | H0 : exists _ , _ |- _ => destruct H0
                 | H0 : _ /\ _ |- _ => destruct H0
               end;
        (let Hp := type of H in
         let H' := fresh in
         assert Hp as H' by exact H; clear H; rename H' into H); sep normal;
        sep eexists; sep split;
        match goal with
          | |- _ |= _ => scancel
          | _ => sep_pure
        end
      | H:(?o, ?O, ?op) |= _
        |- (?o, ?O, ?op') |= _ =>
        try (solve [ apply atrue_intro ]); sep normal in H; sep destruct H;
        sep split in H; subst;
        (let Hp := type of H in
         let H' := fresh in
         assert Hp as H' by exact H; clear H; rename H' into H); sep normal;
        sep eexists; sep split;
        match goal with
          | |- _ |= _ =>
            apply change_aop_rule with (aop := op);
              [ scancel | can_change_aop_solver ]
          | _ => sep_pure
        end
      | _ => idtac
    end.

Ltac sep_semiauto_nosplit :=
    intros;
    match goal with
      | H:?s |= _
        |- ?s |= _ =>
        try (solve [ exact H | apply atrue_intro ]); sep normal in H; sep
                                                                        destruct H;  (try progress ssplit_apure_in H); subst;
        repeat match goal with
                 | H0 : exists _ , _ |- _ => destruct H0
                 | H0 : _ /\ _ |- _ => destruct H0
               end;
        (let Hp := type of H in
         let H' := fresh in
         assert Hp as H' by exact H; clear H; rename H' into H); sep normal;
        sep eexists; ssplit_apure;
        match goal with
          | |- _ |= _ => scancel
          | _ => sep_pure
        end
      | H:(?o, ?O, ?op) |= _
        |- (?o, ?O, ?op') |= _ =>
        try (solve [ apply atrue_intro ]); sep normal in H; sep destruct H;
         (try progress ssplit_apure_in H); subst;
        (let Hp := type of H in
         let H' := fresh in
         assert Hp as H' by exact H; clear H; rename H' into H); sep normal;
        sep eexists; ssplit_apure;
        match goal with
          | |- _ |= _ =>
            apply change_aop_rule with (aop := op);
              [ scancel | can_change_aop_solver ]
          | _ => sep_pure
        end
      | _ => idtac
    end.


Tactic Notation "sep" "semiauto" :=
  first [ solve [ sep_semiauto; sep_pure ]
        | sep_semiauto ].

Tactic Notation "sep" "semiauton" "nosplit" :=
  first [ solve [ sep_semiauto_nosplit; sep_pure ]
        | sep_semiauto_nosplit ].


Tactic Notation "sep" "auto" :=
  first [ solve [ sep_auto; sep_pure ]
        | sep_auto ].

(** sep lift m n o ... **)

Ltac multiSepLiftInc a l :=
  match l with
    | nil => constr:(@nil nat)
    | ?b::?l' => let l'' := multiSepLiftInc a l' in
                 let x := constr:(NPeano.Nat.ltb a b) in
                 match eval compute in x with
                   | true => constr:(b::l'')
                   | false => constr:((S b)::l'')
                 end
  end.

Ltac multiSepLift l :=
  match l with
    | nil => constr:(@nil nat)
    | ?b::?l' => let l0 := multiSepLiftInc b l' in
                 let l1 := multiSepLift l0 in
                 constr:(b::l1)
  end.

Ltac sepliftsn_in' H l :=
  match l with
    | nil => idtac
    | ?a::?l' => sepliftn_in H a;
                sepliftsn_in' H l'
  end.

Ltac sepliftsn_in H l :=
  let l1 := constr:(rev l) in
  let l2 := (eval compute in l1) in
  let l3 := multiSepLift l2 in
  let l4 := (eval compute in l3) in
  sepliftsn_in' H l4.

Ltac sepliftsn' l :=
  match l with
    | nil => idtac
    | ?a::?l' => sepliftn a;
                sepliftsn' l'
  end.

Ltac sepliftsn l :=
  let l1 := constr:(rev l) in
  let l2 := (eval compute in l1) in
  let l3 := multiSepLift l2 in
  let l4 := (eval compute in l3) in
  sepliftsn' l4.

Tactic Notation "sep" "lifts" constr (l) "in" hyp (H) :=
  try progress (sepliftsn_in H l; cbv beta in H).
Tactic Notation "sep" "lifts" constr (l) :=
  try progress (sepliftsn l; cbv beta).


(** add an Aemp to the end of the asrt *)

Fixpoint list_addempR (l:list asrtTree) : list asrtTree :=
  match l with
    | nil => empTree::nil
    | a::l' => a::(list_addempR l')
  end.

Lemma listeq_addemp :
  forall l,
    listeq (empTree::l) (list_addempR l).
Proof.
  induction l.
  simpl.
  apply listeq_prop1.
  simpl.
  replace (empTree::a::l) with (list_insert (empTree::l) a 1).
  2 : simpl; rewrite list_insert_prop1; auto.
  replace (a::list_addempR l) with (list_insert (list_addempR l) a 0).
  2 : apply list_insert_prop1.
  constructor.
  auto.
Qed.

Theorem saddempL :
  forall l,
    unTree (list_to_asrtTree_simpl l) <==> unTree (list_to_asrtTree_simpl (empTree::l)).
Proof.
  split; intros.
  apply list_to_asrtTree_simpl_prop1.
  unfold1 unTree; scancel.
  apply list_to_asrtTree_simpl_prop1 in H.
  unfold1 unTree; scancel.
Qed.

Theorem saddempR :
  forall l,
    unTree (list_to_asrtTree_simpl l) <==> unTree (list_to_asrtTree_simpl (list_addempR l)).
Proof.
  symmetry.
  split; intros.
  apply saddempL.
  eapply unTree_prop2.
  2 : apply H.
  apply listeq_addemp.
  apply saddempL in H.
  eapply unTree_prop2.
  2 : apply H.
  apply listeq_comm.
  apply listeq_addemp.
Qed.

Theorem saddempRE :
  forall t,
    unTree t ==> unTree (list_to_asrtTree_simpl (list_addempR (asrtTree_to_list t))).
Proof.
  intros.
  apply ssimplE_simpl in H.
  apply saddempR in H.
  auto.
Qed.

Theorem saddempRI :
  forall t,
    unTree (list_to_asrtTree_simpl (list_addempR (asrtTree_to_list t))) ==> unTree t.
Proof.
  intros.
  apply ssimplI_simpl.
  apply saddempR.
  auto.
Qed.

Theorem saddempRE' :
  forall t P,
    unTree t //\\ P ==> unTree (list_to_asrtTree_simpl (list_addempR (asrtTree_to_list t))) //\\ P.
Proof.
  intros t P.
  apply aconj_mono; [ apply saddempRE | auto ].
Qed.

Theorem saddempRI' :
  forall t P,
    unTree (list_to_asrtTree_simpl (list_addempR (asrtTree_to_list t))) //\\ P ==> unTree t //\\ P.
Proof.
  intros t P.
  apply aconj_mono; [ apply saddempRI | auto ].
Qed.

Ltac saddEmpHR H :=
  let H' := fresh in
  match type of H with
    | _ |= ?A //\\ _ =>
      let t := toTree A in
      pose (H' := saddempRE' t);
        cbv [asrtTree_to_list asrtTree_to_list' list_addempR list_to_asrtTree_simpl unTree] in H';
        apply H' in H; clear H'
    | _ |= ?A =>
      let t := toTree A in
      pose (H' := saddempRE t);
        cbv [asrtTree_to_list asrtTree_to_list' list_addempR list_to_asrtTree_simpl unTree] in H';
        apply H' in H; clear H'
    | _ => fail
  end.

Ltac saddEmpR :=
  let H := fresh in
  match goal with
    | |- _ |= ?A //\\ _  =>
      let t := toTree A in
      pose (H := saddempRI' t);
        cbv [asrtTree_to_list asrtTree_to_list' list_addempR list_to_asrtTree_simpl unTree] in H;
        apply H; clear H
    | |- _ |= ?A =>
      let t := toTree A in
      pose (H := saddempRI t);
        cbv [asrtTree_to_list asrtTree_to_list' list_addempR list_to_asrtTree_simpl unTree] in H;
        apply H; clear H
    | _ => fail
  end.

Tactic Notation "sep" "add" "emp" "in" hyp (H) :=
  saddEmpHR H.

Tactic Notation "sep" "add" "emp" :=
  saddEmpR.

(** sep rewrite n *)

Ltac srewrite_in' H Heq :=
  match type of H with
    | _ |= _ ** _ => let H' := fresh in
                     eapply astar_mono in H;
                       [ idtac
                       | intros ? H'; srewrite_in' H' Heq; exact H'
                       | intros ? H'; srewrite_in' H' Heq; exact H']
    | _ |= _ //\\ _ => let H' := fresh in
                       eapply aconj_mono in H;
                         [ idtac
                         | intros ? H'; srewrite_in' H' Heq; exact H'
                         | intros ? H'; srewrite_in' H' Heq; exact H']
    | _ |= [| ?x = ?y |] => match type of Heq with
                              | (x = y) => idtac
                              | _ => try rewrite Heq in H
                            end
    | _ |= _ => try rewrite Heq in H
  end.

Ltac srewriten_in' H n :=
  let H' := fresh in
  let newH := fresh in
  let Heq := fresh in
  match type of H with
    | _ |= EX _ , _ => 
      eapply aexists_prop in H; [idtac | intros ? H'; srewriten_in' H' n; exact H']
    | _ |= _ =>
      let x := type of H in
      assert x as newH by exact H;
        sep lift n in newH;
        match type of newH with
          | _ |= [| ?x = ?y |] ** _ //\\ _ =>
            let newH' := fresh in
            destruct newH as [ newH newH' ]; clear newH';
            apply astar_l_apure_elim in newH; destruct newH as [ Heq newH ];
            clear newH; srewrite_in' H Heq; clear Heq
          | _ |= [| ?x = ?y |] //\\ _ => clear newH
          | _ |= [| ?x = ?y |] ** _ => 
            apply astar_l_apure_elim in newH; destruct newH as [ Heq newH ];
            clear newH; srewrite_in' H Heq; clear Heq
          | _ |= [| ?x = ?y |] => clear newH
        end
  end.

Ltac srewriten_in H n :=
  srewriten_in' H n; cbv beta in H.

Tactic Notation "sep" "rewrite" constr(n) "in" hyp(H) :=
  srewriten_in H n.

Ltac srewrite_pure_H'' H H' :=
  let H'' := fresh in
  match type of H' with
    | _ |= ?P =>
      match find_apure P with
        | some ?n => sep lift n in H';
                    match type of H' with
                      | _ |= [| _ = _ |] ** _ =>
                        apply astar_l_apure_elim in H'; destruct H' as [H'' H'];
                          srewrite_in' H H''; clear H''; srewrite_pure_H'' H H'
                        | _ |= [| _ |] ** _ =>
                          apply astar_l_apure_elim in H'; destruct H' as [H'' H'];
                          clear H''; srewrite_pure_H'' H H'
                        | _ |= [| _ = _ |] =>
                          apply apure_elim in H'; destruct H' as [H'' H'];
                          srewrite_in' H H''; clear H'' H'
                        | _ |= [| _ |] => clear H'
                      end
          | _ => clear H'
      end
  end.

Ltac srewrite_pure_H' H :=
  let H' := fresh in
  let newH := fresh in
  match type of H with
    | _ |= EX _ , _ => 
      eapply aexists_prop in H; [idtac | intros ? H'; srewrite_pure_H' H'; exact H']
    | _ |= _ =>
      let x := type of H in
      assert x as newH by exact H;
        srewrite_pure_H'' H newH
  end.

Ltac srewrite_pure_H H :=
  srewrite_pure_H' H; cbv beta in H.

Tactic Notation "sep" "rewrite" "pure" "in" hyp(H) :=
  srewrite_pure_H H.

(** sep destruct *)

Ltac sdestroy_in' H :=
  match type of H with
    | _ |= _ //\\ _ => let H1 := fresh in
                       let H2 := fresh in
                       destruct H as [ H1 H2 ];
                         sdestroy_in' H1; sdestroy_in' H2 
    | _ |= _ ** _ => apply astar_prop in H; do 2 destruct H as [ ? H ];
                     let H1 := fresh in
                     let H2 := fresh in
                     destruct H as [ H1 H2 ];
                       sdestroy_in' H1; sdestroy_in' H2
    | _ |= _ => idtac
  end.

Ltac sdestroy_in H :=
  sep normal in H;
  sep destruct H;
  sep split in H;
  sdestroy_in' H.

Tactic Notation "sep" "destroy" hyp(H) := sdestroy_in H.


(** advanced scancel *)

Lemma cancel_lvarmapsto :
  forall v1 v2 x t P Q perm,
    (P ==> Q) ->
    v1 = v2 ->  
    LV x @ t |=> v1 @ perm ** P ==> LV x @ t |=> v2 @ perm ** Q.
Proof.
  intros; subst; scancel; auto.
Qed.

Lemma cancel_gvarmapsto :
  forall v1 v2 x t P Q perm,
    (P ==> Q) ->
    v1 = v2 ->    
    GV x @ t |=> v1 @ perm ** P ==> GV x @ t |=> v2 @ perm ** Q.
Proof.
  intros; subst; scancel; auto.
Qed.

Lemma cancel_ptrmapsto :
  forall v1 v2 l t P Q perm,
    (P ==> Q) ->
    v1 = v2 ->
    PV l @ t |=> v1 @ perm ** P ==> PV l @ t |=> v2 @ perm ** Q.
Proof.
  intros; subst; scancel; auto.
Qed.

Lemma cancel_ptrstruct :
  forall ls1 ls2 l t P Q,
    (P ==> Q) ->
    ls1 = ls2 ->
    Astruct l t ls1 ** P ==> Astruct l t ls2 ** Q.
Proof.
  intros; subst; scancel; auto.
Qed.

Lemma cancel_ptrarray :
  forall ls1 ls2 l t P Q,
    (P ==> Q) ->
    ls1 = ls2 ->
    Aarray l t ls1 ** P ==> Aarray l t ls2 ** Q.
Proof.
  intros; subst; scancel; auto.
Qed.

Lemma cancel_lvararray :
  forall ls1 ls2 x t P Q,
    (P ==> Q) ->
    ls1 = ls2 ->
    LAarray x t ls1 ** P ==> LAarray x t ls2 ** Q.
Proof.
  intros; subst; scancel; auto.
Qed.

Lemma cancel_gvararray :
  forall ls1 ls2 x t P Q,
    (P ==> Q) ->
    ls1 = ls2 ->
    GAarray x t ls1 ** P ==> GAarray x t ls2 ** Q.
Proof.
  intros; subst; scancel; auto.
Qed.

Lemma cancel_absdata :
  forall absdataid absdata1 absdata2 P Q,
    (P ==> Q) ->
    absdata1 = absdata2 ->
    Aabsdata absdataid absdata1 ** P ==> Aabsdata absdataid absdata2 ** Q.
Proof.
  intros; subst; scancel; auto.
Qed.

Ltac cancel_same' :=
  let s' := fresh in
  let H' := fresh in
  match goal with
    | H : ?s |= LV ?x @ _ |=> _ @ _ ** _ |- ?s |= LV ?x @ _ |=> _ @ _ ** _ =>
      lets H' : H;
        generalize dependent H; apply cancel_lvarmapsto; 
        [ clear H'; first [ clear s; intros s H | intros s' H ] | rename H' into H; auto ]
    | H : ?s |= GV ?x @ _ |=> _ @ _ ** _ |- ?s |= GV ?x @ _ |=> _ @ _ ** _ =>
      lets H' : H;
        generalize dependent H; apply cancel_gvarmapsto; 
        [ clear H'; first [ clear s; intros s H | intros s' H ] | rename H' into H; auto ]
    | H : ?s |= PV ?l @ _ |=> _ @ _ ** _ |- ?s |= PV ?l @ _ |=> _ @ _ ** _ =>
      lets H' : H;
        generalize dependent H; apply cancel_ptrmapsto; 
        [ clear H'; first [ clear s; intros s H | intros s' H ] | rename H' into H; auto ]
    | H : ?s |= Astruct ?l _ _ ** _ |- ?s |= Astruct ?l _ _ ** _ =>
      lets H' : H;
        generalize dependent H; apply cancel_ptrstruct; 
        [ clear H'; first [ clear s; intros s H | intros s' H ] | rename H' into H; auto ]
    | H : ?s |= Aarray ?l _ _  ** _ |- ?s |= Aarray ?l _ _ ** _ =>
      lets H' : H;
        generalize dependent H; apply cancel_ptrarray; 
        [ clear H'; first [ clear s; intros s H | intros s' H ] | rename H' into H; auto ]
    | H : ?s |= LAarray ?x _ _ ** _ |- ?s |= LAarray ?x _ _ ** _ =>
      lets H' : H;
        generalize dependent H; apply cancel_lvararray; 
        [ clear H'; first [ clear s; intros s H | intros s' H ] | rename H' into H; auto ]
    | H : ?s |= GAarray ?x _ _ ** _ |- ?s |= GAarray ?x _ _ ** _ =>
      lets H' : H;
        generalize dependent H; apply cancel_gvararray; 
        [ clear H'; first [ clear s; intros s H | intros s' H ] | rename H' into H; auto ]
    | H : ?s |= Aabsdata ?id _  ** _ |- ?s |= Aabsdata ?id _ ** _ =>
      lets H' : H;
        generalize dependent H; apply cancel_absdata; 
        [ clear H'; first [ clear s; intros s H | intros s' H ] | rename H' into H; auto ]
    | H : ?s |= ?A ** _ |- ?s |= ?A ** _ =>
      generalize dependent H; apply astar_mono; 
      [ intros s' H; exact H | first [ clear s; intros s H | intros s' H ] ]

  end.

Ltac cancel_same :=
  match goal with
    | H : ?s |= ?X |- ?s |= ?Y =>
         try solve [ exact H | apply atrue_intro ];
        match search_match Y X with
          | Some (?m,?n) =>
            sep lift m in H; sep lift n;
            match goal with
              | H : ?s |= ?A ** ?B |- ?s |= ?C ** ?D =>
                cancel_same'; [ cancel_same | idtac .. ]
              | H : ?s |= ?A ** ?B |- ?s |= ?C =>
                apply astar_r_aemp_elim; cancel_same'; [ cancel_same | idtac .. ]
              | H : ?s |= ?A |- ?s |= ?C ** ?D =>
                apply astar_r_aemp_intro in H; cancel_same'; [ cancel_same | idtac .. ]
              | H : ?s |= ?A |- ?s |= ?C =>
                apply astar_r_aemp_intro in H; apply astar_r_aemp_elim;
                cancel_same'; [ cancel_same | idtac .. ]
            end
          | @None => idtac
        end
  end.

Ltac scancel' ::= cancel_same.

Ltac scancel ::=
     match goal with
       | H:?s |= _ |- ?s |= _ =>
         sep normal in H; sep normal;
         scancel';
         match goal with
           | |- _ |= _ => sclearemp_in H; sclearemp
           | _ => idtac
         end
       | _ => idtac
     end.

Ltac sep_cancel m n :=
  let s':= fresh in
  match goal with
    | H: ?s |= _ |- ?s |= _ =>
      sep lift m in H;
        sep lift n;
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

(* Tactic Notation "sep" "cancel" constr(m) constr(n) :=
 *   sep_cancel m n. *)

Ltac find_match_context' Hp x :=
  match Hp with
  | ?A ** ?B =>
      match find_match_context' A x with
      | some ?a => constr:(some a)
      | none ?a =>
          match find_match_context' B x with
          | some ?b => constr:(some (a + b)%nat)
          | none ?b => constr:(none (a + b)%nat)
          end
      end
  | context [x] => constr:(some 1%nat)
  | _ => constr:(none 1%nat)
  end.

Ltac find_match_context Hp x :=
  let y := find_match_context' Hp x in
  eval compute in y.


Ltac sep_cancel_context x :=
  match goal with
    | H: ?s |= ?P |- ?s |= ?Q =>
      match find_match_context P x with
        | none _ => fail 1
        | some ?m =>
          match find_match_context Q x with
            | none _ => fail 2
            | some ?n =>
              sep_cancel m n
          end
      end
  end.

Tactic Notation "sep" "cancel" constr(x) :=
  sep_cancel_context x.

(* sep remember list *)

Ltac asrt_get_after_n p n :=
  match n with
    | 0%nat => constr:(Some p)
    | S ?n' =>
      match p with
        | ?p' ** ?q' => asrt_get_after_n q' n'
        | _ => constr:(@None)
      end
  end.

Ltac sep_remember_in H l :=
  sep lifts l in H;
  let x := constr:(length l) in
  let y := (eval compute in x) in
  let a := fresh in
  match type of H with
    | _ |= ?p =>
      match asrt_get_after_n p y with
        | @None => fail 1
        | Some ?p' => remember p' as a
      end
  end.

Ltac sep_remember l :=
  sep lifts l;
  let x := constr:(length l) in
  let y := (eval compute in x) in
  let a := fresh in
  match goal with
    | |- _ |= ?p =>
      match asrt_get_after_n p y with
        | @None => fail 1
        | Some ?p' => remember p' as a
      end
  end.

Tactic Notation "sep" "remember" constr(l) "in" hyp(H) :=
  sep_remember_in H l.

Tactic Notation "sep" "remember" constr(l) :=
  sep_remember l.


(* sep destroy *)

Ltac sep_destroy' H :=
  match type of H with
    | _ |= _ ** _ => apply astar_prop in H; do 2 destruct H as [ ? H ];
                     let H1 := fresh in
                     let H2 := fresh in
                     destruct H as [ H1 H2 ];
                       sep_destroy' H1; sep_destroy' H2
    | _ |= _ => idtac
  end.

Ltac sep_destroy H :=
  sep normal in H;
  sep destruct H;
  sep split in H;
  sep_destroy' H.

Tactic Notation "sep" "destroy" hyp(H) :=
  sep_destroy H.
  
Lemma insert_star:forall s p r q l, p <==> q ** r -> (s |= l ** p <->  s |= q ** l **r).
Proof.
  intros.
  split;intros.
  sep_auto.
  destruct H with s.
  apply H1 in H0.
  sep_auto.
  sep_auto.
  destruct H with s.
  apply H2.
  sep_auto.
Qed.

Lemma asrt_eq_trans: forall p q r, p <==> q -> q <==> r -> p <==> r.
Proof.
  intros.
  split;intros.
  destruct H with s.
  destruct H0 with s.
  apply H4.
  apply H2;auto.
  destruct H with s.
  destruct H0 with s.
  apply H3.
  apply H5;auto.
Qed.


Lemma star_star_eq_rep:
  forall p q r q' A, (A <==> p ** q ** r) -> (q <==> q') -> (A <==> p ** q' ** r).
Proof.
  intros.
  split;intros.
  destruct H with s.
  apply H2 in H1.
  sep_auto.
  destruct H0 with H4.
  apply H5;auto.
  destruct H with s.
  apply H3.
  sep_auto.
  destruct H0 with H4.
  apply H6;auto.
Qed.

Lemma star_star_comm: forall p q r, p ** q ** r <==> q ** p ** r.
Proof.
  intros.
  split;intros;sep_auto.
Qed.

  
  Theorem Alvarenv_cancel :
  forall x t v1 v2 P Q,
    P ==> Q ->
    v1 = v2 ->
    L& x @ t == v1 ** P ==> L& x @ t == v2 ** Q.
Proof.
  intros; subst; sep_auto; auto.
Qed.

Theorem Agvarenv_cancel :
  forall x t v1 v2 P Q,
    P ==> Q ->
    v1 = v2 ->
    G& x @ t == v1 ** P ==> G& x @ t == v2 ** Q.
Proof.
  intros; subst; sep_auto; auto.
Qed.

Theorem Aptrmapsto_cancel :
  forall l t v1 v2 P Q perm ,
    P ==> Q ->
    v1 = v2 ->
    PV l @ t |=> v1 @ perm ** P ==> PV l @ t |=> v2 @ perm ** Q.
Proof.
  intros; subst; sep_auto; auto.
Qed.


  Lemma sep_aconj_r_aistrue_to_astar :
  forall P e t v,
    P ==> Rv e @ t == v ->
    P //\\ Aistrue e ==> P ** [| v <> Vint32 Int.zero /\ v <> Vnull /\ v <> Vundef |].
Proof.
  intros.
  apply aconj_elim in H0; destruct H0.
  lets H100 : H0.
  apply H in H100.
  cut (v <> Vint32 Int.zero /\ v <> Vnull /\ v <> Vundef); [ sep_auto | idtac ].
  gen H1 H100; clear; intros.
  simpl in *.
  destruct H1.
  destruct H.
  destruct H100.
  destruct H2.
  rewrite H in H1; inverts H1.
  unfold istrue in *.
  destruct v; tryfalse || intuition.
  inverts H1.
  rewrite Int.eq_true in H0; tryfalse.
  tryfalse.
  tryfalse.
  tryfalse.
Qed.

Lemma sep_aconj_r_aisfalse_to_astar :
  forall P e t v,
    P ==> Rv e @ t == v ->
    P //\\ Aisfalse e ==> P ** [| v = Vint32 Int.zero \/ v = Vnull |].
Proof.
  intros.
  apply aconj_elim in H0; destruct H0.
  lets H100 : H0.
  apply H in H100.
  cut (v = Vint32 Int.zero \/ v = Vnull); [ sep_auto | idtac ].
  gen H1 H100; clear; intros.
  simpl in *.
  destruct H1.
  destruct H.
  destruct H100.
  destruct H2.
  rewrite H in H1; inverts H1.
  unfold istrue in *.
  destruct v; tryfalse || intuition.
  remember (Int.eq i Int.zero) as bool; destruct bool; tryfalse.
  lets H100 : Int.eq_spec i Int.zero.
  rewrite <- Heqbool in H100.
  subst; intuition.
Qed.

Theorem aisfalse_prop_ptr :
  forall s P e v,
    s |= P ->
    s |= Aisfalse e ->
    (P ==> Rv e @ Tnull== v) ->
    s |=  [| v= Vnull |] ** P.
Proof.
  intros.
  sep_auto.
  simpl in H0.
  destruct H0.
  simpl in H1.
  apply H1 in H.
  destruct H.
  destruct H2.
  destruct H0.
  rewrite H in H0.
  inverts H0.
  clear -H2 H4 H H3.
  destruct s as [[]].
  destruct t as [[[[]]]].
  simpl in H2.
  induction e.
  simpl in H2;tryfalse.
  simpl in H.
  inverts H;auto.
  simpl in H2.
  remember (get e1 v) as  X.
  destruct X;tryfalse.
  destruct p.
  inverts H2.
  simpl in H.
  rewrite <- HeqX in H.
  unfold load in *;unfold loadm in *.
  remember (loadbytes m (b, BinNums.Z0) (typelen Tnull) ) as Y.
  destruct Y ;tryfalse.
  inverts H.
  unfold decode_val in *.
  destruct (proj_bytes l0);tryfalse.
  destruct l0;tryfalse.
  destruct m0;tryfalse.
  destruct l0;tryfalse.
  destruct m0;tryfalse.
  destruct l0;tryfalse.
  destruct m0;tryfalse.
  destruct l0;tryfalse.
  destruct m0;tryfalse.
  destruct l0;tryfalse.
  auto.
  remember (get e0 v) as  G.
  destruct G;tryfalse.
  destruct p.
  inverts H2.
  simpl in H.
  rewrite <- HeqX in H.
  rewrite <- HeqG in H.
  unfold load in *;unfold loadm in *.
  remember (loadbytes m (b, BinNums.Z0) (typelen Tnull) ) as Y.
  destruct Y ;tryfalse.
  inverts H.
  unfold decode_val in *.
  destruct (proj_bytes l0);tryfalse.
  destruct l0;tryfalse.
  destruct m0;tryfalse.
  destruct l0;tryfalse.
  destruct m0;tryfalse.
  destruct l0;tryfalse.
  destruct m0;tryfalse.
  destruct l0;tryfalse.
  destruct m0;tryfalse.
  destruct l0;tryfalse.
  auto.
  simpl in H2;tryfalse.
  simpl in H2.
  destruct (evaltype e (e0,e1,m));simpl in H2;tryfalse.
  destruct t;simpl in H2;tryfalse.
  simpl in H2.
  remember (evaltype e2 (e0, e1, m)) as E2.
  destruct E2;simpl in H2;tryfalse.
  remember (evaltype e3 (e0, e1, m)) as E3.
  destruct E3 ;simpl in H3;tryfalse.
  destruct t;destruct t0;destruct b;simpl in H2;tryfalse.
  simpl in H2.
  remember (evaltype e (e0, e1, m)) as  X.
  destruct X;tryfalse.
  destruct t;tryfalse.
  inverts H2.
  simpl in H.
  rewrite <- HeqX in H.
  remember (evalval e (e0, e1, m) ) as Y.
  destruct Y;tryfalse.
  destruct v;tryfalse.
  destruct x;simpl in H4;tryfalse;auto.
  destruct a0.
  unfold addrval_to_addr in H.
  unfold load in H.
  unfold load in *;unfold loadm in *.
  remember (loadbytes m (b, Int.unsigned i1) (typelen Tnull)) as F.
  destruct F;tryfalse.
  inverts H.
  unfold decode_val in *.
  destruct (proj_bytes l0);tryfalse.

  destruct l0;tryfalse.
  destruct m0;tryfalse.
  destruct l0;tryfalse.
  destruct m0;tryfalse.
  destruct l0;tryfalse.
  destruct m0;tryfalse.
  destruct l0;tryfalse.
  destruct m0;tryfalse.
  destruct l0;tryfalse.

  simpl in H2.
  destruct e;tryfalse.
  destruct ( evaltype (evar v) (e0, e1, m));tryfalse.
  destruct (evaltype e (e0, e1, m));tryfalse.
  destruct t;tryfalse.
  destruct ( evaltype (efield e i0) (e0, e1, m) );tryfalse.
  destruct (evaltype (earrayelem e2 e3) (e0, e1, m));tryfalse.
  simpl in H2.
  remember ( evaltype e (e0, e1, m)) as X.
  destruct X.
  destruct t;tryfalse.
  simpl in H.
  rewrite <- HeqX in H.
  rewrite H2 in H.
  destruct (evaladdr e (e0, e1, m));tryfalse.
  destruct v;tryfalse.
  destruct a0.
  unfold getoff in *.
  rewrite <- HeqX in H.
  destruct ( field_offset i0 d);tryfalse.
  destruct x;simpl in H4;tryfalse;auto.
  unfold addrval_to_addr in H.
  unfold load in H.
  unfold load in *;unfold loadm in *.
  remember (loadbytes m  (b, Int.unsigned (Int.add (Int.repr (Int.unsigned i2)) i3))
                      (typelen Tnull)) as F.
  destruct F;tryfalse.
  inverts H.
  unfold decode_val in *.
  destruct (proj_bytes l0);tryfalse.
  destruct l0;tryfalse.
  destruct m0;tryfalse.
  destruct l0;tryfalse.
  destruct m0;tryfalse.
  destruct l0;tryfalse.
  destruct m0;tryfalse.
  destruct l0;tryfalse.
  destruct m0;tryfalse.
  destruct l0;tryfalse.
  
  tryfalse.

  simpl in H2.
  destruct (evaltype e (e0, e1, m));simpl in H2;tryfalse.
  destruct t0;simpl in H2;tryfalse.
  destruct t;simpl in H2;tryfalse.
  destruct t;simpl in H2;tryfalse.
  destruct t;simpl in H2;tryfalse.
  destruct t;simpl in H2;tryfalse.
  destruct t;simpl in H2;tryfalse.
  destruct t;simpl in H2;tryfalse.
 
  
  simpl in H2.
  remember (evaltype e2 (e0, e1, m)) as X.
  destruct X;tryfalse.
  destruct t;tryfalse.
  remember (evaltype e3 (e0, e1, m)) as Y.
  destruct Y;tryfalse.
  destruct t0;tryfalse.
  inverts H2.
  destruct x;simpl in H4;tryfalse;auto.
  simpl in H.
  rewrite <- HeqX in H.
  rewrite <- HeqY in H.
  remember (evalval e2 (e0, e1, m)) as A.
  destruct A;tryfalse.
  destruct v;tryfalse.
  destruct a0.
  remember ( evalval e3 (e0, e1, m) ) as W.
  destruct W;tryfalse.
  destruct v;tryfalse.
  unfold load in *;unfold loadm in *.
  remember ( loadbytes m
                       (b,
                        Int.unsigned
                          (Int.add i1
                                   (Int.mul (Int.repr (BinInt.Z.of_nat (typelen Tnull))) i2)))
                       (typelen Tnull)) as K.
  destruct K;tryfalse.
  inverts H.
  unfold decode_val in *.
  destruct (proj_bytes l0);tryfalse.
  destruct l0;tryfalse.
  destruct m0;tryfalse.
  destruct l0;tryfalse.
  destruct m0;tryfalse.
  destruct l0;tryfalse.
  destruct m0;tryfalse.
  destruct l0;tryfalse.
  destruct m0;tryfalse.
  destruct l0;tryfalse.

  inverts H2.
  destruct x;simpl in H4;tryfalse;auto.
  simpl in H.
  rewrite <- HeqX in H.
  rewrite <- HeqY in H.
  remember (evalval e2 (e0, e1, m)) as A.
  destruct A;tryfalse.
  destruct v;tryfalse.
  destruct a0.
  remember ( evalval e3 (e0, e1, m) ) as W.
  destruct W;tryfalse.
  destruct v;tryfalse.
  unfold load in *;unfold loadm in *.
  remember ( loadbytes m
                       (b,
                        Int.unsigned
                          (Int.add i1
                                   (Int.mul (Int.repr (BinInt.Z.of_nat (typelen Tnull))) i2)))
                       (typelen Tnull)) as K.
  destruct K;tryfalse.
  inverts H.
  unfold decode_val in *.
  destruct (proj_bytes l0);tryfalse.
  destruct l0;tryfalse.
  destruct m0;tryfalse.
  destruct l0;tryfalse.
  destruct m0;tryfalse.
  destruct l0;tryfalse.
  destruct m0;tryfalse.
  destruct l0;tryfalse.
  destruct m0;tryfalse.
  destruct l0;tryfalse.

  inverts H2.
  destruct x;simpl in H4;tryfalse;auto.
  simpl in H.
  rewrite <- HeqX in H.
  rewrite <- HeqY in H.
  remember (evalval e2 (e0, e1, m)) as A.
  destruct A;tryfalse.
  destruct v;tryfalse.
  destruct a0.
  remember ( evalval e3 (e0, e1, m) ) as W.
  destruct W;tryfalse.
  destruct v;tryfalse.
  unfold load in *;unfold loadm in *.
  remember ( loadbytes m
                       (b,
                        Int.unsigned
                          (Int.add i1
                                   (Int.mul (Int.repr (BinInt.Z.of_nat (typelen Tnull))) i2)))
                       (typelen Tnull)) as K.
  destruct K;tryfalse.
  inverts H.
  unfold decode_val in *.
  destruct (proj_bytes l0);tryfalse.
  destruct l0;tryfalse.
  destruct m0;tryfalse.
  destruct l0;tryfalse.
  destruct m0;tryfalse.
  destruct l0;tryfalse.
  destruct m0;tryfalse.
  destruct l0;tryfalse.
  destruct m0;tryfalse.
  destruct l0;tryfalse.

   remember (evaltype e3 (e0, e1, m)) as Y.
  destruct Y;tryfalse.
  destruct t0;tryfalse.
  inverts H2.
  destruct x;simpl in H4;tryfalse;auto.
  simpl in H.
  rewrite <- HeqX in H.
  rewrite <- HeqY in H.
  remember (evalval e2 (e0, e1, m)) as A.
  destruct A;tryfalse.
  destruct v;tryfalse.
  destruct a0.
  remember ( evalval e3 (e0, e1, m) ) as W.
  destruct W;tryfalse.
  destruct v;tryfalse.
  unfold load in *;unfold loadm in *.
  remember ( loadbytes m
                       (b,
                        Int.unsigned
                          (Int.add i1
                                   (Int.mul (Int.repr (BinInt.Z.of_nat (typelen Tnull))) i2)))
                       (typelen Tnull)) as K.
  destruct K;tryfalse.
  inverts H.
  unfold decode_val in *.
  destruct (proj_bytes l0);tryfalse.
  destruct l0;tryfalse.
  destruct m0;tryfalse.
  destruct l0;tryfalse.
  destruct m0;tryfalse.
  destruct l0;tryfalse.
  destruct m0;tryfalse.
  destruct l0;tryfalse.
  destruct m0;tryfalse.
  destruct l0;tryfalse.

  inverts H2.
  destruct x;simpl in H4;tryfalse;auto.
  simpl in H.
  rewrite <- HeqX in H.
  rewrite <- HeqY in H.
  remember (evalval e2 (e0, e1, m)) as A.
  destruct A;tryfalse.
  destruct v;tryfalse.
  destruct a0.
  remember ( evalval e3 (e0, e1, m) ) as W.
  destruct W;tryfalse.
  destruct v;tryfalse.
  unfold load in *;unfold loadm in *.
  remember ( loadbytes m
                       (b,
                        Int.unsigned
                          (Int.add i1
                                   (Int.mul (Int.repr (BinInt.Z.of_nat (typelen Tnull))) i2)))
                       (typelen Tnull)) as K.
  destruct K;tryfalse.
  inverts H.
  unfold decode_val in *.
  destruct (proj_bytes l0);tryfalse.
  destruct l0;tryfalse.
  destruct m0;tryfalse.
  destruct l0;tryfalse.
  destruct m0;tryfalse.
  destruct l0;tryfalse.
  destruct m0;tryfalse.
  destruct l0;tryfalse.
  destruct m0;tryfalse.
  destruct l0;tryfalse.

  inverts H2.
  destruct x;simpl in H4;tryfalse;auto.
  simpl in H.
  rewrite <- HeqX in H.
  rewrite <- HeqY in H.
  remember (evalval e2 (e0, e1, m)) as A.
  destruct A;tryfalse.
  destruct v;tryfalse.
  destruct a0.
  remember ( evalval e3 (e0, e1, m) ) as W.
  destruct W;tryfalse.
  destruct v;tryfalse.
  unfold load in *;unfold loadm in *.
  remember ( loadbytes m
                       (b,
                        Int.unsigned
                          (Int.add i1
                                   (Int.mul (Int.repr (BinInt.Z.of_nat (typelen Tnull))) i2)))
                       (typelen Tnull)) as K.
  destruct K;tryfalse.
  inverts H.
  unfold decode_val in *.
  destruct (proj_bytes l0);tryfalse.
  destruct l0;tryfalse.
  destruct m0;tryfalse.
  destruct l0;tryfalse.
  destruct m0;tryfalse.
  destruct l0;tryfalse.
  destruct m0;tryfalse.
  destruct l0;tryfalse.
  destruct m0;tryfalse.
  destruct l0;tryfalse.
Qed.

Lemma array_asrt_imp_length :
  forall s l t n vl P,
    s|= Aarray l (Tarray t n) vl ** P ->
       length vl = n.
Proof.
  intros.
  gen s l t vl P H.
  induction n.
  intros.
  destruct vl.
  simpl;eauto.
  unfold Aarray in H.
  unfold Aarray' in H. 
  simpl in H.
  do 6 destruct H.
  simp join.
  inverts H3.
  intros.
  destruct vl.
  simpl in H.
  do 6 destruct H.
  simp join.
  inverts H3.
  unfold Aarray in H.
  unfold  Aarray' in H; fold Aarray' in H.
  destruct l.
  simpl. 
  erewrite IHn.
  auto.
  unfold Aarray.
  sep lift 2%nat in H.
  apply H.
Qed.

Lemma GAarray_imp_length :
  forall s x t n vl,
    s |= GAarray x (Tarray t n) vl -> length vl = n.
Proof.
  intros.
  unfold GAarray in H.
  sep normal in H; sep destruct H.
  sep lift 2%nat in H.
  eapply array_asrt_imp_length; eauto.
Qed.

Lemma LAarray_imp_length :
  forall s x t n vl,
    s |= LAarray x (Tarray t n) vl -> length vl = n.
Proof.
  intros.
  unfold LAarray in H.
  sep normal in H; sep destruct H.
  sep lift 2%nat in H.
  eapply array_asrt_imp_length; eauto.
Qed.


Lemma GAarray_imp_length_P :
  forall s x t n vl P,
    s |= GAarray x (Tarray t n) vl**P -> length vl = n.
Proof.
  intros.
  unfold GAarray in H.
  sep normal in H; sep destruct H.
  sep lift 2%nat in H.
  eapply array_asrt_imp_length; eauto.
Qed.

Lemma LAarray_imp_length_P :
  forall s x t n vl,
    s |= LAarray x (Tarray t n) vl -> length vl = n.
Proof.
  intros.
  unfold LAarray in H.
  sep normal in H; sep destruct H.
  sep lift 2%nat in H.
  eapply array_asrt_imp_length; eauto.
Qed.

Lemma array'_length_intro: 
  forall n   vl   s b i t P,
    s |= Aarray' (b,i) n t vl ** P -> length vl = n.
Proof.
  intros.
  sep destroy H.
  inductions n; inductions vl; simpl; intros; simp join; tryfalse;auto.
  simpl Aarray' in H0.
  sep destroy H0.
  assert (length vl = n).
  
  eapply IHn; eauto.
  omega.     
Qed.

Lemma array_length_intro: 
  forall s  t n x vl  P,
    s |= Aarray x (Tarray t n) vl ** P -> length vl = n.
Proof.
  intros.
  unfold Aarray in H.
  destruct x.
  apply array'_length_intro in H.
  auto.
Qed.


Lemma dllseg_head_isptr :
  forall l v1 v2 v3   t  n p P s,
    s |= dllseg v1 v2  v3 Vnull l t n p ** P  -> isptr v1.
Proof.
  inductions l. 
  intros.
  simpl in H.
  simp join ; unfolds; simpl; auto.
  intros.
  unfold dllseg in H.
  fold dllseg in H.
  sep destroy H.
  right.
  unfold node in H3.
  sep destroy H3.
  simp join.
  eauto.
Qed.

Lemma sll_head_isptr : 
  forall v' s  v t n P, s |= sll v v' t n ** P  -> isptr v.
Proof.
  inductions v'. 
  intros.
  simpl in H.
  simp join ; unfolds; simpl; auto.
  intros.
  unfold sll in H.
  unfold sllseg  in H.
  fold sllseg in H.
  sep destroy H.
  right.
  unfold node in H2.
  sep destroy H2.
  simp join.
  eauto.
Qed.


 Lemma sllseg_head_isptr :
   forall  vl l t n s P, 
     s |= sllseg l Vnull vl t n ** P -> isptr l.
 Proof.
   inductions vl ; intros; simpl in *; tryfalse;  simp join; 
   unfolds; simpl; eauto.
 Qed.    

 Lemma disj_star_elim'' :
   forall p q x y r: asrt, (( p\\//q\\//x\\//y) ** r) ==> (p**r) \\// (q**r) \\// (x**r) \\// (y**r).
 Proof.
   intros.
   simpl in *.
   simp join.
   destruct H3.
   left.
   do 6 eexists; splits; eauto.
   repeat destruct H;[right; left| right; right; left| right;right;right]; do 6 eexists; splits; eauto.
 Qed.

Lemma disj_star_elim''' :
  forall p q x y p' q' x' y' p'' q'' x'' y'' r z : asrt,
    ((p \\// q \\// x \\// y \\// p' \\// q' \\// x' \\// y' \\// p'' \\// q'' \\// x'' \\// y'') ** z) ** r ==>
                                                                                                        p ** z ** r \\// q ** z ** r \\// x ** z ** r \\// y ** z ** r \\//  p' ** z ** r \\// q' ** z ** r \\// x' ** z ** r \\// y' ** z ** r \\//  p'' ** z ** r \\// q'' ** z ** r \\// x'' ** z ** r \\// y'' ** z ** r.
Proof.
  intros.
  sep_auto.
  apply disj_star_elim in H.
  destruct H.
  left; auto.
  apply disj_star_elim in H.
  destruct H.
  branch 2; auto.
  apply disj_star_elim in H.
  destruct H.
  branch 3; auto.
  apply disj_star_elim in H.
  destruct H.
  branch 4; auto.
  apply disj_star_elim in H.
  destruct H.
  branch 5; auto.
  apply disj_star_elim in H.
  destruct H.
  branch 6; auto.
  apply disj_star_elim in H.
  destruct H.
  branch 7; auto.
  apply disj_star_elim in H.
  destruct H.
  branch 8; auto.
  apply disj_star_elim in H.
  destruct H.
  right.
  branch 8; auto.
  apply disj_star_elim in H.
  destruct H.
  right.
  right.
  branch 8; auto.
  apply disj_star_elim in H.
  destruct H.
  right.
  right.
  right.
  branch 8; auto.
  right.
  right.
  right.
  right.
  branch 8; auto.
Qed.

Lemma disj_star_elim'
: forall p q x y r z: asrt, 
    ((p \\// q \\// x \\// y)** z) ** r ==> 
    	(p ** z ** r) \\// (q ** z ** r) \\// (x** z** r) \\// (y** z ** r).
Proof.
  intros.
  apply disj_star_elim''.
  sep_auto.
Qed.



Module DeprecatedTactic.
  Ltac mytac_1 :=
    match goal with
      | H : exists _, _ |- _ => destruct H; mytac_1
      | H : (_ /\ _) |- _ => destruct H; mytac_1
      | |- _ /\ _ => split; mytac_1

      | H : emposabst _ |- _ =>
        unfold emposabst in H; subst; mytac_1

      | H :  join empmem _ _ |- _ =>
        apply  map_join_emp'' in H; subst; mytac_1

      | H :  join _ empmem _ |- _ =>
        apply  map_join_comm in H; apply  map_join_emp'' in H; subst; mytac_1

      | |-  join empmem _ _ =>
        apply  map_join_comm;apply  map_join_emp; mytac_1
      | |-  join _ empmem _ =>
        apply  map_join_emp; mytac_1
      (*
    | H : join empenv _ _ |- _ =>
      apply map_join_emp_eq in H; subst; mytac_1
    | H : join _ empenv _ |- _ =>
      apply map_join_comm in H; apply map_join_emp_eq in H; subst; mytac_1
    | |- join empenv _ _ =>
      apply map_join_emp; mytac_1
    | |- join _ empenv _ =>
      apply map_join_comm; apply map_join_emp; mytac_1

    | H : join empabst _ _ |- _ =>
      apply map_join_emp_eq in H; subst; mytac_1
    | H : join _ empabst _ |- _ =>
      apply map_join_comm in H; apply map_join_emp_eq in H; subst; mytac_1
    | |- join empabst _ _ =>
       apply map_join_emp; mytac_1
    | |- join _ empabst _ =>
      apply map_join_comm; apply map_join_emp; mytac_1
       *)

      | H : join ?a ?b ?ab |- join ?b ?a ?ab =>
        apply map_join_comm; auto

      | H : (_, _) = (_, _) |- _ => inversion H; clear H; mytac_1
      | H : ?x = ?x |- _ => clear H; mytac_1
      | |- ?x = ?x => reflexivity

      | |-  join _ ?a ?a => apply  map_join_comm; mytac_1
      | |-  join ?a _ ?a => apply  map_join_emp; mytac_1

      | |- empmem = _ => reflexivity; mytac_1
      | |- _ = empmem => reflexivity; mytac_1

      | |- empenv = _ => reflexivity; mytac_1
      | |- _ = empenv => reflexivity; mytac_1

      | |- emposabst _ => unfold emposabst; reflexivity; mytac_1
      | |- empabst = _ => reflexivity; mytac_1
      | |- _ = empabst => reflexivity; mytac_1

      | |- empisr = _ => reflexivity; mytac_1
      | |- _ = empisr => reflexivity; mytac_1

      | H : True |- _ => clear H; mytac_1
      | |- True => auto
      | _ => try (progress subst; mytac_1)
    end.

  Ltac mytac := repeat progress mytac_1.
End DeprecatedTactic.


Tactic Notation "sep" "pauto"  :=
  first [ solve [ sep_semiauto_nosplit; sep_pure ]
        | sep_semiauto_nosplit ].
