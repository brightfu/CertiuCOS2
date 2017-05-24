Require Import include_frm.
Require Import lmachLib.
Require Import inline_definitions.
Require Import symbolic_execution.
Require Import symbolic_lemmas.
Require Import meta_find.
Require Import sep_auto.

Local Open Scope code_scope.

Definition memmono_asrt p :=
  forall genv lenv mem isr localst osabst absop mem' mem'',
    join mem mem'' mem' ->
    (genv, lenv, mem, isr, localst, osabst, absop) |= p ->
    (genv, lenv, mem', isr, localst, osabst, absop) |= p.

Definition osabstmono_asrt p :=
  forall genv lenv mem isr localst osabst absop osabst' osabst'',
    join osabst osabst'' osabst' ->
    (genv, lenv, mem, isr, localst, osabst, absop) |= p ->
    (genv, lenv, mem, isr, localst, osabst', absop) |= p.

Definition mono_asrt p :=
  osabstmono_asrt p /\ memmono_asrt p.

Lemma Lv_memmono:
  forall a b c,
    memmono_asrt (Lv a @ b == c).
Proof.
  intros.
  unfolds.
  intros.
  simpl.
  simpl in H0.
  simpljoin.
  splits.
  eapply lmachLib.evaladdr_mono.
  eauto.
  auto.
  erewrite lmachLib.evaltype_mono.
  eauto.
  eauto.
Qed.

Lemma Lv_osabstmono:
  forall a b c,
    osabstmono_asrt (Lv a @ b == c).
Proof.
  intros.
  unfolds.
  intros.
  simpl in *.
  auto.
Qed.

Lemma Lv_mono:
  forall a b c,
    mono_asrt (Lv a @ b == c).
Proof.
  intros.
  unfolds.
  split.
  apply Lv_osabstmono.
  apply Lv_memmono.
Qed.

Lemma Rv_memmono:
  forall a b c,
    memmono_asrt (Rv a @ b == c).
Proof.
  intros.
  unfolds.
  intros.
  simpl.
  simpl in H0.
  simpljoin; splits.
  erewrite lmachLib.evalval_mono.
  eauto.
  eauto.
  eauto.
  erewrite lmachLib.evaltype_mono.
  eauto.
  eauto.
  auto.
Qed.

Lemma Rv_osabstmono:
  forall a b c,
    osabstmono_asrt (Rv a @ b == c).
Proof.
  intros.
  unfolds.
  intros.
  simpl in *.
  auto.
Qed.

Lemma Rv_mono:
  forall a b c,
    mono_asrt (Rv a @ b == c).
Proof.
  intros.
  unfolds.
  split.
  apply Rv_osabstmono.
  apply Rv_memmono.
Qed.

Lemma startrue_memmono:
  forall p,
         memmono_asrt (p ** Atrue).
Proof.
  intros.
  unfolds.
  intros.
  simpl in H0.
  simpljoin.
  simpl.
  do 6 eexists.
  splits.
  eauto.
  2:eauto.
  3:eauto.
  join auto.
  join auto.
  auto.
Qed.


Lemma startrue_osabstmono:
  forall p,
         osabstmono_asrt (p ** Atrue).
Proof.
  intros.
  unfolds.
  intros.
  simpl in H0.
  simpljoin.
  simpl.
  do 6 eexists.
  splits.
  eauto.
  2:eauto.
  3:eauto.
  join auto.
  join auto.
  auto.
Qed.

Lemma startrue_mono:
  forall p,
    mono_asrt ( p ** Atrue).
Proof.
  intros; unfolds.
  split.
  apply startrue_osabstmono.
  apply startrue_memmono.
Qed.

  

Lemma monoasrt_mono:
  forall s p q,
    mono_asrt p ->
    s|= p**q  ->
    s |= p .
Proof.
  intros.
  simpl in *.
  simpljoin.
  simpl.
  unfolds in H.
  simpljoin.
  unfolds in H0.
  destruct s as [[[[[[]]]]]].
  eapply H0.
  simpl in H4.
  simpl in H5.
  eauto.
  simpl in H4.
  simpl in H5.
  eapply H.
  eauto.
  auto.
Qed.

Lemma monoasrt_imp_mono:
  forall s p q r,
    mono_asrt r ->
    s |= p ** q ->
    p==>r ->
    s |= r.
Proof.
  intros.
  destruct s as [[[[[[]]]]]].
  unfolds in H.
  simpljoin.
  simpl in H0.
  simpljoin.
  eapply H.
  eauto.
  eapply H2.
  eauto.
  apply H1.
  auto.
Qed.

Definition emposabst_asrt p :=
  forall genv lenv mem isr localst osabst absop,
    (genv, lenv, mem, isr, localst, osabst, absop) |= p ->
    emposabst osabst.

(*
Goal forall a b c, emposabst_asrt (PV a @ b |-> c).
intros.
unfolds.
intros.
simpl in H.
mytac.
Qed.

Goal forall p q s r,  memmono_asrt p -> emposabst_asrt q -> r ==> p -> s |= q ** r  -> s |= p.
intros.
destruct s as [[[[[[]]]]]].
simpl in *.

mytac.
eapply H.
apply MemMod.join_comm.
eauto.
apply H0 in H6.
unfolds in H6.
subst x2.
apply OSAbstMod.join_comm in H5.
apply asrtLib.Abs_join_eq in H5.
subst x3.
apply H1.
auto.
Qed.
*)

Lemma sep_infer_conjE:
  forall p a b,
    p ==> a //\\ b  ->
    (p==>a /\ p==>b). 
  intros.
  simpl in H.
  split.
  intro.

  intros.
  lets fff: H s H0.    
  tauto.
  intro.
  intros.
  lets fff: H s H0.    
  tauto.
Qed.

Lemma sep_infer_conjI:
  forall p a b,
    ( p==>a /\ p==>b) ->
    p ==> a //\\ b . 
  intros.

  eapply seplog_lemmas.aconj_mono.
  simpljoin; auto.
  exact s0.
  simpljoin; auto.
  exact s1.
  simpl.
  splits; auto.
Qed.

Ltac sep_conj_handlerH H :=
  let H' := fresh in
  let H'' := fresh in
  match type of H with
    | _ ==> _ //\\ _ =>
      apply sep_infer_conjE in H; destruct H as ( H' & H'') ; try sep_conj_handlerH H''
  end.


(* below is tactic for apply inline function *)

(* inline pre/ post unfolder *)

Ltac inline_unfolder inl_pp inline_record :=
  unfold inl_pp; unfold inline_record;
  let a := eval simpl in (inl_pp inline_record) in unfold a; simpl inl_pp.
Ltac inline_pre_unfolder inline_record :=
  inline_unfolder inl_pre inline_record.
Ltac inline_post_unfolder inline_record :=
  inline_unfolder inl_post inline_record.
(* assume post is ? *)

(* Ltac inline_forward :=
 *   match goal with
 *     | |- {| _ , _ , _, _, _, _|} |- _ {{ _ }} inline_call ?inline_record _ {{ _ }} => eapply backward_rule2; [eapply (inl_proof inline_record)  | intro;intros;inline_pre_unfolder inline_record |idtac..]
 *   end. *)
Local Open Scope int_scope.

Lemma arrayLv :
  forall ntbl T sz v,
    L& ntbl @ Tarray T sz == (v, $0) ==> Rv ntbl ′ @ Tarray T sz == Vptr (v, $0).
Proof.
  intros.
  unfolds.
  simpl in H.
  simpljoin; splits.
  destruct s as [[[[[[]]]]]].
  simpl in *.
  rewrite H.
  simpl.
  auto.
  destruct s as [[[[[[]]]]]].
  simpl in *.
  rewrite H.
  auto.
  intro; tryfalse.
Qed.


(* for sep get lv *)
Ltac is_ldom_asrt H :=
  match H with
    | A_dom_lenv _ => constr:1%nat
    | _ => constr:0%nat
  end.

Ltac is_gref_asrt H :=
  match H with
    | G& ?l @ _ == _ => constr:(1%nat, l)
    | _ => constr:0%nat
  end.

Ltac gen_notin_lenv H name :=
  match meta_find_in_H is_ldom_asrt 1%nat H with
    | fres_Y ?n ?A =>
      match A with
        | A_dom_lenv ?ls =>
          assert (var_notin_dom name ls = true); auto
        | _ => fail 2
      end
    | _ => fail 1
  end.

Lemma Lref2Lv : forall n T p, L& n @ T == (p, $0) ==> Lv n ′ @ T == (p, $0).
Proof.
  intros.
  unfolds.
  simpl in H.
  destruct s as [[[[[[]]]]]].
  simpljoin; simpl in *.
  rewrite H.
  auto.
Qed.

Lemma array_lv2rv: forall a t sz l, 
                     Lv a ′  @ Tarray t sz == l ==> Rv a ′  @ Tarray t sz == Vptr l.
Proof.
  intros.
  destruct s as [[[[[[]]]]]].
  simpl in *.
  simpljoin.
  splits.
  destruct (get e0 a).
  destruct p.
  inverts H0.
  inverts H.
  unfolds.
  simpl.
  auto.

  destruct (get e a).
  destruct p.
  inverts H.    
  inverts H0.
  unfolds.	
  auto.
  auto.

  auto.
  intro; tryfalse.
Qed.

Ltac sep_get_lv_g := 
  match goal with
    | H: ?s |=?P |- ?s |= Lv ?name ′ @  _ ==  _ =>
      meta_find_and_lift_in_H is_gref_asrt (1%nat, name) H;
        meta_find_and_lift_in_H is_ldom_asrt 1%nat H; gen_notin_lenv H name
  end;eapply gvar_to_lv; eapply dom_lenv_imp_notin_lenv; eauto.

Ltac sep_get_lv := sep_get_lv_g.

Ltac lrv_conj_solver :=
  match goal with
    | _ : _ |- _ |= _ //\\ _ => split; lrv_conj_solver
    | _ => idtac
  end.


Ltac lrv_solver :=
  lrv_conj_solver;
  try lazymatch goal with
| |- _ |= Rv _ @ Tarray _ _ == _ => eapply array_lv2rv; sep_get_lv
| |- _ |= Lv _ @ _ == _          => sep_get_lv
| |- _ |= Rv _ @ _ == _          => sep_get_rv
end.

(* end of sep get lv*)

(* combine X& and PV *)

Inductive pattern : Type :=
| pattern_default : pattern
| pattern_lvarenv : pattern
| pattern_gvarenv : pattern
| pattern_memory : pattern.

Ltac asrt_to_pattern Hp :=
  match Hp with
    | L& _ @ _ == _ => constr:(pattern_lvarenv)
    | G& _ @ _ == _ => constr:(pattern_gvarenv)
    | PV ?l @ _ |-> _ => constr:(pattern_memory, l)
    | Aarray ?l _ _ => constr: (pattern_memory, l)
    | _ => constr:(pattern_default, Hp)
  end.

Ltac myliftH n H :=
  let b:= eval compute in n in
      sep lift b in H.

Goal forall n T b v P, G& n @ T == (b, $0) ** PV (b, $0) @ T |-> v ** P ==> GV n @ T |-> v ** P.
Proof.
  intros.
  unfold Agvarmapsto.
  sep pauto.
Save GrefPV.

Goal forall n T p v P, G& n @ T == p ** Aarray p T v **P ==> GAarray n T v ** P.
Proof.
  intros.
  unfold GAarray.
  sep pauto.
Save GrefArray.  

Ltac combineGrefH H :=
  match type of H with
    | ?s |= ?P  =>
      match find_match P pattern_gvarenv with
        | (some ?n, ?AA) =>  match AA with
                                 (G& _ @ _ == ?l) =>
                                 match find_match P (pattern_memory, l) with
                                   | (some ?m, ?BB) =>  sep lift m in H; sep lift n in H;
                                                        match BB with
                                                          | PV _ @ _ |-> _ => apply GrefPV in H
                                                          |	Aarray _ _ _ => apply GrefArray in H
                                                        end
                                 end
                             end
      end
  end.

(* end of combine X& and PV *)
