Require Import include_frm.

Lemma good_frm_star : 
  forall p q, GoodFrm p -> GoodFrm q -> 
              GoodFrm (p ** q). 
Proof.
  introv Hp Hq.
  simpl; auto.
Qed.

Lemma good_frm_ex :
  forall (t:Type)  (p : t -> asrt), 
    (forall x, GoodFrm (p x)) -> GoodFrm (EX x, p x).
Proof.
  intros.
  simpl.
  auto.
Qed.

Lemma good_frm_aemp :
  GoodFrm ( Aemp).
Proof.
  simpl; auto.
Qed.


Lemma good_frm_lenv : 
  forall x , GoodFrm ( A_dom_lenv x).
Proof.
  intros. simpl; auto.
Qed.


Lemma good_frm_astruct': 
  forall l dls vl,  GoodFrm (Astruct' l dls vl). 
Proof.  
  introv.
  gen dls l vl.
  inductions dls; intros; simpl; jauto.
  destruct vl; simpl; auto.
  destruct vl; simpl; auto.
  destruct t; destruct l; simpl; auto.
Qed.

Lemma good_frm_astruct : 
  forall  l  t vl , GoodFrm (Astruct l t vl ).
Proof.
  intros.
  unfolds Astruct.
  destruct t; simpl; auto.
  apply good_frm_astruct'.
Qed.

Lemma good_frm_sllseg : 
  forall vl head tail  t next, 
    GoodFrm (sllseg head tail vl t next). 
Proof.
  inductions vl; intros;  simpl; jauto.
  splits; auto.
  intros; splits; auto.
  intros; splits;eauto.
  apply good_frm_astruct.
Qed.    

Lemma  good_frm_sll : 
  forall head vl t next, GoodFrm (sll head vl t next). 
Proof.
  intros.
  unfold sll.
  apply good_frm_sllseg.
Qed.


Lemma good_frm_dllseg : 
  forall vl head hp tail tn t next pre, 
    GoodFrm (dllseg head hp tail tn vl t next pre). 
Proof.
  inductions vl; intros;  simpl; jauto.
  splits; auto.
  intros; splits; auto.
  intros; splits;eauto.
  apply good_frm_astruct.
Qed.   

Lemma good_frm_array' : 
  forall x n t vl,  GoodFrm (Aarray' x n t vl).
Proof.
  introv.
  gen n t vl  x.
  inductions n.
  intros.
  simpl.
  destruct vl; simpl; auto.
  intros.
  simpl.
  destruct vl; simpl; auto.
  destruct x.
  simpl;splits; auto.
Qed.

Lemma good_frm_array :
  forall x  t vl,  GoodFrm (Aarray x  t vl).
Proof.
  introv.
  unfold Aarray.
  destruct t; try simpl; auto.
  apply good_frm_array'.
Qed.

Lemma good_frm_garray:
  forall l t n vl, 
    GoodFrm (GAarray l (Tarray t n) vl).
Proof.
  introv.
  unfold GAarray.
  simpl.
  intros.
  splits; auto.
  apply good_frm_array'.
Qed.

Lemma good_frm_pure: 
  forall (p:Prop), GoodFrm (Apure p). 
Proof.
  intros. simpl ;  auto.
Qed.

Lemma good_frm_absop : 
  forall a b, GoodFrm (Aabsdata a b).
Proof.
  intros; simpl; auto.
Qed.

Lemma good_frm_perm: 
  forall x t v b,  GoodFrm (x # t |=> v @ b).
Proof. 
  intros; simpl; auto.
Qed.


Lemma good_frm_gvar_half: 
  forall x t v,  GoodFrm (GV x @ t |-r-> v).
Proof. 
  intros; simpl; auto.
Qed.

Hint Resolve good_frm_gvar_half : good_frm_lemmas.

Lemma good_frm_lvar_half: 
  forall x t v,  GoodFrm (LV x @ t |-r-> v).
Proof. 
  intros. simpl. auto.
Qed.

Hint Resolve good_frm_lvar_half : good_frm_lemmas.

Lemma good_frm_gvar: 
  forall x t v,  GoodFrm (GV x @ t |-> v).
Proof. 
  intros; simpl; auto.
Qed.

Hint Resolve good_frm_gvar : good_frm_lemmas.

Lemma good_frm_lvar: 
  forall x t v,  GoodFrm (LV x @ t |-> v).
Proof. 
  intros. simpl. auto.
Qed.

Hint Resolve good_frm_lvar : good_frm_lemmas.

Lemma good_frm_ptr : 
  forall x t v, GoodFrm (PV x@t |-> v).
Proof. 
  intros. simpl. auto.
Qed.

Lemma good_frm_ptr_half: 
  forall x t v, GoodFrm (PV x@t |-r-> v).
Proof. 
  intros. simpl. auto.
Qed.

Hint Resolve good_frm_ptr_half: good_frm_lemmas.
Hint Resolve good_frm_perm: good_frm_lemmas.
Hint Resolve good_frm_aemp : good_frm_lemmas.
Hint Resolve good_frm_ptr : good_frm_lemmas.
Hint Resolve good_frm_astruct' : good_frm_lemmas.
Hint Resolve  good_frm_astruct  : good_frm_lemmas.
Hint Resolve good_frm_sllseg : good_frm_lemmas.
Hint Resolve  good_frm_sll : good_frm_lemmas.
Hint Resolve  good_frm_dllseg : good_frm_lemmas.
Hint Resolve  good_frm_array : good_frm_lemmas.
Hint Resolve   good_frm_garray: good_frm_lemmas.
Hint Resolve good_frm_pure : good_frm_lemmas.
Hint Resolve good_frm_absop : good_frm_lemmas.
Hint Resolve good_frm_array' : good_frm_lemmas.
Hint Resolve good_frm_array : good_frm_lemmas.
Hint Resolve good_frm_garray : good_frm_lemmas.
Hint Resolve good_frm_lenv : good_frm_lemmas.

Ltac good_frm_sovler := 
  match goal with
   | |- GoodFrm ?p =>
     match p with
         | Aexists _  => apply good_frm_ex; intros; good_frm_sovler
         | ?p1 ** ?p2 => apply good_frm_star; good_frm_sovler
         | _ =>   first [auto with good_frm_lemmas | simpl; auto]
     end
   | _ => idtac
end.


Lemma  can_change_aop_star : 
  forall p q,  can_change_aop p ->  can_change_aop q -> 
               can_change_aop (p ** q). 
Proof.
  introv Hp Hq.
  simpl; auto.
Qed.

Lemma  can_change_aop_ex :
  forall (t:Type)  (p : t -> asrt), 
    (forall x,  can_change_aop (p x)) ->  can_change_aop (EX x, p x).
Proof.
  intros.
  simpl.
  auto.
Qed.

Lemma  can_change_aop_aemp :
   can_change_aop ( Aemp).
Proof.
  simpl; auto.
Qed.


Lemma  can_change_aop_lenv : 
  forall x , GoodFrm ( A_dom_lenv x).
Proof.
  intros. simpl; auto.
Qed.

Hint Resolve
     can_change_aop_star
     can_change_aop_ex
     can_change_aop_aemp
     can_change_aop_lenv
        : can_change_aop.


Theorem can_change_aop_ptrmapsto_perm :
  forall l t v b,
    can_change_aop (l# t |=> v@b).
Proof.
  intros.
  simpl;auto.
Qed.

Hint Resolve can_change_aop_ptrmapsto_perm : can_change_aop.
  

Theorem can_change_aop_ptrmapsto :
  forall l t v,
    can_change_aop (PV l @ t |-> v).
Proof.
  intros.
  unfold Aptrmapsto.
  unfold can_change_aop; fold can_change_aop; intuition auto.
Qed.

Theorem can_change_aop_ptrmapsto_half :
  forall l t v,
    can_change_aop (PV l @ t |-r-> v).
Proof.
  intros.
  auto with can_change_aop.
Qed.

Hint Resolve can_change_aop_ptrmapsto_half : can_change_aop.


Theorem can_change_aop_lvarenv :
  forall x t a,
    can_change_aop (L& x @ t == a).
Proof.
  intros.
  unfold Alvarenv'.
  unfold can_change_aop; fold can_change_aop; intuition auto.
Qed.

Theorem can_change_aop_gvarenv :
  forall x t a,
    can_change_aop (G& x @ t == a).
Proof.
  intros.
  unfold Agvarenv'.
  unfold can_change_aop; fold can_change_aop; intuition auto.
Qed.


Theorem can_change_aop_half_lvarmapsto :
  forall x t v,
    can_change_aop (LV x @ t |-r-> v).
Proof.
  intros.
  simpl ; auto.
Qed.

Theorem can_change_aop_half_gvarmapsto :
  forall x t v,
    can_change_aop (GV x @ t |-r-> v).
Proof.
  intros.
  simpl; auto.
Qed.

Hint Resolve can_change_aop_half_lvarmapsto can_change_aop_half_gvarmapsto : can_change_aop.


Hint Resolve can_change_aop_ptrmapsto can_change_aop_lvarenv can_change_aop_gvarenv : can_change_aop.

Theorem can_change_aop_lvarmapsto :
  forall x t v,
    can_change_aop (LV x @ t |-> v).
Proof.
  intros.
  unfold Alvarmapsto.
  unfold can_change_aop; fold can_change_aop; intuition auto with can_change_aop.
Qed.

Theorem can_change_aop_gvarmapsto :
  forall x t v,
    can_change_aop (GV x @ t |-> v).
Proof.
  intros.
  unfold Agvarmapsto.
  unfold can_change_aop; fold can_change_aop; intuition auto with can_change_aop.
Qed.

Hint Resolve can_change_aop_lvarmapsto can_change_aop_gvarmapsto : can_change_aop.



Theorem can_change_aop_ptrarray' :
  forall l n t vl,
    can_change_aop (Aarray' l n t vl).
Proof.
  intros.
  gen n l t.
  induction vl; induction n; intros; unfold Aarray'; fold Aarray'.
  unfold can_change_aop; fold can_change_aop; intuition auto with can_change_aop.
  unfold can_change_aop; fold can_change_aop; intuition auto with can_change_aop.
  unfold can_change_aop; fold can_change_aop; intuition auto with can_change_aop.
  destruct l.
  unfold can_change_aop; fold can_change_aop; intuition auto with can_change_aop.
Qed.  

Hint Resolve can_change_aop_ptrarray' : can_change_aop.

Theorem can_change_aop_ptrarray :
  forall l t vl,
    can_change_aop (Aarray l t vl).
Proof.
  unfold Aarray; intros.
  destruct t; unfold can_change_aop; fold can_change_aop; intuition auto with can_change_aop.
Qed.  

Hint Resolve can_change_aop_ptrarray : can_change_aop.

Theorem can_change_aop_lvararray :
  forall x t vl,
    can_change_aop (LAarray x t vl).
Proof.
  unfold LAarray; intros.
  destruct t; unfold can_change_aop; fold can_change_aop; intuition auto with can_change_aop.
Qed.  

Theorem can_change_aop_gvararray :
  forall x t vl,
    can_change_aop (GAarray x t vl).
Proof.
  unfold GAarray; intros.
  destruct t; unfold can_change_aop; fold can_change_aop; intuition auto with can_change_aop.
Qed.  

Hint Resolve can_change_aop_lvararray can_change_aop_gvararray : can_change_aop.

Theorem can_change_aop_struct' :
  forall l dls ls,
    can_change_aop (Astruct' l dls ls).
Proof.
  intros.
  gen dls l.
  induction ls; induction dls; intros; unfold Astruct'; fold Astruct'.
  unfold can_change_aop; fold can_change_aop; intuition auto with can_change_aop.
  unfold can_change_aop; fold can_change_aop; intuition auto with can_change_aop.
  unfold can_change_aop; fold can_change_aop; intuition auto with can_change_aop.
  destruct l. 
  destruct t; unfold can_change_aop; fold can_change_aop; intuition auto with can_change_aop.
Qed.

Hint Resolve can_change_aop_struct' : can_change_aop.

Theorem can_change_aop_struct :
  forall l t ls,
    can_change_aop (Astruct l t ls).
Proof.
  intros.
  unfold Astruct; intros.
  destruct t; unfold can_change_aop;
  fold can_change_aop; intuition auto with can_change_aop.
Qed.

Hint Resolve can_change_aop_struct : can_change_aop.

Theorem can_change_aop_sllseg :
  forall  h tn t l next,
    can_change_aop (sllseg  h tn l t next).
Proof.
  intros.
  gen h t tn.
  induction l; intros; simpl in *; intuition auto.
  auto with can_change_aop.
Qed.

Hint Resolve can_change_aop_sllseg : can_change_aop.

Theorem can_change_aop_node :
  forall x v T,
    can_change_aop (node x v T).
Proof.
  intros.
  unfold node.
  simpl.
  intros.
  splits; auto with can_change_aop.
Qed.

Hint Resolve can_change_aop_node : can_change_aop.

Theorem can_change_aop_sll :
  forall h l tp  next,
    can_change_aop (sll h l tp  next).
Proof.
  intros.
  unfold sll.
  auto with  can_change_aop.
Qed.


Hint Resolve can_change_aop_sll : can_change_aop.

Theorem can_change_aop_dllseg :
  forall h hp t tn l tp pre next,
    can_change_aop (dllseg h hp t tn l tp pre next).
Proof.
  intros.
  gen h hp t tn tp pre next .
  induction l; intros.
  simpl; intuition auto.
  unfold dllseg; fold dllseg.
  simpl.
  split; auto.
  intros.
  splits; auto.
  intros.
  split;  auto with can_change_aop.
Qed.

Hint Resolve can_change_aop_dllseg : can_change_aop.

Ltac can_change_aop_solver := 
  match goal with
   | |-  can_change_aop ?p =>
     match p with
         | Aexists _  => apply  can_change_aop_ex; intros;  can_change_aop_solver
         | ?p1 ** ?p2 => apply  can_change_aop_star; can_change_aop_solver
         | _ =>   first [auto with  can_change_aop | simpl; auto]
     end
   | _ => idtac
end.
