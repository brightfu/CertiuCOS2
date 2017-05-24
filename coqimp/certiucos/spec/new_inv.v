Require Import os_inv.
Require Import ucos_include.
(*------auxiliary lemmas------*)


Lemma beq_val_true_eq :
  forall v1 v2, beq_val v1 v2 = true -> v1 = v2.
Proof.
  intros.
  destruct v1, v2; simpl in H; tryfalse; auto.
  pose proof Int.eq_spec i i0.
  rewrite H in H0; substs; auto.
  unfolds in H.
  destruct a, a0.
  apply andb_true_iff in H; destruct H.
  rewrite beq_pos_Pos_eqb_eq in H.
  apply Pos.eqb_eq in H; substs.
  pose proof Int.eq_spec i i0.
  rewrite H0 in H; substs.
  auto.
Qed.

Lemma beq_addrval_true : forall a, beq_addrval a a = true.
Proof.
  intro.
  destruct a; simpl.
  rewrite Int.eq_true.
  rewrite beq_pos_Pos_eqb_eq.
  rewrite Pos.eqb_refl.
  simpl; auto.
Qed.

Lemma beq_val_true : forall v, beq_val v v = true.
Proof.
  intro.
  destruct v; simpl; auto.
  rewrite Int.eq_true; auto.
  rewrite beq_addrval_true; auto.
Qed.

Lemma beq_addrval_sym : forall a1 a2, beq_addrval a1 a2 = beq_addrval a2 a1.
Proof.
  intros.
  unfolds.
  destruct a1, a2.
  rewrite Int.eq_sym.
  do 2 rewrite beq_pos_Pos_eqb_eq.
  rewrite Pos.eqb_sym.
  auto.
Qed.

Lemma beq_val_sym : forall v1 v2, beq_val v1 v2 = beq_val v2 v1.
Proof.
  intros.
  destruct v1, v2; simpl; auto.
  rewrite Int.eq_sym; auto.
  rewrite beq_addrval_sym; auto.
Qed.



Lemma nth_val_nth_val'_some_eq : forall n vl x,
  nth_val n vl = Some x -> nth_val' n vl = x.
Proof.
  inductions n; intros.
  destruct vl; simpl in H; tryfalse.
  unfolds; simpl; inverts H; auto.
  simpl.
  destruct vl; simpl in H; tryfalse.
  apply IHn in H; auto.
Qed.

(*------end of auxiliary lemmas------*)

(*---definitions---*)
(*
  the user should guarantee that 'head' is actually the head pointer of 'l',
  if not, this definition doesn't make any sense.
*)


Lemma ptr_in_tcbdllseg_preserve :
  forall l1 l2 head x x' p,
    ptr_in_tcbdllseg p head (l1++x::l2) ->
    same_prev_next x x' ->
    ptr_in_tcbdllseg p head (l1++x'::l2).
Proof.
  inductions l1; intros.
  rewrite app_nil_l in *.
  simpl ptr_in_tcbdllseg in *.
  destruct (beq_val p head) eqn : eq1.
  auto.
  unfolds in H0.
  destruct (V_OSTCBNext x); destruct(V_OSTCBNext x');
  destruct (V_OSTCBPrev x); destruct(V_OSTCBPrev x');
  simp join; tryfalse; auto.

  rewrite <- app_comm_cons in *.
  unfold ptr_in_tcbdllseg in *; fold ptr_in_tcbdllseg in *.
  destruct (beq_val p head); auto.
  destruct (V_OSTCBNext a); tryfalse.
  eapply IHl1; eauto.
Qed.

(*use this lemma after modifying the node, to get ptr_in_tcblist on the new list *)
Lemma ptr_in_tcblist_preserve :
  forall l1 l2 head x x' p,
    ptr_in_tcblist p head (l1++x::l2) ->
    same_prev_next x x' ->
    ptr_in_tcblist p head (l1++x'::l2).
Proof.
  unfold ptr_in_tcblist.
  apply ptr_in_tcbdllseg_preserve.
Qed.

(*---aux lemmas---*)
Lemma tcbdllseg_vptr :
  forall head headprev tail tailnext h l P s,
    s |= tcbdllseg head headprev tail tailnext (h::l) ** P ->
    exists x, head = Vptr x.
Proof.
  intros.
  unfold tcbdllseg in H.
  unfold dllseg in H; fold dllseg in H.
  sep normal in H.
  destruct H.
  unfold node in H.
  sep normal in H; destruct H.
  sep split in H; simp join.
  eauto.
Qed.


Lemma tcbdllseg_ptr_in_tcbdllseg:
  forall l1 l2 tcbcur p1 p2 tail1 tail2 s P headprev1 tailnext2,
    s |= tcbdllseg p1 headprev1 tail1 p2 l1 **
      tcbdllseg p2 tail1 tail2 tailnext2 (tcbcur :: l2) ** P
    ->
    ptr_in_tcbdllseg p2 p1 (l1 ++ tcbcur :: l2).
Proof.
  inductions l1; intros.
  unfold tcbdllseg at 1 in H.
  unfold dllseg in H.
  sep split in H; substs.
  rewrite app_nil_l.
  simpl.
  rewrite beq_val_true.
  auto.

  rewrite <- app_comm_cons.
  unfold ptr_in_tcbdllseg; fold ptr_in_tcbdllseg.
  destruct (beq_val p2 p1) eqn : eq1.
  auto.
  assert(exists next, V_OSTCBNext a = Some next).
  unfold tcbdllseg at 1 in H.
  unfold dllseg in H; fold dllseg in H.
  sep normal in H; destruct H.
  sep split in H.
  eauto.
  destruct H0.
  rewrite H0.
  unfold tcbdllseg at 1 in H.
  unfold dllseg in H; fold dllseg in H.
  sep normal in H.
  destruct H.
  sep split in H.
  sep remember (1::nil)%nat in H.
  destruct_s s; simpl_sat H; simp join.
  rewrite H0 in H1; inverts H1.
  eapply IHl1; eauto.
Qed.


Lemma ptr_in_tcbdllseg_split :
  forall l p head headprev tail2 tailnext2 P s,
    ptr_in_tcbdllseg p head l ->
    s |= tcbdllseg head headprev tail2 tailnext2 l ** P ->
    exists l1 l2 tail1, s |= tcbdllseg head headprev tail1 p l1 ** tcbdllseg p tail1 tail2 tailnext2 l2 ** P /\ l = l1 ++ l2.
Proof.
  inductions l; intros.
  simpl in H; tryfalse.

  unfold ptr_in_tcbdllseg in H; fold ptr_in_tcbdllseg in H.
  destruct (beq_val p head) eqn : eq1.
  exists (nil (A:= vallist)) (a::l) headprev.
  apply beq_val_true_eq in eq1; substs.
  split.
  sep auto.
  unfold tcbdllseg.
  unfold dllseg.
  sep auto.
  rewrite app_nil_l; auto.
  
  destruct (V_OSTCBNext a) eqn : eq2; tryfalse.
  unfold tcbdllseg in H0.
  unfold dllseg in H0; fold dllseg in H0.
  sep normal in H0.
  destruct H0.
  sep split in H0.
  sep remember (1::nil)%nat in H0.
  destruct_s s.

  simpl_sat H0; simp join.
  unfold tcbdllseg at 1 in IHl.
  rewrite eq2 in H1; inverts H1.
  eapply IHl in H9; eauto.
  simp join.
  exists (a::x2) x5 x6.
  split.
  unfold tcbdllseg at 1 in H0.
  unfold tcbdllseg at 1.
  unfold dllseg; fold dllseg.
  sep split; auto.
  sep normal.
  exists x.
  sep split; eauto.
  sep remember (1::nil)%nat.
  simpl_sat_goal.
  do 6 eexists; splits; eauto.
  rewrite app_comm_cons; auto.
Qed.


Fixpoint last_next_ptr_tcbdllseg (l:list vallist) (default:val) :=
  match l with
    | nil => default
    | h::nil => (nth_val' 0%nat h)
    | h::l' => last_next_ptr_tcbdllseg l' default
  end.

Lemma tcbdllseg_last_next_ptr_tcbdllseg' :
  forall l v head headprev tail tailnext P s x,
    s |= tcbdllseg head headprev tail tailnext (v :: l) ** P ->
    last_next_ptr_tcbdllseg (v :: l) x = tailnext.
Proof.
  inductions l; intros.
  unfold tcbdllseg in H; unfold dllseg in H; fold dllseg in H.
  sep normal in H; destruct H.
  sep split in H; substs.
  simpl.
  unfold V_OSTCBNext in H0.
  destruct v; simpl in H0; tryfalse.
  inverts H0; auto.

  unfold last_next_ptr_tcbdllseg; fold last_next_ptr_tcbdllseg.
  unfold last_next_ptr_tcbdllseg in IHl; fold last_next_ptr_tcbdllseg in IHl.
  unfold tcbdllseg in H; unfold dllseg in H; fold dllseg in H.
  sep normal in H.
  do 2 destruct H.
  sep split in H.
  sep remember (3::nil)%nat in H.
  destruct_s s; simpl_sat H; simp join.
  eapply IHl.
  unfold tcbdllseg.
  unfold dllseg; fold dllseg.
  sep split; auto.
  sep normal.
  exists x1.
  sep split; eauto.
  auto.
Qed.

Lemma tcbdllseg_last_next_ptr_tcbdllseg :
  forall l head headprev tail tailnext P s,
    s |= tcbdllseg head headprev tail tailnext l ** P ->
    last_next_ptr_tcbdllseg l head = tailnext.
Proof.
  intros.
  destruct l.
  unfold tcbdllseg in H; unfold dllseg in H.
  sep split in H; substs.
  simpl; auto.  
  gen v head headprev tail tailnext P s.

  intros.
  eapply tcbdllseg_last_next_ptr_tcbdllseg'; eauto.
Qed.


Lemma TCBList_P_split_last_next_ptr_tcbdllseg' :
  forall l1 h1 l2 head p2 tcbls rtbl x,
    last_next_ptr_tcbdllseg (h1::l1) x = p2 ->
    TCBList_P head ((h1::l1) ++ l2) rtbl tcbls ->
    exists tcbls1 tcbls2, TCBList_P head (h1::l1) rtbl tcbls1 /\ TCBList_P p2 l2 rtbl tcbls2 /\ TcbMod.join tcbls1 tcbls2 tcbls.
Proof.
  inductions l1; intros.
  rewrite <- app_comm_cons in H0.
  rewrite app_nil_l in H0.
  unfold TCBList_P in H0; fold TCBList_P in H0; simp join.
  exists (TcbMod.sig x0 x3) x2.
  splits; auto.
  unfold TCBList_P.
  do 4 eexists; splits; eauto.
  unfold TcbJoin.
  apply TcbMod.join_comm.
  apply TcbMod.join_emp; auto.
  unfold last_next_ptr_tcbdllseg.
  unfolds in H1.
  erewrite nth_val_nth_val'_some_eq; eauto.
  rewrite <- app_comm_cons in H0.
  unfold TCBList_P in H0; fold TCBList_P in H0.
  do 4 destruct H0.
  destruct H0; destruct H1; destruct H2; destruct H3.
  unfold last_next_ptr_tcbdllseg in H; fold last_next_ptr_tcbdllseg in H.
  unfold last_next_ptr_tcbdllseg in IHl1; fold last_next_ptr_tcbdllseg in IHl1.
  eapply IHl1 in H; eauto.
  simpljoin.
  unfold TcbJoin in *.

  exists (TcbMod.merge (TcbMod.sig x0 x3) x4) x5.
  splits; auto.
  unfold TCBList_P; fold TCBList_P.
  do 4 eexists.
  splits; eauto.
  clear - H2 H6.

  unfold TcbJoin.
  unfold join, sig in *; simpl in *.
  unfold TcbMod.join; intros.
  rewrite TcbMod.merge_sem.
  destruct (tidspec.beq x0 a) eqn : eq1.
  lets Hx: tidspec.beq_true_eq eq1; substs.
  rewrite TcbMod.get_sig_some.
  pose proof H6 a.
  pose proof H2 a.
  rewrite TcbMod.get_sig_some in H0.
  destruct(TcbMod.get x4 a);
    destruct(TcbMod.get x5 a);
    destruct(TcbMod.get x2 a);
    destruct(TcbMod.get tcbls a); tryfalse; auto.
  lets Hx: tidspec.beq_false_neq eq1.
  rewrite TcbMod.get_sig_none; auto.
  pose proof H2 a; pose proof H6 a.
  rewrite TcbMod.get_sig_none in H; auto.
  destruct(TcbMod.get x4 a);
    destruct(TcbMod.get x5 a);
    destruct(TcbMod.get x2 a);
    destruct(TcbMod.get tcbls a); tryfalse; auto.

  clear - H2 H6.
  unfold join, sig in *; simpl in *.
  unfold TcbMod.join; intros.
  rewrite TcbMod.merge_sem.
  destruct (tidspec.beq x0 a) eqn : eq1.
  lets Hx: tidspec.beq_true_eq eq1; substs.
  rewrite TcbMod.get_sig_some.
  pose proof H6 a.
  pose proof H2 a.
  rewrite TcbMod.get_sig_some in H0.
  destruct(TcbMod.get x4 a);
    destruct(TcbMod.get x5 a);
    destruct(TcbMod.get x2 a);
    destruct(TcbMod.get tcbls a); tryfalse; auto.
  lets Hx: tidspec.beq_false_neq eq1.
  rewrite TcbMod.get_sig_none; auto.
  pose proof H2 a; pose proof H6 a.
  rewrite TcbMod.get_sig_none in H; auto.
  destruct(TcbMod.get x4 a);
    destruct(TcbMod.get x5 a);
    destruct(TcbMod.get x2 a);
    destruct(TcbMod.get tcbls a); tryfalse; substs; auto.
Qed.


Lemma TCBList_P_split_last_next_ptr_tcbdllseg :
  forall l1 l2 head p2 tcbls rtbl,
    last_next_ptr_tcbdllseg l1 head = p2 ->
    TCBList_P head (l1 ++ l2) rtbl tcbls ->
    exists tcbls1 tcbls2, TCBList_P head l1 rtbl tcbls1 /\ TCBList_P p2 l2 rtbl tcbls2 /\ TcbMod.join tcbls1 tcbls2 tcbls.
Proof.
  intros.
  destruct l1.
  simpl in H; substs.
  rewrite app_nil_l in H0.
  do 2 eexists.
  splits; eauto.
  simpl; eauto.
  apply TcbMod.join_emp; auto.
  eapply TCBList_P_split_last_next_ptr_tcbdllseg'; eauto.
Qed.
(*--end of aux lemmas--*)


(* 2 depracated lemmas *)
Lemma tcbdllseg_combine :
  forall p1 p2 l1 l2 rtbl tcbls tail1 tail2 tcbls1 tcbls2 tcbcur P,
    tcbdllseg p1 Vnull tail1 p2 l1 **
    tcbdllseg p2 tail1 tail2 Vnull (tcbcur::l2) **
    [|TcbMod.join tcbls1 tcbls2 tcbls|] **
    [|TCBList_P p1 l1 rtbl tcbls1|] **
    [|TCBList_P p2 (tcbcur::l2) rtbl tcbls2|] **
    P
    ==>        
    [|ptr_in_tcbdllseg p2 p1 (l1++tcbcur::l2)|] **
    tcbdllseg p1 Vnull tail2 Vnull (l1++tcbcur::l2) **
    [|TCBList_P p1 (l1++tcbcur::l2) rtbl tcbls|] **
    P.
Proof.
  intros.
  sep split.
  apply tcbdllseg_compose in H.
  sep auto.

  sep split in H.
  destruct l1.
  rewrite app_nil_l.
  unfold tcbdllseg at 1 in H.
  simpl dllseg in H.
  sep split in H; substs.
  simpl in H1.
  substs.
  apply TcbMod.join_emp_eq in H0; substs.
  auto.
  
  eapply TCBList_P_combine_copy; eauto.
(*  intro; tryfalse.*)
  
  assert(exists x, p2 = Vptr x).
  sep lift 2%nat in H.
  eapply tcbdllseg_vptr; eauto.
  destruct H3; substs.
  eapply tcbdllseg_last_nextptr; eauto.

  sep split in H.
  eapply tcbdllseg_ptr_in_tcbdllseg; eauto.
Qed.

Lemma tcbdllseg_split :
  forall l p1 p2 tail2 rtbl tcbls P,
    [|ptr_in_tcbdllseg p2 p1 l|] **
    tcbdllseg p1 Vnull tail2 Vnull l **
    [|TCBList_P p1 l rtbl tcbls|] **
    P
    ==>
    EX l1 l2 tail1 tcbls1 tcbls2,
    tcbdllseg p1 Vnull tail1 p2 l1 **
    tcbdllseg p2 tail1 tail2 Vnull l2 **
    [|l = l1 ++ l2|] **          
    [|TcbMod.join tcbls1 tcbls2 tcbls|] **          
    [|TCBList_P p1 l1 rtbl tcbls1|] **
    [|TCBList_P p2 l2 rtbl tcbls2|] **
    P.
Proof.
  intros.
  sep split in H.
  eapply ptr_in_tcbdllseg_split in H; eauto.
  simpljoin.
  exists x x0 x1.

  intros.
  lets Hx : tcbdllseg_last_next_ptr_tcbdllseg H.
  eapply TCBList_P_split_last_next_ptr_tcbdllseg in H1; auto; simpljoin.
  exists x2 x3.
  sep auto.
Qed.

Lemma tcbdllseg_split' :
  forall l p1 p2 tail2 rtbl tcbls P,
    ptr_in_tcbdllseg p2 p1 l ->
    TCBList_P p1 l rtbl tcbls ->

    tcbdllseg p1 Vnull tail2 Vnull l **
    P
    ==>
    EX l1 l2 tail1 tcbls1 tcbls2,
    tcbdllseg p1 Vnull tail1 p2 l1 **
    tcbdllseg p2 tail1 tail2 Vnull l2 **
    [|l = l1 ++ l2|] **          
    [|TcbMod.join tcbls1 tcbls2 tcbls|] **          
    [|TCBList_P p1 l1 rtbl tcbls1|] **
    [|TCBList_P p2 l2 rtbl tcbls2|] **
    P.
Proof.
  intros.
  sep split in H.
  eapply ptr_in_tcbdllseg_split in H1; eauto.
  simpljoin.
  exists x x0 x1.

  intros.
  lets Hx : tcbdllseg_last_next_ptr_tcbdllseg H1.
  eapply TCBList_P_split_last_next_ptr_tcbdllseg in H0; auto; simpljoin.
  exists x2 x3.
  sep auto.
Qed.



(*combine 2 tcblist into one, 
  with the knowledge that the head ptr of list2 is in the combined list*)
Lemma tcblist_combine :
  forall l1 l2 tcbcur head1 head2 headprev1 tail1 tail2  tailnext2 rtbl tcbls tcbls1 tcbls2 P,
    tcblist head1 headprev1 tail1 head2 l1 rtbl tcbls1 **
    tcblist head2 tail1 tail2 tailnext2 (tcbcur::l2) rtbl tcbls2 **
    [|TcbMod.join tcbls1 tcbls2 tcbls|] ** P
    ==>
    EX l,
    [|l=l1++(tcbcur::l2)|] **
    [|ptr_in_tcblist head2 head1 l|] **
    tcblist head1 headprev1 tail2 tailnext2 l rtbl tcbls ** P.
Proof.
  unfold tcblist.
  intros.
  exists (l1 ++ (tcbcur::l2)).
  sep split; auto.
  sep normal in H.
  sep lifts (1::3::nil)%nat in H.
  apply tcbdllseg_compose in H.
  sep auto.

  sep split in H.
  destruct l1.
  rewrite app_nil_l.
  unfold tcbdllseg at 1 in H.
  simpl dllseg in H.
  sep split in H; substs.
  simpl in H0.
  substs.
  apply TcbMod.join_emp_eq in H2; substs.
  auto.
  
  eapply TCBList_P_combine_copy; eauto.
(*  intro; tryfalse.*)
  assert(exists x, head2 = Vptr x).
  sep lift 2%nat in H.
  eapply tcbdllseg_vptr; eauto.
  destruct H3; substs.
  eapply tcbdllseg_last_nextptr; eauto.

  sep split in H.
  eapply tcbdllseg_ptr_in_tcbdllseg; eauto.
Qed.


(*split a tcblist into two parts*)
Lemma tcblist_split :
  forall l p head headprev tail tailnext rtbl tcbls P,
    [|ptr_in_tcblist p head l|] **
    tcblist head headprev tail tailnext l rtbl tcbls ** P
    ==>
    EX l1 l2 tail1 tcbls1 tcbls2,
    tcblist head headprev tail1 p l1 rtbl tcbls1 **
    tcblist p tail1 tail tailnext l2 rtbl tcbls2 **
    [|l = l1 ++ l2|] **          
    [|TcbMod.join tcbls1 tcbls2 tcbls|] ** P. 
Proof.
  unfold tcblist.
  intros.
  sep split in H.
  eapply ptr_in_tcbdllseg_split in H; eauto.
  simpljoin.
  exists x x0 x1.
  lets Hx : tcbdllseg_last_next_ptr_tcbdllseg H.
  eapply TCBList_P_split_last_next_ptr_tcbdllseg in H1; auto; simpljoin.
  exists x2 x3.
  sep auto.
Qed.


(*a more specific version for easy usage*)
Lemma tcblist_split' :
  forall l x head headprev tail rtbl tcbls P,
    [|ptr_in_tcblist (Vptr x) head l|] **
    tcblist head headprev tail Vnull l rtbl tcbls ** P
    ==>
    EX l1 l2 curtcb tail1 tcbls1 tcbls2,
    tcblist head headprev tail1 (Vptr x) l1 rtbl tcbls1 **
    tcblist (Vptr x) tail1 tail Vnull (curtcb::l2) rtbl tcbls2 **
    [|l = l1 ++ (curtcb::l2)|] **          
    [|TcbMod.join tcbls1 tcbls2 tcbls|] ** P.
Proof.
  unfold tcblist.
  intros.
  sep split in H.
  eapply ptr_in_tcbdllseg_split in H; eauto.
  simpljoin.
  destruct x1.
  unfold tcbdllseg at 2 in H.
  unfold dllseg in H.
  sep split in H; tryfalse.

  sep normal.
  eapply TCBList_P_split_last_next_ptr_tcbdllseg in H1; auto; simpljoin.
  do 6 eexists.
  sep auto; eauto.
  lets Hx : tcbdllseg_last_next_ptr_tcbdllseg H.
  rewrite Hx in H2.
  auto.
Qed.




(*lemmas to change between the new OSInv and the old one*)
(*
Lemma OSInv_OSInv' :
  forall P,
  OSInv ** P ==> OSInv' ** P.
Proof.
  (*
  unfold OSInv; unfold OSInv'.
  intros.
  sep normal in H.
  do 20 destruct H.
  sep normal.
  do 15 eexists.
  sep pauto.
  auto.
  do 5 sep cancel 1%nat 1%nat.
  unfold AOSTCBList in H.
  unfold AOSTCBList'.
  sep normal in H.
  do 4 destruct H.
  unfold tcblist.
  sep normal.
  do 3 eexists.
  sep pauto.
  eapply tcbdllseg_compose; eauto.
  sep lifts (2::4::nil)%nat in H.
  unfold ptr_in_tcblist.
  eapply tcbdllseg_ptr_in_tcbdllseg; eauto.
  destruct x7.
  simpl in H4; substs.
  unfold tcbdllseg at 1 in H.
  unfold dllseg in H.
  sep split in H.
  substs.
  rewrite app_nil_l.
  apply TcbMod.join_emp_eq in H3; substs.
  auto.
  sep lifts (2::4::nil)%nat in H.
  eapply TCBList_P_combine_copy; eauto.
  eapply tcbdllseg_last_nextptr; eauto.
Qed.
   *)
(* Admitted. *)

Lemma OSInv'_OSInv :
  forall P,
  OSInv' ** P ==> OSInv ** P.
Proof.
  (*
  unfold OSInv; unfold OSInv'.
  intros.
  sep normal in H.
  do 15 destruct H.
  unfold AOSTCBList' in H.
  sep normal in H.
  do 3 destruct H.
  sep lifts (4::3::nil)%nat in H.
  apply tcblist_split' in H.
  do 6 destruct H.
  unfold tcblist in H.
  sep normal.
  do 20 eexists.
  unfold AOSTCBList.
  sep normal.
  do 4 eexists.
  sep pauto; eauto.
  split; auto.
  destruct x17.
  unfold tcbdllseg at 1 in H.
  unfold dllseg in H.
  sep split in H; substs.
  unfold tcbdllseg in H.
  unfold dllseg in H; fold dllseg in H.
  sep split in H; substs; auto.

  unfold tcbdllseg at 1 in H.
  unfold dllseg in H; fold dllseg in H.
  sep split in H; substs; auto.
Qed.*)
(* Admitted. *)
*)



(*----------------------------------------------------------------------*)
(*------------definitions-----------------------------------------------*)
Fixpoint pair_list_get (p:val) (l:list (val*vallist)) : option vallist :=
  match l with
    | nil => None
    | (p',vl)::l' =>
      if beq_val p p'
      then Some vl
      else pair_list_get p l'
  end.

Fixpoint tcbdllseg1 (head headprev tail tailnext:val) (l:list vallist)
         (holes:list (val*vallist)) :=
  match l with
    | nil => [|head = tailnext|] ** [|headprev = tail|]
    | vl::l' =>
      [|head <> Vnull|] **
     (EX vn,          
      [|V_OSTCBNext vl = Some vn|] **
      [|V_OSTCBPrev vl = Some headprev|] **
      match pair_list_get head holes with 
       | Some vl' =>
          [|vl = vl'|] 
        | None =>
          node head vl OS_TCB_flag
      end **
      tcbdllseg1 vn head tail tailnext l' holes)
  end.

Fixpoint ptr_in (p:val) (l:list (val*vallist)) : Prop :=
  match l with
    | nil => False
    | (p',vl)::l' =>
      if beq_val p p'
      then True
      else ptr_in p l'
  end.

Fixpoint distinct_ptr (l:list (val*vallist)) : Prop :=
  match l with
    | nil => True
    | (a,vl)::l' =>
      ~ (ptr_in a l') /\ (distinct_ptr l')
  end.

Fixpoint ptr_in_tcbdllseg1 (p:val) (head:val) (l:list vallist) : Prop :=
  match l with
    | nil => False
    | h::l' =>
      if (beq_val p head)
      then True
      else
        match (V_OSTCBNext h) with
          | None => False
          | Some next => ptr_in_tcbdllseg1 p next l'
        end
  end.

Definition ptr_in_tcblist1 (p:val) (head:val) (l:list vallist) (holes:list (val*vallist)) : Prop := ptr_in_tcbdllseg1 p head l /\ pair_list_get p holes = None.

Fixpoint distinct_tcbdllseg_next_ptr (head:val) (l:list vallist) : Prop :=
  match l with
    | nil => True (*? should it be True this case*)
    | h::nil => True
    | h::l' =>
      match V_OSTCBNext h with
        | Some vn => (~ ptr_in_tcbdllseg1 head vn l') /\ distinct_tcbdllseg_next_ptr vn l'
        | None => False
      end
  end.

Fixpoint ptrs_in_tcblist (ptrs:list val) (head:val) (l:list vallist): Prop :=
  match ptrs with
    | nil => True
    | p::ptrs' =>
      ptr_in_tcblist p head l /\ ptrs_in_tcblist ptrs' head l
  end.

Fixpoint ptrs_in_tcblist1 (ptrs:list val) (head:val) (l:list vallist) (holes:list(val*vallist)): Prop :=
  match ptrs with
    | nil => True
    | p::ptrs' =>
      ptr_in_tcblist1 p head l holes /\ ptrs_in_tcblist1 ptrs' head l holes
  end.

Fixpoint split_tcb_nodes' (ptrs:list val) (head headprev tail tailnext:val) (l:list vallist) (holes:list(val*vallist)) : asrt :=
  match ptrs with
    | nil => tcbdllseg1 head headprev tail tailnext l holes
    | p::ptrs' => 
      EX vl, node p vl OS_TCB_flag ** (split_tcb_nodes' ptrs' head headprev tail tailnext l ((p,vl)::holes))
  end.

Definition split_tcb_nodes (ptrs:list val) (head headprev tail tailnext:val) (l:list vallist): asrt
  := split_tcb_nodes' ptrs head headprev tail tailnext l nil.

Fixpoint tcb_nodes (nodes:list (val*vallist)) : asrt :=
  match nodes with
    | nil => Aemp
    | (p,vl)::nodes' =>
      (node p vl OS_TCB_flag) ** (tcb_nodes nodes')
  end.

Fixpoint nodes_holes_match (nodes holes:list (val*vallist)) : Prop :=
  match nodes, holes with
    | nil, nil => True
    | (p1,vl1)::nodes', (p2,vl2)::holes' =>
      if beq_val p1 p2
      then same_prev_next vl1 vl2 /\ nodes_holes_match nodes' holes'
      else False
    | _, _ => False
  end.

(*
Fixpoint set_node (p:val) (vl':vallist) (head:val) (l:list vallist) :=
  match l with
    | nil => nil
    | vl::l' =>
      if beq_val p head
      then vl'::l'
      else vl::set_node p vl' (nth_val' 0 vl) l'
  end.
 *)

Fixpoint set_nodes (nodes:list(val*vallist)) (head:val) (l:list vallist) : list vallist :=
  match nodes with
    | nil => l
    | (p,vl)::nodes' =>
      set_nodes nodes' head (set_node p vl head l)
  end.

Fixpoint nodes_in_tcblist (nodes:list(val*vallist)) (head:val) (l:list vallist) : Prop :=
  match nodes with
    | nil => True
    | (p,vl)::nodes' =>
      ptr_in_tcbdllseg1 p head l /\ nodes_in_tcblist nodes' head l
  end.

Fixpoint tcbdllseg1_get_node (p:val) (head:val) (l:list vallist) : option vallist :=
  match l with
    | nil => None
    | vl::l' =>
      if beq_val p head
      then Some vl
      else
        match V_OSTCBNext vl with
          | Some vn =>
            tcbdllseg1_get_node p vn l'
          | None => None
        end
  end.

Fixpoint ptrs_not_change (nodes:list(val*vallist)) (head:val) (l:list vallist) : Prop :=
  match nodes with
    | nil => True
    | (p,vl')::nodes' =>
      match tcbdllseg1_get_node p head l with
        | Some vl => same_prev_next vl vl' /\ ptrs_not_change nodes' head l
        | None => False
      end
  end.

(*--------------------end of definitions-------------------------*)


(*---------------------------lemmas------------------------------*)
(*
moved to OS_InvDef.v

Lemma node_OS_TCB_dup_false :
  forall p a1 a2 P s,
    s |= node p a1 OS_TCB_flag ** node p a2 OS_TCB_flag ** P ->
    False.
Proof.
  (*
  intros.
  unfold node in H.
  unfold Astruct in H.
  sep normal in H.
  do 2 destruct H.
  sep split in H.
  unfold OS_TCB in H.
  unfold Astruct' in H.
  mytac.
  destruct a1.
  simpl in H2; tryfalse.
  destruct a2.
  simpl in H3; tryfalse.
  sep normal in H.
  sep remember (1::3::nil)%nat in H.
  clear HeqH0.
  inverts H1.
  sep remember (3::nil)%nat in H.
  destruct_s s.
  simpl_sat H; mytac.
  simpl in H2, H3; mytac.
  clear - H H2 H8.
  simpl in H8; mytac.
  apply MemMod.join_disj_meq in H1; destruct H1.
  Require Import common.
  eapply mapstoval_disj_false with (m1:=x0) (m2:=x2); eauto.
  simpl; omega.
Qed.
   *)
(* Admitted. *)
*)

Lemma tcbdllseg1_tcbdllseg :
  forall l head headprev tail tailnext,
    tcbdllseg1 head headprev tail tailnext l nil
    ==>
    tcbdllseg head headprev tail tailnext l.           
Proof. 
  inductions l; intros.
  destruct_s s; simpl in H; simp join.
  simpl; do 6 eexists; splits; eauto.
  apply map_join_emp.

  unfold tcbdllseg1 in H; fold tcbdllseg1 in H.
  sep normal in H; destruct H.
  assert (pair_list_get head nil = None).
  simpl; auto.
  rewrite H0 in H.
  unfold tcbdllseg; fold tcbdllseg.
  unfold dllseg; fold dllseg.
  sep normal.
  exists x.
  sep split in H.
  sep split; auto.
  sep auto.
  apply IHl; auto.
Qed.

Lemma tcbdllseg1_tcbdllseg' :
  forall l head headprev tail tailnext P,
    tcbdllseg1 head headprev tail tailnext l nil ** P
    ==>
    tcbdllseg head headprev tail tailnext l ** P.
Proof.
  intros.
  sep auto.
  apply tcbdllseg1_tcbdllseg; auto.
Qed.


Lemma tcbdllseg_tcbdllseg1 :
  forall l head headprev tail tailnext,
    tcbdllseg head headprev tail tailnext l
    ==>
    tcbdllseg1 head headprev tail tailnext l nil.           
Proof.
  inductions l; intros.
  destruct_s s; simpl in H; simp join.
  simpl; do 6 eexists; splits; eauto.
  apply map_join_emp.

  unfold tcbdllseg in H; fold tcbdllseg in H.
  unfold dllseg in H; fold dllseg in H.
  sep normal in H; destruct H.
  unfold tcbdllseg1; fold tcbdllseg1.
  sep normal.
  exists x.
  sep split in H.
  sep split; auto.
  assert (pair_list_get head nil = None).
  simpl; auto.
  rewrite H3.
  sep auto.
Qed.

Lemma not_ptr_in_tcbdllseg1 :
  forall l p vl head headprev tail tailnext s P,
    s |= node p vl OS_TCB_flag ** tcbdllseg head headprev tail tailnext l ** P ->
    ~ ptr_in_tcbdllseg1 p head l.
Proof.
  inductions l; intros.
  simpl; auto.

  unfold tcbdllseg in H.
  unfold dllseg in H; fold dllseg in H.
  unfold ptr_in_tcbdllseg1; fold ptr_in_tcbdllseg1.
  destruct (beq_val p head) eqn : eq1.
  sep normal in H; destruct H.
  sep split in H.
  apply beq_val_true_eq in eq1; substs.
  sep lifts (1::3::nil)%nat in H.
  apply node_OS_TCB_dup_false in H; tryfalse.

  sep normal in H; destruct H.
  sep split in H.
  rewrite H0.
  sep remember (1::nil)%nat in H.
  destruct_s s; simpl_sat H; simp join.
  eapply IHl; eauto.
  unfold tcbdllseg.
  sep lift 2%nat.
  eauto.
Qed.


(*a lemma for a condition required by the combine lemma
*)
Lemma distinct_tcbdllseg_next_ptr_intro :
  forall l head headprev tail tailnext s P,
    s |= tcbdllseg head headprev tail tailnext l ** P ->
    distinct_tcbdllseg_next_ptr head l.
Proof.
  inductions l; intros.
  simpl; auto.

  unfold tcbdllseg in H; fold tcbdllseg in H.
  unfold dllseg in H; fold dllseg in H.
  sep normal in H; destruct H.
  unfold distinct_tcbdllseg_next_ptr; fold distinct_tcbdllseg_next_ptr.
  destruct l; auto.
  sep split in H.
  rewrite H0.
  split.
  unfold ptr_in_tcbdllseg1; fold ptr_in_tcbdllseg1.
  unfold dllseg in H; fold dllseg in H.
  sep normal in H; destruct H.
  sep normal in H.
  sep split in H.
  destruct (beq_val head x) eqn : eq1.
  apply beq_val_true_eq in eq1; substs.
  sep lifts (1::3::nil)%nat in H.
  apply node_OS_TCB_dup_false in H; tryfalse.
  rewrite H3.
  sep lifts (3::2::nil)%nat in H.
  eapply not_ptr_in_tcbdllseg1.
  unfold tcbdllseg.
  eauto.

  destruct_s s.
  sep remember (1::nil)%nat in H.
  simpl_sat H; simp join.
  eapply IHl.
  unfold tcbdllseg.
  eauto.
Qed.


Lemma ptr_in_tcblist1_init :
  forall l p head,
    ptr_in_tcblist p head l ->
    ptr_in_tcblist1 p head l nil.
Proof.
  inductions l; intros.
  simpl in H; tryfalse.

  unfold ptr_in_tcblist in H.
  unfold ptr_in_tcbdllseg in H; fold ptr_in_tcbdllseg in H.
  destruct (beq_val p head) eqn : eq1.
  apply beq_val_true_eq in eq1; substs.
  unfolds.
  unfold ptr_in_tcbdllseg1; fold ptr_in_tcbdllseg1.
  rewrite beq_val_true.
  eauto.

  destruct (V_OSTCBNext a) eqn : eq2; tryfalse.
  apply IHl in H.
  unfold ptr_in_tcblist1.
  unfold ptr_in_tcbdllseg1; fold ptr_in_tcbdllseg1.
  rewrite eq1.
  rewrite eq2.
  eauto.
Qed.

Lemma ptrs_in_tcblist_ptrs_in_tcblist1 :
  forall ptrs head l,
    ptrs_in_tcblist ptrs head l ->
    ptrs_in_tcblist1 ptrs head l nil.
Proof.
  inductions ptrs; intros.
  simpl; auto.

  unfold ptrs_in_tcblist in H; fold ptrs_in_tcblist in H.
  destruct H.
  unfold ptrs_in_tcblist1; fold ptrs_in_tcblist1.
  split.
  apply ptr_in_tcblist1_init; auto.
  apply IHptrs; auto.
Qed.


(*main lemma*)
Lemma tcbdllseg1_init' :
  forall l P head headprev tail tailnext,
    tcbdllseg head headprev tail tailnext l ** P
    ==>
    tcbdllseg1 head headprev tail tailnext l nil **
    [|distinct_tcbdllseg_next_ptr head l|] ** P.
Proof.
  inductions l; intros.
  sep auto.
  simpl; auto.
 
  unfold tcbdllseg in H; fold tcbdllseg in H.
  unfold dllseg in H; fold dllseg in H.
  sep normal in H; destruct H; sep split in H.
  unfold tcbdllseg1; fold tcbdllseg1.
  sep normal.
  exists x.
  assert(exists tid, head = Vptr tid).
  unfold node in H.
  sep normal in H; destruct H; sep split in H.
  destruct H3; eauto.
  destruct H3.
  sep split; auto.
  unfold pair_list_get.
  sep cancel 1%nat 1%nat.
  unfold tcbdllseg in IHl.
  apply IHl in H; sep split in H; auto.
  eapply distinct_tcbdllseg_next_ptr_intro.
  unfold tcbdllseg.
  unfold dllseg; fold dllseg.
  sep normal.
  exists x.
  sep split; eauto.
Qed.


Lemma tcbdllseg1_head_not_in_tail :
  forall l p a head headprev tail tailnext holes s P,
    pair_list_get p holes = None ->
    s |= node p a OS_TCB_flag ** tcbdllseg1 head headprev tail tailnext l holes ** P ->
    ~ ptr_in_tcbdllseg p head l.
Proof.
  inductions l; intros.
  simpl; auto.

  destruct (beq_val p head) eqn : eq1.
  apply beq_val_true_eq in eq1; substs.
  unfold tcbdllseg1 in H0; fold tcbdllseg1 in H0.
  sep normal in H0.
  destruct H0.
  sep split in H0.
  rewrite H in H0.
  sep lifts (1::3::nil)%nat in H0.
  apply node_OS_TCB_dup_false in H0; tryfalse.
  
  unfold tcbdllseg1 in H0; fold tcbdllseg1 in H0.
  sep normal in H0; destruct H0.
  sep split in H0.
  sep remember (1::nil)%nat in H0.
  destruct_s s.
  simpl_sat H0; simp join.
  sep lift 2%nat in H9.
  apply IHl in H9; auto.
  unfold ptr_in_tcbdllseg; fold ptr_in_tcbdllseg.
  rewrite eq1.
  rewrite H1.
  auto.
Qed.

Lemma holes_add1 :
  forall l p head headprev tail tailnext holes a s ,
    (~ ptr_in_tcbdllseg1 p head l) ->
    s |= tcbdllseg1 head headprev tail tailnext l holes ->
    s |= tcbdllseg1 head headprev tail tailnext l ((p, a)::holes).
Proof.
  inductions l; intros.
  destruct_s s.
  simpl in H0; simp join.
  simpl.
  do 6 eexists; splits; eauto.
  apply join_emp; auto.

  unfold tcbdllseg1 in H0; fold tcbdllseg1 in H0.
  sep normal in H0.
  destruct H0.
  sep split in H0.
  unfold ptr_in_tcbdllseg1 in H; fold ptr_in_tcbdllseg1 in H.
  destruct (beq_val p head) eqn : eq1.
  false.
  apply H; auto.
  
  rewrite H1 in H.
  destruct_s s.
  simpl_sat H0; simp join.
  eapply IHl with (a:=a0) in H8; eauto.
  unfold tcbdllseg1; fold tcbdllseg1.
  sep normal.
  exists x.
  sep split; auto.
  simpl_sat_goal.
  do 6 eexists; splits; eauto.
  assert(pair_list_get head ((p, a0) :: holes) = pair_list_get head holes).
  unfold pair_list_get; fold pair_list_get.
  rewrite beq_val_sym in eq1.
  rewrite eq1; auto.
  rewrite H0.
  auto.
Qed.


(*main lemma*)
Lemma tcbdllseg1_split :
  forall l p head headprev tail tailnext holes P,
    tcbdllseg1 head headprev tail tailnext l holes **
    [|ptr_in_tcblist1 p head l holes|] ** P
    ==>
    EX vl,
    node p vl OS_TCB_flag ** tcbdllseg1 head headprev tail tailnext l ((p,vl)::holes) ** P.
Proof.
  inductions l; intros.
  sep split in H.
  unfolds in H0; simp join.
  simpl in H1; tryfalse.

  destruct (beq_val p head) eqn : eq1.
  apply beq_val_true_eq in eq1; substs.
  unfold tcbdllseg1 in H; fold tcbdllseg1 in H.
  unfold tcbdllseg1; fold tcbdllseg1.
  assert(pair_list_get head holes = None).
  sep normal in H.
  destruct H.
  sep split in H.
  unfolds in H3; simp join; auto.

  sep normal in H.
  destruct H.
  sep split in H.
  rewrite H0 in H.
  exists a.
  sep normal.
  exists x.
  unfold pair_list_get; fold pair_list_get.
  rewrite beq_val_true.
  sep split; auto.
  
  assert(~ptr_in_tcbdllseg head x l).
  sep split in H.
  eapply tcbdllseg1_head_not_in_tail with (holes:=holes) in H; eauto.
  sep auto.
  
  apply holes_add1; auto.
  unfold tcbdllseg1 in H; fold tcbdllseg1 in H.
  sep normal in H.
  destruct H.
  sep split in H.
  unfolds in H3.
  unfold ptr_in_tcbdllseg1 in H3; fold ptr_in_tcbdllseg1 in H3.
  rewrite eq1 in H3.
  rewrite H0 in H3.
  sep remember (1::nil)%nat in H.
  destruct_s s.
  simpl_sat H; simp join.
  pose proof IHl p x head tail tailnext holes P (e, e0, x1, i, (i0, i1, c), x4, a0).
  assert(
      (e, e0, x1, i, (i0, i1, c), x4, a0)
      |= tcbdllseg1 x head tail tailnext l holes **
         [|ptr_in_tcblist1 p x l holes|] ** P
    ).
  sep auto.
  unfolds; split; auto.
  apply H in H4; clear H.
  destruct H4.
  exists x2.
  unfold tcbdllseg1; fold tcbdllseg1.
  sep normal.
  exists x.
  sep split; auto.
  sep remember (1::nil)%nat.
  simpl_sat_goal.
  do 6 eexists; splits; eauto.

  unfold pair_list_get; fold pair_list_get.
  rewrite beq_val_sym in eq1.
  rewrite eq1.
  auto.

  substs.
  sep auto.
Qed.


Lemma ptrs_in_tcblist1_holes_add1 :
  forall ptrs head l p vl holes,
    ptrs_in_tcblist1 ptrs head l holes ->
    ~ In p ptrs ->
    ptrs_in_tcblist1 ptrs head l ((p, vl) :: holes).
Proof.
  inductions ptrs; intros.
  simpl; auto.

  unfold ptrs_in_tcblist1 in H; fold ptrs_in_tcblist1 in H.
  destruct H.
  unfold ptrs_in_tcblist1; fold ptrs_in_tcblist1.
  split.
  2: eapply IHptrs; eauto.
  unfolds in H; destruct H.
  unfolds; split; auto.
  unfold pair_list_get; fold pair_list_get.
  destruct (beq_val a p) eqn : eq1.
  apply beq_val_true_eq in eq1; substs.
  unfolds in H0.
  false; apply H0.
  simpl; auto.
  auto.

  intro.
  apply H0.
  unfold In.
  auto.
Qed.

Lemma tcbdllseg1_init1 :
  forall ptrs l head headprev tail tailnext holes P,
    ptrs_in_tcblist1 ptrs head l holes->
    NoDup ptrs ->
    tcbdllseg1 head headprev tail tailnext l holes ** P
               ==>
               split_tcb_nodes' ptrs head headprev tail tailnext l holes ** P.
Proof.
  inductions ptrs; intros.
  simpl split_tcb_nodes'.
  sep auto.

  unfold ptrs_in_tcblist in H; fold ptrs_in_tcblist in H.
  destruct H.
  pose proof tcbdllseg1_split l a head headprev tail tailnext holes P s.
  assert(
      s
        |= tcbdllseg1 head headprev tail tailnext l holes **
        [|ptr_in_tcblist1 a head l holes|] ** P
    ).
  sep auto.
  apply H3 in H4; clear H3.
  unfold split_tcb_nodes'; fold split_tcb_nodes'.
  destruct H4.
  sep normal.
  exists x.
  sep cancel 1%nat 1%nat.
  inverts H0.
  lets Hx: IHptrs H3; auto.

  apply ptrs_in_tcblist1_holes_add1; auto.
Qed.


Lemma tcb_nodes_not_ptr_in :
  forall nodes p vl s,
    s |= node p vl OS_TCB_flag ** tcb_nodes nodes ->
    ~ ptr_in p nodes.
Proof.
  inductions nodes; intros.
  simpl; auto.

  unfold tcb_nodes in H; fold tcb_nodes in H.
  destruct a.
  unfold ptr_in; fold ptr_in.
  destruct (beq_val p v) eqn : eq1.
  apply beq_val_true_eq in eq1; substs.
  apply node_OS_TCB_dup_false in H; tryfalse.

  sep remember (2::nil)%nat in H.
  destruct_s s; simpl_sat H; simp join.
  clear H4.
  eapply IHnodes; eauto.
Qed.


Lemma nodes_holes_match_not_ptr_in :
  forall nodes holes p,
    nodes_holes_match nodes holes ->
    ~ ptr_in p nodes ->
    ~ ptr_in p holes.
Proof.
  inductions nodes; intros.
  destruct holes.
  simpl; auto.
  simpl in H; tryfalse.

  destruct holes.
  simpl in H; destruct a; tryfalse.
  unfold nodes_holes_match in H; fold nodes_holes_match in H.
  destruct a, p0.
  destruct (beq_val v v1) eqn : eq1; tryfalse.
  destruct H.
  apply beq_val_true_eq in eq1; substs.
  unfold ptr_in in *; fold ptr_in in *.
  destruct (beq_val p v1) eqn : eq1.
  auto.
  eapply IHnodes; auto.
Qed.


Lemma distinct_ptr_holes :
  forall nodes holes s,
    s |= tcb_nodes nodes ** [|nodes_holes_match nodes holes|] ->
    distinct_ptr holes.
Proof.
  inductions nodes; intros.
  destruct_s s.
  simpl in H; simp join.
  destruct holes; tryfalse.
  simpl; auto.

  sep split in H.
  destruct holes.
  simpl in H0; destruct a; tryfalse.

  unfold tcb_nodes in H; fold tcb_nodes in H; destruct a.
  unfold distinct_ptr; fold distinct_ptr.
  destruct p.
  unfold nodes_holes_match in H0; fold nodes_holes_match in H0.
  destruct (beq_val v v1) eqn: eq1; tryfalse.
  destruct H0.
  apply beq_val_true_eq in eq1; substs.
  split.

  eapply nodes_holes_match_not_ptr_in; eauto.
  eapply tcb_nodes_not_ptr_in; eauto.

  destruct_s s.
  simpl_sat H; simp join.
  clear H5.
  eapply IHnodes.
  sep split.
  eauto.
  auto.
Qed.


Lemma not_ptr_in_pair_list_get_none :
  forall l p,
    ~ ptr_in p l ->
    pair_list_get p l = None.
Proof.
  inductions l; intros.
  simpl; auto.

  unfold pair_list_get; fold pair_list_get.
  destruct a.
  unfold ptr_in in H; fold ptr_in in H.
  destruct (beq_val p v) eqn : eq1.
  false; apply H; auto.
  eapply IHl; eauto.
Qed.

Lemma holes_delete1 :
  forall l head headprev tail tailnext p vl holes,
    ~ ptr_in_tcbdllseg1 p head l ->
    tcbdllseg1 head headprev tail tailnext l ((p,vl)::holes)
               ==>
               tcbdllseg1 head headprev tail tailnext l holes.
Proof.
  inductions l; intros.
  destruct_s s; simpl in H0; simp join.
  simpl.
  do 6 eexists; splits; eauto.
  eapply join_emp; auto.

  unfold tcbdllseg1 in H0; fold tcbdllseg1 in H0.
  sep normal in H0; destruct H0.
  sep split in H0.
  unfold ptr_in_tcbdllseg1 in H; fold ptr_in_tcbdllseg1 in H.
  rewrite H1 in H.
  destruct (beq_val p head) eqn : eq1.
  false; apply H; auto.
  unfold tcbdllseg1; fold tcbdllseg1.
  sep normal.
  exists x.
  sep split; auto.
  unfold pair_list_get in H0; fold pair_list_get in H0.
  rewrite beq_val_sym in eq1.
  rewrite eq1 in H0.
  sep auto.
  eapply IHl; eauto.
Qed.


Lemma tcbdllseg1_node_join :
  forall l p vl vl' head headprev tail tailnext holes,
    ptr_in_tcbdllseg1 p head l ->
    same_prev_next vl' vl ->
    ~ ptr_in p holes ->
    distinct_ptr holes ->
    distinct_tcbdllseg_next_ptr head l ->
    node p vl' OS_TCB_flag ** tcbdllseg1 head headprev tail tailnext l ((p,vl)::holes)
         ==> tcbdllseg1 head headprev tail tailnext (set_node p vl' head l) holes.
Proof.
  inductions l; intros.
  simpl in H; tryfalse.

  unfold ptr_in_tcbdllseg1 in H; fold ptr_in_tcbdllseg1 in H.
  destruct (beq_val p head) eqn : eq1.
  apply beq_val_true_eq in eq1; substs.
  unfold tcbdllseg1 in H4; fold tcbdllseg1 in H4.
  sep normal in H4; destruct H4.
  sep split in H4.
  unfold pair_list_get in H4; fold pair_list_get in H4.
  rewrite beq_val_true in H4.
  
  sep split in H4; substs.
  unfold set_node; fold set_node.
  rewrite beq_val_true.
  unfold tcbdllseg1; fold tcbdllseg1.
  sep normal.
  exists x.
  unfolds in H0.
  rewrite H5 in H0.
  rewrite H6 in H0.
  
  destruct (V_OSTCBNext vl'); tryfalse; simp join.
  destruct (V_OSTCBPrev vl'); tryfalse; simp join.
  sep auto.
  apply not_ptr_in_pair_list_get_none in H1.
  rewrite H1.
  unfold distinct_tcbdllseg_next_ptr in H3; fold distinct_tcbdllseg_next_ptr in H3.
  rewrite H5 in H3.
  destruct l.
  simpl tcbdllseg1 in H4.
  sep split in H4.
  simpl tcbdllseg1.
  sep auto.
  destruct H3.
  sep auto.

  eapply holes_delete1; eauto.
  unfold tcbdllseg1 in H4; fold tcbdllseg1 in H4.
  sep normal in H4; destruct H4.
  sep split in H4.
  rewrite H5 in H.
  unfold set_node; fold set_node.
  rewrite eq1.
  unfold tcbdllseg1; fold tcbdllseg1.
  sep normal.
  exists x.
  sep split; auto.
  unfold pair_list_get in H4; fold pair_list_get in H4.
  rewrite beq_val_sym in eq1.
  rewrite eq1 in H4.
  sep auto.
  sep lift 2%nat in H4.
  unfold distinct_tcbdllseg_next_ptr in H3; fold distinct_tcbdllseg_next_ptr in H3.
  destruct l.
  simpl in H; tryfalse.
  rewrite H5 in H3.
  destruct H3.
  assert (nth_val' 0 a = x).
  apply nth_val_nth_val'_some_eq; auto.
  rewrite H9.
  eapply IHl; eauto.
Qed.


Lemma ptr_in_tcbdllseg1_get_some :
  forall l head headprev tail tailnext p vl holes s P,
    ptr_in_tcbdllseg1 p head l ->
    s |= tcbdllseg1 head headprev tail tailnext l ((p,vl)::holes) ** P ->
    tcbdllseg1_get_node p head l = Some vl.
Proof.
  inductions l; intros.
  simpl in H; tryfalse.

  unfold ptr_in_tcbdllseg1 in H; fold ptr_in_tcbdllseg1 in H.
  unfold tcbdllseg1 in H0; fold tcbdllseg1 in H0.
  sep normal in H0.
  destruct H0.
  sep split in H0.
  rewrite H1 in H.
  destruct (beq_val p head) eqn : eq1.
  apply beq_val_true_eq in eq1; substs.
  unfold pair_list_get in H0; fold pair_list_get in H0.
  rewrite beq_val_true in H0.
  unfold tcbdllseg1_get_node; fold tcbdllseg1_get_node.
  rewrite beq_val_true.
  sep split in H0; substs; auto.
  unfold tcbdllseg1_get_node; fold tcbdllseg1_get_node.
  rewrite eq1.
  rewrite H1.
  sep remember (1::nil)%nat in H0.
  destruct_s s; simpl_sat H0; simp join.
  eapply IHl; eauto.
Qed.


Lemma not_ptr_in_tcbdllseg1_set_node :
  forall l head p1 p2 vl1 vl2,
    tcbdllseg1_get_node p1 head l = Some vl1 ->
    same_prev_next vl1 vl2 ->
    ~ ptr_in_tcbdllseg1 p2 head l ->
    ~ ptr_in_tcbdllseg1 p2 head (set_node p1 vl2 head l).
Proof.
  inductions l; intros.
  simpl in H; tryfalse.

  unfold tcbdllseg1_get_node in H; fold tcbdllseg1_get_node in H.
  destruct (beq_val p1 head) eqn : eq1.
  inverts H.
  apply beq_val_true_eq in eq1; substs.
  unfold set_node; fold set_node.
  rewrite beq_val_true.
  unfold ptr_in_tcbdllseg1 in *; fold ptr_in_tcbdllseg1 in *.
  destruct (beq_val p2 head) eqn : eq1; auto.
  destruct (V_OSTCBNext vl1) eqn : eq2.
  unfolds in H0.
  rewrite eq2 in H0.
  destruct (V_OSTCBNext vl2); tryfalse.
  destruct H0; substs.
  auto.
  destruct (V_OSTCBNext vl2) eqn: eq3; auto.
  unfolds in H0.
  rewrite eq2 in H0; tryfalse.

  destruct (V_OSTCBNext a) eqn : eq2; tryfalse.
  unfold ptr_in_tcbdllseg1 in H1; fold ptr_in_tcbdllseg1 in H1.
  rewrite eq2 in H1.
  unfold set_node; fold set_node.
  rewrite eq1.
  unfold ptr_in_tcbdllseg1; fold ptr_in_tcbdllseg1.
  rewrite eq2.
  destruct (beq_val p2 head) eqn : eq3.
  intro; apply H1; auto.
  assert (nth_val' 0 a = v).
  apply nth_val_nth_val'_some_eq; auto.
  substs.
  eapply IHl; eauto.
Qed.

Lemma distinct_tcbdllseg_next_ptr_set_node :
  forall l head p vl1 vl2,
    distinct_tcbdllseg_next_ptr head l ->
    tcbdllseg1_get_node p head l = Some vl1 ->
    same_prev_next vl1 vl2 ->
    distinct_tcbdllseg_next_ptr head (set_node p vl2 head l).
Proof.
  inductions l; intros.
  simpl in H0; tryfalse.

  unfold distinct_tcbdllseg_next_ptr in H; fold distinct_tcbdllseg_next_ptr in H.
  unfold tcbdllseg1_get_node in H0; fold tcbdllseg1_get_node in H0.
  destruct l.
  destruct (beq_val p head) eqn : eq1.
  simpl set_node.
  rewrite eq1.
  simpl; auto.
  destruct (V_OSTCBNext a); tryfalse.

  destruct(V_OSTCBNext a) eqn : eq1; tryfalse.
  destruct H.
  unfold set_node; fold set_node.
  destruct (beq_val p head) eqn : eq2.
  inverts H0.
  unfold distinct_tcbdllseg_next_ptr; fold distinct_tcbdllseg_next_ptr.
  unfolds in H1.
  rewrite eq1 in H1.
  destruct (V_OSTCBNext vl2) eqn : eq3; tryfalse.
  destruct H1; substs.
  split; auto.

  
  lets Hx: IHl H2 H0 H1.
  unfold set_node in Hx; fold set_node in Hx.
  assert(nth_val' 0 a = v0).
  apply nth_val_nth_val'_some_eq; auto.
  substs.
  unfold distinct_tcbdllseg_next_ptr; fold distinct_tcbdllseg_next_ptr.
  rewrite eq1.
  destruct (beq_val p (nth_val' 0 a)) eqn : eq3; split; auto.
  apply beq_val_true_eq in eq3; substs.
  unfold tcbdllseg1_get_node in H0; fold tcbdllseg1_get_node in H0.
  rewrite beq_val_true in H0.
  inverts H0.
  intro.
  apply H.
  clear - H1 H0.
  unfold ptr_in_tcbdllseg1 in *; fold ptr_in_tcbdllseg1 in *.
  destruct (beq_val head (nth_val' 0 a)); auto.
  destruct (V_OSTCBNext vl2) eqn : eq1; tryfalse.
  unfolds in H1.
  rewrite eq1 in H1.
  destruct (V_OSTCBNext vl1); tryfalse.
  destruct H1; substs; auto.

  clear - H1 H H0 eq3.
  assert ((v :: set_node p vl2 (nth_val' 0 v) l) = (set_node p vl2 (nth_val' 0 a) (v::l))).
  unfold set_node at 2; fold set_node.
  rewrite eq3; auto.
  rewrite H2; clear H2.
  eapply not_ptr_in_tcbdllseg1_set_node; eauto.
Qed.

Lemma same_prev_next_sym :
  forall vl1 vl2,
    same_prev_next vl1 vl2 -> same_prev_next vl2 vl1.
Proof.
  intros.
  unfold same_prev_next in *.
  destruct (V_OSTCBNext vl1);
    destruct (V_OSTCBNext vl2);
    destruct (V_OSTCBPrev vl1);
    destruct (V_OSTCBPrev vl2);
    simp join; tryfalse; auto.
Qed.


Lemma ptr_in_tcbdllseg1_set_node :
  forall l head p1 p2 vl1 vl2,
    tcbdllseg1_get_node p1 head l = Some vl1 ->
    same_prev_next vl1 vl2 ->
    ptr_in_tcbdllseg1 p2 head l ->
    ptr_in_tcbdllseg1 p2 head (set_node p1 vl2 head l).
Proof.
  inductions l; intros.
  simpl in H; tryfalse.
  
  unfold tcbdllseg1_get_node in H; fold tcbdllseg1_get_node in H.
  destruct (beq_val p1 head) eqn : eq1.
  inverts H.
  apply beq_val_true_eq in eq1; substs.
  unfold set_node; fold set_node.
  rewrite beq_val_true.
  unfold ptr_in_tcbdllseg1 in *; fold ptr_in_tcbdllseg1 in *.
  destruct (beq_val p2 head) eqn : eq1; auto.
  destruct (V_OSTCBNext vl1) eqn : eq2.
  unfolds in H0.
  rewrite eq2 in H0.
  destruct (V_OSTCBNext vl2); tryfalse.
  destruct H0; substs.
  auto.
  destruct (V_OSTCBNext vl2) eqn: eq3; auto.
  unfolds in H0.
  rewrite eq2 in H0; tryfalse.

  destruct (V_OSTCBNext a) eqn : eq2; tryfalse.
  unfold ptr_in_tcbdllseg1 in H1; fold ptr_in_tcbdllseg1 in H1.
  rewrite eq2 in H1.
  unfold set_node; fold set_node.
  rewrite eq1.
  unfold ptr_in_tcbdllseg1; fold ptr_in_tcbdllseg1.
  rewrite eq2.
  destruct (beq_val p2 head) eqn : eq3; auto.
  assert (nth_val' 0 a = v).
  apply nth_val_nth_val'_some_eq; auto.
  substs.
  eapply IHl; eauto.
Qed.

Lemma nodes_in_tcblist_set_node :
  forall nodes head l p vl1 vl2,
    nodes_in_tcblist nodes head l ->
    tcbdllseg1_get_node p head l = Some vl1 ->
    same_prev_next vl1 vl2 ->
    nodes_in_tcblist nodes head (set_node p vl2 head l).
Proof.
  inductions nodes; intros.
  simpl; auto.

  unfold nodes_in_tcblist in *; fold nodes_in_tcblist in *.
  destruct a.
  destruct H.
  split.
  
  eapply ptr_in_tcbdllseg1_set_node; eauto.
  eapply IHnodes; eauto.
Qed.

Lemma tcbdllseg1_get_node_set_node_same :
  forall l head p vl,
    ptr_in_tcbdllseg1 p head l ->
    tcbdllseg1_get_node p head (set_node p vl head l) = Some vl.
Proof.
  inductions l; intros.
  simpl in H; tryfalse.

  unfold ptr_in_tcbdllseg1 in H; fold ptr_in_tcbdllseg1 in H.
  unfold set_node; fold set_node.
  destruct (beq_val p head) eqn : eq1.
  apply beq_val_true_eq in eq1; substs.
  unfold tcbdllseg1_get_node; fold tcbdllseg1_get_node.
  rewrite beq_val_true; auto.

  destruct (V_OSTCBNext a) eqn : eq2; tryfalse.
  unfold tcbdllseg1_get_node; fold tcbdllseg1_get_node.
  rewrite eq1.
  rewrite eq2.
  rewrite nth_val_nth_val'_some_eq with (x:=v); auto.
Qed.

Lemma tcbdllseg1_get_node_set_node_diff' :
  forall l head p1 p2 vl1 vl2 vl2',
    beq_val p1 p2 = false ->
    tcbdllseg1_get_node p2 head l = Some vl2 ->
    same_prev_next vl2 vl2' ->
    tcbdllseg1_get_node p1 head (set_node p2 vl2' head l) = Some vl1 ->
    tcbdllseg1_get_node p1 head l = Some vl1.
Proof.
  inductions l; intros.
  simpl in H0; tryfalse.

  unfold tcbdllseg1_get_node in H0; fold tcbdllseg1_get_node in H0.
  unfold set_node in H2; fold set_node in H2.

  destruct (beq_val p1 head) eqn : eq1;
    destruct (beq_val p2 head) eqn : eq2.
  apply beq_val_true_eq in eq1;
    apply beq_val_true_eq in eq2; substs.
  rewrite beq_val_true in H; tryfalse.
  unfold tcbdllseg1_get_node; fold tcbdllseg1_get_node.
  rewrite eq1; auto. 
  unfold tcbdllseg1_get_node in H2; fold tcbdllseg1_get_node in H2.
  rewrite eq1 in H2.
  inverts H2; auto.
  
  unfold tcbdllseg1_get_node; fold tcbdllseg1_get_node.
  rewrite eq1.
  unfold tcbdllseg1_get_node in H2; fold tcbdllseg1_get_node in H2.
  rewrite eq1 in H2.
  inverts H0.
  destruct(V_OSTCBNext vl2') eqn : eq3; tryfalse.
  unfolds in H1.
  rewrite eq3 in H1.
  destruct (V_OSTCBNext vl2); tryfalse.
  destruct H1; substs.
  auto.

  unfold tcbdllseg1_get_node; fold tcbdllseg1_get_node.
  rewrite eq1.
  destruct (V_OSTCBNext a) eqn : eq3; tryfalse.
  unfold tcbdllseg1_get_node in H2; fold tcbdllseg1_get_node in H2.
  rewrite eq1 in H2.
  rewrite eq3 in H2.
  rewrite nth_val_nth_val'_some_eq with (x:=v) in H2; auto.
  lets Hx: IHl H2; eauto.
Qed.

Lemma same_prev_next_trans :
  forall vl1 vl2 vl3,
    same_prev_next vl1 vl2 ->
    same_prev_next vl2 vl3 ->
    same_prev_next vl1 vl3.
Proof.
  unfold same_prev_next; intros.
  destruct (V_OSTCBNext vl1);
    destruct (V_OSTCBNext vl2);
    destruct (V_OSTCBNext vl3);
    destruct (V_OSTCBPrev vl1);
    destruct (V_OSTCBPrev vl2);
    destruct (V_OSTCBPrev vl3); simp join; tryfalse.
  split; auto.
Qed.

Lemma tcbdllseg1_get_node_ptr_in_tcbdllseg1 :
  forall l head p vl,
    tcbdllseg1_get_node p head l = Some vl ->
    ptr_in_tcbdllseg1 p head l.
Proof.
  inductions l; intros.
  simpl in H; tryfalse.
  unfold tcbdllseg1_get_node in H; fold tcbdllseg1_get_node in H.
  unfold ptr_in_tcbdllseg1; fold ptr_in_tcbdllseg1.
  destruct (beq_val p head); auto.
  destruct (V_OSTCBNext a); tryfalse.
  eapply IHl; eauto.
Qed.

Lemma ptrs_not_change_set_node' :
  forall nodes l head p vl vl',
    tcbdllseg1_get_node p head l = Some vl ->
    same_prev_next vl vl' ->
    ptrs_not_change nodes head (set_node p vl' head l) ->
    ptrs_not_change nodes head l. 
Proof.
  inductions nodes; intros.
  simpl; auto.

  unfold ptrs_not_change in H1; fold ptrs_not_change in H1.
  destruct a.
  unfold ptrs_not_change; fold ptrs_not_change.
  destruct (tcbdllseg1_get_node v head (set_node p vl' head l)) eqn : eq1; tryfalse.
  destruct H1.
  destruct (beq_val v p) eqn : eq2.
  apply beq_val_true_eq in eq2; substs.
  rewrite H.
  split.
  rewrite tcbdllseg1_get_node_set_node_same in eq1.
  inverts eq1.
  eapply same_prev_next_trans; eauto.
  eapply tcbdllseg1_get_node_ptr_in_tcbdllseg1; eauto.
  eapply IHnodes; eauto.
  
  lets Hx: tcbdllseg1_get_node_set_node_diff' eq2 H H0 eq1.
  rewrite Hx.
  split; auto.
  lets Hx1: IHnodes H2; eauto.
Qed.

Lemma tcbdllseg1_node_join' :
  forall l p vl vl' head headprev tail tailnext holes P,
    ptr_in_tcbdllseg1 p head l ->
    same_prev_next vl' vl ->
    ~ ptr_in p holes ->
    distinct_ptr holes ->
    distinct_tcbdllseg_next_ptr head l ->
    node p vl' OS_TCB_flag ** tcbdllseg1 head headprev tail tailnext l ((p,vl)::holes) ** P
         ==>
         tcbdllseg1 head headprev tail tailnext (set_node p vl' head l) holes ** P.
Proof.
  intros.
  sep auto.
  eapply tcbdllseg1_node_join; eauto.
Qed.


Lemma ptrs_not_change_intro :
  forall nodes l head headprev tail tailnext holes s P,
    s |= tcb_nodes nodes ** tcbdllseg1 head headprev tail tailnext l holes ** P ->
    nodes_in_tcblist nodes head l ->
    nodes_holes_match nodes holes ->
    distinct_tcbdllseg_next_ptr head l ->
    distinct_ptr holes ->
    ptrs_not_change nodes head l.
Proof.
  inductions nodes; intros.
  simpl; auto.

  unfold ptrs_not_change; fold ptrs_not_change; destruct a.
  unfold nodes_in_tcblist in H0; fold nodes_in_tcblist in H0; destruct H0.
  destruct holes.
  simpl in H1; tryfalse.
  destruct p.
  unfold nodes_holes_match in H1; fold nodes_holes_match in H1.
  destruct (beq_val v v1) eqn : eq1; tryfalse.
  destruct H1.
  apply beq_val_true_eq in eq1; substs.
  sep lift 2%nat in H.
  lets Hx: ptr_in_tcbdllseg1_get_some H; auto.
  rewrite Hx.
  split.
  apply same_prev_next_sym; auto.

  unfold tcb_nodes in H; fold tcb_nodes in H.
  sep normal in H.
  sep lift 2%nat in H.
  unfold distinct_ptr in H3; fold distinct_ptr in H3; destruct H3.
  eapply tcbdllseg1_node_join' in H; eauto.
  sep lift 2%nat in H.
  lets Hx1: IHnodes H H5 H6.
  eapply nodes_in_tcblist_set_node; eauto.
  apply same_prev_next_sym; auto.
  eapply distinct_tcbdllseg_next_ptr_set_node; eauto.
  apply same_prev_next_sym; auto.
  eapply ptrs_not_change_set_node'; eauto.
  apply same_prev_next_sym; auto.
Qed.

Lemma TCBList_P_set_node :
  forall l head vl vl' tcbls t absdata rtbl,
    TCBNode_P vl' rtbl absdata ->
    tcbdllseg1_get_node (Vptr t) head l = Some vl ->
    same_prev_next vl vl' ->
    TCBList_P head l rtbl tcbls ->
    TCBList_P head (set_node (Vptr t) vl' head l) rtbl (TcbMod.set tcbls t absdata).
Proof.
  inductions l; intros.
  simpl in H0; tryfalse.

  unfold tcbdllseg1_get_node in H0; fold tcbdllseg1_get_node in H0.
  unfold set_node; fold set_node.
  unfold TCBList_P in H2; fold TCBList_P in H2; simp join.
  destruct (beq_val (Vptr t) (Vptr x)) eqn : eq1.
  apply beq_val_true_eq in eq1; inverts eq1.
  inverts H0.
  unfold TCBList_P; fold TCBList_P.
  do 4 eexists; splits; eauto.
  unfolds in H1.
  rewrite H3 in H1.
  destruct (V_OSTCBNext vl'); tryfalse; simp join.

  unfold TcbJoin.
  clear - H4.
  unfolds; intro.
  unfold sig; simpl.
  pose proof H4 a.
  destruct (tidspec.beq x a) eqn : eq1.
  lets Hx: tidspec.beq_true_eq eq1; substs.
  rewrite TcbMod.get_sig_some in *.
  rewrite TcbMod.set_a_get_a; auto.
  destruct (TcbMod.get x1 a); tryfalse; auto.

  lets Hx: tidspec.beq_false_neq eq1.
  rewrite TcbMod.get_sig_none in *; auto.
  rewrite TcbMod.set_a_get_a'; auto.

  destruct (V_OSTCBNext a) eqn : eq2; tryfalse.
  unfold TCBList_P; fold TCBList_P.
  do 4 eexists; splits; eauto.
  instantiate (1:= TcbMod.set x1 t absdata).
  simpl in eq1.
  clear - H4 eq1.
  intro.
  pose proof H4 a.
  destruct (tidspec.beq x a) eqn : eq2.
  lets Hx: tidspec.beq_true_eq eq2.
  substs.
  rewrite TcbMod.get_sig_some in *.
  assert(t <> a).
  intro; substs.
  rewrite beq_addrval_true in eq1; tryfalse.
  rewrite TcbMod.set_a_get_a'; auto.
  rewrite TcbMod.set_a_get_a'; auto.

  lets Hx: tidspec.beq_false_neq eq2.
  rewrite TcbMod.get_sig_none in *; auto.
  destruct (tidspec.beq t a) eqn : eq3.
  lets Hx1: tidspec.beq_true_eq eq3; substs.
  rewrite TcbMod.set_a_get_a; auto.
  rewrite TcbMod.set_a_get_a; auto.
  
  lets Hx1: tidspec.beq_false_neq eq3.
  rewrite TcbMod.set_a_get_a'; auto.
  rewrite TcbMod.set_a_get_a'; auto.

  assert(nth_val' 0 a = v).
  apply nth_val_nth_val'_some_eq; auto.
  inverts H3.
  substs.
  eapply IHl; eauto.
Qed.

Lemma tcbdllseg1_get_node_set_node_diff :
  forall l head p1 p2 vl1 vl2 vl2',
    beq_val p1 p2 = false ->
    tcbdllseg1_get_node p1 head l = Some vl1 ->
    tcbdllseg1_get_node p2 head l = Some vl2 ->
    same_prev_next vl2 vl2' ->
    tcbdllseg1_get_node p1 head (set_node p2 vl2' head l) = Some vl1.
Proof.
  inductions l; intros.
  simpl in H0; tryfalse.

  unfold tcbdllseg1_get_node in H0; fold tcbdllseg1_get_node in H0.
  unfold set_node; fold set_node.

  destruct (beq_val p1 head) eqn : eq1;
    destruct (beq_val p2 head) eqn : eq2.
  apply beq_val_true_eq in eq1;
    apply beq_val_true_eq in eq2; substs.
  rewrite beq_val_true in H; tryfalse.
  unfold tcbdllseg1_get_node; fold tcbdllseg1_get_node.
  rewrite eq1; auto.
  unfold tcbdllseg1_get_node; fold tcbdllseg1_get_node.
  rewrite eq1.
  unfold tcbdllseg1_get_node in H1; fold tcbdllseg1_get_node in H1.
  rewrite eq2 in H1.
  inverts H1.
  destruct(V_OSTCBNext vl2) eqn : eq3; tryfalse.
  unfolds in H2.
  rewrite eq3 in H2.
  destruct (V_OSTCBNext vl2'); tryfalse.
  destruct H2; substs.
  auto.

  unfold tcbdllseg1_get_node; fold tcbdllseg1_get_node.
  rewrite eq1.
  destruct (V_OSTCBNext a) eqn : eq4; tryfalse.
  unfold tcbdllseg1_get_node in H1; fold tcbdllseg1_get_node in H1.
  rewrite eq2 in H1.
  rewrite eq4 in H1.
  rewrite nth_val_nth_val'_some_eq with (x:=v); auto.
  eapply IHl; eauto.
Qed.

Lemma ptrs_not_change_set_node :
  forall nodes l head p vl vl',
    tcbdllseg1_get_node p head l = Some vl ->
    same_prev_next vl vl' ->
    ptrs_not_change nodes head l ->
    ptrs_not_change nodes head (set_node p vl' head l). 
Proof.
  inductions nodes; intros.
  simpl; auto.

  unfold ptrs_not_change; fold ptrs_not_change.
  destruct a.
  unfold ptrs_not_change in H1; fold ptrs_not_change in H1.
  destruct (tcbdllseg1_get_node v head l) eqn : eq1; tryfalse.
  destruct H1.
  destruct (beq_val v p) eqn : eq2.
  apply beq_val_true_eq in eq2; substs.
  rewrite H in eq1; inverts eq1.
  
  rewrite tcbdllseg1_get_node_set_node_same.
  split.
  apply same_prev_next_sym in H0.

  eapply same_prev_next_trans; eauto.
  eapply IHnodes; eauto.

  eapply tcbdllseg1_get_node_ptr_in_tcbdllseg1; eauto.

  erewrite tcbdllseg1_get_node_set_node_diff; eauto.
Qed.


(*-------------------------end of lemmas-----------------------------------*)
(*-------------------------------------------------------------------------*)
(*------------------------ main lemmas ------------------------------------*)
 
Lemma tcbdllseg1_init :
  forall ptrs l head headprev tail tailnext P,
    tcbdllseg head headprev tail tailnext l **
    [|ptrs_in_tcblist ptrs head l|] **
    [|NoDup ptrs|]** P
  ==>
    split_tcb_nodes ptrs head headprev tail tailnext l **

    (*the 2 pure properties below are used by the combining lemma*)
    [|ptrs_in_tcblist ptrs head l|] **
    [|distinct_tcbdllseg_next_ptr head l|] ** P.
Proof.
  intros.  
  sep split in H.
  apply tcbdllseg1_init' in H.
  sep split in H; sep split; auto.
  apply ptrs_in_tcblist_ptrs_in_tcblist1 in H0.
  eapply tcbdllseg1_init1; eauto.
Qed.


Lemma tcbdllseg1_combine :
  forall nodes l head headprev tail tailnext holes P,
    tcb_nodes nodes **
    tcbdllseg1 head headprev tail tailnext l holes **
    [|nodes_in_tcblist nodes head l|] **  (*from ptrs_in_tcblist*)         
    [|nodes_holes_match nodes holes|] **
    [|distinct_tcbdllseg_next_ptr head l|] ** P
  ==>
    tcbdllseg head headprev tail tailnext (set_nodes nodes head l) **
    [|nodes_in_tcblist nodes head l|] **
    [|ptrs_not_change nodes head l|] ** P.
Proof.
  intros.
  
  assert(distinct_ptr holes).
  sep split in H.
  sep remember (1::nil)%nat in H.
  simpl_sat H; simp join.
  eapply distinct_ptr_holes.
  sep split; eauto.
  rename H0 into Hxx.
  sep split.
  
  inductions nodes; intros.
  unfold tcb_nodes in H.
  unfold set_nodes.
  sep auto.
  unfolds in H1.
  destruct holes; tryfalse.
  apply tcbdllseg1_tcbdllseg; auto.
 
  unfold set_nodes; fold set_nodes; destruct a.
  sep split in H.
  destruct holes.
  simpl in H1; tryfalse.
  unfold nodes_holes_match in H1; fold nodes_holes_match in H1.
  destruct p.
  destruct (beq_val v v1) eqn : eq1; tryfalse.
  destruct H1.
  unfold nodes_in_tcblist in H0; fold nodes_in_tcblist in H0; destruct H0.
  unfold distinct_ptr in Hxx; fold distinct_ptr in Hxx; destruct Hxx.  
  eapply IHnodes with (holes:=holes); auto.
  sep split; eauto.
  unfold tcb_nodes in H; fold tcb_nodes in H.
  sep auto.
  apply beq_val_true_eq in eq1; substs.

  eapply tcbdllseg1_node_join; eauto.
  apply beq_val_true_eq in eq1; substs.

  assert (tcbdllseg1_get_node v1 head l = Some v2).
  sep lift 2%nat in H.
  eapply ptr_in_tcbdllseg1_get_some in H; auto.

  eapply distinct_tcbdllseg_next_ptr_set_node; eauto.
  apply same_prev_next_sym; auto.

  apply beq_val_true_eq in eq1; substs.
  sep lift 2%nat in H.
  eapply ptr_in_tcbdllseg1_get_some in H; auto.
  
  eapply nodes_in_tcblist_set_node; eauto.
  apply same_prev_next_sym; auto.
  
  sep split in H.
  eapply ptrs_not_change_intro; eauto.
  sep split in H; auto.
Qed.


(*----------end-------------*)

Fixpoint nodes_absnodes_match (nodes:list(val*vallist)) (absnodes:list(tid*(priority*taskstatus*msg))) (rtbl:vallist) : Prop :=
  match nodes, absnodes with
    | nil, nil => True
    | (p,vl)::nodes', (tid,abstcb)::absnodes' =>
      p = Vptr tid /\ TCBNode_P vl rtbl abstcb /\ nodes_absnodes_match nodes' absnodes' rtbl
    | _, _ => False
  end.

Fixpoint set_abstcb (absnodes:list(tid*(priority*taskstatus*msg))) (tcbls:TcbMod.map) : TcbMod.map :=
  match absnodes with
    | nil => tcbls
    | (tid,abstcb)::absnodes' =>
      set_abstcb absnodes' (TcbMod.set tcbls tid abstcb)
  end.

Lemma TCBList_P_set_nodes :
  forall nodes absnodes head l rtbl tcbls,
    TCBList_P head l rtbl tcbls ->
    nodes_absnodes_match nodes absnodes rtbl ->
    nodes_in_tcblist nodes head l ->
    ptrs_not_change nodes head l ->
    TCBList_P head (set_nodes nodes head l) rtbl (set_abstcb absnodes tcbls).
Proof.
  inductions nodes; intros; destruct absnodes.
  simpl; auto.
  simpl in H0; tryfalse.
  simpl in H0; destruct a; tryfalse.

  unfold set_nodes; fold set_nodes.
  unfold set_abstcb; fold set_abstcb.
  destruct a, p.
  unfold nodes_absnodes_match in H0; fold nodes_absnodes_match in H0; simp join.
  apply IHnodes; auto.
  unfold nodes_in_tcblist in H1; fold nodes_in_tcblist in H1.
  destruct H1.
  unfold ptrs_not_change in H2; fold ptrs_not_change in H2.
  destruct (tcbdllseg1_get_node (Vptr t) head l) eqn : eq1; tryfalse; destruct H2.
  
  eapply TCBList_P_set_node; eauto.
  unfold nodes_in_tcblist in H1; fold nodes_in_tcblist in H1; destruct H1.
  unfold ptrs_not_change in H2; fold ptrs_not_change in H2.
  destruct (tcbdllseg1_get_node (Vptr t) head l) eqn : eq1; tryfalse.
  destruct H2.
  eapply nodes_in_tcblist_set_node; eauto.

  unfold nodes_in_tcblist in H1; fold nodes_in_tcblist in H1; destruct H1.
  unfold ptrs_not_change in H2; fold ptrs_not_change in H2.
  destruct (tcbdllseg1_get_node (Vptr t) head l) eqn : eq1; tryfalse.
  destruct H2.

  eapply ptrs_not_change_set_node; eauto.
Qed.
