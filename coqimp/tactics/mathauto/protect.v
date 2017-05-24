Require Import LibTactics.

Definition ProtectWrapper (a:Type) : Type :=a.
Lemma MakeProtectWrapper : forall H, H -> ProtectWrapper H.
Proof.
  auto.
Qed.
Ltac protect H := let H' := fresh in rename H into H'; lets H : MakeProtectWrapper H'; clear H'.
Ltac unprotect H := unfold ProtectWrapper in H.

