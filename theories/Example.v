Require Import OLPlugin.



(* Subsets of a set S form an ortholattice. *)

#[refine] Instance SubsetsOL (*{S: Set}*) : Ortholattice := {
  A := nat -> bool; (*S -> bool;*)
  e := fun x => false;
  leq x y := forall e, x e = true -> y e = true;
  meet x y := fun e => x e && y e;
  join x y := fun e => x e || y e;
  neg x := fun e => negb (x e);
  equiv x y := forall e, x e = y e;
  zero := fun e => false;
  one := fun e => true;
}.
Proof.
  all: intros.
  - repeat split; intros.
    + congruence.
    + congruence.
    + destruct H as [H1 H2]; specialize (H1 e); specialize (H2 e).
      destruct (x e); destruct (y e); simpl in *; auto. symmetry; auto.
  - congruence.
  - congruence.
  - auto.
  - intuition.
  - destruct (x e); auto.
  - destruct (x e); destruct (y e); auto.
  - specialize (H e H1). specialize (H0 e H1).
    destruct (y e); destruct (z e); simpl in *; auto.
  - destruct (x e); auto.
  - specialize (H e). 
    destruct (x e); destruct (y e); simpl in *; auto.
  - destruct (x e); simpl in *; congruence.
  - rewrite H; simpl; auto.
  - rewrite H; destruct (x e); simpl; auto.
  - apply Bool.orb_prop in H1; destruct H1; eauto.
  - destruct (x e); simpl in *; auto.
  - destruct (y e); simpl; auto.
Defined.

Example test9  (a b c: nat -> bool): 
  c <= ((a ∩ b) ∪ (¬a) ∪ (¬b)).
Proof.
  solveOLPointers SubsetsOL.
Qed.
