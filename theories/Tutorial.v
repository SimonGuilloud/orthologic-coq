Require Import OLPlugin.
Require Import OL_Reflection_1_base.

(* The orthologic-coq plugin enables orthologic-based reasoning *)

(* the `solveOLPointers` tactic allows to solve inequality in ortholattices: *)

Example example1 {OL: Ortholattice} a b c: 
  ¬(b ∪ ¬(c ∩ ¬b) ∪ a) <= (¬a ∪ ¬(b ∩ ¬a)).
Proof.
  intros. 
  solveOLPointers OL.
Qed.

Example example2 (a b c: bool): 
  ((a && b) || (negb a) || (negb b)) = true.
Proof.
  intros. 
  solveOLPointers BoolOL.
Qed.

(* solveOLPointers is reflection-based. Alternatively, use the `olcert_goal` tactic which is proof-producing. *)
Example example3 (a b c: bool): 
  (a && (negb a)) = (((b && c) || b) && (negb b)).
Proof.
  intros. 
  olcert_goal.
Qed.

(* if the goal is not an ol-tautology, it is still possible to make progress by normalizing it: *)
Example example4 (f: bool -> nat) (a b c: bool) : f (a && (b || c) && (a && b) || (a && c)) >= 5.
Proof.
  olnormalize.
  admit.
Admitted.

(* Finally, arbitrary boolean equality an be solved using oltauto.*)
Example example5 : forall a b c: bool,  (a && (b || c) || (a && b) || (a && c)) = a && (b || c) && (a && b) || (a && c).
Proof.
  intros. 
  oltauto.
Qed.

(* olnormalize_cert and oltauto_cert are also available, the difference being that they rely on 
   olcert_goal rater than solveOlPointers. *)


(* We can also define new ortholattices to benefit from the reflexive decision procedure. *)

(* For example, the type of subsets of the natural numbers is an ortholattice. *)

#[refine] Instance SubsetsNatOL  : Ortholattice := {
  A := nat -> bool; 
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

Example example6 (a b c: nat -> bool): 
  c <= ((a ∩ b) ∪ (¬a) ∪ (¬b)).
Proof.
  solveOLPointers SubsetsNatOL.
Qed.



(* In fact, we can generalize the construction, for any base set S and any ortholattice O *)


#[refine] Instance OL_Valued_Set (S: Set) (O: Ortholattice) : Ortholattice := {
  A := S -> @A O;
  e := fun x => @zero O;
  leq x y := forall e, leq (x e) (y e);
  meet x y := fun e => x e ∩ y e;
  join x y := fun e => x e ∪ y e;
  neg x := fun e => ¬ (x e);
  equiv x y := forall e, equiv (x e) (y e);
  zero := fun e => @zero O;
  one := fun e => @one O;
}.
Proof.
  all: intros.
  - (*pose proof equiv_leq as H.*)
   repeat split; intros; pose proof (equiv_leq (x e) (y e)).
    + intuition. apply H1; auto.
    + intuition. apply H1; auto.
    + intuition.
  - apply zero_leq.
  - apply one_leq.
  - apply P1.
  - eapply P2; eauto.
  - apply P4.
  - apply P5.
  - apply P6; auto.
  - apply P7.
  - apply P8; auto.
  - apply P9.
  - apply P4'.
  - apply P5'.
  - apply P6'; auto.
  - apply P7'.
  - apply P9'; auto.
Defined.


(* Then SubsetsNatOL is isomorphic to (OL_Valued_Set nat BoolOL) *)

(* And we can chain the construction to obtain that the "ol-powerset" of any set is an ortholattice: *)

Definition myOl S T := (OL_Valued_Set S (OL_Valued_Set T SubsetsNatOL)).

Example example7 (S T: Set) (a: S -> T -> (@A SubsetsNatOL)): 
  @leq (myOl S T) a a.
Proof.
  solveOLPointers (myOl S T).
Qed.