Require Import OLPlugin.
Require Import OL_Reflection_1_base.

(* The orthologic-coq plugin enables orthologic-based reasoning *)

(* the `solveOLPointers` tactic allows to solve inequality in ortholattices: *)

Example example1 {OL: Ortholattice} a b c:
  ¬(b ∪ ¬(c ∩ ¬b) ∪ a) <= (¬a ∪ ¬(b ∩ ¬a)).
Proof.
  solveOLPointers OL.
Qed.

Example example2 (a b c: bool):
  ((a && b) || (negb a) || (negb b)) = true.
Proof.
  solveOLPointers BoolOL.
Qed.

(* solveOLPointers is reflection-based. Alternatively, use the `olcert_goal` tactic which is proof-producing. *)
Example example3 (a b c: bool):
  (a && (negb a)) = (((b && c) || b) && (negb b)).
Proof.
  olcert_goal.
Qed.

Axiom admit: forall A, A.

(* if the goal is not an ol-tautology, it is still possible to make progress by normalizing it: *)
Example example4 (f: bool -> nat) (a b c: bool) : f (a && (b || c) && (a && b) || (a && c)) >= 5.
Proof.
  olnormalize.
  Validate Proof.
Admitted.

(* olnormalize uses solveOLPointers under the hood; olnormalize_cert is similar
   but uses olcert_goal instead. *)
Example example4a (f: bool -> nat) (a b c: bool) : f (a && (b || c) && (a && b) || (a && c)) >= 5.
Proof.
  olnormalize_cert.
  Validate Proof.
Admitted.

(* Finally, arbitrary boolean equalities (not just OL equalities) can be solved using oltauto. *)
Example example5 (a b c: bool):
    (a && (b || c) || (a && b) || (a && c)) = a && (b || c) && (a && b) || (a && c).
Proof.
  oltauto.
Qed.

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
  all: firstorder;
    repeat match goal with
      | [ e: nat, H: nat -> _ |- _ ] => specialize (H e)
      end;
    try destruct (x e); try destruct (y e);
    firstorder.
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
  all: intros; eauto 2 with ol.
  - repeat split; intros; pose proof (equiv_leq (x e) (y e)); firstorder.
Defined.

(* Then SubsetsNatOL is isomorphic to (OL_Valued_Set nat BoolOL) *)

(* And we can chain the construction to obtain that the "ol-powerset" of any set is an ortholattice: *)

Definition myOl S T := (OL_Valued_Set S (OL_Valued_Set T SubsetsNatOL)).

Example example7 (S T: Set) (a: S -> T -> (@A SubsetsNatOL)):
  @leq (myOl S T) a a.
Proof.
  solveOLPointers (myOl S T).
Qed.
