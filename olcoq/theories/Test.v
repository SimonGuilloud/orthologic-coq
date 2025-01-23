Require Import OLPlugin.
Require Import OL_Reflection_4_pointers.
Require Import OL_Theory.

Open Scope bool_scope.


Lemma foo : True. 

Proof.
hello. 
hello_ol.
now auto.
Qed.

Example test8 : forall a b c: bool,  (a ∩ (negb a)) <= (a || (b && c)).
Proof.
  intros.
  olget ((a ∩ (negb a)) <= (a || (b && c))).
  solveOLPointers BoolOL.
Qed.

Check test8.
