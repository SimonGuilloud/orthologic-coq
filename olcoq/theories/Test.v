Require Import OLPlugin.
Require Import OL_Reflection_5_pointers.
Require Import OL_Reflection_1_base.
Require Import OL_Theory.

Open Scope bool_scope.
Require Import Btauto.


Axiom False : forall (P:Prop), P.

Ltac sorry := apply False.


Ltac ol_norm e := let e' := fresh "e" with Hol := fresh "Hol" in
  olget e e'; assert (e = e') as Hol by (subst e'; (solveOLPointers BoolOL)); subst e'; try rewrite Hol; clear Hol.

Ltac ol_norm_unsafe e := let e' := fresh "e" with Hol := fresh "Hol" in
  olget e e'; assert (e = e') as Hol by sorry; subst e'; try rewrite Hol; clear Hol.

Ltac ol_norm2 e := match e with 
  | _ => 
    lazymatch type of e with
      | bool => ol_norm e
      | _ => fail
    end
  | ?f ?arg => ol_norm2 f; ol_norm2 arg
  | _ => idtac
end.

Ltac ol_norm2_unsafe e := match e with 
  | _ => 
    lazymatch type of e with
      | bool => ol_norm_unsafe e
      | _ => fail
    end
  | ?f ?arg => ol_norm2_unsafe f; ol_norm2_unsafe arg
  | _ => idtac
end.

Ltac ol_norm3_unsafe := (lazymatch goal with
  | [ |- ?e ] => ol_norm2_unsafe e
end).



Ltac ol_norm3 := (lazymatch goal with
  | [ |- ?e ] => ol_norm2 e
end).

Tactic Notation "olnormalize" constr(e) := ol_norm2 e.
Tactic Notation "olnormalize" := ol_norm3.


Ltac destr_subbool e := 
  lazymatch e with
  | ?e1 <= ?e2 => first [destr_subbool e1 | destr_subbool e2]
  | ?e1 = ?e2 => first [destr_subbool e1 | destr_subbool e2]
  | true => fail
  | false => fail
  | (negb ?a) => destr_subbool a
  | ?a && ?b => first [destr_subbool a | destr_subbool b]
  | ?a || ?b => first [destr_subbool a | destr_subbool b]
  | _ => destruct e
  end.

Ltac destr_subbool_goal := match goal with
  | [ |- ?e ] => destr_subbool e
end.

Ltac oltauto := 
  repeat (olnormalize; lazymatch goal with
  | [ |- ?e1 = ?e1 ] => reflexivity
  | [ |- ?e1 <= ?e1 ] => apply P1
  | [ |- ?e ] => destr_subbool_goal
  end).

Example test9 : forall a b c: bool,  (a && (b || c) || (a && b) || (a && c)) = a && (b || c) && (a && b) || (a && c).
Proof.
  intros.
(*olnormalize. *)
  oltauto.
Qed.

Example test10 : forall a b c: bool,  (a && (b || c) || (a && b) || (a && c)) = a && (b || c) && (a && b) || (a && c).
Proof.
  intros.
  assert ((a && (b || c) || (a && b) || (a && c)) = a && (b || c) && (a && b) || (a && c)).
  - destruct a; ol_norm3; reflexivity.
  - destruct a; ol_norm3_unsafe; reflexivity.
Qed.

Example test8 : forall a b c: bool,  (a && (negb a)) <= (c || (b && negb b)).
Proof.
  intros.
  olnormalize (a && (negb a)).
  olnormalize.
  solveOLPointers BoolOL.
Qed.