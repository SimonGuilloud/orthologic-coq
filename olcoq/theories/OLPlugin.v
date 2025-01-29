Declare ML Module "coq_ol:coq-ol.plugin".

Require Import OL_Theory.
Require Import OL_Reflection_5_pointers.
Require Import OL_Reflection_1_base.
Require Import Bool.
Require Import Btauto.
Open Scope bool_scope.

Definition tpair a b := (a || b) = true.

Ltac easy := intros; unfold tpair in *; repeat match goal with
  | [ b : bool|- _ ] => destruct b
  | _ => simpl in *; unfold tpair; congruence
end.


Theorem left_true_or b : tpair true b. easy.  Qed.
Theorem right_true_or a : tpair a true. easy. Qed.
Theorem left_neg_or b : tpair (negb b) b. easy. Qed.
Theorem right_neg_or a : tpair a (negb a). easy. Qed.
Theorem left_and_or a1 a2 b : tpair a1 b -> tpair a2 b -> tpair (a1 && a2) b. intros; easy. Qed.
Theorem right_and_or a b1 b2 : tpair a b1 -> tpair a b2 -> tpair a (b1 && b2). easy. Qed.
Theorem left_or_or_1 a1 a2 b : tpair a1 b -> tpair (a1 || a2) b. easy. Qed.
Theorem left_or_or_2 a1 a2 b : tpair a2 b -> tpair (a1 || a2) b. easy. Qed.
Theorem right_or_or_1 a b1 b2 : tpair a b1 -> tpair a (b1 || b2). easy. Qed.
Theorem right_or_or_2 a b1 b2 : tpair a b2 -> tpair a (b1 || b2). easy. Qed.
Theorem contract_or_1 a b : tpair a a -> tpair a b. easy. Qed.
Theorem contract_or_2 a b : tpair b b -> tpair a b. easy. Qed.

Register OLPlugin.tpair as olplugin.tpair.
Register OLPlugin.left_true_or as olplugin.left_true_or.
Register OLPlugin.right_true_or as olplugin.right_true_or.
Register OLPlugin.left_neg_or as olplugin.left_neg_or.
Register OLPlugin.right_neg_or as olplugin.right_neg_or.
Register OLPlugin.left_and_or as olplugin.left_and_or.
Register OLPlugin.right_and_or as olplugin.right_and_or.
Register OLPlugin.left_or_or_1 as olplugin.left_or_or_1.
Register OLPlugin.left_or_or_2 as olplugin.left_or_or_2.
Register OLPlugin.right_or_or_1 as olplugin.right_or_or_1.
Register OLPlugin.right_or_or_2 as olplugin.right_or_or_2.
Register OLPlugin.contract_or_1 as olplugin.contract_or_1.
Register OLPlugin.contract_or_2 as olplugin.contract_or_2.

Theorem tpair_to_eq a b : tpair (negb a) b -> tpair a (negb b) -> a = b.
Proof.
  intros. easy.
Qed.

Theorem tpair_to_leq a b : tpair (negb a) b -> a <= b.
Proof.
  intros. easy; simpl in *; auto.
Qed.

Register OLPlugin.tpair_to_eq as olplugin.tpair_to_eq.
Register OLPlugin.tpair_to_leq as olplugin.tpair_to_leq.


  (* olget *)


  (* nnf *)
Lemma xorb_decompose a b : xorb a b = andb (orb a b) (orb (negb a) (negb b)).
Proof.
  destruct a, b; auto.
Qed.

Lemma eqb_decompose a b : eqb a b = orb (andb a b) (andb (negb a) (negb b)).
Proof.
  destruct a, b; auto.
Qed.

Lemma negb_false : negb (false) = true.
Proof.
  reflexivity.
Qed.

Lemma negb_true : negb (true) = false.
Proof.
  reflexivity.
Qed.

Hint Rewrite negb_orb negb_andb negb_involutive negb_true_iff 
             negb_false_iff xorb_decompose eqb_decompose negb_false negb_true
            : nnf_lemmas.


Ltac nnf := autorewrite with nnf_lemmas.



Example test1 : tpair true true.
Proof.
  olcert_goal. 
Qed.

Example test2 a : tpair true a.
Proof.
  olcert_goal. 
Qed.

Example test3 a : tpair a true.
Proof.
  olcert_goal. 
Qed.

Example test4 a b: tpair true (a || b).
Proof.
  olcert_goal. 
Qed.

Example test5 a b: tpair (a && b) true.
Proof.
  olcert_goal. 
Qed.

Example test6 a : tpair (negb a) a.
Proof.
  olcert_goal. 
Qed.

Example test7 a : tpair a (negb a).
Proof.
  olcert_goal. 
Qed.

Example test8 a: tpair (a && a ) (negb a).
Proof.
  olcert_goal. 
Qed.

Example test9 a: tpair a ((negb a) && (negb a)).
Proof.
  olcert_goal. 
Qed.

Example test10 a b: tpair (a || b) (negb a).
Proof.
  olcert_goal. 
Qed.

Example test11 a b: tpair (a || b) (negb b).
Proof.
  olcert_goal. 
Qed.

Example test12 a b: tpair a ((negb a) || b).
Proof.
  olcert_goal. 
Qed.

Example test13 a b: tpair a (b || (negb a)).
Proof.
  olcert_goal. 
Qed.

Example test14 a b c: tpair (a || negb a) (b || c).
Proof.
  olcert_goal. 
Qed.

Example test15 (a:bool) : a = a.
Proof.
  olcert_goal.
Qed.

Example test16 a b: (a && b) = (b && a).
Proof.
  olcert_goal.
Qed.


Example test17_1 (a b : bool) : tpair (negb a) (a && a).
Proof.
  olcert_goal. 
Qed.

Example test17_2 (a b : bool) : tpair a (negb (a && a)).
Proof.
  olcert_goal. 
Qed.
Example test17 (a b : bool) : a && a = (a).
Proof.
  olcert_goal.
Qed.

Example test18 a: (a || a || negb a) = true.
Proof.
  olcert_goal. 
Qed.

Example test19 a b: ((negb a) || (negb b) || (a && b)) = true.
Proof.
  olcert_goal.
Qed.

Example test20 : forall a b c: bool,  (a && a) = (a && a && a) .
Proof.
  intros.
  olcert_goal.
Qed.


(* olnormalize *)

Ltac ol_norm e := let e' := fresh "e" with Hol := fresh "Hol" in
  olget e e'; 
  replace e with e' by (subst e'; (solveOLPointers BoolOL)); subst e'.
  
Ltac ol_norm2 e := match e with 
  | _ => 
    lazymatch type of e with
      | bool => ol_norm e
      | _ => fail
    end
  | ?f ?arg => ol_norm2 f; ol_norm2 arg
  | _ => idtac
end.

Ltac ol_norm3 := (lazymatch goal with
  | [ |- ?e ] => ol_norm2 e
end).


Tactic Notation "olnormalize" constr(e) := ol_norm2 e.
Tactic Notation "olnormalize" := ol_norm3.

Tactic Notation "olnormalize_cert" constr(e) := ol_norm_cert e.
Tactic Notation "olnormalize_cert" := ol_norm_cert_goal.

Example test_olnortmalize_1 a b : (a && b) = (b && a).
Proof.
  olnormalize (a && b).
  olnormalize (b && a).
  solveOLPointers BoolOL.
Qed.

Example test_olnortmalize_2 a b : (a && negb a) = (b && negb b).
Proof.
  olnormalize.
  solveOLPointers BoolOL.
Qed.

Example test_olnortmalize_3 a b c: (a && (negb a)) = (((b && c) || b) && (negb b)).
Proof.
  olnormalize.
  solveOLPointers BoolOL.
Qed.

Example test_olnortmalize_4 a b : (a && b) = (b && a).
Proof.
  olnormalize_cert (a && b).
  solveOLPointers BoolOL.
Qed.

Example test_olnortmalize_5 a b : (a && negb a) = (b && negb b).
Proof.
  olnormalize_cert.
  solveOLPointers BoolOL.
Qed.

Example test_olnortmalize_6 a b c: (a && (negb a)) = (((b && c) || b) && (negb b)).
Proof.
  olnormalize_cert.
  solveOLPointers BoolOL.
Qed.




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


  (* oltauto*)

Ltac oltauto := 
  repeat (try (now solveOLPointers BoolOL); olnormalize; destr_subbool_goal).




  (* tests *)
Example test23 : forall a b c: bool,  (a && (b || c) || (a && b) || (a && c)) = a && (b || c) && (a && b) || (a && c).
Proof.
  intros.
  ol_norm_cert_goal. destruct a; olcert_goal.
Qed.

Example test24 : forall a b c: bool,  (a && (b || c) || (a && b) || (a && c)) = a && (b || c) && (a && b) || (a && c).
Proof.
  intros.
  oltauto.
Qed.

Example test25 : forall a b c: bool,  (a && (negb a)) <= (c || (b && negb b)).
Proof.
  intros.
  olnormalize (a && (negb a)).
  olnormalize.
  solveOLPointers BoolOL.
Qed.


Example oltauto1 : forall a b c: bool,  (a && (b || c) || (a && b) || (a && c)) = a && (b || c) && (a && b) || (a && c).
Proof.
  intros.
  oltauto.
Qed.

Example oltauto_cert1 : forall a b c: bool,  (a && a) = (a && a && a) .
Proof.
  intros.
  oltauto_cert.
Qed.


Example oltauto_cert2 : forall a b c: bool,  (a && (b || c) || (a && b) || (a && c)) = a && (b || c) && (a && b) || (a && c).
Proof.
  intros. 
  oltauto_cert.
Qed.














