Declare ML Module "coq_ol:coq-ol.plugin".

Require Import OL_Theory.
Require Import OL_Reflection_5_pointers.
Require Import OL_Reflection_1_base.
Require Import Bool.
Require Import Btauto.
Open Scope bool_scope.

(*

      let left_true_or = Lazy.force left_true_or in
      let right_true_or = Lazy.force right_true_or in
      let left_neg_or = Lazy.force left_neg_or in
      let right_neg_or = Lazy.force right_neg_or in
      let left_and_or = Lazy.force left_and_or in
      let right_and_or = Lazy.force right_and_or in
      let left_or_or_1 = Lazy.force left_or_or_1 in
      let left_or_or_2 = Lazy.force left_or_or_2 in
      let right_or_or_1 = Lazy.force right_or_or_1 in
      let right_or_or_2 = Lazy.force right_or_or_2 in
      
*)

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


  (* nnf *)
Lemma xorb_decompose a b : xorb a b = andb (orb a b) (orb (negb a) (negb b)).
Proof.
  destruct a, b; auto.
Qed.

Lemma eqb_decompose a b : eqb a b = orb (andb a b) (andb (negb a) (negb b)).
Proof.
  destruct a, b; auto.
Qed.


Hint Rewrite negb_orb negb_andb negb_involutive negb_true_iff 
             negb_false_iff xorb_decompose eqb_decompose 
            : nnf_lemmas.

Ltac nnf := repeat (autorewrite with nnf_lemmas;
  try simpl negb
).


  (* olcert *)
Ltac olcert_goal_tpair := lazymatch goal with
  | [ |- tpair ?a ?b ] => let hh := fresh "hh" in olcert (tpair a b) hh
  | _ => fail "olcert_goal_tpair: Goal is not a tpair"

end.


Ltac olcert_goal := nnf; lazymatch goal with
  | [ |- tpair ?a ?b ] => nnf; olcert_goal_tpair
  | [ |- ?a = ?b ] => apply tpair_to_eq; nnf; olcert_goal_tpair
  | [ |- ?a <= ?b ] => apply tpair_to_leq; nnf; olcert_goal_tpair
  | _ => fail "olcert_goal: Goal not supported"
end.














Example test1 : tpair true true.
Proof.
  olcert_goal. auto.
Qed.

Example test2 a : tpair true a.
Proof.
  olcert_goal. auto.
Qed.

Example test3 a : tpair a true.
Proof.
  olcert_goal. auto.
Qed.

Example test4 a b: tpair true (a || b).
Proof.
  olcert_goal. auto.
Qed.

Example test5 a b: tpair (a && b) true.
Proof.
  olcert_goal. auto.
Qed.

Example test6 a : tpair (negb a) a.
Proof.
  olcert_goal. auto.
Qed.

Example test7 a : tpair a (negb a).
Proof.
  olcert_goal. auto.
Qed.

Example test8 a: tpair (a && a ) (negb a).
Proof.
  olcert_goal. auto.
Qed.

Example test9 a: tpair a ((negb a) && (negb a)).
Proof.
  olcert_goal. auto.
Qed.

Example test10 a b: tpair (a || b) (negb a).
Proof.
  olcert_goal. auto.
Qed.

Example test11 a b: tpair (a || b) (negb b).
Proof.
  olcert_goal. auto.
Qed.

Example test12 a b: tpair a ((negb a) || b).
Proof.
  olcert_goal. auto.
Qed.

Example test13 a b: tpair a (b || (negb a)).
Proof.
  olcert_goal. auto.
Qed.

Example test14 a b c: tpair (a || negb a) (b || c).
Proof.
  olcert_goal. auto.
Qed.


(* olnormalize *)


Ltac ol_norm e := let e' := fresh "e" with Hol := fresh "Hol" in
  olget e e'; assert (e = e') as Hol by (subst e'; (solveOLPointers BoolOL)); subst e'; try rewrite Hol; clear Hol.

Ltac ol_norm_cert e := let e' := fresh "e" with Hol := fresh "Hol" in
  olget e e'; assert (e = e') as Hol by (subst e'; olcert_goal; auto); subst e'; try rewrite Hol.

Ltac ol_norm2 e := match e with 
  | _ => 
    lazymatch type of e with
      | bool => ol_norm e
      | _ => fail
    end
  | ?f ?arg => ol_norm2 f; ol_norm2 arg
  | _ => idtac
end.

Ltac ol_norm2_cert e := match e with 
  | _ => 
    lazymatch type of e with
      | bool => ol_norm_cert e
      | _ => fail
    end
  | ?f ?arg => ol_norm2_cert f; ol_norm2_cert arg
  | _ => idtac
end.

Ltac ol_norm3 := (lazymatch goal with
  | [ |- ?e ] => ol_norm2 e
end).

Ltac ol_norm3_cert := (lazymatch goal with
  | [ |- ?e ] => ol_norm2_cert e
end).

Tactic Notation "olnormalize" constr(e) := ol_norm2 e.
Tactic Notation "olnormalize" := ol_norm3.

Tactic Notation "olnormalize_cert" constr(e) := ol_norm2_cert e.
Tactic Notation "olnormalize_cert" := ol_norm3_cert.


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
  repeat (olnormalize; lazymatch goal with
  | [ |- ?e1 = ?e1 ] => reflexivity
  | [ |- ?e1 <= ?e1 ] => apply P1
  | [ |- ?e ] => destr_subbool_goal
  end).

Ltac oltauto_cert :=
  repeat (olnormalize_cert; lazymatch goal with
  | [ |- ?e1 = ?e1 ] => reflexivity
  | [ |- ?e1 <= ?e1 ] => apply P1
  | [ |- ?e ] => destr_subbool_goal
  end).


  (* tests *)
Example test15 : forall a b c: bool,  (a && (b || c) || (a && b) || (a && c)) = a && (b || c) && (a && b) || (a && c).
Proof.
  intros.
  oltauto.
Qed.

Example test16 : forall a b c: bool,  (a && (b || c) || (a && b) || (a && c)) = a && (b || c) && (a && b) || (a && c).
Proof.
  intros.
  - oltauto_cert.
Qed.

Example test17 : forall a b c: bool,  (a && (negb a)) <= (c || (b && negb b)).
Proof.
  intros.
  olnormalize (a && (negb a)).
  olnormalize.
  solveOLPointers BoolOL.
Qed.




















