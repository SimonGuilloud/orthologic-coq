
Require Import NArith.
Require Import OL_Theory.

Require Import OL_Reflection_1_base.

Require Import Setoid Morphisms.
Require Import Lia.
Require Import Coq.Arith.Bool_nat.
Require Import Coq.Arith.PeanoNat.
Require Import Btauto.


Open Scope bool_scope.
Import List.
Import ListNotations.
  (* Decision Algorithm for OL *)



  Fixpoint decideOL_opti (fuel: nat) (g d: AnTerm) : bool :=
  match fuel with
  | 0 => false
  | S n =>
    match (g, d) with
    | (L (Var a), R (Var b) )  => (Pos.eqb a b) (* Hyp *)
    | (R (Var a), L (Var b)) => (Pos.eqb a b) (* Hyp *)
    | (L (Var a), L (Var b))  => false
    | (R (Var a), R (Var b)) => false
    | (L (Var a), N) => false
    | (R (Var a), N) => false
    | (N, L (Var a)) => false
    | (N, R (Var a)) => false
    | (L (Join a b), _) => decideOL_opti n (L a) d && decideOL_opti n (L b) d
    | (_, L (Join a b)) => decideOL_opti n g (L a) && decideOL_opti n g (L b)
    | (R (Meet a b), _) => decideOL_opti n (R a) d && decideOL_opti n (R b) d
    | (_, R (Meet a b)) => decideOL_opti n g (R a) && decideOL_opti n g (R b)
    | (L (Not a), _) => decideOL_opti n (R a) d
    | (_, L (Not a)) => decideOL_opti n g (R a)
    | (R (Not a), _) => decideOL_opti n (L a) d
    | (_, R (Not a)) => decideOL_opti n g (L a)
    | _ => (
      match g with 
      | L (Meet a b) => decideOL_opti n (L a) d 
      | _ => false
      end || (
      match g with 
      | L (Meet a b) => decideOL_opti n (L b) d
      | _ => false
      end || (
      match d with 
      | L (Meet a b) => decideOL_opti n g (L a) 
      | _ => false
      end || (
      match d with 
      | L (Meet a b) => decideOL_opti n g (L b) 
      | _ => false
      end || (
      match g with
      | R (Join a b) => decideOL_opti n (R a) d
      | _ => false
      end || (
      match g with
      | R (Join a b) => decideOL_opti n (R b) d
      | _ => false
      end || (
      match d with
      | R (Join a b) => decideOL_opti n g (R a)
      | _ => false
      end || (
      match d with
      | R (Join a b) => decideOL_opti n g (R b)
      | _ => false
      end || (
      match d with 
      | N => decideOL_opti n g g 
      | _ => false
      end || (
      match g with 
      | N => decideOL_opti n d d
      | _ => false
      end )))))))))) ||
      decideOL_opti n g N || 
      decideOL_opti n N d
    end
  end.

Ltac recurse := simpl in *; lia.

Hint Constructors OLProof squash : olproof.
Hint Resolve full_hyp : olproof.


Lemma rewrite_false_eq_true_left c : c -> false = true \/ c.
Proof. 
  firstorder.
Qed.

Lemma rewrite_false_eq_true_right c : c -> c \/ false = true.
Proof. 
  firstorder.
Qed.


Hint Rewrite
  Bool.orb_false_r
  Bool.andb_true_iff Bool.orb_true_iff
  rewrite_false_eq_true_left rewrite_false_eq_true_right
  Pos.eqb_eq Nat.eqb_eq : rw_bool.


Theorem decideOL_opti_correct : forall n g d, (decideOL_opti n g d) = true -> squash (OLProof (g, d)).
Proof.
  induction n; intros; simpl in *;
    repeat match goal with
           | _ => congruence
           | [ H: _ /\ _ |- _ ] => destruct H
           | [ H: _ \/ _ |- _ ] => destruct H
           | [ H: context[match ?x with _ => _ end] |- _ ] => destruct x; simpl in H
           | [ H: _ = _, IH: forall _ _, _ = _ -> squash _ |- _ ] => apply IHn in H; inversion_clear H
           | _ => autorewrite with rw_bool in *; subst
           end.
  all: clear IHn; eauto 6 with olproof.
Qed.

Lemma decideOL_opti_monotonic : forall (n2 n1: nat) g d, n2 >= n1 -> decideOL_opti n1 g d = true -> decideOL_opti n2 g d = true.
  induction n2.
  - intros. simpl in *. assert (n1 = 0). lia. subst. simpl in *. congruence.
  - intros. destruct n1. simpl in *; congruence. destruct g as [ | t | t ]; try destruct t.
    all: try destruct d as [ | t0 | t0 ]; try destruct t0; simpl; simpl in H0.
      all: repeat rewrite Bool.orb_false_r in *; repeat rewrite Bool.orb_true_iff in *; repeat rewrite Bool.andb_true_iff in *; auto.
      all: repeat match goal with
      | [H: _ \/ _ |- _] => destruct H; only 1: left; only 2: right
      | [H: _ /\ _ |- _] => destruct H; split
      | _ => idtac
      end. all: try apply (IHn2 n1); try lia; auto.
Qed.


Definition decideOL_opti_simp (g d: AnTerm): bool := decideOL_opti (anterm_size g + anterm_size d) g d.

  (* Reflection: solve goals using the algorithm in arbitrary Ortholattice *)


Theorem decideOL_opti_simp_correct : forall g d, (decideOL_opti_simp g d) = true -> anTerm_leq g d.
Proof.
  intros. assert (squash (OLProof (g, d))). apply decideOL_opti_correct in H; auto; lia.
  destruct H0. apply (soundness (g, d)). auto.
Qed.


Theorem reduce_to_decideOL_opti {OL: Ortholattice} : forall t1 t2 f, (decideOL_opti_simp (L t1) (R t2)) = true -> ((eval t1 f) <= (eval t2 f)).
Proof.
  intros. assert (anTerm_leq  (L t1) (R t2)). all: auto using decideOL_opti_simp_correct.
Qed.


Ltac solve_OL_opti OL := 
  reify_goal OL; apply reduce_to_decideOL_opti; auto; vm_compute; (try reflexivity).

(* Small tests *)


Example test1 {OL: Ortholattice} : forall a,  a <= a.
Proof.
  intro. 
  solve_OL_opti OL.
Qed.

Example test2 {OL: Ortholattice} : forall a,  a == (a ∩ a).
Proof.
  intro. 
  solve_OL_opti OL.
Qed.

(*
Example test3 {OL: Ortholattice} a b c: 
  ¬(b ∪ ¬(c ∩ ¬b) ∪ a) <= (¬a ∪ ¬(b ∩ ¬a)).
Proof.
  solve_OL_opti OL.
Qed.
*)


Example test4 : forall a: (@A BoolOL),  a <= (a || a).
Proof.
  intro.
  solve_OL_opti BoolOL.
Qed.


Example test5 : forall a: (@A BoolOL), Bool.le a (andb a a).
Proof.
  intro. 
  solve_OL_opti BoolOL.
Qed.


Example test6 : forall a b : bool,   ( a ∩ (neg a)) <= b.
Proof.
  intros.
  solve_OL_opti BoolOL.
Qed.


Example test7 : forall a b : bool,  Bool.le (andb a (negb a)) b.
Proof.
  intros. 
  solve_OL_opti BoolOL.
Qed.


Example test8 : forall a b c: bool,  (a ∩ (negb a)) <= (a || (b && c)).
Proof.
  intros. 
  solve_OL_opti BoolOL.
Qed.



Example test9 {OL: Ortholattice} a b c: 
  c <= ((a ∩ b) ∪ (¬a) ∪ (¬b)).
Proof.
  solve_OL_opti OL.
Qed.

