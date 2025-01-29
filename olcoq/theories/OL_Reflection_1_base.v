
Require Import NArith.
Require Import OL_Theory.

Require Import Setoid Morphisms.
Require Import Lia.
Require Import Coq.Arith.Bool_nat.
Require Import Coq.Arith.PeanoNat.
Require Import Btauto.


Open Scope bool_scope.
Import List.
Import ListNotations.
  (* Decision Algorithm for OL *)


Fixpoint decideOL_base (fuel: nat) (g d: AnTerm) : bool :=
  match fuel with
  | 0 => false
  | S n =>
    match (g, d) with 
    | (L (Var a), R (Var b) )  => (Pos.eqb a b) (* Hyp *)
    | _ => false
    end || (
    decideOL_base n g N || (
    match d with 
    | N => decideOL_base n g g 
    | _ => false
    end || (
    match g with 
    | L (Meet a b) => decideOL_base n (L a) d
    | _ => false
    end || (
    match g with
    | L (Meet a b) => decideOL_base n (L b) d
    | _ => false
    end || (
    match g with 
    | L (Join a b) => decideOL_base n (L a) d && decideOL_base n (L b) d
    | _ => false
    end || (
    match g with 
    | L (Not a) => decideOL_base n (R a) d
    | _ => false
    end || (
    match d with 
    | R (Meet a b) => decideOL_base n g (R a) && decideOL_base n g (R b)
    | _ => false
    end || (
    match d with
    | R (Join a b) => decideOL_base n g (R a)
    | _ => false
    end || (
    match d with
    | R (Join a b) => decideOL_base n g (R b)
    | _ => false
    end || (
    match d with
    | R (Not a) => decideOL_base n g (L a)
    | _ => false
    end || (
    decideOL_base n d g
    )))))))))))
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


Theorem decideOL_base_correct : forall n g d, (decideOL_base n g d) = true -> squash (OLProof (g, d)).
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
  all: clear IHn; eauto 7 with olproof.
Qed.

Lemma decideOL_base_monotonic : forall (n2 n1: nat) g d, n2 >= n1 -> decideOL_base n1 g d = true -> decideOL_base n2 g d = true.
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

Theorem decideOL_base_complete: 
  forall n g d, 
  forall p: (OLProof (g, d)),
  is_cut_free p ->
  n >= proof_size p ->
  exists n0, (decideOL_base n0 g d) = true.
Proof. 
  induction n; intros; simpl in *.
  - destruct p; simpl in *; lia.
  - generalize H; generalize H0; dependent inversion p; intro Hfuel; intro Hcut; simpl in Hcut; try destruct Hcut.
    all: repeat match goal with
    | [o: (OLProof (?og, ?od)), o0: (OLProof (?o0g, ?o0d)),  Hfuel: context[proof_size(?constr ?o ?o0)] |- _ ] => 
      simpl in Hfuel;
      pose proof (IHn og od o) as IHo; pose proof (IHn o0g o0d o0) as IHo0; 
      destruct IHo as [n1 IHo]; destruct IHo0 as [n2 IHo0]; auto; try lia;
      apply (decideOL_base_monotonic (max n1 n2)) in IHo; apply (decideOL_base_monotonic (max n1 n2)) in IHo0; auto; try lia;
      exists (S (max n1 n2)); simpl
    | [o: (OLProof (?og, ?od)), Hfuel: context[proof_size(?constr ?o)] |- _ ] => 
      simpl in Hfuel;
      pose proof (IHn og od o) as IHo;
      destruct IHo as [n1 IHo]; auto; try lia;
      exists (S n1); simpl
    | [ |- exists _, _] => exists 1; simpl in *; auto
    | _ => autorewrite with rw_bool in *; subst
    end.
    all: repeat match goal with 
      | [ |- context[match ?x with _ => _ end] ] => destruct x; simpl in *
      | _ => autorewrite with rw_bool in *; repeat apply rewrite_false_eq_true_left
    end. all: try rewrite IHo; try rewrite IHo0; auto.
    all: try (repeat (auto; try (left; reflexivity); right); fail).
Qed.


Definition anterm_size (t: AnTerm) : nat := match t with
  | L t1 => 1 + term_size t1
  | R t1 => 1 + term_size t1
  | N => 1
end.


Theorem anterm_size_positive : forall t, anterm_size t >= 1. Proof. intros. destruct t; simpl; lia. Qed.


Definition decideOL_base_simp (g d: AnTerm): bool := decideOL_base (anterm_size g + anterm_size d) g d.

  (* Reflection: solve goals using the algorithm in arbitrary Ortholattice *)


Theorem decideOL_base_simp_correct : forall g d, (decideOL_base_simp g d) = true -> anTerm_leq g d.
Proof.
  intros. assert (squash (OLProof (g, d))). apply decideOL_base_correct in H; auto; lia.
  destruct H0. apply (soundness (g, d)). auto.
Qed.


Theorem reduce_to_decideOL {OL: Ortholattice} : forall t1 t2 f, (decideOL_base_simp (L t1) (R t2)) = true -> ((eval t1 f) <= (eval t2 f)).
Proof.
  intros. assert (anTerm_leq  (L t1) (R t2)). all: auto using decideOL_base_simp_correct.
Qed.


Ltac contains x l :=
  match l with
  | x :: _ => true
  | _ ::  ?tail => contains x ?tail
  | _ => false
  end.

Ltac add_if_not_exists x l :=
  
  let cont := contains x l in 
  match cont with
  | true => l
  | false => constr:(x :: l)
  end.

Ltac index_of x l :=
  match l with
  | x :: ?tail => xH
  | _ :: ?tail => let r := (index_of x tail) in constr:(Pos.succ r)
  | _ => fail "element not found. x:" x "l:" l
  end.

(* Ugly way to check if two terms are convertible, but that's all internet gave me *)
Ltac convertible x y := constr:(eq_refl x : x = y).

(* Puts all leaves of the expression (i.e. which are neither meets, joins nor neg) into a list. *)
Ltac leaves OL l exp := 
  match exp with
  | (?op ?X1 ?X2) => let __ := convertible op (@meet OL) in let l1 := leaves OL l X1 in
                 let l2 := leaves OL l1 X2 in
                 constr:(l2)
  | (?op ?X1 ?X2) => let __ := convertible op (@join OL) in let l1 := leaves OL l X1 in
                 let l2 := leaves OL l1 X2 in
                 constr:(l2)
  | (?op ?X1) => let __ := convertible op (@neg OL) in leaves OL l X1
  | ?X1 => add_if_not_exists X1 l
  end.


Ltac reify_term OL t env := match t with
  | (?op ?X1 ?X2) => let __ := convertible op (@meet OL) in let r1 := reify_term OL X1 env
                    with r2 := reify_term OL X2 env in 
                    constr:(Meet r1 r2)
  | (?op ?X1 ?X2) => let __ := convertible op (@join OL)  in let r1 := reify_term OL X1 env
                    with r2 := reify_term OL X2 env in
                    constr:(Join r1 r2)
  | (?op ?X1) => let __ := convertible op (@neg OL)  in let r1 := reify_term OL X1 env in
                    constr:(Not r1)
  | ?X1 => let j := index_of X1 env in constr:(Var j)
end.

(* get the head of a list, if there is one (and there always is). Used in nth, to transform the list into a function nat -> A.*)
Ltac head_tac l := match l with
  | ?h :: _ => h
  | _ => fail "Empty list"
  end.


Ltac reify_leq OL S T := 
  let AA := (eval simpl in (@A OL)) with
      m := (eval simpl in (@meet OL)) with
      j := (eval simpl in (@join OL)) with
      n := (eval simpl in (@neg OL)) with
      f := (eval simpl in (@zero OL)) with
      t := (eval simpl in (@one OL)) in
  let l1 := leaves OL (@nil AA) S in
  let l2 := leaves OL l1 T in
  let t1' := (reify_term OL S l2) with
      t2' := (reify_term OL T l2) in
  let env := constr:(fun k:positive => nth (pred (Pos.to_nat k)) l2 (@e OL) ) in
      change ((@eval OL t1' env) <= (@eval OL t2' env));try unfold Zero; try unfold One.



Ltac bool_unfold := 
  replace false with (@zero BoolOL) by reflexivity; replace true with (@one BoolOL) by reflexivity.

  
Ltac reify_goal OL := bool_unfold; try rewrite false_eq; try rewrite true_eq;
  match goal with
  | [ |- ?f ?S ?T ] =>  
        change ((@OL_Theory.equiv OL) S T)
  | [ |- ?f ?S ?T ] =>  
        change ((@OL_Theory.leq OL) S T)
  | _ => fail "No detected ortholattice equivalence or order relation in goal"
  end;
  lazymatch goal with
  | [ |- (@OL_Theory.equiv OL) ?S ?T ] =>  
        rewrite equiv_leq; split; only 1: reify_leq OL S T; only 2: reify_leq OL T S
  | [ |- (@OL_Theory.leq OL) ?S ?T ] =>  
         reify_leq OL S T
  | _ => fail "Should not happen"
  end.


Ltac solve_OL OL := 
  reify_goal OL; apply reduce_to_decideOL; vm_compute; (try exact eq_refl).


(* Small tests *)


Example test1 {OL: Ortholattice} : forall a,  a <= a.
Proof.
  intro. 
  solve_OL OL.
Qed.

Example test2 {OL: Ortholattice} : forall a,  a == (a ∩ a).
Proof.
  intro. 
  solve_OL OL.
Qed.

(*
Example test3 {OL: Ortholattice} a b c: 
  ¬(b ∪ ¬(c ∩ ¬b) ∪ a) <= (¬a ∪ ¬(b ∩ ¬a)).
Proof.
  solve_OL OL.
Qed.
*)


Example test4 : forall a: (@A BoolOL),  a <= (a || a).
Proof.
  intro.
  solve_OL BoolOL.
Qed.


Example test5 : forall a: (@A BoolOL), Bool.le a (andb a a).
Proof.
  intro. 
  solve_OL BoolOL.
Qed.


Example test6 : forall a b : bool,   ( a ∩ (neg a)) <= b.
Proof.
  intros.
  solve_OL BoolOL.
Qed.


Example test7 : forall a b : bool,  Bool.le (andb a (negb a)) b.
Proof.
  intros. 
  solve_OL BoolOL.
Qed.


Example test8 : forall a b c: bool,  (a ∩ (negb a)) <= (a || (b && c)).
Proof.
  intros. 
  solve_OL BoolOL.
Qed.


Example test9 {OL: Ortholattice} a b c: 
  c <= ((a ∩ b) ∪ (¬a) ∪ (¬b)).
Proof.
  solve_OL OL.
Qed.

