Require Import Setoid Morphisms.
Require Import Lia.
Require Import Coq.Arith.Bool_nat.
Require Import Coq.Arith.PeanoNat.
Require Import Btauto.
Ltac Tauto.intuition_solver ::= auto.


Open Scope bool_scope.

Generalizable All Variables.


Reserved Infix "==" (at level 145, left associativity).
Reserved Infix "∪" (at level 40, left associativity).
Reserved Infix "∩" (at level 40, left associativity).
Reserved Notation "¬ x" (at level 20).

  (* Ortholattices *)

Class Ortholattice := {

  A : Set;
  e : A;

  leq : relation A where "x <= y" := (leq x y);
  meet : A -> A -> A where "x ∩ y" := (meet x y);
  join : A -> A -> A where "x ∪ y" := (join x y);
  neg : A -> A where "¬ x" := (neg x);
  zero : A;
  one : A;

  equiv: relation A where "x == y" := (equiv x y);
  equiv_leq : forall x y, (x == y) <-> ( (x <= y) /\ (y <= x));
  zero_leq : forall x, (leq zero x);
  one_leq : forall x, (leq x one);

  P1 : forall x, x <= x;
  P2 : forall x y z, x <= y -> y <= z -> x <= z;
  P4 : forall x y, (x ∩ y) <= x;
  P5 : forall x y, (x ∩ y) <= y;
  P6 : forall x y z, (x <= y) -> (x <= z) -> x <= (y ∩ z);
  P7 : forall x, x <= (¬ (¬ x));
  P8 : forall x y, x <= y -> (¬ y) <= (¬ x);
  P9 : forall x y, (x ∩ (¬ x)) <= y;

  P4' : forall x y, x <= (x ∪ y);
  P5' : forall x y, y <= (x ∪ y);
  P6' : forall x y z, (x <= z) -> (y <= z) -> (x ∪ y) <= z;
  P7' : forall x, (¬ (¬ x)) <= x;
  P9' : forall x y, x <= ( y ∪ (¬ y));
}.

Infix "∩" := meet.
Infix "∪" := join.
Notation "¬ x" := (neg x) (at level 20).
Infix "<=" := leq.
Infix "==" := equiv.

Hint Resolve equiv_leq zero_leq one_leq P1 P2 P4 P5 P6 P7 P8 P9 P4' P5' P6' P7' P9' : ol.

(* Some useful lemmas needed for Withman's algorithm*)
Lemma swap_equiv {OL: Ortholattice} x y: (x == y) -> y == x. Proof. intro. rewrite equiv_leq in *. exact (conj (proj2 H) (proj1 H)).  Qed.
Lemma glb1 {OL: Ortholattice} x y z: y <= x -> y ∩ z <= x. Proof. intros. apply P2 with y. apply P4. auto. Qed.
Lemma glb2 {OL: Ortholattice} x y z: z <= x -> y ∩ z <= x. Proof. intros. apply P2 with z. apply P5. auto. Qed.
Lemma lub1 {OL: Ortholattice} x y z: x <= y -> x <= y ∪ z. Proof. intros. apply P2 with y. auto. apply P4'. Qed.
Lemma lub2 {OL: Ortholattice} x y z: x <= z -> x <= y ∪ z. Proof. intros. apply P2 with z. auto. apply P5'. Qed.


(*
  This tactic simulates Withman's algorithm, which is a complete decision procedure for lattices. 
  The decision procedure for ortholattice is in some sense an extension, but much more complicated.
*)
Ltac withman := match goal with
  | [ |- _ == _] => rewrite equiv_leq; split; withman
  | [ |- zero <= _] => apply zero_leq
  | [ |- _ <= one] => apply one_leq
  | [ |- ?x <= ?x] => apply P1
  | [ |- _ <= _ ∩ _] => apply P6; withman
  | [ |- _ ∪ _ <= _] => apply P6'; withman
  | [ |- _ ∩ _ <= _] => 
    try (apply glb1; withman; eauto; fail);
    try (apply glb2; withman; eauto; fail)
  | [ |- _ <= _ ∪ _] => 
    try (apply lub1; withman; eauto; fail);
    try (apply lub2; withman; eauto; fail)
  | [ |- ¬ _ <= ¬ _] => apply P8; withman (* This is an extension to the base algorithm. It's not complete for ortholattices but it's still useful. *)
  | [ |- _ <= _] => try (eauto;fail)
end.
Lemma example {OL: Ortholattice} a b : (a ∩ b) <= (a ∪ b).
Proof. withman. Qed.

Instance equivalence_eq {OL: Ortholattice}: Equivalence equiv.
  constructor.
  - intro. withman.
  - unfold Symmetric; intros. rewrite equiv_leq in *. intuition.
  - unfold Transitive; intros. rewrite equiv_leq in *. intuition; apply P2 with y; auto.
Qed.


  (* Showing that == is a congruence relation for ∩, ∪, ¬ and <=. Allows using setoid rewrites. *)


Ltac destruct_equiv := match goal with
  | [H: (equiv ?x ?y) |- _] => destruct H
end.

Instance proper_meet {OL: Ortholattice}: Proper (equiv ==> equiv ==> equiv) meet. 
  unfold Proper. unfold respectful. intros. rewrite equiv_leq in *. intuition; withman.
Qed.


Instance proper_join {OL: Ortholattice}: Proper (equiv ==> equiv ==> equiv) join.
  unfold Proper. unfold respectful. intros. rewrite equiv_leq in *. intuition; withman.
Qed.

Instance proper_neg {OL: Ortholattice}: Proper (equiv ==> equiv) neg.
  unfold Proper. unfold respectful. intros. rewrite equiv_leq in *. intuition; withman.
Qed.

Instance proper_leq {OL: Ortholattice}: Proper (equiv ==> equiv ==> iff) leq. split; rewrite equiv_leq in *; intuition.
  - apply P2 with x; withman. apply P2 with x0; withman.
  - apply P2 with y; withman. apply P2 with y0; withman.
Qed.


  (* Alternative axiomtization in terms of == *)

Lemma V1 {OL: Ortholattice} x y : x ∪ y == y ∪ x. Proof. withman. Qed.
Lemma V2 {OL: Ortholattice} x y z : (x ∪ y) ∪ z == x ∪ (y ∪ z). Proof. withman. Qed.
Lemma V3 {OL: Ortholattice} x : x ∪ x == x. Proof. withman. Qed.
Lemma V6 {OL: Ortholattice} x : ¬ (¬ x) == x. Proof. withman. apply P7'. apply P7. Qed.
Lemma V8 {OL: Ortholattice} x y : ¬ (x ∪ y) == (¬ x) ∩ (¬ y). Proof.
  withman. rewrite <- V6 at 1. withman.
  - rewrite <- V6 at 1. withman.
  - rewrite <- V6 at 1. withman.
Qed.
Lemma V9 {OL: Ortholattice} x y : x ∪ (x ∩ y) == x. Proof. withman. Qed.


Lemma V1' {OL: Ortholattice} x y : x ∩ y == y ∩ x. Proof. withman. Qed.
Lemma V2' {OL: Ortholattice} x y z : (x ∩ y) ∩ z == x ∩ (y ∩ z). Proof. withman. Qed.
Lemma V3' {OL: Ortholattice} x : x ∩ x == x. Proof. withman. Qed.
Lemma V8' {OL: Ortholattice} x y : ¬ (x ∩ y) == (¬ x) ∪ (¬ y). Proof.
  withman. rewrite <- (V6 (¬ x ∪ ¬ y)). withman.
  - rewrite <- (V6 x) at 2. withman.
  - rewrite <- (V6 y) at 2. withman.
Qed.
Lemma V9' {OL: Ortholattice} x y : x ∩ (x ∪ y) == x. Proof. withman. Qed.

Lemma false_eq {OL: Ortholattice} : zero == e ∩ (¬ e). Proof. withman. apply P9. Qed.
Lemma true_eq {OL: Ortholattice} : one == e ∪ (¬ e). Proof. withman. apply P9'. Qed.

  (* Term Algebra *)

Require Import NArith.

Inductive Term : Set :=
  | Var : positive -> Term
  | Meet : Term -> Term -> Term
  | Join : Term -> Term -> Term
  | Not : Term -> Term.


Definition Zero := Meet (Var xH) (Not (Var xH)).
Definition One := Join (Var xH) (Not (Var xH)).


  (* Evaluation of a term in an arbitrary ortholattice *)

Fixpoint eval {OL: Ortholattice} (t: Term) (f: positive -> A) : A :=
  match t with
  | Var n => f n
  | Meet t1 t2 => (eval t1 f) ∩ (eval t2 f)
  | Join t1 t2 => (eval t1 f) ∪ (eval t2 f)
  | Not t1 => ¬ (eval t1 f)
  end.


Definition term_leq (t1 t2: Term) : Prop := forall (OL: Ortholattice), 
  forall f: positive -> A, eval t1 f <= eval t2 f.

Declare Instance proper_eval {OL: Ortholattice}: Proper (eq ==> eq ==> eq) eval.


  (* Proof System *)

Inductive AnTerm: Set :=
  | N : AnTerm (* Empty formula *)
  | L : Term -> AnTerm  (* Formula left of a sequent*)
  | R : Term -> AnTerm. (* Formula right of a sequent*)


Definition Sequent (l r : AnTerm) := (l, r).

Inductive OLProof : AnTerm*AnTerm -> Set := 
  | Hyp : forall {p}, OLProof (L (Var p), R (Var p))
  | Weaken : forall {gamma} {delta}, OLProof (gamma, N) -> OLProof (gamma, delta)
  | Contract : forall {gamma}, OLProof (gamma, gamma) -> OLProof (gamma, N)
  | LeftAnd1 : forall {a} {b} {delta}, OLProof (L a, delta) -> OLProof (L (Meet a b), delta)
  | LeftAnd2 : forall {a} {b} {delta}, OLProof (L b, delta) -> OLProof (L (Meet a b), delta)
  | LeftOr : forall {a} {b} {delta}, OLProof (L a, delta) -> OLProof (L b, delta) -> OLProof (L (Join a b), delta)
  | LeftNot : forall {a} {delta}, OLProof (R a, delta) -> OLProof (L (Not a), delta)
  | RightAnd : forall {a} {b} {gamma}, OLProof (gamma, R a) -> OLProof (gamma, R b) -> OLProof (gamma, R (Meet a b))
  | RightOr1 : forall {a} {b} {gamma}, OLProof (gamma, R a) -> OLProof (gamma, R (Join a b))
  | RightOr2 : forall {a} {b} {gamma}, OLProof (gamma, R b) -> OLProof (gamma, R (Join a b))
  | RightNot : forall {a} {gamma}, OLProof (gamma, L a) -> OLProof (gamma, R (Not a))
  | Swap : forall {gamma} {delta}, OLProof (gamma, delta) -> OLProof (delta, gamma)
  | Cut : forall {gamma} {b} {delta}, OLProof (gamma, R b) -> OLProof (L b, delta) -> OLProof (gamma, delta).


(* Semantic truth of a sequent *)

Definition interp t: Term := match t with
  | L a => a
  | R a => Not a
  | N => One
end.


Definition not_interp t: Term := match t with
  | L a => Not a
  | R a => a
  | N => Zero
end.


Definition anTerm_leq (l r : AnTerm): Prop := 
  term_leq (interp l) (not_interp r).

Notation "⊢ a b" := (anTerm_leq a b _) (at level 90).

  (* In particular, ⊢ (L a) (R b)   <->   leq a b  *)


  (* Some useful lemmas *)

Lemma zero_min {OL: Ortholattice} : forall f t, eval Zero f <= eval t f.
Proof.
  intros.
  unfold Zero.
  unfold eval.
  apply P9.
Qed.


Lemma one_max {OL: Ortholattice} : forall f t, eval t f <= eval One f.
Proof.
  intros.
  unfold One.
  unfold eval.
  apply P9'.
Qed.


Lemma zero_eq {OL: Ortholattice} : forall f t, eval Zero f == eval (Meet t (Not t)) f.
Proof.
  intros.
  unfold Zero.
  rewrite equiv_leq; split; apply P9.
Qed.


Lemma one_eq {OL: Ortholattice} : forall f t, eval One f == eval (Join t (Not t)) f.
Proof.
  intros.
  unfold One.
  rewrite equiv_leq; split; apply P9'.
Qed.


Lemma contract_soundness {OL: Ortholattice} : forall f t, eval t f <= eval (Not t) f -> eval t f == eval Zero f.
Proof.
  intros.
  rewrite  (zero_eq f t). rewrite equiv_leq; split; simpl.
  - apply P6.
    + apply P1.
    + auto.
  - apply P4.
Qed.


Theorem swap_interp {OL: Ortholattice} a f: eval (not_interp a) f == ¬ eval (interp a) f.
Proof.
  destruct a; simpl.
  - withman. apply P9. rewrite V8. apply P9.
  - reflexivity.
  - apply swap_equiv. apply V6.
Qed.





(* soundness *)

Theorem soundness s (p: OLProof s) : anTerm_leq (fst s) (snd s).
Proof.
  intros.
  induction p.
  - unfold anTerm_leq, term_leq, interp, not_interp.
    intros.
    simpl.
    apply P1.
  - unfold anTerm_leq, term_leq, interp, not_interp in *; simpl in *.
    intros.
    apply P2 with (eval Zero f). apply IHp. apply zero_min.
  - unfold anTerm_leq, term_leq, interp, not_interp in *; simpl in *.
    intros.
    destruct gamma. auto. 
      + assert (eval t f == eval Zero f).
        apply contract_soundness. auto.
        rewrite H. apply P1.
      + assert (eval (Not t) f == eval Zero f).
        apply contract_soundness. unfold eval. rewrite V6. fold eval. apply IHp.
        rewrite H. apply P1.

  - unfold anTerm_leq, term_leq, interp, not_interp in *; simpl in *.
    intros. (* eauto using P2, P4. *)
    apply P2 with (eval a f). apply P4. apply IHp.
  - unfold anTerm_leq, term_leq, interp, not_interp in *; simpl in *.
    intros.
    apply P2 with (eval b f). apply P5. apply IHp.
  - unfold anTerm_leq, term_leq, interp, not_interp in *; simpl in *.
    intros.
    apply P6'.  apply IHp1. apply IHp2.
  - unfold anTerm_leq, term_leq in *; simpl in *.
    intros. specialize (IHp OL f). auto.
  - unfold anTerm_leq, term_leq, interp, not_interp in *; simpl in *.
    intros. 
    apply P6.  apply IHp1. apply IHp2.
  - unfold anTerm_leq, term_leq, interp, not_interp in *; simpl in *.
    intros.
    apply P2 with (eval a f). apply IHp. apply P4'.  
  - unfold anTerm_leq, term_leq, interp, not_interp in *; simpl in *.
    intros.
    apply P2 with (eval b f). apply IHp. apply P5'.
  - unfold anTerm_leq, term_leq, interp, not_interp in *; simpl in *.
    intros. auto.
  - unfold anTerm_leq, term_leq in *; simpl in *.
    intros.
    specialize (IHp OL f).
    rewrite swap_interp. rewrite swap_interp in IHp. rewrite <- V6 at 1. apply P8. exact IHp.
  - unfold anTerm_leq, term_leq, interp, not_interp in *; simpl in *.
    intros.
    apply P2 with (eval b f). apply IHp1. apply IHp2.
  
Qed.

Hint Constructors OLProof : olproof_constr.

Lemma full_hyp s : OLProof (L s, R s).
Proof.
  induction s; eauto 4 with olproof_constr.
Qed.

(* completeness *)

Inductive squash (T:Type) : Prop :=
  | Squash (t: T) : squash T.

Ltac sq := apply Squash.


Definition has_proof (l: Term) (r: Term): Prop := squash (OLProof (L l, R r)).


Lemma proof_exists {l r: Term} (p: OLProof (L l, R r)): has_proof l r.
Proof.
  constructor. exact p.
Qed.


#[refine] Instance TermOL : Ortholattice := {
    A := Term;
    e := Var xH;
    leq := has_proof;
    meet := Meet;
    join := Join;
    neg := Not;
    zero := Zero;
    one := One;
    equiv := fun x y => (has_proof x y) /\ (has_proof y x);
  }.
Proof.
  all: intros.
  - reflexivity.
  - unfold Zero. apply proof_exists. apply Weaken. apply Contract. 
    apply LeftAnd1; apply Swap; apply LeftAnd2. apply LeftNot; apply Swap; apply full_hyp.
  - unfold One. apply proof_exists. apply Swap. apply Weaken. apply Contract.
    apply RightOr1. apply Swap. apply RightOr2. apply RightNot. apply Swap. apply full_hyp.
  - apply proof_exists. apply (full_hyp).
  - destruct H. destruct H0. apply proof_exists. eapply Cut. eauto. intuition.
  - apply proof_exists. apply LeftAnd1. apply full_hyp.
  - apply proof_exists. apply LeftAnd2. apply full_hyp.
  - destruct H. destruct H0. apply proof_exists. apply RightAnd; auto.
  - apply proof_exists. apply RightNot. apply Swap. apply LeftNot. apply Swap. apply full_hyp.
  - destruct H. apply proof_exists. apply LeftNot. apply RightNot. apply Swap. auto.
  - apply proof_exists. apply Weaken. apply Contract. apply LeftAnd1. apply Swap. apply LeftAnd2. apply LeftNot. apply Swap. apply full_hyp.
  - apply proof_exists. apply RightOr1. apply full_hyp.
  - apply proof_exists. apply RightOr2. apply full_hyp.
  - destruct H. destruct H0. apply proof_exists. apply LeftOr; auto.
  - apply proof_exists. apply LeftNot. apply Swap. apply RightNot. apply Swap. apply full_hyp.
  - apply proof_exists. apply Swap. apply Weaken. apply Contract. apply RightOr1. apply Swap. apply RightOr2. apply RightNot. apply Swap. apply full_hyp.
Defined.


Lemma var_eval (t: Term ): @eval TermOL t Var = t.
Proof.
  induction t.
  - auto.
  - simpl. rewrite IHt1. rewrite IHt2. auto.
  - simpl. rewrite IHt1. rewrite IHt2. auto.
  - simpl. rewrite IHt. auto.
Qed.


Theorem completeness l r : term_leq l r -> has_proof l r.
Proof.
  intros. specialize (H TermOL Var).
  destruct H as [p]. repeat rewrite var_eval in p. sq. exact p.
Qed.


  (* Useful lemma using soundness *)


#[refine] Instance BoolOL : Ortholattice := {
  A := bool;
  e := false;
  leq := Bool.le;
  meet := andb;
  join := orb;
  neg := negb;
  equiv := eq;
  zero := false;
  one := true;
}.
Proof.
  all: intros.
  - destruct x, y; simpl; intuition.
  - simpl; auto.
  - destruct x; simpl; auto.
  - destruct x; unfold Bool.le; auto.
  - destruct x, y, z; simpl in *; auto.
  - destruct x, y; simpl in *; auto.
  - destruct x, y; simpl in *; auto.
  - destruct x, y; simpl in *; auto.
  - destruct x; simpl in *; auto.
  - destruct x, y; simpl in *; auto.
  - destruct x, y; simpl in *; auto.
  - destruct x, y; simpl in *; auto.
  - destruct x, y; simpl in *; auto.
  - destruct x, y; simpl in *; auto.
  - destruct x; simpl in *; auto.
  - destruct x, y; simpl in *; auto.
Defined.


Theorem no_proof_NN (P: OLProof (N, N)): False.
Proof.
  pose (@Weaken _ (L One) (Swap (@Weaken _ (R Zero) P))) as P2.
  assert (not (anTerm_leq (R Zero) (L One))).
    - intro. unfold anTerm_leq, leq in *. specialize (H BoolOL).  simpl in *. specialize (H (fun _ => false)). simpl in *. discriminate.
    - apply H. intros. remember (soundness (R Zero, L One) P2) as s. simpl in *. auto.
Qed.


  (* Cut Elimination *)

Fixpoint is_cut_free {s: AnTerm * AnTerm} (p : OLProof s) : Prop := match p with
  | Hyp => True
  | Weaken p => is_cut_free p
  | Contract p => is_cut_free p
  | Swap p => is_cut_free p
  | LeftAnd1 p => is_cut_free p
  | LeftAnd2 p => is_cut_free p
  | LeftOr p1 p2 => is_cut_free p1 /\ is_cut_free p2
  | LeftNot p => is_cut_free p
  | RightAnd p1 p2 => is_cut_free p1 /\ is_cut_free p2
  | RightOr1 p => is_cut_free p
  | RightOr2 p => is_cut_free p
  | RightNot p => is_cut_free p
  | Cut p1 p2 => False
end.


Fixpoint num_cut {s: AnTerm * AnTerm} (p : OLProof s) : nat := match p with
  | Hyp => 0
  | Weaken p => num_cut p
  | Contract p => num_cut p
  | Swap p => num_cut p
  | LeftAnd1 p => num_cut p
  | LeftAnd2 p => num_cut p
  | LeftOr p1 p2 => num_cut p1 + num_cut p2
  | LeftNot p => num_cut p
  | RightAnd p1 p2 => num_cut p1 + num_cut p2
  | RightOr1 p => num_cut p
  | RightOr2 p => num_cut p
  | RightNot p => num_cut p
  | Cut p1 p2 => 1 + num_cut p1 + num_cut p2
end.


Lemma cut_free_eq_zero_cut {s: AnTerm * AnTerm} (p : OLProof s) : is_cut_free p <-> num_cut p = 0.
  induction p. all: simpl. all: intuition.
  - lia.
  - apply H0. lia.
  - apply H2. lia.
  - lia.
  - apply H0. lia.
  - apply H2. lia.
- lia.
Qed.


Fixpoint term_size (t: Term) : nat := match t with
  | Var _ => 1
  | Meet t1 t2 => 1 + term_size t1 + term_size t2
  | Join t1 t2 => 1 + term_size t1 + term_size t2
  | Not t1 => 1 + term_size t1
end.

  (* First measure for induction *)

  (* Starting with size 1 and not 0 is useful because when doing induction we never have to analyze the case where a proof has size 0 *)
Fixpoint proof_size {s: AnTerm * AnTerm} (p : OLProof s) : nat := match p with
  | Hyp => 1 
  | Weaken p => S (S (proof_size p))
  | Contract p => S (S (proof_size p))
  | Swap p => S (proof_size p)
  | LeftAnd1 p => S (S (proof_size p))
  | LeftAnd2 p => S (S (proof_size p))
  | LeftOr p1 p2 => S (S ( (proof_size p1) + (proof_size p2)))
  | LeftNot p => S (S (proof_size p))
  | RightAnd p1 p2 => S (S ( (proof_size p1) + (proof_size p2)))
  | RightOr1 p => S (S (proof_size p))
  | RightOr2 p => S (S (proof_size p))
  | RightNot p => S (S (proof_size p))
  | Cut p1 p2 => S (S ( (proof_size p1) + (proof_size p2)))
end.


  (* Core Theorem *)
Lemma inner_cut_elim : forall
  (fuelB: nat) 
  (b: Term) (good_fuelB: fuelB >= term_size b)
  (fuelSize: nat)
  (gamma: AnTerm) (delta: AnTerm)
  (A: OLProof (gamma, R b)) (p1: is_cut_free A) 
  (B: OLProof (L b, delta)) (p2: is_cut_free B) 
  (good_fuelSize: fuelSize >= (proof_size A + proof_size B)), 
  {p: OLProof (gamma, delta) | is_cut_free p}.
Proof.
  induction fuelB.
  {intros. destruct b; simpl in *; lia. }
  induction fuelSize; intros; rename A0 into A.
  {destruct A; simpl in *; lia. }


  (* Tactics handling recursion, proving the necessary fuel properties and the cut-freeness of parameters of the recursive calls *)
  Tactic Notation "cutelimSize" ident(fuelSize) constr(A) constr(B) := 
    let gS := (fresh "gS") in let cfA := (fresh "cfA") in let cfB := (fresh "cfB") in
      assert (fuelSize >= proof_size A + proof_size B) as gS; (only 2: assert (is_cut_free A) as cfA); (only 3: assert (is_cut_free B) as cfB);
      (match goal with 
        | [IHfuelSize : forall (gamma delta : AnTerm) (A : OLProof _), is_cut_free A -> forall B : OLProof _, is_cut_free B -> fuelSize >= proof_size A + proof_size B -> {p : OLProof (gamma, delta) | is_cut_free p} |- {p: OLProof ?s | _}]  => 
          try (exact (IHfuelSize _ _ A cfA B cfB gS));
          let P := fresh "P" in let CF := fresh "CF" in destruct (IHfuelSize _ _ A cfA B cfB gS) as [P CF]
        | [ |- _ >= (proof_size _ + proof_size _)] => (subst; simpl in *; (try lia))
        | [ |- _ >= (term_size _)] => (subst; simpl in *; (try lia))
        | [ |- is_cut_free _] => (subst; simpl in *; intuition)
      end).

  Tactic Notation "cutelimb" ident(fuelSize) ident(fuelB) constr(b) constr(A) constr(B) := 
    let gS := (fresh "gS") in let gb := (fresh "gb") in let cfA := (fresh "cfA") in let cfB := (fresh "cfB") in
      assert (proof_size A + proof_size B >= proof_size A + proof_size B) as gS; (only 2: assert (fuelB >= term_size b) as gb); (only 3: assert (is_cut_free A) as cfA); (only 4: assert (is_cut_free B) as cfB);
      (match goal with 
        | [IHfuelB : forall b : Term, fuelB >= term_size b -> forall (fuelSize : nat) (gamma delta : AnTerm) (A : OLProof (gamma, R b)), 
                     is_cut_free A -> forall B : OLProof (L b, delta), is_cut_free B -> fuelSize >= proof_size A + proof_size B -> {p : OLProof _ | is_cut_free p} |- {p: OLProof ?s | _}]  => 
            try (exact (IHfuelB b gb (proof_size A + proof_size B) _ _ A cfA B cfB gS));
            let P := fresh "P" in let CF := fresh "CF" in destruct (IHfuelB b gb (proof_size A + proof_size B) _ _ A cfA B cfB gS) as [P CF]
        | [ |- _ >= (proof_size _ + proof_size _)] => (subst; simpl in *; (try lia))
        | [ |- _ >= (term_size _)] => (subst; simpl in *; (try lia))
        | [ |- is_cut_free _] => (subst; simpl in *; intuition)
      end).


    (* This does the kind of dependent case analysis we want on the proof, but it's tricky *)
    Tactic Notation "analyze" hyp(proof) ident(good_fuelSize) ident(p) ident(good_fuelB) := 
      generalize good_fuelSize, good_fuelB, p; clear good_fuelSize; clear good_fuelB; clear p; dependent inversion proof; intros; subst.

    (* for cases where One of the proof has a cut when it is supposed to be cut free. *)
    Ltac cutContradict := simpl in *; exfalso; auto.

    (* Complete the proofs of the easy side conditions *)
    Ltac finish := simpl term_size in *; simpl is_cut_free in *; intuition; lia.
    
    
    (* Let's do the case analysis. In theory there should be more than 500 cases, but fortunately, we can do *some* of them at once. *)

    analyze A good_fuelSize good_fuelB p1.
    all: try (rename o into A'); try (rename o0 into A'').
    - exists B. auto.
    - exists (Weaken A'). simpl in *. auto.
    - cutelimSize fuelSize A' B. exists (LeftAnd1 P). finish.
    - cutelimSize fuelSize A' B. exists (LeftAnd2 P). finish.
    - cutelimSize fuelSize A' B. cutelimSize fuelSize A'' B. exists (LeftOr P P0). finish.
    - cutelimSize fuelSize A' B. exists (LeftNot P). finish.
      (*Here we also inverse B, generalizing the necessary fuel conditions*)
    - analyze B good_fuelSize good_fuelB p2. all: try (rename o into B'). all: try (rename o0 into B'').
      + cutelimSize fuelSize (RightAnd A' A'') B'. exists (Weaken P). finish.
      + simpl in *. analyze B' good_fuelSize good_fuelB p2. all: try (rename o into B1). all: try (rename o0 into B2).
        * cutelimSize fuelSize (RightAnd A' A'') B1.
        * cutelimSize fuelSize (RightAnd A' A'') (Swap B1). cutelimb fuelSize fuelB a A' (Swap P).
          exists (Contract P0). auto.
        * cutelimSize fuelSize (RightAnd A' A'') (Swap B1). cutelimb fuelSize fuelB b0 A'' (Swap P).
          exists (Contract P0). auto.
        * cutelimSize fuelSize (RightAnd A' A'') (Contract B1).
        * cutContradict.

      + cutelimb fuelSize fuelB a A' B'. 
      + cutelimb fuelSize fuelB b0 A'' B'.
      + cutelimSize fuelSize  (RightAnd A' A'') B'. cutelimSize fuelSize  (RightAnd A' A'') B''.
        exists (RightAnd P P0). finish.
      + cutelimSize fuelSize  (RightAnd A' A'') B'. exists (RightOr1 P). finish.
      + cutelimSize fuelSize  (RightAnd A' A'') B'. exists (RightOr2 P). finish.
      + cutelimSize fuelSize  (RightAnd A' A'') B'. exists (RightNot P). finish.
      + simpl in *. analyze B' good_fuelSize good_fuelB p2. all: try (rename o into B1). all: try (rename o0 into B2).
        * exists (Swap (Weaken B1)). auto.
        * cutelimSize fuelSize (RightAnd A' A'') (Swap B1). exists (Swap (LeftAnd1 (Swap P))). finish.
        * cutelimSize fuelSize (RightAnd A' A'') (Swap B1). exists (Swap (LeftAnd2 (Swap P))). finish.
        * cutelimSize fuelSize (RightAnd A' A'') (Swap B1). cutelimSize fuelSize (RightAnd A' A'') (Swap B2). exists (Swap (LeftOr (Swap P) (Swap P0))). finish.
        * cutelimSize fuelSize (RightAnd A' A'') (Swap B1). exists (Swap (LeftNot (Swap P))). finish.
        * cutelimSize fuelSize (RightAnd A' A'') B1.
        * cutContradict.
      + cutContradict.
    - analyze B good_fuelSize good_fuelB p2. all: try (rename o into B'). all: try (rename o0 into B'').
      + cutelimSize fuelSize (@RightOr1 _ b0 _ A') B'. exists (Weaken P). finish.
      + simpl in *. analyze B' good_fuelSize good_fuelB p2. all: try (rename o into B1). all: try (rename o0 into B2).
        * cutelimSize fuelSize (@RightOr1 _ b0 _ A') B1.
        * cutelimSize fuelSize (@RightOr1 _ b0 _ A') (Swap B1). cutelimb fuelSize fuelB a A' (Swap P).
          exists (Contract P0). auto.
        * cutelimSize fuelSize (@RightOr1 _ b0 _ A') (Contract B1).
        * cutContradict.

      + cutelimb fuelSize fuelB a A' B'. (* Example case *)
      + cutelimSize fuelSize  (@RightOr1 _ b0 _ A') B'. cutelimSize fuelSize  (@RightOr1 _ b0 _ A') B''.
        exists (RightAnd P P0). finish.
      + cutelimSize fuelSize  (@RightOr1 _ b0 _ A') B'. exists (RightOr1 P). finish.
      + cutelimSize fuelSize  (@RightOr1 _ b0 _ A') B'. exists (RightOr2 P). finish.
      + cutelimSize fuelSize  (@RightOr1 _ b0 _ A') B'. exists (RightNot P). finish.
      + simpl in *. analyze B' good_fuelSize good_fuelB p2. all: try (rename o into B1). all: try (rename o0 into B2).
        * exists (Swap (Weaken B1)). auto.
        * cutelimSize fuelSize (@RightOr1 _ b0 _ A') (Swap B1). exists (Swap (LeftAnd1 (Swap P))). finish.
        * cutelimSize fuelSize (@RightOr1 _ b0 _ A') (Swap B1). exists (Swap (LeftAnd2 (Swap P))). finish.
        * cutelimSize fuelSize (@RightOr1 _ b0 _ A') (Swap B1). cutelimSize fuelSize (@RightOr1 _ b0 _ A') (Swap B2). exists (Swap (LeftOr (Swap P) (Swap P0))). finish.
        * cutelimSize fuelSize (@RightOr1 _ b0 _ A') (Swap B1). exists (Swap (LeftNot (Swap P))). finish.
        * cutelimSize fuelSize (@RightOr1 _ b0 _ A') B1.
        * cutContradict.
      + cutContradict.
    - analyze B good_fuelSize good_fuelB p2. all: try (rename o into B'). all: try (rename o0 into B'').
      + cutelimSize fuelSize (@RightOr2 a _  _ A') B'. exists (Weaken P). finish.
      + simpl in *. analyze B' good_fuelSize good_fuelB p2. all: try (rename o into B1). all: try (rename o0 into B2).
        * cutelimSize fuelSize (@RightOr2 a _  _ A') B1.
        * cutelimSize fuelSize (@RightOr2 a _  _ A') (Swap B2). cutelimb fuelSize fuelB b0 A' (Swap P).
          exists (Contract P0). auto.
        * cutelimSize fuelSize (@RightOr2 a _  _ A') (Contract B1).
        * cutContradict.

      + cutelimb fuelSize fuelB b0 A' B''.
      + cutelimSize fuelSize  (@RightOr2 a _  _ A') B'. cutelimSize fuelSize  (@RightOr2 a _  _ A') B''.
        exists (RightAnd P P0). finish.
      + cutelimSize fuelSize  (@RightOr2 a _  _ A') B'. exists (RightOr1 P). finish.
      + cutelimSize fuelSize  (@RightOr2 a _  _ A') B'. exists (RightOr2 P). finish.
      + cutelimSize fuelSize  (@RightOr2 a _  _ A') B'. exists (RightNot P). finish.
      + simpl in *. analyze B' good_fuelSize good_fuelB p2. all: try (rename o into B1). all: try (rename o0 into B2).
        * exists (Swap (Weaken B1)). auto.
        * cutelimSize fuelSize (@RightOr2 a _  _ A') (Swap B1). exists (Swap (LeftAnd1 (Swap P))). finish.
        * cutelimSize fuelSize (@RightOr2 a _  _ A') (Swap B1). exists (Swap (LeftAnd2 (Swap P))). finish.
        * cutelimSize fuelSize (@RightOr2 a _  _ A') (Swap B1). cutelimSize fuelSize (@RightOr2 a _  _ A') (Swap B2). exists (Swap (LeftOr (Swap P) (Swap P0))). finish.
        * cutelimSize fuelSize (@RightOr2 a _  _ A') (Swap B1). exists (Swap (LeftNot (Swap P))). finish.
        * cutelimSize fuelSize (@RightOr2 a _  _ A') B1.
        * cutContradict.
      + cutContradict.
    - analyze B good_fuelSize good_fuelB p2. all: try (rename o into B'). all: try (rename o0 into B'').
      + cutelimSize fuelSize (RightNot A') B'. exists (Weaken P). finish.
      + simpl in *. analyze B' good_fuelSize good_fuelB p2. all: try (rename o into B1). all: try (rename o0 into B2).
        * cutelimSize fuelSize (RightNot A') B1.
        * cutelimSize fuelSize (RightNot A') (Swap B1). cutelimb fuelSize fuelB a P (Swap A'). 
          exists (Contract P0). auto.
        * cutelimSize fuelSize (RightNot A') (Contract B1).
        * cutContradict.

      + cutelimb fuelSize fuelB a (Swap B') (Swap A'). exists (Swap P). auto.
      + cutelimSize fuelSize  (RightNot A') B'. cutelimSize fuelSize  (RightNot A') B''.
        exists (RightAnd P P0). finish.
      + cutelimSize fuelSize  (RightNot A') B'. exists (RightOr1 P). finish.
      + cutelimSize fuelSize  (RightNot A') B'. exists (RightOr2 P). finish.
      + cutelimSize fuelSize  (RightNot A') B'. exists (RightNot P). finish.
      + simpl in *. analyze B' good_fuelSize good_fuelB p2. all: try (rename o into B1). all: try (rename o0 into B2).
        * exists (Swap (Weaken B1)). auto.
        * cutelimSize fuelSize (RightNot A') (Swap B1). exists (Swap (LeftAnd1 (Swap P))). finish.
        * cutelimSize fuelSize (RightNot A') (Swap B1). exists (Swap (LeftAnd2 (Swap P))). finish.
        * cutelimSize fuelSize (RightNot A') (Swap B1). cutelimSize fuelSize (RightNot A') (Swap B2). exists (Swap (LeftOr (Swap P) (Swap P0))). finish.
        * cutelimSize fuelSize (RightNot A') (Swap B1). exists (Swap (LeftNot (Swap P))). finish.
        * cutelimSize fuelSize (RightNot A') B1.
        * cutContradict.
      + cutContradict.
    - simpl in *. analyze B good_fuelSize good_fuelB p2. all: try (rename o into B'); try (rename o0 into B'').
      + exists (Swap A'). eauto.
      + cutelimSize fuelSize (Swap A') B'. exists (Weaken P). finish.
      + simpl in *. analyze A' good_fuelSize good_fuelB p1. all: try (rename o into A1). all: try (rename o0 into A2).
        * cutelimSize fuelSize (Swap A1) (Contract B'). exists (Swap (Weaken P)). auto.
        * exfalso. apply no_proof_NN. exact (Cut A B).
        * cutelimSize fuelSize (Swap A1) (Contract B'). cutelimSize fuelSize (Swap A2) (Contract B'). exists (Swap (RightAnd  (Swap P) (Swap P0))). finish.
        * cutelimSize fuelSize (Swap A1) (Contract B'). exists (Swap (RightOr1 (Swap P))). finish.
        * cutelimSize fuelSize (Swap A1) (Contract B'). exists (Swap (RightOr2 (Swap P))). finish.
        * cutelimSize fuelSize (Swap A1) (Contract B'). exists (Swap (RightNot (Swap P))). finish.
        * cutelimSize fuelSize (A1) (Contract B').
        * cutContradict.
      + simpl in *. analyze A' good_fuelSize good_fuelB p1. all: try (rename o into A'1); try (rename o0 into A'2).
        * cutelimSize fuelSize (Swap A'1) (@LeftAnd1 _ b0 _ B'). exists (Swap (Weaken (Swap P))). finish.
        * simpl in *. analyze A'1 good_fuelSize good_fuelB p1. all: try (rename o into A'1'); try (rename o0 into A'1'').
          ** cutelimSize fuelSize (Swap A'1') (@LeftAnd1 _ b0 _ B').
          ** cutelimSize fuelSize (Swap A'1') (@LeftAnd1 _ b0 _ B'). cutelimb fuelSize fuelB a (Swap P) B'. 
            exists (Swap (Contract P0)). auto.
          ** cutelimSize fuelSize (Swap (Contract A'1')) (@LeftAnd1 _ b0 _ B').
          ** cutContradict.
        * cutelimSize fuelSize (Swap A'1) (@LeftAnd1 _ b0 _ B'). cutelimSize fuelSize (Swap A'2) (@LeftAnd1 _ b0 _ B').
          exists (Swap (RightAnd (Swap P) (Swap P0))). finish.
        * cutelimSize fuelSize (Swap A'1) (@LeftAnd1 _ b0 _ B'). exists (Swap (RightOr1 (Swap P))). finish.
        * cutelimSize fuelSize (Swap A'1) (@LeftAnd1 _ b0 _ B'). exists (Swap (RightOr2 (Swap P))). finish.
        * cutelimSize fuelSize (Swap A'1) (@LeftAnd1 _ b0 _ B'). exists (Swap (RightNot (Swap P))). finish.
        * cutelimSize fuelSize (A'1) (@LeftAnd1 _ b0 _ B').
        * cutContradict.
      + simpl in *. analyze A' good_fuelSize good_fuelB p1. all: try (rename o into A'1); try (rename o0 into A'2).
        * cutelimSize fuelSize (Swap A'1) (@LeftAnd2 a _ _ B'). exists (Swap (Weaken (Swap P))). finish.
        * simpl in *. analyze A'1 good_fuelSize good_fuelB p1. all: try (rename o into A'1'); try (rename o0 into A'1'').
          ** cutelimSize fuelSize (Swap A'1') (@LeftAnd2 a _ _ B').
          ** cutelimSize fuelSize (Swap A'1'') (@LeftAnd2 a _ _ B'). cutelimb fuelSize fuelB b0 (Swap P) B'. 
            exists (Swap (Contract P0)). auto.
          ** cutelimSize fuelSize (Swap (Contract A'1')) (@LeftAnd2 a _ _ B').
          ** cutContradict.
        * cutelimSize fuelSize (Swap A'1) (@LeftAnd2 a _ _ B'). cutelimSize fuelSize (Swap A'2) (@LeftAnd2 a _ _ B').
          exists (Swap (RightAnd (Swap P) (Swap P0))). finish.
        * cutelimSize fuelSize (Swap A'1) (@LeftAnd2 a _ _ B'). exists (Swap (RightOr1 (Swap P))). finish.
        * cutelimSize fuelSize (Swap A'1) (@LeftAnd2 a _ _ B'). exists (Swap (RightOr2 (Swap P))). finish.
        * cutelimSize fuelSize (Swap A'1) (@LeftAnd2 a _ _ B'). exists (Swap (RightNot (Swap P))). finish.
        * cutelimSize fuelSize (A'1) (@LeftAnd2 a _ _ B').
        * cutContradict.
      + simpl in *. analyze A' good_fuelSize good_fuelB p1. all: try (rename o into A'1); try (rename o0 into A'2).
        * cutelimSize fuelSize (Swap A'1) (LeftOr B' B''). exists (Swap (Weaken (Swap P))). finish.
        * simpl in *. analyze A'1 good_fuelSize good_fuelB p1. all: try (rename o into A'1'); try (rename o0 into A'1'').
          ** cutelimSize fuelSize (Swap A'1') (LeftOr B' B'').
          ** cutelimSize fuelSize (Swap A'1') (LeftOr B' B''). cutelimb fuelSize fuelB a (Swap P) B'. 
            exists (Swap (Contract P0)). auto.
          ** cutelimSize fuelSize (Swap A'1') (LeftOr B' B''). cutelimb fuelSize fuelB b0 (Swap P) B''. 
            exists (Swap (Contract P0)). auto.
          ** cutelimSize fuelSize (Swap (Contract A'1')) (LeftOr B' B'').
          ** cutContradict.
        * cutelimSize fuelSize (Swap A'1) (LeftOr B' B''). cutelimSize fuelSize (Swap A'2) (LeftOr B' B'').
          exists (Swap (RightAnd (Swap P) (Swap P0))). finish.
        * cutelimSize fuelSize (Swap A'1) (LeftOr B' B''). exists (Swap (RightOr1 (Swap P))). finish.
        * cutelimSize fuelSize (Swap A'1) (LeftOr B' B''). exists (Swap (RightOr2 (Swap P))). finish.
        * cutelimSize fuelSize (Swap A'1) (LeftOr B' B''). exists (Swap (RightNot (Swap P))). finish.
        * cutelimSize fuelSize (A'1) (LeftOr B' B'').
        * cutContradict.
      + simpl in *. analyze A' good_fuelSize good_fuelB p1. all: try (rename o into A'1); try (rename o0 into A'2).
        * cutelimSize fuelSize (Swap A'1) (LeftNot B'). exists (Swap (Weaken (Swap P))). finish.
        * simpl in *. analyze A'1 good_fuelSize good_fuelB p1. all: try (rename o into A'1'); try (rename o0 into A'1'').
          ** cutelimSize fuelSize (Swap A'1') (LeftNot B').
          ** cutelimSize fuelSize (Swap A'1') (LeftNot B'). cutelimb fuelSize fuelB a (Swap B') P. 
            exists (Swap (Contract P0)). auto.
          ** cutelimSize fuelSize (Swap (Contract A'1')) (LeftNot B').
          ** cutContradict.
        * cutelimSize fuelSize (Swap A'1) (LeftNot B'). cutelimSize fuelSize (Swap A'2) (LeftNot B').
          exists (Swap (RightAnd (Swap P) (Swap P0))). finish.
        * cutelimSize fuelSize (Swap A'1) (LeftNot B'). exists (Swap (RightOr1 (Swap P))). finish.
        * cutelimSize fuelSize (Swap A'1) (LeftNot B'). exists (Swap (RightOr2 (Swap P))). finish.
        * cutelimSize fuelSize (Swap A'1) (LeftNot B'). exists (Swap (RightNot (Swap P))). finish.
        * cutelimSize fuelSize (A'1) (LeftNot B').
        * cutContradict.
      + cutelimSize fuelSize (Swap A') B'. cutelimSize fuelSize (Swap A') B''. exists (RightAnd P P0). finish.
      + cutelimSize fuelSize (Swap A') B'. exists (RightOr1 P). finish.
      + cutelimSize fuelSize (Swap A') B'. exists (RightOr2 P). finish.
      + cutelimSize fuelSize (Swap A') B'. exists (RightNot P). finish.
      + simpl in *. analyze A' good_fuelSize good_fuelB p1. all: try (rename o into A1). all: try (rename o0 into A2).
        * cutelimSize fuelSize (Swap A1) (Swap B'). exists (Swap (Weaken (Swap P))). auto.
        * simpl in *. analyze B' good_fuelSize good_fuelB p2. all: try (rename o into B1). all: try (rename o0 into B2).
          ** exists (Swap B1). finish.
          ** cutelimSize fuelSize (Swap (Contract A1)) (Swap B1). exists (Swap (LeftAnd1 (Swap P))). finish.
          ** cutelimSize fuelSize (Swap (Contract A1)) (Swap B1). exists (Swap (LeftAnd2 (Swap P))). finish.
          ** cutelimSize fuelSize (Swap (Contract A1)) (Swap B1). cutelimSize fuelSize (Swap (Contract A1)) (Swap B2). exists (Swap (LeftOr (Swap P) (Swap P0))). finish.
          ** cutelimSize fuelSize (Swap (Contract A1)) (Swap B1). exists (Swap (LeftNot (Swap P))). finish.
          ** cutelimSize fuelSize (Swap (Contract A1)) B1.
          ** cutContradict.
        * cutelimSize fuelSize (Swap A1) (Swap B'). cutelimSize fuelSize (Swap A2) (Swap B'). exists (Swap (RightAnd (Swap P) (Swap P0))). finish.
        * cutelimSize fuelSize (Swap A1) (Swap B'). exists (Swap (RightOr1 (Swap P))). finish.
        * cutelimSize fuelSize (Swap A1) (Swap B'). exists (Swap (RightOr2 (Swap P))). finish.
        * cutelimSize fuelSize (Swap A1) (Swap B'). exists (Swap (RightNot (Swap P))). finish.
        * cutelimSize fuelSize (A1) (Swap B').
        * cutContradict.
      + cutContradict.
    - cutContradict.
Qed.

  (* Outer recursion. Informally, corresponds to saying ''Consider the topmost instance of Cut in the proof''. *)

Theorem cut_elimination_fuel : forall (fuelCut: nat) (fuelSize: nat)
  (s: AnTerm*AnTerm) (proof : OLProof s)
  (good_fuelSize: fuelSize >= (proof_size proof))
  (good_fuelCut: fuelCut >= (num_cut proof)),
  {p: OLProof s | is_cut_free p}.
  induction fuelCut.
    (* If num_cut = 0 *) 
  {intros. simpl. assert (0 = (num_cut proof)). lia. symmetry in H. rewrite <- cut_free_eq_zero_cut in H. exists proof. auto. }
  (* If num_cut = S n *) 
  induction fuelSize; intros.
    (* If proof_size = 0 *)
    { destruct proof. exists (Hyp). simpl. auto. all: subst. all: (unfold proof_size in good_fuelSize; lia). }
    (* If proof_size = S n *)
    destruct proof eqn: Hp. 
    all: try (rename gamma into g). all: try (rename delta into d). all: try (rename o into p). all: try (rename o1 into p1; rename o2 into p2). all: (rename fuelSize into n). 
    
    Tactic Notation "goodSize" ident(n) ident(proof)  := let name := (fresh "gS_" proof) in
      assert ((n >= proof_size proof)) as name; (only 1: (subst; simpl in *; (try lia))).

    Tactic Notation "goodCut" ident(fuelCut) ident(proof)  := let name := (fresh "gC_" proof) in
      assert ((S fuelCut) >= num_cut proof) as name; (only 1:  subst; simpl in *; (try lia)).
    
    { exists (Hyp). finish. }
    1, 2, 3, 4, 6, 8, 9, 10, 11: ( goodSize n p;  goodCut fuelCut p).
    1, 2, 3, 4, 5, 6, 7, 8, 9: destruct (IHfuelSize _ p gS_p gC_p) as [P CF]; intuition.
    { exists (Weaken P). finish. }
    { exists (Contract P). finish. }
    { exists (LeftAnd1 P). finish. }
    { exists (LeftAnd2 P). finish. }
    { exists (LeftNot P). finish. }
    { exists (RightOr1 P). finish. }
    { exists (RightOr2 P). finish. }
    { exists (RightNot P). finish. }
    { exists (Swap P). finish. }
    1, 2: ( goodSize n p1;  goodCut fuelCut p1).
    1, 2: ( goodSize n p2;  goodCut fuelCut p2).
    1, 2: destruct (IHfuelSize _ p1 gS_p1 gC_p1) as [P1 CF1]; destruct (IHfuelSize _ p2 gS_p2 gC_p2) as [P2 CF2].
    { exists (LeftOr P1 P2). finish. }
    { exists (RightAnd P1 P2). finish. }
    { destruct (num_cut p1) eqn: p1cut.
      - destruct (num_cut p2) eqn: p2cut.
        + unshelve eapply (inner_cut_elim (term_size b) b _ (proof_size p1 + proof_size p2) _ _ p1 _ p2 _); (try lia); rewrite cut_free_eq_zero_cut; auto.
        + ( goodSize n p2;  goodCut fuelCut p2). destruct (IHfuelSize _ p2 gS_p2 gC_p2) as [P CF]. rewrite cut_free_eq_zero_cut in CF.
          remember (Cut p1 P) as newproof. assert (S (num_cut proof) >= num_cut newproof ). subst. simpl. lia.
          eapply (IHfuelCut (proof_size newproof) _ newproof) . lia. subst. simpl in *. lia.
      - ( goodSize n p1;  goodCut fuelCut p1). destruct (IHfuelSize _ p1 gS_p1 gC_p1) as [P CF]. rewrite cut_free_eq_zero_cut in CF.
          remember (Cut P p2) as newproof. assert (S (num_cut proof) >= num_cut newproof ). subst. simpl. lia.
          eapply (IHfuelCut (proof_size newproof) _ newproof). lia. subst. simpl in *. lia.
    }
Qed.


Theorem cut_elimination s (proof : OLProof s): {p: OLProof s | is_cut_free p}.
Proof.
  eapply cut_elimination_fuel with (fuelCut := (num_cut proof)) (fuelSize := (proof_size proof)); eauto.
Qed.
