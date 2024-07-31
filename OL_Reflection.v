Require Import OL_Theory.

Require Import Setoid Morphisms.
Require Import Lia.
Require Import Coq.Arith.Bool_nat.
Require Import Coq.Arith.PeanoNat.


Open Scope bool_scope.
Import List.
Import ListNotations.

(* TODO: Explicit support for inequalities containing Zero and One in OL*)
(* TODO: Prove decideOL_with_without_memos *)




(* Decision Algorithm for OL *)


(*
(* OrderedType for AnTerm,  needed if using TreeMaps *)

Require Import Coq.Program.Tactics.
Require Import Coq.Program.Wf.
Require Import Coq.Structures.OrderedType.
Require Import Coq.Arith.Compare_dec.

Program Fixpoint compare_Term (x y : Term) {measure ((termSize x) + (termSize y))}: comparison :=
  match x, y with
  | Var n1, Var n2 => Nat.compare n1 n2
  | Var _, Meet _ _ => Lt
  | Var _, Join _ _ => Lt
  | Var _, Not _ => Lt
  | Meet _ _, Var _ => Gt
  | Meet l1 r1, Meet l2 r2 => 
      match compare_Term l1 l2 with
      | Lt => Lt
      | Eq => compare_Term r1 r2
      | Gt => Gt
      end
  | Meet _ _, Join _ _ => Lt
  | Meet _ _, Not _ => Lt
  | Join _ _, Var _ => Gt
  | Join _ _, Meet _ _ => Gt
  | Join l1 r1, Join l2 r2 => 
      match compare_Term l1 l2 with
      | Lt => Lt
      | Eq => compare_Term r1 r2
      | Gt => Gt
      end
  | Join _ _, Not _ => Lt
  | Not _, Var _ => Gt
  | Not _, Meet _ _ => Gt
  | Not _, Join _ _ => Gt
  | Not t1, Not t2 => compare_Term t1 t2
  end.
Next Obligation.
  simpl. lia.
Qed.
Next Obligation.
  simpl. lia.
Qed.
Next Obligation.
  simpl. lia.
Qed.
Next Obligation.
  simpl. lia.
Qed.
Next Obligation.
  simpl. lia.
Qed.

Search Nat.compare.

Lemma term_refl: forall x: Term, compare_Term x x = Eq.
Proof.
  induction x; simpl.
  - simpl. cbv. rewrite PeanoNat.Nat.compare_eq_iff. reflexivity.
  - unfold compare_Term. unfold
  
Qed.

Definition compare_AnTerm (x y: AnTerm) : comparison :=
  match x, y with
  | L n1, L n2 => compare_Term n1 n2
  | L _, _ => Lt
  | _, L _ => Gt
  | R n1, R n2 => compare_Term n1 n2
  | R _, _ => Lt
  | _, R _ => Gt
  | N, N => Eq
  end.


Module AnTermOrderedType <: OrderedType.
  Definition t := AnTerm.

  Definition compare (x y: AnTerm) : comparison := compare_AnTerm x y.

  Definition eq (x y: AnTerm) := compare x y = Eq.
  Definition lt (x y: AnTerm) := compare x y = Lt.

  Theorem eq_refl : forall x : t, eq x x.
  Proof.
    intros x. destruct x; simpl. reflexivity.
  Qed.

  Theorem eq_sym : forall x y : t, eq x y -> eq y x.
  Proof.
    intros x y H. unfold eq in *. destruct (compare_AnTerm x y); destruct (compare_AnTerm y x); try reflexivity; inversion H.
  Qed.

  Theorem eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof.
    intros x y z Hxy Hyz. unfold eq in *. destruct (compare_AnTerm x y); destruct (compare_AnTerm y z); try reflexivity; inversion Hxy; inversion Hyz.
  Qed.

  Theorem lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    intros x y z Hxy Hyz. unfold lt in *. destruct (compare_AnTerm x y); destruct (compare_AnTerm y z); try reflexivity; inversion Hxy; inversion Hyz.
  Qed.

  Theorem lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    intros x y Hlt Heq. unfold lt, eq in *. destruct (compare_AnTerm x y); inversion Hlt; inversion Heq.
  Qed.
End AnTermOrderedType.

Print AnTerm.

*)

Definition anSize (t: AnTerm) : nat := match t with
  | L t1 => 1 + termSize t1
  | R t1 => 1 + termSize t1
  | N => 1
end.


Lemma anSizePositive : forall t, anSize t >= 1. Proof. intros. destruct t; simpl; lia. Qed.




  (* Decision Algorithm for OL, using bool *)

Fixpoint decideOL_bool (fuel: nat) (g d: AnTerm) : bool :=
  match fuel with
  | 0 => false
  | S n =>
     
    (* Guaranteed sufficent cases. Not in a disjunction because if they evaluate to false, there is no need to compute the others. *)
    match (g, d) with 
    | (L (Var a), R (Var b) )  => (Nat.eqb a b) (* Hyp *)
    | (L (Meet a b), N) => decideOL_bool n (L a) (L b) (* LeftAnd1-2 *)
    | (N, R (Join a b)) => decideOL_bool n (R a) (R b) (* RightOr1-2 *)
    | (L (Join a b), _) => (decideOL_bool n (L a) d) && (decideOL_bool n (L b) d) (* LeftOr *)
    | (L (Not a), _) => decideOL_bool n (R a) d (* LeftNot *)
    | (_, R (Meet a b)) => (decideOL_bool n g (R a)) && (decideOL_bool n g (R b)) (* RightAnd *)
    | (_, R (Not a)) => decideOL_bool n g (L a) (* RightNot *)
    (* Swap cases *)
    | (R (Var a), L (Var b) )  => (Nat.eqb b a) (* Hyp *)
    | (N, L (Meet a b)) => decideOL_bool n (L a) (L b) (* LeftAnd1-2 *)
    | (R (Join a b), N) => decideOL_bool n (R a) (R b) (* RightOr1-2 *)
    | (_, L (Join a b)) => (decideOL_bool n g (L a)) && (decideOL_bool n g (L b)) (* LeftOr *)
    | (_, L (Not a)) => decideOL_bool n g (R a) (* LeftNot *)
    | (R (Meet a b), _) => (decideOL_bool n (R a) d) && (decideOL_bool n (R b) d) (* RightAnd *)
    | (R (Not a), _) => decideOL_bool n (L a) d (* RightNot *)
    | _ => false
    end ||
    (let half := fun (g d: AnTerm) =>
      (* Other cases, if none of the above apply. Thos need to be disjunctively tried if multiple apply *)
      match d with (* Weaken *)
      | L a => decideOL_bool n g N 
      | R a => decideOL_bool n g N 
      | N => false
      end ||
      match g with (* LeftAnd1 *)
      | L (Meet a b) => decideOL_bool n (L a) d
      | _ => false
      end ||
      match g with (* LeftAnd2 *)
      | L (Meet a b) => decideOL_bool n (L b) d
      | _ => false
      end ||
      match d with (* RightOr1 *)
      | R (Join a b) => decideOL_bool n g (R a)
      | _ => false
      end ||
      match d with (* RightOr2 *)
      | R (Join a b) => decideOL_bool n g (R b)
      | _ => false
      end
    in half g d || half d g)
    
  end.


Ltac recurse := simpl in *; lia.

Theorem decideOLBoolCorrect : forall n g d, (n >= (anSize g + anSize d)) -> (decideOL_bool n g d) = true -> squash (OLProof (g, d)).
Proof.
  Ltac dest g := destruct g; try congruence.
  Ltac swapNames g d := let q := fresh "q" in (rename g into q; rename d into g; rename q into d).

  induction n.
  - intros. pose proof (anSizePositive g). pose proof (anSizePositive d). lia.
  - intros. simpl in H0. (rewrite Bool.orb_true_iff in H0). destruct H0.
    Ltac induct IHn H := apply IHn in H; inversion H; (try recurse). 

    + repeat (rewrite Bool.orb_true_iff in H0). intuition.
      dest g; dest d; (try dest t0); (try dest t).
      all: match goal with
      | [ H: (?n0 =? ?n1) = true |- _ ] =>  rewrite Nat.eqb_eq in H; subst; sq; (try apply Hyp); (apply Swap; apply Hyp)
      | _ => idtac
      end.
      all: (match goal with 
      | [ H: (_ && _) = true |- _ ] => (rewrite Bool.andb_true_iff in H; destruct H)
      | _ => idtac
      end).
      all: repeat match goal with
      | [ H: decideOL_bool _ _ _ = true |- _ ] => induct IHn H
      | _ => idtac
      end. 
      all: sq. (*60 cases at this point, but many comes from the same match clause (wildcard).*)
      all: (try (apply LeftOr; auto; fail)).
      all: (try (apply RightAnd; auto; fail)).
      all: (try (apply LeftNot; auto; fail)).
      all: (try (apply RightNot; auto; fail)).
      all: (try (apply Swap; apply Contract; apply RightOr1; apply Swap; apply RightOr2; auto)).
      all: (try (apply Contract; apply LeftAnd2; apply Swap; apply LeftAnd1; auto)).
      all: apply Swap.
      all: (try (apply LeftOr; apply Swap; auto; fail)).
      all: (try (apply RightAnd; apply Swap; auto; fail)).
      all: (try (apply LeftNot; apply Swap; auto; fail)).
      all: (try (apply RightNot; apply Swap; auto; fail)).
      all: (try (apply Swap; apply Contract; apply RightOr1; apply Swap; apply RightOr2; auto)).
      all: (try (apply Contract; apply LeftAnd2; apply Swap; apply LeftAnd1; auto)).
    + rewrite Bool.orb_true_iff in H0. destruct H0.
      * repeat rewrite Bool.orb_true_iff in H0. intuition.
        ** dest d; dest t. all: induct IHn H0; sq; apply Weaken; auto.
        ** dest g; dest t. induct IHn H0. sq. apply LeftAnd1. auto.
        ** dest g; dest t. induct IHn H1. sq. apply LeftAnd2. auto.
        ** dest d; dest t. induct IHn H0. sq. apply RightOr1. auto.
        ** dest d; dest t. induct IHn H1. sq. apply RightOr2. auto.
      * repeat rewrite Bool.orb_true_iff in H0. intuition.
        ** dest g; dest t; induct IHn H0; sq; apply Swap; apply Weaken; auto.
        ** dest d; dest t. induct IHn H0. sq. apply Swap. apply LeftAnd1. auto.
        ** dest d; dest t. induct IHn H1. sq. apply Swap. apply LeftAnd2. auto.
        ** dest g; dest t. induct IHn H0. sq. apply Swap. apply RightOr1. auto.
        ** dest g; dest t. induct IHn H1. sq. apply Swap. apply RightOr2. auto.
Qed.






(* Memoized version of the above algorithm. 
  O(e^n) => O(n^5). Optimal is O(n^2). 
  Using Lists over HashMap: cost n^2.
  Using syntactic equality costs n, while in practice we only need pointer equality 
  (not even hash consing, though in Coq that's pretty much the same.) *)



Definition MemoKey := (AnTerm * AnTerm)%type.

Definition MemoMap := list (MemoKey * bool).

Definition MemoMapBool := MemoMap -> (bool * MemoMap).

Definition OrMemo (left : MemoMapBool ) (right : MemoMapBool)  := fun (memo : MemoMap) => match left memo with
| (true, m) => (true, m)
| (false, m) => right m
end.

Definition AndMemo (left : MemoMapBool ) (right : MemoMapBool)  := fun (memo : MemoMap) => match left memo with
| (true, m) => right m
| (false, m) => (false, m)
end.

Definition Mbool b : MemoMapBool  := fun (memo: MemoMap) => (b, memo).
Definition Mtrue := Mbool true.
Definition Mfalse := Mbool false.

Infix "|||" := OrMemo (at level 60).
Infix "&&&" := AndMemo (at level 60).

Definition MemoKey_eqdec : forall (x y: MemoKey), {x = y} + {x <> y}.
Proof. repeat decide equality. Defined.

Fixpoint decideOL_boolM (fuel: nat) (g d: AnTerm) (memo: list (MemoKey * bool)) : (bool * list (MemoKey * bool)) :=
match List.find (fun x => if MemoKey_eqdec (fst x) (g, d) then true else false) memo with
| Some (_, b) => (b, memo)
| None => let (b, m) :=
  (match fuel with
  | 0 => (false, memo)
  | S n =>
    let half := fun (g d: AnTerm) => 
    (* Guaranteed sufficent cases. Puting  *)
      match (g, d) with 
      | (L (Var a), R (Var b) )  => Mbool (Nat.eqb a b) (* Hyp *)
      | (L (Meet a b), N) => decideOL_boolM n (L a) (L b) (* LeftAnd1-2 *)
      | (N, R (Join a b)) => decideOL_boolM n (R a) (R b) (* RightOr1-2 *)
      | (L (Join a b), _) => (decideOL_boolM n (L a) d) &&& (decideOL_boolM n (L b) d) (* LeftOr *)
      | (L (Not a), _) => decideOL_boolM n (R a) d (* LeftNot *)
      | (_, R (Meet a b)) => (decideOL_boolM n g (R a)) &&& (decideOL_boolM n g (R b)) (* RightAnd *)
      | (_, R (Not a)) => decideOL_boolM n g (L a) (* RightNot *)
      | _ => Mfalse
      end |||
      (* Other cases, if none of the above apply *)
      match d with (* Weaken *)
      | L a => decideOL_boolM n g N 
      | R a => decideOL_boolM n g N 
      | N => Mfalse
      end |||
      match g with (* LeftAnd1 *)
      | L (Meet a b) => decideOL_boolM n (L a) d
      | _ => Mfalse
      end |||
      match g with (* LeftAnd2 *)
      | L (Meet a b) => decideOL_boolM n (L b) d
      | _ => Mfalse
      end |||
      match d with (* RightOr1 *)
      | R (Join a b) => decideOL_boolM n g (R a)
      | _ => Mfalse
      end |||
      match d with (* RightOr2 *)
      | R (Join a b) => decideOL_boolM n g (R b)
      | _ => Mfalse
      end
    in (half g d ||| half d g) memo
  end) in (b, ((g, d), b) :: m)
end.


Definition decideOL_boolMemo (g d: AnTerm): bool := fst (decideOL_boolM (anSize g + anSize d) g d []).

Definition decideOL_bool_simp (g d: AnTerm): bool := decideOL_bool (anSize g + anSize d) g d.

(* Left to prove monadisation of the memoization is correct *)
Axiom decideOL_with_without_memos : forall g d,  decideOL_boolMemo g d = decideOL_bool (anSize g + anSize d) g d.



  (* Reflection: solve goals using the algorithm in arbitrary Ortholattice *)


Theorem decideOLBoolSimpCorrect : forall g d, (decideOL_bool_simp g d) = true -> AnLeq g d.
Proof.
  intros. assert (squash (OLProof (g, d))). apply decideOLBoolCorrect in H; auto; lia.
  destruct H0. apply (Soundness (g, d)). auto.
Qed.


 (* If the algorithms outputs True, then g is semanticaly smaller than d.*)
Theorem decideOLBoolMemoCorrect : forall g d, (decideOL_boolMemo g d) = true -> AnLeq g d.
Proof.
  intros. assert (squash (OLProof (g, d))). rewrite  decideOL_with_without_memos in H. apply decideOLBoolCorrect in H; auto; lia.
  destruct H0. apply (Soundness (g, d)). auto.
Qed.





Theorem reduceToAlgo {OL: Ortholattice} : forall t1 t2 f, (decideOL_bool_simp (L t1) (R t2)) = true -> ((eval t1 f) <= (eval t2 f)).
Proof.
  intros. assert (AnLeq  (L t1) (R t2)). all: auto using decideOLBoolSimpCorrect.
Qed.

Theorem reduceToAlgoMemo {OL: Ortholattice} : forall t1 t2 f, (decideOL_boolMemo (L t1) (R t2)) = true -> ((eval t1 f) <= (eval t2 f)).
Proof.
  intros. assert (AnLeq  (L t1) (R t2)). all: auto using decideOLBoolMemoCorrect.
Qed.


(* List management for environment *)

Ltac contains x l :=
  match l with
  | x :: _ => true
  | _ ::  ?tail => contains x ?tail
  | _ => false
  end.

Ltac addIfNotExists x l :=
  
  let cont := contains x l in 
  match cont with
  | true => l
  | false => constr:(x :: l)
  end.

Ltac indexOf x l :=
  match l with
  | x :: ?tail => O
  | _ :: ?tail => let r := (indexOf x tail) in constr:(S r)
  | _ => fail "element not found. x:" x "l:" l
  end.

(* Ugly way to check if two terms are convertible, but that's all internet gave me *)
Ltac convertible x y := constr:(eq_refl x : x = y).

(* Puts all leaves of the expression (i.e. which are neither meets, joins nor neg) into a list. *)
Ltac leaves AA m j n l exp := 
  match exp with
  | (?op ?X1 ?X2) => let __ := convertible op m in let l1 := leaves AA m j n l X1 in
                 let l2 := leaves AA m j n l1 X2 in
                 constr:(l2)
  | (?op ?X1 ?X2) => let __ := convertible op j in let l1 := leaves AA m j n l X1 in
                 let l2 := leaves AA m j n l1 X2 in
                 constr:(l2)
  | (?op ?X1) => let __ := convertible op n in leaves AA m j n l X1
  | ?X1 => addIfNotExists X1 l
  end.


Ltac reify_term A m j n t env := match t with
  | (?op ?X1 ?X2) => let __ := convertible op m in let r1 := reify_term A m j n X1 env
                    with r2 := reify_term A m j n X2 env in 
                    constr:(Meet r1 r2)
  | (?op ?X1 ?X2) => let __ := convertible op j in let r1 := reify_term A m j n X1 env
                    with r2 := reify_term A m j n X2 env in
                    constr:(Join r1 r2)
  | (?op ?X1) => let __ := convertible op n in let r1 := reify_term A m j n X1 env in
                    constr:(Not r1)
  | ?X1 => let j := indexOf X1 env in constr:(Var j)
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
      n := (eval simpl in (@neg OL)) in
  let l1 := leaves AA m j n (@nil AA) S in
  let l2 := leaves AA m j n l1 T in
  let S' := (eval simpl in S) with
      T' := (eval simpl in T) in
  let t1' := (reify_term AA m j n S' l2) with
      t2' := (reify_term AA m j n T' l2) in
  let h := head_tac l2 in
  let env := constr:(fun k:nat => nth k l2 h ) in
      change ((@eval OL t1' env) <= (@eval OL t2' env)).


Ltac reify_goal OL := 
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

Ltac solveOL OL := 
  reify_goal OL; apply reduceToAlgo; auto; vm_compute; (try reflexivity).

Ltac solveOLMemo OL := 
  reify_goal OL; apply reduceToAlgoMemo; auto; vm_compute; (try reflexivity).


(* Sure, higher order matching is hard, but getting both of those to work was too. 
   Tried cbv with all kinds of parameters first, simpl works in the end. *)

Theorem test00 {OL: Ortholattice} : forall a,  a <= a.
Proof.
  intro. 
  solveOLMemo OL.
Qed.

Theorem test0 {OL: Ortholattice} : forall a,  a <= (a ∩ a).
Proof.
  intro. 
  solveOLMemo OL.
Qed.


Theorem test1 {OL: Ortholattice} : forall a,  a == (a ∩ a).
Proof.
  intro. 
  solveOLMemo OL.
Qed.



Theorem test2 : forall a: (@A BoolOL),  a <= (a || a).
Proof.
  intro.
  solveOLMemo BoolOL.
Qed.



Theorem test3 : forall a: (@A BoolOL), Bool.le a (andb a a).
Proof.
  intro. 
  solveOLMemo BoolOL.
Qed.


Theorem test4 : forall a b : bool,   ( a ∩ (neg a)) <= b.
Proof.
  intros.
  solveOLMemo BoolOL.
Qed.


Theorem test6 : forall a b : bool,  Bool.le (andb a (negb a)) b.
Proof.
  intros. 
  solveOLMemo BoolOL.
Qed.

Theorem test7 : forall a b c: bool,  (a ∩ (negb a)) <= (a || (b && c)).
Proof.
  intros. 
  solveOLMemo BoolOL.
Qed.


