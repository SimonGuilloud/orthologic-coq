
Require Import NArith.
Require Import OL_Theory.

Require Import Setoid Morphisms.
Require Import Lia.
Require Import Coq.Arith.Bool_nat.
Require Import Coq.Arith.PeanoNat.


Open Scope bool_scope.
Import List.
Import ListNotations.
  (* Decision Algorithm for OL *)


Fixpoint decideOL_bool (fuel: nat) (g d: AnTerm) : bool :=
  match fuel with
  | 0 => false
  | S n =>
     
    (* Guaranteed sufficent cases. Not in a disjunction because if they evaluate to false, there is no need to compute the others. *)
    match (g, d) with 
    | (L (Var a), R (Var b) )  => (Pos.eqb a b) (* Hyp *)
    (*| (L (Meet a b), N) => decideOL_bool n (L (Meet a b)) (L (Meet a b)) (* LeftAnd1-2 *)*)
    (*| (N, R (Join a b)) => decideOL_bool n (R (Join a b)) (R (Join a b)) (* RightOr1-2 *) *)
    | (L (Join a b), _) => (decideOL_bool n (L a) d) && (decideOL_bool n (L b) d) (* LeftOr *)
    | (L (Not a), _) => decideOL_bool n (R a) d (* LeftNot *)
    | (_, R (Meet a b)) => (decideOL_bool n g (R a)) && (decideOL_bool n g (R b)) (* RightAnd *)
    | (_, R (Not a)) => decideOL_bool n g (L a) (* RightNot *)
    (* Swap cases *)
    | (R (Var a), L (Var b) )  => (Pos.eqb b a) (* Hyp *)
    (*| (N, L (Meet a b)) => decideOL_bool n (L (Meet a b)) (L (Meet a b)) (* LeftAnd1-2 *)*)
    (*| (R (Join a b), N) => decideOL_bool n (R (Join a b)) (R (Join a b)) (* RightOr1-2 *)*)
    | (_, L (Join a b)) => (decideOL_bool n g (L a)) && (decideOL_bool n g (L b)) (* LeftOr *)
    | (_, L (Not a)) => decideOL_bool n g (R a) (* LeftNot *)
    | (R (Meet a b), _) => (decideOL_bool n (R a) d) && (decideOL_bool n (R b) d) (* RightAnd *)
    | (R (Not a), _) => decideOL_bool n (L a) d (* RightNot *)
    | _ => 
      (* Other cases, if none of the above apply. Thos need to be disjunctively tried if multiple apply *)
        match d with (* Weaken g*)
        | L a => decideOL_bool n g N 
        | R a => decideOL_bool n g N 
        | N => false
        end ||(
        match g with (* Weaken d*)
        | L a => decideOL_bool n d N 
        | R a => decideOL_bool n d N 
        | N => false
        end ||(
        match g with (* LeftAnd1 g*)
        | L (Meet a b) => decideOL_bool n (L a) d
        | _ => false
        end ||(
        match d with (* LeftAnd1 d*)
        | L (Meet a b) => decideOL_bool n (L a) g
        | _ => false
        end ||(
        match g with (* LeftAnd2 g*)
        | L (Meet a b) => decideOL_bool n (L b) d
        | _ => false
        end ||(
        match d with (* LeftAnd2 d*)
        | L (Meet a b) => decideOL_bool n (L b) g
        | _ => false
        end ||(
        match g with (* RightOr1 g*)
        | R (Join a b) => decideOL_bool n d (R a)
        | _ => false
        end ||(
        match d with (* RightOr1 d*)
        | R (Join a b) => decideOL_bool n g (R a)
        | _ => false
        end ||(
        match g with (* RightOr2 g*)
        | R (Join a b) => decideOL_bool n d (R b)
        | _ => false
        end ||(
        match d with (* RightOr2 d*)
        | R (Join a b) => decideOL_bool n g (R b)
        | _ => false
        end ||(
        match (g, d) with
        | (N, L(_)) => decideOL_bool n d d
        | (N, R(_)) => decideOL_bool n d d
        | (L(_), N) => decideOL_bool n g g
        | (R(_), N) => decideOL_bool n g g
        | _ => false
        end
        ))))))))))
    end
  end.


Ltac recurse := simpl in *; lia.

Hint Constructors OLProof squash : olproof.

Hint Rewrite
  Bool.orb_false_r
  Bool.andb_true_iff Bool.orb_true_iff
  Pos.eqb_eq Nat.eqb_eq : rw_bool.

Theorem decideOLBoolCorrect : forall n g d, (decideOL_bool n g d) = true -> squash (OLProof (g, d)).
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

Definition anSize (t: AnTerm) : nat := match t with
  | L t1 => 1 + termSize t1
  | R t1 => 1 + termSize t1
  | N => 1
end.

Theorem anSizePositive : forall t, anSize t >= 1. Proof. intros. destruct t; simpl; lia. Qed.

Definition decideOL_bool_simp (g d: AnTerm): bool := decideOL_bool (anSize g + anSize d) g d.

  (* Reflection: solve goals using the algorithm in arbitrary Ortholattice *)


Theorem decideOLBoolSimpCorrect : forall g d, (decideOL_bool_simp g d) = true -> AnLeq g d.
Proof.
  intros. assert (squash (OLProof (g, d))). apply decideOLBoolCorrect in H; auto; lia.
  destruct H0. apply (Soundness (g, d)). auto.
Qed.



Theorem reduceToAlgo {OL: Ortholattice} : forall t1 t2 f, (decideOL_bool_simp (L t1) (R t2)) = true -> ((eval t1 f) <= (eval t2 f)).
Proof.
  intros. assert (AnLeq  (L t1) (R t2)). all: auto using decideOLBoolSimpCorrect.
Qed.


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
  | x :: ?tail => xH
  | _ :: ?tail => let r := (indexOf x tail) in constr:(Pos.succ r)
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


Ltac reify_term OL t env := match t with
  | (?op ?X1 ?X2) => let __ := convertible op (@meet OL) in let r1 := reify_term OL X1 env
                    with r2 := reify_term OL X2 env in 
                    constr:(Meet r1 r2)
  | (?op ?X1 ?X2) => let __ := convertible op (@join OL)  in let r1 := reify_term OL X1 env
                    with r2 := reify_term OL X2 env in
                    constr:(Join r1 r2)
  | (?op ?X1) => let __ := convertible op (@neg OL)  in let r1 := reify_term OL X1 env in
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
  let t1' := (reify_term OL S l2) with
      t2' := (reify_term OL T l2) in
  let h := head_tac l2 in
  let env := constr:(fun k:positive => nth (pred (Pos.to_nat k)) l2 h ) in
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




(* Small tests *)

Example test1 {OL: Ortholattice} : forall a,  a <= a.
Proof.
  intro. 
  solveOL OL.
Qed.

Example test2 {OL: Ortholattice} : forall a,  a == (a ∩ a).
Proof.
  intro. 
  solveOL OL.
Qed.

(*
Example test3 {OL: Ortholattice} a b c: 
  ¬(b ∪ ¬(c ∩ ¬b) ∪ a) <= (¬a ∪ ¬(b ∩ ¬a)).
Proof.
  solveOL OL.
Qed.
*)


Example test4 : forall a: (@A BoolOL),  a <= (a || a).
Proof.
  intro.
  solveOL BoolOL.
Qed.



Example test5 : forall a: (@A BoolOL), Bool.le a (andb a a).
Proof.
  intro. 
  solveOL BoolOL.
Qed.


Example test6 : forall a b : bool,   ( a ∩ (neg a)) <= b.
Proof.
  intros.
  solveOL BoolOL.
Qed.


Example test7 : forall a b : bool,  Bool.le (andb a (negb a)) b.
Proof.
  intros. 
  solveOL BoolOL.
Qed.


Example test8 : forall a b c: bool,  (a ∩ (negb a)) <= (a || (b && c)).
Proof.
  intros. 
  solveOL BoolOL.
Qed.



Example test9 {OL: Ortholattice} a b c: 
  c <= ((a ∩ b) ∪ (¬a) ∪ (¬b)).
Proof.
  solveOL OL.
Qed.

