Require Import OL_Theory.

Require Import OL_Reflection_1_base.

Require Import Setoid Morphisms.
Require Import Lia.
Require Import Coq.Arith.Bool_nat.
Require Import Coq.Arith.PeanoNat.


Open Scope bool_scope.
Import List.
Import ListNotations.



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


Fixpoint find (x: MemoKey) (l: MemoMap) : option (MemoKey * bool) := match l with
| [] => None
| head :: tail => if MemoKey_eqdec x (fst head) then Some head else find x tail
end.

Fixpoint decideOL_boolM (fuel: nat) (g d: AnTerm) (memo: MemoMap) : (bool * MemoMap) :=
match find (g, d) memo with
| Some (_, b) => (b, memo)
| None => let (b, m) :=
  (match fuel with
  | 0 => (false, memo)
  | S n =>
    (* Guaranteed sufficent cases. *)
      match (g, d) with 
      | (L (Var a), R (Var b) )  => Mbool (Nat.eqb a b) (* Hyp *)
      | (L (Meet a b), N) => decideOL_boolM n (L a) (L b) (* LeftAnd1-2 *)
      | (N, R (Join a b)) => decideOL_boolM n (R a) (R b) (* RightOr1-2 *)
      | (L (Join a b), _) => (decideOL_boolM n (L a) d) &&& (decideOL_boolM n (L b) d) (* LeftOr *)
      | (L (Not a), _) => decideOL_boolM n (R a) d (* LeftNot *)
      | (_, R (Meet a b)) => (decideOL_boolM n g (R a)) &&& (decideOL_boolM n g (R b)) (* RightAnd *)
      | (_, R (Not a)) => decideOL_boolM n g (L a) (* RightNot *)
          (* Swap cases *)
      | (R (Var a), L (Var b) )  => Mbool (Nat.eqb b a) (* Hyp *)
      | (N, L (Meet a b)) => decideOL_boolM n (L a) (L b) (* LeftAnd1-2 *)
      | (R (Join a b), N) => decideOL_boolM n (R a) (R b) (* RightOr1-2 *)
      | (_, L (Join a b)) => (decideOL_boolM n g (L a)) &&& (decideOL_boolM n g (L b)) (* LeftOr *)
      | (_, L (Not a)) => decideOL_boolM n g (R a) (* LeftNot *)
      | (R (Meet a b), _) => (decideOL_boolM n (R a) d) &&& (decideOL_boolM n (R b) d) (* RightAnd *)
      | (R (Not a), _) => decideOL_boolM n (L a) d (* RightNot *)
      | _ => 
                match d with (* Weaken g*)
        | L a => decideOL_boolM n g N 
        | R a => decideOL_boolM n g N 
        | N => Mfalse
        end |||(
        match g with (* Weaken d*)
        | L a => decideOL_boolM n d N 
        | R a => decideOL_boolM n d N 
        | N => Mfalse
        end |||(
        match g with (* LeftAnd1 g*)
        | L (Meet a b) => decideOL_boolM n (L a) d
        | _ => Mfalse
        end |||(
        match d with (* LeftAnd1 d*)
        | L (Meet a b) => decideOL_boolM n (L a) g
        | _ => Mfalse
        end |||(
        match g with (* LeftAnd2 g*)
        | L (Meet a b) => decideOL_boolM n (L b) d
        | _ => Mfalse
        end |||(
        match d with (* LeftAnd2 d*)
        | L (Meet a b) => decideOL_boolM n (L b) g
        | _ => Mfalse
        end |||(
        match g with (* RightOr1 g*)
        | R (Join a b) => decideOL_boolM n d (R a)
        | _ => Mfalse
        end |||(
        match d with (* RightOr1 d*)
        | R (Join a b) => decideOL_boolM n g (R a)
        | _ => Mfalse
        end |||(
        match g with (* RightOr2 g*)
        | R (Join a b) => decideOL_boolM n d (R b)
        | _ => Mfalse
        end|||(
        match d with (* RightOr2 d*)
        | R (Join a b) => decideOL_boolM n g (R b)
        | _ => Mfalse
        end
        )))))))))
      end memo
  end) in (b, ((g, d), b) :: m)
end.


Definition decideOL_boolMemo (g d: AnTerm): bool := fst (decideOL_boolM (anSize g + anSize d) g d []).

Definition decideOL_bool_simp (g d: AnTerm): bool := decideOL_bool (anSize g + anSize d) g d.


Definition correctMemoMap (l: MemoMap) :=  forall g d, 
  match find (g, d) l with
  | Some (_, true) => forall n, (n >= anSize g + anSize d) -> (decideOL_bool n g d = true)
  | _ => True
  end.


Require Import Coq.Logic.FunctionalExtensionality.

Lemma let_if (A: MemoMapBool) memo : (let (b, m) := A memo in if b then (true, m) else (false, m)) = A memo.
Proof.
  destruct (A memo). destruct b; auto.
Qed.

Theorem AndMemo_Mfalse_r A l: fst ((A &&& Mfalse) l) = fst (Mfalse l).
Proof.
  cbv. destruct (A l); destruct b; simpl; auto.
Qed.

Theorem OrMemo_Mfalse_r A: (A ||| Mfalse) = A .
Proof. 
  apply functional_extensionality. intro. cbv. rewrite let_if. auto.
Qed.

Theorem AndMemo_Mfalse_l A: (Mfalse &&& A) = Mfalse.
Proof.
  apply functional_extensionality. intro. cbv. destruct (A x); destruct b; auto.
Qed.

Theorem OrMemo_Mfalse_l A: (Mfalse ||| A) = A.
Proof. 
  apply functional_extensionality. intro. cbv. auto.
Qed.


Lemma MemoKey_eqdec_refl T1 x y (A B: T1) : x = y -> (if MemoKey_eqdec x y then A else B) = A.
Proof. 
  intro. destruct (MemoKey_eqdec x y); congruence.
Qed.

Lemma MemoKey_eqdec_refl2 T1 x y (A B: T1) : x <> y -> (if MemoKey_eqdec y x then A else B) = B.
Proof. 
  intro. destruct (MemoKey_eqdec y x); congruence.
Qed.

Lemma SplitAndEq a b c d: a = c -> b = d -> (a && b = c && d).
Proof.
  intros. subst. auto.
Qed.

Lemma SplitOrEq a b c d: a = c -> b = d -> (a || b = c || d).
Proof.
  intros. subst. auto.
Qed.

Ltac dest g := destruct g; try congruence.

Theorem decideOL_bool_big_fuel  : forall n n0 g d, (n >= anSize g + anSize d) -> ( n0 >= anSize g + anSize d) -> decideOL_bool n g d = decideOL_bool n0 g d.
Proof.
  induction n. intros. pose proof anSizePositive g; pose proof anSizePositive d. lia.
  induction n0. intros. pose proof anSizePositive g; pose proof anSizePositive d. lia.

  intros. dest g; dest d; (try dest t0); (try dest t); simpl; auto.
  all: repeat rewrite Bool.orb_false_r. 
  all: repeat apply SplitAndEq; repeat apply SplitOrEq; try (apply IHn; simpl in *; lia).
Qed.

Lemma fst_let_simpl {T1} {T2} (A: T1 * T2) (c: T1 -> T2 -> T2) : fst (let (b, m) := A in (b, c b m)) = fst A.
Proof.
  destruct A. auto.
Qed.

Lemma snd_let_simpl {T1} {T2} (A: T1 * T2) (c: T1 -> T2 -> T2) : snd (let (b, m) := A in (b, c b m )) = c (fst A) (snd A).
Proof.
  destruct A. auto.
Qed.

Lemma correctMemoMap_second_let : 
  forall (A: bool * MemoMap) g d,  
  correctMemoMap ((g, d, fst A) :: (snd A)) ->
  correctMemoMap (snd (let (b, m) := A in (b, (g, d, b) :: m))).
Proof.
  intros. rewrite snd_let_simpl. auto.
Qed.



Lemma correctMemoAdditionEq2 n g d l e : 
  (n >= anSize g + anSize d) -> 
  correctMemoMap l -> 
  (e = true -> decideOL_bool n g d = true) -> 
  correctMemoMap ((g, d, e) :: l).
Proof.
  intros. unfold correctMemoMap. intros.
  unfold find. fold find. destruct (MemoKey_eqdec (g0, d0) (fst (g, d, decideOL_bool n g d))).
  - rewrite MemoKey_eqdec_refl; auto. destruct (decideOL_bool n g d) eqn: res; simpl in *. all:  destruct e; simpl in *; auto.
    intros. simpl in *.  assert (g0 = g). congruence. assert (d0 = d). congruence. subst. auto. rewrite (decideOL_bool_big_fuel n0 n); auto. exfalso. auto with *.
  - rewrite MemoKey_eqdec_refl2. 2: auto. apply H0.
Qed.


Ltac destSimp g := destruct g; repeat rewrite OrMemo_Mfalse_r; try (simpl; congruence).



Lemma destroy_triplet_equality {T1} {T2} {T3} (a:T1) (b:T2) (c d: T3) : c = d -> (a, b, c) = (a, b, d).
Proof.
  intros. subst. auto.
Qed.


Theorem decideOLBoolMemoCorrect : 
  forall n g d l, 
  (n >= anSize g + anSize d) -> 
  (correctMemoMap l) -> 
  (correctMemoMap (snd (decideOL_boolM n g d l))) /\
  (((fst (decideOL_boolM n g d l)) = true) ->  (decideOL_bool n g d) = true).
Proof.
  induction n.
  - intros. split. 
    + intros. dest g; dest d; simpl in *; lia.
  
    + simpl in *. unfold correctMemoMap in *. specialize (H0 g d).
      destruct (find (g, d) l).
      destruct p; simpl in *. destruct b. subst. specialize (H0 0 H). simpl in *. congruence. auto. auto.


  - intros. split.
    + simpl. pose proof H0. unfold correctMemoMap in H0.  specialize (H0 g d).
      destruct (find (g, d) l) eqn: res; simpl in *. destruct p; simpl in *. auto.
      destSimp g; destSimp d; (try destSimp t0); (try destSimp t).

      all: apply correctMemoMap_second_let.  all: repeat rewrite OrMemo_Mfalse_r; repeat rewrite OrMemo_Mfalse_l; repeat rewrite AndMemo_Mfalse_l. 
   
      Ltac rewriteOr x y l:= 
        assert ((x ||| y) l = let (b, m) := x l in if b then (true, m) else (y m) ) as rew_first_or; (only 1: reflexivity); rewrite rew_first_or in *; clear rew_first_or.
      Ltac rewriteAnd x y l:= 
        assert ((x &&& y) l = let (b, m) := x l in if b then (y m) else (false, m) ) as rew_first_and; (only 1: reflexivity); rewrite rew_first_and in *; clear rew_first_and.

      (* recursively prove goals of the form 
            correctMemoMap (snd (decideOL_boolM n g1 d1 ||| (decideOL_boolM n g2 d2||| (decideOL_boolM n g3 d3 ||| ... ))) )
        and
            fst ( (decideOL_boolM n g1 d1 ||| (decideOL_boolM n g2 d2||| (decideOL_boolM n g3 d3 ||| ... ))) l) =
                        (decideOL_bool n g1 d1 ||| (decideOL_bool n g2 d2||| (decideOL_bool n g3 d3 ||| ... )))
        as well as conjunctions
      *)
      Ltac reduceAndOr rest IHn l H :=
        let IHn_ := (fresh "IHn") in let IHn_snd := (fresh "IHn_snd") in 
        let IHn_fst := (fresh "IHn_fst") in let HS_ := (fresh "HS") in 
        let b_ := (fresh "b") in let l_ := (fresh "l") in
          lazymatch rest with 
          | ?op (decideOL_boolM ?n ?g ?d) ?rest2 => 
            try rewriteOr (decideOL_boolM n g d) rest2 l;
            try rewriteAnd (decideOL_boolM n g d) rest2 l;
            pose proof IHn as IHn_; specialize (IHn_ g d l);  simpl in *;
            assert (n >= anSize g + anSize d) as HS_; simpl; (try lia); specialize (IHn_ HS_ H); destruct IHn_ as [IHn_snd IHn_fst];
            destruct (decideOL_boolM n g d l)  as [ b_ l_];
            destruct b_; simpl in *; auto;
            intros;
            repeat rewrite Bool.orb_false_r;  repeat rewrite OrMemo_Mfalse_r; repeat rewrite OrMemo_Mfalse_l; repeat rewrite AndMemo_Mfalse_l;
            match goal with | [ |- (_ -> _) ] => intro  | _ => idtac end;
            try (rewrite IHn_fst; simpl; repeat rewrite Bool.orb_true_r; auto;  fail);
            try (apply Bool.orb_true_iff; right);
            try (apply Bool.andb_true_iff; split);
            try (eapply IHn; simpl in *; eauto; lia); 
            try (eapply IHn_fst; simpl in *; eauto; lia); 
            reduceAndOr rest2 IHn l_ IHn_snd;
            idtac
          | _ => 
            simpl in *; repeat rewrite Bool.orb_false_r; auto;
            try (eapply IHn; simpl in *; eauto; lia)
          | _ => fail "unknown shape" rest
          end.

      all: try (lazymatch goal with
      | [H : correctMemoMap ?l |- 
          correctMemoMap ( (?g, ?d, fst (?rest ?l)) :: snd (?rest ?l)) ] => 
        apply (correctMemoAdditionEq2 (S n) g d); only 1: (simpl in *; lia);
        reduceAndOr rest IHn l H;
        idtac
      | _ => idtac
      end).

      (* Need to do the second half of the proof, which could be the same as the first *)
    + Opaque decideOL_bool. simpl. pose proof H0. unfold correctMemoMap in H0.  specialize (H0 g d).
      destruct (find (g, d) l) eqn: res; simpl in *. destruct p; simpl in *. 
      * destruct b eqn:b_eq; simpl in *; intro; auto; try congruence.
      * Transparent decideOL_bool. destSimp g; destSimp d; (try destSimp t0); (try destSimp t).
        all: rewrite fst_let_simpl; simpl in *; repeat rewrite Bool.orb_false_r; repeat rewrite OrMemo_Mfalse_r; repeat rewrite OrMemo_Mfalse_l.
        all: try ( apply IHn; auto; simpl in *; lia).
        all: try (lazymatch goal with
            | [H : correctMemoMap ?l |- 
                fst (?rest ?l) = true -> _ ] => 
              reduceAndOr rest IHn l H
            | _ => idtac
            end).
Qed.



  (* Reflection: solve goals using the algorithm in arbitrary Ortholattice *)


 (* If the algorithms outputs True, then g is semanticaly smaller than d.*)
Theorem decideOLBoolMemoCorrect2 : forall g d, (decideOL_boolMemo g d) = true -> AnLeq g d.
Proof. 
  intros. assert (squash (OLProof (g, d))). apply decideOLBoolCorrect with (anSize g + anSize d). 
  generalize H. apply decideOLBoolMemoCorrect. auto; lia. unfold correctMemoMap. simpl in *. auto.
  destruct H0. apply (Soundness (g, d)). auto.
Qed.


Theorem reduceToAlgoMemo {OL: Ortholattice} : forall t1 t2 f, (decideOL_boolMemo (L t1) (R t2)) = true -> ((eval t1 f) <= (eval t2 f)).
Proof.
  intros. assert (AnLeq  (L t1) (R t2)). all: auto using decideOLBoolMemoCorrect2.
Qed.


Ltac solveOLMemo OL := 
  reify_goal OL; apply reduceToAlgoMemo; auto; vm_compute; (try reflexivity).



Example test1 {OL: Ortholattice} : forall a,  a <= a.
Proof.
  intro. 
  solveOLMemo OL.
Qed.

Example test2 {OL: Ortholattice} : forall a,  a == (a ∩ a).
Proof.
  intro. 
  solveOLMemo OL.
Qed.

Example test3 {OL: Ortholattice} a b c: 
  ¬(b ∪ ¬(c ∩ ¬b) ∪ a) <= (¬a ∪ ¬(b ∩ ¬a)).
Proof.
  intros. 
  solveOLMemo OL.
Qed.



Example test4 : forall a: (@A BoolOL),  a <= (a || a).
Proof.
  intro.
  solveOLMemo BoolOL.
Qed.



Example test5 : forall a: (@A BoolOL), Bool.le a (andb a a).
Proof.
  intro. 
  solveOLMemo BoolOL.
Qed.


Example test6 : forall a b : bool,   ( a ∩ (neg a)) <= b.
Proof.
  intros.
  solveOLMemo BoolOL.
Qed.


Example test7 : forall a b : bool,  Bool.le (andb a (negb a)) b.
Proof.
  intros. 
  solveOLMemo BoolOL.
Qed.


Example test8 : forall a b c: bool,  (a ∩ (negb a)) <= (a || (b && c)).
Proof.
  intros. 
  solveOLMemo BoolOL.
Qed.