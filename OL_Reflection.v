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

Fixpoint compare_Term (x y : Term): comparison :=
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

Lemma compare_Term_refl: forall x: Term, compare_Term x x = Eq.
Proof.
  induction x; simpl;
    repeat match goal with
      | [ H: _ = _ |- _ ] => rewrite H
      end.
  all: firstorder using Nat.compare_eq_iff.
Qed.

Lemma compare_Term_eq_iff: forall x y: Term, compare_Term x y = Eq <-> x = y.
Proof.
  split; [ | intros; subst; eauto using compare_Term_refl ].
  revert x y; induction x; destruct y; simpl; try congruence;
    repeat match goal with
      | [ H: forall _, _ = _ |- _ ] => rewrite H
      end.
  all: firstorder using Nat.compare_eq_iff, Nat.compare_antisym.
  all: destruct compare_Term eqn:Hx; try congruence; simpl; f_equal; intuition.
Qed.

Lemma compare_Term_antisym: forall x y: Term, compare_Term y x = CompOpp (compare_Term x y).
Proof.
  induction x; destruct y; simpl;
    repeat match goal with
      | [ H: forall _, _ = _ |- _ ] => rewrite H
      end.
  all: firstorder using Nat.compare_antisym.
  all: destruct compare_Term; simpl; reflexivity.
Qed.

Lemma compare_Term_antisym_iff: forall x y c, compare_Term x y = c <-> compare_Term y x = CompOpp c.
Proof.
  intros; rewrite compare_Term_antisym.
  destruct compare_Term, c; simpl; intuition congruence.
Qed.

Lemma nat_compare_trans: forall x y z: nat,
    x ?= y = Lt ->
    y ?= z = Lt ->
    x ?= z = Lt.
Proof.
  intros ???.
  rewrite !Nat.compare_lt_iff.
  apply Nat.lt_trans.
Qed.

Lemma compare_Term_lt_trans: forall x y z: Term,
    compare_Term x y = Lt ->
    compare_Term y z = Lt ->
    compare_Term x z = Lt.
Proof.
  induction x; destruct y, z; simpl in *; try congruence;
    repeat match goal with
      | [ H: forall _, _ = _ |- _ ] => rewrite H
      end.

  all: firstorder using nat_compare_trans.
  all: destruct (compare_Term x1) eqn:Hx1, (compare_Term x2) eqn:Hx2; try congruence.
  all: destruct (compare_Term y1) eqn:Hy1; try congruence.

  all: repeat match goal with
         | [ H: _ = _ |- _ ] => rewrite H
         | [ H: compare_Term _ _ = Eq |- _ ] => apply compare_Term_eq_iff in H; subst
         | [  |- context[compare_Term ?x ?x] ] => rewrite compare_Term_refl
         end.
  all: erewrite ?IHx1 by eauto; eauto.
Qed.

Lemma compare_Term_trans: forall c x y z,
    compare_Term x y = c ->
    compare_Term y z = c ->
    compare_Term x z = c.
Proof.
  destruct c; intros ???.
  - rewrite !compare_Term_eq_iff; congruence.
  - apply compare_Term_lt_trans.
  - rewrite (compare_Term_antisym_iff x y), (compare_Term_antisym_iff y z), (compare_Term_antisym_iff x z).
    simpl; eauto using compare_Term_lt_trans.
Qed.

Lemma compare_Term_eq_sym: forall x y: Term, compare_Term x y = Eq -> compare_Term y x = Eq.
Proof.
  intros * Heq; rewrite compare_Term_antisym, Heq; reflexivity.
Qed.

Lemma compare_Term_eq_trans: forall x y z: Term,
    compare_Term x y = Eq ->
    compare_Term y z = Eq ->
    compare_Term x z = Eq.
Proof.
  eauto using compare_Term_trans.
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

Definition compare_Term_eq_impl :=
  (fun x y => proj1 (compare_Term_eq_iff x y)).

Definition compare_Term_antisym_impl :=
  (fun x y c => proj1 (compare_Term_antisym_iff x y c)).

Hint Resolve compare_Term_refl compare_Term_antisym compare_Term_trans
  compare_Term_antisym_impl compare_Term_eq_sym compare_Term_eq_trans compare_Term_eq_impl
  : compare_Term.

Ltac compare_AnTerm_t :=
  repeat match goal with
    | _ => progress (simpl; subst)
    | [  |- forall _: AnTerm, _ ] => intros x; destruct x
    | _ => intro
    end;
  congruence || eauto using f_equal with compare_Term.

Lemma compare_AnTerm_refl: forall x: AnTerm, compare_AnTerm x x = Eq.
Proof. compare_AnTerm_t. Qed.

Lemma compare_AnTerm_eq: forall x y: AnTerm, compare_AnTerm x y = Eq -> x = y.
Proof. compare_AnTerm_t. Qed.

Lemma compare_AnTerm_antisym: forall x y: AnTerm, compare_AnTerm y x = CompOpp (compare_AnTerm x y).
Proof. compare_AnTerm_t. Qed.

Lemma compare_AnTerm_antisym_impl: forall x y c, compare_AnTerm x y = c -> compare_AnTerm y x = CompOpp c.
Proof. compare_AnTerm_t. Qed.

Lemma compare_AnTerm_trans: forall c x y z,
    compare_AnTerm x y = c ->
    compare_AnTerm y z = c ->
    compare_AnTerm x z = c.
Proof. compare_AnTerm_t. Qed.

Lemma compare_AnTerm_eq_sym: forall x y: AnTerm, compare_AnTerm x y = Eq -> compare_AnTerm y x = Eq.
Proof. compare_AnTerm_t. Qed.

Lemma compare_AnTerm_eq_trans: forall x y z: AnTerm,
    compare_AnTerm x y = Eq ->
    compare_AnTerm y z = Eq ->
    compare_AnTerm x z = Eq.
Proof. compare_AnTerm_t. Qed.

Require OrderedType OrderedTypeAlt.

Module AnTerm_as_OTA <: OrderedTypeAlt.OrderedTypeAlt.
  Definition t := AnTerm.
  Definition compare := compare_AnTerm.
  Definition compare_sym := compare_AnTerm_antisym.
  Definition compare_trans := compare_AnTerm_trans.
End AnTerm_as_OTA.

(* Legacy interface, but direct implementation may be useful for performance? *)
Module AnTerm_as_OT <: OrderedType.OrderedType.
  Definition t := AnTerm.

  Definition eq (x y: AnTerm) := compare_AnTerm x y = Eq.
  Definition lt (x y: AnTerm) := compare_AnTerm x y = Lt.

  Definition eq_refl : forall x : t, eq x x := compare_AnTerm_refl.
  Definition eq_sym : forall x y : t, eq x y -> eq y x := compare_AnTerm_eq_sym.
  Definition eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z := compare_AnTerm_eq_trans.
  Definition lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z := compare_AnTerm_trans Lt.

  Theorem lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof. unfold lt, eq; congruence. Qed.

  Theorem compare : forall x y : t, OrderedType.Compare lt eq x y.
  Proof.
    intros x y; destruct (compare_AnTerm x y) eqn:Hcmp;
      [ | | apply compare_AnTerm_antisym_impl in Hcmp; simpl in Hcmp ].
    all: econstructor; solve [unfold lt, eq; eassumption].
  Defined.

  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Proof.
    intros x y; destruct (compare_AnTerm x y) eqn:Hcmp; [ left | right.. ].
    all: unfold eq; congruence.
  Defined.
End AnTerm_as_OT.

Require MSets MSetAVL MSetFacts.

Module AnTerm_as_OOT := OrdersAlt.OT_from_Alt AnTerm_as_OTA.
Module AnTermAVL := MSetAVL.Make AnTerm_as_OOT.
Module AnTermPair_as_OOT := OrdersEx.PairOrderedType AnTerm_as_OOT AnTerm_as_OOT.
Module AnTermPairAVL := MSetAVL.Make AnTermPair_as_OOT.
Module AnTermPairAVLFacts := MSetFacts.Facts AnTermPairAVL.

Require Import FMapAVL FMapFacts.
Module AnTermPair_as_OT := OrderedTypeEx.PairOrderedType AnTerm_as_OT AnTerm_as_OT.
(* Module AnTermPair_as_OOT := OrdersAlt.Update_OT AnTermPair_as_OT. *)
(* Module AnTermPairAVL := MSetAVL.Make AnTermPair_as_OOT. *)
Module AnTermPairAVLMap := FMapAVL.Make AnTermPair_as_OT.
Module AnTermPairAVLMapFacts := FMapFacts.Facts AnTermPairAVLMap.

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
        end||(
        match d with (* RightOr2 d*)
        | R (Join a b) => decideOL_bool n g (R b)
        | _ => false
        end
        )))))))))
    end
    
    
  end.


Ltac recurse := simpl in *; lia.

Hint Constructors OLProof squash : olproof.

Hint Rewrite
  Bool.orb_false_r
  Bool.andb_true_iff Bool.orb_true_iff
  Nat.eqb_eq : rw_bool.

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

(* Memoized version of the above algorithm. 
  O(e^n) => O(n^5). Optimal is O(n^2). 
  Using Lists over HashMap: cost n^2.
  Using syntactic equality costs n, while in practice we only need pointer equality 
  (not even hash consing) *)



Definition MemoKey := (AnTerm * AnTerm)%type.

Definition MemoMap := AnTermPairAVLMap.t bool.

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

Infix "|||" := OrMemo (at level 50, left associativity).
Infix "&&&" := AndMemo (at level 40, left associativity).

Module M := AnTermPairAVLMap.
Module F := AnTermPairAVLMapFacts.

(* Module Import M := AnTermPairAVL. *)
(* Module Import F := AnTermPairAVLFacts. *)

Fixpoint decideOL_boolM (fuel: nat) (g d: AnTerm) (memo: MemoMap) : (bool * MemoMap) :=
match M.find (g, d) memo with
| Some b => (b, memo)
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
  end) in (b, AnTermPairAVLMap.add (g, d) b m)
end.

Definition decideOL_boolMemo (g d: AnTerm): bool :=
  fst (decideOL_boolM (anSize g + anSize d) g d (AnTermPairAVLMap.empty bool)).

Definition decideOL_bool_simp (g d: AnTerm): bool := decideOL_bool (anSize g + anSize d) g d.

Definition correctMemoMap (l: MemoMap) :=  forall g d, 
  match M.find (g, d) l with
  | Some true => forall n, (n >= anSize g + anSize d) -> (decideOL_bool n g d = true)
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
  correctMemoMap (AnTermPairAVLMap.add (g, d) (fst A) (snd A)) ->
  correctMemoMap (snd (let (b, m) := A in (b, AnTermPairAVLMap.add (g, d) b m))).
Proof.
  intros. rewrite snd_let_simpl. auto.
Qed.

Lemma comparison_eq_decidable {c0 c1: comparison} : Decidable.decidable (c0 = c1).
Proof. red; destruct c0, c1; intuition congruence. Qed.
(* [Heq1 | Heq2]%(Decidable.not_and _ _ comparison_eq_decidable) *)

Lemma correctMemoAdditionEq2 n g d l e : (n >= anSize g + anSize d) -> correctMemoMap l -> (e = true -> decideOL_bool n g d = true)  -> correctMemoMap (AnTermPairAVLMap.add (g, d) e l).
Proof.
  unfold correctMemoMap; intros Hge Hok He *.
  rewrite F.add_o; destruct F.eq_dec as [(Heq1%compare_AnTerm_eq, Heq2%compare_AnTerm_eq) | Hneq ];
    simpl in *; subst.
  - destruct e; intuition eauto using decideOL_bool_big_fuel.
  - apply Hok.
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
      destruct M.find.
      destruct b. subst. specialize (H0 0 H). simpl in *. congruence. auto. auto.


  - intros. split.
    + simpl. pose proof H0. unfold correctMemoMap in H0.  specialize (H0 g d).
      destruct M.find eqn: res; simpl in *. auto.
      destSimp g; destSimp d; (try destSimp t0); (try destSimp t).

      all: apply correctMemoMap_second_let.  all: rewrite ?OrMemo_Mfalse_r, ?OrMemo_Mfalse_l, ?AndMemo_Mfalse_l.
   
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

      all: (lazymatch goal with
      | [H : correctMemoMap ?l |- 
          correctMemoMap (AnTermPairAVLMap.add (?g, ?d) (fst (?rest ?l)) (snd (?rest ?l))) ] =>
        apply (correctMemoAdditionEq2 (S n) g d); only 1: (simpl in *; lia);
        reduceAndOr rest IHn l H;
        idtac
      | _ => idtac
      end).

      (* Need to do the second half of the proof, which could be the same as the first *)
    + Opaque decideOL_bool. simpl. pose proof H0. unfold correctMemoMap in H0.  specialize (H0 g d).
      destruct (M.find (g, d) l) eqn: res; simpl in *.
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


Theorem decideOLBoolSimpCorrect : forall g d, (decideOL_bool_simp g d) = true -> AnLeq g d.
Proof.
  intros. assert (squash (OLProof (g, d))). apply decideOLBoolCorrect in H; auto; lia.
  destruct H0. apply (Soundness (g, d)). auto.
Qed.


 (* If the algorithms outputs True, then g is semanticaly smaller than d.*)
Theorem decideOLBoolMemoCorrect2 : forall g d, (decideOL_boolMemo g d) = true -> AnLeq g d.
Proof. 
  intros. assert (squash (OLProof (g, d))). apply decideOLBoolCorrect with (anSize g + anSize d). 
  generalize H. apply decideOLBoolMemoCorrect. auto; lia. unfold correctMemoMap. simpl in *. auto.
  destruct H0. apply (Soundness (g, d)). auto.
Qed.





Theorem reduceToAlgo {OL: Ortholattice} : forall t1 t2 f, (decideOL_bool_simp (L t1) (R t2)) = true -> ((eval t1 f) <= (eval t2 f)).
Proof.
  intros. assert (AnLeq  (L t1) (R t2)). all: auto using decideOLBoolSimpCorrect.
Qed.

Theorem reduceToAlgoMemo {OL: Ortholattice} : forall t1 t2 f, (decideOL_boolMemo (L t1) (R t2)) = true -> ((eval t1 f) <= (eval t2 f)).
Proof.
  intros. assert (AnLeq  (L t1) (R t2)). all: auto using decideOLBoolMemoCorrect2.
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
  let S' := (eval simpl in S) with
      T' := (eval simpl in T) in
  let t1' := (reify_term OL S' l2) with
      t2' := (reify_term OL T' l2) in
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

Theorem example2 {OL: Ortholattice} a b c: 
  ¬(b ∪ ¬(c ∩ ¬b) ∪ a) <= (¬a ∪ ¬(b ∩ ¬a)).
Proof.
  intros. 
  solveOL OL.
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


Theorem test8 : forall a b : bool, a && negb a = negb b && (a && b).
Proof.
  intros. 
  solveOLMemo BoolOL.
Qed.

Theorem test9 : forall a b : bool, a && negb a = negb b && (a && b).
Proof.
  intros. 
  solveOL BoolOL.
Qed.

