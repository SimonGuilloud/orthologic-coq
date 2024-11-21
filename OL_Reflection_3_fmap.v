Require Import NArith.
Require Import OL_Theory.


Require Import OL_Reflection_1_base.

Require Import Setoid Morphisms.
Require Import Lia.
Require Import Coq.Arith.Bool_nat.


Open Scope bool_scope.
Import List.
Import ListNotations.





Fixpoint compare_Term (x y : Term): comparison :=
  match x, y with
  | Var n1, Var n2 => Pos.compare n1 n2
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
  all: firstorder using Pos.compare_eq_iff.
Qed.

Lemma compare_Term_eq_iff: forall x y: Term, compare_Term x y = Eq <-> x = y.
Proof.
  split; [ | intros; subst; eauto using compare_Term_refl ].
  revert x y; induction x; destruct y; simpl; try congruence;
    repeat match goal with
      | [ H: forall _, _ = _ |- _ ] => rewrite H
      end.
  all: firstorder (try congruence) using Pos.compare_eq_iff, Pos.compare_antisym; auto using xH. (* TODO *)
  all: destruct compare_Term eqn:Hx; try congruence; simpl; f_equal; intuition.
Qed.

Lemma compare_Term_antisym: forall x y: Term, compare_Term y x = CompOpp (compare_Term x y).
Proof.
  induction x; destruct y; simpl;
    repeat match goal with
      | [ H: forall _, _ = _ |- _ ] => rewrite H
      end.
  all: firstorder using Pos.compare_antisym.
  all: destruct compare_Term; simpl; reflexivity.
Qed.

Lemma compare_Term_antisym_iff: forall x y c, compare_Term x y = c <-> compare_Term y x = CompOpp c.
Proof.
  intros; rewrite compare_Term_antisym.
  destruct compare_Term, c; simpl; intuition congruence.
Qed.

Lemma nat_compare_trans: forall x y z: positive,
    (x ?= y = Lt)%positive ->
    (y ?= z = Lt)%positive ->
    (x ?= z = Lt)%positive.
Proof.
  intros ???.
  rewrite !Pos.compare_lt_iff.
  apply Pos.lt_trans.
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
| None => (match fuel with
  | 0 => (false, memo) 
  | S n => let (b, m) :=
    (* Guaranteed sufficent cases. *)
      match (g, d) with 
      | (L (Var a), R (Var b) )  => Mbool (Pos.eqb a b) (* Hyp *)
      (*| (L (Meet a b), N) => decideOL_boolM n (L a) (L b) (* LeftAnd1-2 *)*)
      (*| (N, R (Join a b)) => decideOL_boolM n (R a) (R b) (* RightOr1-2 *)*)
      | (L (Join a b), _) => (decideOL_boolM n (L a) d) &&& (decideOL_boolM n (L b) d) (* LeftOr *)
      | (L (Not a), _) => decideOL_boolM n (R a) d (* LeftNot *)
      | (_, R (Meet a b)) => (decideOL_boolM n g (R a)) &&& (decideOL_boolM n g (R b)) (* RightAnd *)
      | (_, R (Not a)) => decideOL_boolM n g (L a) (* RightNot *)
          (* Swap cases *)
      | (R (Var a), L (Var b) )  => Mbool (Pos.eqb b a) (* Hyp *)
      (*| (N, L (Meet a b)) => decideOL_boolM n (L a) (L b) (* LeftAnd1-2 *)*)
      (*| (R (Join a b), N) => decideOL_boolM n (R a) (R b) (* RightOr1-2 *)*)
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
        end |||(
        match d with (* RightOr2 d*)
        | R (Join a b) => decideOL_boolM n g (R b)
        | _ => Mfalse
        end |||(
        match (g, d) with
        | (N, L(_)) => decideOL_boolM n d d
        | (N, R(_)) => decideOL_boolM n d d
        | (L(_), N) => decideOL_boolM n g g
        | (R(_), N) => decideOL_boolM n g g
        | _ => Mfalse
        end
        ))))))))))
      end (AnTermPairAVLMap.add (g, d) false memo)
  in (b, AnTermPairAVLMap.add (g, d) b m) end)
end.

Definition decideOL_boolMemo (g d: AnTerm): bool :=
  fst (decideOL_boolM ((anSize g * anSize d) + 4) g d (AnTermPairAVLMap.empty bool)).

Definition correctMemoMap (l: MemoMap) :=  forall g d, 
  match M.find (g, d) l with
  | Some true => exists n,  (decideOL_bool n g d = true)
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

(*
Lemma correctMemoAdditionEq2 n g d l e : (n >= anSize g + anSize d) -> correctMemoMap l -> (e = true -> decideOL_bool n g d = true)  -> correctMemoMap (AnTermPairAVLMap.add (g, d) e l).
Proof.
  unfold correctMemoMap; intros Hge Hok He *.
  rewrite F.add_o; destruct F.eq_dec as [(Heq1%compare_AnTerm_eq, Heq2%compare_AnTerm_eq) | Hneq ];
    simpl in *; subst.
  - destruct e; intuition eauto using decideOL_bool_big_fuel.
  - apply Hok.
Qed.*)

Lemma correctMemoAdditionEq2 g d l e : 
  (*(n >= anSize g + anSize d) -> *)
  correctMemoMap l -> 
  (e = true -> exists n, decideOL_bool n g d = true) -> 
  correctMemoMap (AnTermPairAVLMap.add (g, d) e l).
Proof.
  unfold correctMemoMap; intros Hok He *.
  rewrite F.add_o; destruct F.eq_dec as [(Heq1%compare_AnTerm_eq, Heq2%compare_AnTerm_eq) | Hneq ].
  - destruct e; auto. simpl in *; subst; apply He, reflexivity.
  - simpl in *. apply Hok.
Qed.


Ltac destSimp g := destruct g; repeat rewrite OrMemo_Mfalse_r; try (simpl; congruence).



Lemma destroy_triplet_equality {T1} {T2} {T3} (a:T1) (b:T2) (c d: T3) : c = d -> (a, b, c) = (a, b, d).
Proof.
  intros. subst. auto.
Qed.

Lemma correctMemoMap_false g d l: correctMemoMap l -> correctMemoMap ( AnTermPairAVLMap.add (g, d) false l).
Proof.
  intros. unfold correctMemoMap. intros. rewrite F.add_o; destruct F.eq_dec as [(Heq1%compare_AnTerm_eq, Heq2%compare_AnTerm_eq) | Hneq ]; auto.
  simpl in *. apply H.
Qed.

Lemma decideOL_bool_monotonic : forall (n2 n1: nat) g d, n2 >= n1 -> decideOL_bool n1 g d = true -> decideOL_bool n2 g d = true.
Proof.
  induction n2.
  - intros. simpl in *. assert (n1 = 0). lia. subst. simpl in *. congruence.
  - intros. destruct n1. simpl in *; congruence. destruct g as [ | t | t ]; try destruct t.
    all: try destruct d as [ | t0 | t0 ]; try destruct t0; simpl; simpl in H0.
      all: repeat rewrite Bool.orb_false_r in *; repeat rewrite Bool.orb_true_iff in *; repeat rewrite Bool.andb_true_iff in *; auto.
      all: repeat match goal with
      | [H: _ \/ _ |- _] => destruct H; only 1: left; only 2: right
      | [H: _ /\ _ |- _] => destruct H; split
      | _ => idtac
      end. all: apply (IHn2 n1); try lia; auto.
Qed.

Theorem decideOLBoolFmapCorrect : 
  forall n g d l, 
  (correctMemoMap l) -> 
  (correctMemoMap (snd (decideOL_boolM n g d l))) /\
  (((fst (decideOL_boolM n g d l)) = true) ->  exists n0, (decideOL_bool n0 g d) = true).
Proof.
  induction n.
  - intros. split. 
    + intros. pose proof (H g d). simpl in *.  destruct M.find; simpl in *; auto.
    + specialize (H g d). simpl in *.
      destruct M.find; intros; simpl in *; subst; congruence.

  - intros. split.
    + simpl. pose proof H. unfold correctMemoMap in H0.  specialize (H0 g d).
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
        let IHn_fst := (fresh "IHn_fst") in let n0 := (fresh "n0") in 
        let b_ := (fresh "b") in let l_ := (fresh "l") in let found := (fresh "found") in
          lazymatch rest with 
          | (decideOL_boolM ?n ?g ?d) ||| ?rest2 => 
            try rewriteOr (decideOL_boolM n g d) rest2 l;
            pose proof (IHn g d l H) as IHn_; simpl in *; destruct IHn_ as [IHn_snd IHn_fst];
            destruct (decideOL_boolM n g d l)  as [ b_ l_] eqn: found;
            destruct b_; simpl in *; auto;
            intros;
            try(destruct IHn_fst as [n0 IHn_fst]; auto; exists (S n0); eauto);
            simpl in *;
            repeat rewrite Bool.orb_false_r;
            repeat rewrite OrMemo_Mfalse_r;
            repeat rewrite OrMemo_Mfalse_l;
            repeat rewrite AndMemo_Mfalse_l;
            match goal with | [ |- (_ -> _) ] => intro  | _ => idtac end;
            try congruence;
            try (apply Bool.orb_true_iff; left; congruence);
            try (apply Bool.orb_true_iff; right);
            try (eapply IHn; simpl in *; eauto; fail); 
            try (eapply IHn_fst; simpl in *; eauto; fail);
            try (rewrite IHn_fst; simpl; repeat rewrite Bool.orb_true_r; auto;  fail);
            reduceAndOr rest2 IHn l_ IHn_snd;
            idtac
          | (decideOL_boolM ?n ?g ?d) &&& ?rest2 => 
            try rewriteAnd (decideOL_boolM n g d) rest2 l;
            pose proof (IHn g d l H) as IHn_; simpl in *; destruct IHn_ as [IHn_snd IHn_fst];
            destruct (decideOL_boolM n g d l)  as [ b_ l_] eqn: found;
            destruct b_; simpl in *; auto;
            intros; try congruence;
            match goal with
            | [ HH: true = true -> _ |- _ ]=> destruct IHn_fst as [n0 IHn_fst]; auto; idtac
            | [ HH: false = true -> _ |- _ ]=> clear IHn_fst
            | _ => idtac
            end;
            simpl in *;
            repeat rewrite Bool.orb_false_r;
            repeat rewrite OrMemo_Mfalse_r;
            repeat rewrite OrMemo_Mfalse_l;
            repeat rewrite AndMemo_Mfalse_l;
            try (apply Bool.andb_true_iff; split);
            try (eapply IHn; simpl in *; eauto; fail); 
            try (eapply IHn_fst; simpl in *; eauto; fail);
            try (rewrite IHn_fst; simpl; repeat rewrite Bool.orb_true_r; auto;  fail);
            reduceAndOr rest2 IHn l_ IHn_snd;
            idtac
          | decideOL_boolM ?n ?g ?d =>  
            simpl in *; repeat rewrite Bool.orb_false_r; simpl in *; auto; intros; try congruence;
            try (apply IHn; simpl in *; eauto; congruence);
            pose proof (IHn g d l H) as IHn_; simpl in *; destruct IHn_ as [IHn_snd IHn_fst]; 
            destruct IHn_fst as [n0 IHn_fst]; auto;
            lazymatch goal with
            | [ J1: decideOL_bool ?m1 _ _ = true, J2: decideOL_bool ?m2 _ _ = true |- _ ] => 
                exists (S (Nat.max m1 m2)); simpl; apply Bool.andb_true_iff; split; 
                only 1: (apply (decideOL_bool_monotonic (Nat.max m1 m2) m1); try lia); 
                only 2: (apply (decideOL_bool_monotonic (Nat.max m1 m2) m2); try lia);
                idtac
            | [ J1: decideOL_bool ?m1 _ _ = true |- _ ] =>  exists (S m1); simpl
            | _ => idtac
            end;
            repeat rewrite Bool.orb_false_r;
            repeat (apply Bool.orb_true_iff; right); eauto;
            idtac
          | Mfalse => simpl in *; auto; intros; congruence;
            idtac
          | (Mbool _) => intros; simpl in *; auto; exists 1; simpl; auto; intros; congruence
          | _ => fail "unknown shape" rest
          end. idtac.

      all: try (lazymatch goal with
      | [H : correctMemoMap ?l |- 
        correctMemoMap (_ (?g, ?d) (fst (?rest (_ ?k ?v ?l))) (snd (?rest (_ ?k ?v ?l)))) ] =>
        apply (correctMemoAdditionEq2 g d);
        let H0 := (fresh "H0") in
        pose proof (correctMemoMap_false g d l H) as H0;
        reduceAndOr rest IHn (AnTermPairAVLMap.add k v l) H0;
        idtac
      | _ => fail "unknown shape"
      end; fail).

    + Opaque decideOL_bool. simpl. pose proof H as H0. unfold correctMemoMap in H0.  specialize (H0 g d).
      destruct (M.find (g, d) l) eqn: res; simpl in *.
      * destruct b eqn:b_eq; simpl in *; intro; auto; try congruence.
      * Transparent decideOL_bool. destSimp g; destSimp d; (try destSimp t0); (try destSimp t).
        all: rewrite fst_let_simpl; simpl in *; repeat rewrite Bool.orb_false_r; repeat rewrite OrMemo_Mfalse_r; repeat rewrite OrMemo_Mfalse_l.
        all: try ( apply IHn; auto; simpl in *; lia).
        all: try (lazymatch goal with
          | [H : correctMemoMap ?l |- 
            (fst (?rest (_ ?k ?v ?l))) = true -> _ ] =>
            let H0 := (fresh "H0") in
            epose proof (correctMemoMap_false _ _ l H) as H0;
            reduceAndOr rest IHn (AnTermPairAVLMap.add k v l) H0
          | [H : correctMemoMap ?l |- ?inner = true -> _ ] => 
            reduceAndOr (Mbool inner) IHn l H
          | _ => fail "unknown shape"
            idtac
          end; fail).
Qed.


Theorem decideOLBoolFmapCorrect2 : forall g d, (decideOL_boolMemo g d) = true -> AnLeq g d.
Proof. 
  intros. assert (squash (OLProof (g, d))). 
  pose proof (decideOLBoolFmapCorrect (anSize g * anSize d + 4) g d (AnTermPairAVLMap.empty bool)). 
  destruct H0. unfold correctMemoMap; simpl in *; auto. destruct H1 as [n0 H1]; auto. apply decideOLBoolCorrect with n0; auto.
  destruct H0. apply (Soundness (g, d)). auto.
Qed.


Theorem reduceToAlgoFmap {OL: Ortholattice} : forall t1 t2 f, (decideOL_boolMemo (L t1) (R t2)) = true -> ((eval t1 f) <= (eval t2 f)).
Proof.
  intros. assert (AnLeq  (L t1) (R t2)). all: auto using decideOLBoolFmapCorrect2.
Qed.

Ltac solveOLFmap OL := 
  reify_goal OL; apply reduceToAlgoFmap; auto; vm_compute; (try reflexivity).

Example test1 {OL: Ortholattice} : forall a,  a <= a.
Proof.
  intro. 
  solveOLFmap OL.
Qed.

Example test2 {OL: Ortholattice} : forall a,  a == (a ∩ a).
Proof.
  intro. 
  solveOLFmap OL.
Qed.

Example test3 {OL: Ortholattice} a b c: 
  ¬(b ∪ ¬(c ∩ ¬b) ∪ a) <= (¬a ∪ ¬(b ∩ ¬a)).
Proof.
  intros. 
  solveOLFmap OL.
Qed.



Example test4 : forall a: (@A BoolOL),  a <= (a || a).
Proof.
  intro.
  solveOLFmap BoolOL.
Qed.



Example test5 : forall a: (@A BoolOL), Bool.le a (andb a a).
Proof.
  intro. 
  solveOLFmap BoolOL.
Qed.


Example test6 : forall a b : bool,   ( a ∩ (neg a)) <= b.
Proof.
  intros.
  solveOLFmap BoolOL.
Qed.


Example test7 : forall a b : bool,  Bool.le (andb a (negb a)) b.
Proof.
  intros. 
  solveOLFmap BoolOL.
Qed.


Example test8 : forall a b c: bool,  (a ∩ (negb a)) <= (a || (b && c)).
Proof.
  intros. 
  solveOLFmap BoolOL.
Qed.
