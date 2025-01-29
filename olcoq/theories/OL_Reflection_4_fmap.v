Require Import NArith.
Require Import OL_Theory.


Require Import OL_Reflection_1_base.
Require Import OL_Reflection_2_opti.

Require Import Setoid Morphisms.
Require Import Lia.
Require Import Coq.Arith.Bool_nat.
Require Import Btauto.


Open Scope bool_scope.
Import List.
Import ListNotations.


Fixpoint compare_term (x y : Term): comparison :=
  match x, y with
  | Var n1, Var n2 => Pos.compare n1 n2
  | Var _, Meet _ _ => Lt
  | Var _, Join _ _ => Lt
  | Var _, Not _ => Lt
  | Meet _ _, Var _ => Gt
  | Meet l1 r1, Meet l2 r2 =>
      match compare_term l1 l2 with
      | Lt => Lt
      | Eq => compare_term r1 r2
      | Gt => Gt
      end
  | Meet _ _, Join _ _ => Lt
  | Meet _ _, Not _ => Lt
  | Join _ _, Var _ => Gt
  | Join _ _, Meet _ _ => Gt
  | Join l1 r1, Join l2 r2 =>
      match compare_term l1 l2 with
      | Lt => Lt
      | Eq => compare_term r1 r2
      | Gt => Gt
      end
  | Join _ _, Not _ => Lt
  | Not _, Var _ => Gt
  | Not _, Meet _ _ => Gt
  | Not _, Join _ _ => Gt
  | Not t1, Not t2 => compare_term t1 t2
  end.


Lemma compare_term_refl: forall x: Term, compare_term x x = Eq.
Proof.
  induction x; simpl;
    repeat match goal with
      | [ H: _ = _ |- _ ] => rewrite H
      end.
  all: firstorder using Pos.compare_eq_iff.
Qed.


Lemma compare_term_eq_iff: forall x y: Term, compare_term x y = Eq <-> x = y.
Proof.
  split; [ | intros; subst; eauto using compare_term_refl ].
  revert x y; induction x; destruct y; simpl; try congruence;
    repeat match goal with
      | [ H: forall _, _ = _ |- _ ] => rewrite H
      end.
  all: firstorder (try congruence) using Pos.compare_eq_iff, Pos.compare_antisym; auto using xH. (* TODO *)
  all: destruct compare_term eqn:Hx; try congruence; simpl; f_equal; intuition.
Qed.


Lemma compare_term_antisym: forall x y: Term, compare_term y x = CompOpp (compare_term x y).
Proof.
  induction x; destruct y; simpl;
    repeat match goal with
      | [ H: forall _, _ = _ |- _ ] => rewrite H
      end.
  all: firstorder using Pos.compare_antisym.
  all: destruct compare_term; simpl; reflexivity.
Qed.


Lemma compare_term_antisym_iff: forall x y c, compare_term x y = c <-> compare_term y x = CompOpp c.
Proof.
  intros; rewrite compare_term_antisym.
  destruct compare_term, c; simpl; intuition congruence.
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


Lemma compare_term_lt_trans: forall x y z: Term,
    compare_term x y = Lt ->
    compare_term y z = Lt ->
    compare_term x z = Lt.
Proof.
  induction x; destruct y, z; simpl in *; try congruence;
    repeat match goal with
      | [ H: forall _, _ = _ |- _ ] => rewrite H
      end.

  all: firstorder using nat_compare_trans.
  all: destruct (compare_term x1) eqn:Hx1, (compare_term x2) eqn:Hx2; try congruence.
  all: destruct (compare_term y1) eqn:Hy1; try congruence.

  all: repeat match goal with
         | [ H: _ = _ |- _ ] => rewrite H
         | [ H: compare_term _ _ = Eq |- _ ] => apply compare_term_eq_iff in H; subst
         | [  |- context[compare_term ?x ?x] ] => rewrite compare_term_refl
         end.
  all: erewrite ?IHx1 by eauto; eauto.
Qed.


Lemma compare_term_trans: forall c x y z,
    compare_term x y = c ->
    compare_term y z = c ->
    compare_term x z = c.
Proof.
  destruct c; intros ???.
  - rewrite !compare_term_eq_iff; congruence.
  - apply compare_term_lt_trans.
  - rewrite (compare_term_antisym_iff x y), (compare_term_antisym_iff y z), (compare_term_antisym_iff x z).
    simpl; eauto using compare_term_lt_trans.
Qed.


Lemma compare_term_eq_sym: forall x y: Term, compare_term x y = Eq -> compare_term y x = Eq.
Proof.
  intros * Heq; rewrite compare_term_antisym, Heq; reflexivity.
Qed.


Lemma compare_term_eq_trans: forall x y z: Term,
    compare_term x y = Eq ->
    compare_term y z = Eq ->
    compare_term x z = Eq.
Proof.
  eauto using compare_term_trans.
Qed.


Definition compare_anterm (x y: AnTerm) : comparison :=
  match x, y with
  | L n1, L n2 => compare_term n1 n2
  | L _, _ => Lt
  | _, L _ => Gt
  | R n1, R n2 => compare_term n1 n2
  | R _, _ => Lt
  | _, R _ => Gt
  | N, N => Eq
  end.


Definition compare_term_eq_impl :=
  (fun x y => proj1 (compare_term_eq_iff x y)).


Definition compare_term_antisym_impl :=
  (fun x y c => proj1 (compare_term_antisym_iff x y c)).

Hint Resolve compare_term_refl compare_term_antisym compare_term_trans
  compare_term_antisym_impl compare_term_eq_sym compare_term_eq_trans compare_term_eq_impl
  : compare_term.

Ltac compare_anterm_t :=
  repeat match goal with
    | _ => progress (simpl; subst)
    | [  |- forall _: AnTerm, _ ] => intros x; destruct x
    | _ => intro
    end;
  congruence || eauto using f_equal with compare_term.


Lemma compare_anterm_refl: forall x: AnTerm, compare_anterm x x = Eq.
Proof. compare_anterm_t. Qed.


Lemma compare_anterm_eq: forall x y: AnTerm, compare_anterm x y = Eq -> x = y.
Proof. compare_anterm_t. Qed.


Lemma compare_anterm_antisym: forall x y: AnTerm, compare_anterm y x = CompOpp (compare_anterm x y).
Proof. compare_anterm_t. Qed.


Lemma compare_anterm_antisym_impl: forall x y c, compare_anterm x y = c -> compare_anterm y x = CompOpp c.
Proof. compare_anterm_t. Qed.


Lemma compare_anterm_trans: forall c x y z,
    compare_anterm x y = c ->
    compare_anterm y z = c ->
    compare_anterm x z = c.
Proof. compare_anterm_t. Qed.


Lemma compare_anterm_eq_sym: forall x y: AnTerm, compare_anterm x y = Eq -> compare_anterm y x = Eq.
Proof. compare_anterm_t. Qed.


Lemma compare_anterm_eq_trans: forall x y z: AnTerm,
    compare_anterm x y = Eq ->
    compare_anterm y z = Eq ->
    compare_anterm x z = Eq.
Proof. compare_anterm_t. Qed.

Require OrderedType OrderedTypeAlt.

Module AnTerm_as_OTA <: OrderedTypeAlt.OrderedTypeAlt.
  Definition t := AnTerm.
  Definition compare := compare_anterm.
  Definition compare_sym := compare_anterm_antisym.
  Definition compare_trans := compare_anterm_trans.
End AnTerm_as_OTA.

(* Legacy interface, but direct implementation may be useful for performance? *)
Module AnTerm_as_OT <: OrderedType.OrderedType.
  Definition t := AnTerm.

  Definition eq (x y: AnTerm) := compare_anterm x y = Eq.
  Definition lt (x y: AnTerm) := compare_anterm x y = Lt.

  Definition eq_refl : forall x : t, eq x x := compare_anterm_refl.
  Definition eq_sym : forall x y : t, eq x y -> eq y x := compare_anterm_eq_sym.
  Definition eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z := compare_anterm_eq_trans.
  Definition lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z := compare_anterm_trans Lt.

  Theorem lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof. unfold lt, eq; congruence. Qed.

  Theorem compare : forall x y : t, OrderedType.Compare lt eq x y.
  Proof.
    intros x y; destruct (compare_anterm x y) eqn:Hcmp;
      [ | | apply compare_anterm_antisym_impl in Hcmp; simpl in Hcmp ].
    all: econstructor; solve [unfold lt, eq; eassumption].
  Defined.

  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Proof.
    intros x y; destruct (compare_anterm x y) eqn:Hcmp; [ left | right.. ].
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


Definition mor (left : MemoMapBool ) (right : MemoMapBool)  := fun (memo : MemoMap) => match left memo with
| (true, m) => (true, m)
| (false, m) => right m
end.


Definition mand (left : MemoMapBool ) (right : MemoMapBool)  := fun (memo : MemoMap) => match left memo with
| (true, m) => right m
| (false, m) => (false, m)
end.


Definition mbool b : MemoMapBool  := fun (memo: MemoMap) => (b, memo).
Definition mtrue := mbool true.
Definition mfalse := mbool false.

Infix "|||" := mor (at level 50, left associativity).
Infix "&&&" := mand (at level 40, left associativity).

Module M := AnTermPairAVLMap.
Module F := AnTermPairAVLMapFacts.

(* Module Import M := AnTermPairAVL. *)
(* Module Import F := AnTermPairAVLFacts. *)

Fixpoint decideOL_fmap (fuel: nat) (g d: AnTerm) (memo: MemoMap) : (bool * MemoMap) :=
  match M.find (g, d) memo with
  | Some b => (b, memo)
  | None => (match fuel with
    | 0 => (false, memo) 
    | S n => let (b, m) :=
      (match (g, d) with
      | (L (Var a), R (Var b) )  => mbool (Pos.eqb a b) (* Hyp *)
      | (R (Var a), L (Var b)) => mbool (Pos.eqb a b) (* Hyp *)
      | (L (Var a), L (Var b))  => mfalse
      | (R (Var a), R (Var b)) => mfalse
      | (L (Var a), N) => mfalse
      | (R (Var a), N) => mfalse
      | (N, L (Var a)) => mfalse
      | (N, R (Var a)) => mfalse
      | (L (Join a b), _) => decideOL_fmap n (L a) d &&& decideOL_fmap n (L b) d
      | (_, L (Join a b)) => decideOL_fmap n g (L a) &&& decideOL_fmap n g (L b)
      | (R (Meet a b), _) => decideOL_fmap n (R a) d &&& decideOL_fmap n (R b) d
      | (_, R (Meet a b)) => decideOL_fmap n g (R a) &&& decideOL_fmap n g (R b)
      | (L (Not a), _) => decideOL_fmap n (R a) d
      | (_, L (Not a)) => decideOL_fmap n g (R a)
      | (R (Not a), _) => decideOL_fmap n (L a) d
      | (_, R (Not a)) => decideOL_fmap n g (L a)
      | _ => (
        match g with 
        | L (Meet a b) => decideOL_fmap n (L a) d 
        | _ => mfalse
        end ||| (
        match g with 
        | L (Meet a b) => decideOL_fmap n (L b) d
        | _ => mfalse
        end ||| (
        match d with 
        | L (Meet a b) => decideOL_fmap n g (L a) 
        | _ => mfalse
        end ||| (
        match d with 
        | L (Meet a b) => decideOL_fmap n g (L b) 
        | _ => mfalse
        end ||| (
        match g with
        | R (Join a b) => decideOL_fmap n (R a) d
        | _ => mfalse
        end ||| (
        match g with
        | R (Join a b) => decideOL_fmap n (R b) d
        | _ => mfalse
        end ||| (
        match d with
        | R (Join a b) => decideOL_fmap n g (R a) 
        | _ => mfalse
        end ||| (
        match d with
        | R (Join a b) => decideOL_fmap n g (R b)
        | _ => mfalse
        end ||| (
        match d with 
        | N => decideOL_fmap n g g 
        | _ => mfalse
        end ||| (
        match g with 
        | N => decideOL_fmap n d d
        | _ => mfalse
        end  ||| (
        decideOL_fmap n g N ||| 
        decideOL_fmap n N d
        )))))))))))
      end) (AnTermPairAVLMap.add (g, d) false memo)
    in (b, AnTermPairAVLMap.add (g, d) b m) end)
end.


Definition decideOL_fmap_simp (g d: AnTerm): bool :=
  fst (decideOL_fmap ((anterm_size g * anterm_size d) + 4) g d (AnTermPairAVLMap.empty bool)).


Definition memomap_correct (l: MemoMap) :=  forall g d, 
  match M.find (g, d) l with
  | Some true => exists n,  (decideOL_opti n g d = true)
  | _ => True
  end.

Require Import Coq.Logic.FunctionalExtensionality.


Lemma let_if (A: MemoMapBool) memo : (let (b, m) := A memo in if b then (true, m) else (false, m)) = A memo.
Proof.
  destruct (A memo). destruct b; auto.
Qed.


Theorem mand_mfalse_r A l: fst ((A &&& mfalse) l) = fst (mfalse l).
Proof.
  cbv. destruct (A l); destruct b; simpl; auto.
Qed.


Theorem mor_mtrue_r A: (A ||| mfalse) = A .
Proof. 
  apply functional_extensionality. intro. cbv. rewrite let_if. auto.
Qed.


Theorem mand_mtrue_l A: (mfalse &&& A) = mfalse.
Proof.
  apply functional_extensionality. intro. cbv. destruct (A x); destruct b; auto.
Qed.


Theorem mor_mfalse_l A: (mfalse ||| A) = A.
Proof. 
  apply functional_extensionality. intro. cbv. auto.
Qed.


Lemma and_eq_split a b c d: a = c -> b = d -> (a && b = c && d).
Proof.
  intros. subst. auto.
Qed.


Lemma or_eq_split a b c d: a = c -> b = d -> (a || b = c || d).
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


Lemma memomap_correct_snd_unfold : 
  forall (A: bool * MemoMap) g d,  
  memomap_correct (AnTermPairAVLMap.add (g, d) (fst A) (snd A)) ->
  memomap_correct (snd (let (b, m) := A in (b, AnTermPairAVLMap.add (g, d) b m))).
Proof.
  intros. rewrite snd_let_simpl. auto.
Qed.


Lemma comparison_eq_decidable {c0 c1: comparison} : Decidable.decidable (c0 = c1).
Proof. 
  red; destruct c0, c1; intuition congruence. 
Qed.


Lemma memomap_correct_cons g d l e : 
  memomap_correct l /\
  (e = true -> exists n, decideOL_opti n g d = true) -> 
  memomap_correct (AnTermPairAVLMap.add (g, d) e l) /\ (e = true -> exists n, decideOL_opti n g d = true).
Proof.
  unfold memomap_correct; intro H1; destruct H1 as [Hok He]. split; auto. intros.
  rewrite F.add_o; destruct F.eq_dec as [(Heq1%compare_anterm_eq, Heq2%compare_anterm_eq) | Hneq ].
  - destruct e; auto. simpl in *; subst; apply He, reflexivity.
  - simpl in *. apply Hok.
Qed.


Ltac dest_simp g := destruct g; repeat rewrite mor_mtrue_r; try (simpl; congruence).


Lemma destroy_triplet_equality {T1} {T2} {T3} (a:T1) (b:T2) (c d: T3) : c = d -> (a, b, c) = (a, b, d).
Proof.
  intros. subst. auto.
Qed.


Lemma memomap_correct_false g d l: memomap_correct l -> memomap_correct ( AnTermPairAVLMap.add (g, d) false l).
Proof.
  intros. unfold memomap_correct. intros. rewrite F.add_o; destruct F.eq_dec as [(Heq1%compare_anterm_eq, Heq2%compare_anterm_eq) | Hneq ]; auto.
  simpl in *. apply H.
Qed.


Theorem decideOL_fmap_correct : 
  forall n g d l, 
  (memomap_correct l) -> 
  (memomap_correct (snd (decideOL_fmap n g d l))) /\
  (((fst (decideOL_fmap n g d l)) = true) ->  exists n0, (decideOL_opti n0 g d) = true).
Proof.
    induction n.
  - intros. split.
    + intros. pose proof (H g d). simpl in *. destruct M.find; simpl in *; auto.
    + specialize (H g d). simpl in *.
      destruct M.find; intros; simpl in *; subst; congruence.
  - intros.
    + simpl. pose proof H. unfold memomap_correct in H0.  specialize (H0 g d).
      destruct M.find eqn: res. simpl in *. destruct b; simpl in *; auto. split; auto; intro; congruence.

      pose proof (memomap_correct_false g d l H) as H1. 
      dest_simp g; dest_simp d; (try dest_simp t0); (try dest_simp t). all: repeat rewrite mor_mtrue_r; repeat rewrite mor_mfalse_l; repeat rewrite mand_mtrue_l.

      all: rewrite snd_let_simpl; rewrite fst_let_simpl. all: repeat rewrite mor_mtrue_r; repeat rewrite mor_mfalse_l; repeat rewrite mand_mtrue_l.

      Ltac rewrite_mor x y l:= 
        assert ((x ||| y) l = let (b, m) := x l in if b then (true, m) else (y m) ) as rew_first_or; (only 1: reflexivity); rewrite rew_first_or in *; clear rew_first_or.
      Ltac rewrite_mand x y l:= 
        assert ((x &&& y) l = let (b, m) := x l in if b then (y m) else (false, m) ) as rew_first_and; (only 1: reflexivity); rewrite rew_first_and in *; clear rew_first_and.

      Ltac reduce_or rest IHn l H :=
        let IHn_ := (fresh "IHn") in let IHn_snd := (fresh "IHn_snd") in 
        let IHn_fst := (fresh "IHn_fst") in let n0 := (fresh "n0") in 
        let b_ := (fresh "b") in let l_ := (fresh "l") in let found := (fresh "found") in
          lazymatch rest with
          | decideOL_fmap ?n ?g ?d => 
            pose proof (IHn g d l H) as IHn_; simpl in *; destruct IHn_ as [IHn_snd IHn_fst];
            destruct (decideOL_fmap n g d l) as [b_ l_] eqn: found;
            destruct b_; simpl in *;
            only 1: (destruct IHn_fst as [n0 IHn_fst]; auto; simpl in *;
              split; auto; intro; exists (S n0); simpl; 
              autorewrite with rw_bool in *; auto 7);
            split; auto; congruence;
            idtac

          | decideOL_fmap ?n ?g ?d ||| ?rest2 =>
            try rewrite_mor (decideOL_fmap n g d) rest2 l;
            pose proof (IHn g d l H) as IHn_; simpl in *; destruct IHn_ as [IHn_snd IHn_fst];
            destruct (decideOL_fmap n g d l) as [b_ l_] eqn: found;
            destruct b_; simpl in *;
            only 1: (destruct IHn_fst as [n0 IHn_fst]; auto; simpl in *;
              split; auto; intro; exists (S n0); simpl; 
              autorewrite with rw_bool in *; auto 7);
            reduce_or rest2 IHn l_ IHn_snd;
            idtac

          | (decideOL_fmap ?n ?g1 ?d1) &&& (decideOL_fmap ?n ?g2 ?d2)  =>
            try rewrite_mand (decideOL_fmap n g1 d1) (decideOL_fmap n g2 d2) l;
            let IHn_snd_r := (fresh "IHn_snd_r") in let IHn_fst_r := (fresh "IHn_fst_r") in
            let IHn_r := (fresh "IHn_r") in let m1 := (fresh "m1") in let m2 := (fresh "m2") in
            let b_r := (fresh "b_r") in let l_r := (fresh "l_r") in let found_r := (fresh "found_r") in
            pose proof (IHn g1 d1 l H) as IHn_; simpl in *; destruct IHn_ as [IHn_snd IHn_fst];
            destruct (decideOL_fmap n g1 d1 l)  as [ b_ l_] eqn: found;
            pose proof (IHn g2 d2 l_ IHn_snd) as IHn_r; simpl in *; destruct IHn_r as [IHn_snd_r IHn_fst_r];
            destruct (decideOL_fmap n g2 d2 l_)  as [ b_r l_r] eqn: found_r;
            simpl in *;
            destruct b_ ; destruct b_r ; simpl in *;
            only 1: (destruct IHn_fst as [m1 IHn_fst]; destruct IHn_fst_r as [m2 IHn_fst_r]; auto;
              split; auto; intros;
              exists (S (Nat.max m1 m2)); simpl;
              apply (decideOL_opti_monotonic (Nat.max m1 m2)) in IHn_fst; try lia;
              apply (decideOL_opti_monotonic (Nat.max m1 m2)) in IHn_fst_r; try lia;
              rewrite IHn_fst; rewrite IHn_fst_r; btauto;
              simpl in *; autorewrite with rw_bool in *; auto); intuition; congruence;
            idtac
          | decideOL_fmap ?n ?g ?d =>
            
            idtac
          | mfalse => simpl; intuition; congruence
          | (mbool (?p0 =? ?p)%positive) => 
            let p_eq := (fresh "p_eq") in
            destruct (p0 =? p)%positive eqn: p_eq; simpl in *; 
            only 1: (split; intros; auto; exists 1; simpl; autorewrite with rw_bool in *; auto);
            intuition; congruence;
            idtac
      end.
      all: try (lazymatch goal with
      | [ |- memomap_correct (_ (?g, ?d) (fst (?rest ?l)) (snd (?rest ?l))) /\ _ ] => 
        apply memomap_correct_cons;
        reduce_or rest IHn l H1;
        idtac
      | _ => fail "unknown shape"
      end; fail). 
Qed.


Theorem decideOL_fmap_simp_correct : forall g d, (decideOL_fmap_simp g d) = true -> anTerm_leq g d.
Proof. 
  intros. assert (squash (OLProof (g, d))). 
  pose proof (decideOL_fmap_correct (anterm_size g * anterm_size d + 4) g d (AnTermPairAVLMap.empty bool)). 
  destruct H0. unfold memomap_correct; simpl in *; auto. destruct H1 as [n0 H1]; auto. apply decideOL_opti_correct with n0; auto.
  destruct H0. apply (soundness (g, d)). auto.
Qed.


Theorem reduce_to_decideOL_fmap {OL: Ortholattice} : forall t1 t2 f, (decideOL_fmap_simp (L t1) (R t2)) = true -> ((eval t1 f) <= (eval t2 f)).
Proof.
  intros. assert (anTerm_leq  (L t1) (R t2)). all: auto using decideOL_fmap_simp_correct.
Qed.

Ltac solveOL_fmap OL := 
  reify_goal OL; apply reduce_to_decideOL_fmap; auto; vm_compute; (try reflexivity).

Example test1 {OL: Ortholattice} : forall a,  a <= a.
Proof.
  intro. 
  solveOL_fmap OL.
Qed.

Example test2 {OL: Ortholattice} : forall a,  a == (a ∩ a).
Proof.
  intro. 
  solveOL_fmap OL.
Qed.

Example test3 {OL: Ortholattice} a b c: 
  ¬(b ∪ ¬(c ∩ ¬b) ∪ a) <= (¬a ∪ ¬(b ∩ ¬a)).
Proof.
  intros. 
  solveOL_fmap OL.
Qed.


Example test4 : forall a: (@A BoolOL),  a <= (a || a).
Proof.
  intro.
  solveOL_fmap BoolOL.
Qed.


Example test5 : forall a: (@A BoolOL), Bool.le a (andb a a).
Proof.
  intro. 
  solveOL_fmap BoolOL.
Qed.


Example test6 : forall a b : bool,   ( a ∩ (neg a)) <= b.
Proof.
  intros.
  solveOL_fmap BoolOL.
Qed.


Example test7 : forall a b : bool,  Bool.le (andb a (negb a)) b.
Proof.
  intros. 
  solveOL_fmap BoolOL.
Qed.


Example test8 : forall a b c: bool,  (a ∩ (negb a)) <= (a || (b && c)).
Proof.
  intros. 
  solveOL_fmap BoolOL.
Qed.
