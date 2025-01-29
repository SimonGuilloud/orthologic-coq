Require Import NArith.
Require Import OL_Theory.


Require Import OL_Reflection_1_base.
Require Import OL_Reflection_2_opti.
Require OL_Reflection_4_fmap.

Require Import Setoid Morphisms.
Require Import Lia.
Require Import Coq.Arith.Bool_nat.
Require Import Coq.Arith.PeanoNat.
Require Import Btauto.


Open Scope bool_scope.
Import List.
Import ListNotations.
Require Import Coq.Numbers.BinNums.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.PArith.BinPos.


Definition Pointer:= positive.

Inductive TermPointer : Set :=
  | VarP : positive -> Pointer -> TermPointer
  | MeetP : TermPointer -> TermPointer -> Pointer -> TermPointer
  | JoinP : TermPointer -> TermPointer -> Pointer -> TermPointer
  | NotP : TermPointer -> Pointer -> TermPointer.


Fixpoint forget_pointer (t: TermPointer) : Term :=
  match t with
  | VarP n p => Var n
  | MeetP a b p => Meet (forget_pointer a) (forget_pointer b)
  | JoinP a b p => Join (forget_pointer a) (forget_pointer b)
  | NotP a p => Not (forget_pointer a)
  end.


Definition get_pointer (t: TermPointer) : Pointer :=
  match t with
  | VarP _ p => p
  | MeetP a b p => p
  | JoinP a b p => p
  | NotP a p => p
  end.


Inductive AnTermPointer : Set :=
  | NTP : AnTermPointer 
  | LTP : TermPointer -> AnTermPointer
  | RTP : TermPointer -> AnTermPointer.


Definition forget_anpointer (t: AnTermPointer) : AnTerm :=
  match t with
  | NTP => OL_Theory.N
  | LTP t => L (forget_pointer t)
  | RTP t => R (forget_pointer t)
  end.


Inductive AnPointer : Set :=
  | NP : AnPointer
  | LP : Pointer -> AnPointer
  | RP : Pointer -> AnPointer.


Definition compare_anpointer (x y: AnPointer) : comparison :=
  match x, y with
  | LP n1, LP n2 => Pos.compare n1 n2
  | LP _, _ => Lt
  | _, LP _ => Gt
  | RP n1, RP n2 => Pos.compare n1 n2
  | RP _, _ => Lt
  | _, RP _ => Gt
  | NP, NP => Eq
  end.


Lemma pos_compare_antisym_iff: forall x y c, Pos.compare x y = c <-> Pos.compare y x = CompOpp c.
Proof.
  intros; rewrite Pos.compare_antisym.
  destruct Pos.compare, c; simpl; intuition congruence.
Qed.


Lemma pos_compare_trans: forall c x y z,
    Pos.compare x y = c ->
    Pos.compare y z = c ->
    Pos.compare x z = c.
Proof.
  destruct c; intros ???.
  - rewrite !Pos.compare_eq_iff; congruence.
  - apply Pos.lt_trans.
  - rewrite (pos_compare_antisym_iff x y), (pos_compare_antisym_iff y z), (pos_compare_antisym_iff x z). simpl.
    intros. exact (Pos.lt_trans z y x H0 H).
Qed.


Definition pos_compare_eq_impl :=
  (fun x y => proj1 (Pos.compare_eq_iff x y)).


Definition pos_compare_antisym_impl :=
  (fun x y c => proj1 (pos_compare_antisym_iff x y c)).


Lemma pos_compare_eq_sym: forall x y, Pos.compare x y = Eq -> Pos.compare y x = Eq.
Proof.
  intros * Heq; rewrite Pos.compare_antisym, Heq; reflexivity.
Qed.


Lemma pos_compare_eq_trans: forall x y z,
    Pos.compare x y = Eq ->
    Pos.compare y z = Eq ->
    Pos.compare x z = Eq.
Proof.
  eauto using pos_compare_trans.
Qed.

Hint Resolve Pos.compare_refl Pos.compare_antisym pos_compare_trans
  pos_compare_antisym_impl pos_compare_eq_sym pos_compare_trans pos_compare_eq_impl
  : compare_nat.

  Ltac compare_anpointer_t :=
  repeat match goal with
    | _ => progress (simpl; subst)
    | [  |- forall _: AnPointer, _ ] => intros x; destruct x
    | _ => intro
    end;
  try congruence || eauto using f_equal with compare_nat .


Lemma compare_anpointer_refl: forall x: AnPointer, compare_anpointer x x = Eq.
Proof. compare_anpointer_t. Qed.


Lemma compare_anpointer_eq: forall x y: AnPointer, compare_anpointer x y = Eq -> x = y.
Proof. compare_anpointer_t. Qed.


Lemma compare_anpointer_antisym: forall x y: AnPointer, compare_anpointer y x = CompOpp (compare_anpointer x y).
Proof. compare_anpointer_t. Qed.


Lemma compare_anpointer_antisym_impl: forall x y c, compare_anpointer x y = c -> compare_anpointer y x = CompOpp c.
Proof. compare_anpointer_t. Qed.


Lemma compare_anpointer_trans: forall c x y z,
    compare_anpointer x y = c ->
    compare_anpointer y z = c ->
    compare_anpointer x z = c.
Proof. compare_anpointer_t. Qed.


Lemma compare_anpointer_eq_sym: forall x y, compare_anpointer x y = Eq -> compare_anpointer y x = Eq.
Proof. compare_anpointer_t. Qed.


Lemma compare_anpointer_eq_trans: forall x y z,
    compare_anpointer x y = Eq ->
    compare_anpointer y z = Eq ->
    compare_anpointer x z = Eq.
Proof. compare_anpointer_t. Qed.

Require OrderedType OrderedTypeAlt.

Module AnPointer_as_OTA <: OrderedTypeAlt.OrderedTypeAlt.
  Definition t := AnPointer.
  Definition compare := compare_anpointer.
  Definition compare_sym := compare_anpointer_antisym.
  Definition compare_trans := compare_anpointer_trans.
End AnPointer_as_OTA.

(* Legacy interface, but direct implementation may be useful for performance? *)
Module AnPointer_as_OT <: OrderedType.OrderedType.
  Definition t := AnPointer.

  Definition eq (x y: AnPointer) := compare_anpointer x y = Eq.
  Definition lt (x y: AnPointer) := compare_anpointer x y = Lt.

  Definition eq_refl : forall x : t, eq x x := compare_anpointer_refl.
  Definition eq_sym : forall x y : t, eq x y -> eq y x := compare_anpointer_eq_sym.
  Definition eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z := compare_anpointer_eq_trans.
  Definition lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z := compare_anpointer_trans Lt.

  Theorem lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof. unfold lt, eq; congruence. Qed.

  Theorem compare : forall x y : t, OrderedType.Compare lt eq x y.
  Proof.
    intros x y; destruct (compare_anpointer x y) eqn:Hcmp;
      [ | | apply compare_anpointer_antisym_impl in Hcmp; simpl in Hcmp ].
    all: econstructor; solve [unfold lt, eq; eassumption].
  Defined.

  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Proof.
    intros x y; destruct (compare_anpointer x y) eqn:Hcmp; [ left | right.. ].
    all: unfold eq; congruence.
  Defined.
End AnPointer_as_OT.

Require MSets MSetAVL MSetFacts.

Module AnPointer_as_OOT := OrdersAlt.OT_from_Alt AnPointer_as_OTA.
Module AnPointerAVL := MSetAVL.Make AnPointer_as_OOT.
Module AnPointerPair_as_OOT := OrdersEx.PairOrderedType AnPointer_as_OOT AnPointer_as_OOT.
Module AnPointerPairAVL := MSetAVL.Make AnPointerPair_as_OOT.
Module AnPointerPairAVLFacts := MSetFacts.Facts AnPointerPairAVL.

Require Import FMapAVL FMapFacts.
Module AnPointerPair_as_OT := OrderedTypeEx.PairOrderedType AnPointer_as_OT AnPointer_as_OT.
(* Module AnPointerPair_as_OOT := OrdersAlt.Update_OT AnPointerPair_as_OT. *)
(* Module AnPointerPairAVL := MSetAVL.Make AnPointerPair_as_OOT. *)
Module AnPointerPairAVLMap := FMapAVL.Make AnPointerPair_as_OT.
Module AnPointerPairAVLMapFacts := FMapFacts.Facts AnPointerPairAVLMap.


Definition MemoKey := (AnPointer * AnPointer)%type.


Definition MemoMap := AnPointerPairAVLMap.t bool.


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

Module M := AnPointerPairAVLMap.
Module F := AnPointerPairAVLMapFacts.

(* Module Import M := AnPointerPairAVL. *)
(* Module Import F := AnPointerPairAVLFacts. *)

Definition get_pointer_anterm (t: AnTermPointer) : AnPointer :=
  match t with
  | NTP => NP
  | LTP p => LP (get_pointer p)
  | RTP p => RP (get_pointer p)
  end.
Notation "[[ x ]]" := (get_pointer_anterm x) (at level 0).


Fixpoint decideOL_pointers (fuel: nat) (g d: AnTermPointer) (memo: MemoMap) : (bool * MemoMap) :=
  match M.find ([[g]], [[d]]) memo with
  | Some b => (b, memo)
  | None => (match fuel with
    | 0 => (false, memo) 
    | S n => let (b, m) :=
      (match (g, d) with 
      | (LTP (VarP a _), RTP (VarP b _) )  => mbool (Pos.eqb a b) (* Hyp *)
      | (RTP (VarP a _), LTP (VarP b _)) => mbool (Pos.eqb a b) (* Hyp *)
      | (LTP (VarP a _), LTP (VarP b _))  => mfalse
      | (RTP (VarP a _), RTP (VarP b _)) => mfalse
      | (LTP (VarP a _), NTP) => mfalse
      | (RTP (VarP a _), NTP) => mfalse
      | (NTP, LTP (VarP a _)) => mfalse
      | (NTP, RTP (VarP a _)) => mfalse
      | (LTP (JoinP a b _), _) => decideOL_pointers n (LTP a) d &&& decideOL_pointers n (LTP b) d
      | (_, LTP (JoinP a b _)) => decideOL_pointers n g (LTP a) &&& decideOL_pointers n g (LTP b)
      | (RTP (MeetP a b _), _) => decideOL_pointers n (RTP a) d &&& decideOL_pointers n (RTP b) d
      | (_, RTP (MeetP a b _)) => decideOL_pointers n g (RTP a) &&& decideOL_pointers n g (RTP b)
      | (LTP (NotP a _), _) => decideOL_pointers n (RTP a) d
      | (_, LTP (NotP a _)) => decideOL_pointers n g (RTP a)
      | (RTP (NotP a _), _) => decideOL_pointers n (LTP a) d
      | (_, RTP (NotP a _)) => decideOL_pointers n g (LTP a)
      | _ => (
        match g with 
        | LTP (MeetP a b _) => decideOL_pointers n (LTP a) d 
        | _ => mfalse
        end ||| (
        match g with 
        | LTP (MeetP a b _) => decideOL_pointers n (LTP b) d
        | _ => mfalse
        end ||| (
        match d with 
        | LTP (MeetP a b _) => decideOL_pointers n g (LTP a) 
        | _ => mfalse
        end ||| (
        match d with 
        | LTP (MeetP a b _) => decideOL_pointers n g (LTP b) 
        | _ => mfalse
        end ||| (
        match g with
        | RTP (JoinP a b _) => decideOL_pointers n (RTP a) d
        | _ => mfalse
        end ||| (
        match g with
        | RTP (JoinP a b _) => decideOL_pointers n (RTP b) d
        | _ => mfalse
        end ||| (
        match d with
        | RTP (JoinP a b _) => decideOL_pointers n g (RTP a) 
        | _ => mfalse
        end ||| (
        match d with
        | RTP (JoinP a b _) => decideOL_pointers n g (RTP b)
        | _ => mfalse
        end ||| (
        match d with 
        | NTP => decideOL_pointers n g g 
        | _ => mfalse
        end ||| (
        match g with 
        | NTP => decideOL_pointers n d d
        | _ => mfalse
        end  ||| (
        decideOL_pointers n g NTP ||| 
        decideOL_pointers n NTP d
      ))))))))))) end) (AnPointerPairAVLMap.add ([[g]], [[d]]) false memo)
    in (b, AnPointerPairAVLMap.add ([[g]], [[d]]) b m) end)
end.


(*
Fixpoint correctPointer_list (g : TermPointer) (l : list Pointer) : (Prop * list Pointer) :=
  match g with
  | VarP _ p => (not (In p l), l)
  | MeetP a b p => let (r1, l1) := correctPointer_list a l in let (r2, l2) := correctPointer_list b l1 in ((not (In p l)) /\ r1 /\ r2, l2)
  | JoinP a b p => let (r1, l1) := correctPointer_list a l in let (r2, l2) := correctPointer_list b l1 in ((not (In p l)) /\ r1 /\ r2, l2)
  | NotP a p => let (r1, l1) := correctPointer_list a l in (not (In p l) /\ r1, l1)
  end.


Definition CorrectInput (g d: AnTermPointer) : Prop :=
  match (g, d) with 
  | (LTP a, LTP b) => let (r1, l1) := correctPointer_list a [] in let (r2, l2) := correctPointer_list b l1 in r1 /\ r2
  | (LTP a, RTP b) => let (r1, l1) := correctPointer_list a [] in let (r2, l2) := correctPointer_list b l1 in r1 /\ r2
  | (LTP a, NTP) => let (r1, l1) := correctPointer_list a [] in r1
  | (RTP a, LTP b) => let (r1, l1) := correctPointer_list a [] in let (r2, l2) := correctPointer_list b l1 in r1 /\ r2
  | (RTP a, RTP b) => let (r1, l1) := correctPointer_list a [] in let (r2, l2) := correctPointer_list b l1 in r1 /\ r2
  | (RTP a, NTP) => let (r1, l1) := correctPointer_list a [] in r1
  | (NTP, LTP b) => let (r2, l2) := correctPointer_list b [] in r2
  | (NTP, RTP b) => let (r2, l2) := correctPointer_list b [] in r2
  | (NTP, NTP) => True
  end.
*)

Definition RefMap := {refmap : Pointer -> TermPointer | forall p, get_pointer (refmap p) = p}.


Definition points_to (refmap : RefMap) (p: Pointer):  (TermPointer) :=
  proj1_sig refmap p.


Definition lift_refmap (refmap : RefMap) : (AnPointer -> AnTermPointer) :=
  fun (p: AnPointer) => match p with
  | LP n => LTP (points_to refmap n)
  | RP n => RTP (points_to refmap n)
  | NP => NTP
  end.


Fixpoint termP_size (p: TermPointer) : nat :=
  match p with
  | VarP _ _ => 1
  | MeetP a b _ => 1 + termP_size a + termP_size b
  | JoinP a b _ => 1 + termP_size a + termP_size b
  | NotP a _ => 1 + termP_size a
  end.


Definition antermP_size (p: AnTermPointer) : nat :=
  match p with
  | NTP => 1
  | LTP t => 1 + termP_size t
  | RTP t => 1 + termP_size t
  end.


Definition memomap_correct (refmap : RefMap) (l: MemoMap) :=  forall pg pd, 
  match M.find (pg, pd) l with
  | Some true => 
      let liftedReverseRef := lift_refmap refmap in
      let g := liftedReverseRef pg in let d := liftedReverseRef pd in
      exists n, (decideOL_opti n (forget_anpointer g) (forget_anpointer d) = true)
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


Ltac dest g := destruct g; try congruence.


Lemma memomap_correct_snd_unfold (refmap : RefMap) : 
  forall (A: bool * MemoMap) g d,  
  memomap_correct refmap (AnPointerPairAVLMap.add (g, d) (fst A) (snd A)) ->
  memomap_correct refmap (snd (let (b, m) := A in (b, AnPointerPairAVLMap.add (g, d) b m))).
Proof.
  intros. rewrite OL_Reflection_4_fmap.snd_let_simpl. auto.
Qed.


Lemma comparison_eq_decidable {c0 c1: comparison} : Decidable.decidable (c0 = c1).
Proof. red; destruct c0, c1; intuition congruence. Qed.
(* [Heq1 | Heq2]%(Decidable.not_and _ _ comparison_eq_decidable) *)

Theorem termP_size_eq_termSize (p: TermPointer) : termP_size p = term_size (forget_pointer p).
Proof. induction p; simpl; lia. Qed.


Theorem antermP_size_eq_anSize (p: AnTermPointer) : antermP_size p = anterm_size (forget_anpointer p).
Proof. destruct p; simpl; eauto using termP_size_eq_termSize. Qed.


Lemma memomap_correct_cons (refmap : RefMap) pg pd l e : 
  let liftedReverseRef := lift_refmap refmap in
  let g := liftedReverseRef pg in let d := liftedReverseRef pd in
  memomap_correct refmap l /\
  (e = true -> exists n, decideOL_opti n (forget_anpointer g) (forget_anpointer d) = true) -> 
  memomap_correct refmap (AnPointerPairAVLMap.add (pg, pd) e l) /\ (e = true -> exists n, decideOL_opti n (forget_anpointer g) (forget_anpointer d) = true).
Proof.
  unfold memomap_correct; intro H1; destruct H1 as [Hok He]. split; auto. intros.
  rewrite F.add_o; destruct F.eq_dec as [(Heq1%compare_anpointer_eq, Heq2%compare_anpointer_eq) | Hneq ];
    simpl in *; subst.
  - destruct e; auto.
  - apply Hok.
Qed.


Ltac dest_simp g := destruct g ; repeat rewrite OL_Reflection_4_fmap.mor_mtrue_r; try (simpl; congruence).


Fixpoint refmap_inv_get_pointer (refmap : RefMap) (t: TermPointer): Prop :=
  (points_to refmap (get_pointer t)) = t /\ 
  match t with
  | VarP _ _ => True
  | MeetP a b _ => refmap_inv_get_pointer refmap a /\ refmap_inv_get_pointer refmap b
  | JoinP a b _ => refmap_inv_get_pointer refmap a /\ refmap_inv_get_pointer refmap b
  | NotP a _ => refmap_inv_get_pointer refmap a
  end.


Definition refmap_inv_get_pointer_anterm (refmap : RefMap) (t: AnTermPointer): Prop :=
  match t with
  | NTP => True
  | LTP p => refmap_inv_get_pointer refmap p
  | RTP p => refmap_inv_get_pointer refmap p
  end.


Theorem get_pointer_inv_refmap_anterm (refmap : RefMap) : 
  forall p, [[(lift_refmap refmap) p]] = p.
Proof.
  intros. destruct p; simpl in *; auto.
  all: unfold points_to; destruct refmap as [f H]; simpl in *; rewrite H; auto.
Qed.


Theorem forget_rev_equal (refmap : RefMap) a : 
  refmap_inv_get_pointer_anterm refmap a -> (lift_refmap refmap [[a]]) = a.
Proof.
  intros.
   destruct a; simpl in *; auto; destruct t; simpl in *; intuition; rewrite H0; auto.
Qed.

Theorem forget_rev_equal_2 (refmap : RefMap) a : 
  refmap_inv_get_pointer_anterm refmap a -> (forget_anpointer (lift_refmap refmap [[a]])) = (forget_anpointer a).
Proof.
  intro.
  rewrite forget_rev_equal; auto.
Qed.


Lemma memomap_correct_false (refmap : RefMap) pg pd l: memomap_correct refmap l -> memomap_correct refmap (AnPointerPairAVLMap.add (pg, pd) false l).
Proof.
  intros. unfold memomap_correct. intros. rewrite F.add_o; destruct F.eq_dec as [(Heq1%compare_anpointer_eq, Heq2%compare_anpointer_eq) | Hneq ]; auto.
  simpl in *. apply H.
Qed.


Theorem decideOL_pointers_correct (refmap : RefMap) : 
  forall n pg pd l, 
  let liftedReverseRef := lift_refmap refmap in
  let g := liftedReverseRef pg in let d := liftedReverseRef pd in
  (memomap_correct refmap l) -> 
  refmap_inv_get_pointer_anterm refmap g ->
  refmap_inv_get_pointer_anterm refmap d ->
  (memomap_correct refmap (snd (decideOL_pointers n g d l))) /\
  (((fst (decideOL_pointers n g d l)) = true) ->  exists n, (decideOL_opti n (forget_anpointer g) (forget_anpointer d)) = true).
Proof.



      Ltac niceSimpl := simpl fst in *; simpl snd in *; simpl andb in *; simpl orb in *.
      Ltac repRewRev := (repeat (rewrite forget_rev_equal; auto)); do 2 (try (rewrite forget_rev_equal in *; try (niceSimpl; simpl refmap_inv_get_pointer_anterm in *; auto; fail))).
      Ltac repRew := (repeat (rewrite forget_rev_equal; auto)).
      Ltac splitConj := repeat match goal with
      | [H: _ /\ _ |- _] => destruct H
      end.


  induction n.
  - intros. split. 
    + intros. pose proof (H [[g]] [[d]] ). simpl in *. 
      subst g d liftedReverseRef. rewrite !(get_pointer_inv_refmap_anterm) in *.
      destruct M.find; simpl in *; auto.
    + intros. pose proof (H pg pd). simpl in *. 
      subst g d liftedReverseRef. rewrite !(get_pointer_inv_refmap_anterm) in *.
      destruct M.find; intros; simpl in *; subst; congruence.

  - intros. 
    + Opaque decideOL_opti. rewrite <- (forget_rev_equal_2 refmap g); auto. rewrite <- (forget_rev_equal_2 refmap d); auto. simpl. pose proof (H [[g]] [[d]]) as H2. unfold memomap_correct in H2. 
      destruct (M.find ([[g]], [[d]]) l) eqn: res; simpl in *.
      split; auto. destruct b eqn:b_eq; simpl in *; intro; auto; repRewRev; congruence.
      fold liftedReverseRef; fold g d.
      subst liftedReverseRef; fold g d.
      pose proof (memomap_correct_false refmap [[g]] [[d]] l H) as H3. 
      dest_simp g ; dest_simp d; (try dest_simp t0); (try dest_simp t). 
      all: rewrite OL_Reflection_4_fmap.snd_let_simpl; rewrite OL_Reflection_4_fmap.fst_let_simpl;
      rewrite ?mor_mtrue_r, ?mor_mfalse_l, ?mand_mtrue_l.
      Transparent decideOL_opti.

    Ltac rewrite_mor x y l:= 
      assert ((x ||| y) l = let (b, m) := x l in if b then (true, m) else (y m) ) as rew_first_or; (only 1: reflexivity); 
      try rewrite rew_first_or in *;
      simpl in rew_first_or; try rewrite rew_first_or in *; clear rew_first_or.
    Ltac rewrite_mand x y l:= 
      assert ((x &&& y) l = let (b, m) := x l in if b then (y m) else (false, m) ) as rew_first_and; (only 1: reflexivity); rewrite rew_first_and in *; clear rew_first_and.

    Ltac reduce_or rest IHn l H :=
          let IHn_ := (fresh "IHn") in let IHn_snd := (fresh "IHn_snd") in 
          let IHn_fst := (fresh "IHn_fst") in let n0 := (fresh "n0") in 
          let b_ := (fresh "b") in let l_ := (fresh "l") in let found := (fresh "found") in
            lazymatch rest with
            | decideOL_pointers ?n ?g ?d => 
              pose proof (IHn [[g]] [[d]]  l H) as IHn_; destruct IHn_ as [IHn_snd IHn_fst]; auto;
              do 2 (try (rewrite forget_rev_equal in *; auto;  try (simpl in *;intuition; fail)));
              destruct (decideOL_pointers n g d l) as [b_ l_] eqn: found;
              destruct b_; niceSimpl; (**)
              try only 1: (
                destruct IHn_fst as [n0 IHn_fst]; auto; try rewrite found in *; niceSimpl;
                split; auto; intro; exists (S n0); simpl; 
                autorewrite with rw_bool in *; auto 7;(**) idtac);
              split; auto; congruence;
              idtac

            | decideOL_pointers ?n ?g ?d ||| ?rest2 =>
              try rewrite_mor (decideOL_pointers n g d) rest2 l;
              pose proof (IHn [[g]] [[d]]  l H) as IHn_; destruct IHn_ as [IHn_snd IHn_fst]; auto;
              (do 2 try (rewrite forget_rev_equal in *; auto;  try (intuition; fail)));
              try (simpl in *; repeat splitConj; auto; fail);
              destruct (decideOL_pointers n g d l) as [b_ l_] eqn: found;
              destruct b_; niceSimpl; simpl in found; try rewrite found in *;
              only 1: (destruct IHn_fst as [n0 IHn_fst]; auto;  niceSimpl; auto;
                split; auto; intro; exists (S n0); simpl; 
                autorewrite with rw_bool in *; auto 7; fail(**));
              reduce_or rest2 IHn l_ IHn_snd;(**)
              idtac

            | (decideOL_pointers ?n ?g1 ?d1) &&& (decideOL_pointers ?n ?g2 ?d2) =>
              try rewrite_mand (decideOL_pointers n g1 d1) (decideOL_pointers n g2 d2) l;
              let IHn_snd_r := (fresh "IHn_snd_r") in let IHn_fst_r := (fresh "IHn_fst_r") in
              let IHn_r := (fresh "IHn_r") in let m1 := (fresh "m1") in let m2 := (fresh "m2") in
              let b_r := (fresh "b_r") in let l_r := (fresh "l_r") in let found_r := (fresh "found_r") in
              pose proof (IHn [[g1]] [[d1]]  l H) as IHn_; destruct IHn_ as [IHn_snd IHn_fst]; auto;
              (do 2 try (rewrite forget_rev_equal in *; auto;  try (intuition; fail)));
              try (simpl in *; repeat splitConj; auto; fail);
              destruct (decideOL_pointers n g1 d1 l)  as [ b_ l_] eqn: found;
              pose proof (IHn [[g2]] [[d2]]  l_ IHn_snd) as IHn_r; destruct IHn_r as [IHn_snd_r IHn_fst_r]; auto;
              (do 2 try (rewrite forget_rev_equal in *; auto;  try (intuition; fail)));
              try (simpl in *; repeat splitConj; auto; fail);
              destruct (decideOL_pointers n g2 d2 l_)  as [ b_r l_r] eqn: found_r;
              destruct b_ ; destruct b_r ; niceSimpl;
              only 1: (destruct IHn_fst as [m1 IHn_fst]; destruct IHn_fst_r as [m2 IHn_fst_r];  (* HERE *)
                try rewrite found in *; try rewrite found_r in *;auto;
                split; auto; intros;
                exists (S (Nat.max m1 m2)); simpl in *;
                apply (decideOL_opti_monotonic (Nat.max m1 m2)) in IHn_fst; try lia;
                apply (decideOL_opti_monotonic (Nat.max m1 m2)) in IHn_fst_r; try lia;
                rewrite IHn_fst; rewrite IHn_fst_r; btauto;
                idtac); 
              intuition; congruence;
              idtac
            | decideOL_pointers ?n ?g ?d =>
              
              idtac
            | mfalse => simpl; intuition; congruence
            | (mbool (?p0 =? ?p)%positive) => 
              let p_eq := (fresh "p_eq") in
              destruct (p0 =? p)%positive eqn: p_eq; niceSimpl;
              (do 2 try (rewrite forget_rev_equal in *; auto;  try (intuition; fail)));
              only 1: (split; intros; auto; exists 1; simpl; autorewrite with rw_bool in *; auto;(**) idtac);
              intuition; congruence;
              idtac
        end. 

      all: try (lazymatch goal with
      | [ |- memomap_correct ?revref (_ (?g, ?d) (fst (?rest ?l)) (snd (?rest ?l))) /\ _ ] => 
        apply memomap_correct_cons;
        reduce_or rest IHn l H3;
        idtac
      | _ => fail "unknown shape"
      end; fail).
Qed.


Fixpoint add_pointer (t: Term) (p: Pointer): (TermPointer * Pointer) :=
  match t with
  | Var n => (VarP n p, Pos.succ p)
  | Not a => 
      let (t1, p1) := (add_pointer a (Pos.succ p)) in (NotP t1 p, p1)
  | Meet a b => 
      let (t1, p1) := (add_pointer a (Pos.succ p)) in let (t2, p2) := (add_pointer b p1)  in (MeetP t1 t2 p, p2)
  | Join a b => 
      let (t1, p1) := (add_pointer a (Pos.succ p)) in let (t2, p2) := (add_pointer b p1)  in (JoinP t1 t2 p, p2)
  end.


Fixpoint subterms_of_pointer (t: TermPointer) : list TermPointer :=
  match t with
  | VarP _ _ => [t]
  | NotP a _ => t :: subterms_of_pointer a
  | MeetP a b _ => t :: subterms_of_pointer a ++ subterms_of_pointer b
  | JoinP a b _ => t :: subterms_of_pointer a ++ subterms_of_pointer b
  end.


Definition func_from_list (l: list TermPointer) : (Pointer -> TermPointer) := fun p =>
  match find (fun x => Pos.eqb (get_pointer x) p) l with
  | Some x => x
  | None => VarP xH p
  end.


Definition func_of_add_pointer (t: TermPointer) : (Pointer -> TermPointer) := 
  func_from_list (subterms_of_pointer t).
      

Fixpoint is_inv_get_pointer_t (map : Pointer -> TermPointer) (t: TermPointer): Prop :=
  (map (get_pointer t)) = t /\ 
  match t with
  | VarP _ _ => True
  | MeetP a b _ => is_inv_get_pointer_t map a /\ is_inv_get_pointer_t map b
  | JoinP a b _ => is_inv_get_pointer_t map a /\ is_inv_get_pointer_t map b
  | NotP a _ => is_inv_get_pointer_t map a
  end.


Theorem succ_pos_neq : forall p : positive, p <> (Pos.succ p).
Proof.
  intros p.
  induction p; simpl; intro H; discriminate H.
Qed.


Lemma add_pointer_correct_1 (t: Term)  : 
  forall p,
  (forall p0, get_pointer (func_of_add_pointer (fst (add_pointer t p)) p0) = p0).
Proof.
  intros. unfold func_of_add_pointer; unfold func_from_list; simpl in *. induction (subterms_of_pointer (fst (add_pointer t p))); simpl in *; auto.
  destruct a; simpl in *; destruct Pos.eqb eqn: equals; simpl in *; repeat rewrite Pos.eqb_eq in *; auto.
Qed.


Fixpoint subterm (t t0: TermPointer) : Prop :=
t = t0 \/
  match t with
  | VarP _ _ => False
  | NotP a _ => subterm a t0
  | MeetP a b _ => subterm a t0 \/ subterm b t0
  | JoinP a b _ => subterm a t0 \/ subterm b t0
  end.


Theorem get_add_pointer t p:
  get_pointer (fst (add_pointer t p)) = p.
Proof.
  destruct t; simpl in *; auto.
  - destruct (add_pointer t1 (Pos.succ p)); simpl in *; auto. destruct (add_pointer t2 p0); simpl in *; auto.
  - destruct (add_pointer t1 (Pos.succ p)); simpl in *; auto. destruct (add_pointer t2 p0); simpl in *; auto.
  - destruct (add_pointer t (Pos.succ p)); simpl in *; auto.
Qed.


Theorem get_add_pointer_eq t p t1 p1:
  add_pointer t p = (t1, p1) ->
  get_pointer t1 = p.
Proof.
  intro. pose proof (get_add_pointer t p). rewrite H in H0. auto.
Qed.


Lemma fst_let_simpl {T1} {T2} {T3} {T4} (A: T1 * T2) (c: T1 -> T2 -> T3) (d: T1 -> T2 -> T4) : 
  fst (let (b, m) := A in (c b m, d b m )) = c (fst A) (snd A).
Proof.
  destruct A; auto.
Qed.


Lemma snd_let_simpl {T1} {T2} {T3} {T4} (A: T1 * T2) (c: T1 -> T2 -> T3) (d: T1 -> T2 -> T4) : 
  snd (let (b, m) := A in (c b m, d b m )) = d (fst A) (snd A).
Proof.
  destruct A; auto.
Qed.


Ltac let_simpl := repeat rewrite fst_let_simpl in *; repeat rewrite snd_let_simpl in *.


Theorem subterm_refl t: subterm t t.
Proof.
  destruct t; simpl in *; intuition.
Qed.


Hint Resolve Pos.lt_succ_diag_r Pos.le_refl : pos_order.

Ltac rewGetAddLeft t p := (erewrite <- (get_add_pointer_eq t p)) ; eauto; eauto using subterm_refl with pos_order.
Ltac rewGetAdd t p := (erewrite (get_add_pointer_eq t p)) ; eauto; eauto using subterm_refl with pos_order.
Ltac lt_trans_succ := eapply Pos.lt_trans with (Pos.succ _); try eapply Pos.lt_succ_diag_r.


Theorem add_pointer_returns_gt t : 
  forall st,
  forall p,
  subterm (fst (add_pointer t p)) st -> 
  Pos.lt (get_pointer st) (snd (add_pointer t p)).
Proof.
  induction t as [ | ta IHta tb IHtb  | ta IHta tb IHtb  | ta IHta].
  - simpl; intros; intuition; subst; simpl; apply Pos.lt_succ_diag_r .
  - intros. simpl in *. let_simpl. pose proof IHta as IHta_.
    specialize (IHta (fst (add_pointer ta (Pos.succ p))) (Pos.succ p)). specialize (IHta_ st (Pos.succ p)).
    destruct (add_pointer ta (Pos.succ p)) as [t1 p1] eqn: eqt; simpl in *.
    pose proof IHtb as IHtb_.
    specialize (IHtb (fst (add_pointer tb p1)) p1). specialize (IHtb_ st p1).
    destruct (add_pointer tb p1) as [t2 p2] eqn: eqt2; simpl in *. repeat destruct H; auto; simpl in *.
    + apply Pos.lt_trans with p1.
      * intuition; subst; simpl in *. apply Pos.lt_trans with (Pos.succ p). apply Pos.lt_succ_diag_r.
         rewGetAddLeft ta (Pos.succ p).
      * rewGetAddLeft tb p1.
    + apply Pos.lt_trans with p1; intuition. rewGetAddLeft tb p1.
  - intros. simpl in *. let_simpl. pose proof IHta as IHta_.
    specialize (IHta (fst (add_pointer ta (Pos.succ p))) (Pos.succ p)). specialize (IHta_ st (Pos.succ p)).
    destruct (add_pointer ta (Pos.succ p)) as [t1 p1] eqn: eqt; simpl in *.
    pose proof IHtb as IHtb_.
    specialize (IHtb (fst (add_pointer tb p1)) p1). specialize (IHtb_ st p1).
    destruct (add_pointer tb p1) as [t2 p2] eqn: eqt2; simpl in *. repeat destruct H; auto; simpl in *.
    + apply Pos.lt_trans with p1.
      * intuition; subst; simpl in *. lt_trans_succ. rewGetAddLeft ta (Pos.succ p).
      * rewGetAddLeft tb p1.
    + apply Pos.lt_trans with p1; intuition. rewGetAddLeft tb p1.
  - intros. simpl in *. let_simpl. pose proof IHta as IHta_. 
    specialize (IHta (fst (add_pointer ta (Pos.succ p))) (Pos.succ p)). specialize (IHta_ st (Pos.succ p)).
    destruct (add_pointer ta (Pos.succ p)) eqn: eqt; simpl in *.
    intuition; subst; simpl in *. lt_trans_succ. rewGetAddLeft ta (Pos.succ p).
Qed.


Theorem subterm_trans t1 t2 t3:
  subterm t1 t2 -> subterm t2 t3 -> subterm t1 t3.
Proof.
  intros. induction t1; simpl in *; intuition.
  all: subst; simpl in *; intuition.
Qed.  


Lemma subterm_get_pointer_lt t :
  forall st,
  forall p,
  subterm (fst (add_pointer t p)) st -> 
  ((fst (add_pointer t p)) = st \/ (Pos.lt (get_pointer (fst (add_pointer t p))) (get_pointer st))).
Proof.
  induction t as [ | ta IHta tb IHtb  | ta IHta tb IHtb  | ta IHta]; intros; simpl in *.
  - intuition.
  - pose proof IHta as IHta_. specialize (IHta st (Pos.succ p)). specialize (IHta_ (fst (add_pointer ta (Pos.succ p))) (Pos.succ p)).
    destruct (add_pointer ta (Pos.succ p)) as [ta1 pa1] eqn: taeq; simpl in *.
    pose proof IHtb as IHtb_. specialize (IHtb st pa1). specialize (IHtb_ (fst (add_pointer tb pa1)) (Pos.succ p)).
    destruct (add_pointer tb pa1) as [tb1 pb1] eqn: taeq_tb; simpl in *. destruct H.
    + left. auto.
    + right.
      destruct H.
      *  specialize (IHta H). destruct IHta.
        ** subst; simpl in *; rewGetAdd ta (Pos.succ p).
        ** apply Pos.lt_trans with (get_pointer ta1); auto; rewGetAdd ta (Pos.succ p).
      * specialize (IHtb H).
        assert (p < pa1)%positive as Hpa1.
        lt_trans_succ. 
        pose proof (get_add_pointer ta (Pos.succ p)). rewrite <- H0. 
        pose proof (add_pointer_returns_gt ta ta1 (Pos.succ p)). rewrite taeq in *. simpl in *. auto using subterm_refl.
        destruct IHtb.
        ** subst; simpl in *; rewGetAdd tb pa1.
        ** apply Pos.lt_trans with (get_pointer tb1); auto; rewGetAdd tb pa1.
  - pose proof IHta as IHta_. specialize (IHta st (Pos.succ p)). specialize (IHta_ (fst (add_pointer ta (Pos.succ p))) (Pos.succ p)).
    destruct (add_pointer ta (Pos.succ p)) as [ta1 pa1] eqn: taeq; simpl in *.
    pose proof IHtb as IHtb_. specialize (IHtb st pa1). specialize (IHtb_ (fst (add_pointer tb pa1)) (Pos.succ p)).
    destruct (add_pointer tb pa1) as [tb1 pb1] eqn: taeq_tb; simpl in *. destruct H.
    + left. auto.
    + right.
      destruct H.
      *  specialize (IHta H). destruct IHta.
        ** subst; simpl in *; rewGetAdd ta (Pos.succ p).
        ** apply Pos.lt_trans with (get_pointer ta1); auto; rewGetAdd ta (Pos.succ p).
      * specialize (IHtb H).
        assert (p < pa1)%positive as Hpa1.
        lt_trans_succ. 
        pose proof (get_add_pointer ta (Pos.succ p)). rewrite <- H0. 
        pose proof (add_pointer_returns_gt ta ta1 (Pos.succ p)). rewrite taeq in *. simpl in *. auto using subterm_refl.
        destruct IHtb.
        ** subst; simpl in *; rewGetAdd tb pa1.
        ** apply Pos.lt_trans with (get_pointer tb1); auto; rewGetAdd tb pa1.
  - pose proof IHta as IHta_. specialize (IHta st (Pos.succ p)). specialize (IHta_ (fst (add_pointer ta (Pos.succ p))) (Pos.succ p)).
    destruct (add_pointer ta (Pos.succ p)) as [t1 p1] eqn: taeq; simpl in *. destruct H.
    + left. auto.
    + right. specialize (IHta H). destruct IHta.
      * subst; simpl in *; rewGetAdd ta (Pos.succ p).
      * apply Pos.lt_trans with (get_pointer t1); auto; rewGetAdd ta (Pos.succ p).
Qed.


Theorem subterm_get_pointer_le t :
  forall st,
  forall p,
  subterm (fst (add_pointer t p)) st -> 
  (Pos.le (get_pointer (fst (add_pointer t p))) (get_pointer st)).
Proof.
  intros. pose proof subterm_get_pointer_lt t st p H. intuition.
  - subst; simpl in *. apply Pos.le_refl.
  - apply Pos.lt_le_incl; auto.
Qed. 


Ltac solve_case_eq_subterm p st1 st2 IHta_ :=
    let H := fresh "H" in let H0 := fresh "H" in
      lazymatch goal with
      | [ Hst1: _ = st1,
        eqt: add_pointer ?ta (Pos.succ ?p) = (?t1, ?p1),
        H_GP : get_pointer _ = get_pointer _,
        Hst2: subterm ?t1 st2 
        |- _ ] => 
        assert (Pos.lt (get_pointer st1) (get_pointer st2)) as H; try (rewrite H_GP in H; apply Pos.lt_irrefl in H; contradiction);
        subst; simpl in *; apply Pos.lt_le_trans with (Pos.succ p); try apply Pos.lt_succ_diag_r;
        (try rewGetAddLeft ta (Pos.succ p));
        pose proof (subterm_get_pointer_le ta st2 (Pos.succ p)) as H0; rewrite eqt in H0; simpl in *; intuition;
        idtac
      | [ Hst1: _ = st1,
        eqt: add_pointer ?ta (Pos.succ ?p) = (?t1, ?p1),
        eqt2 : add_pointer ?tb ?p1 = (?t2, ?p2),
        H_GP : get_pointer _ = get_pointer _,
        Hst2: subterm ?t2 st2 
        |- _ ] => 
        pose proof 1 as detected;
        assert (Pos.lt (get_pointer st1) (get_pointer st2)) as H; try (rewrite H_GP in H; apply Pos.lt_irrefl in H; contradiction);
        subst; simpl in *; apply Pos.lt_le_trans with p1;
        try (rewGetAddLeft tb p1; pose proof (subterm_get_pointer_le tb st2 p1) as H0; rewrite eqt2 in H0; simpl in *; intuition; fail);
        lt_trans_succ; rewGetAddLeft ta (Pos.succ p);
        pose proof (add_pointer_returns_gt ta t1 (Pos.succ p)) as APRG_ta; rewrite eqt in APRG_ta; simpl in *; apply APRG_ta; apply subterm_refl;
        idtac
      | [ Hst1: subterm ?t1 st1,
        eqt: add_pointer ?ta (Pos.succ ?p) = (?t1, ?p1),
        eqt2 : add_pointer ?tb ?p1 = (?t2, ?p2),
        H_GP : get_pointer _ = get_pointer _,
        Hst2: subterm ?t2 st2 
        |- _ ] =>
        assert (Pos.lt (get_pointer st1) (get_pointer st2)) as H; try (rewrite H_GP in H; apply Pos.lt_irrefl in H; contradiction);
        apply Pos.lt_le_trans with p1;
        try (rewGetAddLeft tb p1; pose proof (subterm_get_pointer_le tb st2 p1) as H0; rewrite eqt2 in H0; simpl in *; intuition; fail);
        pose proof (add_pointer_returns_gt ta st1 (Pos.succ p)) as APRG_ta; rewrite eqt in APRG_ta; simpl in *; auto;
        
        idtac
      end.


Theorem add_pointer_no_duplicate t :
  forall st1 st2,
  forall p,
  subterm (fst (add_pointer t p)) st1 -> 
  subterm (fst (add_pointer t p)) st2 -> 
  get_pointer st1 = get_pointer st2 ->
  st1 = st2.
Proof.
  induction t as [ | ta IHta tb IHtb  | ta IHta tb IHtb  | ta IHta].
  - intros; simpl in *; intuition; subst; reflexivity.
  - intros ??? Hst1 Hst2 H_GP; simpl in *; pose proof IHta as IHta_.
    specialize (IHta st1 st2 (Pos.succ p)). 
    destruct (add_pointer ta (Pos.succ p)) as [t1 p1] eqn: eqt; simpl in *.
    destruct (add_pointer tb p1) as [t2 p2] eqn: eqt2; simpl in *.
    repeat destruct Hst1 as [Hst1 | Hst1]; repeat destruct Hst2 as [Hst2 | Hst2];
    intuition; try congruence.
    all: try (solve_case_eq_subterm p st1 st2 IHta_; fail).
    all: try (solve_case_eq_subterm p st2 st1 IHta_; fail).
    + specialize (IHtb st1 st2 p1). rewrite eqt2 in IHtb. simpl in *. intuition.
  - intros ??? Hst1 Hst2 H_GP; simpl in *; pose proof IHta as IHta_.
    specialize (IHta st1 st2 (Pos.succ p)). 
    destruct (add_pointer ta (Pos.succ p)) as [t1 p1] eqn: eqt; simpl in *.
    destruct (add_pointer tb p1) as [t2 p2] eqn: eqt2; simpl in *.
    repeat destruct Hst1 as [Hst1 | Hst1]; repeat destruct Hst2 as [Hst2 | Hst2];
    intuition; try congruence.
    all: try (solve_case_eq_subterm p st1 st2 IHta_; fail).
    all: try (solve_case_eq_subterm p st2 st1 IHta_; fail).
    + specialize (IHtb st1 st2 p1). rewrite eqt2 in IHtb. simpl in *. intuition.
  - intros ??? Hst1 Hst2 H_GP; simpl in *. pose proof IHta as IHta_.
    specialize (IHta st1 st2 (Pos.succ p)). 
    destruct (add_pointer ta (Pos.succ p)) as [t1 p1] eqn: eqt; simpl in *.
    destruct Hst1 as [Hst1 | Hst1]; destruct Hst2 as [Hst2 | Hst2]; 
    intuition; try congruence.
    + solve_case_eq_subterm p st1 st2 IHta_.
    + solve_case_eq_subterm p st2 st1 IHta_.
Qed.


Lemma find_append_some {A: Type} f (l1 l2: list A) e:
  find f l1 = Some e -> find f (l1 ++ l2) = Some e.
Proof.
  induction l1 as [ | head tail].
  - simpl in *. intros. congruence.
  - simpl in *. intro. destruct (f head); auto.
Qed.


Lemma find_append_none {A: Type} f (l1 l2: list A):
  find f l1 = None -> find f (l1 ++ l2) = find f l2.
Proof.
  induction l1 as [ | head tail].
  - simpl in *. intros. congruence.
  - simpl in *. intro. destruct (f head); auto; try congruence.
Qed.


Lemma term_is_head_of_subterms t1 head tail:
  subterms_of_pointer t1 = head :: tail ->
  t1 = head.
Proof.
  destruct t1; simpl in *; congruence.
Qed.


Theorem subterm_in_subterms t :
  forall p st,
  In st (subterms_of_pointer (fst (add_pointer t p))) -> subterm (fst (add_pointer t p)) st.
Proof.
  induction t as [ | ta IHta tb IHtb  | ta IHta tb IHtb  | ta IHta]; intros; simpl in *; intuition.
  - destruct (add_pointer ta (Pos.succ p)) as [t1 p1] eqn: eqt_ta; simpl in *.
    destruct (add_pointer tb p1) as [t2 p2] eqn: eqt_tb; simpl in *. intuition.
    right. rewrite in_app_iff in H0. destruct H0.
    + pose proof (IHta (Pos.succ p) st). rewrite eqt_ta in H0. simpl in *. intuition.
    + pose proof (IHtb p1 st). rewrite eqt_tb in H0. simpl in *. intuition.
  - destruct (add_pointer ta (Pos.succ p)) as [t1 p1] eqn: eqt_ta; simpl in *.
    destruct (add_pointer tb p1) as [t2 p2] eqn: eqt_tb; simpl in *. intuition.
    right. rewrite in_app_iff in H0. destruct H0.
    + pose proof (IHta (Pos.succ p) st). rewrite eqt_ta in H0. simpl in *. intuition.
    + pose proof (IHtb p1 st). rewrite eqt_tb in H0. simpl in *. intuition.
  - destruct (add_pointer ta (Pos.succ p)) as [tap p1] eqn: eqt_ta; simpl in *. intuition.
    right. pose proof (IHta (Pos.succ p) st). rewrite eqt_ta in H. simpl in *. apply H. auto.
Qed.


Lemma in_subterms_imp_pointer_lt ta p t1 p1 st:
  add_pointer ta (Pos.succ p) = (t1, p1) ->
  In st (subterms_of_pointer t1) -> (get_pointer st < p1)%positive.
Proof.
  intros. pose proof (subterm_in_subterms ta (Pos.succ p) st). rewrite H in H1. simpl in *. intuition.
  pose proof (add_pointer_returns_gt ta st (Pos.succ p)). rewrite H in H1. simpl in *. intuition.
Qed.


Lemma find_classical {A: Type} f (l: list A):
  ((exists r, find f l = Some r) -> False) ->
  find f l = None.
Proof.
  intros; destruct (find f l); intuition.
  exfalso; apply H. exists a; auto.
Qed.


Lemma find_some_in {A: Type} f (l: list A) x:
  find f l = Some x -> In x l.
Proof.
  apply find_some.
Qed.


Lemma find_some_sat {A: Type} f (l: list A) x:
  find f l = Some x -> f x = true.
Proof.
  apply find_some.
Qed.


Lemma find_too_large_none ta p t1 p1 tp:
  add_pointer ta (Pos.succ p) = (t1, p1) ->
  (p1 <= get_pointer tp)%positive ->
  find (fun x : TermPointer => (get_pointer x =? get_pointer tp)%positive) (subterms_of_pointer t1) = None.
Proof.
  intros. 
  assert (forall r, (p1 <= get_pointer r)%positive -> In r (subterms_of_pointer t1) -> False).
  - intros. pose proof (in_subterms_imp_pointer_lt ta p t1 p1 r H H2) as ILPintuition. apply H1. apply Pos.lt_gt. auto.
  - apply find_classical; intros.
    destruct H2 as [r]. apply H1 with r. clear H1.
    + assert (get_pointer r = get_pointer tp) as gpr_gpt; try rewrite gpr_gpt in *; auto.
      rewrite <- Pos.eqb_eq.
      eauto using (find_some_sat (fun x : TermPointer => (get_pointer x =? get_pointer tp)%positive) ).
    + eauto using find_some_in.
Qed.


Ltac unfoldBoth := unfold func_of_add_pointer in *; unfold func_from_list in *; simpl in *.


Lemma add_pointer_subterm_some (t: Term) :
  forall p ,
  forall tp,
  subterm (fst (add_pointer t p)) tp -> 
  find (fun x => Pos.eqb (get_pointer x) (get_pointer tp)) (subterms_of_pointer (fst (add_pointer t p))) = Some tp.
Proof.
  induction t as [ | ta IHta tb IHtb  | ta IHta tb IHtb  | ta IHta].
  - simpl in *. intros; intuition; subst; simpl in *. unfoldBoth; auto; intuition. 
    destruct Pos.eqb%positive eqn: equal; auto. rewrite Pos.eqb_refl in equal; subst; congruence.
  - intros ?? H_st. simpl in *. 
    destruct (add_pointer ta (Pos.succ p)) as [t1 p1] eqn: eqt; simpl in *.
    destruct (add_pointer tb p1) as [t2 p2] eqn: eqt2; simpl in *.
    repeat destruct H_st as [H_st | H_st]; intuition; subst; simpl in *; unfoldBoth; simpl in *; auto.
    + rewrite Pos.eqb_refl; simpl in *; auto.
    + destruct (Pos.eqb p (get_pointer tp)) eqn: equal; simpl in *; auto.
      * rewrite Pos.eqb_eq in equal.
        assert (Pos.lt p (get_pointer tp) ) as H; try (subst; apply Pos.lt_irrefl in H; intuition; fail).
        apply Pos.lt_le_trans with (Pos.succ p). apply Pos.lt_succ_diag_r.
        rewGetAddLeft ta (Pos.succ p). 
        pose proof (subterm_get_pointer_le ta tp (Pos.succ p)). rewrite eqt in H; simpl in *; auto.
      * specialize (IHta (Pos.succ p) tp ). rewrite eqt in IHta. simpl in *. auto. apply find_append_some; auto.
    + destruct (Pos.eqb p (get_pointer tp)) eqn: equal; simpl in *; auto.
      * rewrite Pos.eqb_eq in equal.
        assert (Pos.lt p (get_pointer tp) ) as H; try (subst; apply Pos.lt_irrefl in H; intuition; fail).
        apply Pos.lt_le_trans with (Pos.succ p). apply Pos.lt_succ_diag_r.
        rewGetAddLeft ta (Pos.succ p). 
        apply Pos.le_trans with p1.
        ** pose proof (add_pointer_returns_gt ta t1 (Pos.succ p)) as APRG_ta; rewrite eqt in APRG_ta; simpl in *. 
           apply Pos.lt_le_incl; apply APRG_ta; apply subterm_refl.
        ** rewGetAddLeft tb p1.
           pose proof (subterm_get_pointer_le tb tp p1). rewrite eqt2 in H; simpl in *; auto.
      * specialize (IHtb p1 tp). rewrite eqt2 in IHtb. simpl in *. rewrite <-IHtb; auto. apply find_append_none; auto.
        assert (Pos.le p1 (get_pointer tp)) as H. rewGetAddLeft tb p1.
        pose proof (subterm_get_pointer_le tb tp p1). rewrite eqt2 in H; simpl in *; auto.
        eapply find_too_large_none; eauto.
  - intros ?? H_st. simpl in *. 
    destruct (add_pointer ta (Pos.succ p)) as [t1 p1] eqn: eqt; simpl in *.
    destruct (add_pointer tb p1) as [t2 p2] eqn: eqt2; simpl in *.
    repeat destruct H_st as [H_st | H_st]; intuition; subst; simpl in *; unfoldBoth; simpl in *; auto.
    + rewrite Pos.eqb_refl; simpl in *; auto.
    + destruct (Pos.eqb p (get_pointer tp)) eqn: equal; simpl in *; auto.
      * rewrite Pos.eqb_eq in equal.
        assert (Pos.lt p (get_pointer tp) ) as H; try (subst; apply Pos.lt_irrefl in H; intuition; fail).
        apply Pos.lt_le_trans with (Pos.succ p). apply Pos.lt_succ_diag_r.
        rewGetAddLeft ta (Pos.succ p). 
        pose proof (subterm_get_pointer_le ta tp (Pos.succ p)). rewrite eqt in H; simpl in *; auto.
      * specialize (IHta (Pos.succ p) tp ). rewrite eqt in IHta. simpl in *. auto. apply find_append_some; auto.
    + destruct (Pos.eqb p (get_pointer tp)) eqn: equal; simpl in *; auto.
      * rewrite Pos.eqb_eq in equal.
        assert (Pos.lt p (get_pointer tp) ) as H; try (subst; apply Pos.lt_irrefl in H; intuition; fail).
        apply Pos.lt_le_trans with (Pos.succ p). apply Pos.lt_succ_diag_r.
        rewGetAddLeft ta (Pos.succ p). 
        apply Pos.le_trans with p1.
        ** pose proof (add_pointer_returns_gt ta t1 (Pos.succ p)) as APRG_ta; rewrite eqt in APRG_ta; simpl in *. 
           apply Pos.lt_le_incl; apply APRG_ta; apply subterm_refl.
        ** rewGetAddLeft tb p1.
           pose proof (subterm_get_pointer_le tb tp p1). rewrite eqt2 in H; simpl in *; auto.
      * specialize (IHtb p1 tp). rewrite eqt2 in IHtb. simpl in *. rewrite <-IHtb; auto. apply find_append_none; auto.
        assert (Pos.le p1 (get_pointer tp)) as H. rewGetAddLeft tb p1.
        pose proof (subterm_get_pointer_le tb tp p1). rewrite eqt2 in H; simpl in *; auto.
        eapply find_too_large_none; eauto.
  - intros ?? H_st. simpl in *. destruct (add_pointer ta (Pos.succ p)) as [t1 p1] eqn: eqt; simpl in *.
    destruct H_st as [H_st | H_st]; intuition; subst; simpl in *; unfoldBoth; simpl in *; auto.
    + rewrite Pos.eqb_refl; simpl in *; auto.
    + destruct (Pos.eqb p (get_pointer tp)) eqn: equal; simpl in *; auto.
      * rewrite Pos.eqb_eq in equal.
        assert (Pos.lt p (get_pointer tp) ) as H; try (subst; apply Pos.lt_irrefl in H; intuition; fail).
        apply Pos.lt_le_trans with (Pos.succ p). apply Pos.lt_succ_diag_r.
        rewGetAddLeft ta (Pos.succ p). 
        pose proof (subterm_get_pointer_le ta tp (Pos.succ p)). rewrite eqt in H; simpl in *; auto.
      * specialize (IHta (Pos.succ p) tp ). rewrite eqt in IHta. simpl in *. auto.
Qed. 


Lemma func_add_pointer_inverse_get (t: Term) :
  forall p ,
  forall tp,
  subterm (fst (add_pointer t p)) tp -> 
  func_of_add_pointer (fst (add_pointer t p)) (get_pointer tp) = tp.
Proof.
  intros. unfoldBoth. rewrite add_pointer_subterm_some; auto.
Qed.


Lemma func_add_inv_get_subterm (t: Term) :
  forall p ,
  forall tp,
  subterm (fst (add_pointer t p)) tp -> 
  is_inv_get_pointer_t (func_of_add_pointer (fst (add_pointer t p))) tp.
Proof.
  induction tp as [ | tpa IHtpa tpb IHtpb  | tpa IHtpa tpb IHtpb  | tpa IHtpa]; intros; simpl in *; simpl in *;
  intros.
  - intuition. pose proof (func_add_pointer_inverse_get t p (VarP p0 p1)). intuition.
  - intuition.
    + pose proof (func_add_pointer_inverse_get t p (MeetP tpa tpb p0)). simpl in *. intuition.
    + apply IHtpa. eapply subterm_trans; eauto; simpl in *. right. left. apply subterm_refl.
    + apply IHtpb. eapply subterm_trans; eauto; simpl in *. right. right. apply subterm_refl.
  - intuition.
    + pose proof (func_add_pointer_inverse_get t p (JoinP tpa tpb p0)). simpl in *. intuition.
    + apply IHtpa. eapply subterm_trans; eauto; simpl in *. right. left. apply subterm_refl.
    + apply IHtpb. eapply subterm_trans; eauto; simpl in *. right. right. apply subterm_refl.
  - pose proof (func_add_pointer_inverse_get t p (NotP tpa p0)). simpl in *. intuition.
    apply IHtpa. eapply subterm_trans; eauto; simpl in *. right. apply subterm_refl.
Qed.


Lemma func_add_inv_get (t: Term) :
  forall p,
  is_inv_get_pointer_t (func_of_add_pointer (fst (add_pointer t p))) (fst (add_pointer t p)).
Proof.
  intros.
  apply (func_add_inv_get_subterm t p (fst (add_pointer t p))). apply subterm_refl.
Qed.


Definition add_anpointer (t: AnTerm) (p: Pointer): (AnTermPointer * Pointer) :=
  match t with
  | L a => let (t1, p1) := (add_pointer a p) in (LTP t1, p1)
  | R a => let (t1, p1) := (add_pointer a p) in (RTP t1, p1)
  | OL_Theory.N => (NTP, p)
  end.


Definition pair_anterm_to_term (ant1 ant2: AnTerm) : Term :=
  match (ant1, ant2) with
  | (L t1, L t2) => Meet t1 t2
  | (L t1, R t2) => Meet t1 t2
  | (R t1, L t2) => Meet t1 t2
  | (R t1, R t2) => Meet t1 t2
  | (OL_Theory.N, L t2) => Not t2
  | (OL_Theory.N, R t2) => Not t2
  | (L t1, OL_Theory.N) => Not t1
  | (R t1, OL_Theory.N) => Not t1
  | (OL_Theory.N, OL_Theory.N) => Var xH
  end.


Definition func_off_add_anpointers (ant1 ant2: AnTerm) : (Pointer -> TermPointer) :=
  func_of_add_pointer ((fst (add_pointer (pair_anterm_to_term ant1 ant2) xH))).


Lemma pair_anterm_to_refmap (ant1 ant2: AnTerm) : RefMap.
Proof.
  exists (func_off_add_anpointers ant1 ant2).
  intros. apply add_pointer_correct_1.
Defined.
  

Definition add_anpointers (t1 t2: AnTerm) (p: Pointer): (AnTermPointer * AnTermPointer * Pointer) :=
  let (t1, p1) := (add_anpointer t1 p) in let (t2, p2) := (add_anpointer t2 p1) in (t1, t2, p2).


Definition decideOL_pointers_simp (g d: AnTerm): bool :=
  let (gd,  _) := add_anpointers g d 2%positive in let (g1, d1) := gd in 
  fst (decideOL_pointers (anterm_size g * anterm_size d + 4) g1 d1 (AnPointerPairAVLMap.empty bool)).


Theorem forget_inverse_add t :
  forall p,
  forget_pointer (fst (add_pointer t p)) = t.
Proof. 
  induction t; simpl in *; auto.
  - intros. destruct (add_pointer t1 (Pos.succ p)) as [t1' p1] eqn: eqt1. destruct (add_pointer t2 p1) as [t2' p2] eqn: eqt2.
    simpl in *. apply f_equal2. specialize (IHt1 (Pos.succ p)). rewrite eqt1 in IHt1. simpl in *. auto.
    specialize (IHt2 p1). rewrite eqt2 in IHt2. simpl in *. auto.
  - intros. destruct (add_pointer t1 (Pos.succ p)) as [t1' p1] eqn: eqt1. destruct (add_pointer t2 p1) as [t2' p2] eqn: eqt2.
    simpl in *. apply f_equal2. specialize (IHt1 (Pos.succ p)). rewrite eqt1 in IHt1. simpl in *. auto.
    specialize (IHt2 p1). rewrite eqt2 in IHt2. simpl in *. auto.
  - intros. destruct (add_pointer t (Pos.succ p)) as [t1' p1] eqn: eqt1.
    simpl in *. apply f_equal. specialize (IHt (Pos.succ p)). rewrite eqt1 in IHt. simpl in *. auto.
Qed.  


Theorem an_forget_inverse_add g :
  forall p,
  forget_anpointer (fst (add_anpointer g p)) = g.
Proof.
  intros. destruct g; simpl in *; try congruence; rewrite fst_let_simpl; simpl in *; rewrite forget_inverse_add; auto.
Qed.


Theorem termP_size_eq t :
  forall p1 p2,
  termP_size (fst (add_pointer t p1)) = termP_size (fst (add_pointer t p2)).
Proof.
  induction t; simpl in *; auto; intros.
  - destruct (add_pointer t1 (Pos.succ p1)) as [t1' p1'] eqn: eqt1. destruct (add_pointer t2 p1') as [t2' p2'] eqn: eqt2.
    destruct (add_pointer t1 (Pos.succ p2)) as [t1'' p1''] eqn: eqt1'. destruct (add_pointer t2 p1'') as [t2'' p2''] eqn: eqt2'.
    simpl in *. apply f_equal.
    specialize (IHt1 (Pos.succ p1) (Pos.succ p2)). specialize (IHt2 p1' p1''). 
    rewrite eqt1 in IHt1. rewrite eqt2 in IHt2. simpl in *.
    rewrite eqt1' in IHt1. rewrite eqt2' in IHt2. simpl in *. lia.
  - destruct (add_pointer t1 (Pos.succ p1)) as [t1' p1'] eqn: eqt1. destruct (add_pointer t2 p1') as [t2' p2'] eqn: eqt2.
    destruct (add_pointer t1 (Pos.succ p2)) as [t1'' p1''] eqn: eqt1'. destruct (add_pointer t2 p1'') as [t2'' p2''] eqn: eqt2'.
    simpl in *. apply f_equal.
    specialize (IHt1 (Pos.succ p1) (Pos.succ p2)). specialize (IHt2 p1' p1''). 
    rewrite eqt1 in IHt1. rewrite eqt2 in IHt2. simpl in *.
    rewrite eqt1' in IHt1. rewrite eqt2' in IHt2. simpl in *. lia.
  - destruct (add_pointer t (Pos.succ p1)) as [t1' p1'] eqn: eqt1. destruct (add_pointer t (Pos.succ p2)) as [t2' p2'] eqn: eqt2.
    simpl in *. apply f_equal. specialize (IHt (Pos.succ p1) (Pos.succ p2)). rewrite eqt1 in IHt. rewrite eqt2 in IHt. simpl in *. lia.
Qed.


Theorem term_size_eq_termP_size t :
  forall p,
  term_size t = termP_size (fst (add_pointer t p)).
Proof.
  induction t; simpl in *; auto; intros.
  - specialize (IHt1 (Pos.succ p)). specialize (IHt2 p). 
    destruct (add_pointer t1 (Pos.succ p)) as [t1' p1] eqn: eqt1.
    simpl in *.
     destruct (add_pointer t2 p1) as [t2' p2] eqn: eqt2.
    simpl in *. apply f_equal. erewrite termP_size_eq in IHt2 . rewrite eqt2 in IHt2. simpl in *. rewrite IHt2. auto.
  - specialize (IHt1 (Pos.succ p)). specialize (IHt2 p). 
    destruct (add_pointer t1 (Pos.succ p)) as [t1' p1] eqn: eqt1.
    simpl in *.
     destruct (add_pointer t2 p1) as [t2' p2] eqn: eqt2.
    simpl in *. apply f_equal. erewrite termP_size_eq in IHt2 . rewrite eqt2 in IHt2. simpl in *. rewrite IHt2. auto.
  - specialize (IHt (Pos.succ p)). 
    destruct (add_pointer t (Pos.succ p)) as [t1' p1] eqn: eqt1.
    simpl in *. congruence.
Qed.
  

Theorem anterm_size_eq_antermP_size g p:
  anterm_size (g) = antermP_size (fst (add_anpointer g p)).
Proof.
  destruct g; simpl in *; auto; rewrite fst_let_simpl; simpl in *; auto using term_size_eq_termP_size.
Qed.


Ltac substAll := 
  let Ha := fresh "Ha" in let Hb := fresh "Hb" in
    lazymatch goal with 
    | [H: (?a1, ?a2) = (?b1, ?b2) |- _] => assert (a1=b1) as Ha; assert (a2=b2) as Hb; try congruence; subst; clear H
    | [H: ?a = ?a |- _] => clear H
    | [H: ?c ?a = ?c ?b |- _] => try (assert (a=b) as Ha; only 1: (congruence; fail); subst; clear H)
    end.


Lemma subterm_meetP_1 p t1 t2 :
  subterm (MeetP t1 t2 p) t1 .
Proof.
  simpl in *. right; left; apply subterm_refl.
Qed.


Lemma subterm_meetP_2 p t1 t2 :
  subterm (MeetP t1 t2 p) t2 .
Proof.
  simpl in *. right; right; apply subterm_refl.
Qed.


Lemma subterm_joinP_1 p t1 t2 :
  subterm (JoinP t1 t2 p) t1 .
Proof.
  simpl in *. right; left; apply subterm_refl.
Qed.


Lemma subterm_joinP_2 p t1 t2 :
  subterm (JoinP t1 t2 p) t2 .
Proof.
  simpl in *. right; right; apply subterm_refl.
Qed.


Lemma subterm_notP p t :
  subterm (NotP t p) t.
Proof.
  simpl in *. right; apply subterm_refl.
Qed.


Opaque subterm.

Ltac solve_LL_LR_RL_RR tg td t:= 
  induction t as [ n p| t1 IHt1 t2 IHt2 | t1 IHt1 t2 IHt2 | t IHt]; intros; simpl in *;
  try ( pose proof (func_add_inv_get_subterm (Meet tg td) 1%positive (VarP n p)) as APC5; simpl in *;
            unfold func_off_add_anpointers; simpl in *; repeat (rewrite fst_let_simpl; simpl);
            destruct (add_pointer tg 2%positive) as [t p0] eqn: eq_tg; simpl in *;
            destruct (add_pointer td p0) eqn: eq_td; simpl in *; intuition; fail);
  try ( pose proof (func_add_inv_get_subterm (Meet tg td) 1%positive (MeetP t1 t2 p)) as APC5; simpl in *;
            unfold func_off_add_anpointers; simpl in *; repeat (rewrite fst_let_simpl; simpl);
            destruct (add_pointer tg 2%positive) as [t p0] eqn: eq_tg; simpl in *;
            destruct (add_pointer td p0) eqn: eq_td; simpl in *; intuition; 
            try (apply IHt1; auto; eapply subterm_trans; eauto using subterm_meetP_1);
            try (apply IHt2; auto; eapply subterm_trans; eauto using subterm_meetP_2); fail);
  try ( pose proof (func_add_inv_get_subterm (Meet tg td) 1%positive (JoinP t1 t2 p)) as APC5; simpl in *;
            unfold func_off_add_anpointers; simpl in *; repeat (rewrite fst_let_simpl; simpl);
            destruct (add_pointer tg 2%positive) as [t p0] eqn: eq_tg; simpl in *;
            destruct (add_pointer td p0) eqn: eq_td; simpl in *; intuition;
            try (apply IHt1; auto; eapply subterm_trans; eauto using subterm_joinP_1);
            try (apply IHt2; auto; eapply subterm_trans; eauto using subterm_joinP_2); fail);
      ( pose proof (func_add_inv_get_subterm (Meet tg td) 1%positive (NotP t p)) as APC5; simpl in *;
            unfold func_off_add_anpointers; simpl in *; repeat (rewrite fst_let_simpl; simpl);
            destruct (add_pointer tg 2%positive) as [t1 p0] eqn: eq_tg; simpl in *;
            destruct (add_pointer td p0) eqn: eq_td; simpl in *; intuition;
            apply IHt; auto; eapply subterm_trans; eauto using subterm_notP; fail).


Ltac solve_LN_RN tg t:= 
  induction t as [ n p| t1 IHt1 t2 IHt2 | t1 IHt1 t2 IHt2 | t IHt]; intros; simpl in *;
  try ( pose proof (func_add_inv_get_subterm (Not tg) 1%positive (VarP n p)) as APC5; simpl in *;
            unfold func_off_add_anpointers; simpl in *; repeat (rewrite fst_let_simpl; simpl);
            destruct (add_pointer tg 2%positive) as [t p0] eqn: eq_tg; simpl in *;
            intuition; fail);
  try ( pose proof (func_add_inv_get_subterm (Not tg) 1%positive (MeetP t1 t2 p)) as APC5; simpl in *;
            unfold func_off_add_anpointers; simpl in *; repeat (rewrite fst_let_simpl; simpl);
            destruct (add_pointer tg 2%positive) as [t p0] eqn: eq_tg; simpl in *;
            intuition; 
            try (apply IHt1; auto; eapply subterm_trans; eauto using subterm_meetP_1);
            try (apply IHt2; auto; eapply subterm_trans; eauto using subterm_meetP_2); fail);
  try ( pose proof (func_add_inv_get_subterm (Not tg) 1%positive (JoinP t1 t2 p)) as APC5; simpl in *;
            unfold func_off_add_anpointers; simpl in *; repeat (rewrite fst_let_simpl; simpl);
            destruct (add_pointer tg 2%positive) as [t p0] eqn: eq_tg; simpl in *;
            intuition;
            try (apply IHt1; auto; eapply subterm_trans; eauto using subterm_joinP_1);
            try (apply IHt2; auto; eapply subterm_trans; eauto using subterm_joinP_2); fail);
      ( pose proof (func_add_inv_get_subterm (Not tg) 1%positive (NotP t p)) as APC5; simpl in *;
            unfold func_off_add_anpointers; simpl in *; repeat (rewrite fst_let_simpl; simpl);
            destruct (add_pointer tg 2%positive) as [t1 p0] eqn: eq_tg; simpl in *;
            intuition;
            apply IHt; auto; eapply subterm_trans; eauto using subterm_notP; fail).


Lemma pointco_inter_equivLL tg td t:
  subterm (fst (add_pointer (pair_anterm_to_term (L tg) (L td)) xH)) t ->
((is_inv_get_pointer_t (func_of_add_pointer (fst (add_pointer tg 2%positive))) t) \/
  (is_inv_get_pointer_t (func_of_add_pointer (fst (add_pointer td (snd (add_pointer tg 2%positive))) ))) t) ->
  refmap_inv_get_pointer (pair_anterm_to_refmap (L tg) (L td)) t.
Proof.
  solve_LL_LR_RL_RR tg td t.
Qed. 


Lemma pointco_inter_equivLR tg td t:
  subterm (fst (add_pointer (pair_anterm_to_term (L tg) (R td)) xH)) t ->
((is_inv_get_pointer_t (func_of_add_pointer (fst (add_pointer tg 2%positive))) t) \/
  (is_inv_get_pointer_t (func_of_add_pointer (fst (add_pointer td (snd (add_pointer tg 2%positive))) ))) t) ->
  refmap_inv_get_pointer (pair_anterm_to_refmap (L tg) (R td)) t.
Proof.
  solve_LL_LR_RL_RR tg td t.
Qed.


Lemma pointco_inter_equivRL tg td t:
  subterm (fst (add_pointer (pair_anterm_to_term (R tg) (L td)) xH)) t ->
((is_inv_get_pointer_t (func_of_add_pointer (fst (add_pointer tg 2%positive))) t) \/
  (is_inv_get_pointer_t (func_of_add_pointer (fst (add_pointer td (snd (add_pointer tg 2%positive))) ))) t) ->
  refmap_inv_get_pointer (pair_anterm_to_refmap (R tg) (L td)) t.
Proof.
  solve_LL_LR_RL_RR tg td t.
Qed.


Lemma pointco_inter_equivRR tg td t:
  subterm (fst (add_pointer (pair_anterm_to_term (R tg) (R td)) xH)) t ->
((is_inv_get_pointer_t (func_of_add_pointer (fst (add_pointer tg 2%positive))) t) \/
  (is_inv_get_pointer_t (func_of_add_pointer (fst (add_pointer td (snd (add_pointer tg 2%positive))) ))) t) ->
  refmap_inv_get_pointer (pair_anterm_to_refmap (R tg) (R td)) t.
Proof.
  solve_LL_LR_RL_RR tg td t.
Qed.


Lemma pointco_inter_equivNL td t:
  subterm (fst (add_pointer (pair_anterm_to_term OL_Theory.N (L td)) xH)) t ->
  is_inv_get_pointer_t (func_of_add_pointer (fst (add_pointer td 2%positive))) t ->
  refmap_inv_get_pointer (pair_anterm_to_refmap OL_Theory.N (L td)) t.
Proof.
  solve_LN_RN td t.
Qed.


Lemma pointco_inter_equivNR td t:
  subterm (fst (add_pointer (pair_anterm_to_term OL_Theory.N (R td)) xH)) t ->
  is_inv_get_pointer_t (func_of_add_pointer (fst (add_pointer td 2%positive))) t ->
  refmap_inv_get_pointer (pair_anterm_to_refmap OL_Theory.N (R td)) t.
Proof.
  solve_LN_RN td t.
Qed.


Lemma pointco_inter_equivLN tg t:
  subterm (fst (add_pointer (pair_anterm_to_term (L tg) OL_Theory.N) xH)) t ->
  is_inv_get_pointer_t (func_of_add_pointer (fst (add_pointer tg 2%positive))) t ->
  refmap_inv_get_pointer (pair_anterm_to_refmap (L tg) OL_Theory.N) t.
Proof.
  solve_LN_RN tg t.
Qed. 


Lemma pointco_inter_equivRN tg t:
  subterm (fst (add_pointer (pair_anterm_to_term (R tg) OL_Theory.N) xH)) t ->
  is_inv_get_pointer_t (func_of_add_pointer (fst (add_pointer tg 2%positive))) t ->
  refmap_inv_get_pointer (pair_anterm_to_refmap (R tg) OL_Theory.N) t.
Proof.
  solve_LN_RN tg t.
Qed.


Lemma add_pointer_correct_g1 d g p1 p2 g1 d1 :
  add_anpointer g 2%positive = (g1, p1) ->
  add_anpointer d p1 = (d1, p2) ->
  refmap_inv_get_pointer_anterm (pair_anterm_to_refmap g d) g1.
Proof.
  intros.
  destruct g1 eqn: dest_g1; destruct g eqn: dest_g; simpl in *; try congruence; auto. 
  all: try destruct (add_pointer t0 2%positive ) eqn: dest_t02; subst; simpl in *; try congruence.
  all: destruct d1 eqn: dest_d1; destruct d eqn: dest_d; simpl in *; try congruence; auto.
  all: try destruct (add_pointer _ p1 ) eqn: dest_tp1; subst; simpl in *; try congruence; auto.
  all: repeat substAll; try congruence.
  - pose proof (func_add_inv_get t0 2%positive); apply pointco_inter_equivLN; simpl in *;
    rewrite dest_t02 in *; simpl in *; auto using subterm_notP.
  - pose proof (func_add_inv_get_subterm t0 2%positive t).
    apply pointco_inter_equivLL; simpl in *.
    all: rewrite dest_t02 in *; simpl in *.
    all: destruct (add_pointer t3 p1) eqn: dest_t3; simpl in *; auto using subterm_meetP_1, subterm_refl.
  - pose proof (func_add_inv_get_subterm t0 2%positive t).
    apply pointco_inter_equivLR; simpl in *.
    all: rewrite dest_t02 in *; simpl in *.
    all: destruct (add_pointer t3 p1) eqn: dest_t3; simpl in *; auto using subterm_meetP_1, subterm_refl.
  - pose proof (func_add_inv_get t0 2%positive); apply pointco_inter_equivLN; simpl in *;
    rewrite dest_t02 in *; simpl in *; auto using subterm_notP.
  - pose proof (func_add_inv_get_subterm t0 2%positive t).
    apply pointco_inter_equivRL; simpl in *.
    all: rewrite dest_t02 in *; simpl in *.
    all: destruct (add_pointer t3 p1) eqn: dest_t3; simpl in *; auto using subterm_meetP_1, subterm_refl.
  - pose proof (func_add_inv_get_subterm t0 2%positive t).
    apply pointco_inter_equivLR; simpl in *.
    all: rewrite dest_t02 in *; simpl in *.
    all: destruct (add_pointer t3 p1) eqn: dest_t3; simpl in *; auto using subterm_meetP_1, subterm_refl.
Qed.


Lemma add_pointer_correct_d1 d g p1 p2 g1 d1 :
  add_anpointer g 2%positive = (g1, p1) ->
  add_anpointer d p1 = (d1, p2) ->
  refmap_inv_get_pointer_anterm (pair_anterm_to_refmap g d) d1.
Proof.
  intros.
  destruct g1 eqn: dest_g1; destruct g eqn: dest_g; simpl in *; try congruence; auto. 
  all: try destruct (add_pointer _ 2%positive ) eqn: dest_t02; subst; simpl in *; try congruence.
  all: destruct d1 eqn: dest_d1; destruct d eqn: dest_d; simpl in *; try congruence; auto.
  all: try destruct (add_pointer _ p1 ) eqn: dest_tp1; subst; simpl in *; try congruence; auto.
  all: repeat substAll; try congruence.
  - pose proof (func_add_inv_get t0 2%positive); apply pointco_inter_equivNL; simpl in *;
    rewrite dest_tp1 in *; simpl in *; auto using subterm_notP.
  - pose proof (func_add_inv_get t0 2%positive); apply pointco_inter_equivNR; simpl in *;
    rewrite dest_tp1 in *; simpl in *; auto using subterm_notP.
  - pose proof (func_add_inv_get_subterm t3 p1 t2).
    apply pointco_inter_equivLL; simpl in *.
    all: rewrite dest_t02 in *; simpl in *.
    all: rewrite dest_tp1 in *; simpl in *.
    all: destruct (add_pointer t3 p1) eqn: dest_t3; simpl in *; auto using subterm_meetP_2, subterm_refl.
  - pose proof (func_add_inv_get_subterm t3 p1 t2).
    apply pointco_inter_equivLR; simpl in *.
    all: rewrite dest_t02 in *; simpl in *.
    all: rewrite dest_tp1 in *; simpl in *.
    all: destruct (add_pointer t3 p1) eqn: dest_t3; simpl in *; auto using subterm_meetP_2, subterm_refl.
  - pose proof (func_add_inv_get_subterm t3 p1 t2).
    apply pointco_inter_equivRL; simpl in *.
    all: rewrite dest_t02 in *; simpl in *.
    all: rewrite dest_tp1 in *; simpl in *.
    all: destruct (add_pointer t3 p1) eqn: dest_t3; simpl in *; auto using subterm_meetP_2, subterm_refl.
  - pose proof (func_add_inv_get_subterm t3 p1 t2).
    apply pointco_inter_equivRR; simpl in *.
    all: rewrite dest_t02 in *; simpl in *.
    all: rewrite dest_tp1 in *; simpl in *.
    all: destruct (add_pointer t3 p1) eqn: dest_t3; simpl in *; auto using subterm_meetP_2, subterm_refl.
Qed.


Theorem decideOL_pointers_simp_correct : forall g d, (decideOL_pointers_simp g d) = true -> anTerm_leq g d.
Proof. 
  intros. assert (squash (OLProof (g, d))). 
  - unfold decideOL_pointers_simp in H. simpl in *. destruct (add_anpointers g d 2%positive) as [gd p] eqn: eqgd.
    destruct gd as [g1 d1]. simpl in *. destruct (decideOL_pointers (anterm_size g * anterm_size d + 4) g1 d1 (AnPointerPairAVLMap.empty bool)) eqn: eq.
    simpl in *; subst.
    unfold add_anpointers in eqgd. simpl in *. 
    destruct (add_anpointer g 2%positive) as [t1 p1] eqn: eqg1. destruct (add_anpointer d p1) as [t2 p2] eqn: eqd1.
    assert (t1 = g1); try congruence. assert (t2 = d1); try congruence. assert (p2 = p); try congruence. subst.
    pose proof decideOL_pointers_correct. simpl in *.
    pose (pair_anterm_to_refmap g d) as refmap. specialize (H refmap (anterm_size g * anterm_size d + 4)). simpl in *.
    specialize (H [[g1]] [[d1]] (AnPointerPairAVLMap.empty bool)). simpl in *.
    rewrite (anterm_size_eq_antermP_size g 2%positive) in H at 1. rewrite (anterm_size_eq_antermP_size d p1) in H at 1. simpl in *.
    rewrite eqg1 in H at 1. rewrite eqd1 in H at 1. simpl in *.
    Opaque forget_anpointer. Opaque antermP_size.
    Ltac simp a b := try simpl in a; simpl in b.
    assert (refmap_inv_get_pointer_anterm refmap g1) as pcat_refmap_g; auto using (add_pointer_correct_g1 d g p1 p g1 d1).
    assert (refmap_inv_get_pointer_anterm refmap d1) as pcat_refmap_d; auto using (add_pointer_correct_d1 d g p1 p g1 d1).
    assert (memomap_correct refmap (AnPointerPairAVLMap.empty bool)).
    unfold memomap_correct; simpl in *; intros; auto.
    destruct H; auto. all: rewrite ?forget_rev_equal; auto.
    destruct H1 as [n0 H1]; auto. rewrite ?forget_rev_equal; auto.  rewrite eq. simpl. reflexivity.
    apply (decideOL_opti_correct n0). rewrite ?forget_rev_equal in *; auto.
    assert (g1 = fst (add_anpointer g 2%positive)). rewrite eqg1; simpl; auto.
    assert (d1 = fst (add_anpointer d p1)). rewrite eqd1; simpl; auto. rewrite H2, H3 in H1.
    rewrite !an_forget_inverse_add in H1. auto.
  - destruct H0. apply (soundness (g, d)). auto.
Qed.


Theorem reduce_to_decideOL_pointer {OL: Ortholattice} : forall t1 t2 f, (decideOL_pointers_simp (L t1) (R t2)) = true -> ((eval t1 f) <= (eval t2 f)).
Proof.
  intros. assert (anTerm_leq  (L t1) (R t2)). all: auto using decideOL_pointers_simp_correct.
Qed.

Ltac solveOLPointers OL := 
  reify_goal OL; apply reduce_to_decideOL_pointer; vm_compute; (try exact eq_refl).

Example test1 {OL: Ortholattice} : forall a,  a <= a.
Proof.
  intro. 
  solveOLPointers OL.
Qed.

Example test2 {OL: Ortholattice} : forall a,  a == (a ∩ a).
Proof.
  intro. 
  solveOLPointers OL.
Qed.

Example test3 {OL: Ortholattice} a b c: 
  ¬(b ∪ ¬(c ∩ ¬b) ∪ a) <= (¬a ∪ ¬(b ∩ ¬a)).
Proof.
  intros. 
  solveOLPointers OL.
Qed.


Example test4 : forall a: (@A BoolOL),  a <= (a || a).
Proof.
  intro.
  solveOLPointers BoolOL.
Qed.


Example test5 : forall a: (@A BoolOL), Bool.le a (andb a a).
Proof.
  intro. 
  solveOLPointers BoolOL.
Qed.


Example test6 : forall a b : bool,   ( a ∩ (neg a)) <= b.
Proof.
  intros.
  solveOLPointers BoolOL.
Qed.


Example test7 : forall a b : bool,  Bool.le (andb a (negb a)) b.
Proof.
  intros. 
  solveOLPointers BoolOL.
Qed.


Example test8 : forall a b c: bool,  (a ∩ (negb a)) <= (a || (b && c)).
Proof.
  intros. 
  solveOLPointers BoolOL.
Qed.
