Require Import OL_Theory.


Require Import OL_Reflection_1_base.
Require OL_Reflection_3_fmap.

Require Import Setoid Morphisms.
Require Import Lia.
Require Import Coq.Arith.Bool_nat.
Require Import Coq.Arith.PeanoNat.


Open Scope bool_scope.
Import List.
Import ListNotations.
Require Import Coq.Numbers.BinNums.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.PArith.BinPos.

Definition Pointer:= positive.

Inductive TermPointer : Set :=
  | VarP : nat -> Pointer -> TermPointer
  | MeetP : TermPointer -> TermPointer -> Pointer -> TermPointer
  | JoinP : TermPointer -> TermPointer -> Pointer -> TermPointer
  | NotP : TermPointer -> Pointer -> TermPointer.

Fixpoint ForgetPointer (t: TermPointer) : Term :=
  match t with
  | VarP n p => Var n
  | MeetP a b p => Meet (ForgetPointer a) (ForgetPointer b)
  | JoinP a b p => Join (ForgetPointer a) (ForgetPointer b)
  | NotP a p => Not (ForgetPointer a)
  end.


Definition GetPointer (t: TermPointer) : Pointer :=
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



Definition ForgetAnPointer (t: AnTermPointer) : AnTerm :=
  match t with
  | NTP => OL_Theory.N
  | LTP t => L (ForgetPointer t)
  | RTP t => R (ForgetPointer t)
  end.


Inductive AnPointer : Set :=
  | NP : AnPointer
  | LP : Pointer -> AnPointer
  | RP : Pointer -> AnPointer.


Definition compare_AnPointer (x y: AnPointer) : comparison :=
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

  Ltac compare_AnPointer_t :=
  repeat match goal with
    | _ => progress (simpl; subst)
    | [  |- forall _: AnPointer, _ ] => intros x; destruct x
    | _ => intro
    end;
  try congruence || eauto using f_equal with compare_nat .

Lemma compare_AnPointer_refl: forall x: AnPointer, compare_AnPointer x x = Eq.
Proof. compare_AnPointer_t. Qed.

Lemma compare_AnPointer_eq: forall x y: AnPointer, compare_AnPointer x y = Eq -> x = y.
Proof. compare_AnPointer_t. Qed.

Lemma compare_AnPointer_antisym: forall x y: AnPointer, compare_AnPointer y x = CompOpp (compare_AnPointer x y).
Proof. compare_AnPointer_t. Qed.

Lemma compare_AnPointer_antisym_impl: forall x y c, compare_AnPointer x y = c -> compare_AnPointer y x = CompOpp c.
Proof. compare_AnPointer_t. Qed.

Lemma compare_AnPointer_trans: forall c x y z,
    compare_AnPointer x y = c ->
    compare_AnPointer y z = c ->
    compare_AnPointer x z = c.
Proof. compare_AnPointer_t. Qed.

Lemma compare_AnPointer_eq_sym: forall x y, compare_AnPointer x y = Eq -> compare_AnPointer y x = Eq.
Proof. compare_AnPointer_t. Qed.

Lemma compare_AnPointer_eq_trans: forall x y z,
    compare_AnPointer x y = Eq ->
    compare_AnPointer y z = Eq ->
    compare_AnPointer x z = Eq.
Proof. compare_AnPointer_t. Qed.

Require OrderedType OrderedTypeAlt.

Module AnPointer_as_OTA <: OrderedTypeAlt.OrderedTypeAlt.
  Definition t := AnPointer.
  Definition compare := compare_AnPointer.
  Definition compare_sym := compare_AnPointer_antisym.
  Definition compare_trans := compare_AnPointer_trans.
End AnPointer_as_OTA.

(* Legacy interface, but direct implementation may be useful for performance? *)
Module AnPointer_as_OT <: OrderedType.OrderedType.
  Definition t := AnPointer.

  Definition eq (x y: AnPointer) := compare_AnPointer x y = Eq.
  Definition lt (x y: AnPointer) := compare_AnPointer x y = Lt.

  Definition eq_refl : forall x : t, eq x x := compare_AnPointer_refl.
  Definition eq_sym : forall x y : t, eq x y -> eq y x := compare_AnPointer_eq_sym.
  Definition eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z := compare_AnPointer_eq_trans.
  Definition lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z := compare_AnPointer_trans Lt.

  Theorem lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof. unfold lt, eq; congruence. Qed.

  Theorem compare : forall x y : t, OrderedType.Compare lt eq x y.
  Proof.
    intros x y; destruct (compare_AnPointer x y) eqn:Hcmp;
      [ | | apply compare_AnPointer_antisym_impl in Hcmp; simpl in Hcmp ].
    all: econstructor; solve [unfold lt, eq; eassumption].
  Defined.

  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Proof.
    intros x y; destruct (compare_AnPointer x y) eqn:Hcmp; [ left | right.. ].
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

Module M := AnPointerPairAVLMap.
Module F := AnPointerPairAVLMapFacts.

(* Module Import M := AnPointerPairAVL. *)
(* Module Import F := AnPointerPairAVLFacts. *)

Definition AnTermPointer_to_AnPointer (t: AnTermPointer) : AnPointer :=
  match t with
  | NTP => NP
  | LTP p => LP (GetPointer p)
  | RTP p => RP (GetPointer p)
  end.
Notation "[[ x ]]" := (AnTermPointer_to_AnPointer x) (at level 0).

Fixpoint decideOL_pointer_atp (fuel: nat) (g d: AnTermPointer) (memo: MemoMap) : (bool * MemoMap) :=
match M.find ([[g]], [[d]]) memo with
| Some b => (b, memo)
| None => let (b, m) :=
  (match fuel with
  | 0 => (false, memo)
  | S n =>
    (* Guaranteed sufficent cases. *)
      match (g, d) with 
      | (LTP (VarP a _), RTP (VarP b _) )  => Mbool (Nat.eqb a b) (* Hyp *)
      | (LTP (MeetP a b _), NTP) => decideOL_pointer_atp n (LTP a) (LTP b) (* LeftAnd1-2 *)
      | (NTP, RTP (JoinP a b _)) => decideOL_pointer_atp n (RTP a) (RTP b) (* RightOr1-2 *)
      | (LTP (JoinP a b _), _) => (decideOL_pointer_atp n (LTP a) d) &&& (decideOL_pointer_atp n (LTP b) d) (* LeftOr *)
      | (LTP (NotP a _), _) => decideOL_pointer_atp n (RTP a) d (* LeftNot *)
      | (_, RTP (MeetP a b _)) => (decideOL_pointer_atp n g (RTP a)) &&& (decideOL_pointer_atp n g (RTP b)) (* RightAnd *)
      | (_, RTP (NotP a _)) => decideOL_pointer_atp n g (LTP a) (* RightNot *)
          (* Swap cases *)
      | (RTP (VarP a _), LTP (VarP b _) )  => Mbool (Nat.eqb b a) (* Hyp *)
      | (NTP, LTP (MeetP a b _)) => decideOL_pointer_atp n (LTP a) (LTP b) (* LeftAnd1-2 *)
      | (RTP (JoinP a b _), NTP) => decideOL_pointer_atp n (RTP a) (RTP b) (* RightOr1-2 *)
      | (_, LTP (JoinP a b _)) => (decideOL_pointer_atp n g (LTP a)) &&& (decideOL_pointer_atp n g (LTP b)) (* LeftOr *)
      | (_, LTP (NotP a _)) => decideOL_pointer_atp n g (RTP a) (* LeftNot *)
      | (RTP (MeetP a b _), _) => (decideOL_pointer_atp n (RTP a) d) &&& (decideOL_pointer_atp n (RTP b) d) (* RightAnd *)
      | (RTP (NotP a _), _) => decideOL_pointer_atp n (LTP a) d (* RightNot *)
      | _ => 
                match d with (* Weaken g*)
        | LTP a => decideOL_pointer_atp n g NTP 
        | RTP a => decideOL_pointer_atp n g NTP 
        | NTP => Mfalse
        end |||(
        match g with (* Weaken d*)
        | LTP a => decideOL_pointer_atp n d NTP 
        | RTP a => decideOL_pointer_atp n d NTP 
        | NTP => Mfalse
        end |||(
        match g with (* LeftAnd1 g*)
        | LTP (MeetP a b _) => decideOL_pointer_atp n (LTP a) d
        | _ => Mfalse
        end |||(
        match d with (* LeftAnd1 d*)
        | LTP (MeetP a b _) => decideOL_pointer_atp n (LTP a) g
        | _ => Mfalse
        end |||(
        match g with (* LeftAnd2 g*)
        | LTP (MeetP a b _) => decideOL_pointer_atp n (LTP b) d
        | _ => Mfalse
        end |||(
        match d with (* LeftAnd2 d*)
        | LTP (MeetP a b _) => decideOL_pointer_atp n (LTP b) g
        | _ => Mfalse
        end |||(
        match g with (* RightOr1 g*)
        | RTP (JoinP a b _) => decideOL_pointer_atp n d (RTP a)
        | _ => Mfalse
        end |||(
        match d with (* RightOr1 d*)
        | RTP (JoinP a b _) => decideOL_pointer_atp n g (RTP a)
        | _ => Mfalse
        end |||(
        match g with (* RightOr2 g*)
        | RTP (JoinP a b _) => decideOL_pointer_atp n d (RTP b)
        | _ => Mfalse
        end|||(
        match d with (* RightOr2 d*)
        | RTP (JoinP a b _) => decideOL_pointer_atp n g (RTP b)
        | _ => Mfalse
        end
        )))))))))
      end memo
  end) in (b, AnPointerPairAVLMap.add ([[g]], [[d]]) b m)
end.



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

Definition RefMap := {reverseRef : Pointer -> TermPointer | forall p, GetPointer (reverseRef p) = p}.

Definition pointsTo (reverseRef : RefMap) (p: Pointer):  (TermPointer) :=
  proj1_sig reverseRef p.

Definition LiftReverseRef (reverseRef : RefMap) : (AnPointer -> AnTermPointer) :=
  fun (p: AnPointer) => match p with
  | LP n => LTP (pointsTo reverseRef n)
  | RP n => RTP (pointsTo reverseRef n)
  | NP => NTP
  end.


Fixpoint termPSize (p: TermPointer) : nat :=
  match p with
  | VarP _ _ => 1
  | MeetP a b _ => 1 + termPSize a + termPSize b
  | JoinP a b _ => 1 + termPSize a + termPSize b
  | NotP a _ => 1 + termPSize a
  end.

Definition anPSize (p: AnTermPointer) : nat :=
  match p with
  | NTP => 1
  | LTP t => 1 + termPSize t
  | RTP t => 1 + termPSize t
  end.



Definition correctMemoMap (reverseRef : RefMap) (l: MemoMap) :=  forall pg pd, 
  match M.find (pg, pd) l with
  | Some true => 
      let liftedReverseRef := LiftReverseRef reverseRef in
      let g := liftedReverseRef pg in let d := liftedReverseRef pd in
      forall n, (n >= anPSize g + anPSize d) -> (decideOL_bool n (ForgetAnPointer g) (ForgetAnPointer d) = true)
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


Ltac dest g := destruct g; try congruence.

Lemma correctMemoMap_second_let (reverseRef : RefMap) : 
  forall (A: bool * MemoMap) g d,  
  correctMemoMap reverseRef (AnPointerPairAVLMap.add (g, d) (fst A) (snd A)) ->
  correctMemoMap reverseRef (snd (let (b, m) := A in (b, AnPointerPairAVLMap.add (g, d) b m))).
Proof.
  intros. rewrite OL_Reflection_3_fmap.snd_let_simpl. auto.
Qed.

Lemma comparison_eq_decidable {c0 c1: comparison} : Decidable.decidable (c0 = c1).
Proof. red; destruct c0, c1; intuition congruence. Qed.
(* [Heq1 | Heq2]%(Decidable.not_and _ _ comparison_eq_decidable) *)

Theorem termPSize_eq_termSize (p: TermPointer) : termPSize p = termSize (ForgetPointer p).
Proof. induction p; simpl; lia. Qed.

Theorem anPSize_eq_anSize (p: AnTermPointer) : anPSize p = anSize (ForgetAnPointer p).
Proof. destruct p; simpl; eauto using termPSize_eq_termSize. Qed.

Lemma correctMemoAdditionEq2 (reverseRef : RefMap)  n pg pd l e : 
  let liftedReverseRef := LiftReverseRef reverseRef in
  let g := liftedReverseRef pg in let d := liftedReverseRef pd in
  (n >= anPSize g + anPSize d) -> 
  correctMemoMap reverseRef l -> 
  (e = true -> decideOL_bool n (ForgetAnPointer g) (ForgetAnPointer d) = true) -> 
  correctMemoMap reverseRef (AnPointerPairAVLMap.add (pg, pd) e l).
Proof.
  unfold correctMemoMap; intros Hge Hok He *.
  rewrite F.add_o; destruct F.eq_dec as [(Heq1%compare_AnPointer_eq, Heq2%compare_AnPointer_eq) | Hneq ];
    simpl in *; subst.
  - destruct e eqn: eq; intuition. erewrite OL_Reflection_3_fmap.decideOL_bool_big_fuel; eauto;
    rewrite <- !anPSize_eq_anSize; auto.
  - apply Hok.
Qed.


Ltac destSimp g := destruct g ; repeat rewrite OL_Reflection_3_fmap.OrMemo_Mfalse_r; try (simpl; congruence).

Fixpoint PointerCorrectnessTerm (reverseRef : RefMap) (t: TermPointer): Prop :=
  (pointsTo reverseRef (GetPointer t)) = t /\ 
  match t with
  | VarP _ _ => True
  | MeetP a b _ => PointerCorrectnessTerm reverseRef a /\ PointerCorrectnessTerm reverseRef b
  | JoinP a b _ => PointerCorrectnessTerm reverseRef a /\ PointerCorrectnessTerm reverseRef b
  | NotP a _ => PointerCorrectnessTerm reverseRef a
  end.

Definition PointerCorrectnessAnTerm (reverseRef : RefMap) (t: AnTermPointer): Prop :=
  match t with
  | NTP => True
  | LTP p => PointerCorrectnessTerm reverseRef p
  | RTP p => PointerCorrectnessTerm reverseRef p
  end.

Theorem lifted_project_anPointer (reverseRef : RefMap) : 
  forall p, [[(LiftReverseRef reverseRef) p]] = p.
Proof.
  intros. destruct p; simpl in *; auto.
  all: unfold pointsTo; destruct reverseRef as [f H]; simpl in *; rewrite H; auto.
Qed.

Theorem forget_rev_equal (reverseRef : RefMap) a : 
  PointerCorrectnessAnTerm reverseRef a -> (LiftReverseRef reverseRef [[a]]) = a.
Proof.
  intros.
   destruct a; simpl in *; auto; destruct t; simpl in *; intuition; rewrite H0; auto.
Qed.

Theorem decideOLPointerATPCorrect (reverseRef : RefMap) : 
  forall n pg pd l, 
  let liftedReverseRef := LiftReverseRef reverseRef in
  let g := liftedReverseRef pg in let d := liftedReverseRef pd in
  (n >= anPSize g + anPSize d) -> 
  (correctMemoMap reverseRef l) -> 
  PointerCorrectnessAnTerm reverseRef g ->
  PointerCorrectnessAnTerm reverseRef d ->
  (correctMemoMap reverseRef (snd (decideOL_pointer_atp n g d l))) /\
  (((fst (decideOL_pointer_atp n g d l)) = true) ->  (decideOL_bool n (ForgetAnPointer g) (ForgetAnPointer d)) = true).
Proof.
  induction n.
  - intros. split. 
    + intros. dest g; dest d; simpl in *; lia.
  
    + simpl in *. unfold correctMemoMap in *. specialize (H0 pg pd).
      subst g d liftedReverseRef.
      rewrite  !(lifted_project_anPointer).
      destruct M.find.
      destruct b. subst. specialize (H0 0 H). simpl in *. congruence. auto. auto.


  - intros. split.
    + simpl. pose proof H0. unfold correctMemoMap in H0. specialize (H0 pg pd).
      unfold g. unfold d. unfold liftedReverseRef. rewrite  !(lifted_project_anPointer).
      destruct M.find eqn: res; simpl in *. auto.

    Ltac rewriteOr x y l:= 
      assert ((x ||| y) l = let (b, m) := x l in if b then (true, m) else (y m) ) as rew_first_or; (only 1: reflexivity); rewrite rew_first_or in *; clear rew_first_or.
    Ltac rewriteAnd x y l:= 
      assert ((x &&& y) l = let (b, m) := x l in if b then (y m) else (false, m) ) as rew_first_and; (only 1: reflexivity); rewrite rew_first_and in *; clear rew_first_and.

      (* recursively prove goals of the form 
            correctMemoMap (snd (decideOL_pointer_atp n g1 d1 ||| (decideOL_pointer_atp n g2 d2||| (decideOL_pointer_atp n g3 d3 ||| ... ))) )
        and
            fst ( (decideOL_pointer_atp n g1 d1 ||| (decideOL_pointer_atp n g2 d2||| (decideOL_pointer_atp n g3 d3 ||| ... ))) l) =
                        (decideOL_bool n g1 d1 ||| (decideOL_bool n g2 d2||| (decideOL_bool n g3 d3 ||| ... )))
        as well as conjunctions
      *)

      Ltac niceSimpl := simpl fst in *; simpl snd in *; simpl andb in *; simpl orb in *; simpl decideOL_bool in *.

      Ltac repRewSize := (repeat (rewrite anPSize_eq_anSize in *; auto)).
      Ltac repRewRev := (repeat (rewrite forget_rev_equal; auto)); do 2 (try (rewrite forget_rev_equal in *; try (niceSimpl; simpl PointerCorrectnessAnTerm in *; auto; fail))).
      Ltac repRew := (repeat (rewrite anPSize_eq_anSize in *; auto)); (repeat (rewrite forget_rev_equal; auto)).
      Ltac splitConj := repeat match goal with
      | [H: _ /\ _ |- _] => destruct H
      end.


      Ltac reduceAndOr rest IHn l H :=
        let IHn_ := (fresh "IHn") in let IHn_snd := (fresh "IHn_snd") in 
        let IHn_fst := (fresh "IHn_fst") in let HS_ := (fresh "HS") in 
        let b_ := (fresh "b") in let l_ := (fresh "l") in
        let A_ := (fresh "A") in let B_ := (fresh "B") in
          lazymatch rest with 
          | ?op (decideOL_pointer_atp ?n ?g ?d) ?rest2 => 
            lazymatch goal with
            | [H1: PointerCorrectnessAnTerm ?rev ?g1,
              H2: PointerCorrectnessAnTerm ?rev ?d1 |- _ ] =>

              try rewriteOr (decideOL_pointer_atp n g d) rest2 l;
              try rewriteAnd (decideOL_pointer_atp n g d) rest2 l;
              pose proof IHn as IHn_; specialize (IHn_ [[g]] [[d]] l); 
              pose proof H1; pose proof H2;
              pose proof H1; pose proof H2; simpl in  H1; simpl in H2; splitConj;
              do 2 (try (rewrite forget_rev_equal in *; auto;  try (intuition; fail)));
              assert (n >= anPSize g + anPSize d) as HS_; try (simpl in *; lia); 
              specialize (IHn_ HS_ H); destruct IHn_ as [IHn_snd IHn_fst]; auto;
              destruct (decideOL_pointer_atp n g d l)  as [ b_ l_];
              destruct b_; niceSimpl; auto; try congruence;
              intros;
              repeat rewrite Bool.orb_false_r;  
              repeat rewrite OL_Reflection_3_fmap.OrMemo_Mfalse_r; 
              repeat rewrite OL_Reflection_3_fmap.OrMemo_Mfalse_l; 
              repeat rewrite OL_Reflection_3_fmap.AndMemo_Mfalse_l;
              match goal with | [ |- (_ -> _) ] => intro  | _ => idtac end;
              try (rewrite IHn_fst; simpl; repeat rewrite Bool.orb_true_r; auto;  fail);
              try (apply Bool.orb_true_iff; right);
              try (apply Bool.andb_true_iff; split);
              try (eapply IHn; simpl in *; eauto; lia); 
              try (eapply IHn_fst; simpl in *; eauto; lia); 
              reduceAndOr rest2 IHn l_ IHn_snd;
              idtac
            | _ => fail "did not find H1 and H2"

            end
          | (decideOL_pointer_atp ?n ?g ?d ) => 
            try (simpl in *; lia);
            repRew; niceSimpl; simpl PointerCorrectnessAnTerm in *; repeat rewrite Bool.orb_false_r; auto; intuition;
            specialize (IHn [[g]] [[d]] l) as IHn_; destruct IHn_ as [A_ B_]; auto; repRew; try (simpl in *; lia); 
            try (niceSimpl; simpl PointerCorrectnessAnTerm in *;  intuition; fail);
            repRewRev;
            try (simpl in *; rewrite <- !termPSize_eq_termSize; simpl in *; lia)
          
          | _ => 
          repRewSize; repRewRev; simpl in *; repeat rewrite Bool.orb_false_r; auto;
            simpl in *; eauto; (try lia);
          (fail "failed on shape:" rest)
          end.

      fold liftedReverseRef; fold g d;
      rewrite <- (lifted_project_anPointer reverseRef pg);  rewrite <- (lifted_project_anPointer reverseRef pd);
      subst liftedReverseRef; fold g d.


      destSimp g ; destSimp d; (try destSimp t0); (try destSimp t);
      apply correctMemoMap_second_let; 
      rewrite ?OrMemo_Mfalse_r, ?OrMemo_Mfalse_l, ?AndMemo_Mfalse_l.
      all: (try (lazymatch goal with
      | [H : correctMemoMap ?rev ?l |- 
          correctMemoMap ?rev (AnPointerPairAVLMap.add (?g, ?d) (fst (?rest ?l)) (snd (?rest ?l))) ] =>
        apply (correctMemoAdditionEq2 rev (S n) g d);
        only 1: (try (repRewSize; repRewRev; simpl in *; lia; fail));
        reduceAndOr rest IHn l H;
        idtac
      | _ => idtac
      end; fail)).



      (* Need to do the second half of the proof, which could be the same as the first *)
    + Opaque decideOL_bool. simpl. pose proof H0. unfold correctMemoMap in H0.  specialize (H0 [[g]] [[d]]).
      destruct (M.find ([[g]], [[d]]) l) eqn: res; simpl in *.
      * destruct b eqn:b_eq; simpl in *; intro; auto; repRewRev; try congruence.
      * Transparent decideOL_bool. destSimp g; destSimp d; (try destSimp t0); (try destSimp t).
        all: rewrite OL_Reflection_3_fmap.fst_let_simpl; niceSimpl;
             repeat rewrite Bool.orb_false_r; 
             repeat rewrite OrMemo_Mfalse_r; 
             repeat rewrite OrMemo_Mfalse_l.

        all: try ( apply IHn; auto; simpl in *; lia).
        all: try (lazymatch goal with
            | [H : correctMemoMap ?rev ?l |- 
                fst (?rest ?l) = true -> _ ] => 
              reduceAndOr rest IHn l H
            | _ => idtac
            end).
Qed.






Fixpoint AddPointer (t: Term) (p: Pointer): (TermPointer * Pointer) :=
  match t with
  | Var n => (VarP n p, Pos.succ p)
  | Not a => 
      let (t1, p1) := (AddPointer a (Pos.succ p)) in (NotP t1 p, p1)
  | Meet a b => 
      let (t1, p1) := (AddPointer a (Pos.succ p)) in let (t2, p2) := (AddPointer b p1)  in (MeetP t1 t2 p, p2)
  | Join a b => 
      let (t1, p1) := (AddPointer a (Pos.succ p)) in let (t2, p2) := (AddPointer b p1)  in (JoinP t1 t2 p, p2)
  end.



Fixpoint subtermsPointer (t: TermPointer) : list TermPointer :=
  match t with
  | VarP _ _ => [t]
  | NotP a _ => t :: subtermsPointer a
  | MeetP a b _ => t :: subtermsPointer a ++ subtermsPointer b
  | JoinP a b _ => t :: subtermsPointer a ++ subtermsPointer b
  end.

Definition func_of_list (l: list TermPointer) : (Pointer -> TermPointer) := fun p =>
  match find (fun x => Pos.eqb (GetPointer x) p) l with
  | Some x => x
  | None => VarP 0 p
  end.

Definition func_of_AddPointer (t: TermPointer) : (Pointer -> TermPointer) := 
  func_of_list (subtermsPointer t).
      

(* Definition RefMap := {reverseRef : Pointer -> TermPointer | forall p, GetPointer (reverseRef p) = p}. *)


Fixpoint PointerCorrectnessTerm_inter (map : Pointer -> TermPointer) (t: TermPointer): Prop :=
  (map (GetPointer t)) = t /\ 
  match t with
  | VarP _ _ => True
  | MeetP a b _ => PointerCorrectnessTerm_inter map a /\ PointerCorrectnessTerm_inter map b
  | JoinP a b _ => PointerCorrectnessTerm_inter map a /\ PointerCorrectnessTerm_inter map b
  | NotP a _ => PointerCorrectnessTerm_inter map a
  end.

Theorem succ_pos_neq : forall p : positive, p <> (Pos.succ p).
Proof.
  intros p.
  induction p; simpl; intro H; discriminate H.
Qed.


Ltac rewEqs := repeat rewrite Pos.eqb_refl in *; repeat rewrite Pos.eqb_eq in *.



Theorem AddPointerCorrect_1 (t: Term)  : 
  forall p,
  (forall p0, GetPointer (func_of_AddPointer (fst (AddPointer t p)) p0) = p0).
Proof.
  intros. unfold func_of_AddPointer; unfold func_of_list; simpl in *. induction (subtermsPointer (fst (AddPointer t p))); simpl in *; auto.
  destruct a; simpl in *; destruct (p1 =? p0)%positive eqn: equals; simpl in *; repeat rewrite Pos.eqb_eq in *; auto.
Qed.



(* func_of_AddPointer (fst (AddPointer t p)) *)

Fixpoint subterm (t t0: TermPointer) : Prop :=
t = t0 \/
  match t with
  | VarP _ _ => False
  | NotP a _ => subterm a t0
  | MeetP a b _ => subterm a t0 \/ subterm b t0
  | JoinP a b _ => subterm a t0 \/ subterm b t0
  end.



  Ltac unfoldBoth := unfold func_of_AddPointer in *; unfold func_of_list in *; simpl in *.

Theorem funcAdd2Monotone t p0 p:
  p <> p0 ->
  func_of_AddPointer t p0 = func_of_AddPointer (NotP t p) p0.
Proof.
  intros. destruct t; simpl in *; auto.
  all: (unfoldBoth; simpl in *; auto; destruct (p =? p0)%positive eqn:equals; simpl in *; auto; try congruence;
    destruct (p1 =? p0)%positive eqn:equal; simpl in *; rewEqs; try congruence).
Qed.


Theorem GetAddPointer t p:
  GetPointer (fst (AddPointer t p)) = p.
Proof.
  destruct t; simpl in *; auto.
  - destruct (AddPointer t1 (Pos.succ p)); simpl in *; auto. destruct (AddPointer t2 p0); simpl in *; auto.
  - destruct (AddPointer t1 (Pos.succ p)); simpl in *; auto. destruct (AddPointer t2 p0); simpl in *; auto.
  - destruct (AddPointer t (Pos.succ p)); simpl in *; auto.
Qed.
(* AddPointer ta (Pos.succ p) = (t1, p1) *)

Theorem GetAddPointer_eq t p t1 p1:
  AddPointer t p = (t1, p1) ->
  GetPointer t1 = p.
Proof.
  intro. pose proof (GetAddPointer t p). rewrite H in H0. auto.
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

Ltac let_simp := repeat rewrite fst_let_simpl in *; repeat rewrite snd_let_simpl in *.

Theorem subterm_refl t: subterm t t.
Proof.
  destruct t; simpl in *; intuition.
Qed.

Hint Resolve  Pos.lt_succ_diag_r Pos.le_refl 
  : pos_order.
Ltac rewGetAddLeft t p := (erewrite <- (GetAddPointer_eq t p)) ; eauto; eauto using subterm_refl with pos_order.
Ltac rewGetAdd t p := (erewrite (GetAddPointer_eq t p)) ; eauto; eauto using subterm_refl with pos_order.
Ltac lt_trans_succ := eapply Pos.lt_trans with (Pos.succ _); try eapply Pos.lt_succ_diag_r.

Theorem AddPointerReturnsGreater t : 
  forall st,
  forall p,
  subterm (fst (AddPointer t p)) st -> 
  Pos.lt (GetPointer st) (snd (AddPointer t p)).
Proof.
  induction t as [ | ta IHta tb IHtb  | ta IHta tb IHtb  | ta IHta].
  - simpl; intros; intuition; subst; simpl; apply Pos.lt_succ_diag_r .
  - intros. simpl in *. let_simp. pose proof IHta as IHta_.
    specialize (IHta (fst (AddPointer ta (Pos.succ p))) (Pos.succ p)). specialize (IHta_ st (Pos.succ p)).
    destruct (AddPointer ta (Pos.succ p)) as [t1 p1] eqn: eqt; simpl in *.
    pose proof IHtb as IHtb_.
    specialize (IHtb (fst (AddPointer tb p1)) p1). specialize (IHtb_ st p1).
    destruct (AddPointer tb p1) as [t2 p2] eqn: eqt2; simpl in *. repeat destruct H; auto; simpl in *.
    + apply Pos.lt_trans with p1.
      * intuition; subst; simpl in *. apply Pos.lt_trans with (Pos.succ p). apply Pos.lt_succ_diag_r.
         rewGetAddLeft ta (Pos.succ p).
      * rewGetAddLeft tb p1.
    + apply Pos.lt_trans with p1; intuition. rewGetAddLeft tb p1.
  - intros. simpl in *. let_simp. pose proof IHta as IHta_.
    specialize (IHta (fst (AddPointer ta (Pos.succ p))) (Pos.succ p)). specialize (IHta_ st (Pos.succ p)).
    destruct (AddPointer ta (Pos.succ p)) as [t1 p1] eqn: eqt; simpl in *.
    pose proof IHtb as IHtb_.
    specialize (IHtb (fst (AddPointer tb p1)) p1). specialize (IHtb_ st p1).
    destruct (AddPointer tb p1) as [t2 p2] eqn: eqt2; simpl in *. repeat destruct H; auto; simpl in *.
    + apply Pos.lt_trans with p1.
      * intuition; subst; simpl in *. lt_trans_succ. rewGetAddLeft ta (Pos.succ p).
      * rewGetAddLeft tb p1.
    + apply Pos.lt_trans with p1; intuition. rewGetAddLeft tb p1.
  - intros. simpl in *. let_simp. pose proof IHta as IHta_. 
    specialize (IHta (fst (AddPointer ta (Pos.succ p))) (Pos.succ p)). specialize (IHta_ st (Pos.succ p)).
    destruct (AddPointer ta (Pos.succ p)) eqn: eqt; simpl in *.
    intuition; subst; simpl in *. lt_trans_succ. rewGetAddLeft ta (Pos.succ p).
Qed.




Theorem subterm_trans t1 t2 t3:
  subterm t1 t2 -> subterm t2 t3 -> subterm t1 t3.
Proof.
  intros. induction t1; simpl in *; intuition.
  all: subst; simpl in *; intuition.
Qed.  

Theorem AddPointerMonotone t :
  forall st,
  forall p,
  subterm (fst (AddPointer t p)) st -> 
  ((fst (AddPointer t p)) = st \/ (Pos.lt (GetPointer (fst (AddPointer t p))) (GetPointer st))).
Proof.
  induction t as [ | ta IHta tb IHtb  | ta IHta tb IHtb  | ta IHta]; intros; simpl in *.
  - intuition.
  - pose proof IHta as IHta_. specialize (IHta st (Pos.succ p)). specialize (IHta_ (fst (AddPointer ta (Pos.succ p))) (Pos.succ p)).
    destruct (AddPointer ta (Pos.succ p)) as [ta1 pa1] eqn: taeq; simpl in *.
    pose proof IHtb as IHtb_. specialize (IHtb st pa1). specialize (IHtb_ (fst (AddPointer tb pa1)) (Pos.succ p)).
    destruct (AddPointer tb pa1) as [tb1 pb1] eqn: taeq_tb; simpl in *. destruct H.
    + left. auto.
    + right.
      destruct H.
      *  specialize (IHta H). destruct IHta.
        ** subst; simpl in *; rewGetAdd ta (Pos.succ p).
        ** apply Pos.lt_trans with (GetPointer ta1); auto; rewGetAdd ta (Pos.succ p).
      * specialize (IHtb H).
        assert (p < pa1)%positive as Hpa1.
        lt_trans_succ. 
        pose proof (GetAddPointer ta (Pos.succ p)). rewrite <- H0. 
        pose proof (AddPointerReturnsGreater ta ta1 (Pos.succ p)). rewrite taeq in *. simpl in *. auto using subterm_refl.
        destruct IHtb.
        ** subst; simpl in *; rewGetAdd tb pa1.
        ** apply Pos.lt_trans with (GetPointer tb1); auto; rewGetAdd tb pa1.
  - pose proof IHta as IHta_. specialize (IHta st (Pos.succ p)). specialize (IHta_ (fst (AddPointer ta (Pos.succ p))) (Pos.succ p)).
    destruct (AddPointer ta (Pos.succ p)) as [ta1 pa1] eqn: taeq; simpl in *.
    pose proof IHtb as IHtb_. specialize (IHtb st pa1). specialize (IHtb_ (fst (AddPointer tb pa1)) (Pos.succ p)).
    destruct (AddPointer tb pa1) as [tb1 pb1] eqn: taeq_tb; simpl in *. destruct H.
    + left. auto.
    + right.
      destruct H.
      *  specialize (IHta H). destruct IHta.
        ** subst; simpl in *; rewGetAdd ta (Pos.succ p).
        ** apply Pos.lt_trans with (GetPointer ta1); auto; rewGetAdd ta (Pos.succ p).
      * specialize (IHtb H).
        assert (p < pa1)%positive as Hpa1.
        lt_trans_succ. 
        pose proof (GetAddPointer ta (Pos.succ p)). rewrite <- H0. 
        pose proof (AddPointerReturnsGreater ta ta1 (Pos.succ p)). rewrite taeq in *. simpl in *. auto using subterm_refl.
        destruct IHtb.
        ** subst; simpl in *; rewGetAdd tb pa1.
        ** apply Pos.lt_trans with (GetPointer tb1); auto; rewGetAdd tb pa1.
  - pose proof IHta as IHta_. specialize (IHta st (Pos.succ p)). specialize (IHta_ (fst (AddPointer ta (Pos.succ p))) (Pos.succ p)).
    destruct (AddPointer ta (Pos.succ p)) as [t1 p1] eqn: taeq; simpl in *. destruct H.
    + left. auto.
    + right. specialize (IHta H). destruct IHta.
      * subst; simpl in *; rewGetAdd ta (Pos.succ p).
      * apply Pos.lt_trans with (GetPointer t1); auto; rewGetAdd ta (Pos.succ p).

Qed.

Theorem AddPointerMonotone2 t :
  forall st,
  forall p,
  subterm (fst (AddPointer t p)) st -> 
  (Pos.le (GetPointer (fst (AddPointer t p))) (GetPointer st)).
Proof.
  intros. pose proof AddPointerMonotone t st p H. intuition.
  - subst; simpl in *. apply Pos.le_refl.
  - apply Pos.lt_le_incl; auto.
Qed. 

Ltac solveCaseEqSubterm p st1 st2 IHta_ :=
    let H := fresh "H" in let H0 := fresh "H" in
      lazymatch goal with
      | [ Hst1: _ = st1,
        eqt: AddPointer ?ta (Pos.succ ?p) = (?t1, ?p1),
        H_GP : GetPointer _ = GetPointer _,
        Hst2: subterm ?t1 st2 
        |- _ ] => 
        assert (Pos.lt (GetPointer st1) (GetPointer st2)) as H; try (rewrite H_GP in H; apply Pos.lt_irrefl in H; contradiction);
        subst; simpl in *; apply Pos.lt_le_trans with (Pos.succ p); try apply Pos.lt_succ_diag_r;
        (try rewGetAddLeft ta (Pos.succ p));
        pose proof (AddPointerMonotone2 ta st2 (Pos.succ p)) as H0; rewrite eqt in H0; simpl in *; intuition;
        idtac
      | [ Hst1: _ = st1,
        eqt: AddPointer ?ta (Pos.succ ?p) = (?t1, ?p1),
        eqt2 : AddPointer ?tb ?p1 = (?t2, ?p2),
        H_GP : GetPointer _ = GetPointer _,
        Hst2: subterm ?t2 st2 
        |- _ ] => 
        pose proof 1 as detected;
        assert (Pos.lt (GetPointer st1) (GetPointer st2)) as H; try (rewrite H_GP in H; apply Pos.lt_irrefl in H; contradiction);
        subst; simpl in *; apply Pos.lt_le_trans with p1;
        try (rewGetAddLeft tb p1; pose proof (AddPointerMonotone2 tb st2 p1) as H0; rewrite eqt2 in H0; simpl in *; intuition; fail);
        lt_trans_succ; rewGetAddLeft ta (Pos.succ p);
        pose proof (AddPointerReturnsGreater ta t1 (Pos.succ p)) as APRG_ta; rewrite eqt in APRG_ta; simpl in *; apply APRG_ta; apply subterm_refl;
        idtac
      | [ Hst1: subterm ?t1 st1,
        eqt: AddPointer ?ta (Pos.succ ?p) = (?t1, ?p1),
        eqt2 : AddPointer ?tb ?p1 = (?t2, ?p2),
        H_GP : GetPointer _ = GetPointer _,
        Hst2: subterm ?t2 st2 
        |- _ ] =>
        assert (Pos.lt (GetPointer st1) (GetPointer st2)) as H; try (rewrite H_GP in H; apply Pos.lt_irrefl in H; contradiction);
        apply Pos.lt_le_trans with p1;
        try (rewGetAddLeft tb p1; pose proof (AddPointerMonotone2 tb st2 p1) as H0; rewrite eqt2 in H0; simpl in *; intuition; fail);
        pose proof (AddPointerReturnsGreater ta st1 (Pos.succ p)) as APRG_ta; rewrite eqt in APRG_ta; simpl in *; auto;
        
        idtac

      end.

Theorem AddPointerNoDuplicate t :
  forall st1 st2,
  forall p,
  subterm (fst (AddPointer t p)) st1 -> 
  subterm (fst (AddPointer t p)) st2 -> 
  GetPointer st1 = GetPointer st2 ->
  st1 = st2.
Proof.
  induction t as [ | ta IHta tb IHtb  | ta IHta tb IHtb  | ta IHta].
  - intros; simpl in *; intuition; subst; reflexivity.
  - intros ??? Hst1 Hst2 H_GP; simpl in *; pose proof IHta as IHta_.
    specialize (IHta st1 st2 (Pos.succ p)). 
    destruct (AddPointer ta (Pos.succ p)) as [t1 p1] eqn: eqt; simpl in *.
    destruct (AddPointer tb p1) as [t2 p2] eqn: eqt2; simpl in *.
    repeat destruct Hst1 as [Hst1 | Hst1]; repeat destruct Hst2 as [Hst2 | Hst2];
    intuition; try congruence.
    all: try (solveCaseEqSubterm p st1 st2 IHta_; fail).
    all: try (solveCaseEqSubterm p st2 st1 IHta_; fail).
    + specialize (IHtb st1 st2 p1). rewrite eqt2 in IHtb. simpl in *. intuition.
  - intros ??? Hst1 Hst2 H_GP; simpl in *; pose proof IHta as IHta_.
    specialize (IHta st1 st2 (Pos.succ p)). 
    destruct (AddPointer ta (Pos.succ p)) as [t1 p1] eqn: eqt; simpl in *.
    destruct (AddPointer tb p1) as [t2 p2] eqn: eqt2; simpl in *.
    repeat destruct Hst1 as [Hst1 | Hst1]; repeat destruct Hst2 as [Hst2 | Hst2];
    intuition; try congruence.
    all: try (solveCaseEqSubterm p st1 st2 IHta_; fail).
    all: try (solveCaseEqSubterm p st2 st1 IHta_; fail).
    + specialize (IHtb st1 st2 p1). rewrite eqt2 in IHtb. simpl in *. intuition.
  - intros ??? Hst1 Hst2 H_GP; simpl in *. pose proof IHta as IHta_.
    specialize (IHta st1 st2 (Pos.succ p)). 
    destruct (AddPointer ta (Pos.succ p)) as [t1 p1] eqn: eqt; simpl in *.
    destruct Hst1 as [Hst1 | Hst1]; destruct Hst2 as [Hst2 | Hst2]; 
    intuition; try congruence.
    + solveCaseEqSubterm p st1 st2 IHta_.
    + solveCaseEqSubterm p st2 st1 IHta_.
Qed.

Theorem FindListHalf {A: Type} f (l1 l2: list A) e:
  find f l1 = Some e -> find f (l1 ++ l2) = Some e.
Proof.
  induction l1 as [ | head tail].
  - simpl in *. intros. congruence.
  - simpl in *. intro. destruct (f head); auto.
Qed.

Theorem FindListSndHalf {A: Type} f (l1 l2: list A):
  find f l1 = None -> find f (l1 ++ l2) = find f l2.
Proof.
  induction l1 as [ | head tail].
  - simpl in *. intros. congruence.
  - simpl in *. intro. destruct (f head); auto; try congruence.
Qed.

Theorem SubpointersHead t1 head tail:
  subtermsPointer t1 = head :: tail ->
  t1 = head.
Proof.
  destruct t1; simpl in *; congruence.
Qed.



Definition sbt := subtermsPointer. 


(*
Definition subtermsPointerList (l: list TermPointer) : list TermPointer := 
  flat_map subtermsPointer l.
*)



Theorem SubtermInList t :
  forall p st,
  In st (subtermsPointer (fst (AddPointer t p))) -> subterm (fst (AddPointer t p)) st.
Proof.
  induction t as [ | ta IHta tb IHtb  | ta IHta tb IHtb  | ta IHta]; intros; simpl in *; intuition.
  - destruct (AddPointer ta (Pos.succ p)) as [t1 p1] eqn: eqt_ta; simpl in *.
    destruct (AddPointer tb p1) as [t2 p2] eqn: eqt_tb; simpl in *. intuition.
    right. rewrite in_app_iff in H0. destruct H0.
    + pose proof (IHta (Pos.succ p) st). rewrite eqt_ta in H0. simpl in *. intuition.
    + pose proof (IHtb p1 st). rewrite eqt_tb in H0. simpl in *. intuition.
  - destruct (AddPointer ta (Pos.succ p)) as [t1 p1] eqn: eqt_ta; simpl in *.
    destruct (AddPointer tb p1) as [t2 p2] eqn: eqt_tb; simpl in *. intuition.
    right. rewrite in_app_iff in H0. destruct H0.
    + pose proof (IHta (Pos.succ p) st). rewrite eqt_ta in H0. simpl in *. intuition.
    + pose proof (IHtb p1 st). rewrite eqt_tb in H0. simpl in *. intuition.
  - destruct (AddPointer ta (Pos.succ p)) as [tap p1] eqn: eqt_ta; simpl in *. intuition.
    right. pose proof (IHta (Pos.succ p) st). rewrite eqt_ta in H. simpl in *. apply H. auto.
Qed.



Theorem inListPointer ta p t1 p1 st:
  AddPointer ta (Pos.succ p) = (t1, p1) ->
  In st (subtermsPointer t1) -> (GetPointer st < p1)%positive.
Proof.
  intros. pose proof (SubtermInList ta (Pos.succ p) st). rewrite H in H1. simpl in *. intuition.
  pose proof (AddPointerReturnsGreater ta st (Pos.succ p)). rewrite H in H1. simpl in *. intuition.
Qed.

Theorem find_classical {A: Type} f (l: list A):
  ((exists r, find f l = Some r) -> False) ->
  find f l = None.
Proof.
  intros; destruct (find f l); intuition.
  exfalso; apply H. exists a; auto.
Qed.

Theorem find_some_in {A: Type} f (l: list A) x:
  find f l = Some x -> In x l.
Proof.
  apply find_some.
Qed.


Theorem find_some_sat {A: Type} f (l: list A) x:
  find f l = Some x -> f x = true.
  apply find_some.
Qed.

Theorem FindTooSmall ta p t1 p1 tp:
  AddPointer ta (Pos.succ p) = (t1, p1) ->
  (p1 <= GetPointer tp)%positive ->
  find (fun x : TermPointer => (GetPointer x =? GetPointer tp)%positive) (subtermsPointer t1) = None.
Proof.
  intros. 
  assert (forall r, (p1 <= GetPointer r)%positive -> In r (subtermsPointer t1) -> False).
  - intros. pose proof (inListPointer ta p t1 p1 r H H2) as ILPintuition. apply H1. apply Pos.lt_gt. auto.
  - apply find_classical; intros.
    destruct H2 as [r]. apply H1 with r. clear H1.

    + assert (GetPointer r = GetPointer tp) as gpr_gpt; try rewrite gpr_gpt in *; auto.
      rewrite <- Pos.eqb_eq.
      eauto using (find_some_sat (fun x : TermPointer => (GetPointer x =? GetPointer tp)%positive) ).
    + eauto using find_some_in.
Defined.




Theorem AddPointerCorrect_2 (t: Term) :
  forall p ,
  forall tp,
  subterm (fst (AddPointer t p)) tp -> 
  find (fun x => Pos.eqb (GetPointer x) (GetPointer tp)) (subtermsPointer (fst (AddPointer t p))) = Some tp.
Proof.

  induction t as [ | ta IHta tb IHtb  | ta IHta tb IHtb  | ta IHta].
  - simpl in *. intros; intuition; subst; simpl in *. unfoldBoth; auto; intuition. 
    destruct (p =? p)%positive eqn: equal; auto. rewrite Pos.eqb_refl in equal; subst; congruence.
  - intros ?? H_st. simpl in *. 
    destruct (AddPointer ta (Pos.succ p)) as [t1 p1] eqn: eqt; simpl in *.
    destruct (AddPointer tb p1) as [t2 p2] eqn: eqt2; simpl in *.
    repeat destruct H_st as [H_st | H_st]; intuition; subst; simpl in *; unfoldBoth; simpl in *; auto.
    + rewrite Pos.eqb_refl; simpl in *; auto.
    + destruct (Pos.eqb p (GetPointer tp)) eqn: equal; simpl in *; auto.
      * rewrite Pos.eqb_eq in equal.
        assert (Pos.lt p (GetPointer tp) ) as H; try (subst; apply Pos.lt_irrefl in H; intuition; fail).
        apply Pos.lt_le_trans with (Pos.succ p). apply Pos.lt_succ_diag_r.
        rewGetAddLeft ta (Pos.succ p). 
        pose proof (AddPointerMonotone2 ta tp (Pos.succ p)). rewrite eqt in H; simpl in *; auto.
      * specialize (IHta (Pos.succ p) tp ). rewrite eqt in IHta. simpl in *. auto. apply FindListHalf; auto.
    + destruct (Pos.eqb p (GetPointer tp)) eqn: equal; simpl in *; auto.
      * rewrite Pos.eqb_eq in equal.
        assert (Pos.lt p (GetPointer tp) ) as H; try (subst; apply Pos.lt_irrefl in H; intuition; fail).
        apply Pos.lt_le_trans with (Pos.succ p). apply Pos.lt_succ_diag_r.
        rewGetAddLeft ta (Pos.succ p). 
        apply Pos.le_trans with p1.
        ** pose proof (AddPointerReturnsGreater ta t1 (Pos.succ p)) as APRG_ta; rewrite eqt in APRG_ta; simpl in *. 
           apply Pos.lt_le_incl; apply APRG_ta; apply subterm_refl.
        ** rewGetAddLeft tb p1.
           pose proof (AddPointerMonotone2 tb tp p1). rewrite eqt2 in H; simpl in *; auto.
      * specialize (IHtb p1 tp). rewrite eqt2 in IHtb. simpl in *. rewrite <-IHtb; auto. apply FindListSndHalf; auto.
        assert (Pos.le p1 (GetPointer tp)) as H. rewGetAddLeft tb p1.
        pose proof (AddPointerMonotone2 tb tp p1). rewrite eqt2 in H; simpl in *; auto.
        eapply FindTooSmall; eauto.
  - intros ?? H_st. simpl in *. 
    destruct (AddPointer ta (Pos.succ p)) as [t1 p1] eqn: eqt; simpl in *.
    destruct (AddPointer tb p1) as [t2 p2] eqn: eqt2; simpl in *.
    repeat destruct H_st as [H_st | H_st]; intuition; subst; simpl in *; unfoldBoth; simpl in *; auto.
    + rewrite Pos.eqb_refl; simpl in *; auto.
    + destruct (Pos.eqb p (GetPointer tp)) eqn: equal; simpl in *; auto.
      * rewrite Pos.eqb_eq in equal.
        assert (Pos.lt p (GetPointer tp) ) as H; try (subst; apply Pos.lt_irrefl in H; intuition; fail).
        apply Pos.lt_le_trans with (Pos.succ p). apply Pos.lt_succ_diag_r.
        rewGetAddLeft ta (Pos.succ p). 
        pose proof (AddPointerMonotone2 ta tp (Pos.succ p)). rewrite eqt in H; simpl in *; auto.
      * specialize (IHta (Pos.succ p) tp ). rewrite eqt in IHta. simpl in *. auto. apply FindListHalf; auto.
    + destruct (Pos.eqb p (GetPointer tp)) eqn: equal; simpl in *; auto.
      * rewrite Pos.eqb_eq in equal.
        assert (Pos.lt p (GetPointer tp) ) as H; try (subst; apply Pos.lt_irrefl in H; intuition; fail).
        apply Pos.lt_le_trans with (Pos.succ p). apply Pos.lt_succ_diag_r.
        rewGetAddLeft ta (Pos.succ p). 
        apply Pos.le_trans with p1.
        ** pose proof (AddPointerReturnsGreater ta t1 (Pos.succ p)) as APRG_ta; rewrite eqt in APRG_ta; simpl in *. 
           apply Pos.lt_le_incl; apply APRG_ta; apply subterm_refl.
        ** rewGetAddLeft tb p1.
           pose proof (AddPointerMonotone2 tb tp p1). rewrite eqt2 in H; simpl in *; auto.
      * specialize (IHtb p1 tp). rewrite eqt2 in IHtb. simpl in *. rewrite <-IHtb; auto. apply FindListSndHalf; auto.
        assert (Pos.le p1 (GetPointer tp)) as H. rewGetAddLeft tb p1.
        pose proof (AddPointerMonotone2 tb tp p1). rewrite eqt2 in H; simpl in *; auto.
        eapply FindTooSmall; eauto.
  - intros ?? H_st. simpl in *. destruct (AddPointer ta (Pos.succ p)) as [t1 p1] eqn: eqt; simpl in *.
    destruct H_st as [H_st | H_st]; intuition; subst; simpl in *; unfoldBoth; simpl in *; auto.
    + rewrite Pos.eqb_refl; simpl in *; auto.
    + destruct (Pos.eqb p (GetPointer tp)) eqn: equal; simpl in *; auto.
      * rewrite Pos.eqb_eq in equal.
        assert (Pos.lt p (GetPointer tp) ) as H; try (subst; apply Pos.lt_irrefl in H; intuition; fail).
        apply Pos.lt_le_trans with (Pos.succ p). apply Pos.lt_succ_diag_r.
        rewGetAddLeft ta (Pos.succ p). 
        pose proof (AddPointerMonotone2 ta tp (Pos.succ p)). rewrite eqt in H; simpl in *; auto.
      * specialize (IHta (Pos.succ p) tp ). rewrite eqt in IHta. simpl in *. auto.
Qed. 


Theorem AddPointerCorrect_3 (t: Term) :
  forall p ,
  forall tp,
  subterm (fst (AddPointer t p)) tp -> 
  func_of_AddPointer (fst (AddPointer t p)) (GetPointer tp) = tp.
Proof.
  intros. unfoldBoth. rewrite AddPointerCorrect_2; auto.
Qed.


  Ltac apc23 t p := pose proof (AddPointerCorrect_3 t p (fst (AddPointer t p))) as H; simpl in *.

Theorem AddPointerCorrect_4 (t: Term) :
  forall p ,
  forall tp,
  subterm (fst (AddPointer t p)) tp -> 
  PointerCorrectnessTerm_inter (func_of_AddPointer (fst (AddPointer t p))) tp.
Proof.
  induction tp as [ | tpa IHtpa tpb IHtpb  | tpa IHtpa tpb IHtpb  | tpa IHtpa]; intros; simpl in *; simpl in *;
  intros.
  - intuition. pose proof (AddPointerCorrect_3 t p (VarP n p0)). intuition.
  - intuition.
    + pose proof (AddPointerCorrect_3 t p (MeetP tpa tpb p0)). simpl in *. intuition.
    + apply IHtpa. eapply subterm_trans; eauto; simpl in *. right. left. apply subterm_refl.
    + apply IHtpb. eapply subterm_trans; eauto; simpl in *. right. right. apply subterm_refl.
  - intuition.
    + pose proof (AddPointerCorrect_3 t p (JoinP tpa tpb p0)). simpl in *. intuition.
    + apply IHtpa. eapply subterm_trans; eauto; simpl in *. right. left. apply subterm_refl.
    + apply IHtpb. eapply subterm_trans; eauto; simpl in *. right. right. apply subterm_refl.
  - pose proof (AddPointerCorrect_3 t p (NotP tpa p0)). simpl in *. intuition.
    apply IHtpa. eapply subterm_trans; eauto; simpl in *. right. apply subterm_refl.
Qed.








Theorem AddPointerCorrect_5 (t: Term) :
  forall p,
  PointerCorrectnessTerm_inter (func_of_AddPointer (fst (AddPointer t p))) (fst (AddPointer t p)).
Proof.
  intros.
  apply (AddPointerCorrect_4 t p (fst (AddPointer t p))). apply subterm_refl.
Qed.





Definition AddAnPointer (t: AnTerm) (p: Pointer): (AnTermPointer * Pointer) :=
  match t with
  | L a => let (t1, p1) := (AddPointer a p) in (LTP t1, p1)
  | R a => let (t1, p1) := (AddPointer a p) in (RTP t1, p1)
  | OL_Theory.N => (NTP, p)
  end.

Definition pairAnTerm_to_Term (ant1 ant2: AnTerm) : Term :=
  match (ant1, ant2) with
  | (L t1, L t2) => Meet t1 t2
  | (L t1, R t2) => Meet t1 t2
  | (R t1, L t2) => Meet t1 t2
  | (R t1, R t2) => Meet t1 t2
  | (OL_Theory.N, L t2) => Not t2
  | (OL_Theory.N, R t2) => Not t2
  | (L t1, OL_Theory.N) => Not t1
  | (R t1, OL_Theory.N) => Not t1
  | (OL_Theory.N, OL_Theory.N) => Var 0
  end.

Definition func_of_AddAnPointerTwice (ant1 ant2: AnTerm) : (Pointer -> TermPointer) :=
  func_of_AddPointer ((fst (AddPointer (pairAnTerm_to_Term ant1 ant2) xH))).

Theorem func_to_RefMap (ant1 ant2: AnTerm) : RefMap.
Proof.
  exists (func_of_AddAnPointerTwice ant1 ant2).
  intros. apply AddPointerCorrect_1.
Defined.
  

Definition AddAnPointerTwice (t1 t2: AnTerm) (p: Pointer): (AnTermPointer * AnTermPointer * Pointer) :=
  let (t1, p1) := (AddAnPointer t1 p) in let (t2, p2) := (AddAnPointer t2 p1) in (t1, t2, p2).

Definition decideOL_pointer_at (g d: AnTerm): bool :=
  let (gd,  _) := AddAnPointerTwice g d 2%positive in let (g1, d1) := gd in 
  fst (decideOL_pointer_atp (anSize g + anSize d) g1 d1 (AnPointerPairAVLMap.empty bool)).



Theorem ForgetAddInverse t :
  forall p,
  ForgetPointer (fst (AddPointer t p)) = t.
Proof. 
  induction t; simpl in *; auto.
  - intros. destruct (AddPointer t1 (Pos.succ p)) as [t1' p1] eqn: eqt1. destruct (AddPointer t2 p1) as [t2' p2] eqn: eqt2.
    simpl in *. apply f_equal2. specialize (IHt1 (Pos.succ p)). rewrite eqt1 in IHt1. simpl in *. auto.
    specialize (IHt2 p1). rewrite eqt2 in IHt2. simpl in *. auto.
  - intros. destruct (AddPointer t1 (Pos.succ p)) as [t1' p1] eqn: eqt1. destruct (AddPointer t2 p1) as [t2' p2] eqn: eqt2.
    simpl in *. apply f_equal2. specialize (IHt1 (Pos.succ p)). rewrite eqt1 in IHt1. simpl in *. auto.
    specialize (IHt2 p1). rewrite eqt2 in IHt2. simpl in *. auto.
  - intros. destruct (AddPointer t (Pos.succ p)) as [t1' p1] eqn: eqt1.
    simpl in *. apply f_equal. specialize (IHt (Pos.succ p)). rewrite eqt1 in IHt. simpl in *. auto.
Qed.  

Theorem AnForgetAddInverse g :
  forall p,
  ForgetAnPointer (fst (AddAnPointer g p)) = g.
Proof.
  intros. destruct g; simpl in *; try congruence; rewrite fst_let_simpl; simpl in *; rewrite ForgetAddInverse; auto.
Qed.

(*
Theorem lif_cast refmap g1 : LiftReverseRef refmap [[g1]] = g1.
destruct g1; simpl in *; auto; destruct refmap as [f]; simpl in *; auto; apply f_equal.
*)

Theorem TermPSize_irell_p t :
  forall p1 p2,
  termPSize (fst (AddPointer t p1)) = termPSize (fst (AddPointer t p2)).
Proof.
  induction t; simpl in *; auto; intros.
  - destruct (AddPointer t1 (Pos.succ p1)) as [t1' p1'] eqn: eqt1. destruct (AddPointer t2 p1') as [t2' p2'] eqn: eqt2.
    destruct (AddPointer t1 (Pos.succ p2)) as [t1'' p1''] eqn: eqt1'. destruct (AddPointer t2 p1'') as [t2'' p2''] eqn: eqt2'.
    simpl in *. apply f_equal.
    specialize (IHt1 (Pos.succ p1) (Pos.succ p2)). specialize (IHt2 p1' p1''). 
    rewrite eqt1 in IHt1. rewrite eqt2 in IHt2. simpl in *.
    rewrite eqt1' in IHt1. rewrite eqt2' in IHt2. simpl in *. lia.
  - destruct (AddPointer t1 (Pos.succ p1)) as [t1' p1'] eqn: eqt1. destruct (AddPointer t2 p1') as [t2' p2'] eqn: eqt2.
    destruct (AddPointer t1 (Pos.succ p2)) as [t1'' p1''] eqn: eqt1'. destruct (AddPointer t2 p1'') as [t2'' p2''] eqn: eqt2'.
    simpl in *. apply f_equal.
    specialize (IHt1 (Pos.succ p1) (Pos.succ p2)). specialize (IHt2 p1' p1''). 
    rewrite eqt1 in IHt1. rewrite eqt2 in IHt2. simpl in *.
    rewrite eqt1' in IHt1. rewrite eqt2' in IHt2. simpl in *. lia.
  - destruct (AddPointer t (Pos.succ p1)) as [t1' p1'] eqn: eqt1. destruct (AddPointer t (Pos.succ p2)) as [t2' p2'] eqn: eqt2.
    simpl in *. apply f_equal. specialize (IHt (Pos.succ p1) (Pos.succ p2)). rewrite eqt1 in IHt. rewrite eqt2 in IHt. simpl in *. lia.
Qed.

Theorem termSize_eq_termPSize t :
  forall p,
  termSize t = termPSize (fst (AddPointer t p)).
Proof.
  induction t; simpl in *; auto; intros.
  - specialize (IHt1 (Pos.succ p)). specialize (IHt2 p). 
    destruct (AddPointer t1 (Pos.succ p)) as [t1' p1] eqn: eqt1.
    simpl in *.
     destruct (AddPointer t2 p1) as [t2' p2] eqn: eqt2.
    simpl in *. apply f_equal. erewrite TermPSize_irell_p in IHt2 . rewrite eqt2 in IHt2. simpl in *. rewrite IHt2. auto.
  - specialize (IHt1 (Pos.succ p)). specialize (IHt2 p). 
    destruct (AddPointer t1 (Pos.succ p)) as [t1' p1] eqn: eqt1.
    simpl in *.
     destruct (AddPointer t2 p1) as [t2' p2] eqn: eqt2.
    simpl in *. apply f_equal. erewrite TermPSize_irell_p in IHt2 . rewrite eqt2 in IHt2. simpl in *. rewrite IHt2. auto.
  - specialize (IHt (Pos.succ p)). 
    destruct (AddPointer t (Pos.succ p)) as [t1' p1] eqn: eqt1.
    simpl in *. congruence.
Qed.
  

Theorem anSize_eq_anPSize_Add g p:
  anSize (g) = anPSize (fst (AddAnPointer g p)).
Proof.
  destruct g; simpl in *; auto; rewrite fst_let_simpl; simpl in *; auto using termSize_eq_termPSize.
Qed.


(*
Theorem AddPointerCorrect_6 t d g p1 :
  forall p,
  AddAnPointer g 1%positive = (NTP, p1) ->
  AddAnPointer d p1 = (LTP t, p) ->
  AddAnPointer d (Pos.succ p1) = (LTP t, p) ->
  subterm (fst (AddPointer (pairAnTerm_to_Term g d) p1 )) t.
Proof.
  intros.
  destruct g eqn: dest_g; destruct d eqn: dest_d; simpl in *;  unfold pairAnTerm_to_Term; try congruence.
  - destruct (AddPointer t0 (Pos.succ p1)) as [t1 p2] eqn: eqt1; simpl in *. assert( t1 = t); try congruence; subst. auto using subterm_refl.
  - destruct (AddPointer t0 (Pos.succ p1)) as [t1 p2] eqn: eqt1; simpl in *. assert (t1 = t); try congruence; subst; auto using subterm_refl.
  -
  
   destruct (AddPointer t1 (Pos.succ p1)) eqn: eqt1; simpl in *.
    assert (t2 = t); try congruence. rewrite H0 in *; clear H0. clear H.
    destruct (AddPointer t0 (Pos.succ p1)) eqn: eqt2; simpl in *.
    destruct (AddPointer t1 p2) eqn: eqt3; simpl in *. subst. 

    assert (t2 = t); try congruence; subst; auto using subterm_refl. right.



  all:  try destruct (AddPointer t0 p1) as [t1 p2] eqn: eqt1; simpl in *; 
        try destruct (AddPointer t1 p) as [t2 p3] eqn: eqt2; simpl in *;
        try destruct (AddPointer t0 (Pos.succ p1)) as [t3 p4] eqn: eqt3; simpl in *;
        try destruct (AddPointer t3 p) as [t4 p5] eqn: eqt4; simpl in *; try congruence.

  -all: do 5 try destruct AddPointer; auto.
  all: unfold pairAnTerm_to_Term; simpl in *; intuition.
  all:
*)

        Ltac substAll := 
      let Ha := fresh "Ha" in let Hb := fresh "Hb" in
        lazymatch goal with 
        | [H: (?a1, ?a2) = (?b1, ?b2) |- _] => assert (a1=b1) as Ha; assert (a2=b2) as Hb; try congruence; subst; clear H
        | [H: ?a = ?a |- _] => clear H
        | [H: ?c ?a = ?c ?b |- _] => try (assert (a=b) as Ha; only 1: (congruence; fail); subst; clear H)
        end.

(* Fixpoint PointerCorrectnessTerm_inter (map : Pointer -> TermPointer) (t: TermPointer): Prop :=
  (map (GetPointer t)) = t /\ 
  match t with
  | VarP _ _ => True
  | MeetP a b _ => PointerCorrectnessTerm_inter map a /\ PointerCorrectnessTerm_inter map b
  | JoinP a b _ => PointerCorrectnessTerm_inter map a /\ PointerCorrectnessTerm_inter map b
  | NotP a _ => PointerCorrectnessTerm_inter map a
  end.
*)

(*
Fixpoint PointerCorrectnessTerm (reverseRef : RefMap) (t: TermPointer): Prop :=
  (pointsTo reverseRef (GetPointer t)) = t /\ 
  match t with
  | VarP _ _ => True
  | MeetP a b _ => PointerCorrectnessTerm reverseRef a /\ PointerCorrectnessTerm reverseRef b
  | JoinP a b _ => PointerCorrectnessTerm reverseRef a /\ PointerCorrectnessTerm reverseRef b
  | NotP a _ => PointerCorrectnessTerm reverseRef a
  end.
  *)

Theorem subtermMeetP_1 p t1 t2 :
  subterm (MeetP t1 t2 p) t1 .
Proof.
  simpl in *. right; left; apply subterm_refl.
Qed.
Theorem subtermMeetP_2 p t1 t2 :
  subterm (MeetP t1 t2 p) t2 .
Proof.
  simpl in *. right; right; apply subterm_refl.
Qed.

Theorem subtermJoinP_1 p t1 t2 :
  subterm (JoinP t1 t2 p) t1 .
Proof.
  simpl in *. right; left; apply subterm_refl.
Qed.
Theorem subtermJoinP_2 p t1 t2 :
  subterm (JoinP t1 t2 p) t2 .
Proof.
  simpl in *. right; right; apply subterm_refl.
Qed.

Theorem subtermNotP p t :
  subterm (NotP t p) t.
Proof.
  simpl in *. right; apply subterm_refl.
Qed.


Opaque subterm.

Ltac solve_LL_LR_RL_RR tg td t:= 
  induction t as [ n p| t1 IHt1 t2 IHt2 | t1 IHt1 t2 IHt2 | t IHt]; intros; simpl in *;
  try ( pose proof (AddPointerCorrect_4 (Meet tg td) 1%positive (VarP n p)) as APC5; simpl in *;
            unfold func_of_AddAnPointerTwice; simpl in *; repeat (rewrite fst_let_simpl; simpl);
            destruct (AddPointer tg 2%positive) as [t p0] eqn: eq_tg; simpl in *;
            destruct (AddPointer td p0) eqn: eq_td; simpl in *; intuition; fail);
  try ( pose proof (AddPointerCorrect_4 (Meet tg td) 1%positive (MeetP t1 t2 p)) as APC5; simpl in *;
            unfold func_of_AddAnPointerTwice; simpl in *; repeat (rewrite fst_let_simpl; simpl);
            destruct (AddPointer tg 2%positive) as [t p0] eqn: eq_tg; simpl in *;
            destruct (AddPointer td p0) eqn: eq_td; simpl in *; intuition; 
            try (apply IHt1; auto; eapply subterm_trans; eauto using subtermMeetP_1);
            try (apply IHt2; auto; eapply subterm_trans; eauto using subtermMeetP_2); fail);
  try ( pose proof (AddPointerCorrect_4 (Meet tg td) 1%positive (JoinP t1 t2 p)) as APC5; simpl in *;
            unfold func_of_AddAnPointerTwice; simpl in *; repeat (rewrite fst_let_simpl; simpl);
            destruct (AddPointer tg 2%positive) as [t p0] eqn: eq_tg; simpl in *;
            destruct (AddPointer td p0) eqn: eq_td; simpl in *; intuition;
            try (apply IHt1; auto; eapply subterm_trans; eauto using subtermJoinP_1);
            try (apply IHt2; auto; eapply subterm_trans; eauto using subtermJoinP_2); fail);
      ( pose proof (AddPointerCorrect_4 (Meet tg td) 1%positive (NotP t p)) as APC5; simpl in *;
            unfold func_of_AddAnPointerTwice; simpl in *; repeat (rewrite fst_let_simpl; simpl);
            destruct (AddPointer tg 2%positive) as [t1 p0] eqn: eq_tg; simpl in *;
            destruct (AddPointer td p0) eqn: eq_td; simpl in *; intuition;
            apply IHt; auto; eapply subterm_trans; eauto using subtermNotP; fail).

Ltac solve_LN_RN tg t:= 
  induction t as [ n p| t1 IHt1 t2 IHt2 | t1 IHt1 t2 IHt2 | t IHt]; intros; simpl in *;
  try ( pose proof (AddPointerCorrect_4 (Not tg) 1%positive (VarP n p)) as APC5; simpl in *;
            unfold func_of_AddAnPointerTwice; simpl in *; repeat (rewrite fst_let_simpl; simpl);
            destruct (AddPointer tg 2%positive) as [t p0] eqn: eq_tg; simpl in *;
            intuition; fail);
  try ( pose proof (AddPointerCorrect_4 (Not tg) 1%positive (MeetP t1 t2 p)) as APC5; simpl in *;
            unfold func_of_AddAnPointerTwice; simpl in *; repeat (rewrite fst_let_simpl; simpl);
            destruct (AddPointer tg 2%positive) as [t p0] eqn: eq_tg; simpl in *;
            intuition; 
            try (apply IHt1; auto; eapply subterm_trans; eauto using subtermMeetP_1);
            try (apply IHt2; auto; eapply subterm_trans; eauto using subtermMeetP_2); fail);
  try ( pose proof (AddPointerCorrect_4 (Not tg) 1%positive (JoinP t1 t2 p)) as APC5; simpl in *;
            unfold func_of_AddAnPointerTwice; simpl in *; repeat (rewrite fst_let_simpl; simpl);
            destruct (AddPointer tg 2%positive) as [t p0] eqn: eq_tg; simpl in *;
            intuition;
            try (apply IHt1; auto; eapply subterm_trans; eauto using subtermJoinP_1);
            try (apply IHt2; auto; eapply subterm_trans; eauto using subtermJoinP_2); fail);
      ( pose proof (AddPointerCorrect_4 (Not tg) 1%positive (NotP t p)) as APC5; simpl in *;
            unfold func_of_AddAnPointerTwice; simpl in *; repeat (rewrite fst_let_simpl; simpl);
            destruct (AddPointer tg 2%positive) as [t1 p0] eqn: eq_tg; simpl in *;
            intuition;
            apply IHt; auto; eapply subterm_trans; eauto using subtermNotP; fail).





Theorem pointco_inter_equivLL tg td t:
  subterm (fst (AddPointer (pairAnTerm_to_Term (L tg) (L td)) xH)) t ->
((PointerCorrectnessTerm_inter (func_of_AddPointer (fst (AddPointer tg 2%positive))) t) \/
  (PointerCorrectnessTerm_inter (func_of_AddPointer (fst (AddPointer td (snd (AddPointer tg 2%positive))) ))) t) ->
  PointerCorrectnessTerm (func_to_RefMap (L tg) (L td)) t.
Proof.
  solve_LL_LR_RL_RR tg td t.
Qed. 

Theorem pointco_inter_equivLR tg td t:
  subterm (fst (AddPointer (pairAnTerm_to_Term (L tg) (R td)) xH)) t ->
((PointerCorrectnessTerm_inter (func_of_AddPointer (fst (AddPointer tg 2%positive))) t) \/
  (PointerCorrectnessTerm_inter (func_of_AddPointer (fst (AddPointer td (snd (AddPointer tg 2%positive))) ))) t) ->
  PointerCorrectnessTerm (func_to_RefMap (L tg) (R td)) t.
Proof.
  solve_LL_LR_RL_RR tg td t.
Qed.

Theorem pointco_inter_equivRL tg td t:
  subterm (fst (AddPointer (pairAnTerm_to_Term (R tg) (L td)) xH)) t ->
((PointerCorrectnessTerm_inter (func_of_AddPointer (fst (AddPointer tg 2%positive))) t) \/
  (PointerCorrectnessTerm_inter (func_of_AddPointer (fst (AddPointer td (snd (AddPointer tg 2%positive))) ))) t) ->
  PointerCorrectnessTerm (func_to_RefMap (R tg) (L td)) t.
Proof.
  solve_LL_LR_RL_RR tg td t.
Qed.

Theorem pointco_inter_equivRR tg td t:
  subterm (fst (AddPointer (pairAnTerm_to_Term (R tg) (R td)) xH)) t ->
((PointerCorrectnessTerm_inter (func_of_AddPointer (fst (AddPointer tg 2%positive))) t) \/
  (PointerCorrectnessTerm_inter (func_of_AddPointer (fst (AddPointer td (snd (AddPointer tg 2%positive))) ))) t) ->
  PointerCorrectnessTerm (func_to_RefMap (R tg) (R td)) t.
Proof.
  solve_LL_LR_RL_RR tg td t.
Qed.

Theorem pointco_inter_equivNL td t:
  subterm (fst (AddPointer (pairAnTerm_to_Term OL_Theory.N (L td)) xH)) t ->
  PointerCorrectnessTerm_inter (func_of_AddPointer (fst (AddPointer td 2%positive))) t ->
  PointerCorrectnessTerm (func_to_RefMap OL_Theory.N (L td)) t.
Proof.
  solve_LN_RN td t.
Qed.

Theorem pointco_inter_equivNR td t:
  subterm (fst (AddPointer (pairAnTerm_to_Term OL_Theory.N (R td)) xH)) t ->
  PointerCorrectnessTerm_inter (func_of_AddPointer (fst (AddPointer td 2%positive))) t ->
  PointerCorrectnessTerm (func_to_RefMap OL_Theory.N (R td)) t.
Proof.
  solve_LN_RN td t.
Qed.

Theorem pointco_inter_equivLN tg t:
  subterm (fst (AddPointer (pairAnTerm_to_Term (L tg) OL_Theory.N) xH)) t ->
  PointerCorrectnessTerm_inter (func_of_AddPointer (fst (AddPointer tg 2%positive))) t ->
  PointerCorrectnessTerm (func_to_RefMap (L tg) OL_Theory.N) t.
Proof.
  solve_LN_RN tg t.
Qed. 

Theorem pointco_inter_equivRN tg t:
  subterm (fst (AddPointer (pairAnTerm_to_Term (R tg) OL_Theory.N) xH)) t ->
  PointerCorrectnessTerm_inter (func_of_AddPointer (fst (AddPointer tg 2%positive))) t ->
  PointerCorrectnessTerm (func_to_RefMap (R tg) OL_Theory.N) t.
Proof.
  solve_LN_RN tg t.
Qed.






Theorem AddPointerCorrect_6_g1 d g p1 p2 g1 d1 :
  AddAnPointer g 2%positive = (g1, p1) ->
  AddAnPointer d p1 = (d1, p2) ->
  PointerCorrectnessAnTerm (func_to_RefMap g d) g1.
Proof.
  intros.
  destruct g1 eqn: dest_g1; destruct g eqn: dest_g; simpl in *; try congruence; auto. 
  all: try destruct (AddPointer t0 2%positive ) eqn: dest_t02; subst; simpl in *; try congruence.
  all: destruct d1 eqn: dest_d1; destruct d eqn: dest_d; simpl in *; try congruence; auto.
  all: try destruct (AddPointer _ p1 ) eqn: dest_tp1; subst; simpl in *; try congruence; auto.
  all: repeat substAll; try congruence.
  - pose proof (AddPointerCorrect_5 t0 2%positive); apply pointco_inter_equivLN; simpl in *;
    rewrite dest_t02 in *; simpl in *; auto using subtermNotP.
  - pose proof (AddPointerCorrect_4 t0 2%positive t).
    apply pointco_inter_equivLL; simpl in *.
    all: rewrite dest_t02 in *; simpl in *.
    all: destruct (AddPointer t3 p1) eqn: dest_t3; simpl in *; auto using subtermMeetP_1, subterm_refl.
  - pose proof (AddPointerCorrect_4 t0 2%positive t).
    apply pointco_inter_equivLR; simpl in *.
    all: rewrite dest_t02 in *; simpl in *.
    all: destruct (AddPointer t3 p1) eqn: dest_t3; simpl in *; auto using subtermMeetP_1, subterm_refl.
  - pose proof (AddPointerCorrect_5 t0 2%positive); apply pointco_inter_equivLN; simpl in *;
    rewrite dest_t02 in *; simpl in *; auto using subtermNotP.
  - pose proof (AddPointerCorrect_4 t0 2%positive t).
    apply pointco_inter_equivLL; simpl in *.
    all: rewrite dest_t02 in *; simpl in *.
    all: destruct (AddPointer t3 p1) eqn: dest_t3; simpl in *; auto using subtermMeetP_1, subterm_refl.
  - pose proof (AddPointerCorrect_4 t0 2%positive t).
    apply pointco_inter_equivLR; simpl in *.
    all: rewrite dest_t02 in *; simpl in *.
    all: destruct (AddPointer t3 p1) eqn: dest_t3; simpl in *; auto using subtermMeetP_1, subterm_refl.
Qed.

Theorem AddPointerCorrect_6_d1 d g p1 p2 g1 d1 :
  AddAnPointer g 2%positive = (g1, p1) ->
  AddAnPointer d p1 = (d1, p2) ->
  PointerCorrectnessAnTerm (func_to_RefMap g d) d1.
Proof.
  intros.
  destruct g1 eqn: dest_g1; destruct g eqn: dest_g; simpl in *; try congruence; auto. 
  all: try destruct (AddPointer _ 2%positive ) eqn: dest_t02; subst; simpl in *; try congruence.
  all: destruct d1 eqn: dest_d1; destruct d eqn: dest_d; simpl in *; try congruence; auto.
  all: try destruct (AddPointer _ p1 ) eqn: dest_tp1; subst; simpl in *; try congruence; auto.
  all: repeat substAll; try congruence.
  - pose proof (AddPointerCorrect_5 t0 2%positive); apply pointco_inter_equivNL; simpl in *;
    rewrite dest_tp1 in *; simpl in *; auto using subtermNotP.
  - pose proof (AddPointerCorrect_5 t0 2%positive); apply pointco_inter_equivNR; simpl in *;
    rewrite dest_tp1 in *; simpl in *; auto using subtermNotP.
  - pose proof (AddPointerCorrect_4 t3 p1 t2).
    apply pointco_inter_equivLL; simpl in *.
    all: rewrite dest_t02 in *; simpl in *.
    all: rewrite dest_tp1 in *; simpl in *.
    all: destruct (AddPointer t3 p1) eqn: dest_t3; simpl in *; auto using subtermMeetP_2, subterm_refl.
  - pose proof (AddPointerCorrect_4 t3 p1 t2).
    apply pointco_inter_equivLR; simpl in *.
    all: rewrite dest_t02 in *; simpl in *.
    all: rewrite dest_tp1 in *; simpl in *.
    all: destruct (AddPointer t3 p1) eqn: dest_t3; simpl in *; auto using subtermMeetP_2, subterm_refl.
  - pose proof (AddPointerCorrect_4 t3 p1 t2).
    apply pointco_inter_equivRL; simpl in *.
    all: rewrite dest_t02 in *; simpl in *.
    all: rewrite dest_tp1 in *; simpl in *.
    all: destruct (AddPointer t3 p1) eqn: dest_t3; simpl in *; auto using subtermMeetP_2, subterm_refl.
  - pose proof (AddPointerCorrect_4 t3 p1 t2).
    apply pointco_inter_equivRR; simpl in *.
    all: rewrite dest_t02 in *; simpl in *.
    all: rewrite dest_tp1 in *; simpl in *.
    all: destruct (AddPointer t3 p1) eqn: dest_t3; simpl in *; auto using subtermMeetP_2, subterm_refl.
Qed.



Theorem subterm_refl_eq t1 t2:
  t1 = t2 -> subterm t1 t2.
Proof.
  intros. subst. apply subterm_refl.
Qed.



Theorem decideOLPointerATCorrect : forall g d, (decideOL_pointer_at g d) = true -> AnLeq g d.
Proof. 
  intros. assert (squash (OLProof (g, d))). apply decideOLBoolCorrect with (anSize g + anSize d).
  - 
    unfold decideOL_pointer_at in H. simpl in *. destruct (AddAnPointerTwice g d 2%positive) as [gd p] eqn: eqgd.
    destruct gd as [g1 d1]. simpl in *. destruct (decideOL_pointer_atp (anSize g + anSize d) g1 d1 (AnPointerPairAVLMap.empty bool)) eqn: eq.
    simpl in *; subst.
    unfold AddAnPointerTwice in eqgd. simpl in *. 
    destruct (AddAnPointer g 2%positive) as [t1 p1] eqn: eqg1. destruct (AddAnPointer d p1) as [t2 p2] eqn: eqd1.
    assert (t1 = g1); try congruence. assert (t2 = d1); try congruence. assert (p2 = p); try congruence. subst.
    pose proof decideOLPointerATPCorrect. simpl in *.
    pose (func_to_RefMap g d) as refmap. specialize (H refmap). simpl in *.
    rewrite <- (AnForgetAddInverse g 2%positive ) at 2. rewrite <- (AnForgetAddInverse d p1) at 2. rewrite eqg1 in *; rewrite eqd1 in *; simpl in *.
    specialize (H (anSize g + anSize d)). simpl in *.
    Opaque ForgetAnPointer. Opaque anPSize.
    specialize (H [[g1]] [[d1]] (AnPointerPairAVLMap.empty bool)). simpl in *.
    rewrite (anSize_eq_anPSize_Add g 2%positive) in H at 1. rewrite (anSize_eq_anPSize_Add d p1) in H at 1. simpl in *.
    rewrite eqg1 in H at 1. rewrite eqd1 in H at 1. simpl in *.
    Ltac simp a b := try simpl in a; simpl in b.
    assert (PointerCorrectnessAnTerm refmap g1) as pcat_refmap_g; auto using (AddPointerCorrect_6_g1 d g p1 p g1 d1).
    assert (PointerCorrectnessAnTerm refmap d1) as pcat_refmap_d; auto using (AddPointerCorrect_6_d1 d g p1 p g1 d1).
    assert (correctMemoMap refmap (AnPointerPairAVLMap.empty bool)). unfold correctMemoMap. simpl in *. auto.

    destruct g1 eqn: dest_g1; destruct g eqn: dest_g; simpl in eqg1, eqd1; try congruence. 
    all: try destruct (AddPointer t 2%positive ) eqn: dest_t2; simp eqg1 eqd1; try congruence.
    all: try destruct (AddPointer t0 2%positive ) eqn: dest_t02; simp eqg1 eqd1; try congruence.
    all: destruct d1 eqn: dest_d1; destruct d eqn: dest_d; simp eqg1 eqd1; try congruence.
    all: try destruct (AddPointer _ p1 ) eqn: dest_tp1; simp eqg1 eqd1; try congruence.
    Opaque decideOL_bool. Opaque decideOL_pointer_atp.

    (* g is N *)
    + apply H; auto. simpl; simpl in eq; rewrite eq; simpl; auto.
    + assert (func_of_AddAnPointerTwice (ForgetAnPointer NTP) (ForgetAnPointer (LTP t)) (GetPointer t) = t).
      * Transparent ForgetAnPointer.
        unfold func_of_AddAnPointerTwice. apply (AddPointerCorrect_3 _ 1%positive). simpl.
        destruct (AddPointer (ForgetPointer t) 2%positive) eqn: dest_t; simpl; auto.  
        repeat substAll. right. apply subterm_refl_eq.
        pose proof (ForgetAddInverse t0 2%positive) as fai. rewrite dest_tp1 in fai; simpl in fai; subst. congruence.
      * simpl in *. repeat substAll.
        assert (ForgetPointer t = t0) as t_t0. pose proof (ForgetAddInverse t0 2%positive). rewrite dest_tp1 in *; simpl in *; congruence.
        rewrite t_t0 in H1. rewrite H1 in H. apply H; auto.
        unfold func_of_AddAnPointerTwice in *;  simpl in *. 
        rewrite fst_let_simpl in *.
        destruct (AddPointer (ForgetPointer t) 2%positive) eqn: dest_t; simpl in *. rewrite eq; simpl; auto.
    + assert (func_of_AddAnPointerTwice (ForgetAnPointer NTP) (ForgetAnPointer (RTP t)) (GetPointer t) = t).
      * Transparent ForgetAnPointer.
        unfold func_of_AddAnPointerTwice. apply (AddPointerCorrect_3 _ 1%positive). simpl.
        destruct (AddPointer (ForgetPointer t) 2%positive) eqn: dest_t; simpl; auto.  
        repeat substAll. right. apply subterm_refl_eq.
        pose proof (ForgetAddInverse t0 2%positive) as fai. rewrite dest_tp1 in fai; simpl in fai; subst. congruence.
      * simpl in *. repeat substAll.
        assert (ForgetPointer t = t0) as t_t0. pose proof (ForgetAddInverse t0 2%positive). rewrite dest_tp1 in *; simpl in *; congruence.
        rewrite t_t0 in H1. rewrite H1 in H. apply H; auto.
        unfold func_of_AddAnPointerTwice in *;  simpl in *. 
        rewrite fst_let_simpl in *.
        destruct (AddPointer (ForgetPointer t) 2%positive) eqn: dest_t; simpl in *. rewrite eq; simpl; auto.
    (* g is L *)
    + assert (func_of_AddAnPointerTwice (ForgetAnPointer (LTP t)) (ForgetAnPointer NTP) (GetPointer t) = t).
      * Transparent ForgetAnPointer.
        unfold func_of_AddAnPointerTwice. apply (AddPointerCorrect_3 _ 1%positive). simpl.
        destruct (AddPointer (ForgetPointer t) 2%positive) eqn: dest_t; simpl; auto.  
        repeat substAll. right. apply subterm_refl_eq.
        pose proof (ForgetAddInverse t0 2%positive) as fai. rewrite dest_t02 in fai; simpl in fai; subst. congruence.
      * simpl in *. repeat substAll.
        assert (ForgetPointer t = t0) as t_t0. pose proof (ForgetAddInverse t0 2%positive). rewrite dest_t02 in *; simpl in *; congruence.
        rewrite t_t0 in H1. rewrite H1 in H. apply H; auto.
        unfold func_of_AddAnPointerTwice in *;  simpl in *. 
        rewrite fst_let_simpl in *.
        destruct (AddPointer (ForgetPointer t) 2%positive) eqn: dest_t; simpl in *. rewrite eq; simpl; auto.
    + assert (func_of_AddAnPointerTwice (ForgetAnPointer (LTP t)) (ForgetAnPointer (LTP t2)) (GetPointer t) = t).
        unfold func_of_AddAnPointerTwice. apply (AddPointerCorrect_3 _ 1%positive). simpl.
        destruct (AddPointer (ForgetPointer t) 2%positive) eqn: dest_t; simpl; auto.  
        destruct (AddPointer (ForgetPointer t2) p3) eqn: dest_t2; simpl; auto.  
        repeat substAll. right. left. apply subterm_refl_eq.
        pose proof (ForgetAddInverse t0 2%positive) as fai. rewrite dest_t02 in fai. simpl in fai. subst. congruence.
      assert (func_of_AddAnPointerTwice (ForgetAnPointer (LTP t)) (ForgetAnPointer (LTP t2)) (GetPointer t2) = t2).
        unfold func_of_AddAnPointerTwice. apply (AddPointerCorrect_3 _ 1%positive). simpl.
        destruct (AddPointer (ForgetPointer t) 2%positive) eqn: dest_t; simpl; auto.  
        destruct (AddPointer (ForgetPointer t2) p3) eqn: dest_t2; simpl; auto.  
        repeat substAll. right. right. apply subterm_refl_eq.
        pose proof (ForgetAddInverse t0 2%positive) as fai. rewrite dest_t02 in fai; simpl in fai.
        assert (t=t5); try congruence. assert (p1 = p3); try congruence. subst. 
        pose proof (ForgetAddInverse t3 p3) as fai. rewrite dest_tp1 in fai; simpl in fai; subst. congruence.
      * simpl in *. repeat substAll.
        assert (ForgetPointer t = t0) as t_t0. pose proof (ForgetAddInverse t0 2%positive). rewrite dest_t02 in *; simpl in *; congruence.
        assert (ForgetPointer t2 = t3) as t_t2. pose proof (ForgetAddInverse t3 p1). rewrite dest_tp1 in *; simpl in *; congruence.
        rewrite t_t0 in H1, H2. rewrite t_t2 in H1, H2. repeat rewrite H1, H2 in H.  apply H; auto.
        unfold func_of_AddAnPointerTwice in *;  simpl in *. 
        rewrite dest_t02 in *; rewrite fst_let_simpl in *; rewrite eq; simpl; auto.
    + assert (func_of_AddAnPointerTwice (ForgetAnPointer (LTP t)) (ForgetAnPointer (RTP t2)) (GetPointer t) = t).
        unfold func_of_AddAnPointerTwice. apply (AddPointerCorrect_3 _ 1%positive). simpl.
        destruct (AddPointer (ForgetPointer t) 2%positive) eqn: dest_t; simpl; auto.  
        destruct (AddPointer (ForgetPointer t2) p3) eqn: dest_t2; simpl; auto.  
        repeat substAll. right. left. apply subterm_refl_eq.
        pose proof (ForgetAddInverse t0 2%positive) as fai. rewrite dest_t02 in fai. simpl in fai. subst. congruence.
      assert (func_of_AddAnPointerTwice (ForgetAnPointer (LTP t)) (ForgetAnPointer (RTP t2)) (GetPointer t2) = t2).
        unfold func_of_AddAnPointerTwice. apply (AddPointerCorrect_3 _ 1%positive). simpl.
        destruct (AddPointer (ForgetPointer t) 2%positive) eqn: dest_t; simpl; auto.  
        destruct (AddPointer (ForgetPointer t2) p3) eqn: dest_t2; simpl; auto.  
        repeat substAll. right. right. apply subterm_refl_eq.
        pose proof (ForgetAddInverse t0 2%positive) as fai. rewrite dest_t02 in fai; simpl in fai.
        assert (t=t5); try congruence. assert (p1 = p3); try congruence. subst. 
        pose proof (ForgetAddInverse t3 p3) as fai. rewrite dest_tp1 in fai; simpl in fai; subst. congruence.
      * simpl in *. repeat substAll.
        assert (ForgetPointer t = t0) as t_t0. pose proof (ForgetAddInverse t0 2%positive). rewrite dest_t02 in *; simpl in *; congruence.
        assert (ForgetPointer t2 = t3) as t_t2. pose proof (ForgetAddInverse t3 p1). rewrite dest_tp1 in *; simpl in *; congruence.
        rewrite t_t0 in H1, H2. rewrite t_t2 in H1, H2. repeat rewrite H1, H2 in H.  apply H; auto.
        unfold func_of_AddAnPointerTwice in *;  simpl in *. 
        rewrite dest_t02 in *; rewrite fst_let_simpl in *; rewrite eq; simpl; auto.
    (* g is R *)
    + assert (func_of_AddAnPointerTwice (ForgetAnPointer (RTP t)) (ForgetAnPointer NTP) (GetPointer t) = t).
      * Transparent ForgetAnPointer.
        unfold func_of_AddAnPointerTwice. apply (AddPointerCorrect_3 _ 1%positive). simpl.
        destruct (AddPointer (ForgetPointer t) 2%positive) eqn: dest_t; simpl; auto.  
        repeat substAll. right. apply subterm_refl_eq.
        pose proof (ForgetAddInverse t0 2%positive) as fai. rewrite dest_t02 in fai; simpl in fai; subst. congruence.
      * simpl in *. repeat substAll.
        assert (ForgetPointer t = t0) as t_t0. pose proof (ForgetAddInverse t0 2%positive). rewrite dest_t02 in *; simpl in *; congruence.
        rewrite t_t0 in H1. rewrite H1 in H. apply H; auto.
        unfold func_of_AddAnPointerTwice in *;  simpl in *. 
        rewrite fst_let_simpl in *.
        destruct (AddPointer (ForgetPointer t) 2%positive) eqn: dest_t; simpl in *. rewrite eq; simpl; auto.
    + assert (func_of_AddAnPointerTwice (ForgetAnPointer (RTP t)) (ForgetAnPointer (LTP t2)) (GetPointer t) = t).
        unfold func_of_AddAnPointerTwice. apply (AddPointerCorrect_3 _ 1%positive). simpl.
        destruct (AddPointer (ForgetPointer t) 2%positive) eqn: dest_t; simpl; auto.  
        destruct (AddPointer (ForgetPointer t2) p3) eqn: dest_t2; simpl; auto.  
        repeat substAll. right. left. apply subterm_refl_eq.
        pose proof (ForgetAddInverse t0 2%positive) as fai. rewrite dest_t02 in fai. simpl in fai. subst. congruence.
      assert (func_of_AddAnPointerTwice (ForgetAnPointer (RTP t)) (ForgetAnPointer (LTP t2)) (GetPointer t2) = t2).
        unfold func_of_AddAnPointerTwice. apply (AddPointerCorrect_3 _ 1%positive). simpl.
        destruct (AddPointer (ForgetPointer t) 2%positive) eqn: dest_t; simpl; auto.  
        destruct (AddPointer (ForgetPointer t2) p3) eqn: dest_t2; simpl; auto.  
        repeat substAll. right. right. apply subterm_refl_eq.
        pose proof (ForgetAddInverse t0 2%positive) as fai. rewrite dest_t02 in fai; simpl in fai.
        assert (t=t5); try congruence. assert (p1 = p3); try congruence. subst. 
        pose proof (ForgetAddInverse t3 p3) as fai. rewrite dest_tp1 in fai; simpl in fai; subst. congruence.
      * simpl in *. repeat substAll.
        assert (ForgetPointer t = t0) as t_t0. pose proof (ForgetAddInverse t0 2%positive). rewrite dest_t02 in *; simpl in *; congruence.
        assert (ForgetPointer t2 = t3) as t_t2. pose proof (ForgetAddInverse t3 p1). rewrite dest_tp1 in *; simpl in *; congruence.
        rewrite t_t0 in H1, H2. rewrite t_t2 in H1, H2. repeat rewrite H1, H2 in H.  apply H; auto.
        unfold func_of_AddAnPointerTwice in *;  simpl in *. 
        rewrite dest_t02 in *; rewrite fst_let_simpl in *; rewrite eq; simpl; auto.
    + assert (func_of_AddAnPointerTwice (ForgetAnPointer (RTP t)) (ForgetAnPointer (RTP t2)) (GetPointer t) = t).
        unfold func_of_AddAnPointerTwice. apply (AddPointerCorrect_3 _ 1%positive). simpl.
        destruct (AddPointer (ForgetPointer t) 2%positive) eqn: dest_t; simpl; auto.  
        destruct (AddPointer (ForgetPointer t2) p3) eqn: dest_t2; simpl; auto.  
        repeat substAll. right. left. apply subterm_refl_eq.
        pose proof (ForgetAddInverse t0 2%positive) as fai. rewrite dest_t02 in fai. simpl in fai. subst. congruence.
      assert (func_of_AddAnPointerTwice (ForgetAnPointer (RTP t)) (ForgetAnPointer (RTP t2)) (GetPointer t2) = t2).
        unfold func_of_AddAnPointerTwice. apply (AddPointerCorrect_3 _ 1%positive). simpl.
        destruct (AddPointer (ForgetPointer t) 2%positive) eqn: dest_t; simpl; auto.  
        destruct (AddPointer (ForgetPointer t2) p3) eqn: dest_t2; simpl; auto.  
        repeat substAll. right. right. apply subterm_refl_eq.
        pose proof (ForgetAddInverse t0 2%positive) as fai. rewrite dest_t02 in fai; simpl in fai.
        assert (t=t5); try congruence. assert (p1 = p3); try congruence. subst. 
        pose proof (ForgetAddInverse t3 p3) as fai. rewrite dest_tp1 in fai; simpl in fai; subst. congruence.
      * simpl in *. repeat substAll.
        assert (ForgetPointer t = t0) as t_t0. pose proof (ForgetAddInverse t0 2%positive). rewrite dest_t02 in *; simpl in *; congruence.
        assert (ForgetPointer t2 = t3) as t_t2. pose proof (ForgetAddInverse t3 p1). rewrite dest_tp1 in *; simpl in *; congruence.
        rewrite t_t0 in H1, H2. rewrite t_t2 in H1, H2. repeat rewrite H1, H2 in H.  apply H; auto.
        unfold func_of_AddAnPointerTwice in *;  simpl in *. 
        rewrite dest_t02 in *; rewrite fst_let_simpl in *; rewrite eq; simpl; auto.

  - destruct H0. apply (Soundness (g, d)). auto.
Qed.


Theorem reduceToAlgoPointers {OL: Ortholattice} : forall t1 t2 f, (decideOL_pointer_at (L t1) (R t2)) = true -> ((eval t1 f) <= (eval t2 f)).
Proof.
  intros. assert (AnLeq  (L t1) (R t2)). all: auto using decideOLPointerATCorrect.
Qed.

Ltac solveOLPointers OL := 
  reify_goal OL; apply reduceToAlgoPointers; auto; vm_compute; (try reflexivity).

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
