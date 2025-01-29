Require Import NArith.
Require Import OL_Theory.

Require Import OL_Reflection_1_base.
Require Import OL_Reflection_2_opti.


Require Import Setoid Morphisms.
Require Import Lia.
Require Import Coq.Arith.Bool_nat.
Require Import Coq.Arith.PeanoNat.
Require Import Btauto.


Open Scope bool_scope.
Import List.
Import ListNotations.


Definition MemoKey := (AnTerm * AnTerm)%type.


Definition MemoMap := list (MemoKey * bool).


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

Infix "|||" := mor (at level 60).
Infix "&&&" := mand (at level 60).


Definition memokey_eqdec : forall (x y: MemoKey), {x = y} + {x <> y}.
Proof. repeat decide equality. Defined.


Fixpoint find (x: MemoKey) (l: MemoMap) : option (MemoKey * bool) := match l with
| [] => None
| head :: tail => if memokey_eqdec x (fst head) then Some head else find x tail
end.


Fixpoint decideOL_memo (fuel: nat) (g d: AnTerm) (memo: MemoMap) : (bool * MemoMap) :=
  match find (g, d) memo with
  | Some (_, b) => (b, memo)
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
      | (L (Join a b), _) => decideOL_memo n (L a) d &&& decideOL_memo n (L b) d
      | (_, L (Join a b)) => decideOL_memo n g (L a) &&& decideOL_memo n g (L b)
      | (R (Meet a b), _) => decideOL_memo n (R a) d &&& decideOL_memo n (R b) d
      | (_, R (Meet a b)) => decideOL_memo n g (R a) &&& decideOL_memo n g (R b)
      | (L (Not a), _) => decideOL_memo n (R a) d
      | (_, L (Not a)) => decideOL_memo n g (R a)
      | (R (Not a), _) => decideOL_memo n (L a) d
      | (_, R (Not a)) => decideOL_memo n g (L a)
      | _ => (
        match g with 
        | L (Meet a b) => decideOL_memo n (L a) d 
        | _ => mfalse
        end ||| (
        match g with 
        | L (Meet a b) => decideOL_memo n (L b) d
        | _ => mfalse
        end ||| (
        match d with 
        | L (Meet a b) => decideOL_memo n g (L a) 
        | _ => mfalse
        end ||| (
        match d with 
        | L (Meet a b) => decideOL_memo n g (L b) 
        | _ => mfalse
        end ||| (
        match g with
        | R (Join a b) => decideOL_memo n (R a) d
        | _ => mfalse
        end ||| (
        match g with
        | R (Join a b) => decideOL_memo n (R b) d
        | _ => mfalse
        end ||| (
        match d with
        | R (Join a b) => decideOL_memo n g (R a) 
        | _ => mfalse
        end ||| (
        match d with
        | R (Join a b) => decideOL_memo n g (R b)
        | _ => mfalse
        end ||| (
        match d with 
        | N => decideOL_memo n g g 
        | _ => mfalse
        end ||| (
        match g with 
        | N => decideOL_memo n d d
        | _ => mfalse
        end  ||| (
        decideOL_memo n g N ||| 
        decideOL_memo n N d
        )))))))))))
      end) ((g, d, false) :: memo)
    in (b, ((g, d), b) :: m) end)
end.


Definition decideOL_memo_simp (g d: AnTerm): bool := fst (decideOL_memo (anterm_size g * anterm_size d + 4) g d []).


Definition memomap_correct (l: MemoMap) :=  forall g d, 
  match find (g, d) l with
  | Some (_, true) => exists n,  (decideOL_opti n g d = true)
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


Lemma memokey_eqdec_refl T1 x y (A B: T1) : x = y -> (if memokey_eqdec x y then A else B) = A.
Proof. 
  intro. destruct (memokey_eqdec x y); congruence.
Qed.


Lemma memokey_eqdec_refl2 T1 x y (A B: T1) : x <> y -> (if memokey_eqdec y x then A else B) = B.
Proof. 
  intro. destruct (memokey_eqdec y x); congruence.
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
  memomap_correct ((g, d, fst A) :: (snd A)) ->
  memomap_correct (snd (let (b, m) := A in (b, (g, d, b) :: m))).
Proof.
  intros. rewrite snd_let_simpl. auto.
Qed.


Lemma memomap_correct_cons g d l e : 
  (*(n >= anterm_size g + anterm_size d) -> *)
  memomap_correct l /\ 
  (e = true -> exists n, decideOL_opti n g d = true) -> 
  memomap_correct ((g, d, e) :: l) /\ (e = true -> exists n, decideOL_opti n g d = true).
Proof.
  intros. unfold memomap_correct. intros. split; intuition. 
  unfold find. fold find. destruct e.
  - destruct H1 as [n H1]; auto. destruct (memokey_eqdec (g0, d0) (fst (g, d, decideOL_opti n g d))).
    + rewrite memokey_eqdec_refl; auto. exists n. destruct (decideOL_opti n g d) eqn: res; simpl in *.
      intros. simpl in *.  assert (g0 = g). congruence. assert (d0 = d). congruence. subst. auto. exfalso. auto with *.
    + rewrite memokey_eqdec_refl2. 2: auto. apply H0.
  - destruct (memokey_eqdec (g0, d0) (fst (g, d, false))).
    + rewrite memokey_eqdec_refl; auto.
    + rewrite memokey_eqdec_refl2; auto. apply H0.
Qed.


Ltac dest_simp g := destruct g; repeat rewrite mor_mtrue_r; try (simpl; congruence).


Lemma destroy_triplet_equality {T1} {T2} {T3} (a:T1) (b:T2) (c d: T3) : c = d -> (a, b, c) = (a, b, d).
Proof.
  intros. subst. auto.
Qed.


Lemma memomap_correct_false g d l: memomap_correct l -> memomap_correct ((g, d, false) :: l).
Proof.
  intros. unfold memomap_correct. intros. unfold find. fold find. destruct (memokey_eqdec (g0, d0) (g, d)).
  - rewrite memokey_eqdec_refl; auto.
  - rewrite memokey_eqdec_refl2; auto. apply H.
Qed.


Lemma move_exists {T} A B : (exists x, A -> B x) -> (A -> (exists x: T, B x)).
Proof.
  intuition. destruct H. exists x. auto.
Qed.


Lemma correct_with_false_rewrite g d l: memomap_correct l -> memomap_correct ((g, d, false) :: l) /\ memomap_correct l.
Proof. intuition. apply memomap_correct_false; auto. Qed.


Lemma find_irrelevant g d g1 d1 r l l2: 
  fst match find (g, d) ((g1, d1, false) :: l) with
  | Some (_, b) => (b, (g1, d1, false) :: l)
  | None => (r, (g1, d1, false) :: l2)
  end = true ->
  fst match find (g, d) l with
  | Some (_, b) => (b, l)
  | None => (r, l2)
  end = true.
Proof.
  intros. unfold find in *. fold find in *. destruct (memokey_eqdec (g, d) (g1, d1)).
  - rewrite memokey_eqdec_refl in H; simpl in *; congruence.
  - rewrite memokey_eqdec_refl2 in H; auto. destruct (find (g, d) l); auto. destruct p; simpl in *; auto.
Qed.


Theorem decideOL_memo_correct : 
  forall n g d l, 
  (memomap_correct l) -> 
  (memomap_correct (snd (decideOL_memo n g d l))) /\
  (((fst (decideOL_memo n g d l)) = true) ->  exists n0, (decideOL_opti n0 g d) = true).
Proof.
  induction n.
  - intros. split.
    + intros. pose proof (H g d). simpl in *. destruct (find (g, d) l); simpl in *.
      * dest g; dest d; simpl in *; destruct p; simpl in *; auto.
      * auto.
    + specialize (H g d). simpl in *.
      destruct (find (g, d) l); intros.
      destruct p; simpl in *. destruct b. destruct H. all: simpl in *; try congruence. eexists; intros; subst. all: simpl in *; (try congruence). apply H. 

  - intros.
    + simpl. pose proof H. unfold memomap_correct in H.  specialize (H g d).
      destruct (find (g, d) l) eqn: res; simpl in *. destruct p; simpl in *. auto. destruct b; simpl in *; auto. split; auto; intro; congruence.

      pose proof (memomap_correct_false g d l H0) as H1. 
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
          | decideOL_memo ?n ?g ?d => 
            pose proof (IHn g d l H) as IHn_; simpl in *; destruct IHn_ as [IHn_snd IHn_fst];
            destruct (decideOL_memo n g d l) as [b_ l_] eqn: found;
            destruct b_; simpl in *;
            only 1: (destruct IHn_fst as [n0 IHn_fst]; auto; simpl in *;
              split; auto; intro; exists (S n0); simpl; 
              autorewrite with rw_bool in *; auto 7);
            split; auto; congruence;
            idtac

          | decideOL_memo ?n ?g ?d ||| ?rest2 =>
            rewrite_mor (decideOL_memo n g d) rest2 l;
            pose proof (IHn g d l H) as IHn_; simpl in *; destruct IHn_ as [IHn_snd IHn_fst];
            destruct (decideOL_memo n g d l) as [b_ l_] eqn: found;
            destruct b_; simpl in *;
            only 1: (destruct IHn_fst as [n0 IHn_fst]; auto; simpl in *;
              split; auto; intro; exists (S n0); simpl; 
              autorewrite with rw_bool in *; auto 7);
            reduce_or rest2 IHn l_ IHn_snd;
            idtac
          | (decideOL_memo ?n ?g1 ?d1) &&& (decideOL_memo ?n ?g2 ?d2) =>
            rewrite_mand (decideOL_memo n g1 d1) (decideOL_memo n g2 d2) l;
            let IHn_snd_r := (fresh "IHn_snd_r") in let IHn_fst_r := (fresh "IHn_fst_r") in
            let IHn_r := (fresh "IHn_r") in let m1 := (fresh "m1") in let m2 := (fresh "m2") in
            let b_r := (fresh "b_r") in let l_r := (fresh "l_r") in let found_r := (fresh "found_r") in
            pose proof (IHn g1 d1 l H) as IHn_; simpl in *; destruct IHn_ as [IHn_snd IHn_fst];
            destruct (decideOL_memo n g1 d1 l)  as [ b_ l_] eqn: found;
            pose proof (IHn g2 d2 l_ IHn_snd) as IHn_r; simpl in *; destruct IHn_r as [IHn_snd_r IHn_fst_r];
            destruct (decideOL_memo n g2 d2 l_)  as [ b_r l_r] eqn: found_r;
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
          | decideOL_memo ?n ?g ?d =>
            
            idtac
          | mfalse => simpl; intuition; congruence
          | (mbool (?p0 =? ?p)%positive)  => 
            let p_eq := (fresh "p_eq") in
            destruct (p0 =? p)%positive eqn: p_eq; simpl in *; 
            only 1: (split; intros; auto; exists 1; simpl; autorewrite with rw_bool in *; auto);
            intuition; congruence;
            idtac
      end.
      all: try (lazymatch goal with
      | [ |- memomap_correct ( (?g, ?d, fst (?rest ?l)) :: snd (?rest ?l)) /\ _ ] => 
        apply memomap_correct_cons;
        reduce_or rest IHn l H1;
        idtac
      | _ => fail "unknown shape"
      end; fail). 
      
Qed.


  (* Reflection: solve goals using the algorithm in arbitrary Ortholattice *)


 (* If the algorithms outputs True, then g is semanticaly smaller than d.*)
Theorem decideOL_memo_simp_correct : forall g d, (decideOL_memo_simp g d) = true -> anTerm_leq g d.
Proof. 
  intros. assert (squash (OLProof (g, d))). (pose proof decideOL_memo_correct (anterm_size g * anterm_size d + 4) g d []). destruct H0. unfold memomap_correct; simpl in *; auto.
  specialize (H1 H). destruct H1 as [n0 H1]. apply decideOL_opti_correct with n0; auto. 
  destruct H0. apply (soundness (g, d)). auto.
Qed.


Theorem reduce_to_decideOL_memo {OL: Ortholattice} : forall t1 t2 f, (decideOL_memo_simp (L t1) (R t2)) = true -> ((eval t1 f) <= (eval t2 f)).
Proof.
  intros. assert (anTerm_leq  (L t1) (R t2)). all: auto using decideOL_memo_simp_correct.
Qed.


Ltac solveOL_memo OL := 
  reify_goal OL; apply reduce_to_decideOL_memo; auto; vm_compute; (try reflexivity).

Example test1 {OL: Ortholattice} : forall a,  a <= a.
Proof.
  intro. 
  solveOL_memo OL.
Qed.

Example test2 {OL: Ortholattice} : forall a,  a == (a ∩ a).
Proof.
  intro. 
  solveOL_memo OL.
Qed.


Example test3 {OL: Ortholattice} a b c: 
  ¬(b ∪ ¬(c ∩ ¬b) ∪ a) <= (¬a ∪ ¬(b ∩ ¬a)).
Proof.
  intros. 
  solveOL_memo OL.
Qed.


Example test4 : forall a: (@A BoolOL),  a <= (a || a).
Proof.
  intro.
  solveOL_memo BoolOL.
Qed.


Example test5 : forall a: (@A BoolOL), Bool.le a (andb a a).
Proof.
  intro. 
  solveOL_memo BoolOL.
Qed.


Example test6 : forall a b : bool,   ( a ∩ (neg a)) <= b.
Proof.
  intros.
  solveOL_memo BoolOL.
Qed.


Example test7 : forall a b : bool,  Bool.le (andb a (negb a)) b.
Proof.
  intros. 
  solveOL_memo BoolOL.
Qed.


Example test8 : forall a b c: bool,  (a ∩ (negb a)) <= (a || (b && c)).
Proof.
  intros. 
  solveOL_memo BoolOL.
Qed.
