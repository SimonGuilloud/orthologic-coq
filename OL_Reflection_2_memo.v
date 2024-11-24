Require Import NArith.
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
    (* Guaranteed sufficent cases. *)
      match (g, d) with 
      | (L (Var a), R (Var b) )  => mbool (Pos.eqb a b) (* Hyp *)
      | (L (Join a b), _) => (decideOL_memo n (L a) d) &&& (decideOL_memo n (L b) d) (* LeftOr *)
      | (L (Not a), _) => decideOL_memo n (R a) d (* LeftNot *)
      | (_, R (Meet a b)) => (decideOL_memo n g (R a)) &&& (decideOL_memo n g (R b)) (* RightAnd *)
      | (_, R (Not a)) => decideOL_memo n g (L a) (* RightNot *)
          (* Swap cases *)
      | (R (Var a), L (Var b) )  => mbool (Pos.eqb b a) (* Hyp *)
      | (_, L (Join a b)) => (decideOL_memo n g (L a)) &&& (decideOL_memo n g (L b)) (* LeftOr *)
      | (_, L (Not a)) => decideOL_memo n g (R a) (* LeftNot *)
      | (R (Meet a b), _) => (decideOL_memo n (R a) d) &&& (decideOL_memo n (R b) d) (* RightAnd *)
      | (R (Not a), _) => decideOL_memo n (L a) d (* RightNot *)
      | _ => 
                match d with (* Weaken g*)
        | L a => decideOL_memo n g N 
        | R a => decideOL_memo n g N 
        | N => mfalse
        end |||(
        match g with (* Weaken d*)
        | L a => decideOL_memo n d N 
        | R a => decideOL_memo n d N 
        | N => mfalse
        end |||(
        match g with (* LeftAnd1 g*)
        | L (Meet a b) => decideOL_memo n (L a) d
        | _ => mfalse
        end |||(
        match d with (* LeftAnd1 d*)
        | L (Meet a b) => decideOL_memo n (L a) g
        | _ => mfalse
        end |||(
        match g with (* LeftAnd2 g*)
        | L (Meet a b) => decideOL_memo n (L b) d
        | _ => mfalse
        end |||(
        match d with (* LeftAnd2 d*)
        | L (Meet a b) => decideOL_memo n (L b) g
        | _ => mfalse
        end |||(
        match g with (* RightOr1 g*)
        | R (Join a b) => decideOL_memo n d (R a)
        | _ => mfalse
        end |||(
        match d with (* RightOr1 d*)
        | R (Join a b) => decideOL_memo n g (R a)
        | _ => mfalse
        end |||(
        match g with (* RightOr2 g*)
        | R (Join a b) => decideOL_memo n d (R b)
        | _ => mfalse
        end |||(
        match d with (* RightOr2 d*)
        | R (Join a b) => decideOL_memo n g (R b)
        | _ => mfalse
        end |||(
        match (g, d) with
        | (N, L(_)) => decideOL_memo n d d
        | (N, R(_)) => decideOL_memo n d d
        | (L(_), N) => decideOL_memo n g g
        | (R(_), N) => decideOL_memo n g g
        | _ => mfalse
        end
        ))))))))))
      end ((g, d, false) :: memo)
  in (b, ((g, d), b) :: m) end)
end.


Definition decideOL_memo_simp (g d: AnTerm): bool := fst (decideOL_memo (anterm_size g * anterm_size d + 4) g d []).


Definition memomap_correct (l: MemoMap) :=  forall g d, 
  match find (g, d) l with
  | Some (_, true) => exists n,  (decideOL_base n g d = true)
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


Theorem mor_mtrue_l A: (mfalse ||| A) = A.
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
  memomap_correct l -> 
  (e = true -> exists n, decideOL_base n g d = true) -> 
  memomap_correct ((g, d, e) :: l).
Proof.
  intros. unfold memomap_correct. intros.
  unfold find. fold find. destruct e.
  - destruct H0 as [n H0]; auto.  destruct (memokey_eqdec (g0, d0) (fst (g, d, decideOL_base n g d))).
    + rewrite memokey_eqdec_refl; auto. exists n. destruct (decideOL_base n g d) eqn: res; simpl in *.
      intros. simpl in *.  assert (g0 = g). congruence. assert (d0 = d). congruence. subst. auto. exfalso. auto with *.
    + rewrite memokey_eqdec_refl2. 2: auto. apply H.
  - destruct (memokey_eqdec (g0, d0) (fst (g, d, false))).
    + rewrite memokey_eqdec_refl; auto.
    + rewrite memokey_eqdec_refl2; auto. apply H.
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
  (((fst (decideOL_memo n g d l)) = true) ->  exists n0, (decideOL_base n0 g d) = true).
Proof.
  induction n.
  - intros. split.
    + intros. pose proof (H g d). simpl in *. destruct (find (g, d) l); simpl in *.
      * dest g; dest d; simpl in *; destruct p; simpl in *; auto.
      * auto.
    + specialize (H g d). simpl in *.
      destruct (find (g, d) l); intros.
      destruct p; simpl in *. destruct b. destruct H. all: eexists; intros; subst. all: simpl in *; (try congruence). apply H. 

  - intros. split.
    + simpl. pose proof H. unfold memomap_correct in H.  specialize (H g d).
      destruct (find (g, d) l) eqn: res; simpl in *. destruct p; simpl in *. auto.
      dest_simp g; dest_simp d; (try dest_simp t0); (try dest_simp t). all: repeat rewrite mor_mtrue_r; repeat rewrite mor_mtrue_l; repeat rewrite mand_mtrue_l.

      all: apply memomap_correct_snd_unfold. all: repeat rewrite mor_mtrue_r; repeat rewrite mor_mtrue_l; repeat rewrite mand_mtrue_l.

      Ltac rewrite_mor x y l:= 
        assert ((x ||| y) l = let (b, m) := x l in if b then (true, m) else (y m) ) as rew_first_or; (only 1: reflexivity); rewrite rew_first_or in *; clear rew_first_or.
      Ltac rewrite_mand x y l:= 
        assert ((x &&& y) l = let (b, m) := x l in if b then (y m) else (false, m) ) as rew_first_and; (only 1: reflexivity); rewrite rew_first_and in *; clear rew_first_and.

      (* recursively prove goals of the form 
            memomap_correct (snd (decideOL_memo n g1 d1 ||| (decideOL_memo n g2 d2||| (decideOL_memo n g3 d3 ||| ... ))) )
        and
            fst ( (decideOL_memo n g1 d1 ||| (decideOL_memo n g2 d2||| (decideOL_memo n g3 d3 ||| ... ))) l) =
                        (decideOL_base n g1 d1 ||| (decideOL_base n g2 d2||| (decideOL_base n g3 d3 ||| ... )))
        as well as conjunctions
      *)
      Ltac reduce_and_or rest IHn l H :=
        let IHn_ := (fresh "IHn") in let IHn_snd := (fresh "IHn_snd") in 
        let IHn_fst := (fresh "IHn_fst") in let n0 := (fresh "n0") in 
        let b_ := (fresh "b") in let l_ := (fresh "l") in let found := (fresh "found") in
          lazymatch rest with 
          | (decideOL_memo ?n ?g ?d) ||| ?rest2 => 
            try rewrite_mor (decideOL_memo n g d) rest2 l;
            pose proof (IHn g d l H) as IHn_; simpl in *; destruct IHn_ as [IHn_snd IHn_fst];
            destruct (decideOL_memo n g d l)  as [ b_ l_] eqn: found;
            destruct b_; simpl in *; auto;
            intros;
            try(destruct IHn_fst as [n0 IHn_fst]; auto; exists (S n0); eauto using 1);
            simpl in *;
            repeat rewrite Bool.orb_false_r;  repeat rewrite mor_mtrue_r; repeat rewrite mor_mtrue_l; repeat rewrite mand_mtrue_l;
            match goal with | [ |- (_ -> _) ] => intro  | _ => idtac end;
            try congruence;
            try (apply Bool.orb_true_iff; left; congruence);
            try (apply Bool.orb_true_iff; right);
            try (eapply IHn; simpl in *; eauto using 1; fail); 
            try (eapply IHn_fst; simpl in *; eauto using 1; fail);
            try (rewrite IHn_fst; simpl; repeat rewrite Bool.orb_true_r; auto;  fail);
            reduce_and_or rest2 IHn l_ IHn_snd;
            idtac
          | (decideOL_memo ?n ?g ?d) &&& ?rest2 => 
            try rewrite_mand (decideOL_memo n g d) rest2 l;
            pose proof (IHn g d l H) as IHn_; simpl in *; destruct IHn_ as [IHn_snd IHn_fst];
            destruct (decideOL_memo n g d l)  as [ b_ l_] eqn: found;
            destruct b_; simpl in *; auto;
            intros; try congruence;
            match goal with
            | [ HH: true = true -> _ |- _ ]=> destruct IHn_fst as [n0 IHn_fst]; auto; idtac
            | [ HH: false = true -> _ |- _ ]=> clear IHn_fst
            | _ => idtac
            end;
            simpl in *;
            repeat rewrite Bool.orb_false_r;  repeat rewrite mor_mtrue_r; repeat rewrite mor_mtrue_l; repeat rewrite mand_mtrue_l;
            try (apply Bool.andb_true_iff; split);
            try (eapply IHn; simpl in *; eauto using 1; fail); 
            try (eapply IHn_fst; simpl in *; eauto using 1; fail);
            try (rewrite IHn_fst; simpl; repeat rewrite Bool.orb_true_r; auto;  fail);
            reduce_and_or rest2 IHn l_ IHn_snd;
            idtac
          | decideOL_memo ?n ?g ?d =>  
            simpl in *; repeat rewrite Bool.orb_false_r; simpl in *; auto; intros; try congruence;
            try (apply IHn; simpl in *; eauto using 1; congruence);
            pose proof (IHn g d l H) as IHn_; simpl in *; destruct IHn_ as [IHn_snd IHn_fst]; 
            destruct IHn_fst as [n0 IHn_fst]; auto;
            lazymatch goal with
            | [ J1: decideOL_base ?m1 _ _ = true, J2: decideOL_base ?m2 _ _ = true |- _ ] => 
                exists (S (Nat.max m1 m2)); simpl; apply Bool.andb_true_iff; split; 
                only 1: (apply (decideOL_base_monotonic (Nat.max m1 m2) m1); try lia); 
                only 2: (apply (decideOL_base_monotonic (Nat.max m1 m2) m2); try lia);
                idtac
            | [ J1: decideOL_base ?m1 _ _ = true |- _ ] =>  exists (S m1); simpl
            | _ => idtac
            end;
            repeat rewrite Bool.orb_false_r;
            repeat (apply Bool.orb_true_iff; right); eauto using 1;
            idtac
          | mfalse => simpl in *; auto; intros; congruence;
            idtac
          | (mbool _) => intros; simpl in *; auto; exists 1; simpl; auto; intros; congruence
          | _ => fail "unknown shape" rest
          end.


      all: try (lazymatch goal with
      | [H : memomap_correct ?l |- 
          memomap_correct ( (?g, ?d, fst (?rest (?head :: ?l))) :: snd (?rest (?head :: ?l))) ] => 
        apply (memomap_correct_cons g d);
        let H0 := (fresh "H0") in
        pose proof (memomap_correct_false g d l H) as H0;
        reduce_and_or rest IHn (head :: l) H0;
        idtac
      | _ => fail "unknown shape"
      end; fail).

      (* Need to do the second half of the proof, which could be the same as the first *)
    + Opaque decideOL_base. simpl. pose proof H as H0. unfold memomap_correct in H0.  specialize (H0 g d).
      destruct (find (g, d) l) eqn: res; simpl in *. destruct p; simpl in *. 
      * destruct b eqn:b_eq; simpl in *; intro; auto; try congruence.
      * Transparent decideOL_base. dest_simp g; dest_simp d; (try dest_simp t0); (try dest_simp t).
        all: rewrite fst_let_simpl; simpl in *; repeat rewrite Bool.orb_false_r; repeat rewrite mor_mtrue_r; repeat rewrite mor_mtrue_l.
        all: try ( apply IHn; auto; simpl in *; lia).
        all: try (lazymatch goal with
            | [H : memomap_correct ?l |- fst (?rest (?head :: ?l)) = true -> _ ] => 
              let H0 := (fresh "H0") in
              epose proof (memomap_correct_false _ _ l H) as H0;
              reduce_and_or rest IHn (head :: l) H0
            | [H : memomap_correct ?l |- ?inner = true -> _ ] => 
              reduce_and_or (mbool inner) IHn l H
            | _ => fail "unknown shape"
            end; fail). 
    Unshelve. all: try exact 1.
Qed.


  (* Reflection: solve goals using the algorithm in arbitrary Ortholattice *)


 (* If the algorithms outputs True, then g is semanticaly smaller than d.*)
Theorem decideOL_memo_simp_correct : forall g d, (decideOL_memo_simp g d) = true -> anTerm_leq g d.
Proof. 
  intros. assert (squash (OLProof (g, d))). (pose proof decideOL_memo_correct (anterm_size g * anterm_size d + 4) g d []). destruct H0. unfold memomap_correct; simpl in *; auto.
  specialize (H1 H). destruct H1 as [n0 H1]. apply decideOL_base_correct with n0; auto. 
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
