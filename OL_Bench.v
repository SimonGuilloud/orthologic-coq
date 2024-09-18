Require Export Setoid Morphisms.
Require Export Lia.
Require Export Coq.Arith.Bool_nat.
Require Export Coq.Arith.PeanoNat.

Require Export OL_Theory.
Require OL_Reflection_1_base.
Require OL_Reflection_2_memo.
Require OL_Reflection_3_fmap.
Require OL_Reflection_4_pointers.

Open Scope bool_scope.
Require Export Btauto.
Import List.
Import ListNotations.

Ltac solveOL OL thm reduction :=
  OL_Reflection_1_base.reify_goal OL;
  simple apply thm; reduction (); exact eq_refl.

Tactic Notation "run1" tactic(t) :=
  idtac;
  first
    [ timeout 30
        first[ assert_succeeds (idtac; solve[t]); idtac "solved"
             | fail 2 "not solved" ]
    | idtac "timeout" ].

Require Export String.
Open Scope string_scope.

Inductive reduction := compute | lazy | vm_compute | none.

Tactic Notation "header" uconstr(id) constr(thm) constr(reduction) :=
  idtac "--------------------------------------------------------------------------------";
  idtac "::" id ":::" thm ":::" reduction.

Tactic Notation "bench1" uconstr(id) constr(thm) constr(reduction)  :=
  header id thm reduction;
  let reduction := lazymatch reduction with
                  | compute => fun _ => compute
                  | lazy => fun _ => lazy
                  | vm_compute => fun _ => vm_compute
                  | none => fun _ => idtac
                  end in
  time (run1 (solveOL BoolOL thm reduction)).

Tactic Notation "benchSuperFast" uconstr(id) :=
  do 10 (bench1 id OL_Reflection_1_base.reduceToAlgo lazy);
  do 10 (bench1 id OL_Reflection_1_base.reduceToAlgo vm_compute);
  do 10 (bench1 id OL_Reflection_2_memo.reduceToAlgoMemo lazy);
  do 10 (bench1 id OL_Reflection_2_memo.reduceToAlgoMemo vm_compute);
  do 10 (bench1 id OL_Reflection_3_fmap.reduceToAlgoFmap lazy);
  do 10 (bench1 id OL_Reflection_3_fmap.reduceToAlgoFmap vm_compute);
  do 10 (bench1 id OL_Reflection_4_pointers.reduceToAlgoPointers lazy);
  do 10 (bench1 id OL_Reflection_4_pointers.reduceToAlgoPointers vm_compute);
  do 10 (header id "btauto" "none"; time (run1 (btauto)));
  idtac.

Tactic Notation "benchFast" uconstr(id) :=
  benchSuperFast id;
  idtac.

Tactic Notation "bench" uconstr(id) :=
  benchFast id;
  idtac.

Tactic Notation "benchSlow" uconstr(id) :=
  bench id;
  idtac.

Notation "! a" := (negb a) (at level 9).
