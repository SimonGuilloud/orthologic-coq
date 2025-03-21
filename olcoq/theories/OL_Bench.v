Require Export Setoid Morphisms.
Require Export Lia.
Require Export Coq.Arith.Bool_nat.
Require Export Coq.Arith.PeanoNat.

Require Export OL_Theory.
Require OL_Reflection_1_base.
Require OL_Reflection_2_opti.
Require OL_Reflection_3_memo.
Require OL_Reflection_4_fmap.
Require OL_Reflection_5_pointers.
Require Export OLPlugin.

Open Scope bool_scope.
Require Export Btauto.
Import List.
Import ListNotations.



Ltac solve_OL OL thm reduction :=
  OL_Reflection_1_base.reify_goal OL;
  simple apply thm; reduction (); exact eq_refl.


Tactic Notation "run1" tactic(t) :=
  idtac;
  first
    [ timeout 30
        first[ assert_succeeds (idtac; solve[t]); idtac "solved"
             | fail 2 "not solved" ]
    | idtac "timeout" ].

Tactic Notation "run2" tactic(t) :=
  idtac;
  first
    [ timeout 30
        first[ assert_succeeds (idtac; solve[t]); idtac "solved"
             | idtac "not solved" ]
    | idtac "timeout" ].

Require Export String.
Open Scope string_scope.

Inductive reduction := compute | lazy | vm_compute | none.

#[global] Set Printing Width 1200. (* Avoid line wraps in output *)

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
  time (run1 (solve_OL BoolOL thm reduction)).

Inductive strategy := oltauto | oltauto_cert | btauto.

Tactic Notation "bench2" uconstr(id) constr(strategy) :=
  header id strategy "none";
  let strategy := lazymatch strategy with
                 | oltauto => fun _ => oltauto
                 | oltauto_cert => fun _ => oltauto_cert
                 | btauto => fun _ => btauto
                 end in
  time (run2 (idtac; strategy ())).

Tactic Notation "benchtauto" uconstr(id) :=
  do 5 (bench2 id oltauto);
  do 5 (bench2 id oltauto_cert);
  do 5 (bench2 id btauto).

Tactic Notation "benchSuperFast" uconstr(id) :=
  do 5 (bench1 id OL_Reflection_4_fmap.reduce_to_decideOL_fmap lazy);
  do 5 (bench1 id OL_Reflection_4_fmap.reduce_to_decideOL_fmap vm_compute);
  do 5 (bench1 id OL_Reflection_5_pointers.reduce_to_decideOL_pointer lazy);
  do 5 (bench1 id OL_Reflection_5_pointers.reduce_to_decideOL_pointer vm_compute);
  do 5 (header id "olcert_goal" "none"; time (run1 (olcert_goal)));
  (* do 1 (header id "oltauto_cert" "none"; time (run1 (oltauto_cert))); *)
  (* do 1 (header id "oltauto" "none"; time (run1 (oltauto))); *)
  idtac.

Tactic Notation "benchFast" uconstr(id) :=
  do 5 (bench1 id OL_Reflection_3_memo.reduce_to_decideOL_memo lazy);
  do 5 (bench1 id OL_Reflection_3_memo.reduce_to_decideOL_memo vm_compute);
  benchSuperFast id;
  idtac.

Tactic Notation "bench" uconstr(id) :=
  do 5 (header id "btauto" "none"; time (run1 (btauto)));
  benchFast id;
  idtac.

Tactic Notation "benchSlow" uconstr(id) :=
  do 5 (bench1 id OL_Reflection_1_base.reduce_to_decideOL lazy);
  do 5 (bench1 id OL_Reflection_1_base.reduce_to_decideOL vm_compute);
  do 5 (bench1 id OL_Reflection_2_opti.reduce_to_decideOL_opti lazy);
  do 5 (bench1 id OL_Reflection_2_opti.reduce_to_decideOL_opti vm_compute);
  bench id;
  idtac.

Notation "! a" := (negb a) (at level 9).
