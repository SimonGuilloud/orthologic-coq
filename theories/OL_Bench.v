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

Ltac solve_OL OL thm refl :=
  OL_Reflection_1_base.reify_goal OL;
  simple apply thm; refl ().

(* We want to check that the proofs that we produce are well-formed.  For this,
   we use the `abstract` tactical: `abstract t` runs `t`, then typechecks the
   proof produced by `t` the way `Qed` would.

   Unfortunately, `abstract` works only with complete proofs (unlike the
   `Validate Proof` command).  This isn't a problem for tactics that fully solve
   the goal, but it is an issue for simplification tactics, which do not produce
   a complete proof.  To typecheck the result of the latter, we use the axiom
   `give_up` below to produce a complete proof term, which `abstract` can then
   typecheck. *)
Axiom give_up : forall {A: Type}, A.

Ltac give_up :=
  idtac;
  let n := numgoals in
  idtac "Goals left:" n;
  guard n > 0; apply give_up.

(* Change the number below to adjust the timeout *)
Tactic Notation "run1" tactic(t) :=
  idtac;
  first
    [ timeout 30 first
        [ assert_succeeds abstract (first [ t | idtac "tactic failed" ]; give_up)
        | idtac "abstract failed" ]
    | idtac "timeout" ].

Require Export String.
Open Scope string_scope.

Inductive reduction := lazy | vm_compute.

#[global] Set Printing Width 1200. (* Avoid line wraps in output *)

Tactic Notation "header" uconstr(id) constr(thm) constr(reduction) :=
  idtac "--------------------------------------------------------------------------------";
  idtac "::" id ":::" thm ":::" reduction.

Tactic Notation "bench1" uconstr(id) constr(thm) constr(reduction)  :=
  header id thm reduction;
  let refl := lazymatch reduction with
                  | lazy => fun _ => lazy; exact_no_check (@eq_refl bool true)
                  | vm_compute => fun _ => vm_cast_no_check (@eq_refl bool true)
                  end in
  time (run1 (solve_OL BoolOL thm refl)).

Inductive strategy := oltauto | oltauto_cert | btauto.

Tactic Notation "bench2" uconstr(id) constr(strategy) :=
  header id strategy "none";
  let strategy := lazymatch strategy with
                 | oltauto => fun _ => oltauto
                 | oltauto_cert => fun _ => oltauto_cert
                 | btauto => fun _ => btauto
                 end in
  time (run1 (idtac; strategy ())).

(* Change the number below to do more repetitions *)
Tactic Notation "doN" tactic3(t) :=
  do 1 t.

Tactic Notation "benchtauto" uconstr(id) :=
  doN (bench2 id oltauto);
  doN (bench2 id oltauto_cert);
  doN (bench2 id btauto).

Tactic Notation "benchSuperFast" uconstr(id) :=
  doN (bench1 id OL_Reflection_4_fmap.reduce_to_decideOL_fmap lazy);
  doN (bench1 id OL_Reflection_4_fmap.reduce_to_decideOL_fmap vm_compute);
  doN (bench1 id OL_Reflection_5_pointers.reduce_to_decideOL_pointer lazy);
  doN (bench1 id OL_Reflection_5_pointers.reduce_to_decideOL_pointer vm_compute);
  doN (header id "olcert_goal" "none"; time (run1 (olcert_goal)));
  idtac.

Tactic Notation "benchFast" uconstr(id) :=
  doN (bench1 id OL_Reflection_3_memo.reduce_to_decideOL_memo lazy);
  doN (bench1 id OL_Reflection_3_memo.reduce_to_decideOL_memo vm_compute);
  benchSuperFast id;
  idtac.

Tactic Notation "bench" uconstr(id) :=
  doN (header id "btauto" "none"; time (run1 (btauto)));
  benchFast id;
  idtac.

Tactic Notation "benchSlow" uconstr(id) :=
  doN (bench1 id OL_Reflection_1_base.reduce_to_decideOL lazy);
  doN (bench1 id OL_Reflection_1_base.reduce_to_decideOL vm_compute);
  doN (bench1 id OL_Reflection_2_opti.reduce_to_decideOL_opti lazy);
  doN (bench1 id OL_Reflection_2_opti.reduce_to_decideOL_opti vm_compute);
  bench id;
  idtac.

Notation "! a" := (negb a) (at level 9).
