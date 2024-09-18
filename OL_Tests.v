Require Import Setoid Morphisms.
Require Import Lia.
Require Import Coq.Arith.Bool_nat.
Require Import Coq.Arith.PeanoNat.

Require Import OL_Theory.
Require OL_Reflection_1_base.
Require OL_Reflection_2_memo.
Require OL_Reflection_3_fmap.
Require OL_Reflection_4_pointers.

Open Scope bool_scope.
Require Import Btauto.
Import List.
Import ListNotations.

Ltac solveOL OL thm reduction :=
  OL_Reflection_1_base.reify_goal OL;
  simple apply thm; reduction (); exact eq_refl.

Tactic Notation "run1" tactic(t) :=
  idtac;
  first
    [ timeout 60
        first[ assert_succeeds (idtac; solve[t]); idtac "solved"
             | fail 2 "not solved" ]
    | idtac "timeout" ].

Require Import String.
Open Scope string_scope.

Inductive reduction := compute | vm_compute | none.

Tactic Notation "header" uconstr(id) constr(thm) constr(reduction) :=
  idtac "--------------------------------------------------------------------------------";
  idtac "::" id ":::" thm ":::" reduction.

Tactic Notation "bench1" uconstr(id) constr(thm) constr(reduction)  :=
  header id thm reduction;
  let reduction := lazymatch reduction with
                  | compute => fun _ => compute
                  | vm_compute => fun _ => vm_compute
                  | none => fun _ => idtac
                  end in
  time (run1 (solveOL BoolOL thm reduction)).

Tactic Notation "benchAll" uconstr(id) :=
  (* do 5 (bench1 id OL_Reflection_1_base.reduceToAlgo none); *)
  (* do 5 (bench1 id OL_Reflection_2_memo.reduceToAlgoMemo none); *)
  (* do 5 (bench1 id OL_Reflection_3_fmap.reduceToAlgoFmap none); *)
  (* do 5 (bench1 id OL_Reflection_4_pointers.reduceToAlgoPointers none); *)
  do 5 (bench1 id OL_Reflection_1_base.reduceToAlgo vm_compute);
  do 5 (bench1 id OL_Reflection_2_memo.reduceToAlgoMemo vm_compute);
  do 5 (bench1 id OL_Reflection_3_fmap.reduceToAlgoFmap vm_compute);
  do 5 (bench1 id OL_Reflection_4_pointers.reduceToAlgoPointers vm_compute);
  do 5 (header id "btauto" "btauto"; time (run1 (btauto))).

Notation "! a" := (negb a) (at level 9).

(**)

Theorem test1 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20: bool) :
  ((((((((((x0||x1)&&(x2||x3))&&(x4||x5))&&(x6||x7))&&(x8||x9))&&(x10||x11))&&(x12||x13))&&(x14||x15))&&(x16||x17))&&(x18||x19))
    =
  ((((((((((x1||x0)&&(x3||x2))&&(x5||x4))&&(x7||x6))&&(x9||x8))&&(x11||x10))&&(x13||x12))&&(x15||x14))&&(x17||x16))&&(x19||x18)).
Proof.
  benchAll "test1" .
Abort.

Theorem test2 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25: bool) :
  (((((((((((((x0||x1)&&(x2||x3))&&(x4||x5))&&(x6||x7))&&(x8||x9))&&(x10||x11))&&(x12||x13))&&(x14||x15))&&(x16||x17))&&(x18||x19))&&(x20||x21))&&(x22||x23))&&(x24||x25))
    =
  (((((((((((((x1||x0)&&(x3||x2))&&(x5||x4))&&(x7||x6))&&(x9||x8))&&(x11||x10))&&(x13||x12))&&(x15||x14))&&(x17||x16))&&(x19||x18))&&(x21||x20))&&(x23||x22))&&(x25||x24)).
Proof.
  benchAll "test2".
Abort.

Theorem test3 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30: bool) :
  (((((((((((((((x0||x1)&&(x2||x3))&&(x4||x5))&&(x6||x7))&&(x8||x9))&&(x10||x11))&&(x12||x13))&&(x14||x15))&&(x16||x17))&&(x18||x19))&&(x20||x21))&&(x22||x23))&&(x24||x25))&&(x26||x27))&&(x28||x29))
    =
  (((((((((((((((x1||x0)&&(x3||x2))&&(x5||x4))&&(x7||x6))&&(x9||x8))&&(x11||x10))&&(x13||x12))&&(x15||x14))&&(x17||x16))&&(x19||x18))&&(x21||x20))&&(x23||x22))&&(x25||x24))&&(x27||x26))&&(x29||x28)).
Proof.
  benchAll "test3".
Abort.

Theorem test4 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35: bool) :
  ((((((((((((((((((x0||x1)&&(x2||x3))&&(x4||x5))&&(x6||x7))&&(x8||x9))&&(x10||x11))&&(x12||x13))&&(x14||x15))&&(x16||x17))&&(x18||x19))&&(x20||x21))&&(x22||x23))&&(x24||x25))&&(x26||x27))&&(x28||x29))&&(x30||x31))&&(x32||x33))&&(x34||x35))
    =
  ((((((((((((((((((x1||x0)&&(x3||x2))&&(x5||x4))&&(x7||x6))&&(x9||x8))&&(x11||x10))&&(x13||x12))&&(x15||x14))&&(x17||x16))&&(x19||x18))&&(x21||x20))&&(x23||x22))&&(x25||x24))&&(x27||x26))&&(x29||x28))&&(x31||x30))&&(x33||x32))&&(x35||x34)).
Proof.
  benchAll "test4".
Abort.

Theorem test5 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40: bool) :
  ((((((((((((((((((((x0||x1)&&(x2||x3))&&(x4||x5))&&(x6||x7))&&(x8||x9))&&(x10||x11))&&(x12||x13))&&(x14||x15))&&(x16||x17))&&(x18||x19))&&(x20||x21))&&(x22||x23))&&(x24||x25))&&(x26||x27))&&(x28||x29))&&(x30||x31))&&(x32||x33))&&(x34||x35))&&(x36||x37))&&(x38||x39))
    =
  ((((((((((((((((((((x1||x0)&&(x3||x2))&&(x5||x4))&&(x7||x6))&&(x9||x8))&&(x11||x10))&&(x13||x12))&&(x15||x14))&&(x17||x16))&&(x19||x18))&&(x21||x20))&&(x23||x22))&&(x25||x24))&&(x27||x26))&&(x29||x28))&&(x31||x30))&&(x33||x32))&&(x35||x34))&&(x37||x36))&&(x39||x38)).
Proof.
  benchAll "test5".
Abort.

Theorem test6 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45: bool) :
  (((((((((((((((((((((((x0||x1)&&(x2||x3))&&(x4||x5))&&(x6||x7))&&(x8||x9))&&(x10||x11))&&(x12||x13))&&(x14||x15))&&(x16||x17))&&(x18||x19))&&(x20||x21))&&(x22||x23))&&(x24||x25))&&(x26||x27))&&(x28||x29))&&(x30||x31))&&(x32||x33))&&(x34||x35))&&(x36||x37))&&(x38||x39))&&(x40||x41))&&(x42||x43))&&(x44||x45))
    =
  (((((((((((((((((((((((x1||x0)&&(x3||x2))&&(x5||x4))&&(x7||x6))&&(x9||x8))&&(x11||x10))&&(x13||x12))&&(x15||x14))&&(x17||x16))&&(x19||x18))&&(x21||x20))&&(x23||x22))&&(x25||x24))&&(x27||x26))&&(x29||x28))&&(x31||x30))&&(x33||x32))&&(x35||x34))&&(x37||x36))&&(x39||x38))&&(x41||x40))&&(x43||x42))&&(x45||x44)).
Proof.
  benchAll "test6".
Abort.



Theorem test8 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20: bool) :
  ((!x9&&!x14)||((!x16||x12)&&((x0&&x11)||!x19||((!x11||!x0)&&!x3&&!x5&&((x10&&x10)||x9)))&&!x0)||(((!x14&&!x10)||x4||x0||!x0||!x1||((!x19||x17)&&!x13)||!x10||(x15&&(x8||x11)&&x7)||!x7||!x14||x11)&&x7&&(((x13||x4)&&x9)||((!x9||!x1||!x3)&&!x18))))
    =
  !(!(!x9&&!x14)&&!(!(x16&&!x12)&&!(!(x0&&x11)&&x19&&!(!(x11&&x0)&&!x3&&!x5&&!(!x10&&!x9)))&&!x0)&&!(x7&&!(!(!(!x13&&!x4)&&x9)&&!(!(x9&&x1&&x3)&&!x18)))).
Proof.
  benchAll "test8".
Abort.

Theorem test9 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20: bool) :
  ((x14||x17||!x2||x16||(x7&&x14)||x3||(x15&&x8)||(!x18&&!x17)||(x2&&!x13&&!x2&&x0))&&(((x1||x1)&&x18)||x7||!x7||!x3)&&(((x19||x19)&&!x16)||(!x12&&!x12))&&((((x9&&!x6)||(!x2&&x7)||x19)&&!x6)||x4)&&((x6&&!x16&&(!x7||x14||!x3))||(x15&&x2))&&!x6)
    =
  (!(!x14&&!x17&&x2&&!x16&&!x3&&!(x15&&x8)&&!(!x18&&!x17))&&!(!(x19&&!x16)&&x12)&&!(!(!(!(x9&&!x6)&&!(!x2&&x7)&&!x19)&&!x6)&&!x4)&&!(!(x6&&!x16&&!(x7&&!x14&&x3))&&!(x15&&x2))&&!x6).
Proof.
  benchAll "test9".
Abort.

Theorem test10 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20: bool) :
  (((!x13||(!x2&&x15&&x1))&&x14&&(x12||x10||x11||((!x3||x14)&&x5)||(!x16&&!x11))&&!x9&&x11)||!x6||(((!x19&&!x3&&x19)||x2||((!x10||!x12)&&!x17)||(!x15&&x8)||(!x1&&x16)||x16)&&(!x5||x2||!x3||x9))||(x17&&x8&&!x4)||!x11||x19||x3)
    =
  !(!(!(x13&&!(!x2&&x15&&x1))&&x14&&x11&&!x9)&&x6&&!(!(!x2&&!(!(x10&&x12)&&!x17)&&!(!x15&&x8)&&!x16)&&!(x5&&!x2&&x3&&!x9))&&!(x17&&x8&&!x4)&&x11&&!x19&&!x3).
Proof.
  benchAll "test10".
Abort.
