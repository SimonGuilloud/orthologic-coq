
Require Import OL_Theory.
Require Import OL_Reflection.

Require Import Setoid Morphisms.
Require Import Lia.
Require Import Coq.Arith.Bool_nat.
Require Import Coq.Arith.PeanoNat.


Open Scope bool_scope.
Require Import Btauto.
Import List.
Import ListNotations.


Notation "! a" := (negb a) (at level 9).

Theorem test1_solveOL (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : bool) : 
  (x9 || (!x11 && x11 && !x7) || !x8 || !x0 || x13 || !x14 || x2 || ((((x2 || x6) && !x5) || (x1 && ((x3 && !x5) || !x13) && x9)) && !x13 && !x0 && !x7)) =
  !(!x9 && x8 && x0 && !x13 && x14 && !x2)
.
Proof.
  solveOL BoolOL.
Qed.

Theorem test1_btauto (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : bool) : 
  (x9 || (!x11 && x11 && !x7) || !x8 || !x0 || x13 || !x14 || x2 || ((((x2 || x6) && !x5) || (x1 && ((x3 && !x5) || !x13) && x9)) && !x13 && !x0 && !x7)) =
  !(!x9 && x8 && x0 && !x13 && x14 && !x2)
.
Proof.
  timeout 10 (btauto). 
Qed.




Theorem test2_solveOL (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 : bool) : 
(x49||(x48&&(x47||(x46&&(x45||(x44&&(x43||(x42&&(x41||(x40&&(x39||(x38&&(x37||(x36&&(x35||(x34&&(x33||(x32&&(x31||(x30&&(x29||(x28&&(x27||(x26&&(x25||(x24&&(x23||(x22&&(x21||(x20&&(x19||(x18&&(x17||(x16&&(x15||(x14&&(x13||(x12&&(x11||(x10&&(x9||(x8&&(x7||(x6&&(x5||(x4&&(x3||(x2&&(x0||x1)))))))))))))))))))))))))))))))))))))))))))))))))
  =
(x49||(x48&&(x47||(x46&&(x45||(x44&&(x43||(x42&&(x41||(x40&&(x39||(x38&&(x37||(x36&&(x35||(x34&&(x33||(x32&&(x31||(x30&&(x29||(x28&&(x27||(x26&&(x25||(x24&&(x23||(x22&&(x21||(x20&&(x19||(x18&&(x17||(x16&&(x15||(x14&&(x13||(x12&&(x11||(x10&&(x9||(x8&&(x7||(x6&&(x5||(x4&&(x3||(x2&&(x1||x0)))))))))))))))))))))))))))))))))))))))))))))))))
.
Proof.
  timeout 10 (solveOL BoolOL).
Qed.

Theorem test2_btauto (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 : bool) : 
(x49||(x48&&(x47||(x46&&(x45||(x44&&(x43||(x42&&(x41||(x40&&(x39||(x38&&(x37||(x36&&(x35||(x34&&(x33||(x32&&(x31||(x30&&(x29||(x28&&(x27||(x26&&(x25||(x24&&(x23||(x22&&(x21||(x20&&(x19||(x18&&(x17||(x16&&(x15||(x14&&(x13||(x12&&(x11||(x10&&(x9||(x8&&(x7||(x6&&(x5||(x4&&(x3||(x2&&(x0||x1)))))))))))))))))))))))))))))))))))))))))))))))))
  =
(x49||(x48&&(x47||(x46&&(x45||(x44&&(x43||(x42&&(x41||(x40&&(x39||(x38&&(x37||(x36&&(x35||(x34&&(x33||(x32&&(x31||(x30&&(x29||(x28&&(x27||(x26&&(x25||(x24&&(x23||(x22&&(x21||(x20&&(x19||(x18&&(x17||(x16&&(x15||(x14&&(x13||(x12&&(x11||(x10&&(x9||(x8&&(x7||(x6&&(x5||(x4&&(x3||(x2&&(x1||x0)))))))))))))))))))))))))))))))))))))))))))))))))
.
Proof.
  timeout 10 (btauto).
Admitted.



Theorem test3_solveOL (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25: bool) :
  (((((((((((((x0||x1)&&(x2||x3))&&(x4||x5))&&(x6||x7))&&(x8||x9))&&(x10||x11))&&(x12||x13))&&(x14||x15))&&(x16||x17))&&(x18||x19))&&(x20||x21))&&(x22||x23))&&(x24||x25)) 
    = 
  (((((((((((((x1||x0)&&(x3||x2))&&(x5||x4))&&(x7||x6))&&(x9||x8))&&(x11||x10))&&(x13||x12))&&(x15||x14))&&(x17||x16))&&(x19||x18))&&(x21||x20))&&(x23||x22))&&(x25||x24))
. Proof. timeout 10 (solveOL BoolOL). Qed.

Theorem test3_btauto (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25: bool) :
  (((((((((((((x0||x1)&&(x2||x3))&&(x4||x5))&&(x6||x7))&&(x8||x9))&&(x10||x11))&&(x12||x13))&&(x14||x15))&&(x16||x17))&&(x18||x19))&&(x20||x21))&&(x22||x23))&&(x24||x25)) 
    = 
  (((((((((((((x1||x0)&&(x3||x2))&&(x5||x4))&&(x7||x6))&&(x9||x8))&&(x11||x10))&&(x13||x12))&&(x15||x14))&&(x17||x16))&&(x19||x18))&&(x21||x20))&&(x23||x22))&&(x25||x24))
. Proof. timeout 10 (btauto). Qed.