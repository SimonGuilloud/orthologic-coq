Require Import OL_Bench.

Theorem test10 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10: bool) :
  (((((x0||x1)&&(x2||x3))&&(x4||x5))&&(x6||x7))&&(x8||x9)) 
    = 
  (((((x1||x0)&&(x3||x2))&&(x5||x4))&&(x7||x6))&&(x9||x8))
. Proof.
    benchslow "test10".
Admitted.
