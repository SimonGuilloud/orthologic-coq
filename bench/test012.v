Require Import OL_Bench.

Theorem test012 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12: bool) :
  ((((((x0||x1)&&(x2||x3))&&(x4||x5))&&(x6||x7))&&(x8||x9))&&(x10||x11)) 
    = 
  ((((((x1||x0)&&(x3||x2))&&(x5||x4))&&(x7||x6))&&(x9||x8))&&(x11||x10))
. Proof.
    benchSlow "test12".
Admitted.
