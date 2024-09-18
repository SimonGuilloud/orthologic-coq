Require Import OL_Bench.

Theorem test8 (x0 x1 x2 x3 x4 x5 x6 x7 x8: bool) :
  ((((x0||x1)&&(x2||x3))&&(x4||x5))&&(x6||x7)) 
    = 
  ((((x1||x0)&&(x3||x2))&&(x5||x4))&&(x7||x6))
. Proof.
    benchslow "test8".
Admitted.
