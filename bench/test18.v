Require Import OL_Bench.

Theorem test18 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18: bool) :
  (((((((((x0||x1)&&(x2||x3))&&(x4||x5))&&(x6||x7))&&(x8||x9))&&(x10||x11))&&(x12||x13))&&(x14||x15))&&(x16||x17)) 
    = 
  (((((((((x1||x0)&&(x3||x2))&&(x5||x4))&&(x7||x6))&&(x9||x8))&&(x11||x10))&&(x13||x12))&&(x15||x14))&&(x17||x16))
. Proof.
    benchSlow "test18".
Admitted.
