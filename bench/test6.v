Require Import OL_Bench.

Theorem test6 (x0 x1 x2 x3 x4 x5 x6: bool) :
  (((x0||x1)&&(x2||x3))&&(x4||x5)) 
    = 
  (((x1||x0)&&(x3||x2))&&(x5||x4))
. Proof.
    benchslow "test6".
Admitted.
