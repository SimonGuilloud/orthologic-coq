Require Import OL_Bench.

Theorem test06 (x0 x1 x2 x3 x4 x5 x6: bool) :
  (((x0||x1)&&(x2||x3))&&(x4||x5)) 
    = 
  (((x1||x0)&&(x3||x2))&&(x5||x4))
. Proof.
    benchSlow "test6".
Admitted.
