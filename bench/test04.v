Require Import OL_Bench.

Theorem test04 (x0 x1 x2 x3 x4: bool) :
  ((x0||x1)&&(x2||x3)) 
    = 
  ((x1||x0)&&(x3||x2))
. Proof.
    benchSlow "test4".
Admitted.
