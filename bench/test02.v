Require Import OL_Bench.

Theorem test2 (x0 x1 x2: bool) :
  (x0||x1) 
    = 
  (x1||x0)
. Proof.
    benchSlow "test02".
Admitted.
