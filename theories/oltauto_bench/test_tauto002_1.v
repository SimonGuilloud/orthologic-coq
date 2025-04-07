Require Import OL_Bench.


Theorem test_tauto02_1 (x0 x1 x2: bool) :
  !(((x0&&!x0)||(x1&&!x0)||(!x0&&!x1)||(x1&&!x1))&&((!x1&&x1)||(!x1&&x0)||(!x0&&x0)||(!x1&&x1))) 
    = 
  true
. Proof.
    benchtauto "test02_1".
Admitted.
