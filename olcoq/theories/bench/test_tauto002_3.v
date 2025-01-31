Require Import OL_Bench.


Theorem test_tauto02_3 (x0 x1 x2: bool) :
  !(((x0&&x1)||(x1&&x0)||(!x0&&!x1)||(x0&&x1))&&((!x0&&!x1)||(!x0&&x0)||(!x0&&!x1)||(x1&&!x0))) 
    = 
  true
. Proof.
    benchtauto "test02_3".
Admitted.
