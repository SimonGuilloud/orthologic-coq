Require Import OL_Bench.


Theorem test_tauto02_0 (x0 x1 x2: bool) :
  !(((!x0&&!x0)||(x0&&x1)||(x0&&!x1)||(!x0&&!x0))&&((x1&&x0)||(!x0&&x1)||(!x0&&!x1)||(!x0&&x1))) 
    = 
  true
. Proof.
    benchtauto "test02_0".
Admitted.
