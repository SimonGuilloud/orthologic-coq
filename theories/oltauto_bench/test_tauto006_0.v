Require Import OL_Bench.


Theorem test_tauto06_0 (x0 x1 x2 x3 x4 x5 x6: bool) :
  !(((((!x5&&!x3)||(!x2&&x0)||(!x2&&x3))&&((x4&&x4)||(x1&&!x3)||(!x3&&x4)))||(((x2&&!x5)||(!x0&&!x2)||(!x0&&!x5))&&((!x0&&x2)||(x2&&!x1)||(x4&&x1)))||(((!x0&&x3)||(x5&&!x0)||(x1&&x4))&&((x5&&!x2)||(!x4&&!x5)||(!x2&&!x1)))||(((x4&&!x4)||(!x5&&x0)||(x1&&!x5))&&((!x1&&x5)||(!x3&&x3)||(!x4&&x4))))&&((((x2&&!x1)||(x4&&!x3)||(!x3&&!x3))&&((!x1&&x0)||(!x5&&!x2)||(x5&&x1)))||(((x2&&x5)||(!x3&&!x0)||(x4&&!x4))&&((!x2&&!x4)||(!x2&&x2)||(x4&&x2)))||(((!x1&&x0)||(x5&&!x4)||(x5&&x3))&&((!x2&&x4)||(!x1&&!x1)||(!x0&&!x1)))||(((!x0&&x0)||(x1&&!x2)||(x0&&x0))&&((!x2&&!x3)||(!x1&&x1)||(x4&&!x3))))) 
    = 
  true
. Proof.
    benchtauto "test06_0".
Admitted.
