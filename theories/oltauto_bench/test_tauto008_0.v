Require Import OL_Bench.


Theorem test_tauto08_0 (x0 x1 x2 x3 x4 x5 x6 x7 x8: bool) :
  !(((((!x1&&!x0)||(!x3&&x5)||(!x2&&!x4)||(x6&&x7))&&((x0&&!x1)||(x0&&!x3)||(!x4&&x1)||(!x3&&x5)))||(((x0&&x7)||(x1&&!x2)||(!x2&&x0)||(!x6&&!x7))&&((x5&&!x7)||(!x6&&x7)||(x2&&!x6)||(!x2&&x4)))||(((x4&&x6)||(x2&&x4)||(x7&&x6)||(x4&&x6))&&((!x4&&!x4)||(!x3&&x2)||(!x3&&x1)||(!x4&&!x1)))||(((x2&&x3)||(!x5&&x3)||(!x7&&!x1)||(!x4&&!x3))&&((!x5&&x3)||(x7&&!x5)||(x3&&!x2)||(x4&&!x6))))&&((((x5&&x0)||(!x3&&x4)||(!x3&&!x6)||(x0&&!x6))&&((!x7&&x7)||(x3&&!x6)||(!x0&&!x5)||(!x5&&!x7)))||(((x1&&x2)||(x1&&!x2)||(!x6&&x4)||(x3&&x2))&&((x2&&x4)||(x3&&x6)||(x3&&x0)||(!x7&&!x0)))||(((x5&&!x5)||(x4&&x2)||(x6&&x1)||(!x7&&x5))&&((x2&&!x3)||(!x4&&!x3)||(x4&&!x7)||(!x0&&x5)))||(((x2&&!x0)||(x2&&x7)||(!x4&&x3)||(x0&&x2))&&((x1&&!x7)||(!x3&&!x0)||(x5&&x3)||(x5&&!x5))))) 
    = 
  true
. Proof.
    benchtauto "test08_0".
Admitted.
