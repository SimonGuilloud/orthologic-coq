Require Import OL_Bench.


Theorem test_tauto16_0 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16: bool) :
  !(((((!x9&&x3)||(x8&&x8)||(!x11&&!x3)||(!x6&&x6))&&((!x0&&!x3)||(x4&&!x13)||(!x2&&!x5)||(!x3&&x10)))||(((x7&&!x13)||(!x0&&!x3)||(!x4&&x6)||(!x10&&x15))&&((!x0&&x13)||(x13&&x9)||(x8&&x7)||(!x12&&!x6)))||(((!x11&&x15)||(!x8&&x4)||(x2&&!x9)||(x8&&!x5))&&((!x9&&x8)||(x13&&!x15)||(!x5&&x14)||(x13&&x0)))||(((!x12&&!x10)||(!x3&&!x8)||(x6&&!x2)||(!x0&&x13))&&((!x8&&!x15)||(!x1&&!x12)||(!x1&&!x15)||(!x7&&!x1))))&&((((x12&&x14)||(x12&&x6)||(!x4&&x15)||(!x9&&x8))&&((x14&&x13)||(x3&&x6)||(!x5&&x8)||(!x15&&x15)))||(((!x0&&!x3)||(x11&&!x0)||(x2&&x15)||(!x0&&x6))&&((x3&&!x13)||(x11&&x15)||(!x11&&!x13)||(!x7&&x10)))||(((x9&&!x7)||(x12&&!x2)||(x6&&x9)||(x3&&x13))&&((x9&&x13)||(x9&&x4)||(!x15&&!x12)||(!x14&&!x7)))||(((!x10&&!x8)||(!x9&&!x11)||(!x15&&x14)||(x10&&!x2))&&((!x14&&x5)||(!x15&&!x5)||(x7&&!x12)||(!x14&&x14))))&&((((!x14&&x14)||(!x9&&x7)||(x7&&x5)||(!x0&&!x14))&&((!x7&&!x7)||(x14&&x9)||(!x2&&x6)||(!x7&&!x12)))||(((x13&&x6)||(!x11&&x5)||(x8&&x0)||(x15&&x0))&&((x6&&!x8)||(!x10&&x4)||(!x7&&x1)||(!x13&&x13)))||(((x8&&!x3)||(x4&&x8)||(!x8&&!x13)||(x0&&x4))&&((!x12&&x14)||(!x8&&!x13)||(!x6&&x14)||(!x9&&!x11)))||(((x5&&!x13)||(!x6&&!x10)||(!x3&&x1)||(!x5&&!x7))&&((!x12&&!x1)||(x1&&!x13)||(!x13&&!x8)||(x2&&x1))))) 
    = 
  true
. Proof.
    benchtauto "test16_0".
Admitted.
