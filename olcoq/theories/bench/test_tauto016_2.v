Require Import OL_Bench.


Theorem test_tauto16_2 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16: bool) :
  !(((((!x15&&x1)||(!x0&&!x8)||(!x2&&!x1)||(!x9&&x7))&&((x15&&!x3)||(x6&&x9)||(!x2&&x4)||(x3&&x4)))||(((!x7&&x12)||(x8&&x5)||(x1&&x4)||(x3&&!x3))&&((x14&&x6)||(!x9&&!x4)||(x7&&!x14)||(!x4&&!x7)))||(((!x2&&x4)||(!x3&&!x9)||(x15&&!x0)||(x11&&!x8))&&((x6&&!x12)||(x14&&x11)||(x13&&x10)||(x1&&x5)))||(((x3&&!x0)||(x2&&x1)||(!x11&&!x5)||(!x15&&x13))&&((!x12&&x4)||(!x11&&x6)||(!x11&&x12)||(!x9&&!x9))))&&((((!x0&&!x12)||(x2&&!x10)||(x15&&x7)||(!x10&&!x14))&&((!x0&&x1)||(x2&&x8)||(!x0&&x12)||(x2&&!x4)))||(((!x15&&!x10)||(x0&&!x12)||(!x6&&!x12)||(!x1&&!x6))&&((!x10&&!x7)||(x10&&!x12)||(x6&&!x15)||(x7&&x0)))||(((x4&&!x11)||(!x2&&x12)||(!x7&&!x5)||(x15&&!x7))&&((x2&&!x5)||(x1&&!x15)||(!x1&&x7)||(!x15&&!x10)))||(((!x4&&!x6)||(x12&&!x11)||(x13&&x9)||(!x13&&!x10))&&((!x13&&x0)||(!x13&&!x3)||(!x8&&x12)||(!x6&&!x6))))&&((((!x12&&x12)||(x2&&!x12)||(x10&&!x14)||(!x12&&!x4))&&((x15&&!x6)||(!x1&&!x2)||(!x12&&x2)||(!x12&&x4)))||(((x4&&!x0)||(x15&&x9)||(!x12&&x4)||(!x13&&x15))&&((x7&&x7)||(!x4&&x8)||(x5&&x14)||(x15&&!x15)))||(((!x14&&!x0)||(!x10&&x12)||(!x2&&!x11)||(x5&&!x15))&&((!x8&&!x12)||(x3&&x0)||(x3&&!x2)||(!x10&&!x14)))||(((x9&&!x6)||(!x2&&!x7)||(x2&&x13)||(x1&&!x15))&&((x7&&!x8)||(!x8&&!x1)||(!x13&&x3)||(!x3&&!x11))))) 
    = 
  true
. Proof.
    benchtauto "test16_2".
Admitted.
