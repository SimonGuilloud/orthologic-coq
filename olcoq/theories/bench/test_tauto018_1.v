Require Import OL_Bench.


Theorem test_tauto18_1 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18: bool) :
  !(((((x2&&!x6)||(!x1&&x10)||(x14&&x6)||(!x17&&x1))&&((!x1&&x2)||(x12&&!x16)||(!x6&&x15)||(!x10&&x10)))||(((x0&&x8)||(x4&&!x1)||(x2&&x15)||(x7&&x8))&&((x7&&x10)||(x1&&!x9)||(!x0&&!x10)||(!x5&&!x0)))||(((!x1&&x8)||(!x11&&x10)||(!x6&&!x0)||(x0&&x14))&&((!x4&&!x6)||(x9&&x11)||(x17&&x12)||(!x4&&!x6)))||(((!x15&&x12)||(x14&&x11)||(!x13&&x7)||(x17&&x6))&&((!x7&&x5)||(!x9&&x3)||(!x17&&x11)||(!x15&&x7))))&&((((!x12&&x11)||(x8&&!x3)||(x0&&x4)||(!x10&&x9))&&((!x10&&x16)||(x15&&!x5)||(!x15&&!x3)||(!x4&&x8)))||(((x9&&x2)||(x14&&x11)||(!x11&&x9)||(!x4&&x8))&&((!x13&&x17)||(!x8&&x4)||(x5&&!x16)||(x13&&x5)))||(((!x15&&x17)||(!x6&&x4)||(!x2&&x8)||(!x8&&!x15))&&((!x6&&x13)||(x13&&x16)||(!x13&&!x5)||(x4&&!x0)))||(((x7&&x1)||(!x2&&x9)||(!x6&&x17)||(!x4&&x12))&&((!x12&&x8)||(!x4&&x16)||(x6&&!x9)||(!x3&&!x14))))&&((((!x10&&!x6)||(x11&&x7)||(!x17&&x15)||(!x7&&x14))&&((x14&&!x7)||(!x13&&!x17)||(!x12&&x4)||(x7&&x7)))||(((x12&&!x6)||(!x8&&x13)||(!x4&&x2)||(x7&&x8))&&((!x6&&x12)||(x1&&x0)||(x12&&!x1)||(x2&&x12)))||(((!x13&&!x8)||(!x12&&x0)||(!x15&&!x11)||(x16&&x1))&&((x0&&!x14)||(x17&&x15)||(!x9&&!x5)||(x3&&!x9)))||(((x6&&x10)||(!x15&&x5)||(!x8&&!x10)||(!x15&&!x2))&&((x9&&x15)||(!x11&&!x7)||(!x3&&x10)||(x17&&!x13))))) 
    = 
  true
. Proof.
    benchtauto "test18_1".
Admitted.
