Require Import OL_Bench.


Theorem test_tauto20_1 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20: bool) :
  !(((((!x10&&x5)||(x14&&x6)||(x11&&!x17)||(!x18&&!x6))&&((x9&&!x13)||(!x1&&x0)||(!x15&&x2)||(!x2&&!x13)))||(((x17&&!x0)||(!x0&&x11)||(x19&&x15)||(x16&&!x5))&&((x13&&x19)||(x11&&x4)||(x7&&x14)||(!x14&&!x6)))||(((x4&&x11)||(!x9&&!x18)||(!x13&&!x7)||(x10&&x13))&&((x17&&!x1)||(x5&&!x1)||(x4&&!x2)||(x12&&!x9)))||(((x13&&x3)||(!x9&&!x10)||(!x13&&!x8)||(x0&&!x1))&&((x7&&x9)||(!x5&&x7)||(!x11&&x14)||(!x19&&x7))))&&((((x17&&!x16)||(x9&&x8)||(x6&&!x19)||(x7&&!x9))&&((x19&&!x8)||(!x9&&!x11)||(!x11&&x18)||(!x18&&x19)))||(((x19&&x6)||(!x16&&x6)||(!x13&&!x9)||(x18&&!x10))&&((!x11&&x2)||(x3&&x16)||(x6&&x14)||(!x18&&!x18)))||(((x5&&x17)||(!x6&&!x4)||(x9&&x8)||(x8&&!x12))&&((x17&&!x6)||(!x6&&x19)||(!x9&&x14)||(x8&&!x11)))||(((x8&&!x9)||(!x3&&x8)||(!x15&&!x13)||(!x7&&!x14))&&((x17&&!x6)||(!x18&&!x11)||(!x11&&x9)||(x5&&!x6))))&&((((!x15&&x9)||(x7&&!x13)||(x19&&!x4)||(!x11&&!x12))&&((x17&&x9)||(!x15&&!x16)||(x9&&!x5)||(!x3&&!x16)))||(((x12&&x7)||(x18&&!x12)||(!x0&&!x13)||(x2&&!x6))&&((x15&&!x2)||(!x18&&!x7)||(!x3&&x4)||(!x8&&x8)))||(((x12&&!x9)||(x17&&x15)||(x7&&!x12)||(!x5&&!x17))&&((!x3&&x3)||(!x5&&!x7)||(x12&&x11)||(x3&&!x3)))||(((x6&&x5)||(x6&&!x2)||(x8&&!x9)||(!x5&&!x9))&&((x11&&!x14)||(x2&&x1)||(!x9&&x14)||(!x16&&x8))))) 
    = 
  true
. Proof.
    benchtauto "test20_1".
Admitted.
