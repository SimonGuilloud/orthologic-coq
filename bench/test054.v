Require Import OL_Bench.


Theorem test054 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54: bool) :
  (((((((((((((((((((((((((((x0||x1)&&(x2||x3))&&(x4||x5))&&(x6||x7))&&(x8||x9))&&(x10||x11))&&(x12||x13))&&(x14||x15))&&(x16||x17))&&(x18||x19))&&(x20||x21))&&(x22||x23))&&(x24||x25))&&(x26||x27))&&(x28||x29))&&(x30||x31))&&(x32||x33))&&(x34||x35))&&(x36||x37))&&(x38||x39))&&(x40||x41))&&(x42||x43))&&(x44||x45))&&(x46||x47))&&(x48||x49))&&(x50||x51))&&(x52||x53)) 
    = 
  (((((((((((((((((((((((((((x1||x0)&&(x3||x2))&&(x5||x4))&&(x7||x6))&&(x9||x8))&&(x11||x10))&&(x13||x12))&&(x15||x14))&&(x17||x16))&&(x19||x18))&&(x21||x20))&&(x23||x22))&&(x25||x24))&&(x27||x26))&&(x29||x28))&&(x31||x30))&&(x33||x32))&&(x35||x34))&&(x37||x36))&&(x39||x38))&&(x41||x40))&&(x43||x42))&&(x45||x44))&&(x47||x46))&&(x49||x48))&&(x51||x50))&&(x53||x52))
. Proof.
    benchFast "test54".
Admitted.
