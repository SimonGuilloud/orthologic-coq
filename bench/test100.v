Require Import OL_Bench.

Theorem test100 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 x60 x61 x62 x63 x64 x65 x66 x67 x68 x69 x70 x71 x72 x73 x74 x75 x76 x77 x78 x79 x80 x81 x82 x83 x84 x85 x86 x87 x88 x89 x90 x91 x92 x93 x94 x95 x96 x97 x98 x99 x100: bool) :
  ((((((((((((((((((((((((((((((((((((((((((((((((((x0||x1)&&(x2||x3))&&(x4||x5))&&(x6||x7))&&(x8||x9))&&(x10||x11))&&(x12||x13))&&(x14||x15))&&(x16||x17))&&(x18||x19))&&(x20||x21))&&(x22||x23))&&(x24||x25))&&(x26||x27))&&(x28||x29))&&(x30||x31))&&(x32||x33))&&(x34||x35))&&(x36||x37))&&(x38||x39))&&(x40||x41))&&(x42||x43))&&(x44||x45))&&(x46||x47))&&(x48||x49))&&(x50||x51))&&(x52||x53))&&(x54||x55))&&(x56||x57))&&(x58||x59))&&(x60||x61))&&(x62||x63))&&(x64||x65))&&(x66||x67))&&(x68||x69))&&(x70||x71))&&(x72||x73))&&(x74||x75))&&(x76||x77))&&(x78||x79))&&(x80||x81))&&(x82||x83))&&(x84||x85))&&(x86||x87))&&(x88||x89))&&(x90||x91))&&(x92||x93))&&(x94||x95))&&(x96||x97))&&(x98||x99)) 
    = 
  ((((((((((((((((((((((((((((((((((((((((((((((((((x1||x0)&&(x3||x2))&&(x5||x4))&&(x7||x6))&&(x9||x8))&&(x11||x10))&&(x13||x12))&&(x15||x14))&&(x17||x16))&&(x19||x18))&&(x21||x20))&&(x23||x22))&&(x25||x24))&&(x27||x26))&&(x29||x28))&&(x31||x30))&&(x33||x32))&&(x35||x34))&&(x37||x36))&&(x39||x38))&&(x41||x40))&&(x43||x42))&&(x45||x44))&&(x47||x46))&&(x49||x48))&&(x51||x50))&&(x53||x52))&&(x55||x54))&&(x57||x56))&&(x59||x58))&&(x61||x60))&&(x63||x62))&&(x65||x64))&&(x67||x66))&&(x69||x68))&&(x71||x70))&&(x73||x72))&&(x75||x74))&&(x77||x76))&&(x79||x78))&&(x81||x80))&&(x83||x82))&&(x85||x84))&&(x87||x86))&&(x89||x88))&&(x91||x90))&&(x93||x92))&&(x95||x94))&&(x97||x96))&&(x99||x98))
. Proof.

    benchSuperFast "test100".
Admitted.
