a1:      db    0x55                ; just the byte 0x55 
a2:      db    0x55,0x56,0x57      ; three bytes in succession 
a3:      db    'a',0x55            ; character constants are OK 
a4:      db    'hello',13,10,'$'   ; so are string constants 
a5:      dw    0x1234              ; 0x34 0x12 
a6:      dw    'a' ; 0x61 0x00 (it's just a number) 
a7:      dw    'ab'  ; 0x61 0x62 (character constant) 
a8:      dw    'abc'               ; 0x61 0x62 0x63 0x00 (string) 
a9:      dd    0x12345678          ; 0x78 0x56 0x34 0x12 
a10:      dd    1.234567e20         ; floating-point constant 
a11:      dq  0x123456789abcdef0  ; eight byte constant 
a12:      dq   1.234567e20         ; double-precision float 
a13:      dt    1.234567e20         ; extended-precision float
str: db `"yeah"`

buffer:        resb    64              ; reserve 64 bytes 
wordvar:       resw    1               ; reserve a word 
realarray:   resq    10              ; array of ten reals 
ymmval:         resy    1               ; one YMM register 
zmmvals:       resz    32              ; 32 ZMM registers
