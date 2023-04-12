
; format string for printf
int1:     dd    1234567
int2:     dd    0o1234567
int3:     dd    $1234
    mov eax, ecx
hex1:     dd    0x6789ABCD
flt0:     dd    5.327
flt1:     dd    5.327e-30
flt2:     dq    -123.456789e300
flt3:     dq    0x1a.30
flt4:     dq    $1a.30
uninit:   resq 16
