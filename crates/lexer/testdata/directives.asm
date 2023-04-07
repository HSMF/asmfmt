    SECTION .data        ; data section
    section .text
    a:    db "aaaaaa\n"
    mov    eax, [a]
    push    dword [a]    ; value of variable a
    push    dword fmt    ; address of ctrl string
main:
    
    int 0x80

