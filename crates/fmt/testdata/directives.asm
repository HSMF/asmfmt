[bits 32];comment that is very close
 [   bits 64 ]
            section .text       ; comment that is far away
    section .data
 section .bss  ; comment that is at the right place
 [  bits       16 ]

         section .text
global _main
  extern printf,exit,malloc
