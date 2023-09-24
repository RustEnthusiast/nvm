extern main
global _start
section .text
_start:
    call main
    xor rdi, rdi
    mov rax, 60
    syscall
