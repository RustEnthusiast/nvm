push %rax
call main
mov %rax, %rdi
pop %rax
syscall
