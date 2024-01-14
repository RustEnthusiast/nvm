push %rax
push %rdi
call main
pop %rdi
pop %rax
syscall
