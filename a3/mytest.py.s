  .globl main
main:
  pushq %rbp
  movq %rsp, %rbp
  subq $0, %rsp
  movq $5, %rdx
  movq $6, %rdx
  movq $7, %r10
  movq $8, %rdx
  movq $9, %rdx
  movq $10, %rdx
  movq $11, %r11
  movq $12, %rdx
  movq $13, %rdx
  movq $14, %rdx
  movq $15, %rdx
  movq $16, %rdi
  movq $17, %r8
  movq $18, %rdx
  movq %rdx, %rax
  addq %rdx, %rax
  movq %rax, %rdx
  movq %rdx, %rax
  addq %r10, %rax
  movq %rax, %rdx
  movq %rdx, %rax
  addq %rdx, %rax
  movq %rax, %rdx
  movq %rdx, %rax
  addq %rdx, %rax
  movq %rax, %rcx
  movq %rcx, %rax
  addq %rdx, %rax
  movq %rax, %rdx
  movq %rdx, %rax
  addq %r11, %rax
  movq %rax, %rdx
  movq %rdx, %rax
  addq %rdx, %rax
  movq %rax, %rdx
  movq %rdx, %rax
  addq %rdx, %rax
  movq %rax, %rdx
  movq %rdx, %rax
  addq %rdx, %rax
  movq %rax, %rdx
  movq %rdx, %rax
  addq %rdx, %rax
  movq %rax, %rsi
  movq %rsi, %rax
  addq %rdi, %rax
  movq %rax, %r9
  movq %r9, %rax
  addq %r8, %rax
  movq %rax, %rdx
  movq %rdx, %rax
  addq %rdx, %rax
  movq %rax, %rdx
  movq %rdx, %rdi
  callq print_int
  addq $0, %rsp
  popq %rbp
  retq
