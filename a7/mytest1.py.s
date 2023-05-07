  .globl main
factlabel_8:
  movq $0, %rax
  jmp conclusion
factlabel_9:
  movq $1, %rax
  jmp conclusion
  jmp factlabel_8
factlabel_10:
  movq %rbx, %rax
  subq $1, %rax
  movq %rax, %rdx
  leaq fact(%rip), %rcx
  movq %rdx, %rdi
  callq *#tmp_3
  movq %rax, %rdx
  movq %rbx, %rax
  imulq %rdx, %rax
  movq %rax, %rdx
  movq %rdx, %rax
  jmp conclusion
  jmp factlabel_8
factstart:
  movq %rdi, %rbx
  cmpq $0, %rbx
  sete %al
  movzbq %al, %rdx
  movq $1, %rax
  cmpq %rdx, %rax
  je factlabel_9
  jmp factlabel_10
main:
  pushq %rbp
  movq %rsp, %rbp
  pushq %r12
  pushq %r13
  pushq %r14
  pushq %r15
  subq $0, %rsp
  movq rootstack_begin(%rip), %r15
  movq $16384, %rdi
  movq $16, %rsi
  callq initialize
  jmp main
factconclusion:
  jmp factconclusion
  addq $0, %r15
  popq %r15
  popq %r14
  popq %r13
  popq %r12
  addq $0, %rsp
  popq %rbp
  retq
mainstart:
  leaq fact(%rip), %rdx
  movq $5, %rdi
  callq *#tmp_6
  movq %rax, %rdx
  movq %rdx, %rdi
  callq print_int
  movq $0, %rax
  jmp conclusion
mainconclusion:
  jmp mainconclusion
  addq $0, %r15
  popq %r15
  popq %r14
  popq %r13
  popq %r12
  addq $0, %rsp
  popq %rbp
  retq
