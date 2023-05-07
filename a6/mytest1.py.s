  .globl main
label_9:
  movq $24, %rax
  cmpq $261, %rax
  seta %al
  movzbq %al, %r14
  movq %r14, %r11
  movq $Constant(val=3), 8(%r11)
  movq %r14, %r11
  movq $Var(var='x'), 16(%r11)
  movq %r14, %r14
  cmpq $1, %r14
  sets %al
  movzbq %al, %r14
  cmpq $0, %r14
  sets %al
  movzbq %al, %r14
  movq %r14, %rdi
  callq print_int
  movq $0, %rax
  jmp conclusion
label_10:
  jmp label_9
label_11:
  movq %r15, %rdi
  movq $24, %rsi
  callq collect
  jmp label_9
label_12:
  movq $24, %rax
  cmpq $5, %rax
  seta %al
  movzbq %al, %r14
  movq %r14, %r11
  movq $Constant(val=1), 8(%r11)
  movq %r14, %r11
  movq $Constant(val=2), 16(%r11)
  movq %r14, %r14
  movq free_ptr(%rip), %rax
  addq $24, %rax
  movq %rax, %r14
  cmpq fromspace_end(%rip), %r14
  setl %al
  movzbq %al, %r14
  movq $1, %rax
  cmpq %r14, %rax
  je label_10
  jmp label_11
label_13:
  jmp label_12
label_14:
  movq %r15, %rdi
  movq $24, %rsi
  callq collect
  jmp label_12
start:
  movq free_ptr(%rip), %rax
  addq $24, %rax
  movq %rax, %r14
  cmpq fromspace_end(%rip), %r14
  setl %al
  movzbq %al, %r14
  movq $1, %rax
  cmpq %r14, %rax
  je label_13
  jmp label_14
main:
  pushq %rbp
  movq %rsp, %rbp
  subq $0, %rsp
  movq $16384, %rdi
  movq $16, %rsi
  callq initialize
  jmp start
conclusion:
  addq $0, %rsp
  popq %rbp
  retq
