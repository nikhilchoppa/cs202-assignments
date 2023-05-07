from __future__ import annotations

from typing import List, Set, Dict, Tuple
import sys
import traceback

from cs202_support.python import *
import cs202_support.x86 as x86
from cs202_support.python_ast import Program
from cs202_support.x86 import Instr, X86Program

# Input Language: LVar
# op ::= "add"
# Expr ::= Var(x) | Constant(n) | Prim(op, [Expr])
# Stmt ::= Assign(x, Expr) | Print(Expr)
# LVar ::= Program([Stmt])

gensym_num = 0


def gensym(x):
    """
    Constructs a new variable name guaranteed to be unique.
    :param x: A "base" variable name (e.g. "x")
    :return: A unique variable name (e.g. "x_1")
    """

    global gensym_num
    gensym_num = gensym_num + 1
    return f'{x}_{gensym_num}'


##################################################
# remove-complex-opera*
##################################################
def rco(prog: Program) -> Program:
    """
    Removes complex operands. After this pass, the arguments to operators (unary and binary
    operators, and function calls like "print") will be atomic.
    :param prog: An Lvar program
    :return: An Lvar program with atomic operator arguments.
    """
    """rco exp compiles an expression
       rco stmt compiles a statement
       rco stmts compiles a list of statements"""

    # responsible for returning atomic things only
    def rco_exp(e: Expr, bindings: Dict[str, Expr]) -> Expr:
        match e:
            # - Constant or Var expression : just return it
            case Constant(n):
                return Constant(n)
            case Var(x):
                return Var(x)
            # Prim expression:
            case Prim(op, args):
                new_args = [rco_exp(a, bindings) for a in args]
                tmp = gensym('tmp')
                bindings[tmp] = Prim(op, new_args)
                return Var(tmp)
            # empty case
            case _:
                raise Exception('rco_exp', e)

    # For each argument to the prim, create a new temporary variable (if needed) and bind it to the result of
    # compiling the Argument expression. - We can store new bindings in an environment L str -> Expr
    def rco_stmt(s: Stmt, bindings: Dict[str, Expr]) -> Stmt:
        match s:
            case Assign(x, e):
                return Assign(x, rco_exp(e, bindings))
            case Print(e):
                return Print(rco_exp(e, bindings))
            case _:
                raise Exception('rco_stmt', s)

    # Assignment(x, e): call rco_exp on e
    # - Print(e): call rco_exp on e
    # - Challenge: what about binding?
    def rco_stmts(stmts: List[Stmt], bindings: Dict[str, Expr] = {}) -> List[Stmt]:
        # - For each stmt
        # - call rco_stmt on the statement
        # - turn the binding that were created into assignment statements
        new_stmts = []
        for stmt in stmts:
            new_stmt = rco_stmt(stmt, bindings)
            new_stmts.append(new_stmt)

        for x, e in bindings.items():
            new_stmts.append(Assign(x, e))

        return new_stmts

    return Program(rco_stmts(prog.stmts))


# Self review: not given empty case after every function

##################################################
# select-instructions
##################################################

# Output language: pseudo-x86
# ATM ::= Immediate(n) | Var(x) | Reg(str)
# instr_name ::= "movq" | "addq"
# Instr ::= NamedInstr(instr_name, [Atm]) | Callq(str) | Retq()
# X86 ::= X86Program(Dict[str, [Instr]])

def select_instructions(prog: Program) -> X86Program:
    """
    Transforms a Lvar program into a pseudo-x86 assembly program.
    :param prog: a Lvar program
    :return: a pseudo-x86 program
    """
    """
    
- si_atm converts an LVar atomic an x86 atomic.
    - Var(x) => x86.Var(x)
    - Constant(n) => x86.Immediate(n)
- si_stmt converts an LVar statements into on eor more x86 instructions. `stmt = statement`
    - Assign(x, Prim('add', [atm1, atm2])) `these are the cases of the match statements`
        - movq si_atm(atm1), %rax
        - addq si_atm(atm2), %rax
        - movq %rax, #var
    - Assign(x, atm1) 
        - movq si_atm(atm1), #x
    - Print(atm1)
        - movq si_atm(atm1), %rdi
        - callq print_int
- si_stmts compiles a list of structures

    """

    # si_atm converts an LVar atomic an x86 atomic.
    def si_atm(atm: Expr) -> x86.Arg:
        if isinstance(atm, Constant):
            return x86.Immediate(atm.val)
        elif isinstance(atm, Var):
            return x86.Var(atm.name)

    # si_stmt converts an LVar statement into one or more x86 instructions.
    def si_stmt(stmt: Stmt) -> List[x86.Instr]:
        if isinstance(stmt, Assign):
            x = stmt.name
            rhs = stmt.rhs
            if isinstance(rhs, Prim) and rhs.op == 'add':
                arg1 = si_atm(rhs.args[0])
                arg2 = si_atm(rhs.args[1])
                return [x86.NamedInstr("movq", [arg1, x86.Reg("%rax")]),
                        x86.NamedInstr("addq", [arg2, x86.Reg("%rax")]),
                        x86.NamedInstr("movq", [x86.Reg("%rax"), x86.Var(x)])]
            else:
                arg1 = si_atm(rhs)
                return [x86.NamedInstr("movq", [arg1, x86.Var(x)])]
        elif isinstance(stmt, Print):
            arg1 = si_atm(stmt.arg)
            return [x86.NamedInstr("movq", [arg1, x86.Reg("%rdi")]),
                    x86.Callq("print_int")]

    # si_stmts compiles a list of statements
    def si_stmts(stmts: List[Stmt]) -> List[x86.Instr]:
        instrs = []
        for stmt in stmts:
            i = si_stmt(stmt)
            instrs.extend(i)
        return instrs

    # Main function to convert an Lvar program into a pseudo-x86 program.
    return x86.X86Program({'main': si_stmts(prog.stmts)})


# self review: just else or empty case of exception not given

##################################################
# assign-homes
##################################################

def assign_homes(program: x86.X86Program) -> x86.X86Program:
    """
    Assigns homes to variables in the input program. Allocates a stack location for each
    variable in the program.
    :param program: A pseudo-x86 program.
    :return: An x86 program, annotated with the amount of stack space used
    """

    """self review: didn't used align function for assign homes"""

    def align(num_bytes: int) -> int:
        if num_bytes % 16 == 0:
            return num_bytes
        else:
            return num_bytes + (16 - (num_bytes % 16))

    homes: Dict[str, x86.Arg] = {}

    def ah_arg(a: x86.Arg, offset=0) -> x86.Arg:
        # should replace variables with their homes
        match a:
            case x86.Immediate(i):
                return a
            case x86.Var(x):
                # here is the thinking part
                # need to replace the var with a Deref
                # return something like this : x86.Deref('rbp', ???)
                # Otherwise create a home for x, add it to "homes", and return it
                if x in homes:
                    return x86.Deref('rbp', homes[x].offset)
                else:
                    homes[x] = x86.Deref('rbp', offset)
                    offset += 8
                    return homes[x]
            case x86.Reg(r):
                return a

    # self-review: Reg case position has to be in between Immediate and Var
    def ah_instr(i: x86.Instr) -> x86.Instr:
        # should call ah_arg on NamedInstr
        match i:
            case x86.NamedInstr(op, args):
                return x86.NamedInstr(op, [ah_arg(a) for a in args])
            case _:
                return i

    def ah_block(instrs: List[x86.Instr]) -> List[x86.Instr]:
        # call ah_instr on each instruction
        return [ah_instr(i) for i in instrs]

    blocks = program.blocks
    new_blocks = {}
    for label, instrs in blocks.items():
        new_blocks[label] = ah_block(instrs)
    return x86.X86Program(new_blocks, stack_space=len(homes) * 8)  # use the len(homes) to determine how much was used


##################################################
# patch-instructions
##################################################


class NameInstr:
    def __init__(self, name: str, operands: list):
        self.name = name
        self.operands = operands


def patch_instructions(program: x86.X86Program) -> x86.X86Program:
    """
    Patches instructions with two memory location inputs, using %rax as a temporary location.
    :param program: An x86 program.
    :return: A patched x86 program.
    """

    # pi_instr compile one instruction, may output two instructions
    def pi_instr(i: x86.Instr) -> list[NameInstr] | list[Instr]:
        match i:
            case NameInstr('movq', [x86.Deref(r1, o1), x86.Deref(r2, o2)]):
                return [
                    NameInstr("movq", [r1, x86.Reg("%rax")]),
                    NameInstr("movq", [(x86.Reg("%rax"), o1), x86.Deref(r2, o2)])
                ]
            case NameInstr('addq', [x86.Deref(r1, o1), x86.Deref(r2, o2)]):
                return [
                    NameInstr("movq", [r1, x86.Reg("%rax")]),
                    NameInstr("addq", [(x86.Reg("%rax"), o1), x86.Deref(r2, o2)])
                ]
            case _:
                return [i]
        # Self-review: used unnecessary x86 instructions which caused errors in pi_instr

    # pi_block compiles one block of the program by calling pi_instr
    def pi_block(instrs: List[x86.Instr]) -> List[x86.Instr]:
        new_instrs = []
        for i in instrs:
            new_instrs.extend(pi_instr(i))
        return new_instrs

    # call pi_block for each block of the program
    new_blocks = {}
    for b in program.blocks:
        new_instrs = pi_block(program.blocks[b])
        new_blocks[b] = new_instrs

    Program.blocks = new_blocks
    return program


##################################################
# prelude-and-conclusion
##################################################
def prelude_and_conclusion(program: x86.X86Program) -> x86.X86Program:
    """
    Adds the prelude and conclusion for the program.
    :param program: An x86 program.
    :return: An x86 program, with prelude and conclusion.
    """
    # self-review: didn't used subq in perlude and in conclude  have to add in popq value to  x86.Retq() also.
    prelude_instructions = [
        NameInstr("pushq", [x86.Reg("%rbp")]),
        NameInstr("movq", [x86.Reg("%rsp"), x86.Reg("%rbp")])
    ]
    conclusion_instructions = [
        NameInstr("movq", [x86.Reg("%rbp"), x86.Reg("%rsp")]),
        NameInstr("popq", [x86.Reg("%rbp")])
    ]

    main_instrs = program.blocks['main']
    new_main_instrs = prelude_instructions + main_instrs + conclusion_instructions
    return x86.X86Program(new_main_instrs, stack_space = program.stack_space)


##################################################
# Compiler definition
##################################################

compiler_passes = {
    'remove complex opera*': rco,
    'select instructions': select_instructions,
    'assign homes': assign_homes,
    'patch instructions': patch_instructions,
    'prelude & conclusion': prelude_and_conclusion,
    'print x86': x86.print_x86
}


def run_compiler(s, logging=False):
    def print_prog(current_program):
        print('Concrete syntax:')
        if isinstance(current_program, x86.X86Program):
            print(x86.print_x86(current_program))
        elif isinstance(current_program, Program):
            print(print_program(current_program))

        print()
        print('Abstract syntax:')
        print(print_ast(current_program))

    current_program = parse(s)

    if logging == True:
        print()
        print('==================================================')
        print(' Input program')
        print('==================================================')
        print()
        print_prog(current_program)

    for pass_name, pass_fn in compiler_passes.items():
        current_program = pass_fn(current_program)

        if logging == True:
            print()
            print('==================================================')
            print(f' Output of pass: {pass_name}')
            print('==================================================')
            print()
            print_prog(current_program)

    return current_program


if __name__ == '__main__':
    if len(sys.argv) != 2:
        print('Usage: python compiler.py <source filename>')
    else:
        file_name = sys.argv[1]
        with open(file_name) as f:
            print(f'Compiling program {file_name}...')

            try:
                program = f.read()
                x86_program = run_compiler(program, logging=True)

                with open(file_name + '.s', 'w') as output_file:
                    output_file.write(x86_program)

            except:
                print('Error during compilation! **************************************************')
                traceback.print_exception(*sys.exc_info())
