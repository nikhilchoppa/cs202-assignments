from typing import Set, Dict
import itertools
import sys
import traceback

from cs202_support.python import *
import cs202_support.x86 as x86
import constants
import cif
from interference_graph import InterferenceGraph

comparisons = ['eq', 'gt', 'gte', 'lt', 'lte']
gensym_num = 0
global_logging = False


def log(label, value):
    if global_logging:
        print()
        print(f'--------------------------------------------------')
        print(f'Logging: {label}')
        print(value)
        print(f'--------------------------------------------------')


def log_ast(label, value):
    log(label, print_ast(value))


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
# typecheck
##################################################
# op    ::= "add" | "sub" | "not" | "or" | "and" | "eq" | "gt" | "gte" | "lt" | "lte"
# Expr  ::= Var(x) | Constant(n) | Prim(op, List[Expr])
# Stmt  ::= Assign(x, Expr) | Print(Expr) | If(Expr, Stmts, Stmts)
# Stmts ::= List[Stmt]
# LVar  ::= Program(Stmts)

TEnv = Dict[str, type]


def typecheck(program: Program) -> Program:
    """
    Typechecks the input program; throws an error if the program is not well-typed.
    :param program: The Lif program to typecheck
    :return: The program, if it is well-typed
    """

    def tc_exp(e: Expr, env: TEnv) -> type:
        match e:
            case Var(x):
                return env[x]
            case Constant(n):
                return type(n)
            case Prim('add', [e1, e2]):
                assert tc_exp(e1, env) == int
                assert tc_exp(e2, env) == int
                return int
            case Prim('eq', [e1, e2]):
                assert tc_exp(e1, env) == tc_exp(e2, env)
                return bool

    def tc_stmt(s: Stmt, env: TEnv):
        # assign (x, Expr) | Print(Expr)| If (Expr, Stmts, Stmts)
        match s:
            case Assign(x, e):
                if x in env:
                    assert env[x] == tc_exp(e, env)
                else:
                    env[x] = tc_exp(e, env)
            case Print(e):
                tc_exp(e, env)
            case If(e1, s1, s2):
                assert tc_exp(e1, env) == bool
                for s in s1:
                    tc_stmt(s, env)
                for s in s2:
                    tc_stmt(s, env)

    def tc_stmts(ss: List[Stmt]):
        env = {}
        for s in ss:
            tc_stmt(s, env)
    tc_stmts(program.stmts)

    return program


##################################################
# remove-complex-opera*
##################################################
# op    ::= "add" | "sub" | "not" | "or" | "and" | "eq" | "gt" | "gte" | "lt" | "lte"
# Expr  ::= Var(x) | Constant(n) | Prim(op, List[Expr])
# Stmt  ::= Assign(x, Expr) | Print(Expr) | If(Expr, Stmts, Stmts)
# Stmts ::= List[Stmt]
# LVar  ::= Program(Stmts)

def rco(prog: Program) -> Program:
    """
    Removes complex operands. After this pass, the arguments to operators (unary and binary
    operators, and function calls like "print") will be atomic.
    :param prog: An Lif program
    :return: An Lif program with atomic operator arguments.
    """

    def rco_stmt(stmt: Stmt, bindings: Dict[str, Expr]) -> Stmt:
            match stmt:
                case Assign(x, e1):
                    new_e1 = rco_exp(e1, bindings)
                    return Assign(x, new_e1)
                case Print(e1):
                    new_e1 = rco_exp(e1, bindings)
                    return Print(new_e1)
                case If(condition, then_stmts, else_stmts):
                    return If(rco_exp(condition,bindings),
                              rco_stmts(then_stmts),
                              rco_stmts(else_stmts))
                case _:
                    raise Exception('rco_stmt', stmt)

    def rco_stmts(stmts: List[Stmt]) -> List[Stmt]:

        new_stmts = []

        for stmt in stmts:
            bindings = {}
            # (1) compile the statement
            new_stmt = rco_stmt(stmt, bindings)
            # (2) add the new bindings created by rco_exp
            new_stmts.extend([Assign(x, e) for x, e in bindings.items()])
            # (3) add the compiled statement itself
            new_stmts.append(new_stmt)

        return new_stmts

    def rco_exp(e: Expr, bindings: Dict[str, Expr]) -> Expr:
        match e:
            case Var(x):
                return Var(x)
            case Constant(i):
                return Constant(i)
            case Prim(op, args):
                new_args = [rco_exp(arg, bindings) for arg in args]
                new_e = Prim(op, new_args)
                new_v = gensym('tmp')
                bindings[new_v] = new_e
                return Var(new_v)
            case _:
                raise Exception('rco_exp', e)

    return Program(rco_stmts(prog.stmts))




##################################################
# explicate-control
##################################################
# op    ::= "add" | "sub" | "not" | "or" | "and" | "eq" | "gt" | "gte" | "lt" | "lte"
# Atm   ::= Var(x) | Constant(n)
# Expr  ::= Atm | Prim(op, List[Expr])
# Stmt  ::= Assign(x, Expr) | Print(Expr) | If(Expr, Stmts, Stmts)
# Stmts ::= List[Stmt]
# LVar  ::= Program(Stmts)

def explicate_pred(prog: Program) -> cif.CProgram:
    """
    Transforms an Lif Expression into a Cif program.
    :param prog: An Lif Expression
    :return: A Cif Program
    """
    basic_blocks: Dict[str, List[cif.Stmt]] = {}

    def create_block(stmts: List[cif.Stmt]) -> str:
        new_label = gensym('label')
        basic_blocks[new_label] = stmts
        return new_label

    def ec_atm(a: Expr) -> cif.Atm:
        match a:
            case Constant(i):
                return cif.Constant(i)
            case Var(i):
                return cif.Var(i)
            case _:
                raise Exception('ec_atm', a)

    def ec_expr(e: Expr) -> cif.Expr:
        match e:
            case Prim(op, args):
                new_args = [ec_atm(a) for a in args]
                return ec_atm(op, new_args)
            case _:
                raise Exception('ec_expr', e)

    def ec_pred(p: Expr, if_label: str, else_label: str) -> cif.Stmt:
        match p:
            case Prim("eq", [lhs, rhs]):
                return cif.If(cif.Prim("eq", [ec_atm(lhs), ec_atm(rhs)]), cif.Goto(if_label), cif.Goto(else_label))
            case Prim("lt", [lhs, rhs]):
                return cif.If(cif.Prim("lt", [ec_atm(lhs), ec_atm(rhs)]), cif.Goto(if_label), cif.Goto(else_label))
            case Prim("gt", [lhs, rhs]):
                return cif.If(cif.Prim("gt", [ec_atm(lhs), ec_atm(rhs)]), cif.Goto(if_label), cif.Goto(else_label))
            case Prim("lte", [lhs, rhs]):
                return cif.If(cif.Prim("lte", [ec_atm(lhs), ec_atm(rhs)]), cif.Goto(if_label), cif.Goto(else_label))
            case Prim("not", [e]):
                return ec_pred(Prim("eq", [e, Constant(0)]), if_label, else_label)
            case _:
                return cif.If(ec_expr(p), cif.Goto(if_label), cif.Goto(else_label))

    def ec_stmt(s: Stmt, cont: List[cif.Stmt]) -> List[cif.Stmt]:
        match s:
            case Assign(x, e):
                return [cif.Assign(x, ec_expr(e))] + cont
            case Print(e):
                return [cif.Print(ec_expr(e))] + cont
            case If(condition, then_stmts, else_stmts):
                then_label = create_block(ec_stmts(then_stmts, cont))
                else_label = create_block(ec_stmts(else_stmts, cont))
                return [ec_pred(condition, then_label, else_label)]
            case _:
                raise Exception('ec_stmt', s)

    def ec_stmts(stmts: List[Stmt], cont: List[cif.Stmt]) -> List[cif.Stmt]:
        for s in reversed(stmts):
            cont = ec_stmt(s, cont)
        return cont

    cont = [cif.Return(0)]
    start_block = create_block(ec_stmts(prog.stmts, cont))
    basic_blocks['start'] = [cif.Goto(start_block)]

    return cif.CProgram(basic_blocks)


##################################################
# select-instructions
##################################################
# op    ::= "add" | "sub" | "not" | "or" | "and" | "eq" | "gt" | "gte" | "lt" | "lte"
# Atm   ::= Var(x) | Constant(n)
# Expr  ::= Atm | Prim(op, List[Expr])
# Stmt  ::= Assign(x, Expr) | Print(Expr)
#        | If(Expr, Goto(label), Goto(label)) | Goto(label) | Return(Expr)
# Stmts ::= List[Stmt]
# Cif   ::= CProgram(Dict[label, Stmts])

def select_instructions(prog: cif.CProgram) -> x86.X86Program:
    def si_atm(a: cif.Expr) -> x86.Arg:
        match a:
            case cif.Constant(i):
                return x86.Immediate(int(i))
            case cif.Var(x):
                return x86.Var(x)
            case _:
                raise Exception('si_atm', a)

    def si_expr(e: cif.Expr) -> x86.Arg:
        match e:
            case cif.Prim(op, args):
                if op in {'add', 'sub', 'and', 'or'}:
                    assert len(args) == 2
                    instr = {'add': 'addq', 'sub': 'subq', 'and': 'andq', 'or': 'orq'}[op]
                    return [si_atm(args[0]), instr, si_atm(args[1])]
                elif op == 'not':
                    assert len(args) == 1
                    return [si_atm(args[0]), 'xorq', x86.Immediate(1)]
                else:
                    raise Exception('si_expr', e)
            case _:
                return si_atm(e)

    def si_stmts(stmts: List[cif.Stmt]) -> List[x86.Instr]:
        instrs = []
        for stmt in stmts:
            instrs.extend(si_stmt(stmt))
        return instrs

    def si_pred(p: cif.Expr, label: str) -> List[cif.x86.Instr]:
        match p:
            case cif.Prim('eq', [lhs, rhs]):
                return [si_atm(lhs), 'cmpq', si_atm(rhs), 'je', label]
            case cif.Prim('lt', [lhs, rhs]):
                return [si_atm(lhs), 'cmpq', si_atm(rhs), 'jl', label]
            case cif.Prim('gt', [lhs, rhs]):
                return [si_atm(lhs), 'cmpq', si_atm(rhs), 'jg', label]
            case cif.Prim('lte', [lhs, rhs]):
                return [si_atm(lhs), 'cmpq', si_atm(rhs), 'jle', label]
            case _:
                raise Exception('si_pred', p)

    def si_stmt(stmt: cif.Stmt) -> List[x86.Instr]:
        match stmt:
            case cif.Assign(x, e):
                return [si_expr(e), x86.NamedInstr('movq', [x86.Reg('rax'), x86.Var(x)])]
            case cif.Print(e):
                return [si_expr(e), x86.NamedInstr('movq', [x86.Reg('rdi'), x86.Var('rax')]), x86.Callq('print_int')]
            case cif.If(p, cif.Goto(label1), cif.Goto(label2)):
                return si_pred(p, label1) + [x86.NamedInstr('jmp', [label2])]
            case cif.Goto(label):
                return [x86.NamedInstr('jmp', [label])]
            case cif.Return(e):
                return [si_expr(e), x86.NamedInstr('jmp', ['conclusion'])]
            case _:
                raise Exception('si_stmt', stmt)

    x86_blocks = {}
    for label in prog.blocks:
        instrs = si_stmts(prog.blocks[label])
        x86_blocks[label] = instrs

    return x86.X86Program(x86_blocks)

##################################################
# allocate-registers
##################################################
# Arg    ::= Immediate(i) | Reg(r) | ByteReg(r) | Var(x) | Deref(r, offset)
# op     ::= 'addq' | 'cmpq' | 'andq' | 'orq' | 'xorq' | 'movq' | 'movzbq'
# cc     ::= 'e'| 'g' | 'ge' | 'l' | 'le'
# Instr  ::= NamedInstr(op, List[Arg]) | Callq(label) | Retq()
#         | Jmp(label) | JmpIf(cc, label) | Set(cc, Arg)
# Blocks ::= Dict[label, List[Instr]]
# X86    ::= X86Program(Blocks)

Color = int
Coloring = Dict[x86.Var, Color]
Saturation = Set[Color]

def allocate_registers(program: x86.X86Program) -> x86.X86Program:
    """
    Assigns homes to variables in the input program. Allocates registers and
    stack locations as needed, based on a graph-coloring register allocation
    algorithm.
    :param program: A pseudo-x86 program.
    :return: An x86 program, annotated with the number of bytes needed in stack
    locations.
    """

    all_vars: Set[x86.Var] = set()
    live_after_sets: Dict[str, List[Set[x86.Var]]] = {}
    live_before_sets: Dict[str, Set[x86.Var]] = {}

    # --------------------------------------------------
    # utilities
    # --------------------------------------------------
    def vars_arg(a: x86.Arg) -> Set[x86.Var]:
        match a:
            case x86.Immediate(i):
                return set()
            case x86.Reg(r):
                return set()
            case x86.Var(x):
                all_vars.add(a)
                return {a}
            case _:
                raise Exception('ul_arg', a)

    def reads_of(i: x86.Instr) -> Set[x86.Var]:
        match i:
            case x86.NamedInstr('movq', [e1, e2]):
                return vars_arg(e1)
            case x86.NamedInstr('addq', [e1, e2]):
                return vars_arg(e1).union(vars_arg(e2))
            case x86.Jmp(label) | x86.JmpIf(label):
                # what gets read by a jmp? everything in the destination's live-before set
                if label in live_before_sets:
                    return live_before_sets[label]
                else:
                    # go compute the live-before set, and save it in live_before_sets
                    ul_block(label)
                    return live_before_sets[label]
            case _:
                return set()

    def writes_of(i: x86.Instr) -> Set[x86.Var]:
        match i:
            case x86.NamedInstr('movq', [e1, e2]):
                return vars_arg(e2)
            case x86.NamedInstr('addq', [e1, e2]):
                return vars_arg(e2)
            case _:
                return set()

    # --------------------------------------------------
    # liveness analysis
    # --------------------------------------------------
    def ul_instr(i: x86.Instr, live_after: Set[x86.Var]) -> Set[x86.Var]:
        return live_after.difference(writes_of(i)).union(reads_of(i))

    # TODO: change this so that it takes a label, and fetches the instructions
    # for that label from prog.blocks
    # save the live-after sets in the global dict
    # save the live-before set in the global dict
    def ul_block(instrs: List[x86.Instr]) -> List[Set[x86.Var]]:
        current_live_after: Set[x86.Var] = set()

        live_after_sets = []
        for i in reversed(instrs):
            live_after_sets.append(current_live_after)
            current_live_after = ul_instr(i, current_live_after)

        return list(reversed(live_after_sets))

        # --------------------------------------------------
        # interference graph
        # --------------------------------------------------

    def bi_instr(e: x86.Instr, live_after: Set[x86.Var], graph: InterferenceGraph):
        for v1 in writes_of(e):
            for v2 in live_after:
                graph.add_edge(v1, v2)

    def bi_block(instrs: List[x86.Instr], live_afters: List[Set[x86.Var]], graph: InterferenceGraph):
        for instr, live_after in zip(instrs, live_afters):
            bi_instr(instr, live_after, graph)

        # --------------------------------------------------
        # graph coloring
        # --------------------------------------------------

    def color_graph(local_vars: Set[x86.Var], interference_graph: InterferenceGraph) -> Coloring:
        coloring: Coloring = {}

        to_color = local_vars.copy()

        # Saturation sets start out empty
        saturation_sets = {x: set() for x in local_vars}

        # Loop until we are finished coloring
        while to_color:
            # Find the variable x with the largest saturation set
            x = max(to_color, key=lambda x: len(saturation_sets[x]))

            # Remove x from the variables to color
            to_color.remove(x)

            # Find the smallest color not in x's saturation set
            x_color = next(i for i in itertools.count() if i not in saturation_sets[x])

            # Assign x's color
            coloring[x] = x_color

            # Add x's color to the saturation sets of its neighbors
            for y in interference_graph.neighbors(x):
                saturation_sets[y].add(x_color)

        return coloring

        # --------------------------------------------------
        # assigning homes
        # --------------------------------------------------

    def align(num_bytes: int) -> int:
        if num_bytes % 16 == 0:
            return num_bytes
        else:
            return num_bytes + (16 - (num_bytes % 16))

    homes: Dict[str, x86.Arg] = {}

    def ah_arg(a: x86.Arg) -> x86.Arg:
        match a:
            case x86.Immediate(i):
                return a
            case x86.Reg(r):
                return a
            case x86.Var(x):
                return homes[a]
            case _:
                raise Exception('ah_arg', a)

    def ah_instr(e: x86.Instr) -> x86.Instr:
        match e:
            case x86.NamedInstr(i, args):
                return x86.NamedInstr(i, [ah_arg(a) for a in args])
            case _:
                if isinstance(e, (x86.Callq, x86.Retq, x86.Jmp)):
                    return e
                else:
                    raise Exception('ah_instr', e)

    def ah_block(instrs: List[x86.Instr]) -> List[x86.Instr]:
        return [ah_instr(i) for i in instrs]

        # --------------------------------------------------
        # main body of the pass
        # --------------------------------------------------

        # Step 1: Perform liveness analysis

    blocks = program.blocks
    # live_after_sets = {label: ul_block(block) for label, block in blocks.items()}
    ul_block('start')
    log_ast('live-after sets', live_after_sets)

    # Step 2: Build the interference graph
    interference_graph = InterferenceGraph()

    for label in blocks.keys():
        bi_block(blocks[label], live_after_sets[label], interference_graph)

    log_ast('interference graph', interference_graph)

    # Step 3: Color the graph
    coloring = color_graph(all_vars, interference_graph)
    colors_used = set(coloring.values())
    log('coloring', coloring)

    # Defines the set of registers to use
    available_registers = constants.caller_saved_registers + constants.callee_saved_registers

    # Step 4: map variables to homes
    color_map = {}
    stack_locations_used = 0

    # Step 4.1: Map colors to locations (the "color map")
    for color in sorted(colors_used):
        if available_registers != []:
            r = available_registers.pop()
            color_map[color] = x86.Reg(r)
        else:
            offset = stack_locations_used + 1
            color_map[color] = x86.Deref('rbp', -(offset * 8))
            stack_locations_used += 1

    # Step 4.2: Compose the "coloring" with the "color map" to get "homes"
    for v in all_vars:
        homes[v] = color_map[coloring[v]]
    log('homes', homes)

    # Step 5: replace variables with their homes
    blocks = program.blocks
    new_blocks = {label: ah_block(block) for label, block in blocks.items()}
    return x86.X86Program(new_blocks, stack_space=align(8 * stack_locations_used))


##################################################
# patch-instructions
##################################################
# Arg    ::= Immediate(i) | Reg(r) | ByteReg(r) | Deref(r, offset)
# op     ::= 'addq' | 'cmpq' | 'andq' | 'orq' | 'xorq' | 'movq' | 'movzbq'
# cc     ::= 'e'| 'g' | 'ge' | 'l' | 'le'
# Instr  ::= NamedInstr(op, List[Arg]) | Callq(label) | Retq()
#         | Jmp(label) | JmpIf(cc, label) | Set(cc, Arg)
# Blocks ::= Dict[label, List[Instr]]
# X86    ::= X86Program(Blocks)

def patch_instructions(program: x86.X86Program) -> x86.X86Program:
    """
    Patches instructions with two memory location inputs, using %rax as a temporary location.
    :param program: An x86 program.
    :return: A patched x86 program.
    """

    pass


##################################################
# prelude-and-conclusion
##################################################
# Arg    ::= Immediate(i) | Reg(r) | ByteReg(r) | Deref(r, offset)
# op     ::= 'addq' | 'cmpq' | 'andq' | 'orq' | 'xorq' | 'movq' | 'movzbq'
# cc     ::= 'e'| 'g' | 'ge' | 'l' | 'le'
# Instr  ::= NamedInstr(op, List[Arg]) | Callq(label) | Retq()
#         | Jmp(label) | JmpIf(cc, label) | Set(cc, Arg)
# Blocks ::= Dict[label, List[Instr]]
# X86    ::= X86Program(Blocks)

def prelude_and_conclusion(program: x86.X86Program) -> x86.X86Program:
    """
    Adds the prelude and conclusion for the program.
    :param program: An x86 program.
    :return: An x86 program, with prelude and conclusion.
    """

    pass


##################################################
# Compiler definition
##################################################

compiler_passes = {
    'typecheck': typecheck,
    'remove complex opera*': rco,
    'explicate control': explicate_pred,
    'select instructions': select_instructions,
    'allocate registers': allocate_registers,
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
        elif isinstance(current_program, cif.CProgram):
            print(cif.print_program(current_program))

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
                print('Error during compilation! ******************')
                traceback.print_exception(*sys.exc_info())