from typing import Set, Dict, Tuple
import sys
import traceback
from dataclasses import dataclass

from cs202_support.python import *
import cs202_support.x86 as x86
import constants
import cfun
import print_x86defs
from interference_graph import InterferenceGraph

comparisons = ['eq', 'gt', 'gte', 'lt', 'lte']
gensym_num = 0
global_logging = False

global_values = ['free_ptr', 'fromspace_end']

tuple_var_types = {}
function_names = set()


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
# op     ::= "add" | "sub" | "mult" | "not" | "or" | "and" | "eq" | "gt" | "gte" | "lt" | "lte"
#          | "tuple" | "subscript"
# Expr   ::= Var(x) | Constant(n) | Prim(op, List[Expr]) | Begin(Stmts, Expr)
#          | Call(Expr, List[Expr])
# Stmt   ::= Assign(x, Expr) | Print(Expr) | If(Expr, Stmts, Stmts) | While(Expr, Stmts)
#          | Return(Expr) | FunctionDef(str, List[Tuple[str, type]], List[Stmt], type)
# Stmts  ::= List[Stmt]
# LFun   ::= Program(Stmts)

@dataclass
class Callable:
    args: List[type]
    output_type: type


TEnv = Dict[str, Callable | Tuple | type]


# Two new cases
# 1. FunctionDef(name, params, body_stmts, return types)
# 2. Return(e)
# 3. Call(func, args)
def typecheck(program: Program) -> Program:
    """
    Typechecks the input program; throws an error if the program is not well-typed.
    :param program: The Ltup program to typecheck
    :return: The program, if it is well-typed
    """

    prim_arg_types = {
        'add': [int, int],
        'sub': [int, int],
        'mult': [int, int],
        'not': [bool],
        'or': [bool, bool],
        'and': [bool, bool],
        'gt': [int, int],
        'gte': [int, int],
        'lt': [int, int],
        'lte': [int, int],
    }

    prim_output_types = {
        'add': int,
        'sub': int,
        'mult': int,
        'not': bool,
        'or': bool,
        'and': bool,
        'gt': bool,
        'gte': bool,
        'lt': bool,
        'lte': bool,
    }

    def tc_exp(e: Expr, env: TEnv) -> type:
        match e:
            case Call(func, args):
                # Treated like prim... run the arg types through the type checker and put them in a list
                arg_types = [tc_exp(a, env) for a in args]
                # Run the function through tc_exp, since this should already be stored in the enviorment, this should
                # always be type callable
                callable_func = tc_exp(func, env)
                assert arg_types == callable_func.args
                return callable_func.output_type  # Should be the callables return type
            case Var(x):
                if x in global_values:
                    return int
                else:
                    return env[x]
            case Constant(i):
                if isinstance(i, bool):
                    return bool
                elif isinstance(i, int):
                    return int
                else:
                    raise Exception('tc_exp', e)
            case Prim('tuple', args):
                arg_types = [tc_exp(a, env) for a in args]
                t = tuple(arg_types)
                return t
            case Prim('subscript', [e1, Constant(i)]):
                t = tc_exp(e1, env)
                assert isinstance(t, tuple)
                return t[i]
            case Prim('eq', [e1, e2]):
                assert tc_exp(e1, env) == tc_exp(e2, env)
                return bool
            case Prim(op, args):
                arg_types = [tc_exp(a, env) for a in args]
                assert arg_types == prim_arg_types[op]
                return prim_output_types[op]
            case Begin(stmts, e):
                tc_stmts(stmts, env)
                return tc_exp(e, env)
            case _:
                raise Exception('tc_exp', e)

    def tc_stmt(s: Stmt, env: TEnv):
        match s:
            case FunctionDef(name, params, body_stmts, ret_type):
                # Collect parameter types
                param_types = []
                for p in params:
                    param_types.append(p[1])  # The type is always the second parameter
                env[name] = Callable(param_types, ret_type)

                # Create a copy of env to add our parameter types to
                new_env = env.copy()
                new_env['retvalue'] = ret_type

                # Update the temp enviorment with the parameter names and types
                for p in params:
                    new_env[p[0]] = p[1]

                # Now that the parameter names and types are in our enviorment, should be good to type check the function body
                tc_stmts(body_stmts, new_env)
                for e in new_env:
                    if isinstance(new_env[e], tuple):
                        tuple_var_types[e] = new_env[e]
                function_names.add(
                    name)  # Hopefully this is the right function, adds the name of the function to function_names
            case Return(e):
                assert tc_exp(e, env) == env[
                    'retvalue']  # but retvalue is stored in new_env?... Return will only be found in the body statement of a function!
            case While(condition, body_stmts):
                assert tc_exp(condition, env) == bool
                tc_stmts(body_stmts, env)
            case If(condition, then_stmts, else_stmts):
                assert tc_exp(condition, env) == bool
                tc_stmts(then_stmts, env)
                tc_stmts(else_stmts, env)
            case Print(e):
                tc_exp(e, env)
            case Assign(x, e):
                t_e = tc_exp(e, env)
                if x in env:
                    assert t_e == env[x]
                else:
                    env[x] = t_e
            case _:
                raise Exception('tc_stmt', s)

    def tc_stmts(stmts: List[Stmt], env: TEnv):
        for s in stmts:
            tc_stmt(s, env)

    env = {}
    tc_stmts(program.stmts, env)
    for x in env:
        if isinstance(env[x], tuple):
            tuple_var_types[x] = env[x]
    return program


##################################################
# remove-complex-opera*
##################################################
# op     ::= "add" | "sub" | "mult" | "not" | "or" | "and" | "eq" | "gt" | "gte" | "lt" | "lte"
#          | "tuple" | "subscript"
# Expr   ::= Var(x) | Constant(n) | Prim(op, List[Expr])
#          | Call(Expr, List[Expr])
# Stmt   ::= Assign(x, Expr) | Print(Expr) | If(Expr, Stmts, Stmts) | While(Expr, Stmts)
#          | Return(Expr) | FunctionDef(str, List[Tuple[str, type]], List[Stmt], type)
# Stmts  ::= List[Stmt]
# LFun   ::= Program(Stmts)

def rco(prog: Program) -> Program:
    """
    Removes complex operands. After this pass, the arguments to operators (unary and binary
    operators, and function calls like "print") will be atomic.
    :param prog: An Ltup program
    :return: An Ltup program with atomic operator arguments.
    """

    def rco_stmt(stmt: Stmt, bindings: Dict[str, Expr]) -> Stmt:
        match stmt:
            case FunctionDef(name, params, body_stmts, ret_type):
                return FunctionDef(name, params, rco_stmts(body_stmts), ret_type)
            case Return(e):
                return Return(rco_exp(e, bindings))
            case Assign(x, e1):
                new_e1 = rco_exp(e1, bindings)
                return Assign(x, new_e1)
            case Print(e1):
                new_e1 = rco_exp(e1, bindings)
                return Print(new_e1)
            case While(condition, body_stmts):
                condition_bindings = {}
                condition_exp = rco_exp(condition, condition_bindings)
                condition_stmts = [Assign(x, e) for x, e in condition_bindings.items()]
                new_condition = Begin(condition_stmts, condition_exp)

                new_body_stmts = rco_stmts(body_stmts)
                return While(new_condition, new_body_stmts)

            case If(condition, then_stmts, else_stmts):
                new_condition = rco_exp(condition, bindings)
                new_then_stmts = rco_stmts(then_stmts)
                new_else_stmts = rco_stmts(else_stmts)

                return If(new_condition,
                          new_then_stmts,
                          new_else_stmts)
            case _:
                raise Exception('rco_stmt', stmt)

    def rco_stmts(stmts: List[Stmt]) -> List[Stmt]:
        new_stmts = []

        for stmt in stmts:
            print(stmt)
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
            case Call(func, args):
                # Generate atomic arguments to the function
                new_args = [rco_exp(a, bindings) for a in args]

                # Run the function through rco_exp, this will get us the tmp var to assign the function to
                new_f = rco_exp(func, bindings)

                # Create a binding to the variable which holds the function with a tmp var
                bindings[new_f.name] = func

                # Generate the new call expression and bind it. This should be using the new function and new args
                new_e = Call(new_f, new_args)
                new_v = gensym('tmp')
                bindings[new_v] = new_e

                # Need to assign a variable to the function definition, if we have not done so already
                # Would that be found in bindings?
                return Var(new_v)
            case Var(x):
                # Double check the function isn't already bound?
                if x in function_names:
                    new_v = gensym('tmp')
                    return Var(new_v)
                return Var(x)
            case Constant(i):
                return Constant(i)
            case Prim(op, args):
                new_args = [rco_exp(e, bindings) for e in args]
                new_e = Prim(op, new_args)
                new_v = gensym('tmp')
                bindings[new_v] = new_e
                return Var(new_v)
            case _:
                raise Exception('rco_exp', e)

    return Program(rco_stmts(prog.stmts))


##################################################
# expose-allocation
##################################################
# op     ::= "add" | "sub" | "mult" | "not" | "or" | "and" | "eq" | "gt" | "gte" | "lt" | "lte"
#          | "tuple" | "subscript"
# Expr   ::= Var(x) | Constant(n) | Prim(op, List[Expr])
#          | Call(Expr, List[Expr])
# Stmt   ::= Assign(x, Expr) | Print(Expr) | If(Expr, Stmts, Stmts) | While(Begin(Stmts, Expr), Stmts)
#          | Return(Expr) | FunctionDef(str, List[Tuple[str, type]], List[Stmt], type)
# Stmts  ::= List[Stmt]
# LFun   ::= Program(Stmts)

def expose_alloc(prog: Program) -> Program:
    """
    Exposes allocations in an Ltup program. Replaces tuple(...) with explicit
    allocation.
    :param prog: An Ltup program
    :return: An Ltup program, without Tuple constructors
    """

    def mk_tag(types: Tuple[type]) -> int:
        """
        Builds a vector tag. See section 5.2.2 in the textbook.
        :param types: A list of the types of the vector's elements.
        :return: A vector tag, as an integer.
        """
        pointer_mask = 0
        # for each type in the vector, encode it in the pointer mask
        for t in reversed(types):
            # shift the mask by 1 bit to make room for this type
            pointer_mask = pointer_mask << 1

            if isinstance(t, tuple):
                # if it's a vector type, the mask is 1
                pointer_mask = pointer_mask + 1
            else:
                # otherwise, the mask is 0 (do nothing)
                pass

        # shift the pointer mask by 6 bits to make room for the length field
        mask_and_len = pointer_mask << 6
        mask_and_len = mask_and_len + len(types)  # add the length

        # shift the mask and length by 1 bit to make room for the forwarding bit
        tag = mask_and_len << 1
        tag = tag + 1

        return tag

    def ea_stmt(stmt: Stmt) -> List[Stmt]:
        match stmt:
            case FunctionDef(name, params, body_stmts, ret_type):
                return [FunctionDef(name, params, ea_stmts(body_stmts), ret_type)]
            case If(cond, then_stmts, else_stmts):
                return [If(cond, ea_stmts(then_stmts), ea_stmts(else_stmts))]
            case While(Begin(s1, cond), s2):
                return [While(Begin(ea_stmts(s1), cond), ea_stmts(s2))]
            case Assign(x, Prim('tuple', args)):
                new_stmts = []
                num_bytes = 8 * (len(args) + 1)
                new_fp = gensym('tmp')
                lt_var = gensym('tmp')
                tag = mk_tag(tuple_var_types[x])
                new_stmts += [
                    Assign(new_fp, Prim('add', [Var('free_ptr'), Constant(num_bytes)])),
                    Assign(lt_var, Prim('lt', [Var(new_fp), Var('fromspace_end')])),
                    If(Var(lt_var),
                       [],
                       [Assign('_', Prim('collect', [Constant(num_bytes)]))]),
                    Assign(x, Prim('allocate', [Constant(num_bytes), Constant(tag)]))]

                # fill in the values of the tuple
                for i, a in enumerate(args):
                    new_stmts.append(Assign('_', Prim('tuple_set', [Var(x), Constant(i), a])))
                return new_stmts
            case _:
                return [stmt]

    def ea_stmts(stmts: List[Stmt]) -> List[Stmt]:
        new_stmts = []
        for s in stmts:
            new_stmts.extend(ea_stmt(s))
        return new_stmts

    return Program(ea_stmts(prog.stmts))


##################################################
# explicate-control
##################################################
# op     ::= "add" | "sub" | "mult" | "not" | "or" | "and" | "eq" | "gt" | "gte" | "lt" | "lte"
#          | "subscript" | "allocate" | "collect" | "tuple_set"
# Atm    ::= Var(x) | Constant(n)
# Expr   ::= Atm | Prim(op, List[Expr])
#          | Call(Expr, List[Expr])
# Stmt   ::= Assign(x, Expr) | Print(Expr) | If(Expr, Stmts, Stmts) | While(Begin(Stmts, Expr), Stmts)
#          | Return(Expr) | FunctionDef(str, List[Tuple[str, type]], List[Stmt], type)
# Stmts  ::= List[Stmt]
# LFun   ::= Program(Stmts)

def explicate_control(prog: Program) -> cfun.CProgram:
    """
    Transforms a Ltup Expression into a Ctup program.
    :param prog: A Ltup Expression
    :return: A Ctup Program
    """

    # the basic blocks of the program
    basic_blocks: Dict[str, List[cfun.Stmt]] = {}
    functions: List[cfun.CFunctionDef] = []
    current_function = 'main'

    # create a new basic block to hold some statements
    # generates a brand-new name for the block and returns it
    def create_block(stmts: List[cfun.Stmt]) -> str:
        # Add function name as a prefix to the label
        label = current_function + gensym('label')
        basic_blocks[label] = stmts
        return label

    def explicate_atm(e: Expr) -> cfun.Atm:
        match e:
            case Var(x):
                return cfun.Var(x)
            case Constant(c):
                return cfun.Constant(c)
            case _:
                raise RuntimeError(e)

    def explicate_exp(e: Expr) -> cfun.Expr:
        match e:
            case Call(func, args):
                new_args = [explicate_atm(a) for a in args]
                return cfun.Call(explicate_atm(func), new_args)
            case Prim(op, args):
                new_args = [explicate_atm(a) for a in args]
                return cfun.Prim(op, new_args)
            case _:
                return explicate_atm(e)

    def ec_function(name: str, params: List[Tuple[str, type]],
                    body_stmts: List[Stmt], return_type: type) -> cfun.CFunctionDef:
        # Save basic blocks and current function so they can be restored at the end
        # Nonlocal looks to outside the function scope instead of the global script scope
        nonlocal basic_blocks
        nonlocal current_function
        old_basic_blocks = basic_blocks
        old_current_function = current_function
        basic_blocks = {}
        current_function = name

        # Call ec_stmts on body statments with the continuation Return(0)
        # but the continuation should only be Return(0) for main?

        new_bod = explicate_stmts(body_stmts, [cfun.Return(cfun.Constant(0))])


        # Set basic_blocks[name+'start'] to the result
        basic_blocks[name + 'start'] = new_bod

        # Construct new FunctionDef and append it to functions
        # Second param is args, a list of strings but params is type List[tuple[str, type]]
        # So we have to deconstruct this, start by looping through each param which is a tuple
        # and only grab the first item which is the string
        new_params = [t[0] for t in params]
        new_func = cfun.CFunctionDef(name, new_params, basic_blocks)
        functions.append(new_func)

        # Restore basic blocks and current_function
        basic_blocks = old_basic_blocks
        current_function = old_current_function

        return new_func

    def explicate_stmt(stmt: Stmt, cont: List[cfun.Stmt]) -> List[cfun.Stmt]:
        match stmt:
            case Return(e):
                # New case alert!
                new_stmt: List[cfun.Stmt] = [cfun.Return(explicate_atm(e))]
                return new_stmt + cont
            case FunctionDef(name, params, body_stmts, return_type):
                ec_function(name, params, body_stmts, return_type)
                return cont
            case Assign(x, exp):
                new_exp = explicate_exp(exp)
                new_stmt: List[cfun.Stmt] = [cfun.Assign(x, new_exp)]
                return new_stmt + cont
            case Print(exp):
                new_exp = explicate_atm(exp)
                new_stmt: List[cfun.Stmt] = [cfun.Print(new_exp)]
                return new_stmt + cont
            case While(Begin(condition_stmts, condition_exp), body_stmts):
                cont_label = create_block(cont)
                test_label = gensym('current_function'+'loop_label')
                body_label = create_block(explicate_stmts(body_stmts, [cfun.Goto(test_label)]))
                test_stmts = [cfun.If(explicate_exp(condition_exp),
                                      cfun.Goto(body_label),
                                      cfun.Goto(cont_label))]
                basic_blocks[test_label] = explicate_stmts(condition_stmts, test_stmts)
                return [cfun.Goto(test_label)]
            case If(condition, then_stmts, else_stmts):
                cont_label = create_block(cont)
                e2_label = create_block(explicate_stmts(then_stmts, [cfun.Goto(cont_label)]))
                e3_label = create_block(explicate_stmts(else_stmts, [cfun.Goto(cont_label)]))
                return [cfun.If(explicate_exp(condition),
                                cfun.Goto(e2_label),
                                cfun.Goto(e3_label))]

            case _:
                raise RuntimeError(stmt)

    def explicate_stmts(stmts: List[Stmt], cont: List[cfun.Stmt]) -> List[cfun.Stmt]:
        for s in reversed(stmts):
            cont = explicate_stmt(s, cont)
        return cont

    new_body = [cfun.Return(cfun.Constant(0))]
    new_body = explicate_stmts(prog.stmts, new_body)
    basic_blocks['mainstart'] = new_body
    functions.append(cfun.CFunctionDef('main', [], basic_blocks))

    return cfun.CProgram(functions)


##################################################
# select-instructions
##################################################
# op           ::= "add" | "sub" | "mult" | "not" | "or" | "and" | "eq" | "gt" | "gte" | "lt" | "lte"
#                | "subscript" | "allocate" | "collect" | "tuple_set"
# Atm          ::= Var(x) | Constant(n)
# Expr         ::= Atm | Prim(op, List[Expr])
# Stmt         ::= Assign(x, Expr) | Print(Expr)
#                | If(Expr, Goto(label), Goto(label)) | Goto(label) | Return(Expr)
# Stmts        ::= List[Stmt]
# CFunctionDef ::= CFunctionDef(name, List[str], Dict[label, Stmts])
# Cfun         ::= CProgram(List[CFunctionDef])

@dataclass(frozen=True, eq=True)
class X86FunctionDef(AST):
    label: str
    blocks: Dict[str, List[x86.Instr]]
    stack_space: Tuple[int, int]


@dataclass(frozen=True, eq=True)
class X86ProgramDefs(AST):
    defs: List[X86FunctionDef]


def select_instructions(prog: cfun.CProgram) -> X86ProgramDefs:
    """
    Transforms a Ltup program into a pseudo-x86 assembly program.
    :param prog: a Ltup program
    :return: a pseudo-x86 program
    """

    current_function = 'main'

    def si_atm(a: cfun.Expr) -> x86.Arg:
        match a:
            case cfun.Constant(i):
                return x86.Immediate(int(i))
            case cfun.Var(x):
                if x in global_values:
                    return x86.GlobalVal(x)
                else:
                    return x86.Var(x)
            case _:
                raise Exception('si_atm', a)

    def si_stmts(stmts: List[cfun.Stmt]) -> List[x86.Instr]:
        instrs = []

        for stmt in stmts:
            instrs.extend(si_stmt(stmt))

        return instrs

    op_cc = {'eq': 'e', 'gt': 'g', 'gte': 'ge', 'lt': 'l', 'lte': 'le'}

    binop_instrs = {'add': 'addq', 'sub': 'subq', 'mult': 'imulq', 'and': 'andq', 'or': 'orq'}

    def si_stmt(stmt: cfun.Stmt) -> List[x86.Instr]:
        match stmt:
            case cfun.Assign(x, cfun.Call(fun, args)):
                instrs = []
                # Move args into parameter registers
                # Hopefully never more than 5 arguments lol
                for a, r in zip(args, constants.argument_registers):
                    # There is a chance this could be something other than immediate
                    instrs.append(x86.NamedInstr('movq', [x86.Immediate(a.val), x86.Reg(r)]))

                instrs.append(x86.IndirectCallq(si_atm(fun), 0))
                instrs.append(x86.NamedInstr('movq', [x86.Reg('rax'), x86.Var(x)]))
                return instrs
            case cfun.Assign(x, cfun.Var(f)):
                if f in function_names:
                    return [x86.NamedInstr('leaq', [x86.GlobalVal(f), x86.Var(x)])]

                # hmmmmmmmmmmmmm
                # This would make si_atm pretty much obsolete
                return [x86.NamedInstr('movq', [si_atm(cfun.Var(f)), x86.Var(x)])]
            case cfun.Assign(x, cfun.Prim('allocate', [cfun.Constant(num_bytes), cfun.Constant(tag)])):
                return [x86.NamedInstr('movq', [x86.GlobalVal('free_ptr'), x86.Var(x)]),
                        x86.NamedInstr('addq', [x86.Immediate(num_bytes), x86.GlobalVal('free_ptr')]),
                        x86.NamedInstr('movq', [x86.Var(x), x86.Reg('r11')]),
                        x86.NamedInstr('movq', [x86.Immediate(tag), x86.Deref('r11', 0)])]
            case cfun.Assign(_, cfun.Prim('tuple_set', [cfun.Var(x), cfun.Constant(offset), atm1])):
                offset_bytes = 8 * (offset + 1)
                return [x86.NamedInstr('movq', [x86.Var(x), x86.Reg('r11')]),
                        x86.NamedInstr('movq', [si_atm(atm1), x86.Deref('r11', offset_bytes)])]
            case cfun.Assign(x, cfun.Prim('subscript', [atm1, cfun.Constant(offset)])):
                offset_bytes = 8 * (offset + 1)
                return [x86.NamedInstr('movq', [si_atm(atm1), x86.Reg('r11')]),
                        x86.NamedInstr('movq', [x86.Deref('r11', offset_bytes), x86.Var(x)])]
            case cfun.Assign(_, cfun.Prim('collect', [cfun.Constant(num_bytes)])):
                return [x86.NamedInstr('movq', [x86.Reg('r15'), x86.Reg('rdi')]),
                        x86.NamedInstr('movq', [x86.Immediate(num_bytes), x86.Reg('rsi')]),
                        x86.Callq('collect')]
            case cfun.Assign(x, cfun.Prim(op, [atm1, atm2])):
                if op in binop_instrs:
                    return [x86.NamedInstr('movq', [si_atm(atm1), x86.Reg('rax')]),
                            x86.NamedInstr(binop_instrs[op], [si_atm(atm2), x86.Reg('rax')]),
                            x86.NamedInstr('movq', [x86.Reg('rax'), x86.Var(x)])]
                elif op in op_cc:
                    return [x86.NamedInstr('cmpq', [si_atm(atm2), si_atm(atm1)]),
                            x86.Set(op_cc[op], x86.ByteReg('al')),
                            x86.NamedInstr('movzbq', [x86.ByteReg('al'), x86.Var(x)])]
                else:
                    raise Exception('si_stmt failed op', op)
            case cfun.Assign(x, cfun.Prim('not', [atm1])):
                return [x86.NamedInstr('movq', [si_atm(atm1), x86.Var(x)]),
                        x86.NamedInstr('xorq', [x86.Immediate(1), x86.Var(x)])]
            case cfun.Assign(x, atm1):
                return [x86.NamedInstr('movq', [si_atm(atm1), x86.Var(x)])]
            case cfun.Print(atm1):
                return [x86.NamedInstr('movq', [si_atm(atm1), x86.Reg('rdi')]),
                        x86.Callq('print_int')]
            case cfun.Return(atm1):
                return [x86.NamedInstr('movq', [si_atm(atm1), x86.Reg('rax')]),
                        x86.Jmp(current_function + 'conclusion')]
            case cfun.Goto(label):
                return [x86.Jmp(label)]
            case cfun.If(a, cfun.Goto(then_label), cfun.Goto(else_label)):
                return [x86.NamedInstr('cmpq', [si_atm(a), x86.Immediate(1)]),
                        x86.JmpIf('e', then_label),
                        x86.Jmp(else_label)]
            case _:
                raise Exception('si_stmt', stmt)

    def si_def(d: cfun.CFunctionDef) -> X86FunctionDef:
        # Set the current function
        nonlocal current_function
        current_function = d.name
        new_blocks = {}

        # Call si_stmts on the statements of each block
        for b in d.blocks:
            new_stmts = []

            if 'start' in b:
                for a, r in zip(d.args, constants.argument_registers):
                    new_stmts.append(x86.NamedInstr('movq', [x86.Reg(r), x86.Var(a)]))

            new_stmts.extend(si_stmts(d.blocks[b]))
            new_blocks[b] = new_stmts

        print(new_blocks)

        return X86FunctionDef(current_function, new_blocks, (None, None))

    functions = []
    for d in prog.defs:
        functions.append(si_def(d))

    return X86ProgramDefs(functions)


##################################################
# allocate-registers
##################################################
# Arg            ::= Immediate(i) | Reg(r) | ByteReg(r) | Var(x) | Deref(r, offset) | GlobalVal(x)
# op             ::= 'addq' | 'subq' | 'imulq' | 'cmpq' | 'andq' | 'orq' | 'xorq' | 'movq' | 'movzbq'
#                  | 'leaq'
# cc             ::= 'e'| 'g' | 'ge' | 'l' | 'le'
# Instr          ::= NamedInstr(op, List[Arg]) | Callq(label) | Retq()
#                  | Jmp(label) | JmpIf(cc, label) | Set(cc, Arg)
#                  | IndirectCallq(Arg)
# Blocks         ::= Dict[label, List[Instr]]
# X86FunctionDef ::= X86FunctionDef(name, Blocks)
# X86ProgramDefs ::= List[X86FunctionDef]

Color = x86.Arg
Coloring = Dict[x86.Var, x86.Arg]
Saturation = Set[x86.Arg]


def allocate_registers(program: X86ProgramDefs) -> X86ProgramDefs:
    """
    Assigns homes to variables in the input program. Allocates registers and
    stack locations as needed, based on a graph-coloring register allocation
    algorithm.
    :param program: A pseudo-x86 program.
    :return: An x86 program, annotated with the number of bytes needed in stack
    locations.
    """

    new_defs = []
    for d in program.defs:
        main_prog = x86.X86Program(d.blocks, None)
        result_mini_program = _allocate_registers(d.label, main_prog)
        new_def = X86FunctionDef(d.label, result_mini_program.blocks, result_mini_program.stack_space)
        new_defs.append(new_def)

    return X86ProgramDefs(new_defs)


def _allocate_registers(name: str, program: x86.X86Program) -> x86.X86Program:
    blocks = program.blocks
    all_vars: Set[x86.Var] = set()
    live_before_sets = {name + 'conclusion': set()}
    for label in blocks:
        live_before_sets[label] = set()

    live_after_sets = {}
    homes: Dict[x86.Var, x86.Arg] = {}

    # --------------------------------------------------
    # utilities
    # --------------------------------------------------
    def vars_arg(a: x86.Arg) -> Set[x86.Arg]:
        match a:
            case x86.Immediate(i):
                return set()
            case x86.Reg(r):
                return {x86.Reg(r)}
            case x86.ByteReg(r):
                return set()
            case x86.Var(x):
                all_vars.add(x86.Var(x))
                return {x86.Var(x)}
            case x86.Deref(r, offset):
                return set()
            case x86.GlobalVal(x):
                return set()
            case _:
                raise Exception('ul_arg', a)

    def reads_of(i: x86.Instr) -> Set[x86.Arg]:
        match i:
            case x86.NamedInstr(i, [e1, e2]) if i in ['movq', 'movzbq']:
                return vars_arg(e1)
            case x86.NamedInstr(i, [e1, e2]) if i in ['addq', 'subq', 'imulq', 'cmpq', 'andq', 'orq', 'xorq', 'leaq']:
                return vars_arg(e1).union(vars_arg(e2))
            case x86.Jmp(label) | x86.JmpIf(_, label):
                # the variables that might be read after this instruction
                # are the live-before variables of the destination block
                return live_before_sets[label]
            case _:
                if isinstance(i, (x86.Callq, x86.IndirectCallq, x86.Set)):
                    return set()
                else:
                    raise Exception(i)

    def writes_of(i: x86.Instr) -> Set[x86.Arg]:
        match i:
            case x86.NamedInstr(i, [e1, e2]) if i in ['movq', 'movzbq', 'addq', 'subq', 'imulq', 'cmpq', 'andq', 'orq',
                                                      'xorq', 'leaq']:
                return vars_arg(e2)
            case _:
                if isinstance(i, (x86.Jmp, x86.JmpIf, x86.Callq, x86.IndirectCallq, x86.Set)):
                    return set()
                else:
                    raise Exception(i)

    # --------------------------------------------------
    # liveness analysis
    # --------------------------------------------------
    def ul_instr(i: x86.Instr, live_after: Set[x86.Arg]) -> Set[x86.Arg]:
        return live_after.difference(writes_of(i)).union(reads_of(i))

    def ul_block(label: str):
        instrs = blocks[label]
        current_live_after: Set[x86.Arg] = set()

        block_live_after_sets = []
        for i in reversed(instrs):
            block_live_after_sets.append(current_live_after)
            current_live_after = ul_instr(i, current_live_after)

        live_before_sets[label] = current_live_after
        live_after_sets[label] = list(reversed(block_live_after_sets))

    def ul_fixpoint(labels: List[str]):
        fixpoint_reached = False

        while not fixpoint_reached:
            old_live_befores = live_before_sets.copy()

            for label in labels:
                ul_block(label)

            if old_live_befores == live_before_sets:
                fixpoint_reached = True

    # --------------------------------------------------
    # interference graph
    # --------------------------------------------------
    def bi_instr(e: x86.Instr, live_after: Set[x86.Var], graph: InterferenceGraph):
        match e:
            case x86.Callq(l) | x86.IndirectCallq(l):
                # add an edge in the interference graph between each live variable and each caller saved register
                for var in live_after:
                    print(var)
                    for r in constants.caller_saved_registers:
                        graph.add_edge(x86.Reg(r), var)
                    if var.val in tuple_var_types:
                        for r in constants.callee_saved_registers:
                            graph.add_edge(x86.Reg(r), var)
            case _:
                for v1 in writes_of(e):
                    for v2 in live_after:
                        graph.add_edge(v1, v2)

    def bi_block(instrs: List[x86.Instr], live_afters: List[Set[x86.Var]], graph: InterferenceGraph):
        for instr, live_after in zip(instrs, live_afters):
            bi_instr(instr, live_after, graph)

    # --------------------------------------------------
    # graph coloring
    # --------------------------------------------------
    def color_graph(local_vars: Set[x86.Var],
                    interference_graph: InterferenceGraph,
                    regular_locations: List[x86.Arg],
                    tuple_locations: List[x86.Arg]) -> Coloring:
        coloring: Coloring = {}

        to_color = local_vars.copy()

        # Saturation sets start out empty
        saturation_sets = {x: set() for x in local_vars}
        for x in local_vars:
            for y in interference_graph.neighbors(x):
                if isinstance(y, x86.Reg):
                    saturation_sets[x].add(y)

        # Loop until we are finished coloring
        while to_color:
            # Find the variable x with the largest saturation set
            x = max(to_color, key=lambda x: len(saturation_sets[x]))

            # Remove x from the variables to color
            to_color.remove(x)

            # Find the smallest color not in x's saturation set
            if x.var in tuple_var_types:
                x_color = next(i for i in tuple_locations if i not in saturation_sets[x])
            else:
                x_color = next(i for i in regular_locations if i not in saturation_sets[x])

            # Assign x's color
            coloring[x] = x_color

            # Add x's color to the saturation sets of its neighbors
            for y in interference_graph.neighbors(x):
                if isinstance(y, x86.Var):
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

    def ah_arg(a: x86.Arg) -> x86.Arg:
        match a:
            case x86.Immediate(_) | x86.Reg(_) | x86.ByteReg(_) | x86.GlobalVal(_) | x86.Deref(_, _):
                return a
            case x86.Var(x):
                return homes[x86.Var(x)]
            case _:
                raise Exception('ah_arg', a)

    def ah_instr(e: x86.Instr) -> x86.Instr:
        match e:
            case x86.NamedInstr(i, args):
                return x86.NamedInstr(i, [ah_arg(a) for a in args])
            case x86.Set(cc, a1):
                return x86.Set(cc, ah_arg(a1))
            case _:
                if isinstance(e, (x86.Callq, x86.IndirectCallq, x86.Retq, x86.Jmp, x86.JmpIf)):
                    return e
                else:
                    raise Exception('ah_instr', e)

    def ah_block(instrs: List[x86.Instr]) -> List[x86.Instr]:
        return [ah_instr(i) for i in instrs]

    # --------------------------------------------------
    # main body of the pass
    # --------------------------------------------------

    # Step 1: Perform liveness analysis
    all_labels = list(blocks.keys())
    ul_fixpoint(all_labels)
    log_ast('live-after sets', live_after_sets)

    # Step 2: Build the interference graph
    interference_graph = InterferenceGraph()

    for label in blocks.keys():
        bi_block(blocks[label], live_after_sets[label], interference_graph)

    log_ast('interference graph', interference_graph)

    # Step 3: Color the graph
    available_registers = constants.caller_saved_registers + constants.callee_saved_registers
    regular_locations = [x86.Reg(r) for r in available_registers] + \
                        [x86.Deref('rbp', -(offset * 8)) for offset in range(1, 200)]
    tuple_locations = [x86.Reg(r) for r in available_registers] + \
                      [x86.Deref('r15', -(offset * 8)) for offset in range(1, 200)]

    coloring = color_graph(all_vars, interference_graph, regular_locations, tuple_locations)
    homes = coloring
    log('homes', homes)

    stack_locations_used = 0
    root_stack_locations_used = 0
    for loc_used in homes.values():
        match loc_used:
            case x86.Reg(x):
                pass
            case x86.Deref('rbp', _):
                stack_locations_used += 1
            case x86.Deref('r15', _):
                root_stack_locations_used += 1

    # Step 5: replace variables with their homes
    blocks = program.blocks
    new_blocks = {label: ah_block(block) for label, block in blocks.items()}
    return x86.X86Program(new_blocks, stack_space=(align(8 * stack_locations_used), root_stack_locations_used))


##################################################
# patch-instructions
##################################################
# Arg            ::= Immediate(i) | Reg(r) | ByteReg(r) | Var(x) | Deref(r, offset) | GlobalVal(x)
# op             ::= 'addq' | 'subq' | 'imulq' | 'cmpq' | 'andq' | 'orq' | 'xorq' | 'movq' | 'movzbq'
#                  | 'leaq'
# cc             ::= 'e'| 'g' | 'ge' | 'l' | 'le'
# Instr          ::= NamedInstr(op, List[Arg]) | Callq(label) | Retq()
#                  | Jmp(label) | JmpIf(cc, label) | Set(cc, Arg)
#                  | IndirectCallq(Arg)
# Blocks         ::= Dict[label, List[Instr]]
# X86FunctionDef ::= X86FunctionDef(name, Blocks)
# X86ProgramDefs ::= List[X86FunctionDef]

def patch_instructions(program: X86ProgramDefs) -> X86ProgramDefs:
    """
    Patches instructions with two memory location inputs, using %rax as a temporary location.
    :param program: An x86 program.
    :return: A patched x86 program.
    """

    new_defs = []
    for d in program.defs:
        main_prog = x86.X86Program(d.blocks, None)
        result_mini_program = _patch_instructions(main_prog)
        new_def = X86FunctionDef(d.label, result_mini_program.blocks, result_mini_program.stack_space)
        new_defs.append(new_def)

    return X86ProgramDefs(new_defs)


def _patch_instructions(program: x86.X86Program) -> x86.X86Program:
    def pi_instr(e: x86.Instr) -> List[x86.Instr]:
        match e:
            case x86.NamedInstr(i, [x86.Deref(r1, o1), x86.GlobalVal(x)]):
                return [x86.NamedInstr('movq', [x86.Deref(r1, o1), x86.Reg('rax')]),
                        x86.NamedInstr(i, [x86.Reg('rax'), x86.GlobalVal(x)])]
            case x86.NamedInstr(i, [x86.GlobalVal(x), x86.Deref(r1, o1)]):
                return [x86.NamedInstr('movq', [x86.GlobalVal(x), x86.Reg('rax')]),
                        x86.NamedInstr(i, [x86.Reg('rax'), x86.Deref(r1, o1)])]
            case x86.NamedInstr(i, [x86.Deref(r1, o1), x86.Deref(r2, o2)]):
                return [x86.NamedInstr('movq', [x86.Deref(r1, o1), x86.Reg('rax')]),
                        x86.NamedInstr(i, [x86.Reg('rax'), x86.Deref(r2, o2)])]
            case x86.NamedInstr('movzbq', [x86.Deref(r1, o1), x86.Deref(r2, o2)]):
                return [x86.NamedInstr('movzbq', [x86.Deref(r1, o1), x86.Reg('rax')]),
                        x86.NamedInstr('movq', [x86.Reg('rax'), x86.Deref(r2, o2)])]
            case x86.NamedInstr('cmpq', [a1, x86.Immediate(i)]):
                return [x86.NamedInstr('movq', [x86.Immediate(i), x86.Reg('rax')]),
                        x86.NamedInstr('cmpq', [a1, x86.Reg('rax')])]
            case _:
                if isinstance(e, (x86.Callq, x86.IndirectCallq, x86.Retq, x86.Jmp, x86.JmpIf, x86.NamedInstr, x86.Set)):
                    return [e]
                else:
                    raise Exception('pi_instr', e)

    def pi_block(instrs: List[x86.Instr]) -> List[x86.Instr]:
        new_instrs = [pi_instr(i) for i in instrs]
        flattened = [val for sublist in new_instrs for val in sublist]
        return flattened

    blocks = program.blocks
    new_blocks = {label: pi_block(block) for label, block in blocks.items()}
    return x86.X86Program(new_blocks, stack_space=program.stack_space)


##################################################
# prelude-and-conclusion
##################################################
# Arg    ::= Immediate(i) | Reg(r) | ByteReg(r) | Deref(r, offset) | GlobalVal(x)
# op     ::= 'addq' | 'subq' | 'imulq' | 'cmpq' | 'andq' | 'orq' | 'xorq' | 'movq' | 'movzbq'
#          | 'leaq'
# cc     ::= 'e'| 'g' | 'ge' | 'l' | 'le'
# Instr  ::= NamedInstr(op, List[Arg]) | Callq(label) | Retq()
#          | Jmp(label) | JmpIf(cc, label) | Set(cc, Arg)
#          | IndirectCallq(Arg)
# Blocks ::= Dict[label, List[Instr]]
# X86    ::= X86Program(Blocks)

def prelude_and_conclusion(program: X86ProgramDefs) -> x86.X86Program:
    """
    Adds the prelude and conclusion for the program.
    :param program: An x86 program.
    :return: An x86 program, with prelude and conclusion.
    """
    new_blocks = {}
    for d in program.defs:
        main_prog = x86.X86Program(d.blocks)
        result_mini_program = _prelude_and_conclusion(d.label, main_prog)
        new_blocks.update(result_mini_program.blocks)
    return x86.X86Program(new_blocks)


def _prelude_and_conclusion(name: str, program: x86.X86Program) -> x86.X86Program:
    """
    Adds the prelude and conclusion for the program.
    :param program: An x86 program.
    :return: An x86 program, with prelude and conclusion.
    """

    stack_bytes, root_stack_locations = program.stack_space

    prelude = [x86.NamedInstr('pushq', [x86.Reg('rbp')]),
               x86.NamedInstr('movq', [x86.Reg('rsp'), x86.Reg('rbp')]),
               x86.NamedInstr('subq', [x86.Immediate(stack_bytes),
                                       x86.Reg('rsp')]),
               x86.NamedInstr('movq', [x86.Immediate(constants.root_stack_size),
                                       x86.Reg('rdi')]),
               x86.NamedInstr('movq', [x86.Immediate(constants.heap_size),
                                       x86.Reg('rsi')]),
               x86.Callq('initialize'),
               x86.NamedInstr('movq', [x86.GlobalVal('rootstack_begin'), x86.Reg('r15')])]
    for offset in range(root_stack_locations):
        prelude += [x86.NamedInstr('movq', [x86.Immediate(0), x86.Deref('r15', 0)]),
                    x86.NamedInstr('addq', [x86.Immediate(8), x86.Reg('r15')])]
    prelude += [x86.Jmp('start')]

    conclusion = [x86.NamedInstr('addq', [x86.Immediate(stack_bytes),
                                          x86.Reg('rsp')]),
                  x86.NamedInstr('popq', [x86.Reg('rbp')]),
                  x86.NamedInstr('subq', [x86.Immediate(8 * root_stack_locations), x86.Reg('r15')]),
                  x86.Retq()]

    # TODO: change to be the right thing
    new_blocks = program.blocks.copy()
    new_blocks['main'] = prelude
    new_blocks['conclusion'] = conclusion
    return x86.X86Program(new_blocks, stack_space=program.stack_space)


##################################################
# Compiler definition
##################################################

compiler_passes = {
    'typecheck': typecheck,
    'remove complex opera*': rco,
    'typecheck2': typecheck,
    'expose allocation': expose_alloc,
    'explicate control': explicate_control,
    'select instructions': select_instructions,
    'allocate registers': allocate_registers,
    'patch instructions': patch_instructions,
    'prelude & conclusion': prelude_and_conclusion,
    'print x86': x86.print_x86
}


def run_compiler(s, logging=False):
    global global_logging

    old_logging = global_logging
    global_logging = logging

    def print_prog(current_program):
        print('Concrete syntax:')
        if isinstance(current_program, x86.X86Program):
            print(x86.print_x86(current_program))
        elif isinstance(current_program, X86ProgramDefs):
            print(print_x86defs.print_x86_defs(current_program))
        elif isinstance(current_program, Program):
            print(print_program(current_program))
        elif isinstance(current_program, cfun.CProgram):
            print(cfun.print_program(current_program))

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

    global_logging = old_logging
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

