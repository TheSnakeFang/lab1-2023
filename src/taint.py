#!/usr/bin/env python3

from symbolic import box, Result
from tinyscript_util import (
    check_sat,
    fmla_enc,
    state_from_z3_model,
    vars_formula,
    vars_prog,
    vars_term,
)
from functools import reduce
import interpreter as interp
import tinyscript as tn
import z3

TAINTED = '#was_tainted'

def add_instrumentation(alpha: tn.Prog) -> tn.Prog:
    """
    This function takes a TinyScript program alpha and returns a new program
    with added instrumentation code to check for the tainted analysis policy. 
    Specifically, it instruments the code to identify if any variable is being 
    used before it is defined.
    
    Args:
        alpha (tn.Prog): Program to instrument
    
    Returns:

    A TinyScript program with the following instrumentation added:
        - Assignment (tn.Asgn): Adds conditional checks to propagate 
          taint status from source variables to the assigned variable.
          Removes taint from assignee if all sources are untainted.
        - Output (tn.Output): Adds checks to identify if any variable 
          in the output expression is tainted and should be flagged.
    """
    match alpha:
        # assignments create a new variable, so we need to add instrumentation
        case tn.Asgn(name, aexp):
            output = vars_term(aexp)
            # print("Asgn output", output)
            if output != []:
                check = tn.If(tn.EqF(tn.Var(f'#taint_{output[0]}'), tn.Const(1)), tn.Asgn(f'#taint_{name}', tn.Const(1)), (tn.Asgn(f'#taint_{name}', tn.Const(0))))
                for i in output[1:]:
                    check = tn.If(tn.EqF(tn.Var(f'#taint_{i}'), tn.Const(1)), tn.Asgn(f'#taint_{name}', tn.Const(1)), check)
                return tn.Seq(check, tn.Asgn(name, aexp))
            return tn.Seq((tn.Asgn(f'#taint_{name}', tn.Const(0))), tn.Asgn(name, aexp))
        case tn.Seq(alpha_p, beta_p):
            ins_alpha = add_instrumentation(alpha_p)
            ins_beta = add_instrumentation(beta_p)
            return tn.Seq(ins_alpha, ins_beta)
        case tn.If(p, alpha_p, beta_p):
            output = vars_formula(p)
            ins_alpha = add_instrumentation(alpha_p)
            ins_beta = add_instrumentation(beta_p)
            return tn.If(p, ins_alpha, ins_beta)
        case tn.While(q, alpha_p):
            output = vars_formula(q)
            ins_alpha = add_instrumentation(alpha_p)
            return tn.While(q, ins_alpha)
        case tn.Skip(): 
            return tn.Skip()
        case tn.Abort(): 
            return tn.Abort()
        case tn.Output(e): 
            output = vars_term(e)
            if output != []:
                check = tn.If(tn.EqF(tn.Var(f'#taint_{output[0]}'), tn.Const(1)), tn.Asgn(TAINTED, tn.Const(1)), tn.Skip())
                for i in output[1:]:
                    check = tn.Seq(tn.If(tn.EqF(tn.Var(f'#taint_{i}'), tn.Const(1)), tn.Asgn(TAINTED, tn.Const (1)), tn.Skip()), check)
                return tn.Seq(check, tn.Output(e))
            return tn.Output(e)
        case _:
            raise TypeError(
                f"instrument got {type(alpha)} ({alpha}), not Prog"
            )


def instrument(alpha: tn.Prog, source_prefix: str='sec_') -> tn.Prog:
    """
    Instruments a program to support symbolic checking 
    for violations of a taint policy that considers any variable 
    prefixed with `secret_prefix` to be a source, and the argument 
    to any `output` statement to be a sink.
    
    Args:
        alpha (tn.Prog): A tinyscript program to instrument
        source_prefix (str, optional): The string prefix for
            source variables
    
    Returns:
        tn.Prog: The instrumented program. It should be possible
            to use the box modality and a satisfiability solver
            to determine whether a trace in the original program
            `alpha` exists that violates the taint policy.
    """
    counter = tn.Asgn(TAINTED, tn.Const(0))
    var_list = vars_prog(alpha)
    if var_list[0].name.startswith(source_prefix):
            create = (tn.Asgn(f'#taint_{var_list[0]}', tn.Const(1)))
    else: create = tn.Asgn(f'#taint_{var_list[0]}', tn.Const(0))
    for i in var_list[1:]:
        if i.name.startswith(source_prefix):
            create = tn.Seq(tn.Asgn(f'#taint_{i}', tn.Const(1)), create)
        else: create = tn.Seq(tn.Asgn(f'#taint_{i}', tn.Const(0)), create)
    instr = add_instrumentation(alpha)
   
    return tn.Seq(counter, tn.Seq(create, instr))

def symbolic_check(
    alpha: tn.Prog, 
    source_prefix: str='sec_', 
    max_depth: int=99,
    timeout: int=10) -> Result:
    """
    Uses the box modality and a satisfiability solver to determine
    whether there are any traces that violate a taint policy that 
    considers any variable prefixed with `secret_prefix` to be a 
    source, and the argument to any `output` statement to be a sink.
    This function only considers traces generated after unrolling 
    loops up to `max_depth` times, and will terminate the solver 
    after `timeout` seconds.
    
    Args:
        alpha (tn.Prog): Program to check
        source_prefix (str, optional): String prefix for source
            variables
        max_depth (int, optional): Loop unrolling depth
        timeout (int, optional): Solver timeout, in seconds
    
    Returns:
        Result: The status of the check, one of three values:
            - Result.Satisfies: All traces up to the unrolling depth
              satisfy the taint policy. This result *does not* signify 
              anything about traces that exceed the unrolling depth.
            - Result.Violates: There exists a trace within the unrolling
              depth that violates the taint policy.
            - Result.Unknown: The result is indeterminate (e.g. the
              solver timed out, returning z3.unknown).
    """
    alpha_p = instrument(alpha)
    post = tn.EqF(tn.Var(TAINTED), tn.Const(0))

    weakest_pre = box(alpha_p, fmla_enc(post), max_depth, False)

    res, model = check_sat([z3.Not(weakest_pre)], timeout)

    if (res == z3.unsat):
        return Result.Satisfies
    elif (res == z3.sat):
        return Result.Violates
    return Result.Unknown

if __name__ == "__main__":
    from parser import parse, fmla_parse
    import sys
    from pathlib import Path

    TEST_DIR = Path('.') / 'tests'

    if not TEST_DIR.is_dir():
        raise ValueError(f"Expected {TEST_DIR} to be a directory")

    passed = 0
    violate = 0
    unknown = 0

    for test_file in list(TEST_DIR.iterdir()):
        if not str(test_file).endswith('tinyscript'):
            continue
        with test_file.open() as f:
            prog = parse(f.read())
            res = symbolic_check(prog)
            print((
                f"{test_file} result:" 
                f"{res}"))
            match res:
                case Result.Satisfies:
                    passed += 1
                case Result.Violates:
                    violate += 1
                case Result.Unknown:
                    unknown += 1

    print(f"\n{passed=}, {violate=}, {unknown=}")