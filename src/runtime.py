#!/usr/bin/env python3

from typing import Optional
from symbolic import box, Result
import z3
from tinyscript_util import (
    check_sat,
    fmla_enc,
    term_stringify,
    state_from_z3_model
)
import tinyscript as tn

CNR_VAR = '#counter'

def add_instrumentation(alpha: tn.Prog, inv: tn.Formula) -> tn.Prog:
    increment_counter = tn.Asgn(CNR_VAR, tn.Sum(tn.Var(CNR_VAR), tn.Const(1)))
    # print("add_instrumentaion_alpha:", stringify(alpha))
    match alpha:
        # assignments represent a step, so we need to add instrumentation
        case tn.Asgn(name, aexp):
            return tn.Seq(increment_counter, tn.Asgn(name, aexp))
        # composition is not listed as a step
        case tn.Seq(alpha_p, beta_p):
            ins_alpha = add_instrumentation(alpha_p, inv)
            ins_beta = add_instrumentation(beta_p, inv)
            return tn.Seq(ins_alpha, ins_beta)
        # conditionals are also not steps
        case tn.If(p, alpha_p, beta_p):
            ins_alpha = add_instrumentation(alpha_p, inv)
            ins_beta = add_instrumentation(beta_p, inv)
            return tn.If(p, ins_alpha, ins_beta)
        # same with while loops
        case tn.While(q, alpha_p):
            ins_alpha = add_instrumentation(alpha_p, inv)
            return tn.While(q, ins_alpha)
        case tn.Skip(): # this is a step
            return tn.Seq(increment_counter, tn.Skip())
        case tn.Abort(): # this is a step
            return tn.Seq(increment_counter, tn.Abort())
        case tn.Output(e): # this is a step
            return tn.Seq(increment_counter, tn.Output(e))
        case _:
            raise TypeError(
                f"instrument got {type(alpha)} ({alpha}), not Prog"
            )
        
def instrument(alpha: tn.Prog, step_bound: Optional[int]=None) -> tn.Prog:
    """
    Instruments a program to support symbolic checking 
    for violations of the maximum execution length policy.
    
    Args:
        alpha (tn.Prog): A tinyscript program to instrument
        step_bound (int, optional): A bound on runtime steps
    
    Returns:
        tn.Prog: The instrumented program. It should be possible
            to use the box modality and a satisfiability solver
            to determine whether a trace in the original program
            `alpha` exists that executes for longer than the bound
            on steps. A step occurs when the program executes an
            assignment, output, abort, or skip statement.
    """

	# counter?
    counter = tn.Asgn(CNR_VAR, tn.Const(0))
	
    instr = add_instrumentation(alpha, tn.LtF(tn.Var(CNR_VAR), tn.Const(step_bound)))
    #print(stringify(instr))
    return tn.Seq(counter, instr)

def symbolic_check(
    alpha: tn.Prog, 
    step_bound: int,
    max_depth: int=100,
    timeout: int=10) -> Result:
    """
    Uses the box modality and a satisfiability solver to determine
    whether there are any traces that execute more than `step_bound`
    steps. A step occurs when the program executes an assignment, 
    output, abort, or skip statement. This function only considers 
    traces generated after unrolling loops up to `max_depth` times, 
    and will terminate the solver after `timeout` seconds.
    
    Args:
        alpha (tn.Prog): Program to check
        step_bound (int): Step bound to check
        max_depth (int, optional): Loop unrolling depth
        timeout (int, optional): Solver timeout, in seconds
    
    Returns:
        Result: The status of the check, one of three values:
            - Result.Satisfies: All traces, up to the given unrolling 
              depth, terminate within `step_bound` steps. 
            - Result.Violates: There exists a trace that violates the
              step bound. This result *includes* traces that do not 
              terminate within the unrolling depth, e.g., 
              the program "while(true) skip" should yield this result
              with an unrolling depth of 1 if the solver is able to 
              provide a state that causes the interpreter to execute
              at least `step_bound` steps.
            - Result.Unknown: The result is indeterminate. This could
              mean that the solver timed out, returning z3.unknown. It
              could also signify that there is a trace that fails to
              terminate within the unrolling bound, but the solver did
              not return a state that caused the interpreter to execute
              at least `step_bound` steps.
    """

    alpha_p = instrument(alpha, step_bound)
    post = tn.LtF(tn.Var(CNR_VAR), tn.Const(step_bound))

    # print("varsprog", vars_prog(alpha_p))

    weakest_pre = box(alpha_p, fmla_enc(post), max_depth, False)

    res, model = check_sat([z3.Not(weakest_pre)], timeout)

    # print(stringify(alpha_p))
    print("step_bound:", step_bound)
    print("maxdepth:", max_depth)
    print("res, model:", res, model)
    print("boolref:", weakest_pre)
    print("test1", term_stringify(tn.Var(CNR_VAR)))
    print("test",  (tn.Asgn(CNR_VAR, tn.Sum(tn.Var(CNR_VAR), tn.Const(1)))))
    print("CNTRVAR:", CNR_VAR)

    if (res == z3.unsat):
        return Result.Satisfies
    elif (res == z3.sat):
            state = state_from_z3_model(alpha_p, model)
            print(state)
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
            res = symbolic_check(prog, 100)
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
