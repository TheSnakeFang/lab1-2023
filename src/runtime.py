#!/usr/bin/env python3

from typing import Optional
from symbolic import box, Result
from tinyscript_util import (
    check_sat,
    stringify
)
import tinyscript as tn

SETUP_VAR = '#inv_established'
INV_VAR = '#inv_true'

def invariant_instrument(Q: BoolRef) -> tn.Prog:
    """
    Construct instrumentation to enforce an invariant P,
    to be placed immediately before an assignment alpha.
    
    Args:
        Q (z3.BoolRef): A box-free formula that is equivalent
            to [alpha] P.
    
    Returns:
        tn.Prog: A tinyscript program that will set the
            policy variables appropriately to enforce the
            invariant P.
    """
    true_ins = tn.If(tn.EqF(tn.Var(SETUP_VAR), tn.Const(0)),
                     tn.Seq(tn.Asgn(INV_VAR, tn.Const(1)),
                            tn.Asgn(SETUP_VAR, tn.Const(1))),
                     tn.Skip())
    false_ins = tn.Asgn(INV_VAR, tn.Const(0))
    if is_true(Q):
        return true_ins
    elif is_false(Q):
        return false_ins
    else:
        return tn.If(z3_to_fmla(Q),
                     true_ins,
                     false_ins)

def add_instrumentation(alpha: tn.Prog, inv: tn.Formula) -> tn.Prog:
    match alpha:
        # assignments represent a step, so we need to add instrumentation
        case tn.Asgn(name, aexp):
            pre = box(alpha, fmla_enc(inv))
            # pre will be equivalent to inv if and only if the assignment
            # has no effect on whether the invariant will be violated or
            # established, so we don't add instrumentation if this is
            # the case.
            if not fmlas_equiv(fmla_enc(inv), pre):
                ins = invariant_instrument(pre)
                if ins != tn.Skip():
                    return tn.Seq(ins, alpha)
            return alpha
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
        # skips do nothing for invariants, so no instrumentation
        case tn.Skip(): # this is a step
            return alpha 
        case _:
            raise TypeError(
                "instrument got {type(alpha)} ({alpha}), not Prog"
            )
        # where is output and abort?
        
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
	Counter = tn.Var('#counter, 0') 
	
    instr = add_instrumentation(alpha, #COUNTER < STEP_BOUND) 
    initialize = tn.If(instr,
                       tn.Seq(tn.Asgn(SETUP_VAR, tn.Const(1)),
                              tn.Asgn(INV_VAR, tn.Const(1))),
                       tn.Seq(tn.Asgn(SETUP_VAR, tn.Const(0)),
                              tn.Asgn(INV_VAR, tn.Const(0))))
    return tn.Seq(initialize, instr)

def symbolic_check(
    alpha: tn.Prog, 
    step_bound: int,
    max_depth: int=1,
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
