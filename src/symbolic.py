from tinyscript_util import (
    fmla_enc,
    simplify,
    term_enc,
    stringify
)
from enum import Enum
import tinyscript as tn
import z3

Result = Enum('Result', ['Satisfies', 'Violates', 'Unknown'])

@simplify
def box(
    alpha: tn.Prog,
    postcondition: z3.BoolRef,
    max_depth: int=10,
    depth_exceed_strict: bool=True
) -> z3.BoolRef:
    """
    Apply the axioms of dynamic logic to convert a box formula to
    and equivalent box-free formula over integer arithmetic. If
    the program has loops, then the loop axiom is applied up to
    `max_depth` times. After reaching this bound, `box` returns
    `z3.BoolVal(False)` if `depth_exceed_strict` is `True`, and 
    `z3.BoolVal(True)` otherwise.

    Args:
        alpha (tn.Prog): Program inside the box formula
        postcondition (z3.BoolRef): Formula outside the box
        max_depth (int, optional): Recursion limit for loop axiom; 
            defaults to `10`.
        depth_exceed_strict (bool, optional): Flags strict
            verification conditions for traces that exceed the
            loop recursion bound; defaults to `True`.
    
    Returns:
        z3.BoolRef: Result of applying axioms
    
    Raises:
        TypeError: `alpha` isn't a program
    """
    if max_depth < 1:
        return z3.unknown if depth_exceed_strict else z3.BoolVal(True)
    
    print(stringify(alpha))

    match alpha:
        case tn.Skip():
            return postcondition
        case tn.Asgn(name, e):
            return z3.substitute(postcondition, [(term_enc(tn.Var(name)), term_enc(e))])
        case tn.Seq(alpha_p, beta_p):
            return box(alpha_p, box(beta_p, postcondition))
        case tn.If(q, alpha_p, beta_p):
            encoding = fmla_enc(q)
            alpha_conv = box(alpha_p, postcondition, max_depth - 1)
            beta_conv = box(beta_p, postcondition, max_depth - 1)
            return z3.And(z3.And(encoding, alpha_conv), z3.And(z3.Not(encoding), beta_conv))
        case tn.While(q, alpha_p):
            unwound = tn.If(q, tn.Seq(alpha_p, tn.While(q, alpha_p)), tn.Skip())
            return box(unwound, postcondition, max_depth - 1)
        case tn.Output(e):
            return postcondition
        case tn.Abort():
            return postcondition
        case _:
            raise TypeError(
                f"box got {type(alpha)} ({alpha}), not Prog"
            )
