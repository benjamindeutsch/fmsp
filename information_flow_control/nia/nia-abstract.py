#!/usr/bin/env python3.12

import z3
import sys
import pathlib
from whilelang import *
from parser import *
from helpers import *

HBIDA = 'hbidA'
HBIDB = 'hbidB'


z3.set_param(proof=True)
z3.set_param(model=True)


def observed_variables(vars: list[str]) -> list[str]:
    """
    Returns the variables whose exact initial values should be stored in `Variables.im`.

    Under the relaxed auction analysis, `im` should contain the low part of the initial memory
    together with enough concrete high information to compute the abstraction φ later in
    `relate_executions`.
    """
    observed = [x for x in vars if is_low_var(x)]

    # PROJECT DONE
    if(HBIDA in vars and HBIDB in vars):
        observed.extend([HBIDA, HBIDB])
    return observed


def auction_winner(m: mem) -> z3.AstRef:
    """
    Returns the abstract class of the auction example.
    Use the concrete values stored in `m` (typically an initial snapshot from `im`) to
    distinguish A-wins, B-wins, and tie.
    """
    # PROJECT DONE
    if(HBIDA not in m) or (HBIDB not in m):
        return z3.IntVal(0) # variables are not present
    
    return z3.If(m[HBIDB] < m[HBIDA], z3.IntVal(0), 
                 z3.If(m[HBIDA] < m[HBIDB], z3.IntVal(1), z3.IntVal(2)))


def lub(x: z3.AstRef, y: z3.AstRef) -> z3.AstRef:
    """
    Returns a z3 formula that models the least-upper-bound of two taints.
    "untainted" is lower than "tainted"
    """
    ## PROJECT DONE
    # untainted = false, tainted = true
    return z3.Or(x,y)


def relate_executions(vs1: Variables, vs2: Variables) -> z3.AstRef:
    """
    This function returns a Boolean z3 expression that evaluates to true, if the Join rule
    should consider the variables in `vs1` and `vs2` related (i.e., derived from a low-equal
    initial configuration).
    """
     # PROJECT DONE
    abstract_nia = auction_winner(vs1.im) == auction_winner(vs2.im)
    default_nia = z3.And(vs1.im[k] == vs2.im[k] for k in vs1.im if is_low_var(k))

    return z3.And(abstract_nia, default_nia) if (HBIDA in vs1.im and HBIDB in vs1.im) else default_nia


def join_memories(vs: Variables, vs1: Variables, vs2: Variables) -> z3.AstRef:
    """
    This function returns a Boolean z3 expression that restricts the values stored in `vs` to
    be a valid result of the Join-Rule. That is, joining the variables `vs1` and `vs2` into the output `vs`.

    apply(m₁', U₁) or apply(m₂', U₂) should be stored in vs.m
    Λ' should be stored in vs.l

    m₁' is stored in `vs1.m`
    m₂' is stored in `vs2.m`
    Λ₁ is stored in `vs1.l`
    Λ₂ is stored in `vs2.l`

    Note that you also need to constrain the variables of the initial memory configurations
    stored in `vs.im`, `vs1.im`, `vs2.im`.
    """
    # PROJECT DONE
    return z3.And(
        z3.Or(
            z3.And(vs.m[k] == vs1.m[k] for k in vs.m),
            z3.And(vs.m[k] == vs2.m[k] for k in vs.m)
        ),
        z3.And(z3.If(vs1.m[k] == vs2.m[k], L, lub(vs1.l[k], vs2.l[k])) == vs.l[k] for k in vs.l),
        # Same auction winners
        z3.And(vs.im[k] == vs1.im[k] for k in vs.im)
    )


def is_possible_join(c1: Cmd) -> bool:
    """
    Returns if the the sequencing operator `;` in a sequence `c1 ; _` should be (potentially)
    used to apply the Join-Rule or not.
    """
    # PROJECT DONE
    return isinstance(c1, IfThenElse) or isinstance(c1, While)


def is_context_same(vs1: Variables, vs2: Variables) -> z3.AstRef:
    """
    Returns a Boolean z3 expression that describes if the context objects in `vs1` and `vs2` are
    the same. This is used in the join rule, as it is only applied if the two executions have
    the same context object.

    The context objects are stored in `vs1.ctx` and `vs2.ctx`.
    """
    # PROJECT DONE
    return z3.And(vs1.ctx.label == vs2.ctx.label, vs1.ctx.pc == vs2.ctx.pc)


def context_is_untainted(vs: Variables) -> z3.AstRef:
    """
    Returns a Boolean z3 expression that describes if the context object in `vs` is the
    untainted context object. Looks like (=)_ctx in the rules.
    """
    # PROJECT DONE
    return vs.ctx.label == L


def context_is_untainted_or_not_ready_to_join_yet(vs: Variables, pc: int) -> z3.AstRef:
    """
    Returns a Boolean z3 expression that describes if the context object in `vs` is untainted
    or not ready to join at the given `pc`. This is used to differentiate potential applications
    of Join from Propagate-Taint when applying the sequencing operator.
    """
    # PROJECT DONE
    # pc + 1 is the counter of the parent Seq.
    return z3.Or(vs.ctx.label == L, vs.ctx.pc != pc + 1)


def context_is_tainted_and_ready_to_join(vs: Variables, pc: int) -> z3.AstRef:
    """
    Returns a Boolean z3 expression that describes if the context object in `vs` is tainted
    and ready to join at the given `pc`. This is used to differentiate potential applications
    of Join from Propagate-Taint when applying the sequencing operator.
    """
    # PROJECT DONE
    # pc + 1 is the counter of the parent Seq.
    return z3.And(vs.ctx.label == H, vs.ctx.pc == pc + 1)


def formula_and_least_upper_bound_of(e: expr, vs: Variables) -> tuple[z3.AstRef, z3.AstRef]:
    """
    This function returns, given an expression `e` that may use variables from `vs`, a tuple of
    z3 expressions. The first element of the tuple describes the value of the expression, the
    second one its taint.

    Note that this function does not appear as-is in the nia rules, but it eases the implementation
    of the update of the label map Λ', the apply(m', U) (where U is the result of astep(m',...)
    in Propagate-Taint), as well as the computation of control-flow conditions (pp'' and labels
    of I_pp in Raise-Context-Step).

    m' is stored in `vs.m`
    Λ  is stored in `vs.l`
    """
    # PROJECT DONE
    match e:
        case var():
            return vs.m[e], vs.l[e]
        case const():
            return z3.IntVal(e), L
        case (op, a, b):
            va, la = formula_and_least_upper_bound_of(a, vs)
            vb, lb = formula_and_least_upper_bound_of(b, vs)
            l = lub(la, lb)
            match op:
                case '+': return va + vb, l
                case '-': return va - vb, l
                case '*': return va * vb, l
                case '<': return z3.If(va < vb, z3.IntVal(1), z3.IntVal(0)), l
                case '>': return z3.If(va > vb, z3.IntVal(1), z3.IntVal(0)), l
                case '==': return z3.If(va == vb, z3.IntVal(1), z3.IntVal(0)), l
                case '!=': return z3.If(va != vb, z3.IntVal(1), z3.IntVal(0)), l
                case _: raise RuntimeError('unknown operator!')
        case _: raise RuntimeError('unknown expression type!')

    return z3.IntVal(0), L


def abstraction(c: Cmd, pc: int, vs: Variables) -> tuple[list[z3.AstRef], int]:
    match c:
        case Empty():
            # Propagate-Taint
            s_pc, e_pc = vs.predicate(('S', 'E'), pc)
            return [rule([s_pc], e_pc)], pc

        case Assign(x, e):
            # Propagate-Taint
            rvs = vs.renamed_copy_for_memory_access(x)
            s_pc = vs.predicate('S', pc)
            e_pc = rvs.predicate('E', pc)
            phi, lphi = formula_and_least_upper_bound_of(e, vs)
            lphi = lub(lphi, vs.ctx.label)
            return [ rule([ s_pc, rvs.m[x] == phi,  rvs.l[x] == lphi ], e_pc) ], pc

        case Seq(c1, c2):
            a1, mpc1 = abstraction(c1, pc+1, vs)
            a2, mpc2 = abstraction(c2, mpc1+1, vs)
            s_pc, e_pc = vs.predicate(('S', 'E'), pc)
            s_pc1, e_pc1 = vs.predicate(('S', 'E'), pc+1)
            s_pc2, e_pc2 = vs.predicate(('S', 'E'), mpc1+1)

            if is_possible_join(c1):
                # Join
                vs1 = vs.renamed_copy(keep=[],suffix='_1')
                vs2 = vs.renamed_copy(keep=[],suffix='_2')

                e1_pc1 = vs1.predicate('E', pc+1)
                e2_pc1 = vs2.predicate('E', pc+1)

                propagate_joined_memory_to_next_command = rule([
                    e1_pc1,
                    e2_pc1,
                    is_context_same(vs1, vs2),
                    context_is_tainted_and_ready_to_join(vs1,pc),
                    relate_executions(vs1, vs2),
                    join_memories(vs, vs1, vs2),
                    context_is_untainted(vs)
                ], s_pc2)

                # Propagate-Taint
                propagate_unjoined_memory_to_next_command = rule([e_pc1, context_is_untainted_or_not_ready_to_join_yet(vs, pc)], s_pc2)

                propagation_from_pc1_to_pc2 = [ propagate_joined_memory_to_next_command, propagate_unjoined_memory_to_next_command ]
            else:
                # Propagate-Taint
                propagation_from_pc1_to_pc2 = [ rule([e_pc1], s_pc2) ]

            return [ rule([s_pc], s_pc1), *a1,  *propagation_from_pc1_to_pc2, *a2, rule([e_pc2], e_pc) ], mpc2

        case IfThenElse(e, c1, c2):
            phi, lphi = formula_and_least_upper_bound_of(e, vs)

            a1, mpc1 = abstraction(c1, pc+1, vs)
            a2, mpc2 = abstraction(c2, mpc1+1, vs)

            vs1 = vs.renamed_copy(update=['ctx'])

            s_pc, e_pc = vs.predicate(('S', 'E'), pc)

            s_pc1 = vs1.predicate('S', pc + 1)
            e_pc1 = vs.predicate('E', pc + 1)
            s_pc2 = vs1.predicate('S', mpc1 + 1)
            e_pc2 = vs.predicate('E', mpc1 + 1)

            # Propagate-Taint
            context_already_high_or_condition_low = z3.Or(vs.ctx.label == H, lphi == L)
            context_stays_the_same = z3.And(vs1.ctx.label == vs.ctx.label, vs1.ctx.pc == vs.ctx.pc)

            # Raise-Context
            context_is_updated = z3.And(vs1.ctx.label == H, vs1.ctx.pc == pc)


            return ([rule([z3.Not(phi==0), z3.If(context_already_high_or_condition_low, context_stays_the_same, context_is_updated), s_pc], s_pc1),
                     rule([phi==0,         z3.If(context_already_high_or_condition_low, context_stays_the_same, context_is_updated), s_pc], s_pc2),
                     *a1, *a2,
                     rule([e_pc1], e_pc), rule([e_pc2], e_pc)]), mpc2
        case While(e, c1):
            # PROJECT DONE
            phi, lphi = formula_and_least_upper_bound_of(e, vs)

            a_body, mpc_body = abstraction(c1, pc + 1, vs)

            vs_body = vs.renamed_copy(update=['ctx'])

            s_pc = vs.predicate('S', pc)
            # If we skip the loop, the context might be raised (needed for joining)
            e_pc = vs_body.predicate('E', pc)
            s_body = vs_body.predicate('S', pc + 1)
            e_body = vs.predicate('E', pc + 1)

            # Propagate-Taint
            context_already_high_or_condition_low = z3.Or(vs.ctx.label == H, lphi == L)
            context_stays_the_same = z3.And(vs_body.ctx.label == vs.ctx.label, vs_body.ctx.pc == vs.ctx.pc)

            # Raise-Context
            context_is_updated = z3.And(vs_body.ctx.label == H, vs_body.ctx.pc == pc)

            return ([rule([z3.Not(phi==0), z3.If(context_already_high_or_condition_low, context_stays_the_same, context_is_updated), s_pc], s_body),
                     rule([phi==0,         z3.If(context_already_high_or_condition_low, context_stays_the_same, context_is_updated), s_pc], e_pc),
                     *a_body,
                     rule([e_body], s_pc)]), mpc_body

        case _: raise RuntimeError('unreachable!')


if __name__ == '__main__':
    try:
        print("STRICT NONINTERFERENCE\n")

        for test_case in pathlib.Path('tests/nia').glob('*/*'):
            cmd = Parser.cmd.parse_strict(test_case.read_text())
            run_test(test_case.stem, cmd, z3.unsat if test_case.parent.stem == 'pos' else z3.sat, abstraction_fn=abstraction)

        print("\nABSTRACT NONINTERFERENCE\n")

        for test_case in pathlib.Path('tests/abstract').glob('*/*'):
            cmd = Parser.cmd.parse_strict(test_case.read_text())
            run_test(test_case.stem, cmd, z3.unsat if test_case.parent.stem == 'pos' else z3.sat, abstraction_fn=abstraction, observed_vars_fn=observed_variables)

        print(f"\n\033[32;1m ✔️✔️✔️ TEST SUCCESSFUL ✔️✔️✔️ \033[0m")
    except:
        import traceback
        traceback.print_exc()
        print(f"\n\033[31;1m❌❌❌ TEST FAILED ❌❌❌ \033[0m")
