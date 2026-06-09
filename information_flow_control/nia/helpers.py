import z3

import copy
from whilelang import *


"""
We will model taints as Booleans.
"untainted" will be `False`, mnemonic L (low)
"tainted" will be `True`, mnemonic H (high)
"""
L : z3.AstRef = z3.BoolVal(False)
H : z3.AstRef = z3.BoolVal(True)


mem  = dict[str, z3.AstRef]
lmap = dict[str, z3.AstRef]

def renamed_variable_copy(v, suffix="_"):
    return z3.Const(v.decl().name() + suffix, v.sort())

def renamed_variable_copy_dict(d, suffix="_"):
    dr = dict()
    for k in d:
        dr[k] = renamed_variable_copy(d[k], suffix)

    return dr

@dataclass(frozen=True)
class Context:
    label: z3.AstRef
    pc: z3.AstRef

    def renamed_copy(self, suffix="_"):
        return Context(renamed_variable_copy(self.label, suffix), renamed_variable_copy(self.pc, suffix))

@dataclass(frozen=True)
class Variables:
    """
    Combines all z3-variables needed for a predicate application modeling a program state.

    ctx ... the variables describing context label and pc
    m   ... the variables describing the memories (indexed by program-level variable name)
    l   ... the variables describing the label map (indexed by program-level variable name)
    im  ... the variables describing the initial values used to relate executions
    """

    ctx: Context
    m: mem
    l: lmap
    im: mem

    @classmethod
    def from_vars(cls, vars, observed_vars=None):
        """
        Initialized Variables object from a list of variable names.
        `observed_vars` determines which exact initial variables are stored in `im`, so that
        the abstraction φ can later be computed in `relate_executions`.
        """
        if any('_' in v for v in vars):
            raise Exception("Underscores ('_') are not allowed in variable names, as they are used to generate copies of variables!")

        if not all(is_high_var(v) or is_low_var(v) for v in vars):
            raise Exception("Variable name have to start with 'l' or 'h' (respectively 'ah' and 'al' for array variables) to indicate their security level.")

        if observed_vars is None:
            observed_vars = [x for x in vars if is_low_var(x)]

        ctx = Context(z3.Bool('ctxl'), z3.Int('ctxpc'))
        m   = { x : z3.Int(x) for x in vars }
        im  = { x : z3.Int(x+'_i') for x in observed_vars }
        l   = { x : z3.Bool(x+'_t') for x in vars }

        return Variables(ctx, m, l, im)

    def predicate(self, pred: str | tuple[str,str], pc: int) -> z3.AstRef | tuple[z3.AstRef, z3.AstRef]:
        """
        Returns predicate application that is parametrized by `pc` and has the variables in `self` as arguments.

        If pred is a string, a single predicate application will be returned, if pred is a tuple, two predicate applications will be returned.
        """
        context = [ z3.BoolSort(), z3.IntSort() ]
        values = [ x.sort() for x in self.m.values() ]
        labels = [ z3.BoolSort() for x in self.m.values() ]
        lvalues = [ x.sort() for x in self.im.values() ]

        match pred:
            case str():
                p_pc = z3.Function(f'{pred}{pc}', context + values + labels + lvalues + [z3.BoolSort()])
                return p_pc(self.ctx.label, self.ctx.pc, *self.m.values(), *self.l.values(), *self.im.values())
            case (str(), str()):
                s_pc = z3.Function(f'{pred[0]}{pc}', context + values + labels + lvalues + [z3.BoolSort()])
                e_pc = z3.Function(f'{pred[1]}{pc}', context + values + labels + lvalues + [z3.BoolSort()])
                return s_pc(self.ctx.label, self.ctx.pc, *self.m.values(), *self.l.values(), *self.im.values()), e_pc(self.ctx.label, self.ctx.pc, *self.m.values(), *self.l.values(), *self.im.values())
        raise Exception("{pred} is not supported as predicate parameter.")

    def renamed_copy(self, keep: list[str] | None = None, update: list[str] | None = None, suffix='_'):
        """
        If `keep` is given, copy all variables and rename all of belonging to components not listed in `keep`.
        If `update` is given, copy all variables and rename all of belonging to components listed in `updated`.

        Renaming works by appending `suffix` to the z3 variables name.
        """

        if (keep == None) == (update == None):
            raise Exception("Either keep or update have to be specified!")

        if keep is not None:
            ctx = self.ctx.renamed_copy(suffix)                if 'ctx' not in keep else self.ctx
            m   = renamed_variable_copy_dict(self.m, suffix)   if 'm'   not in keep else copy.copy(self.m)
            l   = renamed_variable_copy_dict(self.l, suffix)   if 'l'   not in keep else copy.copy(self.l)
            im  = renamed_variable_copy_dict(self.im, suffix)  if 'im'  not in keep else copy.copy(self.im)
        elif update is not None:
            ctx = self.ctx.renamed_copy(suffix)                if 'ctx' in update else self.ctx
            m   = renamed_variable_copy_dict(self.m, suffix)   if 'm'   in update else copy.copy(self.m)
            l   = renamed_variable_copy_dict(self.l, suffix)   if 'l'   in update else copy.copy(self.l)
            im  = renamed_variable_copy_dict(self.im, suffix)  if 'im'  in update else copy.copy(self.im)

        return Variables(ctx, m, l, im)

    def renamed_copy_for_memory_access(self, varx: str, suffix='_'):
        """
        Returns copy of variables where the variables describing `varx`'s position in the memory and label map
        have been renamed.
        """
        rvs = self.renamed_copy(update=[])
        # create new memory
        rvs.m[varx] = renamed_variable_copy(self.m[varx])

        # create label map
        rvs.l[varx] = renamed_variable_copy(self.l[varx])

        return rvs


def get_vars(x: z3.AstRef, ret: set[z3.AstRef]):
    """
    Adds all variables that appear in a z3.AstRef to the provided set
    """
    if x.children():
        for y in x.children():
            get_vars(y, ret)
    else:
        if isinstance(x.decl(), z3.z3.FuncDeclRef) and z3.is_app_of(x, z3.Z3_OP_UNINTERPRETED):
            ret.add(x)

def is_low_var(s: str) -> bool:
    return any(s.startswith(p) for p in ["al", "l"])

def is_high_var(s: str) -> bool:
    return any(s.startswith(p) for p in ["ah", "h"])


def rule(premises: list[z3.AstRef], conclusion: z3.AstRef):
    """
    Turn a list of boolean-valued z3.AstRef `premises` and a boolean-valued z3.AstRef `conclusion` and
    provides a universally quantified implication  ∀ ⋀ p[i] ⇒ c
    """
    var_set : set[z3.AstRef] = set()

    for f in [*premises, conclusion]:
        get_vars(f, var_set)

    vars = list(var_set)

    match len(premises):
        case 0: return z3.ForAll(vars, conclusion)
        case 1: return z3.ForAll(vars, z3.Implies(*premises, conclusion))
        case _: return z3.ForAll(vars, z3.Implies(z3.And(*premises), conclusion))


def query(program, vars, abstraction_fn, observed_vars_fn=None, spacer=True, verbose=False):
    """
    Common query function for both strict and abstract noninterference analysis.

    `abstraction_fn` is the abstraction function from the calling module.
    `observed_vars_fn` is an optional function that determines which initial variables
    should be tracked (defaults to low variables only if None).
    """
    observed_vars = observed_vars_fn(vars) if observed_vars_fn else None
    vs = Variables.from_vars(vars, observed_vars)

    # We abstract the program as a set of Horn-clauses
    clauses, _ = abstraction_fn(program, 0, vs)

    # Let us generate the predicates representing the initial and final states
    s0, e0 = vs.predicate(('S', 'E'), 0)

    s = z3.Solver()
    if spacer:
        s = z3.SolverFor('HORN')
        s.set('engine', 'spacer')
        s.set('spacer.random_seed', 666)
        s.set('smt.random_seed', 666)

    # Initial constraints:
    # - the context is labeled L (untainted) and the pc has a dummy value of -1
    # - each l variable is labeled L in the label map
    # - each h variable is labeled H in the label map
    # - each tracked initial variable is equal to its current value

    initial_restrictions = [vs.ctx.label == L, vs.ctx.pc == -1]
    for k in vs.m.keys():
        if is_high_var(k):
            initial_restrictions.append(vs.l[k] == H)

        elif is_low_var(k):
            initial_restrictions.append(vs.l[k] == L)

    for k in vs.im.keys():
        initial_restrictions.append(vs.m[k] == vs.im[k])

    # The initial constraints should hold for s0 to be reachable
    s.add(rule(initial_restrictions, s0))
    # We add the program rules to the solver
    s.add(clauses)

    # Query:
    # e0 /\ q -> False
    # q := is any low variable tainted (i.e., H, a.k.a. True)?
    low_positions = [k for k in vs.m.keys() if is_low_var(k)]
    match len(low_positions):
        case 0:
            q = z3.BoolVal(False)
        case 1:
            q = vs.l[low_positions[0]]
        case _:
            q = z3.Or(*(vs.l[p] for p in low_positions))
    s.add(rule([e0, q], z3.BoolVal(False)))

    # Check if the set of rules is satisfiable:
    # - unsat means that the query is true, i.e., there is a tainted low variable (BAD!)
    # - sat means that the query is false, i.e., no tainted low variable
    res = s.check()
    if verbose:
        print(res)
        if res==z3.sat: print(s.model())
        if res==z3.unsat: print(s.proof())
    return res


def run_test(name: str, cmd: Cmd, res, abstraction_fn, observed_vars_fn=None):
    """
    Common test runner for both strict and abstract noninterference analysis.

    `abstraction_fn` is the abstraction function from the calling module.
    `observed_vars_fn` is an optional function that determines which initial variables
    should be tracked (defaults to low variables only if None).
    """
    var_set : set[var] = set()

    get_vars_program(cmd, var_set)
    vars = list(sorted(var_set))

    q = query(vars = vars, program = cmd, abstraction_fn=abstraction_fn, observed_vars_fn=observed_vars_fn, verbose=False)
    if q == res:
        print(f"test {name} successful!")
    else:
        print(f"test {name} unsuccessful!")
        raise RuntimeError(f"Test {name} Failed")
