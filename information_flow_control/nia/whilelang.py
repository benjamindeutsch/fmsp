#!/usr/bin/env python3.12

from dataclasses import dataclass

op = str
const = int
var = str 
expr = var | const | tuple[op, (var | const), (var | const)]

@dataclass(frozen=True)
class Cmd: pass
 
@dataclass(frozen=True)
class Empty(Cmd): pass
 
@dataclass(frozen=True)
class Assign(Cmd):
    x : var
    e : expr
 
@dataclass(frozen=True)
class Seq(Cmd):
    c1 : Cmd
    c2 : Cmd
 
@dataclass(frozen=True)
class IfThenElse(Cmd):
    e: expr 
    thn: Cmd
    els: Cmd
 
@dataclass(frozen=True)
class While(Cmd):
    e: expr
    b: Cmd
 

def get_vars_expr(e: expr, ret: set[var]):
    match e:
        case int(): return
        case str():
            ret.add(e)
            return
        case (op, a, b):
            get_vars_expr(a, ret)
            get_vars_expr(b, ret)
            return

    raise RuntimeError('unreachable')

def get_vars_program(c: Cmd, ret: set[var]):
    match c:
        case Empty():
            return 
        case Assign(x, e):
            match x:
                case str():
                    ret.add(x)
                case _:
                    raise Exception(f"variable '{x}' not parsed")
                    
            get_vars_expr(e, ret)
        case Seq(c1, c2):
            get_vars_program(c1, ret)
            get_vars_program(c2, ret)
        case IfThenElse(e, c1, c2):
            get_vars_expr(e, ret)
            get_vars_program(c1, ret)
            get_vars_program(c2, ret)
        case While(e, c1):
            get_vars_expr(e, ret)
            get_vars_program(c1, ret)
        case _: raise RuntimeError('unreachable!')
