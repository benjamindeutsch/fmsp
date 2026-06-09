#!/usr/bin/env python3.12

import parsec
from whilelang import *

class Parser:
    spaces = parsec.many(parsec.one_of(" \n\t"))
    def token(p): return Parser.spaces >> p << Parser.spaces
    def symbol(s):return Parser.token(parsec.string(s))

    @parsec.generate
    def integer():
        i = yield Parser.token(parsec.regex("-?[0-9]+")).parsecmap(int)
        return i

    @parsec.generate
    def identifier():
        name = yield Parser.token(parsec.regex("[a-zA-Z\\-\\_]+[0-9]*"))
        return name

    @parsec.generate
    def expr():
        var = Parser.identifier
        const = Parser.integer
        @parsec.generate
        def op():
            e1 = yield (const | var)
            p  = yield Parser.token(parsec.regex("\\+|-|\\*|<|>|==|!="))
            e2 = yield (const | var)
            return (p, e1, e2)
        exp = yield (op ^ const ^ var)
        return exp

    def empty(text,index):
        return parsec.Value.success(index, Empty())

    @parsec.generate
    def assign():
        x = yield Parser.identifier
        yield Parser.symbol('=')
        c = yield Parser.expr
        return Assign(x, c)

    @parsec.generate
    def ifthenelse():
        yield Parser.symbol("IF")
        cnd = yield Parser.expr
        yield Parser.symbol("THEN")
        c1  = yield Parser.cmd
        c2  = yield (Parser.symbol("ELSE") >> Parser.cmd ^ Parser.empty)
        yield Parser.symbol("END")
        return IfThenElse(cnd, c1, c2)

    @parsec.generate
    def _while():
        yield Parser.symbol("WHILE")
        cnd  = yield Parser.expr
        yield Parser.symbol("DO")
        cmd  = yield Parser.cmd
        yield Parser.symbol("END")
        return While(cnd, cmd)

    @parsec.generate
    def cmd():
        yield Parser.spaces
        single = (Parser._while | Parser.ifthenelse | Parser.assign)
        @parsec.generate
        def seq():
            c1 = yield single
            yield Parser.symbol(';')
            c2 = yield Parser.cmd
            return Seq(c1,c2)
        cmd = yield (seq ^ single)
        return cmd
