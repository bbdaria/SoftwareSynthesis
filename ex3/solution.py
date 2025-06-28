import typing
import operator
from http.client import UnimplementedFileMode

import z3

from syntax.while_lang import (
    parse,
    Id,
    Expr,
    Int,
    BinOp,
    Skip,
    Assign,
    Seq,
    If,
    While,
    Stmt,
)


type Formula = z3.Ast | bool
type PVar = str
type Env = dict[PVar, Formula]
type Invariant = typing.Callable[[Env], Formula]

TRIVIAL: typing.Final = lambda _: True


OP = {
    "+": operator.add,
    "-": operator.sub,
    "*": operator.mul,
    "/": operator.floordiv,
    "!=": operator.ne,
    ">": operator.gt,
    "<": operator.lt,
    "<=": operator.le,
    ">=": operator.ge,
    "=": operator.eq,
}


def mk_env(pvars: set[PVar]) -> Env:
    return {v: z3.Int(v) for v in pvars}


def upd(d: Env, k: PVar, v: Formula) -> Env:
    d = d.copy()
    d[k] = v
    return d


def collect_vars(stmt: Stmt) -> set[str]:
    vars = set()

    def visit_expr(e: Expr):
        match e:
            case Id(name): vars.add(name)
            case BinOp(_, lhs, rhs): visit_expr(lhs); visit_expr(rhs)

    def visit_stmt(s: Stmt):
        match s:
            case Skip(): pass
            case Assign(Id(name), expr): vars.add(name); visit_expr(expr)
            case Seq(s1, s2): visit_stmt(s1); visit_stmt(s2)
            case If(cond, t, e): visit_expr(cond); visit_stmt(t); visit_stmt(e)
            case While(cond, body): visit_expr(cond); visit_stmt(body)

    visit_stmt(stmt)
    return vars


def wp(stmt: Stmt, pre:Invariant, post: Invariant, linv: Invariant) -> Invariant:
    def _eval_expr(expr: Expr, env: Env) -> z3.Ast:
        match expr:
            case Int(v): return z3.IntVal(v)
            case Id(name): return env[name]
            case BinOp(op, lhs, rhs):
                return OP[op](_eval_expr(lhs, env), _eval_expr(rhs, env))
        raise NotImplementedError

    def _wp(s: Stmt, P: Invariant, Q: Invariant, linv: Invariant) -> Invariant:
        match s:
            case Skip():
                return Q
            case Assign(Id(x), e):
                return lambda env: Q(upd(env, x, _eval_expr(e, env)))
            case Seq(s1, s2):
                return _wp(s1, P, _wp(s2, P, Q, linv), linv)
            case If(cond, then_branch, else_branch):
                return lambda env: z3.And(
                    z3.Implies(_eval_expr(cond, env), _wp(then_branch, P, Q, linv)(env)),
                    z3.Implies(z3.Not(_eval_expr(cond, env)), _wp(else_branch, P, Q, linv)(env)),
                )
            case While(cond, body):
                I = linv
                return lambda env: z3.And(
                    z3.Implies(P(env), I(env)),  # Initiation
                    z3.Implies(z3.And(I(env), b := _eval_expr(cond, env)), _wp(body, I, I, I)(env)),  # Preservation
                    z3.Implies(z3.And(I(env), z3.Not(b)), Q(env))  # Exit implies post
                )
            case _:
                raise NotImplementedError(f"Unhandled stmt type: {type(s)}")

    return _wp(stmt, pre, post, linv)

def find_solution(P: Invariant, stmt: Stmt, Q: Invariant, linv: Invariant = TRIVIAL) -> z3.Solver:
    solver = z3.Solver()
    all_vars = collect_vars(stmt)  # you should implement this to find all Ids
    env = mk_env(all_vars)
    pre = wp(stmt, P, Q, linv)
    solver.add(z3.Not(z3.Implies(P(env), pre(env))))
    return solver


def verify(P: Invariant, stmt: Stmt, Q: Invariant, linv: Invariant = TRIVIAL) -> bool:
    """
    Verifies a Hoare triple {P} c {Q}
    Where P, Q are assertions, and stmt is the modern AST.
    Returns True if the triple is valid.
    """
    solver = find_solution(P, stmt, Q, linv)
    return solver.check() == z3.unsat


def main() -> None:
    # example program
    program = "a := b ; while i < n do ( a := a + 1 ; b := b + 1 )"
    P = TRIVIAL
    Q = lambda d: d["a"] == d["b"]
    linv = lambda d: d["a"] == d["b"]

    ast = parse(program)
    # Your task is to implement "verify"
    solver = find_solution(P, ast, Q, linv=linv)
    if solver.check() == z3.sat:
        print("Counterexample found:")
        print(solver.model())
    else:
        print("No counterexample found. The Hoare triple is valid.")


if __name__ == "__main__":
    main()