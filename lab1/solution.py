from syntax.lambda_pure import *


def substitute(sub: Id, tosub: Id, body: LambdaExpr) -> LambdaExpr:
    exp_type = type(body)
    match exp_type:
        #todo

def alpha_equivalent(e1: LambdaExpr, e2: LambdaExpr) -> bool:
    """Check if two lambda expressions differ only in the names of their bound variables."""
    raise NotImplementedError


def interpret(e: LambdaExpr, fuel: int = 100_000) -> LambdaExpr:
    if fuel <= 0:
        raise RecursionError
    
    exp = parse(e)
    if isinstance(exp, Id):
        return exp
    if isinstance(exp, Int):
        pass
    if isinstance(exp, Let):
        pass
    if isinstance(exp, App):
        lambdaeval = interpret(exp.func, fuel - 1)
        # substitute exp.arg with exp.func.var inside lambdaeval.
    if isinstance(exp, Lambda):
        bodyeval = interpret(exp.body, fuel - 1)
        return Lambda(exp.var, bodyeval)

    """Keep performing normal-order reduction steps until you reach normal form, detect divergence or run out of fuel."""
    raise NotImplementedError
