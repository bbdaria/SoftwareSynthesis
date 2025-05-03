from syntax.lambda_pure import *


def substitute(sub: LambdaExpr, tosub: Id, body: LambdaExpr) -> LambdaExpr:
    match body:
        case Id(name):
            if name == tosub.name:
                return sub
            else:
                return body

        case Int(_):
            return body

        case Let(decl, defn, let_body):
            defn_subbed = substitute(sub, tosub, defn)
            if decl.name == tosub.name:
                return Let(decl, defn_subbed, let_body)
            else:
                return Let(decl, defn_subbed, substitute(sub, tosub, let_body))

        case Lambda(var, lam_body):
            if var.name == tosub.name:
                return Lambda(var, lam_body)
            else:
                return Lambda(var, substitute(sub, tosub, lam_body))

        case App(func, arg):
            return App(
                substitute(sub, tosub, func),
                substitute(sub, tosub, arg)
            )

        case _:
            raise TypeError()
        
def church_encode(n: int) -> LambdaExpr:
    f = Id("f")
    x = Id("x")
    body = x
    for _ in range(n):
        body = App(f, body)
    return Lambda(f, Lambda(x, body))

            

def alpha_equivalent(e1: LambdaExpr, e2: LambdaExpr) -> bool:
    def helper(e1, e2, env1, env2):
        match e1, e2:
            case Id(n1), Id(n2):
                return env1.get(n1, n1) == env2.get(n2, n2)
            case Int(n1), Int(n2):
                return n1 == n2
            case App(f1, a1), App(f2, a2):
                return helper(f1, f2, env1, env2) and helper(a1, a2, env1, env2)
            case Lambda(v1, b1), Lambda(v2, b2):
                new = f"v{len(env1)}"
                env1_new = env1 | {v1.name: new}
                env2_new = env2 | {v2.name: new}
                return helper(b1, b2, env1_new, env2_new)
            case Let(d1, def1, b1), Let(d2, def2, b2):
                if not helper(def1, def2, env1, env2):
                    return False
                new = f"v{len(env1)}"
                env1_new = env1 | {d1.name: new}
                env2_new = env2 | {d2.name: new}
                return helper(b1, b2, env1_new, env2_new)
            case _:
                return False

    return helper(e1, e2, {}, {})



def interpret(e: LambdaExpr, fuel: int = 100_000) -> LambdaExpr:
    if fuel <= 0:
        raise RecursionError()

    match e:
        case Int(n):
            return interpret(church_encode(n), fuel - 1)

        case Let(decl, defn, body):
            substituted = substitute(defn, decl, body)
            return interpret(substituted, fuel - 1)

        case App(func, arg):
            func_eval = interpret(func, fuel - 1)
            if isinstance(func_eval, Lambda):
                new_body = substitute(arg, func_eval.var, func_eval.body)
                return interpret(new_body, fuel - 1)
            else:
                return App(func_eval, arg)

        case Lambda(var, body):
            return Lambda(var, body)

        case Id(_):
            return e

        case _:
            raise TypeError()

# excercise 2

TRUE = Lambda(Id("t"), Lambda(Id("f"), Id("t")))

FALSE = Lambda(Id("t"), Lambda(Id("f"), Id("f")))

IF = Lambda(Id("b"), Lambda(Id("x"), Lambda(Id("y"), App(App(Id("b"), Id("x")), Id("y")))))

ZERO = Lambda(Id("f"), Lambda(Id("x"), Id("x")))

SUCC = Lambda(Id("n"), Lambda(Id("f"), Lambda(Id("x"), App(Id("f"), App(App(Id("n"), Id("f")), Id("x"))))))

ADD = Lambda(Id("m"), Lambda(Id("n"), Lambda(Id("f"), Lambda(Id("x"),
      App(App(Id("m"), Id("f")), App(App(Id("n"), Id("f")), Id("x")))))))

MULT = Lambda(Id("m"), Lambda(Id("n"), Lambda(Id("f"), App(Id("m"), App(Id("n"), Id("f"))))))

PRED = parse(r"\n.\f.\x. n (\g.\h. h (g f)) (\u. x) (\u. u)")

SUB = Lambda(Id("m"), Lambda(Id("n"), App(App(Id("n"), PRED), Id("m"))))

ISZERO = Lambda(Id("n"), App(App(Id("n"), Lambda(Id("x"), FALSE)), TRUE))

LEQ = Lambda(Id("m"), Lambda(Id("n"), App(ISZERO, App(App(SUB, Id("m")), Id("n")))))

Y = parse(r"\f.(\x.f (x x)) (\x.f (x x))")

# excercise 3

# GCD = Y (λg.λa.λb.
#   IF (ISZERO b)
#     a
#     (g b (MOD a b))
# )

MOD = parse(r"""
\f.\a.\b.
  IF (LEQ b a)
    (f (SUB a b) b)
    a
""")

GCD_BODY = Lambda(Id("g"), Lambda(Id("a"), Lambda(Id("b"),
    App(App(App(IF, App(ISZERO, Id("b"))),
        Id("a")),
        App(App(Id("g"), Id("b")), App(App(MOD, Id("a")), Id("b"))))
)))

GCD = App(Y, GCD_BODY)


