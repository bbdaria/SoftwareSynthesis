"""
Homework 1

Your task:
Implement type checking and type inference for simply-typed lambda calculus.
"""

from syntax.lambda_typed import  *
from typing import Dict, List, Tuple


class TypeMismatchError(TypeError):
    pass


class InsufficientAnnotationsError(TypeError):
    pass

type Context = Dict[str, LambdaType]
type Substitution = Dict[int, LambdaType]

def fresh_var() -> TypeVar:
    return fresh_typevar()  # Provided in lambda_typed.py

def generate_constraints(expr: TypedExpr, ctx: Context) -> Tuple[LambdaType, List[Tuple[LambdaType, LambdaType]]]:
    match expr.expr:
        case Id(name):
            if name not in ctx:
                raise InsufficientAnnotationsError(f"Unbound variable: {name}")
            return ctx[name], []

        case Int(_):
            return Primitive.INT, []

        case Bool():
            return Primitive.BOOL, []

        case Lambda(decl, body, _):
            arg_type = decl.type
            ctx1 = ctx.copy()
            ctx1[decl.var.name] = arg_type
            body_type, c_body = generate_constraints(body, ctx1)
            return Arrow(arg_type, body_type), c_body

        case App(func, arg):
            tf, c_func = generate_constraints(func, ctx)
            ta, c_arg = generate_constraints(arg, ctx)
            fres = fresh_var()
            return fres, c_func + c_arg + [(tf, Arrow(ta, fres))]

        case Let(decl, defn, body):
            t_defn, c_defn = generate_constraints(defn, ctx)
            ctx1 = ctx.copy()
            ctx1[decl.var.name] = t_defn
            t_body, c_body = generate_constraints(body, ctx1)
            return t_body, c_defn + c_body

def unify(constraints: List[Tuple[LambdaType, LambdaType]]) -> Substitution:
    subst: Substitution = {}

    def apply_subst(t: LambdaType) -> LambdaType:
        match t:
            case TypeVar(id) if id in subst:
                return apply_subst(subst[id])
            case Arrow(l, r):
                return Arrow(apply_subst(l), apply_subst(r))
            case _:
                return t

    def unify_one(t1: LambdaType, t2: LambdaType):
        t1 = apply_subst(t1)
        t2 = apply_subst(t2)

        match (t1, t2):
            case (TypeVar(id1), _) if t1 != t2:
                if occurs(id1, t2):
                    raise TypeMismatchError(f"Occurs check failed: {id1} in {t2}")
                subst[id1] = t2
            case (_, TypeVar(id2)):
                unify_one(t2, t1)
            case (Primitive() as p1, Primitive() as p2):
                if p1 != p2:
                    raise TypeMismatchError(f"Type mismatch: {p1} != {p2}")
            case (Arrow(a1, b1), Arrow(a2, b2)):
                unify_one(a1, a2)
                unify_one(b1, b2)
            case _:
                raise TypeMismatchError(f"Cannot unify: {t1} vs {t2}")

    def occurs(var_id: int, typ: LambdaType) -> bool:
        match typ:
            case TypeVar(id):
                return var_id == id
            case Arrow(left, right):
                return occurs(var_id, left) or occurs(var_id, right)
            case _:
                return False

    for t1, t2 in constraints:
        unify_one(t1, t2)

    return subst

def apply_substitution(t: LambdaType, subst: Substitution) -> LambdaType:
    match t:
        case TypeVar(id):
            if id in subst:
                replacement = subst[id]
                if replacement == t:  # avoid self-reference loop
                    return t
                return apply_substitution(replacement, subst)
            return t
        case Arrow(a, b):
            return Arrow(apply_substitution(a, subst), apply_substitution(b, subst))
        case _:
            return t

def annotate(expr: TypedExpr, subst: Substitution) -> TypedExpr:
    new_type = apply_substitution(expr.type, subst)
    match expr.expr:
        case Id(_):
            return TypedExpr(expr.expr, new_type)
        case Int(_) | Bool():
            return TypedExpr(expr.expr, new_type)
        case App(func, arg):
            func_anno = annotate(func, subst)
            arg_anno = annotate(arg, subst)
            return TypedExpr(App(func_anno, arg_anno), new_type)
        case Lambda(decl, body, _):
            decl_type = apply_substitution(decl.type, subst)
            decl_anno = VarDecl(decl.var, decl_type)
            body_anno = annotate(body, subst)
            return TypedExpr(Lambda(decl_anno, body_anno, apply_substitution(new_type.ret, subst)), apply_substitution(new_type, subst))
        case Let(decl, defn, body):
            decl_type = apply_substitution(decl.type, subst)
            decl_anno = VarDecl(decl.var, decl_type)
            defn_anno = annotate(defn, subst)
            body_anno = annotate(body, subst)
            return TypedExpr(Let(decl_anno, defn_anno, body_anno), new_type)
        case _:
            raise TypeMismatchError(f"Cannot annotate: {expr.expr}")


def infer_types(expr: TypedExpr) -> TypedExpr:
    """
    Input: an expression with ungrounded type variables (t.is_internal()).
    Output: An ast with all the types explicitly inferred.
     * If encountered a unification error, raise TypeMismatchError
     * If some types cannot be inferred, raise InsufficientAnnotationsError
    """
    assert is_grounded_expr(expr, require_fully_annotated=False)

    ctx: Context = {}
    t_expr, constraints = generate_constraints(expr, ctx)
    subst = unify(constraints)
    result = annotate(TypedExpr(expr.expr, t_expr), subst)
    # assert is_grounded_expr(result, require_fully_annotated=True)
    return result


def main() -> None:
    expr = parse(r"""\x : int. x""")
    print(f"{expr!r}")
    print(f"{expr}")
    print(infer_types(expr))


if __name__ == "__main__":
    main()
