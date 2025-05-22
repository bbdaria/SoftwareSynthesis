from typing import Optional, Union, Dict, List, Tuple, Any
from syntax.lambda_typed import (
    is_grounded_expr, fresh_typevar, TypedExpr, Arrow, Primitive, TypeVar,
    Id, Int, Bool, Lambda, App, Let, VarDecl, parse
)

class TypeMismatchError(TypeError):
    pass

class InsufficientAnnotationsError(TypeError):
    pass

Type = Union[Primitive, Arrow, TypeVar]
Env = Dict[str, Type]
Equations = List[Tuple[Type, Type]]
Substitution = Dict[TypeVar, Type]

def generate_constraints(e: TypedExpr, env: Env, equations: Equations) -> TypedExpr:
    match e.expr:
        case Id(name):
            if name in env:
                return TypedExpr(Id(name), env[name])
            else:
                raise InsufficientAnnotationsError
        case Int(_):
            return TypedExpr(e.expr, Primitive.INT)
        case Bool(_):
            return TypedExpr(e.expr, Primitive.BOOL)
        case Lambda(decl, body, ret):
            if not decl.type:
                raise InsufficientAnnotationsError
            param_type = decl.type
            new_env = env.copy()
            new_env[decl.var.name] = param_type
            typed_body = generate_constraints(body, new_env, equations)
            typ = Arrow(param_type, typed_body.type)
            if ret:
                equations.append((ret, typed_body.type))
            return TypedExpr(Lambda(VarDecl(decl.var, param_type), typed_body, ret), typ)
        case App(func, arg):
            typed_func = generate_constraints(func, env, equations)
            typed_arg = generate_constraints(arg, env, equations)
            result_type = fresh_typevar()
            equations.append((typed_func.type, Arrow(typed_arg.type, result_type)))
            return TypedExpr(App(typed_func, typed_arg), result_type)
        case Let(decl, defn, body):
            typed_defn = generate_constraints(defn, env, equations)
            var_type = decl.type or typed_defn.type
            if decl.type:
                equations.append((decl.type, typed_defn.type))
            new_env = env.copy()
            new_env[decl.var.name] = var_type
            typed_body = generate_constraints(body, new_env, equations)
            return TypedExpr(Let(VarDecl(decl.var, var_type), typed_defn, typed_body), typed_body.type)
        case _:
            raise TypeMismatchError

def unify_all(equations: Equations) -> Substitution:
    substitution: Substitution = {}

    def find(t: Type) -> Type:
        while isinstance(t, TypeVar) and t in substitution:
            t = substitution[t]
        return t

    def occurs(tv: TypeVar, t: Type) -> bool:
        if tv == t:
            return True
        if isinstance(t, Arrow):
            return occurs(tv, t.arg) or occurs(tv, t.ret)
        return False

    while equations:
        a, b = equations.pop()
        a, b = find(a), find(b)

        match (a, b):
            case _ if a == b:
                continue
            case (TypeVar() as v, t):
                if occurs(v, t):
                    raise TypeMismatchError
                substitution[v] = t
            case (t, TypeVar() as v):
                if occurs(v, t):
                    raise TypeMismatchError
                substitution[v] = t
            case (Arrow(arg1, ret1), Arrow(arg2, ret2)):
                equations.append((arg1, arg2))
                equations.append((ret1, ret2))
            case (Primitive() as p1, Primitive() as p2) if p1 == p2:
                continue
            case _:
                raise TypeMismatchError
    return substitution

def subst_type(t: Type, subst: Substitution) -> Type:
    match t:
        case TypeVar():
            return subst_type(subst[t], subst) if t in subst else t
        case Arrow():
            return Arrow(subst_type(t.arg, subst), subst_type(t.ret, subst))
        case _:
            return t

def subst_expr(expr: TypedExpr, substitution: Substitution) -> TypedExpr:
    typ = subst_type(expr.type, substitution)
    match expr.expr:
        case Id(_) as expr_inner:
            return TypedExpr(expr_inner, typ)
        case Int(n) as expr_inner:
            return TypedExpr(expr_inner, typ)
        case Bool(b):
            return TypedExpr(Bool(b), typ)
        case Lambda(decl, body, ret):
            return TypedExpr(
                Lambda(
                    VarDecl(decl.var, subst_type(decl.type, substitution)),
                    subst_expr(body, substitution),
                    subst_type(ret, substitution) if ret is not None else None
                ),
                typ
            )
        case App(func, arg):
            return TypedExpr(
                App(subst_expr(func, substitution), subst_expr(arg, substitution)),
                typ
            )
        case Let(decl, defn, body):
            return TypedExpr(
                Let(
                    VarDecl(decl.var, subst_type(decl.type, substitution)),
                    subst_expr(defn, substitution),
                    subst_expr(body, substitution)
                ),
                typ
            )
        case _:
            raise TypeMismatchError



def infer_types(expr: TypedExpr) -> TypedExpr:
    """
    Input: an expression with ungrounded types (containing TypeVar types).
    Output: An ast with all the types explicitly inferred.
     * If encountered a unification error, raise TypeMismatchError
     * If some types cannot be inferred, raise InsufficientAnnotationsError
    """

    assert is_grounded_expr(expr, require_fully_annotated=False)
    equations = []

    typed = generate_constraints(expr, {}, equations)
    subst = unify_all(equations)
    result = subst_expr(typed, subst)

    if not is_grounded_expr(result, require_fully_annotated=True):
        raise InsufficientAnnotationsError

    return result 

def main() -> None:
    expr = parse(r"""\x: int. x""")
    print(f"{expr!r}")
    print(f"{expr}")
    print(infer_types(expr))


if __name__ == "__main__":
    main()
