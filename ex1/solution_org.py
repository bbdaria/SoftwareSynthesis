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


Env = Dict[str, LambdaType]
Equations = List[Tuple[LambdaType, LambdaType]]
Substitution = Dict[TypeVar, LambdaType]


def collect_constraints(expr: TypedExpr, env: Env, equations: Equations) -> TypedExpr:
    """Recursively generates type constraints from a typed lambda expression."""
    match expr.expr:
        case Id(name):
            if name in env:
                return TypedExpr(Id(name), env[name])
            else:
                raise InsufficientAnnotationsError(f"Unbound variable: {name}")

        case Int(_):
            return TypedExpr(expr.expr, Primitive.INT)

        case Bool(_):
            return TypedExpr(expr.expr, Primitive.BOOL)

        case Lambda(param_decl, body_expr, return_type_hint):
            if not param_decl.type:
                raise InsufficientAnnotationsError("Lambda parameter type annotation is missing.")
            param_type = param_decl.type
            new_env = env.copy()
            new_env[param_decl.var.name] = param_type
            typed_body = collect_constraints(body_expr, new_env, equations)
            result_type = Arrow(param_type, typed_body.type)
            if return_type_hint is not None:
                equations.append((return_type_hint, typed_body.type))
            return TypedExpr(Lambda(VarDecl(param_decl.var, param_type), typed_body, return_type_hint), result_type)

        case App(func_expr, arg_expr):
            typed_func = collect_constraints(func_expr, env, equations)
            typed_arg = collect_constraints(arg_expr, env, equations)
            result_type = fresh_typevar()
            equations.append((typed_func.type, Arrow(typed_arg.type, result_type)))
            return TypedExpr(App(typed_func, typed_arg), result_type)

        case Let(var_decl, defn_expr, body_expr):
            typed_defn = collect_constraints(defn_expr, env, equations)
            inferred_type = var_decl.type or typed_defn.type
            if var_decl.type:
                equations.append((var_decl.type, typed_defn.type))
            extended_env = env.copy()
            extended_env[var_decl.var.name] = inferred_type
            typed_body = collect_constraints(body_expr, extended_env, equations)
            return TypedExpr(Let(VarDecl(var_decl.var, inferred_type), typed_defn, typed_body), typed_body.type)

        case _:
            raise TypeMismatchError(f"Unsupported expression: {expr.expr}")


def unify_constraints(equations: Equations) -> Substitution:
    """Solves type constraints by unifying types, returning a substitution."""
    substitution: Substitution = {}

    def resolve(t: LambdaType) -> LambdaType:
        """Resolves a type variable to its substituted form, if it exists."""
        while isinstance(t, TypeVar) and t in substitution:
            t = substitution[t]
        return t

    def occurs_in(var: TypeVar, typ: LambdaType) -> bool:
        """Checks if var occurs in typ (occurs check)."""
        if var == typ:
            return True
        if isinstance(typ, Arrow):
            return occurs_in(var, typ.arg) or occurs_in(var, typ.ret)
        return False

    while equations:
        lhs, rhs = equations.pop()
        lhs, rhs = resolve(lhs), resolve(rhs)

        match (lhs, rhs):
            case _ if lhs == rhs:
                continue
            case (TypeVar() as var, typ):
                if occurs_in(var, typ):
                    raise TypeMismatchError(f"Occurs check failed: {var} in {typ}")
                substitution[var] = typ
            case (typ, TypeVar() as var):
                if occurs_in(var, typ):
                    raise TypeMismatchError(f"Occurs check failed: {var} in {typ}")
                substitution[var] = typ
            case (Arrow(arg1, ret1), Arrow(arg2, ret2)):
                equations.append((arg1, arg2))
                equations.append((ret1, ret2))
            case (Primitive() as prim1, Primitive() as prim2) if prim1 == prim2:
                continue
            case _:
                raise TypeMismatchError(f"Cannot unify: {lhs} vs {rhs}")
    return substitution


def apply_substitution_to_type(typ: LambdaType, substitution: Substitution) -> LambdaType:
    """Recursively applies type substitutions to a LambdaType."""
    match typ:
        case TypeVar(_) if typ in substitution:
            return apply_substitution_to_type(substitution[typ], substitution)
        case Arrow(arg_type, ret_type):
            return Arrow(
                apply_substitution_to_type(arg_type, substitution),
                apply_substitution_to_type(ret_type, substitution)
            )
        case _:
            return typ


def apply_substitution_to_expr(expr: TypedExpr, substitution: Substitution) -> TypedExpr:
    """Recursively applies a substitution to all types in an expression."""
    resolved_type = apply_substitution_to_type(expr.type, substitution)

    match expr.expr:
        case Id(_) | Int(_) | Bool(_):
            return TypedExpr(expr.expr, resolved_type)

        case Lambda(param_decl, body, ret_hint):
            new_param_type = apply_substitution_to_type(param_decl.type, substitution)
            new_ret_hint = (
                apply_substitution_to_type(ret_hint, substitution) if ret_hint is not None else None
            )
            new_body = apply_substitution_to_expr(body, substitution)
            return TypedExpr(
                Lambda(VarDecl(param_decl.var, new_param_type), new_body, new_ret_hint),
                resolved_type
            )

        case App(func, arg):
            return TypedExpr(
                App(
                    apply_substitution_to_expr(func, substitution),
                    apply_substitution_to_expr(arg, substitution)
                ),
                resolved_type
            )

        case Let(var_decl, defn, body):
            new_decl_type = apply_substitution_to_type(var_decl.type, substitution)
            new_defn = apply_substitution_to_expr(defn, substitution)
            new_body = apply_substitution_to_expr(body, substitution)
            return TypedExpr(
                Let(VarDecl(var_decl.var, new_decl_type), new_defn, new_body),
                resolved_type
            )

        case _:
            raise TypeMismatchError(f"Unsupported expression in substitution: {expr.expr}")


def infer_types(expr: TypedExpr) -> TypedExpr:
    """
    Input: an expression with ungrounded type variables (t.is_internal()).
    Output: An ast with all the types explicitly inferred.
     * If encountered a unification error, raise TypeMismatchError
     * If some types cannot be inferred, raise InsufficientAnnotationsError
    """
    assert is_grounded_expr(expr, require_fully_annotated=False)

    equations: Equations = []
    t_expr, constraints = collect_constraints(expr, equations)
    print(f'constraints: {constraints}')
    subst = unify_constraints(constraints)
    print(f'subst: {subst}')
    result = apply_substitution_to_expr(TypedExpr(expr.expr, t_expr), subst)
    # result = annotate(expr, subst)
    # assert is_grounded_expr(result, require_fully_annotated=True)
    return result


def main() -> None:
    expr = parse(r"""\(x : int). \(x : bool). (\(x : int). x)""")
    print(f"{expr!r}")
    print(f"{expr}")
    print(infer_types(expr))


if __name__ == "__main__":
    main()
