from typing import Union, Dict, List, Tuple
from multipledispatch import dispatch
from syntax.lambda_typed import (
    is_grounded_expr, fresh_typevar, TypedExpr, Arrow, Primitive, TypeVar,
    Id, Int, Bool, Lambda, App, Let, VarDecl, parse
)

class TypeMismatchError(TypeError):
    pass

class InsufficientAnnotationsError(TypeError):
    pass

type Type = Union[Primitive, Arrow, TypeVar] # Type is a primitive type, an arrow operator or a variable type
type Env = Dict[str, Type]
type Equations = List[Tuple[Type, Type]]     # the equations we solve are of the form: Type1 = Type2
type Substitution = Dict[TypeVar, Type]      # substitution map from the variable unknown type to the derived type

@dispatch(TypedExpr)
def generate_constraints(e: TypedExpr) -> Tuple[TypedExpr, Equations]:
    """
    A wrapper of generate_constraints(expr: TypedExpr, env: Env, equations: Equations)
    :param e: the AST expression tree
    :return: the constrained AST tree and the equations
    """
    equations: Equations = []
    env: Env = {}
    return generate_constraints(e, env, equations), equations


@dispatch(TypedExpr, dict, list)
def generate_constraints(expr: TypedExpr, env: Env, eqs: Equations) -> TypedExpr:
    """
    Generate the constraints for an expression using environment known variables
    :param expr: the AST expression tree
    :param env: the environment
    :param eqs: the equations
    :return: the constrained AST tree
    """

    # Generate the constraints using postorder over the AST
    match expr.expr:
        # leaf node reached
        case Int():
            return TypedExpr(expr.expr, Primitive.INT)
        case Bool():
            return TypedExpr(expr.expr, Primitive.BOOL)
        case Id(name):
            if name in env:
                return TypedExpr(Id(name), env[name])
            raise InsufficientAnnotationsError

        # continue recursively
        case Lambda(v_decl, body, ret_t):
            if not v_decl.type:
                raise InsufficientAnnotationsError

            param_type = v_decl.type
            new_env = env.copy()
            new_env[v_decl.var.name] = param_type
            typed_body = generate_constraints(body, new_env, eqs)

            if ret_t:
                eqs.append((ret_t, typed_body.type))
            return TypedExpr(
                expr=Lambda(VarDecl(v_decl.var, param_type), typed_body, ret_t),
                type=Arrow(param_type, typed_body.type)
            )
        case App(func, arg):
            # generate the constraints for the argument and the
            typed_func = generate_constraints(func, env, eqs)
            typed_arg = generate_constraints(arg, env, eqs)

            result_type = fresh_typevar()
            eqs.append((typed_func.type, Arrow(typed_arg.type, result_type)))
            return TypedExpr(
                expr=App(typed_func, typed_arg),
                type=result_type
            )
        case Let(v_decl, defn, body):
            typed_defn = generate_constraints(defn, env, eqs)
            var_type = v_decl.type or typed_defn.type

            if v_decl.type:
                eqs.append((v_decl.type, typed_defn.type))
            new_env = env.copy()
            new_env[v_decl.var.name] = var_type
            typed_body = generate_constraints(body, new_env, eqs)
            return TypedExpr(
                Let(
                    decl=VarDecl(v_decl.var, var_type),
                    defn=typed_defn,
                    body=typed_body
                ), typed_body.type
            )
        case _:
            raise TypeMismatchError


def unify_all(equations: Equations) -> Substitution:
    """
    Solve the equations and generate substitution mapping
    :param equations: the equations to solve
    :return: the substitution mapping
    """
    substitution: Substitution = {}

    def occurs(var_typ: TypeVar, typ: Type) -> bool:
        # Checks if var_typ (the temp placeholder) is found in typ
        if var_typ == typ:
            return True
        return occurs(var_typ, typ.arg) or occurs(var_typ, typ.ret) if isinstance(typ, Arrow) else False

    def find(typ: Type) -> Type:
        # Try to find the "end" type of typ in each iteration.
        while isinstance(typ, TypeVar) and (typ in substitution):
            typ = substitution[typ]
        return typ

    while equations:
        a, b = equations.pop()
        a, b = find(a), find(b)

        match a, b:
            case _ if a == b:
                continue
            case (Primitive() as p1, Primitive() as p2) if p1 == p2:
                continue
            case Arrow(arg1, ret1), Arrow(arg2, ret2):
                equations.append((arg1, arg2))
                equations.append((ret1, ret2))
            case TypeVar() as var_type, typ:
                if occurs(var_type, typ):
                    raise TypeMismatchError
                substitution[var_type] = typ
            case typ, TypeVar() as var_type:
                if occurs(var_type, typ):
                    raise TypeMismatchError
                substitution[var_type] = typ
            case _:
                raise TypeMismatchError
    return substitution

def substitute_expression(expr: TypedExpr, substitution: Substitution) -> TypedExpr:
    """
    Substitute in the expression using the mapping
    :param expr: the expression to substitute
    :param substitution: the mapping
    :return: the substituted expression in a new AST
    """
    def subst_type(typ: Type, subst: Substitution) -> Type:
        match typ:
            case Arrow():
                return Arrow(subst_type(typ.arg, subst), subst_type(typ.ret, subst))
            case TypeVar():
                return subst_type(subst[typ], subst) if typ in subst else typ
            case _:
                return typ

    # use the substitution mapping to recursively reconstruct the type of each node in the AST
    typ = subst_type(expr.type, substitution)
    match expr.expr:
        case Id() | Int() | Bool() as expr_inner:
            # type is immediate
            return TypedExpr(expr_inner, typ)
        case App(func, arg):
            return TypedExpr(
                expr=App(substitute_expression(func, substitution), substitute_expression(arg, substitution)),
                type=typ
            )
        case Lambda(decl, body, ret):
            return TypedExpr(
                expr=Lambda(
                    decl=VarDecl(decl.var, subst_type(decl.type, substitution)),
                    body=substitute_expression(body, substitution),
                    ret=subst_type(ret, substitution) if ret else None
                ),
                type=typ
            )
        case Let(decl, defn, body):
            return TypedExpr(
                expr=Let(
                    decl=VarDecl(decl.var, subst_type(decl.type, substitution)),
                    defn=substitute_expression(defn, substitution),
                    body=substitute_expression(body, substitution)
                ),
                type=typ
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

    typed, equations = generate_constraints(expr)
    subst = unify_all(equations)
    result = substitute_expression(typed, subst)

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
