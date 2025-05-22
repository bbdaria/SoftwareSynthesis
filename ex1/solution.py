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

        case Lambda(decl, body, ret):
            # 1. Handle declaration type
            arg_type = decl.type
            
            # 2. Create new context with argument type
            ctx1 = ctx.copy()
            ctx1[decl.var.name] = arg_type
            
            # 3. Generate constraints for body
            body_type, c_body = generate_constraints(body, ctx1)
            
            # 4. Handle return type
            if ret and not (isinstance(ret, TypeVar) and ret.is_internal()):
                c_body.append((body_type, ret))
            
            # 5. Create arrow type
            arrow_type = Arrow(arg_type, body_type)
            
            # 6. If expr has a type, add constraint
            if not (isinstance(expr.type, TypeVar) and expr.type.is_internal()):
                c_body.append((arrow_type, expr.type))
            
            return arrow_type, c_body

        case App(func, arg):
            # 1. Generate constraints for function and argument
            tf, c_func = generate_constraints(func, ctx)
            ta, c_arg = generate_constraints(arg, ctx)
            
            # 2. Create fresh variable for result
            fres = fresh_var()
            
            # 3. Add constraint that function type must be arrow type
            arrow_type = Arrow(ta, fres)
            c_app = [(tf, arrow_type)]
            
            # 4. If expression has a type, add constraint
            if not (isinstance(expr.type, TypeVar) and expr.type.is_internal()):
                c_app.append((fres, expr.type))
            
            return fres, c_func + c_arg + c_app

        case Let(decl, defn, body):
            # 1. Generate constraints for definition
            t_defn, c_defn = generate_constraints(defn, ctx)
            
            # 2. If declaration has explicit type, add constraint
            if decl.type and not (isinstance(decl.type, TypeVar) and decl.type.is_internal()):
                c_defn.append((t_defn, decl.type))
            
            # 3. Create new context with definition type
            ctx1 = ctx.copy()
            ctx1[decl.var.name] = t_defn
            
            # 4. Generate constraints for body
            t_body, c_body = generate_constraints(body, ctx1)
            
            # 5. If expression has a type, add constraint
            if not (isinstance(expr.type, TypeVar) and expr.type.is_internal()):
                c_body.append((t_body, expr.type))
            
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
            case (Primitive(), _) | (_, Primitive()):
                raise TypeMismatchError(f"Cannot unify primitive type with non-primitive: {t1} vs {t2}")
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
    """Apply substitutions to a type, ensuring all type variables are properly substituted."""
    def apply_recursive(typ: LambdaType, seen: set[int]) -> LambdaType:
        match typ:
            case TypeVar(id):
                if id in subst:
                    if id in seen:
                        # Avoid infinite recursion
                        return typ
                    seen.add(id)
                    return apply_recursive(subst[id], seen)
                return typ
            case Arrow(a, b):
                return Arrow(apply_recursive(a, seen.copy()), apply_recursive(b, seen.copy()))
            case _:
                return typ

    return apply_recursive(t, set())

def annotate(expr: TypedExpr, subst: Substitution) -> TypedExpr:
    """Annotate an expression with types, applying substitutions to all type variables."""
    new_type = apply_substitution(expr.type, subst)
    match expr.expr:
        case Id(_):
            return TypedExpr(expr.expr, new_type)
        case Int(_):
            return TypedExpr(expr.expr, Primitive.INT)
        case Bool():
            return TypedExpr(expr.expr, Primitive.BOOL)
        case App(func, arg):
            func_anno = annotate(func, subst)
            arg_anno = annotate(arg, subst)
            # The result type should be the return type of the function
            match func_anno.type:
                case Arrow(_, ret_type):
                    return TypedExpr(App(func_anno, arg_anno), ret_type)
                case _:
                    raise TypeMismatchError(f"Expected function type, got {func_anno.type}")
        case Lambda(decl, body, _):
            decl_type = apply_substitution(decl.type, subst)
            decl_anno = VarDecl(decl.var, decl_type)
            body_anno = annotate(body, subst)
            # Create arrow type from declaration type to body type
            arrow_type = Arrow(decl_type, body_anno.type)
            return TypedExpr(Lambda(decl_anno, body_anno, body_anno.type), arrow_type)
        case Let(decl, defn, body):
            decl_type = apply_substitution(decl.type, subst)
            decl_anno = VarDecl(decl.var, decl_type)
            defn_anno = annotate(defn, subst)
            body_anno = annotate(body, subst)
            return TypedExpr(Let(decl_anno, defn_anno, body_anno), body_anno.type)
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

    # 1. Generate constraints from the expression
    ctx: Context = {}
    t_expr, constraints = generate_constraints(expr, ctx)

    # 2. Unify the constraints to get substitutions
    subst = unify(constraints)

    # 3. Apply the substitutions to get the final typed expression
    result = annotate(TypedExpr(expr.expr, t_expr), subst)

    # 4. Verify the result is fully annotated
    assert is_grounded_expr(result, require_fully_annotated=True)
    return result

def main() -> None:
    expr = parse(r"""\x : int. x""")
    print(f"{expr!r}")
    print(f"{expr}")
    print(infer_types(expr))


if __name__ == "__main__":
    main()
