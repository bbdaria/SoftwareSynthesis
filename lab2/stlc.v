Definition native_bool := bool.


Inductive Var : Set := x | y | z.

Inductive TyBase : Set := int | bool.

Inductive Ty : Set :=
  | Base : TyBase -> Ty
  | Arrow : Ty -> Ty -> Ty.

Inductive Term : Set :=
  | TVar : Var -> Term
  | Abs : (Var * Ty) -> Term -> Term
  | App : Term -> Term -> Term.

(* Equality *)
Definition eq_var v1 v2 := match v1, v2 with
  | x, x => true  | y, y => true  | z, z => true
  | _, _ => false 
end.

Definition eq_tybase t1 t2 := match t1, t2 with
  | int, int => true    | bool, bool => true
  | _, _ => false
end.

Open Scope bool_scope.

Fixpoint eq_ty t1 t2 := match t1, t2 with
  | Base b1,
    Base b2         => eq_tybase b1 b2
  | Arrow t'1 s'1,
    Arrow t'2 s'2   => (eq_ty t'1 t'2) && (eq_ty s'1 s'2)
  | _, _ => false
end.


(* Syntax sugar *)
Notation "\ v : t , e" := (Abs (v, t) e)
  (at level 70, v at level 0, right associativity, only parsing).
Notation "'λ' v : t , e" := (Abs (v, t) e)
  (at level 70, v at level 0, right associativity, format "'λ' v  :  t ,  e").
Notation "e1 @ e2" := (App e1 e2) (at level 65).

Check \x : Base int , TVar y @ TVar z.
Check \x : Base int , (TVar y @ TVar z).
Check (\x : Base int , TVar y) @ TVar z.
Check TVar x @ \x : Base int, \y : Base bool, TVar y.


Definition Valuation := Var -> Ty.


Module Typecheck.

Inductive Result :=
  | Ok : Ty -> Result
  | Mismatch : Term -> Ty -> Ty -> Result
  | ExpectedArrow : Term -> Ty -> Result.

Definition extend_env (v : Var) (t : Ty) (env : Valuation) : Valuation :=
  fun v' => if eq_var v v' then t else env v'.
  
Fixpoint typecheck (e : Term) (env : Valuation): Result :=
  match e with 
    | TVar v => Ok (env v)
    | Abs (v, ty1) body => 
      match typecheck body (extend_env v ty1 env) with
      | Ok ty2 => Ok (Arrow ty1 ty2)
      | err => err
      end
    | App e1 e2 =>
      match typecheck e1 env with
      | Ok ty1 =>
          match ty1 with
          | Arrow ty_arg ty_res =>
              match typecheck e2 env with
              | Ok ty2 =>
                  if eq_ty ty2 ty_arg then Ok ty_res
                  else Mismatch e2 ty_arg ty2
              | err => err
              end
          | _ => ExpectedArrow e1 ty1
          end
      | err => err
      end
  end.


(* Examples *)

Definition env : Valuation := fun v => Base int.

Compute typecheck (\x : Base bool, TVar y @ TVar x) env.
(* ExpectedArrow (TVar y) (Base int) *)

Compute typecheck
  (\x : Arrow (Base bool) (Base int), TVar x @ TVar y) env.
(* Mismatch (TVar y) (Base bool) (Base int) *)

Compute typecheck
  (\x : Arrow (Base int) (Base bool), TVar x @ TVar y) env.
(* Ok (Arrow (Arrow (Base int) (Base bool)) (Base bool)) *)
(* ⟹   (int → bool) → bool  *)


End Typecheck.
