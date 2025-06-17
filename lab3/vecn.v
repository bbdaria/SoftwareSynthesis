Set Implicit Arguments. (* Allows us to use inference for dependent arguments *)
Require Import Reals.   (* Imports real arithmetic. *)
Notation Real := R.        (* Notice: due to the absence of overloading, all       *)
Delimit Scope R_scope   (* numerical constants and operators are nat-typed,     *)
  with Real.               (* unless stated otherwise via the scope delimiter '%'. *)

Check 3 + 4.            (* : ℕ  (nat)  *)
Check (3 + 4) % Real.      (* : ℝ  (Real) *)


Inductive Vec : nat -> Set :=
  VNil : Vec 0
| VCons : forall n, Real -> Vec n -> Vec (S n).

(* Some syntactic sugar *)
Notation "<< x , .. , y >>" := (VCons x .. (VCons y VNil) .. ).

Check << 5, 9, 6 >> .


(* Q1: concat *)
Fixpoint concat {n m : nat} (v1 : Vec n) (v2 : Vec m) : Vec (n + m) :=
  match v1 with
  | VNil => v2
  | VCons x xs => VCons x (concat xs v2)
  end.


(* Q2: head *)
Definition head {n : nat} (v : Vec (S n)) : Real :=
  match v with
  | VCons x _ => x
  end.

(* For Q3 + Q4 *)

Fixpoint Vec' n : Set :=
  match n with
    0 => unit
  | S k => Real * Vec' k
  end.

(* Q3: vec_to_vec' *)
Fixpoint vec_to_vec' {n : nat} (v : Vec n) : Vec' n :=
  match v with
  | VNil => tt
  | VCons x xs => (x, vec_to_vec' xs)
  end.

(* Q4: inner product *)
Fixpoint inner_product' (n : nat) (v1 v2 : Vec' n) : Real :=
  match n return Vec' n -> Vec' n -> Real with
  | 0 => fun _ _ => 0%Real
  | S k => fun v1 v2 =>
      let (x1, t1) := v1 in
      let (x2, t2) := v2 in
      (x1 * x2 + inner_product' k t1 t2)%Real
  end v1 v2.

Definition inner_product {n : nat} (v1 v2 : Vec n) : Real :=
  inner_product' n (vec_to_vec' v1) (vec_to_vec' v2).

(* Q5: outer product *)
Fixpoint scale_vec {n : nat} (r : Real) (v : Vec n) : Vec n :=
  match v with
  | VNil => VNil
  | VCons x xs => VCons (r * x)%Real (scale_vec r xs)
  end.

Fixpoint outer_product {n m : nat} (v1 : Vec n) (v2 : Vec m) : list (Vec m) :=
  match v1 with
  | VNil => nil
  | VCons x xs => scale_vec x v2 :: outer_product xs v2
  end.
  