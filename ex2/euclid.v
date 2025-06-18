Require Import Arith.Arith.
Import Nat.
Require Import Lia.


(* -- this is the simplified version of Euclid we saw in class -- *)
Inductive gcd : nat -> nat -> nat -> Prop :=
  base   : forall z, gcd z z z
| step_a : forall a b z, gcd a b z -> gcd (a + b) b z
| step_b : forall a b z, gcd a b z -> gcd a (a + b) z.


(* -- This is a more accurate description of Euclid's algorithm -- *)
(*
   def euclid(a, b):                 # (Python equivalent)
     if a == b: return a
     elif a > b: return euclid(a - b, b)
     elif a < b: return euclid(a, b - a)
*)
Inductive euclid : nat -> nat -> nat -> Prop :=
  stop    : forall z, euclid z z z
| step_a' : forall a b z, a > b -> euclid (a - b) b z -> euclid a b z
| step_b' : forall a b z, a < b -> euclid a (b - a) z -> euclid a b z.  


Search "+" "-".   (* remember to use Search to find lemmas *)

Lemma add_sub_cancel_l : forall a b,
  a <= b -> a + (b - a) = b.
Proof.
  intros. lia.
Qed.

Theorem euclid_gcd : forall a b z, euclid a b z -> gcd a b z.
Proof.
  intros a b z H.
  induction H.
  - apply base.
  - assert (H1 : gcd ((a-b)+b) b z) by (apply step_a; exact IHeuclid).
    replace a with ((a-b)+b) by (apply Nat.sub_add; lia).
    exact H1.
  - assert (H1 : gcd a (a + (b-a)) z) by (apply step_b; exact IHeuclid).
    rewrite (add_sub_cancel_l a b) in H1 by lia.
    exact H1.
Qed.
