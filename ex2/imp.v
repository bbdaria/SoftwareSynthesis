Set Implicit Arguments.


Inductive var := a | b | n | x | y.

Definition op := nat -> nat -> nat.
  
Inductive expr :=
  expr_var : var -> expr
| expr_num : nat -> expr
| expr_op : expr -> op -> expr -> expr.

Inductive cmd :=
  assign : var -> expr -> cmd
| seq : cmd -> cmd -> cmd
| skip : cmd
| if_then_else : expr -> cmd -> cmd -> cmd
| while : expr -> cmd -> cmd
| assume : expr -> cmd.

Definition state := var -> nat.

Fixpoint sem (e : expr) (s : state) :=
  match e with
  | expr_var v => s v
  | expr_num m => m
  | expr_op e1 op e2 => op (sem e1 s) (sem e2 s)
  end.


(* -- Defining the program `euclid` in IMP -- *)
Require Import Arith.
Require Import Lia.
Import Nat.

(* some operators *)
Definition gt01 n m := if gt_dec n m then 1 else 0.
Definition ne01 n m := if eq_dec n m then 0 else 1.

(* This notation will shorten things a bit *)
Notation "$ v" := (expr_var v) (at level 7, format "$ v").

Definition euclid_body :=
    seq (assume (expr_op $a ne01 $b))
        (if_then_else (expr_op $a gt01 $b)
                      (assign a (expr_op $a sub $b))
                      (assign b (expr_op $b sub $a))).

(* copy pasted GCD definition from euclid.v - Nat does not work here *)
Inductive gcd : nat -> nat -> nat -> Prop :=
  base   : forall z, gcd z z z
| step_a : forall a b z, gcd a b z -> gcd (a + b) b z
| step_b : forall a b z, gcd a b z -> gcd a (a + b) z.

(* copy pasted the tc tc' definitions *)
Section ReflexiveTransitiveClosureAltDef.

  Variable D : Set.
  Variable R : D -> D -> Prop.

  Inductive tc' : D -> D -> Prop :=
    tc'_refl : forall s, tc' s s
  | tc'_step : forall s u t, R s u -> tc' u t -> tc' s t.

End ReflexiveTransitiveClosureAltDef.

Section ReflexiveTransitiveClosureDef.

  Variable D : Set.
  Variable R : D -> D -> Prop.

  Inductive tc : D -> D -> Prop :=
    tc_refl : forall s, tc s s
  | tc_step : forall s u t, tc s u -> R u t -> tc s t.

End ReflexiveTransitiveClosureDef.

Definition eq_var_dec : forall (v1 v2 : var), {v1 = v2} + {v1 <> v2}.
Proof. decide equality. Qed.

Definition update (st : state) (v : var) (n : nat) : state :=
  fun x => if eq_var_dec x v then n else st x.

Inductive sos : (state * cmd) -> (state * cmd) -> Prop := 
  | step_seq : forall st c1 st' c1' c2, 
    sos (st, c1) (st', c1') -> sos (st, seq c1 c2) (st', seq c1' c2)
  | step_seq_skip : forall st c2, 
    sos (st, seq skip c2) (st, c2)
  | step_assign : forall st v e, 
    sos (st, assign v e) (update st v (sem e st), skip)
  | step_if_true : forall st e c1 c2, 
    sem e st <> 0 -> sos (st, if_then_else e c1 c2) (st, c1)
  | step_if_false : forall st e c1 c2, 
    sem e st = 0 -> sos (st, if_then_else e c1 c2) (st, c2)
  | step_while_true : forall st e c, 
    sem e st <> 0 -> sos (st, while e c) (st, seq c (while e c))
  | step_while_false : forall st e c, 
    sem e st = 0 -> sos (st, while e c) (st, skip)
  | step_assume_true : forall st e, 
    sem e st <> 0 -> sos (st, assume e) (st, skip).
 
Inductive step : state -> state -> Prop := 
  | cons : forall st st', sos (st, euclid_body) (st', skip) -> step st st'.
  
Lemma Q4 : forall a0 b0 s s', s a = a0 -> s b = b0 -> tc' step s s' -> s' a = s' b -> gcd a0 b0 (s' a).
Proof.
  intros a0 b0 s s' Ha0 Hb0 Hstepss Hskip.
  induction Hstepss.
  - assert (Heq : a0 = b0) by lia.
    rewrite Ha0.
    rewrite Heq.
    apply base.
  - inversion H.
    inversion H0.
Qed.