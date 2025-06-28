Set Implicit Arguments.

Require Import Arith.
Import Nat.

(*
 * M:
 * 1	c = 1 
 * 2  while c > 0 
 * 3    if n > 100 
 * 4      n := n – 10 
 * 5      c := c – 1 
 * 6    else
 * 7      n := n + 11 
 * 8      c := c + 1 
 * 9  return n
 *)

Definition state : Set := nat * nat.  (* n, c *)

Inductive step : state -> state -> Prop :=
  step_hi : forall n c, c > 0 -> n > 100 -> step (n, c) (n - 10, c - 1)
| step_lo : forall n c, c > 0 -> n <= 100 -> step (n, c) (n + 11, c + 1).

(* = Loop Invariant = *)
Definition inv s :=
  match s with
    (n, c) => n <= c * 10 + 91
  end.

(* Useful arithmetic lemmas from the standard library *)
Check le_add_r.
Check sub_le_mono_r.
Check add_sub_swap.
Check add_comm.
Check mul_succ_l.
Check mul_sub_distr_r.

Require Import Lia.

Lemma preserves s1 s2 : inv s1 -> step s1 s2 -> inv s2.
Proof.
  intros Before Step.
  destruct s1 as [n c].
  simpl in Before.
  inversion Step; subst; simpl.
  - lia.
  - lia.
Qed.

(*
 * Now we prove that the invariant holds for all reachable 
 * states.
 *)
Section ReflexiveTransitiveClosureDef.

  Variable D : Set.
  Variable R : D -> D -> Prop.

  Inductive tc : D -> D -> Prop :=
    tc_refl : forall s, tc s s
  | tc_step : forall s u t, R s u -> tc u t -> tc s t.

End ReflexiveTransitiveClosureDef.
                                              

Lemma inv_tc s1 s2 : inv s1 -> tc step s1 s2 -> inv s2.
Proof.
  intros Before TcStep.
  induction TcStep.
  - exact Before.
  - apply IHTcStep.
    apply (preserves Before H); assumption.
Qed.

Theorem mccarthy91 n n' : n <= 101 ->
                          tc step (n, 1) (n', 0) ->
                          n' <= 91.
Proof.
   intros Hle Htc.
   assert (inv (n, 1)).
   {
     unfold inv. 
     lia.
   }
   apply (inv_tc H Htc).
Qed.

(*
 * Bonus: prove that n' >= 91 as well.
 *)
