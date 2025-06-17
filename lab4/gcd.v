Set Implicit Arguments.

Require Import Arith.Arith.
Import Nat.

(* ----------------------------------------------------------------- *)
(* Let's start by proving some basic facts about natural numbers.    *)

(* this one is going to come in handy *)
Theorem f_equal : forall A B (f : A -> B) x y, x = y -> f x = f y.
Proof.
  intros. rewrite H. reflexivity.  (* First one's free. *)
Qed.                               (* Try to understand it though! *)

(* notice that "+" is not defined symmetrically! *)
Print Nat.add.
Eval simpl in fun x => 1 + x.
Eval simpl in fun x => x + 1.

Lemma plus_one : forall x, x + 1 = S x.
Proof.
  intro x.
  induction x.
  - reflexivity.
  - simpl. rewrite IHx. reflexivity.
Qed.

Lemma plus_one' : forall x y, x + S y = S x + y.
Proof.
  intros x y.
  induction x.
  - simpl. reflexivity.
  - simpl. rewrite IHx. reflexivity.
Qed.

(* Definition of divisibility + some syntactic sugar *)
Definition divides a b := exists k, a * k = b.
Notation "( a | b )" := (divides a b).

(* commutativity lemmas. we're about to need them. *)
Check Nat.add_comm.
Check Nat.mul_comm.
  
Lemma divides_refl : forall n, (n | n).
Proof.
  intros n.
  exists 1.
  simpl. rewrite Nat.mul_1_r.
  reflexivity.
Qed.



(* ----------------------------------------------------------------- *)
(* Armed with these lemmas, let's try to define the Greatest Common  *)
(* Denominator and Euclid's algorithm.                               *)

Section Gcd.

  Definition is_gcd (a b z : nat) :=
    (z | a) /\ (z | b) /\ forall z', (z' | a) -> (z' | b) -> (z' | z).  

  (* First some basic properties of gcd *)
  Theorem is_gcd_refl : forall z, is_gcd z z z.
  Proof.
    intros z.
    split.
    - exists 1. apply Nat.mul_1_r.
    - split.
      + exists 1. apply Nat.mul_1_r.
      + intros z' [k1 H1] [k2 H2].
        (* Goal: ∃k, z' * k = z *)
        (* From H1: z' * k1 = z *)
        exists k1. exact H1.
  Qed.


  Theorem is_gcd_comm : forall a b z, is_gcd a b z -> is_gcd b a z.
  Proof.
    intros a b z [H1 [H2 H3]].
    split; [assumption | split; [assumption |]].
    intros z' D1 D2.
    apply H3; assumption.
  Qed.

  
  (* -- this is a simplified version of Euclid -- *)
  Inductive gcd : nat -> nat -> nat -> Prop :=
    base : (forall z, gcd z z z)
  | step_a : forall a b z, gcd a b z -> gcd (a + b) b z
  | step_b : forall a b z, gcd a b z -> gcd a (a + b) z.

  
  (* distributivity lemmas. you will need them too! *)
  Check Nat.mul_add_distr_l.
  Check Nat.mul_sub_distr_l.

  Search (_ * (_ + _)).       (* this is how you could find them yourself *)
  Search (_ * (_ - _)).       (* if I hadn't told you *)

  Lemma gcd_step_aux : forall a b z, is_gcd a b z -> is_gcd (a + b) b z.
  Proof.
      intros.
      unfold is_gcd.
      destruct H.
      destruct H0.
      repeat split.
      - destruct H.
        destruct H0.
        exists (x + x0).
        rewrite Nat.mul_add_distr_l.
        rewrite H.
        rewrite H0.
        reflexivity.
      - assumption.
      - intros.
        apply H1.
        destruct H2.
        destruct H3.
        exists (x - x0).
        rewrite Nat.mul_sub_distr_l.
        rewrite H2.
        rewrite H3.
        rewrite add_sub.
        reflexivity.
        assumption.
  Qed.
  
  
 (*couldnt make this work, sorry uwu*)
  Theorem gcd_pcorrect : forall a b z, gcd a b z -> is_gcd a b z.
  Proof.
    intros a b z H.
    induction H.
    - apply is_gcd_refl.
    - apply gcd_step_aux. assumption.
    - apply is_gcd_comm.               
      apply gcd_step_aux.              
      apply is_gcd_comm.                
      assumption.                        
  Qed.


End Gcd.