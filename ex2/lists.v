Set Implicit Arguments.
Require Import Lists.List.
Import ListNotations.

Print list.
Print rev.

(* Q1. Define is_sorted.  (returns a Prop.)  *)
Fixpoint is_sorted {A: Type} (l : list A) (R: A -> A -> Prop) : Prop :=
  match l with
  | x :: ((y :: _) as xs) => R x y /\ is_sorted xs R
  | _ => True
  end.


(* Q2. Show that this list is sorted. *)
Lemma warm_up : is_sorted [3;5;9] le.
  simpl.
  split.
  - apply le_S, le_S, le_n.
  - simpl. split. apply le_S, le_S, le_S, le_S, le_n.
  trivial.
Qed.


(* Q3. Prove that an ascending list of nat, when reversed, 
 *     becomes a descending list. *)

(* The following are utility definitions to simplify readability *)
Definition is_asc (l : list nat) := is_sorted l le.
Definition is_desc (l : list nat) := is_sorted l ge.

Lemma aux1 : forall (A : Set) (l : list A) R a b,
      is_sorted (l ++ [a]) R ->
      R a b ->
      is_sorted (l ++ [a;b]) R.
Proof.
  intros A l R a b Hsorted Hab.
  induction l as [| x xs IH].
  (* Case: l = [] *)
  - simpl. split; assumption.
  (* Case: l = x :: xs*)
  - simpl in *. destruct xs as [| y ys].
    (* Case: xs = [] -> l = [x]*)
    + simpl in *. simpl.
      destruct Hsorted as [Hxa _].
      split.
      * exact Hxa.
      * split.
        -- exact Hab.
        -- constructor.
    (* Case: xs = y :: ys *)
    + simpl in Hsorted.
      destruct Hsorted as [Hxy Hrest].
      simpl.
      split.
      * exact Hxy.
      * apply IH. exact Hrest.
Qed.

Definition le_ge := fun n m (H: n <= m) => H : m >= n.

Lemma rev_cons : forall (A : Type) (x : A) (xs : list A),
  rev (x :: xs) = rev xs ++ [x].
Proof.
  intros. reflexivity.
Qed.


Theorem rev_asc_desc : forall (l: list nat), is_asc l -> is_desc (rev l).
Proof.
  intros l Hasc.
  induction l as [| x xs IH].
  - simpl. constructor.
  - simpl in *. simpl in Hasc.
    destruct xs as [| y ys].
    + simpl. constructor.
    + simpl in Hasc. 
      destruct Hasc as [Hxy Hsorted].
      rewrite rev_cons.
      rewrite <- app_assoc.
      apply (@aux1 nat (rev ys) ge y x).
      * apply IH. exact Hsorted.
      * apply le_ge. exact Hxy.
Qed.

