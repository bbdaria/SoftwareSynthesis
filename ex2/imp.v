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

  Inductive tc : D -> D -> Prop :=
    tc_refl : forall s, tc s s
  | tc_step : forall s u t, R s u -> tc u t -> tc s t.

End ReflexiveTransitiveClosureAltDef.


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
  | cons : forall st st', tc sos (st, euclid_body) (st', skip) -> step st st'.
  
Lemma alt_step: forall s u, step s u -> 
  (
      (s a < s b -> (u a = s a /\ u b = s b - s a)) 
      /\
      (s a > s b -> (u b = s b /\ u a = s a - s b))
  ). 
Proof.
  (* extract *)
  intros s u Hstep.
  inversion Hstep. subst.
  inversion H. subst.
  inversion H0. subst.
  inversion H6. subst.
  inversion H1. subst.
  inversion H2. subst.
  
  clear Hstep H H0 H6 H2 H4.
  rename H10 into H.
  
  inversion H. subst.
  rename H3 into Hneq.
  rename H4 into Hsos.
  clear H2 H1 H6 H0 Hstep H.
  
  inversion Hsos. subst.
  inversion H. subst.
  rename H6 into Hgt.
  rename H0 into Htcsos.
  clear H Hsos.
  
  - inversion Htcsos. subst.
    inversion H. subst.
    inversion H0. subst.
    clear H0 H Htcsos.
    + assert (st' a > st' b).
      {
        unfold sem in Hgt.
        unfold gt01 in Hgt.
        destruct gt_dec.
        - assumption.
        - contradiction.
      }
      
      firstorder.
      simpl in *.
      unfold ne01 in Hneq.
      unfold gt01 in Hgt.
      destruct eq_dec in Hneq.
      destruct gt_dec in Hgt.
      * lia.
      * lia. 
      * lia.
      * lia.
      * unfold update.
        destruct eq_var_dec as [a1 | a2].
        {
          simpl in *.
          unfold ne01 in Hneq.
          unfold gt01 in Hgt.
          destruct eq_dec in Hneq.
          destruct gt_dec in Hgt.
          { contradiction. }
          { contradiction. }
          { rewrite a1 in n0. contradiction. }
        }
        tauto.
      * unfold update.
        destruct eq_var_dec.
        { tauto. }
        exfalso.
        tauto.
    + clear H0 H H3 H4 Htcsos.
      rename H1 into Hsos.
      rename H2 into Htcsos.
      inversion Hsos.
  
  - subst.
    clear H Hsos.
    rename H0 into Htcsos.
    rename H6 into Hgt.
    inversion Htcsos. subst.
    inversion H. subst.
    inversion H0. subst.
    clear Htcsos H H0.
    + firstorder.
      * unfold update.
        unfold sem in *.
        unfold ne01 in Hneq.
        unfold gt01 in Hgt.
        destruct eq_dec in Hneq.
        destruct gt_dec in Hgt.
        { contradiction. }
        { contradiction. }
        {
          destruct gt_dec in Hgt.
          { contradiction. }
          {
            destruct eq_var_dec.
            { rewrite e in n0. contradiction. }
            { tauto. }
          }
        }
      * unfold update.
        destruct eq_var_dec.
        { tauto. }
        { contradiction. }
      * unfold update.
        destruct eq_var_dec.
        {
          unfold sem in *.
          unfold ne01 in Hneq.
          unfold gt01 in Hgt.
          destruct eq_dec in Hneq.
          destruct gt_dec in Hgt.
          { contradiction. }
          { contradiction. }
          { 
            destruct gt_dec in Hgt.
            { contradiction. }
            { contradiction. }
          }
        }
        tauto.
      * unfold update.
        destruct eq_var_dec.
        { rewrite e. tauto. }
        { 
          unfold sem in *.
          unfold ne01 in Hneq.
          unfold gt01 in Hgt.
          destruct eq_dec in Hneq.
          destruct gt_dec in Hgt.
          { contradiction. }
          { contradiction. }
          { 
            destruct gt_dec in Hgt.
            { contradiction. }
            { contradiction. }
          }
        }
        
    + clear Htcsos H3 H4 H H0. 
    inversion H1; clear H1; subst.
Qed.




Lemma alt_step_ass: forall s u, step s u -> s a <> s b.
Proof.
  intros.
  inversion H.
  subst.
  unfold euclid_body in H0.
  inversion H0 as [| s1 s2 s3 Hsos Htc' ]. subst.
  
  inversion Hsos. subst.
  inversion H5. subst.
  unfold sem in H2.
  rename H2 into Goal.
  unfold ne01 in Goal.
  destruct (eq_dec (st' a) (st' b)).
  - subst. simpl in H. contradiction.
  - assumption.
Qed.


Theorem Q4 : forall a0 b0 s s', s a = a0 -> s b = b0 -> tc step s s' -> s' a = s' b -> gcd a0 b0 (s' a).
Proof.
  intros a0 b0 s s' Ha Hb Htcstep Hskip. subst.
  induction Htcstep.
  
  - rewrite Hskip. apply base.
  - assert (gcd (u a) (u b) (t0 a)) as Hgcdfin.
    { firstorder. }
    
    apply alt_step in H as H0.
    rename H0 into Hcond.
    destruct Hcond.
    rename H0 into Hcondlt.
    rename H1 into Hcondgt.
    destruct (Nat.ltb_spec (s a) (s b)).
    + destruct Hcondlt.
      * exact H0.
      * rewrite <- H1.
        assert (s b = u a + u b) by lia.
        rewrite H3.
        apply step_b.
        exact Hgcdfin.
    + destruct (Nat.eqb_spec (s a) (s b)).
      * assert (s a <> s b).
        apply (alt_step_ass H).
        contradiction.
      * assert (s a > s b) by lia.
        destruct Hcondgt.
        { exact H1. }
        { 
          rewrite <- H2.
          assert (s a = u a + u b) by lia.
          rewrite H4.
          apply step_a.
          exact Hgcdfin.
        }
Qed.