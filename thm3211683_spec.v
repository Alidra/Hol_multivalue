Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3211683 : forall {A : Type'} (s : A -> Prop) (x : A) (y : A), (fun y' : A => (@IN A x (@DELETE A s y')) = ((@IN A x s) /\ (~ (x = y')))) y.
