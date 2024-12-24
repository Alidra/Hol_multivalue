Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3186538 : forall {A : Type'}, forall s : A -> Prop, forall x : A, (@INSERT A x s) = (fun y : A => (@IN A y s) \/ (y = x)).
