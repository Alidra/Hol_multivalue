Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4797007 : forall {A : Type'}, forall P : A -> A -> Prop, forall Q : A -> A -> Prop, forall s : A -> Prop, ((@pairwise A P s) /\ (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((P x y) /\ (~ (x = y))))) -> Q x y)) -> @pairwise A Q s.
