Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6949047 : forall {A : Type'}, forall f : A -> nat, forall b : nat, forall s : A -> Prop, ((@FINITE A s) /\ (Peano.le (@nsum A s f) b)) -> forall x : A, (@IN A x s) -> Peano.le (f x) b.
