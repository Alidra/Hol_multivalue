Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6930973 : forall {A : Type'}, forall f : A -> nat, forall s : A -> Prop, (forall x : A, (@IN A x s) -> (f x) = (NUMERAL 0)) -> (@nsum A s f) = (NUMERAL 0).
