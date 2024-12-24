Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7069292 : forall {A : Type'}, forall f : A -> real, forall s : A -> Prop, (forall x : A, (@IN A x s) -> (f x) = (real_of_num (NUMERAL 0))) -> (@sum A s f) = (real_of_num (NUMERAL 0)).
