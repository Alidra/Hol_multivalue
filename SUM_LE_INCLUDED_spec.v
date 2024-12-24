Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7196249 : forall {A B : Type'}, forall f : A -> real, forall g : B -> real, forall s : A -> Prop, forall t : B -> Prop, forall i : B -> A, ((@FINITE A s) /\ ((@FINITE B t) /\ ((forall y : B, (@IN B y t) -> real_le (real_of_num (NUMERAL 0)) (g y)) /\ (forall x : A, (@IN A x s) -> exists y : B, (@IN B y t) /\ (((i y) = x) /\ (real_le (f x) (g y))))))) -> real_le (@sum A s f) (@sum B t g).
