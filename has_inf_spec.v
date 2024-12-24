Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5289985 : forall s : real -> Prop, forall b : real, (has_inf s b) = (forall c : real, (forall x : real, (@IN real x s) -> real_le c x) = (real_le c b)).
