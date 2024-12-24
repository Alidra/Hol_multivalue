Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5291214 : forall s : real -> Prop, forall b : real, (has_sup s b) = (forall c : real, (forall x : real, (@IN real x s) -> real_le x c) = (real_le b c)).
