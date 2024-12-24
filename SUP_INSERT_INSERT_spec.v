Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5180944 : forall a : real, forall b : real, forall s : real -> Prop, (sup (@INSERT real b (@INSERT real a s))) = (sup (@INSERT real (real_max a b) s)).
