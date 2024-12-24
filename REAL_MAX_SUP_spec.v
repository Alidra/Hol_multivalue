Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5203039 : forall x : real, forall y : real, (real_max x y) = (sup (@INSERT real x (@INSERT real y (@EMPTY real)))).
