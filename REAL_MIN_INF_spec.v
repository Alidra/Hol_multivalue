Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5288764 : forall x : real, forall y : real, (real_min x y) = (inf (@INSERT real x (@INSERT real y (@EMPTY real)))).
