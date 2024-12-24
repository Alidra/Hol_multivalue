Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5178241 : forall a : real, (sup (@INSERT real a (@EMPTY real))) = a.
