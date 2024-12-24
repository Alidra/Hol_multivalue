Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5256827 : forall a : real, (inf (@INSERT real a (@EMPTY real))) = a.
