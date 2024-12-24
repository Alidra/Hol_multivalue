Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem91530 : forall n : nat, Peano.lt (NUMERAL 0) (S n).
