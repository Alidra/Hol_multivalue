Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem98731 : forall n : nat, (Peano.lt (NUMERAL 0) n) = (~ (n = (NUMERAL 0))).
