Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1011992 : forall (n : nat), (Peano.le (NUMERAL n) (NUMERAL n)) = True.
