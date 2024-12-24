Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem513190 : forall (n : nat), ((fun n' : nat => (NUMERAL n') = n') n) = ((NUMERAL n) = n).
