Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1010765 : forall (n : nat), (Peano.lt (NUMERAL n) (NUMERAL n)) = False.
