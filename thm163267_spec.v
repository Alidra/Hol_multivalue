Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem163267 : forall m : nat, (Peano.lt m (NUMERAL 0)) = False.
