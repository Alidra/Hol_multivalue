Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem158192 : forall n : nat, (Nat.div n (NUMERAL 0)) = (NUMERAL 0).