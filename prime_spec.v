Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3137997 : forall p : nat, (prime p) = ((~ (p = (NUMERAL (BIT1 0)))) /\ (forall x : nat, (num_divides x p) -> (x = (NUMERAL (BIT1 0))) \/ (x = p))).
