Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem146110 : ((Factorial.fact (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall n : nat, (Factorial.fact (S n)) = (Nat.mul (S n) (Factorial.fact n))).
