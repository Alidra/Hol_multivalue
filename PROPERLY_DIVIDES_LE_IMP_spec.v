Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3102344 : forall m : nat, forall n : nat, ((num_divides m n) /\ ((~ (n = (NUMERAL 0))) /\ (~ (m = n)))) -> Peano.le (Nat.mul (NUMERAL (BIT0 (BIT1 0))) m) n.
