Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3112686 : forall m : nat, forall n : nat, ((~ (n = (NUMERAL 0))) /\ (num_divides m n)) -> (Nat.div n (Nat.div n m)) = m.
