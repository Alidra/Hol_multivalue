Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3157314 : forall p : nat, forall a : nat, forall b : nat, ((p = (NUMERAL 0)) \/ ((p = (NUMERAL (BIT1 0))) \/ (prime p))) -> (num_divides p (Nat.mul a b)) = ((num_divides p a) \/ (num_divides p b)).
