Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2528100 : (forall m : int, forall n : int, ((int_mul n (div m n)) = m) = (int_divides n m)) /\ (forall m : int, forall n : int, ((int_mul (div m n) n) = m) = (int_divides n m)).
