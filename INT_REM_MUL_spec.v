Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2599936 : (forall m : int, forall n : int, (rem (int_mul m n) n) = (int_of_num (NUMERAL 0))) /\ (forall m : int, forall n : int, (rem (int_mul m n) m) = (int_of_num (NUMERAL 0))).
