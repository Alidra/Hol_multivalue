Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2651482 : forall m : int, forall n : int, forall p : int, ((~ (n = (int_of_num (NUMERAL 0)))) /\ (int_le (int_abs n) (int_abs p))) -> (rem (rem m n) p) = (rem m n).
