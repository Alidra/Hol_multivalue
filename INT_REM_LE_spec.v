Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2660728 : forall m : int, forall n : int, forall p : int, (((n = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) m)) /\ (int_le m p)) -> int_le (rem m n) p.
