Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2541190 : (forall n : int, (div n n) = (@COND int (n = (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0))))) /\ (forall n : int, (rem n n) = (int_of_num (NUMERAL 0))).