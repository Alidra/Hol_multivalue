Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2338026 : forall x : int, forall y : int, ((int_mul x y) = (int_of_num (NUMERAL (BIT1 0)))) = (((x = (int_of_num (NUMERAL (BIT1 0)))) /\ (y = (int_of_num (NUMERAL (BIT1 0))))) \/ ((x = (int_neg (int_of_num (NUMERAL (BIT1 0))))) /\ (y = (int_neg (int_of_num (NUMERAL (BIT1 0))))))).
