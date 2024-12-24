Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2310037 : forall x : int, forall y : int, ((int_add (int_pow x (NUMERAL (BIT0 (BIT1 0)))) (int_pow y (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) = ((x = (int_of_num (NUMERAL 0))) /\ (y = (int_of_num (NUMERAL 0)))).
