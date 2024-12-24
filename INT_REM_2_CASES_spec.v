Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2716252 : forall n : int, ((rem n (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) \/ ((rem n (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))).
