Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2728171 : forall x : int, (rem (int_neg x) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (rem x (int_of_num (NUMERAL (BIT0 (BIT1 0))))).
