Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1648586 : forall x : real, forall y : real, ((real_add (real_pow x (NUMERAL (BIT0 (BIT1 0)))) (real_pow y (NUMERAL (BIT0 (BIT1 0))))) = (real_of_num (NUMERAL 0))) = ((x = (real_of_num (NUMERAL 0))) /\ (y = (real_of_num (NUMERAL 0)))).
