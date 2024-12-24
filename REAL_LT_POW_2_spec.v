Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1647411 : forall x : real, (real_lt (real_of_num (NUMERAL 0)) (real_pow x (NUMERAL (BIT0 (BIT1 0))))) = (~ (x = (real_of_num (NUMERAL 0)))).
