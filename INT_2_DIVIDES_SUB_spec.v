Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2745113 : forall m : int, forall n : int, (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_sub m n)) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) m) = (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) n)).
