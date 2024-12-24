Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2309043 : forall x : int, (int_sgn x) = (@COND int (int_lt (int_of_num (NUMERAL 0)) x) (int_of_num (NUMERAL (BIT1 0))) (@COND int (int_lt x (int_of_num (NUMERAL 0))) (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0)))).
