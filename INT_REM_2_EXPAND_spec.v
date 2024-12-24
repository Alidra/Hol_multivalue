Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2726747 : forall x : int, (rem x (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (@COND int (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x) (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))).
