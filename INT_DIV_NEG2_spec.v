Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2589738 : forall m : int, forall n : int, (div (int_neg m) (int_neg n)) = (@COND int ((rem m n) = (int_of_num (NUMERAL 0))) (div m n) (int_add (div m n) (int_sgn n))).
