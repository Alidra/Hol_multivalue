Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2586280 : forall m : int, forall n : int, (div (int_neg m) n) = (@COND int ((rem m n) = (int_of_num (NUMERAL 0))) (int_neg (div m n)) (int_sub (int_neg (div m n)) (int_sgn n))).
