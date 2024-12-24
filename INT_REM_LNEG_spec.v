Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2586279 : forall m : int, forall n : int, (rem (int_neg m) n) = (@COND int ((rem m n) = (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL 0)) (int_sub (int_abs n) (rem m n))).
