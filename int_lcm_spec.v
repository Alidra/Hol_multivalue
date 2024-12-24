Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2802699 : forall m : int, forall n : int, (int_lcm (@pair int int m n)) = (@COND int ((int_mul m n) = (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL 0)) (div (int_abs (int_mul m n)) (int_gcd (@pair int int m n)))).
