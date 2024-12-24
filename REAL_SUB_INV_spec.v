Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1634063 : forall x : real, forall y : real, ((~ (x = (real_of_num (NUMERAL 0)))) /\ (~ (y = (real_of_num (NUMERAL 0))))) -> (real_sub (real_inv x) (real_inv y)) = (real_div (real_sub y x) (real_mul x y)).
