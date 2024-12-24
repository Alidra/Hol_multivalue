Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2812541 : forall m : int, forall n : int, (int_mul (int_lcm (@pair int int m n)) (int_gcd (@pair int int m n))) = (int_abs (int_mul m n)).
