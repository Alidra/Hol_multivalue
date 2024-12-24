Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2801880 : forall a : int, forall b : int, (int_le (int_of_num (NUMERAL 0)) (int_gcd (@pair int int a b))) /\ ((int_divides (int_gcd (@pair int int a b)) a) /\ ((int_divides (int_gcd (@pair int int a b)) b) /\ (exists x : int, exists y : int, (int_gcd (@pair int int a b)) = (int_add (int_mul a x) (int_mul b y))))).
