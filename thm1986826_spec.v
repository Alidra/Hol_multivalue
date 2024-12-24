Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1986826 : (forall x : real, (real_mul (real_of_num (NUMERAL 0)) x) = (real_of_num (NUMERAL 0))) /\ ((forall x : real, forall y : real, forall z : real, ((real_add x y) = (real_add x z)) = (y = z)) /\ (forall w : real, forall x : real, forall y : real, forall z : real, ((real_add (real_mul w y) (real_mul x z)) = (real_add (real_mul w z) (real_mul x y))) = ((w = x) \/ (y = z)))).
