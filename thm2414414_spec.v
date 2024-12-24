Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2414414 : (forall x : int, forall y : int, forall z : int, (int_add x (int_add y z)) = (int_add (int_add x y) z)) /\ ((forall x : int, forall y : int, (int_add x y) = (int_add y x)) /\ ((forall x : int, (int_add (int_of_num (NUMERAL 0)) x) = x) /\ ((forall x : int, forall y : int, forall z : int, (int_mul x (int_mul y z)) = (int_mul (int_mul x y) z)) /\ ((forall x : int, forall y : int, (int_mul x y) = (int_mul y x)) /\ ((forall x : int, (int_mul (int_of_num (NUMERAL (BIT1 0))) x) = x) /\ ((forall x : int, (int_mul (int_of_num (NUMERAL 0)) x) = (int_of_num (NUMERAL 0))) /\ ((forall x : int, forall y : int, forall z : int, (int_mul x (int_add y z)) = (int_add (int_mul x y) (int_mul x z))) /\ ((forall x : int, (int_pow x (NUMERAL 0)) = (int_of_num (NUMERAL (BIT1 0)))) /\ (forall x : int, forall n : nat, (int_pow x (S n)) = (int_mul x (int_pow x n))))))))))).
