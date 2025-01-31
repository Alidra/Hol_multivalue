Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1982758 : forall (a : real) (c : real) (d : real) (p : nat) (y : real) (z : real) (x : real) (q : nat), ((real_add a c) = (real_add c a)) /\ (((real_add a (real_add c d)) = (real_add (real_add a c) d)) /\ (((real_mul (real_pow x p) (real_pow x q)) = (real_pow x (Nat.add p q))) /\ (((real_mul x (real_pow x q)) = (real_pow x (S q))) /\ (((real_mul (real_pow x q) x) = (real_pow x (S q))) /\ (((real_mul x x) = (real_pow x (NUMERAL (BIT0 (BIT1 0))))) /\ (((real_pow (real_mul x y) q) = (real_mul (real_pow x q) (real_pow y q))) /\ (((real_pow (real_pow x p) q) = (real_pow x (Nat.mul p q))) /\ (((real_pow x (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (((real_pow x (NUMERAL (BIT1 0))) = x) /\ (((real_mul x (real_add y z)) = (real_add (real_mul x y) (real_mul x z))) /\ ((real_pow x (S q)) = (real_mul x (real_pow x q))))))))))))).
