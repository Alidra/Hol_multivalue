Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2416550 : forall (rx : int) (lx : int) (ry : int) (b : int) (a : int) (c : int) (d : int) (p : nat) (y : int) (z : int) (x : int) (q : nat), ((int_mul lx (int_mul rx ry)) = (int_mul rx (int_mul lx ry))) /\ (((int_add (int_add a b) (int_add c d)) = (int_add (int_add a c) (int_add b d))) /\ (((int_add (int_add a b) c) = (int_add a (int_add b c))) /\ (((int_add a (int_add c d)) = (int_add c (int_add a d))) /\ (((int_add (int_add a b) c) = (int_add (int_add a c) b)) /\ (((int_add a c) = (int_add c a)) /\ (((int_add a (int_add c d)) = (int_add (int_add a c) d)) /\ (((int_mul (int_pow x p) (int_pow x q)) = (int_pow x (Nat.add p q))) /\ (((int_mul x (int_pow x q)) = (int_pow x (S q))) /\ (((int_mul (int_pow x q) x) = (int_pow x (S q))) /\ (((int_mul x x) = (int_pow x (NUMERAL (BIT0 (BIT1 0))))) /\ (((int_pow (int_mul x y) q) = (int_mul (int_pow x q) (int_pow y q))) /\ (((int_pow (int_pow x p) q) = (int_pow x (Nat.mul p q))) /\ (((int_pow x (NUMERAL 0)) = (int_of_num (NUMERAL (BIT1 0)))) /\ (((int_pow x (NUMERAL (BIT1 0))) = x) /\ (((int_mul x (int_add y z)) = (int_add (int_mul x y) (int_mul x z))) /\ ((int_pow x (S q)) = (int_mul x (int_pow x q)))))))))))))))))).