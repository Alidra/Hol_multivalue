Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) (x6 : nat) (x7 : nat) := ((Nat.add x0 (Nat.add x1 x2)) = (Nat.add (Nat.add x0 x1) x2)) /\ (((Nat.mul (Nat.pow x6 x3) (Nat.pow x6 x7)) = (Nat.pow x6 (Nat.add x3 x7))) /\ (((Nat.mul x6 (Nat.pow x6 x7)) = (Nat.pow x6 (S x7))) /\ (((Nat.mul (Nat.pow x6 x7) x6) = (Nat.pow x6 (S x7))) /\ (((Nat.mul x6 x6) = (Nat.pow x6 (NUMERAL (BIT0 (BIT1 0))))) /\ (((Nat.pow (Nat.mul x6 x4) x7) = (Nat.mul (Nat.pow x6 x7) (Nat.pow x4 x7))) /\ (((Nat.pow (Nat.pow x6 x3) x7) = (Nat.pow x6 (Nat.mul x3 x7))) /\ (((Nat.pow x6 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (((Nat.pow x6 (NUMERAL (BIT1 0))) = x6) /\ (((Nat.mul x6 (Nat.add x4 x5)) = (Nat.add (Nat.mul x6 x4) (Nat.mul x6 x5))) /\ ((Nat.pow x6 (S x7)) = (Nat.mul x6 (Nat.pow x6 x7)))))))))))).
