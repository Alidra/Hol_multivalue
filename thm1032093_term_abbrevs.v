Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) (x6 : nat) (x7 : nat) (x8 : nat) := ((Nat.add (Nat.add x1 x0) x2) = (Nat.add (Nat.add x1 x2) x0)) /\ (((Nat.add x1 x2) = (Nat.add x2 x1)) /\ (((Nat.add x1 (Nat.add x2 x3)) = (Nat.add (Nat.add x1 x2) x3)) /\ (((Nat.mul (Nat.pow x7 x4) (Nat.pow x7 x8)) = (Nat.pow x7 (Nat.add x4 x8))) /\ (((Nat.mul x7 (Nat.pow x7 x8)) = (Nat.pow x7 (S x8))) /\ (((Nat.mul (Nat.pow x7 x8) x7) = (Nat.pow x7 (S x8))) /\ (((Nat.mul x7 x7) = (Nat.pow x7 (NUMERAL (BIT0 (BIT1 0))))) /\ (((Nat.pow (Nat.mul x7 x5) x8) = (Nat.mul (Nat.pow x7 x8) (Nat.pow x5 x8))) /\ (((Nat.pow (Nat.pow x7 x4) x8) = (Nat.pow x7 (Nat.mul x4 x8))) /\ (((Nat.pow x7 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (((Nat.pow x7 (NUMERAL (BIT1 0))) = x7) /\ (((Nat.mul x7 (Nat.add x5 x6)) = (Nat.add (Nat.mul x7 x5) (Nat.mul x7 x6))) /\ ((Nat.pow x7 (S x8)) = (Nat.mul x7 (Nat.pow x7 x8)))))))))))))).
