Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := (forall y0 : nat, forall y1 : nat, (Nat.mul (NUMERAL y0) (NUMERAL y1)) = (NUMERAL (Nat.mul y0 y1))) /\ (((Nat.mul 0 0) = 0) /\ ((forall y0 : nat, (Nat.mul 0 (BIT0 y0)) = 0) /\ ((forall y0 : nat, (Nat.mul 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, (Nat.mul (BIT0 y0) 0) = 0) /\ ((forall y0 : nat, (Nat.mul (BIT1 y0) 0) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT0 y1)) = (BIT0 (BIT0 (Nat.mul y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT1 y1)) = (Nat.add (BIT0 y0) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT0 y1)) = (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT1 y1)) = (Nat.add (BIT1 y0) (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1)))))))))))))).
