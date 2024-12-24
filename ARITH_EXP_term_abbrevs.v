Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := (forall y0 : nat, forall y1 : nat, (Nat.pow (NUMERAL y0) (NUMERAL y1)) = (NUMERAL (Nat.pow y0 y1))) /\ (((Nat.pow 0 0) = (BIT1 0)) /\ ((forall y0 : nat, (Nat.pow (BIT0 y0) 0) = (BIT1 0)) /\ ((forall y0 : nat, (Nat.pow (BIT1 y0) 0) = (BIT1 0)) /\ ((forall y0 : nat, (Nat.pow 0 (BIT0 y0)) = (Nat.mul (Nat.pow 0 y0) (Nat.pow 0 y0))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1))) /\ ((forall y0 : nat, (Nat.pow 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT1 y1)) = (Nat.mul (BIT0 y0) (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1)))) /\ (forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT1 y1)) = (Nat.mul (BIT1 y0) (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1)))))))))))).
