Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := (forall y0 : nat, forall y1 : nat, (Nat.sub (NUMERAL y0) (NUMERAL y1)) = (NUMERAL (Nat.sub y0 y1))) /\ (((Nat.sub 0 0) = 0) /\ ((forall y0 : nat, (Nat.sub 0 (BIT0 y0)) = 0) /\ ((forall y0 : nat, (Nat.sub 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, (Nat.sub (BIT0 y0) 0) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.sub (BIT1 y0) 0) = (BIT1 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.sub (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.sub y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.sub (BIT0 y0) (BIT1 y1)) = (Nat.pred (BIT0 (Nat.sub y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.sub (BIT1 y0) (BIT0 y1)) = (@COND nat (Peano.le y1 y0) (BIT1 (Nat.sub y0 y1)) 0)) /\ (forall y0 : nat, forall y1 : nat, (Nat.sub (BIT1 y0) (BIT1 y1)) = (BIT0 (Nat.sub y0 y1))))))))))).
