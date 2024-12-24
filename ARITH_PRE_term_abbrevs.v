Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := (forall y0 : nat, (Nat.pred (NUMERAL y0)) = (NUMERAL (Nat.pred y0))) /\ (((Nat.pred 0) = 0) /\ ((forall y0 : nat, (Nat.pred (BIT0 y0)) = (@COND nat (y0 = 0) 0 (BIT1 (Nat.pred y0)))) /\ (forall y0 : nat, (Nat.pred (BIT1 y0)) = (BIT0 y0)))).
