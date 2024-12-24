Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := (forall y0 : nat, forall y1 : nat, (Peano.le (NUMERAL y0) (NUMERAL y1)) = (Peano.le y0 y1)) /\ (((Peano.le 0 0) = True) /\ ((forall y0 : nat, (Peano.le (BIT0 y0) 0) = (Peano.le y0 0)) /\ ((forall y0 : nat, (Peano.le (BIT1 y0) 0) = False) /\ ((forall y0 : nat, (Peano.le 0 (BIT0 y0)) = True) /\ ((forall y0 : nat, (Peano.le 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1)))))))))).
