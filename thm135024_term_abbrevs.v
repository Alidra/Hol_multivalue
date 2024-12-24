Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := @ε (nat -> nat -> nat -> nat) (fun y0 : type1602 => forall y1 : nat, (forall y2 : nat, (y0 y1 y2 (NUMERAL 0)) = y2) /\ (forall y2 : nat, forall y3 : nat, (y0 y1 y2 (S y3)) = (Nat.pred (y0 y1 y2 y3)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 0))))))).
