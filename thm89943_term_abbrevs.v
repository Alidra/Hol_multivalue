Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := @ε (nat -> nat -> nat -> Prop) (fun y0 : type1601 => forall y1 : nat, (forall y2 : nat, (y0 y1 y2 (NUMERAL 0)) = False) /\ (forall y2 : nat, forall y3 : nat, (y0 y1 y2 (S y3)) = ((y2 = y3) \/ (y0 y1 y2 y3)))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 0))))))).
