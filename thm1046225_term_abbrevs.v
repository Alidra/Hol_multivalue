Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, (~ (y0 = (NUMERAL 0))) -> ((y1 = y2) /\ (~ (y3 = y4))) -> ~ ((Nat.add y1 (Nat.mul y0 y3)) = (Nat.add y2 (Nat.mul y0 y4))).
