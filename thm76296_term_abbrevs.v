Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := @ε (nat -> nat) (fun y0 : nat -> nat => ((y0 (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y1 : nat, (y0 (S y1)) = (S (S (y0 y1))))).
