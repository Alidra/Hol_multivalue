Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : nat) := (fun y0 : nat => y0) x0.
Definition term3 (x0 : nat) := (fun y0 : nat => (NUMERAL y0) = y0) x0.
Definition term0 := fun y0 : nat => y0.
Definition term2 := forall y0 : nat, (NUMERAL y0) = y0.
