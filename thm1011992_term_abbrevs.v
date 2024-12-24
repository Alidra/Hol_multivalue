Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat) := (fun y0 : nat => Peano.le y0 y0) x0.
Definition term1 (x0 : nat) := Peano.le (NUMERAL x0) (NUMERAL x0).
