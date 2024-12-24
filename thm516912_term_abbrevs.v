Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 := fun y0 : nat => Peano.le (NUMERAL 0) y0.
Definition term6 (x0 : nat) := (fun y0 : nat => Peano.le 0 y0) x0.
Definition term5 := forall y0 : nat, Peano.le 0 y0.
Definition term4 := forall y0 : nat, Peano.le (NUMERAL 0) y0.
Definition term1 (x0 : nat) := Peano.le (NUMERAL 0) x0.
Definition term0 := Peano.le (NUMERAL 0).
Definition term3 := fun y0 : nat => Peano.le 0 y0.
