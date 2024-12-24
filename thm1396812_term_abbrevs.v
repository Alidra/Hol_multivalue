Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat) := (fun y0 : nat => real_le (real_of_num (NUMERAL 0)) (real_of_num y0)) x0.
Definition term13 := real_of_num (NUMERAL 0).
Definition term12 (x0 : nat) := real_ge (real_of_num x0) (real_of_num (NUMERAL 0)).
Definition term5 (x0 : real) := forall y0 : real, (real_le x0 y0) = (real_ge y0 x0).
Definition term11 (x0 : real) (x1 : real) := (fun y0 : real => (real_le x0 y0) = (real_ge y0 x0)) x1.
Definition term4 (x0 : real) := forall y0 : real, (real_ge y0 x0) = (real_le x0 y0).
Definition term9 := forall y0 : real, forall y1 : real, (real_le y0 y1) = (real_ge y1 y0).
Definition term8 := forall y0 : real, forall y1 : real, (real_ge y1 y0) = (real_le y0 y1).
Definition term1 (x0 : nat) := real_le (real_of_num (NUMERAL 0)) (real_of_num x0).
Definition term7 := fun y0 : real => forall y1 : real, (real_le y0 y1) = (real_ge y1 y0).
Definition term6 := fun y0 : real => forall y1 : real, (real_ge y1 y0) = (real_le y0 y1).
Definition term10 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le y0 y1) = (real_ge y1 y0)) x0.
Definition term3 (x0 : real) := fun y0 : real => (real_le x0 y0) = (real_ge y0 x0).
Definition term2 (x0 : real) := fun y0 : real => (real_ge y0 x0) = (real_le x0 y0).
