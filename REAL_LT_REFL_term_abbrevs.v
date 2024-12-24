Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term11 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term3 (x0 : real) (x1 : real) := (fun y0 : real => (real_lt y0 x0) = (~ (real_le x0 y0))) x1.
Definition term8 := fun y0 : real => True.
Definition term10 := forall y0 : real, True.
Definition term12 (x0 : Prop) := forall y0 : real, x0.
Definition term6 (x0 : real) := ~ (real_lt x0 x0).
Definition term5 (x0 : real) := ~ (real_le x0 x0).
Definition term1 (x0 : real) := (fun y0 : real => forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) x0.
Definition term2 (x0 : real) := forall y0 : real, (real_lt y0 x0) = (~ (real_le x0 y0)).
Definition term7 := fun y0 : real => ~ (real_lt y0 y0).
Definition term0 (x0 : real) := (fun y0 : real => real_le y0 y0) x0.
Definition term4 (x0 : real) (x1 : real) := ~ (real_le x0 x1).
Definition term9 := forall y0 : real, ~ (real_lt y0 y0).
