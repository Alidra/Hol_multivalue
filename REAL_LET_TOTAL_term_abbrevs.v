Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term20 := True \/ (~ True).
Definition term24 := False \/ (~ False).
Definition term9 (x0 : real) := forall y0 : real, (real_le x0 y0) \/ (real_lt y0 x0).
Definition term2 (x0 : real) (x1 : real) := (fun y0 : real => (real_lt y0 x0) = (~ (real_le x0 y0))) x1.
Definition term18 (x0 : real) (x1 : real) := (fun y0 : Prop => y0 \/ (~ y0)) (real_le x0 x1).
Definition term7 (x0 : real) := fun y0 : real => (real_le x0 y0) \/ (real_lt y0 x0).
Definition term22 (x0 : real) (x1 : real) := @eq Prop ((real_le x0 x1) \/ (~ (real_le x0 x1))).
Definition term14 := forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (~ (real_le y0 y1)).
Definition term13 := forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_lt y1 y0).
Definition term5 (x0 : real) (x1 : real) := (real_le x1 x0) \/ (real_lt x0 x1).
Definition term4 (x0 : real) (x1 : real) := or (real_le x0 x1).
Definition term17 := fun y0 : Prop => y0 \/ (~ y0).
Definition term21 (x0 : real) (x1 : real) := @eq Prop ((fun y0 : Prop => y0 \/ (~ y0)) (real_le x0 x1)).
Definition term10 (x0 : real) := forall y0 : real, (real_le x0 y0) \/ (~ (real_le x0 y0)).
Definition term11 := fun y0 : real => forall y1 : real, (real_le y0 y1) \/ (real_lt y1 y0).
Definition term0 (x0 : real) := (fun y0 : real => forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) x0.
Definition term19 := (fun y0 : Prop => y0 \/ (~ y0)) True.
Definition term1 (x0 : real) := forall y0 : real, (real_lt y0 x0) = (~ (real_le x0 y0)).
Definition term15 (x0 : real) (x1 : real) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) (real_le x0 x1).
Definition term3 (x0 : real) (x1 : real) := ~ (real_le x0 x1).
Definition term23 := (fun y0 : Prop => y0 \/ (~ y0)) False.
Definition term6 (x0 : real) (x1 : real) := (real_le x0 x1) \/ (~ (real_le x0 x1)).
Definition term16 (x0 : real) (x1 : real) := ((real_le x0 x1) = True) \/ ((real_le x0 x1) = False).
Definition term8 (x0 : real) := fun y0 : real => (real_le x0 y0) \/ (~ (real_le x0 y0)).
Definition term12 := fun y0 : real => forall y1 : real, (real_le y0 y1) \/ (~ (real_le y0 y1)).
