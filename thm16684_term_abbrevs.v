Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term16 (x0 : Prop) := imp (~ x0).
Definition term4 (x0 : Prop) := (fun y0 : Prop => (~ (y0 \/ x0)) -> ~ x0) True.
Definition term10 (x0 : Prop) := (~ (False \/ x0)) -> ~ x0.
Definition term5 (x0 : Prop) := (~ (True \/ x0)) -> ~ x0.
Definition term8 (x0 : Prop) (x1 : Prop) := @eq Prop ((~ (x0 \/ x1)) -> ~ x1).
Definition term11 (x0 : Prop) := ~ (True \/ x0).
Definition term3 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (~ (y0 \/ x0)) -> ~ x0) x1.
Definition term12 (x0 : Prop) := imp (~ (True \/ x0)).
Definition term15 (x0 : Prop) := imp (~ (False \/ x0)).
Definition term18 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term6 (x0 : Prop) (x1 : Prop) := @eq Prop ((fun y0 : Prop => (~ (y0 \/ x0)) -> ~ x0) x1).
Definition term17 (x0 : Prop) := (~ x0) -> ~ x0.
Definition term1 (x0 : Prop) := (x0 = True) \/ (x0 = False).
Definition term13 (x0 : Prop) := False -> ~ x0.
Definition term14 (x0 : Prop) := ~ (False \/ x0).
Definition term2 (x0 : Prop) := fun y0 : Prop => (~ (y0 \/ x0)) -> ~ x0.
Definition term7 (x0 : Prop) (x1 : Prop) := (~ (x0 \/ x1)) -> ~ x1.
Definition term9 (x0 : Prop) := (fun y0 : Prop => (~ (y0 \/ x0)) -> ~ x0) False.
Definition term0 (x0 : Prop) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) x0.
