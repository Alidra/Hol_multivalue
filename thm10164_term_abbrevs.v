Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 := (fun y0 : Prop => (~ (~ y0)) = y0) True.
Definition term5 := ~ (~ True).
Definition term7 (x0 : Prop) := ~ (~ x0).
Definition term6 (x0 : Prop) := @eq Prop ((fun y0 : Prop => (~ (~ y0)) = y0) x0).
Definition term8 (x0 : Prop) := @eq Prop ((~ (~ x0)) = x0).
Definition term11 := ~ (~ (~ False)).
Definition term10 := ~ (~ False).
Definition term1 (x0 : Prop) := (x0 = True) \/ (x0 = False).
Definition term3 (x0 : Prop) := (fun y0 : Prop => (~ (~ y0)) = y0) x0.
Definition term2 := fun y0 : Prop => (~ (~ y0)) = y0.
Definition term9 := (fun y0 : Prop => (~ (~ y0)) = y0) False.
Definition term0 (x0 : Prop) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) x0.
