Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term12 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := True \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term8 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term21 := (fun y0 : Prop => (~ y0) \/ y0) False.
Definition term22 := (~ False) \/ False.
Definition term16 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : Prop => (~ y0) \/ y0) (x0 = x1).
Definition term5 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := (x0 = x0) /\ ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term13 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) (x0 = x1).
Definition term11 (a0 : Type') (x0 : a0) (x1 : a0) := (~ (x0 = x1)) -> (x0 = x1) = False.
Definition term19 (a0 : Type') (x0 : a0) (x1 : a0) := @eq Prop ((fun y0 : Prop => (~ y0) \/ y0) (x0 = x1)).
Definition term17 := (fun y0 : Prop => (~ y0) \/ y0) True.
Definition term7 (a0 : Type') (x0 : a0) (x1 : a0) := or (~ (x0 = x1)).
Definition term6 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := True /\ ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term3 (a0 : Type') (x0 : a0) := and (x0 = x0).
Definition term1 (a0 : Type') (x0 : a0) (x1 : a0) := (x0 = x1) \/ (~ (x0 = x1)).
Definition term10 (a0 : Type') (x0 : a0) (x1 : a0) := False \/ ((~ (x0 = x1)) \/ (x0 = x1)).
Definition term2 (a0 : Type') (x0 : a0) (x1 : a0) := ~ (x0 = x1).
Definition term0 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = x1).
Definition term14 (a0 : Type') (x0 : a0) (x1 : a0) := ((x0 = x1) = True) \/ ((x0 = x1) = False).
Definition term18 := (~ True) \/ True.
Definition term4 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term9 (a0 : Type') (x0 : a0) (x1 : a0) := (~ (x0 = x1)) \/ (x0 = x1).
Definition term20 (a0 : Type') (x0 : a0) (x1 : a0) := @eq Prop ((~ (x0 = x1)) \/ (x0 = x1)).
Definition term15 := fun y0 : Prop => (~ y0) \/ y0.
