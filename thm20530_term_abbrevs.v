Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term11 := or (~ True).
Definition term6 (x0 : Prop) (x1 : Prop) := (True = True) -> x0 = x1.
Definition term10 (x0 : Prop) (x1 : Prop) := imp (x0 = x1).
Definition term14 (x0 : Prop) (x1 : Prop) := ((~ True) \/ x0) /\ (True \/ x1).
Definition term0 := imp (True = False).
Definition term5 (x0 : Prop) (x1 : Prop) := (x0 = x0) -> x1.
Definition term4 (a0 : Type') (x0 : a0) (x1 : Prop) := (x0 = x0) -> x1.
Definition term12 (x0 : Prop) := (~ True) \/ x0.
Definition term9 (x0 : Prop) (x1 : Prop) (x2 : Prop) := imp (((True = False) -> x1 = x0) /\ ((True = True) -> x1 = x2)).
Definition term16 (x0 : Prop) (x1 : Prop) := (x0 = x1) -> x0 = x1.
Definition term7 (x0 : Prop) (x1 : Prop) (x2 : Prop) := ((True = False) -> x1 = x0) /\ ((True = True) -> x1 = x2).
Definition term2 (x0 : Prop) (x1 : Prop) := False -> x0 = x1.
Definition term8 (x0 : Prop) (x1 : Prop) := True /\ (x0 = x1).
Definition term15 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (((True = False) -> x0 = x2) /\ ((True = True) -> x0 = x1)) -> x0 = (((~ True) \/ x1) /\ (True \/ x2)).
Definition term1 (x0 : Prop) (x1 : Prop) := (True = False) -> x0 = x1.
Definition term13 (x0 : Prop) := and ((~ True) \/ x0).
Definition term3 (x0 : Prop) (x1 : Prop) := and ((True = False) -> x0 = x1).
