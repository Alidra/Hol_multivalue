Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term5 := imp (False = True).
Definition term11 (x0 : Prop) (x1 : Prop) := imp (x0 = x1).
Definition term2 (x0 : Prop) (x1 : Prop) := (False = False) -> x0 = x1.
Definition term13 (x0 : Prop) := (~ False) \/ x0.
Definition term12 := or (~ False).
Definition term1 (x0 : Prop) (x1 : Prop) := (x0 = x0) -> x1.
Definition term0 (a0 : Type') (x0 : a0) (x1 : Prop) := (x0 = x0) -> x1.
Definition term10 (x0 : Prop) (x1 : Prop) (x2 : Prop) := imp (((False = False) -> x1 = x0) /\ ((False = True) -> x1 = x2)).
Definition term17 (x0 : Prop) (x1 : Prop) := (x0 = x1) -> x0 = x1.
Definition term8 (x0 : Prop) (x1 : Prop) (x2 : Prop) := ((False = False) -> x1 = x0) /\ ((False = True) -> x1 = x2).
Definition term7 (x0 : Prop) (x1 : Prop) := False -> x0 = x1.
Definition term18 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (((x2 = False) -> x0 = x3) /\ ((x2 = True) -> x0 = x1)) -> x0 = (((~ x2) \/ x1) /\ (x2 \/ x3)).
Definition term9 (x0 : Prop) (x1 : Prop) := (x0 = x1) /\ True.
Definition term4 (x0 : Prop) (x1 : Prop) := and (x0 = x1).
Definition term6 (x0 : Prop) (x1 : Prop) := (False = True) -> x0 = x1.
Definition term16 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (((False = False) -> x0 = x2) /\ ((False = True) -> x0 = x1)) -> x0 = (((~ False) \/ x1) /\ (False \/ x2)).
Definition term15 (x0 : Prop) (x1 : Prop) := ((~ False) \/ x0) /\ (False \/ x1).
Definition term14 (x0 : Prop) := and ((~ False) \/ x0).
Definition term3 (x0 : Prop) (x1 : Prop) := and ((False = False) -> x0 = x1).
