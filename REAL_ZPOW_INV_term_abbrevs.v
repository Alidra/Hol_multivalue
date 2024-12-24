Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 (x0 : real) (x1 : int) := real_zpow (real_inv x0) x1.
Definition term2 (x0 : real) (x1 : int) := (fun y0 : int => (real_inv (real_zpow x0 y0)) = (real_zpow (real_inv x0) y0)) x1.
Definition term10 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term7 := fun y0 : int => True.
Definition term5 (x0 : real) (x1 : int) := @eq real (real_zpow (real_inv x0) x1).
Definition term13 := fun y0 : real => True.
Definition term15 := forall y0 : real, True.
Definition term16 (x0 : Prop) := forall y0 : real, x0.
Definition term14 := forall y0 : real, forall y1 : int, (real_zpow (real_inv y0) y1) = (real_inv (real_zpow y0 y1)).
Definition term12 := fun y0 : real => forall y1 : int, (real_zpow (real_inv y0) y1) = (real_inv (real_zpow y0 y1)).
Definition term1 (x0 : real) := forall y0 : int, (real_inv (real_zpow x0 y0)) = (real_zpow (real_inv x0) y0).
Definition term3 (x0 : real) (x1 : int) := real_inv (real_zpow x0 x1).
Definition term11 (x0 : Prop) := forall y0 : int, x0.
Definition term8 (x0 : real) := forall y0 : int, (real_zpow (real_inv x0) y0) = (real_inv (real_zpow x0 y0)).
Definition term9 := forall y0 : int, True.
Definition term6 (x0 : real) := fun y0 : int => (real_zpow (real_inv x0) y0) = (real_inv (real_zpow x0 y0)).
Definition term0 (x0 : real) := (fun y0 : real => forall y1 : int, (real_inv (real_zpow y0 y1)) = (real_zpow (real_inv y0) y1)) x0.
