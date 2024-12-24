Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term13 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term11 := fun y0 : int => True.
Definition term4 (x0 : int) := (fun y0 : int => forall y1 : int, (int_divides (int_abs y0) y1) = (int_divides y0 y1)) x0.
Definition term0 (x0 : int) := (fun y0 : int => forall y1 : int, (int_divides y0 (int_abs y1)) = (int_divides y0 y1)) x0.
Definition term17 := and (forall y0 : int, forall y1 : int, (int_divides (int_abs y0) y1) = (int_divides y0 y1)).
Definition term1 (x0 : int) := forall y0 : int, (int_divides x0 (int_abs y0)) = (int_divides x0 y0).
Definition term7 (x0 : int) (x1 : int) := int_divides (int_abs x0) x1.
Definition term22 := (forall y0 : int, forall y1 : int, (int_divides (int_abs y0) y1) = (int_divides y0 y1)) /\ (forall y0 : int, forall y1 : int, (int_divides y0 (int_abs y1)) = (int_divides y0 y1)).
Definition term3 (x0 : int) (x1 : int) := int_divides x0 (int_abs x1).
Definition term9 (x0 : int) (x1 : int) := @eq Prop (int_divides x0 x1).
Definition term6 (x0 : int) (x1 : int) := (fun y0 : int => (int_divides (int_abs x0) y0) = (int_divides x0 y0)) x1.
Definition term19 (x0 : int) := fun y0 : int => (int_divides x0 (int_abs y0)) = (int_divides x0 y0).
Definition term14 (x0 : Prop) := forall y0 : int, x0.
Definition term21 := forall y0 : int, forall y1 : int, (int_divides y0 (int_abs y1)) = (int_divides y0 y1).
Definition term16 := forall y0 : int, forall y1 : int, (int_divides (int_abs y0) y1) = (int_divides y0 y1).
Definition term20 := fun y0 : int => forall y1 : int, (int_divides y0 (int_abs y1)) = (int_divides y0 y1).
Definition term15 := fun y0 : int => forall y1 : int, (int_divides (int_abs y0) y1) = (int_divides y0 y1).
Definition term2 (x0 : int) (x1 : int) := (fun y0 : int => (int_divides x0 (int_abs y0)) = (int_divides x0 y0)) x1.
Definition term8 (x0 : int) (x1 : int) := @eq Prop (int_divides (int_abs x0) x1).
Definition term12 := forall y0 : int, True.
Definition term10 (x0 : int) := fun y0 : int => (int_divides (int_abs x0) y0) = (int_divides x0 y0).
Definition term5 (x0 : int) := forall y0 : int, (int_divides (int_abs x0) y0) = (int_divides x0 y0).
Definition term18 (x0 : int) (x1 : int) := @eq Prop (int_divides x0 (int_abs x1)).
