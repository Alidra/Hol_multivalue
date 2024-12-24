Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term10 (x0 : real) (x1 : real) := real_add x0 (real_neg x1).
Definition term1 (x0 : real) := real_neg (real_neg x0).
Definition term17 (x0 : real) (x1 : real) := @eq real (real_add (real_neg x0) x1).
Definition term15 (x0 : real) (x1 : real) := real_add (real_neg x0) x1.
Definition term29 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term27 := fun y0 : real => True.
Definition term12 (x0 : real) (x1 : real) := real_neg (real_add x0 (real_neg x1)).
Definition term16 (x0 : real) (x1 : real) := @eq real (real_neg (real_sub x0 x1)).
Definition term28 := forall y0 : real, True.
Definition term30 (x0 : Prop) := forall y0 : real, x0.
Definition term19 (x0 : real) := fun y0 : real => (real_add (real_neg x0) y0) = (real_add y0 (real_neg x0)).
Definition term25 := forall y0 : real, forall y1 : real, (real_add (real_neg y0) y1) = (real_add y1 (real_neg y0)).
Definition term24 := forall y0 : real, forall y1 : real, (real_neg (real_sub y0 y1)) = (real_sub y1 y0).
Definition term13 (x0 : real) (x1 : real) := real_add (real_neg x0) (real_neg (real_neg x1)).
Definition term23 := fun y0 : real => forall y1 : real, (real_add (real_neg y0) y1) = (real_add y1 (real_neg y0)).
Definition term26 (x0 : real) (x1 : real) := @eq real (real_add x0 (real_neg x1)).
Definition term20 (x0 : real) := forall y0 : real, (real_neg (real_sub x0 y0)) = (real_sub y0 x0).
Definition term18 (x0 : real) := fun y0 : real => (real_neg (real_sub x0 y0)) = (real_sub y0 x0).
Definition term4 (x0 : real) (x1 : real) := (fun y0 : real => (real_neg (real_add x0 y0)) = (real_add (real_neg x0) (real_neg y0))) x1.
Definition term0 (x0 : real) := (fun y0 : real => (real_neg (real_neg y0)) = y0) x0.
Definition term22 := fun y0 : real => forall y1 : real, (real_neg (real_sub y0 y1)) = (real_sub y1 y0).
Definition term7 (x0 : real) := (fun y0 : real => forall y1 : real, (real_sub y0 y1) = (real_add y0 (real_neg y1))) x0.
Definition term2 (x0 : real) := (fun y0 : real => forall y1 : real, (real_neg (real_add y0 y1)) = (real_add (real_neg y0) (real_neg y1))) x0.
Definition term5 (x0 : real) (x1 : real) := real_neg (real_add x0 x1).
Definition term21 (x0 : real) := forall y0 : real, (real_add (real_neg x0) y0) = (real_add y0 (real_neg x0)).
Definition term8 (x0 : real) := forall y0 : real, (real_sub x0 y0) = (real_add x0 (real_neg y0)).
Definition term9 (x0 : real) (x1 : real) := (fun y0 : real => (real_sub x0 y0) = (real_add x0 (real_neg y0))) x1.
Definition term3 (x0 : real) := forall y0 : real, (real_neg (real_add x0 y0)) = (real_add (real_neg x0) (real_neg y0)).
Definition term6 (x0 : real) (x1 : real) := real_add (real_neg x0) (real_neg x1).
Definition term14 (x0 : real) := real_add (real_neg x0).
Definition term11 (x0 : real) (x1 : real) := real_neg (real_sub x0 x1).
