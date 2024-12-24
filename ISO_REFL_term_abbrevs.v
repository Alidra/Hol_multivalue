Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term26 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term9 (a0 : Type') := (fun y0 : Prop => y0 = (forall y1 : a0, ((fun y2 : a0 => y2) ((fun y2 : a0 => y2) y1)) = y1)) ((forall y0 : a0, ((fun y1 : a0 => y1) ((fun y1 : a0 => y1) y0)) = y0) /\ (forall y0 : a0, ((fun y1 : a0 => y1) ((fun y1 : a0 => y1) y0)) = y0)).
Definition term14 (a0 : Type') (x0 : a0) := (fun y0 : a0 => (fun y1 : a0 => y1) y0) ((fun y0 : a0 => y0) x0).
Definition term0 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) := (fun y0 : a1 -> a0 => forall y1 : a0 -> a1, (@ExtensionalityFacts.is_inverse a0 a1 y1 y0) = ((forall y2 : a1, (y1 (y0 y2)) = y2) /\ (forall y2 : a0, (y0 (y1 y2)) = y2))) x0.
Definition term25 (a0 : Type') := forall y0 : a0, True.
Definition term6 (a0 : Type') := (forall y0 : a0, ((fun y1 : a0 => y1) ((fun y1 : a0 => y1) y0)) = y0) /\ (forall y0 : a0, ((fun y1 : a0 => y1) ((fun y1 : a0 => y1) y0)) = y0).
Definition term4 (a0 : Type') (x0 : a0 -> a0) (x1 : a0 -> a0) := (forall y0 : a0, (x1 (x0 y0)) = y0) /\ (forall y0 : a0, (x0 (x1 y0)) = y0).
Definition term3 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a0 -> a1) := (forall y0 : a1, (x1 (x0 y0)) = y0) /\ (forall y0 : a0, (x0 (x1 y0)) = y0).
Definition term11 (a0 : Type') := @eq Prop (((forall y0 : a0, ((fun y1 : a0 => y1) ((fun y1 : a0 => y1) y0)) = y0) /\ (forall y0 : a0, ((fun y1 : a0 => y1) ((fun y1 : a0 => y1) y0)) = y0)) = (forall y0 : a0, ((fun y1 : a0 => y1) ((fun y1 : a0 => y1) y0)) = y0)).
Definition term22 (a0 : Type') (x0 : a0) := @eq a0 ((fun y0 : a0 => y0) x0).
Definition term21 (a0 : Type') (x0 : a0) := @eq a0 ((fun y0 : a0 => (fun y1 : a0 => y1) y0) x0).
Definition term20 (a0 : Type') (x0 : a0) := (fun y0 : a0 => (fun y1 : a0 => y1) y0) x0.
Definition term19 (a0 : Type') (x0 : a0) := @eq a0 ((fun y0 : a0 => y0) ((fun y0 : a0 => y0) x0)).
Definition term2 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => (@ExtensionalityFacts.is_inverse a0 a1 y0 x0) = ((forall y1 : a1, (y0 (x0 y1)) = y1) /\ (forall y1 : a0, (x0 (y0 y1)) = y1))) x1.
Definition term1 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) := forall y0 : a0 -> a1, (@ExtensionalityFacts.is_inverse a0 a1 y0 x0) = ((forall y1 : a1, (y0 (x0 y1)) = y1) /\ (forall y1 : a0, (x0 (y0 y1)) = y1)).
Definition term5 (a0 : Type') := @ExtensionalityFacts.is_inverse a0 a0 (fun y0 : a0 => y0) (fun y0 : a0 => y0).
Definition term13 (a0 : Type') (x0 : a0 -> a0) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term12 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term24 (a0 : Type') := fun y0 : a0 => True.
Definition term16 (a0 : Type') (x0 : a0) := (fun y0 : a0 => y0) x0.
Definition term8 (a0 : Type') := forall y0 : a0, ((fun y1 : a0 => y1) ((fun y1 : a0 => y1) y0)) = y0.
Definition term7 (a0 : Type') := fun y0 : a0 => y0.
Definition term23 (a0 : Type') := fun y0 : a0 => ((fun y1 : a0 => y1) ((fun y1 : a0 => y1) y0)) = y0.
Definition term18 (a0 : Type') (x0 : a0) := @eq a0 ((fun y0 : a0 => (fun y1 : a0 => y1) y0) ((fun y0 : a0 => y0) x0)).
Definition term10 (a0 : Type') := @eq Prop ((fun y0 : Prop => y0 = (forall y1 : a0, ((fun y2 : a0 => y2) ((fun y2 : a0 => y2) y1)) = y1)) ((forall y0 : a0, ((fun y1 : a0 => y1) ((fun y1 : a0 => y1) y0)) = y0) /\ (forall y0 : a0, ((fun y1 : a0 => y1) ((fun y1 : a0 => y1) y0)) = y0))).
Definition term15 (a0 : Type') (x0 : a0) := (fun y0 : a0 => y0) ((fun y0 : a0 => y0) x0).
Definition term17 (a0 : Type') := fun y0 : a0 => (fun y1 : a0 => y1) y0.
