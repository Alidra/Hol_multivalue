Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term8 (a0 : Type') (x0 : type1538 a0) (x1 : Prop) := (fun y0 : Prop => x0 y0) x1.
Definition term15 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) := (fun y0 : a0 => x0 /\ (x1 = y0)) x2.
Definition term13 (a0 : Type') (x0 : a0) (x1 : Prop) := @eq (a0 -> Prop) ((fun y0 : Prop => fun y1 : a0 => y0 /\ (x0 = y1)) x1).
Definition term25 (a0 : Type') (x0 : Prop) (x1 : a0) := forall y0 : a0, (@SETSPEC a0 x1 x0 y0) = (x0 /\ (x1 = y0)).
Definition term5 (a0 : Type') (x0 : a0) (x1 : Prop) := (fun y0 : Prop => fun y1 : a0 => y0 /\ (x0 = y1)) x1.
Definition term22 (a0 : Type') (x0 : a0) (x1 : Prop) (x2 : a0) := @eq Prop (@SETSPEC a0 x0 x1 x2).
Definition term27 (a0 : Type') (x0 : a0) := fun y0 : Prop => forall y1 : a0, (@SETSPEC a0 x0 y0 y1) = (y0 /\ (x0 = y1)).
Definition term1 (a0 : Type') (x0 : type1538 a0) (x1 : type1538 a0) := forall y0 : Prop, (x0 y0) = (x1 y0).
Definition term17 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) := (fun y0 : a0 => (fun y1 : a0 => x0 /\ (x1 = y1)) y0) x2.
Definition term14 (a0 : Type') (x0 : a0) (x1 : Prop) (x2 : a0) := (fun y0 : Prop => fun y1 : a0 => y0 /\ (x0 = y1)) x1 x2.
Definition term7 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term16 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term6 (a0 : Type') (x0 : a0) (x1 : Prop) := forall y0 : a0, (@SETSPEC a0 x0 x1 y0) = ((fun y1 : Prop => fun y2 : a0 => y1 /\ (x0 = y2)) x1 y0).
Definition term11 (a0 : Type') (x0 : a0) := fun y0 : Prop => (fun y1 : Prop => fun y2 : a0 => y1 /\ (x0 = y2)) y0.
Definition term20 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) := @eq Prop ((fun y0 : a0 => (fun y1 : a0 => x0 /\ (x1 = y1)) y0) x2).
Definition term24 (a0 : Type') (x0 : Prop) (x1 : a0) := fun y0 : a0 => (@SETSPEC a0 x1 x0 y0) = (x0 /\ (x1 = y0)).
Definition term28 (a0 : Type') (x0 : a0) := forall y0 : Prop, forall y1 : a0, (@SETSPEC a0 x0 y0 y1) = (y0 /\ (x0 = y1)).
Definition term10 (a0 : Type') (x0 : Prop) (x1 : a0) := fun y0 : a0 => x0 /\ (x1 = y0).
Definition term18 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) := x0 /\ (x1 = x2).
Definition term19 (a0 : Type') (x0 : Prop) (x1 : a0) := fun y0 : a0 => (fun y1 : a0 => x0 /\ (x1 = y1)) y0.
Definition term23 (a0 : Type') (x0 : a0) (x1 : Prop) := fun y0 : a0 => (@SETSPEC a0 x0 x1 y0) = ((fun y1 : Prop => fun y2 : a0 => y1 /\ (x0 = y2)) x1 y0).
Definition term26 (a0 : Type') (x0 : a0) := fun y0 : Prop => (@SETSPEC a0 x0 y0) = ((fun y1 : Prop => fun y2 : a0 => y1 /\ (x0 = y2)) y0).
Definition term21 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) := @eq Prop ((fun y0 : a0 => x0 /\ (x1 = y0)) x2).
Definition term12 (a0 : Type') (x0 : a0) (x1 : Prop) := @eq (a0 -> Prop) ((fun y0 : Prop => (fun y1 : Prop => fun y2 : a0 => y1 /\ (x0 = y2)) y0) x1).
Definition term2 (a0 : Type') (x0 : a0) := fun y0 : Prop => fun y1 : a0 => y0 /\ (x0 = y1).
Definition term9 (a0 : Type') (x0 : a0) (x1 : Prop) := (fun y0 : Prop => (fun y1 : Prop => fun y2 : a0 => y1 /\ (x0 = y2)) y0) x1.
Definition term4 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) = (x1 y0).
Definition term0 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> a1) := forall y0 : a0, (x0 y0) = (x1 y0).
Definition term3 (a0 : Type') (x0 : a0) := forall y0 : Prop, (@SETSPEC a0 x0 y0) = ((fun y1 : Prop => fun y2 : a0 => y1 /\ (x0 = y2)) y0).
