Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1209 a0 a1 a2) (x1 : a0) := (fun y0 : a0 => fun y1 : a1 => x0 (@pair a0 a1 y0 y1)) x1.
Definition term11 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1209 a0 a1 a2) (x1 : a0) := (fun y0 : a0 => forall y1 : a1, (@CURRY a0 a1 a2 x0 y0 y1) = (x0 (@pair a0 a1 y0 y1))) x1.
Definition term5 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1209 a0 a1 a2) (x1 : a0) (x2 : a1) := (fun y0 : a1 => x0 (@pair a0 a1 x1 y0)) x2.
Definition term2 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1209 a0 a1 a2) := fun y0 : a0 => fun y1 : a1 => x0 (@pair a0 a1 y0 y1).
Definition term6 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1209 a0 a1 a2) (x1 : a0) (x2 : a1) := x0 (@pair a0 a1 x1 x2).
Definition term0 (a0 : Type') (a1 : Type') (a2 : Type') := fun y0 : type1209 a0 a1 a2 => fun y1 : a0 => fun y2 : a1 => y0 (@pair a0 a1 y1 y2).
Definition term10 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1209 a0 a1 a2) := (fun y0 : type1209 a0 a1 a2 => forall y1 : a0, forall y2 : a1, (@CURRY a0 a1 a2 y0 y1 y2) = (y0 (@pair a0 a1 y1 y2))) x0.
Definition term1 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1209 a0 a1 a2) := (fun y0 : type1209 a0 a1 a2 => fun y1 : a0 => fun y2 : a1 => y0 (@pair a0 a1 y1 y2)) x0.
Definition term9 (a0 : Type') (a1 : Type') (a2 : Type') := forall y0 : type1209 a0 a1 a2, forall y1 : a0, forall y2 : a1, (@CURRY a0 a1 a2 y0 y1 y2) = (y0 (@pair a0 a1 y1 y2)).
Definition term8 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1209 a0 a1 a2) := forall y0 : a0, forall y1 : a1, (@CURRY a0 a1 a2 x0 y0 y1) = (x0 (@pair a0 a1 y0 y1)).
Definition term7 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1209 a0 a1 a2) (x1 : a0) := forall y0 : a1, (@CURRY a0 a1 a2 x0 x1 y0) = (x0 (@pair a0 a1 x1 y0)).
Definition term12 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1209 a0 a1 a2) (x1 : a0) (x2 : a1) := (fun y0 : a1 => (@CURRY a0 a1 a2 x0 x1 y0) = (x0 (@pair a0 a1 x1 y0))) x2.
Definition term4 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1209 a0 a1 a2) (x1 : a0) := fun y0 : a1 => x0 (@pair a0 a1 x1 y0).