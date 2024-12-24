Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term10 (a0 : Type') (x0 : type919 a0) (x1 : a0) := @eq Prop ((fun y0 : a0 => (fun y1 : a0 => x0 (@SETSPEC a0 y1)) y0) x1).
Definition term1 (a0 : Type') (x0 : type919 a0) (x1 : a0) := @GSPEC a0 (fun y0 : a0 => x0 (@SETSPEC a0 y0)) x1.
Definition term7 (a0 : Type') (x0 : type919 a0) (x1 : a0) := (fun y0 : a0 => (fun y1 : a0 => x0 (@SETSPEC a0 y1)) y0) x1.
Definition term4 (a0 : Type') (x0 : type919 a0) (x1 : a0) := (fun y0 : a0 => x0 (@SETSPEC a0 y0)) x1.
Definition term12 (a0 : Type') (x0 : a0) (x1 : type919 a0) := @eq Prop (@IN a0 x0 (@GSPEC a0 (fun y0 : a0 => x1 (@SETSPEC a0 y0)))).
Definition term5 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term6 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term3 (a0 : Type') (x0 : type919 a0) := fun y0 : a0 => x0 (@SETSPEC a0 y0).
Definition term11 (a0 : Type') (x0 : type919 a0) (x1 : a0) := @eq Prop ((fun y0 : a0 => x0 (@SETSPEC a0 y0)) x1).
Definition term13 (a0 : Type') (x0 : type919 a0) (x1 : a0) := @eq Prop (x0 (@SETSPEC a0 x1)).
Definition term0 (a0 : Type') (x0 : a0) (x1 : type919 a0) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => x1 (@SETSPEC a0 y0))).
Definition term2 (a0 : Type') (x0 : type919 a0) := @GSPEC a0 (fun y0 : a0 => x0 (@SETSPEC a0 y0)).
Definition term14 (a0 : Type') (x0 : type919 a0) (x1 : a0) := x0 (fun y0 : Prop => fun y1 : a0 => y0 /\ (x1 = y1)).
Definition term9 (a0 : Type') (x0 : type919 a0) := fun y0 : a0 => (fun y1 : a0 => x0 (@SETSPEC a0 y1)) y0.
Definition term8 (a0 : Type') (x0 : type919 a0) (x1 : a0) := x0 (@SETSPEC a0 x1).
