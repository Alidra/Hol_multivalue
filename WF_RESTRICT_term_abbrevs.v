Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 -> x1 -> x2.
Definition term52 (a0 : Type') (x0 : a0 -> Prop) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := (((x0 x2) /\ ((x0 x3) /\ (x1 x2 x3))) -> (x1 x2 x3) = True) -> (((fun y0 : a0 => fun y1 : a0 => (x0 y0) /\ ((x0 y1) /\ (x1 y0 y1))) x2 x3) -> x1 x2 x3) = (((x0 x2) /\ ((x0 x3) /\ (x1 x2 x3))) -> True).
Definition term47 (a0 : Type') (x0 : a0 -> Prop) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := @eq Prop ((fun y0 : a0 => (x0 x2) /\ ((x0 y0) /\ (x1 x2 y0))) x3).
Definition term63 (a0 : Type') (x0 : type1402 a0) := forall y0 : a0 -> Prop, (@WF a0 x0) -> @WF a0 (fun y1 : a0 => fun y2 : a0 => (y0 y1) /\ ((y0 y2) /\ (x0 y1 y2))).
Definition term59 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term53 (a0 : Type') (x0 : a0 -> Prop) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := ((fun y0 : a0 => fun y1 : a0 => (x0 y0) /\ ((x0 y1) /\ (x1 y0 y1))) x2 x3) -> x1 x2 x3.
Definition term45 (a0 : Type') (x0 : a0 -> Prop) (x1 : type1402 a0) (x2 : a0) := fun y0 : a0 => (fun y1 : a0 => (x0 x2) /\ ((x0 y1) /\ (x1 x2 y1))) y0.
Definition term43 (a0 : Type') (x0 : a0 -> Prop) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := (fun y0 : a0 => (fun y1 : a0 => (x0 x2) /\ ((x0 y1) /\ (x1 x2 y1))) y0) x3.
Definition term58 (a0 : Type') := forall y0 : a0, True.
Definition term17 (a0 : Type') (x0 : type1402 a0) := forall y0 : type1402 a0, (forall y1 : a0, forall y2 : a0, (y0 y1 y2) -> x0 y1 y2) -> (@WF a0 x0) -> @WF a0 y0.
Definition term8 (a0 : Type') (x0 : type1402 a0) := forall y0 : type1402 a0, (forall y1 : a0, forall y2 : a0, (x0 y1 y2) -> y0 y1 y2) -> (@WF a0 y0) -> @WF a0 x0.
Definition term19 (a0 : Type') := (forall y0 : type1402 a0, forall y1 : type1402 a0, (forall y2 : a0, forall y3 : a0, (y0 y2 y3) -> y1 y2 y3) -> (@WF a0 y1) -> @WF a0 y0) -> forall y0 : type1402 a0, forall y1 : type1402 a0, (forall y2 : a0, forall y3 : a0, (y1 y2 y3) -> y0 y2 y3) -> (@WF a0 y0) -> @WF a0 y1.
Definition term32 (a0 : Type') (x0 : a0 -> Prop) (x1 : type1402 a0) (x2 : a0) (x3 : a0) (x4 : Prop) (x5 : Prop) := (((fun y0 : a0 => fun y1 : a0 => (x0 y0) /\ ((x0 y1) /\ (x1 y0 y1))) x2 x3) = x4) -> (x4 -> (x1 x2 x3) = x5) -> (((fun y0 : a0 => fun y1 : a0 => (x0 y0) /\ ((x0 y1) /\ (x1 y0 y1))) x2 x3) -> x1 x2 x3) = (x4 -> x5).
Definition term21 (a0 : Type') (x0 : type1402 a0) (x1 : type1402 a0) := (fun y0 : type1402 a0 => (forall y1 : a0, forall y2 : a0, (y0 y1 y2) -> x0 y1 y2) -> (@WF a0 x0) -> @WF a0 y0) x1.
Definition term14 (a0 : Type') (x0 : type1402 a0) (x1 : type1402 a0) := (fun y0 : type1402 a0 => (forall y1 : a0, forall y2 : a0, (x0 y1 y2) -> y0 y1 y2) -> (@WF a0 y0) -> @WF a0 x0) x1.
Definition term28 (a0 : Type') (x0 : a0 -> Prop) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := (fun y0 : a0 => fun y1 : a0 => (x0 y0) /\ ((x0 y1) /\ (x1 y0 y1))) x2 x3.
Definition term3 (a0 : Type') (x0 : type1402 a0) (x1 : type1402 a0) := (forall y0 : a0, forall y1 : a0, (x1 y0 y1) -> x0 y0 y1) -> (@WF a0 x0) -> @WF a0 x1.
Definition term51 (a0 : Type') (x0 : a0 -> Prop) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := ((x0 x2) /\ ((x0 x3) /\ (x1 x2 x3))) -> (x1 x2 x3) = True.
Definition term24 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term60 (a0 : Type') (x0 : a0 -> Prop) (x1 : type1402 a0) := fun y0 : a0 => forall y1 : a0, ((fun y2 : a0 => fun y3 : a0 => (x0 y2) /\ ((x0 y3) /\ (x1 y2 y3))) y0 y1) -> x1 y0 y1.
Definition term7 (a0 : Type') (x0 : type1402 a0) := forall y0 : type1402 a0, ((forall y1 : a0, forall y2 : a0, (x0 y1 y2) -> y0 y1 y2) /\ (@WF a0 y0)) -> @WF a0 x0.
Definition term54 (a0 : Type') (x0 : a0 -> Prop) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := ((x0 x2) /\ ((x0 x3) /\ (x1 x2 x3))) -> True.
Definition term35 (a0 : Type') (x0 : a0 -> Prop) (x1 : type1402 a0) (x2 : a0) := (fun y0 : a0 => (fun y1 : a0 => fun y2 : a0 => (x0 y1) /\ ((x0 y2) /\ (x1 y1 y2))) y0) x2.
Definition term39 (a0 : Type') (x0 : a0 -> Prop) (x1 : type1402 a0) (x2 : a0) := @eq (a0 -> Prop) ((fun y0 : a0 => (fun y1 : a0 => fun y2 : a0 => (x0 y1) /\ ((x0 y2) /\ (x1 y1 y2))) y0) x2).
Definition term33 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term2 (a0 : Type') (x0 : type1402 a0) (x1 : type1402 a0) := ((forall y0 : a0, forall y1 : a0, (x1 y0 y1) -> x0 y0 y1) /\ (@WF a0 x0)) -> @WF a0 x1.
Definition term40 (a0 : Type') (x0 : a0 -> Prop) (x1 : type1402 a0) (x2 : a0) := @eq (a0 -> Prop) ((fun y0 : a0 => fun y1 : a0 => (x0 y0) /\ ((x0 y1) /\ (x1 y0 y1))) x2).
Definition term56 (a0 : Type') := fun y0 : a0 => True.
Definition term42 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term34 (a0 : Type') (x0 : type1402 a0) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term37 (a0 : Type') (x0 : a0 -> Prop) (x1 : type1402 a0) (x2 : a0) := fun y0 : a0 => (x0 x2) /\ ((x0 y0) /\ (x1 x2 y0)).
Definition term10 (a0 : Type') := fun y0 : type1402 a0 => forall y1 : type1402 a0, (forall y2 : a0, forall y3 : a0, (y0 y2 y3) -> y1 y2 y3) -> (@WF a0 y1) -> @WF a0 y0.
Definition term5 (a0 : Type') (x0 : type1402 a0) := fun y0 : type1402 a0 => ((forall y1 : a0, forall y2 : a0, (x0 y1 y2) -> y0 y1 y2) /\ (@WF a0 y0)) -> @WF a0 x0.
Definition term50 (a0 : Type') (x0 : a0 -> Prop) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := (x0 x3) /\ (x1 x2 x3).
Definition term23 (a0 : Type') (x0 : a0 -> Prop) (x1 : type1402 a0) := fun y0 : a0 => fun y1 : a0 => (x0 y0) /\ ((x0 y1) /\ (x1 y0 y1)).
Definition term20 (a0 : Type') (x0 : type1402 a0) := (fun y0 : type1402 a0 => forall y1 : type1402 a0, (forall y2 : a0, forall y3 : a0, (y1 y2 y3) -> y0 y2 y3) -> (@WF a0 y0) -> @WF a0 y1) x0.
Definition term13 (a0 : Type') (x0 : type1402 a0) := (fun y0 : type1402 a0 => forall y1 : type1402 a0, (forall y2 : a0, forall y3 : a0, (y0 y2 y3) -> y1 y2 y3) -> (@WF a0 y1) -> @WF a0 y0) x0.
Definition term15 (a0 : Type') (x0 : type1402 a0) (x1 : type1402 a0) := (@WF a0 x0) -> @WF a0 x1.
Definition term22 (a0 : Type') (x0 : a0 -> Prop) (x1 : type1402 a0) := (forall y0 : a0, forall y1 : a0, ((fun y2 : a0 => fun y3 : a0 => (x0 y2) /\ ((x0 y3) /\ (x1 y2 y3))) y0 y1) -> x1 y0 y1) -> (@WF a0 x1) -> @WF a0 (fun y0 : a0 => fun y1 : a0 => (x0 y0) /\ ((x0 y1) /\ (x1 y0 y1))).
Definition term6 (a0 : Type') (x0 : type1402 a0) := fun y0 : type1402 a0 => (forall y1 : a0, forall y2 : a0, (x0 y1 y2) -> y0 y1 y2) -> (@WF a0 y0) -> @WF a0 x0.
Definition term30 (a0 : Type') (x0 : a0 -> Prop) (x1 : type1402 a0) (x2 : a0) (x3 : a0) (x4 : Prop) := forall y0 : Prop, (((fun y1 : a0 => fun y2 : a0 => (x0 y1) /\ ((x0 y2) /\ (x1 y1 y2))) x2 x3) = x4) -> (x4 -> (x1 x2 x3) = y0) -> (((fun y1 : a0 => fun y2 : a0 => (x0 y1) /\ ((x0 y2) /\ (x1 y1 y2))) x2 x3) -> x1 x2 x3) = (x4 -> y0).
Definition term25 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term0 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 /\ x1) -> x2.
Definition term27 (a0 : Type') (x0 : a0 -> Prop) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := forall y0 : Prop, forall y1 : Prop, (((fun y2 : a0 => fun y3 : a0 => (x0 y2) /\ ((x0 y3) /\ (x1 y2 y3))) x2 x3) = y0) -> (y0 -> (x1 x2 x3) = y1) -> (((fun y2 : a0 => fun y3 : a0 => (x0 y2) /\ ((x0 y3) /\ (x1 y2 y3))) x2 x3) -> x1 x2 x3) = (y0 -> y1).
Definition term26 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term36 (a0 : Type') (x0 : a0 -> Prop) (x1 : type1402 a0) (x2 : a0) := (fun y0 : a0 => fun y1 : a0 => (x0 y0) /\ ((x0 y1) /\ (x1 y0 y1))) x2.
Definition term64 (a0 : Type') := forall y0 : type1402 a0, forall y1 : a0 -> Prop, (@WF a0 y0) -> @WF a0 (fun y2 : a0 => fun y3 : a0 => (y1 y2) /\ ((y1 y3) /\ (y0 y2 y3))).
Definition term18 (a0 : Type') := forall y0 : type1402 a0, forall y1 : type1402 a0, (forall y2 : a0, forall y3 : a0, (y1 y2 y3) -> y0 y2 y3) -> (@WF a0 y0) -> @WF a0 y1.
Definition term12 (a0 : Type') := forall y0 : type1402 a0, forall y1 : type1402 a0, (forall y2 : a0, forall y3 : a0, (y0 y2 y3) -> y1 y2 y3) -> (@WF a0 y1) -> @WF a0 y0.
Definition term11 (a0 : Type') := forall y0 : type1402 a0, forall y1 : type1402 a0, ((forall y2 : a0, forall y3 : a0, (y0 y2 y3) -> y1 y2 y3) /\ (@WF a0 y1)) -> @WF a0 y0.
Definition term55 (a0 : Type') (x0 : a0 -> Prop) (x1 : type1402 a0) (x2 : a0) := fun y0 : a0 => ((fun y1 : a0 => fun y2 : a0 => (x0 y1) /\ ((x0 y2) /\ (x1 y1 y2))) x2 y0) -> x1 x2 y0.
Definition term31 (a0 : Type') (x0 : a0 -> Prop) (x1 : type1402 a0) (x2 : a0) (x3 : a0) (x4 : Prop) (x5 : Prop) := (fun y0 : Prop => (((fun y1 : a0 => fun y2 : a0 => (x0 y1) /\ ((x0 y2) /\ (x1 y1 y2))) x2 x3) = x4) -> (x4 -> (x1 x2 x3) = y0) -> (((fun y1 : a0 => fun y2 : a0 => (x0 y1) /\ ((x0 y2) /\ (x1 y1 y2))) x2 x3) -> x1 x2 x3) = (x4 -> y0)) x5.
Definition term41 (a0 : Type') (x0 : a0 -> Prop) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := (fun y0 : a0 => (x0 x2) /\ ((x0 y0) /\ (x1 x2 y0))) x3.
Definition term44 (a0 : Type') (x0 : a0 -> Prop) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := (x0 x2) /\ ((x0 x3) /\ (x1 x2 x3)).
Definition term9 (a0 : Type') := fun y0 : type1402 a0 => forall y1 : type1402 a0, ((forall y2 : a0, forall y3 : a0, (y0 y2 y3) -> y1 y2 y3) /\ (@WF a0 y1)) -> @WF a0 y0.
Definition term48 (a0 : Type') (x0 : a0 -> Prop) (x1 : type1402 a0) (x2 : a0) (x3 : a0) (x4 : Prop) := (((fun y0 : a0 => fun y1 : a0 => (x0 y0) /\ ((x0 y1) /\ (x1 y0 y1))) x2 x3) = ((x0 x2) /\ ((x0 x3) /\ (x1 x2 x3)))) -> (((x0 x2) /\ ((x0 x3) /\ (x1 x2 x3))) -> (x1 x2 x3) = x4) -> (((fun y0 : a0 => fun y1 : a0 => (x0 y0) /\ ((x0 y1) /\ (x1 y0 y1))) x2 x3) -> x1 x2 x3) = (((x0 x2) /\ ((x0 x3) /\ (x1 x2 x3))) -> x4).
Definition term61 (a0 : Type') (x0 : a0 -> Prop) (x1 : type1402 a0) := forall y0 : a0, forall y1 : a0, ((fun y2 : a0 => fun y3 : a0 => (x0 y2) /\ ((x0 y3) /\ (x1 y2 y3))) y0 y1) -> x1 y0 y1.
Definition term4 (a0 : Type') (x0 : type1402 a0) (x1 : type1402 a0) := forall y0 : a0, forall y1 : a0, (x0 y0 y1) -> x1 y0 y1.
Definition term46 (a0 : Type') (x0 : a0 -> Prop) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := @eq Prop ((fun y0 : a0 => (fun y1 : a0 => (x0 x2) /\ ((x0 y1) /\ (x1 x2 y1))) y0) x3).
Definition term38 (a0 : Type') (x0 : a0 -> Prop) (x1 : type1402 a0) := fun y0 : a0 => (fun y1 : a0 => fun y2 : a0 => (x0 y1) /\ ((x0 y2) /\ (x1 y1 y2))) y0.
Definition term57 (a0 : Type') (x0 : a0 -> Prop) (x1 : type1402 a0) (x2 : a0) := forall y0 : a0, ((fun y1 : a0 => fun y2 : a0 => (x0 y1) /\ ((x0 y2) /\ (x1 y1 y2))) x2 y0) -> x1 x2 y0.
Definition term16 (a0 : Type') (x0 : type1402 a0) (x1 : type1402 a0) := (forall y0 : type1402 a0, forall y1 : type1402 a0, (forall y2 : a0, forall y3 : a0, (y0 y2 y3) -> y1 y2 y3) -> (@WF a0 y1) -> @WF a0 y0) -> (@WF a0 x0) -> @WF a0 x1.
Definition term62 (a0 : Type') (x0 : a0 -> Prop) (x1 : type1402 a0) := (@WF a0 x1) -> @WF a0 (fun y0 : a0 => fun y1 : a0 => (x0 y0) /\ ((x0 y1) /\ (x1 y0 y1))).
Definition term29 (a0 : Type') (x0 : a0 -> Prop) (x1 : type1402 a0) (x2 : a0) (x3 : a0) (x4 : Prop) := (fun y0 : Prop => forall y1 : Prop, (((fun y2 : a0 => fun y3 : a0 => (x0 y2) /\ ((x0 y3) /\ (x1 y2 y3))) x2 x3) = y0) -> (y0 -> (x1 x2 x3) = y1) -> (((fun y2 : a0 => fun y3 : a0 => (x0 y2) /\ ((x0 y3) /\ (x1 y2 y3))) x2 x3) -> x1 x2 x3) = (y0 -> y1)) x4.
Definition term49 (a0 : Type') (x0 : a0 -> Prop) (x1 : type1402 a0) (x2 : a0) (x3 : a0) (x4 : Prop) := (((x0 x2) /\ ((x0 x3) /\ (x1 x2 x3))) -> (x1 x2 x3) = x4) -> (((fun y0 : a0 => fun y1 : a0 => (x0 y0) /\ ((x0 y1) /\ (x1 y0 y1))) x2 x3) -> x1 x2 x3) = (((x0 x2) /\ ((x0 x3) /\ (x1 x2 x3))) -> x4).
