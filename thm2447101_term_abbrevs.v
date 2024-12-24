Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term17 (a0 : Type') := fun y0 : Prop => forall y1 : a0, forall y2 : a0, (~ (y2 = y1)) -> ((y2 = y1) \/ y0) -> y0.
Definition term16 (a0 : Type') := fun y0 : Prop => forall y1 : a0, forall y2 : a0, (~ ((~ (y2 = y1)) -> ((y2 = y1) \/ y0) -> y0)) -> False.
Definition term22 (a0 : Type') := forall y0 : Prop, (fun y1 : Prop => forall y2 : a0, forall y3 : a0, (~ (y3 = y2)) -> ((y3 = y2) \/ y1) -> y1) y0.
Definition term27 (a0 : Type') := @eq Prop (forall y0 : Prop, forall y1 : a0, forall y2 : a0, (~ (y2 = y1)) -> ((y2 = y1) \/ y0) -> y0).
Definition term6 (x0 : Prop) := ~ (~ x0).
Definition term12 (a0 : Type') (x0 : Prop) := fun y0 : a0 => forall y1 : a0, (~ ((~ (y1 = y0)) -> ((y1 = y0) \/ x0) -> x0)) -> False.
Definition term45 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term25 (a0 : Type') := fun y0 : Prop => (fun y1 : Prop => forall y2 : a0, forall y3 : a0, (~ (y3 = y2)) -> ((y3 = y2) \/ y1) -> y1) y0.
Definition term37 (a0 : Type') (x0 : a0) (x1 : a0) := imp (~ (x0 = x1)).
Definition term49 (a0 : Type') (x0 : a0) (x1 : a0) := (x0 = x1) \/ False.
Definition term44 (a0 : Type') := forall y0 : a0, True.
Definition term11 (a0 : Type') (x0 : a0) (x1 : Prop) := forall y0 : a0, (~ (y0 = x0)) -> ((y0 = x0) \/ x1) -> x1.
Definition term34 (a0 : Type') := (forall y0 : a0, forall y1 : a0, (~ (y1 = y0)) -> ((y1 = y0) \/ True) -> True) /\ (forall y0 : a0, forall y1 : a0, (~ (y1 = y0)) -> ((y1 = y0) \/ False) -> False).
Definition term7 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : Prop) := (~ (x0 = x1)) -> ((x0 = x1) \/ x2) -> x2.
Definition term10 (a0 : Type') (x0 : a0) (x1 : Prop) := forall y0 : a0, (~ ((~ (y0 = x0)) -> ((y0 = x0) \/ x1) -> x1)) -> False.
Definition term48 (a0 : Type') (x0 : a0) (x1 : a0) := ~ ((x0 = x1) \/ False).
Definition term21 (x0 : Prop -> Prop) := (x0 True) /\ (x0 False).
Definition term54 (a0 : Type') := fun y0 : a0 => forall y1 : a0, (~ (y1 = y0)) -> ((y1 = y0) \/ False) -> False.
Definition term56 (a0 : Type') (x0 : Prop) (x1 : a0) := (fun y0 : a0 => forall y1 : a0, (~ ((~ (y1 = y0)) -> ((y1 = y0) \/ x0) -> x0)) -> False) x1.
Definition term2 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : Prop) := ((~ ((~ (x0 = x1)) -> ((x0 = x1) \/ x2) -> x2)) -> False) -> (~ ((~ (x0 = x1)) -> ((x0 = x1) \/ x2) -> x2)) -> False.
Definition term42 (a0 : Type') := fun y0 : a0 => True.
Definition term38 (a0 : Type') (x0 : a0) (x1 : a0) := (~ (x0 = x1)) -> ((x0 = x1) \/ True) -> True.
Definition term8 (a0 : Type') (x0 : a0) (x1 : Prop) := fun y0 : a0 => (~ ((~ (y0 = x0)) -> ((y0 = x0) \/ x1) -> x1)) -> False.
Definition term52 (a0 : Type') (x0 : a0) := fun y0 : a0 => (~ (y0 = x0)) -> ((y0 = x0) \/ False) -> False.
Definition term28 (a0 : Type') := (fun y0 : Prop => forall y1 : a0, forall y2 : a0, (~ (y2 = y1)) -> ((y2 = y1) \/ y0) -> y0) True.
Definition term39 (a0 : Type') (x0 : a0) (x1 : a0) := (~ (x0 = x1)) -> True.
Definition term26 (a0 : Type') := @eq Prop (forall y0 : Prop, (fun y1 : Prop => forall y2 : a0, forall y3 : a0, (~ (y3 = y2)) -> ((y3 = y2) \/ y1) -> y1) y0).
Definition term31 (a0 : Type') := and (forall y0 : a0, forall y1 : a0, (~ (y1 = y0)) -> ((y1 = y0) \/ True) -> True).
Definition term35 (a0 : Type') (x0 : a0) (x1 : a0) := ((x0 = x1) \/ True) -> True.
Definition term46 (a0 : Type') := fun y0 : a0 => forall y1 : a0, (~ (y1 = y0)) -> ((y1 = y0) \/ True) -> True.
Definition term3 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : Prop) := (((~ ((~ (x0 = x1)) -> ((x0 = x1) \/ x2) -> x2)) -> False) -> (~ ((~ (x0 = x1)) -> ((x0 = x1) \/ x2) -> x2)) -> False) -> (~ ((~ (x0 = x1)) -> ((x0 = x1) \/ x2) -> x2)) -> False.
Definition term19 (a0 : Type') := forall y0 : Prop, forall y1 : a0, forall y2 : a0, (~ (y2 = y1)) -> ((y2 = y1) \/ y0) -> y0.
Definition term18 (a0 : Type') := forall y0 : Prop, forall y1 : a0, forall y2 : a0, (~ ((~ (y2 = y1)) -> ((y2 = y1) \/ y0) -> y0)) -> False.
Definition term40 (a0 : Type') (x0 : a0) (x1 : a0) := ~ (x0 = x1).
Definition term23 (a0 : Type') := ((fun y0 : Prop => forall y1 : a0, forall y2 : a0, (~ (y2 = y1)) -> ((y2 = y1) \/ y0) -> y0) True) /\ ((fun y0 : Prop => forall y1 : a0, forall y2 : a0, (~ (y2 = y1)) -> ((y2 = y1) \/ y0) -> y0) False).
Definition term41 (a0 : Type') (x0 : a0) := fun y0 : a0 => (~ (y0 = x0)) -> ((y0 = x0) \/ True) -> True.
Definition term0 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : Prop) := ~ ((~ (x0 = x1)) -> ((x0 = x1) \/ x2) -> x2).
Definition term32 (a0 : Type') := (fun y0 : Prop => forall y1 : a0, forall y2 : a0, (~ (y2 = y1)) -> ((y2 = y1) \/ y0) -> y0) False.
Definition term20 (x0 : Prop -> Prop) := forall y0 : Prop, x0 y0.
Definition term47 (a0 : Type') (x0 : a0) (x1 : a0) := ((x0 = x1) \/ False) -> False.
Definition term53 (a0 : Type') (x0 : a0) := forall y0 : a0, (~ (y0 = x0)) -> ((y0 = x0) \/ False) -> False.
Definition term33 (a0 : Type') := forall y0 : a0, forall y1 : a0, (~ (y1 = y0)) -> ((y1 = y0) \/ False) -> False.
Definition term29 (a0 : Type') := forall y0 : a0, forall y1 : a0, (~ (y1 = y0)) -> ((y1 = y0) \/ True) -> True.
Definition term15 (a0 : Type') (x0 : Prop) := forall y0 : a0, forall y1 : a0, (~ (y1 = y0)) -> ((y1 = y0) \/ x0) -> x0.
Definition term57 (a0 : Type') (x0 : a0) (x1 : Prop) (x2 : a0) := (fun y0 : a0 => (~ ((~ (y0 = x0)) -> ((y0 = x0) \/ x1) -> x1)) -> False) x2.
Definition term55 (a0 : Type') (x0 : Prop) := (fun y0 : Prop => forall y1 : a0, forall y2 : a0, (~ ((~ (y2 = y1)) -> ((y2 = y1) \/ y0) -> y0)) -> False) x0.
Definition term24 (a0 : Type') (x0 : Prop) := (fun y0 : Prop => forall y1 : a0, forall y2 : a0, (~ (y2 = y1)) -> ((y2 = y1) \/ y0) -> y0) x0.
Definition term50 (a0 : Type') (x0 : a0) (x1 : a0) := (~ (x0 = x1)) -> ((x0 = x1) \/ False) -> False.
Definition term1 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : Prop) := (~ ((~ (x0 = x1)) -> ((x0 = x1) \/ x2) -> x2)) -> False.
Definition term5 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : Prop) := ~ (~ ((~ (x0 = x1)) -> ((x0 = x1) \/ x2) -> x2)).
Definition term43 (a0 : Type') (x0 : a0) := forall y0 : a0, (~ (y0 = x0)) -> ((y0 = x0) \/ True) -> True.
Definition term4 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : Prop) := (((~ ((~ (x0 = x1)) -> ((x0 = x1) \/ x2) -> x2)) -> False) -> (~ ((~ (x0 = x1)) -> ((x0 = x1) \/ x2) -> x2)) -> False) -> ((~ ((~ (x0 = x1)) -> ((x0 = x1) \/ x2) -> x2)) -> False) -> (~ ((~ (x0 = x1)) -> ((x0 = x1) \/ x2) -> x2)) -> False.
Definition term13 (a0 : Type') (x0 : Prop) := fun y0 : a0 => forall y1 : a0, (~ (y1 = y0)) -> ((y1 = y0) \/ x0) -> x0.
Definition term9 (a0 : Type') (x0 : a0) (x1 : Prop) := fun y0 : a0 => (~ (y0 = x0)) -> ((y0 = x0) \/ x1) -> x1.
Definition term36 (a0 : Type') (x0 : a0) (x1 : a0) := (x0 = x1) \/ True.
Definition term51 (a0 : Type') (x0 : a0) (x1 : a0) := (~ (x0 = x1)) -> ~ (x0 = x1).
Definition term30 (a0 : Type') := and ((fun y0 : Prop => forall y1 : a0, forall y2 : a0, (~ (y2 = y1)) -> ((y2 = y1) \/ y0) -> y0) True).
Definition term14 (a0 : Type') (x0 : Prop) := forall y0 : a0, forall y1 : a0, (~ ((~ (y1 = y0)) -> ((y1 = y0) \/ x0) -> x0)) -> False.
