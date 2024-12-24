Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term51 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (False /\ x0) -> x1 = x2.
Definition term67 (x0 : type1605) := ((forall y0 : nat, x0 y0 y0) /\ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2) /\ (forall y0 : nat, x0 y0 (S y0)))) -> forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1.
Definition term45 (x0 : Prop) := imp (~ x0).
Definition term8 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := @eq Prop (((x0 /\ x1) -> x3 = x2) -> (x0 /\ (x1 /\ x2)) -> x3).
Definition term36 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (y0 = x0) -> x0 -> y0) x1.
Definition term22 (x0 : Prop) (x1 : Prop) := fun y0 : Prop => (y0 -> x1 = x0) -> (y0 /\ x0) -> x1.
Definition term63 (x0 : type1605) := forall y0 : nat, x0 y0 (S y0).
Definition term57 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 /\ (x1 /\ x2)) -> x3.
Definition term33 (x0 : Prop) (x1 : Prop) := (True /\ x0) -> x1.
Definition term42 (x0 : Prop) := (False = x0) -> x0 -> False.
Definition term10 (x0 : Prop) (x1 : Prop) (x2 : Prop) := ((False /\ x0) -> x2 = x1) -> (False /\ (x0 /\ x1)) -> x2.
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := ((True /\ x0) -> x2 = x1) -> (True /\ (x0 /\ x1)) -> x2.
Definition term48 (x0 : Prop) (x1 : Prop) := imp (False -> x0 = x1).
Definition term13 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 -> x1 = x2.
Definition term32 (x0 : Prop) (x1 : Prop) := imp (x0 = x1).
Definition term49 (x0 : Prop) := imp (False /\ x0).
Definition term56 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 /\ x1) -> x2 = x3.
Definition term16 (x0 : Prop) (x1 : Prop) := True /\ (x0 /\ x1).
Definition term43 (x0 : Prop) := imp (True = x0).
Definition term11 (x0 : Prop) := imp (True /\ x0).
Definition term54 (x0 : Prop) (x1 : Prop) := imp (False /\ (x0 /\ x1)).
Definition term25 (x0 : Prop) (x1 : Prop) := (True -> x1 = x0) -> (True /\ x0) -> x1.
Definition term52 (x0 : Prop) (x1 : Prop) (x2 : Prop) := imp ((False /\ x0) -> x1 = x2).
Definition term14 (x0 : Prop) (x1 : Prop) (x2 : Prop) := imp ((True /\ x0) -> x1 = x2).
Definition term65 (x0 : type1605) := (fun y0 : type1605 => ((forall y1 : nat, y0 y1 y1) /\ (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 y1 y2) /\ (y0 y2 y3)) -> y0 y1 y3)) -> (forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> y0 y1 y2) = (forall y1 : nat, y0 y1 (S y1))) x0.
Definition term55 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (False /\ (x0 /\ x1)) -> x2.
Definition term7 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := ((x0 /\ x1) -> x3 = x2) -> (x0 /\ (x1 /\ x2)) -> x3.
Definition term2 (x0 : Prop) (x1 : Prop) (x2 : Prop) := fun y0 : Prop => ((y0 /\ x0) -> x2 = x1) -> (y0 /\ (x0 /\ x1)) -> x2.
Definition term34 (x0 : Prop) (x1 : Prop) := (x1 = x0) -> x0 -> x1.
Definition term19 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (True /\ (x0 /\ x1)) -> x2.
Definition term66 (x0 : type1605) := ((forall y0 : nat, x0 y0 y0) /\ (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1) = (forall y0 : nat, x0 y0 (S y0)).
Definition term29 (x0 : Prop) (x1 : Prop) := (False -> x1 = x0) -> (False /\ x0) -> x1.
Definition term58 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (((x0 /\ x1) -> x3 = x2) -> (x0 /\ (x1 /\ x2)) -> x3) -> (x0 /\ (x1 /\ x2)) -> x3.
Definition term64 (x0 : type1605) := forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1.
Definition term62 (x0 : type1605) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2.
Definition term38 (x0 : Prop) := (True = x0) -> x0 -> True.
Definition term23 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (y0 -> x1 = x0) -> (y0 /\ x0) -> x1) x2.
Definition term31 (x0 : Prop) (x1 : Prop) := imp (True -> x0 = x1).
Definition term60 (x0 : type1605) := (((forall y0 : nat, x0 y0 y0) /\ (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1) = (forall y0 : nat, x0 y0 (S y0))) -> ((forall y0 : nat, x0 y0 y0) /\ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2) /\ (forall y0 : nat, x0 y0 (S y0)))) -> forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1.
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => ((y0 /\ x0) -> x2 = x1) -> (y0 /\ (x0 /\ x1)) -> x2) True.
Definition term39 (x0 : Prop) (x1 : Prop) := @eq Prop ((fun y0 : Prop => (y0 = x0) -> x0 -> y0) x1).
Definition term9 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => ((y0 /\ x0) -> x2 = x1) -> (y0 /\ (x0 /\ x1)) -> x2) False.
Definition term24 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (y0 -> x1 = x0) -> (y0 /\ x0) -> x1) True.
Definition term40 (x0 : Prop) (x1 : Prop) := @eq Prop ((x1 = x0) -> x0 -> x1).
Definition term46 (x0 : Prop) := (~ x0) -> ~ x0.
Definition term53 (x0 : Prop) (x1 : Prop) := False /\ (x0 /\ x1).
Definition term1 (x0 : Prop) := (x0 = True) \/ (x0 = False).
Definition term20 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 /\ x1) -> x2.
Definition term68 := forall y0 : type1605, ((forall y1 : nat, y0 y1 y1) /\ ((forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 y1 y2) /\ (y0 y2 y3)) -> y0 y1 y3) /\ (forall y1 : nat, y0 y1 (S y1)))) -> forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> y0 y1 y2.
Definition term41 (x0 : Prop) := (fun y0 : Prop => (y0 = x0) -> x0 -> y0) False.
Definition term44 (x0 : Prop) := imp (False = x0).
Definition term47 (x0 : Prop) (x1 : Prop) := False -> x0 = x1.
Definition term37 (x0 : Prop) := (fun y0 : Prop => (y0 = x0) -> x0 -> y0) True.
Definition term35 (x0 : Prop) := fun y0 : Prop => (y0 = x0) -> x0 -> y0.
Definition term21 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 -> x2 = x1) -> (x0 /\ x1) -> x2.
Definition term27 (x0 : Prop) (x1 : Prop) (x2 : Prop) := @eq Prop ((x0 -> x2 = x1) -> (x0 /\ x1) -> x2).
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := @eq Prop ((fun y0 : Prop => ((y0 /\ x0) -> x2 = x1) -> (y0 /\ (x0 /\ x1)) -> x2) x3).
Definition term30 (x0 : Prop) (x1 : Prop) := True -> x0 = x1.
Definition term18 (x0 : Prop) (x1 : Prop) := imp (x0 /\ x1).
Definition term3 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (fun y0 : Prop => ((y0 /\ x0) -> x2 = x1) -> (y0 /\ (x0 /\ x1)) -> x2) x3.
Definition term15 (x0 : Prop) (x1 : Prop) (x2 : Prop) := imp (x0 -> x1 = x2).
Definition term0 (x0 : Prop) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) x0.
Definition term50 (x0 : Prop) (x1 : Prop) := (False /\ x0) -> x1.
Definition term59 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (((x0 /\ x1) -> x3 = x2) -> (x0 /\ (x1 /\ x2)) -> x3) -> ((x0 /\ x1) -> x3 = x2) -> (x0 /\ (x1 /\ x2)) -> x3.
Definition term17 (x0 : Prop) (x1 : Prop) := imp (True /\ (x0 /\ x1)).
Definition term28 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (y0 -> x1 = x0) -> (y0 /\ x0) -> x1) False.
Definition term12 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (True /\ x0) -> x1 = x2.
Definition term26 (x0 : Prop) (x1 : Prop) (x2 : Prop) := @eq Prop ((fun y0 : Prop => (y0 -> x1 = x0) -> (y0 /\ x0) -> x1) x2).
Definition term61 (x0 : type1605) := forall y0 : nat, x0 y0 y0.
