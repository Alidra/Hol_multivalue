Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term23 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.mul y0 y1) = (Nat.mul y0 y2)) = ((y0 = (NUMERAL 0)) \/ (y1 = y2))) x0.
Definition term8 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((Nat.mul x1 x0) = (Nat.mul x1 x2)).
Definition term7 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((Nat.mul x0 x2) = (Nat.mul x1 x2)).
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, (y0 \/ y1) = (y1 \/ y0)) x0.
Definition term10 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (NUMERAL 0)) \/ (x1 = x2).
Definition term9 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x1) \/ (x2 = (NUMERAL 0)).
Definition term13 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Nat.mul x0 y0) = (Nat.mul x1 y0)) = ((x0 = x1) \/ (y0 = (NUMERAL 0))).
Definition term25 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.mul x0 y0) = (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (y0 = y1))) x1.
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (x0 \/ y0) = (y0 \/ x0)) x1.
Definition term24 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Nat.mul x0 y0) = (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (y0 = y1)).
Definition term22 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Nat.mul y2 y0) = (Nat.mul y2 y1)) = ((y2 = (NUMERAL 0)) \/ (y0 = y1)).
Definition term21 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Nat.mul y0 y2) = (Nat.mul y1 y2)) = ((y0 = y1) \/ (y2 = (NUMERAL 0))).
Definition term18 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Nat.mul y1 x0) = (Nat.mul y1 y0)) = ((y1 = (NUMERAL 0)) \/ (x0 = y0)).
Definition term17 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Nat.mul x0 y1) = (Nat.mul y0 y1)) = ((x0 = y0) \/ (y1 = (NUMERAL 0))).
Definition term26 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Nat.mul x0 x1) = (Nat.mul x0 y0)) = ((x0 = (NUMERAL 0)) \/ (x1 = y0)).
Definition term14 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Nat.mul y0 x0) = (Nat.mul y0 x1)) = ((y0 = (NUMERAL 0)) \/ (x0 = x1)).
Definition term4 (x0 : nat) := forall y0 : nat, (Nat.mul x0 y0) = (Nat.mul y0 x0).
Definition term5 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul x0 y0) = (Nat.mul y0 x0)) x1.
Definition term12 (x0 : nat) (x1 : nat) := fun y0 : nat => ((Nat.mul y0 x0) = (Nat.mul y0 x1)) = ((y0 = (NUMERAL 0)) \/ (x0 = x1)).
Definition term3 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) x0.
Definition term27 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Nat.mul x0 x1) = (Nat.mul x0 y0)) = ((x0 = (NUMERAL 0)) \/ (x1 = y0))) x2.
Definition term6 (x0 : nat) (x1 : nat) := @eq nat (Nat.mul x0 x1).
Definition term1 (x0 : Prop) := forall y0 : Prop, (x0 \/ y0) = (y0 \/ x0).
Definition term11 (x0 : nat) (x1 : nat) := fun y0 : nat => ((Nat.mul x0 y0) = (Nat.mul x1 y0)) = ((x0 = x1) \/ (y0 = (NUMERAL 0))).
Definition term16 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((Nat.mul y1 x0) = (Nat.mul y1 y0)) = ((y1 = (NUMERAL 0)) \/ (x0 = y0)).
Definition term15 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((Nat.mul x0 y1) = (Nat.mul y0 y1)) = ((x0 = y0) \/ (y1 = (NUMERAL 0))).
Definition term20 := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.mul y2 y0) = (Nat.mul y2 y1)) = ((y2 = (NUMERAL 0)) \/ (y0 = y1)).
Definition term19 := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.mul y0 y2) = (Nat.mul y1 y2)) = ((y0 = y1) \/ (y2 = (NUMERAL 0))).
