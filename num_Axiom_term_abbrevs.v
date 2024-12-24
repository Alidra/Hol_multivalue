Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term19 (a0 : Type') := forall y0 : a0, forall y1 : type1423 a0, @ex1 (nat -> a0) (fun y2 : nat -> a0 => ((y2 (NUMERAL 0)) = y0) /\ (forall y3 : nat, (y2 (S y3)) = (y1 (y2 y3) y3))).
Definition term18 (a0 : Type') := forall y0 : a0, forall y1 : type1423 a0, @ex1 (nat -> a0) (fun y2 : nat -> a0 => ((y2 0) = y0) /\ (forall y3 : nat, (y2 (S y3)) = (y1 (y2 y3) y3))).
Definition term17 (a0 : Type') := fun y0 : a0 => forall y1 : type1423 a0, @ex1 (nat -> a0) (fun y2 : nat -> a0 => ((y2 (NUMERAL 0)) = y0) /\ (forall y3 : nat, (y2 (S y3)) = (y1 (y2 y3) y3))).
Definition term16 (a0 : Type') := fun y0 : a0 => forall y1 : type1423 a0, @ex1 (nat -> a0) (fun y2 : nat -> a0 => ((y2 0) = y0) /\ (forall y3 : nat, (y2 (S y3)) = (y1 (y2 y3) y3))).
Definition term0 (a0 : Type') (x0 : nat -> a0) := x0 (NUMERAL 0).
Definition term15 (a0 : Type') (x0 : a0) := forall y0 : type1423 a0, @ex1 (nat -> a0) (fun y1 : nat -> a0 => ((y1 (NUMERAL 0)) = x0) /\ (forall y2 : nat, (y1 (S y2)) = (y0 (y1 y2) y2))).
Definition term14 (a0 : Type') (x0 : a0) := forall y0 : type1423 a0, @ex1 (nat -> a0) (fun y1 : nat -> a0 => ((y1 0) = x0) /\ (forall y2 : nat, (y1 (S y2)) = (y0 (y1 y2) y2))).
Definition term9 (a0 : Type') (x0 : a0) (x1 : type1423 a0) := fun y0 : nat -> a0 => ((y0 (NUMERAL 0)) = x0) /\ (forall y1 : nat, (y0 (S y1)) = (x1 (y0 y1) y1)).
Definition term8 (a0 : Type') (x0 : a0) (x1 : type1423 a0) := fun y0 : nat -> a0 => ((y0 0) = x0) /\ (forall y1 : nat, (y0 (S y1)) = (x1 (y0 y1) y1)).
Definition term11 (a0 : Type') (x0 : a0) (x1 : type1423 a0) := @ex1 (nat -> a0) (fun y0 : nat -> a0 => ((y0 (NUMERAL 0)) = x0) /\ (forall y1 : nat, (y0 (S y1)) = (x1 (y0 y1) y1))).
Definition term10 (a0 : Type') (x0 : a0) (x1 : type1423 a0) := @ex1 (nat -> a0) (fun y0 : nat -> a0 => ((y0 0) = x0) /\ (forall y1 : nat, (y0 (S y1)) = (x1 (y0 y1) y1))).
Definition term4 (a0 : Type') (x0 : nat -> a0) (x1 : a0) := and ((x0 (NUMERAL 0)) = x1).
Definition term2 (a0 : Type') (x0 : nat -> a0) := @eq a0 (x0 (NUMERAL 0)).
Definition term6 (a0 : Type') (x0 : a0) (x1 : type1423 a0) (x2 : nat -> a0) := ((x2 0) = x0) /\ (forall y0 : nat, (x2 (S y0)) = (x1 (x2 y0) y0)).
Definition term13 (a0 : Type') (x0 : a0) := fun y0 : type1423 a0 => @ex1 (nat -> a0) (fun y1 : nat -> a0 => ((y1 (NUMERAL 0)) = x0) /\ (forall y2 : nat, (y1 (S y2)) = (y0 (y1 y2) y2))).
Definition term12 (a0 : Type') (x0 : a0) := fun y0 : type1423 a0 => @ex1 (nat -> a0) (fun y1 : nat -> a0 => ((y1 0) = x0) /\ (forall y2 : nat, (y1 (S y2)) = (y0 (y1 y2) y2))).
Definition term3 (a0 : Type') (x0 : nat -> a0) (x1 : a0) := and ((x0 0) = x1).
Definition term7 (a0 : Type') (x0 : a0) (x1 : type1423 a0) (x2 : nat -> a0) := ((x2 (NUMERAL 0)) = x0) /\ (forall y0 : nat, (x2 (S y0)) = (x1 (x2 y0) y0)).
Definition term5 (a0 : Type') (x0 : type1423 a0) (x1 : nat -> a0) := forall y0 : nat, (x1 (S y0)) = (x0 (x1 y0) y0).
Definition term1 (a0 : Type') (x0 : nat -> a0) := @eq a0 (x0 0).
