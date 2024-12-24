Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term24 := @eq Prop (forall y0 : type1670, exists y1 : nat -> Prop, exists y2 : nat -> nat, forall y3 : Prop, forall y4 : nat, ((y1 (NUMSUM y3 y4)) = y3) /\ ((y2 (NUMSUM y3 y4)) = y4)).
Definition term23 := @eq Prop (forall y0 : type1670, exists y1 : nat -> Prop, (fun y2 : type1670 => fun y3 : nat -> Prop => exists y4 : nat -> nat, forall y5 : Prop, forall y6 : nat, ((y3 (NUMSUM y5 y6)) = y5) /\ ((y4 (NUMSUM y5 y6)) = y6)) y0 y1).
Definition term32 := fun y0 : type1260 => forall y1 : type1670, (fun y2 : type1670 => fun y3 : nat -> Prop => exists y4 : nat -> nat, forall y5 : Prop, forall y6 : nat, ((y3 (NUMSUM y5 y6)) = y5) /\ ((y4 (NUMSUM y5 y6)) = y6)) y1 (y0 y1).
Definition term19 (x0 : type1670) := fun y0 : nat -> Prop => (fun y1 : type1670 => fun y2 : nat -> Prop => exists y3 : nat -> nat, forall y4 : Prop, forall y5 : nat, ((y2 (NUMSUM y4 y5)) = y4) /\ ((y3 (NUMSUM y4 y5)) = y5)) x0 y0.
Definition term0 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1412 a0 a1 a2) := (fun y0 : type1412 a0 a1 a2 => (forall y1 : a0, forall y2 : a1, forall y3 : a0, forall y4 : a1, ((y0 y1 y2) = (y0 y3 y4)) = ((y1 = y3) /\ (y2 = y4))) -> exists y1 : a2 -> a0, exists y2 : a2 -> a1, forall y3 : a0, forall y4 : a1, ((y1 (y0 y3 y4)) = y3) /\ ((y2 (y0 y3 y4)) = y4)) x0.
Definition term15 := fun y0 : nat -> Prop => exists y1 : nat -> nat, forall y2 : Prop, forall y3 : nat, ((y0 (NUMSUM y2 y3)) = y2) /\ ((y1 (NUMSUM y2 y3)) = y3).
Definition term22 := fun y0 : type1670 => exists y1 : nat -> Prop, exists y2 : nat -> nat, forall y3 : Prop, forall y4 : nat, ((y1 (NUMSUM y3 y4)) = y3) /\ ((y2 (NUMSUM y3 y4)) = y4).
Definition term4 := exists y0 : nat -> Prop, exists y1 : nat -> nat, forall y2 : Prop, forall y3 : nat, ((y0 (NUMSUM y2 y3)) = y2) /\ ((y1 (NUMSUM y2 y3)) = y3).
Definition term7 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term12 := exists y0 : type1260, forall y1 : type1670, (fun y2 : type1670 => fun y3 : nat -> Prop => exists y4 : nat -> nat, forall y5 : Prop, forall y6 : nat, ((y3 (NUMSUM y5 y6)) = y5) /\ ((y4 (NUMSUM y5 y6)) = y6)) y1 (y0 y1).
Definition term10 (x0 : type1257) := exists y0 : type1260, forall y1 : type1670, x0 y1 (y0 y1).
Definition term30 (x0 : type1260) := forall y0 : type1670, (fun y1 : type1670 => fun y2 : nat -> Prop => exists y3 : nat -> nat, forall y4 : Prop, forall y5 : nat, ((y2 (NUMSUM y4 y5)) = y4) /\ ((y3 (NUMSUM y4 y5)) = y5)) y0 (x0 y0).
Definition term36 := fun y0 : type347 => y0 (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> nat -> Prop) y0).
Definition term33 := fun y0 : type1260 => forall y1 : type1670, exists y2 : nat -> nat, forall y3 : Prop, forall y4 : nat, ((y0 y1 (NUMSUM y3 y4)) = y3) /\ ((y2 (NUMSUM y3 y4)) = y4).
Definition term14 (x0 : type1670) := (fun y0 : type1670 => fun y1 : nat -> Prop => exists y2 : nat -> nat, forall y3 : Prop, forall y4 : nat, ((y1 (NUMSUM y3 y4)) = y3) /\ ((y2 (NUMSUM y3 y4)) = y4)) x0.
Definition term13 := fun y0 : type1670 => fun y1 : nat -> Prop => exists y2 : nat -> nat, forall y3 : Prop, forall y4 : nat, ((y1 (NUMSUM y3 y4)) = y3) /\ ((y2 (NUMSUM y3 y4)) = y4).
Definition term35 (a0 : Type') := fun y0 : a0 -> Prop => y0 (@ε a0 y0).
Definition term38 := (fun y0 : type1260 => forall y1 : type1670, exists y2 : nat -> nat, forall y3 : Prop, forall y4 : nat, ((y0 y1 (NUMSUM y3 y4)) = y3) /\ ((y2 (NUMSUM y3 y4)) = y4)) (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> nat -> Prop) (fun y0 : type1260 => forall y1 : type1670, exists y2 : nat -> nat, forall y3 : Prop, forall y4 : nat, ((y0 y1 (NUMSUM y3 y4)) = y3) /\ ((y2 (NUMSUM y3 y4)) = y4))).
Definition term37 := (fun y0 : type347 => y0 (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> nat -> Prop) y0)) (fun y0 : type1260 => forall y1 : type1670, exists y2 : nat -> nat, forall y3 : Prop, forall y4 : nat, ((y0 y1 (NUMSUM y3 y4)) = y3) /\ ((y2 (NUMSUM y3 y4)) = y4)).
Definition term20 (x0 : type1670) := exists y0 : nat -> Prop, (fun y1 : type1670 => fun y2 : nat -> Prop => exists y3 : nat -> nat, forall y4 : Prop, forall y5 : nat, ((y2 (NUMSUM y4 y5)) = y4) /\ ((y3 (NUMSUM y4 y5)) = y5)) x0 y0.
Definition term28 (x0 : type1260) := fun y0 : type1670 => (fun y1 : type1670 => fun y2 : nat -> Prop => exists y3 : nat -> nat, forall y4 : Prop, forall y5 : nat, ((y2 (NUMSUM y4 y5)) = y4) /\ ((y3 (NUMSUM y4 y5)) = y5)) y0 (x0 y0).
Definition term26 (x0 : type1260) (x1 : type1670) := (fun y0 : nat -> Prop => exists y1 : nat -> nat, forall y2 : Prop, forall y3 : nat, ((y0 (NUMSUM y2 y3)) = y2) /\ ((y1 (NUMSUM y2 y3)) = y3)) (x0 x1).
Definition term34 := exists y0 : type1260, forall y1 : type1670, exists y2 : nat -> nat, forall y3 : Prop, forall y4 : nat, ((y0 y1 (NUMSUM y3 y4)) = y3) /\ ((y2 (NUMSUM y3 y4)) = y4).
Definition term27 (x0 : type1260) (x1 : type1670) := exists y0 : nat -> nat, forall y1 : Prop, forall y2 : nat, ((x0 x1 (NUMSUM y1 y2)) = y1) /\ ((y0 (NUMSUM y1 y2)) = y2).
Definition term18 (x0 : nat -> Prop) := exists y0 : nat -> nat, forall y1 : Prop, forall y2 : nat, ((x0 (NUMSUM y1 y2)) = y1) /\ ((y0 (NUMSUM y1 y2)) = y2).
Definition term16 (x0 : type1670) (x1 : nat -> Prop) := (fun y0 : type1670 => fun y1 : nat -> Prop => exists y2 : nat -> nat, forall y3 : Prop, forall y4 : nat, ((y1 (NUMSUM y3 y4)) = y3) /\ ((y2 (NUMSUM y3 y4)) = y4)) x0 x1.
Definition term31 (x0 : type1260) := forall y0 : type1670, exists y1 : nat -> nat, forall y2 : Prop, forall y3 : nat, ((x0 y0 (NUMSUM y2 y3)) = y2) /\ ((y1 (NUMSUM y2 y3)) = y3).
Definition term5 := forall y0 : type1670, exists y1 : nat -> Prop, exists y2 : nat -> nat, forall y3 : Prop, forall y4 : nat, ((y1 (NUMSUM y3 y4)) = y3) /\ ((y2 (NUMSUM y3 y4)) = y4).
Definition term6 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := (fun y0 : type1413 a0 a1 => (forall y1 : a0, exists y2 : a1, y0 y1 y2) = (exists y1 : a0 -> a1, forall y2 : a0, y0 y2 (y1 y2))) x0.
Definition term17 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => exists y1 : nat -> nat, forall y2 : Prop, forall y3 : nat, ((y0 (NUMSUM y2 y3)) = y2) /\ ((y1 (NUMSUM y2 y3)) = y3)) x0.
Definition term29 (x0 : type1260) := fun y0 : type1670 => exists y1 : nat -> nat, forall y2 : Prop, forall y3 : nat, ((x0 y0 (NUMSUM y2 y3)) = y2) /\ ((y1 (NUMSUM y2 y3)) = y3).
Definition term8 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term11 := forall y0 : type1670, exists y1 : nat -> Prop, (fun y2 : type1670 => fun y3 : nat -> Prop => exists y4 : nat -> nat, forall y5 : Prop, forall y6 : nat, ((y3 (NUMSUM y5 y6)) = y5) /\ ((y4 (NUMSUM y5 y6)) = y6)) y0 y1.
Definition term9 (x0 : type1257) := forall y0 : type1670, exists y1 : nat -> Prop, x0 y0 y1.
Definition term25 (x0 : type1260) (x1 : type1670) := (fun y0 : type1670 => fun y1 : nat -> Prop => exists y2 : nat -> nat, forall y3 : Prop, forall y4 : nat, ((y1 (NUMSUM y3 y4)) = y3) /\ ((y2 (NUMSUM y3 y4)) = y4)) x1 (x0 x1).
Definition term3 := (forall y0 : Prop, forall y1 : nat, forall y2 : Prop, forall y3 : nat, ((NUMSUM y0 y1) = (NUMSUM y2 y3)) = ((y0 = y2) /\ (y1 = y3))) -> exists y0 : nat -> Prop, exists y1 : nat -> nat, forall y2 : Prop, forall y3 : nat, ((y0 (NUMSUM y2 y3)) = y2) /\ ((y1 (NUMSUM y2 y3)) = y3).
Definition term2 (x0 : type1545) := (forall y0 : Prop, forall y1 : nat, forall y2 : Prop, forall y3 : nat, ((x0 y0 y1) = (x0 y2 y3)) = ((y0 = y2) /\ (y1 = y3))) -> exists y0 : nat -> Prop, exists y1 : nat -> nat, forall y2 : Prop, forall y3 : nat, ((y0 (x0 y2 y3)) = y2) /\ ((y1 (x0 y2 y3)) = y3).
Definition term1 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1412 a0 a1 a2) := (forall y0 : a0, forall y1 : a1, forall y2 : a0, forall y3 : a1, ((x0 y0 y1) = (x0 y2 y3)) = ((y0 = y2) /\ (y1 = y3))) -> exists y0 : a2 -> a0, exists y1 : a2 -> a1, forall y2 : a0, forall y3 : a1, ((y0 (x0 y2 y3)) = y2) /\ ((y1 (x0 y2 y3)) = y3).
Definition term21 := fun y0 : type1670 => exists y1 : nat -> Prop, (fun y2 : type1670 => fun y3 : nat -> Prop => exists y4 : nat -> nat, forall y5 : Prop, forall y6 : nat, ((y3 (NUMSUM y5 y6)) = y5) /\ ((y4 (NUMSUM y5 y6)) = y6)) y0 y1.
