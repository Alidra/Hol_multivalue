Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term34 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add x0 (Nat.add x1 (S (Nat.add x2 x3))).
Definition term15 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := exists y0 : nat, (Nat.add x0 x1) = (Nat.add (Nat.add x2 x3) (S y0)).
Definition term10 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x0 x1) /\ (Peano.lt x2 x3).
Definition term39 (x0 : nat) (x1 : nat) := @eq nat (Nat.add x0 x1).
Definition term44 (x0 : nat) (x1 : nat) := fun y0 : nat => x0 = (Nat.add x1 y0).
Definition term20 := (forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))).
Definition term17 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((exists y0 : nat, x0 = (Nat.add x2 y0)) /\ (exists y0 : nat, x1 = (Nat.add x3 (S y0)))) -> exists y0 : nat, (Nat.add x0 x1) = (Nat.add (Nat.add x2 x3) (S y0)).
Definition term28 (x0 : nat) := forall y0 : nat, ((S x0) = (S y0)) = (x0 = y0).
Definition term37 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add x0 (S (Nat.add x1 (Nat.add x2 x3))).
Definition term41 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add x0 (Nat.add x1 (Nat.add x2 x3)).
Definition term5 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1)).
Definition term1 (x0 : nat) := forall y0 : nat, (Peano.lt x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 (S y1))).
Definition term40 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq nat (S (Nat.add x0 (Nat.add x1 (Nat.add x2 x3)))).
Definition term32 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add x0 x1) x2.
Definition term38 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := S (Nat.add x0 (Nat.add x1 (Nat.add x2 x3))).
Definition term7 (x0 : nat) (x1 : nat) := exists y0 : nat, x0 = (Nat.add x1 y0).
Definition term26 (x0 : nat) (x1 : nat) := S (Nat.add x0 x1).
Definition term48 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.lt y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3).
Definition term47 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le x0 y1) /\ (Peano.lt y0 y2)) -> Peano.lt (Nat.add x0 y0) (Nat.add y1 y2).
Definition term46 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.lt x1 y1)) -> Peano.lt (Nat.add x0 x1) (Nat.add y0 y1).
Definition term21 := forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)).
Definition term13 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp ((exists y0 : nat, x0 = (Nat.add x1 y0)) /\ (exists y0 : nat, x2 = (Nat.add x3 (S y0)))).
Definition term30 (x0 : nat) (x1 : nat) := Nat.add (Nat.add x0 x1).
Definition term18 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.add (Nat.add x1 x0) x2) = (Nat.add x1 (Nat.add x0 x2))) /\ ((Nat.add x1 (Nat.add x0 x2)) = (Nat.add x0 (Nat.add x1 x2))).
Definition term16 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Peano.le x0 x2) /\ (Peano.lt x1 x3)) -> Peano.lt (Nat.add x0 x1) (Nat.add x2 x3).
Definition term31 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (Nat.add x0 x1) (S (Nat.add x2 x3)).
Definition term3 (x0 : nat) (x1 : nat) := exists y0 : nat, x0 = (Nat.add x1 (S y0)).
Definition term24 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 (S y0)) = (S (Nat.add x0 y0))) x1.
Definition term19 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term33 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (Nat.add x1 x2).
Definition term14 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.lt (Nat.add x0 x1) (Nat.add x2 x3).
Definition term11 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (exists y0 : nat, x0 = (Nat.add x1 y0)) /\ (exists y0 : nat, x2 = (Nat.add x3 (S y0))).
Definition term27 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((S y0) = (S y1)) = (y0 = y1)) x0.
Definition term22 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))) x0.
Definition term4 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 (S y2)))) x0.
Definition term45 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, ((Peano.le x0 x2) /\ (Peano.lt x1 y0)) -> Peano.lt (Nat.add x0 x1) (Nat.add x2 y0).
Definition term35 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (S (Nat.add x1 x2)).
Definition term9 (x0 : nat) (x1 : nat) := and (exists y0 : nat, x0 = (Nat.add x1 y0)).
Definition term43 (x0 : nat) (x1 : nat) := fun y0 : nat => x0 = (Nat.add x1 (S y0)).
Definition term25 (x0 : nat) (x1 : nat) := Nat.add x0 (S x1).
Definition term36 (x0 : nat) (x1 : nat) (x2 : nat) := S (Nat.add x0 (Nat.add x1 x2)).
Definition term6 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1))) x1.
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 (S y1)))) x1.
Definition term12 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp ((Peano.le x0 x1) /\ (Peano.lt x2 x3)).
Definition term29 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((S x0) = (S y0)) = (x0 = y0)) x1.
Definition term42 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := fun y0 : nat => (Nat.add x0 x1) = (Nat.add (Nat.add x2 x3) (S y0)).
Definition term8 (x0 : nat) (x1 : nat) := and (Peano.le x0 x1).
Definition term23 (x0 : nat) := forall y0 : nat, (Nat.add x0 (S y0)) = (S (Nat.add x0 y0)).
