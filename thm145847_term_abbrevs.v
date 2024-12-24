Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term51 (x0 : type1292) := forall y0 : type1673, ((x0 y0 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y1 : nat, (x0 y0 (S y1)) = (Nat.mul (S y1) (x0 y0 y1))).
Definition term53 := fun y0 : type1292 => forall y1 : type1673, ((y0 y1 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y2 : nat, (y0 y1 (S y2)) = (Nat.mul (S y2) (y0 y1 y2))).
Definition term44 := @eq Prop (forall y0 : type1673, exists y1 : nat -> nat, ((y1 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y2 : nat, (y1 (S y2)) = (Nat.mul (S y2) (y1 y2)))).
Definition term43 := @eq Prop (forall y0 : type1673, exists y1 : nat -> nat, (fun y2 : type1673 => fun y3 : nat -> nat => ((y3 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y4 : nat, (y3 (S y4)) = (Nat.mul (S y4) (y3 y4)))) y0 y1).
Definition term52 := fun y0 : type1292 => forall y1 : type1673, (fun y2 : type1673 => fun y3 : nat -> nat => ((y3 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y4 : nat, (y3 (S y4)) = (Nat.mul (S y4) (y3 y4)))) y1 (y0 y1).
Definition term39 (x0 : type1673) := fun y0 : nat -> nat => (fun y1 : type1673 => fun y2 : nat -> nat => ((y2 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y3 : nat, (y2 (S y3)) = (Nat.mul (S y3) (y2 y3)))) x0 y0.
Definition term25 := fun y0 : nat -> nat => ((y0 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y1 : nat, (y0 (S y1)) = (Nat.mul (S y1) (y0 y1))).
Definition term24 := fun y0 : nat -> nat => ((y0 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y1 : nat, (y0 (S y1)) = ((fun y2 : nat => fun y3 : nat => Nat.mul (S y3) y2) (y0 y1) y1)).
Definition term37 (x0 : type1673) (x1 : nat -> nat) := (fun y0 : type1673 => fun y1 : nat -> nat => ((y1 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y2 : nat, (y1 (S y2)) = (Nat.mul (S y2) (y1 y2)))) x0 x1.
Definition term9 (a0 : Type') (x0 : a0) (x1 : type1423 a0) := (fun y0 : type1423 a0 => exists y1 : nat -> a0, ((y1 (NUMERAL 0)) = x0) /\ (forall y2 : nat, (y1 (S y2)) = (y0 (y1 y2) y2))) x1.
Definition term38 (x0 : nat -> nat) := (fun y0 : nat -> nat => ((y0 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y1 : nat, (y0 (S y1)) = (Nat.mul (S y1) (y0 y1)))) x0.
Definition term58 := (fun y0 : type1292 => forall y1 : type1673, ((y0 y1 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y2 : nat, (y0 y1 (S y2)) = (Nat.mul (S y2) (y0 y1 y2)))) (@ε ((prod nat (prod nat (prod nat nat))) -> nat -> nat) (fun y0 : type1292 => forall y1 : type1673, ((y0 y1 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y2 : nat, (y0 y1 (S y2)) = (Nat.mul (S y2) (y0 y1 y2))))).
Definition term16 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => fun y1 : nat => Nat.mul (S y1) y0) (x0 x1) x1.
Definition term21 (x0 : nat -> nat) := forall y0 : nat, (x0 (S y0)) = ((fun y1 : nat => fun y2 : nat => Nat.mul (S y2) y1) (x0 y0) y0).
Definition term29 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term54 := exists y0 : type1292, forall y1 : type1673, ((y0 y1 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y2 : nat, (y0 y1 (S y2)) = (Nat.mul (S y2) (y0 y1 y2))).
Definition term34 := exists y0 : type1292, forall y1 : type1673, (fun y2 : type1673 => fun y3 : nat -> nat => ((y3 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y4 : nat, (y3 (S y4)) = (Nat.mul (S y4) (y3 y4)))) y1 (y0 y1).
Definition term32 (x0 : type1288) := exists y0 : type1292, forall y1 : type1673, x0 y1 (y0 y1).
Definition term50 (x0 : type1292) := forall y0 : type1673, (fun y1 : type1673 => fun y2 : nat -> nat => ((y2 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y3 : nat, (y2 (S y3)) = (Nat.mul (S y3) (y2 y3)))) y0 (x0 y0).
Definition term46 (x0 : type1292) (x1 : type1673) := (fun y0 : nat -> nat => ((y0 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y1 : nat, (y0 (S y1)) = (Nat.mul (S y1) (y0 y1)))) (x0 x1).
Definition term56 := fun y0 : type363 => y0 (@ε ((prod nat (prod nat (prod nat nat))) -> nat -> nat) y0).
Definition term26 := exists y0 : nat -> nat, ((y0 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y1 : nat, (y0 (S y1)) = (Nat.mul (S y1) (y0 y1))).
Definition term12 := exists y0 : nat -> nat, ((y0 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y1 : nat, (y0 (S y1)) = ((fun y2 : nat => fun y3 : nat => Nat.mul (S y3) y2) (y0 y1) y1)).
Definition term19 (x0 : nat -> nat) := fun y0 : nat => (x0 (S y0)) = ((fun y1 : nat => fun y2 : nat => Nat.mul (S y2) y1) (x0 y0) y0).
Definition term7 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : type1423 a0, exists y2 : nat -> a0, ((y2 (NUMERAL 0)) = y0) /\ (forall y3 : nat, (y2 (S y3)) = (y1 (y2 y3) y3))) x0.
Definition term42 := fun y0 : type1673 => exists y1 : nat -> nat, ((y1 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y2 : nat, (y1 (S y2)) = (Nat.mul (S y2) (y1 y2))).
Definition term55 (a0 : Type') := fun y0 : a0 -> Prop => y0 (@ε a0 y0).
Definition term45 (x0 : type1292) (x1 : type1673) := (fun y0 : type1673 => fun y1 : nat -> nat => ((y1 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y2 : nat, (y1 (S y2)) = (Nat.mul (S y2) (y1 y2)))) x1 (x0 x1).
Definition term23 (x0 : nat -> nat) := ((x0 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y0 : nat, (x0 (S y0)) = ((fun y1 : nat => fun y2 : nat => Nat.mul (S y2) y1) (x0 y0) y0)).
Definition term57 := (fun y0 : type363 => y0 (@ε ((prod nat (prod nat (prod nat nat))) -> nat -> nat) y0)) (fun y0 : type1292 => forall y1 : type1673, ((y0 y1 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y2 : nat, (y0 y1 (S y2)) = (Nat.mul (S y2) (y0 y1 y2)))).
Definition term15 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => Nat.mul (S y0) (x0 x1).
Definition term40 (x0 : type1673) := exists y0 : nat -> nat, (fun y1 : type1673 => fun y2 : nat -> nat => ((y2 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y3 : nat, (y2 (S y3)) = (Nat.mul (S y3) (y2 y3)))) x0 y0.
Definition term14 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => fun y1 : nat => Nat.mul (S y1) y0) (x0 x1).
Definition term18 (x0 : nat -> nat) (x1 : nat) := @eq nat (x0 (S x1)).
Definition term13 := fun y0 : nat => fun y1 : nat => Nat.mul (S y1) y0.
Definition term48 (x0 : type1292) := fun y0 : type1673 => (fun y1 : type1673 => fun y2 : nat -> nat => ((y2 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y3 : nat, (y2 (S y3)) = (Nat.mul (S y3) (y2 y3)))) y0 (x0 y0).
Definition term6 (x0 : nat -> nat) := ((x0 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y0 : nat, (x0 (S y0)) = (Nat.mul (S y0) (x0 y0))).
Definition term22 (x0 : nat -> nat) := and ((x0 (NUMERAL 0)) = (NUMERAL (BIT1 0))).
Definition term0 (x0 : nat -> nat) := x0 (NUMERAL 0).
Definition term17 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => Nat.mul (S y0) (x0 x1)) x1.
Definition term47 (x0 : type1292) (x1 : type1673) := ((x0 x1 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y0 : nat, (x0 x1 (S y0)) = (Nat.mul (S y0) (x0 x1 y0))).
Definition term49 (x0 : type1292) := fun y0 : type1673 => ((x0 y0 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y1 : nat, (x0 y0 (S y1)) = (Nat.mul (S y1) (x0 y0 y1))).
Definition term20 (x0 : nat -> nat) := fun y0 : nat => (x0 (S y0)) = (Nat.mul (S y0) (x0 y0)).
Definition term4 (x0 : nat -> nat) (x1 : nat) := x0 (S x1).
Definition term8 (a0 : Type') (x0 : a0) := forall y0 : type1423 a0, exists y1 : nat -> a0, ((y1 (NUMERAL 0)) = x0) /\ (forall y2 : nat, (y1 (S y2)) = (y0 (y1 y2) y2)).
Definition term28 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := (fun y0 : type1413 a0 a1 => (forall y1 : a0, exists y2 : a1, y0 y1 y2) = (exists y1 : a0 -> a1, forall y2 : a0, y0 y2 (y1 y2))) x0.
Definition term36 (x0 : type1673) := (fun y0 : type1673 => fun y1 : nat -> nat => ((y1 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y2 : nat, (y1 (S y2)) = (Nat.mul (S y2) (y1 y2)))) x0.
Definition term2 (x0 : nat -> nat) := forall y0 : nat, (x0 (S y0)) = (Nat.mul (S y0) (x0 y0)).
Definition term30 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term11 (x0 : nat) (x1 : type1606) := exists y0 : nat -> nat, ((y0 (NUMERAL 0)) = x0) /\ (forall y1 : nat, (y0 (S y1)) = (x1 (y0 y1) y1)).
Definition term10 (a0 : Type') (x0 : a0) (x1 : type1423 a0) := exists y0 : nat -> a0, ((y0 (NUMERAL 0)) = x0) /\ (forall y1 : nat, (y0 (S y1)) = (x1 (y0 y1) y1)).
Definition term33 := forall y0 : type1673, exists y1 : nat -> nat, (fun y2 : type1673 => fun y3 : nat -> nat => ((y3 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y4 : nat, (y3 (S y4)) = (Nat.mul (S y4) (y3 y4)))) y0 y1.
Definition term31 (x0 : type1288) := forall y0 : type1673, exists y1 : nat -> nat, x0 y0 y1.
Definition term3 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => (x0 (S y0)) = (Nat.mul (S y0) (x0 y0))) x1.
Definition term1 := NUMERAL (BIT1 0).
Definition term27 := forall y0 : type1673, exists y1 : nat -> nat, ((y1 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y2 : nat, (y1 (S y2)) = (Nat.mul (S y2) (y1 y2))).
Definition term35 := fun y0 : type1673 => fun y1 : nat -> nat => ((y1 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y2 : nat, (y1 (S y2)) = (Nat.mul (S y2) (y1 y2))).
Definition term5 (x0 : nat -> nat) (x1 : nat) := Nat.mul (S x1) (x0 x1).
Definition term41 := fun y0 : type1673 => exists y1 : nat -> nat, (fun y2 : type1673 => fun y3 : nat -> nat => ((y3 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y4 : nat, (y3 (S y4)) = (Nat.mul (S y4) (y3 y4)))) y0 y1.
