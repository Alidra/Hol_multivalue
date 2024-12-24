Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term50 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul x0 (S y0)) = (Nat.add x0 (Nat.mul x0 y0))) x1.
Definition term63 (x0 : nat) (x1 : nat) := @eq nat (Nat.add (Nat.mul x1 x0) x1).
Definition term38 := @eq nat (NUMERAL 0).
Definition term44 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term34 := forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0).
Definition term42 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term21 := forall y0 : nat, (forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.mul y1 (S y0)).
Definition term49 (x0 : nat) := forall y0 : nat, (Nat.mul x0 (S y0)) = (Nat.add x0 (Nat.mul x0 y0)).
Definition term60 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 x1).
Definition term46 := (forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))).
Definition term56 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul (S x0) y0) = (Nat.add (Nat.mul x0 y0) y0)) x1.
Definition term35 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) x0.
Definition term29 := ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (Nat.mul y0 (NUMERAL 0))) /\ (forall y0 : nat, (forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.mul y1 (S y0)))) -> forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0).
Definition term61 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x1 x0) x1.
Definition term12 (x0 : nat) := imp ((fun y0 : nat => forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) x0).
Definition term4 := (((fun y0 : nat => forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Nat.mul y1 y2) = (Nat.mul y2 y1)) y0) -> (fun y1 : nat => forall y2 : nat, (Nat.mul y1 y2) = (Nat.mul y2 y1)) (S y0))) -> forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Nat.mul y1 y2) = (Nat.mul y2 y1)) y0.
Definition term15 (x0 : nat) := forall y0 : nat, (Nat.mul (S x0) y0) = (Nat.mul y0 (S x0)).
Definition term3 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term24 := imp (((fun y0 : nat => forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Nat.mul y1 y2) = (Nat.mul y2 y1)) y0) -> (fun y1 : nat => forall y2 : nat, (Nat.mul y1 y2) = (Nat.mul y2 y1)) (S y0))).
Definition term57 (x0 : nat) (x1 : nat) := Nat.mul (S x0) x1.
Definition term20 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Nat.mul y1 y2) = (Nat.mul y2 y1)) y0) -> (fun y1 : nat => forall y2 : nat, (Nat.mul y1 y2) = (Nat.mul y2 y1)) (S y0).
Definition term5 := fun y0 : nat => forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0).
Definition term51 (x0 : nat) (x1 : nat) := Nat.mul x0 (S x1).
Definition term32 (x0 : nat) := (fun y0 : nat => (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) x0.
Definition term8 := and ((fun y0 : nat => forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) (NUMERAL 0)).
Definition term13 (x0 : nat) := imp (forall y0 : nat, (Nat.mul x0 y0) = (Nat.mul y0 x0)).
Definition term9 := and (forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (Nat.mul y0 (NUMERAL 0))).
Definition term14 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) (S x0).
Definition term6 := (fun y0 : nat => forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) (NUMERAL 0).
Definition term25 := imp ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (Nat.mul y0 (NUMERAL 0))) /\ (forall y0 : nat, (forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.mul y1 (S y0)))).
Definition term37 (x0 : nat) := @eq nat (Nat.mul (NUMERAL 0) x0).
Definition term53 := forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1).
Definition term47 := forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)).
Definition term28 := forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0).
Definition term62 (x0 : nat) (x1 : nat) := @eq nat (Nat.mul (S x0) x1).
Definition term41 := forall y0 : nat, True.
Definition term55 (x0 : nat) := forall y0 : nat, (Nat.mul (S x0) y0) = (Nat.add (Nat.mul x0 y0) y0).
Definition term40 := fun y0 : nat => True.
Definition term11 (x0 : nat) := forall y0 : nat, (Nat.mul x0 y0) = (Nat.mul y0 x0).
Definition term1 (x0 : nat) := forall y0 : nat, (Nat.add x0 y0) = (Nat.add y0 x0).
Definition term19 := fun y0 : nat => (forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.mul y1 (S y0)).
Definition term18 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, (Nat.mul y1 y2) = (Nat.mul y2 y1)) y0) -> (fun y1 : nat => forall y2 : nat, (Nat.mul y1 y2) = (Nat.mul y2 y1)) (S y0).
Definition term59 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul x0 y0) = (Nat.mul y0 x0)) x1.
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 y0) = (Nat.add y0 x0)) x1.
Definition term45 := (forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))).
Definition term23 := (forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (Nat.mul y0 (NUMERAL 0))) /\ (forall y0 : nat, (forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.mul y1 (S y0))).
Definition term26 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (Nat.mul y1 y2) = (Nat.mul y2 y1)) y0.
Definition term54 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) x0.
Definition term48 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))) x0.
Definition term10 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) x0.
Definition term31 := forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0).
Definition term58 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 x1) x1.
Definition term22 := ((fun y0 : nat => forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Nat.mul y1 y2) = (Nat.mul y2 y1)) y0) -> (fun y1 : nat => forall y2 : nat, (Nat.mul y1 y2) = (Nat.mul y2 y1)) (S y0)).
Definition term64 (x0 : nat) := fun y0 : nat => (Nat.mul (S x0) y0) = (Nat.mul y0 (S x0)).
Definition term52 (x0 : nat) (x1 : nat) := Nat.add x0 (Nat.mul x0 x1).
Definition term33 (x0 : nat) := Nat.mul x0 (NUMERAL 0).
Definition term39 := fun y0 : nat => (Nat.mul (NUMERAL 0) y0) = (Nat.mul y0 (NUMERAL 0)).
Definition term43 (x0 : Prop) := forall y0 : nat, x0.
Definition term36 (x0 : nat) := Nat.mul (NUMERAL 0) x0.
Definition term7 := forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (Nat.mul y0 (NUMERAL 0)).
Definition term16 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) x0) -> (fun y0 : nat => forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) (S x0).
Definition term27 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Nat.mul y1 y2) = (Nat.mul y2 y1)) y0.
Definition term30 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term17 (x0 : nat) := (forall y0 : nat, (Nat.mul x0 y0) = (Nat.mul y0 x0)) -> forall y0 : nat, (Nat.mul (S x0) y0) = (Nat.mul y0 (S x0)).
