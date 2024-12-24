Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term35 (x0 : nat) := ((fun y0 : nat => Peano.le y0 (Nat.mul y0 y0)) x0) -> (fun y0 : nat => Peano.le y0 (Nat.mul y0 y0)) (S x0).
Definition term13 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul x0 (S y0)) = (Nat.add x0 (Nat.mul x0 y0))) x1.
Definition term51 (x0 : nat) := Nat.add (Nat.mul x0 (S x0)) (S x0).
Definition term32 (x0 : nat) := imp (Peano.le x0 (Nat.mul x0 x0)).
Definition term7 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term53 (x0 : nat) := Nat.add x0 (Nat.mul x0 x0).
Definition term26 := Peano.le (NUMERAL 0) (Nat.mul (NUMERAL 0) (NUMERAL 0)).
Definition term56 (x0 : nat) := Nat.add (Nat.add x0 (Nat.mul x0 x0)) (S x0).
Definition term12 (x0 : nat) := forall y0 : nat, (Nat.mul x0 (S y0)) = (Nat.add x0 (Nat.mul x0 y0)).
Definition term9 := (forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))).
Definition term19 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul (S x0) y0) = (Nat.add (Nat.mul x0 y0) y0)) x1.
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le y0 (Nat.add x0 y0)) x1.
Definition term55 (x0 : nat) := Nat.add (Nat.add x0 (Nat.mul x0 x0)).
Definition term46 := forall y0 : nat, (fun y1 : nat => Peano.le y1 (Nat.mul y1 y1)) y0.
Definition term41 := ((fun y0 : nat => Peano.le y0 (Nat.mul y0 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => Peano.le y1 (Nat.mul y1 y1)) y0) -> (fun y1 : nat => Peano.le y1 (Nat.mul y1 y1)) (S y0)).
Definition term29 (x0 : nat) := (fun y0 : nat => Peano.le y0 (Nat.mul y0 y0)) x0.
Definition term4 (x0 : nat) := (fun y0 : nat => Peano.le (NUMERAL 0) y0) x0.
Definition term23 := (((fun y0 : nat => Peano.le y0 (Nat.mul y0 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => Peano.le y1 (Nat.mul y1 y1)) y0) -> (fun y1 : nat => Peano.le y1 (Nat.mul y1 y1)) (S y0))) -> forall y0 : nat, (fun y1 : nat => Peano.le y1 (Nat.mul y1 y1)) y0.
Definition term22 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term28 := and (Peano.le (NUMERAL 0) (Nat.mul (NUMERAL 0) (NUMERAL 0))).
Definition term43 := imp (((fun y0 : nat => Peano.le y0 (Nat.mul y0 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => Peano.le y1 (Nat.mul y1 y1)) y0) -> (fun y1 : nat => Peano.le y1 (Nat.mul y1 y1)) (S y0))).
Definition term20 (x0 : nat) (x1 : nat) := Nat.mul (S x0) x1.
Definition term39 := forall y0 : nat, ((fun y1 : nat => Peano.le y1 (Nat.mul y1 y1)) y0) -> (fun y1 : nat => Peano.le y1 (Nat.mul y1 y1)) (S y0).
Definition term14 (x0 : nat) (x1 : nat) := Nat.mul x0 (S x1).
Definition term27 := and ((fun y0 : nat => Peano.le y0 (Nat.mul y0 y0)) (NUMERAL 0)).
Definition term30 (x0 : nat) := Peano.le x0 (Nat.mul x0 x0).
Definition term37 := fun y0 : nat => ((fun y1 : nat => Peano.le y1 (Nat.mul y1 y1)) y0) -> (fun y1 : nat => Peano.le y1 (Nat.mul y1 y1)) (S y0).
Definition term16 := forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1).
Definition term10 := forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)).
Definition term34 (x0 : nat) := Peano.le (S x0) (Nat.mul (S x0) (S x0)).
Definition term42 := (Peano.le (NUMERAL 0) (Nat.mul (NUMERAL 0) (NUMERAL 0))) /\ (forall y0 : nat, (Peano.le y0 (Nat.mul y0 y0)) -> Peano.le (S y0) (Nat.mul (S y0) (S y0))).
Definition term36 (x0 : nat) := (Peano.le x0 (Nat.mul x0 x0)) -> Peano.le (S x0) (Nat.mul (S x0) (S x0)).
Definition term5 (x0 : nat) := Peano.le (NUMERAL 0) x0.
Definition term18 (x0 : nat) := forall y0 : nat, (Nat.mul (S x0) y0) = (Nat.add (Nat.mul x0 y0) y0).
Definition term54 (x0 : nat) := Nat.add (Nat.mul x0 (S x0)).
Definition term8 := (forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))).
Definition term45 := fun y0 : nat => (fun y1 : nat => Peano.le y1 (Nat.mul y1 y1)) y0.
Definition term3 (x0 : nat) (x1 : nat) := Peano.le x1 (Nat.add x0 x1).
Definition term17 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) x0.
Definition term11 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le y1 (Nat.add y0 y1)) x0.
Definition term21 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 x1) x1.
Definition term15 (x0 : nat) (x1 : nat) := Nat.add x0 (Nat.mul x0 x1).
Definition term58 (x0 : nat) := Peano.le (S x0) (Nat.add (Nat.add x0 (Nat.mul x0 x0)) (S x0)).
Definition term44 := imp ((Peano.le (NUMERAL 0) (Nat.mul (NUMERAL 0) (NUMERAL 0))) /\ (forall y0 : nat, (Peano.le y0 (Nat.mul y0 y0)) -> Peano.le (S y0) (Nat.mul (S y0) (S y0)))).
Definition term52 (x0 : nat) := Nat.mul x0 (S x0).
Definition term49 := Nat.mul (NUMERAL 0) (NUMERAL 0).
Definition term57 (x0 : nat) := Peano.le (S x0).
Definition term40 := forall y0 : nat, (Peano.le y0 (Nat.mul y0 y0)) -> Peano.le (S y0) (Nat.mul (S y0) (S y0)).
Definition term50 (x0 : nat) := Nat.mul (S x0) (S x0).
Definition term48 := ((Peano.le (NUMERAL 0) (Nat.mul (NUMERAL 0) (NUMERAL 0))) /\ (forall y0 : nat, (Peano.le y0 (Nat.mul y0 y0)) -> Peano.le (S y0) (Nat.mul (S y0) (S y0)))) -> forall y0 : nat, Peano.le y0 (Nat.mul y0 y0).
Definition term31 (x0 : nat) := imp ((fun y0 : nat => Peano.le y0 (Nat.mul y0 y0)) x0).
Definition term24 := fun y0 : nat => Peano.le y0 (Nat.mul y0 y0).
Definition term25 := (fun y0 : nat => Peano.le y0 (Nat.mul y0 y0)) (NUMERAL 0).
Definition term6 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term38 := fun y0 : nat => (Peano.le y0 (Nat.mul y0 y0)) -> Peano.le (S y0) (Nat.mul (S y0) (S y0)).
Definition term47 := forall y0 : nat, Peano.le y0 (Nat.mul y0 y0).
Definition term1 (x0 : nat) := forall y0 : nat, Peano.le y0 (Nat.add x0 y0).
Definition term33 (x0 : nat) := (fun y0 : nat => Peano.le y0 (Nat.mul y0 y0)) (S x0).
