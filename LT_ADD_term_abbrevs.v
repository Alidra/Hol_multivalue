Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term58 (x0 : nat) := fun y0 : nat => (Peano.lt (S x0) (Nat.add (S x0) y0)) = (Peano.lt (NUMERAL 0) y0).
Definition term35 := fun y0 : nat => (Peano.lt (NUMERAL 0) (Nat.add (NUMERAL 0) y0)) = (Peano.lt (NUMERAL 0) y0).
Definition term38 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term18 := forall y0 : nat, (forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) = (Peano.lt (NUMERAL 0) y1)) -> forall y1 : nat, (Peano.lt (S y0) (Nat.add (S y0) y1)) = (Peano.lt (NUMERAL 0) y1).
Definition term45 := (forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))).
Definition term41 (x0 : nat) := forall y0 : nat, (Peano.lt (S x0) (S y0)) = (Peano.lt x0 y0).
Definition term26 := ((forall y0 : nat, (Peano.lt (NUMERAL 0) (Nat.add (NUMERAL 0) y0)) = (Peano.lt (NUMERAL 0) y0)) /\ (forall y0 : nat, (forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) = (Peano.lt (NUMERAL 0) y1)) -> forall y1 : nat, (Peano.lt (S y0) (Nat.add (S y0) y1)) = (Peano.lt (NUMERAL 0) y1))) -> forall y0 : nat, forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) = (Peano.lt (NUMERAL 0) y1).
Definition term9 (x0 : nat) := imp ((fun y0 : nat => forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) = (Peano.lt (NUMERAL 0) y1)) x0).
Definition term55 (x0 : nat) (x1 : nat) := Peano.lt (S x0) (Nat.add (S x0) x1).
Definition term1 := (((fun y0 : nat => forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) = (Peano.lt (NUMERAL 0) y1)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Peano.lt y1 (Nat.add y1 y2)) = (Peano.lt (NUMERAL 0) y2)) y0) -> (fun y1 : nat => forall y2 : nat, (Peano.lt y1 (Nat.add y1 y2)) = (Peano.lt (NUMERAL 0) y2)) (S y0))) -> forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.lt y1 (Nat.add y1 y2)) = (Peano.lt (NUMERAL 0) y2)) y0.
Definition term0 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term48 (x0 : nat) := forall y0 : nat, (Nat.add (S x0) y0) = (S (Nat.add x0 y0)).
Definition term21 := imp (((fun y0 : nat => forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) = (Peano.lt (NUMERAL 0) y1)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Peano.lt y1 (Nat.add y1 y2)) = (Peano.lt (NUMERAL 0) y2)) y0) -> (fun y1 : nat => forall y2 : nat, (Peano.lt y1 (Nat.add y1 y2)) = (Peano.lt (NUMERAL 0) y2)) (S y0))).
Definition term12 (x0 : nat) := forall y0 : nat, (Peano.lt (S x0) (Nat.add (S x0) y0)) = (Peano.lt (NUMERAL 0) y0).
Definition term8 (x0 : nat) := forall y0 : nat, (Peano.lt x0 (Nat.add x0 y0)) = (Peano.lt (NUMERAL 0) y0).
Definition term4 := forall y0 : nat, (Peano.lt (NUMERAL 0) (Nat.add (NUMERAL 0) y0)) = (Peano.lt (NUMERAL 0) y0).
Definition term17 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Peano.lt y1 (Nat.add y1 y2)) = (Peano.lt (NUMERAL 0) y2)) y0) -> (fun y1 : nat => forall y2 : nat, (Peano.lt y1 (Nat.add y1 y2)) = (Peano.lt (NUMERAL 0) y2)) (S y0).
Definition term2 := fun y0 : nat => forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) = (Peano.lt (NUMERAL 0) y1).
Definition term33 (x0 : nat) := @eq Prop (Peano.lt (NUMERAL 0) (Nat.add (NUMERAL 0) x0)).
Definition term49 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add (S x0) y0) = (S (Nat.add x0 y0))) x1.
Definition term5 := and ((fun y0 : nat => forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) = (Peano.lt (NUMERAL 0) y1)) (NUMERAL 0)).
Definition term10 (x0 : nat) := imp (forall y0 : nat, (Peano.lt x0 (Nat.add x0 y0)) = (Peano.lt (NUMERAL 0) y0)).
Definition term6 := and (forall y0 : nat, (Peano.lt (NUMERAL 0) (Nat.add (NUMERAL 0) y0)) = (Peano.lt (NUMERAL 0) y0)).
Definition term11 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) = (Peano.lt (NUMERAL 0) y1)) (S x0).
Definition term3 := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) = (Peano.lt (NUMERAL 0) y1)) (NUMERAL 0).
Definition term57 (x0 : nat) (x1 : nat) := @eq Prop (Peano.lt (S x0) (Nat.add (S x0) x1)).
Definition term29 (x0 : nat) := Nat.add (NUMERAL 0) x0.
Definition term22 := imp ((forall y0 : nat, (Peano.lt (NUMERAL 0) (Nat.add (NUMERAL 0) y0)) = (Peano.lt (NUMERAL 0) y0)) /\ (forall y0 : nat, (forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) = (Peano.lt (NUMERAL 0) y1)) -> forall y1 : nat, (Peano.lt (S y0) (Nat.add (S y0) y1)) = (Peano.lt (NUMERAL 0) y1))).
Definition term51 (x0 : nat) (x1 : nat) := S (Nat.add x0 x1).
Definition term46 := forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1)).
Definition term25 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) = (Peano.lt (NUMERAL 0) y1).
Definition term52 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 (Nat.add x0 y0)) = (Peano.lt (NUMERAL 0) y0)) x1.
Definition term30 := Peano.lt (NUMERAL 0).
Definition term37 := forall y0 : nat, True.
Definition term27 := forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0.
Definition term28 (x0 : nat) := (fun y0 : nat => (Nat.add (NUMERAL 0) y0) = y0) x0.
Definition term36 := fun y0 : nat => True.
Definition term56 (x0 : nat) (x1 : nat) := Peano.lt (S x0) (S (Nat.add x0 x1)).
Definition term42 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt (S x0) (S y0)) = (Peano.lt x0 y0)) x1.
Definition term16 := fun y0 : nat => (forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) = (Peano.lt (NUMERAL 0) y1)) -> forall y1 : nat, (Peano.lt (S y0) (Nat.add (S y0) y1)) = (Peano.lt (NUMERAL 0) y1).
Definition term15 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, (Peano.lt y1 (Nat.add y1 y2)) = (Peano.lt (NUMERAL 0) y2)) y0) -> (fun y1 : nat => forall y2 : nat, (Peano.lt y1 (Nat.add y1 y2)) = (Peano.lt (NUMERAL 0) y2)) (S y0).
Definition term44 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term31 (x0 : nat) := Peano.lt (NUMERAL 0) (Nat.add (NUMERAL 0) x0).
Definition term20 := (forall y0 : nat, (Peano.lt (NUMERAL 0) (Nat.add (NUMERAL 0) y0)) = (Peano.lt (NUMERAL 0) y0)) /\ (forall y0 : nat, (forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) = (Peano.lt (NUMERAL 0) y1)) -> forall y1 : nat, (Peano.lt (S y0) (Nat.add (S y0) y1)) = (Peano.lt (NUMERAL 0) y1)).
Definition term23 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (Peano.lt y1 (Nat.add y1 y2)) = (Peano.lt (NUMERAL 0) y2)) y0.
Definition term47 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) x0.
Definition term40 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt (S y0) (S y1)) = (Peano.lt y0 y1)) x0.
Definition term7 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) = (Peano.lt (NUMERAL 0) y1)) x0.
Definition term34 (x0 : nat) := @eq Prop (Peano.lt (NUMERAL 0) x0).
Definition term19 := ((fun y0 : nat => forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) = (Peano.lt (NUMERAL 0) y1)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Peano.lt y1 (Nat.add y1 y2)) = (Peano.lt (NUMERAL 0) y2)) y0) -> (fun y1 : nat => forall y2 : nat, (Peano.lt y1 (Nat.add y1 y2)) = (Peano.lt (NUMERAL 0) y2)) (S y0)).
Definition term43 (x0 : nat) (x1 : nat) := Peano.lt (S x0) (S x1).
Definition term54 (x0 : nat) := Peano.lt (S x0).
Definition term53 (x0 : nat) (x1 : nat) := Peano.lt x0 (Nat.add x0 x1).
Definition term39 (x0 : Prop) := forall y0 : nat, x0.
Definition term13 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) = (Peano.lt (NUMERAL 0) y1)) x0) -> (fun y0 : nat => forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) = (Peano.lt (NUMERAL 0) y1)) (S x0).
Definition term24 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.lt y1 (Nat.add y1 y2)) = (Peano.lt (NUMERAL 0) y2)) y0.
Definition term32 (x0 : nat) := Peano.lt (NUMERAL 0) x0.
Definition term50 (x0 : nat) (x1 : nat) := Nat.add (S x0) x1.
Definition term14 (x0 : nat) := (forall y0 : nat, (Peano.lt x0 (Nat.add x0 y0)) = (Peano.lt (NUMERAL 0) y0)) -> forall y0 : nat, (Peano.lt (S x0) (Nat.add (S x0) y0)) = (Peano.lt (NUMERAL 0) y0).
