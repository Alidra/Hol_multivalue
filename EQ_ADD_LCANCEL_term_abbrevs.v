Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term7 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) = (y1 = y2)) x0.
Definition term57 (x0 : nat) (x1 : nat) := fun y0 : nat => ((Nat.add (S x0) x1) = (Nat.add (S x0) y0)) = (x1 = y0).
Definition term14 (x0 : nat) := (forall y0 : nat, forall y1 : nat, ((Nat.add x0 y0) = (Nat.add x0 y1)) = (y0 = y1)) -> forall y0 : nat, forall y1 : nat, ((Nat.add (S x0) y0) = (Nat.add (S x0) y1)) = (y0 = y1).
Definition term37 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term18 := forall y0 : nat, (forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) = (y1 = y2)) -> forall y1 : nat, forall y2 : nat, ((Nat.add (S y0) y1) = (Nat.add (S y0) y2)) = (y1 = y2).
Definition term54 (x0 : nat) (x1 : nat) := @eq nat (Nat.add (S x0) x1).
Definition term44 := (forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))).
Definition term33 (x0 : nat) := fun y0 : nat => ((Nat.add (NUMERAL 0) x0) = (Nat.add (NUMERAL 0) y0)) = (x0 = y0).
Definition term58 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Nat.add (S x0) x1) = (Nat.add (S x0) y0)) = (x1 = y0).
Definition term52 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Nat.add x0 x1) = (Nat.add x0 y0)) = (x1 = y0).
Definition term41 (x0 : nat) := forall y0 : nat, ((S x0) = (S y0)) = (x0 = y0).
Definition term35 (x0 : nat) := forall y0 : nat, ((Nat.add (NUMERAL 0) x0) = (Nat.add (NUMERAL 0) y0)) = (x0 = y0).
Definition term26 := ((forall y0 : nat, forall y1 : nat, ((Nat.add (NUMERAL 0) y0) = (Nat.add (NUMERAL 0) y1)) = (y0 = y1)) /\ (forall y0 : nat, (forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) = (y1 = y2)) -> forall y1 : nat, forall y2 : nat, ((Nat.add (S y0) y1) = (Nat.add (S y0) y2)) = (y1 = y2))) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) = (y1 = y2).
Definition term9 (x0 : nat) := imp ((fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) = (y1 = y2)) x0).
Definition term1 := (((fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) = (y1 = y2)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Nat.add y1 y2) = (Nat.add y1 y3)) = (y2 = y3)) y0) -> (fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Nat.add y1 y2) = (Nat.add y1 y3)) = (y2 = y3)) (S y0))) -> forall y0 : nat, (fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Nat.add y1 y2) = (Nat.add y1 y3)) = (y2 = y3)) y0.
Definition term0 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term47 (x0 : nat) := forall y0 : nat, (Nat.add (S x0) y0) = (S (Nat.add x0 y0)).
Definition term21 := imp (((fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) = (y1 = y2)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Nat.add y1 y2) = (Nat.add y1 y3)) = (y2 = y3)) y0) -> (fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Nat.add y1 y2) = (Nat.add y1 y3)) = (y2 = y3)) (S y0))).
Definition term51 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.add x0 y0) = (Nat.add x0 y1)) = (y0 = y1)) x1.
Definition term17 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Nat.add y1 y2) = (Nat.add y1 y3)) = (y2 = y3)) y0) -> (fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Nat.add y1 y2) = (Nat.add y1 y3)) = (y2 = y3)) (S y0).
Definition term59 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((Nat.add (S x0) y0) = (Nat.add (S x0) y1)) = (y0 = y1).
Definition term39 := fun y0 : nat => forall y1 : nat, ((Nat.add (NUMERAL 0) y0) = (Nat.add (NUMERAL 0) y1)) = (y0 = y1).
Definition term30 (x0 : nat) := @eq nat (Nat.add (NUMERAL 0) x0).
Definition term48 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add (S x0) y0) = (S (Nat.add x0 y0))) x1.
Definition term5 := and ((fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) = (y1 = y2)) (NUMERAL 0)).
Definition term11 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) = (y1 = y2)) (S x0).
Definition term3 := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) = (y1 = y2)) (NUMERAL 0).
Definition term29 (x0 : nat) := Nat.add (NUMERAL 0) x0.
Definition term22 := imp ((forall y0 : nat, forall y1 : nat, ((Nat.add (NUMERAL 0) y0) = (Nat.add (NUMERAL 0) y1)) = (y0 = y1)) /\ (forall y0 : nat, (forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) = (y1 = y2)) -> forall y1 : nat, forall y2 : nat, ((Nat.add (S y0) y1) = (Nat.add (S y0) y2)) = (y1 = y2))).
Definition term50 (x0 : nat) (x1 : nat) := S (Nat.add x0 x1).
Definition term45 := forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1)).
Definition term25 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) = (y1 = y2).
Definition term12 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Nat.add (S x0) y0) = (Nat.add (S x0) y1)) = (y0 = y1).
Definition term8 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Nat.add x0 y0) = (Nat.add x0 y1)) = (y0 = y1).
Definition term4 := forall y0 : nat, forall y1 : nat, ((Nat.add (NUMERAL 0) y0) = (Nat.add (NUMERAL 0) y1)) = (y0 = y1).
Definition term36 := forall y0 : nat, True.
Definition term56 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((Nat.add (S x1) x0) = (Nat.add (S x1) x2)).
Definition term27 := forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0.
Definition term28 (x0 : nat) := (fun y0 : nat => (Nat.add (NUMERAL 0) y0) = y0) x0.
Definition term34 := fun y0 : nat => True.
Definition term15 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Nat.add y1 y2) = (Nat.add y1 y3)) = (y2 = y3)) y0) -> (fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Nat.add y1 y2) = (Nat.add y1 y3)) = (y2 = y3)) (S y0).
Definition term43 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term6 := and (forall y0 : nat, forall y1 : nat, ((Nat.add (NUMERAL 0) y0) = (Nat.add (NUMERAL 0) y1)) = (y0 = y1)).
Definition term23 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Nat.add y1 y2) = (Nat.add y1 y3)) = (y2 = y3)) y0.
Definition term46 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) x0.
Definition term40 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((S y0) = (S y1)) = (y0 = y1)) x0.
Definition term55 (x0 : nat) (x1 : nat) := @eq nat (S (Nat.add x0 x1)).
Definition term16 := fun y0 : nat => (forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) = (y1 = y2)) -> forall y1 : nat, forall y2 : nat, ((Nat.add (S y0) y1) = (Nat.add (S y0) y2)) = (y1 = y2).
Definition term19 := ((fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) = (y1 = y2)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Nat.add y1 y2) = (Nat.add y1 y3)) = (y2 = y3)) y0) -> (fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Nat.add y1 y2) = (Nat.add y1 y3)) = (y2 = y3)) (S y0)).
Definition term53 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Nat.add x0 x1) = (Nat.add x0 y0)) = (x1 = y0)) x2.
Definition term32 (x0 : nat) (x1 : nat) := @eq Prop (x0 = x1).
Definition term38 (x0 : Prop) := forall y0 : nat, x0.
Definition term31 (x0 : nat) (x1 : nat) := @eq Prop ((Nat.add (NUMERAL 0) x0) = (Nat.add (NUMERAL 0) x1)).
Definition term13 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) = (y1 = y2)) x0) -> (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) = (y1 = y2)) (S x0).
Definition term42 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((S x0) = (S y0)) = (x0 = y0)) x1.
Definition term24 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Nat.add y1 y2) = (Nat.add y1 y3)) = (y2 = y3)) y0.
Definition term10 (x0 : nat) := imp (forall y0 : nat, forall y1 : nat, ((Nat.add x0 y0) = (Nat.add x0 y1)) = (y0 = y1)).
Definition term20 := (forall y0 : nat, forall y1 : nat, ((Nat.add (NUMERAL 0) y0) = (Nat.add (NUMERAL 0) y1)) = (y0 = y1)) /\ (forall y0 : nat, (forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) = (y1 = y2)) -> forall y1 : nat, forall y2 : nat, ((Nat.add (S y0) y1) = (Nat.add (S y0) y2)) = (y1 = y2)).
Definition term49 (x0 : nat) (x1 : nat) := Nat.add (S x0) x1.
Definition term2 := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) = (y1 = y2).
