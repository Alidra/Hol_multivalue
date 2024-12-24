Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term55 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.sub (Nat.add x0 x1) (Nat.add x0 y0)) = (Nat.sub x1 y0)) x2.
Definition term7 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.sub (Nat.add y0 y1) (Nat.add y0 y2)) = (Nat.sub y1 y2)) x0.
Definition term14 (x0 : nat) := (forall y0 : nat, forall y1 : nat, (Nat.sub (Nat.add x0 y0) (Nat.add x0 y1)) = (Nat.sub y0 y1)) -> forall y0 : nat, forall y1 : nat, (Nat.sub (Nat.add (S x0) y0) (Nat.add (S x0) y1)) = (Nat.sub y0 y1).
Definition term38 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term34 (x0 : nat) := fun y0 : nat => (Nat.sub (Nat.add (NUMERAL 0) x0) (Nat.add (NUMERAL 0) y0)) = (Nat.sub x0 y0).
Definition term18 := forall y0 : nat, (forall y1 : nat, forall y2 : nat, (Nat.sub (Nat.add y0 y1) (Nat.add y0 y2)) = (Nat.sub y1 y2)) -> forall y1 : nat, forall y2 : nat, (Nat.sub (Nat.add (S y0) y1) (Nat.add (S y0) y2)) = (Nat.sub y1 y2).
Definition term46 := (forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))).
Definition term63 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.sub (Nat.add (S x0) x1) (Nat.add (S x0) y0)) = (Nat.sub x1 y0).
Definition term54 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.sub (Nat.add x0 x1) (Nat.add x0 y0)) = (Nat.sub x1 y0).
Definition term42 (x0 : nat) := forall y0 : nat, (Nat.sub (S x0) (S y0)) = (Nat.sub x0 y0).
Definition term36 (x0 : nat) := forall y0 : nat, (Nat.sub (Nat.add (NUMERAL 0) x0) (Nat.add (NUMERAL 0) y0)) = (Nat.sub x0 y0).
Definition term26 := ((forall y0 : nat, forall y1 : nat, (Nat.sub (Nat.add (NUMERAL 0) y0) (Nat.add (NUMERAL 0) y1)) = (Nat.sub y0 y1)) /\ (forall y0 : nat, (forall y1 : nat, forall y2 : nat, (Nat.sub (Nat.add y0 y1) (Nat.add y0 y2)) = (Nat.sub y1 y2)) -> forall y1 : nat, forall y2 : nat, (Nat.sub (Nat.add (S y0) y1) (Nat.add (S y0) y2)) = (Nat.sub y1 y2))) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.sub (Nat.add y0 y1) (Nat.add y0 y2)) = (Nat.sub y1 y2).
Definition term43 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.sub (S x0) (S y0)) = (Nat.sub x0 y0)) x1.
Definition term9 (x0 : nat) := imp ((fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.sub (Nat.add y0 y1) (Nat.add y0 y2)) = (Nat.sub y1 y2)) x0).
Definition term1 := (((fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.sub (Nat.add y0 y1) (Nat.add y0 y2)) = (Nat.sub y1 y2)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, forall y3 : nat, (Nat.sub (Nat.add y1 y2) (Nat.add y1 y3)) = (Nat.sub y2 y3)) y0) -> (fun y1 : nat => forall y2 : nat, forall y3 : nat, (Nat.sub (Nat.add y1 y2) (Nat.add y1 y3)) = (Nat.sub y2 y3)) (S y0))) -> forall y0 : nat, (fun y1 : nat => forall y2 : nat, forall y3 : nat, (Nat.sub (Nat.add y1 y2) (Nat.add y1 y3)) = (Nat.sub y2 y3)) y0.
Definition term61 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.sub (Nat.add (S x1) x0) (Nat.add (S x1) x2)).
Definition term0 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term49 (x0 : nat) := forall y0 : nat, (Nat.add (S x0) y0) = (S (Nat.add x0 y0)).
Definition term60 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.sub (S (Nat.add x1 x0)) (S (Nat.add x1 x2)).
Definition term21 := imp (((fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.sub (Nat.add y0 y1) (Nat.add y0 y2)) = (Nat.sub y1 y2)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, forall y3 : nat, (Nat.sub (Nat.add y1 y2) (Nat.add y1 y3)) = (Nat.sub y2 y3)) y0) -> (fun y1 : nat => forall y2 : nat, forall y3 : nat, (Nat.sub (Nat.add y1 y2) (Nat.add y1 y3)) = (Nat.sub y2 y3)) (S y0))).
Definition term32 (x0 : nat) (x1 : nat) := @eq nat (Nat.sub (Nat.add (NUMERAL 0) x0) (Nat.add (NUMERAL 0) x1)).
Definition term53 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.sub (Nat.add x0 y0) (Nat.add x0 y1)) = (Nat.sub y0 y1)) x1.
Definition term17 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, forall y3 : nat, (Nat.sub (Nat.add y1 y2) (Nat.add y1 y3)) = (Nat.sub y2 y3)) y0) -> (fun y1 : nat => forall y2 : nat, forall y3 : nat, (Nat.sub (Nat.add y1 y2) (Nat.add y1 y3)) = (Nat.sub y2 y3)) (S y0).
Definition term64 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.sub (Nat.add (S x0) y0) (Nat.add (S x0) y1)) = (Nat.sub y0 y1).
Definition term40 := fun y0 : nat => forall y1 : nat, (Nat.sub (Nat.add (NUMERAL 0) y0) (Nat.add (NUMERAL 0) y1)) = (Nat.sub y0 y1).
Definition term57 (x0 : nat) (x1 : nat) := Nat.sub (Nat.add (S x0) x1).
Definition term50 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add (S x0) y0) = (S (Nat.add x0 y0))) x1.
Definition term5 := and ((fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.sub (Nat.add y0 y1) (Nat.add y0 y2)) = (Nat.sub y1 y2)) (NUMERAL 0)).
Definition term11 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.sub (Nat.add y0 y1) (Nat.add y0 y2)) = (Nat.sub y1 y2)) (S x0).
Definition term3 := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.sub (Nat.add y0 y1) (Nat.add y0 y2)) = (Nat.sub y1 y2)) (NUMERAL 0).
Definition term29 (x0 : nat) := Nat.add (NUMERAL 0) x0.
Definition term22 := imp ((forall y0 : nat, forall y1 : nat, (Nat.sub (Nat.add (NUMERAL 0) y0) (Nat.add (NUMERAL 0) y1)) = (Nat.sub y0 y1)) /\ (forall y0 : nat, (forall y1 : nat, forall y2 : nat, (Nat.sub (Nat.add y0 y1) (Nat.add y0 y2)) = (Nat.sub y1 y2)) -> forall y1 : nat, forall y2 : nat, (Nat.sub (Nat.add (S y0) y1) (Nat.add (S y0) y2)) = (Nat.sub y1 y2))).
Definition term52 (x0 : nat) (x1 : nat) := S (Nat.add x0 x1).
Definition term47 := forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1)).
Definition term25 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.sub (Nat.add y0 y1) (Nat.add y0 y2)) = (Nat.sub y1 y2).
Definition term12 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.sub (Nat.add (S x0) y0) (Nat.add (S x0) y1)) = (Nat.sub y0 y1).
Definition term8 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.sub (Nat.add x0 y0) (Nat.add x0 y1)) = (Nat.sub y0 y1).
Definition term4 := forall y0 : nat, forall y1 : nat, (Nat.sub (Nat.add (NUMERAL 0) y0) (Nat.add (NUMERAL 0) y1)) = (Nat.sub y0 y1).
Definition term37 := forall y0 : nat, True.
Definition term27 := forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0.
Definition term28 (x0 : nat) := (fun y0 : nat => (Nat.add (NUMERAL 0) y0) = y0) x0.
Definition term35 := fun y0 : nat => True.
Definition term15 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, forall y3 : nat, (Nat.sub (Nat.add y1 y2) (Nat.add y1 y3)) = (Nat.sub y2 y3)) y0) -> (fun y1 : nat => forall y2 : nat, forall y3 : nat, (Nat.sub (Nat.add y1 y2) (Nat.add y1 y3)) = (Nat.sub y2 y3)) (S y0).
Definition term45 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term59 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.sub (Nat.add (S x1) x0) (Nat.add (S x1) x2).
Definition term62 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.sub (Nat.add (S x0) x1) (Nat.add (S x0) y0)) = (Nat.sub x1 y0).
Definition term6 := and (forall y0 : nat, forall y1 : nat, (Nat.sub (Nat.add (NUMERAL 0) y0) (Nat.add (NUMERAL 0) y1)) = (Nat.sub y0 y1)).
Definition term44 (x0 : nat) (x1 : nat) := Nat.sub (S x0) (S x1).
Definition term23 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, forall y3 : nat, (Nat.sub (Nat.add y1 y2) (Nat.add y1 y3)) = (Nat.sub y2 y3)) y0.
Definition term48 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) x0.
Definition term41 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.sub (S y0) (S y1)) = (Nat.sub y0 y1)) x0.
Definition term16 := fun y0 : nat => (forall y1 : nat, forall y2 : nat, (Nat.sub (Nat.add y0 y1) (Nat.add y0 y2)) = (Nat.sub y1 y2)) -> forall y1 : nat, forall y2 : nat, (Nat.sub (Nat.add (S y0) y1) (Nat.add (S y0) y2)) = (Nat.sub y1 y2).
Definition term19 := ((fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.sub (Nat.add y0 y1) (Nat.add y0 y2)) = (Nat.sub y1 y2)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, forall y3 : nat, (Nat.sub (Nat.add y1 y2) (Nat.add y1 y3)) = (Nat.sub y2 y3)) y0) -> (fun y1 : nat => forall y2 : nat, forall y3 : nat, (Nat.sub (Nat.add y1 y2) (Nat.add y1 y3)) = (Nat.sub y2 y3)) (S y0)).
Definition term33 (x0 : nat) (x1 : nat) := @eq nat (Nat.sub x0 x1).
Definition term58 (x0 : nat) (x1 : nat) := Nat.sub (S (Nat.add x0 x1)).
Definition term39 (x0 : Prop) := forall y0 : nat, x0.
Definition term56 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.sub (Nat.add x1 x0) (Nat.add x1 x2).
Definition term30 (x0 : nat) := Nat.sub (Nat.add (NUMERAL 0) x0).
Definition term13 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.sub (Nat.add y0 y1) (Nat.add y0 y2)) = (Nat.sub y1 y2)) x0) -> (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.sub (Nat.add y0 y1) (Nat.add y0 y2)) = (Nat.sub y1 y2)) (S x0).
Definition term24 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, forall y3 : nat, (Nat.sub (Nat.add y1 y2) (Nat.add y1 y3)) = (Nat.sub y2 y3)) y0.
Definition term10 (x0 : nat) := imp (forall y0 : nat, forall y1 : nat, (Nat.sub (Nat.add x0 y0) (Nat.add x0 y1)) = (Nat.sub y0 y1)).
Definition term20 := (forall y0 : nat, forall y1 : nat, (Nat.sub (Nat.add (NUMERAL 0) y0) (Nat.add (NUMERAL 0) y1)) = (Nat.sub y0 y1)) /\ (forall y0 : nat, (forall y1 : nat, forall y2 : nat, (Nat.sub (Nat.add y0 y1) (Nat.add y0 y2)) = (Nat.sub y1 y2)) -> forall y1 : nat, forall y2 : nat, (Nat.sub (Nat.add (S y0) y1) (Nat.add (S y0) y2)) = (Nat.sub y1 y2)).
Definition term51 (x0 : nat) (x1 : nat) := Nat.add (S x0) x1.
Definition term2 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.sub (Nat.add y0 y1) (Nat.add y0 y2)) = (Nat.sub y1 y2).
Definition term31 (x0 : nat) (x1 : nat) := Nat.sub (Nat.add (NUMERAL 0) x0) (Nat.add (NUMERAL 0) x1).
