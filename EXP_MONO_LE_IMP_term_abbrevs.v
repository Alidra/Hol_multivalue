Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term23 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) -> forall y0 : nat, Peano.le (Nat.pow x0 y0) (Nat.pow x1 y0).
Definition term49 (x0 : nat) (x1 : nat) := (Peano.le (Nat.pow x0 (NUMERAL 0)) (Nat.pow x1 (NUMERAL 0))) /\ (forall y0 : nat, (Peano.le (Nat.pow x0 y0) (Nat.pow x1 y0)) -> Peano.le (Nat.pow x0 (S y0)) (Nat.pow x1 (S y0))).
Definition term67 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y1) /\ (Peano.le y2 y3)) -> Peano.le (Nat.mul y0 y2) (Nat.mul y1 y3)) x0.
Definition term73 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => ((Peano.le x0 x2) /\ (Peano.le x1 y0)) -> Peano.le (Nat.mul x0 x1) (Nat.mul x2 y0)) x3.
Definition term7 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le x0 x1) -> (fun y1 : nat => Peano.le (Nat.pow x0 y1) (Nat.pow x1 y1)) y0.
Definition term63 (x0 : nat) := forall y0 : nat, (Nat.pow x0 (S y0)) = (Nat.mul x0 (Nat.pow x0 y0)).
Definition term21 (x0 : nat) (x1 : nat) := forall y0 : nat, (fun y1 : nat => Peano.le (Nat.pow x0 y1) (Nat.pow x1 y1)) y0.
Definition term48 (x0 : nat) (x1 : nat) := ((fun y0 : nat => Peano.le (Nat.pow x0 y0) (Nat.pow x1 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => Peano.le (Nat.pow x0 y1) (Nat.pow x1 y1)) y0) -> (fun y1 : nat => Peano.le (Nat.pow x0 y1) (Nat.pow x1 y1)) (S y0)).
Definition term2 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (forall y1 : a0, x0 -> y0 y1) = (x0 -> forall y1 : a0, y0 y1)) x1.
Definition term65 (x0 : nat) (x1 : nat) := Nat.pow x0 (S x1).
Definition term12 (x0 : nat) (x1 : nat) := imp (Peano.le x0 x1).
Definition term9 (x0 : nat) (x1 : nat) := fun y0 : nat => Peano.le (Nat.pow x0 y0) (Nat.pow x1 y0).
Definition term33 (x0 : nat) (x1 : nat) := (((fun y0 : nat => Peano.le (Nat.pow x0 y0) (Nat.pow x1 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => Peano.le (Nat.pow x0 y1) (Nat.pow x1 y1)) y0) -> (fun y1 : nat => Peano.le (Nat.pow x0 y1) (Nat.pow x1 y1)) (S y0))) -> forall y0 : nat, (fun y1 : nat => Peano.le (Nat.pow x0 y1) (Nat.pow x1 y1)) y0.
Definition term27 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) -> forall y1 : nat, Peano.le (Nat.pow x0 y1) (Nat.pow y0 y1).
Definition term64 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.pow x0 (S y0)) = (Nat.mul x0 (Nat.pow x0 y0))) x1.
Definition term11 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.pow x0 x2) (Nat.pow x1 x2).
Definition term56 (x0 : nat) := Nat.pow x0 (NUMERAL 0).
Definition term32 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term19 (x0 : nat) (x1 : nat) := @eq Prop (forall y0 : nat, (Peano.le x0 x1) -> Peano.le (Nat.pow x0 y0) (Nat.pow x1 y0)).
Definition term18 (x0 : nat) (x1 : nat) := @eq Prop (forall y0 : nat, (Peano.le x0 x1) -> (fun y1 : nat => Peano.le (Nat.pow x0 y1) (Nat.pow x1 y1)) y0).
Definition term50 (x0 : nat) (x1 : nat) := imp (((fun y0 : nat => Peano.le (Nat.pow x0 y0) (Nat.pow x1 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => Peano.le (Nat.pow x0 y1) (Nat.pow x1 y1)) y0) -> (fun y1 : nat => Peano.le (Nat.pow x0 y1) (Nat.pow x1 y1)) (S y0))).
Definition term46 (x0 : nat) (x1 : nat) := forall y0 : nat, ((fun y1 : nat => Peano.le (Nat.pow x0 y1) (Nat.pow x1 y1)) y0) -> (fun y1 : nat => Peano.le (Nat.pow x0 y1) (Nat.pow x1 y1)) (S y0).
Definition term3 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := forall y0 : a0, x0 -> x1 y0.
Definition term0 (a0 : Type') (x0 : Prop) := (fun y0 : Prop => forall y1 : a0 -> Prop, (forall y2 : a0, y0 -> y1 y2) = (y0 -> forall y2 : a0, y1 y2)) x0.
Definition term15 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le x0 x1) -> (fun y1 : nat => Peano.le (Nat.pow x0 y1) (Nat.pow x1 y1)) y0.
Definition term1 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, (forall y1 : a0, x0 -> y0 y1) = (x0 -> forall y1 : a0, y0 y1).
Definition term53 (x0 : nat) := (fun y0 : nat => Peano.le y0 y0) x0.
Definition term36 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => Peano.le (Nat.pow x0 y0) (Nat.pow x1 y0)) (NUMERAL 0)).
Definition term78 (x0 : nat) (x1 : nat) := Peano.le (Nat.mul x0 (Nat.pow x0 x1)).
Definition term17 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le x0 x1) -> Peano.le (Nat.pow x0 y0) (Nat.pow x1 y0).
Definition term22 (x0 : nat) (x1 : nat) := forall y0 : nat, Peano.le (Nat.pow x0 y0) (Nat.pow x1 y0).
Definition term40 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => Peano.le (Nat.pow x0 y0) (Nat.pow x1 y0)) (S x2).
Definition term55 (x0 : nat) := (fun y0 : nat => (Nat.pow y0 (NUMERAL 0)) = (NUMERAL (BIT1 0))) x0.
Definition term44 (x0 : nat) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => Peano.le (Nat.pow x0 y1) (Nat.pow x1 y1)) y0) -> (fun y1 : nat => Peano.le (Nat.pow x0 y1) (Nat.pow x1 y1)) (S y0).
Definition term4 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 -> forall y0 : a0, x1 y0.
Definition term8 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) -> forall y0 : nat, (fun y1 : nat => Peano.le (Nat.pow x0 y1) (Nat.pow x1 y1)) y0.
Definition term43 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le (Nat.pow x0 x2) (Nat.pow x1 x2)) -> Peano.le (Nat.pow x0 (S x2)) (Nat.pow x1 (S x2)).
Definition term13 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) -> (fun y0 : nat => Peano.le (Nat.pow x0 y0) (Nat.pow x1 y0)) x2.
Definition term70 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 x1) /\ (Peano.le y0 y1)) -> Peano.le (Nat.mul x0 y0) (Nat.mul x1 y1).
Definition term68 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le x0 y0) /\ (Peano.le y1 y2)) -> Peano.le (Nat.mul x0 y1) (Nat.mul y0 y2).
Definition term61 := forall y0 : nat, forall y1 : nat, (Nat.pow y0 (S y1)) = (Nat.mul y0 (Nat.pow y0 y1)).
Definition term31 := forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> forall y2 : nat, Peano.le (Nat.pow y0 y2) (Nat.pow y1 y2).
Definition term30 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le y0 y1) -> Peano.le (Nat.pow y0 y2) (Nat.pow y1 y2).
Definition term26 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le x0 y0) -> Peano.le (Nat.pow x0 y1) (Nat.pow y0 y1).
Definition term58 (x0 : nat) := Peano.le (Nat.pow x0 (NUMERAL 0)).
Definition term83 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) /\ (Peano.le (Nat.pow x0 x2) (Nat.pow x1 x2)).
Definition term71 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le x0 x1) /\ (Peano.le y0 y1)) -> Peano.le (Nat.mul x0 y0) (Nat.mul x1 y1)) x2.
Definition term69 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le x0 y0) /\ (Peano.le y1 y2)) -> Peano.le (Nat.mul x0 y1) (Nat.mul y0 y2)) x1.
Definition term29 := fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) -> forall y2 : nat, Peano.le (Nat.pow y0 y2) (Nat.pow y1 y2).
Definition term80 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Peano.le x0 x2) /\ (Peano.le x1 x3)) -> (Peano.le (Nat.mul x0 x1) (Nat.mul x2 x3)) = True.
Definition term14 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) -> Peano.le (Nat.pow x0 x2) (Nat.pow x1 x2).
Definition term35 (x0 : nat) (x1 : nat) := Peano.le (Nat.pow x0 (NUMERAL 0)) (Nat.pow x1 (NUMERAL 0)).
Definition term76 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.mul x0 x1) (Nat.mul x2 x3).
Definition term66 (x0 : nat) (x1 : nat) := Nat.mul x0 (Nat.pow x0 x1).
Definition term20 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => Peano.le (Nat.pow x0 y1) (Nat.pow x1 y1)) y0.
Definition term81 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x0 x1) /\ (Peano.le (Nat.pow x0 x2) (Nat.pow x1 x2))) -> (Peano.le (Nat.mul x0 (Nat.pow x0 x2)) (Nat.mul x1 (Nat.pow x1 x2))) = True.
Definition term52 (x0 : nat) (x1 : nat) := ((Peano.le (Nat.pow x0 (NUMERAL 0)) (Nat.pow x1 (NUMERAL 0))) /\ (forall y0 : nat, (Peano.le (Nat.pow x0 y0) (Nat.pow x1 y0)) -> Peano.le (Nat.pow x0 (S y0)) (Nat.pow x1 (S y0)))) -> forall y0 : nat, Peano.le (Nat.pow x0 y0) (Nat.pow x1 y0).
Definition term10 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => Peano.le (Nat.pow x0 y0) (Nat.pow x1 y0)) x2.
Definition term74 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Peano.le x0 x2) /\ (Peano.le x1 x3)) -> Peano.le (Nat.mul x0 x1) (Nat.mul x2 x3).
Definition term77 (x0 : nat) (x1 : nat) := Peano.le (Nat.pow x0 (S x1)).
Definition term6 (x0 : Prop) (x1 : nat -> Prop) := x0 -> forall y0 : nat, x1 y0.
Definition term34 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le (Nat.pow x0 y0) (Nat.pow x1 y0)) (NUMERAL 0).
Definition term62 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.pow y0 (S y1)) = (Nat.mul y0 (Nat.pow y0 y1))) x0.
Definition term54 := forall y0 : nat, (Nat.pow y0 (NUMERAL 0)) = (NUMERAL (BIT1 0)).
Definition term75 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x0 x1) /\ (Peano.le x2 x3).
Definition term72 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, ((Peano.le x0 x2) /\ (Peano.le x1 y0)) -> Peano.le (Nat.mul x0 x1) (Nat.mul x2 y0).
Definition term37 (x0 : nat) (x1 : nat) := and (Peano.le (Nat.pow x0 (NUMERAL 0)) (Nat.pow x1 (NUMERAL 0))).
Definition term41 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.pow x0 (S x2)) (Nat.pow x1 (S x2)).
Definition term39 (x0 : nat) (x1 : nat) (x2 : nat) := imp (Peano.le (Nat.pow x0 x2) (Nat.pow x1 x2)).
Definition term51 (x0 : nat) (x1 : nat) := imp ((Peano.le (Nat.pow x0 (NUMERAL 0)) (Nat.pow x1 (NUMERAL 0))) /\ (forall y0 : nat, (Peano.le (Nat.pow x0 y0) (Nat.pow x1 y0)) -> Peano.le (Nat.pow x0 (S y0)) (Nat.pow x1 (S y0)))).
Definition term47 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.pow x0 y0) (Nat.pow x1 y0)) -> Peano.le (Nat.pow x0 (S y0)) (Nat.pow x1 (S y0)).
Definition term42 (x0 : nat) (x1 : nat) (x2 : nat) := ((fun y0 : nat => Peano.le (Nat.pow x0 y0) (Nat.pow x1 y0)) x2) -> (fun y0 : nat => Peano.le (Nat.pow x0 y0) (Nat.pow x1 y0)) (S x2).
Definition term38 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((fun y0 : nat => Peano.le (Nat.pow x0 y0) (Nat.pow x1 y0)) x2).
Definition term79 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x0 (Nat.pow x0 x2)) (Nat.mul x1 (Nat.pow x1 x2)).
Definition term60 := Peano.le (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term25 (x0 : nat) := fun y0 : nat => (Peano.le x0 y0) -> forall y1 : nat, Peano.le (Nat.pow x0 y1) (Nat.pow y0 y1).
Definition term5 (x0 : Prop) (x1 : nat -> Prop) := forall y0 : nat, x0 -> x1 y0.
Definition term24 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Peano.le x0 y0) -> Peano.le (Nat.pow x0 y1) (Nat.pow y0 y1).
Definition term82 (x0 : nat) (x1 : nat) := and (Peano.le x0 x1).
Definition term57 := NUMERAL (BIT1 0).
Definition term59 := Peano.le (NUMERAL (BIT1 0)).
Definition term28 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le y0 y1) -> Peano.le (Nat.pow y0 y2) (Nat.pow y1 y2).
Definition term45 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le (Nat.pow x0 y0) (Nat.pow x1 y0)) -> Peano.le (Nat.pow x0 (S y0)) (Nat.pow x1 (S y0)).
Definition term16 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le x0 x1) -> Peano.le (Nat.pow x0 y0) (Nat.pow x1 y0).
