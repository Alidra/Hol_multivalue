Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term154 (x0 : nat) := ~ ((NUMERAL 0) = (S x0)).
Definition term170 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul x0 (S y0)) = (Nat.add x0 (Nat.mul x0 y0))) x1.
Definition term71 (x0 : nat) (x1 : nat) := @eq nat (Nat.add (Nat.mul x0 x1) x1).
Definition term132 (x0 : nat) (x1 : nat) := fun y0 : nat => ((Nat.add (Nat.mul x0 (S x1)) (S x1)) = (Nat.add (Nat.mul x0 y0) y0)) = ((S x1) = y0).
Definition term58 := @eq nat (NUMERAL 0).
Definition term18 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term27 := forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0).
Definition term194 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add (Nat.add y0 y1) y2) = (Nat.add y0 (Nat.add y1 y2))) x0.
Definition term189 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) = (y1 = y2)) x0.
Definition term37 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.mul y0 y1) = (Nat.mul y0 y2)) = ((y0 = (NUMERAL 0)) \/ (y1 = y2))) x0.
Definition term78 (x0 : nat) (x1 : nat) := fun y0 : nat => ((Nat.add (Nat.mul x0 x1) x1) = (Nat.add (Nat.mul x0 y0) y0)) = (x1 = y0).
Definition term44 (x0 : nat) := (forall y0 : nat, forall y1 : nat, ((Nat.mul x0 y0) = (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (y0 = y1))) -> forall y0 : nat, forall y1 : nat, ((Nat.mul (S x0) y0) = (Nat.mul (S x0) y1)) = (((S x0) = (NUMERAL 0)) \/ (y0 = y1)).
Definition term67 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term147 (x0 : nat) (x1 : nat) := (((Nat.add (Nat.mul x0 (S x1)) (S x1)) = (Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0))) = ((S x1) = (NUMERAL 0))) /\ (forall y0 : nat, (((Nat.add (Nat.mul x0 (S x1)) (S x1)) = (Nat.add (Nat.mul x0 y0) y0)) = ((S x1) = y0)) -> ((Nat.add (Nat.mul x0 (S x1)) (S x1)) = (Nat.add (Nat.mul x0 (S y0)) (S y0))) = ((S x1) = (S y0))).
Definition term125 (x0 : nat) := (((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0))) = ((NUMERAL 0) = (NUMERAL 0))) /\ (forall y0 : nat, (((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 y0) y0)) = ((NUMERAL 0) = y0)) -> ((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 (S y0)) (S y0))) = ((NUMERAL 0) = (S y0))).
Definition term99 (x0 : nat) := forall y0 : nat, (forall y1 : nat, ((Nat.add (Nat.mul x0 y0) y0) = (Nat.add (Nat.mul x0 y1) y1)) = (y0 = y1)) -> forall y1 : nat, ((Nat.add (Nat.mul x0 (S y0)) (S y0)) = (Nat.add (Nat.mul x0 y1) y1)) = ((S y0) = y1).
Definition term48 := forall y0 : nat, (forall y1 : nat, forall y2 : nat, ((Nat.mul y0 y1) = (Nat.mul y0 y2)) = ((y0 = (NUMERAL 0)) \/ (y1 = y2))) -> forall y1 : nat, forall y2 : nat, ((Nat.mul (S y0) y1) = (Nat.mul (S y0) y2)) = (((S y0) = (NUMERAL 0)) \/ (y1 = y2)).
Definition term169 (x0 : nat) := forall y0 : nat, (Nat.mul x0 (S y0)) = (Nat.add x0 (Nat.mul x0 y0)).
Definition term157 := (forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))).
Definition term20 := (forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))).
Definition term92 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.add (Nat.mul x0 y0) y0) = (Nat.add (Nat.mul x0 y1) y1)) = (y0 = y1)) (S x1).
Definition term24 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul (S x0) y0) = (Nat.add (Nat.mul x0 y0) y0)) x1.
Definition term28 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) x0.
Definition term198 (x0 : nat) := forall y0 : nat, ((S x0) = (S y0)) = (x0 = y0).
Definition term192 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Nat.add x0 x1) = (Nat.add x0 y0)) = (x1 = y0).
Definition term80 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Nat.add (Nat.mul x0 x1) x1) = (Nat.add (Nat.mul x0 y0) y0)) = (x1 = y0).
Definition term108 (x0 : nat) := fun y0 : nat => ((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 y0) y0)) = ((NUMERAL 0) = y0).
Definition term106 (x0 : nat) := ((forall y0 : nat, ((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 y0) y0)) = ((NUMERAL 0) = y0)) /\ (forall y0 : nat, (forall y1 : nat, ((Nat.add (Nat.mul x0 y0) y0) = (Nat.add (Nat.mul x0 y1) y1)) = (y0 = y1)) -> forall y1 : nat, ((Nat.add (Nat.mul x0 (S y0)) (S y0)) = (Nat.add (Nat.mul x0 y1) y1)) = ((S y0) = y1))) -> forall y0 : nat, forall y1 : nat, ((Nat.add (Nat.mul x0 y0) y0) = (Nat.add (Nat.mul x0 y1) y1)) = (y0 = y1).
Definition term56 := ((forall y0 : nat, forall y1 : nat, ((Nat.mul (NUMERAL 0) y0) = (Nat.mul (NUMERAL 0) y1)) = (((NUMERAL 0) = (NUMERAL 0)) \/ (y0 = y1))) /\ (forall y0 : nat, (forall y1 : nat, forall y2 : nat, ((Nat.mul y0 y1) = (Nat.mul y0 y2)) = ((y0 = (NUMERAL 0)) \/ (y1 = y2))) -> forall y1 : nat, forall y2 : nat, ((Nat.mul (S y0) y1) = (Nat.mul (S y0) y2)) = (((S y0) = (NUMERAL 0)) \/ (y1 = y2)))) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Nat.mul y0 y1) = (Nat.mul y0 y2)) = ((y0 = (NUMERAL 0)) \/ (y1 = y2)).
Definition term151 (x0 : nat) (x1 : nat) := forall y0 : nat, (fun y1 : nat => ((Nat.add (Nat.mul x0 (S x1)) (S x1)) = (Nat.add (Nat.mul x0 y1) y1)) = ((S x1) = y1)) y0.
Definition term129 (x0 : nat) := forall y0 : nat, (fun y1 : nat => ((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 y1) y1)) = ((NUMERAL 0) = y1)) y0.
Definition term146 (x0 : nat) (x1 : nat) := ((fun y0 : nat => ((Nat.add (Nat.mul x0 (S x1)) (S x1)) = (Nat.add (Nat.mul x0 y0) y0)) = ((S x1) = y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Nat.add (Nat.mul x0 (S x1)) (S x1)) = (Nat.add (Nat.mul x0 y1) y1)) = ((S x1) = y1)) y0) -> (fun y1 : nat => ((Nat.add (Nat.mul x0 (S x1)) (S x1)) = (Nat.add (Nat.mul x0 y1) y1)) = ((S x1) = y1)) (S y0)).
Definition term124 (x0 : nat) := ((fun y0 : nat => ((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 y0) y0)) = ((NUMERAL 0) = y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 y1) y1)) = ((NUMERAL 0) = y1)) y0) -> (fun y1 : nat => ((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 y1) y1)) = ((NUMERAL 0) = y1)) (S y0)).
Definition term39 (x0 : nat) := imp ((fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.mul y0 y1) = (Nat.mul y0 y2)) = ((y0 = (NUMERAL 0)) \/ (y1 = y2))) x0).
Definition term113 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 y0) y0)) = ((NUMERAL 0) = y0)) x1.
Definition term183 (x0 : nat) (x1 : nat) := @eq Prop ((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 (S x1)) (S x1))).
Definition term165 (x0 : nat) := (fun y0 : nat => (Nat.add y0 (NUMERAL 0)) = y0) x0.
Definition term1 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add x0 x1) x2.
Definition term141 (x0 : nat) (x1 : nat) (x2 : nat) := (((Nat.add (Nat.mul x0 (S x1)) (S x1)) = (Nat.add (Nat.mul x0 x2) x2)) = ((S x1) = x2)) -> ((Nat.add (Nat.mul x0 (S x1)) (S x1)) = (Nat.add (Nat.mul x0 (S x2)) (S x2))) = ((S x1) = (S x2)).
Definition term118 (x0 : nat) (x1 : nat) := ((fun y0 : nat => ((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 y0) y0)) = ((NUMERAL 0) = y0)) x1) -> (fun y0 : nat => ((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 y0) y0)) = ((NUMERAL 0) = y0)) (S x1).
Definition term131 (x0 : nat) (x1 : nat) := (((fun y0 : nat => ((Nat.add (Nat.mul x0 (S x1)) (S x1)) = (Nat.add (Nat.mul x0 y0) y0)) = ((S x1) = y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Nat.add (Nat.mul x0 (S x1)) (S x1)) = (Nat.add (Nat.mul x0 y1) y1)) = ((S x1) = y1)) y0) -> (fun y1 : nat => ((Nat.add (Nat.mul x0 (S x1)) (S x1)) = (Nat.add (Nat.mul x0 y1) y1)) = ((S x1) = y1)) (S y0))) -> forall y0 : nat, (fun y1 : nat => ((Nat.add (Nat.mul x0 (S x1)) (S x1)) = (Nat.add (Nat.mul x0 y1) y1)) = ((S x1) = y1)) y0.
Definition term107 (x0 : nat) := (((fun y0 : nat => ((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 y0) y0)) = ((NUMERAL 0) = y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 y1) y1)) = ((NUMERAL 0) = y1)) y0) -> (fun y1 : nat => ((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 y1) y1)) = ((NUMERAL 0) = y1)) (S y0))) -> forall y0 : nat, (fun y1 : nat => ((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 y1) y1)) = ((NUMERAL 0) = y1)) y0.
Definition term84 (x0 : nat) := (((fun y0 : nat => forall y1 : nat, ((Nat.add (Nat.mul x0 y0) y0) = (Nat.add (Nat.mul x0 y1) y1)) = (y0 = y1)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.add (Nat.mul x0 y1) y1) = (Nat.add (Nat.mul x0 y2) y2)) = (y1 = y2)) y0) -> (fun y1 : nat => forall y2 : nat, ((Nat.add (Nat.mul x0 y1) y1) = (Nat.add (Nat.mul x0 y2) y2)) = (y1 = y2)) (S y0))) -> forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Nat.add (Nat.mul x0 y1) y1) = (Nat.add (Nat.mul x0 y2) y2)) = (y1 = y2)) y0.
Definition term31 := (((fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.mul y0 y1) = (Nat.mul y0 y2)) = ((y0 = (NUMERAL 0)) \/ (y1 = y2))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Nat.mul y1 y2) = (Nat.mul y1 y3)) = ((y1 = (NUMERAL 0)) \/ (y2 = y3))) y0) -> (fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Nat.mul y1 y2) = (Nat.mul y1 y3)) = ((y1 = (NUMERAL 0)) \/ (y2 = y3))) (S y0))) -> forall y0 : nat, (fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Nat.mul y1 y2) = (Nat.mul y1 y3)) = ((y1 = (NUMERAL 0)) \/ (y2 = y3))) y0.
Definition term2 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.add x0 (Nat.add x1 y0)) = (Nat.add (Nat.add x0 x1) y0).
Definition term30 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term148 (x0 : nat) (x1 : nat) := imp (((fun y0 : nat => ((Nat.add (Nat.mul x0 (S x1)) (S x1)) = (Nat.add (Nat.mul x0 y0) y0)) = ((S x1) = y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Nat.add (Nat.mul x0 (S x1)) (S x1)) = (Nat.add (Nat.mul x0 y1) y1)) = ((S x1) = y1)) y0) -> (fun y1 : nat => ((Nat.add (Nat.mul x0 (S x1)) (S x1)) = (Nat.add (Nat.mul x0 y1) y1)) = ((S x1) = y1)) (S y0))).
Definition term126 (x0 : nat) := imp (((fun y0 : nat => ((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 y0) y0)) = ((NUMERAL 0) = y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 y1) y1)) = ((NUMERAL 0) = y1)) y0) -> (fun y1 : nat => ((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 y1) y1)) = ((NUMERAL 0) = y1)) (S y0))).
Definition term102 (x0 : nat) := imp (((fun y0 : nat => forall y1 : nat, ((Nat.add (Nat.mul x0 y0) y0) = (Nat.add (Nat.mul x0 y1) y1)) = (y0 = y1)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.add (Nat.mul x0 y1) y1) = (Nat.add (Nat.mul x0 y2) y2)) = (y1 = y2)) y0) -> (fun y1 : nat => forall y2 : nat, ((Nat.add (Nat.mul x0 y1) y1) = (Nat.add (Nat.mul x0 y2) y2)) = (y1 = y2)) (S y0))).
Definition term51 := imp (((fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.mul y0 y1) = (Nat.mul y0 y2)) = ((y0 = (NUMERAL 0)) \/ (y1 = y2))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Nat.mul y1 y2) = (Nat.mul y1 y3)) = ((y1 = (NUMERAL 0)) \/ (y2 = y3))) y0) -> (fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Nat.mul y1 y2) = (Nat.mul y1 y3)) = ((y1 = (NUMERAL 0)) \/ (y2 = y3))) (S y0))).
Definition term93 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Nat.add (Nat.mul x0 (S x1)) (S x1)) = (Nat.add (Nat.mul x0 y0) y0)) = ((S x1) = y0).
Definition term86 (x0 : nat) := forall y0 : nat, ((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 y0) y0)) = ((NUMERAL 0) = y0).
Definition term4 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.add x0 (Nat.add x1 y0)) = (Nat.add (Nat.add x0 x1) y0).
Definition term166 (x0 : nat) := Nat.add x0 (NUMERAL 0).
Definition term195 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add (Nat.add x0 y0) y1) = (Nat.add x0 (Nat.add y0 y1))) x1.
Definition term191 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.add x0 y0) = (Nat.add x0 y1)) = (y0 = y1)) x1.
Definition term89 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.add (Nat.mul x0 y0) y0) = (Nat.add (Nat.mul x0 y1) y1)) = (y0 = y1)) x1.
Definition term25 (x0 : nat) (x1 : nat) := Nat.mul (S x0) x1.
Definition term153 (x0 : nat) := @eq Prop ((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0))).
Definition term144 (x0 : nat) (x1 : nat) := forall y0 : nat, ((fun y1 : nat => ((Nat.add (Nat.mul x0 (S x1)) (S x1)) = (Nat.add (Nat.mul x0 y1) y1)) = ((S x1) = y1)) y0) -> (fun y1 : nat => ((Nat.add (Nat.mul x0 (S x1)) (S x1)) = (Nat.add (Nat.mul x0 y1) y1)) = ((S x1) = y1)) (S y0).
Definition term122 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => ((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 y1) y1)) = ((NUMERAL 0) = y1)) y0) -> (fun y1 : nat => ((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 y1) y1)) = ((NUMERAL 0) = y1)) (S y0).
Definition term98 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.add (Nat.mul x0 y1) y1) = (Nat.add (Nat.mul x0 y2) y2)) = (y1 = y2)) y0) -> (fun y1 : nat => forall y2 : nat, ((Nat.add (Nat.mul x0 y1) y1) = (Nat.add (Nat.mul x0 y2) y2)) = (y1 = y2)) (S y0).
Definition term47 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Nat.mul y1 y2) = (Nat.mul y1 y3)) = ((y1 = (NUMERAL 0)) \/ (y2 = y3))) y0) -> (fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Nat.mul y1 y2) = (Nat.mul y1 y3)) = ((y1 = (NUMERAL 0)) \/ (y2 = y3))) (S y0).
Definition term82 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((Nat.add (Nat.mul x0 y0) y0) = (Nat.add (Nat.mul x0 y1) y1)) = (y0 = y1).
Definition term6 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add (Nat.add x0 y0) y1).
Definition term171 (x0 : nat) (x1 : nat) := Nat.mul x0 (S x1).
Definition term164 := forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0.
Definition term110 (x0 : nat) := Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0).
Definition term134 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => ((Nat.add (Nat.mul x0 (S x1)) (S x1)) = (Nat.add (Nat.mul x0 y0) y0)) = ((S x1) = y0)) (NUMERAL 0)).
Definition term111 (x0 : nat) := and ((fun y0 : nat => ((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 y0) y0)) = ((NUMERAL 0) = y0)) (NUMERAL 0)).
Definition term174 (x0 : nat) := (fun y0 : nat => (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) x0.
Definition term202 (x0 : nat) (x1 : nat) := @eq nat (Nat.add (Nat.add x0 (Nat.mul x0 x1)) x1).
Definition term87 (x0 : nat) := and ((fun y0 : nat => forall y1 : nat, ((Nat.add (Nat.mul x0 y0) y0) = (Nat.add (Nat.mul x0 y1) y1)) = (y0 = y1)) (NUMERAL 0)).
Definition term35 := and ((fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.mul y0 y1) = (Nat.mul y0 y2)) = ((y0 = (NUMERAL 0)) \/ (y1 = y2))) (NUMERAL 0)).
Definition term91 (x0 : nat) (x1 : nat) := imp (forall y0 : nat, ((Nat.add (Nat.mul x0 x1) x1) = (Nat.add (Nat.mul x0 y0) y0)) = (x1 = y0)).
Definition term88 (x0 : nat) := and (forall y0 : nat, ((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 y0) y0)) = ((NUMERAL 0) = y0)).
Definition term41 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.mul y0 y1) = (Nat.mul y0 y2)) = ((y0 = (NUMERAL 0)) \/ (y1 = y2))) (S x0).
Definition term85 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.add (Nat.mul x0 y0) y0) = (Nat.add (Nat.mul x0 y1) y1)) = (y0 = y1)) (NUMERAL 0).
Definition term33 := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.mul y0 y1) = (Nat.mul y0 y2)) = ((y0 = (NUMERAL 0)) \/ (y1 = y2))) (NUMERAL 0).
Definition term142 (x0 : nat) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => ((Nat.add (Nat.mul x0 (S x1)) (S x1)) = (Nat.add (Nat.mul x0 y1) y1)) = ((S x1) = y1)) y0) -> (fun y1 : nat => ((Nat.add (Nat.mul x0 (S x1)) (S x1)) = (Nat.add (Nat.mul x0 y1) y1)) = ((S x1) = y1)) (S y0).
Definition term120 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => ((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 y1) y1)) = ((NUMERAL 0) = y1)) y0) -> (fun y1 : nat => ((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 y1) y1)) = ((NUMERAL 0) = y1)) (S y0).
Definition term188 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((S (Nat.add (Nat.add x1 (Nat.mul x1 x0)) x0)) = (S (Nat.add (Nat.add x1 (Nat.mul x1 x2)) x2))).
Definition term76 (x0 : nat) (x1 : nat) := False \/ (x0 = x1).
Definition term103 (x0 : nat) := imp ((forall y0 : nat, ((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 y0) y0)) = ((NUMERAL 0) = y0)) /\ (forall y0 : nat, (forall y1 : nat, ((Nat.add (Nat.mul x0 y0) y0) = (Nat.add (Nat.mul x0 y1) y1)) = (y0 = y1)) -> forall y1 : nat, ((Nat.add (Nat.mul x0 (S y0)) (S y0)) = (Nat.add (Nat.mul x0 y1) y1)) = ((S y0) = y1))).
Definition term52 := imp ((forall y0 : nat, forall y1 : nat, ((Nat.mul (NUMERAL 0) y0) = (Nat.mul (NUMERAL 0) y1)) = (((NUMERAL 0) = (NUMERAL 0)) \/ (y0 = y1))) /\ (forall y0 : nat, (forall y1 : nat, forall y2 : nat, ((Nat.mul y0 y1) = (Nat.mul y0 y2)) = ((y0 = (NUMERAL 0)) \/ (y1 = y2))) -> forall y1 : nat, forall y2 : nat, ((Nat.mul (S y0) y1) = (Nat.mul (S y0) y2)) = (((S y0) = (NUMERAL 0)) \/ (y1 = y2)))).
Definition term182 (x0 : nat) (x1 : nat) := S (Nat.add (Nat.add x0 (Nat.mul x0 x1)) x1).
Definition term177 (x0 : nat) (x1 : nat) := S (Nat.add (Nat.mul x0 (S x1)) x1).
Definition term163 (x0 : nat) (x1 : nat) := S (Nat.add x0 x1).
Definition term119 (x0 : nat) (x1 : nat) := (((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 x1) x1)) = ((NUMERAL 0) = x1)) -> ((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 (S x1)) (S x1))) = ((NUMERAL 0) = (S x1)).
Definition term57 (x0 : nat) := @eq nat (Nat.mul (NUMERAL 0) x0).
Definition term72 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((Nat.mul (S x1) x0) = (Nat.mul (S x1) x2)).
Definition term190 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Nat.add x0 y0) = (Nat.add x0 y1)) = (y0 = y1).
Definition term167 := forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)).
Definition term158 := forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)).
Definition term83 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Nat.add (Nat.mul x0 y0) y0) = (Nat.add (Nat.mul x0 y1) y1)) = (y0 = y1).
Definition term55 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Nat.mul y0 y1) = (Nat.mul y0 y2)) = ((y0 = (NUMERAL 0)) \/ (y1 = y2)).
Definition term42 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Nat.mul (S x0) y0) = (Nat.mul (S x0) y1)) = (((S x0) = (NUMERAL 0)) \/ (y0 = y1)).
Definition term38 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Nat.mul x0 y0) = (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (y0 = y1)).
Definition term34 := forall y0 : nat, forall y1 : nat, ((Nat.mul (NUMERAL 0) y0) = (Nat.mul (NUMERAL 0) y1)) = (((NUMERAL 0) = (NUMERAL 0)) \/ (y0 = y1)).
Definition term21 := forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1).
Definition term13 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add (Nat.add y0 y1) y2) = (Nat.add y0 (Nat.add y1 y2)).
Definition term12 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2).
Definition term9 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add x0 y0) y1) = (Nat.add x0 (Nat.add y0 y1)).
Definition term8 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add (Nat.add x0 y0) y1).
Definition term184 (x0 : nat) (x1 : nat) := @eq nat (Nat.add (Nat.mul x0 (S x1)) (S x1)).
Definition term176 (x0 : nat) := @eq nat (Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)).
Definition term203 (x0 : nat) (x1 : nat) := @eq nat (Nat.add x0 (Nat.add (Nat.mul x0 x1) x1)).
Definition term70 (x0 : nat) (x1 : nat) := @eq nat (Nat.mul (S x0) x1).
Definition term66 := forall y0 : nat, True.
Definition term73 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((Nat.add (Nat.mul x1 x0) x0) = (Nat.add (Nat.mul x1 x2) x2)).
Definition term114 (x0 : nat) (x1 : nat) := imp ((fun y0 : nat => ((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 y0) y0)) = ((NUMERAL 0) = y0)) x1).
Definition term23 (x0 : nat) := forall y0 : nat, (Nat.mul (S x0) y0) = (Nat.add (Nat.mul x0 y0) y0).
Definition term64 := fun y0 : nat => True.
Definition term79 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Nat.mul (S x0) x1) = (Nat.mul (S x0) y0)) = (((S x0) = (NUMERAL 0)) \/ (x1 = y0)).
Definition term65 (x0 : nat) := forall y0 : nat, ((Nat.mul (NUMERAL 0) x0) = (Nat.mul (NUMERAL 0) y0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ (x0 = y0)).
Definition term152 (x0 : nat) (x1 : nat) := ((((Nat.add (Nat.mul x0 (S x1)) (S x1)) = (Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0))) = ((S x1) = (NUMERAL 0))) /\ (forall y0 : nat, (((Nat.add (Nat.mul x0 (S x1)) (S x1)) = (Nat.add (Nat.mul x0 y0) y0)) = ((S x1) = y0)) -> ((Nat.add (Nat.mul x0 (S x1)) (S x1)) = (Nat.add (Nat.mul x0 (S y0)) (S y0))) = ((S x1) = (S y0)))) -> forall y0 : nat, ((Nat.add (Nat.mul x0 (S x1)) (S x1)) = (Nat.add (Nat.mul x0 y0) y0)) = ((S x1) = y0).
Definition term130 (x0 : nat) := ((((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0))) = ((NUMERAL 0) = (NUMERAL 0))) /\ (forall y0 : nat, (((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 y0) y0)) = ((NUMERAL 0) = y0)) -> ((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 (S y0)) (S y0))) = ((NUMERAL 0) = (S y0)))) -> forall y0 : nat, ((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 y0) y0)) = ((NUMERAL 0) = y0).
Definition term15 (x0 : nat) := ~ ((S x0) = (NUMERAL 0)).
Definition term90 (x0 : nat) (x1 : nat) := imp ((fun y0 : nat => forall y1 : nat, ((Nat.add (Nat.mul x0 y0) y0) = (Nat.add (Nat.mul x0 y1) y1)) = (y0 = y1)) x1).
Definition term112 (x0 : nat) := and (((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0))) = ((NUMERAL 0) = (NUMERAL 0))).
Definition term196 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.add (Nat.add x0 x1) y0) = (Nat.add x0 (Nat.add x1 y0))) x2.
Definition term116 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 y0) y0)) = ((NUMERAL 0) = y0)) (S x1).
Definition term161 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 (S y0)) = (S (Nat.add x0 y0))) x1.
Definition term97 (x0 : nat) := fun y0 : nat => (forall y1 : nat, ((Nat.add (Nat.mul x0 y0) y0) = (Nat.add (Nat.mul x0 y1) y1)) = (y0 = y1)) -> forall y1 : nat, ((Nat.add (Nat.mul x0 (S y0)) (S y0)) = (Nat.add (Nat.mul x0 y1) y1)) = ((S y0) = y1).
Definition term96 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, ((Nat.add (Nat.mul x0 y1) y1) = (Nat.add (Nat.mul x0 y2) y2)) = (y1 = y2)) y0) -> (fun y1 : nat => forall y2 : nat, ((Nat.add (Nat.mul x0 y1) y1) = (Nat.add (Nat.mul x0 y2) y2)) = (y1 = y2)) (S y0).
Definition term45 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Nat.mul y1 y2) = (Nat.mul y1 y3)) = ((y1 = (NUMERAL 0)) \/ (y2 = y3))) y0) -> (fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Nat.mul y1 y2) = (Nat.mul y1 y3)) = ((y1 = (NUMERAL 0)) \/ (y2 = y3))) (S y0).
Definition term115 (x0 : nat) (x1 : nat) := imp (((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 x1) x1)) = ((NUMERAL 0) = x1)).
Definition term133 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.add (Nat.mul x0 (S x1)) (S x1)) = (Nat.add (Nat.mul x0 y0) y0)) = ((S x1) = y0)) (NUMERAL 0).
Definition term109 (x0 : nat) := (fun y0 : nat => ((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 y0) y0)) = ((NUMERAL 0) = y0)) (NUMERAL 0).
Definition term178 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 (S x1)).
Definition term156 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term19 := (forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))).
Definition term94 (x0 : nat) (x1 : nat) := ((fun y0 : nat => forall y1 : nat, ((Nat.add (Nat.mul x0 y0) y0) = (Nat.add (Nat.mul x0 y1) y1)) = (y0 = y1)) x1) -> (fun y0 : nat => forall y1 : nat, ((Nat.add (Nat.mul x0 y0) y0) = (Nat.add (Nat.mul x0 y1) y1)) = (y0 = y1)) (S x1).
Definition term0 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (Nat.add x1 x2).
Definition term138 (x0 : nat) (x1 : nat) (x2 : nat) := imp (((Nat.add (Nat.mul x0 (S x1)) (S x1)) = (Nat.add (Nat.mul x0 x2) x2)) = ((S x1) = x2)).
Definition term185 (x0 : nat) (x1 : nat) := @eq nat (S (Nat.add (Nat.add x0 (Nat.mul x0 x1)) x1)).
Definition term101 (x0 : nat) := (forall y0 : nat, ((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 y0) y0)) = ((NUMERAL 0) = y0)) /\ (forall y0 : nat, (forall y1 : nat, ((Nat.add (Nat.mul x0 y0) y0) = (Nat.add (Nat.mul x0 y1) y1)) = (y0 = y1)) -> forall y1 : nat, ((Nat.add (Nat.mul x0 (S y0)) (S y0)) = (Nat.add (Nat.mul x0 y1) y1)) = ((S y0) = y1)).
Definition term36 := and (forall y0 : nat, forall y1 : nat, ((Nat.mul (NUMERAL 0) y0) = (Nat.mul (NUMERAL 0) y1)) = (((NUMERAL 0) = (NUMERAL 0)) \/ (y0 = y1))).
Definition term181 (x0 : nat) (x1 : nat) := Nat.add (Nat.add x0 (Nat.mul x0 x1)) x1.
Definition term74 (x0 : nat) := or ((S x0) = (NUMERAL 0)).
Definition term77 (x0 : nat) (x1 : nat) := fun y0 : nat => ((Nat.mul (S x0) x1) = (Nat.mul (S x0) y0)) = (((S x0) = (NUMERAL 0)) \/ (x1 = y0)).
Definition term63 (x0 : nat) := fun y0 : nat => ((Nat.mul (NUMERAL 0) x0) = (Nat.mul (NUMERAL 0) y0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ (x0 = y0)).
Definition term104 (x0 : nat) := fun y0 : nat => (fun y1 : nat => forall y2 : nat, ((Nat.add (Nat.mul x0 y1) y1) = (Nat.add (Nat.mul x0 y2) y2)) = (y1 = y2)) y0.
Definition term53 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Nat.mul y1 y2) = (Nat.mul y1 y3)) = ((y1 = (NUMERAL 0)) \/ (y2 = y3))) y0.
Definition term139 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Nat.add (Nat.mul x0 (S x1)) (S x1)) = (Nat.add (Nat.mul x0 y0) y0)) = ((S x1) = y0)) (S x2).
Definition term197 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((S y0) = (S y1)) = (y0 = y1)) x0.
Definition term168 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))) x0.
Definition term159 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))) x0.
Definition term22 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) x0.
Definition term201 (x0 : nat) (x1 : nat) := Nat.add x0 (Nat.add (Nat.mul x0 x1) x1).
Definition term14 (x0 : nat) := (fun y0 : nat => ~ ((S y0) = (NUMERAL 0))) x0.
Definition term46 := fun y0 : nat => (forall y1 : nat, forall y2 : nat, ((Nat.mul y0 y1) = (Nat.mul y0 y2)) = ((y0 = (NUMERAL 0)) \/ (y1 = y2))) -> forall y1 : nat, forall y2 : nat, ((Nat.mul (S y0) y1) = (Nat.mul (S y0) y2)) = (((S y0) = (NUMERAL 0)) \/ (y1 = y2)).
Definition term173 := forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0).
Definition term26 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 x1) x1.
Definition term100 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, ((Nat.add (Nat.mul x0 y0) y0) = (Nat.add (Nat.mul x0 y1) y1)) = (y0 = y1)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.add (Nat.mul x0 y1) y1) = (Nat.add (Nat.mul x0 y2) y2)) = (y1 = y2)) y0) -> (fun y1 : nat => forall y2 : nat, ((Nat.add (Nat.mul x0 y1) y1) = (Nat.add (Nat.mul x0 y2) y2)) = (y1 = y2)) (S y0)).
Definition term49 := ((fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.mul y0 y1) = (Nat.mul y0 y2)) = ((y0 = (NUMERAL 0)) \/ (y1 = y2))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Nat.mul y1 y2) = (Nat.mul y1 y3)) = ((y1 = (NUMERAL 0)) \/ (y2 = y3))) y0) -> (fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Nat.mul y1 y2) = (Nat.mul y1 y3)) = ((y1 = (NUMERAL 0)) \/ (y2 = y3))) (S y0)).
Definition term172 (x0 : nat) (x1 : nat) := Nat.add x0 (Nat.mul x0 x1).
Definition term175 (x0 : nat) := Nat.mul x0 (NUMERAL 0).
Definition term179 (x0 : nat) (x1 : nat) := Nat.add (Nat.add x0 (Nat.mul x0 x1)).
Definition term136 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Nat.add (Nat.mul x0 (S x1)) (S x1)) = (Nat.add (Nat.mul x0 y0) y0)) = ((S x1) = y0)) x2.
Definition term186 (x0 : nat) (x1 : nat) := @eq Prop ((Nat.add (Nat.mul x1 (S x0)) (S x0)) = (Nat.add (Nat.mul x1 (NUMERAL 0)) (NUMERAL 0))).
Definition term162 (x0 : nat) (x1 : nat) := Nat.add x0 (S x1).
Definition term143 (x0 : nat) (x1 : nat) := fun y0 : nat => (((Nat.add (Nat.mul x0 (S x1)) (S x1)) = (Nat.add (Nat.mul x0 y0) y0)) = ((S x1) = y0)) -> ((Nat.add (Nat.mul x0 (S x1)) (S x1)) = (Nat.add (Nat.mul x0 (S y0)) (S y0))) = ((S x1) = (S y0)).
Definition term121 (x0 : nat) := fun y0 : nat => (((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 y0) y0)) = ((NUMERAL 0) = y0)) -> ((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 (S y0)) (S y0))) = ((NUMERAL 0) = (S y0)).
Definition term16 (x0 : nat) := (~ ((S x0) = (NUMERAL 0))) -> ((S x0) = (NUMERAL 0)) = False.
Definition term117 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 (S x1)) (S x1).
Definition term155 (x0 : nat) := (~ ((NUMERAL 0) = (S x0))) -> ((NUMERAL 0) = (S x0)) = False.
Definition term200 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Nat.add (Nat.mul x0 x1) x1) = (Nat.add (Nat.mul x0 y0) y0)) = (x1 = y0)) x2.
Definition term193 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Nat.add x0 x1) = (Nat.add x0 y0)) = (x1 = y0)) x2.
Definition term149 (x0 : nat) (x1 : nat) := imp ((((Nat.add (Nat.mul x0 (S x1)) (S x1)) = (Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0))) = ((S x1) = (NUMERAL 0))) /\ (forall y0 : nat, (((Nat.add (Nat.mul x0 (S x1)) (S x1)) = (Nat.add (Nat.mul x0 y0) y0)) = ((S x1) = y0)) -> ((Nat.add (Nat.mul x0 (S x1)) (S x1)) = (Nat.add (Nat.mul x0 (S y0)) (S y0))) = ((S x1) = (S y0)))).
Definition term127 (x0 : nat) := imp ((((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0))) = ((NUMERAL 0) = (NUMERAL 0))) /\ (forall y0 : nat, (((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 y0) y0)) = ((NUMERAL 0) = y0)) -> ((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 (S y0)) (S y0))) = ((NUMERAL 0) = (S y0)))).
Definition term204 (x0 : nat) (x1 : nat) := @eq Prop (x0 = x1).
Definition term68 (x0 : Prop) := forall y0 : nat, x0.
Definition term150 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => ((Nat.add (Nat.mul x0 (S x1)) (S x1)) = (Nat.add (Nat.mul x0 y1) y1)) = ((S x1) = y1)) y0.
Definition term128 (x0 : nat) := fun y0 : nat => (fun y1 : nat => ((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 y1) y1)) = ((NUMERAL 0) = y1)) y0.
Definition term5 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.add (Nat.add x0 x1) y0) = (Nat.add x0 (Nat.add x1 y0)).
Definition term62 (x0 : nat) (x1 : nat) := True \/ (x0 = x1).
Definition term145 (x0 : nat) (x1 : nat) := forall y0 : nat, (((Nat.add (Nat.mul x0 (S x1)) (S x1)) = (Nat.add (Nat.mul x0 y0) y0)) = ((S x1) = y0)) -> ((Nat.add (Nat.mul x0 (S x1)) (S x1)) = (Nat.add (Nat.mul x0 (S y0)) (S y0))) = ((S x1) = (S y0)).
Definition term123 (x0 : nat) := forall y0 : nat, (((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 y0) y0)) = ((NUMERAL 0) = y0)) -> ((Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0)) = (Nat.add (Nat.mul x0 (S y0)) (S y0))) = ((NUMERAL 0) = (S y0)).
Definition term29 (x0 : nat) := Nat.mul (NUMERAL 0) x0.
Definition term140 (x0 : nat) (x1 : nat) (x2 : nat) := ((fun y0 : nat => ((Nat.add (Nat.mul x0 (S x1)) (S x1)) = (Nat.add (Nat.mul x0 y0) y0)) = ((S x1) = y0)) x2) -> (fun y0 : nat => ((Nat.add (Nat.mul x0 (S x1)) (S x1)) = (Nat.add (Nat.mul x0 y0) y0)) = ((S x1) = y0)) (S x2).
Definition term137 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((fun y0 : nat => ((Nat.add (Nat.mul x0 (S x1)) (S x1)) = (Nat.add (Nat.mul x0 y0) y0)) = ((S x1) = y0)) x2).
Definition term3 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.add (Nat.add x0 x1) y0) = (Nat.add x0 (Nat.add x1 y0)).
Definition term187 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((Nat.add (Nat.mul x1 (S x0)) (S x0)) = (Nat.add (Nat.mul x1 (S x2)) (S x2))).
Definition term60 := or ((NUMERAL 0) = (NUMERAL 0)).
Definition term59 (x0 : nat) (x1 : nat) := @eq Prop ((Nat.mul (NUMERAL 0) x0) = (Nat.mul (NUMERAL 0) x1)).
Definition term180 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 (S x1)) x1.
Definition term43 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.mul y0 y1) = (Nat.mul y0 y2)) = ((y0 = (NUMERAL 0)) \/ (y1 = y2))) x0) -> (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.mul y0 y1) = (Nat.mul y0 y2)) = ((y0 = (NUMERAL 0)) \/ (y1 = y2))) (S x0).
Definition term199 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((S x0) = (S y0)) = (x0 = y0)) x1.
Definition term105 (x0 : nat) := forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Nat.add (Nat.mul x0 y1) y1) = (Nat.add (Nat.mul x0 y2) y2)) = (y1 = y2)) y0.
Definition term54 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Nat.mul y1 y2) = (Nat.mul y1 y3)) = ((y1 = (NUMERAL 0)) \/ (y2 = y3))) y0.
Definition term40 (x0 : nat) := imp (forall y0 : nat, forall y1 : nat, ((Nat.mul x0 y0) = (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (y0 = y1))).
Definition term17 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term50 := (forall y0 : nat, forall y1 : nat, ((Nat.mul (NUMERAL 0) y0) = (Nat.mul (NUMERAL 0) y1)) = (((NUMERAL 0) = (NUMERAL 0)) \/ (y0 = y1))) /\ (forall y0 : nat, (forall y1 : nat, forall y2 : nat, ((Nat.mul y0 y1) = (Nat.mul y0 y2)) = ((y0 = (NUMERAL 0)) \/ (y1 = y2))) -> forall y1 : nat, forall y2 : nat, ((Nat.mul (S y0) y1) = (Nat.mul (S y0) y2)) = (((S y0) = (NUMERAL 0)) \/ (y1 = y2))).
Definition term81 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((Nat.mul (S x0) y0) = (Nat.mul (S x0) y1)) = (((S x0) = (NUMERAL 0)) \/ (y0 = y1)).
Definition term69 := fun y0 : nat => forall y1 : nat, ((Nat.mul (NUMERAL 0) y0) = (Nat.mul (NUMERAL 0) y1)) = (((NUMERAL 0) = (NUMERAL 0)) \/ (y0 = y1)).
Definition term7 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.add (Nat.add x0 y0) y1) = (Nat.add x0 (Nat.add y0 y1)).
Definition term75 (x0 : nat) (x1 : nat) (x2 : nat) := ((S x0) = (NUMERAL 0)) \/ (x1 = x2).
Definition term32 := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.mul y0 y1) = (Nat.mul y0 y2)) = ((y0 = (NUMERAL 0)) \/ (y1 = y2)).
Definition term11 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add (Nat.add y0 y1) y2) = (Nat.add y0 (Nat.add y1 y2)).
Definition term10 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2).
Definition term61 (x0 : nat) (x1 : nat) := ((NUMERAL 0) = (NUMERAL 0)) \/ (x0 = x1).
Definition term135 (x0 : nat) (x1 : nat) := and (((Nat.add (Nat.mul x0 (S x1)) (S x1)) = (Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0))) = ((S x1) = (NUMERAL 0))).
Definition term95 (x0 : nat) (x1 : nat) := (forall y0 : nat, ((Nat.add (Nat.mul x0 x1) x1) = (Nat.add (Nat.mul x0 y0) y0)) = (x1 = y0)) -> forall y0 : nat, ((Nat.add (Nat.mul x0 (S x1)) (S x1)) = (Nat.add (Nat.mul x0 y0) y0)) = ((S x1) = y0).
Definition term160 (x0 : nat) := forall y0 : nat, (Nat.add x0 (S y0)) = (S (Nat.add x0 y0)).