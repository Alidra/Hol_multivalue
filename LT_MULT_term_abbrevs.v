Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term77 (x0 : nat) := ((fun y0 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) y0)) = ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0))) x0) -> (fun y0 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) y0)) = ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0))) (S x0).
Definition term20 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul x0 (S y0)) = (Nat.add x0 (Nat.mul x0 y0))) x1.
Definition term1 (x0 : nat) := Peano.lt (NUMERAL 0) (S x0).
Definition term115 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (S x0) y1)) = ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) y1))) y0.
Definition term87 := fun y0 : nat => (fun y1 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) y1)) = ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y1))) y0.
Definition term14 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term32 := forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0).
Definition term97 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (S x0) y0)) = ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) y0))) x1.
Definition term106 (x0 : nat) (x1 : nat) := ((Peano.lt (NUMERAL 0) (Nat.mul (S x0) x1)) = ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) x1))) -> (Peano.lt (NUMERAL 0) (Nat.mul (S x0) (S x1))) = ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) (S x1))).
Definition term78 (x0 : nat) := ((Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) x0)) = ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) x0))) -> (Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) (S x0))) = ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (S x0))).
Definition term53 := forall y0 : nat, (forall y1 : nat, (Peano.lt (NUMERAL 0) (Nat.mul y0 y1)) = ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt (NUMERAL 0) y1))) -> forall y1 : nat, (Peano.lt (NUMERAL 0) (Nat.mul (S y0) y1)) = ((Peano.lt (NUMERAL 0) (S y0)) /\ (Peano.lt (NUMERAL 0) y1)).
Definition term19 (x0 : nat) := forall y0 : nat, (Nat.mul x0 (S y0)) = (Nat.add x0 (Nat.mul x0 y0)).
Definition term16 := (forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))).
Definition term3 := (forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))).
Definition term74 (x0 : nat) := (fun y0 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) y0)) = ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0))) (S x0).
Definition term98 (x0 : nat) (x1 : nat) := Peano.lt (NUMERAL 0) (Nat.mul (S x0) x1).
Definition term91 (x0 : nat) := fun y0 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (S x0) y0)) = ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) y0)).
Definition term63 := fun y0 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) y0)) = ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0)).
Definition term26 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul (S x0) y0) = (Nat.add (Nat.mul x0 y0) y0)) x1.
Definition term33 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) x0.
Definition term61 := ((forall y0 : nat, (Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) y0)) = ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0))) /\ (forall y0 : nat, (forall y1 : nat, (Peano.lt (NUMERAL 0) (Nat.mul y0 y1)) = ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt (NUMERAL 0) y1))) -> forall y1 : nat, (Peano.lt (NUMERAL 0) (Nat.mul (S y0) y1)) = ((Peano.lt (NUMERAL 0) (S y0)) /\ (Peano.lt (NUMERAL 0) y1)))) -> forall y0 : nat, forall y1 : nat, (Peano.lt (NUMERAL 0) (Nat.mul y0 y1)) = ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt (NUMERAL 0) y1)).
Definition term116 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (S x0) y1)) = ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) y1))) y0.
Definition term88 := forall y0 : nat, (fun y1 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) y1)) = ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y1))) y0.
Definition term111 (x0 : nat) := ((fun y0 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (S x0) y0)) = ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) y0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (S x0) y1)) = ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) y1))) y0) -> (fun y1 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (S x0) y1)) = ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) y1))) (S y0)).
Definition term83 := ((fun y0 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) y0)) = ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) y1)) = ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y1))) y0) -> (fun y1 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) y1)) = ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y1))) (S y0)).
Definition term44 (x0 : nat) := imp ((fun y0 : nat => forall y1 : nat, (Peano.lt (NUMERAL 0) (Nat.mul y0 y1)) = ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt (NUMERAL 0) y1))) x0).
Definition term11 (x0 : nat) := (fun y0 : nat => (Nat.add y0 (NUMERAL 0)) = y0) x0.
Definition term69 (x0 : nat) := (fun y0 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) y0)) = ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0))) x0.
Definition term105 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (S x0) y0)) = ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) y0))) x1) -> (fun y0 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (S x0) y0)) = ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) y0))) (S x1).
Definition term90 (x0 : nat) := (((fun y0 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (S x0) y0)) = ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) y0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (S x0) y1)) = ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) y1))) y0) -> (fun y1 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (S x0) y1)) = ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) y1))) (S y0))) -> forall y0 : nat, (fun y1 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (S x0) y1)) = ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) y1))) y0.
Definition term62 := (((fun y0 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) y0)) = ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) y1)) = ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y1))) y0) -> (fun y1 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) y1)) = ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y1))) (S y0))) -> forall y0 : nat, (fun y1 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) y1)) = ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y1))) y0.
Definition term36 := (((fun y0 : nat => forall y1 : nat, (Peano.lt (NUMERAL 0) (Nat.mul y0 y1)) = ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt (NUMERAL 0) y1))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Peano.lt (NUMERAL 0) (Nat.mul y1 y2)) = ((Peano.lt (NUMERAL 0) y1) /\ (Peano.lt (NUMERAL 0) y2))) y0) -> (fun y1 : nat => forall y2 : nat, (Peano.lt (NUMERAL 0) (Nat.mul y1 y2)) = ((Peano.lt (NUMERAL 0) y1) /\ (Peano.lt (NUMERAL 0) y2))) (S y0))) -> forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.lt (NUMERAL 0) (Nat.mul y1 y2)) = ((Peano.lt (NUMERAL 0) y1) /\ (Peano.lt (NUMERAL 0) y2))) y0.
Definition term71 (x0 : nat) := (Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) x0).
Definition term35 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term113 (x0 : nat) := imp (((fun y0 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (S x0) y0)) = ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) y0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (S x0) y1)) = ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) y1))) y0) -> (fun y1 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (S x0) y1)) = ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) y1))) (S y0))).
Definition term85 := imp (((fun y0 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) y0)) = ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) y1)) = ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y1))) y0) -> (fun y1 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) y1)) = ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y1))) (S y0))).
Definition term56 := imp (((fun y0 : nat => forall y1 : nat, (Peano.lt (NUMERAL 0) (Nat.mul y0 y1)) = ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt (NUMERAL 0) y1))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Peano.lt (NUMERAL 0) (Nat.mul y1 y2)) = ((Peano.lt (NUMERAL 0) y1) /\ (Peano.lt (NUMERAL 0) y2))) y0) -> (fun y1 : nat => forall y2 : nat, (Peano.lt (NUMERAL 0) (Nat.mul y1 y2)) = ((Peano.lt (NUMERAL 0) y1) /\ (Peano.lt (NUMERAL 0) y2))) (S y0))).
Definition term75 (x0 : nat) := Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) (S x0)).
Definition term12 (x0 : nat) := Nat.add x0 (NUMERAL 0).
Definition term27 (x0 : nat) (x1 : nat) := Nat.mul (S x0) x1.
Definition term109 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (S x0) y1)) = ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) y1))) y0) -> (fun y1 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (S x0) y1)) = ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) y1))) (S y0).
Definition term81 := forall y0 : nat, ((fun y1 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) y1)) = ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y1))) y0) -> (fun y1 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) y1)) = ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y1))) (S y0).
Definition term52 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Peano.lt (NUMERAL 0) (Nat.mul y1 y2)) = ((Peano.lt (NUMERAL 0) y1) /\ (Peano.lt (NUMERAL 0) y2))) y0) -> (fun y1 : nat => forall y2 : nat, (Peano.lt (NUMERAL 0) (Nat.mul y1 y2)) = ((Peano.lt (NUMERAL 0) y1) /\ (Peano.lt (NUMERAL 0) y2))) (S y0).
Definition term21 (x0 : nat) (x1 : nat) := Nat.mul x0 (S x1).
Definition term123 (x0 : nat) := Nat.mul (NUMERAL 0) (S x0).
Definition term10 := forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0.
Definition term128 (x0 : nat) := Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0).
Definition term141 (x0 : nat) (x1 : nat) := @eq Prop (Peano.lt (NUMERAL 0) (Nat.mul (S x0) (S x1))).
Definition term124 (x0 : nat) := @eq Prop (Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) (S x0))).
Definition term95 (x0 : nat) := and ((fun y0 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (S x0) y0)) = ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) y0))) (NUMERAL 0)).
Definition term67 := and ((fun y0 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) y0)) = ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0))) (NUMERAL 0)).
Definition term30 (x0 : nat) := (fun y0 : nat => (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) x0.
Definition term40 := and ((fun y0 : nat => forall y1 : nat, (Peano.lt (NUMERAL 0) (Nat.mul y0 y1)) = ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt (NUMERAL 0) y1))) (NUMERAL 0)).
Definition term45 (x0 : nat) := imp (forall y0 : nat, (Peano.lt (NUMERAL 0) (Nat.mul x0 y0)) = ((Peano.lt (NUMERAL 0) x0) /\ (Peano.lt (NUMERAL 0) y0))).
Definition term41 := and (forall y0 : nat, (Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) y0)) = ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0))).
Definition term46 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt (NUMERAL 0) (Nat.mul y0 y1)) = ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt (NUMERAL 0) y1))) (S x0).
Definition term120 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term38 := (fun y0 : nat => forall y1 : nat, (Peano.lt (NUMERAL 0) (Nat.mul y0 y1)) = ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt (NUMERAL 0) y1))) (NUMERAL 0).
Definition term107 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (S x0) y1)) = ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) y1))) y0) -> (fun y1 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (S x0) y1)) = ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) y1))) (S y0).
Definition term79 := fun y0 : nat => ((fun y1 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) y1)) = ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y1))) y0) -> (fun y1 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) y1)) = ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y1))) (S y0).
Definition term122 := @eq Prop (Peano.lt (NUMERAL 0) (NUMERAL 0)).
Definition term57 := imp ((forall y0 : nat, (Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) y0)) = ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0))) /\ (forall y0 : nat, (forall y1 : nat, (Peano.lt (NUMERAL 0) (Nat.mul y0 y1)) = ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt (NUMERAL 0) y1))) -> forall y1 : nat, (Peano.lt (NUMERAL 0) (Nat.mul (S y0) y1)) = ((Peano.lt (NUMERAL 0) (S y0)) /\ (Peano.lt (NUMERAL 0) y1)))).
Definition term139 (x0 : nat) (x1 : nat) := S (Nat.add (Nat.add x0 (Nat.mul x0 x1)) x1).
Definition term134 (x0 : nat) (x1 : nat) := S (Nat.add (Nat.mul x0 (S x1)) x1).
Definition term9 (x0 : nat) (x1 : nat) := S (Nat.add x0 x1).
Definition term60 := forall y0 : nat, forall y1 : nat, (Peano.lt (NUMERAL 0) (Nat.mul y0 y1)) = ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt (NUMERAL 0) y1)).
Definition term23 := forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1).
Definition term17 := forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)).
Definition term4 := forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)).
Definition term119 := Peano.lt (NUMERAL 0).
Definition term117 (x0 : nat) := (((Peano.lt (NUMERAL 0) (Nat.mul (S x0) (NUMERAL 0))) = ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) (NUMERAL 0)))) /\ (forall y0 : nat, ((Peano.lt (NUMERAL 0) (Nat.mul (S x0) y0)) = ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) y0))) -> (Peano.lt (NUMERAL 0) (Nat.mul (S x0) (S y0))) = ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) (S y0))))) -> forall y0 : nat, (Peano.lt (NUMERAL 0) (Nat.mul (S x0) y0)) = ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) y0)).
Definition term89 := (((Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) (NUMERAL 0))) = ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (NUMERAL 0)))) /\ (forall y0 : nat, ((Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) y0)) = ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0))) -> (Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) (S y0))) = ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (S y0))))) -> forall y0 : nat, (Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) y0)) = ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0)).
Definition term100 (x0 : nat) (x1 : nat) := imp ((fun y0 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (S x0) y0)) = ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) y0))) x1).
Definition term99 (x0 : nat) (x1 : nat) := (Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) x1).
Definition term25 (x0 : nat) := forall y0 : nat, (Nat.mul (S x0) y0) = (Nat.add (Nat.mul x0 y0) y0).
Definition term47 (x0 : nat) := forall y0 : nat, (Peano.lt (NUMERAL 0) (Nat.mul (S x0) y0)) = ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) y0)).
Definition term43 (x0 : nat) := forall y0 : nat, (Peano.lt (NUMERAL 0) (Nat.mul x0 y0)) = ((Peano.lt (NUMERAL 0) x0) /\ (Peano.lt (NUMERAL 0) y0)).
Definition term39 := forall y0 : nat, (Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) y0)) = ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0)).
Definition term94 (x0 : nat) := (Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) (NUMERAL 0)).
Definition term96 (x0 : nat) := and ((Peano.lt (NUMERAL 0) (Nat.mul (S x0) (NUMERAL 0))) = ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) (NUMERAL 0)))).
Definition term68 := and ((Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) (NUMERAL 0))) = ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (NUMERAL 0)))).
Definition term7 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 (S y0)) = (S (Nat.add x0 y0))) x1.
Definition term51 := fun y0 : nat => (forall y1 : nat, (Peano.lt (NUMERAL 0) (Nat.mul y0 y1)) = ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt (NUMERAL 0) y1))) -> forall y1 : nat, (Peano.lt (NUMERAL 0) (Nat.mul (S y0) y1)) = ((Peano.lt (NUMERAL 0) (S y0)) /\ (Peano.lt (NUMERAL 0) y1)).
Definition term50 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, (Peano.lt (NUMERAL 0) (Nat.mul y1 y2)) = ((Peano.lt (NUMERAL 0) y1) /\ (Peano.lt (NUMERAL 0) y2))) y0) -> (fun y1 : nat => forall y2 : nat, (Peano.lt (NUMERAL 0) (Nat.mul y1 y2)) = ((Peano.lt (NUMERAL 0) y1) /\ (Peano.lt (NUMERAL 0) y2))) (S y0).
Definition term135 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 (S x1)).
Definition term15 := (forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))).
Definition term2 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term55 := (forall y0 : nat, (Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) y0)) = ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0))) /\ (forall y0 : nat, (forall y1 : nat, (Peano.lt (NUMERAL 0) (Nat.mul y0 y1)) = ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt (NUMERAL 0) y1))) -> forall y1 : nat, (Peano.lt (NUMERAL 0) (Nat.mul (S y0) y1)) = ((Peano.lt (NUMERAL 0) (S y0)) /\ (Peano.lt (NUMERAL 0) y1))).
Definition term103 (x0 : nat) (x1 : nat) := Peano.lt (NUMERAL 0) (Nat.mul (S x0) (S x1)).
Definition term138 (x0 : nat) (x1 : nat) := Nat.add (Nat.add x0 (Nat.mul x0 x1)) x1.
Definition term126 := (Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ True.
Definition term58 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (Peano.lt (NUMERAL 0) (Nat.mul y1 y2)) = ((Peano.lt (NUMERAL 0) y1) /\ (Peano.lt (NUMERAL 0) y2))) y0.
Definition term42 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt (NUMERAL 0) (Nat.mul y0 y1)) = ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt (NUMERAL 0) y1))) x0.
Definition term24 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) x0.
Definition term18 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))) x0.
Definition term5 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))) x0.
Definition term93 (x0 : nat) := Peano.lt (NUMERAL 0) (Nat.mul (S x0) (NUMERAL 0)).
Definition term29 := forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0).
Definition term131 := True /\ (Peano.lt (NUMERAL 0) (NUMERAL 0)).
Definition term28 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 x1) x1.
Definition term54 := ((fun y0 : nat => forall y1 : nat, (Peano.lt (NUMERAL 0) (Nat.mul y0 y1)) = ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt (NUMERAL 0) y1))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Peano.lt (NUMERAL 0) (Nat.mul y1 y2)) = ((Peano.lt (NUMERAL 0) y1) /\ (Peano.lt (NUMERAL 0) y2))) y0) -> (fun y1 : nat => forall y2 : nat, (Peano.lt (NUMERAL 0) (Nat.mul y1 y2)) = ((Peano.lt (NUMERAL 0) y1) /\ (Peano.lt (NUMERAL 0) y2))) (S y0)).
Definition term66 := (Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (NUMERAL 0)).
Definition term22 (x0 : nat) (x1 : nat) := Nat.add x0 (Nat.mul x0 x1).
Definition term31 (x0 : nat) := Nat.mul x0 (NUMERAL 0).
Definition term136 (x0 : nat) (x1 : nat) := Nat.add (Nat.add x0 (Nat.mul x0 x1)).
Definition term8 (x0 : nat) (x1 : nat) := Nat.add x0 (S x1).
Definition term130 (x0 : nat) := and (Peano.lt (NUMERAL 0) (S x0)).
Definition term73 (x0 : nat) := imp ((Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) x0)) = ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) x0))).
Definition term133 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 (S x1)) (S x1).
Definition term70 (x0 : nat) := Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) x0).
Definition term108 (x0 : nat) := fun y0 : nat => ((Peano.lt (NUMERAL 0) (Nat.mul (S x0) y0)) = ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) y0))) -> (Peano.lt (NUMERAL 0) (Nat.mul (S x0) (S y0))) = ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) (S y0))).
Definition term80 := fun y0 : nat => ((Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) y0)) = ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0))) -> (Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) (S y0))) = ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (S y0))).
Definition term114 (x0 : nat) := imp (((Peano.lt (NUMERAL 0) (Nat.mul (S x0) (NUMERAL 0))) = ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) (NUMERAL 0)))) /\ (forall y0 : nat, ((Peano.lt (NUMERAL 0) (Nat.mul (S x0) y0)) = ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) y0))) -> (Peano.lt (NUMERAL 0) (Nat.mul (S x0) (S y0))) = ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) (S y0))))).
Definition term86 := imp (((Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) (NUMERAL 0))) = ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (NUMERAL 0)))) /\ (forall y0 : nat, ((Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) y0)) = ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0))) -> (Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) (S y0))) = ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (S y0))))).
Definition term104 (x0 : nat) (x1 : nat) := (Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) (S x1)).
Definition term125 := and (Peano.lt (NUMERAL 0) (NUMERAL 0)).
Definition term112 (x0 : nat) := ((Peano.lt (NUMERAL 0) (Nat.mul (S x0) (NUMERAL 0))) = ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) (NUMERAL 0)))) /\ (forall y0 : nat, ((Peano.lt (NUMERAL 0) (Nat.mul (S x0) y0)) = ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) y0))) -> (Peano.lt (NUMERAL 0) (Nat.mul (S x0) (S y0))) = ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) (S y0)))).
Definition term84 := ((Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) (NUMERAL 0))) = ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (NUMERAL 0)))) /\ (forall y0 : nat, ((Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) y0)) = ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0))) -> (Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) (S y0))) = ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (S y0)))).
Definition term127 (x0 : nat) := Nat.mul (S x0) (NUMERAL 0).
Definition term129 (x0 : nat) := @eq Prop (Peano.lt (NUMERAL 0) (Nat.mul (S x0) (NUMERAL 0))).
Definition term121 := @eq Prop (Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) (NUMERAL 0))).
Definition term118 := Nat.mul (NUMERAL 0) (NUMERAL 0).
Definition term110 (x0 : nat) := forall y0 : nat, ((Peano.lt (NUMERAL 0) (Nat.mul (S x0) y0)) = ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) y0))) -> (Peano.lt (NUMERAL 0) (Nat.mul (S x0) (S y0))) = ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) (S y0))).
Definition term82 := forall y0 : nat, ((Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) y0)) = ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0))) -> (Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) (S y0))) = ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (S y0))).
Definition term34 (x0 : nat) := Nat.mul (NUMERAL 0) x0.
Definition term76 (x0 : nat) := (Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (S x0)).
Definition term92 (x0 : nat) := (fun y0 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (S x0) y0)) = ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) y0))) (NUMERAL 0).
Definition term64 := (fun y0 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) y0)) = ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0))) (NUMERAL 0).
Definition term72 (x0 : nat) := imp ((fun y0 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) y0)) = ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0))) x0).
Definition term140 (x0 : nat) (x1 : nat) := Peano.lt (NUMERAL 0) (S (Nat.add (Nat.add x0 (Nat.mul x0 x1)) x1)).
Definition term65 := Peano.lt (NUMERAL 0) (Nat.mul (NUMERAL 0) (NUMERAL 0)).
Definition term137 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 (S x1)) x1.
Definition term48 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, (Peano.lt (NUMERAL 0) (Nat.mul y0 y1)) = ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt (NUMERAL 0) y1))) x0) -> (fun y0 : nat => forall y1 : nat, (Peano.lt (NUMERAL 0) (Nat.mul y0 y1)) = ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt (NUMERAL 0) y1))) (S x0).
Definition term59 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.lt (NUMERAL 0) (Nat.mul y1 y2)) = ((Peano.lt (NUMERAL 0) y1) /\ (Peano.lt (NUMERAL 0) y2))) y0.
Definition term13 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term102 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt (NUMERAL 0) (Nat.mul (S x0) y0)) = ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) y0))) (S x1).
Definition term101 (x0 : nat) (x1 : nat) := imp ((Peano.lt (NUMERAL 0) (Nat.mul (S x0) x1)) = ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) x1))).
Definition term37 := fun y0 : nat => forall y1 : nat, (Peano.lt (NUMERAL 0) (Nat.mul y0 y1)) = ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt (NUMERAL 0) y1)).
Definition term132 (x0 : nat) (x1 : nat) := Nat.mul (S x0) (S x1).
Definition term49 (x0 : nat) := (forall y0 : nat, (Peano.lt (NUMERAL 0) (Nat.mul x0 y0)) = ((Peano.lt (NUMERAL 0) x0) /\ (Peano.lt (NUMERAL 0) y0))) -> forall y0 : nat, (Peano.lt (NUMERAL 0) (Nat.mul (S x0) y0)) = ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) y0)).
Definition term0 (x0 : nat) := (fun y0 : nat => Peano.lt (NUMERAL 0) (S y0)) x0.
Definition term6 (x0 : nat) := forall y0 : nat, (Nat.add x0 (S y0)) = (S (Nat.add x0 y0)).
