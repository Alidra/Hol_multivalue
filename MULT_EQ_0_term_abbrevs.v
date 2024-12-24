Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term77 (x0 : nat) := ((fun y0 : nat => ((Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))) x0) -> (fun y0 : nat => ((Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))) (S x0).
Definition term100 (x0 : nat) (x1 : nat) := imp (((Nat.mul (S x0) x1) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) \/ (x1 = (NUMERAL 0)))).
Definition term73 (x0 : nat) := imp (((Nat.mul (NUMERAL 0) x0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ (x0 = (NUMERAL 0)))).
Definition term21 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul x0 (S y0)) = (Nat.add x0 (Nat.mul x0 y0))) x1.
Definition term114 (x0 : nat) := fun y0 : nat => (fun y1 : nat => ((Nat.mul (S x0) y1) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) y0.
Definition term87 := fun y0 : nat => (fun y1 : nat => ((Nat.mul (NUMERAL 0) y1) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) y0.
Definition term118 := @eq nat (NUMERAL 0).
Definition term15 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term33 := forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0).
Definition term94 (x0 : nat) := ((S x0) = (NUMERAL 0)) \/ ((NUMERAL 0) = (NUMERAL 0)).
Definition term124 (x0 : nat) := @eq nat (Nat.mul (S x0) (NUMERAL 0)).
Definition term54 := forall y0 : nat, (forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) -> forall y1 : nat, ((Nat.mul (S y0) y1) = (NUMERAL 0)) = (((S y0) = (NUMERAL 0)) \/ (y1 = (NUMERAL 0))).
Definition term20 (x0 : nat) := forall y0 : nat, (Nat.mul x0 (S y0)) = (Nat.add x0 (Nat.mul x0 y0)).
Definition term17 := (forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))).
Definition term4 := (forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))).
Definition term27 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul (S x0) y0) = (Nat.add (Nat.mul x0 y0) y0)) x1.
Definition term34 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) x0.
Definition term62 := ((forall y0 : nat, ((Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))) /\ (forall y0 : nat, (forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) -> forall y1 : nat, ((Nat.mul (S y0) y1) = (NUMERAL 0)) = (((S y0) = (NUMERAL 0)) \/ (y1 = (NUMERAL 0))))) -> forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0))).
Definition term115 (x0 : nat) := forall y0 : nat, (fun y1 : nat => ((Nat.mul (S x0) y1) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) y0.
Definition term88 := forall y0 : nat, (fun y1 : nat => ((Nat.mul (NUMERAL 0) y1) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) y0.
Definition term98 (x0 : nat) (x1 : nat) := ((S x0) = (NUMERAL 0)) \/ (x1 = (NUMERAL 0)).
Definition term110 (x0 : nat) := ((fun y0 : nat => ((Nat.mul (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Nat.mul (S x0) y1) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) y0) -> (fun y1 : nat => ((Nat.mul (S x0) y1) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) (S y0)).
Definition term83 := ((fun y0 : nat => ((Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Nat.mul (NUMERAL 0) y1) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) y0) -> (fun y1 : nat => ((Nat.mul (NUMERAL 0) y1) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) (S y0)).
Definition term45 (x0 : nat) := imp ((fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) x0).
Definition term101 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.mul (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))) (S x1).
Definition term12 (x0 : nat) := (fun y0 : nat => (Nat.add y0 (NUMERAL 0)) = y0) x0.
Definition term104 (x0 : nat) (x1 : nat) := ((fun y0 : nat => ((Nat.mul (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))) x1) -> (fun y0 : nat => ((Nat.mul (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))) (S x1).
Definition term90 (x0 : nat) := (((fun y0 : nat => ((Nat.mul (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Nat.mul (S x0) y1) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) y0) -> (fun y1 : nat => ((Nat.mul (S x0) y1) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) (S y0))) -> forall y0 : nat, (fun y1 : nat => ((Nat.mul (S x0) y1) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) y0.
Definition term63 := (((fun y0 : nat => ((Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Nat.mul (NUMERAL 0) y1) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) y0) -> (fun y1 : nat => ((Nat.mul (NUMERAL 0) y1) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) (S y0))) -> forall y0 : nat, (fun y1 : nat => ((Nat.mul (NUMERAL 0) y1) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) y0.
Definition term37 := (((fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = (NUMERAL 0)) = ((y1 = (NUMERAL 0)) \/ (y2 = (NUMERAL 0)))) y0) -> (fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = (NUMERAL 0)) = ((y1 = (NUMERAL 0)) \/ (y2 = (NUMERAL 0)))) (S y0))) -> forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = (NUMERAL 0)) = ((y1 = (NUMERAL 0)) \/ (y2 = (NUMERAL 0)))) y0.
Definition term36 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term112 (x0 : nat) := imp (((fun y0 : nat => ((Nat.mul (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Nat.mul (S x0) y1) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) y0) -> (fun y1 : nat => ((Nat.mul (S x0) y1) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) (S y0))).
Definition term85 := imp (((fun y0 : nat => ((Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Nat.mul (NUMERAL 0) y1) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) y0) -> (fun y1 : nat => ((Nat.mul (NUMERAL 0) y1) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) (S y0))).
Definition term57 := imp (((fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = (NUMERAL 0)) = ((y1 = (NUMERAL 0)) \/ (y2 = (NUMERAL 0)))) y0) -> (fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = (NUMERAL 0)) = ((y1 = (NUMERAL 0)) \/ (y2 = (NUMERAL 0)))) (S y0))).
Definition term13 (x0 : nat) := Nat.add x0 (NUMERAL 0).
Definition term107 (x0 : nat) := fun y0 : nat => (((Nat.mul (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))) -> ((Nat.mul (S x0) (S y0)) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) \/ ((S y0) = (NUMERAL 0))).
Definition term80 := fun y0 : nat => (((Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))) -> ((Nat.mul (NUMERAL 0) (S y0)) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ ((S y0) = (NUMERAL 0))).
Definition term105 (x0 : nat) (x1 : nat) := (((Nat.mul (S x0) x1) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) \/ (x1 = (NUMERAL 0)))) -> ((Nat.mul (S x0) (S x1)) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) \/ ((S x1) = (NUMERAL 0))).
Definition term78 (x0 : nat) := (((Nat.mul (NUMERAL 0) x0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ (x0 = (NUMERAL 0)))) -> ((Nat.mul (NUMERAL 0) (S x0)) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ ((S x0) = (NUMERAL 0))).
Definition term48 (x0 : nat) := forall y0 : nat, ((Nat.mul (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) \/ (y0 = (NUMERAL 0))).
Definition term44 (x0 : nat) := forall y0 : nat, ((Nat.mul x0 y0) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) \/ (y0 = (NUMERAL 0))).
Definition term40 := forall y0 : nat, ((Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ (y0 = (NUMERAL 0))).
Definition term28 (x0 : nat) (x1 : nat) := Nat.mul (S x0) x1.
Definition term108 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => ((Nat.mul (S x0) y1) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) y0) -> (fun y1 : nat => ((Nat.mul (S x0) y1) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) (S y0).
Definition term81 := forall y0 : nat, ((fun y1 : nat => ((Nat.mul (NUMERAL 0) y1) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) y0) -> (fun y1 : nat => ((Nat.mul (NUMERAL 0) y1) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) (S y0).
Definition term53 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = (NUMERAL 0)) = ((y1 = (NUMERAL 0)) \/ (y2 = (NUMERAL 0)))) y0) -> (fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = (NUMERAL 0)) = ((y1 = (NUMERAL 0)) \/ (y2 = (NUMERAL 0)))) (S y0).
Definition term97 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.mul (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))) x1.
Definition term22 (x0 : nat) (x1 : nat) := Nat.mul x0 (S x1).
Definition term75 (x0 : nat) := Nat.mul (NUMERAL 0) (S x0).
Definition term11 := forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0.
Definition term123 (x0 : nat) := Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0).
Definition term95 (x0 : nat) := and ((fun y0 : nat => ((Nat.mul (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))) (NUMERAL 0)).
Definition term68 := and ((fun y0 : nat => ((Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))) (NUMERAL 0)).
Definition term31 (x0 : nat) := (fun y0 : nat => (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) x0.
Definition term41 := and ((fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) (NUMERAL 0)).
Definition term46 (x0 : nat) := imp (forall y0 : nat, ((Nat.mul x0 y0) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))).
Definition term42 := and (forall y0 : nat, ((Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))).
Definition term47 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) (S x0).
Definition term39 := (fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) (NUMERAL 0).
Definition term106 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => ((Nat.mul (S x0) y1) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) y0) -> (fun y1 : nat => ((Nat.mul (S x0) y1) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) (S y0).
Definition term79 := fun y0 : nat => ((fun y1 : nat => ((Nat.mul (NUMERAL 0) y1) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) y0) -> (fun y1 : nat => ((Nat.mul (NUMERAL 0) y1) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) (S y0).
Definition term117 := @eq nat (Nat.mul (NUMERAL 0) (NUMERAL 0)).
Definition term58 := imp ((forall y0 : nat, ((Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))) /\ (forall y0 : nat, (forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) -> forall y1 : nat, ((Nat.mul (S y0) y1) = (NUMERAL 0)) = (((S y0) = (NUMERAL 0)) \/ (y1 = (NUMERAL 0))))).
Definition term133 (x0 : nat) (x1 : nat) := S (Nat.add (Nat.add x0 (Nat.mul x0 x1)) x1).
Definition term128 (x0 : nat) (x1 : nat) := S (Nat.add (Nat.mul x0 (S x1)) x1).
Definition term10 (x0 : nat) (x1 : nat) := S (Nat.add x0 x1).
Definition term74 (x0 : nat) := (fun y0 : nat => ((Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))) (S x0).
Definition term61 := forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0))).
Definition term24 := forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1).
Definition term18 := forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)).
Definition term5 := forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)).
Definition term116 (x0 : nat) := ((((Nat.mul (S x0) (NUMERAL 0)) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) \/ ((NUMERAL 0) = (NUMERAL 0)))) /\ (forall y0 : nat, (((Nat.mul (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))) -> ((Nat.mul (S x0) (S y0)) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) \/ ((S y0) = (NUMERAL 0))))) -> forall y0 : nat, ((Nat.mul (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) \/ (y0 = (NUMERAL 0))).
Definition term89 := ((((Nat.mul (NUMERAL 0) (NUMERAL 0)) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ ((NUMERAL 0) = (NUMERAL 0)))) /\ (forall y0 : nat, (((Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))) -> ((Nat.mul (NUMERAL 0) (S y0)) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ ((S y0) = (NUMERAL 0))))) -> forall y0 : nat, ((Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ (y0 = (NUMERAL 0))).
Definition term96 (x0 : nat) := and (((Nat.mul (S x0) (NUMERAL 0)) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) \/ ((NUMERAL 0) = (NUMERAL 0)))).
Definition term69 := and (((Nat.mul (NUMERAL 0) (NUMERAL 0)) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ ((NUMERAL 0) = (NUMERAL 0)))).
Definition term99 (x0 : nat) (x1 : nat) := imp ((fun y0 : nat => ((Nat.mul (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))) x1).
Definition term70 (x0 : nat) := (fun y0 : nat => ((Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))) x0.
Definition term26 (x0 : nat) := forall y0 : nat, (Nat.mul (S x0) y0) = (Nat.add (Nat.mul x0 y0) y0).
Definition term103 (x0 : nat) (x1 : nat) := ((S x0) = (NUMERAL 0)) \/ ((S x1) = (NUMERAL 0)).
Definition term71 (x0 : nat) := ((NUMERAL 0) = (NUMERAL 0)) \/ (x0 = (NUMERAL 0)).
Definition term1 (x0 : nat) := ~ ((S x0) = (NUMERAL 0)).
Definition term120 (x0 : nat) := @eq nat (Nat.mul (NUMERAL 0) (S x0)).
Definition term8 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 (S y0)) = (S (Nat.add x0 y0))) x1.
Definition term52 := fun y0 : nat => (forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) -> forall y1 : nat, ((Nat.mul (S y0) y1) = (NUMERAL 0)) = (((S y0) = (NUMERAL 0)) \/ (y1 = (NUMERAL 0))).
Definition term51 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = (NUMERAL 0)) = ((y1 = (NUMERAL 0)) \/ (y2 = (NUMERAL 0)))) y0) -> (fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = (NUMERAL 0)) = ((y1 = (NUMERAL 0)) \/ (y2 = (NUMERAL 0)))) (S y0).
Definition term129 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 (S x1)).
Definition term16 := (forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))).
Definition term3 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term135 (x0 : nat) (x1 : nat) := @eq nat (S (Nat.add (Nat.add x0 (Nat.mul x0 x1)) x1)).
Definition term56 := (forall y0 : nat, ((Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))) /\ (forall y0 : nat, (forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) -> forall y1 : nat, ((Nat.mul (S y0) y1) = (NUMERAL 0)) = (((S y0) = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))).
Definition term136 (x0 : nat) (x1 : nat) := @eq Prop ((Nat.mul (S x0) (S x1)) = (NUMERAL 0)).
Definition term121 (x0 : nat) := @eq Prop ((Nat.mul (NUMERAL 0) (S x0)) = (NUMERAL 0)).
Definition term132 (x0 : nat) (x1 : nat) := Nat.add (Nat.add x0 (Nat.mul x0 x1)) x1.
Definition term126 (x0 : nat) := or ((S x0) = (NUMERAL 0)).
Definition term59 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = (NUMERAL 0)) = ((y1 = (NUMERAL 0)) \/ (y2 = (NUMERAL 0)))) y0.
Definition term43 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) x0.
Definition term25 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) x0.
Definition term19 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))) x0.
Definition term6 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => ~ ((S y0) = (NUMERAL 0))) x0.
Definition term91 (x0 : nat) := fun y0 : nat => ((Nat.mul (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) \/ (y0 = (NUMERAL 0))).
Definition term64 := fun y0 : nat => ((Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ (y0 = (NUMERAL 0))).
Definition term30 := forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0).
Definition term29 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 x1) x1.
Definition term55 := ((fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = (NUMERAL 0)) = ((y1 = (NUMERAL 0)) \/ (y2 = (NUMERAL 0)))) y0) -> (fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = (NUMERAL 0)) = ((y1 = (NUMERAL 0)) \/ (y2 = (NUMERAL 0)))) (S y0)).
Definition term23 (x0 : nat) (x1 : nat) := Nat.add x0 (Nat.mul x0 x1).
Definition term32 (x0 : nat) := Nat.mul x0 (NUMERAL 0).
Definition term130 (x0 : nat) (x1 : nat) := Nat.add (Nat.add x0 (Nat.mul x0 x1)).
Definition term9 (x0 : nat) (x1 : nat) := Nat.add x0 (S x1).
Definition term2 (x0 : nat) := (~ ((S x0) = (NUMERAL 0))) -> ((S x0) = (NUMERAL 0)) = False.
Definition term127 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 (S x1)) (S x1).
Definition term113 (x0 : nat) := imp ((((Nat.mul (S x0) (NUMERAL 0)) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) \/ ((NUMERAL 0) = (NUMERAL 0)))) /\ (forall y0 : nat, (((Nat.mul (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))) -> ((Nat.mul (S x0) (S y0)) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) \/ ((S y0) = (NUMERAL 0))))).
Definition term86 := imp ((((Nat.mul (NUMERAL 0) (NUMERAL 0)) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ ((NUMERAL 0) = (NUMERAL 0)))) /\ (forall y0 : nat, (((Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))) -> ((Nat.mul (NUMERAL 0) (S y0)) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ ((S y0) = (NUMERAL 0))))).
Definition term111 (x0 : nat) := (((Nat.mul (S x0) (NUMERAL 0)) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) \/ ((NUMERAL 0) = (NUMERAL 0)))) /\ (forall y0 : nat, (((Nat.mul (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))) -> ((Nat.mul (S x0) (S y0)) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) \/ ((S y0) = (NUMERAL 0)))).
Definition term84 := (((Nat.mul (NUMERAL 0) (NUMERAL 0)) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ ((NUMERAL 0) = (NUMERAL 0)))) /\ (forall y0 : nat, (((Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))) -> ((Nat.mul (NUMERAL 0) (S y0)) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ ((S y0) = (NUMERAL 0)))).
Definition term93 (x0 : nat) := Nat.mul (S x0) (NUMERAL 0).
Definition term66 := Nat.mul (NUMERAL 0) (NUMERAL 0).
Definition term109 (x0 : nat) := forall y0 : nat, (((Nat.mul (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))) -> ((Nat.mul (S x0) (S y0)) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) \/ ((S y0) = (NUMERAL 0))).
Definition term82 := forall y0 : nat, (((Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))) -> ((Nat.mul (NUMERAL 0) (S y0)) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ ((S y0) = (NUMERAL 0))).
Definition term35 (x0 : nat) := Nat.mul (NUMERAL 0) x0.
Definition term92 (x0 : nat) := (fun y0 : nat => ((Nat.mul (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))) (NUMERAL 0).
Definition term65 := (fun y0 : nat => ((Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))) (NUMERAL 0).
Definition term72 (x0 : nat) := imp ((fun y0 : nat => ((Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))) x0).
Definition term122 := or ((NUMERAL 0) = (NUMERAL 0)).
Definition term131 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 (S x1)) x1.
Definition term49 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) x0) -> (fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) (S x0).
Definition term125 (x0 : nat) := @eq Prop ((Nat.mul (S x0) (NUMERAL 0)) = (NUMERAL 0)).
Definition term119 := @eq Prop ((Nat.mul (NUMERAL 0) (NUMERAL 0)) = (NUMERAL 0)).
Definition term60 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = (NUMERAL 0)) = ((y1 = (NUMERAL 0)) \/ (y2 = (NUMERAL 0)))) y0.
Definition term134 (x0 : nat) (x1 : nat) := @eq nat (Nat.mul (S x0) (S x1)).
Definition term14 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term76 (x0 : nat) := ((NUMERAL 0) = (NUMERAL 0)) \/ ((S x0) = (NUMERAL 0)).
Definition term38 := fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0))).
Definition term102 (x0 : nat) (x1 : nat) := Nat.mul (S x0) (S x1).
Definition term67 := ((NUMERAL 0) = (NUMERAL 0)) \/ ((NUMERAL 0) = (NUMERAL 0)).
Definition term50 (x0 : nat) := (forall y0 : nat, ((Nat.mul x0 y0) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))) -> forall y0 : nat, ((Nat.mul (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) \/ (y0 = (NUMERAL 0))).
Definition term7 (x0 : nat) := forall y0 : nat, (Nat.add x0 (S y0)) = (S (Nat.add x0 y0)).
