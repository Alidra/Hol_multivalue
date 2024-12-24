Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term63 (x0 : nat) := ((fun y0 : nat => ((Nat.add (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) x0) -> (fun y0 : nat => ((Nat.add (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) (S x0).
Definition term100 (x0 : nat) := fun y0 : nat => (fun y1 : nat => ((Nat.add (S x0) y1) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) y0.
Definition term73 := fun y0 : nat => (fun y1 : nat => ((Nat.add (NUMERAL 0) y1) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) y0.
Definition term104 := @eq nat (NUMERAL 0).
Definition term53 := ((NUMERAL 0) = (NUMERAL 0)) /\ ((NUMERAL 0) = (NUMERAL 0)).
Definition term40 := forall y0 : nat, (forall y1 : nat, ((Nat.add y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) -> forall y1 : nat, ((Nat.add (S y0) y1) = (NUMERAL 0)) = (((S y0) = (NUMERAL 0)) /\ (y1 = (NUMERAL 0))).
Definition term4 := (forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))).
Definition term56 (x0 : nat) := (fun y0 : nat => ((Nat.add (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) x0.
Definition term48 := ((forall y0 : nat, ((Nat.add (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) /\ (forall y0 : nat, (forall y1 : nat, ((Nat.add y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) -> forall y1 : nat, ((Nat.add (S y0) y1) = (NUMERAL 0)) = (((S y0) = (NUMERAL 0)) /\ (y1 = (NUMERAL 0))))) -> forall y0 : nat, forall y1 : nat, ((Nat.add y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (y1 = (NUMERAL 0))).
Definition term101 (x0 : nat) := forall y0 : nat, (fun y1 : nat => ((Nat.add (S x0) y1) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) y0.
Definition term74 := forall y0 : nat, (fun y1 : nat => ((Nat.add (NUMERAL 0) y1) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) y0.
Definition term77 (x0 : nat) := fun y0 : nat => ((Nat.add (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (y0 = (NUMERAL 0))).
Definition term50 := fun y0 : nat => ((Nat.add (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (y0 = (NUMERAL 0))).
Definition term96 (x0 : nat) := ((fun y0 : nat => ((Nat.add (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Nat.add (S x0) y1) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) y0) -> (fun y1 : nat => ((Nat.add (S x0) y1) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) (S y0)).
Definition term69 := ((fun y0 : nat => ((Nat.add (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Nat.add (NUMERAL 0) y1) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) y0) -> (fun y1 : nat => ((Nat.add (NUMERAL 0) y1) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) (S y0)).
Definition term31 (x0 : nat) := imp ((fun y0 : nat => forall y1 : nat, ((Nat.add y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) x0).
Definition term87 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.add (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) (S x1).
Definition term17 (x0 : nat) := (fun y0 : nat => (Nat.add y0 (NUMERAL 0)) = y0) x0.
Definition term90 (x0 : nat) (x1 : nat) := ((fun y0 : nat => ((Nat.add (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) x1) -> (fun y0 : nat => ((Nat.add (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) (S x1).
Definition term80 (x0 : nat) := ((S x0) = (NUMERAL 0)) /\ ((NUMERAL 0) = (NUMERAL 0)).
Definition term76 (x0 : nat) := (((fun y0 : nat => ((Nat.add (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Nat.add (S x0) y1) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) y0) -> (fun y1 : nat => ((Nat.add (S x0) y1) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) (S y0))) -> forall y0 : nat, (fun y1 : nat => ((Nat.add (S x0) y1) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) y0.
Definition term49 := (((fun y0 : nat => ((Nat.add (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Nat.add (NUMERAL 0) y1) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) y0) -> (fun y1 : nat => ((Nat.add (NUMERAL 0) y1) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) (S y0))) -> forall y0 : nat, (fun y1 : nat => ((Nat.add (NUMERAL 0) y1) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) y0.
Definition term23 := (((fun y0 : nat => forall y1 : nat, ((Nat.add y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.add y1 y2) = (NUMERAL 0)) = ((y1 = (NUMERAL 0)) /\ (y2 = (NUMERAL 0)))) y0) -> (fun y1 : nat => forall y2 : nat, ((Nat.add y1 y2) = (NUMERAL 0)) = ((y1 = (NUMERAL 0)) /\ (y2 = (NUMERAL 0)))) (S y0))) -> forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Nat.add y1 y2) = (NUMERAL 0)) = ((y1 = (NUMERAL 0)) /\ (y2 = (NUMERAL 0)))) y0.
Definition term62 (x0 : nat) := ((NUMERAL 0) = (NUMERAL 0)) /\ ((S x0) = (NUMERAL 0)).
Definition term22 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term13 (x0 : nat) := forall y0 : nat, (Nat.add (S x0) y0) = (S (Nat.add x0 y0)).
Definition term98 (x0 : nat) := imp (((fun y0 : nat => ((Nat.add (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Nat.add (S x0) y1) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) y0) -> (fun y1 : nat => ((Nat.add (S x0) y1) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) (S y0))).
Definition term71 := imp (((fun y0 : nat => ((Nat.add (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Nat.add (NUMERAL 0) y1) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) y0) -> (fun y1 : nat => ((Nat.add (NUMERAL 0) y1) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) (S y0))).
Definition term43 := imp (((fun y0 : nat => forall y1 : nat, ((Nat.add y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.add y1 y2) = (NUMERAL 0)) = ((y1 = (NUMERAL 0)) /\ (y2 = (NUMERAL 0)))) y0) -> (fun y1 : nat => forall y2 : nat, ((Nat.add y1 y2) = (NUMERAL 0)) = ((y1 = (NUMERAL 0)) /\ (y2 = (NUMERAL 0)))) (S y0))).
Definition term18 (x0 : nat) := Nat.add x0 (NUMERAL 0).
Definition term34 (x0 : nat) := forall y0 : nat, ((Nat.add (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (y0 = (NUMERAL 0))).
Definition term30 (x0 : nat) := forall y0 : nat, ((Nat.add x0 y0) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) /\ (y0 = (NUMERAL 0))).
Definition term26 := forall y0 : nat, ((Nat.add (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (y0 = (NUMERAL 0))).
Definition term94 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => ((Nat.add (S x0) y1) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) y0) -> (fun y1 : nat => ((Nat.add (S x0) y1) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) (S y0).
Definition term67 := forall y0 : nat, ((fun y1 : nat => ((Nat.add (NUMERAL 0) y1) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) y0) -> (fun y1 : nat => ((Nat.add (NUMERAL 0) y1) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) (S y0).
Definition term39 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.add y1 y2) = (NUMERAL 0)) = ((y1 = (NUMERAL 0)) /\ (y2 = (NUMERAL 0)))) y0) -> (fun y1 : nat => forall y2 : nat, ((Nat.add y1 y2) = (NUMERAL 0)) = ((y1 = (NUMERAL 0)) /\ (y2 = (NUMERAL 0)))) (S y0).
Definition term16 := forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0.
Definition term109 := and ((NUMERAL 0) = (NUMERAL 0)).
Definition term81 (x0 : nat) := and ((fun y0 : nat => ((Nat.add (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) (NUMERAL 0)).
Definition term54 := and ((fun y0 : nat => ((Nat.add (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) (NUMERAL 0)).
Definition term52 := Nat.add (NUMERAL 0) (NUMERAL 0).
Definition term14 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add (S x0) y0) = (S (Nat.add x0 y0))) x1.
Definition term27 := and ((fun y0 : nat => forall y1 : nat, ((Nat.add y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) (NUMERAL 0)).
Definition term32 (x0 : nat) := imp (forall y0 : nat, ((Nat.add x0 y0) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))).
Definition term28 := and (forall y0 : nat, ((Nat.add (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))).
Definition term33 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.add y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) (S x0).
Definition term25 := (fun y0 : nat => forall y1 : nat, ((Nat.add y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) (NUMERAL 0).
Definition term92 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => ((Nat.add (S x0) y1) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) y0) -> (fun y1 : nat => ((Nat.add (S x0) y1) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) (S y0).
Definition term65 := fun y0 : nat => ((fun y1 : nat => ((Nat.add (NUMERAL 0) y1) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) y0) -> (fun y1 : nat => ((Nat.add (NUMERAL 0) y1) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) (S y0).
Definition term21 (x0 : nat) := Nat.add (NUMERAL 0) x0.
Definition term44 := imp ((forall y0 : nat, ((Nat.add (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) /\ (forall y0 : nat, (forall y1 : nat, ((Nat.add y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) -> forall y1 : nat, ((Nat.add (S y0) y1) = (NUMERAL 0)) = (((S y0) = (NUMERAL 0)) /\ (y1 = (NUMERAL 0))))).
Definition term10 (x0 : nat) (x1 : nat) := S (Nat.add x0 x1).
Definition term60 (x0 : nat) := (fun y0 : nat => ((Nat.add (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) (S x0).
Definition term47 := forall y0 : nat, forall y1 : nat, ((Nat.add y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (y1 = (NUMERAL 0))).
Definition term11 := forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1)).
Definition term5 := forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)).
Definition term102 (x0 : nat) := ((((Nat.add (S x0) (NUMERAL 0)) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ ((NUMERAL 0) = (NUMERAL 0)))) /\ (forall y0 : nat, (((Nat.add (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) -> ((Nat.add (S x0) (S y0)) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ ((S y0) = (NUMERAL 0))))) -> forall y0 : nat, ((Nat.add (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (y0 = (NUMERAL 0))).
Definition term75 := ((((Nat.add (NUMERAL 0) (NUMERAL 0)) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ ((NUMERAL 0) = (NUMERAL 0)))) /\ (forall y0 : nat, (((Nat.add (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) -> ((Nat.add (NUMERAL 0) (S y0)) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ ((S y0) = (NUMERAL 0))))) -> forall y0 : nat, ((Nat.add (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (y0 = (NUMERAL 0))).
Definition term19 := forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0.
Definition term85 (x0 : nat) (x1 : nat) := imp ((fun y0 : nat => ((Nat.add (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) x1).
Definition term20 (x0 : nat) := (fun y0 : nat => (Nat.add (NUMERAL 0) y0) = y0) x0.
Definition term91 (x0 : nat) (x1 : nat) := (((Nat.add (S x0) x1) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)))) -> ((Nat.add (S x0) (S x1)) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ ((S x1) = (NUMERAL 0))).
Definition term64 (x0 : nat) := (((Nat.add (NUMERAL 0) x0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (x0 = (NUMERAL 0)))) -> ((Nat.add (NUMERAL 0) (S x0)) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ ((S x0) = (NUMERAL 0))).
Definition term88 (x0 : nat) (x1 : nat) := Nat.add (S x0) (S x1).
Definition term1 (x0 : nat) := ~ ((S x0) = (NUMERAL 0)).
Definition term86 (x0 : nat) (x1 : nat) := imp (((Nat.add (S x0) x1) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)))).
Definition term59 (x0 : nat) := imp (((Nat.add (NUMERAL 0) x0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (x0 = (NUMERAL 0)))).
Definition term8 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 (S y0)) = (S (Nat.add x0 y0))) x1.
Definition term38 := fun y0 : nat => (forall y1 : nat, ((Nat.add y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) -> forall y1 : nat, ((Nat.add (S y0) y1) = (NUMERAL 0)) = (((S y0) = (NUMERAL 0)) /\ (y1 = (NUMERAL 0))).
Definition term37 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, ((Nat.add y1 y2) = (NUMERAL 0)) = ((y1 = (NUMERAL 0)) /\ (y2 = (NUMERAL 0)))) y0) -> (fun y1 : nat => forall y2 : nat, ((Nat.add y1 y2) = (NUMERAL 0)) = ((y1 = (NUMERAL 0)) /\ (y2 = (NUMERAL 0)))) (S y0).
Definition term113 (x0 : nat) := and ((S x0) = (NUMERAL 0)).
Definition term3 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term42 := (forall y0 : nat, ((Nat.add (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) /\ (forall y0 : nat, (forall y1 : nat, ((Nat.add y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) -> forall y1 : nat, ((Nat.add (S y0) y1) = (NUMERAL 0)) = (((S y0) = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))).
Definition term107 (x0 : nat) := @eq nat (S x0).
Definition term118 (x0 : nat) (x1 : nat) := @eq Prop ((Nat.add (S x0) (S x1)) = (NUMERAL 0)).
Definition term108 (x0 : nat) := @eq Prop ((Nat.add (NUMERAL 0) (S x0)) = (NUMERAL 0)).
Definition term82 (x0 : nat) := and (((Nat.add (S x0) (NUMERAL 0)) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ ((NUMERAL 0) = (NUMERAL 0)))).
Definition term55 := and (((Nat.add (NUMERAL 0) (NUMERAL 0)) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ ((NUMERAL 0) = (NUMERAL 0)))).
Definition term116 (x0 : nat) (x1 : nat) := @eq nat (Nat.add (S x0) (S x1)).
Definition term84 (x0 : nat) (x1 : nat) := ((S x0) = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)).
Definition term114 (x0 : nat) (x1 : nat) := S (Nat.add x0 (S x1)).
Definition term45 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, ((Nat.add y1 y2) = (NUMERAL 0)) = ((y1 = (NUMERAL 0)) /\ (y2 = (NUMERAL 0)))) y0.
Definition term29 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.add y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) x0.
Definition term12 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) x0.
Definition term6 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => ~ ((S y0) = (NUMERAL 0))) x0.
Definition term41 := ((fun y0 : nat => forall y1 : nat, ((Nat.add y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.add y1 y2) = (NUMERAL 0)) = ((y1 = (NUMERAL 0)) /\ (y2 = (NUMERAL 0)))) y0) -> (fun y1 : nat => forall y2 : nat, ((Nat.add y1 y2) = (NUMERAL 0)) = ((y1 = (NUMERAL 0)) /\ (y2 = (NUMERAL 0)))) (S y0)).
Definition term61 (x0 : nat) := Nat.add (NUMERAL 0) (S x0).
Definition term110 (x0 : nat) := S (Nat.add x0 (NUMERAL 0)).
Definition term111 (x0 : nat) := @eq nat (Nat.add (S x0) (NUMERAL 0)).
Definition term9 (x0 : nat) (x1 : nat) := Nat.add x0 (S x1).
Definition term2 (x0 : nat) := (~ ((S x0) = (NUMERAL 0))) -> ((S x0) = (NUMERAL 0)) = False.
Definition term99 (x0 : nat) := imp ((((Nat.add (S x0) (NUMERAL 0)) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ ((NUMERAL 0) = (NUMERAL 0)))) /\ (forall y0 : nat, (((Nat.add (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) -> ((Nat.add (S x0) (S y0)) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ ((S y0) = (NUMERAL 0))))).
Definition term72 := imp ((((Nat.add (NUMERAL 0) (NUMERAL 0)) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ ((NUMERAL 0) = (NUMERAL 0)))) /\ (forall y0 : nat, (((Nat.add (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) -> ((Nat.add (NUMERAL 0) (S y0)) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ ((S y0) = (NUMERAL 0))))).
Definition term97 (x0 : nat) := (((Nat.add (S x0) (NUMERAL 0)) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ ((NUMERAL 0) = (NUMERAL 0)))) /\ (forall y0 : nat, (((Nat.add (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) -> ((Nat.add (S x0) (S y0)) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ ((S y0) = (NUMERAL 0)))).
Definition term70 := (((Nat.add (NUMERAL 0) (NUMERAL 0)) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ ((NUMERAL 0) = (NUMERAL 0)))) /\ (forall y0 : nat, (((Nat.add (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) -> ((Nat.add (NUMERAL 0) (S y0)) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ ((S y0) = (NUMERAL 0)))).
Definition term95 (x0 : nat) := forall y0 : nat, (((Nat.add (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) -> ((Nat.add (S x0) (S y0)) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ ((S y0) = (NUMERAL 0))).
Definition term68 := forall y0 : nat, (((Nat.add (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) -> ((Nat.add (NUMERAL 0) (S y0)) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ ((S y0) = (NUMERAL 0))).
Definition term93 (x0 : nat) := fun y0 : nat => (((Nat.add (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) -> ((Nat.add (S x0) (S y0)) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ ((S y0) = (NUMERAL 0))).
Definition term66 := fun y0 : nat => (((Nat.add (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) -> ((Nat.add (NUMERAL 0) (S y0)) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ ((S y0) = (NUMERAL 0))).
Definition term89 (x0 : nat) (x1 : nat) := ((S x0) = (NUMERAL 0)) /\ ((S x1) = (NUMERAL 0)).
Definition term78 (x0 : nat) := (fun y0 : nat => ((Nat.add (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) (NUMERAL 0).
Definition term51 := (fun y0 : nat => ((Nat.add (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) (NUMERAL 0).
Definition term57 (x0 : nat) := ((NUMERAL 0) = (NUMERAL 0)) /\ (x0 = (NUMERAL 0)).
Definition term58 (x0 : nat) := imp ((fun y0 : nat => ((Nat.add (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) x0).
Definition term35 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, ((Nat.add y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) x0) -> (fun y0 : nat => forall y1 : nat, ((Nat.add y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) (S x0).
Definition term106 (x0 : nat) := @eq nat (Nat.add (NUMERAL 0) (S x0)).
Definition term112 (x0 : nat) := @eq Prop ((Nat.add (S x0) (NUMERAL 0)) = (NUMERAL 0)).
Definition term105 := @eq Prop ((Nat.add (NUMERAL 0) (NUMERAL 0)) = (NUMERAL 0)).
Definition term46 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Nat.add y1 y2) = (NUMERAL 0)) = ((y1 = (NUMERAL 0)) /\ (y2 = (NUMERAL 0)))) y0.
Definition term79 (x0 : nat) := Nat.add (S x0) (NUMERAL 0).
Definition term15 (x0 : nat) (x1 : nat) := Nat.add (S x0) x1.
Definition term24 := fun y0 : nat => forall y1 : nat, ((Nat.add y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (y1 = (NUMERAL 0))).
Definition term103 := @eq nat (Nat.add (NUMERAL 0) (NUMERAL 0)).
Definition term36 (x0 : nat) := (forall y0 : nat, ((Nat.add x0 y0) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) -> forall y0 : nat, ((Nat.add (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (y0 = (NUMERAL 0))).
Definition term83 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.add (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) x1.
Definition term117 (x0 : nat) (x1 : nat) := @eq nat (S (S (Nat.add x0 x1))).
Definition term115 (x0 : nat) (x1 : nat) := S (S (Nat.add x0 x1)).
Definition term7 (x0 : nat) := forall y0 : nat, (Nat.add x0 (S y0)) = (S (Nat.add x0 y0)).
