Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term42 (x0 : nat) := ((fun y0 : nat => ((Nat.pow (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0))))) x0) -> (fun y0 : nat => ((Nat.pow (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0))))) (S x0).
Definition term114 (x0 : nat) := @eq nat (Nat.pow (NUMERAL 0) (S x0)).
Definition term134 (x0 : nat) (x1 : nat) := Nat.mul (S x0) (Nat.pow (S x0) x1).
Definition term80 (x0 : nat) := fun y0 : nat => (fun y1 : nat => ((Nat.pow (S x0) y1) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) y0.
Definition term52 := fun y0 : nat => (fun y1 : nat => ((Nat.pow (NUMERAL 0) y1) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) y0.
Definition term115 := @eq nat (NUMERAL 0).
Definition term125 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term104 := forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0).
Definition term18 := forall y0 : nat, (forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) -> forall y1 : nat, ((Nat.pow (S y0) y1) = (NUMERAL 0)) = (((S y0) = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0)))).
Definition term98 := S (NUMERAL 0).
Definition term113 (x0 : nat) := Nat.mul (NUMERAL 0) (Nat.pow (NUMERAL 0) x0).
Definition term109 (x0 : nat) := forall y0 : nat, (Nat.pow x0 (S y0)) = (Nat.mul x0 (Nat.pow x0 y0)).
Definition term127 := (forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))).
Definition term95 (x0 : nat) := S (Nat.add (NUMERAL x0) (NUMERAL x0)).
Definition term131 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul (S x0) y0) = (Nat.add (Nat.mul x0 y0) y0)) x1.
Definition term105 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) x0.
Definition term26 := ((forall y0 : nat, ((Nat.pow (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0))))) /\ (forall y0 : nat, (forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) -> forall y1 : nat, ((Nat.pow (S y0) y1) = (NUMERAL 0)) = (((S y0) = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0)))))) -> forall y0 : nat, forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0)))).
Definition term35 (x0 : nat) := Nat.pow (NUMERAL 0) x0.
Definition term77 (x0 : nat) := (((Nat.pow (S x0) (NUMERAL 0)) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (~ ((NUMERAL 0) = (NUMERAL 0))))) /\ (forall y0 : nat, (((Nat.pow (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0))))) -> ((Nat.pow (S x0) (S y0)) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (~ ((S y0) = (NUMERAL 0))))).
Definition term49 := (((Nat.pow (NUMERAL 0) (NUMERAL 0)) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (~ ((NUMERAL 0) = (NUMERAL 0))))) /\ (forall y0 : nat, (((Nat.pow (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0))))) -> ((Nat.pow (NUMERAL 0) (S y0)) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (~ ((S y0) = (NUMERAL 0))))).
Definition term81 (x0 : nat) := forall y0 : nat, (fun y1 : nat => ((Nat.pow (S x0) y1) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) y0.
Definition term53 := forall y0 : nat, (fun y1 : nat => ((Nat.pow (NUMERAL 0) y1) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) y0.
Definition term76 (x0 : nat) := ((fun y0 : nat => ((Nat.pow (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0))))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Nat.pow (S x0) y1) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) y0) -> (fun y1 : nat => ((Nat.pow (S x0) y1) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) (S y0)).
Definition term48 := ((fun y0 : nat => ((Nat.pow (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0))))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Nat.pow (NUMERAL 0) y1) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) y0) -> (fun y1 : nat => ((Nat.pow (NUMERAL 0) y1) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) (S y0)).
Definition term9 (x0 : nat) := imp ((fun y0 : nat => forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) x0).
Definition term61 (x0 : nat) := and (((Nat.pow (S x0) (NUMERAL 0)) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (~ ((NUMERAL 0) = (NUMERAL 0))))).
Definition term33 := and (((Nat.pow (NUMERAL 0) (NUMERAL 0)) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (~ ((NUMERAL 0) = (NUMERAL 0))))).
Definition term111 (x0 : nat) (x1 : nat) := Nat.pow x0 (S x1).
Definition term70 (x0 : nat) (x1 : nat) := ((fun y0 : nat => ((Nat.pow (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0))))) x1) -> (fun y0 : nat => ((Nat.pow (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0))))) (S x1).
Definition term55 (x0 : nat) := (((fun y0 : nat => ((Nat.pow (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0))))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Nat.pow (S x0) y1) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) y0) -> (fun y1 : nat => ((Nat.pow (S x0) y1) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) (S y0))) -> forall y0 : nat, (fun y1 : nat => ((Nat.pow (S x0) y1) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) y0.
Definition term27 := (((fun y0 : nat => ((Nat.pow (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0))))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Nat.pow (NUMERAL 0) y1) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) y0) -> (fun y1 : nat => ((Nat.pow (NUMERAL 0) y1) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) (S y0))) -> forall y0 : nat, (fun y1 : nat => ((Nat.pow (NUMERAL 0) y1) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) y0.
Definition term1 := (((fun y0 : nat => forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.pow y1 y2) = (NUMERAL 0)) = ((y1 = (NUMERAL 0)) /\ (~ (y2 = (NUMERAL 0))))) y0) -> (fun y1 : nat => forall y2 : nat, ((Nat.pow y1 y2) = (NUMERAL 0)) = ((y1 = (NUMERAL 0)) /\ (~ (y2 = (NUMERAL 0))))) (S y0))) -> forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Nat.pow y1 y2) = (NUMERAL 0)) = ((y1 = (NUMERAL 0)) /\ (~ (y2 = (NUMERAL 0))))) y0.
Definition term110 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.pow x0 (S y0)) = (Nat.mul x0 (Nat.pow x0 y0))) x1.
Definition term88 (x0 : nat) := Nat.pow x0 (NUMERAL 0).
Definition term0 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term39 (x0 : nat) := (fun y0 : nat => ((Nat.pow (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0))))) (S x0).
Definition term78 (x0 : nat) := imp (((fun y0 : nat => ((Nat.pow (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0))))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Nat.pow (S x0) y1) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) y0) -> (fun y1 : nat => ((Nat.pow (S x0) y1) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) (S y0))).
Definition term50 := imp (((fun y0 : nat => ((Nat.pow (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0))))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Nat.pow (NUMERAL 0) y1) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) y0) -> (fun y1 : nat => ((Nat.pow (NUMERAL 0) y1) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) (S y0))).
Definition term21 := imp (((fun y0 : nat => forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.pow y1 y2) = (NUMERAL 0)) = ((y1 = (NUMERAL 0)) /\ (~ (y2 = (NUMERAL 0))))) y0) -> (fun y1 : nat => forall y2 : nat, ((Nat.pow y1 y2) = (NUMERAL 0)) = ((y1 = (NUMERAL 0)) /\ (~ (y2 = (NUMERAL 0))))) (S y0))).
Definition term30 := Nat.pow (NUMERAL 0) (NUMERAL 0).
Definition term103 := ~ ((NUMERAL 0) = (NUMERAL 0)).
Definition term121 (x0 : nat) := forall y0 : nat, ((Nat.add x0 y0) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) /\ (y0 = (NUMERAL 0))).
Definition term132 (x0 : nat) (x1 : nat) := Nat.mul (S x0) x1.
Definition term117 (x0 : nat) := @eq nat (Nat.pow (S x0) (NUMERAL 0)).
Definition term74 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => ((Nat.pow (S x0) y1) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) y0) -> (fun y1 : nat => ((Nat.pow (S x0) y1) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) (S y0).
Definition term46 := forall y0 : nat, ((fun y1 : nat => ((Nat.pow (NUMERAL 0) y1) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) y0) -> (fun y1 : nat => ((Nat.pow (NUMERAL 0) y1) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) (S y0).
Definition term17 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.pow y1 y2) = (NUMERAL 0)) = ((y1 = (NUMERAL 0)) /\ (~ (y2 = (NUMERAL 0))))) y0) -> (fun y1 : nat => forall y2 : nat, ((Nat.pow y1 y2) = (NUMERAL 0)) = ((y1 = (NUMERAL 0)) /\ (~ (y2 = (NUMERAL 0))))) (S y0).
Definition term123 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)).
Definition term56 (x0 : nat) := fun y0 : nat => ((Nat.pow (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0)))).
Definition term28 := fun y0 : nat => ((Nat.pow (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0)))).
Definition term140 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term36 (x0 : nat) := ((NUMERAL 0) = (NUMERAL 0)) /\ (~ (x0 = (NUMERAL 0))).
Definition term71 (x0 : nat) (x1 : nat) := (((Nat.pow (S x0) x1) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (~ (x1 = (NUMERAL 0))))) -> ((Nat.pow (S x0) (S x1)) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (~ ((S x1) = (NUMERAL 0)))).
Definition term43 (x0 : nat) := (((Nat.pow (NUMERAL 0) x0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (~ (x0 = (NUMERAL 0))))) -> ((Nat.pow (NUMERAL 0) (S x0)) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (~ ((S x0) = (NUMERAL 0)))).
Definition term102 := and ((NUMERAL 0) = (NUMERAL 0)).
Definition term60 (x0 : nat) := and ((fun y0 : nat => ((Nat.pow (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0))))) (NUMERAL 0)).
Definition term32 := and ((fun y0 : nat => ((Nat.pow (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0))))) (NUMERAL 0)).
Definition term97 := Nat.add (NUMERAL 0) (NUMERAL 0).
Definition term100 := @eq nat (S (NUMERAL 0)).
Definition term5 := and ((fun y0 : nat => forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) (NUMERAL 0)).
Definition term10 (x0 : nat) := imp (forall y0 : nat, ((Nat.pow x0 y0) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0))))).
Definition term6 := and (forall y0 : nat, ((Nat.pow (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0))))).
Definition term11 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) (S x0).
Definition term3 := (fun y0 : nat => forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) (NUMERAL 0).
Definition term87 (x0 : nat) := (fun y0 : nat => (Nat.pow y0 (NUMERAL 0)) = (NUMERAL (BIT1 0))) x0.
Definition term72 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => ((Nat.pow (S x0) y1) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) y0) -> (fun y1 : nat => ((Nat.pow (S x0) y1) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) (S y0).
Definition term44 := fun y0 : nat => ((fun y1 : nat => ((Nat.pow (NUMERAL 0) y1) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) y0) -> (fun y1 : nat => ((Nat.pow (NUMERAL 0) y1) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) (S y0).
Definition term34 (x0 : nat) := (fun y0 : nat => ((Nat.pow (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0))))) x0.
Definition term85 (x0 : nat) := Nat.add (NUMERAL 0) x0.
Definition term22 := imp ((forall y0 : nat, ((Nat.pow (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0))))) /\ (forall y0 : nat, (forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) -> forall y1 : nat, ((Nat.pow (S y0) y1) = (NUMERAL 0)) = (((S y0) = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0)))))).
Definition term137 (x0 : nat) (x1 : nat) := @eq nat (Nat.add (Nat.mul x0 (Nat.pow (S x0) x1)) (Nat.pow (S x0) x1)).
Definition term58 (x0 : nat) := Nat.pow (S x0) (NUMERAL 0).
Definition term128 := forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1).
Definition term107 := forall y0 : nat, forall y1 : nat, (Nat.pow y0 (S y1)) = (Nat.mul y0 (Nat.pow y0 y1)).
Definition term25 := forall y0 : nat, forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0)))).
Definition term62 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.pow (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0))))) x1.
Definition term59 (x0 : nat) := ((S x0) = (NUMERAL 0)) /\ (~ ((NUMERAL 0) = (NUMERAL 0))).
Definition term82 (x0 : nat) := ((((Nat.pow (S x0) (NUMERAL 0)) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (~ ((NUMERAL 0) = (NUMERAL 0))))) /\ (forall y0 : nat, (((Nat.pow (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0))))) -> ((Nat.pow (S x0) (S y0)) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (~ ((S y0) = (NUMERAL 0)))))) -> forall y0 : nat, ((Nat.pow (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0)))).
Definition term54 := ((((Nat.pow (NUMERAL 0) (NUMERAL 0)) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (~ ((NUMERAL 0) = (NUMERAL 0))))) /\ (forall y0 : nat, (((Nat.pow (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0))))) -> ((Nat.pow (NUMERAL 0) (S y0)) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (~ ((S y0) = (NUMERAL 0)))))) -> forall y0 : nat, ((Nat.pow (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0)))).
Definition term96 := S (Nat.add (NUMERAL 0) (NUMERAL 0)).
Definition term143 (x0 : nat) (x1 : nat) := ((Nat.mul x0 (Nat.pow (S x0) x1)) = (NUMERAL 0)) /\ False.
Definition term138 (x0 : nat) (x1 : nat) := ((Nat.mul x0 (Nat.pow (S x0) x1)) = (NUMERAL 0)) /\ ((Nat.pow (S x0) x1) = (NUMERAL 0)).
Definition term83 := forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0.
Definition term112 (x0 : nat) (x1 : nat) := Nat.mul x0 (Nat.pow x0 x1).
Definition term65 (x0 : nat) (x1 : nat) := imp ((fun y0 : nat => ((Nat.pow (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0))))) x1).
Definition term84 (x0 : nat) := (fun y0 : nat => (Nat.add (NUMERAL 0) y0) = y0) x0.
Definition term130 (x0 : nat) := forall y0 : nat, (Nat.mul (S x0) y0) = (Nat.add (Nat.mul x0 y0) y0).
Definition term93 (x0 : nat) := (fun y0 : nat => (NUMERAL (BIT1 y0)) = (S (Nat.add (NUMERAL y0) (NUMERAL y0)))) x0.
Definition term91 (x0 : nat) := ~ ((S x0) = (NUMERAL 0)).
Definition term64 (x0 : nat) (x1 : nat) := ((S x0) = (NUMERAL 0)) /\ (~ (x1 = (NUMERAL 0))).
Definition term16 := fun y0 : nat => (forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) -> forall y1 : nat, ((Nat.pow (S y0) y1) = (NUMERAL 0)) = (((S y0) = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0)))).
Definition term15 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, ((Nat.pow y1 y2) = (NUMERAL 0)) = ((y1 = (NUMERAL 0)) /\ (~ (y2 = (NUMERAL 0))))) y0) -> (fun y1 : nat => forall y2 : nat, ((Nat.pow y1 y2) = (NUMERAL 0)) = ((y1 = (NUMERAL 0)) /\ (~ (y2 = (NUMERAL 0))))) (S y0).
Definition term119 (x0 : nat) := and ((S x0) = (NUMERAL 0)).
Definition term126 := (forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))).
Definition term69 (x0 : nat) (x1 : nat) := ((S x0) = (NUMERAL 0)) /\ (~ ((S x1) = (NUMERAL 0))).
Definition term20 := (forall y0 : nat, ((Nat.pow (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0))))) /\ (forall y0 : nat, (forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) -> forall y1 : nat, ((Nat.pow (S y0) y1) = (NUMERAL 0)) = (((S y0) = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))).
Definition term144 (x0 : nat) (x1 : nat) := @eq Prop ((Nat.pow (S x0) (S x1)) = (NUMERAL 0)).
Definition term116 (x0 : nat) := @eq Prop ((Nat.pow (NUMERAL 0) (S x0)) = (NUMERAL 0)).
Definition term23 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, ((Nat.pow y1 y2) = (NUMERAL 0)) = ((y1 = (NUMERAL 0)) /\ (~ (y2 = (NUMERAL 0))))) y0.
Definition term129 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) x0.
Definition term120 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.add y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) x0.
Definition term108 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.pow y0 (S y1)) = (Nat.mul y0 (Nat.pow y0 y1))) x0.
Definition term7 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) x0.
Definition term90 (x0 : nat) := (fun y0 : nat => ~ ((S y0) = (NUMERAL 0))) x0.
Definition term136 (x0 : nat) (x1 : nat) := @eq nat (Nat.pow (S x0) (S x1)).
Definition term86 := forall y0 : nat, (Nat.pow y0 (NUMERAL 0)) = (NUMERAL (BIT1 0)).
Definition term99 := @eq nat (Nat.pow (NUMERAL 0) (NUMERAL 0)).
Definition term63 (x0 : nat) (x1 : nat) := Nat.pow (S x0) x1.
Definition term133 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 x1) x1.
Definition term19 := ((fun y0 : nat => forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.pow y1 y2) = (NUMERAL 0)) = ((y1 = (NUMERAL 0)) /\ (~ (y2 = (NUMERAL 0))))) y0) -> (fun y1 : nat => forall y2 : nat, ((Nat.pow y1 y2) = (NUMERAL 0)) = ((y1 = (NUMERAL 0)) /\ (~ (y2 = (NUMERAL 0))))) (S y0)).
Definition term66 (x0 : nat) (x1 : nat) := imp (((Nat.pow (S x0) x1) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (~ (x1 = (NUMERAL 0))))).
Definition term38 (x0 : nat) := imp (((Nat.pow (NUMERAL 0) x0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (~ (x0 = (NUMERAL 0))))).
Definition term92 (x0 : nat) := (~ ((S x0) = (NUMERAL 0))) -> ((S x0) = (NUMERAL 0)) = False.
Definition term135 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 (Nat.pow (S x0) x1)) (Nat.pow (S x0) x1).
Definition term40 (x0 : nat) := Nat.pow (NUMERAL 0) (S x0).
Definition term79 (x0 : nat) := imp ((((Nat.pow (S x0) (NUMERAL 0)) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (~ ((NUMERAL 0) = (NUMERAL 0))))) /\ (forall y0 : nat, (((Nat.pow (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0))))) -> ((Nat.pow (S x0) (S y0)) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (~ ((S y0) = (NUMERAL 0)))))).
Definition term51 := imp ((((Nat.pow (NUMERAL 0) (NUMERAL 0)) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (~ ((NUMERAL 0) = (NUMERAL 0))))) /\ (forall y0 : nat, (((Nat.pow (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0))))) -> ((Nat.pow (NUMERAL 0) (S y0)) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (~ ((S y0) = (NUMERAL 0)))))).
Definition term75 (x0 : nat) := forall y0 : nat, (((Nat.pow (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0))))) -> ((Nat.pow (S x0) (S y0)) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (~ ((S y0) = (NUMERAL 0)))).
Definition term47 := forall y0 : nat, (((Nat.pow (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0))))) -> ((Nat.pow (NUMERAL 0) (S y0)) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (~ ((S y0) = (NUMERAL 0)))).
Definition term106 (x0 : nat) := Nat.mul (NUMERAL 0) x0.
Definition term67 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.pow (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0))))) (S x1).
Definition term57 (x0 : nat) := (fun y0 : nat => ((Nat.pow (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0))))) (NUMERAL 0).
Definition term29 := (fun y0 : nat => ((Nat.pow (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0))))) (NUMERAL 0).
Definition term37 (x0 : nat) := imp ((fun y0 : nat => ((Nat.pow (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0))))) x0).
Definition term41 (x0 : nat) := ((NUMERAL 0) = (NUMERAL 0)) /\ (~ ((S x0) = (NUMERAL 0))).
Definition term139 (x0 : nat) (x1 : nat) := Nat.mul x0 (Nat.pow (S x0) x1).
Definition term13 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) x0) -> (fun y0 : nat => forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) (S x0).
Definition term118 (x0 : nat) := @eq Prop ((Nat.pow (S x0) (NUMERAL 0)) = (NUMERAL 0)).
Definition term101 := @eq Prop ((Nat.pow (NUMERAL 0) (NUMERAL 0)) = (NUMERAL 0)).
Definition term24 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Nat.pow y1 y2) = (NUMERAL 0)) = ((y1 = (NUMERAL 0)) /\ (~ (y2 = (NUMERAL 0))))) y0.
Definition term68 (x0 : nat) (x1 : nat) := Nat.pow (S x0) (S x1).
Definition term124 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term31 := ((NUMERAL 0) = (NUMERAL 0)) /\ (~ ((NUMERAL 0) = (NUMERAL 0))).
Definition term94 (x0 : nat) := NUMERAL (BIT1 x0).
Definition term142 (x0 : nat) (x1 : nat) := and ((Nat.mul x0 (Nat.pow (S x0) x1)) = (NUMERAL 0)).
Definition term141 (x0 : nat) := False /\ (~ (x0 = (NUMERAL 0))).
Definition term2 := fun y0 : nat => forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0)))).
Definition term89 := NUMERAL (BIT1 0).
Definition term73 (x0 : nat) := fun y0 : nat => (((Nat.pow (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0))))) -> ((Nat.pow (S x0) (S y0)) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (~ ((S y0) = (NUMERAL 0)))).
Definition term45 := fun y0 : nat => (((Nat.pow (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0))))) -> ((Nat.pow (NUMERAL 0) (S y0)) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (~ ((S y0) = (NUMERAL 0)))).
Definition term12 (x0 : nat) := forall y0 : nat, ((Nat.pow (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0)))).
Definition term8 (x0 : nat) := forall y0 : nat, ((Nat.pow x0 y0) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0)))).
Definition term4 := forall y0 : nat, ((Nat.pow (NUMERAL 0) y0) = (NUMERAL 0)) = (((NUMERAL 0) = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0)))).
Definition term14 (x0 : nat) := (forall y0 : nat, ((Nat.pow x0 y0) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0))))) -> forall y0 : nat, ((Nat.pow (S x0) y0) = (NUMERAL 0)) = (((S x0) = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0)))).
Definition term122 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.add x0 y0) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) x1.
