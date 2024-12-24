Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term100 (x0 : nat) := ((fun y0 : nat => ((Nat.mul (NUMERAL 0) y0) = (NUMERAL (BIT1 0))) = (((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))) x0) -> (fun y0 : nat => ((Nat.mul (NUMERAL 0) y0) = (NUMERAL (BIT1 0))) = (((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))) (S x0).
Definition term12 (x0 : nat) := ~ ((NUMERAL 0) = (S x0)).
Definition term43 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul x0 (S y0)) = (Nat.add x0 (Nat.mul x0 y0))) x1.
Definition term93 (x0 : nat) := (fun y0 : nat => ((Nat.mul (NUMERAL 0) y0) = (NUMERAL (BIT1 0))) = (((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))) x0.
Definition term137 (x0 : nat) := fun y0 : nat => (fun y1 : nat => ((Nat.mul (S x0) y1) = (NUMERAL (BIT1 0))) = (((S x0) = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) y0.
Definition term110 := fun y0 : nat => (fun y1 : nat => ((Nat.mul (NUMERAL 0) y1) = (NUMERAL (BIT1 0))) = (((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) y0.
Definition term155 (x0 : nat) := and ((S x0) = (S (NUMERAL 0))).
Definition term141 := @eq nat (NUMERAL 0).
Definition term37 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term55 := forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0).
Definition term16 := forall y0 : nat, ~ ((NUMERAL 0) = (S y0)).
Definition term152 (x0 : nat) := @eq nat (Nat.mul (S x0) (NUMERAL 0)).
Definition term189 (x0 : nat) := True /\ (True \/ (x0 = (NUMERAL 0))).
Definition term188 (x0 : nat) := False /\ (x0 = (NUMERAL 0)).
Definition term76 := forall y0 : nat, (forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) -> forall y1 : nat, ((Nat.mul (S y0) y1) = (NUMERAL (BIT1 0))) = (((S y0) = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0)))).
Definition term126 (x0 : nat) (x1 : nat) := ((S x0) = (NUMERAL (BIT1 0))) /\ ((S x1) = (NUMERAL (BIT1 0))).
Definition term144 := S (NUMERAL 0).
Definition term42 (x0 : nat) := forall y0 : nat, (Nat.mul x0 (S y0)) = (Nat.add x0 (Nat.mul x0 y0)).
Definition term39 := (forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))).
Definition term23 := (forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))).
Definition term168 (x0 : nat) (x1 : nat) := ((S x0) = (S (NUMERAL 0))) /\ ((S x1) = (S (NUMERAL 0))).
Definition term128 (x0 : nat) (x1 : nat) := (((Nat.mul (S x0) x1) = (NUMERAL (BIT1 0))) = (((S x0) = (NUMERAL (BIT1 0))) /\ (x1 = (NUMERAL (BIT1 0))))) -> ((Nat.mul (S x0) (S x1)) = (NUMERAL (BIT1 0))) = (((S x0) = (NUMERAL (BIT1 0))) /\ ((S x1) = (NUMERAL (BIT1 0)))).
Definition term101 (x0 : nat) := (((Nat.mul (NUMERAL 0) x0) = (NUMERAL (BIT1 0))) = (((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ (x0 = (NUMERAL (BIT1 0))))) -> ((Nat.mul (NUMERAL 0) (S x0)) = (NUMERAL (BIT1 0))) = (((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ ((S x0) = (NUMERAL (BIT1 0)))).
Definition term21 (x0 : nat) := S (Nat.add (NUMERAL x0) (NUMERAL x0)).
Definition term49 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul (S x0) y0) = (Nat.add (Nat.mul x0 y0) y0)) x1.
Definition term56 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) x0.
Definition term9 (x0 : nat) := forall y0 : nat, ((S x0) = (S y0)) = (x0 = y0).
Definition term84 := ((forall y0 : nat, ((Nat.mul (NUMERAL 0) y0) = (NUMERAL (BIT1 0))) = (((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))) /\ (forall y0 : nat, (forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) -> forall y1 : nat, ((Nat.mul (S y0) y1) = (NUMERAL (BIT1 0))) = (((S y0) = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0)))))) -> forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0)))).
Definition term138 (x0 : nat) := forall y0 : nat, (fun y1 : nat => ((Nat.mul (S x0) y1) = (NUMERAL (BIT1 0))) = (((S x0) = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) y0.
Definition term111 := forall y0 : nat, (fun y1 : nat => ((Nat.mul (NUMERAL 0) y1) = (NUMERAL (BIT1 0))) = (((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) y0.
Definition term133 (x0 : nat) := ((fun y0 : nat => ((Nat.mul (S x0) y0) = (NUMERAL (BIT1 0))) = (((S x0) = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Nat.mul (S x0) y1) = (NUMERAL (BIT1 0))) = (((S x0) = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) y0) -> (fun y1 : nat => ((Nat.mul (S x0) y1) = (NUMERAL (BIT1 0))) = (((S x0) = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) (S y0)).
Definition term106 := ((fun y0 : nat => ((Nat.mul (NUMERAL 0) y0) = (NUMERAL (BIT1 0))) = (((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Nat.mul (NUMERAL 0) y1) = (NUMERAL (BIT1 0))) = (((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) y0) -> (fun y1 : nat => ((Nat.mul (NUMERAL 0) y1) = (NUMERAL (BIT1 0))) = (((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) (S y0)).
Definition term67 (x0 : nat) := imp ((fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) x0).
Definition term169 (x0 : nat) (x1 : nat) := ((Nat.add x0 (Nat.mul x0 x1)) = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)).
Definition term154 (x0 : nat) := and ((S x0) = (NUMERAL (BIT1 0))).
Definition term124 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.mul (S x0) y0) = (NUMERAL (BIT1 0))) = (((S x0) = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))) (S x1).
Definition term31 (x0 : nat) := (fun y0 : nat => (Nat.add y0 (NUMERAL 0)) = y0) x0.
Definition term130 (x0 : nat) := fun y0 : nat => (((Nat.mul (S x0) y0) = (NUMERAL (BIT1 0))) = (((S x0) = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))) -> ((Nat.mul (S x0) (S y0)) = (NUMERAL (BIT1 0))) = (((S x0) = (NUMERAL (BIT1 0))) /\ ((S y0) = (NUMERAL (BIT1 0)))).
Definition term103 := fun y0 : nat => (((Nat.mul (NUMERAL 0) y0) = (NUMERAL (BIT1 0))) = (((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))) -> ((Nat.mul (NUMERAL 0) (S y0)) = (NUMERAL (BIT1 0))) = (((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ ((S y0) = (NUMERAL (BIT1 0)))).
Definition term175 (x0 : nat) (x1 : nat) := ((x0 = (NUMERAL 0)) /\ ((x0 = (NUMERAL 0)) \/ (x1 = (NUMERAL 0)))) /\ (x1 = (NUMERAL 0)).
Definition term127 (x0 : nat) (x1 : nat) := ((fun y0 : nat => ((Nat.mul (S x0) y0) = (NUMERAL (BIT1 0))) = (((S x0) = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))) x1) -> (fun y0 : nat => ((Nat.mul (S x0) y0) = (NUMERAL (BIT1 0))) = (((S x0) = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))) (S x1).
Definition term171 (x0 : nat) := and (x0 = (NUMERAL 0)).
Definition term113 (x0 : nat) := (((fun y0 : nat => ((Nat.mul (S x0) y0) = (NUMERAL (BIT1 0))) = (((S x0) = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Nat.mul (S x0) y1) = (NUMERAL (BIT1 0))) = (((S x0) = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) y0) -> (fun y1 : nat => ((Nat.mul (S x0) y1) = (NUMERAL (BIT1 0))) = (((S x0) = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) (S y0))) -> forall y0 : nat, (fun y1 : nat => ((Nat.mul (S x0) y1) = (NUMERAL (BIT1 0))) = (((S x0) = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) y0.
Definition term85 := (((fun y0 : nat => ((Nat.mul (NUMERAL 0) y0) = (NUMERAL (BIT1 0))) = (((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Nat.mul (NUMERAL 0) y1) = (NUMERAL (BIT1 0))) = (((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) y0) -> (fun y1 : nat => ((Nat.mul (NUMERAL 0) y1) = (NUMERAL (BIT1 0))) = (((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) (S y0))) -> forall y0 : nat, (fun y1 : nat => ((Nat.mul (NUMERAL 0) y1) = (NUMERAL (BIT1 0))) = (((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) y0.
Definition term59 := (((fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = (NUMERAL (BIT1 0))) = ((y1 = (NUMERAL (BIT1 0))) /\ (y2 = (NUMERAL (BIT1 0))))) y0) -> (fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = (NUMERAL (BIT1 0))) = ((y1 = (NUMERAL (BIT1 0))) /\ (y2 = (NUMERAL (BIT1 0))))) (S y0))) -> forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = (NUMERAL (BIT1 0))) = ((y1 = (NUMERAL (BIT1 0))) /\ (y2 = (NUMERAL (BIT1 0))))) y0.
Definition term58 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term120 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.mul (S x0) y0) = (NUMERAL (BIT1 0))) = (((S x0) = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))) x1.
Definition term135 (x0 : nat) := imp (((fun y0 : nat => ((Nat.mul (S x0) y0) = (NUMERAL (BIT1 0))) = (((S x0) = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Nat.mul (S x0) y1) = (NUMERAL (BIT1 0))) = (((S x0) = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) y0) -> (fun y1 : nat => ((Nat.mul (S x0) y1) = (NUMERAL (BIT1 0))) = (((S x0) = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) (S y0))).
Definition term108 := imp (((fun y0 : nat => ((Nat.mul (NUMERAL 0) y0) = (NUMERAL (BIT1 0))) = (((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Nat.mul (NUMERAL 0) y1) = (NUMERAL (BIT1 0))) = (((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) y0) -> (fun y1 : nat => ((Nat.mul (NUMERAL 0) y1) = (NUMERAL (BIT1 0))) = (((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) (S y0))).
Definition term79 := imp (((fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = (NUMERAL (BIT1 0))) = ((y1 = (NUMERAL (BIT1 0))) /\ (y2 = (NUMERAL (BIT1 0))))) y0) -> (fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = (NUMERAL (BIT1 0))) = ((y1 = (NUMERAL (BIT1 0))) /\ (y2 = (NUMERAL (BIT1 0))))) (S y0))).
Definition term183 (x0 : nat) := True /\ (x0 = (NUMERAL 0)).
Definition term194 (x0 : nat) := False /\ (False \/ (x0 = (NUMERAL 0))).
Definition term117 (x0 : nat) := ((S x0) = (NUMERAL (BIT1 0))) /\ ((NUMERAL 0) = (NUMERAL (BIT1 0))).
Definition term32 (x0 : nat) := Nat.add x0 (NUMERAL 0).
Definition term70 (x0 : nat) := forall y0 : nat, ((Nat.mul (S x0) y0) = (NUMERAL (BIT1 0))) = (((S x0) = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0)))).
Definition term66 (x0 : nat) := forall y0 : nat, ((Nat.mul x0 y0) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0)))).
Definition term62 := forall y0 : nat, ((Nat.mul (NUMERAL 0) y0) = (NUMERAL (BIT1 0))) = (((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0)))).
Definition term5 (x0 : nat) := forall y0 : nat, ((Nat.add x0 y0) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) /\ (y0 = (NUMERAL 0))).
Definition term1 (x0 : nat) := forall y0 : nat, ((Nat.mul x0 y0) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) \/ (y0 = (NUMERAL 0))).
Definition term50 (x0 : nat) (x1 : nat) := Nat.mul (S x0) x1.
Definition term131 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => ((Nat.mul (S x0) y1) = (NUMERAL (BIT1 0))) = (((S x0) = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) y0) -> (fun y1 : nat => ((Nat.mul (S x0) y1) = (NUMERAL (BIT1 0))) = (((S x0) = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) (S y0).
Definition term104 := forall y0 : nat, ((fun y1 : nat => ((Nat.mul (NUMERAL 0) y1) = (NUMERAL (BIT1 0))) = (((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) y0) -> (fun y1 : nat => ((Nat.mul (NUMERAL 0) y1) = (NUMERAL (BIT1 0))) = (((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) (S y0).
Definition term75 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = (NUMERAL (BIT1 0))) = ((y1 = (NUMERAL (BIT1 0))) /\ (y2 = (NUMERAL (BIT1 0))))) y0) -> (fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = (NUMERAL (BIT1 0))) = ((y1 = (NUMERAL (BIT1 0))) /\ (y2 = (NUMERAL (BIT1 0))))) (S y0).
Definition term7 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)).
Definition term114 (x0 : nat) := fun y0 : nat => ((Nat.mul (S x0) y0) = (NUMERAL (BIT1 0))) = (((S x0) = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0)))).
Definition term86 := fun y0 : nat => ((Nat.mul (NUMERAL 0) y0) = (NUMERAL (BIT1 0))) = (((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0)))).
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.mul x0 y0) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))) x1.
Definition term44 (x0 : nat) (x1 : nat) := Nat.mul x0 (S x1).
Definition term182 (x0 : nat) := (True /\ (True \/ (x0 = (NUMERAL 0)))) /\ (x0 = (NUMERAL 0)).
Definition term98 (x0 : nat) := Nat.mul (NUMERAL 0) (S x0).
Definition term156 (x0 : nat) := ((S x0) = (S (NUMERAL 0))) /\ False.
Definition term196 (x0 : nat) := and (False /\ (False \/ (x0 = (NUMERAL 0)))).
Definition term15 := forall y0 : nat, ~ ((S y0) = (NUMERAL 0)).
Definition term30 := forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0.
Definition term151 (x0 : nat) := Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0).
Definition term166 (x0 : nat) (x1 : nat) := @eq Prop ((Nat.mul (S x0) (S x1)) = (NUMERAL (BIT1 0))).
Definition term147 (x0 : nat) := @eq Prop ((Nat.mul (NUMERAL 0) (S x0)) = (NUMERAL (BIT1 0))).
Definition term118 (x0 : nat) := and ((fun y0 : nat => ((Nat.mul (S x0) y0) = (NUMERAL (BIT1 0))) = (((S x0) = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))) (NUMERAL 0)).
Definition term91 := and ((fun y0 : nat => ((Nat.mul (NUMERAL 0) y0) = (NUMERAL (BIT1 0))) = (((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))) (NUMERAL 0)).
Definition term179 (x0 : nat) := fun y0 : Prop => ((y0 /\ (y0 \/ (x0 = (NUMERAL 0)))) /\ (x0 = (NUMERAL 0))) = (y0 /\ (x0 = (NUMERAL 0))).
Definition term143 := Nat.add (NUMERAL 0) (NUMERAL 0).
Definition term53 (x0 : nat) := (fun y0 : nat => (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) x0.
Definition term14 := fun y0 : nat => ~ ((NUMERAL 0) = (S y0)).
Definition term153 (x0 : nat) := @eq Prop ((Nat.mul (S x0) (NUMERAL 0)) = (NUMERAL (BIT1 0))).
Definition term145 := @eq Prop ((Nat.mul (NUMERAL 0) (NUMERAL 0)) = (NUMERAL (BIT1 0))).
Definition term90 := ((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ ((NUMERAL 0) = (NUMERAL (BIT1 0))).
Definition term121 (x0 : nat) (x1 : nat) := ((S x0) = (NUMERAL (BIT1 0))) /\ (x1 = (NUMERAL (BIT1 0))).
Definition term63 := and ((fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) (NUMERAL 0)).
Definition term68 (x0 : nat) := imp (forall y0 : nat, ((Nat.mul x0 y0) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))).
Definition term64 := and (forall y0 : nat, ((Nat.mul (NUMERAL 0) y0) = (NUMERAL (BIT1 0))) = (((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))).
Definition term69 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) (S x0).
Definition term176 (x0 : nat) (x1 : nat) := @eq Prop (((x0 = (NUMERAL 0)) /\ ((x0 = (NUMERAL 0)) \/ (x1 = (NUMERAL 0)))) /\ (x1 = (NUMERAL 0))).
Definition term174 (x0 : nat) (x1 : nat) := and ((x0 = (NUMERAL 0)) /\ ((x0 = (NUMERAL 0)) \/ (x1 = (NUMERAL 0)))).
Definition term61 := (fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) (NUMERAL 0).
Definition term129 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => ((Nat.mul (S x0) y1) = (NUMERAL (BIT1 0))) = (((S x0) = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) y0) -> (fun y1 : nat => ((Nat.mul (S x0) y1) = (NUMERAL (BIT1 0))) = (((S x0) = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) (S y0).
Definition term102 := fun y0 : nat => ((fun y1 : nat => ((Nat.mul (NUMERAL 0) y1) = (NUMERAL (BIT1 0))) = (((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) y0) -> (fun y1 : nat => ((Nat.mul (NUMERAL 0) y1) = (NUMERAL (BIT1 0))) = (((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) (S y0).
Definition term140 := @eq nat (Nat.mul (NUMERAL 0) (NUMERAL 0)).
Definition term35 (x0 : nat) := Nat.add (NUMERAL 0) x0.
Definition term80 := imp ((forall y0 : nat, ((Nat.mul (NUMERAL 0) y0) = (NUMERAL (BIT1 0))) = (((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))) /\ (forall y0 : nat, (forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) -> forall y1 : nat, ((Nat.mul (S y0) y1) = (NUMERAL (BIT1 0))) = (((S y0) = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0)))))).
Definition term163 (x0 : nat) (x1 : nat) := S (Nat.add (Nat.add x0 (Nat.mul x0 x1)) x1).
Definition term158 (x0 : nat) (x1 : nat) := S (Nat.add (Nat.mul x0 (S x1)) x1).
Definition term29 (x0 : nat) (x1 : nat) := S (Nat.add x0 x1).
Definition term180 (x0 : nat) (x1 : nat) := (fun y0 : Prop => ((y0 /\ (y0 \/ (x0 = (NUMERAL 0)))) /\ (x0 = (NUMERAL 0))) = (y0 /\ (x0 = (NUMERAL 0)))) (x1 = (NUMERAL 0)).
Definition term97 (x0 : nat) := (fun y0 : nat => ((Nat.mul (NUMERAL 0) y0) = (NUMERAL (BIT1 0))) = (((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))) (S x0).
Definition term83 := forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0)))).
Definition term46 := forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1).
Definition term40 := forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)).
Definition term24 := forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)).
Definition term13 := fun y0 : nat => ~ ((S y0) = (NUMERAL 0)).
Definition term3 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) \/ (x1 = (NUMERAL 0)).
Definition term185 (x0 : nat) (x1 : nat) := @eq Prop ((((x0 = (NUMERAL 0)) /\ ((x0 = (NUMERAL 0)) \/ (x1 = (NUMERAL 0)))) /\ (x1 = (NUMERAL 0))) = ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)))).
Definition term139 (x0 : nat) := ((((Nat.mul (S x0) (NUMERAL 0)) = (NUMERAL (BIT1 0))) = (((S x0) = (NUMERAL (BIT1 0))) /\ ((NUMERAL 0) = (NUMERAL (BIT1 0))))) /\ (forall y0 : nat, (((Nat.mul (S x0) y0) = (NUMERAL (BIT1 0))) = (((S x0) = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))) -> ((Nat.mul (S x0) (S y0)) = (NUMERAL (BIT1 0))) = (((S x0) = (NUMERAL (BIT1 0))) /\ ((S y0) = (NUMERAL (BIT1 0)))))) -> forall y0 : nat, ((Nat.mul (S x0) y0) = (NUMERAL (BIT1 0))) = (((S x0) = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0)))).
Definition term112 := ((((Nat.mul (NUMERAL 0) (NUMERAL 0)) = (NUMERAL (BIT1 0))) = (((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ ((NUMERAL 0) = (NUMERAL (BIT1 0))))) /\ (forall y0 : nat, (((Nat.mul (NUMERAL 0) y0) = (NUMERAL (BIT1 0))) = (((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))) -> ((Nat.mul (NUMERAL 0) (S y0)) = (NUMERAL (BIT1 0))) = (((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ ((S y0) = (NUMERAL (BIT1 0)))))) -> forall y0 : nat, ((Nat.mul (NUMERAL 0) y0) = (NUMERAL (BIT1 0))) = (((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0)))).
Definition term142 := S (Nat.add (NUMERAL 0) (NUMERAL 0)).
Definition term184 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : Prop => ((y0 /\ (y0 \/ (x0 = (NUMERAL 0)))) /\ (x0 = (NUMERAL 0))) = (y0 /\ (x0 = (NUMERAL 0)))) (x1 = (NUMERAL 0))).
Definition term99 (x0 : nat) := ((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ ((S x0) = (NUMERAL (BIT1 0))).
Definition term33 := forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0.
Definition term122 (x0 : nat) (x1 : nat) := imp ((fun y0 : nat => ((Nat.mul (S x0) y0) = (NUMERAL (BIT1 0))) = (((S x0) = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))) x1).
Definition term34 (x0 : nat) := (fun y0 : nat => (Nat.add (NUMERAL 0) y0) = y0) x0.
Definition term48 (x0 : nat) := forall y0 : nat, (Nat.mul (S x0) y0) = (Nat.add (Nat.mul x0 y0) y0).
Definition term19 (x0 : nat) := (fun y0 : nat => (NUMERAL (BIT1 y0)) = (S (Nat.add (NUMERAL y0) (NUMERAL y0)))) x0.
Definition term11 (x0 : nat) := ~ ((S x0) = (NUMERAL 0)).
Definition term146 (x0 : nat) := @eq nat (Nat.mul (NUMERAL 0) (S x0)).
Definition term17 (x0 : nat) := (fun y0 : nat => ~ ((NUMERAL 0) = (S y0))) x0.
Definition term123 (x0 : nat) (x1 : nat) := imp (((Nat.mul (S x0) x1) = (NUMERAL (BIT1 0))) = (((S x0) = (NUMERAL (BIT1 0))) /\ (x1 = (NUMERAL (BIT1 0))))).
Definition term96 (x0 : nat) := imp (((Nat.mul (NUMERAL 0) x0) = (NUMERAL (BIT1 0))) = (((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ (x0 = (NUMERAL (BIT1 0))))).
Definition term27 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 (S y0)) = (S (Nat.add x0 y0))) x1.
Definition term74 := fun y0 : nat => (forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) -> forall y1 : nat, ((Nat.mul (S y0) y1) = (NUMERAL (BIT1 0))) = (((S y0) = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0)))).
Definition term73 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = (NUMERAL (BIT1 0))) = ((y1 = (NUMERAL (BIT1 0))) /\ (y2 = (NUMERAL (BIT1 0))))) y0) -> (fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = (NUMERAL (BIT1 0))) = ((y1 = (NUMERAL (BIT1 0))) /\ (y2 = (NUMERAL (BIT1 0))))) (S y0).
Definition term191 (x0 : nat) := and (True /\ (True \/ (x0 = (NUMERAL 0)))).
Definition term159 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 (S x1)).
Definition term38 := (forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))).
Definition term22 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term197 (x0 : nat) := @eq Prop ((False /\ (False \/ (x0 = (NUMERAL 0)))) /\ (x0 = (NUMERAL 0))).
Definition term192 (x0 : nat) := @eq Prop ((True /\ (True \/ (x0 = (NUMERAL 0)))) /\ (x0 = (NUMERAL 0))).
Definition term165 (x0 : nat) (x1 : nat) := @eq nat (S (Nat.add (Nat.add x0 (Nat.mul x0 x1)) x1)).
Definition term78 := (forall y0 : nat, ((Nat.mul (NUMERAL 0) y0) = (NUMERAL (BIT1 0))) = (((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))) /\ (forall y0 : nat, (forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) -> forall y1 : nat, ((Nat.mul (S y0) y1) = (NUMERAL (BIT1 0))) = (((S y0) = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))).
Definition term149 (x0 : nat) := @eq nat (S x0).
Definition term187 (x0 : nat) := (False /\ (False \/ (x0 = (NUMERAL 0)))) /\ (x0 = (NUMERAL 0)).
Definition term150 (x0 : nat) := False /\ ((S x0) = (S (NUMERAL 0))).
Definition term181 (x0 : nat) := (fun y0 : Prop => ((y0 /\ (y0 \/ (x0 = (NUMERAL 0)))) /\ (x0 = (NUMERAL 0))) = (y0 /\ (x0 = (NUMERAL 0)))) True.
Definition term162 (x0 : nat) (x1 : nat) := Nat.add (Nat.add x0 (Nat.mul x0 x1)) x1.
Definition term94 (x0 : nat) := ((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ (x0 = (NUMERAL (BIT1 0))).
Definition term119 (x0 : nat) := and (((Nat.mul (S x0) (NUMERAL 0)) = (NUMERAL (BIT1 0))) = (((S x0) = (NUMERAL (BIT1 0))) /\ ((NUMERAL 0) = (NUMERAL (BIT1 0))))).
Definition term92 := and (((Nat.mul (NUMERAL 0) (NUMERAL 0)) = (NUMERAL (BIT1 0))) = (((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ ((NUMERAL 0) = (NUMERAL (BIT1 0))))).
Definition term81 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = (NUMERAL (BIT1 0))) = ((y1 = (NUMERAL (BIT1 0))) /\ (y2 = (NUMERAL (BIT1 0))))) y0.
Definition term195 (x0 : nat) := False \/ (x0 = (NUMERAL 0)).
Definition term65 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) x0.
Definition term47 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) x0.
Definition term41 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))) x0.
Definition term25 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))) x0.
Definition term8 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((S y0) = (S y1)) = (y0 = y1)) x0.
Definition term4 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.add y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) x0.
Definition term190 (x0 : nat) := True \/ (x0 = (NUMERAL 0)).
Definition term52 := forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0).
Definition term51 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 x1) x1.
Definition term186 (x0 : nat) := (fun y0 : Prop => ((y0 /\ (y0 \/ (x0 = (NUMERAL 0)))) /\ (x0 = (NUMERAL 0))) = (y0 /\ (x0 = (NUMERAL 0)))) False.
Definition term77 := ((fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = (NUMERAL (BIT1 0))) = ((y1 = (NUMERAL (BIT1 0))) /\ (y2 = (NUMERAL (BIT1 0))))) y0) -> (fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = (NUMERAL (BIT1 0))) = ((y1 = (NUMERAL (BIT1 0))) /\ (y2 = (NUMERAL (BIT1 0))))) (S y0)).
Definition term45 (x0 : nat) (x1 : nat) := Nat.add x0 (Nat.mul x0 x1).
Definition term54 (x0 : nat) := Nat.mul x0 (NUMERAL 0).
Definition term160 (x0 : nat) (x1 : nat) := Nat.add (Nat.add x0 (Nat.mul x0 x1)).
Definition term28 (x0 : nat) (x1 : nat) := Nat.add x0 (S x1).
Definition term157 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 (S x1)) (S x1).
Definition term18 (x0 : nat) := (~ ((NUMERAL 0) = (S x0))) -> ((NUMERAL 0) = (S x0)) = False.
Definition term167 (x0 : nat) (x1 : nat) := @eq Prop ((S (Nat.add (Nat.add x0 (Nat.mul x0 x1)) x1)) = (S (NUMERAL 0))).
Definition term136 (x0 : nat) := imp ((((Nat.mul (S x0) (NUMERAL 0)) = (NUMERAL (BIT1 0))) = (((S x0) = (NUMERAL (BIT1 0))) /\ ((NUMERAL 0) = (NUMERAL (BIT1 0))))) /\ (forall y0 : nat, (((Nat.mul (S x0) y0) = (NUMERAL (BIT1 0))) = (((S x0) = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))) -> ((Nat.mul (S x0) (S y0)) = (NUMERAL (BIT1 0))) = (((S x0) = (NUMERAL (BIT1 0))) /\ ((S y0) = (NUMERAL (BIT1 0)))))).
Definition term109 := imp ((((Nat.mul (NUMERAL 0) (NUMERAL 0)) = (NUMERAL (BIT1 0))) = (((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ ((NUMERAL 0) = (NUMERAL (BIT1 0))))) /\ (forall y0 : nat, (((Nat.mul (NUMERAL 0) y0) = (NUMERAL (BIT1 0))) = (((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))) -> ((Nat.mul (NUMERAL 0) (S y0)) = (NUMERAL (BIT1 0))) = (((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ ((S y0) = (NUMERAL (BIT1 0)))))).
Definition term177 (x0 : nat) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) (x0 = (NUMERAL 0)).
Definition term134 (x0 : nat) := (((Nat.mul (S x0) (NUMERAL 0)) = (NUMERAL (BIT1 0))) = (((S x0) = (NUMERAL (BIT1 0))) /\ ((NUMERAL 0) = (NUMERAL (BIT1 0))))) /\ (forall y0 : nat, (((Nat.mul (S x0) y0) = (NUMERAL (BIT1 0))) = (((S x0) = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))) -> ((Nat.mul (S x0) (S y0)) = (NUMERAL (BIT1 0))) = (((S x0) = (NUMERAL (BIT1 0))) /\ ((S y0) = (NUMERAL (BIT1 0))))).
Definition term107 := (((Nat.mul (NUMERAL 0) (NUMERAL 0)) = (NUMERAL (BIT1 0))) = (((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ ((NUMERAL 0) = (NUMERAL (BIT1 0))))) /\ (forall y0 : nat, (((Nat.mul (NUMERAL 0) y0) = (NUMERAL (BIT1 0))) = (((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))) -> ((Nat.mul (NUMERAL 0) (S y0)) = (NUMERAL (BIT1 0))) = (((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ ((S y0) = (NUMERAL (BIT1 0))))).
Definition term116 (x0 : nat) := Nat.mul (S x0) (NUMERAL 0).
Definition term88 := Nat.mul (NUMERAL 0) (NUMERAL 0).
Definition term132 (x0 : nat) := forall y0 : nat, (((Nat.mul (S x0) y0) = (NUMERAL (BIT1 0))) = (((S x0) = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))) -> ((Nat.mul (S x0) (S y0)) = (NUMERAL (BIT1 0))) = (((S x0) = (NUMERAL (BIT1 0))) /\ ((S y0) = (NUMERAL (BIT1 0)))).
Definition term105 := forall y0 : nat, (((Nat.mul (NUMERAL 0) y0) = (NUMERAL (BIT1 0))) = (((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))) -> ((Nat.mul (NUMERAL 0) (S y0)) = (NUMERAL (BIT1 0))) = (((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ ((S y0) = (NUMERAL (BIT1 0)))).
Definition term57 (x0 : nat) := Nat.mul (NUMERAL 0) x0.
Definition term115 (x0 : nat) := (fun y0 : nat => ((Nat.mul (S x0) y0) = (NUMERAL (BIT1 0))) = (((S x0) = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))) (NUMERAL 0).
Definition term87 := (fun y0 : nat => ((Nat.mul (NUMERAL 0) y0) = (NUMERAL (BIT1 0))) = (((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))) (NUMERAL 0).
Definition term95 (x0 : nat) := imp ((fun y0 : nat => ((Nat.mul (NUMERAL 0) y0) = (NUMERAL (BIT1 0))) = (((NUMERAL 0) = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))) x0).
Definition term161 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 (S x1)) x1.
Definition term71 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) x0) -> (fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) (S x0).
Definition term148 := and ((NUMERAL 0) = (NUMERAL (BIT1 0))).
Definition term10 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((S x0) = (S y0)) = (x0 = y0)) x1.
Definition term82 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = (NUMERAL (BIT1 0))) = ((y1 = (NUMERAL (BIT1 0))) /\ (y2 = (NUMERAL (BIT1 0))))) y0.
Definition term164 (x0 : nat) (x1 : nat) := @eq nat (Nat.mul (S x0) (S x1)).
Definition term36 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term20 (x0 : nat) := NUMERAL (BIT1 x0).
Definition term172 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) /\ ((x0 = (NUMERAL 0)) \/ (x1 = (NUMERAL 0))).
Definition term173 (x0 : nat) (x1 : nat) := and ((Nat.add x0 (Nat.mul x0 x1)) = (NUMERAL 0)).
Definition term193 (x0 : nat) := @eq Prop (x0 = (NUMERAL 0)).
Definition term170 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) /\ ((Nat.mul x0 x1) = (NUMERAL 0)).
Definition term60 := fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0)))).
Definition term178 (x0 : nat) := ((x0 = (NUMERAL 0)) = True) \/ ((x0 = (NUMERAL 0)) = False).
Definition term89 := NUMERAL (BIT1 0).
Definition term125 (x0 : nat) (x1 : nat) := Nat.mul (S x0) (S x1).
Definition term72 (x0 : nat) := (forall y0 : nat, ((Nat.mul x0 y0) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))) -> forall y0 : nat, ((Nat.mul (S x0) y0) = (NUMERAL (BIT1 0))) = (((S x0) = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0)))).
Definition term6 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.add x0 y0) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) x1.
Definition term26 (x0 : nat) := forall y0 : nat, (Nat.add x0 (S y0)) = (S (Nat.add x0 y0)).
