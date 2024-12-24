Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term30 (x0 : nat) (x1 : nat) := exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 x1).
Definition term89 (x0 : nat) := forall y0 : nat, Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 y0)).
Definition term68 (x0 : nat) := (fun y0 : nat => Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 y0))) (NUMERAL 0).
Definition term104 (x0 : nat) (x1 : nat) := Factorial.fact (Nat.add x0 x1).
Definition term72 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 y0))) x1.
Definition term14 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term22 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) x0.
Definition term6 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.mul y0 y2) (Nat.mul y1 y2)) = ((Peano.le y0 y1) \/ (y2 = (NUMERAL 0)))) x0.
Definition term39 (x0 : nat) := (fun y0 : nat => (Factorial.fact (S y0)) = (Nat.mul (S y0) (Factorial.fact y0))) x0.
Definition term59 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le (Factorial.fact x0) (Factorial.fact y0)) x1.
Definition term121 (x0 : nat) (x1 : nat) := fun y0 : nat => x0 = (Nat.add x1 y0).
Definition term35 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1.
Definition term111 := S (NUMERAL 0).
Definition term44 := (forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))).
Definition term99 (x0 : nat) (x1 : nat) := (exists y0 : nat, (Peano.le (Factorial.fact x0) y0) /\ (Peano.le y0 (Nat.mul (S (Nat.add x0 x1)) (Factorial.fact (Nat.add x0 x1))))) -> Peano.le (Factorial.fact x0) (Nat.mul (S (Nat.add x0 x1)) (Factorial.fact (Nat.add x0 x1))).
Definition term11 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x0 x2) (Nat.mul x1 x2).
Definition term17 := fun y0 : nat => (Nat.mul (NUMERAL (BIT1 0)) y0) = y0.
Definition term3 (x0 : nat) := forall y0 : nat, (Peano.le (S x0) (S y0)) = (Peano.le x0 y0).
Definition term88 (x0 : nat) := forall y0 : nat, (fun y1 : nat => Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 y1))) y0.
Definition term122 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) -> Peano.le (Factorial.fact x0) (Factorial.fact x1).
Definition term29 (x0 : nat) (x1 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> Peano.le x0 x1.
Definition term10 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le (Nat.mul x0 y0) (Nat.mul x1 y0)) = ((Peano.le x0 x1) \/ (y0 = (NUMERAL 0)))) x2.
Definition term83 (x0 : nat) := ((fun y0 : nat => Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 y0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 y1))) y0) -> (fun y1 : nat => Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 y1))) (S y0)).
Definition term55 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1)).
Definition term105 (x0 : nat) (x1 : nat) := Nat.mul (NUMERAL (BIT1 0)) (Factorial.fact (Nat.add x0 x1)).
Definition term92 (x0 : nat) := Peano.le (Factorial.fact x0).
Definition term33 (x0 : nat) := forall y0 : nat, (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) -> Peano.le x0 y0.
Definition term115 (x0 : nat) (x1 : nat) := Peano.le (S (NUMERAL 0)) (S (Nat.add x0 x1)).
Definition term78 (x0 : nat) (x1 : nat) := (Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 x1))) -> Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 (S x1))).
Definition term52 (x0 : nat) := (fun y0 : nat => (Nat.add y0 (NUMERAL 0)) = y0) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => Peano.le (NUMERAL 0) y0) x0.
Definition term62 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : nat => Peano.le (Factorial.fact x0) (Factorial.fact y0)) x1).
Definition term77 (x0 : nat) (x1 : nat) := ((fun y0 : nat => Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 y0))) x1) -> (fun y0 : nat => Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 y0))) (S x1).
Definition term66 (x0 : nat) := (((fun y0 : nat => Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 y0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 y1))) y0) -> (fun y1 : nat => Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 y1))) (S y0))) -> forall y0 : nat, (fun y1 : nat => Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 y1))) y0.
Definition term123 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) -> Peano.le (Factorial.fact x0) (Factorial.fact y0).
Definition term65 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term118 (x0 : nat) (x1 : nat) := True \/ ((Factorial.fact (Nat.add x0 x1)) = (NUMERAL 0)).
Definition term96 (x0 : nat) (x1 : nat) := Peano.le (Factorial.fact x0) (Factorial.fact (S (Nat.add x0 x1))).
Definition term26 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0) x2.
Definition term85 (x0 : nat) := imp (((fun y0 : nat => Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 y0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 y1))) y0) -> (fun y1 : nat => Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 y1))) (S y0))).
Definition term91 (x0 : nat) := Factorial.fact (Nat.add x0 (NUMERAL 0)).
Definition term76 (x0 : nat) (x1 : nat) := Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 (S x1))).
Definition term53 (x0 : nat) := Nat.add x0 (NUMERAL 0).
Definition term9 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.mul x0 y0) (Nat.mul x1 y0)) = ((Peano.le x0 x1) \/ (y0 = (NUMERAL 0))).
Definition term24 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1) x1.
Definition term8 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.mul x0 y1) (Nat.mul y0 y1)) = ((Peano.le x0 y0) \/ (y1 = (NUMERAL 0)))) x1.
Definition term18 := fun y0 : nat => y0 = (Nat.mul (NUMERAL (BIT1 0)) y0).
Definition term81 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 y1))) y0) -> (fun y1 : nat => Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 y1))) (S y0).
Definition term101 (x0 : nat) (x1 : nat) := Peano.le (Factorial.fact (Nat.add x0 x1)) (Nat.mul (S (Nat.add x0 x1)) (Factorial.fact (Nat.add x0 x1))).
Definition term58 (x0 : nat) := fun y0 : nat => Peano.le (Factorial.fact x0) (Factorial.fact y0).
Definition term97 (x0 : nat) (x1 : nat) := Nat.mul (S (Nat.add x0 x1)) (Factorial.fact (Nat.add x0 x1)).
Definition term106 (x0 : nat) (x1 : nat) := Peano.le (Factorial.fact (Nat.add x0 x1)).
Definition term63 (x0 : nat) (x1 : nat) := Peano.le (Factorial.fact x0) (Factorial.fact x1).
Definition term51 := forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0.
Definition term61 (x0 : nat) (x1 : nat) := Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 x1)).
Definition term100 (x0 : nat) (x1 : nat) := and (Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 x1))).
Definition term42 (x0 : nat) := (fun y0 : nat => Peano.le y0 y0) x0.
Definition term70 (x0 : nat) := and ((fun y0 : nat => Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 y0))) (NUMERAL 0)).
Definition term102 (x0 : nat) (x1 : nat) := (Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 x1))) /\ (Peano.le (Factorial.fact (Nat.add x0 x1)) (Nat.mul (S (Nat.add x0 x1)) (Factorial.fact (Nat.add x0 x1)))).
Definition term27 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x1 x0) /\ (Peano.le x0 x2)) -> Peano.le x1 x2.
Definition term108 (x0 : nat) (x1 : nat) := Peano.le (Nat.mul (NUMERAL (BIT1 0)) (Factorial.fact (Nat.add x0 x1))) (Nat.mul (S (Nat.add x0 x1)) (Factorial.fact (Nat.add x0 x1))).
Definition term109 (x0 : nat) (x1 : nat) := (Peano.le (NUMERAL (BIT1 0)) (S (Nat.add x0 x1))) \/ ((Factorial.fact (Nat.add x0 x1)) = (NUMERAL 0)).
Definition term80 (x0 : nat) := fun y0 : nat => (Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 y0))) -> Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 (S y0))).
Definition term79 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 y1))) y0) -> (fun y1 : nat => Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 y1))) (S y0).
Definition term4 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le (S x0) (S y0)) = (Peano.le x0 y0)) x1.
Definition term57 (x0 : nat) (x1 : nat) := exists y0 : nat, x0 = (Nat.add x1 y0).
Definition term50 (x0 : nat) (x1 : nat) := S (Nat.add x0 x1).
Definition term124 := forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> Peano.le (Factorial.fact y0) (Factorial.fact y1).
Definition term45 := forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)).
Definition term34 := forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1.
Definition term23 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1.
Definition term21 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2.
Definition term7 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.mul x0 y1) (Nat.mul y0 y1)) = ((Peano.le x0 y0) \/ (y1 = (NUMERAL 0))).
Definition term64 (x0 : nat) (x1 : nat) := @eq Prop (Peano.le (Factorial.fact x0) (Factorial.fact x1)).
Definition term94 (x0 : nat) (x1 : nat) := Factorial.fact (Nat.add x0 (S x1)).
Definition term38 := forall y0 : nat, (Factorial.fact (S y0)) = (Nat.mul (S y0) (Factorial.fact y0)).
Definition term67 (x0 : nat) := fun y0 : nat => Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 y0)).
Definition term15 := forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0.
Definition term73 (x0 : nat) (x1 : nat) := imp ((fun y0 : nat => Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 y0))) x1).
Definition term1 (x0 : nat) := Peano.le (NUMERAL 0) x0.
Definition term116 (x0 : nat) (x1 : nat) := Peano.le (NUMERAL 0) (Nat.add x0 x1).
Definition term74 (x0 : nat) (x1 : nat) := imp (Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 x1))).
Definition term48 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 (S y0)) = (S (Nat.add x0 y0))) x1.
Definition term20 (x0 : nat) := (fun y0 : nat => y0 = (Nat.mul (NUMERAL (BIT1 0)) y0)) x0.
Definition term119 (x0 : nat) (x1 : nat) := exists y0 : nat, (Peano.le (Factorial.fact x0) y0) /\ (Peano.le y0 (Nat.mul (S (Nat.add x0 x1)) (Factorial.fact (Nat.add x0 x1)))).
Definition term43 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term25 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0.
Definition term84 (x0 : nat) := (Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 (NUMERAL 0)))) /\ (forall y0 : nat, (Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 y0))) -> Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 (S y0)))).
Definition term95 (x0 : nat) (x1 : nat) := Factorial.fact (S (Nat.add x0 x1)).
Definition term103 (x0 : nat) (x1 : nat) := True /\ (Peano.le (Factorial.fact (Nat.add x0 x1)) (Nat.mul (S (Nat.add x0 x1)) (Factorial.fact (Nat.add x0 x1)))).
Definition term87 (x0 : nat) := fun y0 : nat => (fun y1 : nat => Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 y1))) y0.
Definition term54 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))) x0.
Definition term46 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))) x0.
Definition term36 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1) x0.
Definition term2 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (S y0) (S y1)) = (Peano.le y0 y1)) x0.
Definition term69 (x0 : nat) := Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 (NUMERAL 0))).
Definition term93 (x0 : nat) := Peano.le (Factorial.fact x0) (Factorial.fact x0).
Definition term19 := forall y0 : nat, y0 = (Nat.mul (NUMERAL (BIT1 0)) y0).
Definition term28 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) /\ (Peano.le x1 x2).
Definition term113 := Peano.le (S (NUMERAL 0)).
Definition term114 (x0 : nat) (x1 : nat) := Peano.le (NUMERAL (BIT1 0)) (S (Nat.add x0 x1)).
Definition term107 (x0 : nat) (x1 : nat) := Peano.le (Nat.mul (NUMERAL (BIT1 0)) (Factorial.fact (Nat.add x0 x1))).
Definition term49 (x0 : nat) (x1 : nat) := Nat.add x0 (S x1).
Definition term32 (x0 : nat) (x1 : nat) := (exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 x1)) -> Peano.le x0 x1.
Definition term12 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) \/ (x2 = (NUMERAL 0)).
Definition term31 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le x0 y0) /\ (Peano.le y0 x1).
Definition term60 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le (Factorial.fact x0) (Factorial.fact y0)) (Nat.add x0 x1).
Definition term98 (x0 : nat) (x1 : nat) := Peano.le (Factorial.fact x0) (Nat.mul (S (Nat.add x0 x1)) (Factorial.fact (Nat.add x0 x1))).
Definition term41 (x0 : nat) := Nat.mul (S x0) (Factorial.fact x0).
Definition term5 (x0 : nat) (x1 : nat) := Peano.le (S x0) (S x1).
Definition term56 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1))) x1.
Definition term82 (x0 : nat) := forall y0 : nat, (Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 y0))) -> Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 (S y0))).
Definition term71 (x0 : nat) := and (Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 (NUMERAL 0)))).
Definition term75 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 y0))) (S x1).
Definition term13 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term90 (x0 : nat) := ((Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 (NUMERAL 0)))) /\ (forall y0 : nat, (Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 y0))) -> Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 (S y0))))) -> forall y0 : nat, Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 y0)).
Definition term40 (x0 : nat) := Factorial.fact (S x0).
Definition term117 (x0 : nat) (x1 : nat) := or (Peano.le (NUMERAL (BIT1 0)) (S (Nat.add x0 x1))).
Definition term110 := NUMERAL (BIT1 0).
Definition term16 (x0 : nat) := Nat.mul (NUMERAL (BIT1 0)) x0.
Definition term112 := Peano.le (NUMERAL (BIT1 0)).
Definition term120 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le (Factorial.fact x0) y0) /\ (Peano.le y0 (Nat.mul (S (Nat.add x0 x1)) (Factorial.fact (Nat.add x0 x1)))).
Definition term37 (x0 : nat) (x1 : nat) := (fun y0 : nat => (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) -> Peano.le x0 y0) x1.
Definition term86 (x0 : nat) := imp ((Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 (NUMERAL 0)))) /\ (forall y0 : nat, (Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 y0))) -> Peano.le (Factorial.fact x0) (Factorial.fact (Nat.add x0 (S y0))))).
Definition term47 (x0 : nat) := forall y0 : nat, (Nat.add x0 (S y0)) = (S (Nat.add x0 y0)).
