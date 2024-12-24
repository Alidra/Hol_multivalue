Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term39 (x0 : nat) (x1 : nat) := exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 x1).
Definition term117 (x0 : nat) := imp (~ ((S x0) = (NUMERAL 0))).
Definition term11 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul x0 (S y0)) = (Nat.add x0 (Nat.mul x0 y0))) x1.
Definition term91 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 x1).
Definition term79 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.add (Nat.mul x0 (Nat.add x1 x2)) x3).
Definition term127 (x0 : type1606) := exists y0 : nat, forall y1 : nat, forall y2 : nat, Peano.le (x0 y1 y2) (Nat.mul y0 (Nat.add y1 y2)).
Definition term5 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term31 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) x0.
Definition term23 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul (Nat.add y0 y1) y2) = (Nat.add (Nat.mul y0 y2) (Nat.mul y1 y2))) x0.
Definition term17 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.add y0 y1) (Nat.add y0 y2)) = (Peano.le y1 y2)) x0.
Definition term21 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le (Nat.add x0 x1) (Nat.add x0 y0)) = (Peano.le x1 y0)) x2.
Definition term44 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1.
Definition term90 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y0)) x1.
Definition term10 (x0 : nat) := forall y0 : nat, (Nat.mul x0 (S y0)) = (Nat.add x0 (Nat.mul x0 y0)).
Definition term112 (x0 : nat) := Peano.le x0 (Nat.mul x0 (NUMERAL 0)).
Definition term7 := (forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))).
Definition term69 (x0 : type1606) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (exists y0 : nat, (Peano.le (x0 x3 x4) y0) /\ (Peano.le y0 (Nat.mul (Nat.add x1 x2) (Nat.add x3 x4)))) -> Peano.le (x0 x3 x4) (Nat.mul (Nat.add x1 x2) (Nat.add x3 x4)).
Definition term116 (x0 : nat) (x1 : nat) := Peano.le x0 (Nat.add x0 (Nat.mul x0 x1)).
Definition term89 (x0 : nat) := and ((~ ((NUMERAL 0) = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 (NUMERAL 0))).
Definition term20 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.add x0 x1) (Nat.add x0 y0)) = (Peano.le x1 y0).
Definition term107 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (~ (y1 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y1)) y0.
Definition term74 (x0 : type1606) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := and (Peano.le (x0 x2 x3) (Nat.add (Nat.mul x1 (Nat.add x2 x3)) x4)).
Definition term38 (x0 : nat) (x1 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> Peano.le x0 x1.
Definition term102 (x0 : nat) := ((fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (~ (y1 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y1)) y0) -> (fun y1 : nat => (~ (y1 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y1)) (S y0)).
Definition term42 (x0 : nat) := forall y0 : nat, (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) -> Peano.le x0 y0.
Definition term80 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.add (Nat.mul x0 (Nat.add x2 x3)) x1) (Nat.add (Nat.mul x0 (Nat.add x2 x3)) (Nat.mul x1 (Nat.add x2 x3))).
Definition term22 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.add x1 x0) (Nat.add x1 x2).
Definition term132 := forall y0 : type1606, forall y1 : nat, forall y2 : nat, (((y0 (NUMERAL 0) (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y3 : nat, forall y4 : nat, Peano.le (y0 y3 y4) (Nat.add (Nat.mul y1 (Nat.add y3 y4)) y2))) -> exists y3 : nat, forall y4 : nat, forall y5 : nat, Peano.le (y0 y4 y5) (Nat.mul y3 (Nat.add y4 y5)).
Definition term57 (x0 : nat) := (fun y0 : nat => Peano.le (NUMERAL 0) y0) x0.
Definition term71 (x0 : type1606) (x1 : nat) (x2 : nat) (x3 : nat) := forall y0 : nat, Peano.le (x0 x2 y0) (Nat.add (Nat.mul x1 (Nat.add x2 y0)) x3).
Definition term96 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y0)) x1) -> (fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y0)) (S x1).
Definition term86 (x0 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y0)) (NUMERAL 0).
Definition term84 (x0 : nat) := (((fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (~ (y1 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y1)) y0) -> (fun y1 : nat => (~ (y1 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y1)) (S y0))) -> forall y0 : nat, (fun y1 : nat => (~ (y1 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y1)) y0.
Definition term1 (x0 : nat) := forall y0 : nat, Peano.le x0 (Nat.add x0 y0).
Definition term83 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term35 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0) x2.
Definition term104 (x0 : nat) := imp (((fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (~ (y1 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y1)) y0) -> (fun y1 : nat => (~ (y1 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y1)) (S y0))).
Definition term51 (x0 : nat) (x1 : nat) := (fun y0 : Prop => y0 \/ (~ y0)) ((Nat.add x0 x1) = (NUMERAL 0)).
Definition term108 (x0 : nat) := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y0).
Definition term118 (x0 : nat) := (~ ((S x0) = (NUMERAL 0))) -> True.
Definition term110 := ~ ((NUMERAL 0) = (NUMERAL 0)).
Definition term48 (x0 : nat) := forall y0 : nat, ((Nat.add x0 y0) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) /\ (y0 = (NUMERAL 0))).
Definition term33 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1) x1.
Definition term25 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul (Nat.add x0 y0) y1) = (Nat.add (Nat.mul x0 y1) (Nat.mul y0 y1))) x1.
Definition term19 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.add x0 y0) (Nat.add x0 y1)) = (Peano.le y0 y1)) x1.
Definition term93 (x0 : nat) (x1 : nat) := imp ((~ (x1 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 x1)).
Definition term100 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => (~ (y1 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y1)) y0) -> (fun y1 : nat => (~ (y1 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y1)) (S y0).
Definition term50 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)).
Definition term12 (x0 : nat) (x1 : nat) := Nat.mul x0 (S x1).
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le x0 (Nat.add x0 y0)) x1.
Definition term88 (x0 : nat) := and ((fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y0)) (NUMERAL 0)).
Definition term63 := Nat.add (NUMERAL 0) (NUMERAL 0).
Definition term95 (x0 : nat) (x1 : nat) := (~ ((S x1) = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 (S x1)).
Definition term15 (x0 : nat) := (fun y0 : nat => (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) x0.
Definition term36 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x1 x0) /\ (Peano.le x0 x2)) -> Peano.le x1 x2.
Definition term81 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le x0 (Nat.mul x0 (Nat.add x1 x2)).
Definition term98 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (~ (y1 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y1)) y0) -> (fun y1 : nat => (~ (y1 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y1)) (S y0).
Definition term52 (x0 : nat) (x1 : nat) := ((Nat.add x0 x1) = (NUMERAL 0)) \/ (~ ((Nat.add x0 x1) = (NUMERAL 0))).
Definition term106 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (~ (y1 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y1)) y0.
Definition term97 (x0 : nat) (x1 : nat) := ((~ (x1 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 x1)) -> (~ ((S x1) = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 (S x1)).
Definition term65 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.mul (Nat.add x0 x1) (Nat.add x2 x3).
Definition term115 (x0 : nat) (x1 : nat) := Peano.le x0 (Nat.mul x0 (S x1)).
Definition term60 (x0 : type1606) (x1 : nat) (x2 : nat) := Peano.le (x0 x1 x2).
Definition term70 (x0 : type1606) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le (x0 y0 y1) (Nat.add (Nat.mul x1 (Nat.add y0 y1)) x2)) x3.
Definition term121 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((Nat.add x1 x2) = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 (Nat.add x1 x2)).
Definition term131 (x0 : type1606) := forall y0 : nat, forall y1 : nat, (((x0 (NUMERAL 0) (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y2 : nat, forall y3 : nat, Peano.le (x0 y2 y3) (Nat.add (Nat.mul y0 (Nat.add y2 y3)) y1))) -> exists y2 : nat, forall y3 : nat, forall y4 : nat, Peano.le (x0 y3 y4) (Nat.mul y2 (Nat.add y3 y4)).
Definition term126 (x0 : type1606) (x1 : nat) (x2 : nat) := forall y0 : nat, forall y1 : nat, Peano.le (x0 y0 y1) (Nat.mul (Nat.add x1 x2) (Nat.add y0 y1)).
Definition term55 (x0 : type1606) (x1 : nat) (x2 : nat) := forall y0 : nat, forall y1 : nat, Peano.le (x0 y0 y1) (Nat.add (Nat.mul x1 (Nat.add y0 y1)) x2).
Definition term43 := forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1.
Definition term32 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1.
Definition term30 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2.
Definition term24 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul (Nat.add x0 y0) y1) = (Nat.add (Nat.mul x0 y1) (Nat.mul y0 y1)).
Definition term18 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add x0 y0) (Nat.add x0 y1)) = (Peano.le y0 y1).
Definition term8 := forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)).
Definition term94 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y0)) (S x1).
Definition term64 (x0 : nat) (x1 : nat) := Nat.mul (Nat.add x0 x1).
Definition term27 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul (Nat.add x0 x1) y0) = (Nat.add (Nat.mul x0 y0) (Nat.mul x1 y0))) x2.
Definition term109 (x0 : nat) := (((~ ((NUMERAL 0) = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 (NUMERAL 0))) /\ (forall y0 : nat, ((~ (y0 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y0)) -> (~ ((S y0) = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 (S y0)))) -> forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y0).
Definition term92 (x0 : nat) (x1 : nat) := imp ((fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y0)) x1).
Definition term58 (x0 : nat) := Peano.le (NUMERAL 0) x0.
Definition term28 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.add x0 x1) x2.
Definition term130 (x0 : nat) (x1 : type1606) := forall y0 : nat, (((x1 (NUMERAL 0) (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y1 : nat, forall y2 : nat, Peano.le (x1 y1 y2) (Nat.add (Nat.mul x0 (Nat.add y1 y2)) y0))) -> exists y1 : nat, forall y2 : nat, forall y3 : nat, Peano.le (x1 y2 y3) (Nat.mul y1 (Nat.add y2 y3)).
Definition term29 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 x2) (Nat.mul x1 x2).
Definition term119 (x0 : nat) := ~ ((S x0) = (NUMERAL 0)).
Definition term87 (x0 : nat) := (~ ((NUMERAL 0) = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 (NUMERAL 0)).
Definition term114 (x0 : nat) := False -> Peano.le x0 (NUMERAL 0).
Definition term125 (x0 : type1606) (x1 : nat) (x2 : nat) (x3 : nat) := forall y0 : nat, Peano.le (x0 x3 y0) (Nat.mul (Nat.add x1 x2) (Nat.add x3 y0)).
Definition term122 (x0 : type1606) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := exists y0 : nat, (Peano.le (x0 x3 x4) y0) /\ (Peano.le y0 (Nat.mul (Nat.add x1 x2) (Nat.add x3 x4))).
Definition term6 := (forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))).
Definition term34 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0.
Definition term73 (x0 : type1606) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := Peano.le (x0 x2 x3) (Nat.add (Nat.mul x1 (Nat.add x2 x3)) x4).
Definition term77 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := True /\ (Peano.le (Nat.add (Nat.mul x0 (Nat.add x2 x3)) x1) (Nat.mul (Nat.add x0 x1) (Nat.add x2 x3))).
Definition term62 := Nat.add (NUMERAL 0).
Definition term99 (x0 : nat) := fun y0 : nat => ((~ (y0 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y0)) -> (~ ((S y0) = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 (S y0)).
Definition term59 (x0 : type1606) := x0 (NUMERAL 0).
Definition term72 (x0 : type1606) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (fun y0 : nat => Peano.le (x0 x2 y0) (Nat.add (Nat.mul x1 (Nat.add x2 y0)) x3)) x4.
Definition term111 := imp (~ ((NUMERAL 0) = (NUMERAL 0))).
Definition term124 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (Nat.mul x0 (Nat.add x1 x2)) x3.
Definition term123 (x0 : type1606) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := fun y0 : nat => (Peano.le (x0 x3 x4) y0) /\ (Peano.le y0 (Nat.mul (Nat.add x1 x2) (Nat.add x3 x4))).
Definition term3 (x0 : nat) (x1 : nat) := Peano.le x0 (Nat.add x0 x1).
Definition term47 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.add y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) x0.
Definition term45 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1) x0.
Definition term9 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) x0.
Definition term75 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.add (Nat.mul x0 (Nat.add x2 x3)) x1) (Nat.mul (Nat.add x0 x1) (Nat.add x2 x3)).
Definition term103 (x0 : nat) := ((~ ((NUMERAL 0) = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 (NUMERAL 0))) /\ (forall y0 : nat, ((~ (y0 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y0)) -> (~ ((S y0) = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 (S y0))).
Definition term14 := forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0).
Definition term37 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) /\ (Peano.le x1 x2).
Definition term76 (x0 : type1606) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (Peano.le (x0 x3 x4) (Nat.add (Nat.mul x1 (Nat.add x3 x4)) x2)) /\ (Peano.le (Nat.add (Nat.mul x1 (Nat.add x3 x4)) x2) (Nat.mul (Nat.add x1 x2) (Nat.add x3 x4))).
Definition term13 (x0 : nat) (x1 : nat) := Nat.add x0 (Nat.mul x0 x1).
Definition term16 (x0 : nat) := Nat.mul x0 (NUMERAL 0).
Definition term85 (x0 : nat) := fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y0).
Definition term54 (x0 : type1606) (x1 : nat) (x2 : nat) := ((x0 (NUMERAL 0) (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y0 : nat, forall y1 : nat, Peano.le (x0 y0 y1) (Nat.add (Nat.mul x1 (Nat.add y0 y1)) x2)).
Definition term26 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul (Nat.add x0 x1) y0) = (Nat.add (Nat.mul x0 y0) (Nat.mul x1 y0)).
Definition term41 (x0 : nat) (x1 : nat) := (exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 x1)) -> Peano.le x0 x1.
Definition term129 (x0 : nat) (x1 : nat) (x2 : type1606) := (((x2 (NUMERAL 0) (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y0 : nat, forall y1 : nat, Peano.le (x2 y0 y1) (Nat.add (Nat.mul x0 (Nat.add y0 y1)) x1))) -> exists y0 : nat, forall y1 : nat, forall y2 : nat, Peano.le (x2 y1 y2) (Nat.mul y0 (Nat.add y1 y2)).
Definition term105 (x0 : nat) := imp (((~ ((NUMERAL 0) = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 (NUMERAL 0))) /\ (forall y0 : nat, ((~ (y0 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y0)) -> (~ ((S y0) = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 (S y0)))).
Definition term82 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.add x1 x2).
Definition term40 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le x0 y0) /\ (Peano.le y0 x1).
Definition term53 (x0 : nat) (x1 : nat) := ~ ((Nat.add x0 x1) = (NUMERAL 0)).
Definition term61 := Peano.le (NUMERAL 0).
Definition term66 (x0 : nat) (x1 : nat) := Nat.mul (Nat.add x0 x1) (Nat.add (NUMERAL 0) (NUMERAL 0)).
Definition term101 (x0 : nat) := forall y0 : nat, ((~ (y0 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y0)) -> (~ ((S y0) = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 (S y0)).
Definition term67 (x0 : type1606) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := Peano.le (x0 x3 x4) (Nat.mul (Nat.add x1 x2) (Nat.add x3 x4)).
Definition term56 (x0 : type1606) := x0 (NUMERAL 0) (NUMERAL 0).
Definition term113 (x0 : nat) := Peano.le x0 (NUMERAL 0).
Definition term4 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term78 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (Nat.mul x0 (Nat.add x2 x3)) (Nat.mul x1 (Nat.add x2 x3)).
Definition term68 (x0 : nat) (x1 : nat) := Peano.le (NUMERAL 0) (Nat.mul (Nat.add x0 x1) (Nat.add (NUMERAL 0) (NUMERAL 0))).
Definition term128 (x0 : type1606) := fun y0 : nat => forall y1 : nat, forall y2 : nat, Peano.le (x0 y1 y2) (Nat.mul y0 (Nat.add y1 y2)).
Definition term46 (x0 : nat) (x1 : nat) := (fun y0 : nat => (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) -> Peano.le x0 y0) x1.
Definition term49 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.add x0 y0) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) x1.
Definition term120 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y0)) (Nat.add x1 x2).
