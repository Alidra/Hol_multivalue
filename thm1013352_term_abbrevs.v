Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term135 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term149 := (~ False) -> False.
Definition term100 (x0 : nat) := fun y0 : nat => (Nat.add x0 y0) = (Nat.add y0 x0).
Definition term140 (x0 : Prop) := ~ (~ x0).
Definition term134 (x0 : nat) (x1 : nat) := ((S x0) = (S x1)) \/ (~ (x0 = x1)).
Definition term50 (x0 : nat) (x1 : nat) := and (Peano.le (S (Nat.add x0 x1)) x1).
Definition term21 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) /\ (Peano.le x0 x1).
Definition term131 (x0 : nat) (x1 : nat) := (~ ((Nat.add x1 x0) = (Nat.add x0 x1))) -> (Nat.add x1 x0) = (Nat.add x0 x1).
Definition term83 (x0 : nat) (x1 : nat) := (~ ((exists y0 : nat, (S (Nat.add x0 x1)) = (S (Nat.add x1 y0))) \/ (exists y0 : nat, x1 = (S (S (Nat.add (Nat.add x0 x1) y0)))))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> False.
Definition term121 (x0 : nat) (x1 : nat) := and (~ (exists y0 : nat, (S (Nat.add x0 x1)) = (S (Nat.add x1 y0)))).
Definition term41 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : nat => ((NUMERAL y0) = (NUMERAL x0)) = False) x1).
Definition term67 (x0 : nat) (x1 : nat) := or (exists y0 : nat, (S (Nat.add x0 x1)) = (S (Nat.add x1 y0))).
Definition term79 (x0 : nat) (x1 : nat) := (exists y0 : nat, (S (Nat.add x0 x1)) = (S (Nat.add x1 y0))) \/ (exists y0 : nat, x1 = (S (S (Nat.add (Nat.add x0 x1) y0)))).
Definition term144 (x0 : nat) (x1 : nat) := ((Nat.add x1 x0) = (Nat.add x0 x1)) -> (S (Nat.add x1 x0)) = (S (Nat.add x0 x1)).
Definition term85 (x0 : nat) (x1 : nat) := (((~ ((exists y0 : nat, (S (Nat.add x0 x1)) = (S (Nat.add x1 y0))) \/ (exists y0 : nat, x1 = (S (S (Nat.add (Nat.add x0 x1) y0)))))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> False) -> (~ ((exists y0 : nat, (S (Nat.add x0 x1)) = (S (Nat.add x1 y0))) \/ (exists y0 : nat, x1 = (S (S (Nat.add (Nat.add x0 x1) y0)))))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> False) -> (~ ((exists y0 : nat, (S (Nat.add x0 x1)) = (S (Nat.add x1 y0))) \/ (exists y0 : nat, x1 = (S (S (Nat.add (Nat.add x0 x1) y0)))))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> False.
Definition term69 (x0 : nat) (x1 : nat) := Peano.lt (S (Nat.add x0 x1)) x1.
Definition term80 (x0 : Prop) := (~ x0) -> False.
Definition term119 (x0 : nat) (x1 : nat) := fun y0 : nat => ~ (x1 = (S (S (Nat.add (Nat.add x0 x1) y0)))).
Definition term1 := (forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))).
Definition term22 (x0 : nat) := fun y0 : nat => ((Peano.le x0 y0) /\ (Peano.le y0 x0)) = (x0 = y0).
Definition term90 (x0 : nat) (x1 : nat) := imp (~ ((exists y0 : nat, (S (Nat.add x0 x1)) = (S (Nat.add x1 y0))) \/ (exists y0 : nat, x1 = (S (S (Nat.add (Nat.add x0 x1) y0)))))).
Definition term24 (x0 : nat) := forall y0 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 x0)) = (x0 = y0).
Definition term152 (x0 : nat) (x1 : nat) (x2 : nat) := ((S (Nat.add x0 x2)) = x1) -> ((NUMERAL x1) = (NUMERAL x2)) = False.
Definition term146 (x0 : nat) (x1 : nat) := ~ ((S (Nat.add x1 x0)) = (S (Nat.add x0 x1))).
Definition term109 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((S (Nat.add x0 x1)) = (S (Nat.add x1 x2))).
Definition term124 (x0 : nat) (x1 : nat) := (forall y0 : nat, ~ ((S (Nat.add x0 x1)) = (S (Nat.add x1 y0)))) /\ (forall y0 : nat, ~ (x1 = (S (S (Nat.add (Nat.add x0 x1) y0))))).
Definition term51 (x0 : nat) := Peano.le (NUMERAL x0).
Definition term71 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (S (Nat.add x0 x1)) (S x2).
Definition term46 (x0 : nat) (x1 : nat) := Peano.le (S (Nat.add x0 x1)).
Definition term14 (x0 : nat) := forall y0 : nat, (Peano.lt x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 (S y1))).
Definition term107 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (S (Nat.add x0 x1)) = (S (Nat.add x1 y0))) x2.
Definition term138 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term117 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (x1 = (S (S (Nat.add (Nat.add x0 x1) x2)))).
Definition term88 := ~ (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)).
Definition term32 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => ((~ (x0 /\ y0)) = ((~ x0) \/ (~ y0))) /\ ((~ (x0 \/ y0)) = ((~ x0) /\ (~ y0)))) x1.
Definition term122 (x0 : nat) (x1 : nat) := and (forall y0 : nat, ~ ((S (Nat.add x0 x1)) = (S (Nat.add x1 y0)))).
Definition term76 (x0 : nat) (x1 : nat) := fun y0 : nat => x1 = (Nat.add (S (Nat.add x0 x1)) (S y0)).
Definition term57 (x0 : Prop) (x1 : Prop) := (~ x0) \/ (~ x1).
Definition term133 (x0 : Prop) := (~ x0) -> x0.
Definition term33 (x0 : Prop) (x1 : Prop) := ((~ (x0 /\ x1)) = ((~ x0) \/ (~ x1))) /\ ((~ (x0 \/ x1)) = ((~ x0) /\ (~ x1))).
Definition term23 (x0 : nat) := fun y0 : nat => (x0 = y0) = ((Peano.le x0 y0) /\ (Peano.le y0 x0)).
Definition term10 (x0 : nat) := forall y0 : nat, (Nat.add (S x0) y0) = (S (Nat.add x0 y0)).
Definition term30 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((~ (y0 /\ y1)) = ((~ y0) \/ (~ y1))) /\ ((~ (y0 \/ y1)) = ((~ y0) /\ (~ y1)))) x0.
Definition term56 (x0 : Prop) (x1 : Prop) := ~ (x0 /\ x1).
Definition term31 (x0 : Prop) := forall y0 : Prop, ((~ (x0 /\ y0)) = ((~ x0) \/ (~ y0))) /\ ((~ (x0 \/ y0)) = ((~ x0) /\ (~ y0))).
Definition term137 (x0 : nat) (x1 : nat) := @eq Prop (((S x0) = (S x1)) \/ (~ (x0 = x1))).
Definition term102 := fun y0 : nat => forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0).
Definition term26 := fun y0 : nat => forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1).
Definition term93 (x0 : nat) := fun y0 : nat => (~ ((exists y1 : nat, (S (Nat.add y0 x0)) = (S (Nat.add x0 y1))) \/ (exists y1 : nat, x0 = (S (S (Nat.add (Nat.add y0 x0) y1)))))) -> ~ (forall y1 : nat, forall y2 : nat, (Nat.add y1 y2) = (Nat.add y2 y1)).
Definition term44 (x0 : nat) (x1 : nat) := (Peano.le (NUMERAL (S (Nat.add x0 x1))) (NUMERAL x1)) /\ (Peano.le (NUMERAL x1) (NUMERAL (S (Nat.add x0 x1)))).
Definition term20 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term87 := (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> False.
Definition term58 (x0 : nat) (x1 : nat) := (~ (Peano.le (S (Nat.add x0 x1)) x1)) \/ (~ (Peano.le x1 (S (Nat.add x0 x1)))).
Definition term75 (x0 : nat) (x1 : nat) (x2 : nat) := S (S (Nat.add (Nat.add x0 x1) x2)).
Definition term11 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add (S x0) y0) = (S (Nat.add x0 y0))) x1.
Definition term72 (x0 : nat) (x1 : nat) (x2 : nat) := S (Nat.add (Nat.add x0 x1) (S x2)).
Definition term143 (x0 : nat) (x1 : nat) := imp (x0 = x1).
Definition term74 (x0 : nat) (x1 : nat) (x2 : nat) := S (Nat.add (Nat.add x0 x1) x2).
Definition term36 (x0 : nat) := (fun y0 : nat => (NUMERAL y0) = y0) x0.
Definition term60 (x0 : nat) (x1 : nat) := Peano.lt x1 (S (Nat.add x0 x1)).
Definition term35 (x0 : nat) (x1 : nat) := (fun y0 : nat => (x0 = y0) = ((Peano.le x0 y0) /\ (Peano.le y0 x0))) x1.
Definition term7 (x0 : nat) (x1 : nat) := S (Nat.add x0 x1).
Definition term120 (x0 : nat) (x1 : nat) := forall y0 : nat, ~ (x1 = (S (S (Nat.add (Nat.add x0 x1) y0)))).
Definition term99 := forall y0 : nat, forall y1 : nat, (~ ((exists y2 : nat, (S (Nat.add y1 y0)) = (S (Nat.add y0 y2))) \/ (exists y2 : nat, y0 = (S (S (Nat.add (Nat.add y1 y0) y2)))))) -> ~ (forall y2 : nat, forall y3 : nat, (Nat.add y2 y3) = (Nat.add y3 y2)).
Definition term98 := forall y0 : nat, forall y1 : nat, (~ ((exists y2 : nat, (S (Nat.add y1 y0)) = (S (Nat.add y0 y2))) \/ (exists y2 : nat, y0 = (S (S (Nat.add (Nat.add y1 y0) y2)))))) -> (forall y2 : nat, forall y3 : nat, (Nat.add y2 y3) = (Nat.add y3 y2)) -> False.
Definition term89 := forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0).
Definition term29 := forall y0 : nat, forall y1 : nat, (y0 = y1) = ((Peano.le y0 y1) /\ (Peano.le y1 y0)).
Definition term28 := forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1).
Definition term8 := forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1)).
Definition term2 := forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)).
Definition term116 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((fun y0 : nat => x1 = (S (S (Nat.add (Nat.add x0 x1) y0)))) x2).
Definition term108 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((fun y0 : nat => (S (Nat.add x0 x1)) = (S (Nat.add x1 y0))) x2).
Definition term103 (x0 : nat -> Prop) := ~ (ex x0).
Definition term18 (x0 : nat) := forall y0 : nat, (~ (Peano.le x0 y0)) = (Peano.lt y0 x0).
Definition term48 (x0 : nat) (x1 : nat) := Peano.le (S (Nat.add x0 x1)) x1.
Definition term145 (x0 : nat) (x1 : nat) := (~ ((S (Nat.add x1 x0)) = (S (Nat.add x0 x1)))) -> (S (Nat.add x1 x0)) = (S (Nat.add x0 x1)).
Definition term104 (x0 : nat -> Prop) := forall y0 : nat, ~ (x0 y0).
Definition term45 (x0 : nat) (x1 : nat) := Peano.le (NUMERAL (S (Nat.add x0 x1))).
Definition term38 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((NUMERAL y0) = (NUMERAL x0)) = False) x1.
Definition term127 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ~ ((S (Nat.add x0 x1)) = (S (Nat.add x1 y0)))) x2.
Definition term111 (x0 : nat) (x1 : nat) := fun y0 : nat => ~ ((S (Nat.add x0 x1)) = (S (Nat.add x1 y0))).
Definition term78 (x0 : nat) (x1 : nat) := exists y0 : nat, x1 = (S (S (Nat.add (Nat.add x0 x1) y0))).
Definition term63 (x0 : nat) (x1 : nat) := fun y0 : nat => (S (Nat.add x0 x1)) = (Nat.add x1 (S y0)).
Definition term151 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ ((exists y1 : nat, (S (Nat.add y0 x0)) = (S (Nat.add x0 y1))) \/ (exists y1 : nat, x0 = (S (S (Nat.add (Nat.add y0 x0) y1)))))) -> (forall y1 : nat, forall y2 : nat, (Nat.add y1 y2) = (Nat.add y2 y1)) -> False) x1.
Definition term16 (x0 : nat) (x1 : nat) := exists y0 : nat, x0 = (Nat.add x1 (S y0)).
Definition term101 (x0 : nat) := forall y0 : nat, (Nat.add x0 y0) = (Nat.add y0 x0).
Definition term43 (x0 : nat) (x1 : nat) := ~ ((NUMERAL (S (Nat.add x0 x1))) = (NUMERAL x1)).
Definition term94 (x0 : nat) := forall y0 : nat, (~ ((exists y1 : nat, (S (Nat.add y0 x0)) = (S (Nat.add x0 y1))) \/ (exists y1 : nat, x0 = (S (S (Nat.add (Nat.add y0 x0) y1)))))) -> (forall y1 : nat, forall y2 : nat, (Nat.add y1 y2) = (Nat.add y2 y1)) -> False.
Definition term5 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 (S y0)) = (S (Nat.add x0 y0))) x1.
Definition term126 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 y0) = (Nat.add y0 x0)) x1.
Definition term0 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term115 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => x1 = (S (S (Nat.add (Nat.add x0 x1) y0)))) x2.
Definition term114 (x0 : nat) (x1 : nat) := forall y0 : nat, ~ ((fun y1 : nat => x1 = (S (S (Nat.add (Nat.add x0 x1) y1)))) y0).
Definition term106 (x0 : nat) (x1 : nat) := forall y0 : nat, ~ ((fun y1 : nat => (S (Nat.add x0 x1)) = (S (Nat.add x1 y1))) y0).
Definition term150 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ ((exists y2 : nat, (S (Nat.add y1 y0)) = (S (Nat.add y0 y2))) \/ (exists y2 : nat, y0 = (S (S (Nat.add (Nat.add y1 y0) y2)))))) -> (forall y2 : nat, forall y3 : nat, (Nat.add y2 y3) = (Nat.add y3 y2)) -> False) x0.
Definition term125 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) x0.
Definition term34 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (y0 = y1) = ((Peano.le y0 y1) /\ (Peano.le y1 y0))) x0.
Definition term17 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) x0.
Definition term13 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 (S y2)))) x0.
Definition term9 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) x0.
Definition term3 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))) x0.
Definition term62 (x0 : nat) (x1 : nat) := @eq nat (S (Nat.add x0 x1)).
Definition term59 (x0 : nat) (x1 : nat) := ~ (Peano.le (S (Nat.add x0 x1)) x1).
Definition term84 (x0 : nat) (x1 : nat) := ((~ ((exists y0 : nat, (S (Nat.add x0 x1)) = (S (Nat.add x1 y0))) \/ (exists y0 : nat, x1 = (S (S (Nat.add (Nat.add x0 x1) y0)))))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> False) -> (~ ((exists y0 : nat, (S (Nat.add x0 x1)) = (S (Nat.add x1 y0))) \/ (exists y0 : nat, x1 = (S (S (Nat.add (Nat.add x0 x1) y0)))))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> False.
Definition term37 (x0 : nat) := fun y0 : nat => ((NUMERAL y0) = (NUMERAL x0)) = False.
Definition term82 (x0 : nat) (x1 : nat) := ~ ((exists y0 : nat, (S (Nat.add x0 x1)) = (S (Nat.add x1 y0))) \/ (exists y0 : nat, x1 = (S (S (Nat.add (Nat.add x0 x1) y0))))).
Definition term77 (x0 : nat) (x1 : nat) := fun y0 : nat => x1 = (S (S (Nat.add (Nat.add x0 x1) y0))).
Definition term65 (x0 : nat) (x1 : nat) := exists y0 : nat, (S (Nat.add x0 x1)) = (S (Nat.add x1 y0)).
Definition term42 (x0 : nat) (x1 : nat) := @eq Prop (((NUMERAL x0) = (NUMERAL x1)) = False).
Definition term25 (x0 : nat) := forall y0 : nat, (x0 = y0) = ((Peano.le x0 y0) /\ (Peano.le y0 x0)).
Definition term128 (x0 : nat) (x1 : nat) := (x0 = x1) -> (S x0) = (S x1).
Definition term6 (x0 : nat) (x1 : nat) := Nat.add x0 (S x1).
Definition term40 (x0 : nat) (x1 : nat) := NUMERAL (S (Nat.add x0 x1)).
Definition term47 (x0 : nat) (x1 : nat) := Peano.le (NUMERAL (S (Nat.add x0 x1))) (NUMERAL x1).
Definition term68 (x0 : nat) (x1 : nat) := ~ (Peano.le x1 (S (Nat.add x0 x1))).
Definition term129 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term91 (x0 : nat) (x1 : nat) := (~ ((exists y0 : nat, (S (Nat.add x0 x1)) = (S (Nat.add x1 y0))) \/ (exists y0 : nat, x1 = (S (S (Nat.add (Nat.add x0 x1) y0)))))) -> ~ (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)).
Definition term139 (x0 : nat) (x1 : nat) := (~ (~ (x0 = x1))) -> (S x0) = (S x1).
Definition term132 (x0 : nat) (x1 : nat) := ~ ((Nat.add x1 x0) = (Nat.add x0 x1)).
Definition term55 (x0 : nat) (x1 : nat) := ~ ((Peano.le (S (Nat.add x0 x1)) x1) /\ (Peano.le x1 (S (Nat.add x0 x1)))).
Definition term49 (x0 : nat) (x1 : nat) := and (Peano.le (NUMERAL (S (Nat.add x0 x1))) (NUMERAL x1)).
Definition term112 (x0 : nat) (x1 : nat) := forall y0 : nat, ~ ((S (Nat.add x0 x1)) = (S (Nat.add x1 y0))).
Definition term39 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((NUMERAL y0) = (NUMERAL x1)) = False) (S (Nat.add x0 x1)).
Definition term97 := fun y0 : nat => forall y1 : nat, (~ ((exists y2 : nat, (S (Nat.add y1 y0)) = (S (Nat.add y0 y2))) \/ (exists y2 : nat, y0 = (S (S (Nat.add (Nat.add y1 y0) y2)))))) -> ~ (forall y2 : nat, forall y3 : nat, (Nat.add y2 y3) = (Nat.add y3 y2)).
Definition term136 (x0 : nat) (x1 : nat) := @eq Prop ((~ (x0 = x1)) \/ ((S x0) = (S x1))).
Definition term130 (x0 : nat) (x1 : nat) := (~ (x0 = x1)) \/ ((S x0) = (S x1)).
Definition term118 (x0 : nat) (x1 : nat) := fun y0 : nat => ~ ((fun y1 : nat => x1 = (S (S (Nat.add (Nat.add x0 x1) y1)))) y0).
Definition term110 (x0 : nat) (x1 : nat) := fun y0 : nat => ~ ((fun y1 : nat => (S (Nat.add x0 x1)) = (S (Nat.add x1 y1))) y0).
Definition term52 (x0 : nat) (x1 : nat) := Peano.le (NUMERAL x1) (NUMERAL (S (Nat.add x0 x1))).
Definition term123 (x0 : nat) (x1 : nat) := (~ (exists y0 : nat, (S (Nat.add x0 x1)) = (S (Nat.add x1 y0)))) /\ (~ (exists y0 : nat, x1 = (S (S (Nat.add (Nat.add x0 x1) y0))))).
Definition term53 (x0 : nat) (x1 : nat) := Peano.le x1 (S (Nat.add x0 x1)).
Definition term64 (x0 : nat) (x1 : nat) := fun y0 : nat => (S (Nat.add x0 x1)) = (S (Nat.add x1 y0)).
Definition term81 (x0 : nat) (x1 : nat) := (~ ((exists y0 : nat, (S (Nat.add x0 x1)) = (S (Nat.add x1 y0))) \/ (exists y0 : nat, x1 = (S (S (Nat.add (Nat.add x0 x1) y0)))))) -> False.
Definition term19 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.le x0 y0)) = (Peano.lt y0 x0)) x1.
Definition term95 (x0 : nat) := forall y0 : nat, (~ ((exists y1 : nat, (S (Nat.add y0 x0)) = (S (Nat.add x0 y1))) \/ (exists y1 : nat, x0 = (S (S (Nat.add (Nat.add y0 x0) y1)))))) -> ~ (forall y1 : nat, forall y2 : nat, (Nat.add y1 y2) = (Nat.add y2 y1)).
Definition term66 (x0 : nat) (x1 : nat) := or (~ (Peano.le (S (Nat.add x0 x1)) x1)).
Definition term141 (x0 : nat) (x1 : nat) := ~ (~ (x0 = x1)).
Definition term86 (x0 : nat) (x1 : nat) := (((~ ((exists y0 : nat, (S (Nat.add x0 x1)) = (S (Nat.add x1 y0))) \/ (exists y0 : nat, x1 = (S (S (Nat.add (Nat.add x0 x1) y0)))))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> False) -> (~ ((exists y0 : nat, (S (Nat.add x0 x1)) = (S (Nat.add x1 y0))) \/ (exists y0 : nat, x1 = (S (S (Nat.add (Nat.add x0 x1) y0)))))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> False) -> ((~ ((exists y0 : nat, (S (Nat.add x0 x1)) = (S (Nat.add x1 y0))) \/ (exists y0 : nat, x1 = (S (S (Nat.add (Nat.add x0 x1) y0)))))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> False) -> (~ ((exists y0 : nat, (S (Nat.add x0 x1)) = (S (Nat.add x1 y0))) \/ (exists y0 : nat, x1 = (S (S (Nat.add (Nat.add x0 x1) y0)))))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> False.
Definition term15 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 (S y1)))) x1.
Definition term70 (x0 : nat) (x1 : nat) := exists y0 : nat, x1 = (Nat.add (S (Nat.add x0 x1)) (S y0)).
Definition term96 := fun y0 : nat => forall y1 : nat, (~ ((exists y2 : nat, (S (Nat.add y1 y0)) = (S (Nat.add y0 y2))) \/ (exists y2 : nat, y0 = (S (S (Nat.add (Nat.add y1 y0) y2)))))) -> (forall y2 : nat, forall y3 : nat, (Nat.add y2 y3) = (Nat.add y3 y2)) -> False.
Definition term54 (x0 : nat) (x1 : nat) := (Peano.le (S (Nat.add x0 x1)) x1) /\ (Peano.le x1 (S (Nat.add x0 x1))).
Definition term73 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add x0 x1) (S x2).
Definition term61 (x0 : nat) (x1 : nat) := exists y0 : nat, (S (Nat.add x0 x1)) = (Nat.add x1 (S y0)).
Definition term12 (x0 : nat) (x1 : nat) := Nat.add (S x0) x1.
Definition term113 (x0 : nat) (x1 : nat) := ~ (exists y0 : nat, x1 = (S (S (Nat.add (Nat.add x0 x1) y0)))).
Definition term105 (x0 : nat) (x1 : nat) := ~ (exists y0 : nat, (S (Nat.add x0 x1)) = (S (Nat.add x1 y0))).
Definition term27 := fun y0 : nat => forall y1 : nat, (y0 = y1) = ((Peano.le y0 y1) /\ (Peano.le y1 y0)).
Definition term92 (x0 : nat) := fun y0 : nat => (~ ((exists y1 : nat, (S (Nat.add y0 x0)) = (S (Nat.add x0 y1))) \/ (exists y1 : nat, x0 = (S (S (Nat.add (Nat.add y0 x0) y1)))))) -> (forall y1 : nat, forall y2 : nat, (Nat.add y1 y2) = (Nat.add y2 y1)) -> False.
Definition term148 (x0 : nat) (x1 : nat) := ((S (Nat.add x1 x0)) = (S (Nat.add x0 x1))) -> False.
Definition term147 (x0 : nat) (x1 : nat) (x2 : nat) := ((S (Nat.add x0 x1)) = (S (Nat.add x1 x2))) -> False.
Definition term142 (x0 : nat) (x1 : nat) := imp (~ (~ (x0 = x1))).
Definition term4 (x0 : nat) := forall y0 : nat, (Nat.add x0 (S y0)) = (S (Nat.add x0 y0)).
