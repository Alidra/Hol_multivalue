Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term64 := Peano.lt (NUMERAL (BIT1 0)).
Definition term10 (x0 : nat) (x1 : nat) := exists y0 : nat, (Peano.le x0 y0) /\ (Peano.lt y0 x1).
Definition term125 := ~ (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False).
Definition term93 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.lt (Nat.mul x0 y0) (Nat.mul x1 y0)) = ((Peano.lt x0 x1) /\ (~ (y0 = (NUMERAL 0))))) x2.
Definition term8 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) /\ (Peano.lt x1 x2).
Definition term157 (x0 : nat) (x1 : nat) (x2 : nat) := or (~ ((Peano.lt x0 x1) /\ (~ (x2 = (NUMERAL 0))))).
Definition term181 := (~ False) -> False.
Definition term131 := ~ (forall y0 : nat, ~ (Peano.lt y0 (NUMERAL 0))).
Definition term11 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le x0 y0) /\ (Peano.lt y0 x1).
Definition term51 (x0 : nat) (x1 : nat) := (((Peano.lt x0 x1) /\ (~ ((NUMERAL 0) = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 (NUMERAL 0)) (Nat.pow x1 (NUMERAL 0))) /\ (forall y0 : nat, (((Peano.lt x0 x1) /\ (~ (y0 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 y0) (Nat.pow x1 y0)) -> ((Peano.lt x0 x1) /\ (~ ((S y0) = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 (S y0)) (Nat.pow x1 (S y0))).
Definition term35 (x0 : nat) (x1 : nat) := ((Peano.lt x0 x1) /\ (~ ((NUMERAL 0) = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 (NUMERAL 0)) (Nat.pow x1 (NUMERAL 0)).
Definition term177 (x0 : nat) := @eq Prop (~ (x0 = (NUMERAL 0))).
Definition term160 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ (Peano.lt x0 x1)) \/ (x2 = (NUMERAL 0))) \/ (Peano.lt (Nat.pow x0 x2) (Nat.pow x1 x2)).
Definition term185 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (((Peano.lt y2 y1) /\ (~ (y0 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y2 y0) (Nat.pow y1 y0)) -> (Peano.lt y2 y1) -> ((y1 = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0)))) -> (forall y3 : nat, (Peano.lt y3 (NUMERAL 0)) = False) -> False) x0.
Definition term96 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.mul y0 y1) (Nat.mul y0 y2)) = ((y0 = (NUMERAL 0)) \/ (Peano.le y1 y2))) x0.
Definition term89 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.mul y0 y2) (Nat.mul y1 y2)) = ((Peano.lt y0 y1) /\ (~ (y2 = (NUMERAL 0))))) x0.
Definition term82 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le y0 y1) -> Peano.le (Nat.pow y0 y2) (Nat.pow y1 y2)) x0.
Definition term2 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.lt y1 y2)) -> Peano.lt y0 y2) x0.
Definition term158 (x0 : nat) (x1 : nat) (x2 : nat) := or ((~ (Peano.lt x0 x1)) \/ (x2 = (NUMERAL 0))).
Definition term86 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le x0 x1) -> Peano.le (Nat.pow x0 y0) (Nat.pow x1 y0)) x2.
Definition term151 (x0 : nat) (x1 : nat) := or (~ (Peano.lt x0 x1)).
Definition term43 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.lt x0 x1) /\ (~ ((S x2) = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 (S x2)) (Nat.pow x1 (S x2)).
Definition term15 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.lt y1 y2)) -> Peano.lt y0 y2) -> forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.lt y2 y1)) -> Peano.lt y0 y1.
Definition term112 (x0 : nat) := (x0 = (NUMERAL 0)) \/ True.
Definition term102 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (NUMERAL 0)) \/ (Peano.le x1 x2).
Definition term191 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.pow x1 x2).
Definition term65 (x0 : nat) (x1 : nat) := Peano.lt (Nat.pow x0 (NUMERAL 0)) (Nat.pow x1 (NUMERAL 0)).
Definition term132 (x0 : nat) (x1 : nat) := imp ((x0 = (NUMERAL 0)) /\ (~ (x1 = (NUMERAL 0)))).
Definition term20 (x0 : nat) := forall y0 : nat, (Nat.pow x0 (S y0)) = (Nat.mul x0 (Nat.pow x0 y0)).
Definition term182 := (~ ((NUMERAL 0) = (NUMERAL 0))) -> (NUMERAL 0) = (NUMERAL 0).
Definition term47 (x0 : nat) (x1 : nat) := fun y0 : nat => (((Peano.lt x0 x1) /\ (~ (y0 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 y0) (Nat.pow x1 y0)) -> ((Peano.lt x0 x1) /\ (~ ((S y0) = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 (S y0)) (Nat.pow x1 (S y0)).
Definition term76 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt x0 x1) -> Peano.lt (Nat.mul x0 (Nat.pow x0 x2)) (Nat.mul x1 (Nat.pow x1 x2)).
Definition term118 (x0 : nat) (x1 : nat) := True /\ (~ ((x0 = (NUMERAL 0)) /\ (~ (x1 = (NUMERAL 0))))).
Definition term55 (x0 : nat) (x1 : nat) := forall y0 : nat, (fun y1 : nat => ((Peano.lt x0 x1) /\ (~ (y1 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 y1) (Nat.pow x1 y1)) y0.
Definition term50 (x0 : nat) (x1 : nat) := ((fun y0 : nat => ((Peano.lt x0 x1) /\ (~ (y0 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 y0) (Nat.pow x1 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Peano.lt x0 x1) /\ (~ (y1 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 y1) (Nat.pow x1 y1)) y0) -> (fun y1 : nat => ((Peano.lt x0 x1) /\ (~ (y1 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 y1) (Nat.pow x1 y1)) (S y0)).
Definition term45 (x0 : nat) (x1 : nat) (x2 : nat) := (((Peano.lt x0 x1) /\ (~ (x2 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 x2) (Nat.pow x1 x2)) -> ((Peano.lt x0 x1) /\ (~ ((S x2) = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 (S x2)) (Nat.pow x1 (S x2)).
Definition term108 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (NUMERAL 0)) \/ (Peano.le (Nat.pow x0 x2) (Nat.pow x1 x2)).
Definition term13 (x0 : nat) := forall y0 : nat, (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.lt y1 y0)) -> Peano.lt x0 y0.
Definition term22 (x0 : nat) (x1 : nat) := Nat.pow x0 (S x1).
Definition term173 := fun y0 : nat => ~ (y0 = (NUMERAL 0)).
Definition term179 (x0 : Prop) := (~ x0) -> x0.
Definition term32 (x0 : nat) (x1 : nat) := (((fun y0 : nat => ((Peano.lt x0 x1) /\ (~ (y0 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 y0) (Nat.pow x1 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Peano.lt x0 x1) /\ (~ (y1 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 y1) (Nat.pow x1 y1)) y0) -> (fun y1 : nat => ((Peano.lt x0 x1) /\ (~ (y1 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 y1) (Nat.pow x1 y1)) (S y0))) -> forall y0 : nat, (fun y1 : nat => ((Peano.lt x0 x1) /\ (~ (y1 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 y1) (Nat.pow x1 y1)) y0.
Definition term21 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.pow x0 (S y0)) = (Nat.mul x0 (Nat.pow x0 y0))) x1.
Definition term0 := forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False.
Definition term137 (x0 : nat) (x1 : nat) (x2 : nat) := (((Peano.lt x0 x1) /\ (~ (x2 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 x2) (Nat.pow x1 x2)) -> (Peano.lt x0 x1) -> ((x1 = (NUMERAL 0)) /\ (~ (x2 = (NUMERAL 0)))) -> ~ (forall y0 : nat, ~ (Peano.lt y0 (NUMERAL 0))).
Definition term88 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.pow x0 x2) (Nat.pow x1 x2).
Definition term26 (x0 : nat) := Nat.pow x0 (NUMERAL 0).
Definition term31 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term33 (x0 : nat) (x1 : nat) := fun y0 : nat => ((Peano.lt x0 x1) /\ (~ (y0 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 y0) (Nat.pow x1 y0).
Definition term156 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt (Nat.pow x0 x2) (Nat.pow x1 x2).
Definition term52 (x0 : nat) (x1 : nat) := imp (((fun y0 : nat => ((Peano.lt x0 x1) /\ (~ (y0 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 y0) (Nat.pow x1 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Peano.lt x0 x1) /\ (~ (y1 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 y1) (Nat.pow x1 y1)) y0) -> (fun y1 : nat => ((Peano.lt x0 x1) /\ (~ (y1 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 y1) (Nat.pow x1 y1)) (S y0))).
Definition term154 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((Peano.lt x0 x1) /\ (~ (x2 = (NUMERAL 0)))).
Definition term34 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Peano.lt x0 x1) /\ (~ (y0 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 y0) (Nat.pow x1 y0)) (NUMERAL 0).
Definition term37 (x0 : nat) (x1 : nat) := and (((Peano.lt x0 x1) /\ (~ ((NUMERAL 0) = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 (NUMERAL 0)) (Nat.pow x1 (NUMERAL 0))).
Definition term58 := ~ ((NUMERAL 0) = (NUMERAL 0)).
Definition term186 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (((Peano.lt y1 y0) /\ (~ (x0 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y1 x0) (Nat.pow y0 x0)) -> (Peano.lt y1 y0) -> ((y0 = (NUMERAL 0)) /\ (~ (x0 = (NUMERAL 0)))) -> (forall y2 : nat, (Peano.lt y2 (NUMERAL 0)) = False) -> False) x1.
Definition term98 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.mul x0 y0) (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (Peano.le y0 y1))) x1.
Definition term91 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt (Nat.mul x0 y1) (Nat.mul y0 y1)) = ((Peano.lt x0 y0) /\ (~ (y1 = (NUMERAL 0))))) x1.
Definition term84 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le x0 y0) -> Peano.le (Nat.pow x0 y1) (Nat.pow y0 y1)) x1.
Definition term4 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.lt y0 y1)) -> Peano.lt x0 y1) x1.
Definition term122 (x0 : nat) (x1 : nat) (x2 : nat) := (((((Peano.lt x0 x1) /\ (~ (x2 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 x2) (Nat.pow x1 x2)) -> (Peano.lt x0 x1) -> ((x1 = (NUMERAL 0)) /\ (~ (x2 = (NUMERAL 0)))) -> (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) -> False) -> (((Peano.lt x0 x1) /\ (~ (x2 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 x2) (Nat.pow x1 x2)) -> (Peano.lt x0 x1) -> ((x1 = (NUMERAL 0)) /\ (~ (x2 = (NUMERAL 0)))) -> (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) -> False) -> (((Peano.lt x0 x1) /\ (~ (x2 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 x2) (Nat.pow x1 x2)) -> (Peano.lt x0 x1) -> ((x1 = (NUMERAL 0)) /\ (~ (x2 = (NUMERAL 0)))) -> (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) -> False.
Definition term121 (x0 : nat) (x1 : nat) (x2 : nat) := ((((Peano.lt x0 x1) /\ (~ (x2 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 x2) (Nat.pow x1 x2)) -> (Peano.lt x0 x1) -> ((x1 = (NUMERAL 0)) /\ (~ (x2 = (NUMERAL 0)))) -> (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) -> False) -> (((Peano.lt x0 x1) /\ (~ (x2 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 x2) (Nat.pow x1 x2)) -> (Peano.lt x0 x1) -> ((x1 = (NUMERAL 0)) /\ (~ (x2 = (NUMERAL 0)))) -> (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) -> False.
Definition term169 (x0 : nat) (x1 : nat) := (fun y0 : nat => ~ (Peano.lt x0 y0)) x1.
Definition term176 (x0 : nat) := @eq Prop ((fun y0 : nat => ~ (y0 = (NUMERAL 0))) x0).
Definition term48 (x0 : nat) (x1 : nat) := forall y0 : nat, ((fun y1 : nat => ((Peano.lt x0 x1) /\ (~ (y1 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 y1) (Nat.pow x1 y1)) y0) -> (fun y1 : nat => ((Peano.lt x0 x1) /\ (~ (y1 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 y1) (Nat.pow x1 y1)) (S y0).
Definition term155 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term164 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.lt x0 y0) x1.
Definition term133 (x0 : nat) (x1 : nat) := ((x0 = (NUMERAL 0)) /\ (~ (x1 = (NUMERAL 0)))) -> (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) -> False.
Definition term39 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.lt x0 x1) /\ (~ (x2 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 x2) (Nat.pow x1 x2).
Definition term183 := ((NUMERAL 0) = (NUMERAL 0)) -> False.
Definition term129 := fun y0 : nat => ~ (Peano.lt y0 (NUMERAL 0)).
Definition term124 := (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) -> False.
Definition term130 := forall y0 : nat, ~ (Peano.lt y0 (NUMERAL 0)).
Definition term36 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => ((Peano.lt x0 x1) /\ (~ (y0 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 y0) (Nat.pow x1 y0)) (NUMERAL 0)).
Definition term162 (x0 : nat) := (fun y0 : nat => ~ (Peano.lt y0 (NUMERAL 0))) x0.
Definition term174 (x0 : nat) := (fun y0 : nat => ~ (y0 = (NUMERAL 0))) x0.
Definition term81 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) /\ (~ (x1 = (NUMERAL 0))).
Definition term85 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le x0 x1) -> Peano.le (Nat.pow x0 y0) (Nat.pow x1 y0).
Definition term123 (x0 : nat) (x1 : nat) (x2 : nat) := (((((Peano.lt x0 x1) /\ (~ (x2 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 x2) (Nat.pow x1 x2)) -> (Peano.lt x0 x1) -> ((x1 = (NUMERAL 0)) /\ (~ (x2 = (NUMERAL 0)))) -> (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) -> False) -> (((Peano.lt x0 x1) /\ (~ (x2 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 x2) (Nat.pow x1 x2)) -> (Peano.lt x0 x1) -> ((x1 = (NUMERAL 0)) /\ (~ (x2 = (NUMERAL 0)))) -> (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) -> False) -> ((((Peano.lt x0 x1) /\ (~ (x2 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 x2) (Nat.pow x1 x2)) -> (Peano.lt x0 x1) -> ((x1 = (NUMERAL 0)) /\ (~ (x2 = (NUMERAL 0)))) -> (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) -> False) -> (((Peano.lt x0 x1) /\ (~ (x2 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 x2) (Nat.pow x1 x2)) -> (Peano.lt x0 x1) -> ((x1 = (NUMERAL 0)) /\ (~ (x2 = (NUMERAL 0)))) -> (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) -> False.
Definition term6 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Peano.le x1 x0) /\ (Peano.lt x0 y0)) -> Peano.lt x1 y0) x2.
Definition term12 (x0 : nat) (x1 : nat) := (exists y0 : nat, (Peano.le x0 y0) /\ (Peano.lt y0 x1)) -> Peano.lt x0 x1.
Definition term167 (x0 : nat) (x1 : nat) := @eq Prop (Peano.lt x0 x1).
Definition term77 (x0 : nat) (x1 : nat) (x2 : nat) := (exists y0 : nat, (Peano.le (Nat.mul x0 (Nat.pow x0 x2)) y0) /\ (Peano.lt y0 (Nat.mul x1 (Nat.pow x1 x2)))) -> Peano.lt (Nat.mul x0 (Nat.pow x0 x2)) (Nat.mul x1 (Nat.pow x1 x2)).
Definition term127 (x0 : nat) := ~ (Peano.lt x0 (NUMERAL 0)).
Definition term25 (x0 : nat) := (fun y0 : nat => (Nat.pow y0 (NUMERAL 0)) = (NUMERAL (BIT1 0))) x0.
Definition term46 (x0 : nat) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => ((Peano.lt x0 x1) /\ (~ (y1 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 y1) (Nat.pow x1 y1)) y0) -> (fun y1 : nat => ((Peano.lt x0 x1) /\ (~ (y1 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 y1) (Nat.pow x1 y1)) (S y0).
Definition term94 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt (Nat.mul x0 x2) (Nat.mul x1 x2).
Definition term54 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => ((Peano.lt x0 x1) /\ (~ (y1 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 y1) (Nat.pow x1 y1)) y0.
Definition term42 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Peano.lt x0 x1) /\ (~ (y0 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 y0) (Nat.pow x1 y0)) (S x2).
Definition term111 (x0 : nat) := or (x0 = (NUMERAL 0)).
Definition term193 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (~ (y2 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y0 y2) (Nat.pow y1 y2).
Definition term192 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.lt x0 y0) /\ (~ (y1 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 y1) (Nat.pow y0 y1).
Definition term149 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (((Peano.lt y2 y1) /\ (~ (y0 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y2 y0) (Nat.pow y1 y0)) -> (Peano.lt y2 y1) -> ((y1 = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0)))) -> ~ (forall y3 : nat, ~ (Peano.lt y3 (NUMERAL 0))).
Definition term148 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (((Peano.lt y2 y1) /\ (~ (y0 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y2 y0) (Nat.pow y1 y0)) -> (Peano.lt y2 y1) -> ((y1 = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0)))) -> (forall y3 : nat, (Peano.lt y3 (NUMERAL 0)) = False) -> False.
Definition term145 (x0 : nat) := forall y0 : nat, forall y1 : nat, (((Peano.lt y1 y0) /\ (~ (x0 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y1 x0) (Nat.pow y0 x0)) -> (Peano.lt y1 y0) -> ((y0 = (NUMERAL 0)) /\ (~ (x0 = (NUMERAL 0)))) -> ~ (forall y2 : nat, ~ (Peano.lt y2 (NUMERAL 0))).
Definition term144 (x0 : nat) := forall y0 : nat, forall y1 : nat, (((Peano.lt y1 y0) /\ (~ (x0 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y1 x0) (Nat.pow y0 x0)) -> (Peano.lt y1 y0) -> ((y0 = (NUMERAL 0)) /\ (~ (x0 = (NUMERAL 0)))) -> (forall y2 : nat, (Peano.lt y2 (NUMERAL 0)) = False) -> False.
Definition term97 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.mul x0 y0) (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (Peano.le y0 y1)).
Definition term90 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.mul x0 y1) (Nat.mul y0 y1)) = ((Peano.lt x0 y0) /\ (~ (y1 = (NUMERAL 0)))).
Definition term83 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le x0 y0) -> Peano.le (Nat.pow x0 y1) (Nat.pow y0 y1).
Definition term18 := forall y0 : nat, forall y1 : nat, (Nat.pow y0 (S y1)) = (Nat.mul y0 (Nat.pow y0 y1)).
Definition term14 := forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.lt y2 y1)) -> Peano.lt y0 y1.
Definition term3 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.lt y0 y1)) -> Peano.lt x0 y1.
Definition term1 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.lt y1 y2)) -> Peano.lt y0 y2.
Definition term80 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.pow x0 y0) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0))))) x1.
Definition term113 (x0 : nat) (x1 : nat) (x2 : nat) := and (Peano.le (Nat.mul x0 (Nat.pow x0 x2)) (Nat.mul x0 (Nat.pow x1 x2))).
Definition term114 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt (Nat.mul x0 (Nat.pow x1 x2)) (Nat.mul x1 (Nat.pow x1 x2)).
Definition term75 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt (Nat.mul x0 (Nat.pow x0 x2)) (Nat.mul x1 (Nat.pow x1 x2)).
Definition term166 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : nat => Peano.lt x0 y0) x1).
Definition term175 := (fun y0 : nat => ~ (y0 = (NUMERAL 0))) (NUMERAL 0).
Definition term57 (x0 : nat) (x1 : nat) := ((((Peano.lt x0 x1) /\ (~ ((NUMERAL 0) = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 (NUMERAL 0)) (Nat.pow x1 (NUMERAL 0))) /\ (forall y0 : nat, (((Peano.lt x0 x1) /\ (~ (y0 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 y0) (Nat.pow x1 y0)) -> ((Peano.lt x0 x1) /\ (~ ((S y0) = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 (S y0)) (Nat.pow x1 (S y0)))) -> forall y0 : nat, ((Peano.lt x0 x1) /\ (~ (y0 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 y0) (Nat.pow x1 y0).
Definition term105 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 y0) -> Peano.le x0 y0) x1.
Definition term87 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) -> Peano.le (Nat.pow x0 x2) (Nat.pow x1 x2).
Definition term23 (x0 : nat) (x1 : nat) := Nat.mul x0 (Nat.pow x0 x1).
Definition term117 (x0 : nat) (x1 : nat) := ~ ((x0 = (NUMERAL 0)) /\ (~ (x1 = (NUMERAL 0)))).
Definition term99 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.mul x0 x1) (Nat.mul x0 y0)) = ((x0 = (NUMERAL 0)) \/ (Peano.le x1 y0)).
Definition term163 (x0 : nat) := fun y0 : nat => Peano.lt x0 y0.
Definition term29 (x0 : nat) := ~ ((S x0) = (NUMERAL 0)).
Definition term101 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x1 x0) (Nat.mul x1 x2).
Definition term71 (x0 : nat) (x1 : nat) := imp (Peano.lt x0 x1).
Definition term165 (x0 : nat) := (fun y0 : nat => Peano.lt x0 y0) (NUMERAL 0).
Definition term153 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.lt x0 x1)) \/ (x2 = (NUMERAL 0)).
Definition term184 := (forall y0 : nat, ~ (Peano.lt y0 (NUMERAL 0))) -> False.
Definition term41 (x0 : nat) (x1 : nat) (x2 : nat) := imp (((Peano.lt x0 x1) /\ (~ (x2 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 x2) (Nat.pow x1 x2)).
Definition term59 (x0 : nat) (x1 : nat) := and (Peano.lt x0 x1).
Definition term189 (x0 : nat) (x1 : nat) (x2 : nat) := exists y0 : nat, (Peano.le (Nat.mul x0 (Nat.pow x0 x2)) y0) /\ (Peano.lt y0 (Nat.mul x1 (Nat.pow x1 x2))).
Definition term70 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((Peano.lt x0 x1) /\ (~ ((S x2) = (NUMERAL 0)))).
Definition term62 (x0 : nat) (x1 : nat) := imp ((Peano.lt x0 x1) /\ (~ ((NUMERAL 0) = (NUMERAL 0)))).
Definition term5 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.le x1 x0) /\ (Peano.lt x0 y0)) -> Peano.lt x1 y0.
Definition term187 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (((Peano.lt y0 x0) /\ (~ (x1 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y0 x1) (Nat.pow x0 x1)) -> (Peano.lt y0 x0) -> ((x0 = (NUMERAL 0)) /\ (~ (x1 = (NUMERAL 0)))) -> (forall y1 : nat, (Peano.lt y1 (NUMERAL 0)) = False) -> False) x2.
Definition term66 := Peano.lt (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term152 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.lt x0 x1)) \/ (~ (~ (x2 = (NUMERAL 0)))).
Definition term139 (x0 : nat) (x1 : nat) := fun y0 : nat => (((Peano.lt y0 x0) /\ (~ (x1 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y0 x1) (Nat.pow x0 x1)) -> (Peano.lt y0 x0) -> ((x0 = (NUMERAL 0)) /\ (~ (x1 = (NUMERAL 0)))) -> ~ (forall y1 : nat, ~ (Peano.lt y1 (NUMERAL 0))).
Definition term9 (x0 : nat) (x1 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.lt y1 y2)) -> Peano.lt y0 y2) -> Peano.lt x0 x1.
Definition term168 (x0 : nat) := fun y0 : nat => ~ (Peano.lt x0 y0).
Definition term171 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : nat => ~ (Peano.lt x0 y0)) x1).
Definition term126 (x0 : nat) := Peano.lt x0 (NUMERAL 0).
Definition term73 (x0 : nat) (x1 : nat) := Peano.lt (Nat.mul x0 (Nat.pow x0 x1)).
Definition term109 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) -> (Peano.le (Nat.pow x0 x2) (Nat.pow x1 x2)) = True.
Definition term161 (x0 : nat) (x1 : nat) := ~ (Peano.lt x0 x1).
Definition term72 (x0 : nat) (x1 : nat) := Peano.lt (Nat.pow x0 (S x1)).
Definition term134 (x0 : nat) (x1 : nat) := ((x0 = (NUMERAL 0)) /\ (~ (x1 = (NUMERAL 0)))) -> ~ (forall y0 : nat, ~ (Peano.lt y0 (NUMERAL 0))).
Definition term61 (x0 : nat) (x1 : nat) := (Peano.lt x0 x1) /\ False.
Definition term103 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) x0.
Definition term78 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) x0.
Definition term19 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.pow y0 (S y1)) = (Nat.mul y0 (Nat.pow y0 y1))) x0.
Definition term16 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.lt y2 y1)) -> Peano.lt y0 y1) x0.
Definition term28 (x0 : nat) := (fun y0 : nat => ~ ((S y0) = (NUMERAL 0))) x0.
Definition term24 := forall y0 : nat, (Nat.pow y0 (NUMERAL 0)) = (NUMERAL (BIT1 0)).
Definition term120 (x0 : nat) (x1 : nat) (x2 : nat) := (((Peano.lt x0 x1) /\ (~ (x2 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 x2) (Nat.pow x1 x2)) -> (Peano.lt x0 x1) -> ((x1 = (NUMERAL 0)) /\ (~ (x2 = (NUMERAL 0)))) -> (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) -> False.
Definition term56 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.lt x0 x1) /\ (~ (y0 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 y0) (Nat.pow x1 y0).
Definition term74 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt (Nat.pow x0 (S x2)) (Nat.pow x1 (S x2)).
Definition term110 (x0 : nat) (x1 : nat) := (Peano.lt x0 x1) -> (Peano.le x0 x1) = True.
Definition term190 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => (Peano.le (Nat.mul x0 (Nat.pow x0 x2)) y0) /\ (Peano.lt y0 (Nat.mul x1 (Nat.pow x1 x2))).
Definition term128 := fun y0 : nat => (Peano.lt y0 (NUMERAL 0)) = False.
Definition term100 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le (Nat.mul x0 x1) (Nat.mul x0 y0)) = ((x0 = (NUMERAL 0)) \/ (Peano.le x1 y0))) x2.
Definition term7 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x1 x0) /\ (Peano.lt x0 x2)) -> Peano.lt x1 x2.
Definition term95 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt x0 x1) /\ (~ (x2 = (NUMERAL 0))).
Definition term159 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((Peano.lt x0 x1) /\ (~ (x2 = (NUMERAL 0))))) \/ (Peano.lt (Nat.pow x0 x2) (Nat.pow x1 x2)).
Definition term135 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt x0 x1) -> ((x1 = (NUMERAL 0)) /\ (~ (x2 = (NUMERAL 0)))) -> (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) -> False.
Definition term30 (x0 : nat) := (~ ((S x0) = (NUMERAL 0))) -> ((S x0) = (NUMERAL 0)) = False.
Definition term138 (x0 : nat) (x1 : nat) := fun y0 : nat => (((Peano.lt y0 x0) /\ (~ (x1 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y0 x1) (Nat.pow x0 x1)) -> (Peano.lt y0 x0) -> ((x0 = (NUMERAL 0)) /\ (~ (x1 = (NUMERAL 0)))) -> (forall y1 : nat, (Peano.lt y1 (NUMERAL 0)) = False) -> False.
Definition term53 (x0 : nat) (x1 : nat) := imp ((((Peano.lt x0 x1) /\ (~ ((NUMERAL 0) = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 (NUMERAL 0)) (Nat.pow x1 (NUMERAL 0))) /\ (forall y0 : nat, (((Peano.lt x0 x1) /\ (~ (y0 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 y0) (Nat.pow x1 y0)) -> ((Peano.lt x0 x1) /\ (~ ((S y0) = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 (S y0)) (Nat.pow x1 (S y0)))).
Definition term188 (x0 : nat) (x1 : nat) := ((x0 = (NUMERAL 0)) /\ (~ (x1 = (NUMERAL 0)))) -> False.
Definition term63 (x0 : nat) := Peano.lt (Nat.pow x0 (NUMERAL 0)).
Definition term178 (x0 : nat) := (~ (Peano.lt x0 (NUMERAL 0))) -> Peano.lt x0 (NUMERAL 0).
Definition term116 (x0 : nat) (x1 : nat) := ~ ((Nat.pow x0 x1) = (NUMERAL 0)).
Definition term141 (x0 : nat) (x1 : nat) := forall y0 : nat, (((Peano.lt y0 x0) /\ (~ (x1 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y0 x1) (Nat.pow x0 x1)) -> (Peano.lt y0 x0) -> ((x0 = (NUMERAL 0)) /\ (~ (x1 = (NUMERAL 0)))) -> ~ (forall y1 : nat, ~ (Peano.lt y1 (NUMERAL 0))).
Definition term140 (x0 : nat) (x1 : nat) := forall y0 : nat, (((Peano.lt y0 x0) /\ (~ (x1 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y0 x1) (Nat.pow x0 x1)) -> (Peano.lt y0 x0) -> ((x0 = (NUMERAL 0)) /\ (~ (x1 = (NUMERAL 0)))) -> (forall y1 : nat, (Peano.lt y1 (NUMERAL 0)) = False) -> False.
Definition term49 (x0 : nat) (x1 : nat) := forall y0 : nat, (((Peano.lt x0 x1) /\ (~ (y0 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 y0) (Nat.pow x1 y0)) -> ((Peano.lt x0 x1) /\ (~ ((S y0) = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 (S y0)) (Nat.pow x1 (S y0)).
Definition term44 (x0 : nat) (x1 : nat) (x2 : nat) := ((fun y0 : nat => ((Peano.lt x0 x1) /\ (~ (y0 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 y0) (Nat.pow x1 y0)) x2) -> (fun y0 : nat => ((Peano.lt x0 x1) /\ (~ (y0 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 y0) (Nat.pow x1 y0)) (S x2).
Definition term106 (x0 : nat) (x1 : nat) := (Peano.lt x0 x1) -> Peano.le x0 x1.
Definition term40 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((fun y0 : nat => ((Peano.lt x0 x1) /\ (~ (y0 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 y0) (Nat.pow x1 y0)) x2).
Definition term104 (x0 : nat) := forall y0 : nat, (Peano.lt x0 y0) -> Peano.le x0 y0.
Definition term150 (x0 : nat) := ~ (~ (x0 = (NUMERAL 0))).
Definition term119 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le (Nat.mul x0 (Nat.pow x0 x2)) (Nat.mul x0 (Nat.pow x1 x2))) /\ (Peano.lt (Nat.mul x0 (Nat.pow x1 x2)) (Nat.mul x1 (Nat.pow x1 x2))).
Definition term67 := False -> Peano.lt (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term180 (x0 : nat) := (Peano.lt x0 (NUMERAL 0)) -> False.
Definition term38 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Peano.lt x0 x1) /\ (~ (y0 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 y0) (Nat.pow x1 y0)) x2.
Definition term69 (x0 : nat) (x1 : nat) := (Peano.lt x0 x1) /\ True.
Definition term172 (x0 : nat) (x1 : nat) := @eq Prop (~ (Peano.lt x0 x1)).
Definition term136 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt x0 x1) -> ((x1 = (NUMERAL 0)) /\ (~ (x2 = (NUMERAL 0)))) -> ~ (forall y0 : nat, ~ (Peano.lt y0 (NUMERAL 0))).
Definition term170 (x0 : nat) := (fun y0 : nat => ~ (Peano.lt x0 y0)) (NUMERAL 0).
Definition term143 (x0 : nat) := fun y0 : nat => forall y1 : nat, (((Peano.lt y1 y0) /\ (~ (x0 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y1 x0) (Nat.pow y0 x0)) -> (Peano.lt y1 y0) -> ((y0 = (NUMERAL 0)) /\ (~ (x0 = (NUMERAL 0)))) -> ~ (forall y2 : nat, ~ (Peano.lt y2 (NUMERAL 0))).
Definition term142 (x0 : nat) := fun y0 : nat => forall y1 : nat, (((Peano.lt y1 y0) /\ (~ (x0 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y1 x0) (Nat.pow y0 x0)) -> (Peano.lt y1 y0) -> ((y0 = (NUMERAL 0)) /\ (~ (x0 = (NUMERAL 0)))) -> (forall y2 : nat, (Peano.lt y2 (NUMERAL 0)) = False) -> False.
Definition term27 := NUMERAL (BIT1 0).
Definition term107 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x0 (Nat.pow x0 x2)) (Nat.mul x0 (Nat.pow x1 x2)).
Definition term147 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (((Peano.lt y2 y1) /\ (~ (y0 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y2 y0) (Nat.pow y1 y0)) -> (Peano.lt y2 y1) -> ((y1 = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0)))) -> ~ (forall y3 : nat, ~ (Peano.lt y3 (NUMERAL 0))).
Definition term146 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (((Peano.lt y2 y1) /\ (~ (y0 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y2 y0) (Nat.pow y1 y0)) -> (Peano.lt y2 y1) -> ((y1 = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0)))) -> (forall y3 : nat, (Peano.lt y3 (NUMERAL 0)) = False) -> False.
Definition term17 (x0 : nat) (x1 : nat) := (fun y0 : nat => (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.lt y1 y0)) -> Peano.lt x0 y0) x1.
Definition term92 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.lt (Nat.mul x0 y0) (Nat.mul x1 y0)) = ((Peano.lt x0 x1) /\ (~ (y0 = (NUMERAL 0)))).
Definition term79 (x0 : nat) := forall y0 : nat, ((Nat.pow x0 y0) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0)))).
Definition term115 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt x0 x1) /\ (~ ((Nat.pow x1 x2) = (NUMERAL 0))).
Definition term68 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt x0 x1) /\ (~ ((S x2) = (NUMERAL 0))).
Definition term60 (x0 : nat) (x1 : nat) := (Peano.lt x0 x1) /\ (~ ((NUMERAL 0) = (NUMERAL 0))).
