Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term49 (x0 : nat) := ((NUMERAL 0) = (S x0)) \/ ((x0 = (NUMERAL 0)) /\ ((NUMERAL 0) = (NUMERAL 0))).
Definition term244 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term250 (x0 : nat -> Prop) (x1 : nat) := (x1 = x1) -> x0 x1.
Definition term236 (x0 : nat -> Prop) := fun y0 : nat => x0 y0.
Definition term9 (x0 : nat) := ~ ((NUMERAL 0) = (S x0)).
Definition term98 (x0 : nat -> Prop) := forall y0 : nat, (~ (y0 = (NUMERAL 0))) \/ (x0 y0).
Definition term88 (x0 : nat -> Prop) := ~ (all x0).
Definition term157 := (~ False) -> False.
Definition term147 (x0 : nat -> Prop) (x1 : nat) := ~ (x0 x1).
Definition term235 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (fun y0 : nat => (~ (x0 = y0)) \/ (x1 y0)) x2.
Definition term212 (x0 : nat) (x1 : nat -> Prop) := @eq Prop ((x1 x0) /\ (exists y0 : nat, (x0 = y0) /\ (~ (x1 y0)))).
Definition term211 (x0 : nat) (x1 : nat -> Prop) := @eq Prop ((x1 x0) /\ (exists y0 : nat, (fun y1 : nat => (x0 = y1) /\ (~ (x1 y1))) y0)).
Definition term153 (x0 : nat -> Prop) (x1 : nat) := @eq Prop (~ (x0 x1)).
Definition term26 (x0 : nat) (x1 : nat -> Prop) := forall y0 : nat, (((S x0) = (S y0)) \/ ((y0 = (NUMERAL 0)) /\ ((S x0) = (NUMERAL 0)))) -> x1 y0.
Definition term21 (x0 : nat) (x1 : nat -> Prop) := forall y0 : nat, ((x0 = (S y0)) \/ ((y0 = (NUMERAL 0)) /\ (x0 = (NUMERAL 0)))) -> x1 y0.
Definition term184 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ~ ((x0 = x2) -> x1 x2).
Definition term34 (x0 : nat -> Prop) := ((x0 (Nat.pred (NUMERAL 0))) = (forall y0 : nat, (((NUMERAL 0) = (S y0)) \/ ((y0 = (NUMERAL 0)) /\ ((NUMERAL 0) = (NUMERAL 0)))) -> x0 y0)) /\ (forall y0 : nat, ((x0 (Nat.pred y0)) = (forall y1 : nat, ((y0 = (S y1)) \/ ((y1 = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) -> x0 y1)) -> (x0 (Nat.pred (S y0))) = (forall y1 : nat, (((S y0) = (S y1)) \/ ((y1 = (NUMERAL 0)) /\ ((S y0) = (NUMERAL 0)))) -> x0 y1)).
Definition term95 (x0 : nat -> Prop) := fun y0 : nat => (y0 = (NUMERAL 0)) /\ (~ (x0 y0)).
Definition term243 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (x0 x2) \/ (~ (x1 = x2)).
Definition term198 (x0 : nat) (x1 : nat -> Prop) := (~ (x1 x0)) /\ (forall y0 : nat, (~ (x0 = y0)) \/ (x1 y0)).
Definition term197 (x0 : nat) (x1 : nat -> Prop) := (~ (x1 x0)) /\ (forall y0 : nat, (x0 = y0) -> x1 y0).
Definition term139 (x0 : nat -> Prop) (x1 : nat) := or ((fun y0 : nat => (x0 (NUMERAL 0)) /\ ((y0 = (NUMERAL 0)) /\ (~ (x0 y0)))) x1).
Definition term80 (x0 : Prop) := ~ (~ x0).
Definition term23 (x0 : nat) (x1 : nat -> Prop) := imp ((x1 (Nat.pred x0)) = (forall y0 : nat, ((x0 = (S y0)) \/ ((y0 = (NUMERAL 0)) /\ (x0 = (NUMERAL 0)))) -> x1 y0)).
Definition term195 (x0 : nat) (x1 : nat -> Prop) := forall y0 : nat, (~ (x0 = y0)) \/ (x1 y0).
Definition term160 (x0 : nat -> Prop) (x1 : nat) := (x0 x1) \/ (~ (x1 = (NUMERAL 0))).
Definition term180 := fun y0 : nat -> Prop => forall y1 : nat, (~ ((y0 y1) = (forall y2 : nat, (y1 = y2) -> y0 y2))) -> False.
Definition term107 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (~ (forall y0 : nat, (y0 = (NUMERAL 0)) -> x0 y0))) \/ ((~ (x0 (NUMERAL 0))) /\ (forall y0 : nat, (y0 = (NUMERAL 0)) -> x0 y0)).
Definition term192 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (x0 = y0) /\ (~ (x1 y0)).
Definition term142 (x0 : nat) (x1 : nat -> Prop) := ((x1 (NUMERAL 0)) /\ ((x0 = (NUMERAL 0)) /\ (~ (x1 x0)))) \/ ((~ (x1 (NUMERAL 0))) /\ (forall y0 : nat, (~ (y0 = (NUMERAL 0))) \/ (x1 y0))).
Definition term126 (x0 : nat -> Prop) := (exists y0 : nat, (x0 (NUMERAL 0)) /\ ((y0 = (NUMERAL 0)) /\ (~ (x0 y0)))) \/ ((~ (x0 (NUMERAL 0))) /\ (forall y0 : nat, (~ (y0 = (NUMERAL 0))) \/ (x0 y0))).
Definition term218 (x0 : nat) (x1 : nat -> Prop) := or (exists y0 : nat, (x1 x0) /\ ((x0 = y0) /\ (~ (x1 y0)))).
Definition term125 (x0 : nat -> Prop) := or (exists y0 : nat, (x0 (NUMERAL 0)) /\ ((y0 = (NUMERAL 0)) /\ (~ (x0 y0)))).
Definition term150 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => ~ (x0 y0)) x1.
Definition term186 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (~ (x0 = x2)) \/ (x1 x2).
Definition term219 (x0 : nat) (x1 : nat -> Prop) := (exists y0 : nat, (x1 x0) /\ ((x0 = y0) /\ (~ (x1 y0)))) \/ ((~ (x1 x0)) /\ (forall y0 : nat, (~ (x0 = y0)) \/ (x1 y0))).
Definition term242 (x0 : nat) := ~ (x0 = x0).
Definition term53 (x0 : nat -> Prop) (x1 : nat) := (((NUMERAL 0) = (S x1)) \/ ((x1 = (NUMERAL 0)) /\ ((NUMERAL 0) = (NUMERAL 0)))) -> x0 x1.
Definition term110 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term158 := (~ ((NUMERAL 0) = (NUMERAL 0))) -> (NUMERAL 0) = (NUMERAL 0).
Definition term73 (x0 : Prop) := (~ x0) -> False.
Definition term127 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) \/ x1.
Definition term251 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => forall y1 : nat, (~ ((y0 y1) = (forall y2 : nat, (y1 = y2) -> y0 y2))) -> False) x0.
Definition term105 (x0 : nat -> Prop) := or ((x0 (NUMERAL 0)) /\ (~ (forall y0 : nat, (y0 = (NUMERAL 0)) -> x0 y0))).
Definition term66 (x0 : nat) (x1 : nat) := imp (((S x1) = (S x0)) \/ ((x0 = (NUMERAL 0)) /\ ((S x1) = (NUMERAL 0)))).
Definition term51 (x0 : nat) := imp (((NUMERAL 0) = (S x0)) \/ ((x0 = (NUMERAL 0)) /\ ((NUMERAL 0) = (NUMERAL 0)))).
Definition term4 (x0 : nat) := forall y0 : nat, ((S x0) = (S y0)) = (x0 = y0).
Definition term38 (x0 : nat -> Prop) := forall y0 : nat, (fun y1 : nat => (x0 (Nat.pred y1)) = (forall y2 : nat, ((y1 = (S y2)) \/ ((y2 = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) -> x0 y2)) y0.
Definition term99 (x0 : nat -> Prop) := and (~ (x0 (NUMERAL 0))).
Definition term208 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (fun y0 : nat => (x0 = y0) /\ (~ (x1 y0))) x2.
Definition term33 (x0 : nat -> Prop) := ((fun y0 : nat => (x0 (Nat.pred y0)) = (forall y1 : nat, ((y0 = (S y1)) \/ ((y1 = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) -> x0 y1)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (x0 (Nat.pred y1)) = (forall y2 : nat, ((y1 = (S y2)) \/ ((y2 = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) -> x0 y2)) y0) -> (fun y1 : nat => (x0 (Nat.pred y1)) = (forall y2 : nat, ((y1 = (S y2)) \/ ((y2 = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) -> x0 y2)) (S y0)).
Definition term36 (x0 : nat -> Prop) := imp (((x0 (Nat.pred (NUMERAL 0))) = (forall y0 : nat, (((NUMERAL 0) = (S y0)) \/ ((y0 = (NUMERAL 0)) /\ ((NUMERAL 0) = (NUMERAL 0)))) -> x0 y0)) /\ (forall y0 : nat, ((x0 (Nat.pred y0)) = (forall y1 : nat, ((y0 = (S y1)) \/ ((y1 = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) -> x0 y1)) -> (x0 (Nat.pred (S y0))) = (forall y1 : nat, (((S y0) = (S y1)) \/ ((y1 = (NUMERAL 0)) /\ ((S y0) = (NUMERAL 0)))) -> x0 y1))).
Definition term86 (x0 : nat -> Prop) (x1 : nat) := (x1 = (NUMERAL 0)) /\ (~ (x0 x1)).
Definition term81 := fun y0 : nat -> Prop => (~ ((y0 (NUMERAL 0)) = (forall y1 : nat, (y1 = (NUMERAL 0)) -> y0 y1))) -> False.
Definition term164 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term247 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (~ (~ (x0 = x2))) -> x1 x2.
Definition term131 (x0 : nat -> Prop) := (exists y0 : nat, (fun y1 : nat => (x0 (NUMERAL 0)) /\ ((y1 = (NUMERAL 0)) /\ (~ (x0 y1)))) y0) \/ ((~ (x0 (NUMERAL 0))) /\ (forall y0 : nat, (~ (y0 = (NUMERAL 0))) \/ (x0 y0))).
Definition term216 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (x1 x0) /\ ((x0 = y0) /\ (~ (x1 y0))).
Definition term187 (x0 : nat) (x1 : nat -> Prop) := ~ (forall y0 : nat, (x0 = y0) -> x1 y0).
Definition term90 (x0 : nat -> Prop) := ~ (forall y0 : nat, (y0 = (NUMERAL 0)) -> x0 y0).
Definition term154 (x0 : nat -> Prop) := (~ (x0 (NUMERAL 0))) -> x0 (NUMERAL 0).
Definition term129 (x0 : nat -> Prop) (x1 : Prop) := (exists y0 : nat, x0 y0) \/ x1.
Definition term109 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term203 (x0 : nat) (x1 : nat -> Prop) := or ((x1 x0) /\ (exists y0 : nat, (x0 = y0) /\ (~ (x1 y0)))).
Definition term200 (x0 : nat) (x1 : nat -> Prop) := (x1 x0) /\ (~ (forall y0 : nat, (x0 = y0) -> x1 y0)).
Definition term40 (x0 : nat -> Prop) := (((x0 (Nat.pred (NUMERAL 0))) = (forall y0 : nat, (((NUMERAL 0) = (S y0)) \/ ((y0 = (NUMERAL 0)) /\ ((NUMERAL 0) = (NUMERAL 0)))) -> x0 y0)) /\ (forall y0 : nat, ((x0 (Nat.pred y0)) = (forall y1 : nat, ((y0 = (S y1)) \/ ((y1 = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) -> x0 y1)) -> (x0 (Nat.pred (S y0))) = (forall y1 : nat, (((S y0) = (S y1)) \/ ((y1 = (NUMERAL 0)) /\ ((S y0) = (NUMERAL 0)))) -> x0 y1))) -> forall y0 : nat, (x0 (Nat.pred y0)) = (forall y1 : nat, ((y0 = (S y1)) \/ ((y1 = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) -> x0 y1).
Definition term62 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) /\ ((S x1) = (NUMERAL 0)).
Definition term155 (x0 : Prop) := (~ x0) -> x0.
Definition term27 (x0 : nat -> Prop) (x1 : nat) := ((fun y0 : nat => (x0 (Nat.pred y0)) = (forall y1 : nat, ((y0 = (S y1)) \/ ((y1 = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) -> x0 y1)) x1) -> (fun y0 : nat => (x0 (Nat.pred y0)) = (forall y1 : nat, ((y0 = (S y1)) \/ ((y1 = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) -> x0 y1)) (S x1).
Definition term146 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) \/ (x0 y0)) x1.
Definition term120 (x0 : nat -> Prop) (x1 : nat) := (x0 (NUMERAL 0)) /\ ((fun y0 : nat => (y0 = (NUMERAL 0)) /\ (~ (x0 y0))) x1).
Definition term46 (x0 : nat) := and (x0 = (NUMERAL 0)).
Definition term108 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (exists y0 : nat, (y0 = (NUMERAL 0)) /\ (~ (x0 y0)))) \/ ((~ (x0 (NUMERAL 0))) /\ (forall y0 : nat, (~ (y0 = (NUMERAL 0))) \/ (x0 y0))).
Definition term12 (x0 : nat -> Prop) := (((fun y0 : nat => (x0 (Nat.pred y0)) = (forall y1 : nat, ((y0 = (S y1)) \/ ((y1 = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) -> x0 y1)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (x0 (Nat.pred y1)) = (forall y2 : nat, ((y1 = (S y2)) \/ ((y2 = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) -> x0 y2)) y0) -> (fun y1 : nat => (x0 (Nat.pred y1)) = (forall y2 : nat, ((y1 = (S y2)) \/ ((y2 = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) -> x0 y2)) (S y0))) -> forall y0 : nat, (fun y1 : nat => (x0 (Nat.pred y1)) = (forall y2 : nat, ((y1 = (S y2)) \/ ((y2 = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) -> x0 y2)) y0.
Definition term234 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, ((x1 x0) /\ ((x0 = y0) /\ (~ (x1 y0)))) \/ ((~ (x1 x0)) /\ (forall y1 : nat, (~ (x0 = y1)) \/ (x1 y1))).
Definition term145 (x0 : nat -> Prop) := exists y0 : nat, ((x0 (NUMERAL 0)) /\ ((y0 = (NUMERAL 0)) /\ (~ (x0 y0)))) \/ ((~ (x0 (NUMERAL 0))) /\ (forall y1 : nat, (~ (y1 = (NUMERAL 0))) \/ (x0 y1))).
Definition term156 (x0 : nat -> Prop) := (x0 (NUMERAL 0)) -> False.
Definition term57 (x0 : nat -> Prop) := forall y0 : nat, (y0 = (NUMERAL 0)) -> x0 y0.
Definition term16 (x0 : nat -> Prop) := forall y0 : nat, (((NUMERAL 0) = (S y0)) \/ ((y0 = (NUMERAL 0)) /\ ((NUMERAL 0) = (NUMERAL 0)))) -> x0 y0.
Definition term241 (x0 : nat) := (~ (x0 = x0)) -> x0 = x0.
Definition term11 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term252 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => (~ ((x0 y0) = (forall y1 : nat, (y0 = y1) -> x0 y1))) -> False) x1.
Definition term121 (x0 : nat -> Prop) (x1 : nat) := (x0 (NUMERAL 0)) /\ ((x1 = (NUMERAL 0)) /\ (~ (x0 x1))).
Definition term35 (x0 : nat -> Prop) := imp (((fun y0 : nat => (x0 (Nat.pred y0)) = (forall y1 : nat, ((y0 = (S y1)) \/ ((y1 = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) -> x0 y1)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (x0 (Nat.pred y1)) = (forall y2 : nat, ((y1 = (S y2)) \/ ((y2 = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) -> x0 y2)) y0) -> (fun y1 : nat => (x0 (Nat.pred y1)) = (forall y2 : nat, ((y1 = (S y2)) \/ ((y2 = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) -> x0 y2)) (S y0))).
Definition term96 (x0 : nat -> Prop) := exists y0 : nat, (y0 = (NUMERAL 0)) /\ (~ (x0 y0)).
Definition term20 (x0 : nat -> Prop) (x1 : nat) := x0 (Nat.pred x1).
Definition term240 (x0 : nat -> Prop) (x1 : nat) := (x0 x1) -> False.
Definition term24 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => (x0 (Nat.pred y0)) = (forall y1 : nat, ((y0 = (S y1)) \/ ((y1 = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) -> x0 y1)) (S x1).
Definition term159 := ~ ((NUMERAL 0) = (NUMERAL 0)).
Definition term103 (x0 : nat -> Prop) := (x0 (NUMERAL 0)) /\ (~ (forall y0 : nat, (y0 = (NUMERAL 0)) -> x0 y0)).
Definition term102 (x0 : nat -> Prop) := and (x0 (NUMERAL 0)).
Definition term201 (x0 : nat) (x1 : nat -> Prop) := (x1 x0) /\ (exists y0 : nat, (x0 = y0) /\ (~ (x1 y0))).
Definition term31 (x0 : nat -> Prop) := forall y0 : nat, ((fun y1 : nat => (x0 (Nat.pred y1)) = (forall y2 : nat, ((y1 = (S y2)) \/ ((y2 = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) -> x0 y2)) y0) -> (fun y1 : nat => (x0 (Nat.pred y1)) = (forall y2 : nat, ((y1 = (S y2)) \/ ((y2 = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) -> x0 y2)) (S y0).
Definition term161 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term79 (x0 : nat -> Prop) := ~ (~ ((x0 (NUMERAL 0)) = (forall y0 : nat, (y0 = (NUMERAL 0)) -> x0 y0))).
Definition term222 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (fun y0 : nat => (x1 x0) /\ ((x0 = y0) /\ (~ (x1 y0)))) x2.
Definition term232 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => ((fun y1 : nat => (x1 x0) /\ ((x0 = y1) /\ (~ (x1 y1)))) y0) \/ ((~ (x1 x0)) /\ (forall y1 : nat, (~ (x0 = y1)) \/ (x1 y1))).
Definition term143 (x0 : nat -> Prop) := fun y0 : nat => ((fun y1 : nat => (x0 (NUMERAL 0)) /\ ((y1 = (NUMERAL 0)) /\ (~ (x0 y1)))) y0) \/ ((~ (x0 (NUMERAL 0))) /\ (forall y1 : nat, (~ (y1 = (NUMERAL 0))) \/ (x0 y1))).
Definition term52 (x0 : nat) := imp (x0 = (NUMERAL 0)).
Definition term112 (x0 : Prop) (x1 : nat -> Prop) := exists y0 : nat, x0 /\ (x1 y0).
Definition term239 (x0 : nat -> Prop) (x1 : nat) := (~ (x0 x1)) -> x0 x1.
Definition term17 (x0 : nat -> Prop) := and ((fun y0 : nat => (x0 (Nat.pred y0)) = (forall y1 : nat, ((y0 = (S y1)) \/ ((y1 = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) -> x0 y1)) (NUMERAL 0)).
Definition term111 (x0 : Prop) (x1 : nat -> Prop) := x0 /\ (exists y0 : nat, x1 y0).
Definition term221 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, ((fun y1 : nat => (x1 x0) /\ ((x0 = y1) /\ (~ (x1 y1)))) y0) \/ ((~ (x1 x0)) /\ (forall y1 : nat, (~ (x0 = y1)) \/ (x1 y1))).
Definition term132 (x0 : nat -> Prop) := exists y0 : nat, ((fun y1 : nat => (x0 (NUMERAL 0)) /\ ((y1 = (NUMERAL 0)) /\ (~ (x0 y1)))) y0) \/ ((~ (x0 (NUMERAL 0))) /\ (forall y1 : nat, (~ (y1 = (NUMERAL 0))) \/ (x0 y1))).
Definition term196 (x0 : nat -> Prop) (x1 : nat) := and (~ (x0 x1)).
Definition term13 (x0 : nat -> Prop) := fun y0 : nat => (x0 (Nat.pred y0)) = (forall y1 : nat, ((y0 = (S y1)) \/ ((y1 = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) -> x0 y1).
Definition term64 (x0 : nat) (x1 : nat) := ((S x1) = (S x0)) \/ ((x0 = (NUMERAL 0)) /\ ((S x1) = (NUMERAL 0))).
Definition term56 (x0 : nat -> Prop) := fun y0 : nat => (y0 = (NUMERAL 0)) -> x0 y0.
Definition term165 (x0 : nat -> Prop) (x1 : nat) := (~ (~ (x1 = (NUMERAL 0)))) -> x0 x1.
Definition term209 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => (x0 = y1) /\ (~ (x1 y1))) y0.
Definition term116 (x0 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => (y1 = (NUMERAL 0)) /\ (~ (x0 y1))) y0.
Definition term163 (x0 : nat -> Prop) (x1 : nat) := @eq Prop ((x0 x1) \/ (~ (x1 = (NUMERAL 0)))).
Definition term25 (x0 : nat -> Prop) (x1 : nat) := x0 (Nat.pred (S x1)).
Definition term181 := fun y0 : nat -> Prop => forall y1 : nat, (y0 y1) = (forall y2 : nat, (y1 = y2) -> y0 y2).
Definition term87 (x0 : nat -> Prop) (x1 : nat) := (~ (x1 = (NUMERAL 0))) \/ (x0 x1).
Definition term245 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := @eq Prop ((~ (x0 = x2)) \/ (x1 x2)).
Definition term213 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (x1 x0) /\ ((fun y0 : nat => (x0 = y0) /\ (~ (x1 y0))) x2).
Definition term39 (x0 : nat -> Prop) := forall y0 : nat, (x0 (Nat.pred y0)) = (forall y1 : nat, ((y0 = (S y1)) \/ ((y1 = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) -> x0 y1).
Definition term29 (x0 : nat -> Prop) := fun y0 : nat => ((fun y1 : nat => (x0 (Nat.pred y1)) = (forall y2 : nat, ((y1 = (S y2)) \/ ((y2 = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) -> x0 y2)) y0) -> (fun y1 : nat => (x0 (Nat.pred y1)) = (forall y2 : nat, ((y1 = (S y2)) \/ ((y2 = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) -> x0 y2)) (S y0).
Definition term43 (x0 : nat -> Prop) := @eq Prop (x0 (Nat.pred (NUMERAL 0))).
Definition term48 (x0 : nat) := (x0 = (NUMERAL 0)) /\ True.
Definition term220 (x0 : nat) (x1 : nat -> Prop) := (exists y0 : nat, (fun y1 : nat => (x1 x0) /\ ((x0 = y1) /\ (~ (x1 y1)))) y0) \/ ((~ (x1 x0)) /\ (forall y0 : nat, (~ (x0 = y0)) \/ (x1 y0))).
Definition term67 (x0 : nat) (x1 : nat) := imp (x0 = x1).
Definition term115 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => (y0 = (NUMERAL 0)) /\ (~ (x0 y0))) x1.
Definition term172 (x0 : nat) (x1 : nat -> Prop) := ((~ ((x1 x0) = (forall y0 : nat, (x0 = y0) -> x1 y0))) -> False) -> (~ ((x1 x0) = (forall y0 : nat, (x0 = y0) -> x1 y0))) -> False.
Definition term76 (x0 : nat -> Prop) := ((~ ((x0 (NUMERAL 0)) = (forall y0 : nat, (y0 = (NUMERAL 0)) -> x0 y0))) -> False) -> (~ ((x0 (NUMERAL 0)) = (forall y0 : nat, (y0 = (NUMERAL 0)) -> x0 y0))) -> False.
Definition term59 (x0 : nat -> Prop) (x1 : nat) := @eq Prop (x0 x1).
Definition term68 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (((S x0) = (S x2)) \/ ((x2 = (NUMERAL 0)) /\ ((S x0) = (NUMERAL 0)))) -> x1 x2.
Definition term140 (x0 : nat -> Prop) (x1 : nat) := or ((x0 (NUMERAL 0)) /\ ((x1 = (NUMERAL 0)) /\ (~ (x0 x1)))).
Definition term190 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ~ ((fun y0 : nat => (x0 = y0) -> x1 y0) x2).
Definition term229 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := or ((x1 x0) /\ ((x0 = x2) /\ (~ (x1 x2)))).
Definition term237 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => x0 y0) x1.
Definition term101 (x0 : nat -> Prop) := (~ (x0 (NUMERAL 0))) /\ (forall y0 : nat, (~ (y0 = (NUMERAL 0))) \/ (x0 y0)).
Definition term100 (x0 : nat -> Prop) := (~ (x0 (NUMERAL 0))) /\ (forall y0 : nat, (y0 = (NUMERAL 0)) -> x0 y0).
Definition term177 (x0 : nat -> Prop) := fun y0 : nat => (x0 y0) = (forall y1 : nat, (y0 = y1) -> x0 y1).
Definition term233 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => ((x1 x0) /\ ((x0 = y0) /\ (~ (x1 y0)))) \/ ((~ (x1 x0)) /\ (forall y1 : nat, (~ (x0 = y1)) \/ (x1 y1))).
Definition term83 := forall y0 : nat -> Prop, (~ ((y0 (NUMERAL 0)) = (forall y1 : nat, (y1 = (NUMERAL 0)) -> y0 y1))) -> False.
Definition term246 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := @eq Prop ((x0 x2) \/ (~ (x1 = x2))).
Definition term22 (x0 : nat -> Prop) (x1 : nat) := imp ((fun y0 : nat => (x0 (Nat.pred y0)) = (forall y1 : nat, ((y0 = (S y1)) \/ ((y1 = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) -> x0 y1)) x1).
Definition term128 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) \/ x1.
Definition term114 (x0 : nat -> Prop) := exists y0 : nat, (x0 (NUMERAL 0)) /\ ((fun y1 : nat => (y1 = (NUMERAL 0)) /\ (~ (x0 y1))) y0).
Definition term45 (x0 : nat) := or ((NUMERAL 0) = (S x0)).
Definition term151 (x0 : nat -> Prop) := (fun y0 : nat => ~ (x0 y0)) (NUMERAL 0).
Definition term162 (x0 : nat -> Prop) (x1 : nat) := @eq Prop ((~ (x1 = (NUMERAL 0))) \/ (x0 x1)).
Definition term7 (x0 : nat) := ~ ((S x0) = (NUMERAL 0)).
Definition term176 (x0 : nat -> Prop) := fun y0 : nat => (~ ((x0 y0) = (forall y1 : nat, (y0 = y1) -> x0 y1))) -> False.
Definition term18 (x0 : nat -> Prop) := and ((x0 (Nat.pred (NUMERAL 0))) = (forall y0 : nat, (((NUMERAL 0) = (S y0)) \/ ((y0 = (NUMERAL 0)) /\ ((NUMERAL 0) = (NUMERAL 0)))) -> x0 y0)).
Definition term82 := fun y0 : nat -> Prop => (y0 (NUMERAL 0)) = (forall y1 : nat, (y1 = (NUMERAL 0)) -> y0 y1).
Definition term178 (x0 : nat -> Prop) := forall y0 : nat, (~ ((x0 y0) = (forall y1 : nat, (y0 = y1) -> x0 y1))) -> False.
Definition term106 (x0 : nat -> Prop) := or ((x0 (NUMERAL 0)) /\ (exists y0 : nat, (y0 = (NUMERAL 0)) /\ (~ (x0 y0)))).
Definition term44 (x0 : nat -> Prop) := @eq Prop (x0 (NUMERAL 0)).
Definition term19 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => (x0 (Nat.pred y0)) = (forall y1 : nat, ((y0 = (S y1)) \/ ((y1 = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) -> x0 y1)) x1.
Definition term224 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, (fun y1 : nat => (x1 x0) /\ ((x0 = y1) /\ (~ (x1 y1)))) y0.
Definition term210 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, (fun y1 : nat => (x0 = y1) /\ (~ (x1 y1))) y0.
Definition term135 (x0 : nat -> Prop) := exists y0 : nat, (fun y1 : nat => (x0 (NUMERAL 0)) /\ ((y1 = (NUMERAL 0)) /\ (~ (x0 y1)))) y0.
Definition term117 (x0 : nat -> Prop) := exists y0 : nat, (fun y1 : nat => (y1 = (NUMERAL 0)) /\ (~ (x0 y1))) y0.
Definition term123 (x0 : nat -> Prop) := fun y0 : nat => (x0 (NUMERAL 0)) /\ ((y0 = (NUMERAL 0)) /\ (~ (x0 y0))).
Definition term173 (x0 : nat) (x1 : nat -> Prop) := (((~ ((x1 x0) = (forall y0 : nat, (x0 = y0) -> x1 y0))) -> False) -> (~ ((x1 x0) = (forall y0 : nat, (x0 = y0) -> x1 y0))) -> False) -> (~ ((x1 x0) = (forall y0 : nat, (x0 = y0) -> x1 y0))) -> False.
Definition term77 (x0 : nat -> Prop) := (((~ ((x0 (NUMERAL 0)) = (forall y0 : nat, (y0 = (NUMERAL 0)) -> x0 y0))) -> False) -> (~ ((x0 (NUMERAL 0)) = (forall y0 : nat, (y0 = (NUMERAL 0)) -> x0 y0))) -> False) -> (~ ((x0 (NUMERAL 0)) = (forall y0 : nat, (y0 = (NUMERAL 0)) -> x0 y0))) -> False.
Definition term214 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (x1 x0) /\ ((x0 = x2) /\ (~ (x1 x2))).
Definition term69 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (x0 = x2) -> x1 x2.
Definition term217 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, (x1 x0) /\ ((x0 = y0) /\ (~ (x1 y0))).
Definition term175 (x0 : nat) (x1 : nat -> Prop) := ~ (~ ((x1 x0) = (forall y0 : nat, (x0 = y0) -> x1 y0))).
Definition term193 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, (x0 = y0) /\ (~ (x1 y0)).
Definition term104 (x0 : nat -> Prop) := (x0 (NUMERAL 0)) /\ (exists y0 : nat, (y0 = (NUMERAL 0)) /\ (~ (x0 y0))).
Definition term63 (x0 : nat) := (x0 = (NUMERAL 0)) /\ False.
Definition term0 := forall y0 : nat, (Nat.pred (S y0)) = y0.
Definition term152 (x0 : nat -> Prop) (x1 : nat) := @eq Prop ((fun y0 : nat => ~ (x0 y0)) x1).
Definition term183 := forall y0 : nat -> Prop, forall y1 : nat, (y0 y1) = (forall y2 : nat, (y1 = y2) -> y0 y2).
Definition term72 (x0 : nat) (x1 : nat -> Prop) := forall y0 : nat, (x0 = y0) -> x1 y0.
Definition term171 (x0 : nat) (x1 : nat -> Prop) := ~ ((x1 x0) = (forall y0 : nat, (x0 = y0) -> x1 y0)).
Definition term42 (x0 : nat -> Prop) := x0 (NUMERAL 0).
Definition term122 (x0 : nat -> Prop) := fun y0 : nat => (x0 (NUMERAL 0)) /\ ((fun y1 : nat => (y1 = (NUMERAL 0)) /\ (~ (x0 y1))) y0).
Definition term119 (x0 : nat -> Prop) := @eq Prop ((x0 (NUMERAL 0)) /\ (exists y0 : nat, (y0 = (NUMERAL 0)) /\ (~ (x0 y0)))).
Definition term118 (x0 : nat -> Prop) := @eq Prop ((x0 (NUMERAL 0)) /\ (exists y0 : nat, (fun y1 : nat => (y1 = (NUMERAL 0)) /\ (~ (x0 y1))) y0)).
Definition term50 (x0 : nat) := False \/ (x0 = (NUMERAL 0)).
Definition term3 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((S y0) = (S y1)) = (y0 = y1)) x0.
Definition term207 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, (x1 x0) /\ ((fun y1 : nat => (x0 = y1) /\ (~ (x1 y1))) y0).
Definition term6 (x0 : nat) := (fun y0 : nat => ~ ((S y0) = (NUMERAL 0))) x0.
Definition term60 (x0 : nat) (x1 : nat) := or ((S x0) = (S x1)).
Definition term37 (x0 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => (x0 (Nat.pred y1)) = (forall y2 : nat, ((y1 = (S y2)) \/ ((y2 = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) -> x0 y2)) y0.
Definition term169 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => (~ ((y0 (NUMERAL 0)) = (forall y1 : nat, (y1 = (NUMERAL 0)) -> y0 y1))) -> False) x0.
Definition term148 (x0 : nat -> Prop) := ~ (x0 (NUMERAL 0)).
Definition term41 := Nat.pred (NUMERAL 0).
Definition term30 (x0 : nat -> Prop) := fun y0 : nat => ((x0 (Nat.pred y0)) = (forall y1 : nat, ((y0 = (S y1)) \/ ((y1 = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) -> x0 y1)) -> (x0 (Nat.pred (S y0))) = (forall y1 : nat, (((S y0) = (S y1)) \/ ((y1 = (NUMERAL 0)) /\ ((S y0) = (NUMERAL 0)))) -> x0 y1).
Definition term202 (x0 : nat) (x1 : nat -> Prop) := or ((x1 x0) /\ (~ (forall y0 : nat, (x0 = y0) -> x1 y0))).
Definition term55 (x0 : nat -> Prop) := fun y0 : nat => (((NUMERAL 0) = (S y0)) \/ ((y0 = (NUMERAL 0)) /\ ((NUMERAL 0) = (NUMERAL 0)))) -> x0 y0.
Definition term230 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := ((fun y0 : nat => (x2 x1) /\ ((x1 = y0) /\ (~ (x2 y0)))) x0) \/ ((~ (x2 x1)) /\ (forall y0 : nat, (~ (x1 = y0)) \/ (x2 y0))).
Definition term141 (x0 : nat) (x1 : nat -> Prop) := ((fun y0 : nat => (x1 (NUMERAL 0)) /\ ((y0 = (NUMERAL 0)) /\ (~ (x1 y0)))) x0) \/ ((~ (x1 (NUMERAL 0))) /\ (forall y0 : nat, (~ (y0 = (NUMERAL 0))) \/ (x1 y0))).
Definition term227 (x0 : nat) (x1 : nat -> Prop) := @eq Prop ((exists y0 : nat, (x1 x0) /\ ((x0 = y0) /\ (~ (x1 y0)))) \/ ((~ (x1 x0)) /\ (forall y0 : nat, (~ (x0 = y0)) \/ (x1 y0)))).
Definition term226 (x0 : nat) (x1 : nat -> Prop) := @eq Prop ((exists y0 : nat, (fun y1 : nat => (x1 x0) /\ ((x0 = y1) /\ (~ (x1 y1)))) y0) \/ ((~ (x1 x0)) /\ (forall y0 : nat, (~ (x0 = y0)) \/ (x1 y0)))).
Definition term138 (x0 : nat -> Prop) := @eq Prop ((exists y0 : nat, (x0 (NUMERAL 0)) /\ ((y0 = (NUMERAL 0)) /\ (~ (x0 y0)))) \/ ((~ (x0 (NUMERAL 0))) /\ (forall y0 : nat, (~ (y0 = (NUMERAL 0))) \/ (x0 y0)))).
Definition term137 (x0 : nat -> Prop) := @eq Prop ((exists y0 : nat, (fun y1 : nat => (x0 (NUMERAL 0)) /\ ((y1 = (NUMERAL 0)) /\ (~ (x0 y1)))) y0) \/ ((~ (x0 (NUMERAL 0))) /\ (forall y0 : nat, (~ (y0 = (NUMERAL 0))) \/ (x0 y0)))).
Definition term85 (x0 : nat -> Prop) (x1 : nat) := ~ ((x1 = (NUMERAL 0)) -> x0 x1).
Definition term188 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, ~ ((fun y1 : nat => (x0 = y1) -> x1 y1) y0).
Definition term91 (x0 : nat -> Prop) := exists y0 : nat, ~ ((fun y1 : nat => (y1 = (NUMERAL 0)) -> x0 y1) y0).
Definition term228 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := or ((fun y0 : nat => (x1 x0) /\ ((x0 = y0) /\ (~ (x1 y0)))) x2).
Definition term8 (x0 : nat) := (~ ((S x0) = (NUMERAL 0))) -> ((S x0) = (NUMERAL 0)) = False.
Definition term10 (x0 : nat) := (~ ((NUMERAL 0) = (S x0))) -> ((NUMERAL 0) = (S x0)) = False.
Definition term231 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := ((x2 x1) /\ ((x1 = x0) /\ (~ (x2 x0)))) \/ ((~ (x2 x1)) /\ (forall y0 : nat, (~ (x1 = y0)) \/ (x2 y0))).
Definition term223 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => (x1 x0) /\ ((x0 = y1) /\ (~ (x1 y1)))) y0.
Definition term134 (x0 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => (x0 (NUMERAL 0)) /\ ((y1 = (NUMERAL 0)) /\ (~ (x0 y1)))) y0.
Definition term65 (x0 : nat) (x1 : nat) := (x0 = x1) \/ False.
Definition term144 (x0 : nat -> Prop) := fun y0 : nat => ((x0 (NUMERAL 0)) /\ ((y0 = (NUMERAL 0)) /\ (~ (x0 y0)))) \/ ((~ (x0 (NUMERAL 0))) /\ (forall y1 : nat, (~ (y1 = (NUMERAL 0))) \/ (x0 y1))).
Definition term28 (x0 : nat) (x1 : nat -> Prop) := ((x1 (Nat.pred x0)) = (forall y0 : nat, ((x0 = (S y0)) \/ ((y0 = (NUMERAL 0)) /\ (x0 = (NUMERAL 0)))) -> x1 y0)) -> (x1 (Nat.pred (S x0))) = (forall y0 : nat, (((S x0) = (S y0)) \/ ((y0 = (NUMERAL 0)) /\ ((S x0) = (NUMERAL 0)))) -> x1 y0).
Definition term167 (x0 : nat) := imp (~ (~ (x0 = (NUMERAL 0)))).
Definition term205 (x0 : nat) (x1 : nat -> Prop) := ((x1 x0) /\ (exists y0 : nat, (x0 = y0) /\ (~ (x1 y0)))) \/ ((~ (x1 x0)) /\ (forall y0 : nat, (~ (x0 = y0)) \/ (x1 y0))).
Definition term133 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => (x0 (NUMERAL 0)) /\ ((y0 = (NUMERAL 0)) /\ (~ (x0 y0)))) x1.
Definition term92 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => (y0 = (NUMERAL 0)) -> x0 y0) x1.
Definition term15 (x0 : nat -> Prop) := x0 (Nat.pred (NUMERAL 0)).
Definition term71 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (x0 = y0) -> x1 y0.
Definition term199 (x0 : nat -> Prop) (x1 : nat) := and (x0 x1).
Definition term191 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => ~ ((fun y1 : nat => (x0 = y1) -> x1 y1) y0).
Definition term94 (x0 : nat -> Prop) := fun y0 : nat => ~ ((fun y1 : nat => (y1 = (NUMERAL 0)) -> x0 y1) y0).
Definition term93 (x0 : nat -> Prop) (x1 : nat) := ~ ((fun y0 : nat => (y0 = (NUMERAL 0)) -> x0 y0) x1).
Definition term174 (x0 : nat) (x1 : nat -> Prop) := (((~ ((x1 x0) = (forall y0 : nat, (x0 = y0) -> x1 y0))) -> False) -> (~ ((x1 x0) = (forall y0 : nat, (x0 = y0) -> x1 y0))) -> False) -> ((~ ((x1 x0) = (forall y0 : nat, (x0 = y0) -> x1 y0))) -> False) -> (~ ((x1 x0) = (forall y0 : nat, (x0 = y0) -> x1 y0))) -> False.
Definition term78 (x0 : nat -> Prop) := (((~ ((x0 (NUMERAL 0)) = (forall y0 : nat, (y0 = (NUMERAL 0)) -> x0 y0))) -> False) -> (~ ((x0 (NUMERAL 0)) = (forall y0 : nat, (y0 = (NUMERAL 0)) -> x0 y0))) -> False) -> ((~ ((x0 (NUMERAL 0)) = (forall y0 : nat, (y0 = (NUMERAL 0)) -> x0 y0))) -> False) -> (~ ((x0 (NUMERAL 0)) = (forall y0 : nat, (y0 = (NUMERAL 0)) -> x0 y0))) -> False.
Definition term54 (x0 : nat -> Prop) (x1 : nat) := (x1 = (NUMERAL 0)) -> x0 x1.
Definition term170 (x0 : nat) (x1 : nat -> Prop) := (~ ((x1 x0) = (forall y0 : nat, (x0 = y0) -> x1 y0))) -> False.
Definition term74 (x0 : nat -> Prop) := (~ ((x0 (NUMERAL 0)) = (forall y0 : nat, (y0 = (NUMERAL 0)) -> x0 y0))) -> False.
Definition term14 (x0 : nat -> Prop) := (fun y0 : nat => (x0 (Nat.pred y0)) = (forall y1 : nat, ((y0 = (S y1)) \/ ((y1 = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) -> x0 y1)) (NUMERAL 0).
Definition term204 (x0 : nat) (x1 : nat -> Prop) := ((x1 x0) /\ (~ (forall y0 : nat, (x0 = y0) -> x1 y0))) \/ ((~ (x1 x0)) /\ (forall y0 : nat, (x0 = y0) -> x1 y0)).
Definition term225 (x0 : nat) (x1 : nat -> Prop) := or (exists y0 : nat, (fun y1 : nat => (x1 x0) /\ ((x0 = y1) /\ (~ (x1 y1)))) y0).
Definition term136 (x0 : nat -> Prop) := or (exists y0 : nat, (fun y1 : nat => (x0 (NUMERAL 0)) /\ ((y1 = (NUMERAL 0)) /\ (~ (x0 y1)))) y0).
Definition term124 (x0 : nat -> Prop) := exists y0 : nat, (x0 (NUMERAL 0)) /\ ((y0 = (NUMERAL 0)) /\ (~ (x0 y0))).
Definition term182 := forall y0 : nat -> Prop, forall y1 : nat, (~ ((y0 y1) = (forall y2 : nat, (y1 = y2) -> y0 y2))) -> False.
Definition term166 (x0 : nat) := ~ (~ (x0 = (NUMERAL 0))).
Definition term248 (x0 : nat) (x1 : nat) := ~ (~ (x0 = x1)).
Definition term189 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (fun y0 : nat => (x0 = y0) -> x1 y0) x2.
Definition term58 (x0 : nat -> Prop) (x1 : nat) := @eq Prop (x0 (Nat.pred (S x1))).
Definition term47 (x0 : nat) := (x0 = (NUMERAL 0)) /\ ((NUMERAL 0) = (NUMERAL 0)).
Definition term1 (x0 : nat) := (fun y0 : nat => (Nat.pred (S y0)) = y0) x0.
Definition term5 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((S x0) = (S y0)) = (x0 = y0)) x1.
Definition term206 (x0 : nat) (x1 : nat -> Prop) := (x1 x0) /\ (exists y0 : nat, (fun y1 : nat => (x0 = y1) /\ (~ (x1 y1))) y0).
Definition term113 (x0 : nat -> Prop) := (x0 (NUMERAL 0)) /\ (exists y0 : nat, (fun y1 : nat => (y1 = (NUMERAL 0)) /\ (~ (x0 y1))) y0).
Definition term89 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term97 (x0 : nat -> Prop) := fun y0 : nat => (~ (y0 = (NUMERAL 0))) \/ (x0 y0).
Definition term168 (x0 : nat -> Prop) := ((NUMERAL 0) = (NUMERAL 0)) -> x0 (NUMERAL 0).
Definition term32 (x0 : nat -> Prop) := forall y0 : nat, ((x0 (Nat.pred y0)) = (forall y1 : nat, ((y0 = (S y1)) \/ ((y1 = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) -> x0 y1)) -> (x0 (Nat.pred (S y0))) = (forall y1 : nat, (((S y0) = (S y1)) \/ ((y1 = (NUMERAL 0)) /\ ((S y0) = (NUMERAL 0)))) -> x0 y1).
Definition term194 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (~ (x0 = y0)) \/ (x1 y0).
Definition term61 (x0 : nat) (x1 : nat) := or (x0 = x1).
Definition term84 := forall y0 : nat -> Prop, (y0 (NUMERAL 0)) = (forall y1 : nat, (y1 = (NUMERAL 0)) -> y0 y1).
Definition term238 (x0 : nat -> Prop) (x1 : nat) := @eq Prop ((fun y0 : nat => x0 y0) x1).
Definition term75 (x0 : nat -> Prop) := ~ ((x0 (NUMERAL 0)) = (forall y0 : nat, (y0 = (NUMERAL 0)) -> x0 y0)).
Definition term130 (x0 : nat -> Prop) (x1 : Prop) := exists y0 : nat, (x0 y0) \/ x1.
Definition term185 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (x0 = x2) /\ (~ (x1 x2)).
Definition term149 (x0 : nat -> Prop) := fun y0 : nat => ~ (x0 y0).
Definition term179 (x0 : nat -> Prop) := forall y0 : nat, (x0 y0) = (forall y1 : nat, (y0 = y1) -> x0 y1).
Definition term70 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (((S x0) = (S y0)) \/ ((y0 = (NUMERAL 0)) /\ ((S x0) = (NUMERAL 0)))) -> x1 y0.
Definition term2 (x0 : nat) := Nat.pred (S x0).
Definition term249 (x0 : nat) (x1 : nat) := imp (~ (~ (x0 = x1))).
Definition term215 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (x1 x0) /\ ((fun y1 : nat => (x0 = y1) /\ (~ (x1 y1))) y0).
