Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term372 (a0 : Type') (x0 : a0) (x1 : list a0) := (fun y0 : list a0 => ((@cons a0 x0 x1) = y0) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 y0)) /\ (forall y1 : nat, (Peano.lt y1 (@List.length a0 y0)) -> (@EL a0 y1 (@cons a0 x0 x1)) = (@EL a0 y1 y0)))) (@nil a0).
Definition term343 (a0 : Type') := (fun y0 : list a0 => ((@nil a0) = y0) = (((@List.length a0 (@nil a0)) = (@List.length a0 y0)) /\ (forall y1 : nat, (Peano.lt y1 (@List.length a0 y0)) -> (@EL a0 y1 (@nil a0)) = (@EL a0 y1 y0)))) (@nil a0).
Definition term356 (a0 : Type') (x0 : a0) := fun y0 : list a0 => (((@nil a0) = y0) = (((@List.length a0 (@nil a0)) = (@List.length a0 y0)) /\ (forall y1 : nat, (Peano.lt y1 (@List.length a0 y0)) -> (@EL a0 y1 (@nil a0)) = (@EL a0 y1 y0)))) -> ((@nil a0) = (@cons a0 x0 y0)) = (((@List.length a0 (@nil a0)) = (@List.length a0 (@cons a0 x0 y0))) /\ (forall y1 : nat, (Peano.lt y1 (@List.length a0 (@cons a0 x0 y0))) -> (@EL a0 y1 (@nil a0)) = (@EL a0 y1 (@cons a0 x0 y0)))).
Definition term376 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : list a0) := (fun y0 : list a0 => ((@cons a0 x0 x1) = y0) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 y0)) /\ (forall y1 : nat, (Peano.lt y1 (@List.length a0 y0)) -> (@EL a0 y1 (@cons a0 x0 x1)) = (@EL a0 y1 y0)))) x2.
Definition term177 (x0 : nat -> nat) := fun y0 : nat => (fun y1 : nat => fun y2 : nat => (y1 = (NUMERAL 0)) \/ (y1 = (S y2))) y0 (x0 y0).
Definition term204 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term33 (x0 : nat -> Prop) := fun y0 : nat => x0 y0.
Definition term296 (a0 : Type') (x0 : a0) := forall y0 : a0, forall y1 : list a0, forall y2 : list a0, ((@cons a0 x0 y1) = (@cons a0 y0 y2)) = ((x0 = y0) /\ (y1 = y2)).
Definition term153 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) \/ (x0 = (S x1)).
Definition term305 (a0 : Type') (x0 : a0) (x1 : list a0) := (fun y0 : list a0 => ~ ((@cons a0 x0 y0) = (@nil a0))) x1.
Definition term285 (x0 : nat) := ~ ((NUMERAL 0) = (S x0)).
Definition term270 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ~ ((~ (x2 = x0)) \/ (~ (x1 x2))).
Definition term353 (a0 : Type') (x0 : a0) (x1 : list a0) := ((fun y0 : list a0 => ((@nil a0) = y0) = (((@List.length a0 (@nil a0)) = (@List.length a0 y0)) /\ (forall y1 : nat, (Peano.lt y1 (@List.length a0 y0)) -> (@EL a0 y1 (@nil a0)) = (@EL a0 y1 y0)))) x1) -> (fun y0 : list a0 => ((@nil a0) = y0) = (((@List.length a0 (@nil a0)) = (@List.length a0 y0)) /\ (forall y1 : nat, (Peano.lt y1 (@List.length a0 y0)) -> (@EL a0 y1 (@nil a0)) = (@EL a0 y1 y0)))) (@cons a0 x0 x1).
Definition term129 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => (forall y1 : nat, x0 y1) /\ ((~ (x0 (NUMERAL 0))) \/ (~ (x0 (S y0))))) x1.
Definition term35 (x0 : nat -> Prop) := ~ (all x0).
Definition term188 := (~ False) -> False.
Definition term41 (x0 : nat -> Prop) (x1 : nat) := ~ (x0 x1).
Definition term5 (x0 : nat) := Peano.lt (NUMERAL 0) (S x0).
Definition term299 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := (fun y0 : list a0 => forall y1 : list a0, ((@cons a0 x0 y0) = (@cons a0 x1 y1)) = ((x0 = x1) /\ (y0 = y1))) x2.
Definition term114 (x0 : nat -> Prop) := @eq Prop ((exists y0 : nat, ~ (x0 y0)) /\ ((x0 (NUMERAL 0)) /\ (forall y0 : nat, x0 (S y0)))).
Definition term113 (x0 : nat -> Prop) := @eq Prop ((exists y0 : nat, (fun y1 : nat => ~ (x0 y1)) y0) /\ ((x0 (NUMERAL 0)) /\ (forall y0 : nat, x0 (S y0)))).
Definition term334 (a0 : Type') := (forall y0 : list a0, ((@nil a0) = y0) = (((@List.length a0 (@nil a0)) = (@List.length a0 y0)) /\ (forall y1 : nat, (Peano.lt y1 (@List.length a0 y0)) -> (@EL a0 y1 (@nil a0)) = (@EL a0 y1 y0)))) /\ (forall y0 : a0, forall y1 : list a0, (forall y2 : list a0, (y1 = y2) = (((@List.length a0 y1) = (@List.length a0 y2)) /\ (forall y3 : nat, (Peano.lt y3 (@List.length a0 y2)) -> (@EL a0 y3 y1) = (@EL a0 y3 y2)))) -> forall y2 : list a0, ((@cons a0 y0 y1) = y2) = (((@List.length a0 (@cons a0 y0 y1)) = (@List.length a0 y2)) /\ (forall y3 : nat, (Peano.lt y3 (@List.length a0 y2)) -> (@EL a0 y3 (@cons a0 y0 y1)) = (@EL a0 y3 y2)))).
Definition term184 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => (y0 = (NUMERAL 0)) \/ (y0 = (S (x0 y0)))) x1.
Definition term247 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term227 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term410 (a0 : Type') (x0 : a0) (x1 : list a0) := @eq Prop ((@nil a0) = (@cons a0 x0 x1)).
Definition term46 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => x0 (S y0)) x1.
Definition term308 (a0 : Type') (x0 : a0) (x1 : list a0) := ~ ((@nil a0) = (@cons a0 x0 x1)).
Definition term404 (a0 : Type') := fun y0 : nat => (Peano.lt y0 (@List.length a0 (@nil a0))) -> (@EL a0 y0 (@nil a0)) = (@EL a0 y0 (@nil a0)).
Definition term449 (a0 : Type') (x0 : list a0) (x1 : list a0) := ((@List.length a0 x0) = (@List.length a0 x1)) /\ (forall y0 : nat, (Peano.lt y0 (@List.length a0 x1)) -> (@EL a0 y0 x0) = (@EL a0 y0 x1)).
Definition term471 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := ((Peano.lt (NUMERAL 0) (S (@List.length a0 x3))) -> (@EL a0 (NUMERAL 0) (@cons a0 x0 x1)) = (@EL a0 (NUMERAL 0) (@cons a0 x2 x3))) /\ (forall y0 : nat, (Peano.lt (S y0) (S (@List.length a0 x3))) -> (@EL a0 (S y0) (@cons a0 x0 x1)) = (@EL a0 (S y0) (@cons a0 x2 x3))).
Definition term138 (x0 : nat -> Prop) (x1 : nat) := or ((fun y0 : nat => (forall y1 : nat, x0 y1) /\ ((~ (x0 (NUMERAL 0))) \/ (~ (x0 (S y0))))) x1).
Definition term389 (a0 : Type') (x0 : a0) (x1 : list a0) := fun y0 : a0 => forall y1 : list a0, (((@cons a0 x0 x1) = y1) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 y1)) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> (@EL a0 y2 (@cons a0 x0 x1)) = (@EL a0 y2 y1)))) -> ((@cons a0 x0 x1) = (@cons a0 y0 y1)) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 (@cons a0 y0 y1))) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 (@cons a0 y0 y1))) -> (@EL a0 y2 (@cons a0 x0 x1)) = (@EL a0 y2 (@cons a0 y0 y1)))).
Definition term360 (a0 : Type') := fun y0 : a0 => forall y1 : list a0, (((@nil a0) = y1) = (((@List.length a0 (@nil a0)) = (@List.length a0 y1)) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> (@EL a0 y2 (@nil a0)) = (@EL a0 y2 y1)))) -> ((@nil a0) = (@cons a0 y0 y1)) = (((@List.length a0 (@nil a0)) = (@List.length a0 (@cons a0 y0 y1))) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 (@cons a0 y0 y1))) -> (@EL a0 y2 (@nil a0)) = (@EL a0 y2 (@cons a0 y0 y1)))).
Definition term469 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := forall y0 : nat, (fun y1 : nat => (Peano.lt y1 (S (@List.length a0 x3))) -> (@EL a0 y1 (@cons a0 x0 x1)) = (@EL a0 y1 (@cons a0 x2 x3))) (S y0).
Definition term412 := @eq nat (NUMERAL 0).
Definition term382 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := ((fun y0 : list a0 => ((@cons a0 x0 x1) = y0) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 y0)) /\ (forall y1 : nat, (Peano.lt y1 (@List.length a0 y0)) -> (@EL a0 y1 (@cons a0 x0 x1)) = (@EL a0 y1 y0)))) x3) -> (fun y0 : list a0 => ((@cons a0 x0 x1) = y0) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 y0)) /\ (forall y1 : nat, (Peano.lt y1 (@List.length a0 y0)) -> (@EL a0 y1 (@cons a0 x0 x1)) = (@EL a0 y1 y0)))) (@cons a0 x2 x3).
Definition term209 (x0 : Prop) := ~ (~ x0).
Definition term499 (a0 : Type') (x0 : a0) (x1 : list a0) := @hd a0 (@cons a0 x0 x1).
Definition term293 (a0 : Type') (x0 : a0) (x1 : list a0) := @List.length a0 (@cons a0 x0 x1).
Definition term271 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (~ (~ (x2 = x0))) /\ (~ (~ (x1 x2))).
Definition term163 := forall y0 : nat, exists y1 : nat, (fun y2 : nat => fun y3 : nat => (y2 = (NUMERAL 0)) \/ (y2 = (S y3))) y0 y1.
Definition term161 (x0 : type1605) := forall y0 : nat, exists y1 : nat, x0 y0 y1.
Definition term158 := forall y0 : nat, exists y1 : nat, (y0 = (NUMERAL 0)) \/ (y0 = (S y1)).
Definition term280 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => (~ ((forall y1 : nat, y0 y1) = ((y0 (NUMERAL 0)) /\ (forall y1 : nat, y0 (S y1))))) -> (forall y1 : nat, (y1 = (NUMERAL 0)) \/ (exists y2 : nat, y1 = (S y2))) -> False) x0.
Definition term170 (x0 : nat) := exists y0 : nat, (fun y1 : nat => fun y2 : nat => (y1 = (NUMERAL 0)) \/ (y1 = (S y2))) x0 y0.
Definition term483 (a0 : Type') (x0 : nat) (x1 : list a0) := imp (Peano.lt x0 (@List.length a0 x1)).
Definition term157 := fun y0 : nat => exists y1 : nat, (y0 = (NUMERAL 0)) \/ (y0 = (S y1)).
Definition term102 (x0 : nat -> Prop) := or (exists y0 : nat, (forall y1 : nat, x0 y1) /\ ((~ (x0 (NUMERAL 0))) \/ (~ (x0 (S y0))))).
Definition term214 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := ((~ (x0 x2)) /\ (x0 x1)) -> ~ (x1 = x2).
Definition term394 (a0 : Type') (x0 : a0) (x1 : list a0) := imp (((fun y0 : list a0 => ((@cons a0 x0 x1) = y0) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 y0)) /\ (forall y1 : nat, (Peano.lt y1 (@List.length a0 y0)) -> (@EL a0 y1 (@cons a0 x0 x1)) = (@EL a0 y1 y0)))) (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, ((fun y2 : list a0 => ((@cons a0 x0 x1) = y2) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 y2)) /\ (forall y3 : nat, (Peano.lt y3 (@List.length a0 y2)) -> (@EL a0 y3 (@cons a0 x0 x1)) = (@EL a0 y3 y2)))) y1) -> (fun y2 : list a0 => ((@cons a0 x0 x1) = y2) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 y2)) /\ (forall y3 : nat, (Peano.lt y3 (@List.length a0 y2)) -> (@EL a0 y3 (@cons a0 x0 x1)) = (@EL a0 y3 y2)))) (@cons a0 y0 y1))).
Definition term365 (a0 : Type') := imp (((fun y0 : list a0 => ((@nil a0) = y0) = (((@List.length a0 (@nil a0)) = (@List.length a0 y0)) /\ (forall y1 : nat, (Peano.lt y1 (@List.length a0 y0)) -> (@EL a0 y1 (@nil a0)) = (@EL a0 y1 y0)))) (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, ((fun y2 : list a0 => ((@nil a0) = y2) = (((@List.length a0 (@nil a0)) = (@List.length a0 y2)) /\ (forall y3 : nat, (Peano.lt y3 (@List.length a0 y2)) -> (@EL a0 y3 (@nil a0)) = (@EL a0 y3 y2)))) y1) -> (fun y2 : list a0 => ((@nil a0) = y2) = (((@List.length a0 (@nil a0)) = (@List.length a0 y2)) /\ (forall y3 : nat, (Peano.lt y3 (@List.length a0 y2)) -> (@EL a0 y3 (@nil a0)) = (@EL a0 y3 y2)))) (@cons a0 y0 y1))).
Definition term335 (a0 : Type') := imp (((fun y0 : list a0 => forall y1 : list a0, (y0 = y1) = (((@List.length a0 y0) = (@List.length a0 y1)) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> (@EL a0 y2 y0) = (@EL a0 y2 y1)))) (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, ((fun y2 : list a0 => forall y3 : list a0, (y2 = y3) = (((@List.length a0 y2) = (@List.length a0 y3)) /\ (forall y4 : nat, (Peano.lt y4 (@List.length a0 y3)) -> (@EL a0 y4 y2) = (@EL a0 y4 y3)))) y1) -> (fun y2 : list a0 => forall y3 : list a0, (y2 = y3) = (((@List.length a0 y2) = (@List.length a0 y3)) /\ (forall y4 : nat, (Peano.lt y4 (@List.length a0 y3)) -> (@EL a0 y4 y2) = (@EL a0 y4 y3)))) (@cons a0 y0 y1))).
Definition term264 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (~ (x0 x1)) \/ (~ (x1 = x2)).
Definition term250 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term120 (x0 : nat -> Prop) := fun y0 : nat => (~ (x0 y0)) /\ ((x0 (NUMERAL 0)) /\ (forall y1 : nat, x0 (S y1))).
Definition term109 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => ~ (x0 y0)) x1.
Definition term237 (x0 : nat -> nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> x1 = (S (x0 x1)).
Definition term408 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term123 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term122 (x0 : nat -> Prop) := (exists y0 : nat, (forall y1 : nat, x0 y1) /\ ((~ (x0 (NUMERAL 0))) \/ (~ (x0 (S y0))))) \/ (exists y0 : nat, (~ (x0 y0)) /\ ((x0 (NUMERAL 0)) /\ (forall y1 : nat, x0 (S y1)))).
Definition term121 (x0 : nat -> Prop) := exists y0 : nat, (~ (x0 y0)) /\ ((x0 (NUMERAL 0)) /\ (forall y1 : nat, x0 (S y1))).
Definition term92 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => (~ (x0 (NUMERAL 0))) \/ (~ (x0 (S y0)))) x1.
Definition term440 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := fun y0 : nat => (Peano.lt y0 (@List.length a0 (@cons a0 x2 x3))) -> (@EL a0 y0 (@cons a0 x0 x1)) = (@EL a0 y0 (@cons a0 x2 x3)).
Definition term506 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) (x3 : list a0) := (x0 = x1) /\ ((@List.length a0 x2) = (@List.length a0 x3)).
Definition term13 (x0 : nat -> Prop) := (((~ ((forall y0 : nat, x0 y0) = ((x0 (NUMERAL 0)) /\ (forall y0 : nat, x0 (S y0))))) -> (forall y0 : nat, (y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1))) -> False) -> (~ ((forall y0 : nat, x0 y0) = ((x0 (NUMERAL 0)) /\ (forall y0 : nat, x0 (S y0))))) -> (forall y0 : nat, (y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1))) -> False) -> (~ ((forall y0 : nat, x0 y0) = ((x0 (NUMERAL 0)) /\ (forall y0 : nat, x0 (S y0))))) -> (forall y0 : nat, (y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1))) -> False.
Definition term489 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : list a0) := @eq a0 (@EL a0 (S x0) (@cons a0 x1 x2)).
Definition term44 (x0 : nat -> Prop) := ~ (forall y0 : nat, x0 (S y0)).
Definition term484 (a0 : Type') (x0 : nat) (x1 : list a0) := @EL a0 (S x0) x1.
Definition term119 (x0 : nat -> Prop) := fun y0 : nat => ((fun y1 : nat => ~ (x0 y1)) y0) /\ ((x0 (NUMERAL 0)) /\ (forall y1 : nat, x0 (S y1))).
Definition term199 (x0 : nat) := ~ (x0 = x0).
Definition term217 (x0 : nat) := ~ ((NUMERAL 0) = x0).
Definition term313 (a0 : Type') := (fun y0 : list a0 => forall y1 : list a0, (y0 = y1) = (((@List.length a0 y0) = (@List.length a0 y1)) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> (@EL a0 y2 y0) = (@EL a0 y2 y1)))) (@nil a0).
Definition term87 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term178 (x0 : nat -> nat) := fun y0 : nat => (y0 = (NUMERAL 0)) \/ (y0 = (S (x0 y0))).
Definition term315 (a0 : Type') := and ((fun y0 : list a0 => forall y1 : list a0, (y0 = y1) = (((@List.length a0 y0) = (@List.length a0 y1)) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> (@EL a0 y2 y0) = (@EL a0 y2 y1)))) (@nil a0)).
Definition term28 := fun y0 : nat => (y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1)).
Definition term6 (x0 : Prop) := (~ x0) -> False.
Definition term370 (a0 : Type') (x0 : a0) (x1 : list a0) := (((fun y0 : list a0 => ((@cons a0 x0 x1) = y0) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 y0)) /\ (forall y1 : nat, (Peano.lt y1 (@List.length a0 y0)) -> (@EL a0 y1 (@cons a0 x0 x1)) = (@EL a0 y1 y0)))) (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, ((fun y2 : list a0 => ((@cons a0 x0 x1) = y2) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 y2)) /\ (forall y3 : nat, (Peano.lt y3 (@List.length a0 y2)) -> (@EL a0 y3 (@cons a0 x0 x1)) = (@EL a0 y3 y2)))) y1) -> (fun y2 : list a0 => ((@cons a0 x0 x1) = y2) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 y2)) /\ (forall y3 : nat, (Peano.lt y3 (@List.length a0 y2)) -> (@EL a0 y3 (@cons a0 x0 x1)) = (@EL a0 y3 y2)))) (@cons a0 y0 y1))) -> forall y0 : list a0, (fun y1 : list a0 => ((@cons a0 x0 x1) = y1) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 y1)) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> (@EL a0 y2 (@cons a0 x0 x1)) = (@EL a0 y2 y1)))) y0.
Definition term341 (a0 : Type') := (((fun y0 : list a0 => ((@nil a0) = y0) = (((@List.length a0 (@nil a0)) = (@List.length a0 y0)) /\ (forall y1 : nat, (Peano.lt y1 (@List.length a0 y0)) -> (@EL a0 y1 (@nil a0)) = (@EL a0 y1 y0)))) (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, ((fun y2 : list a0 => ((@nil a0) = y2) = (((@List.length a0 (@nil a0)) = (@List.length a0 y2)) /\ (forall y3 : nat, (Peano.lt y3 (@List.length a0 y2)) -> (@EL a0 y3 (@nil a0)) = (@EL a0 y3 y2)))) y1) -> (fun y2 : list a0 => ((@nil a0) = y2) = (((@List.length a0 (@nil a0)) = (@List.length a0 y2)) /\ (forall y3 : nat, (Peano.lt y3 (@List.length a0 y2)) -> (@EL a0 y3 (@nil a0)) = (@EL a0 y3 y2)))) (@cons a0 y0 y1))) -> forall y0 : list a0, (fun y1 : list a0 => ((@nil a0) = y1) = (((@List.length a0 (@nil a0)) = (@List.length a0 y1)) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> (@EL a0 y2 (@nil a0)) = (@EL a0 y2 y1)))) y0.
Definition term311 (a0 : Type') := (((fun y0 : list a0 => forall y1 : list a0, (y0 = y1) = (((@List.length a0 y0) = (@List.length a0 y1)) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> (@EL a0 y2 y0) = (@EL a0 y2 y1)))) (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, ((fun y2 : list a0 => forall y3 : list a0, (y2 = y3) = (((@List.length a0 y2) = (@List.length a0 y3)) /\ (forall y4 : nat, (Peano.lt y4 (@List.length a0 y3)) -> (@EL a0 y4 y2) = (@EL a0 y4 y3)))) y1) -> (fun y2 : list a0 => forall y3 : list a0, (y2 = y3) = (((@List.length a0 y2) = (@List.length a0 y3)) /\ (forall y4 : nat, (Peano.lt y4 (@List.length a0 y3)) -> (@EL a0 y4 y2) = (@EL a0 y4 y3)))) (@cons a0 y0 y1))) -> forall y0 : list a0, (fun y1 : list a0 => forall y2 : list a0, (y1 = y2) = (((@List.length a0 y1) = (@List.length a0 y2)) /\ (forall y3 : nat, (Peano.lt y3 (@List.length a0 y2)) -> (@EL a0 y3 y1) = (@EL a0 y3 y2)))) y0.
Definition term231 (x0 : nat) := ((x0 = x0) /\ (~ ((NUMERAL 0) = x0))) -> ~ (x0 = (NUMERAL 0)).
Definition term490 (a0 : Type') (x0 : nat) (x1 : list a0) := @eq a0 (@EL a0 x0 x1).
Definition term328 (a0 : Type') (x0 : a0) := forall y0 : list a0, (forall y1 : list a0, (y0 = y1) = (((@List.length a0 y0) = (@List.length a0 y1)) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> (@EL a0 y2 y0) = (@EL a0 y2 y1)))) -> forall y1 : list a0, ((@cons a0 x0 y0) = y1) = (((@List.length a0 (@cons a0 x0 y0)) = (@List.length a0 y1)) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> (@EL a0 y2 (@cons a0 x0 y0)) = (@EL a0 y2 y1))).
Definition term252 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term310 (a0 : Type') (x0 : type1143 a0) := ((x0 (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, (x0 y1) -> x0 (@cons a0 y0 y1))) -> forall y0 : list a0, x0 y0.
Definition term194 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (x2 = x0) -> (x1 x0) \/ (~ (x1 x2)).
Definition term9 (x0 : nat -> Prop) := (~ ((forall y0 : nat, x0 y0) = ((x0 (NUMERAL 0)) /\ (forall y0 : nat, x0 (S y0))))) -> False.
Definition term475 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) (x3 : list a0) := (x0 = x1) /\ ((forall y0 : nat, (Peano.lt y0 (@List.length a0 x3)) -> (@EL a0 y0 x2) = (@EL a0 y0 x3)) /\ ((@List.length a0 x2) = (@List.length a0 x3))).
Definition term54 (x0 : nat -> Prop) := (~ (x0 (NUMERAL 0))) \/ (exists y0 : nat, ~ (x0 (S y0))).
Definition term416 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : list a0) := imp (Peano.lt x0 (@List.length a0 (@cons a0 x1 x2))).
Definition term304 (a0 : Type') (x0 : a0) := forall y0 : list a0, ~ ((@cons a0 x0 y0) = (@nil a0)).
Definition term497 (a0 : Type') (x0 : list a0) := @EL a0 (NUMERAL 0) x0.
Definition term415 (a0 : Type') (x0 : nat) (x1 : list a0) := Peano.lt x0 (S (@List.length a0 x1)).
Definition term339 (a0 : Type') := forall y0 : list a0, forall y1 : list a0, (y0 = y1) = (((@List.length a0 y0) = (@List.length a0 y1)) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> (@EL a0 y2 y0) = (@EL a0 y2 y1))).
Definition term298 (a0 : Type') (x0 : a0) (x1 : a0) := forall y0 : list a0, forall y1 : list a0, ((@cons a0 x0 y0) = (@cons a0 x1 y1)) = ((x0 = x1) /\ (y0 = y1)).
Definition term291 (a0 : Type') (x0 : a0) := forall y0 : list a0, (@List.length a0 (@cons a0 x0 y0)) = (S (@List.length a0 y0)).
Definition term166 (x0 : nat) := (fun y0 : nat => fun y1 : nat => (y0 = (NUMERAL 0)) \/ (y0 = (S y1))) x0.
Definition term446 (x0 : nat) := forall y0 : nat, ((S x0) = (S y0)) = (x0 = y0).
Definition term1 (x0 : nat) := forall y0 : nat, (Peano.lt (S x0) (S y0)) = (Peano.lt x0 y0).
Definition term455 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := forall y0 : nat, (fun y1 : nat => (Peano.lt y1 (S (@List.length a0 x3))) -> (@EL a0 y1 (@cons a0 x0 x1)) = (@EL a0 y1 (@cons a0 x2 x3))) y0.
Definition term498 (a0 : Type') (x0 : a0) (x1 : list a0) := @EL a0 (NUMERAL 0) (@cons a0 x0 x1).
Definition term226 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) /\ (~ (x1 = x2)).
Definition term384 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) := fun y0 : list a0 => ((fun y1 : list a0 => ((@cons a0 x0 x1) = y1) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 y1)) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> (@EL a0 y2 (@cons a0 x0 x1)) = (@EL a0 y2 y1)))) y0) -> (fun y1 : list a0 => ((@cons a0 x0 x1) = y1) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 y1)) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> (@EL a0 y2 (@cons a0 x0 x1)) = (@EL a0 y2 y1)))) (@cons a0 x2 y0).
Definition term355 (a0 : Type') (x0 : a0) := fun y0 : list a0 => ((fun y1 : list a0 => ((@nil a0) = y1) = (((@List.length a0 (@nil a0)) = (@List.length a0 y1)) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> (@EL a0 y2 (@nil a0)) = (@EL a0 y2 y1)))) y0) -> (fun y1 : list a0 => ((@nil a0) = y1) = (((@List.length a0 (@nil a0)) = (@List.length a0 y1)) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> (@EL a0 y2 (@nil a0)) = (@EL a0 y2 y1)))) (@cons a0 x0 y0).
Definition term294 (a0 : Type') (x0 : list a0) := S (@List.length a0 x0).
Definition term167 (x0 : nat) (x1 : nat) := (fun y0 : nat => fun y1 : nat => (y0 = (NUMERAL 0)) \/ (y0 = (S y1))) x0 x1.
Definition term71 (x0 : Prop) (x1 : nat -> Prop) := exists y0 : nat, x0 \/ (x1 y0).
Definition term101 (x0 : nat -> Prop) := exists y0 : nat, (forall y1 : nat, x0 y1) /\ ((~ (x0 (NUMERAL 0))) \/ (~ (x0 (S y0)))).
Definition term144 (x0 : nat -> Prop) := exists y0 : nat, ((forall y1 : nat, x0 y1) /\ ((~ (x0 (NUMERAL 0))) \/ (~ (x0 (S y0))))) \/ ((~ (x0 y0)) /\ ((x0 (NUMERAL 0)) /\ (forall y1 : nat, x0 (S y1)))).
Definition term133 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => (~ (x0 y0)) /\ ((x0 (NUMERAL 0)) /\ (forall y1 : nat, x0 (S y1)))) x1.
Definition term378 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : list a0) := imp ((fun y0 : list a0 => ((@cons a0 x0 x1) = y0) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 y0)) /\ (forall y1 : nat, (Peano.lt y1 (@List.length a0 y0)) -> (@EL a0 y1 (@cons a0 x0 x1)) = (@EL a0 y1 y0)))) x2).
Definition term346 (a0 : Type') := and (((@nil a0) = (@nil a0)) = (((@List.length a0 (@nil a0)) = (@List.length a0 (@nil a0))) /\ (forall y0 : nat, (Peano.lt y0 (@List.length a0 (@nil a0))) -> (@EL a0 y0 (@nil a0)) = (@EL a0 y0 (@nil a0))))).
Definition term352 (a0 : Type') (x0 : a0) (x1 : list a0) := ((@List.length a0 (@nil a0)) = (@List.length a0 (@cons a0 x0 x1))) /\ (forall y0 : nat, (Peano.lt y0 (@List.length a0 (@cons a0 x0 x1))) -> (@EL a0 y0 (@nil a0)) = (@EL a0 y0 (@cons a0 x0 x1))).
Definition term59 (x0 : nat -> Prop) := (~ (forall y0 : nat, x0 y0)) /\ ((x0 (NUMERAL 0)) /\ (forall y0 : nat, x0 (S y0))).
Definition term479 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := (forall y0 : nat, (Peano.lt (S y0) (S (@List.length a0 x3))) -> (@EL a0 (S y0) (@cons a0 x0 x1)) = (@EL a0 (S y0) (@cons a0 x2 x3))) /\ ((Peano.lt (NUMERAL 0) (S (@List.length a0 x3))) -> (@EL a0 (NUMERAL 0) (@cons a0 x0 x1)) = (@EL a0 (NUMERAL 0) (@cons a0 x2 x3))).
Definition term200 (x0 : nat -> Prop) (x1 : nat) := (x0 x1) -> ~ (x0 x1).
Definition term202 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term90 (x0 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (exists y0 : nat, (fun y1 : nat => (~ (x0 (NUMERAL 0))) \/ (~ (x0 (S y1)))) y0).
Definition term225 (x0 : nat) (x1 : nat) := and (x0 = x1).
Definition term347 (a0 : Type') (x0 : list a0) := (fun y0 : list a0 => ((@nil a0) = y0) = (((@List.length a0 (@nil a0)) = (@List.length a0 y0)) /\ (forall y1 : nat, (Peano.lt y1 (@List.length a0 y0)) -> (@EL a0 y1 (@nil a0)) = (@EL a0 y1 y0)))) x0.
Definition term18 (x0 : nat -> Prop) := imp (~ ((forall y0 : nat, x0 y0) = ((x0 (NUMERAL 0)) /\ (forall y0 : nat, x0 (S y0))))).
Definition term215 (x0 : nat) (x1 : nat -> Prop) := (~ (x1 x0)) /\ (x1 (NUMERAL 0)).
Definition term413 (a0 : Type') (x0 : a0) (x1 : list a0) := and ((@List.length a0 (@nil a0)) = (@List.length a0 (@cons a0 x0 x1))).
Definition term216 (x0 : nat -> Prop) (x1 : nat) := ((~ (x0 x1)) /\ (x0 (NUMERAL 0))) -> ~ ((NUMERAL 0) = x1).
Definition term16 := ~ (forall y0 : nat, (y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1))).
Definition term261 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := ~ (x0 (S (x1 x2))).
Definition term218 (x0 : nat) := ((NUMERAL 0) = x0) -> ~ ((NUMERAL 0) = x0).
Definition term185 (x0 : nat -> Prop) := (~ (x0 (NUMERAL 0))) -> x0 (NUMERAL 0).
Definition term295 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0, forall y2 : list a0, forall y3 : list a0, ((@cons a0 y0 y2) = (@cons a0 y1 y3)) = ((y0 = y1) /\ (y2 = y3))) x0.
Definition term10 (x0 : nat -> Prop) := ~ ((forall y0 : nat, x0 y0) = ((x0 (NUMERAL 0)) /\ (forall y0 : nat, x0 (S y0)))).
Definition term396 (a0 : Type') (x0 : a0) (x1 : list a0) := fun y0 : list a0 => (fun y1 : list a0 => ((@cons a0 x0 x1) = y1) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 y1)) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> (@EL a0 y2 (@cons a0 x0 x1)) = (@EL a0 y2 y1)))) y0.
Definition term367 (a0 : Type') := fun y0 : list a0 => (fun y1 : list a0 => ((@nil a0) = y1) = (((@List.length a0 (@nil a0)) = (@List.length a0 y1)) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> (@EL a0 y2 (@nil a0)) = (@EL a0 y2 y1)))) y0.
Definition term439 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : nat) (x3 : a0) (x4 : list a0) := (Peano.lt x2 (S (@List.length a0 x4))) -> (@EL a0 x2 (@cons a0 x0 x1)) = (@EL a0 x2 (@cons a0 x3 x4)).
Definition term86 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term260 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := (~ (x0 (S (x1 x2)))) -> x0 (S (x1 x2)).
Definition term155 (x0 : nat) := fun y0 : nat => (x0 = (NUMERAL 0)) \/ (x0 = (S y0)).
Definition term213 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := imp ((~ (x1 x0)) /\ (x1 x2)).
Definition term186 (x0 : Prop) := (~ x0) -> x0.
Definition term383 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := (((@cons a0 x0 x1) = x3) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 x3)) /\ (forall y0 : nat, (Peano.lt y0 (@List.length a0 x3)) -> (@EL a0 y0 (@cons a0 x0 x1)) = (@EL a0 y0 x3)))) -> ((@cons a0 x0 x1) = (@cons a0 x2 x3)) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 (@cons a0 x2 x3))) /\ (forall y0 : nat, (Peano.lt y0 (@List.length a0 (@cons a0 x2 x3))) -> (@EL a0 y0 (@cons a0 x0 x1)) = (@EL a0 y0 (@cons a0 x2 x3)))).
Definition term251 (x0 : nat) (x1 : nat) (x2 : nat) := (x1 = x0) /\ (x1 = x2).
Definition term401 (a0 : Type') (x0 : nat) := Peano.lt x0 (@List.length a0 (@nil a0)).
Definition term58 (x0 : nat -> Prop) := and (exists y0 : nat, ~ (x0 y0)).
Definition term165 := fun y0 : nat => fun y1 : nat => (y0 = (NUMERAL 0)) \/ (y0 = (S y1)).
Definition term248 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term281 := forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False.
Definition term303 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : list a0, ~ ((@cons a0 y0 y1) = (@nil a0))) x0.
Definition term388 (a0 : Type') (x0 : a0) (x1 : list a0) := fun y0 : a0 => forall y1 : list a0, ((fun y2 : list a0 => ((@cons a0 x0 x1) = y2) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 y2)) /\ (forall y3 : nat, (Peano.lt y3 (@List.length a0 y2)) -> (@EL a0 y3 (@cons a0 x0 x1)) = (@EL a0 y3 y2)))) y1) -> (fun y2 : list a0 => ((@cons a0 x0 x1) = y2) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 y2)) /\ (forall y3 : nat, (Peano.lt y3 (@List.length a0 y2)) -> (@EL a0 y3 (@cons a0 x0 x1)) = (@EL a0 y3 y2)))) (@cons a0 y0 y1).
Definition term359 (a0 : Type') := fun y0 : a0 => forall y1 : list a0, ((fun y2 : list a0 => ((@nil a0) = y2) = (((@List.length a0 (@nil a0)) = (@List.length a0 y2)) /\ (forall y3 : nat, (Peano.lt y3 (@List.length a0 y2)) -> (@EL a0 y3 (@nil a0)) = (@EL a0 y3 y2)))) y1) -> (fun y2 : list a0 => ((@nil a0) = y2) = (((@List.length a0 (@nil a0)) = (@List.length a0 y2)) /\ (forall y3 : nat, (Peano.lt y3 (@List.length a0 y2)) -> (@EL a0 y3 (@nil a0)) = (@EL a0 y3 y2)))) (@cons a0 y0 y1).
Definition term329 (a0 : Type') := fun y0 : a0 => forall y1 : list a0, ((fun y2 : list a0 => forall y3 : list a0, (y2 = y3) = (((@List.length a0 y2) = (@List.length a0 y3)) /\ (forall y4 : nat, (Peano.lt y4 (@List.length a0 y3)) -> (@EL a0 y4 y2) = (@EL a0 y4 y3)))) y1) -> (fun y2 : list a0 => forall y3 : list a0, (y2 = y3) = (((@List.length a0 y2) = (@List.length a0 y3)) /\ (forall y4 : nat, (Peano.lt y4 (@List.length a0 y3)) -> (@EL a0 y4 y2) = (@EL a0 y4 y3)))) (@cons a0 y0 y1).
Definition term107 (x0 : nat -> Prop) := (exists y0 : nat, (fun y1 : nat => ~ (x0 y1)) y0) /\ ((x0 (NUMERAL 0)) /\ (forall y0 : nat, x0 (S y0))).
Definition term24 (x0 : nat) := fun y0 : nat => x0 = (S y0).
Definition term462 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := (Peano.lt (NUMERAL 0) (S (@List.length a0 x3))) -> (@EL a0 (NUMERAL 0) (@cons a0 x0 x1)) = (@EL a0 (NUMERAL 0) (@cons a0 x2 x3)).
Definition term187 (x0 : nat -> Prop) := (x0 (NUMERAL 0)) -> False.
Definition term60 (x0 : nat -> Prop) := (exists y0 : nat, ~ (x0 y0)) /\ ((x0 (NUMERAL 0)) /\ (forall y0 : nat, x0 (S y0))).
Definition term459 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := @eq Prop (forall y0 : nat, (fun y1 : nat => (Peano.lt y1 (S (@List.length a0 x3))) -> (@EL a0 y1 (@cons a0 x0 x1)) = (@EL a0 y1 (@cons a0 x2 x3))) y0).
Definition term206 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term40 (x0 : nat -> Prop) (x1 : nat) := ~ ((fun y0 : nat => x0 y0) x1).
Definition term198 (x0 : nat) := (~ (x0 = x0)) -> x0 = x0.
Definition term159 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term245 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term112 (x0 : nat -> Prop) := and (exists y0 : nat, (fun y1 : nat => ~ (x0 y1)) y0).
Definition term460 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := @eq Prop (forall y0 : nat, (Peano.lt y0 (S (@List.length a0 x3))) -> (@EL a0 y0 (@cons a0 x0 x1)) = (@EL a0 y0 (@cons a0 x2 x3))).
Definition term143 (x0 : nat -> Prop) := fun y0 : nat => ((forall y1 : nat, x0 y1) /\ ((~ (x0 (NUMERAL 0))) \/ (~ (x0 (S y0))))) \/ ((~ (x0 y0)) /\ ((x0 (NUMERAL 0)) /\ (forall y1 : nat, x0 (S y1)))).
Definition term246 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term183 := exists y0 : nat -> nat, forall y1 : nat, (y1 = (NUMERAL 0)) \/ (y1 = (S (y0 y1))).
Definition term164 := exists y0 : nat -> nat, forall y1 : nat, (fun y2 : nat => fun y3 : nat => (y2 = (NUMERAL 0)) \/ (y2 = (S y3))) y1 (y0 y1).
Definition term162 (x0 : type1605) := exists y0 : nat -> nat, forall y1 : nat, x0 y1 (y0 y1).
Definition term478 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) (x3 : list a0) := @eq Prop ((forall y0 : nat, (Peano.lt y0 (@List.length a0 x3)) -> (@EL a0 y0 x2) = (@EL a0 y0 x3)) /\ ((x0 = x1) /\ ((@List.length a0 x2) = (@List.length a0 x3)))).
Definition term485 (a0 : Type') (x0 : nat) (x1 : list a0) := @EL a0 x0 (@tl a0 x1).
Definition term51 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 (S y0)).
Definition term279 (x0 : nat -> Prop) (x1 : nat) := (x0 x1) -> False.
Definition term437 (a0 : Type') (x0 : list a0) (x1 : list a0) := and ((S (@List.length a0 x0)) = (S (@List.length a0 x1))).
Definition term265 (x0 : nat -> Prop) (x1 : nat) := or (x0 x1).
Definition term317 (a0 : Type') (x0 : list a0) := (fun y0 : list a0 => forall y1 : list a0, (y0 = y1) = (((@List.length a0 y0) = (@List.length a0 y1)) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> (@EL a0 y2 y0) = (@EL a0 y2 y1)))) x0.
Definition term243 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term32 (x0 : nat -> Prop) := and (x0 (NUMERAL 0)).
Definition term431 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : nat) := False -> (@EL a0 x2 (@cons a0 x0 x1)) = (@EL a0 x2 (@nil a0)).
Definition term488 (a0 : Type') (x0 : a0) (x1 : list a0) := @tl a0 (@cons a0 x0 x1).
Definition term444 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := ((S (@List.length a0 x1)) = (S (@List.length a0 x3))) /\ (forall y0 : nat, (Peano.lt y0 (S (@List.length a0 x3))) -> (@EL a0 y0 (@cons a0 x0 x1)) = (@EL a0 y0 (@cons a0 x2 x3))).
Definition term232 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term229 (x0 : nat) (x1 : nat) (x2 : nat) := ((x1 = x0) /\ (~ (x2 = x0))) -> ~ (x1 = x2).
Definition term30 (x0 : nat -> Prop) := fun y0 : nat => x0 (S y0).
Definition term503 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : a0) (x3 : a0) := ((@List.length a0 x0) = (@List.length a0 x1)) /\ ((forall y0 : nat, (Peano.lt y0 (@List.length a0 x1)) -> (@EL a0 y0 x0) = (@EL a0 y0 x1)) /\ (x2 = x3)).
Definition term141 (x0 : nat) (x1 : nat -> Prop) := ((forall y0 : nat, x1 y0) /\ ((~ (x1 (NUMERAL 0))) \/ (~ (x1 (S x0))))) \/ ((~ (x1 x0)) /\ ((x1 (NUMERAL 0)) /\ (forall y0 : nat, x1 (S y0)))).
Definition term8 (x0 : nat -> Prop) := (x0 (NUMERAL 0)) /\ (forall y0 : nat, x0 (S y0)).
Definition term495 (a0 : Type') (x0 : list a0) := Peano.lt (NUMERAL 0) (S (@List.length a0 x0)).
Definition term52 (x0 : nat -> Prop) := or (~ (x0 (NUMERAL 0))).
Definition term179 (x0 : nat -> nat) := forall y0 : nat, (fun y1 : nat => fun y2 : nat => (y1 = (NUMERAL 0)) \/ (y1 = (S y2))) y0 (x0 y0).
Definition term425 (a0 : Type') (x0 : a0) (x1 : list a0) := False /\ (forall y0 : nat, (Peano.lt y0 (S (@List.length a0 x1))) -> (@EL a0 y0 (@nil a0)) = (@EL a0 y0 (@cons a0 x0 x1))).
Definition term326 (a0 : Type') (x0 : a0) := fun y0 : list a0 => (forall y1 : list a0, (y0 = y1) = (((@List.length a0 y0) = (@List.length a0 y1)) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> (@EL a0 y2 y0) = (@EL a0 y2 y1)))) -> forall y1 : list a0, ((@cons a0 x0 y0) = y1) = (((@List.length a0 (@cons a0 x0 y0)) = (@List.length a0 y1)) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> (@EL a0 y2 (@cons a0 x0 y0)) = (@EL a0 y2 y1))).
Definition term11 (x0 : nat -> Prop) := (~ ((forall y0 : nat, x0 y0) = ((x0 (NUMERAL 0)) /\ (forall y0 : nat, x0 (S y0))))) -> (forall y0 : nat, (y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1))) -> False.
Definition term20 := fun y0 : nat -> Prop => (~ ((forall y1 : nat, y0 y1) = ((y0 (NUMERAL 0)) /\ (forall y1 : nat, y0 (S y1))))) -> (forall y1 : nat, (y1 = (NUMERAL 0)) \/ (exists y2 : nat, y1 = (S y2))) -> False.
Definition term111 (x0 : nat -> Prop) := exists y0 : nat, (fun y1 : nat => ~ (x0 y1)) y0.
Definition term77 (x0 : nat -> Prop) := exists y0 : nat, (fun y1 : nat => ~ (x0 (S y1))) y0.
Definition term448 (a0 : Type') (x0 : list a0) (x1 : list a0) := (fun y0 : list a0 => (x0 = y0) = (((@List.length a0 x0) = (@List.length a0 y0)) /\ (forall y1 : nat, (Peano.lt y1 (@List.length a0 y0)) -> (@EL a0 y1 x0) = (@EL a0 y1 y0)))) x1.
Definition term89 (x0 : Prop) (x1 : nat -> Prop) := exists y0 : nat, x0 /\ (x1 y0).
Definition term257 (x0 : nat -> nat) (x1 : nat) := (~ ((S (x0 x1)) = x1)) -> (S (x0 x1)) = x1.
Definition term273 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := imp (~ ((~ (x2 = x0)) \/ (~ (x1 x2)))).
Definition term23 := forall y0 : nat -> Prop, (~ ((forall y1 : nat, y0 y1) = ((y0 (NUMERAL 0)) /\ (forall y1 : nat, y0 (S y1))))) -> ~ (forall y1 : nat, (y1 = (NUMERAL 0)) \/ (exists y2 : nat, y1 = (S y2))).
Definition term197 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term84 (x0 : nat -> Prop) := exists y0 : nat, (~ (x0 (NUMERAL 0))) \/ (~ (x0 (S y0))).
Definition term278 (x0 : nat -> Prop) (x1 : nat) := (~ (x0 x1)) -> x0 x1.
Definition term17 := forall y0 : nat, (y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1)).
Definition term152 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) \/ ((fun y0 : nat => x0 = (S y0)) x1).
Definition term476 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 /\ (x1 /\ x2).
Definition term463 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := and ((fun y0 : nat => (Peano.lt y0 (S (@List.length a0 x3))) -> (@EL a0 y0 (@cons a0 x0 x1)) = (@EL a0 y0 (@cons a0 x2 x3))) (NUMERAL 0)).
Definition term275 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ((x0 = x2) /\ (x1 x0)) -> x1 x2.
Definition term93 (x0 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => (~ (x0 (NUMERAL 0))) \/ (~ (x0 (S y1)))) y0.
Definition term338 (a0 : Type') := forall y0 : list a0, (fun y1 : list a0 => forall y2 : list a0, (y1 = y2) = (((@List.length a0 y1) = (@List.length a0 y2)) /\ (forall y3 : nat, (Peano.lt y3 (@List.length a0 y2)) -> (@EL a0 y3 y1) = (@EL a0 y3 y2)))) y0.
Definition term244 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term88 (x0 : Prop) (x1 : nat -> Prop) := x0 /\ (exists y0 : nat, x1 y0).
Definition term22 := forall y0 : nat -> Prop, (~ ((forall y1 : nat, y0 y1) = ((y0 (NUMERAL 0)) /\ (forall y1 : nat, y0 (S y1))))) -> (forall y1 : nat, (y1 = (NUMERAL 0)) \/ (exists y2 : nat, y1 = (S y2))) -> False.
Definition term116 (x0 : nat -> Prop) (x1 : nat) := and (~ (x0 x1)).
Definition term19 (x0 : nat -> Prop) := (~ ((forall y0 : nat, x0 y0) = ((x0 (NUMERAL 0)) /\ (forall y0 : nat, x0 (S y0))))) -> ~ (forall y0 : nat, (y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1))).
Definition term127 (x0 : nat -> Prop) := (exists y0 : nat, (fun y1 : nat => (forall y2 : nat, x0 y2) /\ ((~ (x0 (NUMERAL 0))) \/ (~ (x0 (S y1))))) y0) \/ (exists y0 : nat, (fun y1 : nat => (~ (x0 y1)) /\ ((x0 (NUMERAL 0)) /\ (forall y2 : nat, x0 (S y2)))) y0).
Definition term64 (x0 : nat -> Prop) := or ((forall y0 : nat, x0 y0) /\ (~ ((x0 (NUMERAL 0)) /\ (forall y0 : nat, x0 (S y0))))).
Definition term422 (a0 : Type') (x0 : a0) (x1 : list a0) := fun y0 : nat => (Peano.lt y0 (S (@List.length a0 x1))) -> (@EL a0 y0 (@nil a0)) = (@EL a0 y0 (@cons a0 x0 x1)).
Definition term354 (a0 : Type') (x0 : a0) (x1 : list a0) := (((@nil a0) = x1) = (((@List.length a0 (@nil a0)) = (@List.length a0 x1)) /\ (forall y0 : nat, (Peano.lt y0 (@List.length a0 x1)) -> (@EL a0 y0 (@nil a0)) = (@EL a0 y0 x1)))) -> ((@nil a0) = (@cons a0 x0 x1)) = (((@List.length a0 (@nil a0)) = (@List.length a0 (@cons a0 x0 x1))) /\ (forall y0 : nat, (Peano.lt y0 (@List.length a0 (@cons a0 x0 x1))) -> (@EL a0 y0 (@nil a0)) = (@EL a0 y0 (@cons a0 x0 x1)))).
Definition term468 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := fun y0 : nat => (Peano.lt (S y0) (S (@List.length a0 x3))) -> (@EL a0 (S y0) (@cons a0 x0 x1)) = (@EL a0 (S y0) (@cons a0 x2 x3)).
Definition term182 := fun y0 : nat -> nat => forall y1 : nat, (y1 = (NUMERAL 0)) \/ (y1 = (S (y0 y1))).
Definition term181 := fun y0 : nat -> nat => forall y1 : nat, (fun y2 : nat => fun y3 : nat => (y2 = (NUMERAL 0)) \/ (y2 = (S y3))) y1 (y0 y1).
Definition term287 (x0 : nat) := (fun y0 : nat => (Peano.lt y0 (NUMERAL 0)) = False) x0.
Definition term454 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := ((@List.length a0 x1) = (@List.length a0 x3)) /\ (forall y0 : nat, (Peano.lt y0 (S (@List.length a0 x3))) -> (@EL a0 y0 (@cons a0 x0 x1)) = (@EL a0 y0 (@cons a0 x2 x3))).
Definition term340 (a0 : Type') := ((forall y0 : list a0, ((@nil a0) = y0) = (((@List.length a0 (@nil a0)) = (@List.length a0 y0)) /\ (forall y1 : nat, (Peano.lt y1 (@List.length a0 y0)) -> (@EL a0 y1 (@nil a0)) = (@EL a0 y1 y0)))) /\ (forall y0 : a0, forall y1 : list a0, (forall y2 : list a0, (y1 = y2) = (((@List.length a0 y1) = (@List.length a0 y2)) /\ (forall y3 : nat, (Peano.lt y3 (@List.length a0 y2)) -> (@EL a0 y3 y1) = (@EL a0 y3 y2)))) -> forall y2 : list a0, ((@cons a0 y0 y1) = y2) = (((@List.length a0 (@cons a0 y0 y1)) = (@List.length a0 y2)) /\ (forall y3 : nat, (Peano.lt y3 (@List.length a0 y2)) -> (@EL a0 y3 (@cons a0 y0 y1)) = (@EL a0 y3 y2))))) -> forall y0 : list a0, forall y1 : list a0, (y0 = y1) = (((@List.length a0 y0) = (@List.length a0 y1)) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> (@EL a0 y2 y0) = (@EL a0 y2 y1))).
Definition term173 := @eq Prop (forall y0 : nat, exists y1 : nat, (y0 = (NUMERAL 0)) \/ (y0 = (S y1))).
Definition term172 := @eq Prop (forall y0 : nat, exists y1 : nat, (fun y2 : nat => fun y3 : nat => (y2 = (NUMERAL 0)) \/ (y2 = (S y3))) y0 y1).
Definition term307 (a0 : Type') (x0 : a0) (x1 : list a0) := (~ ((@cons a0 x0 x1) = (@nil a0))) -> ((@cons a0 x0 x1) = (@nil a0)) = False.
Definition term494 (a0 : Type') (x0 : list a0) (x1 : list a0) := and (forall y0 : nat, (Peano.lt y0 (@List.length a0 x1)) -> (@EL a0 y0 x0) = (@EL a0 y0 x1)).
Definition term493 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := and (forall y0 : nat, (Peano.lt (S y0) (S (@List.length a0 x3))) -> (@EL a0 (S y0) (@cons a0 x0 x1)) = (@EL a0 (S y0) (@cons a0 x2 x3))).
Definition term211 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (~ (x1 x0)) /\ (x1 x2).
Definition term399 (a0 : Type') := @eq Prop ((@nil a0) = (@nil a0)).
Definition term48 (x0 : nat -> Prop) (x1 : nat) := ~ (x0 (S x1)).
Definition term435 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) (x3 : list a0) := @eq Prop ((x0 = x1) /\ (x2 = x3)).
Definition term458 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := fun y0 : nat => (fun y1 : nat => (Peano.lt y1 (S (@List.length a0 x3))) -> (@EL a0 y1 (@cons a0 x0 x1)) = (@EL a0 y1 (@cons a0 x2 x3))) y0.
Definition term276 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := ((S (x1 x2)) = x2) /\ (x0 (S (x1 x2))).
Definition term66 (x0 : nat -> Prop) := ((forall y0 : nat, x0 y0) /\ (~ ((x0 (NUMERAL 0)) /\ (forall y0 : nat, x0 (S y0))))) \/ ((~ (forall y0 : nat, x0 y0)) /\ ((x0 (NUMERAL 0)) /\ (forall y0 : nat, x0 (S y0)))).
Definition term336 (a0 : Type') := imp ((forall y0 : list a0, ((@nil a0) = y0) = (((@List.length a0 (@nil a0)) = (@List.length a0 y0)) /\ (forall y1 : nat, (Peano.lt y1 (@List.length a0 y0)) -> (@EL a0 y1 (@nil a0)) = (@EL a0 y1 y0)))) /\ (forall y0 : a0, forall y1 : list a0, (forall y2 : list a0, (y1 = y2) = (((@List.length a0 y1) = (@List.length a0 y2)) /\ (forall y3 : nat, (Peano.lt y3 (@List.length a0 y2)) -> (@EL a0 y3 y1) = (@EL a0 y3 y2)))) -> forall y2 : list a0, ((@cons a0 y0 y1) = y2) = (((@List.length a0 (@cons a0 y0 y1)) = (@List.length a0 y2)) /\ (forall y3 : nat, (Peano.lt y3 (@List.length a0 y2)) -> (@EL a0 y3 (@cons a0 y0 y1)) = (@EL a0 y3 y2))))).
Definition term139 (x0 : nat -> Prop) (x1 : nat) := or ((forall y0 : nat, x0 y0) /\ ((~ (x0 (NUMERAL 0))) \/ (~ (x0 (S x1))))).
Definition term65 (x0 : nat -> Prop) := or ((forall y0 : nat, x0 y0) /\ ((~ (x0 (NUMERAL 0))) \/ (exists y0 : nat, ~ (x0 (S y0))))).
Definition term69 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 \/ (x1 y0).
Definition term236 (x0 : nat -> nat) (x1 : nat) := @eq Prop ((x1 = (NUMERAL 0)) \/ (x1 = (S (x0 x1)))).
Definition term147 (x0 : nat) (x1 : nat) := (fun y0 : nat => x0 = (S y0)) x1.
Definition term26 (x0 : nat) := or (x0 = (NUMERAL 0)).
Definition term386 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) := forall y0 : list a0, ((fun y1 : list a0 => ((@cons a0 x0 x1) = y1) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 y1)) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> (@EL a0 y2 (@cons a0 x0 x1)) = (@EL a0 y2 y1)))) y0) -> (fun y1 : list a0 => ((@cons a0 x0 x1) = y1) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 y1)) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> (@EL a0 y2 (@cons a0 x0 x1)) = (@EL a0 y2 y1)))) (@cons a0 x2 y0).
Definition term357 (a0 : Type') (x0 : a0) := forall y0 : list a0, ((fun y1 : list a0 => ((@nil a0) = y1) = (((@List.length a0 (@nil a0)) = (@List.length a0 y1)) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> (@EL a0 y2 (@nil a0)) = (@EL a0 y2 y1)))) y0) -> (fun y1 : list a0 => ((@nil a0) = y1) = (((@List.length a0 (@nil a0)) = (@List.length a0 y1)) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> (@EL a0 y2 (@nil a0)) = (@EL a0 y2 y1)))) (@cons a0 x0 y0).
Definition term327 (a0 : Type') (x0 : a0) := forall y0 : list a0, ((fun y1 : list a0 => forall y2 : list a0, (y1 = y2) = (((@List.length a0 y1) = (@List.length a0 y2)) /\ (forall y3 : nat, (Peano.lt y3 (@List.length a0 y2)) -> (@EL a0 y3 y1) = (@EL a0 y3 y2)))) y0) -> (fun y1 : list a0 => forall y2 : list a0, (y1 = y2) = (((@List.length a0 y1) = (@List.length a0 y2)) /\ (forall y3 : nat, (Peano.lt y3 (@List.length a0 y2)) -> (@EL a0 y3 y1) = (@EL a0 y3 y2)))) (@cons a0 x0 y0).
Definition term290 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : list a0, (@List.length a0 (@cons a0 y0 y1)) = (S (@List.length a0 y1))) x0.
Definition term205 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term337 (a0 : Type') := fun y0 : list a0 => (fun y1 : list a0 => forall y2 : list a0, (y1 = y2) = (((@List.length a0 y1) = (@List.length a0 y2)) /\ (forall y3 : nat, (Peano.lt y3 (@List.length a0 y2)) -> (@EL a0 y3 y1) = (@EL a0 y3 y2)))) y0.
Definition term381 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := ((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 (@cons a0 x2 x3))) /\ (forall y0 : nat, (Peano.lt y0 (@List.length a0 (@cons a0 x2 x3))) -> (@EL a0 y0 (@cons a0 x0 x1)) = (@EL a0 y0 (@cons a0 x2 x3))).
Definition term115 (x0 : nat -> Prop) (x1 : nat) := and ((fun y0 : nat => ~ (x0 y0)) x1).
Definition term402 (a0 : Type') (x0 : nat) := imp (Peano.lt x0 (@List.length a0 (@nil a0))).
Definition term420 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : list a0) := (Peano.lt x0 (S (@List.length a0 x2))) -> (@EL a0 x0 (@nil a0)) = (@EL a0 x0 (@cons a0 x1 x2)).
Definition term68 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 \/ (exists y0 : a0, x1 y0).
Definition term259 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := x0 (S (x1 x2)).
Definition term146 (x0 : nat) := exists y0 : nat, (x0 = (NUMERAL 0)) \/ ((fun y1 : nat => x0 = (S y1)) y0).
Definition term104 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term319 (a0 : Type') (x0 : list a0) := imp ((fun y0 : list a0 => forall y1 : list a0, (y0 = y1) = (((@List.length a0 y0) = (@List.length a0 y1)) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> (@EL a0 y2 y0) = (@EL a0 y2 y1)))) x0).
Definition term219 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((~ (x1 = x0)) \/ (x2 = x0))) -> ~ (x1 = x2).
Definition term73 (x0 : nat -> Prop) := exists y0 : nat, (~ (x0 (NUMERAL 0))) \/ ((fun y1 : nat => ~ (x0 (S y1))) y0).
Definition term128 (x0 : nat -> Prop) := exists y0 : nat, ((fun y1 : nat => (forall y2 : nat, x0 y2) /\ ((~ (x0 (NUMERAL 0))) \/ (~ (x0 (S y1))))) y0) \/ ((fun y1 : nat => (~ (x0 y1)) /\ ((x0 (NUMERAL 0)) /\ (forall y2 : nat, x0 (S y2)))) y0).
Definition term39 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => x0 y0) x1.
Definition term351 (a0 : Type') (x0 : a0) (x1 : list a0) := (fun y0 : list a0 => ((@nil a0) = y0) = (((@List.length a0 (@nil a0)) = (@List.length a0 y0)) /\ (forall y1 : nat, (Peano.lt y1 (@List.length a0 y0)) -> (@EL a0 y1 (@nil a0)) = (@EL a0 y1 y0)))) (@cons a0 x0 x1).
Definition term374 (a0 : Type') (x0 : a0) (x1 : list a0) := and ((fun y0 : list a0 => ((@cons a0 x0 x1) = y0) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 y0)) /\ (forall y1 : nat, (Peano.lt y1 (@List.length a0 y0)) -> (@EL a0 y1 (@cons a0 x0 x1)) = (@EL a0 y1 y0)))) (@nil a0)).
Definition term345 (a0 : Type') := and ((fun y0 : list a0 => ((@nil a0) = y0) = (((@List.length a0 (@nil a0)) = (@List.length a0 y0)) /\ (forall y1 : nat, (Peano.lt y1 (@List.length a0 y0)) -> (@EL a0 y1 (@nil a0)) = (@EL a0 y1 y0)))) (@nil a0)).
Definition term312 (a0 : Type') := fun y0 : list a0 => forall y1 : list a0, (y0 = y1) = (((@List.length a0 y0) = (@List.length a0 y1)) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> (@EL a0 y2 y0) = (@EL a0 y2 y1))).
Definition term193 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (x1 x0) \/ (~ (x1 x2)).
Definition term118 (x0 : nat) (x1 : nat -> Prop) := (~ (x1 x0)) /\ ((x1 (NUMERAL 0)) /\ (forall y0 : nat, x1 (S y0))).
Definition term407 := forall y0 : nat, True.
Definition term320 (a0 : Type') (x0 : list a0) := imp (forall y0 : list a0, (x0 = y0) = (((@List.length a0 x0) = (@List.length a0 y0)) /\ (forall y1 : nat, (Peano.lt y1 (@List.length a0 y0)) -> (@EL a0 y1 x0) = (@EL a0 y1 y0)))).
Definition term371 (a0 : Type') (x0 : a0) (x1 : list a0) := fun y0 : list a0 => ((@cons a0 x0 x1) = y0) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 y0)) /\ (forall y1 : nat, (Peano.lt y1 (@List.length a0 y0)) -> (@EL a0 y1 (@cons a0 x0 x1)) = (@EL a0 y1 y0))).
Definition term34 (x0 : nat -> Prop) := @eq Prop (forall y0 : nat, x0 y0).
Definition term387 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) := forall y0 : list a0, (((@cons a0 x0 x1) = y0) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 y0)) /\ (forall y1 : nat, (Peano.lt y1 (@List.length a0 y0)) -> (@EL a0 y1 (@cons a0 x0 x1)) = (@EL a0 y1 y0)))) -> ((@cons a0 x0 x1) = (@cons a0 x2 y0)) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 (@cons a0 x2 y0))) /\ (forall y1 : nat, (Peano.lt y1 (@List.length a0 (@cons a0 x2 y0))) -> (@EL a0 y1 (@cons a0 x0 x1)) = (@EL a0 y1 (@cons a0 x2 y0)))).
Definition term358 (a0 : Type') (x0 : a0) := forall y0 : list a0, (((@nil a0) = y0) = (((@List.length a0 (@nil a0)) = (@List.length a0 y0)) /\ (forall y1 : nat, (Peano.lt y1 (@List.length a0 y0)) -> (@EL a0 y1 (@nil a0)) = (@EL a0 y1 y0)))) -> ((@nil a0) = (@cons a0 x0 y0)) = (((@List.length a0 (@nil a0)) = (@List.length a0 (@cons a0 x0 y0))) /\ (forall y1 : nat, (Peano.lt y1 (@List.length a0 (@cons a0 x0 y0))) -> (@EL a0 y1 (@nil a0)) = (@EL a0 y1 (@cons a0 x0 y0)))).
Definition term267 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := @eq Prop ((~ (x2 = x0)) \/ ((x1 x0) \/ (~ (x1 x2)))).
Definition term266 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (x0 x2) \/ ((~ (x0 x1)) \/ (~ (x1 = x2))).
Definition term15 := (forall y0 : nat, (y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1))) -> False.
Definition term380 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := (fun y0 : list a0 => ((@cons a0 x0 x1) = y0) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 y0)) /\ (forall y1 : nat, (Peano.lt y1 (@List.length a0 y0)) -> (@EL a0 y1 (@cons a0 x0 x1)) = (@EL a0 y1 y0)))) (@cons a0 x2 x3).
Definition term330 (a0 : Type') := fun y0 : a0 => forall y1 : list a0, (forall y2 : list a0, (y1 = y2) = (((@List.length a0 y1) = (@List.length a0 y2)) /\ (forall y3 : nat, (Peano.lt y3 (@List.length a0 y2)) -> (@EL a0 y3 y1) = (@EL a0 y3 y2)))) -> forall y2 : list a0, ((@cons a0 y0 y1) = y2) = (((@List.length a0 (@cons a0 y0 y1)) = (@List.length a0 y2)) /\ (forall y3 : nat, (Peano.lt y3 (@List.length a0 y2)) -> (@EL a0 y3 (@cons a0 y0 y1)) = (@EL a0 y3 y2))).
Definition term467 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := fun y0 : nat => (fun y1 : nat => (Peano.lt y1 (S (@List.length a0 x3))) -> (@EL a0 y1 (@cons a0 x0 x1)) = (@EL a0 y1 (@cons a0 x2 x3))) (S y0).
Definition term436 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := and ((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 (@cons a0 x2 x3))).
Definition term72 (x0 : nat -> Prop) := (~ (x0 (NUMERAL 0))) \/ (exists y0 : nat, (fun y1 : nat => ~ (x0 (S y1))) y0).
Definition term348 (a0 : Type') (x0 : list a0) := ((@List.length a0 (@nil a0)) = (@List.length a0 x0)) /\ (forall y0 : nat, (Peano.lt y0 (@List.length a0 x0)) -> (@EL a0 y0 (@nil a0)) = (@EL a0 y0 x0)).
Definition term301 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) (x3 : list a0) := (fun y0 : list a0 => ((@cons a0 x0 x2) = (@cons a0 x1 y0)) = ((x0 = x1) /\ (x2 = y0))) x3.
Definition term297 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => forall y1 : list a0, forall y2 : list a0, ((@cons a0 x0 y1) = (@cons a0 y0 y2)) = ((x0 = y0) /\ (y1 = y2))) x1.
Definition term240 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term405 := fun y0 : nat => True.
Definition term53 (x0 : nat -> Prop) := (~ (x0 (NUMERAL 0))) \/ (~ (forall y0 : nat, x0 (S y0))).
Definition term196 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (~ (x2 = x0)) \/ ((x1 x0) \/ (~ (x1 x2))).
Definition term25 (x0 : nat) := exists y0 : nat, x0 = (S y0).
Definition term292 (a0 : Type') (x0 : a0) (x1 : list a0) := (fun y0 : list a0 => (@List.length a0 (@cons a0 x0 y0)) = (S (@List.length a0 y0))) x1.
Definition term106 (x0 : nat -> Prop) (x1 : Prop) := exists y0 : nat, (x0 y0) /\ x1.
Definition term283 (x0 : nat) := ~ ((S x0) = (NUMERAL 0)).
Definition term255 (x0 : nat -> nat) (x1 : nat) := (x1 = (S (x0 x1))) /\ (x1 = x1).
Definition term269 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (~ ((~ (x0 = x2)) \/ (~ (x1 x0)))) -> x1 x2.
Definition term429 (a0 : Type') (x0 : a0) (x1 : list a0) := and ((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 (@nil a0))).
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt (S x0) (S y0)) = (Peano.lt x0 y0)) x1.
Definition term426 (a0 : Type') (x0 : a0) (x1 : list a0) := @eq Prop ((@cons a0 x0 x1) = (@nil a0)).
Definition term450 (a0 : Type') (x0 : a0) (x1 : a0) := and (x0 = x1).
Definition term210 (x0 : nat -> Prop) (x1 : nat) := ~ (~ (x0 x1)).
Definition term333 (a0 : Type') := ((fun y0 : list a0 => forall y1 : list a0, (y0 = y1) = (((@List.length a0 y0) = (@List.length a0 y1)) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> (@EL a0 y2 y0) = (@EL a0 y2 y1)))) (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, ((fun y2 : list a0 => forall y3 : list a0, (y2 = y3) = (((@List.length a0 y2) = (@List.length a0 y3)) /\ (forall y4 : nat, (Peano.lt y4 (@List.length a0 y3)) -> (@EL a0 y4 y2) = (@EL a0 y4 y3)))) y1) -> (fun y2 : list a0 => forall y3 : list a0, (y2 = y3) = (((@List.length a0 y2) = (@List.length a0 y3)) /\ (forall y4 : nat, (Peano.lt y4 (@List.length a0 y3)) -> (@EL a0 y4 y2) = (@EL a0 y4 y3)))) (@cons a0 y0 y1)).
Definition term233 (x0 : nat) := (x0 = (NUMERAL 0)) -> ~ (x0 = (NUMERAL 0)).
Definition term262 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (x1 x0) \/ ((~ (x2 = x0)) \/ (~ (x1 x2))).
Definition term242 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term149 (x0 : nat) := exists y0 : nat, (fun y1 : nat => x0 = (S y1)) y0.
Definition term135 (x0 : nat -> Prop) := exists y0 : nat, (fun y1 : nat => (~ (x0 y1)) /\ ((x0 (NUMERAL 0)) /\ (forall y2 : nat, x0 (S y2)))) y0.
Definition term131 (x0 : nat -> Prop) := exists y0 : nat, (fun y1 : nat => (forall y2 : nat, x0 y2) /\ ((~ (x0 (NUMERAL 0))) \/ (~ (x0 (S y1))))) y0.
Definition term94 (x0 : nat -> Prop) := exists y0 : nat, (fun y1 : nat => (~ (x0 (NUMERAL 0))) \/ (~ (x0 (S y1)))) y0.
Definition term117 (x0 : nat) (x1 : nat -> Prop) := ((fun y0 : nat => ~ (x1 y0)) x0) /\ ((x1 (NUMERAL 0)) /\ (forall y0 : nat, x1 (S y0))).
Definition term403 (a0 : Type') (x0 : nat) := (Peano.lt x0 (@List.length a0 (@nil a0))) -> (@EL a0 x0 (@nil a0)) = (@EL a0 x0 (@nil a0)).
Definition term465 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) (x3 : list a0) (x4 : nat) := (fun y0 : nat => (Peano.lt y0 (S (@List.length a0 x3))) -> (@EL a0 y0 (@cons a0 x0 x1)) = (@EL a0 y0 (@cons a0 x2 x3))) (S x4).
Definition term151 (x0 : nat) := @eq Prop ((x0 = (NUMERAL 0)) \/ (exists y0 : nat, x0 = (S y0))).
Definition term150 (x0 : nat) := @eq Prop ((x0 = (NUMERAL 0)) \/ (exists y0 : nat, (fun y1 : nat => x0 = (S y1)) y0)).
Definition term385 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) := fun y0 : list a0 => (((@cons a0 x0 x1) = y0) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 y0)) /\ (forall y1 : nat, (Peano.lt y1 (@List.length a0 y0)) -> (@EL a0 y1 (@cons a0 x0 x1)) = (@EL a0 y1 y0)))) -> ((@cons a0 x0 x1) = (@cons a0 x2 y0)) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 (@cons a0 x2 y0))) /\ (forall y1 : nat, (Peano.lt y1 (@List.length a0 (@cons a0 x2 y0))) -> (@EL a0 y1 (@cons a0 x0 x1)) = (@EL a0 y1 (@cons a0 x2 y0)))).
Definition term321 (a0 : Type') (x0 : a0) (x1 : list a0) := (fun y0 : list a0 => forall y1 : list a0, (y0 = y1) = (((@List.length a0 y0) = (@List.length a0 y1)) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> (@EL a0 y2 y0) = (@EL a0 y2 y1)))) (@cons a0 x0 x1).
Definition term428 (a0 : Type') (x0 : list a0) := @eq nat (S (@List.length a0 x0)).
Definition term80 (x0 : nat -> Prop) (x1 : nat) := (~ (x0 (NUMERAL 0))) \/ ((fun y0 : nat => ~ (x0 (S y0))) x1).
Definition term224 (x0 : nat) (x1 : nat) := and (~ (~ (x0 = x1))).
Definition term414 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : list a0) := Peano.lt x0 (@List.length a0 (@cons a0 x1 x2)).
Definition term83 (x0 : nat -> Prop) := fun y0 : nat => (~ (x0 (NUMERAL 0))) \/ (~ (x0 (S y0))).
Definition term419 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : list a0) := (Peano.lt x0 (@List.length a0 (@cons a0 x1 x2))) -> (@EL a0 x0 (@nil a0)) = (@EL a0 x0 (@cons a0 x1 x2)).
Definition term169 (x0 : nat) := fun y0 : nat => (fun y1 : nat => fun y2 : nat => (y1 = (NUMERAL 0)) \/ (y1 = (S y2))) x0 y0.
Definition term398 (a0 : Type') (x0 : a0) (x1 : list a0) := ((((@cons a0 x0 x1) = (@nil a0)) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 (@nil a0))) /\ (forall y0 : nat, (Peano.lt y0 (@List.length a0 (@nil a0))) -> (@EL a0 y0 (@cons a0 x0 x1)) = (@EL a0 y0 (@nil a0))))) /\ (forall y0 : a0, forall y1 : list a0, (((@cons a0 x0 x1) = y1) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 y1)) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> (@EL a0 y2 (@cons a0 x0 x1)) = (@EL a0 y2 y1)))) -> ((@cons a0 x0 x1) = (@cons a0 y0 y1)) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 (@cons a0 y0 y1))) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 (@cons a0 y0 y1))) -> (@EL a0 y2 (@cons a0 x0 x1)) = (@EL a0 y2 (@cons a0 y0 y1)))))) -> forall y0 : list a0, ((@cons a0 x0 x1) = y0) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 y0)) /\ (forall y1 : nat, (Peano.lt y1 (@List.length a0 y0)) -> (@EL a0 y1 (@cons a0 x0 x1)) = (@EL a0 y1 y0))).
Definition term369 (a0 : Type') := ((((@nil a0) = (@nil a0)) = (((@List.length a0 (@nil a0)) = (@List.length a0 (@nil a0))) /\ (forall y0 : nat, (Peano.lt y0 (@List.length a0 (@nil a0))) -> (@EL a0 y0 (@nil a0)) = (@EL a0 y0 (@nil a0))))) /\ (forall y0 : a0, forall y1 : list a0, (((@nil a0) = y1) = (((@List.length a0 (@nil a0)) = (@List.length a0 y1)) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> (@EL a0 y2 (@nil a0)) = (@EL a0 y2 y1)))) -> ((@nil a0) = (@cons a0 y0 y1)) = (((@List.length a0 (@nil a0)) = (@List.length a0 (@cons a0 y0 y1))) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 (@cons a0 y0 y1))) -> (@EL a0 y2 (@nil a0)) = (@EL a0 y2 (@cons a0 y0 y1)))))) -> forall y0 : list a0, ((@nil a0) = y0) = (((@List.length a0 (@nil a0)) = (@List.length a0 y0)) /\ (forall y1 : nat, (Peano.lt y1 (@List.length a0 y0)) -> (@EL a0 y1 (@nil a0)) = (@EL a0 y1 y0))).
Definition term438 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : nat) (x3 : a0) (x4 : list a0) := (Peano.lt x2 (@List.length a0 (@cons a0 x3 x4))) -> (@EL a0 x2 (@cons a0 x0 x1)) = (@EL a0 x2 (@cons a0 x3 x4)).
Definition term222 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (x0 = x2))) /\ (~ (x1 = x2)).
Definition term480 (a0 : Type') (x0 : nat) (x1 : list a0) := Peano.lt (S x0) (S (@List.length a0 x1)).
Definition term42 (x0 : nat -> Prop) := fun y0 : nat => ~ ((fun y1 : nat => x0 y1) y0).
Definition term175 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => (x1 = (NUMERAL 0)) \/ (x1 = (S y0))) (x0 x1).
Definition term373 (a0 : Type') (x0 : a0) (x1 : list a0) := ((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 (@nil a0))) /\ (forall y0 : nat, (Peano.lt y0 (@List.length a0 (@nil a0))) -> (@EL a0 y0 (@cons a0 x0 x1)) = (@EL a0 y0 (@nil a0))).
Definition term433 (a0 : Type') (x0 : a0) (x1 : list a0) := forall y0 : nat, (Peano.lt y0 (@List.length a0 (@nil a0))) -> (@EL a0 y0 (@cons a0 x0 x1)) = (@EL a0 y0 (@nil a0)).
Definition term406 (a0 : Type') := forall y0 : nat, (Peano.lt y0 (@List.length a0 (@nil a0))) -> (@EL a0 y0 (@nil a0)) = (@EL a0 y0 (@nil a0)).
Definition term191 (x0 : Prop) (x1 : Prop) := (x1 = x0) -> x0 \/ (~ x1).
Definition term411 (a0 : Type') := @eq nat (@List.length a0 (@nil a0)).
Definition term67 (x0 : nat -> Prop) := ((forall y0 : nat, x0 y0) /\ ((~ (x0 (NUMERAL 0))) \/ (exists y0 : nat, ~ (x0 (S y0))))) \/ ((exists y0 : nat, ~ (x0 y0)) /\ ((x0 (NUMERAL 0)) /\ (forall y0 : nat, x0 (S y0)))).
Definition term306 (a0 : Type') (x0 : a0) (x1 : list a0) := ~ ((@cons a0 x0 x1) = (@nil a0)).
Definition term108 (x0 : nat -> Prop) := exists y0 : nat, ((fun y1 : nat => ~ (x0 y1)) y0) /\ ((x0 (NUMERAL 0)) /\ (forall y1 : nat, x0 (S y1))).
Definition term288 (x0 : nat) := Peano.lt x0 (NUMERAL 0).
Definition term235 (x0 : nat -> nat) (x1 : nat) := S (x0 x1).
Definition term268 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := @eq Prop ((x0 x2) \/ ((~ (x0 x1)) \/ (~ (x1 = x2)))).
Definition term234 (x0 : nat -> nat) (x1 : nat) := (x1 = (S (x0 x1))) \/ (x1 = (NUMERAL 0)).
Definition term239 (x0 : nat -> nat) (x1 : nat) := ~ (x1 = (S (x0 x1))).
Definition term105 (x0 : nat -> Prop) (x1 : Prop) := (exists y0 : nat, x0 y0) /\ x1.
Definition term323 (a0 : Type') (x0 : a0) (x1 : list a0) := ((fun y0 : list a0 => forall y1 : list a0, (y0 = y1) = (((@List.length a0 y0) = (@List.length a0 y1)) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> (@EL a0 y2 y0) = (@EL a0 y2 y1)))) x1) -> (fun y0 : list a0 => forall y1 : list a0, (y0 = y1) = (((@List.length a0 y0) = (@List.length a0 y1)) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> (@EL a0 y2 y0) = (@EL a0 y2 y1)))) (@cons a0 x0 x1).
Definition term56 (x0 : nat -> Prop) := x0 (NUMERAL 0).
Definition term61 (x0 : nat -> Prop) := and (forall y0 : nat, x0 y0).
Definition term300 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := forall y0 : list a0, ((@cons a0 x0 x2) = (@cons a0 x1 y0)) = ((x0 = x1) /\ (x2 = y0)).
Definition term256 (x0 : nat -> nat) (x1 : nat) := ((x1 = (S (x0 x1))) /\ (x1 = x1)) -> (S (x0 x1)) = x1.
Definition term445 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((S y0) = (S y1)) = (y0 = y1)) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt (S y0) (S y1)) = (Peano.lt y0 y1)) x0.
Definition term432 (a0 : Type') (x0 : a0) (x1 : list a0) := fun y0 : nat => (Peano.lt y0 (@List.length a0 (@nil a0))) -> (@EL a0 y0 (@cons a0 x0 x1)) = (@EL a0 y0 (@nil a0)).
Definition term282 (x0 : nat) := (fun y0 : nat => ~ ((S y0) = (NUMERAL 0))) x0.
Definition term457 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) (x3 : list a0) (x4 : nat) := (fun y0 : nat => (Peano.lt y0 (S (@List.length a0 x3))) -> (@EL a0 y0 (@cons a0 x0 x1)) = (@EL a0 y0 (@cons a0 x2 x3))) x4.
Definition term379 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : list a0) := imp (((@cons a0 x0 x1) = x2) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 x2)) /\ (forall y0 : nat, (Peano.lt y0 (@List.length a0 x2)) -> (@EL a0 y0 (@cons a0 x0 x1)) = (@EL a0 y0 x2)))).
Definition term74 (x0 : nat -> Prop) := ~ (x0 (NUMERAL 0)).
Definition term350 (a0 : Type') (x0 : list a0) := imp (((@nil a0) = x0) = (((@List.length a0 (@nil a0)) = (@List.length a0 x0)) /\ (forall y0 : nat, (Peano.lt y0 (@List.length a0 x0)) -> (@EL a0 y0 (@nil a0)) = (@EL a0 y0 x0)))).
Definition term12 (x0 : nat -> Prop) := ((~ ((forall y0 : nat, x0 y0) = ((x0 (NUMERAL 0)) /\ (forall y0 : nat, x0 (S y0))))) -> (forall y0 : nat, (y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1))) -> False) -> (~ ((forall y0 : nat, x0 y0) = ((x0 (NUMERAL 0)) /\ (forall y0 : nat, x0 (S y0))))) -> (forall y0 : nat, (y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1))) -> False.
Definition term461 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := (fun y0 : nat => (Peano.lt y0 (S (@List.length a0 x3))) -> (@EL a0 y0 (@cons a0 x0 x1)) = (@EL a0 y0 (@cons a0 x2 x3))) (NUMERAL 0).
Definition term451 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) (x3 : list a0) := (x0 = x1) /\ (((@List.length a0 x2) = (@List.length a0 x3)) /\ (forall y0 : nat, (Peano.lt y0 (@List.length a0 x3)) -> (@EL a0 y0 x2) = (@EL a0 y0 x3))).
Definition term474 (a0 : Type') (x0 : list a0) (x1 : list a0) := forall y0 : nat, (Peano.lt y0 (@List.length a0 x1)) -> (@EL a0 y0 x0) = (@EL a0 y0 x1).
Definition term99 (x0 : nat -> Prop) := fun y0 : nat => (forall y1 : nat, x0 y1) /\ ((fun y1 : nat => (~ (x0 (NUMERAL 0))) \/ (~ (x0 (S y1)))) y0).
Definition term418 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : list a0) := @EL a0 x0 (@cons a0 x1 x2).
Definition term82 (x0 : nat -> Prop) := fun y0 : nat => (~ (x0 (NUMERAL 0))) \/ ((fun y1 : nat => ~ (x0 (S y1))) y0).
Definition term500 (a0 : Type') (x0 : a0) (x1 : list a0) := @eq a0 (@EL a0 (NUMERAL 0) (@cons a0 x0 x1)).
Definition term176 (x0 : nat -> nat) (x1 : nat) := (x1 = (NUMERAL 0)) \/ (x1 = (S (x0 x1))).
Definition term421 (a0 : Type') (x0 : a0) (x1 : list a0) := fun y0 : nat => (Peano.lt y0 (@List.length a0 (@cons a0 x0 x1))) -> (@EL a0 y0 (@nil a0)) = (@EL a0 y0 (@cons a0 x0 x1)).
Definition term75 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => ~ (x0 (S y0))) x1.
Definition term496 (a0 : Type') (x0 : list a0) := imp (Peano.lt (NUMERAL 0) (S (@List.length a0 x0))).
Definition term322 (a0 : Type') (x0 : a0) (x1 : list a0) := forall y0 : list a0, ((@cons a0 x0 x1) = y0) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 y0)) /\ (forall y1 : nat, (Peano.lt y1 (@List.length a0 y0)) -> (@EL a0 y1 (@cons a0 x0 x1)) = (@EL a0 y1 y0))).
Definition term318 (a0 : Type') (x0 : list a0) := forall y0 : list a0, (x0 = y0) = (((@List.length a0 x0) = (@List.length a0 y0)) /\ (forall y1 : nat, (Peano.lt y1 (@List.length a0 y0)) -> (@EL a0 y1 x0) = (@EL a0 y1 y0))).
Definition term314 (a0 : Type') := forall y0 : list a0, ((@nil a0) = y0) = (((@List.length a0 (@nil a0)) = (@List.length a0 y0)) /\ (forall y1 : nat, (Peano.lt y1 (@List.length a0 y0)) -> (@EL a0 y1 (@nil a0)) = (@EL a0 y1 y0))).
Definition term258 (x0 : nat -> nat) (x1 : nat) := ~ ((S (x0 x1)) = x1).
Definition term3 (x0 : nat) (x1 : nat) := Peano.lt (S x0) (S x1).
Definition term430 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : nat) := (Peano.lt x2 (@List.length a0 (@nil a0))) -> (@EL a0 x2 (@cons a0 x0 x1)) = (@EL a0 x2 (@nil a0)).
Definition term174 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => fun y1 : nat => (y0 = (NUMERAL 0)) \/ (y0 = (S y1))) x1 (x0 x1).
Definition term434 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := @eq Prop ((@cons a0 x0 x1) = (@cons a0 x2 x3)).
Definition term505 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : a0) (x3 : a0) := ((@List.length a0 x0) = (@List.length a0 x1)) /\ (x2 = x3).
Definition term249 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term190 (x0 : nat -> Prop) (x1 : nat) := (x0 (S x1)) -> False.
Definition term45 (x0 : nat -> Prop) := exists y0 : nat, ~ ((fun y1 : nat => x0 (S y1)) y0).
Definition term38 (x0 : nat -> Prop) := exists y0 : nat, ~ ((fun y1 : nat => x0 y1) y0).
Definition term168 (x0 : nat) (x1 : nat) := (fun y0 : nat => (x0 = (NUMERAL 0)) \/ (x0 = (S y0))) x1.
Definition term453 (a0 : Type') (x0 : list a0) (x1 : list a0) := and ((@List.length a0 x0) = (@List.length a0 x1)).
Definition term171 := fun y0 : nat => exists y1 : nat, (fun y2 : nat => fun y3 : nat => (y2 = (NUMERAL 0)) \/ (y2 = (S y3))) y0 y1.
Definition term284 (x0 : nat) := (~ ((S x0) = (NUMERAL 0))) -> ((S x0) = (NUMERAL 0)) = False.
Definition term452 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) (x3 : list a0) := @eq Prop ((x0 = x1) /\ (((@List.length a0 x2) = (@List.length a0 x3)) /\ (forall y0 : nat, (Peano.lt y0 (@List.length a0 x3)) -> (@EL a0 y0 x2) = (@EL a0 y0 x3)))).
Definition term286 (x0 : nat) := (~ ((NUMERAL 0) = (S x0))) -> ((NUMERAL 0) = (S x0)) = False.
Definition term134 (x0 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => (~ (x0 y1)) /\ ((x0 (NUMERAL 0)) /\ (forall y2 : nat, x0 (S y2)))) y0.
Definition term130 (x0 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => (forall y2 : nat, x0 y2) /\ ((~ (x0 (NUMERAL 0))) \/ (~ (x0 (S y1))))) y0.
Definition term79 (x0 : nat -> Prop) := @eq Prop ((~ (x0 (NUMERAL 0))) \/ (exists y0 : nat, ~ (x0 (S y0)))).
Definition term78 (x0 : nat -> Prop) := @eq Prop ((~ (x0 (NUMERAL 0))) \/ (exists y0 : nat, (fun y1 : nat => ~ (x0 (S y1))) y0)).
Definition term145 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (exists y0 : nat, (fun y1 : nat => x0 = (S y1)) y0).
Definition term195 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term487 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : list a0) := @EL a0 x0 (@tl a0 (@cons a0 x1 x2)).
Definition term47 (x0 : nat -> Prop) (x1 : nat) := ~ ((fun y0 : nat => x0 (S y0)) x1).
Definition term417 (a0 : Type') (x0 : nat) (x1 : list a0) := imp (Peano.lt x0 (S (@List.length a0 x1))).
Definition term203 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (~ ((x0 x2) \/ (~ (x0 x1)))) -> ~ (x1 = x2).
Definition term110 (x0 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => ~ (x0 y1)) y0.
Definition term76 (x0 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => ~ (x0 (S y1))) y0.
Definition term473 (a0 : Type') (x0 : list a0) (x1 : list a0) := (forall y0 : nat, (Peano.lt y0 (@List.length a0 x1)) -> (@EL a0 y0 x0) = (@EL a0 y0 x1)) /\ ((@List.length a0 x0) = (@List.length a0 x1)).
Definition term395 (a0 : Type') (x0 : a0) (x1 : list a0) := imp ((((@cons a0 x0 x1) = (@nil a0)) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 (@nil a0))) /\ (forall y0 : nat, (Peano.lt y0 (@List.length a0 (@nil a0))) -> (@EL a0 y0 (@cons a0 x0 x1)) = (@EL a0 y0 (@nil a0))))) /\ (forall y0 : a0, forall y1 : list a0, (((@cons a0 x0 x1) = y1) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 y1)) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> (@EL a0 y2 (@cons a0 x0 x1)) = (@EL a0 y2 y1)))) -> ((@cons a0 x0 x1) = (@cons a0 y0 y1)) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 (@cons a0 y0 y1))) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 (@cons a0 y0 y1))) -> (@EL a0 y2 (@cons a0 x0 x1)) = (@EL a0 y2 (@cons a0 y0 y1)))))).
Definition term366 (a0 : Type') := imp ((((@nil a0) = (@nil a0)) = (((@List.length a0 (@nil a0)) = (@List.length a0 (@nil a0))) /\ (forall y0 : nat, (Peano.lt y0 (@List.length a0 (@nil a0))) -> (@EL a0 y0 (@nil a0)) = (@EL a0 y0 (@nil a0))))) /\ (forall y0 : a0, forall y1 : list a0, (((@nil a0) = y1) = (((@List.length a0 (@nil a0)) = (@List.length a0 y1)) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> (@EL a0 y2 (@nil a0)) = (@EL a0 y2 y1)))) -> ((@nil a0) = (@cons a0 y0 y1)) = (((@List.length a0 (@nil a0)) = (@List.length a0 (@cons a0 y0 y1))) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 (@cons a0 y0 y1))) -> (@EL a0 y2 (@nil a0)) = (@EL a0 y2 (@cons a0 y0 y1)))))).
Definition term180 (x0 : nat -> nat) := forall y0 : nat, (y0 = (NUMERAL 0)) \/ (y0 = (S (x0 y0))).
Definition term501 (a0 : Type') (x0 : a0) (x1 : a0) := True -> x0 = x1.
Definition term81 (x0 : nat -> Prop) (x1 : nat) := (~ (x0 (NUMERAL 0))) \/ (~ (x0 (S x1))).
Definition term409 (x0 : Prop) := forall y0 : nat, x0.
Definition term27 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (exists y0 : nat, x0 = (S y0)).
Definition term57 (x0 : nat -> Prop) := and (~ (forall y0 : nat, x0 y0)).
Definition term29 (x0 : nat -> Prop) (x1 : nat) := x0 (S x1).
Definition term427 (a0 : Type') (x0 : a0) (x1 : list a0) := @eq nat (@List.length a0 (@cons a0 x0 x1)).
Definition term349 (a0 : Type') (x0 : list a0) := imp ((fun y0 : list a0 => ((@nil a0) = y0) = (((@List.length a0 (@nil a0)) = (@List.length a0 y0)) /\ (forall y1 : nat, (Peano.lt y1 (@List.length a0 y0)) -> (@EL a0 y1 (@nil a0)) = (@EL a0 y1 y0)))) x0).
Definition term472 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := ((@List.length a0 x1) = (@List.length a0 x3)) /\ (((Peano.lt (NUMERAL 0) (S (@List.length a0 x3))) -> (@EL a0 (NUMERAL 0) (@cons a0 x0 x1)) = (@EL a0 (NUMERAL 0) (@cons a0 x2 x3))) /\ (forall y0 : nat, (Peano.lt (S y0) (S (@List.length a0 x3))) -> (@EL a0 (S y0) (@cons a0 x0 x1)) = (@EL a0 (S y0) (@cons a0 x2 x3)))).
Definition term96 (x0 : nat -> Prop) := @eq Prop ((forall y0 : nat, x0 y0) /\ (exists y0 : nat, (~ (x0 (NUMERAL 0))) \/ (~ (x0 (S y0))))).
Definition term95 (x0 : nat -> Prop) := @eq Prop ((forall y0 : nat, x0 y0) /\ (exists y0 : nat, (fun y1 : nat => (~ (x0 (NUMERAL 0))) \/ (~ (x0 (S y1)))) y0)).
Definition term253 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term37 (x0 : nat -> Prop) := ~ (forall y0 : nat, x0 y0).
Definition term272 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (x2 = x0) /\ (x1 x2).
Definition term238 (x0 : nat -> nat) (x1 : nat) := (~ (x1 = (S (x0 x1)))) -> x1 = (S (x0 x1)).
Definition term464 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := and ((Peano.lt (NUMERAL 0) (S (@List.length a0 x3))) -> (@EL a0 (NUMERAL 0) (@cons a0 x0 x1)) = (@EL a0 (NUMERAL 0) (@cons a0 x2 x3))).
Definition term156 (x0 : nat) := exists y0 : nat, (x0 = (NUMERAL 0)) \/ (x0 = (S y0)).
Definition term49 (x0 : nat -> Prop) := fun y0 : nat => ~ ((fun y1 : nat => x0 (S y1)) y0).
Definition term126 (x0 : nat -> Prop) (x1 : nat -> Prop) := exists y0 : nat, (x0 y0) \/ (x1 y0).
Definition term470 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := forall y0 : nat, (Peano.lt (S y0) (S (@List.length a0 x3))) -> (@EL a0 (S y0) (@cons a0 x0 x1)) = (@EL a0 (S y0) (@cons a0 x2 x3)).
Definition term443 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := forall y0 : nat, (Peano.lt y0 (S (@List.length a0 x3))) -> (@EL a0 y0 (@cons a0 x0 x1)) = (@EL a0 y0 (@cons a0 x2 x3)).
Definition term442 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := forall y0 : nat, (Peano.lt y0 (@List.length a0 (@cons a0 x2 x3))) -> (@EL a0 y0 (@cons a0 x0 x1)) = (@EL a0 y0 (@cons a0 x2 x3)).
Definition term424 (a0 : Type') (x0 : a0) (x1 : list a0) := forall y0 : nat, (Peano.lt y0 (S (@List.length a0 x1))) -> (@EL a0 y0 (@nil a0)) = (@EL a0 y0 (@cons a0 x0 x1)).
Definition term423 (a0 : Type') (x0 : a0) (x1 : list a0) := forall y0 : nat, (Peano.lt y0 (@List.length a0 (@cons a0 x0 x1))) -> (@EL a0 y0 (@nil a0)) = (@EL a0 y0 (@cons a0 x0 x1)).
Definition term97 (x0 : nat -> Prop) (x1 : nat) := (forall y0 : nat, x0 y0) /\ ((fun y0 : nat => (~ (x0 (NUMERAL 0))) \/ (~ (x0 (S y0)))) x1).
Definition term456 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := ((fun y0 : nat => (Peano.lt y0 (S (@List.length a0 x3))) -> (@EL a0 y0 (@cons a0 x0 x1)) = (@EL a0 y0 (@cons a0 x2 x3))) (NUMERAL 0)) /\ (forall y0 : nat, (fun y1 : nat => (Peano.lt y1 (S (@List.length a0 x3))) -> (@EL a0 y1 (@cons a0 x0 x1)) = (@EL a0 y1 (@cons a0 x2 x3))) (S y0)).
Definition term375 (a0 : Type') (x0 : a0) (x1 : list a0) := and (((@cons a0 x0 x1) = (@nil a0)) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 (@nil a0))) /\ (forall y0 : nat, (Peano.lt y0 (@List.length a0 (@nil a0))) -> (@EL a0 y0 (@cons a0 x0 x1)) = (@EL a0 y0 (@nil a0))))).
Definition term208 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (~ (x1 x0)) /\ (~ (~ (x1 x2))).
Definition term486 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : list a0) := @EL a0 (S x0) (@cons a0 x1 x2).
Definition term55 (x0 : nat -> Prop) := ~ ((x0 (NUMERAL 0)) /\ (forall y0 : nat, x0 (S y0))).
Definition term85 (x0 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (exists y0 : nat, (~ (x0 (NUMERAL 0))) \/ (~ (x0 (S y0)))).
Definition term212 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := imp (~ ((x1 x0) \/ (~ (x1 x2)))).
Definition term103 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term481 (a0 : Type') (x0 : nat) (x1 : list a0) := Peano.lt x0 (@List.length a0 x1).
Definition term220 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term142 (x0 : nat -> Prop) := fun y0 : nat => ((fun y1 : nat => (forall y2 : nat, x0 y2) /\ ((~ (x0 (NUMERAL 0))) \/ (~ (x0 (S y1))))) y0) \/ ((fun y1 : nat => (~ (x0 y1)) /\ ((x0 (NUMERAL 0)) /\ (forall y2 : nat, x0 (S y2)))) y0).
Definition term441 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := fun y0 : nat => (Peano.lt y0 (S (@List.length a0 x3))) -> (@EL a0 y0 (@cons a0 x0 x1)) = (@EL a0 y0 (@cons a0 x2 x3)).
Definition term132 (x0 : nat -> Prop) := or (exists y0 : nat, (fun y1 : nat => (forall y2 : nat, x0 y2) /\ ((~ (x0 (NUMERAL 0))) \/ (~ (x0 (S y1))))) y0).
Definition term342 (a0 : Type') := fun y0 : list a0 => ((@nil a0) = y0) = (((@List.length a0 (@nil a0)) = (@List.length a0 y0)) /\ (forall y1 : nat, (Peano.lt y1 (@List.length a0 y0)) -> (@EL a0 y1 (@nil a0)) = (@EL a0 y1 y0))).
Definition term31 (x0 : nat -> Prop) := forall y0 : nat, x0 (S y0).
Definition term263 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (~ (x2 = x0)) \/ (~ (x1 x2)).
Definition term223 (x0 : nat) (x1 : nat) := ~ (~ (x0 = x1)).
Definition term14 (x0 : nat -> Prop) := (((~ ((forall y0 : nat, x0 y0) = ((x0 (NUMERAL 0)) /\ (forall y0 : nat, x0 (S y0))))) -> (forall y0 : nat, (y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1))) -> False) -> (~ ((forall y0 : nat, x0 y0) = ((x0 (NUMERAL 0)) /\ (forall y0 : nat, x0 (S y0))))) -> (forall y0 : nat, (y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1))) -> False) -> ((~ ((forall y0 : nat, x0 y0) = ((x0 (NUMERAL 0)) /\ (forall y0 : nat, x0 (S y0))))) -> (forall y0 : nat, (y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1))) -> False) -> (~ ((forall y0 : nat, x0 y0) = ((x0 (NUMERAL 0)) /\ (forall y0 : nat, x0 (S y0))))) -> (forall y0 : nat, (y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1))) -> False.
Definition term154 (x0 : nat) := fun y0 : nat => (x0 = (NUMERAL 0)) \/ ((fun y1 : nat => x0 = (S y1)) y0).
Definition term140 (x0 : nat -> Prop) (x1 : nat) := ((fun y0 : nat => (forall y1 : nat, x0 y1) /\ ((~ (x0 (NUMERAL 0))) \/ (~ (x0 (S y0))))) x1) \/ ((fun y0 : nat => (~ (x0 y0)) /\ ((x0 (NUMERAL 0)) /\ (forall y1 : nat, x0 (S y1)))) x1).
Definition term344 (a0 : Type') := ((@List.length a0 (@nil a0)) = (@List.length a0 (@nil a0))) /\ (forall y0 : nat, (Peano.lt y0 (@List.length a0 (@nil a0))) -> (@EL a0 y0 (@nil a0)) = (@EL a0 y0 (@nil a0))).
Definition term309 (a0 : Type') (x0 : a0) (x1 : list a0) := (~ ((@nil a0) = (@cons a0 x0 x1))) -> ((@nil a0) = (@cons a0 x0 x1)) = False.
Definition term241 (x0 : nat) (x1 : nat) := or (~ (x0 = x1)).
Definition term98 (x0 : nat -> Prop) (x1 : nat) := (forall y0 : nat, x0 y0) /\ ((~ (x0 (NUMERAL 0))) \/ (~ (x0 (S x1)))).
Definition term377 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : list a0) := ((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 x2)) /\ (forall y0 : nat, (Peano.lt y0 (@List.length a0 x2)) -> (@EL a0 y0 (@cons a0 x0 x1)) = (@EL a0 y0 x2)).
Definition term447 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((S x0) = (S y0)) = (x0 = y0)) x1.
Definition term492 (a0 : Type') (x0 : list a0) (x1 : list a0) := fun y0 : nat => (Peano.lt y0 (@List.length a0 x1)) -> (@EL a0 y0 x0) = (@EL a0 y0 x1).
Definition term397 (a0 : Type') (x0 : a0) (x1 : list a0) := forall y0 : list a0, (fun y1 : list a0 => ((@cons a0 x0 x1) = y1) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 y1)) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> (@EL a0 y2 (@cons a0 x0 x1)) = (@EL a0 y2 y1)))) y0.
Definition term368 (a0 : Type') := forall y0 : list a0, (fun y1 : list a0 => ((@nil a0) = y1) = (((@List.length a0 (@nil a0)) = (@List.length a0 y1)) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> (@EL a0 y2 (@nil a0)) = (@EL a0 y2 y1)))) y0.
Definition term189 (x0 : nat -> Prop) (x1 : nat) := (~ (x0 (S x1))) -> x0 (S x1).
Definition term160 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term466 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : nat) (x3 : a0) (x4 : list a0) := (Peano.lt (S x2) (S (@List.length a0 x4))) -> (@EL a0 (S x2) (@cons a0 x0 x1)) = (@EL a0 (S x2) (@cons a0 x3 x4)).
Definition term391 (a0 : Type') (x0 : a0) (x1 : list a0) := forall y0 : a0, forall y1 : list a0, (((@cons a0 x0 x1) = y1) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 y1)) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> (@EL a0 y2 (@cons a0 x0 x1)) = (@EL a0 y2 y1)))) -> ((@cons a0 x0 x1) = (@cons a0 y0 y1)) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 (@cons a0 y0 y1))) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 (@cons a0 y0 y1))) -> (@EL a0 y2 (@cons a0 x0 x1)) = (@EL a0 y2 (@cons a0 y0 y1)))).
Definition term390 (a0 : Type') (x0 : a0) (x1 : list a0) := forall y0 : a0, forall y1 : list a0, ((fun y2 : list a0 => ((@cons a0 x0 x1) = y2) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 y2)) /\ (forall y3 : nat, (Peano.lt y3 (@List.length a0 y2)) -> (@EL a0 y3 (@cons a0 x0 x1)) = (@EL a0 y3 y2)))) y1) -> (fun y2 : list a0 => ((@cons a0 x0 x1) = y2) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 y2)) /\ (forall y3 : nat, (Peano.lt y3 (@List.length a0 y2)) -> (@EL a0 y3 (@cons a0 x0 x1)) = (@EL a0 y3 y2)))) (@cons a0 y0 y1).
Definition term362 (a0 : Type') := forall y0 : a0, forall y1 : list a0, (((@nil a0) = y1) = (((@List.length a0 (@nil a0)) = (@List.length a0 y1)) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> (@EL a0 y2 (@nil a0)) = (@EL a0 y2 y1)))) -> ((@nil a0) = (@cons a0 y0 y1)) = (((@List.length a0 (@nil a0)) = (@List.length a0 (@cons a0 y0 y1))) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 (@cons a0 y0 y1))) -> (@EL a0 y2 (@nil a0)) = (@EL a0 y2 (@cons a0 y0 y1)))).
Definition term361 (a0 : Type') := forall y0 : a0, forall y1 : list a0, ((fun y2 : list a0 => ((@nil a0) = y2) = (((@List.length a0 (@nil a0)) = (@List.length a0 y2)) /\ (forall y3 : nat, (Peano.lt y3 (@List.length a0 y2)) -> (@EL a0 y3 (@nil a0)) = (@EL a0 y3 y2)))) y1) -> (fun y2 : list a0 => ((@nil a0) = y2) = (((@List.length a0 (@nil a0)) = (@List.length a0 y2)) /\ (forall y3 : nat, (Peano.lt y3 (@List.length a0 y2)) -> (@EL a0 y3 (@nil a0)) = (@EL a0 y3 y2)))) (@cons a0 y0 y1).
Definition term332 (a0 : Type') := forall y0 : a0, forall y1 : list a0, (forall y2 : list a0, (y1 = y2) = (((@List.length a0 y1) = (@List.length a0 y2)) /\ (forall y3 : nat, (Peano.lt y3 (@List.length a0 y2)) -> (@EL a0 y3 y1) = (@EL a0 y3 y2)))) -> forall y2 : list a0, ((@cons a0 y0 y1) = y2) = (((@List.length a0 (@cons a0 y0 y1)) = (@List.length a0 y2)) /\ (forall y3 : nat, (Peano.lt y3 (@List.length a0 y2)) -> (@EL a0 y3 (@cons a0 y0 y1)) = (@EL a0 y3 y2))).
Definition term331 (a0 : Type') := forall y0 : a0, forall y1 : list a0, ((fun y2 : list a0 => forall y3 : list a0, (y2 = y3) = (((@List.length a0 y2) = (@List.length a0 y3)) /\ (forall y4 : nat, (Peano.lt y4 (@List.length a0 y3)) -> (@EL a0 y4 y2) = (@EL a0 y4 y3)))) y1) -> (fun y2 : list a0 => forall y3 : list a0, (y2 = y3) = (((@List.length a0 y2) = (@List.length a0 y3)) /\ (forall y4 : nat, (Peano.lt y4 (@List.length a0 y3)) -> (@EL a0 y4 y2) = (@EL a0 y4 y3)))) (@cons a0 y0 y1).
Definition term289 (a0 : Type') := forall y0 : a0, forall y1 : list a0, (@List.length a0 (@cons a0 y0 y1)) = (S (@List.length a0 y1)).
Definition term21 := fun y0 : nat -> Prop => (~ ((forall y1 : nat, y0 y1) = ((y0 (NUMERAL 0)) /\ (forall y1 : nat, y0 (S y1))))) -> ~ (forall y1 : nat, (y1 = (NUMERAL 0)) \/ (exists y2 : nat, y1 = (S y2))).
Definition term124 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term274 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := imp ((x2 = x0) /\ (x1 x2)).
Definition term302 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) (x3 : list a0) := (x0 = x1) /\ (x2 = x3).
Definition term254 (x0 : nat) (x1 : nat) (x2 : nat) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term36 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term70 (x0 : Prop) (x1 : nat -> Prop) := x0 \/ (exists y0 : nat, x1 y0).
Definition term50 (x0 : nat -> Prop) := fun y0 : nat => ~ (x0 (S y0)).
Definition term148 (x0 : nat) := fun y0 : nat => (fun y1 : nat => x0 = (S y1)) y0.
Definition term316 (a0 : Type') := and (forall y0 : list a0, ((@nil a0) = y0) = (((@List.length a0 (@nil a0)) = (@List.length a0 y0)) /\ (forall y1 : nat, (Peano.lt y1 (@List.length a0 y0)) -> (@EL a0 y1 (@nil a0)) = (@EL a0 y1 y0)))).
Definition term63 (x0 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ ((~ (x0 (NUMERAL 0))) \/ (exists y0 : nat, ~ (x0 (S y0)))).
Definition term207 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ~ ((x1 x0) \/ (~ (x1 x2))).
Definition term221 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term7 (x0 : nat -> Prop) := forall y0 : nat, x0 y0.
Definition term477 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) (x3 : list a0) := (forall y0 : nat, (Peano.lt y0 (@List.length a0 x3)) -> (@EL a0 y0 x2) = (@EL a0 y0 x3)) /\ ((x0 = x1) /\ ((@List.length a0 x2) = (@List.length a0 x3))).
Definition term324 (a0 : Type') (x0 : a0) (x1 : list a0) := (forall y0 : list a0, (x1 = y0) = (((@List.length a0 x1) = (@List.length a0 y0)) /\ (forall y1 : nat, (Peano.lt y1 (@List.length a0 y0)) -> (@EL a0 y1 x1) = (@EL a0 y1 y0)))) -> forall y0 : list a0, ((@cons a0 x0 x1) = y0) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 y0)) /\ (forall y1 : nat, (Peano.lt y1 (@List.length a0 y0)) -> (@EL a0 y1 (@cons a0 x0 x1)) = (@EL a0 y1 y0))).
Definition term491 (a0 : Type') (x0 : list a0) (x1 : nat) (x2 : list a0) := (Peano.lt x1 (@List.length a0 x2)) -> (@EL a0 x1 x0) = (@EL a0 x1 x2).
Definition term125 (x0 : nat -> Prop) (x1 : nat -> Prop) := (exists y0 : nat, x0 y0) \/ (exists y0 : nat, x1 y0).
Definition term192 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ((x1 x2) = (x1 x0)) -> (x1 x0) \/ (~ (x1 x2)).
Definition term482 (a0 : Type') (x0 : nat) (x1 : list a0) := imp (Peano.lt (S x0) (S (@List.length a0 x1))).
Definition term504 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : a0) (x3 : a0) := (forall y0 : nat, (Peano.lt y0 (@List.length a0 x1)) -> (@EL a0 y0 x0) = (@EL a0 y0 x1)) /\ (((@List.length a0 x0) = (@List.length a0 x1)) /\ (x2 = x3)).
Definition term201 (x0 : Prop) := x0 -> ~ x0.
Definition term43 (x0 : nat -> Prop) := fun y0 : nat => ~ (x0 y0).
Definition term277 (x0 : nat -> nat) (x1 : nat -> Prop) (x2 : nat) := (((S (x0 x2)) = x2) /\ (x1 (S (x0 x2)))) -> x1 x2.
Definition term392 (a0 : Type') (x0 : a0) (x1 : list a0) := ((fun y0 : list a0 => ((@cons a0 x0 x1) = y0) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 y0)) /\ (forall y1 : nat, (Peano.lt y1 (@List.length a0 y0)) -> (@EL a0 y1 (@cons a0 x0 x1)) = (@EL a0 y1 y0)))) (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, ((fun y2 : list a0 => ((@cons a0 x0 x1) = y2) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 y2)) /\ (forall y3 : nat, (Peano.lt y3 (@List.length a0 y2)) -> (@EL a0 y3 (@cons a0 x0 x1)) = (@EL a0 y3 y2)))) y1) -> (fun y2 : list a0 => ((@cons a0 x0 x1) = y2) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 y2)) /\ (forall y3 : nat, (Peano.lt y3 (@List.length a0 y2)) -> (@EL a0 y3 (@cons a0 x0 x1)) = (@EL a0 y3 y2)))) (@cons a0 y0 y1)).
Definition term363 (a0 : Type') := ((fun y0 : list a0 => ((@nil a0) = y0) = (((@List.length a0 (@nil a0)) = (@List.length a0 y0)) /\ (forall y1 : nat, (Peano.lt y1 (@List.length a0 y0)) -> (@EL a0 y1 (@nil a0)) = (@EL a0 y1 y0)))) (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, ((fun y2 : list a0 => ((@nil a0) = y2) = (((@List.length a0 (@nil a0)) = (@List.length a0 y2)) /\ (forall y3 : nat, (Peano.lt y3 (@List.length a0 y2)) -> (@EL a0 y3 (@nil a0)) = (@EL a0 y3 y2)))) y1) -> (fun y2 : list a0 => ((@nil a0) = y2) = (((@List.length a0 (@nil a0)) = (@List.length a0 y2)) /\ (forall y3 : nat, (Peano.lt y3 (@List.length a0 y2)) -> (@EL a0 y3 (@nil a0)) = (@EL a0 y3 y2)))) (@cons a0 y0 y1)).
Definition term228 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((x0 = x2) /\ (~ (x1 = x2))).
Definition term230 (x0 : nat) := (x0 = x0) /\ (~ ((NUMERAL 0) = x0)).
Definition term325 (a0 : Type') (x0 : a0) := fun y0 : list a0 => ((fun y1 : list a0 => forall y2 : list a0, (y1 = y2) = (((@List.length a0 y1) = (@List.length a0 y2)) /\ (forall y3 : nat, (Peano.lt y3 (@List.length a0 y2)) -> (@EL a0 y3 y1) = (@EL a0 y3 y2)))) y0) -> (fun y1 : list a0 => forall y2 : list a0, (y1 = y2) = (((@List.length a0 y1) = (@List.length a0 y2)) /\ (forall y3 : nat, (Peano.lt y3 (@List.length a0 y2)) -> (@EL a0 y3 y1) = (@EL a0 y3 y2)))) (@cons a0 x0 y0).
Definition term62 (x0 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (~ ((x0 (NUMERAL 0)) /\ (forall y0 : nat, x0 (S y0)))).
Definition term400 (a0 : Type') := and ((@List.length a0 (@nil a0)) = (@List.length a0 (@nil a0))).
Definition term100 (x0 : nat -> Prop) := fun y0 : nat => (forall y1 : nat, x0 y1) /\ ((~ (x0 (NUMERAL 0))) \/ (~ (x0 (S y0)))).
Definition term4 (x0 : nat) := (fun y0 : nat => Peano.lt (NUMERAL 0) (S y0)) x0.
Definition term393 (a0 : Type') (x0 : a0) (x1 : list a0) := (((@cons a0 x0 x1) = (@nil a0)) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 (@nil a0))) /\ (forall y0 : nat, (Peano.lt y0 (@List.length a0 (@nil a0))) -> (@EL a0 y0 (@cons a0 x0 x1)) = (@EL a0 y0 (@nil a0))))) /\ (forall y0 : a0, forall y1 : list a0, (((@cons a0 x0 x1) = y1) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 y1)) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> (@EL a0 y2 (@cons a0 x0 x1)) = (@EL a0 y2 y1)))) -> ((@cons a0 x0 x1) = (@cons a0 y0 y1)) = (((@List.length a0 (@cons a0 x0 x1)) = (@List.length a0 (@cons a0 y0 y1))) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 (@cons a0 y0 y1))) -> (@EL a0 y2 (@cons a0 x0 x1)) = (@EL a0 y2 (@cons a0 y0 y1))))).
Definition term364 (a0 : Type') := (((@nil a0) = (@nil a0)) = (((@List.length a0 (@nil a0)) = (@List.length a0 (@nil a0))) /\ (forall y0 : nat, (Peano.lt y0 (@List.length a0 (@nil a0))) -> (@EL a0 y0 (@nil a0)) = (@EL a0 y0 (@nil a0))))) /\ (forall y0 : a0, forall y1 : list a0, (((@nil a0) = y1) = (((@List.length a0 (@nil a0)) = (@List.length a0 y1)) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> (@EL a0 y2 (@nil a0)) = (@EL a0 y2 y1)))) -> ((@nil a0) = (@cons a0 y0 y1)) = (((@List.length a0 (@nil a0)) = (@List.length a0 (@cons a0 y0 y1))) /\ (forall y2 : nat, (Peano.lt y2 (@List.length a0 (@cons a0 y0 y1))) -> (@EL a0 y2 (@nil a0)) = (@EL a0 y2 (@cons a0 y0 y1))))).
Definition term502 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : a0) (x3 : a0) := (forall y0 : nat, (Peano.lt y0 (@List.length a0 x1)) -> (@EL a0 y0 x0) = (@EL a0 y0 x1)) /\ (x2 = x3).
Definition term91 (x0 : nat -> Prop) := exists y0 : nat, (forall y1 : nat, x0 y1) /\ ((fun y1 : nat => (~ (x0 (NUMERAL 0))) \/ (~ (x0 (S y1)))) y0).
Definition term137 (x0 : nat -> Prop) := @eq Prop ((exists y0 : nat, (forall y1 : nat, x0 y1) /\ ((~ (x0 (NUMERAL 0))) \/ (~ (x0 (S y0))))) \/ (exists y0 : nat, (~ (x0 y0)) /\ ((x0 (NUMERAL 0)) /\ (forall y1 : nat, x0 (S y1))))).
Definition term136 (x0 : nat -> Prop) := @eq Prop ((exists y0 : nat, (fun y1 : nat => (forall y2 : nat, x0 y2) /\ ((~ (x0 (NUMERAL 0))) \/ (~ (x0 (S y1))))) y0) \/ (exists y0 : nat, (fun y1 : nat => (~ (x0 y1)) /\ ((x0 (NUMERAL 0)) /\ (forall y2 : nat, x0 (S y2)))) y0)).
