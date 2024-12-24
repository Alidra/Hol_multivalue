Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term61 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := (~ ((x2 (Nat.sub x0 x1)) = (forall y0 : nat, ((x0 = (Nat.add x1 y0)) \/ ((Peano.lt x0 x1) /\ (y0 = (NUMERAL 0)))) -> x2 y0))) -> (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> (forall y0 : nat, forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) = (Peano.le y0 y1)) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> False.
Definition term410 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) (x3 : nat) (x4 : Prop) := ((((Nat.add x0 x2) = (Nat.add x0 x3)) \/ ((Peano.lt (Nat.add x0 x2) x0) /\ (x3 = (NUMERAL 0)))) = (x2 = x3)) -> ((x2 = x3) -> (x1 x3) = x4) -> ((((Nat.add x0 x2) = (Nat.add x0 x3)) \/ ((Peano.lt (Nat.add x0 x2) x0) /\ (x3 = (NUMERAL 0)))) -> x1 x3) = ((x2 = x3) -> x4).
Definition term339 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term498 (x0 : nat -> Prop) (x1 : nat) := (x1 = x1) -> x0 x1.
Definition term485 (x0 : nat -> Prop) := fun y0 : nat => x0 y0.
Definition term311 (x0 : nat) (x1 : nat) := (Peano.lt x1 x0) /\ (Peano.le x0 x1).
Definition term349 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ~ ((~ (x2 = x0)) \/ (~ (x1 x2))).
Definition term403 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat) (x4 : Prop) (x5 : Prop) := ((((Nat.add x1 x0) = (Nat.add x1 x3)) \/ ((Peano.lt (Nat.add x1 x0) x1) /\ (x3 = (NUMERAL 0)))) = x4) -> (x4 -> (x2 x3) = x5) -> ((((Nat.add x1 x0) = (Nat.add x1 x3)) \/ ((Peano.lt (Nat.add x1 x0) x1) /\ (x3 = (NUMERAL 0)))) -> x2 x3) = (x4 -> x5).
Definition term266 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 y2)) \/ (~ (Peano.le y2 y1))) y0) /\ ((fun y1 : nat => forall y2 : nat, (Peano.lt y1 y2) \/ (Peano.le y2 y1)) y0).
Definition term215 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, ((Nat.sub y1 y2) = (NUMERAL 0)) \/ (~ (Peano.le y1 y2))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ ((Nat.sub y1 y2) = (NUMERAL 0))) \/ (Peano.le y1 y2)) y0).
Definition term98 (x0 : nat) (x1 : nat) (x2 : nat) := and (~ (x0 = (Nat.add x1 x2))).
Definition term110 (x0 : nat -> Prop) := ~ (all x0).
Definition term314 := (~ False) -> False.
Definition term286 (x0 : nat -> Prop) (x1 : nat) := ~ (x0 x1).
Definition term107 (x0 : nat) (x1 : nat) (x2 : nat) := or ((~ (x0 = (Nat.add x1 x2))) /\ ((~ (Peano.lt x0 x1)) \/ (~ (x2 = (NUMERAL 0))))).
Definition term484 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (fun y0 : nat => (~ (x0 = y0)) \/ (x1 y0)) x2.
Definition term369 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat) := @eq Prop ((~ (Peano.lt x0 x1)) \/ ((~ (x3 = (NUMERAL 0))) \/ (x2 x3))).
Definition term241 (x0 : nat) := fun y0 : nat => (Peano.lt x0 y0) \/ (Peano.le y0 x0).
Definition term95 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := @eq Prop (x0 (Nat.sub x1 x2)).
Definition term461 (x0 : nat) (x1 : nat -> Prop) := @eq Prop ((x1 x0) /\ (exists y0 : nat, (x0 = y0) /\ (~ (x1 y0)))).
Definition term460 (x0 : nat) (x1 : nat -> Prop) := @eq Prop ((x1 x0) /\ (exists y0 : nat, (fun y1 : nat => (x0 = y1) /\ (~ (x1 y1))) y0)).
Definition term301 (x0 : nat -> Prop) (x1 : nat) := @eq Prop (~ (x0 x1)).
Definition term371 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat) := (~ ((~ (Peano.lt x0 x1)) \/ (~ (x3 = (NUMERAL 0))))) -> x2 x3.
Definition term433 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ~ ((x0 = x2) -> x1 x2).
Definition term2 (x0 : nat) := fun y0 : nat => (Peano.lt y0 x0) = (~ (Peano.le x0 y0)).
Definition term492 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (x0 x2) \/ (~ (x1 = x2)).
Definition term447 (x0 : nat) (x1 : nat -> Prop) := (~ (x1 x0)) /\ (forall y0 : nat, (~ (x0 = y0)) \/ (x1 y0)).
Definition term446 (x0 : nat) (x1 : nat -> Prop) := (~ (x1 x0)) /\ (forall y0 : nat, (x0 = y0) -> x1 y0).
Definition term4 (x0 : nat) := forall y0 : nat, (Peano.lt y0 x0) = (~ (Peano.le x0 y0)).
Definition term259 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 y2)) \/ (~ (Peano.le y2 y1))) y0) /\ ((fun y1 : nat => forall y2 : nat, (Peano.lt y1 y2) \/ (Peano.le y2 y1)) y0).
Definition term238 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => (~ (Peano.lt x0 y1)) \/ (~ (Peano.le y1 x0))) y0) /\ ((fun y1 : nat => (Peano.lt x0 y1) \/ (Peano.le y1 x0)) y0).
Definition term207 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.sub y1 y2) = (NUMERAL 0)) \/ (~ (Peano.le y1 y2))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ ((Nat.sub y1 y2) = (NUMERAL 0))) \/ (Peano.le y1 y2)) y0).
Definition term182 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => ((Nat.sub x0 y1) = (NUMERAL 0)) \/ (~ (Peano.le x0 y1))) y0) /\ ((fun y1 : nat => (~ ((Nat.sub x0 y1) = (NUMERAL 0))) \/ (Peano.le x0 y1)) y0).
Definition term119 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := fun y0 : nat => ((~ (x0 = (Nat.add x1 y0))) /\ ((~ (Peano.lt x0 x1)) \/ (~ (y0 = (NUMERAL 0))))) \/ (x2 y0).
Definition term68 (x0 : nat) (x1 : nat -> Prop) := forall y0 : nat, (Peano.lt y0 x0) -> (~ ((x1 (Nat.sub y0 x0)) = (forall y1 : nat, ((y0 = (Nat.add x0 y1)) \/ ((Peano.lt y0 x0) /\ (y1 = (NUMERAL 0)))) -> x1 y1))) -> (forall y1 : nat, forall y2 : nat, Peano.le y1 (Nat.add y1 y2)) -> (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> Peano.le y1 y2) -> (forall y1 : nat, forall y2 : nat, ((Nat.sub y1 y2) = (NUMERAL 0)) = (Peano.le y1 y2)) -> ~ (forall y1 : nat, forall y2 : nat, (~ (Peano.lt y1 y2)) = (Peano.le y2 y1)).
Definition term67 (x0 : nat) (x1 : nat -> Prop) := forall y0 : nat, (Peano.lt y0 x0) -> (~ ((x1 (Nat.sub y0 x0)) = (forall y1 : nat, ((y0 = (Nat.add x0 y1)) \/ ((Peano.lt y0 x0) /\ (y1 = (NUMERAL 0)))) -> x1 y1))) -> (forall y1 : nat, forall y2 : nat, Peano.le y1 (Nat.add y1 y2)) -> (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> Peano.le y1 y2) -> (forall y1 : nat, forall y2 : nat, ((Nat.sub y1 y2) = (NUMERAL 0)) = (Peano.le y1 y2)) -> (forall y1 : nat, forall y2 : nat, (~ (Peano.lt y1 y2)) = (Peano.le y2 y1)) -> False.
Definition term191 (x0 : nat) (x1 : nat) := (~ ((Nat.sub x0 x1) = (NUMERAL 0))) \/ (Peano.le x0 x1).
Definition term81 (x0 : nat) := fun y0 : nat => ((Nat.sub x0 y0) = (NUMERAL 0)) = (Peano.le x0 y0).
Definition term327 (x0 : Prop) := ~ (~ x0).
Definition term9 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) = (y1 = y2)) x0.
Definition term60 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := imp (~ ((x2 (Nat.sub x0 x1)) = (forall y0 : nat, ((x0 = (Nat.add x1 y0)) \/ ((Peano.lt x0 x1) /\ (y0 = (NUMERAL 0)))) -> x2 y0))).
Definition term444 (x0 : nat) (x1 : nat -> Prop) := forall y0 : nat, (~ (x0 = y0)) \/ (x1 y0).
Definition term365 (x0 : nat -> Prop) (x1 : nat) := (x0 x1) \/ (~ (x1 = (NUMERAL 0))).
Definition term392 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := @eq Prop ((x2 (Nat.sub x0 x1)) = (forall y0 : nat, ((x0 = (Nat.add x1 y0)) \/ ((Peano.lt x0 x1) /\ (y0 = (NUMERAL 0)))) -> x2 y0)).
Definition term429 := fun y0 : nat -> Prop => forall y1 : nat, (~ ((y0 y1) = (forall y2 : nat, (y1 = y2) -> y0 y2))) -> False.
Definition term350 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (~ (~ (x2 = x0))) /\ (~ (~ (x1 x2))).
Definition term129 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := ((x2 (Nat.sub x0 x1)) /\ (~ (forall y0 : nat, ((x0 = (Nat.add x1 y0)) \/ ((Peano.lt x0 x1) /\ (y0 = (NUMERAL 0)))) -> x2 y0))) \/ ((~ (x2 (Nat.sub x0 x1))) /\ (forall y0 : nat, ((x0 = (Nat.add x1 y0)) \/ ((Peano.lt x0 x1) /\ (y0 = (NUMERAL 0)))) -> x2 y0)).
Definition term441 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (x0 = y0) /\ (~ (x1 y0)).
Definition term389 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := x0 (Nat.sub (Nat.add x2 x1) x2).
Definition term399 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.add x1 x0) = (Nat.add x1 x2)) \/ ((Peano.lt (Nat.add x1 x0) x1) /\ (x2 = (NUMERAL 0))).
Definition term246 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (~ (Peano.lt x0 y1)) \/ (~ (Peano.le y1 x0))) y0) /\ ((fun y1 : nat => (Peano.lt x0 y1) \/ (Peano.le y1 x0)) y0).
Definition term193 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => ((Nat.sub x0 y1) = (NUMERAL 0)) \/ (~ (Peano.le x0 y1))) y0) /\ ((fun y1 : nat => (~ ((Nat.sub x0 y1) = (NUMERAL 0))) \/ (Peano.le x0 y1)) y0).
Definition term366 (x0 : nat) (x1 : nat) := or (~ (Peano.lt x0 x1)).
Definition term1 (x0 : nat) := fun y0 : nat => (~ (Peano.le x0 y0)) = (Peano.lt y0 x0).
Definition term45 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := ((Peano.lt x0 x1) -> (~ ((x2 (Nat.sub x0 x1)) = (forall y0 : nat, ((x0 = (Nat.add x1 y0)) \/ ((Peano.lt x0 x1) /\ (y0 = (NUMERAL 0)))) -> x2 y0))) -> (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> (forall y0 : nat, forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) = (Peano.le y0 y1)) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> False) -> (Peano.lt x0 x1) -> (~ ((x2 (Nat.sub x0 x1)) = (forall y0 : nat, ((x0 = (Nat.add x1 y0)) \/ ((Peano.lt x0 x1) /\ (y0 = (NUMERAL 0)))) -> x2 y0))) -> (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> (forall y0 : nat, forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) = (Peano.le y0 y1)) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> False.
Definition term90 (x0 : nat) := fun y0 : nat => Peano.le x0 (Nat.add x0 y0).
Definition term164 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat -> Prop) := ((x3 (Nat.sub x1 x2)) /\ (((x1 = (Nat.add x2 x0)) \/ ((Peano.lt x1 x2) /\ (x0 = (NUMERAL 0)))) /\ (~ (x3 x0)))) \/ ((~ (x3 (Nat.sub x1 x2))) /\ (forall y0 : nat, ((~ (x1 = (Nat.add x2 y0))) /\ ((~ (Peano.lt x1 x2)) \/ (~ (y0 = (NUMERAL 0))))) \/ (x3 y0))).
Definition term148 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := (exists y0 : nat, (x2 (Nat.sub x0 x1)) /\ (((x0 = (Nat.add x1 y0)) \/ ((Peano.lt x0 x1) /\ (y0 = (NUMERAL 0)))) /\ (~ (x2 y0)))) \/ ((~ (x2 (Nat.sub x0 x1))) /\ (forall y0 : nat, ((~ (x0 = (Nat.add x1 y0))) /\ ((~ (Peano.lt x0 x1)) \/ (~ (y0 = (NUMERAL 0))))) \/ (x2 y0))).
Definition term141 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := @eq Prop ((x2 (Nat.sub x0 x1)) /\ (exists y0 : nat, ((x0 = (Nat.add x1 y0)) \/ ((Peano.lt x0 x1) /\ (y0 = (NUMERAL 0)))) /\ (~ (x2 y0)))).
Definition term140 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := @eq Prop ((x2 (Nat.sub x0 x1)) /\ (exists y0 : nat, (fun y1 : nat => ((x0 = (Nat.add x1 y1)) \/ ((Peano.lt x0 x1) /\ (y1 = (NUMERAL 0)))) /\ (~ (x2 y1))) y0)).
Definition term360 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := (((Nat.sub x0 x1) = (NUMERAL 0)) /\ (x2 (Nat.sub x0 x1))) -> x2 (NUMERAL 0).
Definition term467 (x0 : nat) (x1 : nat -> Prop) := or (exists y0 : nat, (x1 x0) /\ ((x0 = y0) /\ (~ (x1 y0)))).
Definition term147 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := or (exists y0 : nat, (x2 (Nat.sub x0 x1)) /\ (((x0 = (Nat.add x1 y0)) \/ ((Peano.lt x0 x1) /\ (y0 = (NUMERAL 0)))) /\ (~ (x2 y0)))).
Definition term341 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (~ (x0 x1)) \/ (~ (x1 = x2)).
Definition term501 (x0 : nat) (x1 : nat) := fun y0 : nat => x0 = (Nat.add x1 y0).
Definition term297 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => ~ (x0 y0)) x1.
Definition term435 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (~ (x0 = x2)) \/ (x1 x2).
Definition term56 := (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> (forall y0 : nat, forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) = (Peano.le y0 y1)) -> ~ (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)).
Definition term468 (x0 : nat) (x1 : nat -> Prop) := (exists y0 : nat, (x1 x0) /\ ((x0 = y0) /\ (~ (x1 y0)))) \/ ((~ (x1 x0)) /\ (forall y0 : nat, (~ (x0 = y0)) \/ (x1 y0))).
Definition term383 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => forall y1 : nat, forall y2 : nat, (Peano.lt y2 y1) -> (~ ((y0 (Nat.sub y2 y1)) = (forall y3 : nat, ((y2 = (Nat.add y1 y3)) \/ ((Peano.lt y2 y1) /\ (y3 = (NUMERAL 0)))) -> y0 y3))) -> (forall y3 : nat, forall y4 : nat, Peano.le y3 (Nat.add y3 y4)) -> (forall y3 : nat, forall y4 : nat, (Peano.lt y3 y4) -> Peano.le y3 y4) -> (forall y3 : nat, forall y4 : nat, ((Nat.sub y3 y4) = (NUMERAL 0)) = (Peano.le y3 y4)) -> (forall y3 : nat, forall y4 : nat, (~ (Peano.lt y3 y4)) = (Peano.le y4 y3)) -> False) x0.
Definition term169 (x0 : nat) := fun y0 : nat => (~ (Peano.lt x0 y0)) \/ (Peano.le x0 y0).
Definition term370 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((x0 x3) \/ ((~ (Peano.lt x1 x2)) \/ (~ (x3 = (NUMERAL 0))))).
Definition term408 (x0 : nat) := False /\ (x0 = (NUMERAL 0)).
Definition term106 (x0 : nat) (x1 : nat) (x2 : nat) := or (~ ((x0 = (Nat.add x1 x2)) \/ ((Peano.lt x0 x1) /\ (x2 = (NUMERAL 0))))).
Definition term31 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term74 := fun y0 : nat -> Prop => forall y1 : nat, forall y2 : nat, (Peano.lt y2 y1) -> (~ ((y0 (Nat.sub y2 y1)) = (forall y3 : nat, ((y2 = (Nat.add y1 y3)) \/ ((Peano.lt y2 y1) /\ (y3 = (NUMERAL 0)))) -> y0 y3))) -> (forall y3 : nat, forall y4 : nat, Peano.le y3 (Nat.add y3 y4)) -> (forall y3 : nat, forall y4 : nat, (Peano.lt y3 y4) -> Peano.le y3 y4) -> (forall y3 : nat, forall y4 : nat, ((Nat.sub y3 y4) = (NUMERAL 0)) = (Peano.le y3 y4)) -> ~ (forall y3 : nat, forall y4 : nat, (~ (Peano.lt y3 y4)) = (Peano.le y4 y3)).
Definition term73 := fun y0 : nat -> Prop => forall y1 : nat, forall y2 : nat, (Peano.lt y2 y1) -> (~ ((y0 (Nat.sub y2 y1)) = (forall y3 : nat, ((y2 = (Nat.add y1 y3)) \/ ((Peano.lt y2 y1) /\ (y3 = (NUMERAL 0)))) -> y0 y3))) -> (forall y3 : nat, forall y4 : nat, Peano.le y3 (Nat.add y3 y4)) -> (forall y3 : nat, forall y4 : nat, (Peano.lt y3 y4) -> Peano.le y3 y4) -> (forall y3 : nat, forall y4 : nat, ((Nat.sub y3 y4) = (NUMERAL 0)) = (Peano.le y3 y4)) -> (forall y3 : nat, forall y4 : nat, (~ (Peano.lt y3 y4)) = (Peano.le y4 y3)) -> False.
Definition term491 (x0 : nat) := ~ (x0 = x0).
Definition term386 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (x1 (Nat.sub y0 x0)) = (forall y1 : nat, ((y0 = (Nat.add x0 y1)) \/ ((Peano.lt y0 x0) /\ (y1 = (NUMERAL 0)))) -> x1 y1).
Definition term132 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term39 (x0 : Prop) := (~ x0) -> False.
Definition term260 := (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 y2)) \/ (~ (Peano.le y2 y1))) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.lt y1 y2) \/ (Peano.le y2 y1)) y0).
Definition term239 (x0 : nat) := (forall y0 : nat, (fun y1 : nat => (~ (Peano.lt x0 y1)) \/ (~ (Peano.le y1 x0))) y0) /\ (forall y0 : nat, (fun y1 : nat => (Peano.lt x0 y1) \/ (Peano.le y1 x0)) y0).
Definition term208 := (forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Nat.sub y1 y2) = (NUMERAL 0)) \/ (~ (Peano.le y1 y2))) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ ((Nat.sub y1 y2) = (NUMERAL 0))) \/ (Peano.le y1 y2)) y0).
Definition term183 (x0 : nat) := (forall y0 : nat, (fun y1 : nat => ((Nat.sub x0 y1) = (NUMERAL 0)) \/ (~ (Peano.le x0 y1))) y0) /\ (forall y0 : nat, (fun y1 : nat => (~ ((Nat.sub x0 y1) = (NUMERAL 0))) \/ (Peano.le x0 y1)) y0).
Definition term104 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat) := ((x0 = (Nat.add x1 x3)) \/ ((Peano.lt x0 x1) /\ (x3 = (NUMERAL 0)))) /\ (~ (x2 x3)).
Definition term277 := (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0)).
Definition term226 := (forall y0 : nat, forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) \/ (~ (Peano.le y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (~ ((Nat.sub y0 y1) = (NUMERAL 0))) \/ (Peano.le y0 y1)).
Definition term235 (x0 : nat) := forall y0 : nat, ((~ (Peano.lt x0 y0)) \/ (~ (Peano.le y0 x0))) /\ ((Peano.lt x0 y0) \/ (Peano.le y0 x0)).
Definition term175 (x0 : nat) := forall y0 : nat, (((Nat.sub x0 y0) = (NUMERAL 0)) \/ (~ (Peano.le x0 y0))) /\ ((~ ((Nat.sub x0 y0) = (NUMERAL 0))) \/ (Peano.le x0 y0)).
Definition term149 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) \/ x1.
Definition term103 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat) := ~ (((x0 = (Nat.add x1 x3)) \/ ((Peano.lt x0 x1) /\ (x3 = (NUMERAL 0)))) -> x2 x3).
Definition term318 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (x2 = x0) -> (x1 x0) \/ (~ (x1 x2)).
Definition term288 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat) := (~ (Peano.lt x0 x1)) \/ ((~ (x3 = (NUMERAL 0))) \/ (x2 x3)).
Definition term499 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => forall y1 : nat, (~ ((y0 y1) = (forall y2 : nat, (y1 = y2) -> y0 y2))) -> False) x0.
Definition term303 (x0 : nat) (x1 : nat) := ~ (Peano.lt (Nat.add x1 x0) x1).
Definition term313 (x0 : nat) (x1 : nat) := ((Peano.lt (Nat.add x0 x1) x0) /\ (Peano.le x0 (Nat.add x0 x1))) -> False.
Definition term233 (x0 : nat) (x1 : nat) := ((~ (Peano.lt x1 x0)) \/ (~ (Peano.le x0 x1))) /\ ((Peano.lt x1 x0) \/ (Peano.le x0 x1)).
Definition term82 (x0 : nat) := forall y0 : nat, ((Nat.sub x0 y0) = (NUMERAL 0)) = (Peano.le x0 y0).
Definition term12 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Nat.add x0 x1) = (Nat.add x0 y0)) = (x1 = y0).
Definition term161 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat) := or ((fun y0 : nat => (x2 (Nat.sub x0 x1)) /\ (((x0 = (Nat.add x1 y0)) \/ ((Peano.lt x0 x1) /\ (y0 = (NUMERAL 0)))) /\ (~ (x2 y0)))) x3).
Definition term387 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (fun y0 : nat => (x1 (Nat.sub y0 x0)) = (forall y1 : nat, ((y0 = (Nat.add x0 y1)) \/ ((Peano.lt y0 x0) /\ (y1 = (NUMERAL 0)))) -> x1 y1)) x2.
Definition term255 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (Peano.lt x0 y1) \/ (Peano.le y1 x0)) y0.
Definition term250 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (~ (Peano.lt x0 y1)) \/ (~ (Peano.le y1 x0))) y0.
Definition term202 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (~ ((Nat.sub x0 y1) = (NUMERAL 0))) \/ (Peano.le x0 y1)) y0.
Definition term197 (x0 : nat) := forall y0 : nat, (fun y1 : nat => ((Nat.sub x0 y1) = (NUMERAL 0)) \/ (~ (Peano.le x0 y1))) y0.
Definition term457 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (fun y0 : nat => (x0 = y0) /\ (~ (x1 y0))) x2.
Definition term37 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 y0) \/ (Peano.le y0 x0)) x1.
Definition term25 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1)).
Definition term325 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term180 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (x0 y0) /\ (x1 y0).
Definition term495 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (~ (~ (x0 = x2))) -> x1 x2.
Definition term153 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := (exists y0 : nat, (fun y1 : nat => (x2 (Nat.sub x0 x1)) /\ (((x0 = (Nat.add x1 y1)) \/ ((Peano.lt x0 x1) /\ (y1 = (NUMERAL 0)))) /\ (~ (x2 y1)))) y0) \/ ((~ (x2 (Nat.sub x0 x1))) /\ (forall y0 : nat, ((~ (x0 = (Nat.add x1 y0))) /\ ((~ (Peano.lt x0 x1)) \/ (~ (y0 = (NUMERAL 0))))) \/ (x2 y0))).
Definition term353 (x0 : nat) (x1 : nat) := and (x0 = x1).
Definition term367 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat) := (~ (Peano.lt x0 x1)) \/ ((x2 x3) \/ (~ (x3 = (NUMERAL 0)))).
Definition term465 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (x1 x0) /\ ((x0 = y0) /\ (~ (x1 y0))).
Definition term108 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat) := (~ ((x0 = (Nat.add x1 x3)) \/ ((Peano.lt x0 x1) /\ (x3 = (NUMERAL 0))))) \/ (x2 x3).
Definition term436 (x0 : nat) (x1 : nat -> Prop) := ~ (forall y0 : nat, (x0 = y0) -> x1 y0).
Definition term112 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := ~ (forall y0 : nat, ((x0 = (Nat.add x1 y0)) \/ ((Peano.lt x0 x1) /\ (y0 = (NUMERAL 0)))) -> x2 y0).
Definition term257 := fun y0 : nat => (forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0))) /\ (forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0)).
Definition term205 := fun y0 : nat => (forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) \/ (~ (Peano.le y0 y1))) /\ (forall y1 : nat, (~ ((Nat.sub y0 y1) = (NUMERAL 0))) \/ (Peano.le y0 y1)).
Definition term162 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat) := or ((x2 (Nat.sub x0 x1)) /\ (((x0 = (Nat.add x1 x3)) \/ ((Peano.lt x0 x1) /\ (x3 = (NUMERAL 0)))) /\ (~ (x2 x3)))).
Definition term362 (x0 : nat -> Prop) := (~ (x0 (NUMERAL 0))) -> x0 (NUMERAL 0).
Definition term76 := forall y0 : nat -> Prop, forall y1 : nat, forall y2 : nat, (Peano.lt y2 y1) -> (~ ((y0 (Nat.sub y2 y1)) = (forall y3 : nat, ((y2 = (Nat.add y1 y3)) \/ ((Peano.lt y2 y1) /\ (y3 = (NUMERAL 0)))) -> y0 y3))) -> (forall y3 : nat, forall y4 : nat, Peano.le y3 (Nat.add y3 y4)) -> (forall y3 : nat, forall y4 : nat, (Peano.lt y3 y4) -> Peano.le y3 y4) -> (forall y3 : nat, forall y4 : nat, ((Nat.sub y3 y4) = (NUMERAL 0)) = (Peano.le y3 y4)) -> ~ (forall y3 : nat, forall y4 : nat, (~ (Peano.lt y3 y4)) = (Peano.le y4 y3)).
Definition term75 := forall y0 : nat -> Prop, forall y1 : nat, forall y2 : nat, (Peano.lt y2 y1) -> (~ ((y0 (Nat.sub y2 y1)) = (forall y3 : nat, ((y2 = (Nat.add y1 y3)) \/ ((Peano.lt y2 y1) /\ (y3 = (NUMERAL 0)))) -> y0 y3))) -> (forall y3 : nat, forall y4 : nat, Peano.le y3 (Nat.add y3 y4)) -> (forall y3 : nat, forall y4 : nat, (Peano.lt y3 y4) -> Peano.le y3 y4) -> (forall y3 : nat, forall y4 : nat, ((Nat.sub y3 y4) = (NUMERAL 0)) = (Peano.le y3 y4)) -> (forall y3 : nat, forall y4 : nat, (~ (Peano.lt y3 y4)) = (Peano.le y4 y3)) -> False.
Definition term49 := ~ (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)).
Definition term151 (x0 : nat -> Prop) (x1 : Prop) := (exists y0 : nat, x0 y0) \/ x1.
Definition term131 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term452 (x0 : nat) (x1 : nat -> Prop) := or ((x1 x0) /\ (exists y0 : nat, (x0 = y0) /\ (~ (x1 y0)))).
Definition term449 (x0 : nat) (x1 : nat -> Prop) := (x1 x0) /\ (~ (forall y0 : nat, (x0 = y0) -> x1 y0)).
Definition term377 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ ((~ (Peano.lt x0 x1)) \/ (~ (x2 = (NUMERAL 0))))).
Definition term333 (x0 : nat) (x1 : nat) := imp (Peano.le x0 x1).
Definition term307 (x0 : Prop) (x1 : Prop) := (~ x0) \/ (~ x1).
Definition term144 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := fun y0 : nat => (x2 (Nat.sub x0 x1)) /\ ((fun y1 : nat => ((x0 = (Nat.add x1 y1)) \/ ((Peano.lt x0 x1) /\ (y1 = (NUMERAL 0)))) /\ (~ (x2 y1))) y0).
Definition term304 (x0 : Prop) := (~ x0) -> x0.
Definition term102 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt x0 x1) /\ (x2 = (NUMERAL 0)).
Definition term130 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := ((x2 (Nat.sub x0 x1)) /\ (exists y0 : nat, ((x0 = (Nat.add x1 y0)) \/ ((Peano.lt x0 x1) /\ (y0 = (NUMERAL 0)))) /\ (~ (x2 y0)))) \/ ((~ (x2 (Nat.sub x0 x1))) /\ (forall y0 : nat, ((~ (x0 = (Nat.add x1 y0))) /\ ((~ (Peano.lt x0 x1)) \/ (~ (y0 = (NUMERAL 0))))) \/ (x2 y0))).
Definition term324 (x0 : nat) (x1 : nat) := @eq Prop ((Peano.le x0 x1) \/ (~ (Peano.lt x0 x1))).
Definition term483 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, ((x1 x0) /\ ((x0 = y0) /\ (~ (x1 y0)))) \/ ((~ (x1 x0)) /\ (forall y1 : nat, (~ (x0 = y1)) \/ (x1 y1))).
Definition term167 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := exists y0 : nat, ((x2 (Nat.sub x0 x1)) /\ (((x0 = (Nat.add x1 y0)) \/ ((Peano.lt x0 x1) /\ (y0 = (NUMERAL 0)))) /\ (~ (x2 y0)))) \/ ((~ (x2 (Nat.sub x0 x1))) /\ (forall y1 : nat, ((~ (x0 = (Nat.add x1 y1))) /\ ((~ (Peano.lt x0 x1)) \/ (~ (y1 = (NUMERAL 0))))) \/ (x2 y1))).
Definition term59 := (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> (forall y0 : nat, forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) = (Peano.le y0 y1)) -> ~ (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)).
Definition term363 (x0 : nat -> Prop) := (x0 (NUMERAL 0)) -> False.
Definition term348 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term15 (x0 : nat) := forall y0 : nat, Peano.le x0 (Nat.add x0 y0).
Definition term490 (x0 : nat) := (~ (x0 = x0)) -> x0 = x0.
Definition term500 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => (~ ((x0 y0) = (forall y1 : nat, (y0 = y1) -> x0 y1))) -> False) x1.
Definition term20 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.sub (Nat.add y0 y1) y0) = y1) x0.
Definition term329 (x0 : nat) (x1 : nat) := (~ (Peano.le x0 x1)) -> Peano.le x0 x1.
Definition term240 (x0 : nat) := fun y0 : nat => (~ (Peano.lt x0 y0)) \/ (~ (Peano.le y0 x0)).
Definition term234 (x0 : nat) := fun y0 : nat => ((~ (Peano.lt x0 y0)) \/ (~ (Peano.le y0 x0))) /\ ((Peano.lt x0 y0) \/ (Peano.le y0 x0)).
Definition term55 := (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> (forall y0 : nat, forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) = (Peano.le y0 y1)) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> False.
Definition term308 (x0 : Prop) (x1 : Prop) := ~ (x0 /\ x1).
Definition term268 := @eq Prop (forall y0 : nat, (forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0))) /\ (forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0))).
Definition term267 := @eq Prop (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 y2)) \/ (~ (Peano.le y2 y1))) y0) /\ ((fun y1 : nat => forall y2 : nat, (Peano.lt y1 y2) \/ (Peano.le y2 y1)) y0)).
Definition term248 (x0 : nat) := @eq Prop (forall y0 : nat, ((~ (Peano.lt x0 y0)) \/ (~ (Peano.le y0 x0))) /\ ((Peano.lt x0 y0) \/ (Peano.le y0 x0))).
Definition term247 (x0 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => (~ (Peano.lt x0 y1)) \/ (~ (Peano.le y1 x0))) y0) /\ ((fun y1 : nat => (Peano.lt x0 y1) \/ (Peano.le y1 x0)) y0)).
Definition term217 := @eq Prop (forall y0 : nat, (forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) \/ (~ (Peano.le y0 y1))) /\ (forall y1 : nat, (~ ((Nat.sub y0 y1) = (NUMERAL 0))) \/ (Peano.le y0 y1))).
Definition term216 := @eq Prop (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.sub y1 y2) = (NUMERAL 0)) \/ (~ (Peano.le y1 y2))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ ((Nat.sub y1 y2) = (NUMERAL 0))) \/ (Peano.le y1 y2)) y0)).
Definition term195 (x0 : nat) := @eq Prop (forall y0 : nat, (((Nat.sub x0 y0) = (NUMERAL 0)) \/ (~ (Peano.le x0 y0))) /\ ((~ ((Nat.sub x0 y0) = (NUMERAL 0))) \/ (Peano.le x0 y0))).
Definition term194 (x0 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => ((Nat.sub x0 y1) = (NUMERAL 0)) \/ (~ (Peano.le x0 y1))) y0) /\ ((fun y1 : nat => (~ ((Nat.sub x0 y1) = (NUMERAL 0))) \/ (Peano.le x0 y1)) y0)).
Definition term137 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat) := (fun y0 : nat => ((x0 = (Nat.add x1 y0)) \/ ((Peano.lt x0 x1) /\ (y0 = (NUMERAL 0)))) /\ (~ (x2 y0))) x3.
Definition term118 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := exists y0 : nat, ((x0 = (Nat.add x1 y0)) \/ ((Peano.lt x0 x1) /\ (y0 = (NUMERAL 0)))) /\ (~ (x2 y0)).
Definition term179 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term283 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.lt x0 y0)) \/ (Peano.le x0 y0)) x1.
Definition term190 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ ((Nat.sub x0 y0) = (NUMERAL 0))) \/ (Peano.le x0 y0)) x1.
Definition term186 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.sub x0 y0) = (NUMERAL 0)) \/ (~ (Peano.le x0 y0))) x1.
Definition term52 := (forall y0 : nat, forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) = (Peano.le y0 y1)) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> False.
Definition term86 (x0 : nat) := fun y0 : nat => (Peano.lt x0 y0) -> Peano.le x0 y0.
Definition term62 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := (~ ((x2 (Nat.sub x0 x1)) = (forall y0 : nat, ((x0 = (Nat.add x1 y0)) \/ ((Peano.lt x0 x1) /\ (y0 = (NUMERAL 0)))) -> x2 y0))) -> (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> (forall y0 : nat, forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) = (Peano.le y0 y1)) -> ~ (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)).
Definition term489 (x0 : nat -> Prop) (x1 : nat) := (x0 x1) -> False.
Definition term342 (x0 : nat -> Prop) (x1 : nat) := or (x0 x1).
Definition term33 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term384 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y1 y0) -> (~ ((x0 (Nat.sub y1 y0)) = (forall y2 : nat, ((y1 = (Nat.add y0 y2)) \/ ((Peano.lt y1 y0) /\ (y2 = (NUMERAL 0)))) -> x0 y2))) -> (forall y2 : nat, forall y3 : nat, Peano.le y2 (Nat.add y2 y3)) -> (forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> Peano.le y2 y3) -> (forall y2 : nat, forall y3 : nat, ((Nat.sub y2 y3) = (NUMERAL 0)) = (Peano.le y2 y3)) -> (forall y2 : nat, forall y3 : nat, (~ (Peano.lt y2 y3)) = (Peano.le y3 y2)) -> False) x1.
Definition term11 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.add x0 y0) = (Nat.add x0 y1)) = (y0 = y1)) x1.
Definition term142 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat) := (x2 (Nat.sub x0 x1)) /\ ((fun y0 : nat => ((x0 = (Nat.add x1 y0)) \/ ((Peano.lt x0 x1) /\ (y0 = (NUMERAL 0)))) /\ (~ (x2 y0))) x3).
Definition term450 (x0 : nat) (x1 : nat -> Prop) := (x1 x0) /\ (exists y0 : nat, (x0 = y0) /\ (~ (x1 y0))).
Definition term368 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 x3) \/ ((~ (Peano.lt x1 x2)) \/ (~ (x3 = (NUMERAL 0)))).
Definition term289 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term262 := fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0).
Definition term210 := fun y0 : nat => forall y1 : nat, (~ ((Nat.sub y0 y1) = (NUMERAL 0))) \/ (Peano.le y0 y1).
Definition term171 := fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (Peano.le y0 y1).
Definition term88 := fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1.
Definition term83 := fun y0 : nat => forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) = (Peano.le y0 y1).
Definition term80 := fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0).
Definition term5 := fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0).
Definition term43 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := ~ ((x2 (Nat.sub x0 x1)) = (forall y0 : nat, ((x0 = (Nat.add x1 y0)) \/ ((Peano.lt x0 x1) /\ (y0 = (NUMERAL 0)))) -> x2 y0)).
Definition term227 (x0 : nat) (x1 : nat) := ~ (~ (Peano.lt x0 x1)).
Definition term322 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) \/ (~ (Peano.lt x0 x1)).
Definition term36 (x0 : nat) := forall y0 : nat, (Peano.lt x0 y0) \/ (Peano.le y0 x0).
Definition term16 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le x0 (Nat.add x0 y0)) x1.
Definition term471 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (fun y0 : nat => (x1 x0) /\ ((x0 = y0) /\ (~ (x1 y0)))) x2.
Definition term481 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => ((fun y1 : nat => (x1 x0) /\ ((x0 = y1) /\ (~ (x1 y1)))) y0) \/ ((~ (x1 x0)) /\ (forall y1 : nat, (~ (x0 = y1)) \/ (x1 y1))).
Definition term165 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := fun y0 : nat => ((fun y1 : nat => (x2 (Nat.sub x0 x1)) /\ (((x0 = (Nat.add x1 y1)) \/ ((Peano.lt x0 x1) /\ (y1 = (NUMERAL 0)))) /\ (~ (x2 y1)))) y0) \/ ((~ (x2 (Nat.sub x0 x1))) /\ (forall y1 : nat, ((~ (x0 = (Nat.add x1 y1))) /\ ((~ (Peano.lt x0 x1)) \/ (~ (y1 = (NUMERAL 0))))) \/ (x2 y1))).
Definition term243 (x0 : nat) (x1 : nat) := (~ (Peano.lt x1 x0)) \/ (~ (Peano.le x0 x1)).
Definition term123 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := (~ (x2 (Nat.sub x0 x1))) /\ (forall y0 : nat, ((~ (x0 = (Nat.add x1 y0))) /\ ((~ (Peano.lt x0 x1)) \/ (~ (y0 = (NUMERAL 0))))) \/ (x2 y0)).
Definition term122 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := (~ (x2 (Nat.sub x0 x1))) /\ (forall y0 : nat, ((x0 = (Nat.add x1 y0)) \/ ((Peano.lt x0 x1) /\ (y0 = (NUMERAL 0)))) -> x2 y0).
Definition term305 (x0 : nat) (x1 : nat) := (~ (Peano.le x0 (Nat.add x0 x1))) -> Peano.le x0 (Nat.add x0 x1).
Definition term326 (x0 : nat) (x1 : nat) := (~ (~ (Peano.lt x0 x1))) -> Peano.le x0 x1.
Definition term378 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((Peano.lt x0 x1) /\ (x2 = (NUMERAL 0))).
Definition term134 (x0 : Prop) (x1 : nat -> Prop) := exists y0 : nat, x0 /\ (x1 y0).
Definition term356 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := imp (~ ((~ (x2 = x0)) \/ (~ (x1 x2)))).
Definition term395 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term278 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat) := ((~ (x0 = (Nat.add x1 x3))) \/ (x2 x3)) /\ (((~ (Peano.lt x0 x1)) \/ (~ (x3 = (NUMERAL 0)))) \/ (x2 x3)).
Definition term488 (x0 : nat -> Prop) (x1 : nat) := (~ (x0 x1)) -> x0 x1.
Definition term358 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ((x0 = x2) /\ (x1 x0)) -> x1 x2.
Definition term0 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term249 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (~ (Peano.lt x0 y1)) \/ (~ (Peano.le y1 x0))) y0.
Definition term196 (x0 : nat) := fun y0 : nat => (fun y1 : nat => ((Nat.sub x0 y1) = (NUMERAL 0)) \/ (~ (Peano.le x0 y1))) y0.
Definition term229 (x0 : nat) (x1 : nat) := or (Peano.lt x0 x1).
Definition term133 (x0 : Prop) (x1 : nat -> Prop) := x0 /\ (exists y0 : nat, x1 y0).
Definition term470 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, ((fun y1 : nat => (x1 x0) /\ ((x0 = y1) /\ (~ (x1 y1)))) y0) \/ ((~ (x1 x0)) /\ (forall y1 : nat, (~ (x0 = y1)) \/ (x1 y1))).
Definition term154 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := exists y0 : nat, ((fun y1 : nat => (x2 (Nat.sub x0 x1)) /\ (((x0 = (Nat.add x1 y1)) \/ ((Peano.lt x0 x1) /\ (y1 = (NUMERAL 0)))) /\ (~ (x2 y1)))) y0) \/ ((~ (x2 (Nat.sub x0 x1))) /\ (forall y1 : nat, ((~ (x0 = (Nat.add x1 y1))) /\ ((~ (Peano.lt x0 x1)) \/ (~ (y1 = (NUMERAL 0))))) \/ (x2 y1))).
Definition term445 (x0 : nat -> Prop) (x1 : nat) := and (~ (x0 x1)).
Definition term185 (x0 : nat) := fun y0 : nat => (~ ((Nat.sub x0 y0) = (NUMERAL 0))) \/ (Peano.le x0 y0).
Definition term48 := (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> False.
Definition term285 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat) := ((~ (Peano.lt x0 x1)) \/ (~ (x3 = (NUMERAL 0)))) \/ (x2 x3).
Definition term458 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => (x0 = y1) /\ (~ (x1 y1))) y0.
Definition term138 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => ((x0 = (Nat.add x1 y1)) \/ ((Peano.lt x0 x1) /\ (y1 = (NUMERAL 0)))) /\ (~ (x2 y1))) y0.
Definition term125 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := (x2 (Nat.sub x0 x1)) /\ (~ (forall y0 : nat, ((x0 = (Nat.add x1 y0)) \/ ((Peano.lt x0 x1) /\ (y0 = (NUMERAL 0)))) -> x2 y0)).
Definition term430 := fun y0 : nat -> Prop => forall y1 : nat, (y0 y1) = (forall y2 : nat, (y1 = y2) -> y0 y2).
Definition term78 (x0 : nat) := fun y0 : nat => (~ (Peano.lt x0 y0)) = (Peano.le y0 x0).
Definition term364 (x0 : nat -> Prop) (x1 : nat) := (~ (x1 = (NUMERAL 0))) \/ (x0 x1).
Definition term493 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := @eq Prop ((~ (x0 = x2)) \/ (x1 x2)).
Definition term253 (x0 : nat) := and (forall y0 : nat, (~ (Peano.lt x0 y0)) \/ (~ (Peano.le y0 x0))).
Definition term200 (x0 : nat) := and (forall y0 : nat, ((Nat.sub x0 y0) = (NUMERAL 0)) \/ (~ (Peano.le x0 y0))).
Definition term295 (x0 : nat) (x1 : nat) := @eq Prop (Peano.lt x0 x1).
Definition term189 (x0 : nat) (x1 : nat) := and (((Nat.sub x0 x1) = (NUMERAL 0)) \/ (~ (Peano.le x0 x1))).
Definition term290 (x0 : nat) := fun y0 : nat => Peano.lt y0 x0.
Definition term280 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := fun y0 : nat => ((~ (x0 = (Nat.add x1 y0))) \/ (x2 y0)) /\ (((~ (Peano.lt x0 x1)) \/ (~ (y0 = (NUMERAL 0)))) \/ (x2 y0)).
Definition term462 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (x1 x0) /\ ((fun y0 : nat => (x0 = y0) /\ (~ (x1 y0))) x2).
Definition term469 (x0 : nat) (x1 : nat -> Prop) := (exists y0 : nat, (fun y1 : nat => (x1 x0) /\ ((x0 = y1) /\ (~ (x1 y1)))) y0) \/ ((~ (x1 x0)) /\ (forall y0 : nat, (~ (x0 = y0)) \/ (x1 y0))).
Definition term497 (x0 : nat) (x1 : nat) := imp (x0 = x1).
Definition term335 (x0 : nat) (x1 : nat) := (~ ((Nat.sub x0 x1) = (NUMERAL 0))) -> (Nat.sub x0 x1) = (NUMERAL 0).
Definition term28 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term27 (x0 : nat) (x1 : nat) := exists y0 : nat, x0 = (Nat.add x1 y0).
Definition term421 (x0 : nat) (x1 : nat -> Prop) := ((~ ((x1 x0) = (forall y0 : nat, (x0 = y0) -> x1 y0))) -> False) -> (~ ((x1 x0) = (forall y0 : nat, (x0 = y0) -> x1 y0))) -> False.
Definition term99 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = (Nat.add x1 x2))) /\ (~ ((Peano.lt x0 x1) /\ (x2 = (NUMERAL 0)))).
Definition term407 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt (Nat.add x1 x0) x1) /\ (x2 = (NUMERAL 0)).
Definition term394 (x0 : nat -> Prop) (x1 : nat) := @eq Prop (x0 x1).
Definition term23 (x0 : nat) (x1 : nat) := Nat.sub (Nat.add x1 x0) x1.
Definition term155 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat) := (fun y0 : nat => (x2 (Nat.sub x0 x1)) /\ (((x0 = (Nat.add x1 y0)) \/ ((Peano.lt x0 x1) /\ (y0 = (NUMERAL 0)))) /\ (~ (x2 y0)))) x3.
Definition term310 (x0 : nat) (x1 : nat) := ((Peano.lt x1 x0) /\ (Peano.le x0 x1)) -> False.
Definition term347 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term184 (x0 : nat) := fun y0 : nat => ((Nat.sub x0 y0) = (NUMERAL 0)) \/ (~ (Peano.le x0 y0)).
Definition term143 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat) := (x2 (Nat.sub x0 x1)) /\ (((x0 = (Nat.add x1 x3)) \/ ((Peano.lt x0 x1) /\ (x3 = (NUMERAL 0)))) /\ (~ (x2 x3))).
Definition term276 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0).
Definition term271 := forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0)).
Definition term237 := forall y0 : nat, forall y1 : nat, ((~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0))) /\ ((Peano.lt y0 y1) \/ (Peano.le y1 y0)).
Definition term225 := forall y0 : nat, forall y1 : nat, (~ ((Nat.sub y0 y1) = (NUMERAL 0))) \/ (Peano.le y0 y1).
Definition term220 := forall y0 : nat, forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) \/ (~ (Peano.le y0 y1)).
Definition term177 := forall y0 : nat, forall y1 : nat, (((Nat.sub y0 y1) = (NUMERAL 0)) \/ (~ (Peano.le y0 y1))) /\ ((~ ((Nat.sub y0 y1) = (NUMERAL 0))) \/ (Peano.le y0 y1)).
Definition term172 := forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (Peano.le y0 y1).
Definition term92 := forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1).
Definition term89 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1.
Definition term84 := forall y0 : nat, forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) = (Peano.le y0 y1).
Definition term72 (x0 : nat -> Prop) := forall y0 : nat, forall y1 : nat, (Peano.lt y1 y0) -> (~ ((x0 (Nat.sub y1 y0)) = (forall y2 : nat, ((y1 = (Nat.add y0 y2)) \/ ((Peano.lt y1 y0) /\ (y2 = (NUMERAL 0)))) -> x0 y2))) -> (forall y2 : nat, forall y3 : nat, Peano.le y2 (Nat.add y2 y3)) -> (forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> Peano.le y2 y3) -> (forall y2 : nat, forall y3 : nat, ((Nat.sub y2 y3) = (NUMERAL 0)) = (Peano.le y2 y3)) -> ~ (forall y2 : nat, forall y3 : nat, (~ (Peano.lt y2 y3)) = (Peano.le y3 y2)).
Definition term71 (x0 : nat -> Prop) := forall y0 : nat, forall y1 : nat, (Peano.lt y1 y0) -> (~ ((x0 (Nat.sub y1 y0)) = (forall y2 : nat, ((y1 = (Nat.add y0 y2)) \/ ((Peano.lt y1 y0) /\ (y2 = (NUMERAL 0)))) -> x0 y2))) -> (forall y2 : nat, forall y3 : nat, Peano.le y2 (Nat.add y2 y3)) -> (forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> Peano.le y2 y3) -> (forall y2 : nat, forall y3 : nat, ((Nat.sub y2 y3) = (NUMERAL 0)) = (Peano.le y2 y3)) -> (forall y2 : nat, forall y3 : nat, (~ (Peano.lt y2 y3)) = (Peano.le y3 y2)) -> False.
Definition term50 := forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0).
Definition term10 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Nat.add x0 y0) = (Nat.add x0 y1)) = (y0 = y1).
Definition term8 := forall y0 : nat, forall y1 : nat, (Peano.lt y1 y0) = (~ (Peano.le y0 y1)).
Definition term7 := forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0).
Definition term128 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := or ((x2 (Nat.sub x0 x1)) /\ (exists y0 : nat, ((x0 = (Nat.add x1 y0)) \/ ((Peano.lt x0 x1) /\ (y0 = (NUMERAL 0)))) /\ (~ (x2 y0)))).
Definition term337 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (~ (x0 (Nat.sub x1 x2))) -> x0 (Nat.sub x1 x2).
Definition term439 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ~ ((fun y0 : nat => (x0 = y0) -> x1 y0) x2).
Definition term406 (x0 : nat) (x1 : nat) := and (Peano.lt (Nat.add x1 x0) x1).
Definition term265 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0))) x0) /\ ((fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0)) x0).
Definition term214 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) \/ (~ (Peano.le y0 y1))) x0) /\ ((fun y0 : nat => forall y1 : nat, (~ ((Nat.sub y0 y1) = (NUMERAL 0))) \/ (Peano.le y0 y1)) x0).
Definition term390 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := forall y0 : nat, (((Nat.add x1 x0) = (Nat.add x1 y0)) \/ ((Peano.lt (Nat.add x1 x0) x1) /\ (y0 = (NUMERAL 0)))) -> x2 y0.
Definition term41 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := forall y0 : nat, ((x0 = (Nat.add x1 y0)) \/ ((Peano.lt x0 x1) /\ (y0 = (NUMERAL 0)))) -> x2 y0.
Definition term478 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := or ((x1 x0) /\ ((x0 = x2) /\ (~ (x1 x2)))).
Definition term79 (x0 : nat) := forall y0 : nat, (~ (Peano.lt x0 y0)) = (Peano.le y0 x0).
Definition term3 (x0 : nat) := forall y0 : nat, (~ (Peano.le x0 y0)) = (Peano.lt y0 x0).
Definition term230 (x0 : nat) (x1 : nat) := (~ (~ (Peano.lt x1 x0))) \/ (Peano.le x0 x1).
Definition term486 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => x0 y0) x1.
Definition term231 (x0 : nat) (x1 : nat) := and ((~ (Peano.lt x1 x0)) \/ (~ (Peano.le x0 x1))).
Definition term413 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat) := ((x1 = x3) -> (x2 x3) = (x2 x3)) -> ((((Nat.add x0 x1) = (Nat.add x0 x3)) \/ ((Peano.lt (Nat.add x0 x1) x0) /\ (x3 = (NUMERAL 0)))) -> x2 x3) = ((x1 = x3) -> x2 x3).
Definition term294 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : nat => Peano.lt y0 x0) x1).
Definition term426 (x0 : nat -> Prop) := fun y0 : nat => (x0 y0) = (forall y1 : nat, (y0 = y1) -> x0 y1).
Definition term482 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => ((x1 x0) /\ ((x0 = y0) /\ (~ (x1 y0)))) \/ ((~ (x1 x0)) /\ (forall y1 : nat, (~ (x0 = y1)) \/ (x1 y1))).
Definition term317 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (x1 x0) \/ (~ (x1 x2)).
Definition term291 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.lt y0 x0) x1.
Definition term198 (x0 : nat) := forall y0 : nat, ((Nat.sub x0 y0) = (NUMERAL 0)) \/ (~ (Peano.le x0 y0)).
Definition term359 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := ((Nat.sub x1 x2) = (NUMERAL 0)) /\ (x0 (Nat.sub x1 x2)).
Definition term344 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := @eq Prop ((~ (x2 = x0)) \/ ((x1 x0) \/ (~ (x1 x2)))).
Definition term343 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (x0 x2) \/ ((~ (x0 x1)) \/ (~ (x1 = x2))).
Definition term494 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := @eq Prop ((x0 x2) \/ (~ (x1 = x2))).
Definition term34 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term21 (x0 : nat) := forall y0 : nat, (Nat.sub (Nat.add x0 y0) x0) = y0.
Definition term309 (x0 : nat) (x1 : nat) := ~ ((Peano.lt x1 x0) /\ (Peano.le x0 x1)).
Definition term105 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (Nat.add x1 x2)) \/ ((Peano.lt x0 x1) /\ (x2 = (NUMERAL 0))).
Definition term150 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) \/ x1.
Definition term381 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := ((Peano.lt x1 x2) /\ ((Nat.sub x1 x2) = (NUMERAL 0))) -> x0 (Nat.sub x1 x2).
Definition term136 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := exists y0 : nat, (x2 (Nat.sub x0 x1)) /\ ((fun y1 : nat => ((x0 = (Nat.add x1 y1)) \/ ((Peano.lt x0 x1) /\ (y1 = (NUMERAL 0)))) /\ (~ (x2 y1))) y0).
Definition term281 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := forall y0 : nat, ((~ (x0 = (Nat.add x1 y0))) \/ (x2 y0)) /\ (((~ (Peano.lt x0 x1)) \/ (~ (y0 = (NUMERAL 0)))) \/ (x2 y0)).
Definition term330 (x0 : nat) (x1 : nat) := (~ (~ (Peano.le x0 x1))) -> (Nat.sub x0 x1) = (NUMERAL 0).
Definition term320 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (~ (x2 = x0)) \/ ((x1 x0) \/ (~ (x1 x2))).
Definition term58 := (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> (forall y0 : nat, forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) = (Peano.le y0 y1)) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> False.
Definition term115 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat) := ~ ((fun y0 : nat => ((x0 = (Nat.add x1 y0)) \/ ((Peano.lt x0 x1) /\ (y0 = (NUMERAL 0)))) -> x2 y0) x3).
Definition term298 (x0 : nat -> Prop) := (fun y0 : nat => ~ (x0 y0)) (NUMERAL 0).
Definition term47 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := (((Peano.lt x0 x1) -> (~ ((x2 (Nat.sub x0 x1)) = (forall y0 : nat, ((x0 = (Nat.add x1 y0)) \/ ((Peano.lt x0 x1) /\ (y0 = (NUMERAL 0)))) -> x2 y0))) -> (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> (forall y0 : nat, forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) = (Peano.le y0 y1)) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> False) -> (Peano.lt x0 x1) -> (~ ((x2 (Nat.sub x0 x1)) = (forall y0 : nat, ((x0 = (Nat.add x1 y0)) \/ ((Peano.lt x0 x1) /\ (y0 = (NUMERAL 0)))) -> x2 y0))) -> (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> (forall y0 : nat, forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) = (Peano.le y0 y1)) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> False) -> ((Peano.lt x0 x1) -> (~ ((x2 (Nat.sub x0 x1)) = (forall y0 : nat, ((x0 = (Nat.add x1 y0)) \/ ((Peano.lt x0 x1) /\ (y0 = (NUMERAL 0)))) -> x2 y0))) -> (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> (forall y0 : nat, forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) = (Peano.le y0 y1)) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> False) -> (Peano.lt x0 x1) -> (~ ((x2 (Nat.sub x0 x1)) = (forall y0 : nat, ((x0 = (Nat.add x1 y0)) \/ ((Peano.lt x0 x1) /\ (y0 = (NUMERAL 0)))) -> x2 y0))) -> (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> (forall y0 : nat, forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) = (Peano.le y0 y1)) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> False.
Definition term425 (x0 : nat -> Prop) := fun y0 : nat => (~ ((x0 y0) = (forall y1 : nat, (y0 = y1) -> x0 y1))) -> False.
Definition term346 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (~ ((~ (x0 = x2)) \/ (~ (x1 x0)))) -> x1 x2.
Definition term401 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat) (x4 : Prop) := forall y0 : Prop, ((((Nat.add x1 x0) = (Nat.add x1 x3)) \/ ((Peano.lt (Nat.add x1 x0) x1) /\ (x3 = (NUMERAL 0)))) = x4) -> (x4 -> (x2 x3) = y0) -> ((((Nat.add x1 x0) = (Nat.add x1 x3)) \/ ((Peano.lt (Nat.add x1 x0) x1) /\ (x3 = (NUMERAL 0)))) -> x2 x3) = (x4 -> y0).
Definition term396 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term245 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (~ (Peano.lt x0 y0)) \/ (~ (Peano.le y0 x0))) x1) /\ ((fun y0 : nat => (Peano.lt x0 y0) \/ (Peano.le y0 x0)) x1).
Definition term192 (x0 : nat) (x1 : nat) := ((fun y0 : nat => ((Nat.sub x0 y0) = (NUMERAL 0)) \/ (~ (Peano.le x0 y0))) x1) /\ ((fun y0 : nat => (~ ((Nat.sub x0 y0) = (NUMERAL 0))) \/ (Peano.le x0 y0)) x1).
Definition term181 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (forall y0 : nat, x1 y0).
Definition term120 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := forall y0 : nat, ((~ (x0 = (Nat.add x1 y0))) /\ ((~ (Peano.lt x0 x1)) \/ (~ (y0 = (NUMERAL 0))))) \/ (x2 y0).
Definition term427 (x0 : nat -> Prop) := forall y0 : nat, (~ ((x0 y0) = (forall y1 : nat, (y0 = y1) -> x0 y1))) -> False.
Definition term126 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := (x2 (Nat.sub x0 x1)) /\ (exists y0 : nat, ((x0 = (Nat.add x1 y0)) \/ ((Peano.lt x0 x1) /\ (y0 = (NUMERAL 0)))) /\ (~ (x2 y0))).
Definition term354 (x0 : nat -> Prop) (x1 : nat) := ~ (~ (x0 x1)).
Definition term145 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := fun y0 : nat => (x2 (Nat.sub x0 x1)) /\ (((x0 = (Nat.add x1 y0)) \/ ((Peano.lt x0 x1) /\ (y0 = (NUMERAL 0)))) /\ (~ (x2 y0))).
Definition term338 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (x1 x0) \/ ((~ (x2 = x0)) \/ (~ (x1 x2))).
Definition term334 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) -> (Nat.sub x0 x1) = (NUMERAL 0).
Definition term292 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.lt y0 x0) (Nat.add x0 x1).
Definition term473 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, (fun y1 : nat => (x1 x0) /\ ((x0 = y1) /\ (~ (x1 y1)))) y0.
Definition term459 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, (fun y1 : nat => (x0 = y1) /\ (~ (x1 y1))) y0.
Definition term157 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := exists y0 : nat, (fun y1 : nat => (x2 (Nat.sub x0 x1)) /\ (((x0 = (Nat.add x1 y1)) \/ ((Peano.lt x0 x1) /\ (y1 = (NUMERAL 0)))) /\ (~ (x2 y1)))) y0.
Definition term139 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := exists y0 : nat, (fun y1 : nat => ((x0 = (Nat.add x1 y1)) \/ ((Peano.lt x0 x1) /\ (y1 = (NUMERAL 0)))) /\ (~ (x2 y1))) y0.
Definition term63 (x0 : nat) (x1 : nat) := imp (Peano.lt x0 x1).
Definition term422 (x0 : nat) (x1 : nat -> Prop) := (((~ ((x1 x0) = (forall y0 : nat, (x0 = y0) -> x1 y0))) -> False) -> (~ ((x1 x0) = (forall y0 : nat, (x0 = y0) -> x1 y0))) -> False) -> (~ ((x1 x0) = (forall y0 : nat, (x0 = y0) -> x1 y0))) -> False.
Definition term463 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (x1 x0) /\ ((x0 = x2) /\ (~ (x1 x2))).
Definition term415 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (x0 = x2) -> x1 x2.
Definition term466 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, (x1 x0) /\ ((x0 = y0) /\ (~ (x1 y0))).
Definition term398 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat) := forall y0 : Prop, forall y1 : Prop, ((((Nat.add x1 x0) = (Nat.add x1 x3)) \/ ((Peano.lt (Nat.add x1 x0) x1) /\ (x3 = (NUMERAL 0)))) = y0) -> (y0 -> (x2 x3) = y1) -> ((((Nat.add x1 x0) = (Nat.add x1 x3)) \/ ((Peano.lt (Nat.add x1 x0) x1) /\ (x3 = (NUMERAL 0)))) -> x2 x3) = (y0 -> y1).
Definition term397 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term29 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term424 (x0 : nat) (x1 : nat -> Prop) := ~ (~ ((x1 x0) = (forall y0 : nat, (x0 = y0) -> x1 y0))).
Definition term375 (x0 : nat) (x1 : nat) := and (Peano.lt x0 x1).
Definition term374 (x0 : nat) (x1 : nat) := and (~ (~ (Peano.lt x0 x1))).
Definition term352 (x0 : nat) (x1 : nat) := and (~ (~ (x0 = x1))).
Definition term442 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, (x0 = y0) /\ (~ (x1 y0)).
Definition term40 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := x0 (Nat.sub x1 x2).
Definition term315 (x0 : Prop) (x1 : Prop) := (x1 = x0) -> x0 \/ (~ x1).
Definition term256 (x0 : nat) := (forall y0 : nat, (~ (Peano.lt x0 y0)) \/ (~ (Peano.le y0 x0))) /\ (forall y0 : nat, (Peano.lt x0 y0) \/ (Peano.le y0 x0)).
Definition term204 (x0 : nat) := (forall y0 : nat, ((Nat.sub x0 y0) = (NUMERAL 0)) \/ (~ (Peano.le x0 y0))) /\ (forall y0 : nat, (~ ((Nat.sub x0 y0) = (NUMERAL 0))) \/ (Peano.le x0 y0)).
Definition term402 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat) (x4 : Prop) (x5 : Prop) := (fun y0 : Prop => ((((Nat.add x1 x0) = (Nat.add x1 x3)) \/ ((Peano.lt (Nat.add x1 x0) x1) /\ (x3 = (NUMERAL 0)))) = x4) -> (x4 -> (x2 x3) = y0) -> ((((Nat.add x1 x0) = (Nat.add x1 x3)) \/ ((Peano.lt (Nat.add x1 x0) x1) /\ (x3 = (NUMERAL 0)))) -> x2 x3) = (x4 -> y0)) x5.
Definition term300 (x0 : nat -> Prop) (x1 : nat) := @eq Prop ((fun y0 : nat => ~ (x0 y0)) x1).
Definition term273 := and (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0))).
Definition term222 := and (forall y0 : nat, forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) \/ (~ (Peano.le y0 y1))).
Definition term345 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := @eq Prop ((x0 x2) \/ ((~ (x0 x1)) \/ (~ (x1 = x2)))).
Definition term77 (x0 : nat) (x1 : nat) := ~ (Peano.lt x0 x1).
Definition term323 (x0 : nat) (x1 : nat) := @eq Prop ((~ (Peano.lt x0 x1)) \/ (Peano.le x0 x1)).
Definition term432 := forall y0 : nat -> Prop, forall y1 : nat, (y0 y1) = (forall y2 : nat, (y1 = y2) -> y0 y2).
Definition term418 (x0 : nat) (x1 : nat -> Prop) := forall y0 : nat, (x0 = y0) -> x1 y0.
Definition term420 (x0 : nat) (x1 : nat -> Prop) := ~ ((x1 x0) = (forall y0 : nat, (x0 = y0) -> x1 y0)).
Definition term361 (x0 : nat -> Prop) := x0 (NUMERAL 0).
Definition term64 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := (Peano.lt x0 x1) -> (~ ((x2 (Nat.sub x0 x1)) = (forall y0 : nat, ((x0 = (Nat.add x1 y0)) \/ ((Peano.lt x0 x1) /\ (y0 = (NUMERAL 0)))) -> x2 y0))) -> (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> (forall y0 : nat, forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) = (Peano.le y0 y1)) -> ~ (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)).
Definition term44 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := (Peano.lt x0 x1) -> (~ ((x2 (Nat.sub x0 x1)) = (forall y0 : nat, ((x0 = (Nat.add x1 y0)) \/ ((Peano.lt x0 x1) /\ (y0 = (NUMERAL 0)))) -> x2 y0))) -> (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> (forall y0 : nat, forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) = (Peano.le y0 y1)) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> False.
Definition term96 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((Peano.lt x0 x1) /\ (x2 = (NUMERAL 0))).
Definition term117 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := fun y0 : nat => ((x0 = (Nat.add x1 y0)) \/ ((Peano.lt x0 x1) /\ (y0 = (NUMERAL 0)))) /\ (~ (x2 y0)).
Definition term274 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (Peano.lt y1 y2) \/ (Peano.le y2 y1)) y0.
Definition term269 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 y2)) \/ (~ (Peano.le y2 y1))) y0.
Definition term223 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (~ ((Nat.sub y1 y2) = (NUMERAL 0))) \/ (Peano.le y1 y2)) y0.
Definition term218 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, ((Nat.sub y1 y2) = (NUMERAL 0)) \/ (~ (Peano.le y1 y2))) y0.
Definition term17 (x0 : nat) (x1 : nat) := Peano.le x0 (Nat.add x0 x1).
Definition term282 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (Peano.le y0 y1)) x0.
Definition term263 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0))) x0.
Definition term213 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ ((Nat.sub y0 y1) = (NUMERAL 0))) \/ (Peano.le y0 y1)) x0.
Definition term211 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) \/ (~ (Peano.le y0 y1))) x0.
Definition term35 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0)) x0.
Definition term24 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))) x0.
Definition term18 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y1 y0) = (~ (Peano.le y0 y1))) x0.
Definition term14 (x0 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) x0.
Definition term456 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, (x1 x0) /\ ((fun y1 : nat => (x0 = y1) /\ (~ (x1 y1))) y0).
Definition term299 (x0 : nat -> Prop) := ~ (x0 (NUMERAL 0)).
Definition term373 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (Peano.lt x0 x1))) /\ (~ (~ (x2 = (NUMERAL 0)))).
Definition term331 (x0 : nat) (x1 : nat) := ~ (~ (Peano.le x0 x1)).
Definition term284 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat) := (fun y0 : nat => ((~ (x0 = (Nat.add x1 y0))) \/ (x2 y0)) /\ (((~ (Peano.lt x0 x1)) \/ (~ (y0 = (NUMERAL 0)))) \/ (x2 y0))) x3.
Definition term372 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (Peano.lt x0 x1)) \/ (~ (x2 = (NUMERAL 0)))).
Definition term121 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := and (~ (x0 (Nat.sub x1 x2))).
Definition term393 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := @eq Prop (x0 (Nat.sub (Nat.add x2 x1) x2)).
Definition term451 (x0 : nat) (x1 : nat -> Prop) := or ((x1 x0) /\ (~ (forall y0 : nat, (x0 = y0) -> x1 y0))).
Definition term479 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := ((fun y0 : nat => (x2 x1) /\ ((x1 = y0) /\ (~ (x2 y0)))) x0) \/ ((~ (x2 x1)) /\ (forall y0 : nat, (~ (x1 = y0)) \/ (x2 y0))).
Definition term163 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat -> Prop) := ((fun y0 : nat => (x3 (Nat.sub x1 x2)) /\ (((x1 = (Nat.add x2 y0)) \/ ((Peano.lt x1 x2) /\ (y0 = (NUMERAL 0)))) /\ (~ (x3 y0)))) x0) \/ ((~ (x3 (Nat.sub x1 x2))) /\ (forall y0 : nat, ((~ (x1 = (Nat.add x2 y0))) /\ ((~ (Peano.lt x1 x2)) \/ (~ (y0 = (NUMERAL 0))))) \/ (x3 y0))).
Definition term168 (x0 : nat) (x1 : nat) := (~ (Peano.lt x0 x1)) \/ (Peano.le x0 x1).
Definition term251 (x0 : nat) := forall y0 : nat, (~ (Peano.lt x0 y0)) \/ (~ (Peano.le y0 x0)).
Definition term476 (x0 : nat) (x1 : nat -> Prop) := @eq Prop ((exists y0 : nat, (x1 x0) /\ ((x0 = y0) /\ (~ (x1 y0)))) \/ ((~ (x1 x0)) /\ (forall y0 : nat, (~ (x0 = y0)) \/ (x1 y0)))).
Definition term475 (x0 : nat) (x1 : nat -> Prop) := @eq Prop ((exists y0 : nat, (fun y1 : nat => (x1 x0) /\ ((x0 = y1) /\ (~ (x1 y1)))) y0) \/ ((~ (x1 x0)) /\ (forall y0 : nat, (~ (x0 = y0)) \/ (x1 y0)))).
Definition term160 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := @eq Prop ((exists y0 : nat, (x2 (Nat.sub x0 x1)) /\ (((x0 = (Nat.add x1 y0)) \/ ((Peano.lt x0 x1) /\ (y0 = (NUMERAL 0)))) /\ (~ (x2 y0)))) \/ ((~ (x2 (Nat.sub x0 x1))) /\ (forall y0 : nat, ((~ (x0 = (Nat.add x1 y0))) /\ ((~ (Peano.lt x0 x1)) \/ (~ (y0 = (NUMERAL 0))))) \/ (x2 y0)))).
Definition term159 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := @eq Prop ((exists y0 : nat, (fun y1 : nat => (x2 (Nat.sub x0 x1)) /\ (((x0 = (Nat.add x1 y1)) \/ ((Peano.lt x0 x1) /\ (y1 = (NUMERAL 0)))) /\ (~ (x2 y1)))) y0) \/ ((~ (x2 (Nat.sub x0 x1))) /\ (forall y0 : nat, ((~ (x0 = (Nat.add x1 y0))) /\ ((~ (Peano.lt x0 x1)) \/ (~ (y0 = (NUMERAL 0))))) \/ (x2 y0)))).
Definition term124 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := and (x0 (Nat.sub x1 x2)).
Definition term388 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (fun y0 : nat => (x0 (Nat.sub y0 x1)) = (forall y1 : nat, ((y0 = (Nat.add x1 y1)) \/ ((Peano.lt y0 x1) /\ (y1 = (NUMERAL 0)))) -> x0 y1)) (Nat.add x1 x2).
Definition term173 (x0 : nat) (x1 : nat) := (((Nat.sub x0 x1) = (NUMERAL 0)) \/ (~ (Peano.le x0 x1))) /\ ((~ ((Nat.sub x0 x1) = (NUMERAL 0))) \/ (Peano.le x0 x1)).
Definition term437 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, ~ ((fun y1 : nat => (x0 = y1) -> x1 y1) y0).
Definition term113 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := exists y0 : nat, ~ ((fun y1 : nat => ((x0 = (Nat.add x1 y1)) \/ ((Peano.lt x0 x1) /\ (y1 = (NUMERAL 0)))) -> x2 y1) y0).
Definition term19 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt y0 x0) = (~ (Peano.le x0 y0))) x1.
Definition term321 (x0 : nat) (x1 : nat) := (~ (Peano.lt x0 x1)) -> Peano.lt x0 x1.
Definition term174 (x0 : nat) := fun y0 : nat => (((Nat.sub x0 y0) = (NUMERAL 0)) \/ (~ (Peano.le x0 y0))) /\ ((~ ((Nat.sub x0 y0) = (NUMERAL 0))) \/ (Peano.le x0 y0)).
Definition term477 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := or ((fun y0 : nat => (x1 x0) /\ ((x0 = y0) /\ (~ (x1 y0)))) x2).
Definition term101 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((x0 = (Nat.add x1 x2)) \/ ((Peano.lt x0 x1) /\ (x2 = (NUMERAL 0)))).
Definition term404 (x0 : nat) (x1 : nat) (x2 : nat) := or ((Nat.add x1 x0) = (Nat.add x1 x2)).
Definition term254 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (Peano.lt x0 y1) \/ (Peano.le y1 x0)) y0.
Definition term201 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (~ ((Nat.sub x0 y1) = (NUMERAL 0))) \/ (Peano.le x0 y1)) y0.
Definition term22 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.sub (Nat.add x0 y0) x0) = y0) x1.
Definition term480 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := ((x2 x1) /\ ((x1 = x0) /\ (~ (x2 x0)))) \/ ((~ (x2 x1)) /\ (forall y0 : nat, (~ (x1 = y0)) \/ (x2 y0))).
Definition term53 := (forall y0 : nat, forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) = (Peano.le y0 y1)) -> ~ (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)).
Definition term472 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => (x1 x0) /\ ((x0 = y1) /\ (~ (x1 y1)))) y0.
Definition term156 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => (x2 (Nat.sub x0 x1)) /\ (((x0 = (Nat.add x1 y1)) \/ ((Peano.lt x0 x1) /\ (y1 = (NUMERAL 0)))) /\ (~ (x2 y1)))) y0.
Definition term409 (x0 : nat) (x1 : nat) := (x0 = x1) \/ False.
Definition term272 := and (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 y2)) \/ (~ (Peano.le y2 y1))) y0).
Definition term252 (x0 : nat) := and (forall y0 : nat, (fun y1 : nat => (~ (Peano.lt x0 y1)) \/ (~ (Peano.le y1 x0))) y0).
Definition term221 := and (forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Nat.sub y1 y2) = (NUMERAL 0)) \/ (~ (Peano.le y1 y2))) y0).
Definition term199 (x0 : nat) := and (forall y0 : nat, (fun y1 : nat => ((Nat.sub x0 y1) = (NUMERAL 0)) \/ (~ (Peano.le x0 y1))) y0).
Definition term319 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term264 (x0 : nat) := and ((fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0))) x0).
Definition term212 (x0 : nat) := and ((fun y0 : nat => forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) \/ (~ (Peano.le y0 y1))) x0).
Definition term232 (x0 : nat) (x1 : nat) := ((~ (Peano.lt x1 x0)) \/ (~ (Peano.le x0 x1))) /\ ((~ (~ (Peano.lt x1 x0))) \/ (Peano.le x0 x1)).
Definition term166 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := fun y0 : nat => ((x2 (Nat.sub x0 x1)) /\ (((x0 = (Nat.add x1 y0)) \/ ((Peano.lt x0 x1) /\ (y0 = (NUMERAL 0)))) /\ (~ (x2 y0)))) \/ ((~ (x2 (Nat.sub x0 x1))) /\ (forall y1 : nat, ((~ (x0 = (Nat.add x1 y1))) /\ ((~ (Peano.lt x0 x1)) \/ (~ (y1 = (NUMERAL 0))))) \/ (x2 y1))).
Definition term30 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term13 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Nat.add x0 x1) = (Nat.add x0 y0)) = (x1 = y0)) x2.
Definition term416 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := fun y0 : nat => (((Nat.add x1 x0) = (Nat.add x1 y0)) \/ ((Peano.lt (Nat.add x1 x0) x1) /\ (y0 = (NUMERAL 0)))) -> x2 y0.
Definition term94 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := fun y0 : nat => ((x0 = (Nat.add x1 y0)) \/ ((Peano.lt x0 x1) /\ (y0 = (NUMERAL 0)))) -> x2 y0.
Definition term127 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := or ((x2 (Nat.sub x0 x1)) /\ (~ (forall y0 : nat, ((x0 = (Nat.add x1 y0)) \/ ((Peano.lt x0 x1) /\ (y0 = (NUMERAL 0)))) -> x2 y0))).
Definition term228 (x0 : nat) (x1 : nat) := or (~ (~ (Peano.lt x0 x1))).
Definition term454 (x0 : nat) (x1 : nat -> Prop) := ((x1 x0) /\ (exists y0 : nat, (x0 = y0) /\ (~ (x1 y0)))) \/ ((~ (x1 x0)) /\ (forall y0 : nat, (~ (x0 = y0)) \/ (x1 y0))).
Definition term391 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := @eq Prop ((fun y0 : nat => (x1 (Nat.sub y0 x0)) = (forall y1 : nat, ((y0 = (Nat.add x0 y1)) \/ ((Peano.lt y0 x0) /\ (y1 = (NUMERAL 0)))) -> x1 y1)) x2).
Definition term261 := fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0)).
Definition term209 := fun y0 : nat => forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) \/ (~ (Peano.le y0 y1)).
Definition term6 := fun y0 : nat => forall y1 : nat, (Peano.lt y1 y0) = (~ (Peano.le y0 y1)).
Definition term97 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.lt x0 x1)) \/ (~ (x2 = (NUMERAL 0))).
Definition term178 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term336 (x0 : nat) (x1 : nat) := ~ ((Nat.sub x0 x1) = (NUMERAL 0)).
Definition term355 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (x2 = x0) /\ (x1 x2).
Definition term258 := forall y0 : nat, (forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0))) /\ (forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0)).
Definition term206 := forall y0 : nat, (forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) \/ (~ (Peano.le y0 y1))) /\ (forall y1 : nat, (~ ((Nat.sub y0 y1) = (NUMERAL 0))) \/ (Peano.le y0 y1)).
Definition term417 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (x0 = y0) -> x1 y0.
Definition term448 (x0 : nat -> Prop) (x1 : nat) := and (x0 x1).
Definition term135 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := (x2 (Nat.sub x0 x1)) /\ (exists y0 : nat, (fun y1 : nat => ((x0 = (Nat.add x1 y1)) \/ ((Peano.lt x0 x1) /\ (y1 = (NUMERAL 0)))) /\ (~ (x2 y1))) y0).
Definition term244 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => (~ (Peano.lt x0 y0)) \/ (~ (Peano.le y0 x0))) x1).
Definition term188 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => ((Nat.sub x0 y0) = (NUMERAL 0)) \/ (~ (Peano.le x0 y0))) x1).
Definition term440 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => ~ ((fun y1 : nat => (x0 = y1) -> x1 y1) y0).
Definition term116 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := fun y0 : nat => ~ ((fun y1 : nat => ((x0 = (Nat.add x1 y1)) \/ ((Peano.lt x0 x1) /\ (y1 = (NUMERAL 0)))) -> x2 y1) y0).
Definition term423 (x0 : nat) (x1 : nat -> Prop) := (((~ ((x1 x0) = (forall y0 : nat, (x0 = y0) -> x1 y0))) -> False) -> (~ ((x1 x0) = (forall y0 : nat, (x0 = y0) -> x1 y0))) -> False) -> ((~ ((x1 x0) = (forall y0 : nat, (x0 = y0) -> x1 y0))) -> False) -> (~ ((x1 x0) = (forall y0 : nat, (x0 = y0) -> x1 y0))) -> False.
Definition term85 (x0 : nat) (x1 : nat) := (Peano.lt x0 x1) -> Peano.le x0 x1.
Definition term32 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term380 (x0 : nat) (x1 : nat) := (Peano.lt x0 x1) /\ ((Nat.sub x0 x1) = (NUMERAL 0)).
Definition term87 (x0 : nat) := forall y0 : nat, (Peano.lt x0 y0) -> Peano.le x0 y0.
Definition term419 (x0 : nat) (x1 : nat -> Prop) := (~ ((x1 x0) = (forall y0 : nat, (x0 = y0) -> x1 y0))) -> False.
Definition term42 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := (~ ((x2 (Nat.sub x0 x1)) = (forall y0 : nat, ((x0 = (Nat.add x1 y0)) \/ ((Peano.lt x0 x1) /\ (y0 = (NUMERAL 0)))) -> x2 y0))) -> False.
Definition term453 (x0 : nat) (x1 : nat -> Prop) := ((x1 x0) /\ (~ (forall y0 : nat, (x0 = y0) -> x1 y0))) \/ ((~ (x1 x0)) /\ (forall y0 : nat, (x0 = y0) -> x1 y0)).
Definition term474 (x0 : nat) (x1 : nat -> Prop) := or (exists y0 : nat, (fun y1 : nat => (x1 x0) /\ ((x0 = y1) /\ (~ (x1 y1)))) y0).
Definition term158 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := or (exists y0 : nat, (fun y1 : nat => (x2 (Nat.sub x0 x1)) /\ (((x0 = (Nat.add x1 y1)) \/ ((Peano.lt x0 x1) /\ (y1 = (NUMERAL 0)))) /\ (~ (x2 y1)))) y0).
Definition term146 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := exists y0 : nat, (x2 (Nat.sub x0 x1)) /\ (((x0 = (Nat.add x1 y0)) \/ ((Peano.lt x0 x1) /\ (y0 = (NUMERAL 0)))) /\ (~ (x2 y0))).
Definition term431 := forall y0 : nat -> Prop, forall y1 : nat, (~ ((y0 y1) = (forall y2 : nat, (y1 = y2) -> y0 y2))) -> False.
Definition term114 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat) := (fun y0 : nat => ((x0 = (Nat.add x1 y0)) \/ ((Peano.lt x0 x1) /\ (y0 = (NUMERAL 0)))) -> x2 y0) x3.
Definition term376 (x0 : nat) := ~ (~ (x0 = (NUMERAL 0))).
Definition term340 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (~ (x2 = x0)) \/ (~ (x1 x2)).
Definition term203 (x0 : nat) := forall y0 : nat, (~ ((Nat.sub x0 y0) = (NUMERAL 0))) \/ (Peano.le x0 y0).
Definition term170 (x0 : nat) := forall y0 : nat, (~ (Peano.lt x0 y0)) \/ (Peano.le x0 y0).
Definition term279 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (x0 = (Nat.add x1 x2)).
Definition term351 (x0 : nat) (x1 : nat) := ~ (~ (x0 = x1)).
Definition term414 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat) := (((Nat.add x1 x0) = (Nat.add x1 x3)) \/ ((Peano.lt (Nat.add x1 x0) x1) /\ (x3 = (NUMERAL 0)))) -> x2 x3.
Definition term93 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat) := ((x0 = (Nat.add x1 x3)) \/ ((Peano.lt x0 x1) /\ (x3 = (NUMERAL 0)))) -> x2 x3.
Definition term26 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1))) x1.
Definition term66 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (Peano.lt y0 x0) -> (~ ((x1 (Nat.sub y0 x0)) = (forall y1 : nat, ((y0 = (Nat.add x0 y1)) \/ ((Peano.lt y0 x0) /\ (y1 = (NUMERAL 0)))) -> x1 y1))) -> (forall y1 : nat, forall y2 : nat, Peano.le y1 (Nat.add y1 y2)) -> (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> Peano.le y1 y2) -> (forall y1 : nat, forall y2 : nat, ((Nat.sub y1 y2) = (NUMERAL 0)) = (Peano.le y1 y2)) -> ~ (forall y1 : nat, forall y2 : nat, (~ (Peano.lt y1 y2)) = (Peano.le y2 y1)).
Definition term65 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (Peano.lt y0 x0) -> (~ ((x1 (Nat.sub y0 x0)) = (forall y1 : nat, ((y0 = (Nat.add x0 y1)) \/ ((Peano.lt y0 x0) /\ (y1 = (NUMERAL 0)))) -> x1 y1))) -> (forall y1 : nat, forall y2 : nat, Peano.le y1 (Nat.add y1 y2)) -> (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> Peano.le y1 y2) -> (forall y1 : nat, forall y2 : nat, ((Nat.sub y1 y2) = (NUMERAL 0)) = (Peano.le y1 y2)) -> (forall y1 : nat, forall y2 : nat, (~ (Peano.lt y1 y2)) = (Peano.le y2 y1)) -> False.
Definition term438 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (fun y0 : nat => (x0 = y0) -> x1 y0) x2.
Definition term400 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat) (x4 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((((Nat.add x1 x0) = (Nat.add x1 x3)) \/ ((Peano.lt (Nat.add x1 x0) x1) /\ (x3 = (NUMERAL 0)))) = y0) -> (y0 -> (x2 x3) = y1) -> ((((Nat.add x1 x0) = (Nat.add x1 x3)) \/ ((Peano.lt (Nat.add x1 x0) x1) /\ (x3 = (NUMERAL 0)))) -> x2 x3) = (y0 -> y1)) x4.
Definition term382 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (x0 (Nat.sub x1 x2)) -> False.
Definition term411 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) (x3 : nat) (x4 : Prop) := ((x2 = x3) -> (x1 x3) = x4) -> ((((Nat.add x0 x2) = (Nat.add x0 x3)) \/ ((Peano.lt (Nat.add x0 x2) x0) /\ (x3 = (NUMERAL 0)))) -> x1 x3) = ((x2 = x3) -> x4).
Definition term306 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 (Nat.add x0 x1)).
Definition term293 (x0 : nat) (x1 : nat) := Peano.lt (Nat.add x1 x0) x1.
Definition term100 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = (Nat.add x1 x2))) /\ ((~ (Peano.lt x0 x1)) \/ (~ (x2 = (NUMERAL 0)))).
Definition term275 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.lt y1 y2) \/ (Peano.le y2 y1)) y0.
Definition term270 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 y2)) \/ (~ (Peano.le y2 y1))) y0.
Definition term224 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ ((Nat.sub y1 y2) = (NUMERAL 0))) \/ (Peano.le y1 y2)) y0.
Definition term219 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Nat.sub y1 y2) = (NUMERAL 0)) \/ (~ (Peano.le y1 y2))) y0.
Definition term91 := fun y0 : nat => forall y1 : nat, Peano.le y0 (Nat.add y0 y1).
Definition term455 (x0 : nat) (x1 : nat -> Prop) := (x1 x0) /\ (exists y0 : nat, (fun y1 : nat => (x0 = y1) /\ (~ (x1 y1))) y0).
Definition term312 (x0 : nat) (x1 : nat) := (Peano.lt (Nat.add x0 x1) x0) /\ (Peano.le x0 (Nat.add x0 x1)).
Definition term57 := imp (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)).
Definition term54 := imp (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1).
Definition term51 := imp (forall y0 : nat, forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) = (Peano.le y0 y1)).
Definition term357 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := imp ((x2 = x0) /\ (x1 x2)).
Definition term287 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := ~ (x0 (Nat.sub x1 x2)).
Definition term111 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term109 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat) := ((~ (x0 = (Nat.add x1 x3))) /\ ((~ (Peano.lt x0 x1)) \/ (~ (x3 = (NUMERAL 0))))) \/ (x2 x3).
Definition term379 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat) := ((Peano.lt x0 x1) /\ (x3 = (NUMERAL 0))) -> x2 x3.
Definition term443 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (~ (x0 = y0)) \/ (x1 y0).
Definition term412 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (x0 = x2) -> (x1 x2) = (x1 x2).
Definition term405 (x0 : nat) (x1 : nat) := or (x0 = x1).
Definition term242 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.lt x0 y0)) \/ (~ (Peano.le y0 x0))) x1.
Definition term236 := fun y0 : nat => forall y1 : nat, ((~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0))) /\ ((Peano.lt y0 y1) \/ (Peano.le y1 y0)).
Definition term176 := fun y0 : nat => forall y1 : nat, (((Nat.sub y0 y1) = (NUMERAL 0)) \/ (~ (Peano.le y0 y1))) /\ ((~ ((Nat.sub y0 y1) = (NUMERAL 0))) \/ (Peano.le y0 y1)).
Definition term70 (x0 : nat -> Prop) := fun y0 : nat => forall y1 : nat, (Peano.lt y1 y0) -> (~ ((x0 (Nat.sub y1 y0)) = (forall y2 : nat, ((y1 = (Nat.add y0 y2)) \/ ((Peano.lt y1 y0) /\ (y2 = (NUMERAL 0)))) -> x0 y2))) -> (forall y2 : nat, forall y3 : nat, Peano.le y2 (Nat.add y2 y3)) -> (forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> Peano.le y2 y3) -> (forall y2 : nat, forall y3 : nat, ((Nat.sub y2 y3) = (NUMERAL 0)) = (Peano.le y2 y3)) -> ~ (forall y2 : nat, forall y3 : nat, (~ (Peano.lt y2 y3)) = (Peano.le y3 y2)).
Definition term69 (x0 : nat -> Prop) := fun y0 : nat => forall y1 : nat, (Peano.lt y1 y0) -> (~ ((x0 (Nat.sub y1 y0)) = (forall y2 : nat, ((y1 = (Nat.add y0 y2)) \/ ((Peano.lt y1 y0) /\ (y2 = (NUMERAL 0)))) -> x0 y2))) -> (forall y2 : nat, forall y3 : nat, Peano.le y2 (Nat.add y2 y3)) -> (forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> Peano.le y2 y3) -> (forall y2 : nat, forall y3 : nat, ((Nat.sub y2 y3) = (NUMERAL 0)) = (Peano.le y2 y3)) -> (forall y2 : nat, forall y3 : nat, (~ (Peano.lt y2 y3)) = (Peano.le y3 y2)) -> False.
Definition term487 (x0 : nat -> Prop) (x1 : nat) := @eq Prop ((fun y0 : nat => x0 y0) x1).
Definition term152 (x0 : nat -> Prop) (x1 : Prop) := exists y0 : nat, (x0 y0) \/ x1.
Definition term46 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := (((Peano.lt x0 x1) -> (~ ((x2 (Nat.sub x0 x1)) = (forall y0 : nat, ((x0 = (Nat.add x1 y0)) \/ ((Peano.lt x0 x1) /\ (y0 = (NUMERAL 0)))) -> x2 y0))) -> (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> (forall y0 : nat, forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) = (Peano.le y0 y1)) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> False) -> (Peano.lt x0 x1) -> (~ ((x2 (Nat.sub x0 x1)) = (forall y0 : nat, ((x0 = (Nat.add x1 y0)) \/ ((Peano.lt x0 x1) /\ (y0 = (NUMERAL 0)))) -> x2 y0))) -> (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> (forall y0 : nat, forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) = (Peano.le y0 y1)) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> False) -> (Peano.lt x0 x1) -> (~ ((x2 (Nat.sub x0 x1)) = (forall y0 : nat, ((x0 = (Nat.add x1 y0)) \/ ((Peano.lt x0 x1) /\ (y0 = (NUMERAL 0)))) -> x2 y0))) -> (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> (forall y0 : nat, forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) = (Peano.le y0 y1)) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> False.
Definition term316 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ((x1 x2) = (x1 x0)) -> (x1 x0) \/ (~ (x1 x2)).
Definition term434 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (x0 = x2) /\ (~ (x1 x2)).
Definition term296 (x0 : nat -> Prop) := fun y0 : nat => ~ (x0 y0).
Definition term385 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (fun y0 : nat => (Peano.lt y0 x0) -> (~ ((x1 (Nat.sub y0 x0)) = (forall y1 : nat, ((y0 = (Nat.add x0 y1)) \/ ((Peano.lt y0 x0) /\ (y1 = (NUMERAL 0)))) -> x1 y1))) -> (forall y1 : nat, forall y2 : nat, Peano.le y1 (Nat.add y1 y2)) -> (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> Peano.le y1 y2) -> (forall y1 : nat, forall y2 : nat, ((Nat.sub y1 y2) = (NUMERAL 0)) = (Peano.le y1 y2)) -> (forall y1 : nat, forall y2 : nat, (~ (Peano.lt y1 y2)) = (Peano.le y2 y1)) -> False) x2.
Definition term428 (x0 : nat -> Prop) := forall y0 : nat, (x0 y0) = (forall y1 : nat, (y0 = y1) -> x0 y1).
Definition term187 (x0 : nat) (x1 : nat) := ((Nat.sub x0 x1) = (NUMERAL 0)) \/ (~ (Peano.le x0 x1)).
Definition term302 (x0 : nat) (x1 : nat) := (~ (Peano.lt (Nat.add x1 x0) x1)) -> Peano.lt (Nat.add x1 x0) x1.
Definition term38 (x0 : nat) (x1 : nat) := (Peano.lt x1 x0) \/ (Peano.le x0 x1).
Definition term496 (x0 : nat) (x1 : nat) := imp (~ (~ (x0 = x1))).
Definition term332 (x0 : nat) (x1 : nat) := imp (~ (~ (Peano.le x0 x1))).
Definition term328 (x0 : nat) (x1 : nat) := imp (~ (~ (Peano.lt x0 x1))).
Definition term464 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (x1 x0) /\ ((fun y1 : nat => (x0 = y1) /\ (~ (x1 y1))) y0).
