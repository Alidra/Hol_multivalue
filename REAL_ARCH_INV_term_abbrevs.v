Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term189 (x0 : nat) (x1 : real) := (x0 = (NUMERAL 0)) \/ ((~ (real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num x0)))) \/ (~ (real_lt (real_inv (real_of_num x0)) x1))).
Definition term325 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ ((~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ (~ (real_lt x0 x1))))) -> real_lt x2 x3.
Definition term275 (x0 : real) (x1 : nat) := (~ (real_lt (real_inv x0) (real_of_num x1))) -> real_lt (real_inv x0) (real_of_num x1).
Definition term168 (x0 : real) (x1 : real) := ((real_lt (real_of_num (NUMERAL 0)) x1) /\ (real_lt x1 x0)) -> real_lt (real_inv x0) (real_inv x1).
Definition term61 (x0 : real) := fun y0 : nat => ((fun y1 : nat => (~ (y1 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y1))) /\ (real_lt (real_inv (real_of_num y1)) x0))) y0) /\ (~ (real_lt (real_of_num (NUMERAL 0)) x0)).
Definition term336 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := imp (~ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (real_lt x2 x3))))).
Definition term196 (x0 : nat -> Prop) := ~ (all x0).
Definition term114 := (~ False) -> False.
Definition term120 (x0 : real) (x1 : nat) := real_lt (real_inv x0) (real_of_num x1).
Definition term125 (x0 : real) := fun y0 : nat => ((fun y1 : nat => real_lt (real_inv x0) (real_of_num y1)) y0) -> (fun y1 : nat => (~ (y1 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y1))) /\ (real_lt (real_inv (real_of_num y1)) x0))) y0.
Definition term156 := imp (forall y0 : real, forall y1 : real, ~ ((real_lt y0 y1) /\ (real_lt y1 y0))).
Definition term153 := imp (forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2).
Definition term25 (x0 : real) := imp (~ ((exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0))) -> real_lt (real_of_num (NUMERAL 0)) x0)).
Definition term66 (x0 : real) (x1 : real) (x2 : real) := or (~ ((real_lt x0 x1) /\ (real_lt x1 x2))).
Definition term316 (x0 : nat) (x1 : real) := ~ (real_lt (real_inv (real_of_num x0)) (real_inv (real_inv x1))).
Definition term246 (x0 : real) (x1 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 x1).
Definition term133 (x0 : real) := imp (exists y0 : nat, (fun y1 : nat => real_lt (real_inv x0) (real_of_num y1)) y0).
Definition term39 (x0 : real) := fun y0 : nat => (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0)).
Definition term103 (x0 : Prop) := ~ (~ x0).
Definition term111 := real_of_num (NUMERAL 0).
Definition term112 (x0 : real) := (~ (real_lt (real_of_num (NUMERAL 0)) x0)) -> real_lt (real_of_num (NUMERAL 0)) x0.
Definition term239 (x0 : real) (x1 : real) := ~ ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 x1)).
Definition term38 (x0 : nat) (x1 : real) := (~ (x0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num x0))) /\ (real_lt (real_inv (real_of_num x0)) x1)).
Definition term167 := forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) -> (~ (forall y1 : nat, (real_lt (real_inv y0) (real_of_num y1)) -> (~ (y1 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y1))) /\ (real_lt (real_inv (real_of_num y1)) y0)))) -> (forall y1 : real, forall y2 : real, ~ ((real_lt y1 y2) /\ (real_lt y2 y1))) -> (forall y1 : real, forall y2 : real, forall y3 : real, ((real_lt y1 y2) /\ (real_lt y2 y3)) -> real_lt y1 y3) -> (forall y1 : real, (real_lt (real_of_num (NUMERAL 0)) (real_inv y1)) = (real_lt (real_of_num (NUMERAL 0)) y1)) -> (forall y1 : real, (real_inv (real_inv y1)) = y1) -> ~ (forall y1 : real, forall y2 : real, ((real_lt (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2)) -> real_lt (real_inv y2) (real_inv y1)).
Definition term166 := forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) -> (~ (forall y1 : nat, (real_lt (real_inv y0) (real_of_num y1)) -> (~ (y1 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y1))) /\ (real_lt (real_inv (real_of_num y1)) y0)))) -> (forall y1 : real, forall y2 : real, ~ ((real_lt y1 y2) /\ (real_lt y2 y1))) -> (forall y1 : real, forall y2 : real, forall y3 : real, ((real_lt y1 y2) /\ (real_lt y2 y3)) -> real_lt y1 y3) -> (forall y1 : real, (real_lt (real_of_num (NUMERAL 0)) (real_inv y1)) = (real_lt (real_of_num (NUMERAL 0)) y1)) -> (forall y1 : real, (real_inv (real_inv y1)) = y1) -> (forall y1 : real, forall y2 : real, ((real_lt (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2)) -> real_lt (real_inv y2) (real_inv y1)) -> False.
Definition term225 (x0 : real) := (~ (real_lt (real_of_num (NUMERAL 0)) (real_inv x0))) \/ (real_lt (real_of_num (NUMERAL 0)) x0).
Definition term161 (x0 : real) := (~ (forall y0 : nat, (real_lt (real_inv x0) (real_of_num y0)) -> (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0)))) -> (forall y0 : real, forall y1 : real, ~ ((real_lt y0 y1) /\ (real_lt y1 y0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) (real_inv y0)) = (real_lt (real_of_num (NUMERAL 0)) y0)) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> ~ (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1)) -> real_lt (real_inv y1) (real_inv y0)).
Definition term160 (x0 : real) := (~ (forall y0 : nat, (real_lt (real_inv x0) (real_of_num y0)) -> (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0)))) -> (forall y0 : real, forall y1 : real, ~ ((real_lt y0 y1) /\ (real_lt y1 y0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) (real_inv y0)) = (real_lt (real_of_num (NUMERAL 0)) y0)) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1)) -> real_lt (real_inv y1) (real_inv y0)) -> False.
Definition term234 := and (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) (real_inv y0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) y0))).
Definition term176 := fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) (real_inv y0)) = (real_lt (real_of_num (NUMERAL 0)) y0).
Definition term193 (x0 : nat) (x1 : real) := (real_lt (real_inv x1) (real_of_num x0)) /\ (~ ((~ (x0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num x0))) /\ (real_lt (real_inv (real_of_num x0)) x1)))).
Definition term18 (x0 : real) := (~ ((exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0))) -> real_lt (real_of_num (NUMERAL 0)) x0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> False.
Definition term333 (x0 : real) (x1 : real) (x2 : real) := (~ (~ (x2 = x0))) /\ (~ (~ (real_lt x1 x2))).
Definition term102 (x0 : real) (x1 : real) (x2 : real) := (~ (~ (real_lt x0 x1))) /\ (~ (~ (real_lt x1 x2))).
Definition term90 (x0 : real) (x1 : real) (x2 : real) := (~ (real_lt x0 x2)) \/ (real_lt x1 x2).
Definition term195 (x0 : nat) (x1 : real) := ~ ((real_lt (real_inv x1) (real_of_num x0)) -> (~ (x0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num x0))) /\ (real_lt (real_inv (real_of_num x0)) x1))).
Definition term20 (x0 : real) := (((~ ((exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0))) -> real_lt (real_of_num (NUMERAL 0)) x0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> False) -> (~ ((exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0))) -> real_lt (real_of_num (NUMERAL 0)) x0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> False) -> (~ ((exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0))) -> real_lt (real_of_num (NUMERAL 0)) x0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> False.
Definition term3 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term267 (x0 : real) := (~ (real_lt (real_of_num (NUMERAL 0)) (real_inv x0))) -> real_lt (real_of_num (NUMERAL 0)) (real_inv x0).
Definition term233 := and (forall y0 : real, (fun y1 : real => (real_lt (real_of_num (NUMERAL 0)) (real_inv y1)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) y1))) y0).
Definition term136 (x0 : real) := (exists y0 : nat, real_lt (real_inv x0) (real_of_num y0)) -> exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0)).
Definition term14 (x0 : Prop) := (~ x0) -> False.
Definition term89 (x0 : nat) (x1 : real) := ~ (real_lt (real_inv (real_of_num x0)) x1).
Definition term311 (x0 : real) (x1 : real) := imp (~ ((~ (real_lt (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_lt x0 x1)))).
Definition term107 (x0 : real) (x1 : real) (x2 : real) := imp (~ ((~ (real_lt x0 x1)) \/ (~ (real_lt x1 x2)))).
Definition term127 (x0 : real) := forall y0 : nat, ((fun y1 : nat => real_lt (real_inv x0) (real_of_num y1)) y0) -> (fun y1 : nat => (~ (y1 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y1))) /\ (real_lt (real_inv (real_of_num y1)) x0))) y0.
Definition term94 (x0 : real) (x1 : real) (x2 : real) := (real_lt x0 x2) \/ ((~ (real_lt x0 x1)) \/ (~ (real_lt x1 x2))).
Definition term163 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) -> (~ (forall y0 : nat, (real_lt (real_inv x0) (real_of_num y0)) -> (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0)))) -> (forall y0 : real, forall y1 : real, ~ ((real_lt y0 y1) /\ (real_lt y1 y0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) (real_inv y0)) = (real_lt (real_of_num (NUMERAL 0)) y0)) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> ~ (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1)) -> real_lt (real_inv y1) (real_inv y0)).
Definition term140 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) -> (~ (forall y0 : nat, (real_lt (real_inv x0) (real_of_num y0)) -> (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0)))) -> (forall y0 : real, forall y1 : real, ~ ((real_lt y0 y1) /\ (real_lt y1 y0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) (real_inv y0)) = (real_lt (real_of_num (NUMERAL 0)) y0)) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1)) -> real_lt (real_inv y1) (real_inv y0)) -> False.
Definition term315 (x0 : nat) (x1 : real) := (~ (real_lt (real_inv (real_of_num x0)) (real_inv (real_inv x1)))) -> real_lt (real_inv (real_of_num x0)) (real_inv (real_inv x1)).
Definition term261 (x0 : real) := (~ (real_lt (real_inv x0) (real_of_num (NUMERAL 0)))) -> real_lt (real_inv x0) (real_of_num (NUMERAL 0)).
Definition term58 (x0 : nat) (x1 : real) := and ((~ (x0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num x0))) /\ (real_lt (real_inv (real_of_num x0)) x1))).
Definition term158 := (forall y0 : real, forall y1 : real, ~ ((real_lt y0 y1) /\ (real_lt y1 y0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) (real_inv y0)) = (real_lt (real_of_num (NUMERAL 0)) y0)) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> ~ (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1)) -> real_lt (real_inv y1) (real_inv y0)).
Definition term240 (x0 : real) (x1 : real) := (~ (real_lt (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_lt x0 x1)).
Definition term126 (x0 : real) := fun y0 : nat => (real_lt (real_inv x0) (real_of_num y0)) -> (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0)).
Definition term27 := fun y0 : real => (~ ((exists y1 : nat, (~ (y1 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y1))) /\ (real_lt (real_inv (real_of_num y1)) y0))) -> real_lt (real_of_num (NUMERAL 0)) y0)) -> (forall y1 : real, forall y2 : real, forall y3 : real, ((real_lt y1 y2) /\ (real_lt y2 y3)) -> real_lt y1 y3) -> False.
Definition term179 (x0 : real) := fun y0 : real => ~ ((real_lt x0 y0) /\ (real_lt y0 x0)).
Definition term97 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term173 := fun y0 : real => (real_inv (real_inv y0)) = y0.
Definition term141 (x0 : real) := ((real_lt (real_of_num (NUMERAL 0)) x0) -> (~ (forall y0 : nat, (real_lt (real_inv x0) (real_of_num y0)) -> (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0)))) -> (forall y0 : real, forall y1 : real, ~ ((real_lt y0 y1) /\ (real_lt y1 y0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) (real_inv y0)) = (real_lt (real_of_num (NUMERAL 0)) y0)) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1)) -> real_lt (real_inv y1) (real_inv y0)) -> False) -> (real_lt (real_of_num (NUMERAL 0)) x0) -> (~ (forall y0 : nat, (real_lt (real_inv x0) (real_of_num y0)) -> (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0)))) -> (forall y0 : real, forall y1 : real, ~ ((real_lt y0 y1) /\ (real_lt y1 y0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) (real_inv y0)) = (real_lt (real_of_num (NUMERAL 0)) y0)) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1)) -> real_lt (real_inv y1) (real_inv y0)) -> False.
Definition term217 := (forall y0 : real, (fun y1 : real => (real_lt (real_of_num (NUMERAL 0)) (real_inv y1)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) y1))) y0) /\ (forall y0 : real, (fun y1 : real => (~ (real_lt (real_of_num (NUMERAL 0)) (real_inv y1))) \/ (real_lt (real_of_num (NUMERAL 0)) y1)) y0).
Definition term139 (x0 : real) := ~ (forall y0 : nat, (real_lt (real_inv x0) (real_of_num y0)) -> (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0))).
Definition term272 (x0 : real) (x1 : real) := (real_lt x1 x0) /\ (real_lt x0 x1).
Definition term202 (x0 : real) := fun y0 : nat => (real_lt (real_inv x0) (real_of_num y0)) /\ ((y0 = (NUMERAL 0)) \/ ((~ (real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0)))) \/ (~ (real_lt (real_inv (real_of_num y0)) x0)))).
Definition term313 (x0 : nat) (x1 : real) := ((real_lt (real_of_num (NUMERAL 0)) (real_inv x1)) /\ (real_lt (real_inv x1) (real_of_num x0))) -> real_lt (real_inv (real_of_num x0)) (real_inv (real_inv x1)).
Definition term259 (x0 : real) (x1 : nat) := @eq Prop ((fun y0 : nat => real_lt (real_inv x0) (real_of_num y0)) x1).
Definition term87 (x0 : nat) (x1 : real) := real_lt (real_inv (real_of_num x0)) x1.
Definition term242 (x0 : real) (x1 : real) := or (~ ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 x1))).
Definition term269 (x0 : Prop) (x1 : Prop) := (~ x0) \/ (~ x1).
Definition term86 (x0 : Prop) := (~ x0) -> x0.
Definition term181 := fun y0 : real => forall y1 : real, ~ ((real_lt y0 y1) /\ (real_lt y1 y0)).
Definition term194 (x0 : nat) (x1 : real) := (real_lt (real_inv x1) (real_of_num x0)) /\ ((x0 = (NUMERAL 0)) \/ ((~ (real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num x0)))) \/ (~ (real_lt (real_inv (real_of_num x0)) x1)))).
Definition term169 (x0 : real) := fun y0 : real => ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 y0)) -> real_lt (real_inv y0) (real_inv x0).
Definition term155 := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) (real_inv y0)) = (real_lt (real_of_num (NUMERAL 0)) y0)) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> ~ (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1)) -> real_lt (real_inv y1) (real_inv y0)).
Definition term334 (x0 : real) (x1 : real) (x2 : real) := (x2 = x0) /\ (real_lt x1 x2).
Definition term339 (x0 : nat) (x1 : real) := ((real_inv (real_inv x1)) = x1) /\ (real_lt (real_inv (real_of_num x0)) (real_inv (real_inv x1))).
Definition term100 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term32 (x0 : real) (x1 : real) := fun y0 : real => ((real_lt x1 x0) /\ (real_lt x0 y0)) -> real_lt x1 y0.
Definition term95 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((~ (real_lt x1 x0)) \/ ((~ (real_lt x0 x2)) \/ (real_lt x1 x2))).
Definition term54 (x0 : real) := and (exists y0 : nat, (fun y1 : nat => (~ (y1 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y1))) /\ (real_lt (real_inv (real_of_num y1)) x0))) y0).
Definition term13 (x0 : real) := exists y0 : nat, real_lt (real_inv x0) (real_of_num y0).
Definition term270 (x0 : Prop) (x1 : Prop) := ~ (x0 /\ x1).
Definition term250 := forall y0 : real, forall y1 : real, ((~ (real_lt (real_of_num (NUMERAL 0)) y0)) \/ (~ (real_lt y0 y1))) \/ (real_lt (real_inv y1) (real_inv y0)).
Definition term208 := forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) \/ (~ (real_lt y1 y0)).
Definition term182 := forall y0 : real, forall y1 : real, ~ ((real_lt y0 y1) /\ (real_lt y1 y0)).
Definition term146 := forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1)) -> real_lt (real_inv y1) (real_inv y0).
Definition term76 := forall y0 : real, forall y1 : real, forall y2 : real, ((~ (real_lt y0 y1)) \/ (~ (real_lt y1 y2))) \/ (real_lt y0 y2).
Definition term74 (x0 : real) := forall y0 : real, forall y1 : real, ((~ (real_lt x0 y0)) \/ (~ (real_lt y0 y1))) \/ (real_lt x0 y1).
Definition term35 (x0 : real) := forall y0 : real, forall y1 : real, ((real_lt x0 y0) /\ (real_lt y0 y1)) -> real_lt x0 y1.
Definition term24 := forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2.
Definition term134 (x0 : real) := imp (exists y0 : nat, real_lt (real_inv x0) (real_of_num y0)).
Definition term41 (x0 : real) := imp (exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0))).
Definition term119 (x0 : real) (x1 : nat) := (fun y0 : nat => real_lt (real_inv x0) (real_of_num y0)) x1.
Definition term96 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((real_lt x0 x2) \/ ((~ (real_lt x0 x1)) \/ (~ (real_lt x1 x2)))).
Definition term211 := forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) (real_inv y0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) y0))) /\ ((~ (real_lt (real_of_num (NUMERAL 0)) (real_inv y0))) \/ (real_lt (real_of_num (NUMERAL 0)) y0)).
Definition term218 := fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) (real_inv y0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) y0)).
Definition term293 (x0 : nat) := ~ ((real_inv (real_of_num x0)) = (real_inv (real_of_num x0))).
Definition term213 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term278 (x0 : real) (x1 : nat) := ((real_lt (real_of_num (NUMERAL 0)) (real_inv x0)) /\ (real_lt (real_inv x0) (real_of_num x1))) -> real_lt (real_of_num (NUMERAL 0)) (real_of_num x1).
Definition term51 (x0 : real) (x1 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0))) x1.
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term279 (x0 : nat) := real_lt (real_of_num (NUMERAL 0)) (real_of_num x0).
Definition term346 := forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) = (exists y1 : nat, (~ (y1 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y1))) /\ (real_lt (real_inv (real_of_num y1)) y0))).
Definition term174 := forall y0 : real, (real_inv (real_inv y0)) = y0.
Definition term300 (x0 : real) (x1 : real) := (real_lt (real_inv x0) (real_inv x1)) \/ ((~ (real_lt x1 x0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) x1))).
Definition term310 (x0 : real) := and (real_lt (real_of_num (NUMERAL 0)) x0).
Definition term42 (x0 : real) := ~ (real_lt (real_of_num (NUMERAL 0)) x0).
Definition term280 (x0 : nat) := (~ (real_lt (real_of_num (NUMERAL 0)) (real_of_num x0))) -> real_lt (real_of_num (NUMERAL 0)) (real_of_num x0).
Definition term191 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term220 (x0 : real) := (fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) (real_inv y0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) y0))) x0.
Definition term337 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := imp ((x2 = x0) /\ ((x3 = x1) /\ (real_lt x2 x3))).
Definition term56 (x0 : real) := @eq Prop ((exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0))) /\ (~ (real_lt (real_of_num (NUMERAL 0)) x0))).
Definition term55 (x0 : real) := @eq Prop ((exists y0 : nat, (fun y1 : nat => (~ (y1 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y1))) /\ (real_lt (real_inv (real_of_num y1)) x0))) y0) /\ (~ (real_lt (real_of_num (NUMERAL 0)) x0))).
Definition term68 (x0 : real) (x1 : real) (x2 : real) := (~ ((real_lt x1 x0) /\ (real_lt x0 x2))) \/ (real_lt x1 x2).
Definition term106 (x0 : real) (x1 : real) := and (real_lt x0 x1).
Definition term317 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (real_lt x0 x1) \/ ((~ (x3 = x1)) \/ (~ (real_lt x2 x3))).
Definition term229 := @eq Prop (forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) (real_inv y0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) y0))) /\ ((~ (real_lt (real_of_num (NUMERAL 0)) (real_inv y0))) \/ (real_lt (real_of_num (NUMERAL 0)) y0))).
Definition term228 := @eq Prop (forall y0 : real, ((fun y1 : real => (real_lt (real_of_num (NUMERAL 0)) (real_inv y1)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) y1))) y0) /\ ((fun y1 : real => (~ (real_lt (real_of_num (NUMERAL 0)) (real_inv y1))) \/ (real_lt (real_of_num (NUMERAL 0)) y1)) y0)).
Definition term85 (x0 : nat) := ~ (real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num x0))).
Definition term321 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (real_lt x0 x1) \/ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (real_lt x2 x3)))).
Definition term91 (x0 : real) (x1 : real) (x2 : real) := (real_lt x0 x2) \/ (~ (real_lt x1 x2)).
Definition term340 (x0 : nat) (x1 : real) := ((real_inv (real_of_num x0)) = (real_inv (real_of_num x0))) /\ (((real_inv (real_inv x1)) = x1) /\ (real_lt (real_inv (real_of_num x0)) (real_inv (real_inv x1)))).
Definition term277 (x0 : real) (x1 : nat) := (real_lt (real_of_num (NUMERAL 0)) (real_inv x0)) /\ (real_lt (real_inv x0) (real_of_num x1)).
Definition term40 (x0 : real) := exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0)).
Definition term249 := fun y0 : real => forall y1 : real, ((~ (real_lt (real_of_num (NUMERAL 0)) y0)) \/ (~ (real_lt y0 y1))) \/ (real_lt (real_inv y1) (real_inv y0)).
Definition term171 := fun y0 : real => forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1)) -> real_lt (real_inv y1) (real_inv y0).
Definition term144 := (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1)) -> real_lt (real_inv y1) (real_inv y0)) -> False.
Definition term22 := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> False.
Definition term264 (x0 : real) := ~ (~ (real_lt (real_of_num (NUMERAL 0)) x0)).
Definition term290 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (x2 = x0) -> (~ (x3 = x1)) \/ ((real_lt x0 x1) \/ (~ (real_lt x2 x3))).
Definition term110 (x0 : nat) := real_inv (real_of_num x0).
Definition term157 := (forall y0 : real, forall y1 : real, ~ ((real_lt y0 y1) /\ (real_lt y1 y0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) (real_inv y0)) = (real_lt (real_of_num (NUMERAL 0)) y0)) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1)) -> real_lt (real_inv y1) (real_inv y0)) -> False.
Definition term345 (x0 : real) := ((real_lt (real_of_num (NUMERAL 0)) x0) -> exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0))) /\ ((exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0))) -> real_lt (real_of_num (NUMERAL 0)) x0).
Definition term303 (x0 : real) (x1 : real) := (~ (real_lt x1 x0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) x1)).
Definition term266 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) -> real_lt (real_of_num (NUMERAL 0)) (real_inv x0).
Definition term224 (x0 : real) := (fun y0 : real => (~ (real_lt (real_of_num (NUMERAL 0)) (real_inv y0))) \/ (real_lt (real_of_num (NUMERAL 0)) y0)) x0.
Definition term318 (x0 : real) (x1 : real) := ~ (x0 = x1).
Definition term320 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x2 = x0)) \/ ((real_lt x0 x1) \/ ((~ (x3 = x1)) \/ (~ (real_lt x2 x3)))).
Definition term130 (x0 : real) := imp (forall y0 : nat, (real_lt (real_inv x0) (real_of_num y0)) -> (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0))).
Definition term129 (x0 : real) := imp (forall y0 : nat, ((fun y1 : nat => real_lt (real_inv x0) (real_of_num y1)) y0) -> (fun y1 : nat => (~ (y1 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y1))) /\ (real_lt (real_inv (real_of_num y1)) x0))) y0).
Definition term131 (x0 : real) := fun y0 : nat => (fun y1 : nat => real_lt (real_inv x0) (real_of_num y1)) y0.
Definition term145 := ~ (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1)) -> real_lt (real_inv y1) (real_inv y0)).
Definition term23 := ~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2).
Definition term237 := forall y0 : real, (~ (real_lt (real_of_num (NUMERAL 0)) (real_inv y0))) \/ (real_lt (real_of_num (NUMERAL 0)) y0).
Definition term177 := forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) (real_inv y0)) = (real_lt (real_of_num (NUMERAL 0)) y0).
Definition term192 (x0 : real) (x1 : nat) := and (real_lt (real_inv x0) (real_of_num x1)).
Definition term109 (x0 : nat) (x1 : real) := ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num x0))) /\ (real_lt (real_inv (real_of_num x0)) x1)) -> real_lt (real_of_num (NUMERAL 0)) x1.
Definition term88 (x0 : nat) (x1 : real) := (~ (real_lt (real_inv (real_of_num x0)) x1)) -> real_lt (real_inv (real_of_num x0)) x1.
Definition term82 (x0 : real) (x1 : real) := ~ (real_lt x0 x1).
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term289 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x3 = x1)) \/ ((real_lt x0 x1) \/ (~ (real_lt x2 x3))).
Definition term322 (x0 : real) (x1 : real) (x2 : real) := (~ (x2 = x0)) \/ (~ (real_lt x1 x2)).
Definition term162 (x0 : real) := imp (real_lt (real_of_num (NUMERAL 0)) x0).
Definition term285 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((real_lt x2 x3) = (real_lt x0 x1)) -> (real_lt x0 x1) \/ (~ (real_lt x2 x3)).
Definition term186 (x0 : nat) := or (~ (~ (x0 = (NUMERAL 0)))).
Definition term324 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := @eq Prop ((real_lt x0 x1) \/ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (real_lt x2 x3))))).
Definition term247 (x0 : real) := fun y0 : real => ((~ (real_lt (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_lt x0 y0))) \/ (real_lt (real_inv y0) (real_inv x0)).
Definition term80 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((~ (real_lt x1 x0)) \/ (~ (real_lt x0 y0))) \/ (real_lt x1 y0)) x2.
Definition term244 (x0 : real) (x1 : real) := (~ ((real_lt (real_of_num (NUMERAL 0)) x1) /\ (real_lt x1 x0))) \/ (real_lt (real_inv x0) (real_inv x1)).
Definition term50 (x0 : real) := exists y0 : nat, ((fun y1 : nat => (~ (y1 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y1))) /\ (real_lt (real_inv (real_of_num y1)) x0))) y0) /\ (~ (real_lt (real_of_num (NUMERAL 0)) x0)).
Definition term258 (x0 : real) := real_lt (real_inv x0) (real_of_num (NUMERAL 0)).
Definition term263 (x0 : real) := (~ (~ (real_lt (real_of_num (NUMERAL 0)) x0))) -> real_lt (real_of_num (NUMERAL 0)) (real_inv x0).
Definition term283 (x0 : nat) := (real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num x0))) -> False.
Definition term92 (x0 : real) (x1 : real) := or (~ (real_lt x0 x1)).
Definition term187 (x0 : nat) := or (x0 = (NUMERAL 0)).
Definition term222 (x0 : real) := and ((fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) (real_inv y0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) y0))) x0).
Definition term172 (x0 : real) := real_inv (real_inv x0).
Definition term271 (x0 : real) (x1 : real) := ((real_lt x1 x0) /\ (real_lt x0 x1)) -> False.
Definition term99 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term170 (x0 : real) := forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 y0)) -> real_lt (real_inv y0) (real_inv x0).
Definition term238 := (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) (real_inv y0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) y0))) /\ (forall y0 : real, (~ (real_lt (real_of_num (NUMERAL 0)) (real_inv y0))) \/ (real_lt (real_of_num (NUMERAL 0)) y0)).
Definition term276 (x0 : real) (x1 : nat) := ~ (real_lt (real_inv x0) (real_of_num x1)).
Definition term59 (x0 : nat) (x1 : real) := ((fun y0 : nat => (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x1))) x0) /\ (~ (real_lt (real_of_num (NUMERAL 0)) x1)).
Definition term46 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term253 (x0 : real) := (fun y0 : real => (real_inv (real_inv y0)) = y0) x0.
Definition term274 (x0 : real) := ((real_lt (real_inv x0) (real_of_num (NUMERAL 0))) /\ (real_lt (real_of_num (NUMERAL 0)) (real_inv x0))) -> False.
Definition term226 (x0 : real) := ((fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) (real_inv y0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) y0))) x0) /\ ((fun y0 : real => (~ (real_lt (real_of_num (NUMERAL 0)) (real_inv y0))) \/ (real_lt (real_of_num (NUMERAL 0)) y0)) x0).
Definition term206 (x0 : real) := forall y0 : real, (~ (real_lt x0 y0)) \/ (~ (real_lt y0 x0)).
Definition term306 (x0 : real) (x1 : real) := (~ ((~ (real_lt (real_of_num (NUMERAL 0)) x1)) \/ (~ (real_lt x1 x0)))) -> real_lt (real_inv x0) (real_inv x1).
Definition term71 (x0 : real) (x1 : real) := fun y0 : real => ((~ (real_lt x1 x0)) \/ (~ (real_lt x0 y0))) \/ (real_lt x1 y0).
Definition term149 := (forall y0 : real, (real_inv (real_inv y0)) = y0) -> ~ (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1)) -> real_lt (real_inv y1) (real_inv y0)).
Definition term230 := fun y0 : real => (fun y1 : real => (real_lt (real_of_num (NUMERAL 0)) (real_inv y1)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) y1))) y0.
Definition term70 (x0 : real) (x1 : real) (x2 : real) := (real_lt x0 x1) /\ (real_lt x1 x2).
Definition term28 := fun y0 : real => (~ ((exists y1 : nat, (~ (y1 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y1))) /\ (real_lt (real_inv (real_of_num y1)) y0))) -> real_lt (real_of_num (NUMERAL 0)) y0)) -> ~ (forall y1 : real, forall y2 : real, forall y3 : real, ((real_lt y1 y2) /\ (real_lt y2 y3)) -> real_lt y1 y3).
Definition term73 (x0 : real) := fun y0 : real => forall y1 : real, ((~ (real_lt x0 y0)) \/ (~ (real_lt y0 y1))) \/ (real_lt x0 y1).
Definition term34 (x0 : real) := fun y0 : real => forall y1 : real, ((real_lt x0 y0) /\ (real_lt y0 y1)) -> real_lt x0 y1.
Definition term108 (x0 : real) (x1 : real) (x2 : real) := imp ((real_lt x0 x1) /\ (real_lt x1 x2)).
Definition term260 (x0 : real) (x1 : nat) := @eq Prop (real_lt (real_inv x0) (real_of_num x1)).
Definition term214 (x0 : real -> Prop) (x1 : real -> Prop) := forall y0 : real, (x0 y0) /\ (x1 y0).
Definition term221 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) (real_inv x0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) x0)).
Definition term219 := fun y0 : real => (~ (real_lt (real_of_num (NUMERAL 0)) (real_inv y0))) \/ (real_lt (real_of_num (NUMERAL 0)) y0).
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term148 := (forall y0 : real, (real_inv (real_inv y0)) = y0) -> (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1)) -> real_lt (real_inv y1) (real_inv y0)) -> False.
Definition term254 (x0 : real) := (fun y0 : real => forall y1 : real, ((~ (real_lt (real_of_num (NUMERAL 0)) y0)) \/ (~ (real_lt y0 y1))) \/ (real_lt (real_inv y1) (real_inv y0))) x0.
Definition term251 (x0 : real) := (fun y0 : real => forall y1 : real, (~ (real_lt y0 y1)) \/ (~ (real_lt y1 y0))) x0.
Definition term121 (x0 : real) (x1 : nat) := imp ((fun y0 : nat => real_lt (real_inv x0) (real_of_num y0)) x1).
Definition term77 (x0 : nat) (x1 : real) := (real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num x0))) /\ (real_lt (real_inv (real_of_num x0)) x1).
Definition term327 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ~ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (real_lt x2 x3)))).
Definition term142 (x0 : real) := (((real_lt (real_of_num (NUMERAL 0)) x0) -> (~ (forall y0 : nat, (real_lt (real_inv x0) (real_of_num y0)) -> (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0)))) -> (forall y0 : real, forall y1 : real, ~ ((real_lt y0 y1) /\ (real_lt y1 y0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) (real_inv y0)) = (real_lt (real_of_num (NUMERAL 0)) y0)) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1)) -> real_lt (real_inv y1) (real_inv y0)) -> False) -> (real_lt (real_of_num (NUMERAL 0)) x0) -> (~ (forall y0 : nat, (real_lt (real_inv x0) (real_of_num y0)) -> (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0)))) -> (forall y0 : real, forall y1 : real, ~ ((real_lt y0 y1) /\ (real_lt y1 y0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) (real_inv y0)) = (real_lt (real_of_num (NUMERAL 0)) y0)) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1)) -> real_lt (real_inv y1) (real_inv y0)) -> False) -> (real_lt (real_of_num (NUMERAL 0)) x0) -> (~ (forall y0 : nat, (real_lt (real_inv x0) (real_of_num y0)) -> (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0)))) -> (forall y0 : real, forall y1 : real, ~ ((real_lt y0 y1) /\ (real_lt y1 y0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) (real_inv y0)) = (real_lt (real_of_num (NUMERAL 0)) y0)) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1)) -> real_lt (real_inv y1) (real_inv y0)) -> False.
Definition term243 (x0 : real) (x1 : real) := or ((~ (real_lt (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_lt x0 x1))).
Definition term67 (x0 : real) (x1 : real) (x2 : real) := or ((~ (real_lt x0 x1)) \/ (~ (real_lt x1 x2))).
Definition term154 := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) (real_inv y0)) = (real_lt (real_of_num (NUMERAL 0)) y0)) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1)) -> real_lt (real_inv y1) (real_inv y0)) -> False.
Definition term296 (x0 : real) (x1 : real) := (~ (real_lt x1 x0)) \/ ((~ (real_lt (real_of_num (NUMERAL 0)) x1)) \/ (real_lt (real_inv x0) (real_inv x1))).
Definition term48 (x0 : nat -> Prop) (x1 : Prop) := exists y0 : nat, (x0 y0) /\ x1.
Definition term203 (x0 : real) := exists y0 : nat, (real_lt (real_inv x0) (real_of_num y0)) /\ ((y0 = (NUMERAL 0)) \/ ((~ (real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0)))) \/ (~ (real_lt (real_inv (real_of_num y0)) x0)))).
Definition term138 (x0 : real) := (~ (forall y0 : nat, (real_lt (real_inv x0) (real_of_num y0)) -> (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0)))) -> False.
Definition term236 := forall y0 : real, (fun y1 : real => (~ (real_lt (real_of_num (NUMERAL 0)) (real_inv y1))) \/ (real_lt (real_of_num (NUMERAL 0)) y1)) y0.
Definition term231 := forall y0 : real, (fun y1 : real => (real_lt (real_of_num (NUMERAL 0)) (real_inv y1)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) y1))) y0.
Definition term143 (x0 : real) := (((real_lt (real_of_num (NUMERAL 0)) x0) -> (~ (forall y0 : nat, (real_lt (real_inv x0) (real_of_num y0)) -> (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0)))) -> (forall y0 : real, forall y1 : real, ~ ((real_lt y0 y1) /\ (real_lt y1 y0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) (real_inv y0)) = (real_lt (real_of_num (NUMERAL 0)) y0)) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1)) -> real_lt (real_inv y1) (real_inv y0)) -> False) -> (real_lt (real_of_num (NUMERAL 0)) x0) -> (~ (forall y0 : nat, (real_lt (real_inv x0) (real_of_num y0)) -> (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0)))) -> (forall y0 : real, forall y1 : real, ~ ((real_lt y0 y1) /\ (real_lt y1 y0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) (real_inv y0)) = (real_lt (real_of_num (NUMERAL 0)) y0)) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1)) -> real_lt (real_inv y1) (real_inv y0)) -> False) -> ((real_lt (real_of_num (NUMERAL 0)) x0) -> (~ (forall y0 : nat, (real_lt (real_inv x0) (real_of_num y0)) -> (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0)))) -> (forall y0 : real, forall y1 : real, ~ ((real_lt y0 y1) /\ (real_lt y1 y0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) (real_inv y0)) = (real_lt (real_of_num (NUMERAL 0)) y0)) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1)) -> real_lt (real_inv y1) (real_inv y0)) -> False) -> (real_lt (real_of_num (NUMERAL 0)) x0) -> (~ (forall y0 : nat, (real_lt (real_inv x0) (real_of_num y0)) -> (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0)))) -> (forall y0 : real, forall y1 : real, ~ ((real_lt y0 y1) /\ (real_lt y1 y0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) (real_inv y0)) = (real_lt (real_of_num (NUMERAL 0)) y0)) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1)) -> real_lt (real_inv y1) (real_inv y0)) -> False.
Definition term178 (x0 : real) (x1 : real) := ~ ((real_lt x1 x0) /\ (real_lt x0 x1)).
Definition term15 (x0 : real) := (exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0))) -> real_lt (real_of_num (NUMERAL 0)) x0.
Definition term262 (x0 : real) := ~ (real_lt (real_inv x0) (real_of_num (NUMERAL 0))).
Definition term294 (x0 : real) := (~ ((real_inv (real_inv x0)) = x0)) -> (real_inv (real_inv x0)) = x0.
Definition term223 (x0 : real) := and ((real_lt (real_of_num (NUMERAL 0)) (real_inv x0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) x0))).
Definition term132 (x0 : real) := exists y0 : nat, (fun y1 : nat => real_lt (real_inv x0) (real_of_num y1)) y0.
Definition term53 (x0 : real) := exists y0 : nat, (fun y1 : nat => (~ (y1 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y1))) /\ (real_lt (real_inv (real_of_num y1)) x0))) y0.
Definition term81 (x0 : real) (x1 : real) (x2 : real) := (~ (real_lt x1 x0)) \/ ((~ (real_lt x0 x2)) \/ (real_lt x1 x2)).
Definition term309 (x0 : real) := and (~ (~ (real_lt (real_of_num (NUMERAL 0)) x0))).
Definition term1 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term344 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) -> exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0)).
Definition term79 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((~ (real_lt x0 y0)) \/ (~ (real_lt y0 y1))) \/ (real_lt x0 y1)) x1.
Definition term330 (x0 : real) (x1 : real) := and (~ (~ (x0 = x1))).
Definition term105 (x0 : real) (x1 : real) := and (~ (~ (real_lt x0 x1))).
Definition term241 (x0 : real) (x1 : real) := real_lt (real_inv x0) (real_inv x1).
Definition term297 (x0 : real) (x1 : real) := (~ (real_lt (real_of_num (NUMERAL 0)) x1)) \/ (real_lt (real_inv x0) (real_inv x1)).
Definition term124 (x0 : nat) (x1 : real) := (real_lt (real_inv x1) (real_of_num x0)) -> (~ (x0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num x0))) /\ (real_lt (real_inv (real_of_num x0)) x1)).
Definition term9 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) -> exists y0 : a0, x1 y0.
Definition term252 (x0 : real) (x1 : real) := (fun y0 : real => (~ (real_lt x0 y0)) \/ (~ (real_lt y0 x0))) x1.
Definition term257 (x0 : real) := (fun y0 : nat => real_lt (real_inv x0) (real_of_num y0)) (NUMERAL 0).
Definition term69 (x0 : real) (x1 : real) (x2 : real) := ((~ (real_lt x1 x0)) \/ (~ (real_lt x0 x2))) \/ (real_lt x1 x2).
Definition term284 (x0 : Prop) (x1 : Prop) := (x1 = x0) -> x0 \/ (~ x1).
Definition term65 (x0 : real) (x1 : real) (x2 : real) := (~ (real_lt x0 x1)) \/ (~ (real_lt x1 x2)).
Definition term147 := imp (forall y0 : real, (real_inv (real_inv y0)) = y0).
Definition term185 (x0 : nat) (x1 : real) := (~ (real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num x0)))) \/ (~ (real_lt (real_inv (real_of_num x0)) x1)).
Definition term37 (x0 : real) := real_lt (real_of_num (NUMERAL 0)) x0.
Definition term188 (x0 : nat) (x1 : real) := (~ (~ (x0 = (NUMERAL 0)))) \/ (~ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num x0))) /\ (real_lt (real_inv (real_of_num x0)) x1))).
Definition term256 (x0 : real) (x1 : real) := (~ (real_lt (real_of_num (NUMERAL 0)) x1)) \/ ((~ (real_lt x1 x0)) \/ (real_lt (real_inv x0) (real_inv x1))).
Definition term302 (x0 : real) (x1 : real) := @eq Prop ((real_lt (real_inv x0) (real_inv x1)) \/ ((~ (real_lt x1 x0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) x1)))).
Definition term205 (x0 : real) := fun y0 : real => (~ (real_lt x0 y0)) \/ (~ (real_lt y0 x0)).
Definition term152 := (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) (real_inv y0)) = (real_lt (real_of_num (NUMERAL 0)) y0)) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> ~ (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1)) -> real_lt (real_inv y1) (real_inv y0)).
Definition term47 (x0 : nat -> Prop) (x1 : Prop) := (exists y0 : nat, x0 y0) /\ x1.
Definition term298 (x0 : real) (x1 : real) := (real_lt (real_inv x0) (real_inv x1)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) x1)).
Definition term104 (x0 : real) (x1 : real) := ~ (~ (real_lt x0 x1)).
Definition term29 := forall y0 : real, (~ ((exists y1 : nat, (~ (y1 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y1))) /\ (real_lt (real_inv (real_of_num y1)) y0))) -> real_lt (real_of_num (NUMERAL 0)) y0)) -> (forall y1 : real, forall y2 : real, forall y3 : real, ((real_lt y1 y2) /\ (real_lt y2 y3)) -> real_lt y1 y3) -> False.
Definition term60 (x0 : nat) (x1 : real) := ((~ (x0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num x0))) /\ (real_lt (real_inv (real_of_num x0)) x1))) /\ (~ (real_lt (real_of_num (NUMERAL 0)) x1)).
Definition term75 := fun y0 : real => forall y1 : real, forall y2 : real, ((~ (real_lt y0 y1)) \/ (~ (real_lt y1 y2))) \/ (real_lt y0 y2).
Definition term36 := fun y0 : real => forall y1 : real, forall y2 : real, ((real_lt y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2.
Definition term19 (x0 : real) := ((~ ((exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0))) -> real_lt (real_of_num (NUMERAL 0)) x0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> False) -> (~ ((exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0))) -> real_lt (real_of_num (NUMERAL 0)) x0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> False.
Definition term305 (x0 : real) (x1 : real) := (real_lt (real_inv x1) (real_inv x0)) \/ ((~ (real_lt (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_lt x0 x1))).
Definition term343 (x0 : real) := (fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) y0) -> (~ (forall y1 : nat, (real_lt (real_inv y0) (real_of_num y1)) -> (~ (y1 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y1))) /\ (real_lt (real_inv (real_of_num y1)) y0)))) -> (forall y1 : real, forall y2 : real, ~ ((real_lt y1 y2) /\ (real_lt y2 y1))) -> (forall y1 : real, forall y2 : real, forall y3 : real, ((real_lt y1 y2) /\ (real_lt y2 y3)) -> real_lt y1 y3) -> (forall y1 : real, (real_lt (real_of_num (NUMERAL 0)) (real_inv y1)) = (real_lt (real_of_num (NUMERAL 0)) y1)) -> (forall y1 : real, (real_inv (real_inv y1)) = y1) -> (forall y1 : real, forall y2 : real, ((real_lt (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2)) -> real_lt (real_inv y2) (real_inv y1)) -> False) x0.
Definition term199 (x0 : real) (x1 : nat) := (fun y0 : nat => (real_lt (real_inv x0) (real_of_num y0)) -> (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0))) x1.
Definition term314 (x0 : nat) (x1 : real) := real_lt (real_inv (real_of_num x0)) (real_inv (real_inv x1)).
Definition term301 (x0 : real) (x1 : real) := @eq Prop ((~ (real_lt (real_of_num (NUMERAL 0)) x1)) \/ ((~ (real_lt x1 x0)) \/ (real_lt (real_inv x0) (real_inv x1)))).
Definition term43 (x0 : real) := and (exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0))).
Definition term204 (x0 : real) (x1 : real) := (~ (real_lt x1 x0)) \/ (~ (real_lt x0 x1)).
Definition term342 (x0 : nat) (x1 : real) := (real_lt (real_inv (real_of_num x0)) x1) -> False.
Definition term135 (x0 : real) := (exists y0 : nat, (fun y1 : nat => real_lt (real_inv x0) (real_of_num y1)) y0) -> exists y0 : nat, (fun y1 : nat => (~ (y1 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y1))) /\ (real_lt (real_inv (real_of_num y1)) x0))) y0.
Definition term7 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, (x0 y0) -> x1 y0) -> (exists y0 : a0, x0 y0) -> exists y0 : a0, x1 y0.
Definition term49 (x0 : real) := (exists y0 : nat, (fun y1 : nat => (~ (y1 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y1))) /\ (real_lt (real_inv (real_of_num y1)) x0))) y0) /\ (~ (real_lt (real_of_num (NUMERAL 0)) x0)).
Definition term326 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (real_lt x2 x3))).
Definition term190 (x0 : nat) (x1 : real) := ~ ((~ (x0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num x0))) /\ (real_lt (real_inv (real_of_num x0)) x1))).
Definition term273 (x0 : real) := (real_lt (real_inv x0) (real_of_num (NUMERAL 0))) /\ (real_lt (real_of_num (NUMERAL 0)) (real_inv x0)).
Definition term295 (x0 : real) := ~ ((real_inv (real_inv x0)) = x0).
Definition term332 (x0 : real) (x1 : real) (x2 : real) := ~ ((~ (x2 = x0)) \/ (~ (real_lt x1 x2))).
Definition term307 (x0 : real) (x1 : real) := ~ ((~ (real_lt (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_lt x0 x1))).
Definition term101 (x0 : real) (x1 : real) (x2 : real) := ~ ((~ (real_lt x0 x1)) \/ (~ (real_lt x1 x2))).
Definition term33 (x0 : real) (x1 : real) := forall y0 : real, ((real_lt x1 x0) /\ (real_lt x0 y0)) -> real_lt x1 y0.
Definition term84 (x0 : nat) := (~ (real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num x0)))) -> real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num x0)).
Definition term323 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := @eq Prop ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ ((real_lt x0 x1) \/ (~ (real_lt x2 x3))))).
Definition term198 (x0 : real) := exists y0 : nat, ~ ((fun y1 : nat => (real_lt (real_inv x0) (real_of_num y1)) -> (~ (y1 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y1))) /\ (real_lt (real_inv (real_of_num y1)) x0))) y0).
Definition term11 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((forall y0 : a0, (x0 y0) -> x1 y0) -> (exists y0 : a0, x0 y0) -> exists y0 : a0, x1 y0) -> (forall y0 : a0, (x0 y0) -> x1 y0) -> (exists y0 : a0, x0 y0) -> exists y0 : a0, x1 y0.
Definition term331 (x0 : real) (x1 : real) := and (x0 = x1).
Definition term52 (x0 : real) := fun y0 : nat => (fun y1 : nat => (~ (y1 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y1))) /\ (real_lt (real_inv (real_of_num y1)) x0))) y0.
Definition term288 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term328 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (~ (x2 = x0))) /\ (~ ((~ (x3 = x1)) \/ (~ (real_lt x2 x3)))).
Definition term227 := fun y0 : real => ((fun y1 : real => (real_lt (real_of_num (NUMERAL 0)) (real_inv y1)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) y1))) y0) /\ ((fun y1 : real => (~ (real_lt (real_of_num (NUMERAL 0)) (real_inv y1))) \/ (real_lt (real_of_num (NUMERAL 0)) y1)) y0).
Definition term235 := fun y0 : real => (fun y1 : real => (~ (real_lt (real_of_num (NUMERAL 0)) (real_inv y1))) \/ (real_lt (real_of_num (NUMERAL 0)) y1)) y0.
Definition term180 (x0 : real) := forall y0 : real, ~ ((real_lt x0 y0) /\ (real_lt y0 x0)).
Definition term115 (x0 : real) := (fun y0 : real => (~ ((exists y1 : nat, (~ (y1 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y1))) /\ (real_lt (real_inv (real_of_num y1)) y0))) -> real_lt (real_of_num (NUMERAL 0)) y0)) -> (forall y1 : real, forall y2 : real, forall y3 : real, ((real_lt y1 y2) /\ (real_lt y2 y3)) -> real_lt y1 y3) -> False) x0.
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term150 := imp (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) (real_inv y0)) = (real_lt (real_of_num (NUMERAL 0)) y0)).
Definition term175 (x0 : real) := real_lt (real_of_num (NUMERAL 0)) (real_inv x0).
Definition term26 (x0 : real) := (~ ((exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0))) -> real_lt (real_of_num (NUMERAL 0)) x0)) -> ~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2).
Definition term312 (x0 : real) (x1 : real) := imp ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 x1)).
Definition term287 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (x3 = x1) -> (real_lt x0 x1) \/ (~ (real_lt x2 x3)).
Definition term98 (x0 : real) (x1 : real) (x2 : real) := (~ ((~ (real_lt x1 x0)) \/ (~ (real_lt x0 x2)))) -> real_lt x1 x2.
Definition term215 (x0 : real -> Prop) (x1 : real -> Prop) := (forall y0 : real, x0 y0) /\ (forall y0 : real, x1 y0).
Definition term255 (x0 : real) (x1 : real) := (fun y0 : real => ((~ (real_lt (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_lt x0 y0))) \/ (real_lt (real_inv y0) (real_inv x0))) x1.
Definition term30 := forall y0 : real, (~ ((exists y1 : nat, (~ (y1 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y1))) /\ (real_lt (real_inv (real_of_num y1)) y0))) -> real_lt (real_of_num (NUMERAL 0)) y0)) -> ~ (forall y1 : real, forall y2 : real, forall y3 : real, ((real_lt y1 y2) /\ (real_lt y2 y3)) -> real_lt y1 y3).
Definition term123 (x0 : real) (x1 : nat) := ((fun y0 : nat => real_lt (real_inv x0) (real_of_num y0)) x1) -> (fun y0 : nat => (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0))) x1.
Definition term281 (x0 : nat) := ~ (real_lt (real_of_num (NUMERAL 0)) (real_of_num x0)).
Definition term165 := fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) y0) -> (~ (forall y1 : nat, (real_lt (real_inv y0) (real_of_num y1)) -> (~ (y1 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y1))) /\ (real_lt (real_inv (real_of_num y1)) y0)))) -> (forall y1 : real, forall y2 : real, ~ ((real_lt y1 y2) /\ (real_lt y2 y1))) -> (forall y1 : real, forall y2 : real, forall y3 : real, ((real_lt y1 y2) /\ (real_lt y2 y3)) -> real_lt y1 y3) -> (forall y1 : real, (real_lt (real_of_num (NUMERAL 0)) (real_inv y1)) = (real_lt (real_of_num (NUMERAL 0)) y1)) -> (forall y1 : real, (real_inv (real_inv y1)) = y1) -> ~ (forall y1 : real, forall y2 : real, ((real_lt (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2)) -> real_lt (real_inv y2) (real_inv y1)).
Definition term164 := fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) y0) -> (~ (forall y1 : nat, (real_lt (real_inv y0) (real_of_num y1)) -> (~ (y1 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y1))) /\ (real_lt (real_inv (real_of_num y1)) y0)))) -> (forall y1 : real, forall y2 : real, ~ ((real_lt y1 y2) /\ (real_lt y2 y1))) -> (forall y1 : real, forall y2 : real, forall y3 : real, ((real_lt y1 y2) /\ (real_lt y2 y3)) -> real_lt y1 y3) -> (forall y1 : real, (real_lt (real_of_num (NUMERAL 0)) (real_inv y1)) = (real_lt (real_of_num (NUMERAL 0)) y1)) -> (forall y1 : real, (real_inv (real_inv y1)) = y1) -> (forall y1 : real, forall y2 : real, ((real_lt (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2)) -> real_lt (real_inv y2) (real_inv y1)) -> False.
Definition term335 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (x2 = x0) /\ ((x3 = x1) /\ (real_lt x2 x3)).
Definition term212 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term8 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) -> x1 y0.
Definition term16 (x0 : real) := (~ ((exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0))) -> real_lt (real_of_num (NUMERAL 0)) x0)) -> False.
Definition term128 (x0 : real) := forall y0 : nat, (real_lt (real_inv x0) (real_of_num y0)) -> (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0)).
Definition term341 (x0 : nat) (x1 : real) := (((real_inv (real_of_num x0)) = (real_inv (real_of_num x0))) /\ (((real_inv (real_inv x1)) = x1) /\ (real_lt (real_inv (real_of_num x0)) (real_inv (real_inv x1))))) -> real_lt (real_inv (real_of_num x0)) x1.
Definition term57 (x0 : real) (x1 : nat) := and ((fun y0 : nat => (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0))) x1).
Definition term201 (x0 : real) := fun y0 : nat => ~ ((fun y1 : nat => (real_lt (real_inv x0) (real_of_num y1)) -> (~ (y1 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y1))) /\ (real_lt (real_inv (real_of_num y1)) x0))) y0).
Definition term200 (x0 : real) (x1 : nat) := ~ ((fun y0 : nat => (real_lt (real_inv x0) (real_of_num y0)) -> (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0))) x1).
Definition term245 (x0 : real) (x1 : real) := ((~ (real_lt (real_of_num (NUMERAL 0)) x1)) \/ (~ (real_lt x1 x0))) \/ (real_lt (real_inv x0) (real_inv x1)).
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term299 (x0 : real) (x1 : real) := (~ (real_lt x1 x0)) \/ ((real_lt (real_inv x0) (real_inv x1)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) x1))).
Definition term118 (x0 : real) := fun y0 : nat => real_lt (real_inv x0) (real_of_num y0).
Definition term93 (x0 : real) (x1 : real) (x2 : real) := (~ (real_lt x0 x1)) \/ ((real_lt x0 x2) \/ (~ (real_lt x1 x2))).
Definition term122 (x0 : real) (x1 : nat) := imp (real_lt (real_inv x0) (real_of_num x1)).
Definition term45 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term286 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (real_lt x0 x1) \/ (~ (real_lt x2 x3)).
Definition term44 (x0 : real) := (exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0))) /\ (~ (real_lt (real_of_num (NUMERAL 0)) x0)).
Definition term183 (x0 : nat) := ~ (~ (x0 = (NUMERAL 0))).
Definition term304 (x0 : real) (x1 : real) := or (real_lt (real_inv x0) (real_inv x1)).
Definition term329 (x0 : real) (x1 : real) := ~ (~ (x0 = x1)).
Definition term21 (x0 : real) := (((~ ((exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0))) -> real_lt (real_of_num (NUMERAL 0)) x0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> False) -> (~ ((exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0))) -> real_lt (real_of_num (NUMERAL 0)) x0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> False) -> ((~ ((exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0))) -> real_lt (real_of_num (NUMERAL 0)) x0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> False) -> (~ ((exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0))) -> real_lt (real_of_num (NUMERAL 0)) x0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> False.
Definition term319 (x0 : real) (x1 : real) := or (~ (x0 = x1)).
Definition term209 (x0 : real) := ((real_lt (real_of_num (NUMERAL 0)) (real_inv x0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) x0))) /\ ((~ (real_lt (real_of_num (NUMERAL 0)) (real_inv x0))) \/ (real_lt (real_of_num (NUMERAL 0)) x0)).
Definition term62 (x0 : real) := fun y0 : nat => ((~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0))) /\ (~ (real_lt (real_of_num (NUMERAL 0)) x0)).
Definition term64 (x0 : real) (x1 : real) (x2 : real) := ~ ((real_lt x0 x1) /\ (real_lt x1 x2)).
Definition term31 (x0 : real) (x1 : real) (x2 : real) := ((real_lt x1 x0) /\ (real_lt x0 x2)) -> real_lt x1 x2.
Definition term78 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((~ (real_lt y0 y1)) \/ (~ (real_lt y1 y2))) \/ (real_lt y0 y2)) x0.
Definition term151 := (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) (real_inv y0)) = (real_lt (real_of_num (NUMERAL 0)) y0)) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1)) -> real_lt (real_inv y1) (real_inv y0)) -> False.
Definition term291 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ ((real_lt x0 x1) \/ (~ (real_lt x2 x3)))).
Definition term137 (x0 : real) := (forall y0 : nat, (real_lt (real_inv x0) (real_of_num y0)) -> (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0))) -> (exists y0 : nat, real_lt (real_inv x0) (real_of_num y0)) -> exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0)).
Definition term117 (x0 : real) := (forall y0 : nat, ((fun y1 : nat => real_lt (real_inv x0) (real_of_num y1)) y0) -> (fun y1 : nat => (~ (y1 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y1))) /\ (real_lt (real_inv (real_of_num y1)) x0))) y0) -> (exists y0 : nat, (fun y1 : nat => real_lt (real_inv x0) (real_of_num y1)) y0) -> exists y0 : nat, (fun y1 : nat => (~ (y1 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y1))) /\ (real_lt (real_inv (real_of_num y1)) x0))) y0.
Definition term116 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, (x0 y0) -> x1 y0) -> (exists y0 : nat, x0 y0) -> exists y0 : nat, x1 y0.
Definition term197 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term268 (x0 : real) := ~ (real_lt (real_of_num (NUMERAL 0)) (real_inv x0)).
Definition term308 (x0 : real) (x1 : real) := (~ (~ (real_lt (real_of_num (NUMERAL 0)) x0))) /\ (~ (~ (real_lt x0 x1))).
Definition term232 := forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) (real_inv y0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) y0)).
Definition term216 := forall y0 : real, ((fun y1 : real => (real_lt (real_of_num (NUMERAL 0)) (real_inv y1)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) y1))) y0) /\ ((fun y1 : real => (~ (real_lt (real_of_num (NUMERAL 0)) (real_inv y1))) \/ (real_lt (real_of_num (NUMERAL 0)) y1)) y0).
Definition term113 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) -> False.
Definition term292 (x0 : nat) := (~ ((real_inv (real_of_num x0)) = (real_inv (real_of_num x0)))) -> (real_inv (real_of_num x0)) = (real_inv (real_of_num x0)).
Definition term83 (x0 : nat) := real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num x0)).
Definition term282 (x0 : nat) := (real_lt (real_of_num (NUMERAL 0)) (real_of_num x0)) -> real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num x0)).
Definition term184 (x0 : nat) (x1 : real) := ~ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num x0))) /\ (real_lt (real_inv (real_of_num x0)) x1)).
Definition term338 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((x0 = x2) /\ ((x1 = x3) /\ (real_lt x0 x1))) -> real_lt x2 x3.
Definition term159 (x0 : real) := imp (~ (forall y0 : nat, (real_lt (real_inv x0) (real_of_num y0)) -> (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0)))).
Definition term265 (x0 : real) := imp (~ (~ (real_lt (real_of_num (NUMERAL 0)) x0))).
Definition term207 := fun y0 : real => forall y1 : real, (~ (real_lt y0 y1)) \/ (~ (real_lt y1 y0)).
Definition term248 (x0 : real) := forall y0 : real, ((~ (real_lt (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_lt x0 y0))) \/ (real_lt (real_inv y0) (real_inv x0)).
Definition term63 (x0 : real) := exists y0 : nat, ((~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0))) /\ (~ (real_lt (real_of_num (NUMERAL 0)) x0)).
Definition term10 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((forall y0 : a0, (x0 y0) -> x1 y0) -> (exists y0 : a0, x0 y0) -> exists y0 : a0, x1 y0) -> (exists y0 : a0, x0 y0) -> exists y0 : a0, x1 y0.
Definition term72 (x0 : real) (x1 : real) := forall y0 : real, ((~ (real_lt x1 x0)) \/ (~ (real_lt x0 y0))) \/ (real_lt x1 y0).
Definition term17 (x0 : real) := ~ ((exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num y0))) /\ (real_lt (real_inv (real_of_num y0)) x0))) -> real_lt (real_of_num (NUMERAL 0)) x0).
Definition term210 := fun y0 : real => ((real_lt (real_of_num (NUMERAL 0)) (real_inv y0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) y0))) /\ ((~ (real_lt (real_of_num (NUMERAL 0)) (real_inv y0))) \/ (real_lt (real_of_num (NUMERAL 0)) y0)).
Definition term12 (x0 : real) := (fun y0 : real => exists y1 : nat, real_lt y0 (real_of_num y1)) (real_inv x0).