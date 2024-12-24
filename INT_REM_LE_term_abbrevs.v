Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term160 (x0 : int) (x1 : int) := (fun y0 : int => ~ (int_le (rem x0 y0) x1)) (int_of_num (NUMERAL 0)).
Definition term175 (x0 : int) := ((int_of_num (NUMERAL 0)) = (int_of_num (NUMERAL 0))) -> int_le (rem x0 (int_of_num (NUMERAL 0))) x0.
Definition term198 (x0 : int) (x1 : int) := ((int_le (rem x0 (int_of_num (NUMERAL 0))) x0) /\ (int_le x0 x1)) -> int_le (rem x0 (int_of_num (NUMERAL 0))) x1.
Definition term147 := fun y0 : int => forall y1 : int, ((int_le (rem y0 y1) y0) \/ (~ (y1 = (int_of_num (NUMERAL 0))))) /\ ((int_le (rem y0 y1) y0) \/ (~ (int_le (int_of_num (NUMERAL 0)) y0))).
Definition term125 := fun y0 : int => forall y1 : int, (~ (int_le (rem y0 y1) y0)) \/ ((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0)).
Definition term124 := fun y0 : int => forall y1 : int, (int_le (rem y0 y1) y0) \/ ((~ (y1 = (int_of_num (NUMERAL 0)))) /\ (~ (int_le (int_of_num (NUMERAL 0)) y0))).
Definition term94 := fun y0 : int => forall y1 : int, ((int_le (rem y0 y1) y0) \/ ((~ (y1 = (int_of_num (NUMERAL 0)))) /\ (~ (int_le (int_of_num (NUMERAL 0)) y0)))) /\ ((~ (int_le (rem y0 y1) y0)) \/ ((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0))).
Definition term27 := fun y0 : int => forall y1 : int, (int_le (rem y0 y1) y0) = ((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0)).
Definition term181 (x0 : int) (x1 : int) (x2 : int) := (int_le x0 x2) \/ (~ (int_le x1 x2)).
Definition term150 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, ((~ (int_le x0 y0)) \/ (~ (int_le y0 y1))) \/ (int_le x0 y1)) x1.
Definition term56 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, (((y0 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x0)) /\ (int_le x0 y1)) -> int_le (rem x0 y0) y1) x1.
Definition term46 (x0 : int -> Prop) := exists y0 : int, ~ (x0 y0).
Definition term45 (x0 : int -> Prop) := ~ (all x0).
Definition term75 (x0 : int) (x1 : int) := forall y0 : int, ((~ (int_le x1 x0)) \/ (~ (int_le x0 y0))) \/ (int_le x1 y0).
Definition term203 := (~ False) -> False.
Definition term78 := fun y0 : int => forall y1 : int, forall y2 : int, ((~ (int_le y0 y1)) \/ (~ (int_le y1 y2))) \/ (int_le y0 y2).
Definition term40 := fun y0 : int => forall y1 : int, forall y2 : int, (((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0)) /\ (int_le y0 y2)) -> int_le (rem y0 y1) y2.
Definition term33 := fun y0 : int => forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2.
Definition term69 (x0 : int) (x1 : int) (x2 : int) := or (~ ((int_le x0 x1) /\ (int_le x1 x2))).
Definition term41 (x0 : int) (x1 : int) (x2 : int) := ~ ((((x1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x0)) /\ (int_le x0 x2)) -> int_le (rem x0 x1) x2).
Definition term208 (x0 : int) := imp (int_le (int_of_num (NUMERAL 0)) x0).
Definition term163 (x0 : int) (x1 : int) (x2 : int) := @eq Prop (~ (int_le (rem x0 x1) x2)).
Definition term104 (x0 : int) (x1 : int) := (fun y0 : int => (int_le (rem x0 y0) x0) \/ ((~ (y0 = (int_of_num (NUMERAL 0)))) /\ (~ (int_le (int_of_num (NUMERAL 0)) x0)))) x1.
Definition term170 (x0 : Prop) := ~ (~ x0).
Definition term180 (x0 : int) (x1 : int) (x2 : int) := (~ (int_le x0 x2)) \/ (int_le x1 x2).
Definition term106 (x0 : int) (x1 : int) := (fun y0 : int => (~ (int_le (rem x0 y0) x0)) \/ ((y0 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x0))) x1.
Definition term211 (x0 : int) (x1 : int) := ~ (int_le (rem x1 x0) x1).
Definition term82 := int_of_num (NUMERAL 0).
Definition term90 (x0 : int) (x1 : int) := ((int_le (rem x1 x0) x1) \/ (~ ((x0 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x1)))) /\ ((~ (int_le (rem x1 x0) x1)) \/ ((x0 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x1))).
Definition term191 (x0 : int) (x1 : int) (x2 : int) := (~ (~ (int_le x0 x1))) /\ (~ (~ (int_le x1 x2))).
Definition term81 (x0 : int) (x1 : int) := (~ (x0 = (int_of_num (NUMERAL 0)))) /\ (~ (int_le (int_of_num (NUMERAL 0)) x1)).
Definition term205 (x0 : int) (x1 : int) := (~ (~ (int_le (int_of_num (NUMERAL 0)) x1))) -> int_le (rem x1 x0) x1.
Definition term152 (x0 : int) := (fun y0 : int => forall y1 : int, ((int_le (rem y0 y1) y0) \/ (~ (y1 = (int_of_num (NUMERAL 0))))) /\ ((int_le (rem y0 y1) y0) \/ (~ (int_le (int_of_num (NUMERAL 0)) y0)))) x0.
Definition term128 (x0 : int) := (fun y0 : int => forall y1 : int, (~ (int_le (rem y0 y1) y0)) \/ ((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0))) x0.
Definition term126 (x0 : int) := (fun y0 : int => forall y1 : int, (int_le (rem y0 y1) y0) \/ ((~ (y1 = (int_of_num (NUMERAL 0)))) /\ (~ (int_le (int_of_num (NUMERAL 0)) y0)))) x0.
Definition term93 (x0 : int) := forall y0 : int, ((int_le (rem x0 y0) x0) \/ ((~ (y0 = (int_of_num (NUMERAL 0)))) /\ (~ (int_le (int_of_num (NUMERAL 0)) x0)))) /\ ((~ (int_le (rem x0 y0) x0)) \/ ((y0 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x0))).
Definition term3 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term201 (x0 : int) (x1 : int) := (~ (int_le (rem x0 (int_of_num (NUMERAL 0))) x1)) -> int_le (rem x0 (int_of_num (NUMERAL 0))) x1.
Definition term7 (x0 : Prop) := (~ x0) -> False.
Definition term113 (x0 : int) := forall y0 : int, (int_le (rem x0 y0) x0) \/ ((~ (y0 = (int_of_num (NUMERAL 0)))) /\ (~ (int_le (int_of_num (NUMERAL 0)) x0))).
Definition term195 (x0 : int) (x1 : int) (x2 : int) := imp (~ ((~ (int_le x0 x1)) \/ (~ (int_le x1 x2)))).
Definition term149 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, ((~ (int_le y0 y1)) \/ (~ (int_le y1 y2))) \/ (int_le y0 y2)) x0.
Definition term62 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, (((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0)) /\ (int_le y0 y2)) -> int_le (rem y0 y1) y2) x0.
Definition term44 (x0 : int) (x1 : int) (x2 : int) := int_le (rem x0 x1) x2.
Definition term51 (x0 : int) (x1 : int) := fun y0 : int => ~ ((fun y1 : int => (((x1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x0)) /\ (int_le x0 y1)) -> int_le (rem x0 x1) y1) y0).
Definition term137 := and (forall y0 : int, forall y1 : int, (int_le (rem y0 y1) y0) \/ ((~ (y1 = (int_of_num (NUMERAL 0)))) /\ (~ (int_le (int_of_num (NUMERAL 0)) y0)))).
Definition term65 := fun y0 : int => exists y1 : int, exists y2 : int, (((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0)) /\ (int_le y0 y2)) /\ (~ (int_le (rem y0 y1) y2)).
Definition term165 := (~ ((int_of_num (NUMERAL 0)) = (int_of_num (NUMERAL 0)))) -> (int_of_num (NUMERAL 0)) = (int_of_num (NUMERAL 0)).
Definition term123 := (forall y0 : int, (fun y1 : int => forall y2 : int, (int_le (rem y1 y2) y1) \/ ((~ (y2 = (int_of_num (NUMERAL 0)))) /\ (~ (int_le (int_of_num (NUMERAL 0)) y1)))) y0) /\ (forall y0 : int, (fun y1 : int => forall y2 : int, (~ (int_le (rem y1 y2) y1)) \/ ((y2 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y1))) y0).
Definition term101 (x0 : int) := (forall y0 : int, (fun y1 : int => (int_le (rem x0 y1) x0) \/ ((~ (y1 = (int_of_num (NUMERAL 0)))) /\ (~ (int_le (int_of_num (NUMERAL 0)) x0)))) y0) /\ (forall y0 : int, (fun y1 : int => (~ (int_le (rem x0 y1) x0)) \/ ((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x0))) y0).
Definition term168 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term119 (x0 : int) := (forall y0 : int, (int_le (rem x0 y0) x0) \/ ((~ (y0 = (int_of_num (NUMERAL 0)))) /\ (~ (int_le (int_of_num (NUMERAL 0)) x0)))) /\ (forall y0 : int, (~ (int_le (rem x0 y0) x0)) \/ ((y0 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x0))).
Definition term173 (x0 : int) := imp (x0 = (int_of_num (NUMERAL 0))).
Definition term153 (x0 : int) (x1 : int) := (fun y0 : int => ((int_le (rem x0 y0) x0) \/ (~ (y0 = (int_of_num (NUMERAL 0))))) /\ ((int_le (rem x0 y0) x0) \/ (~ (int_le (int_of_num (NUMERAL 0)) x0)))) x1.
Definition term167 (x0 : Prop) := (~ x0) -> x0.
Definition term28 (x0 : int) (x1 : int) (x2 : int) := ((int_le x1 x0) /\ (int_le x0 x2)) -> int_le x1 x2.
Definition term12 := ((~ (forall y0 : int, forall y1 : int, forall y2 : int, (((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0)) /\ (int_le y0 y2)) -> int_le (rem y0 y1) y2)) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2) -> (forall y0 : int, forall y1 : int, (int_le (rem y0 y1) y0) = ((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0))) -> False) -> (~ (forall y0 : int, forall y1 : int, forall y2 : int, (((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0)) /\ (int_le y0 y2)) -> int_le (rem y0 y1) y2)) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2) -> (forall y0 : int, forall y1 : int, (int_le (rem y0 y1) y0) = ((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0))) -> False.
Definition term155 (x0 : int) (x1 : int) := ~ (int_le x0 x1).
Definition term166 := ~ ((int_of_num (NUMERAL 0)) = (int_of_num (NUMERAL 0))).
Definition term29 (x0 : int) (x1 : int) := fun y0 : int => ((int_le x1 x0) /\ (int_le x0 y0)) -> int_le x1 y0.
Definition term189 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term63 (x0 : int) := ~ ((fun y0 : int => forall y1 : int, forall y2 : int, (((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0)) /\ (int_le y0 y2)) -> int_le (rem y0 y1) y2) x0).
Definition term172 (x0 : int) := imp (~ (~ (x0 = (int_of_num (NUMERAL 0))))).
Definition term144 (x0 : int) := ~ (int_le (int_of_num (NUMERAL 0)) x0).
Definition term185 (x0 : int) (x1 : int) (x2 : int) := @eq Prop ((~ (int_le x1 x0)) \/ ((~ (int_le x0 x2)) \/ (int_le x1 x2))).
Definition term186 (x0 : int) (x1 : int) (x2 : int) := @eq Prop ((int_le x0 x2) \/ ((~ (int_le x0 x1)) \/ (~ (int_le x1 x2)))).
Definition term97 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term19 := (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2) -> (forall y0 : int, forall y1 : int, (int_le (rem y0 y1) y0) = ((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0))) -> False.
Definition term206 (x0 : int) := ~ (~ (int_le (int_of_num (NUMERAL 0)) x0)).
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term22 := (~ (forall y0 : int, forall y1 : int, forall y2 : int, (((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0)) /\ (int_le y0 y2)) -> int_le (rem y0 y1) y2)) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2) -> ~ (forall y0 : int, forall y1 : int, (int_le (rem y0 y1) y0) = ((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0))).
Definition term200 (x0 : int) (x1 : int) := int_le (rem x0 (int_of_num (NUMERAL 0))) x1.
Definition term116 (x0 : int) := fun y0 : int => (fun y1 : int => (~ (int_le (rem x0 y1) x0)) \/ ((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x0))) y0.
Definition term111 (x0 : int) := fun y0 : int => (fun y1 : int => (int_le (rem x0 y1) x0) \/ ((~ (y1 = (int_of_num (NUMERAL 0)))) /\ (~ (int_le (int_of_num (NUMERAL 0)) x0)))) y0.
Definition term182 (x0 : int) (x1 : int) := or (~ (int_le x0 x1)).
Definition term118 (x0 : int) := forall y0 : int, (~ (int_le (rem x0 y0) x0)) \/ ((y0 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x0)).
Definition term141 := (forall y0 : int, forall y1 : int, (int_le (rem y0 y1) y0) \/ ((~ (y1 = (int_of_num (NUMERAL 0)))) /\ (~ (int_le (int_of_num (NUMERAL 0)) y0)))) /\ (forall y0 : int, forall y1 : int, (~ (int_le (rem y0 y1) y0)) \/ ((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0))).
Definition term213 (x0 : int) (x1 : int) (x2 : int) := ((int_le (rem x0 x1) x0) /\ (int_le x0 x2)) -> int_le (rem x0 x1) x2.
Definition term127 (x0 : int) := and ((fun y0 : int => forall y1 : int, (int_le (rem y0 y1) y0) \/ ((~ (y1 = (int_of_num (NUMERAL 0)))) /\ (~ (int_le (int_of_num (NUMERAL 0)) y0)))) x0).
Definition term177 (x0 : int) := (~ (int_le (rem x0 (int_of_num (NUMERAL 0))) x0)) -> int_le (rem x0 (int_of_num (NUMERAL 0))) x0.
Definition term36 (x0 : int) (x1 : int) := fun y0 : int => (((x1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x0)) /\ (int_le x0 y0)) -> int_le (rem x0 x1) y0.
Definition term136 := and (forall y0 : int, (fun y1 : int => forall y2 : int, (int_le (rem y1 y2) y1) \/ ((~ (y2 = (int_of_num (NUMERAL 0)))) /\ (~ (int_le (int_of_num (NUMERAL 0)) y1)))) y0).
Definition term114 (x0 : int) := and (forall y0 : int, (fun y1 : int => (int_le (rem x0 y1) x0) \/ ((~ (y1 = (int_of_num (NUMERAL 0)))) /\ (~ (int_le (int_of_num (NUMERAL 0)) x0)))) y0).
Definition term49 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => (((x1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x0)) /\ (int_le x0 y0)) -> int_le (rem x0 x1) y0) x2.
Definition term132 := @eq Prop (forall y0 : int, (forall y1 : int, (int_le (rem y0 y1) y0) \/ ((~ (y1 = (int_of_num (NUMERAL 0)))) /\ (~ (int_le (int_of_num (NUMERAL 0)) y0)))) /\ (forall y1 : int, (~ (int_le (rem y0 y1) y0)) \/ ((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0)))).
Definition term131 := @eq Prop (forall y0 : int, ((fun y1 : int => forall y2 : int, (int_le (rem y1 y2) y1) \/ ((~ (y2 = (int_of_num (NUMERAL 0)))) /\ (~ (int_le (int_of_num (NUMERAL 0)) y1)))) y0) /\ ((fun y1 : int => forall y2 : int, (~ (int_le (rem y1 y2) y1)) \/ ((y2 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y1))) y0)).
Definition term110 (x0 : int) := @eq Prop (forall y0 : int, ((int_le (rem x0 y0) x0) \/ ((~ (y0 = (int_of_num (NUMERAL 0)))) /\ (~ (int_le (int_of_num (NUMERAL 0)) x0)))) /\ ((~ (int_le (rem x0 y0) x0)) \/ ((y0 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x0)))).
Definition term109 (x0 : int) := @eq Prop (forall y0 : int, ((fun y1 : int => (int_le (rem x0 y1) x0) \/ ((~ (y1 = (int_of_num (NUMERAL 0)))) /\ (~ (int_le (int_of_num (NUMERAL 0)) x0)))) y0) /\ ((fun y1 : int => (~ (int_le (rem x0 y1) x0)) \/ ((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x0))) y0)).
Definition term87 (x0 : int) (x1 : int) := (int_le (rem x1 x0) x1) \/ ((~ (x0 = (int_of_num (NUMERAL 0)))) /\ (~ (int_le (int_of_num (NUMERAL 0)) x1))).
Definition term169 (x0 : int) (x1 : int) := (~ (~ (x0 = (int_of_num (NUMERAL 0))))) -> int_le (rem x1 x0) x1.
Definition term52 (x0 : int) (x1 : int) := fun y0 : int => (((x1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x0)) /\ (int_le x0 y0)) /\ (~ (int_le (rem x0 x1) y0)).
Definition term15 := (forall y0 : int, forall y1 : int, (int_le (rem y0 y1) y0) = ((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0))) -> False.
Definition term43 (x0 : int) (x1 : int) (x2 : int) := ((x0 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x1)) /\ (int_le x1 x2).
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term176 (x0 : int) := int_le (rem x0 (int_of_num (NUMERAL 0))) x0.
Definition term122 := forall y0 : int, ((fun y1 : int => forall y2 : int, (int_le (rem y1 y2) y1) \/ ((~ (y2 = (int_of_num (NUMERAL 0)))) /\ (~ (int_le (int_of_num (NUMERAL 0)) y1)))) y0) /\ ((fun y1 : int => forall y2 : int, (~ (int_le (rem y1 y2) y1)) \/ ((y2 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y1))) y0).
Definition term100 (x0 : int) := forall y0 : int, ((fun y1 : int => (int_le (rem x0 y1) x0) \/ ((~ (y1 = (int_of_num (NUMERAL 0)))) /\ (~ (int_le (int_of_num (NUMERAL 0)) x0)))) y0) /\ ((fun y1 : int => (~ (int_le (rem x0 y1) x0)) \/ ((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x0))) y0).
Definition term188 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term68 (x0 : int) (x1 : int) (x2 : int) := (~ (int_le x0 x1)) \/ (~ (int_le x1 x2)).
Definition term23 (x0 : int) (x1 : int) := int_le (rem x1 x0) x1.
Definition term53 (x0 : int) (x1 : int) := exists y0 : int, (((x1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x0)) /\ (int_le x0 y0)) /\ (~ (int_le (rem x0 x1) y0)).
Definition term159 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => ~ (int_le (rem x0 y0) x1)) x2.
Definition term174 (x0 : int) (x1 : int) := (x0 = (int_of_num (NUMERAL 0))) -> int_le (rem x1 x0) x1.
Definition term178 (x0 : int) := ~ (int_le (rem x0 (int_of_num (NUMERAL 0))) x0).
Definition term47 (x0 : int) (x1 : int) := ~ (forall y0 : int, (((x1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x0)) /\ (int_le x0 y0)) -> int_le (rem x0 x1) y0).
Definition term157 (x0 : int) (x1 : int) := (int_le (rem x1 x0) x1) \/ (~ (int_le (int_of_num (NUMERAL 0)) x1)).
Definition term184 (x0 : int) (x1 : int) (x2 : int) := (int_le x0 x2) \/ ((~ (int_le x0 x1)) \/ (~ (int_le x1 x2))).
Definition term13 := (((~ (forall y0 : int, forall y1 : int, forall y2 : int, (((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0)) /\ (int_le y0 y2)) -> int_le (rem y0 y1) y2)) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2) -> (forall y0 : int, forall y1 : int, (int_le (rem y0 y1) y0) = ((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0))) -> False) -> (~ (forall y0 : int, forall y1 : int, forall y2 : int, (((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0)) /\ (int_le y0 y2)) -> int_le (rem y0 y1) y2)) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2) -> (forall y0 : int, forall y1 : int, (int_le (rem y0 y1) y0) = ((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0))) -> False) -> (~ (forall y0 : int, forall y1 : int, forall y2 : int, (((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0)) /\ (int_le y0 y2)) -> int_le (rem y0 y1) y2)) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2) -> (forall y0 : int, forall y1 : int, (int_le (rem y0 y1) y0) = ((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0))) -> False.
Definition term121 := forall y0 : int, (forall y1 : int, (int_le (rem y0 y1) y0) \/ ((~ (y1 = (int_of_num (NUMERAL 0)))) /\ (~ (int_le (int_of_num (NUMERAL 0)) y0)))) /\ (forall y1 : int, (~ (int_le (rem y0 y1) y0)) \/ ((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0))).
Definition term146 (x0 : int) := forall y0 : int, ((int_le (rem x0 y0) x0) \/ (~ (y0 = (int_of_num (NUMERAL 0))))) /\ ((int_le (rem x0 y0) x0) \/ (~ (int_le (int_of_num (NUMERAL 0)) x0))).
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term148 := forall y0 : int, forall y1 : int, ((int_le (rem y0 y1) y0) \/ (~ (y1 = (int_of_num (NUMERAL 0))))) /\ ((int_le (rem y0 y1) y0) \/ (~ (int_le (int_of_num (NUMERAL 0)) y0))).
Definition term140 := forall y0 : int, forall y1 : int, (~ (int_le (rem y0 y1) y0)) \/ ((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0)).
Definition term135 := forall y0 : int, forall y1 : int, (int_le (rem y0 y1) y0) \/ ((~ (y1 = (int_of_num (NUMERAL 0)))) /\ (~ (int_le (int_of_num (NUMERAL 0)) y0))).
Definition term95 := forall y0 : int, forall y1 : int, ((int_le (rem y0 y1) y0) \/ ((~ (y1 = (int_of_num (NUMERAL 0)))) /\ (~ (int_le (int_of_num (NUMERAL 0)) y0)))) /\ ((~ (int_le (rem y0 y1) y0)) \/ ((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0))).
Definition term79 := forall y0 : int, forall y1 : int, forall y2 : int, ((~ (int_le y0 y1)) \/ (~ (int_le y1 y2))) \/ (int_le y0 y2).
Definition term77 (x0 : int) := forall y0 : int, forall y1 : int, ((~ (int_le x0 y0)) \/ (~ (int_le y0 y1))) \/ (int_le x0 y1).
Definition term39 (x0 : int) := forall y0 : int, forall y1 : int, (((y0 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x0)) /\ (int_le x0 y1)) -> int_le (rem x0 y0) y1.
Definition term34 := forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2.
Definition term32 (x0 : int) := forall y0 : int, forall y1 : int, ((int_le x0 y0) /\ (int_le y0 y1)) -> int_le x0 y1.
Definition term17 := forall y0 : int, forall y1 : int, (int_le (rem y0 y1) y0) = ((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0)).
Definition term8 := forall y0 : int, forall y1 : int, forall y2 : int, (((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0)) /\ (int_le y0 y2)) -> int_le (rem y0 y1) y2.
Definition term145 (x0 : int) := fun y0 : int => ((int_le (rem x0 y0) x0) \/ (~ (y0 = (int_of_num (NUMERAL 0))))) /\ ((int_le (rem x0 y0) x0) \/ (~ (int_le (int_of_num (NUMERAL 0)) x0))).
Definition term108 (x0 : int) := fun y0 : int => ((fun y1 : int => (int_le (rem x0 y1) x0) \/ ((~ (y1 = (int_of_num (NUMERAL 0)))) /\ (~ (int_le (int_of_num (NUMERAL 0)) x0)))) y0) /\ ((fun y1 : int => (~ (int_le (rem x0 y1) x0)) \/ ((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x0))) y0).
Definition term70 (x0 : int) (x1 : int) (x2 : int) := or ((~ (int_le x0 x1)) \/ (~ (int_le x1 x2))).
Definition term9 := (~ (forall y0 : int, forall y1 : int, forall y2 : int, (((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0)) /\ (int_le y0 y2)) -> int_le (rem y0 y1) y2)) -> False.
Definition term120 := fun y0 : int => (forall y1 : int, (int_le (rem y0 y1) y0) \/ ((~ (y1 = (int_of_num (NUMERAL 0)))) /\ (~ (int_le (int_of_num (NUMERAL 0)) y0)))) /\ (forall y1 : int, (~ (int_le (rem y0 y1) y0)) \/ ((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0))).
Definition term72 (x0 : int) (x1 : int) (x2 : int) := ((~ (int_le x1 x0)) \/ (~ (int_le x0 x2))) \/ (int_le x1 x2).
Definition term76 (x0 : int) := fun y0 : int => forall y1 : int, ((~ (int_le x0 y0)) \/ (~ (int_le y0 y1))) \/ (int_le x0 y1).
Definition term38 (x0 : int) := fun y0 : int => forall y1 : int, (((y0 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x0)) /\ (int_le x0 y1)) -> int_le (rem x0 y0) y1.
Definition term31 (x0 : int) := fun y0 : int => forall y1 : int, ((int_le x0 y0) /\ (int_le y0 y1)) -> int_le x0 y1.
Definition term57 (x0 : int) (x1 : int) := ~ ((fun y0 : int => forall y1 : int, (((y0 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x0)) /\ (int_le x0 y1)) -> int_le (rem x0 y0) y1) x1).
Definition term84 (x0 : int) (x1 : int) := (~ (int_le (rem x1 x0) x1)) \/ ((x0 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x1)).
Definition term158 (x0 : int) (x1 : int) := fun y0 : int => ~ (int_le (rem x0 y0) x1).
Definition term25 (x0 : int) := fun y0 : int => (int_le (rem x0 y0) x0) = ((y0 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x0)).
Definition term80 (x0 : int) (x1 : int) := ~ ((x0 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x1)).
Definition term88 (x0 : int) (x1 : int) := and ((int_le (rem x1 x0) x1) \/ (~ ((x0 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x1)))).
Definition term209 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x1) -> int_le (rem x1 x0) x1.
Definition term14 := (((~ (forall y0 : int, forall y1 : int, forall y2 : int, (((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0)) /\ (int_le y0 y2)) -> int_le (rem y0 y1) y2)) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2) -> (forall y0 : int, forall y1 : int, (int_le (rem y0 y1) y0) = ((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0))) -> False) -> (~ (forall y0 : int, forall y1 : int, forall y2 : int, (((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0)) /\ (int_le y0 y2)) -> int_le (rem y0 y1) y2)) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2) -> (forall y0 : int, forall y1 : int, (int_le (rem y0 y1) y0) = ((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0))) -> False) -> ((~ (forall y0 : int, forall y1 : int, forall y2 : int, (((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0)) /\ (int_le y0 y2)) -> int_le (rem y0 y1) y2)) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2) -> (forall y0 : int, forall y1 : int, (int_le (rem y0 y1) y0) = ((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0))) -> False) -> (~ (forall y0 : int, forall y1 : int, forall y2 : int, (((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0)) /\ (int_le y0 y2)) -> int_le (rem y0 y1) y2)) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2) -> (forall y0 : int, forall y1 : int, (int_le (rem y0 y1) y0) = ((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0))) -> False.
Definition term1 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term50 (x0 : int) (x1 : int) (x2 : int) := ~ ((fun y0 : int => (((x1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x0)) /\ (int_le x0 y0)) -> int_le (rem x0 x1) y0) x2).
Definition term193 (x0 : int) (x1 : int) := and (~ (~ (int_le x0 x1))).
Definition term215 (x0 : int) (x1 : int) (x2 : int) := (int_le (rem x0 x1) x2) -> False.
Definition term139 := forall y0 : int, (fun y1 : int => forall y2 : int, (~ (int_le (rem y1 y2) y1)) \/ ((y2 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y1))) y0.
Definition term134 := forall y0 : int, (fun y1 : int => forall y2 : int, (int_le (rem y1 y2) y1) \/ ((~ (y2 = (int_of_num (NUMERAL 0)))) /\ (~ (int_le (int_of_num (NUMERAL 0)) y1)))) y0.
Definition term143 (x0 : int) := ~ (x0 = (int_of_num (NUMERAL 0))).
Definition term210 (x0 : int) (x1 : int) := (~ (int_le (rem x1 x0) x1)) -> int_le (rem x1 x0) x1.
Definition term54 (x0 : int) := ~ (forall y0 : int, forall y1 : int, (((y0 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x0)) /\ (int_le x0 y1)) -> int_le (rem x0 y0) y1).
Definition term16 := ~ (forall y0 : int, forall y1 : int, (int_le (rem y0 y1) y0) = ((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0))).
Definition term10 := ~ (forall y0 : int, forall y1 : int, forall y2 : int, (((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0)) /\ (int_le y0 y2)) -> int_le (rem y0 y1) y2).
Definition term91 (x0 : int) (x1 : int) := ((int_le (rem x1 x0) x1) \/ ((~ (x0 = (int_of_num (NUMERAL 0)))) /\ (~ (int_le (int_of_num (NUMERAL 0)) x1)))) /\ ((~ (int_le (rem x1 x0) x1)) \/ ((x0 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x1))).
Definition term105 (x0 : int) (x1 : int) := and ((fun y0 : int => (int_le (rem x0 y0) x0) \/ ((~ (y0 = (int_of_num (NUMERAL 0)))) /\ (~ (int_le (int_of_num (NUMERAL 0)) x0)))) x1).
Definition term18 := imp (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2).
Definition term98 (x0 : int -> Prop) (x1 : int -> Prop) := forall y0 : int, (x0 y0) /\ (x1 y0).
Definition term212 (x0 : int) (x1 : int) (x2 : int) := (int_le (rem x1 x0) x1) /\ (int_le x1 x2).
Definition term142 (x0 : int) (x1 : int) := ((int_le (rem x1 x0) x1) \/ (~ (x0 = (int_of_num (NUMERAL 0))))) /\ ((int_le (rem x1 x0) x1) \/ (~ (int_le (int_of_num (NUMERAL 0)) x1))).
Definition term156 (x0 : int) (x1 : int) (x2 : int) := ~ (int_le (rem x0 x1) x2).
Definition term196 (x0 : int) (x1 : int) (x2 : int) := imp ((int_le x0 x1) /\ (int_le x1 x2)).
Definition term92 (x0 : int) := fun y0 : int => ((int_le (rem x0 y0) x0) \/ ((~ (y0 = (int_of_num (NUMERAL 0)))) /\ (~ (int_le (int_of_num (NUMERAL 0)) x0)))) /\ ((~ (int_le (rem x0 y0) x0)) \/ ((y0 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x0))).
Definition term74 (x0 : int) (x1 : int) := fun y0 : int => ((~ (int_le x1 x0)) \/ (~ (int_le x0 y0))) \/ (int_le x1 y0).
Definition term30 (x0 : int) (x1 : int) := forall y0 : int, ((int_le x1 x0) /\ (int_le x0 y0)) -> int_le x1 y0.
Definition term115 (x0 : int) := and (forall y0 : int, (int_le (rem x0 y0) x0) \/ ((~ (y0 = (int_of_num (NUMERAL 0)))) /\ (~ (int_le (int_of_num (NUMERAL 0)) x0)))).
Definition term103 (x0 : int) := fun y0 : int => (~ (int_le (rem x0 y0) x0)) \/ ((y0 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x0)).
Definition term129 (x0 : int) := ((fun y0 : int => forall y1 : int, (int_le (rem y0 y1) y0) \/ ((~ (y1 = (int_of_num (NUMERAL 0)))) /\ (~ (int_le (int_of_num (NUMERAL 0)) y0)))) x0) /\ ((fun y0 : int => forall y1 : int, (~ (int_le (rem y0 y1) y0)) \/ ((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0))) x0).
Definition term194 (x0 : int) (x1 : int) := and (int_le x0 x1).
Definition term102 (x0 : int) := fun y0 : int => (int_le (rem x0 y0) x0) \/ ((~ (y0 = (int_of_num (NUMERAL 0)))) /\ (~ (int_le (int_of_num (NUMERAL 0)) x0))).
Definition term85 (x0 : int) (x1 : int) := or (int_le (rem x1 x0) x1).
Definition term24 (x0 : int) (x1 : int) := (x0 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x1).
Definition term202 (x0 : int) (x1 : int) := (int_le (rem x0 (int_of_num (NUMERAL 0))) x1) -> False.
Definition term190 (x0 : int) (x1 : int) (x2 : int) := ~ ((~ (int_le x0 x1)) \/ (~ (int_le x1 x2))).
Definition term71 (x0 : int) (x1 : int) (x2 : int) := (~ ((int_le x1 x0) /\ (int_le x0 x2))) \/ (int_le x1 x2).
Definition term99 (x0 : int -> Prop) (x1 : int -> Prop) := (forall y0 : int, x0 y0) /\ (forall y0 : int, x1 y0).
Definition term171 (x0 : int) := ~ (~ (x0 = (int_of_num (NUMERAL 0)))).
Definition term37 (x0 : int) (x1 : int) := forall y0 : int, (((x1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x0)) /\ (int_le x0 y0)) -> int_le (rem x0 x1) y0.
Definition term20 := (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2) -> ~ (forall y0 : int, forall y1 : int, (int_le (rem y0 y1) y0) = ((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0))).
Definition term197 (x0 : int) (x1 : int) := (int_le (rem x0 (int_of_num (NUMERAL 0))) x0) /\ (int_le x0 x1).
Definition term164 (x0 : int) (x1 : int) := (int_le (rem x0 x1) x0) \/ (~ (x1 = (int_of_num (NUMERAL 0)))).
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term67 (x0 : int) (x1 : int) (x2 : int) := ~ ((int_le x0 x1) /\ (int_le x1 x2)).
Definition term73 (x0 : int) (x1 : int) (x2 : int) := (int_le x0 x1) /\ (int_le x1 x2).
Definition term130 := fun y0 : int => ((fun y1 : int => forall y2 : int, (int_le (rem y1 y2) y1) \/ ((~ (y2 = (int_of_num (NUMERAL 0)))) /\ (~ (int_le (int_of_num (NUMERAL 0)) y1)))) y0) /\ ((fun y1 : int => forall y2 : int, (~ (int_le (rem y1 y2) y1)) \/ ((y2 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y1))) y0).
Definition term199 (x0 : int) := rem x0 (int_of_num (NUMERAL 0)).
Definition term89 (x0 : int) (x1 : int) := and ((int_le (rem x1 x0) x1) \/ ((~ (x0 = (int_of_num (NUMERAL 0)))) /\ (~ (int_le (int_of_num (NUMERAL 0)) x1)))).
Definition term107 (x0 : int) (x1 : int) := ((fun y0 : int => (int_le (rem x0 y0) x0) \/ ((~ (y0 = (int_of_num (NUMERAL 0)))) /\ (~ (int_le (int_of_num (NUMERAL 0)) x0)))) x1) /\ ((fun y0 : int => (~ (int_le (rem x0 y0) x0)) \/ ((y0 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x0))) x1).
Definition term96 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term61 := exists y0 : int, ~ ((fun y1 : int => forall y2 : int, forall y3 : int, (((y2 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y1)) /\ (int_le y1 y3)) -> int_le (rem y1 y2) y3) y0).
Definition term55 (x0 : int) := exists y0 : int, ~ ((fun y1 : int => forall y2 : int, (((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x0)) /\ (int_le x0 y2)) -> int_le (rem x0 y1) y2) y0).
Definition term48 (x0 : int) (x1 : int) := exists y0 : int, ~ ((fun y1 : int => (((x1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x0)) /\ (int_le x0 y1)) -> int_le (rem x0 x1) y1) y0).
Definition term66 := exists y0 : int, exists y1 : int, exists y2 : int, (((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0)) /\ (int_le y0 y2)) /\ (~ (int_le (rem y0 y1) y2)).
Definition term60 (x0 : int) := exists y0 : int, exists y1 : int, (((y0 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x0)) /\ (int_le x0 y1)) /\ (~ (int_le (rem x0 y0) y1)).
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term83 (x0 : int) := int_le (int_of_num (NUMERAL 0)) x0.
Definition term183 (x0 : int) (x1 : int) (x2 : int) := (~ (int_le x0 x1)) \/ ((int_le x0 x2) \/ (~ (int_le x1 x2))).
Definition term214 (x0 : int) (x1 : int) (x2 : int) := (~ (int_le (rem x0 x1) x2)) -> int_le (rem x0 x1) x2.
Definition term161 (x0 : int) (x1 : int) := ~ (int_le (rem x0 (int_of_num (NUMERAL 0))) x1).
Definition term162 (x0 : int) (x1 : int) (x2 : int) := @eq Prop ((fun y0 : int => ~ (int_le (rem x0 y0) x1)) x2).
Definition term42 (x0 : int) (x1 : int) (x2 : int) := (((x1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x0)) /\ (int_le x0 x2)) /\ (~ (int_le (rem x0 x1) x2)).
Definition term59 (x0 : int) := fun y0 : int => exists y1 : int, (((y0 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x0)) /\ (int_le x0 y1)) /\ (~ (int_le (rem x0 y0) y1)).
Definition term26 (x0 : int) := forall y0 : int, (int_le (rem x0 y0) x0) = ((y0 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x0)).
Definition term11 := (~ (forall y0 : int, forall y1 : int, forall y2 : int, (((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0)) /\ (int_le y0 y2)) -> int_le (rem y0 y1) y2)) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2) -> (forall y0 : int, forall y1 : int, (int_le (rem y0 y1) y0) = ((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0))) -> False.
Definition term154 (x0 : int) (x1 : int) (x2 : int) := (~ (int_le x1 x0)) \/ ((~ (int_le x0 x2)) \/ (int_le x1 x2)).
Definition term117 (x0 : int) := forall y0 : int, (fun y1 : int => (~ (int_le (rem x0 y1) x0)) \/ ((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x0))) y0.
Definition term112 (x0 : int) := forall y0 : int, (fun y1 : int => (int_le (rem x0 y1) x0) \/ ((~ (y1 = (int_of_num (NUMERAL 0)))) /\ (~ (int_le (int_of_num (NUMERAL 0)) x0)))) y0.
Definition term86 (x0 : int) (x1 : int) := (int_le (rem x1 x0) x1) \/ (~ ((x0 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x1))).
Definition term204 (x0 : int) := (~ (int_le (int_of_num (NUMERAL 0)) x0)) -> int_le (int_of_num (NUMERAL 0)) x0.
Definition term151 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => ((~ (int_le x1 x0)) \/ (~ (int_le x0 y0))) \/ (int_le x1 y0)) x2.
Definition term138 := fun y0 : int => (fun y1 : int => forall y2 : int, (~ (int_le (rem y1 y2) y1)) \/ ((y2 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y1))) y0.
Definition term133 := fun y0 : int => (fun y1 : int => forall y2 : int, (int_le (rem y1 y2) y1) \/ ((~ (y2 = (int_of_num (NUMERAL 0)))) /\ (~ (int_le (int_of_num (NUMERAL 0)) y1)))) y0.
Definition term192 (x0 : int) (x1 : int) := ~ (~ (int_le x0 x1)).
Definition term35 (x0 : int) (x1 : int) (x2 : int) := (((x1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x0)) /\ (int_le x0 x2)) -> int_le (rem x0 x1) x2.
Definition term179 (x0 : int) (x1 : int) := (~ (int_le x0 x1)) -> int_le x0 x1.
Definition term187 (x0 : int) (x1 : int) (x2 : int) := (~ ((~ (int_le x1 x0)) \/ (~ (int_le x0 x2)))) -> int_le x1 x2.
Definition term21 := imp (~ (forall y0 : int, forall y1 : int, forall y2 : int, (((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0)) /\ (int_le y0 y2)) -> int_le (rem y0 y1) y2)).
Definition term207 (x0 : int) := imp (~ (~ (int_le (int_of_num (NUMERAL 0)) x0))).
Definition term64 := fun y0 : int => ~ ((fun y1 : int => forall y2 : int, forall y3 : int, (((y2 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y1)) /\ (int_le y1 y3)) -> int_le (rem y1 y2) y3) y0).
Definition term58 (x0 : int) := fun y0 : int => ~ ((fun y1 : int => forall y2 : int, (((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x0)) /\ (int_le x0 y2)) -> int_le (rem x0 y1) y2) y0).
