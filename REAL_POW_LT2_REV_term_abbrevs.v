Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term139 := fun y0 : nat => forall y1 : real, forall y2 : real, ((~ (real_le (real_of_num (NUMERAL 0)) y1)) \/ (~ (real_le y1 y2))) \/ (real_le (real_pow y1 y0) (real_pow y2 y0)).
Definition term39 := fun y0 : nat => forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt (real_pow y1 y0) (real_pow y2 y0))) -> real_lt y1 y2.
Definition term28 := fun y0 : nat => forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0).
Definition term59 (x0 : nat -> Prop) := ~ (all x0).
Definition term43 (x0 : real -> Prop) := ~ (all x0).
Definition term189 := (~ False) -> False.
Definition term18 := imp (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0)).
Definition term141 (x0 : nat) := (fun y0 : nat => forall y1 : real, forall y2 : real, ((~ (real_le (real_of_num (NUMERAL 0)) y1)) \/ (~ (real_le y1 y2))) \/ (real_le (real_pow y1 y0) (real_pow y2 y0))) x0.
Definition term62 (x0 : nat) := (fun y0 : nat => forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt (real_pow y1 y0) (real_pow y2 y0))) -> real_lt y1 y2) x0.
Definition term171 (x0 : nat) (x1 : real) (x2 : real) := (~ ((~ (real_le (real_of_num (NUMERAL 0)) x1)) \/ (real_le (real_pow x1 x0) (real_pow x2 x0)))) -> ~ (real_le x1 x2).
Definition term154 (x0 : Prop) := ~ (~ x0).
Definition term143 (x0 : real) (x1 : nat) (x2 : real) := (fun y0 : real => ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_le x0 y0))) \/ (real_le (real_pow x0 x1) (real_pow y0 x1))) x2.
Definition term121 := and (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) \/ (~ (real_lt y1 y0))).
Definition term168 (x0 : nat) (x1 : real) (x2 : real) := (real_le (real_pow x2 x0) (real_pow x1 x0)) \/ ((~ (real_le x2 x1)) \/ (~ (real_le (real_of_num (NUMERAL 0)) x2))).
Definition term99 (x0 : real) := and (forall y0 : real, (~ (real_le x0 y0)) \/ (~ (real_lt y0 x0))).
Definition term144 (x0 : real) (x1 : real) (x2 : nat) := (~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ ((~ (real_le x0 x1)) \/ (real_le (real_pow x0 x2) (real_pow x1 x2))).
Definition term67 (x0 : real) (x1 : real) := ~ (~ (real_le x0 x1)).
Definition term170 (x0 : nat) (x1 : real) (x2 : real) := @eq Prop ((real_le (real_pow x2 x0) (real_pow x1 x0)) \/ ((~ (real_le x2 x1)) \/ (~ (real_le (real_of_num (NUMERAL 0)) x2)))).
Definition term111 (x0 : real) := and ((fun y0 : real => forall y1 : real, (~ (real_le y0 y1)) \/ (~ (real_lt y1 y0))) x0).
Definition term102 (x0 : real) := forall y0 : real, (real_le x0 y0) \/ (real_lt y0 x0).
Definition term3 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term150 (x0 : real) (x1 : real) (x2 : nat) := (~ (real_lt (real_pow x0 x2) (real_pow x1 x2))) -> real_lt (real_pow x0 x2) (real_pow x1 x2).
Definition term120 := and (forall y0 : real, (fun y1 : real => forall y2 : real, (~ (real_le y1 y2)) \/ (~ (real_lt y2 y1))) y0).
Definition term98 (x0 : real) := and (forall y0 : real, (fun y1 : real => (~ (real_le x0 y1)) \/ (~ (real_lt y1 x0))) y0).
Definition term7 (x0 : Prop) := (~ x0) -> False.
Definition term45 (x0 : nat) (x1 : real) := ~ (forall y0 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_pow x1 x0) (real_pow y0 x0))) -> real_lt x1 y0).
Definition term104 := fun y0 : real => (forall y1 : real, (~ (real_le y0 y1)) \/ (~ (real_lt y1 y0))) /\ (forall y1 : real, (real_le y0 y1) \/ (real_lt y1 y0)).
Definition term74 (x0 : real) (x1 : real) := ((~ (real_le x1 x0)) \/ (~ (real_lt x0 x1))) /\ ((real_le x1 x0) \/ (real_lt x0 x1)).
Definition term86 (x0 : real) := fun y0 : real => (real_le x0 y0) \/ (real_lt y0 x0).
Definition term158 (x0 : real) (x1 : real) := (real_lt x1 x0) -> ~ (real_le x0 x1).
Definition term125 := (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) \/ (~ (real_lt y1 y0))) /\ (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_lt y1 y0)).
Definition term187 (x0 : real) (x1 : real) := (~ (real_lt x0 x1)) -> real_lt x0 x1.
Definition term188 (x0 : real) (x1 : real) := (real_lt x0 x1) -> False.
Definition term152 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term107 := (forall y0 : real, (fun y1 : real => forall y2 : real, (~ (real_le y1 y2)) \/ (~ (real_lt y2 y1))) y0) /\ (forall y0 : real, (fun y1 : real => forall y2 : real, (real_le y1 y2) \/ (real_lt y2 y1)) y0).
Definition term84 (x0 : real) := (forall y0 : real, (fun y1 : real => (~ (real_le x0 y1)) \/ (~ (real_lt y1 x0))) y0) /\ (forall y0 : real, (fun y1 : real => (real_le x0 y1) \/ (real_lt y1 x0)) y0).
Definition term41 (x0 : nat) (x1 : real) (x2 : real) := ((real_le (real_of_num (NUMERAL 0)) x2) /\ (real_lt (real_pow x1 x0) (real_pow x2 x0))) /\ (~ (real_lt x1 x2)).
Definition term73 (x0 : real) (x1 : real) := ((~ (real_le x1 x0)) \/ (~ (real_lt x0 x1))) /\ ((~ (~ (real_le x1 x0))) \/ (real_lt x0 x1)).
Definition term16 := ~ (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)).
Definition term10 := ~ (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt (real_pow y1 y0) (real_pow y2 y0))) -> real_lt y1 y2).
Definition term185 (x0 : real) (x1 : real) := @eq Prop ((real_le x1 x0) \/ (real_lt x0 x1)).
Definition term127 (x0 : real) (x1 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_le x0 x1)).
Definition term130 (x0 : real) (x1 : real) := or (~ ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 x1))).
Definition term148 (x0 : Prop) := (~ x0) -> x0.
Definition term175 (x0 : real) (x1 : real) (x2 : nat) := (~ (~ (real_le (real_of_num (NUMERAL 0)) x0))) /\ (~ (real_le (real_pow x0 x2) (real_pow x1 x2))).
Definition term12 := ((~ (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt (real_pow y1 y0) (real_pow y2 y0))) -> real_lt y1 y2)) -> (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) -> False) -> (~ (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt (real_pow y1 y0) (real_pow y2 y0))) -> real_lt y1 y2)) -> (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) -> False.
Definition term23 (x0 : real) (x1 : real) (x2 : nat) := ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 x1)) -> real_le (real_pow x0 x2) (real_pow x1 x2).
Definition term122 := fun y0 : real => (fun y1 : real => forall y2 : real, (real_le y1 y2) \/ (real_lt y2 y1)) y0.
Definition term117 := fun y0 : real => (fun y1 : real => forall y2 : real, (~ (real_le y1 y2)) \/ (~ (real_lt y2 y1))) y0.
Definition term173 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term145 (x0 : real) := ~ (real_le (real_of_num (NUMERAL 0)) x0).
Definition term164 (x0 : real) (x1 : real) (x2 : nat) := (~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (real_le (real_pow x0 x2) (real_pow x1 x2)).
Definition term138 (x0 : nat) := forall y0 : real, forall y1 : real, ((~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ (~ (real_le y0 y1))) \/ (real_le (real_pow y0 x0) (real_pow y1 x0)).
Definition term124 := forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_lt y1 y0).
Definition term119 := forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) \/ (~ (real_lt y1 y0)).
Definition term78 := forall y0 : real, forall y1 : real, ((~ (real_le y0 y1)) \/ (~ (real_lt y1 y0))) /\ ((real_le y0 y1) \/ (real_lt y1 y0)).
Definition term38 (x0 : nat) := forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt (real_pow y0 x0) (real_pow y1 x0))) -> real_lt y0 y1.
Definition term33 := forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0).
Definition term27 (x0 : nat) := forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y0 y1)) -> real_le (real_pow y0 x0) (real_pow y1 x0).
Definition term76 (x0 : real) := forall y0 : real, ((~ (real_le x0 y0)) \/ (~ (real_lt y0 x0))) /\ ((real_le x0 y0) \/ (real_lt y0 x0)).
Definition term58 (x0 : nat) := exists y0 : real, exists y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt (real_pow y0 x0) (real_pow y1 x0))) /\ (~ (real_lt y0 y1)).
Definition term80 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term19 := (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) -> False.
Definition term50 (x0 : nat) (x1 : real) := fun y0 : real => ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_pow x1 x0) (real_pow y0 x0))) /\ (~ (real_lt x1 y0)).
Definition term70 (x0 : real) (x1 : real) := (~ (~ (real_le x1 x0))) \/ (real_lt x0 x1).
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term22 := (~ (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt (real_pow y1 y0) (real_pow y2 y0))) -> real_lt y1 y2)) -> (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0)) -> ~ (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)).
Definition term147 (x0 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x0)) -> real_le (real_of_num (NUMERAL 0)) x0.
Definition term25 (x0 : real) (x1 : nat) := forall y0 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 y0)) -> real_le (real_pow x0 x1) (real_pow y0 x1).
Definition term53 (x0 : nat) := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt (real_pow y1 x0) (real_pow y2 x0))) -> real_lt y1 y2) y0).
Definition term46 (x0 : nat) (x1 : real) := exists y0 : real, ~ ((fun y1 : real => ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt (real_pow x1 x0) (real_pow y1 x0))) -> real_lt x1 y1) y0).
Definition term75 (x0 : real) := fun y0 : real => ((~ (real_le x0 y0)) \/ (~ (real_lt y0 x0))) /\ ((real_le x0 y0) \/ (real_lt y0 x0)).
Definition term129 (x0 : real) (x1 : real) (x2 : nat) := real_le (real_pow x0 x2) (real_pow x1 x2).
Definition term65 := fun y0 : nat => exists y1 : real, exists y2 : real, ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt (real_pow y1 y0) (real_pow y2 y0))) /\ (~ (real_lt y1 y2)).
Definition term30 (x0 : real) := fun y0 : real => (~ (real_le x0 y0)) = (real_lt y0 x0).
Definition term56 (x0 : nat) := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt (real_pow y1 x0) (real_pow y2 x0))) -> real_lt y1 y2) y0).
Definition term116 := @eq Prop (forall y0 : real, (forall y1 : real, (~ (real_le y0 y1)) \/ (~ (real_lt y1 y0))) /\ (forall y1 : real, (real_le y0 y1) \/ (real_lt y1 y0))).
Definition term115 := @eq Prop (forall y0 : real, ((fun y1 : real => forall y2 : real, (~ (real_le y1 y2)) \/ (~ (real_lt y2 y1))) y0) /\ ((fun y1 : real => forall y2 : real, (real_le y1 y2) \/ (real_lt y2 y1)) y0)).
Definition term94 (x0 : real) := @eq Prop (forall y0 : real, ((~ (real_le x0 y0)) \/ (~ (real_lt y0 x0))) /\ ((real_le x0 y0) \/ (real_lt y0 x0))).
Definition term93 (x0 : real) := @eq Prop (forall y0 : real, ((fun y1 : real => (~ (real_le x0 y1)) \/ (~ (real_lt y1 x0))) y0) /\ ((fun y1 : real => (real_le x0 y1) \/ (real_lt y1 x0)) y0)).
Definition term180 (x0 : real) (x1 : real) (x2 : nat) := imp (~ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (real_le (real_pow x0 x2) (real_pow x1 x2)))).
Definition term178 (x0 : real) := and (real_le (real_of_num (NUMERAL 0)) x0).
Definition term57 (x0 : nat) := fun y0 : real => exists y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt (real_pow y0 x0) (real_pow y1 x0))) /\ (~ (real_lt y0 y1)).
Definition term160 (x0 : real) (x1 : real) (x2 : nat) := ~ (real_le (real_pow x0 x2) (real_pow x1 x2)).
Definition term137 (x0 : nat) := fun y0 : real => forall y1 : real, ((~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ (~ (real_le y0 y1))) \/ (real_le (real_pow y0 x0) (real_pow y1 x0)).
Definition term77 := fun y0 : real => forall y1 : real, ((~ (real_le y0 y1)) \/ (~ (real_lt y1 y0))) /\ ((real_le y0 y1) \/ (real_lt y1 y0)).
Definition term26 (x0 : nat) := fun y0 : real => forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y0 y1)) -> real_le (real_pow y0 x0) (real_pow y1 x0).
Definition term186 (x0 : real) (x1 : real) := (~ (real_le x1 x0)) -> real_lt x0 x1.
Definition term15 := (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) -> False.
Definition term71 (x0 : real) (x1 : real) := (real_le x1 x0) \/ (real_lt x0 x1).
Definition term151 (x0 : real) (x1 : real) (x2 : nat) := ~ (real_lt (real_pow x0 x2) (real_pow x1 x2)).
Definition term31 (x0 : real) := forall y0 : real, (~ (real_le x0 y0)) = (real_lt y0 x0).
Definition term52 (x0 : nat) := ~ (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt (real_pow y0 x0) (real_pow y1 x0))) -> real_lt y0 y1).
Definition term146 (x0 : real) (x1 : real) := ~ (real_lt x0 x1).
Definition term69 (x0 : real) (x1 : real) := or (real_le x0 x1).
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term51 (x0 : nat) (x1 : real) := exists y0 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_pow x1 x0) (real_pow y0 x0))) /\ (~ (real_lt x1 y0)).
Definition term183 (x0 : real) (x1 : real) := (real_le x0 x1) -> ~ (real_le x0 x1).
Definition term172 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term103 (x0 : real) := (forall y0 : real, (~ (real_le x0 y0)) \/ (~ (real_lt y0 x0))) /\ (forall y0 : real, (real_le x0 y0) \/ (real_lt y0 x0)).
Definition term140 := forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (real_le (real_of_num (NUMERAL 0)) y1)) \/ (~ (real_le y1 y2))) \/ (real_le (real_pow y1 y0) (real_pow y2 y0)).
Definition term17 := forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0).
Definition term8 := forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt (real_pow y1 y0) (real_pow y2 y0))) -> real_lt y1 y2.
Definition term167 (x0 : real) (x1 : nat) (x2 : real) := (~ (real_le x2 x0)) \/ ((real_le (real_pow x2 x1) (real_pow x0 x1)) \/ (~ (real_le (real_of_num (NUMERAL 0)) x2))).
Definition term132 (x0 : real) (x1 : real) (x2 : nat) := (~ ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 x1))) \/ (real_le (real_pow x0 x2) (real_pow x1 x2)).
Definition term181 (x0 : real) (x1 : real) (x2 : nat) := imp ((real_le (real_of_num (NUMERAL 0)) x0) /\ (~ (real_le (real_pow x0 x2) (real_pow x1 x2)))).
Definition term169 (x0 : real) (x1 : real) (x2 : nat) := @eq Prop ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ ((~ (real_le x0 x1)) \/ (real_le (real_pow x0 x2) (real_pow x1 x2)))).
Definition term97 (x0 : real) := forall y0 : real, (~ (real_le x0 y0)) \/ (~ (real_lt y0 x0)).
Definition term72 (x0 : real) (x1 : real) := and ((~ (real_le x1 x0)) \/ (~ (real_lt x0 x1))).
Definition term95 (x0 : real) := fun y0 : real => (fun y1 : real => (~ (real_le x0 y1)) \/ (~ (real_lt y1 x0))) y0.
Definition term13 := (((~ (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt (real_pow y1 y0) (real_pow y2 y0))) -> real_lt y1 y2)) -> (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) -> False) -> (~ (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt (real_pow y1 y0) (real_pow y2 y0))) -> real_lt y1 y2)) -> (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) -> False) -> (~ (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt (real_pow y1 y0) (real_pow y2 y0))) -> real_lt y1 y2)) -> (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) -> False.
Definition term109 := fun y0 : real => forall y1 : real, (real_le y0 y1) \/ (real_lt y1 y0).
Definition term37 (x0 : nat) := fun y0 : real => forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt (real_pow y0 x0) (real_pow y1 x0))) -> real_lt y0 y1.
Definition term32 := fun y0 : real => forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0).
Definition term44 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term81 (x0 : real -> Prop) (x1 : real -> Prop) := forall y0 : real, (x0 y0) /\ (x1 y0).
Definition term48 (x0 : nat) (x1 : real) (x2 : real) := ~ ((fun y0 : real => ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_pow x1 x0) (real_pow y0 x0))) -> real_lt x1 y0) x2).
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term157 (x0 : real) (x1 : real) := imp (real_lt x0 x1).
Definition term112 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le y0 y1) \/ (real_lt y1 y0)) x0.
Definition term110 (x0 : real) := (fun y0 : real => forall y1 : real, (~ (real_le y0 y1)) \/ (~ (real_lt y1 y0))) x0.
Definition term24 (x0 : real) (x1 : nat) := fun y0 : real => ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 y0)) -> real_le (real_pow x0 x1) (real_pow y0 x1).
Definition term131 (x0 : real) (x1 : real) := or ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_le x0 x1))).
Definition term128 (x0 : real) := real_le (real_of_num (NUMERAL 0)) x0.
Definition term42 (x0 : real) (x1 : real) (x2 : nat) := (real_le (real_of_num (NUMERAL 0)) x1) /\ (real_lt (real_pow x0 x2) (real_pow x1 x2)).
Definition term9 := (~ (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt (real_pow y1 y0) (real_pow y2 y0))) -> real_lt y1 y2)) -> False.
Definition term101 (x0 : real) := forall y0 : real, (fun y1 : real => (real_le x0 y1) \/ (real_lt y1 x0)) y0.
Definition term96 (x0 : real) := forall y0 : real, (fun y1 : real => (~ (real_le x0 y1)) \/ (~ (real_lt y1 x0))) y0.
Definition term34 (x0 : nat) (x1 : real) (x2 : real) := ((real_le (real_of_num (NUMERAL 0)) x2) /\ (real_lt (real_pow x1 x0) (real_pow x2 x0))) -> real_lt x1 x2.
Definition term165 (x0 : real) (x1 : nat) (x2 : real) := (real_le (real_pow x2 x1) (real_pow x0 x1)) \/ (~ (real_le (real_of_num (NUMERAL 0)) x2)).
Definition term64 := fun y0 : nat => ~ ((fun y1 : nat => forall y2 : real, forall y3 : real, ((real_le (real_of_num (NUMERAL 0)) y3) /\ (real_lt (real_pow y2 y1) (real_pow y3 y1))) -> real_lt y2 y3) y0).
Definition term40 (x0 : nat) (x1 : real) (x2 : real) := ~ (((real_le (real_of_num (NUMERAL 0)) x2) /\ (real_lt (real_pow x1 x0) (real_pow x2 x0))) -> real_lt x1 x2).
Definition term114 := fun y0 : real => ((fun y1 : real => forall y2 : real, (~ (real_le y1 y2)) \/ (~ (real_lt y2 y1))) y0) /\ ((fun y1 : real => forall y2 : real, (real_le y1 y2) \/ (real_lt y2 y1)) y0).
Definition term153 (x0 : real) (x1 : real) := (~ (~ (real_lt x1 x0))) -> ~ (real_le x0 x1).
Definition term174 (x0 : real) (x1 : real) (x2 : nat) := ~ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (real_le (real_pow x0 x2) (real_pow x1 x2))).
Definition term14 := (((~ (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt (real_pow y1 y0) (real_pow y2 y0))) -> real_lt y1 y2)) -> (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) -> False) -> (~ (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt (real_pow y1 y0) (real_pow y2 y0))) -> real_lt y1 y2)) -> (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) -> False) -> ((~ (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt (real_pow y1 y0) (real_pow y2 y0))) -> real_lt y1 y2)) -> (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) -> False) -> (~ (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt (real_pow y1 y0) (real_pow y2 y0))) -> real_lt y1 y2)) -> (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) -> False.
Definition term166 (x0 : real) (x1 : real) := or (~ (real_le x0 x1)).
Definition term177 (x0 : real) := and (~ (~ (real_le (real_of_num (NUMERAL 0)) x0))).
Definition term1 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term91 (x0 : real) (x1 : real) := ((fun y0 : real => (~ (real_le x0 y0)) \/ (~ (real_lt y0 x0))) x1) /\ ((fun y0 : real => (real_le x0 y0) \/ (real_lt y0 x0)) x1).
Definition term142 (x0 : nat) (x1 : real) := (fun y0 : real => forall y1 : real, ((~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ (~ (real_le y0 y1))) \/ (real_le (real_pow y0 x0) (real_pow y1 x0))) x1.
Definition term54 (x0 : nat) (x1 : real) := (fun y0 : real => forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt (real_pow y0 x0) (real_pow y1 x0))) -> real_lt y0 y1) x1.
Definition term161 (x0 : real) (x1 : real) (x2 : nat) := (real_le (real_pow x0 x2) (real_pow x1 x2)) -> ~ (real_le (real_pow x0 x2) (real_pow x1 x2)).
Definition term87 (x0 : real) (x1 : real) := (fun y0 : real => (~ (real_le x0 y0)) \/ (~ (real_lt y0 x0))) x1.
Definition term63 (x0 : nat) := ~ ((fun y0 : nat => forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt (real_pow y1 y0) (real_pow y2 y0))) -> real_lt y1 y2) x0).
Definition term85 (x0 : real) := fun y0 : real => (~ (real_le x0 y0)) \/ (~ (real_lt y0 x0)).
Definition term135 (x0 : real) (x1 : nat) := fun y0 : real => ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_le x0 y0))) \/ (real_le (real_pow x0 x1) (real_pow y0 x1)).
Definition term155 (x0 : real) (x1 : real) := ~ (~ (real_lt x0 x1)).
Definition term55 (x0 : nat) (x1 : real) := ~ ((fun y0 : real => forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt (real_pow y0 x0) (real_pow y1 x0))) -> real_lt y0 y1) x1).
Definition term35 (x0 : nat) (x1 : real) := fun y0 : real => ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_pow x1 x0) (real_pow y0 x0))) -> real_lt x1 y0.
Definition term149 (x0 : real) (x1 : real) (x2 : nat) := real_lt (real_pow x0 x2) (real_pow x1 x2).
Definition term29 (x0 : real) (x1 : real) := ~ (real_le x0 x1).
Definition term88 (x0 : real) (x1 : real) := (~ (real_le x1 x0)) \/ (~ (real_lt x0 x1)).
Definition term105 := forall y0 : real, (forall y1 : real, (~ (real_le y0 y1)) \/ (~ (real_lt y1 y0))) /\ (forall y1 : real, (real_le y0 y1) \/ (real_lt y1 y0)).
Definition term36 (x0 : nat) (x1 : real) := forall y0 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_pow x1 x0) (real_pow y0 x0))) -> real_lt x1 y0.
Definition term61 := exists y0 : nat, ~ ((fun y1 : nat => forall y2 : real, forall y3 : real, ((real_le (real_of_num (NUMERAL 0)) y3) /\ (real_lt (real_pow y2 y1) (real_pow y3 y1))) -> real_lt y2 y3) y0).
Definition term123 := forall y0 : real, (fun y1 : real => forall y2 : real, (real_le y1 y2) \/ (real_lt y2 y1)) y0.
Definition term118 := forall y0 : real, (fun y1 : real => forall y2 : real, (~ (real_le y1 y2)) \/ (~ (real_lt y2 y1))) y0.
Definition term184 (x0 : real) (x1 : real) := (real_lt x1 x0) \/ (real_le x0 x1).
Definition term113 (x0 : real) := ((fun y0 : real => forall y1 : real, (~ (real_le y0 y1)) \/ (~ (real_lt y1 y0))) x0) /\ ((fun y0 : real => forall y1 : real, (real_le y0 y1) \/ (real_lt y1 y0)) x0).
Definition term20 := (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0)) -> ~ (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)).
Definition term92 (x0 : real) := fun y0 : real => ((fun y1 : real => (~ (real_le x0 y1)) \/ (~ (real_lt y1 x0))) y0) /\ ((fun y1 : real => (real_le x0 y1) \/ (real_lt y1 x0)) y0).
Definition term100 (x0 : real) := fun y0 : real => (fun y1 : real => (real_le x0 y1) \/ (real_lt y1 x0)) y0.
Definition term133 (x0 : real) (x1 : real) (x2 : nat) := ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_le x0 x1))) \/ (real_le (real_pow x0 x2) (real_pow x1 x2)).
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term49 (x0 : nat) (x1 : real) := fun y0 : real => ~ ((fun y1 : real => ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt (real_pow x1 x0) (real_pow y1 x0))) -> real_lt x1 y1) y0).
Definition term82 (x0 : real -> Prop) (x1 : real -> Prop) := (forall y0 : real, x0 y0) /\ (forall y0 : real, x1 y0).
Definition term68 (x0 : real) (x1 : real) := or (~ (~ (real_le x0 x1))).
Definition term79 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term66 := exists y0 : nat, exists y1 : real, exists y2 : real, ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt (real_pow y1 y0) (real_pow y2 y0))) /\ (~ (real_lt y1 y2)).
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term136 (x0 : real) (x1 : nat) := forall y0 : real, ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_le x0 y0))) \/ (real_le (real_pow x0 x1) (real_pow y0 x1)).
Definition term47 (x0 : nat) (x1 : real) (x2 : real) := (fun y0 : real => ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_pow x1 x0) (real_pow y0 x0))) -> real_lt x1 y0) x2.
Definition term159 (x0 : real) (x1 : real) (x2 : nat) := (real_lt (real_pow x1 x2) (real_pow x0 x2)) -> ~ (real_le (real_pow x0 x2) (real_pow x1 x2)).
Definition term182 (x0 : nat) (x1 : real) (x2 : real) := ((real_le (real_of_num (NUMERAL 0)) x1) /\ (~ (real_le (real_pow x1 x0) (real_pow x2 x0)))) -> ~ (real_le x1 x2).
Definition term89 (x0 : real) (x1 : real) := and ((fun y0 : real => (~ (real_le x0 y0)) \/ (~ (real_lt y0 x0))) x1).
Definition term126 (x0 : real) (x1 : real) := ~ ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 x1)).
Definition term176 (x0 : real) := ~ (~ (real_le (real_of_num (NUMERAL 0)) x0)).
Definition term11 := (~ (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt (real_pow y1 y0) (real_pow y2 y0))) -> real_lt y1 y2)) -> (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) -> False.
Definition term60 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term179 (x0 : real) (x1 : real) (x2 : nat) := (real_le (real_of_num (NUMERAL 0)) x0) /\ (~ (real_le (real_pow x0 x2) (real_pow x1 x2))).
Definition term106 := forall y0 : real, ((fun y1 : real => forall y2 : real, (~ (real_le y1 y2)) \/ (~ (real_lt y2 y1))) y0) /\ ((fun y1 : real => forall y2 : real, (real_le y1 y2) \/ (real_lt y2 y1)) y0).
Definition term83 (x0 : real) := forall y0 : real, ((fun y1 : real => (~ (real_le x0 y1)) \/ (~ (real_lt y1 x0))) y0) /\ ((fun y1 : real => (real_le x0 y1) \/ (real_lt y1 x0)) y0).
Definition term163 (x0 : real) (x1 : real) (x2 : nat) := (~ (real_le x0 x1)) \/ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (real_le (real_pow x0 x2) (real_pow x1 x2))).
Definition term134 (x0 : real) (x1 : real) := (real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 x1).
Definition term90 (x0 : real) (x1 : real) := (fun y0 : real => (real_le x0 y0) \/ (real_lt y0 x0)) x1.
Definition term21 := imp (~ (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt (real_pow y1 y0) (real_pow y2 y0))) -> real_lt y1 y2)).
Definition term162 (x0 : Prop) := x0 -> ~ x0.
Definition term108 := fun y0 : real => forall y1 : real, (~ (real_le y0 y1)) \/ (~ (real_lt y1 y0)).
Definition term156 (x0 : real) (x1 : real) := imp (~ (~ (real_lt x0 x1))).
