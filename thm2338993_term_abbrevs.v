Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term113 := (~ False) -> False.
Definition term114 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (~ ((exists y2 : a0, (y1 y2) /\ (y0 y2)) = (~ (forall y2 : a0, (y1 y2) -> ~ (y0 y2))))) -> False) x0.
Definition term120 := fun y0 : int => int_le (int_of_num (NUMERAL 0)) y0.
Definition term105 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (((x0 y0) /\ (x1 y0)) /\ (forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 y1)))) \/ ((forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 y1))) /\ ((x0 y0) /\ (x1 y0))).
Definition term85 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 y1))) /\ ((x0 y0) /\ (x1 y0)).
Definition term133 (x0 : int) := imp (int_le (int_of_num (NUMERAL 0)) x0).
Definition term146 (x0 : int -> Prop) (x1 : int) := (fun y0 : int => (x0 y0) /\ (forall y1 : int, ((int_le (int_of_num (NUMERAL 0)) y1) /\ (x0 y1)) -> int_le y0 y1)) x1.
Definition term104 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => ((fun y1 : a0 => ((x0 y1) /\ (x1 y1)) /\ (forall y2 : a0, (~ (x0 y2)) \/ (~ (x1 y2)))) y0) \/ ((fun y1 : a0 => (forall y2 : a0, (~ (x0 y2)) \/ (~ (x1 y2))) /\ ((x0 y1) /\ (x1 y1))) y0).
Definition term9 (x0 : Prop) := ~ (~ x0).
Definition term100 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := or ((fun y0 : a0 => ((x0 y0) /\ (x1 y0)) /\ (forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 y1)))) x2).
Definition term11 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => (exists y1 : a0, (y0 y1) /\ (x0 y1)) = (~ (forall y1 : a0, (y0 y1) -> ~ (x0 y1))).
Definition term21 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (x0 x2) /\ (x1 x2).
Definition term18 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (x0 x2) -> ~ (x1 x2).
Definition term47 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and (~ (exists y0 : a0, (x0 y0) /\ (x1 y0))).
Definition term51 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and (exists y0 : a0, (x0 y0) /\ (x1 y0)).
Definition term87 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term102 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ((fun y0 : a0 => ((x0 y0) /\ (x1 y0)) /\ (forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 y1)))) x2) \/ ((fun y0 : a0 => (forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 y1))) /\ ((x0 y0) /\ (x1 y0))) x2).
Definition term136 (x0 : int -> Prop) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x1) -> ~ (x0 x1).
Definition term39 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (x0 x1).
Definition term26 (a0 : Type') (x0 : a0 -> Prop) := ~ (ex x0).
Definition term126 (x0 : int -> Prop) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x1) /\ (x0 x1).
Definition term40 (a0 : Type') (x0 : a0 -> Prop) := ~ (all x0).
Definition term76 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term132 (x0 : int) := imp ((fun y0 : int => int_le (int_of_num (NUMERAL 0)) y0) x0).
Definition term94 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := or (exists y0 : a0, (fun y1 : a0 => ((x0 y1) /\ (x1 y1)) /\ (forall y2 : a0, (~ (x0 y2)) \/ (~ (x1 y2)))) y0).
Definition term137 (x0 : int -> Prop) := fun y0 : int => ((fun y1 : int => int_le (int_of_num (NUMERAL 0)) y1) y0) -> ~ (x0 y0).
Definition term38 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ~ ((x0 x2) -> ~ (x1 x2)).
Definition term35 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (~ (x0 x1)).
Definition term147 (x0 : int -> Prop) (x1 : int) := (x0 x1) /\ (forall y0 : int, ((int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0)) -> int_le x1 y0).
Definition term107 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (fun y0 : a0 => (~ (x0 y0)) \/ (~ (x1 y0))) x2.
Definition term69 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := ((fun y0 : a0 => (x1 y0) /\ (x2 y0)) x0) /\ (forall y0 : a0, (~ (x1 y0)) \/ (~ (x2 y0))).
Definition term75 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term110 (x0 : Prop) (x1 : Prop) := (~ x0) \/ (~ x1).
Definition term109 (x0 : Prop) := (~ x0) -> x0.
Definition term89 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, (fun y1 : a0 => ((x0 y1) /\ (x1 y1)) /\ (forall y2 : a0, (~ (x0 y2)) \/ (~ (x1 y2)))) y0) \/ (exists y0 : a0, (fun y1 : a0 => (forall y2 : a0, (~ (x0 y2)) \/ (~ (x1 y2))) /\ ((x0 y1) /\ (x1 y1))) y0).
Definition term49 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (exists y0 : a0, (x0 y0) /\ (x1 y0))) /\ (~ (forall y0 : a0, (x0 y0) -> ~ (x1 y0))).
Definition term121 (x0 : int) := (fun y0 : int => int_le (int_of_num (NUMERAL 0)) y0) x0.
Definition term20 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) -> ~ (x1 y0).
Definition term111 (x0 : Prop) (x1 : Prop) := ~ (x0 /\ x1).
Definition term86 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, ((x0 y0) /\ (x1 y0)) /\ (forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 y1)))) \/ (exists y0 : a0, (forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 y1))) /\ ((x0 y0) /\ (x1 y0))).
Definition term139 (x0 : int -> Prop) := forall y0 : int, ((fun y1 : int => int_le (int_of_num (NUMERAL 0)) y1) y0) -> ~ (x0 y0).
Definition term56 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((exists y0 : a0, (x0 y0) /\ (x1 y0)) /\ (~ (~ (forall y0 : a0, (x0 y0) -> ~ (x1 y0))))) \/ ((~ (exists y0 : a0, (x0 y0) /\ (x1 y0))) /\ (~ (forall y0 : a0, (x0 y0) -> ~ (x1 y0)))).
Definition term143 (x0 : int -> Prop) := exists y0 : int, ((fun y1 : int => int_le (int_of_num (NUMERAL 0)) y1) y0) /\ ((fun y1 : int => (x0 y1) /\ (forall y2 : int, ((int_le (int_of_num (NUMERAL 0)) y2) /\ (x0 y2)) -> int_le y1 y2)) y0).
Definition term97 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (fun y1 : a0 => (forall y2 : a0, (~ (x0 y2)) \/ (~ (x1 y2))) /\ ((x0 y1) /\ (x1 y1))) y0.
Definition term93 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (fun y1 : a0 => ((x0 y1) /\ (x1 y1)) /\ (forall y2 : a0, (~ (x0 y2)) \/ (~ (x1 y2)))) y0.
Definition term63 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (fun y1 : a0 => (x0 y1) /\ (x1 y1)) y0.
Definition term45 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => ~ ((fun y1 : a0 => (x0 y1) -> ~ (x1 y1)) y0).
Definition term32 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => ~ ((fun y1 : a0 => (x0 y1) /\ (x1 y1)) y0).
Definition term28 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (exists y0 : a0, (x0 y0) /\ (x1 y0)).
Definition term55 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := or ((exists y0 : a0, (x0 y0) /\ (x1 y0)) /\ (forall y0 : a0, (~ (x0 y0)) \/ (~ (x1 y0)))).
Definition term103 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (((x0 x2) /\ (x1 x2)) /\ (forall y0 : a0, (~ (x0 y0)) \/ (~ (x1 y0)))) \/ ((forall y0 : a0, (~ (x0 y0)) \/ (~ (x1 y0))) /\ ((x0 x2) /\ (x1 x2))).
Definition term140 (x0 : int -> Prop) := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> ~ (x0 y0).
Definition term123 (x0 : int) := and ((fun y0 : int => int_le (int_of_num (NUMERAL 0)) y0) x0).
Definition term149 (x0 : int -> Prop) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x1) /\ ((x0 x1) /\ (forall y0 : int, ((int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0)) -> int_le x1 y0)).
Definition term60 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, (fun y1 : a0 => (x0 y1) /\ (x1 y1)) y0) /\ (forall y0 : a0, (~ (x0 y0)) \/ (~ (x1 y0))).
Definition term61 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, ((fun y1 : a0 => (x0 y1) /\ (x1 y1)) y0) /\ (forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 y1))).
Definition term13 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (exists y1 : a0, (y0 y1) /\ (x0 y1)) = (~ (forall y1 : a0, (y0 y1) -> ~ (x0 y1))).
Definition term23 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop (exists y0 : a0, (x0 y0) /\ (x1 y0)).
Definition term50 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, (~ (x0 y0)) \/ (~ (x1 y0))) /\ (exists y0 : a0, (x0 y0) /\ (x1 y0)).
Definition term53 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, (x0 y0) /\ (x1 y0)) /\ (forall y0 : a0, (~ (x0 y0)) \/ (~ (x1 y0))).
Definition term2 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (forall y0 : a0, (x0 y0) -> ~ (x1 y0)).
Definition term27 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, ~ (x0 y0).
Definition term5 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((~ ((exists y0 : a0, (x0 y0) /\ (x1 y0)) = (~ (forall y0 : a0, (x0 y0) -> ~ (x1 y0))))) -> False) -> (~ ((exists y0 : a0, (x0 y0) /\ (x1 y0)) = (~ (forall y0 : a0, (x0 y0) -> ~ (x1 y0))))) -> False.
Definition term68 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := and ((x0 x2) /\ (x1 x2)).
Definition term127 (x0 : int -> Prop) := fun y0 : int => ((fun y1 : int => int_le (int_of_num (NUMERAL 0)) y1) y0) /\ (x0 y0).
Definition term154 (x0 : int -> Prop) := @eq Prop (exists y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) /\ ((x0 y0) /\ (forall y1 : int, ((int_le (int_of_num (NUMERAL 0)) y1) /\ (x0 y1)) -> int_le y0 y1))).
Definition term153 (x0 : int -> Prop) := @eq Prop (exists y0 : int, ((fun y1 : int => int_le (int_of_num (NUMERAL 0)) y1) y0) /\ ((fun y1 : int => (x0 y1) /\ (forall y2 : int, ((int_le (int_of_num (NUMERAL 0)) y2) /\ (x0 y2)) -> int_le y1 y2)) y0)).
Definition term131 (x0 : int -> Prop) := @eq Prop (exists y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0)).
Definition term130 (x0 : int -> Prop) := @eq Prop (exists y0 : int, ((fun y1 : int => int_le (int_of_num (NUMERAL 0)) y1) y0) /\ (x0 y0)).
Definition term4 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ ((exists y0 : a0, (x0 y0) /\ (x1 y0)) = (~ (forall y0 : a0, (x0 y0) -> ~ (x1 y0)))).
Definition term41 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, ~ (x0 y0).
Definition term16 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (~ ((exists y2 : a0, (y1 y2) /\ (y0 y2)) = (~ (forall y2 : a0, (y1 y2) -> ~ (y0 y2))))) -> False.
Definition term159 (x0 : int -> Prop) := fun y0 : int => ((fun y1 : int => int_le (int_of_num (NUMERAL 0)) y1) y0) -> ~ ((fun y1 : int => (x0 y1) /\ (forall y2 : int, ((int_le (int_of_num (NUMERAL 0)) y2) /\ (x0 y2)) -> int_le y1 y2)) y0).
Definition term96 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (fun y1 : a0 => (forall y2 : a0, (~ (x0 y2)) \/ (~ (x1 y2))) /\ ((x0 y1) /\ (x1 y1))) y0.
Definition term34 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (~ (x0 y0)) \/ (~ (x1 y0)).
Definition term145 (x0 : int -> Prop) := fun y0 : int => (x0 y0) /\ (forall y1 : int, ((int_le (int_of_num (NUMERAL 0)) y1) /\ (x0 y1)) -> int_le y0 y1).
Definition term59 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term36 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (x0 x1).
Definition term106 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (((x0 y0) /\ (x1 y0)) /\ (forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 y1)))) \/ ((forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 y1))) /\ ((x0 y0) /\ (x1 y0))).
Definition term83 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 y1))) /\ ((fun y1 : a0 => (x0 y1) /\ (x1 y1)) y0).
Definition term163 (x0 : int -> Prop) := ~ (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> ~ ((x0 y0) /\ (forall y1 : int, ((int_le (int_of_num (NUMERAL 0)) y1) /\ (x0 y1)) -> int_le y0 y1))).
Definition term144 (x0 : int -> Prop) := ~ (forall y0 : int, ((fun y1 : int => int_le (int_of_num (NUMERAL 0)) y1) y0) -> ~ ((fun y1 : int => (x0 y1) /\ (forall y2 : int, ((int_le (int_of_num (NUMERAL 0)) y2) /\ (x0 y2)) -> int_le y1 y2)) y0)).
Definition term141 (x0 : int -> Prop) := ~ (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> ~ (x0 y0)).
Definition term119 (x0 : int -> Prop) := ~ (forall y0 : int, ((fun y1 : int => int_le (int_of_num (NUMERAL 0)) y1) y0) -> ~ (x0 y0)).
Definition term117 (x0 : int -> Prop) (x1 : int -> Prop) := ~ (forall y0 : int, (x0 y0) -> ~ (x1 y0)).
Definition term152 (x0 : int -> Prop) := exists y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) /\ ((x0 y0) /\ (forall y1 : int, ((int_le (int_of_num (NUMERAL 0)) y1) /\ (x0 y1)) -> int_le y0 y1)).
Definition term151 (x0 : int -> Prop) := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) /\ ((x0 y0) /\ (forall y1 : int, ((int_le (int_of_num (NUMERAL 0)) y1) /\ (x0 y1)) -> int_le y0 y1)).
Definition term158 (x0 : int -> Prop) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x1) -> ~ ((x0 x1) /\ (forall y0 : int, ((int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0)) -> int_le x1 y0)).
Definition term156 (x0 : int -> Prop) (x1 : int) := ~ ((x0 x1) /\ (forall y0 : int, ((int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0)) -> int_le x1 y0)).
Definition term95 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (fun y0 : a0 => (forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 y1))) /\ ((x0 y0) /\ (x1 y0))) x2.
Definition term138 (x0 : int -> Prop) := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) -> ~ (x0 y0).
Definition term129 (x0 : int -> Prop) := exists y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0).
Definition term78 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 y1))) /\ ((fun y1 : a0 => (x0 y1) /\ (x1 y1)) y0).
Definition term150 (x0 : int -> Prop) := fun y0 : int => ((fun y1 : int => int_le (int_of_num (NUMERAL 0)) y1) y0) /\ ((fun y1 : int => (x0 y1) /\ (forall y2 : int, ((int_le (int_of_num (NUMERAL 0)) y2) /\ (x0 y2)) -> int_le y1 y2)) y0).
Definition term30 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (fun y0 : a0 => (x0 y0) /\ (x1 y0)) x2.
Definition term46 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (~ (forall y0 : a0, (x0 y0) -> ~ (x1 y0))).
Definition term8 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (~ ((exists y0 : a0, (x0 y0) /\ (x1 y0)) = (~ (forall y0 : a0, (x0 y0) -> ~ (x1 y0))))).
Definition term81 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (forall y0 : a0, (~ (x0 y0)) \/ (~ (x1 y0))) /\ ((fun y0 : a0 => (x0 y0) /\ (x1 y0)) x2).
Definition term135 (x0 : int -> Prop) (x1 : int) := ((fun y0 : int => int_le (int_of_num (NUMERAL 0)) y0) x1) -> ~ (x0 x1).
Definition term134 (x0 : int -> Prop) (x1 : int) := ~ (x0 x1).
Definition term115 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ ((exists y1 : a0, (y0 y1) /\ (x0 y1)) = (~ (forall y1 : a0, (y0 y1) -> ~ (x0 y1))))) -> False) x1.
Definition term52 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, (x0 y0) /\ (x1 y0)) /\ (~ (~ (forall y0 : a0, (x0 y0) -> ~ (x1 y0)))).
Definition term6 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (((~ ((exists y0 : a0, (x0 y0) /\ (x1 y0)) = (~ (forall y0 : a0, (x0 y0) -> ~ (x1 y0))))) -> False) -> (~ ((exists y0 : a0, (x0 y0) /\ (x1 y0)) = (~ (forall y0 : a0, (x0 y0) -> ~ (x1 y0))))) -> False) -> (~ ((exists y0 : a0, (x0 y0) /\ (x1 y0)) = (~ (forall y0 : a0, (x0 y0) -> ~ (x1 y0))))) -> False.
Definition term12 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (~ ((exists y1 : a0, (y0 y1) /\ (x0 y1)) = (~ (forall y1 : a0, (y0 y1) -> ~ (x0 y1))))) -> False.
Definition term118 (x0 : int -> Prop) := exists y0 : int, ((fun y1 : int => int_le (int_of_num (NUMERAL 0)) y1) y0) /\ (x0 y0).
Definition term17 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (exists y2 : a0, (y1 y2) /\ (y0 y2)) = (~ (forall y2 : a0, (y1 y2) -> ~ (y0 y2))).
Definition term74 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := or (exists y0 : a0, ((x0 y0) /\ (x1 y0)) /\ (forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 y1)))).
Definition term70 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := ((x1 x0) /\ (x2 x0)) /\ (forall y0 : a0, (~ (x1 y0)) \/ (~ (x2 y0))).
Definition term112 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ((x0 x2) /\ (x1 x2)) -> False.
Definition term155 (x0 : int -> Prop) (x1 : int) := ~ ((fun y0 : int => (x0 y0) /\ (forall y1 : int, ((int_le (int_of_num (NUMERAL 0)) y1) /\ (x0 y1)) -> int_le y0 y1)) x1).
Definition term67 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := and ((fun y0 : a0 => (x0 y0) /\ (x1 y0)) x2).
Definition term91 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (fun y0 : a0 => ((x0 y0) /\ (x1 y0)) /\ (forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 y1)))) x2.
Definition term124 (x0 : int) := and (int_le (int_of_num (NUMERAL 0)) x0).
Definition term57 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((exists y0 : a0, (x0 y0) /\ (x1 y0)) /\ (forall y0 : a0, (~ (x0 y0)) \/ (~ (x1 y0)))) \/ ((forall y0 : a0, (~ (x0 y0)) \/ (~ (x1 y0))) /\ (exists y0 : a0, (x0 y0) /\ (x1 y0))).
Definition term48 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and (forall y0 : a0, (~ (x0 y0)) \/ (~ (x1 y0))).
Definition term14 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (~ ((exists y2 : a0, (y1 y2) /\ (y0 y2)) = (~ (forall y2 : a0, (y1 y2) -> ~ (y0 y2))))) -> False.
Definition term77 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, (~ (x0 y0)) \/ (~ (x1 y0))) /\ (exists y0 : a0, (fun y1 : a0 => (x0 y1) /\ (x1 y1)) y0).
Definition term31 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ~ ((fun y0 : a0 => (x0 y0) /\ (x1 y0)) x2).
Definition term128 (x0 : int -> Prop) := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0).
Definition term116 (x0 : int -> Prop) (x1 : int -> Prop) := exists y0 : int, (x0 y0) /\ (x1 y0).
Definition term42 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, ~ ((fun y1 : a0 => (x0 y1) -> ~ (x1 y1)) y0).
Definition term142 (x0 : int -> Prop) := @eq Prop (~ (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> ~ (x0 y0))).
Definition term3 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ ((exists y0 : a0, (x0 y0) /\ (x1 y0)) = (~ (forall y0 : a0, (x0 y0) -> ~ (x1 y0))))) -> False.
Definition term161 (x0 : int -> Prop) := forall y0 : int, ((fun y1 : int => int_le (int_of_num (NUMERAL 0)) y1) y0) -> ~ ((fun y1 : int => (x0 y1) /\ (forall y2 : int, ((int_le (int_of_num (NUMERAL 0)) y2) /\ (x0 y2)) -> int_le y1 y2)) y0).
Definition term72 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => ((x0 y0) /\ (x1 y0)) /\ (forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 y1))).
Definition term71 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => ((fun y1 : a0 => (x0 y1) /\ (x1 y1)) y0) /\ (forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 y1))).
Definition term160 (x0 : int -> Prop) := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) -> ~ ((x0 y0) /\ (forall y1 : int, ((int_le (int_of_num (NUMERAL 0)) y1) /\ (x0 y1)) -> int_le y0 y1)).
Definition term62 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (fun y1 : a0 => (x0 y1) /\ (x1 y1)) y0.
Definition term25 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ (x0 x2)) \/ (~ (x1 x2)).
Definition term90 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, ((fun y1 : a0 => ((x0 y1) /\ (x1 y1)) /\ (forall y2 : a0, (~ (x0 y2)) \/ (~ (x1 y2)))) y0) \/ ((fun y1 : a0 => (forall y2 : a0, (~ (x0 y2)) \/ (~ (x1 y2))) /\ ((x0 y1) /\ (x1 y1))) y0).
Definition term84 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 y1))) /\ ((x0 y0) /\ (x1 y0)).
Definition term162 (x0 : int -> Prop) := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> ~ ((x0 y0) /\ (forall y1 : int, ((int_le (int_of_num (NUMERAL 0)) y1) /\ (x0 y1)) -> int_le y0 y1)).
Definition term15 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (exists y2 : a0, (y1 y2) /\ (y0 y2)) = (~ (forall y2 : a0, (y1 y2) -> ~ (y0 y2))).
Definition term37 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (x0 x2) /\ (~ (~ (x1 x2))).
Definition term43 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (fun y0 : a0 => (x0 y0) -> ~ (x1 y0)) x2.
Definition term19 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (x0 y0) -> ~ (x1 y0).
Definition term80 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop ((forall y0 : a0, (~ (x0 y0)) \/ (~ (x1 y0))) /\ (exists y0 : a0, (x0 y0) /\ (x1 y0))).
Definition term79 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop ((forall y0 : a0, (~ (x0 y0)) \/ (~ (x1 y0))) /\ (exists y0 : a0, (fun y1 : a0 => (x0 y1) /\ (x1 y1)) y0)).
Definition term1 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) /\ (x1 y0).
Definition term66 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop ((exists y0 : a0, (x0 y0) /\ (x1 y0)) /\ (forall y0 : a0, (~ (x0 y0)) \/ (~ (x1 y0)))).
Definition term65 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop ((exists y0 : a0, (fun y1 : a0 => (x0 y1) /\ (x1 y1)) y0) /\ (forall y0 : a0, (~ (x0 y0)) \/ (~ (x1 y0)))).
Definition term7 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (((~ ((exists y0 : a0, (x0 y0) /\ (x1 y0)) = (~ (forall y0 : a0, (x0 y0) -> ~ (x1 y0))))) -> False) -> (~ ((exists y0 : a0, (x0 y0) /\ (x1 y0)) = (~ (forall y0 : a0, (x0 y0) -> ~ (x1 y0))))) -> False) -> ((~ ((exists y0 : a0, (x0 y0) /\ (x1 y0)) = (~ (forall y0 : a0, (x0 y0) -> ~ (x1 y0))))) -> False) -> (~ ((exists y0 : a0, (x0 y0) /\ (x1 y0)) = (~ (forall y0 : a0, (x0 y0) -> ~ (x1 y0))))) -> False.
Definition term92 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (fun y1 : a0 => ((x0 y1) /\ (x1 y1)) /\ (forall y2 : a0, (~ (x0 y2)) \/ (~ (x1 y2)))) y0.
Definition term10 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => (~ ((exists y1 : a0, (y0 y1) /\ (x0 y1)) = (~ (forall y1 : a0, (y0 y1) -> ~ (x0 y1))))) -> False.
Definition term54 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := or ((exists y0 : a0, (x0 y0) /\ (x1 y0)) /\ (~ (~ (forall y0 : a0, (x0 y0) -> ~ (x1 y0))))).
Definition term122 (x0 : int) := int_le (int_of_num (NUMERAL 0)) x0.
Definition term33 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (~ (x0 y0)) \/ (~ (x1 y0)).
Definition term58 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term157 (x0 : int -> Prop) (x1 : int) := ((fun y0 : int => int_le (int_of_num (NUMERAL 0)) y0) x1) -> ~ ((fun y0 : int => (x0 y0) /\ (forall y1 : int, ((int_le (int_of_num (NUMERAL 0)) y1) /\ (x0 y1)) -> int_le y0 y1)) x1).
Definition term64 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and (exists y0 : a0, (fun y1 : a0 => (x0 y1) /\ (x1 y1)) y0).
Definition term29 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, ~ ((fun y1 : a0 => (x0 y1) /\ (x1 y1)) y0).
Definition term108 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (x0 x1)) -> x0 x1.
Definition term88 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term24 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ~ ((x0 x2) /\ (x1 x2)).
Definition term148 (x0 : int -> Prop) (x1 : int) := ((fun y0 : int => int_le (int_of_num (NUMERAL 0)) y0) x1) /\ ((fun y0 : int => (x0 y0) /\ (forall y1 : int, ((int_le (int_of_num (NUMERAL 0)) y1) /\ (x0 y1)) -> int_le y0 y1)) x1).
Definition term101 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := or (((x1 x0) /\ (x2 x0)) /\ (forall y0 : a0, (~ (x1 y0)) \/ (~ (x2 y0)))).
Definition term22 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (x0 y0) /\ (x1 y0).
Definition term73 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, ((x0 y0) /\ (x1 y0)) /\ (forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 y1))).
Definition term82 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (forall y0 : a0, (~ (x0 y0)) \/ (~ (x1 y0))) /\ ((x0 x2) /\ (x1 x2)).
Definition term44 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ~ ((fun y0 : a0 => (x0 y0) -> ~ (x1 y0)) x2).
Definition term125 (x0 : int -> Prop) (x1 : int) := ((fun y0 : int => int_le (int_of_num (NUMERAL 0)) y0) x1) /\ (x0 x1).
Definition term99 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop ((exists y0 : a0, ((x0 y0) /\ (x1 y0)) /\ (forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 y1)))) \/ (exists y0 : a0, (forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 y1))) /\ ((x0 y0) /\ (x1 y0)))).
Definition term98 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop ((exists y0 : a0, (fun y1 : a0 => ((x0 y1) /\ (x1 y1)) /\ (forall y2 : a0, (~ (x0 y2)) \/ (~ (x1 y2)))) y0) \/ (exists y0 : a0, (fun y1 : a0 => (forall y2 : a0, (~ (x0 y2)) \/ (~ (x1 y2))) /\ ((x0 y1) /\ (x1 y1))) y0)).
