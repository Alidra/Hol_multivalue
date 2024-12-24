Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term19 := @eq Prop (~ False).
Definition term8 (x0 : Prop) := fun y0 : Prop => (y0 = x0) = ((~ y0) = (~ x0)).
Definition term74 (x0 : int -> Prop) := ~ ((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> ~ (x0 y0)) = (forall y0 : int, ~ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0)))).
Definition term90 (x0 : int -> Prop) := exists y0 : int, ~ (x0 y0).
Definition term89 (x0 : int -> Prop) := ~ (all x0).
Definition term177 := (~ False) -> False.
Definition term17 (x0 : Prop) := @eq Prop (False = x0).
Definition term52 (x0 : int -> Prop) := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) -> (fun y1 : int => ~ (x0 y1)) y0.
Definition term165 (x0 : int) (x1 : int -> Prop) := ((forall y0 : int, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (~ (x1 y0))) /\ ((int_le (int_of_num (NUMERAL 0)) x0) /\ (x1 x0))) \/ (((int_le (int_of_num (NUMERAL 0)) x0) /\ (x1 x0)) /\ (forall y0 : int, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (~ (x1 y0)))).
Definition term49 (x0 : int) := imp (int_le (int_of_num (NUMERAL 0)) x0).
Definition term167 (x0 : int -> Prop) := fun y0 : int => ((forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (~ (x0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0))) \/ (((int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0)) /\ (forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (~ (x0 y1)))).
Definition term16 (x0 : Prop) := ~ (~ x0).
Definition term3 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ (exists y1 : a0, y0 y1)) = (forall y1 : a0, ~ (y0 y1))) x0.
Definition term149 (x0 : int -> Prop) (x1 : int -> Prop) := (exists y0 : int, x0 y0) \/ (exists y0 : int, x1 y0).
Definition term14 (x0 : Prop) := @eq Prop (True = x0).
Definition term66 (x0 : int -> Prop) := @eq Prop (~ (exists y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0))).
Definition term65 (x0 : int -> Prop) := @eq Prop (~ (exists y0 : int, (fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) /\ (x0 y1)) y0)).
Definition term34 (x0 : int -> Prop) := @eq Prop (~ (exists y0 : nat, x0 (int_of_num y0))).
Definition term33 (x0 : int -> Prop) := @eq Prop (~ (exists y0 : nat, (fun y1 : nat => x0 (int_of_num y1)) y0)).
Definition term0 (x0 : int -> Prop) := (fun y0 : int -> Prop => (forall y1 : nat, y0 (int_of_num y1)) = (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1)) x0.
Definition term147 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term51 (x0 : int -> Prop) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x1) -> ~ (x0 x1).
Definition term143 (x0 : int -> Prop) := fun y0 : int => ((fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) /\ (x0 y1)) y0) /\ (forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (~ (x0 y1))).
Definition term62 (x0 : int -> Prop) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x1) /\ (x0 x1).
Definition term173 (x0 : int -> Prop) (x1 : int) := (~ (x0 x1)) -> x0 x1.
Definition term117 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term72 (x0 : Prop) := (~ x0) -> False.
Definition term128 (x0 : int -> Prop) := exists y0 : int, (forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (~ (x0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0)).
Definition term126 (x0 : int -> Prop) := fun y0 : int => (forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (~ (x0 y1))) /\ ((fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) /\ (x0 y1)) y0).
Definition term133 (x0 : int -> Prop) (x1 : Prop) := exists y0 : int, (x0 y0) /\ x1.
Definition term95 (x0 : int -> Prop) := fun y0 : int => ~ ((fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) -> ~ (x0 y1)) y0).
Definition term69 (x0 : int -> Prop) := fun y0 : int => ~ ((fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) /\ (x0 y1)) y0).
Definition term23 (x0 : int -> Prop) := ~ (exists y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0)).
Definition term12 (x0 : Prop) (x1 : Prop) := @eq Prop ((x0 = x1) = ((~ x0) = (~ x1))).
Definition term70 (x0 : int -> Prop) := fun y0 : int => ~ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0)).
Definition term86 (x0 : int -> Prop) (x1 : int) := ~ ((int_le (int_of_num (NUMERAL 0)) x1) -> ~ (x0 x1)).
Definition term106 (x0 : int -> Prop) := (~ (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> ~ (x0 y0))) /\ (forall y0 : int, ~ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0))).
Definition term44 (x0 : int -> Prop) := fun y0 : nat => (fun y1 : int => ~ (x0 y1)) (int_of_num y0).
Definition term145 (x0 : int -> Prop) := exists y0 : int, ((int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0)) /\ (forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (~ (x0 y1))).
Definition term42 (x0 : int -> Prop) := fun y0 : int => ~ (x0 y0).
Definition term102 (x0 : int -> Prop) (x1 : int) := ~ ((fun y0 : int => ~ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0))) x1).
Definition term43 (x0 : int -> Prop) (x1 : nat) := (fun y0 : int => ~ (x0 y0)) (int_of_num x1).
Definition term71 (x0 : int -> Prop) := forall y0 : int, ~ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0)).
Definition term141 (x0 : int) (x1 : int -> Prop) := ((fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) /\ (x1 y0)) x0) /\ (forall y0 : int, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (~ (x1 y0))).
Definition term96 (x0 : int -> Prop) := fun y0 : int => (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (~ (x0 y0)).
Definition term29 (x0 : int -> Prop) (x1 : nat) := (fun y0 : nat => x0 (int_of_num y0)) x1.
Definition term127 (x0 : int -> Prop) := fun y0 : int => (forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (~ (x0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0)).
Definition term178 (x0 : int -> Prop) := (fun y0 : int -> Prop => (~ ((forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> ~ (y0 y1)) = (forall y1 : int, ~ ((int_le (int_of_num (NUMERAL 0)) y1) /\ (y0 y1))))) -> False) x0.
Definition term116 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term47 (x0 : int -> Prop) (x1 : int) := (fun y0 : int => ~ (x0 y0)) x1.
Definition term174 (x0 : Prop) (x1 : Prop) := (~ x0) \/ (~ x1).
Definition term172 (x0 : Prop) := (~ x0) -> x0.
Definition term105 (x0 : int -> Prop) := and (exists y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0)).
Definition term20 (x0 : int -> Prop) := exists y0 : nat, x0 (int_of_num y0).
Definition term9 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (y0 = x0) = ((~ y0) = (~ x0))) x1.
Definition term162 (x0 : int -> Prop) (x1 : int) := or ((fun y0 : int => (forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (~ (x0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0))) x1).
Definition term171 (x0 : int) := ~ (int_le (int_of_num (NUMERAL 0)) x0).
Definition term114 (x0 : int -> Prop) := ((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> ~ (x0 y0)) /\ (~ (forall y0 : int, ~ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0))))) \/ ((~ (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> ~ (x0 y0))) /\ (forall y0 : int, ~ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0)))).
Definition term175 (x0 : Prop) (x1 : Prop) := ~ (x0 /\ x1).
Definition term98 (x0 : int -> Prop) (x1 : int) := ~ (~ ((int_le (int_of_num (NUMERAL 0)) x1) /\ (x0 x1))).
Definition term107 (x0 : int -> Prop) := (exists y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0)) /\ (forall y0 : int, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (~ (x0 y0))).
Definition term13 (x0 : Prop) := (fun y0 : Prop => (y0 = x0) = ((~ y0) = (~ x0))) False.
Definition term38 (x0 : int -> Prop) := fun y0 : nat => ~ (x0 (int_of_num y0)).
Definition term157 (x0 : int -> Prop) (x1 : int) := (fun y0 : int => ((int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0)) /\ (forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (~ (x0 y1)))) x1.
Definition term45 (x0 : int -> Prop) := @eq Prop (forall y0 : nat, (fun y1 : int => ~ (x0 y1)) (int_of_num y0)).
Definition term121 (x0 : int -> Prop) := exists y0 : int, (forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (~ (x0 y1))) /\ ((fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) /\ (x0 y1)) y0).
Definition term55 (x0 : int -> Prop) := @eq Prop (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> ~ (x0 y0)).
Definition term54 (x0 : int -> Prop) := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> ~ (x0 y0).
Definition term22 (x0 : int -> Prop) := ~ (exists y0 : nat, x0 (int_of_num y0)).
Definition term57 (x0 : int -> Prop) := forall y0 : int, ~ (x0 y0).
Definition term31 (x0 : int -> Prop) := fun y0 : nat => (fun y1 : nat => x0 (int_of_num y1)) y0.
Definition term58 (x0 : int -> Prop) := ~ (exists y0 : int, (fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) /\ (x0 y1)) y0).
Definition term111 (x0 : int -> Prop) := (forall y0 : int, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (~ (x0 y0))) /\ (exists y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0)).
Definition term63 (x0 : int -> Prop) := fun y0 : int => (fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) /\ (x0 y1)) y0.
Definition term124 (x0 : int -> Prop) (x1 : int) := (forall y0 : int, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (~ (x0 y0))) /\ ((fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0)) x1).
Definition term82 := forall y0 : int -> Prop, (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> ~ (y0 y1)) = (forall y1 : int, ~ ((int_le (int_of_num (NUMERAL 0)) y1) /\ (y0 y1))).
Definition term113 (x0 : int -> Prop) := or ((forall y0 : int, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (~ (x0 y0))) /\ (exists y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0))).
Definition term120 (x0 : int -> Prop) := (forall y0 : int, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (~ (x0 y0))) /\ (exists y0 : int, (fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) /\ (x0 y1)) y0).
Definition term85 (x0 : int -> Prop) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x1) /\ (~ (~ (x0 x1))).
Definition term176 (x0 : int -> Prop) (x1 : int) := ((int_le (int_of_num (NUMERAL 0)) x1) /\ (x0 x1)) -> False.
Definition term151 (x0 : int -> Prop) := (exists y0 : int, (fun y1 : int => (forall y2 : int, (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ (~ (x0 y2))) /\ ((int_le (int_of_num (NUMERAL 0)) y1) /\ (x0 y1))) y0) \/ (exists y0 : int, (fun y1 : int => ((int_le (int_of_num (NUMERAL 0)) y1) /\ (x0 y1)) /\ (forall y2 : int, (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ (~ (x0 y2)))) y0).
Definition term5 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, ~ (x0 y0).
Definition term75 (x0 : int -> Prop) := ((~ ((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> ~ (x0 y0)) = (forall y0 : int, ~ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0))))) -> False) -> (~ ((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> ~ (x0 y0)) = (forall y0 : int, ~ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0))))) -> False.
Definition term169 (x0 : int -> Prop) (x1 : int) := (fun y0 : int => (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (~ (x0 y0))) x1.
Definition term18 (x0 : Prop) := @eq Prop (~ x0).
Definition term80 := fun y0 : int -> Prop => (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> ~ (y0 y1)) = (forall y1 : int, ~ ((int_le (int_of_num (NUMERAL 0)) y1) /\ (y0 y1))).
Definition term140 (x0 : int -> Prop) (x1 : int) := and ((int_le (int_of_num (NUMERAL 0)) x1) /\ (x0 x1)).
Definition term146 (x0 : int -> Prop) := (exists y0 : int, (forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (~ (x0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0))) \/ (exists y0 : int, ((int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0)) /\ (forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (~ (x0 y1)))).
Definition term115 (x0 : int -> Prop) := ((forall y0 : int, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (~ (x0 y0))) /\ (exists y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0))) \/ ((exists y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0)) /\ (forall y0 : int, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (~ (x0 y0)))).
Definition term131 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term91 (x0 : int -> Prop) := ~ (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> ~ (x0 y0)).
Definition term119 (x0 : Prop) (x1 : int -> Prop) := exists y0 : int, x0 /\ (x1 y0).
Definition term159 (x0 : int -> Prop) := exists y0 : int, (fun y1 : int => ((int_le (int_of_num (NUMERAL 0)) y1) /\ (x0 y1)) /\ (forall y2 : int, (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ (~ (x0 y2)))) y0.
Definition term155 (x0 : int -> Prop) := exists y0 : int, (fun y1 : int => (forall y2 : int, (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ (~ (x0 y2))) /\ ((int_le (int_of_num (NUMERAL 0)) y1) /\ (x0 y1))) y0.
Definition term64 (x0 : int -> Prop) := exists y0 : int, (fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) /\ (x0 y1)) y0.
Definition term2 (x0 : int -> Prop) := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> x0 y0.
Definition term81 := forall y0 : int -> Prop, (~ ((forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> ~ (y0 y1)) = (forall y1 : int, ~ ((int_le (int_of_num (NUMERAL 0)) y1) /\ (y0 y1))))) -> False.
Definition term93 (x0 : int -> Prop) (x1 : int) := (fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) -> ~ (x0 y0)) x1.
Definition term25 (x0 : nat -> Prop) := forall y0 : nat, ~ (x0 y0).
Definition term56 (x0 : int -> Prop) := ~ (exists y0 : int, x0 y0).
Definition term53 (x0 : int -> Prop) := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) -> ~ (x0 y0).
Definition term21 (x0 : int -> Prop) := exists y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0).
Definition term4 (a0 : Type') (x0 : a0 -> Prop) := ~ (exists y0 : a0, x0 y0).
Definition term144 (x0 : int -> Prop) := fun y0 : int => ((int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0)) /\ (forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (~ (x0 y1))).
Definition term26 (x0 : int -> Prop) := ~ (exists y0 : nat, (fun y1 : nat => x0 (int_of_num y1)) y0).
Definition term11 (x0 : Prop) (x1 : Prop) := @eq Prop ((fun y0 : Prop => (y0 = x0) = ((~ y0) = (~ x0))) x1).
Definition term48 (x0 : int -> Prop) (x1 : int) := ~ (x0 x1).
Definition term99 (x0 : int -> Prop) := ~ (forall y0 : int, ~ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0))).
Definition term166 (x0 : int -> Prop) := fun y0 : int => ((fun y1 : int => (forall y2 : int, (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ (~ (x0 y2))) /\ ((int_le (int_of_num (NUMERAL 0)) y1) /\ (x0 y1))) y0) \/ ((fun y1 : int => ((int_le (int_of_num (NUMERAL 0)) y1) /\ (x0 y1)) /\ (forall y2 : int, (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ (~ (x0 y2)))) y0).
Definition term83 (x0 : int -> Prop) (x1 : int) := ~ (~ (x0 x1)).
Definition term15 := @eq Prop (~ True).
Definition term135 (x0 : int -> Prop) := exists y0 : int, ((fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) /\ (x0 y1)) y0) /\ (forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (~ (x0 y1))).
Definition term50 (x0 : int -> Prop) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x1) -> (fun y0 : int => ~ (x0 y0)) x1.
Definition term76 (x0 : int -> Prop) := (((~ ((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> ~ (x0 y0)) = (forall y0 : int, ~ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0))))) -> False) -> (~ ((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> ~ (x0 y0)) = (forall y0 : int, ~ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0))))) -> False) -> (~ ((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> ~ (x0 y0)) = (forall y0 : int, ~ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0))))) -> False.
Definition term7 (x0 : Prop) := (x0 = True) \/ (x0 = False).
Definition term134 (x0 : int -> Prop) := (exists y0 : int, (fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) /\ (x0 y1)) y0) /\ (forall y0 : int, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (~ (x0 y0))).
Definition term136 (x0 : int -> Prop) := and (exists y0 : int, (fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) /\ (x0 y1)) y0).
Definition term78 (x0 : int -> Prop) := ~ (~ ((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> ~ (x0 y0)) = (forall y0 : int, ~ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0))))).
Definition term168 (x0 : int -> Prop) := exists y0 : int, ((forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (~ (x0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0))) \/ (((int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0)) /\ (forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (~ (x0 y1)))).
Definition term139 (x0 : int -> Prop) (x1 : int) := and ((fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0)) x1).
Definition term94 (x0 : int -> Prop) (x1 : int) := ~ ((fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) -> ~ (x0 y0)) x1).
Definition term67 (x0 : int -> Prop) (x1 : int) := ~ ((fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0)) x1).
Definition term158 (x0 : int -> Prop) := fun y0 : int => (fun y1 : int => ((int_le (int_of_num (NUMERAL 0)) y1) /\ (x0 y1)) /\ (forall y2 : int, (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ (~ (x0 y2)))) y0.
Definition term84 (x0 : int) := and (int_le (int_of_num (NUMERAL 0)) x0).
Definition term40 (x0 : int -> Prop) := forall y0 : nat, (fun y1 : int => ~ (x0 y1)) (int_of_num y0).
Definition term132 (x0 : int -> Prop) (x1 : Prop) := (exists y0 : int, x0 y0) /\ x1.
Definition term61 (x0 : int -> Prop) (x1 : int) := (fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0)) x1.
Definition term142 (x0 : int) (x1 : int -> Prop) := ((int_le (int_of_num (NUMERAL 0)) x0) /\ (x1 x0)) /\ (forall y0 : int, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (~ (x1 y0))).
Definition term60 (x0 : int -> Prop) := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0).
Definition term27 (x0 : int -> Prop) := forall y0 : nat, ~ ((fun y1 : nat => x0 (int_of_num y1)) y0).
Definition term109 (x0 : int -> Prop) := and (forall y0 : int, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (~ (x0 y0))).
Definition term108 (x0 : int -> Prop) := and (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> ~ (x0 y0)).
Definition term1 (x0 : int -> Prop) := forall y0 : nat, x0 (int_of_num y0).
Definition term150 (x0 : int -> Prop) (x1 : int -> Prop) := exists y0 : int, (x0 y0) \/ (x1 y0).
Definition term164 (x0 : int -> Prop) (x1 : int) := ((fun y0 : int => (forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (~ (x0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0))) x1) \/ ((fun y0 : int => ((int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0)) /\ (forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (~ (x0 y1)))) x1).
Definition term39 (x0 : int -> Prop) := forall y0 : nat, ~ (x0 (int_of_num y0)).
Definition term125 (x0 : int -> Prop) (x1 : int) := (forall y0 : int, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (~ (x0 y0))) /\ ((int_le (int_of_num (NUMERAL 0)) x1) /\ (x0 x1)).
Definition term154 (x0 : int -> Prop) := fun y0 : int => (fun y1 : int => (forall y2 : int, (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ (~ (x0 y2))) /\ ((int_le (int_of_num (NUMERAL 0)) y1) /\ (x0 y1))) y0.
Definition term46 (x0 : int -> Prop) := @eq Prop (forall y0 : nat, ~ (x0 (int_of_num y0))).
Definition term112 (x0 : int -> Prop) := or ((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> ~ (x0 y0)) /\ (~ (forall y0 : int, ~ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0))))).
Definition term179 := forall y0 : int -> Prop, (exists y1 : nat, y0 (int_of_num y1)) = (exists y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) /\ (y0 y1)).
Definition term129 (x0 : int -> Prop) := or (exists y0 : int, (forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (~ (x0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0))).
Definition term152 (x0 : int -> Prop) := exists y0 : int, ((fun y1 : int => (forall y2 : int, (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ (~ (x0 y2))) /\ ((int_le (int_of_num (NUMERAL 0)) y1) /\ (x0 y1))) y0) \/ ((fun y1 : int => ((int_le (int_of_num (NUMERAL 0)) y1) /\ (x0 y1)) /\ (forall y2 : int, (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ (~ (x0 y2)))) y0).
Definition term163 (x0 : int -> Prop) (x1 : int) := or ((forall y0 : int, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (~ (x0 y0))) /\ ((int_le (int_of_num (NUMERAL 0)) x1) /\ (x0 x1))).
Definition term36 (x0 : int -> Prop) (x1 : nat) := ~ (x0 (int_of_num x1)).
Definition term41 (x0 : int -> Prop) := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (fun y1 : int => ~ (x0 y1)) y0.
Definition term28 (x0 : int -> Prop) := fun y0 : nat => x0 (int_of_num y0).
Definition term35 (x0 : int -> Prop) (x1 : nat) := ~ ((fun y0 : nat => x0 (int_of_num y0)) x1).
Definition term104 (x0 : int -> Prop) := and (~ (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> ~ (x0 y0))).
Definition term30 (x0 : int -> Prop) (x1 : nat) := x0 (int_of_num x1).
Definition term101 (x0 : int -> Prop) (x1 : int) := (fun y0 : int => ~ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0))) x1.
Definition term123 (x0 : int -> Prop) := @eq Prop ((forall y0 : int, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (~ (x0 y0))) /\ (exists y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0))).
Definition term122 (x0 : int -> Prop) := @eq Prop ((forall y0 : int, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (~ (x0 y0))) /\ (exists y0 : int, (fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) /\ (x0 y1)) y0)).
Definition term156 (x0 : int -> Prop) := or (exists y0 : int, (fun y1 : int => (forall y2 : int, (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ (~ (x0 y2))) /\ ((int_le (int_of_num (NUMERAL 0)) y1) /\ (x0 y1))) y0).
Definition term24 (x0 : nat -> Prop) := ~ (exists y0 : nat, x0 y0).
Definition term100 (x0 : int -> Prop) := exists y0 : int, ~ ((fun y1 : int => ~ ((int_le (int_of_num (NUMERAL 0)) y1) /\ (x0 y1))) y0).
Definition term92 (x0 : int -> Prop) := exists y0 : int, ~ ((fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) -> ~ (x0 y1)) y0).
Definition term37 (x0 : int -> Prop) := fun y0 : nat => ~ ((fun y1 : nat => x0 (int_of_num y1)) y0).
Definition term118 (x0 : Prop) (x1 : int -> Prop) := x0 /\ (exists y0 : int, x1 y0).
Definition term138 (x0 : int -> Prop) := @eq Prop ((exists y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0)) /\ (forall y0 : int, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (~ (x0 y0)))).
Definition term137 (x0 : int -> Prop) := @eq Prop ((exists y0 : int, (fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) /\ (x0 y1)) y0) /\ (forall y0 : int, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (~ (x0 y0)))).
Definition term77 (x0 : int -> Prop) := (((~ ((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> ~ (x0 y0)) = (forall y0 : int, ~ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0))))) -> False) -> (~ ((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> ~ (x0 y0)) = (forall y0 : int, ~ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0))))) -> False) -> ((~ ((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> ~ (x0 y0)) = (forall y0 : int, ~ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0))))) -> False) -> (~ ((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> ~ (x0 y0)) = (forall y0 : int, ~ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0))))) -> False.
Definition term87 (x0 : int) := int_le (int_of_num (NUMERAL 0)) x0.
Definition term130 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term73 (x0 : int -> Prop) := (~ ((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> ~ (x0 y0)) = (forall y0 : int, ~ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0))))) -> False.
Definition term10 (x0 : Prop) := (fun y0 : Prop => (y0 = x0) = ((~ y0) = (~ x0))) True.
Definition term6 (x0 : Prop) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) x0.
Definition term110 (x0 : int -> Prop) := (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> ~ (x0 y0)) /\ (~ (forall y0 : int, ~ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0)))).
Definition term97 (x0 : int -> Prop) := forall y0 : int, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (~ (x0 y0)).
Definition term103 (x0 : int -> Prop) := fun y0 : int => ~ ((fun y1 : int => ~ ((int_le (int_of_num (NUMERAL 0)) y1) /\ (x0 y1))) y0).
Definition term148 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term32 (x0 : int -> Prop) := exists y0 : nat, (fun y1 : nat => x0 (int_of_num y1)) y0.
Definition term170 (x0 : int) := (~ (int_le (int_of_num (NUMERAL 0)) x0)) -> int_le (int_of_num (NUMERAL 0)) x0.
Definition term68 (x0 : int -> Prop) (x1 : int) := ~ ((int_le (int_of_num (NUMERAL 0)) x1) /\ (x0 x1)).
Definition term79 := fun y0 : int -> Prop => (~ ((forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> ~ (y0 y1)) = (forall y1 : int, ~ ((int_le (int_of_num (NUMERAL 0)) y1) /\ (y0 y1))))) -> False.
Definition term88 (x0 : int -> Prop) (x1 : int) := (~ (int_le (int_of_num (NUMERAL 0)) x1)) \/ (~ (x0 x1)).
Definition term153 (x0 : int -> Prop) (x1 : int) := (fun y0 : int => (forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (~ (x0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0))) x1.
Definition term59 (x0 : int -> Prop) := forall y0 : int, ~ ((fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) /\ (x0 y1)) y0).
Definition term161 (x0 : int -> Prop) := @eq Prop ((exists y0 : int, (forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (~ (x0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0))) \/ (exists y0 : int, ((int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0)) /\ (forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (~ (x0 y1))))).
Definition term160 (x0 : int -> Prop) := @eq Prop ((exists y0 : int, (fun y1 : int => (forall y2 : int, (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ (~ (x0 y2))) /\ ((int_le (int_of_num (NUMERAL 0)) y1) /\ (x0 y1))) y0) \/ (exists y0 : int, (fun y1 : int => ((int_le (int_of_num (NUMERAL 0)) y1) /\ (x0 y1)) /\ (forall y2 : int, (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ (~ (x0 y2)))) y0)).
