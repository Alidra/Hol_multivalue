Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term40 := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) /\ (~ ((int_of_num (num_of_int y0)) = y0)).
Definition term122 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := imp (~ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (int_le x2 x3))))).
Definition term66 (x0 : int) := (fun y0 : int => (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ ((int_of_num (num_of_int y0)) = y0)) x0.
Definition term27 (x0 : int -> Prop) := exists y0 : int, ~ (x0 y0).
Definition term26 (x0 : int -> Prop) := ~ (all x0).
Definition term83 := (~ False) -> False.
Definition term124 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := ((x0 = x2) /\ ((x1 = x3) /\ (int_le x0 x1))) -> int_le x2 x3.
Definition term80 (x0 : int) := imp (int_le (int_of_num (NUMERAL 0)) x0).
Definition term10 := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (int_of_num (num_of_int y0)) = y0.
Definition term77 (x0 : Prop) := ~ (~ x0).
Definition term37 (x0 : int -> Prop) (x1 : int -> Prop) := (exists y0 : int, x0 y0) \/ (exists y0 : int, x1 y0).
Definition term29 (x0 : int) := (fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) = ((int_of_num (num_of_int y0)) = y0)) x0.
Definition term86 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (int_le x0 x1) \/ (~ (int_le x2 x3)).
Definition term42 (x0 : int) := (fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) /\ (~ ((int_of_num (num_of_int y0)) = y0))) x0.
Definition term92 := int_of_num (NUMERAL 0).
Definition term118 (x0 : int) (x1 : int) (x2 : int) := (~ (~ (x2 = x0))) /\ (~ (~ (int_le x1 x2))).
Definition term35 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term30 (x0 : int) := ~ ((fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) = ((int_of_num (num_of_int y0)) = y0)) x0).
Definition term72 (x0 : int) := ((int_of_num (num_of_int x0)) = x0) \/ (~ (int_le (int_of_num (NUMERAL 0)) x0)).
Definition term116 (x0 : int) (x1 : int) := and (x0 = x1).
Definition term95 (x0 : int) := int_le (int_of_num (NUMERAL 0)) (int_of_num (num_of_int x0)).
Definition term12 := (forall y0 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y0)) -> (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (int_of_num (num_of_int y0)) = y0) -> False.
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term20 := forall y0 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y0).
Definition term82 (x0 : int) := ((int_of_num (num_of_int x0)) = x0) -> False.
Definition term31 := fun y0 : int => ~ ((fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) = ((int_of_num (num_of_int y1)) = y1)) y0).
Definition term48 (x0 : int) := ((fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) /\ (~ ((int_of_num (num_of_int y0)) = y0))) x0) \/ ((fun y0 : int => (~ (int_le (int_of_num (NUMERAL 0)) y0)) /\ ((int_of_num (num_of_int y0)) = y0)) x0).
Definition term126 (x0 : int) := ((int_of_num (NUMERAL 0)) = (int_of_num (NUMERAL 0))) /\ (((int_of_num (num_of_int x0)) = x0) /\ (int_le (int_of_num (NUMERAL 0)) (int_of_num (num_of_int x0)))).
Definition term93 := (~ ((int_of_num (NUMERAL 0)) = (int_of_num (NUMERAL 0)))) -> (int_of_num (NUMERAL 0)) = (int_of_num (NUMERAL 0)).
Definition term75 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term19 := fun y0 : nat => int_le (int_of_num (NUMERAL 0)) (int_of_num y0).
Definition term90 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (x2 = x0) -> (~ (x3 = x1)) \/ ((int_le x0 x1) \/ (~ (int_le x2 x3))).
Definition term127 (x0 : int) := (((int_of_num (NUMERAL 0)) = (int_of_num (NUMERAL 0))) /\ (((int_of_num (num_of_int x0)) = x0) /\ (int_le (int_of_num (NUMERAL 0)) (int_of_num (num_of_int x0))))) -> int_le (int_of_num (NUMERAL 0)) x0.
Definition term71 (x0 : Prop) := (~ x0) -> x0.
Definition term99 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (int_le x0 x1) \/ ((~ (x3 = x1)) \/ (~ (int_le x2 x3))).
Definition term5 := ((~ (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) = ((int_of_num (num_of_int y0)) = y0))) -> (forall y0 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y0)) -> (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (int_of_num (num_of_int y0)) = y0) -> False) -> (~ (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) = ((int_of_num (num_of_int y0)) = y0))) -> (forall y0 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y0)) -> (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (int_of_num (num_of_int y0)) = y0) -> False.
Definition term101 (x0 : int) (x1 : int) := ~ (int_le x0 x1).
Definition term94 := ~ ((int_of_num (NUMERAL 0)) = (int_of_num (NUMERAL 0))).
Definition term111 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term121 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (x2 = x0) /\ ((x3 = x1) /\ (int_le x2 x3)).
Definition term69 (x0 : int) := ~ (int_le (int_of_num (NUMERAL 0)) x0).
Definition term57 := fun y0 : int => (fun y1 : int => (~ (int_le (int_of_num (NUMERAL 0)) y1)) /\ ((int_of_num (num_of_int y1)) = y1)) y0.
Definition term78 (x0 : int) := ~ (~ (int_le (int_of_num (NUMERAL 0)) x0)).
Definition term98 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term16 (x0 : int) := (int_le (int_of_num (NUMERAL 0)) x0) -> (int_of_num (num_of_int x0)) = x0.
Definition term15 := (~ (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) = ((int_of_num (num_of_int y0)) = y0))) -> (forall y0 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y0)) -> ~ (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (int_of_num (num_of_int y0)) = y0).
Definition term32 := fun y0 : int => ((int_le (int_of_num (NUMERAL 0)) y0) /\ (~ ((int_of_num (num_of_int y0)) = y0))) \/ ((~ (int_le (int_of_num (NUMERAL 0)) y0)) /\ ((int_of_num (num_of_int y0)) = y0)).
Definition term76 (x0 : int) := (~ (~ (int_le (int_of_num (NUMERAL 0)) x0))) -> (int_of_num (num_of_int x0)) = x0.
Definition term65 := forall y0 : int, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ ((int_of_num (num_of_int y0)) = y0).
Definition term73 (x0 : int) := @eq Prop ((~ (int_le (int_of_num (NUMERAL 0)) x0)) \/ ((int_of_num (num_of_int x0)) = x0)).
Definition term123 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := imp ((x2 = x0) /\ ((x3 = x1) /\ (int_le x2 x3))).
Definition term67 (x0 : nat) := (fun y0 : nat => int_le (int_of_num (NUMERAL 0)) (int_of_num y0)) x0.
Definition term33 := exists y0 : int, ((int_le (int_of_num (NUMERAL 0)) y0) /\ (~ ((int_of_num (num_of_int y0)) = y0))) \/ ((~ (int_le (int_of_num (NUMERAL 0)) y0)) /\ ((int_of_num (num_of_int y0)) = y0)).
Definition term64 := fun y0 : int => (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ ((int_of_num (num_of_int y0)) = y0).
Definition term103 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (~ (x2 = x0)) \/ ((int_le x0 x1) \/ ((~ (x3 = x1)) \/ (~ (int_le x2 x3)))).
Definition term11 := imp (forall y0 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y0)).
Definition term125 (x0 : int) := ((int_of_num (num_of_int x0)) = x0) /\ (int_le (int_of_num (NUMERAL 0)) (int_of_num (num_of_int x0))).
Definition term44 (x0 : int) := or ((fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) /\ (~ ((int_of_num (num_of_int y0)) = y0))) x0).
Definition term39 := (exists y0 : int, (fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) /\ (~ ((int_of_num (num_of_int y1)) = y1))) y0) \/ (exists y0 : int, (fun y1 : int => (~ (int_le (int_of_num (NUMERAL 0)) y1)) /\ ((int_of_num (num_of_int y1)) = y1)) y0).
Definition term89 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (~ (x3 = x1)) \/ ((int_le x0 x1) \/ (~ (int_le x2 x3))).
Definition term85 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := ((int_le x2 x3) = (int_le x0 x1)) -> (int_le x0 x1) \/ (~ (int_le x2 x3)).
Definition term107 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := @eq Prop ((int_le x0 x1) \/ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (int_le x2 x3))))).
Definition term59 := exists y0 : int, (~ (int_le (int_of_num (NUMERAL 0)) y0)) /\ ((int_of_num (num_of_int y0)) = y0).
Definition term52 := fun y0 : int => (fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) /\ (~ ((int_of_num (num_of_int y1)) = y1))) y0.
Definition term1 := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) = ((int_of_num (num_of_int y0)) = y0).
Definition term13 := (forall y0 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y0)) -> ~ (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (int_of_num (num_of_int y0)) = y0).
Definition term51 := @eq Prop (exists y0 : int, ((int_le (int_of_num (NUMERAL 0)) y0) /\ (~ ((int_of_num (num_of_int y0)) = y0))) \/ ((~ (int_le (int_of_num (NUMERAL 0)) y0)) /\ ((int_of_num (num_of_int y0)) = y0))).
Definition term50 := @eq Prop (exists y0 : int, ((fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) /\ (~ ((int_of_num (num_of_int y1)) = y1))) y0) \/ ((fun y1 : int => (~ (int_le (int_of_num (NUMERAL 0)) y1)) /\ ((int_of_num (num_of_int y1)) = y1)) y0)).
Definition term68 (x0 : int) := ~ ((int_of_num (num_of_int x0)) = x0).
Definition term110 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term60 := (exists y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) /\ (~ ((int_of_num (num_of_int y0)) = y0))) \/ (exists y0 : int, (~ (int_le (int_of_num (NUMERAL 0)) y0)) /\ ((int_of_num (num_of_int y0)) = y0)).
Definition term108 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (~ ((~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ (~ (int_le x0 x1))))) -> int_le x2 x3.
Definition term9 := ~ (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (int_of_num (num_of_int y0)) = y0).
Definition term3 := ~ (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) = ((int_of_num (num_of_int y0)) = y0)).
Definition term22 (x0 : int) := int_of_num (num_of_int x0).
Definition term6 := (((~ (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) = ((int_of_num (num_of_int y0)) = y0))) -> (forall y0 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y0)) -> (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (int_of_num (num_of_int y0)) = y0) -> False) -> (~ (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) = ((int_of_num (num_of_int y0)) = y0))) -> (forall y0 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y0)) -> (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (int_of_num (num_of_int y0)) = y0) -> False) -> (~ (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) = ((int_of_num (num_of_int y0)) = y0))) -> (forall y0 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y0)) -> (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (int_of_num (num_of_int y0)) = y0) -> False.
Definition term58 := exists y0 : int, (fun y1 : int => (~ (int_le (int_of_num (NUMERAL 0)) y1)) /\ ((int_of_num (num_of_int y1)) = y1)) y0.
Definition term53 := exists y0 : int, (fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) /\ (~ ((int_of_num (num_of_int y1)) = y1))) y0.
Definition term97 (x0 : int) := ~ (int_le (int_of_num (NUMERAL 0)) (int_of_num (num_of_int x0))).
Definition term8 := (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (int_of_num (num_of_int y0)) = y0) -> False.
Definition term63 (x0 : int) := (~ (int_le (int_of_num (NUMERAL 0)) x0)) \/ ((int_of_num (num_of_int x0)) = x0).
Definition term112 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := ~ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (int_le x2 x3)))).
Definition term2 := (~ (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) = ((int_of_num (num_of_int y0)) = y0))) -> False.
Definition term41 := fun y0 : int => (~ (int_le (int_of_num (NUMERAL 0)) y0)) /\ ((int_of_num (num_of_int y0)) = y0).
Definition term25 (x0 : int) := ((int_le (int_of_num (NUMERAL 0)) x0) /\ (~ ((int_of_num (num_of_int x0)) = x0))) \/ ((~ (int_le (int_of_num (NUMERAL 0)) x0)) /\ ((int_of_num (num_of_int x0)) = x0)).
Definition term43 (x0 : int) := (int_le (int_of_num (NUMERAL 0)) x0) /\ (~ ((int_of_num (num_of_int x0)) = x0)).
Definition term49 := fun y0 : int => ((fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) /\ (~ ((int_of_num (num_of_int y1)) = y1))) y0) \/ ((fun y1 : int => (~ (int_le (int_of_num (NUMERAL 0)) y1)) /\ ((int_of_num (num_of_int y1)) = y1)) y0).
Definition term7 := (((~ (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) = ((int_of_num (num_of_int y0)) = y0))) -> (forall y0 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y0)) -> (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (int_of_num (num_of_int y0)) = y0) -> False) -> (~ (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) = ((int_of_num (num_of_int y0)) = y0))) -> (forall y0 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y0)) -> (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (int_of_num (num_of_int y0)) = y0) -> False) -> ((~ (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) = ((int_of_num (num_of_int y0)) = y0))) -> (forall y0 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y0)) -> (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (int_of_num (num_of_int y0)) = y0) -> False) -> (~ (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) = ((int_of_num (num_of_int y0)) = y0))) -> (forall y0 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y0)) -> (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (int_of_num (num_of_int y0)) = y0) -> False.
Definition term24 (x0 : int) := ~ ((int_le (int_of_num (NUMERAL 0)) x0) = ((int_of_num (num_of_int x0)) = x0)).
Definition term115 (x0 : int) (x1 : int) := and (~ (~ (x0 = x1))).
Definition term18 (x0 : nat) := int_le (int_of_num (NUMERAL 0)) (int_of_num x0).
Definition term104 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (int_le x0 x1) \/ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (int_le x2 x3)))).
Definition term84 (x0 : Prop) (x1 : Prop) := (x1 = x0) -> x0 \/ (~ x1).
Definition term100 (x0 : int) (x1 : int) := ~ (x0 = x1).
Definition term45 (x0 : int) := or ((int_le (int_of_num (NUMERAL 0)) x0) /\ (~ ((int_of_num (num_of_int x0)) = x0))).
Definition term36 (x0 : int -> Prop) (x1 : int -> Prop) := exists y0 : int, (x0 y0) \/ (x1 y0).
Definition term105 (x0 : int) (x1 : int) (x2 : int) := (~ (x2 = x0)) \/ (~ (int_le x1 x2)).
Definition term109 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (int_le x2 x3))).
Definition term117 (x0 : int) (x1 : int) (x2 : int) := ~ ((~ (x2 = x0)) \/ (~ (int_le x1 x2))).
Definition term56 := or (exists y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) /\ (~ ((int_of_num (num_of_int y0)) = y0))).
Definition term106 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := @eq Prop ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ ((int_le x0 x1) \/ (~ (int_le x2 x3))))).
Definition term74 (x0 : int) := @eq Prop (((int_of_num (num_of_int x0)) = x0) \/ (~ (int_le (int_of_num (NUMERAL 0)) x0))).
Definition term120 (x0 : int) (x1 : int) (x2 : int) := (x2 = x0) /\ (int_le x1 x2).
Definition term38 := exists y0 : int, ((fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) /\ (~ ((int_of_num (num_of_int y1)) = y1))) y0) \/ ((fun y1 : int => (~ (int_le (int_of_num (NUMERAL 0)) y1)) /\ ((int_of_num (num_of_int y1)) = y1)) y0).
Definition term23 := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) = ((int_of_num (num_of_int y0)) = y0).
Definition term88 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term113 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (~ (~ (x2 = x0))) /\ (~ ((~ (x3 = x1)) \/ (~ (int_le x2 x3)))).
Definition term128 (x0 : int) := (int_le (int_of_num (NUMERAL 0)) x0) -> False.
Definition term17 := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) -> (int_of_num (num_of_int y0)) = y0.
Definition term55 := or (exists y0 : int, (fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) /\ (~ ((int_of_num (num_of_int y1)) = y1))) y0).
Definition term81 (x0 : int) := (~ ((int_of_num (num_of_int x0)) = x0)) -> (int_of_num (num_of_int x0)) = x0.
Definition term28 := exists y0 : int, ~ ((fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) = ((int_of_num (num_of_int y1)) = y1)) y0).
Definition term46 (x0 : int) := (fun y0 : int => (~ (int_le (int_of_num (NUMERAL 0)) y0)) /\ ((int_of_num (num_of_int y0)) = y0)) x0.
Definition term21 (x0 : int) := int_le (int_of_num (NUMERAL 0)) x0.
Definition term114 (x0 : int) (x1 : int) := ~ (~ (x0 = x1)).
Definition term87 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (x3 = x1) -> (int_le x0 x1) \/ (~ (int_le x2 x3)).
Definition term102 (x0 : int) (x1 : int) := or (~ (x0 = x1)).
Definition term47 (x0 : int) := (~ (int_le (int_of_num (NUMERAL 0)) x0)) /\ ((int_of_num (num_of_int x0)) = x0).
Definition term34 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term91 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ ((int_le x0 x1) \/ (~ (int_le x2 x3)))).
Definition term4 := (~ (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) = ((int_of_num (num_of_int y0)) = y0))) -> (forall y0 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y0)) -> (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (int_of_num (num_of_int y0)) = y0) -> False.
Definition term54 := exists y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) /\ (~ ((int_of_num (num_of_int y0)) = y0)).
Definition term70 (x0 : int) := (~ (int_le (int_of_num (NUMERAL 0)) x0)) -> int_le (int_of_num (NUMERAL 0)) x0.
Definition term119 (x0 : int) (x1 : int) := ~ (~ (int_le x0 x1)).
Definition term14 := imp (~ (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) = ((int_of_num (num_of_int y0)) = y0))).
Definition term79 (x0 : int) := imp (~ (~ (int_le (int_of_num (NUMERAL 0)) x0))).
Definition term96 (x0 : int) := (~ (int_le (int_of_num (NUMERAL 0)) (int_of_num (num_of_int x0)))) -> int_le (int_of_num (NUMERAL 0)) (int_of_num (num_of_int x0)).
Definition term62 := @eq Prop ((exists y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) /\ (~ ((int_of_num (num_of_int y0)) = y0))) \/ (exists y0 : int, (~ (int_le (int_of_num (NUMERAL 0)) y0)) /\ ((int_of_num (num_of_int y0)) = y0))).
Definition term61 := @eq Prop ((exists y0 : int, (fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) /\ (~ ((int_of_num (num_of_int y1)) = y1))) y0) \/ (exists y0 : int, (fun y1 : int => (~ (int_le (int_of_num (NUMERAL 0)) y1)) /\ ((int_of_num (num_of_int y1)) = y1)) y0)).
