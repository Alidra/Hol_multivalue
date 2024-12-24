Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term27 (x0 : real) (x1 : nat) (x2 : real) := real_lt x0 (real_mul (real_of_num x1) x2).
Definition term173 (x0 : real -> nat) (x1 : real) (x2 : real) := (~ (real_lt x1 (real_mul (real_of_num (x0 (real_div x1 x2))) x2))) -> real_lt x1 (real_mul (real_of_num (x0 (real_div x1 x2))) x2).
Definition term121 (x0 : real) (x1 : real) (x2 : real) := (real_lt (real_div x0 x2) x1) \/ (~ (real_lt x0 (real_mul x1 x2))).
Definition term71 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : nat, ~ (real_lt y0 (real_mul (real_of_num y1) x0))) x1.
Definition term45 (x0 : real -> Prop) := ~ (all x0).
Definition term178 := (~ False) -> False.
Definition term29 (x0 : real) (x1 : real) := exists y0 : nat, real_lt x0 (real_mul (real_of_num y0) x1).
Definition term81 := fun y0 : real => exists y1 : real, (real_lt (real_of_num (NUMERAL 0)) y0) /\ (forall y2 : nat, ~ (real_lt y1 (real_mul (real_of_num y2) y0))).
Definition term123 (x0 : real) (x1 : real) (x2 : real) := (~ (real_lt (real_div x0 x2) x1)) \/ (real_lt x0 (real_mul x1 x2)).
Definition term11 := imp (forall y0 : real, forall y1 : real, forall y2 : real, (real_lt (real_of_num (NUMERAL 0)) y2) -> (real_lt (real_div y0 y2) y1) = (real_lt y0 (real_mul y1 y2))).
Definition term105 (x0 : real) := fun y0 : nat => (fun y1 : real => fun y2 : nat => real_lt y1 (real_of_num y2)) x0 y0.
Definition term107 := fun y0 : real => exists y1 : nat, (fun y2 : real => fun y3 : nat => real_lt y2 (real_of_num y3)) y0 y1.
Definition term52 (x0 : real) := fun y0 : real => forall y1 : nat, ~ (real_lt y0 (real_mul (real_of_num y1) x0)).
Definition term161 (x0 : Prop) := ~ (~ x0).
Definition term165 (x0 : real) (x1 : real) (x2 : real) := (real_lt (real_of_num (NUMERAL 0)) x1) /\ (real_lt (real_div x0 x1) x2).
Definition term136 (x0 : real) := (~ (real_lt (real_of_num (NUMERAL 0)) x0)) -> real_lt (real_of_num (NUMERAL 0)) x0.
Definition term169 (x0 : real -> nat) (x1 : real) (x2 : real) := (real_lt (real_of_num (NUMERAL 0)) x2) /\ (real_lt (real_div x1 x2) (real_of_num (x0 (real_div x1 x2)))).
Definition term60 (x0 : real) := (fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) y0) -> forall y1 : real, exists y2 : nat, real_lt y1 (real_mul (real_of_num y2) y0)) x0.
Definition term22 (x0 : real) (x1 : real) := forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) -> (real_lt (real_div x0 y0) x1) = (real_lt x0 (real_mul x1 y0)).
Definition term67 (x0 : Prop) (x1 : real -> Prop) := x0 /\ (exists y0 : real, x1 y0).
Definition term106 (x0 : real) := exists y0 : nat, (fun y1 : real => fun y2 : nat => real_lt y1 (real_of_num y2)) x0 y0.
Definition term164 (x0 : real) (x1 : real) (x2 : real) := ~ (~ (real_lt (real_div x0 x1) x2)).
Definition term175 (x0 : real) (x1 : nat) (x2 : real) := (real_lt x0 (real_mul (real_of_num x1) x2)) -> False.
Definition term144 (x0 : real) (x1 : real) (x2 : real) := (~ (real_lt (real_of_num (NUMERAL 0)) x2)) \/ (real_lt x0 (real_mul x1 x2)).
Definition term112 (x0 : real -> nat) (x1 : real) := real_lt x1 (real_of_num (x0 x1)).
Definition term53 (x0 : real) := exists y0 : real, forall y1 : nat, ~ (real_lt y0 (real_mul (real_of_num y1) x0)).
Definition term66 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term166 (x0 : real) (x1 : real) (x2 : real) := imp (~ ((~ (real_lt (real_of_num (NUMERAL 0)) x1)) \/ (~ (real_lt (real_div x0 x1) x2)))).
Definition term3 := ~ (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) -> forall y1 : real, exists y2 : nat, real_lt y1 (real_mul (real_of_num y2) y0)).
Definition term89 (x0 : real) (x1 : real) := fun y0 : real => (~ (real_lt (real_of_num (NUMERAL 0)) y0)) \/ (((real_lt (real_div x0 y0) x1) \/ (~ (real_lt x0 (real_mul x1 y0)))) /\ ((~ (real_lt (real_div x0 y0) x1)) \/ (real_lt x0 (real_mul x1 y0)))).
Definition term168 (x0 : real) (x1 : real) (x2 : real) := ((real_lt (real_of_num (NUMERAL 0)) x2) /\ (real_lt (real_div x0 x2) x1)) -> real_lt x0 (real_mul x1 x2).
Definition term87 (x0 : real) (x1 : real) (x2 : real) := (~ (real_lt (real_of_num (NUMERAL 0)) x2)) \/ ((real_lt (real_div x0 x2) x1) = (real_lt x0 (real_mul x1 x2))).
Definition term103 (x0 : real) (x1 : nat) := (fun y0 : real => fun y1 : nat => real_lt y0 (real_of_num y1)) x0 x1.
Definition term101 := fun y0 : real => fun y1 : nat => real_lt y0 (real_of_num y1).
Definition term155 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term65 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term88 (x0 : real) (x1 : real) (x2 : real) := (~ (real_lt (real_of_num (NUMERAL 0)) x2)) \/ (((real_lt (real_div x0 x2) x1) \/ (~ (real_lt x0 (real_mul x1 x2)))) /\ ((~ (real_lt (real_div x0 x2) x1)) \/ (real_lt x0 (real_mul x1 x2)))).
Definition term148 (x0 : real) (x1 : real) (x2 : real) := (real_lt x0 (real_mul x1 x2)) \/ ((~ (real_lt (real_div x0 x2) x1)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) x2))).
Definition term137 (x0 : Prop) := (~ x0) -> x0.
Definition term33 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) -> forall y0 : real, exists y1 : nat, real_lt y0 (real_mul (real_of_num y1) x0).
Definition term5 := ((~ (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) -> forall y1 : real, exists y2 : nat, real_lt y1 (real_mul (real_of_num y2) y0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_lt (real_of_num (NUMERAL 0)) y2) -> (real_lt (real_div y0 y2) y1) = (real_lt y0 (real_mul y1 y2))) -> (forall y0 : real, exists y1 : nat, real_lt y0 (real_of_num y1)) -> False) -> (~ (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) -> forall y1 : real, exists y2 : nat, real_lt y1 (real_mul (real_of_num y2) y0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_lt (real_of_num (NUMERAL 0)) y2) -> (real_lt (real_div y0 y2) y1) = (real_lt y0 (real_mul y1 y2))) -> (forall y0 : real, exists y1 : nat, real_lt y0 (real_of_num y1)) -> False.
Definition term72 (x0 : real) := fun y0 : real => (fun y1 : real => forall y2 : nat, ~ (real_lt y1 (real_mul (real_of_num y2) x0))) y0.
Definition term158 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term95 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term113 (x0 : real -> nat) := fun y0 : real => (fun y1 : real => fun y2 : nat => real_lt y1 (real_of_num y2)) y0 (x0 y0).
Definition term28 (x0 : real) (x1 : real) := fun y0 : nat => real_lt x0 (real_mul (real_of_num y0) x1).
Definition term129 := forall y0 : real, forall y1 : real, forall y2 : real, ((~ (real_lt (real_of_num (NUMERAL 0)) y2)) \/ ((real_lt (real_div y0 y2) y1) \/ (~ (real_lt y0 (real_mul y1 y2))))) /\ ((~ (real_lt (real_of_num (NUMERAL 0)) y2)) \/ ((~ (real_lt (real_div y0 y2) y1)) \/ (real_lt y0 (real_mul y1 y2)))).
Definition term127 (x0 : real) := forall y0 : real, forall y1 : real, ((~ (real_lt (real_of_num (NUMERAL 0)) y1)) \/ ((real_lt (real_div x0 y1) y0) \/ (~ (real_lt x0 (real_mul y0 y1))))) /\ ((~ (real_lt (real_of_num (NUMERAL 0)) y1)) \/ ((~ (real_lt (real_div x0 y1) y0)) \/ (real_lt x0 (real_mul y0 y1)))).
Definition term94 := forall y0 : real, forall y1 : real, forall y2 : real, (~ (real_lt (real_of_num (NUMERAL 0)) y2)) \/ (((real_lt (real_div y0 y2) y1) \/ (~ (real_lt y0 (real_mul y1 y2)))) /\ ((~ (real_lt (real_div y0 y2) y1)) \/ (real_lt y0 (real_mul y1 y2)))).
Definition term92 (x0 : real) := forall y0 : real, forall y1 : real, (~ (real_lt (real_of_num (NUMERAL 0)) y1)) \/ (((real_lt (real_div x0 y1) y0) \/ (~ (real_lt x0 (real_mul y0 y1)))) /\ ((~ (real_lt (real_div x0 y1) y0)) \/ (real_lt x0 (real_mul y0 y1)))).
Definition term26 := forall y0 : real, forall y1 : real, forall y2 : real, (real_lt (real_of_num (NUMERAL 0)) y2) -> (real_lt (real_div y0 y2) y1) = (real_lt y0 (real_mul y1 y2)).
Definition term24 (x0 : real) := forall y0 : real, forall y1 : real, (real_lt (real_of_num (NUMERAL 0)) y1) -> (real_lt (real_div x0 y1) y0) = (real_lt x0 (real_mul y0 y1)).
Definition term119 := exists y0 : real -> nat, forall y1 : real, real_lt y1 (real_of_num (y0 y1)).
Definition term100 := exists y0 : real -> nat, forall y1 : real, (fun y2 : real => fun y3 : nat => real_lt y2 (real_of_num y3)) y1 (y0 y1).
Definition term98 (x0 : type1622) := exists y0 : real -> nat, forall y1 : real, x0 y1 (y0 y1).
Definition term82 := exists y0 : real, exists y1 : real, (real_lt (real_of_num (NUMERAL 0)) y0) /\ (forall y2 : nat, ~ (real_lt y1 (real_mul (real_of_num y2) y0))).
Definition term12 := (forall y0 : real, forall y1 : real, forall y2 : real, (real_lt (real_of_num (NUMERAL 0)) y2) -> (real_lt (real_div y0 y2) y1) = (real_lt y0 (real_mul y1 y2))) -> (forall y0 : real, exists y1 : nat, real_lt y0 (real_of_num y1)) -> False.
Definition term68 (x0 : Prop) (x1 : real -> Prop) := exists y0 : real, x0 /\ (x1 y0).
Definition term141 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term15 := (~ (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) -> forall y1 : real, exists y2 : nat, real_lt y1 (real_mul (real_of_num y2) y0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_lt (real_of_num (NUMERAL 0)) y2) -> (real_lt (real_div y0 y2) y1) = (real_lt y0 (real_mul y1 y2))) -> ~ (forall y0 : real, exists y1 : nat, real_lt y0 (real_of_num y1)).
Definition term110 (x0 : real -> nat) (x1 : real) := (fun y0 : real => fun y1 : nat => real_lt y0 (real_of_num y1)) x1 (x0 x1).
Definition term54 (x0 : real) := and (real_lt (real_of_num (NUMERAL 0)) x0).
Definition term122 (x0 : real) := ~ (real_lt (real_of_num (NUMERAL 0)) x0).
Definition term116 (x0 : real -> nat) := forall y0 : real, real_lt y0 (real_of_num (x0 y0)).
Definition term138 (x0 : real -> nat) (x1 : real) (x2 : real) := real_lt (real_div x1 x2) (real_of_num (x0 (real_div x1 x2))).
Definition term56 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) /\ (exists y0 : real, forall y1 : nat, ~ (real_lt y0 (real_mul (real_of_num y1) x0))).
Definition term150 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((real_lt x0 (real_mul x1 x2)) \/ ((~ (real_lt (real_div x0 x2) x1)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) x2)))).
Definition term59 := exists y0 : real, ~ ((fun y1 : real => (real_lt (real_of_num (NUMERAL 0)) y1) -> forall y2 : real, exists y3 : nat, real_lt y2 (real_mul (real_of_num y3) y1)) y0).
Definition term48 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => exists y2 : nat, real_lt y1 (real_mul (real_of_num y2) x0)) y0).
Definition term83 (x0 : real) (x1 : real) (x2 : real) := real_lt (real_div x0 x1) x2.
Definition term39 (x0 : real) (x1 : real) (x2 : nat) := (fun y0 : nat => real_lt x0 (real_mul (real_of_num y0) x1)) x2.
Definition term90 (x0 : real) (x1 : real) := forall y0 : real, (~ (real_lt (real_of_num (NUMERAL 0)) y0)) \/ (((real_lt (real_div x0 y0) x1) \/ (~ (real_lt x0 (real_mul x1 y0)))) /\ ((~ (real_lt (real_div x0 y0) x1)) \/ (real_lt x0 (real_mul x1 y0)))).
Definition term111 (x0 : real -> nat) (x1 : real) := (fun y0 : nat => real_lt x1 (real_of_num y0)) (x0 x1).
Definition term51 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => exists y2 : nat, real_lt y1 (real_mul (real_of_num y2) x0)) y0).
Definition term147 (x0 : real) (x1 : real) (x2 : real) := (~ (real_lt (real_div x0 x2) x1)) \/ ((real_lt x0 (real_mul x1 x2)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) x2))).
Definition term143 (x0 : real) (x1 : real) (x2 : real) := ~ (real_lt (real_div x0 x1) x2).
Definition term41 (x0 : real) (x1 : nat) (x2 : real) := ~ (real_lt x0 (real_mul (real_of_num x1) x2)).
Definition term17 (x0 : real) := fun y0 : nat => real_lt x0 (real_of_num y0).
Definition term70 (x0 : real) := exists y0 : real, (real_lt (real_of_num (NUMERAL 0)) x0) /\ ((fun y1 : real => forall y2 : nat, ~ (real_lt y1 (real_mul (real_of_num y2) x0))) y0).
Definition term132 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((~ (real_lt (real_of_num (NUMERAL 0)) y0)) \/ ((real_lt (real_div x0 y0) x1) \/ (~ (real_lt x0 (real_mul x1 y0))))) /\ ((~ (real_lt (real_of_num (NUMERAL 0)) y0)) \/ ((~ (real_lt (real_div x0 y0) x1)) \/ (real_lt x0 (real_mul x1 y0))))) x2.
Definition term126 (x0 : real) := fun y0 : real => forall y1 : real, ((~ (real_lt (real_of_num (NUMERAL 0)) y1)) \/ ((real_lt (real_div x0 y1) y0) \/ (~ (real_lt x0 (real_mul y0 y1))))) /\ ((~ (real_lt (real_of_num (NUMERAL 0)) y1)) \/ ((~ (real_lt (real_div x0 y1) y0)) \/ (real_lt x0 (real_mul y0 y1)))).
Definition term91 (x0 : real) := fun y0 : real => forall y1 : real, (~ (real_lt (real_of_num (NUMERAL 0)) y1)) \/ (((real_lt (real_div x0 y1) y0) \/ (~ (real_lt x0 (real_mul y0 y1)))) /\ ((~ (real_lt (real_div x0 y1) y0)) \/ (real_lt x0 (real_mul y0 y1)))).
Definition term23 (x0 : real) := fun y0 : real => forall y1 : real, (real_lt (real_of_num (NUMERAL 0)) y1) -> (real_lt (real_div x0 y1) y0) = (real_lt x0 (real_mul y0 y1)).
Definition term115 (x0 : real -> nat) := forall y0 : real, (fun y1 : real => fun y2 : nat => real_lt y1 (real_of_num y2)) y0 (x0 y0).
Definition term8 := (forall y0 : real, exists y1 : nat, real_lt y0 (real_of_num y1)) -> False.
Definition term162 (x0 : real) := ~ (~ (real_lt (real_of_num (NUMERAL 0)) x0)).
Definition term57 (x0 : real) := ~ ((real_lt (real_of_num (NUMERAL 0)) x0) -> forall y0 : real, exists y1 : nat, real_lt y0 (real_mul (real_of_num y1) x0)).
Definition term120 (x0 : real) (x1 : real) (x2 : real) := ((~ (real_lt (real_of_num (NUMERAL 0)) x2)) \/ ((real_lt (real_div x0 x2) x1) \/ (~ (real_lt x0 (real_mul x1 x2))))) /\ ((~ (real_lt (real_of_num (NUMERAL 0)) x2)) \/ ((~ (real_lt (real_div x0 x2) x1)) \/ (real_lt x0 (real_mul x1 x2)))).
Definition term47 (x0 : real) := ~ (forall y0 : real, exists y1 : nat, real_lt y0 (real_mul (real_of_num y1) x0)).
Definition term9 := ~ (forall y0 : real, exists y1 : nat, real_lt y0 (real_of_num y1)).
Definition term32 (x0 : real) := imp (real_lt (real_of_num (NUMERAL 0)) x0).
Definition term109 := @eq Prop (forall y0 : real, exists y1 : nat, real_lt y0 (real_of_num y1)).
Definition term108 := @eq Prop (forall y0 : real, exists y1 : nat, (fun y2 : real => fun y3 : nat => real_lt y2 (real_of_num y3)) y0 y1).
Definition term43 (x0 : real) (x1 : real) := fun y0 : nat => ~ (real_lt x0 (real_mul (real_of_num y0) x1)).
Definition term157 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term40 (x0 : real) (x1 : real) (x2 : nat) := ~ ((fun y0 : nat => real_lt x0 (real_mul (real_of_num y0) x1)) x2).
Definition term35 (x0 : nat -> Prop) := ~ (ex x0).
Definition term16 (x0 : real) (x1 : nat) := real_lt x0 (real_of_num x1).
Definition term99 := forall y0 : real, exists y1 : nat, (fun y2 : real => fun y3 : nat => real_lt y2 (real_of_num y3)) y0 y1.
Definition term97 (x0 : type1622) := forall y0 : real, exists y1 : nat, x0 y0 y1.
Definition term31 (x0 : real) := forall y0 : real, exists y1 : nat, real_lt y0 (real_mul (real_of_num y1) x0).
Definition term10 := forall y0 : real, exists y1 : nat, real_lt y0 (real_of_num y1).
Definition term6 := (((~ (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) -> forall y1 : real, exists y2 : nat, real_lt y1 (real_mul (real_of_num y2) y0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_lt (real_of_num (NUMERAL 0)) y2) -> (real_lt (real_div y0 y2) y1) = (real_lt y0 (real_mul y1 y2))) -> (forall y0 : real, exists y1 : nat, real_lt y0 (real_of_num y1)) -> False) -> (~ (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) -> forall y1 : real, exists y2 : nat, real_lt y1 (real_mul (real_of_num y2) y0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_lt (real_of_num (NUMERAL 0)) y2) -> (real_lt (real_div y0 y2) y1) = (real_lt y0 (real_mul y1 y2))) -> (forall y0 : real, exists y1 : nat, real_lt y0 (real_of_num y1)) -> False) -> (~ (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) -> forall y1 : real, exists y2 : nat, real_lt y1 (real_mul (real_of_num y2) y0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_lt (real_of_num (NUMERAL 0)) y2) -> (real_lt (real_div y0 y2) y1) = (real_lt y0 (real_mul y1 y2))) -> (forall y0 : real, exists y1 : nat, real_lt y0 (real_of_num y1)) -> False.
Definition term79 (x0 : real) := fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) x0) /\ (forall y1 : nat, ~ (real_lt y0 (real_mul (real_of_num y1) x0))).
Definition term146 (x0 : real) (x1 : real) (x2 : real) := or (~ (real_lt (real_div x0 x1) x2)).
Definition term86 (x0 : real) := or (~ (real_lt (real_of_num (NUMERAL 0)) x0)).
Definition term63 := fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) y0) /\ (exists y1 : real, forall y2 : nat, ~ (real_lt y1 (real_mul (real_of_num y2) y0))).
Definition term46 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term85 (x0 : real) (x1 : real) (x2 : real) := ((real_lt (real_div x0 x2) x1) \/ (~ (real_lt x0 (real_mul x1 x2)))) /\ ((~ (real_lt (real_div x0 x2) x1)) \/ (real_lt x0 (real_mul x1 x2))).
Definition term36 (x0 : nat -> Prop) := forall y0 : nat, ~ (x0 y0).
Definition term102 (x0 : real) := (fun y0 : real => fun y1 : nat => real_lt y0 (real_of_num y1)) x0.
Definition term34 := fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) y0) -> forall y1 : real, exists y2 : nat, real_lt y1 (real_mul (real_of_num y2) y0).
Definition term77 (x0 : real) (x1 : real) := (real_lt (real_of_num (NUMERAL 0)) x1) /\ (forall y0 : nat, ~ (real_lt x0 (real_mul (real_of_num y0) x1))).
Definition term2 := (~ (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) -> forall y1 : real, exists y2 : nat, real_lt y1 (real_mul (real_of_num y2) y0))) -> False.
Definition term140 (x0 : real -> nat) (x1 : real) (x2 : real) := ~ (real_lt (real_div x1 x2) (real_of_num (x0 (real_div x1 x2)))).
Definition term55 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) /\ (~ (forall y0 : real, exists y1 : nat, real_lt y0 (real_mul (real_of_num y1) x0))).
Definition term84 (x0 : real) (x1 : real) (x2 : real) := real_lt x0 (real_mul x1 x2).
Definition term156 (x0 : real) (x1 : real) (x2 : real) := (~ ((~ (real_lt (real_of_num (NUMERAL 0)) x2)) \/ (~ (real_lt (real_div x0 x2) x1)))) -> real_lt x0 (real_mul x1 x2).
Definition term7 := (((~ (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) -> forall y1 : real, exists y2 : nat, real_lt y1 (real_mul (real_of_num y2) y0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_lt (real_of_num (NUMERAL 0)) y2) -> (real_lt (real_div y0 y2) y1) = (real_lt y0 (real_mul y1 y2))) -> (forall y0 : real, exists y1 : nat, real_lt y0 (real_of_num y1)) -> False) -> (~ (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) -> forall y1 : real, exists y2 : nat, real_lt y1 (real_mul (real_of_num y2) y0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_lt (real_of_num (NUMERAL 0)) y2) -> (real_lt (real_div y0 y2) y1) = (real_lt y0 (real_mul y1 y2))) -> (forall y0 : real, exists y1 : nat, real_lt y0 (real_of_num y1)) -> False) -> ((~ (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) -> forall y1 : real, exists y2 : nat, real_lt y1 (real_mul (real_of_num y2) y0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_lt (real_of_num (NUMERAL 0)) y2) -> (real_lt (real_div y0 y2) y1) = (real_lt y0 (real_mul y1 y2))) -> (forall y0 : real, exists y1 : nat, real_lt y0 (real_of_num y1)) -> False) -> (~ (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) -> forall y1 : real, exists y2 : nat, real_lt y1 (real_mul (real_of_num y2) y0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_lt (real_of_num (NUMERAL 0)) y2) -> (real_lt (real_div y0 y2) y1) = (real_lt y0 (real_mul y1 y2))) -> (forall y0 : real, exists y1 : nat, real_lt y0 (real_of_num y1)) -> False.
Definition term64 := exists y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) /\ (exists y1 : real, forall y2 : nat, ~ (real_lt y1 (real_mul (real_of_num y2) y0))).
Definition term163 (x0 : real) := and (~ (~ (real_lt (real_of_num (NUMERAL 0)) x0))).
Definition term104 (x0 : real) (x1 : nat) := (fun y0 : nat => real_lt x0 (real_of_num y0)) x1.
Definition term131 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((~ (real_lt (real_of_num (NUMERAL 0)) y1)) \/ ((real_lt (real_div x0 y1) y0) \/ (~ (real_lt x0 (real_mul y0 y1))))) /\ ((~ (real_lt (real_of_num (NUMERAL 0)) y1)) \/ ((~ (real_lt (real_div x0 y1) y0)) \/ (real_lt x0 (real_mul y0 y1))))) x1.
Definition term44 (x0 : real) (x1 : real) := forall y0 : nat, ~ (real_lt x0 (real_mul (real_of_num y0) x1)).
Definition term49 (x0 : real) (x1 : real) := (fun y0 : real => exists y1 : nat, real_lt y0 (real_mul (real_of_num y1) x0)) x1.
Definition term75 (x0 : real) := @eq Prop ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (exists y0 : real, forall y1 : nat, ~ (real_lt y0 (real_mul (real_of_num y1) x0)))).
Definition term74 (x0 : real) := @eq Prop ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (exists y0 : real, (fun y1 : real => forall y2 : nat, ~ (real_lt y1 (real_mul (real_of_num y2) x0))) y0)).
Definition term153 (x0 : real) (x1 : real) (x2 : real) := or (real_lt x0 (real_mul x1 x2)).
Definition term174 (x0 : real -> nat) (x1 : real) (x2 : real) := ~ (real_lt x1 (real_mul (real_of_num (x0 (real_div x1 x2))) x2)).
Definition term151 (x0 : real) (x1 : real) (x2 : real) := (~ (real_lt (real_of_num (NUMERAL 0)) x1)) \/ (~ (real_lt (real_div x0 x1) x2)).
Definition term76 (x0 : real) (x1 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) /\ ((fun y0 : real => forall y1 : nat, ~ (real_lt y0 (real_mul (real_of_num y1) x0))) x1).
Definition term58 (x0 : real) := real_lt (real_of_num (NUMERAL 0)) x0.
Definition term135 (x0 : real) (x1 : real) (x2 : real) := (~ (real_lt (real_of_num (NUMERAL 0)) x2)) \/ ((~ (real_lt (real_div x0 x2) x1)) \/ (real_lt x0 (real_mul x1 x2))).
Definition term18 (x0 : real) := exists y0 : nat, real_lt x0 (real_of_num y0).
Definition term19 := fun y0 : real => exists y1 : nat, real_lt y0 (real_of_num y1).
Definition term139 (x0 : real -> nat) (x1 : real) (x2 : real) := (~ (real_lt (real_div x1 x2) (real_of_num (x0 (real_div x1 x2))))) -> real_lt (real_div x1 x2) (real_of_num (x0 (real_div x1 x2))).
Definition term38 (x0 : real) (x1 : real) := forall y0 : nat, ~ ((fun y1 : nat => real_lt x0 (real_mul (real_of_num y1) x1)) y0).
Definition term176 (x0 : real -> nat) (x1 : real) (x2 : real) := (real_lt x1 (real_mul (real_of_num (x0 (real_div x1 x2))) x2)) -> False.
Definition term128 := fun y0 : real => forall y1 : real, forall y2 : real, ((~ (real_lt (real_of_num (NUMERAL 0)) y2)) \/ ((real_lt (real_div y0 y2) y1) \/ (~ (real_lt y0 (real_mul y1 y2))))) /\ ((~ (real_lt (real_of_num (NUMERAL 0)) y2)) \/ ((~ (real_lt (real_div y0 y2) y1)) \/ (real_lt y0 (real_mul y1 y2)))).
Definition term93 := fun y0 : real => forall y1 : real, forall y2 : real, (~ (real_lt (real_of_num (NUMERAL 0)) y2)) \/ (((real_lt (real_div y0 y2) y1) \/ (~ (real_lt y0 (real_mul y1 y2)))) /\ ((~ (real_lt (real_div y0 y2) y1)) \/ (real_lt y0 (real_mul y1 y2)))).
Definition term25 := fun y0 : real => forall y1 : real, forall y2 : real, (real_lt (real_of_num (NUMERAL 0)) y2) -> (real_lt (real_div y0 y2) y1) = (real_lt y0 (real_mul y1 y2)).
Definition term50 (x0 : real) (x1 : real) := ~ ((fun y0 : real => exists y1 : nat, real_lt y0 (real_mul (real_of_num y1) x0)) x1).
Definition term177 (x0 : real -> nat) (x1 : real) (x2 : real) := x0 (real_div x1 x2).
Definition term171 (x0 : real -> nat) (x1 : real) (x2 : real) := real_of_num (x0 (real_div x1 x2)).
Definition term118 := fun y0 : real -> nat => forall y1 : real, real_lt y1 (real_of_num (y0 y1)).
Definition term117 := fun y0 : real -> nat => forall y1 : real, (fun y2 : real => fun y3 : nat => real_lt y2 (real_of_num y3)) y1 (y0 y1).
Definition term154 (x0 : real) (x1 : real) (x2 : real) := (real_lt x0 (real_mul x2 x1)) \/ ((~ (real_lt (real_of_num (NUMERAL 0)) x1)) \/ (~ (real_lt (real_div x0 x1) x2))).
Definition term159 (x0 : real) (x1 : real) (x2 : real) := ~ ((~ (real_lt (real_of_num (NUMERAL 0)) x1)) \/ (~ (real_lt (real_div x0 x1) x2))).
Definition term1 := forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) -> forall y1 : real, exists y2 : nat, real_lt y1 (real_mul (real_of_num y2) y0).
Definition term78 (x0 : real) := fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) x0) /\ ((fun y1 : real => forall y2 : nat, ~ (real_lt y1 (real_mul (real_of_num y2) x0))) y0).
Definition term21 (x0 : real) (x1 : real) := fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) y0) -> (real_lt (real_div x0 y0) x1) = (real_lt x0 (real_mul x1 y0)).
Definition term160 (x0 : real) (x1 : real) (x2 : real) := (~ (~ (real_lt (real_of_num (NUMERAL 0)) x1))) /\ (~ (~ (real_lt (real_div x0 x1) x2))).
Definition term134 (x0 : real) (x1 : real) (x2 : nat) := (fun y0 : nat => ~ (real_lt x0 (real_mul (real_of_num y0) x1))) x2.
Definition term13 := (forall y0 : real, forall y1 : real, forall y2 : real, (real_lt (real_of_num (NUMERAL 0)) y2) -> (real_lt (real_div y0 y2) y1) = (real_lt y0 (real_mul y1 y2))) -> ~ (forall y0 : real, exists y1 : nat, real_lt y0 (real_of_num y1)).
Definition term145 (x0 : real) (x1 : real) (x2 : real) := (real_lt x0 (real_mul x1 x2)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) x2)).
Definition term125 (x0 : real) (x1 : real) := forall y0 : real, ((~ (real_lt (real_of_num (NUMERAL 0)) y0)) \/ ((real_lt (real_div x0 y0) x1) \/ (~ (real_lt x0 (real_mul x1 y0))))) /\ ((~ (real_lt (real_of_num (NUMERAL 0)) y0)) \/ ((~ (real_lt (real_div x0 y0) x1)) \/ (real_lt x0 (real_mul x1 y0)))).
Definition term61 (x0 : real) := ~ ((fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) y0) -> forall y1 : real, exists y2 : nat, real_lt y1 (real_mul (real_of_num y2) y0)) x0).
Definition term133 (x0 : real -> nat) (x1 : real) := (fun y0 : real => real_lt y0 (real_of_num (x0 y0))) x1.
Definition term170 (x0 : real -> nat) (x1 : real) (x2 : real) := ((real_lt (real_of_num (NUMERAL 0)) x2) /\ (real_lt (real_div x1 x2) (real_of_num (x0 (real_div x1 x2))))) -> real_lt x1 (real_mul (real_of_num (x0 (real_div x1 x2))) x2).
Definition term62 := fun y0 : real => ~ ((fun y1 : real => (real_lt (real_of_num (NUMERAL 0)) y1) -> forall y2 : real, exists y3 : nat, real_lt y2 (real_mul (real_of_num y3) y1)) y0).
Definition term149 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((~ (real_lt (real_of_num (NUMERAL 0)) x2)) \/ ((~ (real_lt (real_div x0 x2) x1)) \/ (real_lt x0 (real_mul x1 x2)))).
Definition term114 (x0 : real -> nat) := fun y0 : real => real_lt y0 (real_of_num (x0 y0)).
Definition term142 (x0 : real) (x1 : real) (x2 : real) := (~ (real_lt (real_div x0 x2) x1)) \/ ((~ (real_lt (real_of_num (NUMERAL 0)) x2)) \/ (real_lt x0 (real_mul x1 x2))).
Definition term80 (x0 : real) := exists y0 : real, (real_lt (real_of_num (NUMERAL 0)) x0) /\ (forall y1 : nat, ~ (real_lt y0 (real_mul (real_of_num y1) x0))).
Definition term42 (x0 : real) (x1 : real) := fun y0 : nat => ~ ((fun y1 : nat => real_lt x0 (real_mul (real_of_num y1) x1)) y0).
Definition term172 (x0 : real -> nat) (x1 : real) (x2 : real) := real_lt x1 (real_mul (real_of_num (x0 (real_div x1 x2))) x2).
Definition term124 (x0 : real) (x1 : real) := fun y0 : real => ((~ (real_lt (real_of_num (NUMERAL 0)) y0)) \/ ((real_lt (real_div x0 y0) x1) \/ (~ (real_lt x0 (real_mul x1 y0))))) /\ ((~ (real_lt (real_of_num (NUMERAL 0)) y0)) \/ ((~ (real_lt (real_div x0 y0) x1)) \/ (real_lt x0 (real_mul x1 y0)))).
Definition term30 (x0 : real) := fun y0 : real => exists y1 : nat, real_lt y0 (real_mul (real_of_num y1) x0).
Definition term69 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) /\ (exists y0 : real, (fun y1 : real => forall y2 : nat, ~ (real_lt y1 (real_mul (real_of_num y2) x0))) y0).
Definition term96 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term130 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((~ (real_lt (real_of_num (NUMERAL 0)) y2)) \/ ((real_lt (real_div y0 y2) y1) \/ (~ (real_lt y0 (real_mul y1 y2))))) /\ ((~ (real_lt (real_of_num (NUMERAL 0)) y2)) \/ ((~ (real_lt (real_div y0 y2) y1)) \/ (real_lt y0 (real_mul y1 y2))))) x0.
Definition term4 := (~ (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) -> forall y1 : real, exists y2 : nat, real_lt y1 (real_mul (real_of_num y2) y0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_lt (real_of_num (NUMERAL 0)) y2) -> (real_lt (real_div y0 y2) y1) = (real_lt y0 (real_mul y1 y2))) -> (forall y0 : real, exists y1 : nat, real_lt y0 (real_of_num y1)) -> False.
Definition term20 (x0 : real) (x1 : real) (x2 : real) := (real_lt (real_of_num (NUMERAL 0)) x2) -> (real_lt (real_div x0 x2) x1) = (real_lt x0 (real_mul x1 x2)).
Definition term37 (x0 : real) (x1 : real) := ~ (exists y0 : nat, real_lt x0 (real_mul (real_of_num y0) x1)).
Definition term14 := imp (~ (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) -> forall y1 : real, exists y2 : nat, real_lt y1 (real_mul (real_of_num y2) y0))).
Definition term167 (x0 : real) (x1 : real) (x2 : real) := imp ((real_lt (real_of_num (NUMERAL 0)) x1) /\ (real_lt (real_div x0 x1) x2)).
Definition term152 (x0 : real) (x1 : real) (x2 : real) := (~ (real_lt (real_div x0 x2) x1)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) x2)).
Definition term73 (x0 : real) := exists y0 : real, (fun y1 : real => forall y2 : nat, ~ (real_lt y1 (real_mul (real_of_num y2) x0))) y0.
