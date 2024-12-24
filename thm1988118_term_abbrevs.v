Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term79 (x0 : real) (x1 : real) := ((real_sub x0 x1) = (real_of_num (NUMERAL 0))) /\ (exists y0 : real, (real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term19 (x0 : real) := forall y0 : real, ((real_sub x0 y0) = (real_of_num (NUMERAL 0))) = (x0 = y0).
Definition term92 (x0 : real) (x1 : real) := exists y0 : real, ((real_sub x0 x1) = (real_of_num (NUMERAL 0))) /\ ((fun y1 : real => (real_mul (real_sub x0 x1) y1) = (real_of_num (NUMERAL (BIT1 0)))) y0).
Definition term91 (x0 : real) (x1 : real) := ((real_sub x0 x1) = (real_of_num (NUMERAL 0))) /\ (exists y0 : real, (fun y1 : real => (real_mul (real_sub x0 x1) y1) = (real_of_num (NUMERAL (BIT1 0)))) y0).
Definition term117 (x0 : real) (x1 : real) := fun y0 : real => ((~ ((real_sub x0 x1) = (real_of_num (NUMERAL 0)))) /\ (forall y1 : real, ~ ((real_mul (real_sub x0 x1) y1) = (real_of_num (NUMERAL (BIT1 0)))))) \/ (((real_sub x0 x1) = (real_of_num (NUMERAL 0))) /\ ((real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0))))).
Definition term16 := ~ ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0))).
Definition term41 := forall y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul y0 (real_inv y0)) = (real_of_num (NUMERAL (BIT1 0))).
Definition term144 := (~ False) -> False.
Definition term197 (x0 : real) := (~ ((real_mul (real_of_num (NUMERAL 0)) x0) = (real_of_num (NUMERAL 0)))) -> (real_mul (real_of_num (NUMERAL 0)) x0) = (real_of_num (NUMERAL 0)).
Definition term37 (x0 : real) (x1 : real) := (((~ ((~ ((real_sub x0 x1) = (real_of_num (NUMERAL 0)))) = (exists y0 : real, (real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0)))))) -> (~ ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0)))) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul y0 (real_inv y0)) = (real_of_num (NUMERAL (BIT1 0)))) -> False) -> (~ ((~ ((real_sub x0 x1) = (real_of_num (NUMERAL 0)))) = (exists y0 : real, (real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0)))))) -> (~ ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0)))) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul y0 (real_inv y0)) = (real_of_num (NUMERAL (BIT1 0)))) -> False) -> (~ ((~ ((real_sub x0 x1) = (real_of_num (NUMERAL 0)))) = (exists y0 : real, (real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0)))))) -> (~ ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0)))) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul y0 (real_inv y0)) = (real_of_num (NUMERAL (BIT1 0)))) -> False.
Definition term138 (x0 : real) (x1 : real) := (~ ((real_mul (real_sub x0 x1) (real_inv (real_sub x0 x1))) = (real_of_num (NUMERAL (BIT1 0))))) -> (real_mul (real_sub x0 x1) (real_inv (real_sub x0 x1))) = (real_of_num (NUMERAL (BIT1 0))).
Definition term136 (x0 : real) (x1 : real) := (~ ((real_sub x0 x1) = (real_of_num (NUMERAL 0)))) -> (real_mul (real_sub x0 x1) (real_inv (real_sub x0 x1))) = (real_of_num (NUMERAL (BIT1 0))).
Definition term77 (x0 : real) (x1 : real) := and ((real_sub x0 x1) = (real_of_num (NUMERAL 0))).
Definition term0 (x0 : Prop) := ~ (~ x0).
Definition term3 := real_of_num (NUMERAL 0).
Definition term89 (x0 : Prop) (x1 : real -> Prop) := x0 /\ (exists y0 : real, x1 y0).
Definition term166 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (~ (x0 = x1))) /\ (~ (~ (x2 = x3))).
Definition term188 (x0 : real) (x1 : real) (x2 : real) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term102 (x0 : real) (x1 : real) := ((~ ((real_sub x0 x1) = (real_of_num (NUMERAL 0)))) /\ (forall y0 : real, ~ ((real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0)))))) \/ (exists y0 : real, ((real_sub x0 x1) = (real_of_num (NUMERAL 0))) /\ ((real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0))))).
Definition term160 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := @eq Prop (((real_mul x0 x2) = (real_mul x1 x3)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3)))).
Definition term137 (x0 : real) (x1 : real) := real_mul (real_sub x0 x1) (real_inv (real_sub x0 x1)).
Definition term194 (x0 : real) (x1 : real) (x2 : real) := (((real_mul (real_sub x0 x1) x2) = (real_mul (real_of_num (NUMERAL 0)) x2)) /\ ((real_mul (real_sub x0 x1) x2) = (real_of_num (NUMERAL (BIT1 0))))) -> (real_mul (real_of_num (NUMERAL 0)) x2) = (real_of_num (NUMERAL (BIT1 0))).
Definition term62 := forall y0 : real, (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0)).
Definition term50 (x0 : real) := fun y0 : real => (~ ((~ ((real_sub y0 x0) = (real_of_num (NUMERAL 0)))) = (exists y1 : real, (real_mul (real_sub y0 x0) y1) = (real_of_num (NUMERAL (BIT1 0)))))) -> (~ ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0)))) -> (forall y1 : real, (real_mul (real_of_num (NUMERAL 0)) y1) = (real_of_num (NUMERAL 0))) -> (forall y1 : real, (~ (y1 = (real_of_num (NUMERAL 0)))) -> (real_mul y1 (real_inv y1)) = (real_of_num (NUMERAL (BIT1 0)))) -> False.
Definition term178 (x0 : real) (x1 : real) (x2 : real) := (~ ((real_mul (real_sub x0 x1) x2) = (real_of_num (NUMERAL (BIT1 0))))) -> (real_mul (real_sub x0 x1) x2) = (real_of_num (NUMERAL (BIT1 0))).
Definition term113 (x0 : real) (x1 : real) := @eq Prop (((~ ((real_sub x0 x1) = (real_of_num (NUMERAL 0)))) /\ (forall y0 : real, ~ ((real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0)))))) \/ (exists y0 : real, ((real_sub x0 x1) = (real_of_num (NUMERAL 0))) /\ ((real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0)))))).
Definition term112 (x0 : real) (x1 : real) := @eq Prop (((~ ((real_sub x0 x1) = (real_of_num (NUMERAL 0)))) /\ (forall y0 : real, ~ ((real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0)))))) \/ (exists y0 : real, (fun y1 : real => ((real_sub x0 x1) = (real_of_num (NUMERAL 0))) /\ ((real_mul (real_sub x0 x1) y1) = (real_of_num (NUMERAL (BIT1 0))))) y0)).
Definition term43 := (forall y0 : real, (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul y0 (real_inv y0)) = (real_of_num (NUMERAL (BIT1 0)))) -> False.
Definition term88 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term32 (x0 : Prop) := (~ x0) -> False.
Definition term190 (x0 : real) (x1 : real) (x2 : real) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term171 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := imp (~ ((~ (x0 = x1)) \/ (~ (x2 = x3)))).
Definition term40 := ~ (forall y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul y0 (real_inv y0)) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term134 (x0 : real) := @eq Prop ((x0 = (real_of_num (NUMERAL 0))) \/ ((real_mul x0 (real_inv x0)) = (real_of_num (NUMERAL (BIT1 0))))).
Definition term58 (x0 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_mul x0 (real_inv x0)) = (real_of_num (NUMERAL (BIT1 0))).
Definition term116 (x0 : real) (x1 : real) := fun y0 : real => ((~ ((real_sub x0 x1) = (real_of_num (NUMERAL 0)))) /\ (forall y1 : real, ~ ((real_mul (real_sub x0 x1) y1) = (real_of_num (NUMERAL (BIT1 0)))))) \/ ((fun y1 : real => ((real_sub x0 x1) = (real_of_num (NUMERAL 0))) /\ ((real_mul (real_sub x0 x1) y1) = (real_of_num (NUMERAL (BIT1 0))))) y0).
Definition term49 (x0 : real) (x1 : real) := (~ ((~ ((real_sub x0 x1) = (real_of_num (NUMERAL 0)))) = (exists y0 : real, (real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0)))))) -> (~ ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0)))) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) -> ~ (forall y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul y0 (real_inv y0)) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term127 := forall y0 : real, (y0 = (real_of_num (NUMERAL 0))) \/ ((real_mul y0 (real_inv y0)) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term35 (x0 : real) (x1 : real) := (~ ((~ ((real_sub x0 x1) = (real_of_num (NUMERAL 0)))) = (exists y0 : real, (real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0)))))) -> (~ ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0)))) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul y0 (real_inv y0)) = (real_of_num (NUMERAL (BIT1 0)))) -> False.
Definition term63 (x0 : real) (x1 : real) (x2 : real) := real_mul (real_sub x0 x1) x2.
Definition term93 (x0 : real) (x1 : real) := fun y0 : real => (fun y1 : real => (real_mul (real_sub x0 x1) y1) = (real_of_num (NUMERAL (BIT1 0)))) y0.
Definition term135 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term139 (x0 : real) (x1 : real) := ~ ((real_mul (real_sub x0 x1) (real_inv (real_sub x0 x1))) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term87 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term152 (x0 : real) := (~ (x0 = x0)) -> x0 = x0.
Definition term53 (x0 : real) := forall y0 : real, (~ ((~ ((real_sub y0 x0) = (real_of_num (NUMERAL 0)))) = (exists y1 : real, (real_mul (real_sub y0 x0) y1) = (real_of_num (NUMERAL (BIT1 0)))))) -> (~ ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0)))) -> (forall y1 : real, (real_mul (real_of_num (NUMERAL 0)) y1) = (real_of_num (NUMERAL 0))) -> ~ (forall y1 : real, (~ (y1 = (real_of_num (NUMERAL 0)))) -> (real_mul y1 (real_inv y1)) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term52 (x0 : real) := forall y0 : real, (~ ((~ ((real_sub y0 x0) = (real_of_num (NUMERAL 0)))) = (exists y1 : real, (real_mul (real_sub y0 x0) y1) = (real_of_num (NUMERAL (BIT1 0)))))) -> (~ ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0)))) -> (forall y1 : real, (real_mul (real_of_num (NUMERAL 0)) y1) = (real_of_num (NUMERAL 0))) -> (forall y1 : real, (~ (y1 = (real_of_num (NUMERAL 0)))) -> (real_mul y1 (real_inv y1)) = (real_of_num (NUMERAL (BIT1 0)))) -> False.
Definition term129 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ~ ((real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0))))) x2.
Definition term140 (x0 : Prop) := (~ x0) -> x0.
Definition term172 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := imp ((x0 = x1) /\ (x2 = x3)).
Definition term186 (x0 : real) (x1 : real) (x2 : real) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term100 (x0 : real) (x1 : real) := fun y0 : real => ((real_sub x0 x1) = (real_of_num (NUMERAL 0))) /\ ((real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term164 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term148 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (x0 = x2) -> (~ (x1 = x3)) \/ ((real_mul x0 x1) = (real_mul x2 x3)).
Definition term84 (x0 : real) (x1 : real) := or ((~ ((real_sub x0 x1) = (real_of_num (NUMERAL 0)))) /\ (forall y0 : real, ~ ((real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0)))))).
Definition term183 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term174 (x0 : real) (x1 : real) (x2 : real) := ((real_sub x0 x1) = (real_of_num (NUMERAL 0))) /\ (x2 = x2).
Definition term173 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((x0 = x2) /\ (x1 = x3)) -> (real_mul x0 x1) = (real_mul x2 x3).
Definition term111 (x0 : real) (x1 : real) := exists y0 : real, (fun y1 : real => ((real_sub x0 x1) = (real_of_num (NUMERAL 0))) /\ ((real_mul (real_sub x0 x1) y1) = (real_of_num (NUMERAL (BIT1 0))))) y0.
Definition term94 (x0 : real) (x1 : real) := exists y0 : real, (fun y1 : real => (real_mul (real_sub x0 x1) y1) = (real_of_num (NUMERAL (BIT1 0)))) y0.
Definition term6 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term206 := forall y0 : real, forall y1 : real, (~ (y0 = y1)) = (exists y2 : real, (real_mul (real_sub y0 y1) y2) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term57 := forall y0 : real, forall y1 : real, (~ ((~ ((real_sub y1 y0) = (real_of_num (NUMERAL 0)))) = (exists y2 : real, (real_mul (real_sub y1 y0) y2) = (real_of_num (NUMERAL (BIT1 0)))))) -> (~ ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0)))) -> (forall y2 : real, (real_mul (real_of_num (NUMERAL 0)) y2) = (real_of_num (NUMERAL 0))) -> ~ (forall y2 : real, (~ (y2 = (real_of_num (NUMERAL 0)))) -> (real_mul y2 (real_inv y2)) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term56 := forall y0 : real, forall y1 : real, (~ ((~ ((real_sub y1 y0) = (real_of_num (NUMERAL 0)))) = (exists y2 : real, (real_mul (real_sub y1 y0) y2) = (real_of_num (NUMERAL (BIT1 0)))))) -> (~ ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0)))) -> (forall y2 : real, (real_mul (real_of_num (NUMERAL 0)) y2) = (real_of_num (NUMERAL 0))) -> (forall y2 : real, (~ (y2 = (real_of_num (NUMERAL 0)))) -> (real_mul y2 (real_inv y2)) = (real_of_num (NUMERAL (BIT1 0)))) -> False.
Definition term24 := forall y0 : real, forall y1 : real, (y0 = y1) = ((real_sub y0 y1) = (real_of_num (NUMERAL 0))).
Definition term23 := forall y0 : real, forall y1 : real, ((real_sub y0 y1) = (real_of_num (NUMERAL 0))) = (y0 = y1).
Definition term97 (x0 : real) (x1 : real) (x2 : real) := ((real_sub x0 x1) = (real_of_num (NUMERAL 0))) /\ ((fun y0 : real => (real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0)))) x2).
Definition term184 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term201 := (~ ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0)))) -> (real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0)).
Definition term67 (x0 : real -> Prop) := forall y0 : real, ~ (x0 y0).
Definition term90 (x0 : Prop) (x1 : real -> Prop) := exists y0 : real, x0 /\ (x1 y0).
Definition term157 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term51 (x0 : real) := fun y0 : real => (~ ((~ ((real_sub y0 x0) = (real_of_num (NUMERAL 0)))) = (exists y1 : real, (real_mul (real_sub y0 x0) y1) = (real_of_num (NUMERAL (BIT1 0)))))) -> (~ ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0)))) -> (forall y1 : real, (real_mul (real_of_num (NUMERAL 0)) y1) = (real_of_num (NUMERAL 0))) -> ~ (forall y1 : real, (~ (y1 = (real_of_num (NUMERAL 0)))) -> (real_mul y1 (real_inv y1)) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term107 (x0 : real) (x1 : real) := ((~ ((real_sub x0 x1) = (real_of_num (NUMERAL 0)))) /\ (forall y0 : real, ~ ((real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0)))))) \/ (exists y0 : real, (fun y1 : real => ((real_sub x0 x1) = (real_of_num (NUMERAL 0))) /\ ((real_mul (real_sub x0 x1) y1) = (real_of_num (NUMERAL (BIT1 0))))) y0).
Definition term158 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((real_mul x0 x2) = (real_mul x1 x3)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3))).
Definition term65 (x0 : real) (x1 : real) := ~ (~ ((real_sub x0 x1) = (real_of_num (NUMERAL 0)))).
Definition term151 (x0 : real) (x1 : real) := (~ ((real_sub x0 x1) = (real_of_num (NUMERAL 0)))) -> (real_sub x0 x1) = (real_of_num (NUMERAL 0)).
Definition term125 (x0 : real) := ~ (x0 = (real_of_num (NUMERAL 0))).
Definition term124 (x0 : real) := (x0 = (real_of_num (NUMERAL 0))) \/ ((real_mul x0 (real_inv x0)) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term161 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ ((~ (x0 = x2)) \/ (~ (x1 = x3)))) -> (real_mul x0 x1) = (real_mul x2 x3).
Definition term108 (x0 : real) (x1 : real) := exists y0 : real, ((~ ((real_sub x0 x1) = (real_of_num (NUMERAL 0)))) /\ (forall y1 : real, ~ ((real_mul (real_sub x0 x1) y1) = (real_of_num (NUMERAL (BIT1 0)))))) \/ ((fun y1 : real => ((real_sub x0 x1) = (real_of_num (NUMERAL 0))) /\ ((real_mul (real_sub x0 x1) y1) = (real_of_num (NUMERAL (BIT1 0))))) y0).
Definition term150 (x0 : real) (x1 : real) (x2 : real) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term175 (x0 : real) (x1 : real) (x2 : real) := (((real_sub x0 x1) = (real_of_num (NUMERAL 0))) /\ (x2 = x2)) -> (real_mul (real_sub x0 x1) x2) = (real_mul (real_of_num (NUMERAL 0)) x2).
Definition term123 (x0 : real) := (~ (~ (x0 = (real_of_num (NUMERAL 0))))) \/ ((real_mul x0 (real_inv x0)) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term55 := fun y0 : real => forall y1 : real, (~ ((~ ((real_sub y1 y0) = (real_of_num (NUMERAL 0)))) = (exists y2 : real, (real_mul (real_sub y1 y0) y2) = (real_of_num (NUMERAL (BIT1 0)))))) -> (~ ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0)))) -> (forall y2 : real, (real_mul (real_of_num (NUMERAL 0)) y2) = (real_of_num (NUMERAL 0))) -> ~ (forall y2 : real, (~ (y2 = (real_of_num (NUMERAL 0)))) -> (real_mul y2 (real_inv y2)) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term54 := fun y0 : real => forall y1 : real, (~ ((~ ((real_sub y1 y0) = (real_of_num (NUMERAL 0)))) = (exists y2 : real, (real_mul (real_sub y1 y0) y2) = (real_of_num (NUMERAL (BIT1 0)))))) -> (~ ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0)))) -> (forall y2 : real, (real_mul (real_of_num (NUMERAL 0)) y2) = (real_of_num (NUMERAL 0))) -> (forall y2 : real, (~ (y2 = (real_of_num (NUMERAL 0)))) -> (real_mul y2 (real_inv y2)) = (real_of_num (NUMERAL (BIT1 0)))) -> False.
Definition term22 := fun y0 : real => forall y1 : real, (y0 = y1) = ((real_sub y0 y1) = (real_of_num (NUMERAL 0))).
Definition term195 (x0 : real) := (~ ((real_mul (real_of_num (NUMERAL 0)) x0) = (real_of_num (NUMERAL (BIT1 0))))) -> (real_mul (real_of_num (NUMERAL 0)) x0) = (real_of_num (NUMERAL (BIT1 0))).
Definition term80 (x0 : real) (x1 : real) := and (~ ((real_sub x0 x1) = (real_of_num (NUMERAL 0)))).
Definition term205 (x0 : real) := forall y0 : real, (~ (x0 = y0)) = (exists y1 : real, (real_mul (real_sub x0 y0) y1) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term27 (x0 : real) (x1 : real) := ~ (x0 = x1).
Definition term38 (x0 : real) (x1 : real) := (((~ ((~ ((real_sub x0 x1) = (real_of_num (NUMERAL 0)))) = (exists y0 : real, (real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0)))))) -> (~ ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0)))) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul y0 (real_inv y0)) = (real_of_num (NUMERAL (BIT1 0)))) -> False) -> (~ ((~ ((real_sub x0 x1) = (real_of_num (NUMERAL 0)))) = (exists y0 : real, (real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0)))))) -> (~ ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0)))) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul y0 (real_inv y0)) = (real_of_num (NUMERAL (BIT1 0)))) -> False) -> ((~ ((~ ((real_sub x0 x1) = (real_of_num (NUMERAL 0)))) = (exists y0 : real, (real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0)))))) -> (~ ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0)))) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul y0 (real_inv y0)) = (real_of_num (NUMERAL (BIT1 0)))) -> False) -> (~ ((~ ((real_sub x0 x1) = (real_of_num (NUMERAL 0)))) = (exists y0 : real, (real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0)))))) -> (~ ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0)))) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul y0 (real_inv y0)) = (real_of_num (NUMERAL (BIT1 0)))) -> False.
Definition term7 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term193 (x0 : real) (x1 : real) (x2 : real) := ((real_mul (real_sub x0 x1) x2) = (real_mul (real_of_num (NUMERAL 0)) x2)) /\ ((real_mul (real_sub x0 x1) x2) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term131 (x0 : real) (x1 : real) := ((real_sub x0 x1) = (real_of_num (NUMERAL 0))) -> ~ ((real_sub x0 x1) = (real_of_num (NUMERAL 0))).
Definition term72 (x0 : real) (x1 : real) (x2 : real) := ~ ((real_mul (real_sub x0 x1) x2) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term180 (x0 : real) (x1 : real) (x2 : real) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term78 (x0 : real) (x1 : real) := (~ (~ ((real_sub x0 x1) = (real_of_num (NUMERAL 0))))) /\ (exists y0 : real, (real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term104 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 \/ (x1 y0).
Definition term44 := (forall y0 : real, (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) -> ~ (forall y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul y0 (real_inv y0)) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term114 (x0 : real) (x1 : real) (x2 : real) := ((~ ((real_sub x0 x1) = (real_of_num (NUMERAL 0)))) /\ (forall y0 : real, ~ ((real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0)))))) \/ ((fun y0 : real => ((real_sub x0 x1) = (real_of_num (NUMERAL 0))) /\ ((real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0))))) x2).
Definition term120 (x0 : real) := real_mul x0 (real_inv x0).
Definition term163 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term126 := fun y0 : real => (y0 = (real_of_num (NUMERAL 0))) \/ ((real_mul y0 (real_inv y0)) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term199 (x0 : real) := ((real_mul (real_of_num (NUMERAL 0)) x0) = (real_of_num (NUMERAL (BIT1 0)))) /\ ((real_mul (real_of_num (NUMERAL 0)) x0) = (real_of_num (NUMERAL 0))).
Definition term103 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 \/ (exists y0 : a0, x1 y0).
Definition term28 (x0 : real) (x1 : real) := ~ ((real_sub x0 x1) = (real_of_num (NUMERAL 0))).
Definition term85 (x0 : real) (x1 : real) := ((~ ((real_sub x0 x1) = (real_of_num (NUMERAL 0)))) /\ (~ (exists y0 : real, (real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0)))))) \/ ((~ (~ ((real_sub x0 x1) = (real_of_num (NUMERAL 0))))) /\ (exists y0 : real, (real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0))))).
Definition term46 := (~ ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0)))) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul y0 (real_inv y0)) = (real_of_num (NUMERAL (BIT1 0)))) -> False.
Definition term82 (x0 : real) (x1 : real) := (~ ((real_sub x0 x1) = (real_of_num (NUMERAL 0)))) /\ (forall y0 : real, ~ ((real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0))))).
Definition term66 (x0 : real -> Prop) := ~ (ex x0).
Definition term159 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := @eq Prop ((~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ ((real_mul x0 x1) = (real_mul x2 x3)))).
Definition term45 := imp (~ ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0)))).
Definition term61 := fun y0 : real => (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0)).
Definition term21 := fun y0 : real => forall y1 : real, ((real_sub y0 y1) = (real_of_num (NUMERAL 0))) = (y0 = y1).
Definition term39 := (forall y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul y0 (real_inv y0)) = (real_of_num (NUMERAL (BIT1 0)))) -> False.
Definition term71 (x0 : real) (x1 : real) (x2 : real) := ~ ((fun y0 : real => (real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0)))) x2).
Definition term145 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (x1 = x3) -> (real_mul x0 x1) = (real_mul x2 x3).
Definition term203 (x0 : real) := (fun y0 : real => forall y1 : real, (~ ((~ ((real_sub y1 y0) = (real_of_num (NUMERAL 0)))) = (exists y2 : real, (real_mul (real_sub y1 y0) y2) = (real_of_num (NUMERAL (BIT1 0)))))) -> (~ ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0)))) -> (forall y2 : real, (real_mul (real_of_num (NUMERAL 0)) y2) = (real_of_num (NUMERAL 0))) -> (forall y2 : real, (~ (y2 = (real_of_num (NUMERAL 0)))) -> (real_mul y2 (real_inv y2)) = (real_of_num (NUMERAL (BIT1 0)))) -> False) x0.
Definition term25 (x0 : real) := (fun y0 : real => forall y1 : real, (y0 = y1) = ((real_sub y0 y1) = (real_of_num (NUMERAL 0)))) x0.
Definition term26 (x0 : real) (x1 : real) := (fun y0 : real => (x0 = y0) = ((real_sub x0 y0) = (real_of_num (NUMERAL 0)))) x1.
Definition term76 (x0 : real) (x1 : real) := and (~ (~ ((real_sub x0 x1) = (real_of_num (NUMERAL 0))))).
Definition term105 (x0 : Prop) (x1 : real -> Prop) := x0 \/ (exists y0 : real, x1 y0).
Definition term147 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x1 = x3)) \/ ((real_mul x0 x1) = (real_mul x2 x3)).
Definition term200 (x0 : real) := (((real_mul (real_of_num (NUMERAL 0)) x0) = (real_of_num (NUMERAL (BIT1 0)))) /\ ((real_mul (real_of_num (NUMERAL 0)) x0) = (real_of_num (NUMERAL 0)))) -> (real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0)).
Definition term13 := S (Nat.add 0 0).
Definition term98 (x0 : real) (x1 : real) (x2 : real) := ((real_sub x0 x1) = (real_of_num (NUMERAL 0))) /\ ((real_mul (real_sub x0 x1) x2) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term189 (x0 : real) (x1 : real) (x2 : real) := (x1 = x0) /\ (x1 = x2).
Definition term75 (x0 : real) (x1 : real) := forall y0 : real, ~ ((real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term17 (x0 : real) := fun y0 : real => ((real_sub x0 y0) = (real_of_num (NUMERAL 0))) = (x0 = y0).
Definition term10 := real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term130 (x0 : real) := (fun y0 : real => (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) x0.
Definition term182 (x0 : real) (x1 : real) (x2 : real) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term181 (x0 : real) (x1 : real) (x2 : real) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term31 (x0 : real) (x1 : real) := exists y0 : real, (real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0))).
Definition term168 (x0 : real) (x1 : real) := and (~ (~ (x0 = x1))).
Definition term70 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0)))) x2.
Definition term4 := real_sub (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term30 (x0 : real) (x1 : real) := @eq Prop (~ ((real_sub x0 x1) = (real_of_num (NUMERAL 0)))).
Definition term128 (x0 : real) := (fun y0 : real => (y0 = (real_of_num (NUMERAL 0))) \/ ((real_mul y0 (real_inv y0)) = (real_of_num (NUMERAL (BIT1 0))))) x0.
Definition term115 (x0 : real) (x1 : real) (x2 : real) := ((~ ((real_sub x0 x1) = (real_of_num (NUMERAL 0)))) /\ (forall y0 : real, ~ ((real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0)))))) \/ (((real_sub x0 x1) = (real_of_num (NUMERAL 0))) /\ ((real_mul (real_sub x0 x1) x2) = (real_of_num (NUMERAL (BIT1 0))))).
Definition term106 (x0 : Prop) (x1 : real -> Prop) := exists y0 : real, x0 \/ (x1 y0).
Definition term86 (x0 : real) (x1 : real) := ((~ ((real_sub x0 x1) = (real_of_num (NUMERAL 0)))) /\ (forall y0 : real, ~ ((real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0)))))) \/ (((real_sub x0 x1) = (real_of_num (NUMERAL 0))) /\ (exists y0 : real, (real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0))))).
Definition term156 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x0 = x1)) \/ (((real_mul x0 x2) = (real_mul x1 x3)) \/ (~ (x2 = x3))).
Definition term143 (x0 : real) (x1 : real) := real_inv (real_sub x0 x1).
Definition term142 (x0 : real) (x1 : real) := ((real_mul (real_sub x0 x1) (real_inv (real_sub x0 x1))) = (real_of_num (NUMERAL (BIT1 0)))) -> False.
Definition term5 := real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term11 := @eq real (real_sub (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))).
Definition term81 (x0 : real) (x1 : real) := (~ ((real_sub x0 x1) = (real_of_num (NUMERAL 0)))) /\ (~ (exists y0 : real, (real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0))))).
Definition term99 (x0 : real) (x1 : real) := fun y0 : real => ((real_sub x0 x1) = (real_of_num (NUMERAL 0))) /\ ((fun y1 : real => (real_mul (real_sub x0 x1) y1) = (real_of_num (NUMERAL (BIT1 0)))) y0).
Definition term154 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((real_mul x0 x2) = (real_mul x1 x3)) \/ (~ (x2 = x3)).
Definition term1 := ~ (~ ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0)))).
Definition term141 (x0 : real) (x1 : real) (x2 : real) := ((real_mul (real_sub x0 x1) x2) = (real_of_num (NUMERAL (BIT1 0)))) -> False.
Definition term170 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (x0 = x1) /\ (x2 = x3).
Definition term192 (x0 : real) (x1 : real) (x2 : real) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term187 (x0 : real) (x1 : real) (x2 : real) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term165 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ~ ((~ (x0 = x1)) \/ (~ (x2 = x3))).
Definition term198 (x0 : real) := ~ ((real_mul (real_of_num (NUMERAL 0)) x0) = (real_of_num (NUMERAL 0))).
Definition term2 := real_of_num (NUMERAL (BIT1 0)).
Definition term185 (x0 : real) (x1 : real) (x2 : real) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term47 := (~ ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0)))) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) -> ~ (forall y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul y0 (real_inv y0)) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term110 (x0 : real) (x1 : real) := fun y0 : real => (fun y1 : real => ((real_sub x0 x1) = (real_of_num (NUMERAL 0))) /\ ((real_mul (real_sub x0 x1) y1) = (real_of_num (NUMERAL (BIT1 0))))) y0.
Definition term36 (x0 : real) (x1 : real) := ((~ ((~ ((real_sub x0 x1) = (real_of_num (NUMERAL 0)))) = (exists y0 : real, (real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0)))))) -> (~ ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0)))) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul y0 (real_inv y0)) = (real_of_num (NUMERAL (BIT1 0)))) -> False) -> (~ ((~ ((real_sub x0 x1) = (real_of_num (NUMERAL 0)))) = (exists y0 : real, (real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0)))))) -> (~ ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0)))) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul y0 (real_inv y0)) = (real_of_num (NUMERAL (BIT1 0)))) -> False.
Definition term15 := ((~ (~ ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0))))) -> False) -> ~ ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0))).
Definition term101 (x0 : real) (x1 : real) := exists y0 : real, ((real_sub x0 x1) = (real_of_num (NUMERAL 0))) /\ ((real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term169 (x0 : real) (x1 : real) := and (x0 = x1).
Definition term96 (x0 : real) (x1 : real) := @eq Prop (((real_sub x0 x1) = (real_of_num (NUMERAL 0))) /\ (exists y0 : real, (real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0))))).
Definition term95 (x0 : real) (x1 : real) := @eq Prop (((real_sub x0 x1) = (real_of_num (NUMERAL 0))) /\ (exists y0 : real, (fun y1 : real => (real_mul (real_sub x0 x1) y1) = (real_of_num (NUMERAL (BIT1 0)))) y0)).
Definition term60 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term74 (x0 : real) (x1 : real) := fun y0 : real => ~ ((real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term18 (x0 : real) := fun y0 : real => (x0 = y0) = ((real_sub x0 y0) = (real_of_num (NUMERAL 0))).
Definition term9 := real_add (real_of_num (NUMERAL (BIT1 0))).
Definition term146 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term153 (x0 : real) := ~ (x0 = x0).
Definition term69 (x0 : real) (x1 : real) := forall y0 : real, ~ ((fun y1 : real => (real_mul (real_sub x0 x1) y1) = (real_of_num (NUMERAL (BIT1 0)))) y0).
Definition term122 (x0 : real) := or (x0 = (real_of_num (NUMERAL 0))).
Definition term42 := imp (forall y0 : real, (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))).
Definition term162 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x0 = x1)) \/ (~ (x2 = x3)).
Definition term73 (x0 : real) (x1 : real) := fun y0 : real => ~ ((fun y1 : real => (real_mul (real_sub x0 x1) y1) = (real_of_num (NUMERAL (BIT1 0)))) y0).
Definition term48 (x0 : real) (x1 : real) := imp (~ ((~ ((real_sub x0 x1) = (real_of_num (NUMERAL 0)))) = (exists y0 : real, (real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0)))))).
Definition term118 (x0 : real) (x1 : real) := exists y0 : real, ((~ ((real_sub x0 x1) = (real_of_num (NUMERAL 0)))) /\ (forall y1 : real, ~ ((real_mul (real_sub x0 x1) y1) = (real_of_num (NUMERAL (BIT1 0)))))) \/ (((real_sub x0 x1) = (real_of_num (NUMERAL 0))) /\ ((real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0))))).
Definition term109 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((real_sub x0 x1) = (real_of_num (NUMERAL 0))) /\ ((real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0))))) x2.
Definition term149 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ ((real_mul x0 x1) = (real_mul x2 x3))).
Definition term12 := @eq real (real_of_num (NUMERAL (BIT1 0))).
Definition term191 (x0 : real) (x1 : real) (x2 : real) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term133 (x0 : real) := ((real_mul x0 (real_inv x0)) = (real_of_num (NUMERAL (BIT1 0)))) \/ (x0 = (real_of_num (NUMERAL 0))).
Definition term177 (x0 : real) (x1 : real) (x2 : real) := ~ ((real_mul (real_sub x0 x1) x2) = (real_mul (real_of_num (NUMERAL 0)) x2)).
Definition term176 (x0 : real) (x1 : real) (x2 : real) := (~ ((real_mul (real_sub x0 x1) x2) = (real_mul (real_of_num (NUMERAL 0)) x2))) -> (real_mul (real_sub x0 x1) x2) = (real_mul (real_of_num (NUMERAL 0)) x2).
Definition term33 (x0 : real) (x1 : real) := (~ ((~ ((real_sub x0 x1) = (real_of_num (NUMERAL 0)))) = (exists y0 : real, (real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0)))))) -> False.
Definition term202 := ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0))) -> False.
Definition term34 (x0 : real) (x1 : real) := ~ ((~ ((real_sub x0 x1) = (real_of_num (NUMERAL 0)))) = (exists y0 : real, (real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0))))).
Definition term59 := fun y0 : real => (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul y0 (real_inv y0)) = (real_of_num (NUMERAL (BIT1 0))).
Definition term64 (x0 : real) (x1 : real) := fun y0 : real => (real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0))).
Definition term179 (x0 : real) (x1 : real) (x2 : real) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term167 (x0 : real) (x1 : real) := ~ (~ (x0 = x1)).
Definition term155 (x0 : real) (x1 : real) := or (~ (x0 = x1)).
Definition term121 (x0 : real) := or (~ (~ (x0 = (real_of_num (NUMERAL 0))))).
Definition term14 := (~ (~ ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0))))) -> False.
Definition term29 (x0 : real) (x1 : real) := @eq Prop (~ (x0 = x1)).
Definition term196 (x0 : real) := ~ ((real_mul (real_of_num (NUMERAL 0)) x0) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term119 (x0 : real) := ~ (~ (x0 = (real_of_num (NUMERAL 0)))).
Definition term204 (x0 : real) (x1 : real) := (fun y0 : real => (~ ((~ ((real_sub y0 x0) = (real_of_num (NUMERAL 0)))) = (exists y1 : real, (real_mul (real_sub y0 x0) y1) = (real_of_num (NUMERAL (BIT1 0)))))) -> (~ ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0)))) -> (forall y1 : real, (real_mul (real_of_num (NUMERAL 0)) y1) = (real_of_num (NUMERAL 0))) -> (forall y1 : real, (~ (y1 = (real_of_num (NUMERAL 0)))) -> (real_mul y1 (real_inv y1)) = (real_of_num (NUMERAL (BIT1 0)))) -> False) x1.
Definition term8 := NUMERAL (BIT1 0).
Definition term132 (x0 : Prop) := x0 -> ~ x0.
Definition term83 (x0 : real) (x1 : real) := or ((~ ((real_sub x0 x1) = (real_of_num (NUMERAL 0)))) /\ (~ (exists y0 : real, (real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0)))))).
Definition term20 (x0 : real) := forall y0 : real, (x0 = y0) = ((real_sub x0 y0) = (real_of_num (NUMERAL 0))).
Definition term68 (x0 : real) (x1 : real) := ~ (exists y0 : real, (real_mul (real_sub x0 x1) y0) = (real_of_num (NUMERAL (BIT1 0)))).
