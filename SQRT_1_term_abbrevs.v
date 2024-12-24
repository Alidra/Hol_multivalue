Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term36 := forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0).
Definition term139 := (~ False) -> False.
Definition term27 := (forall y0 : nat, real_le (real_of_num (NUMERAL 0)) (real_of_num y0)) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> ~ (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (sqrt y0) = y1).
Definition term68 := (~ ((real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))))) -> (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))).
Definition term55 (x0 : nat) := (fun y0 : nat => real_le (real_of_num (NUMERAL 0)) (real_of_num y0)) x0.
Definition term77 (x0 : Prop) := ~ (~ x0).
Definition term31 (x0 : real) := fun y0 : real => ((real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0)) -> (sqrt x0) = y0.
Definition term92 (x0 : real) (x1 : real) := (~ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = x0)) \/ ((~ (real_le (real_of_num (NUMERAL 0)) x1)) \/ ((sqrt x0) = x1)).
Definition term84 := ~ ((sqrt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (sqrt (real_of_num (NUMERAL (BIT1 0))))).
Definition term128 (x0 : real) (x1 : real) (x2 : real) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term88 := ~ (real_le (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term115 := ((real_le (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) /\ ((real_pow (real_of_num (NUMERAL (BIT1 0))) (NUMERAL (BIT0 (BIT1 0)))) = (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (sqrt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_of_num (NUMERAL (BIT1 0))).
Definition term38 := fun y0 : real => (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0.
Definition term3 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term20 := (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (sqrt y0) = y1) -> False.
Definition term97 (x0 : real) (x1 : real) := ((sqrt x0) = x1) \/ ((~ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = x0)) \/ (~ (real_le (real_of_num (NUMERAL 0)) x1))).
Definition term7 (x0 : Prop) := (~ x0) -> False.
Definition term132 (x0 : real) (x1 : real) (x2 : real) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term112 (x0 : real) (x1 : real) := imp (~ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (~ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1)))).
Definition term42 := forall y0 : nat, real_le (real_of_num (NUMERAL 0)) (real_of_num y0).
Definition term75 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term57 (x0 : real) := (fun y0 : real => (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) x0.
Definition term69 := ~ ((real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term98 (x0 : real) (x1 : real) := @eq Prop ((~ (real_le (real_of_num (NUMERAL 0)) x1)) \/ ((~ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = x0)) \/ ((sqrt x0) = x1))).
Definition term70 (x0 : Prop) := (~ x0) -> x0.
Definition term46 (x0 : real) (x1 : real) := or (~ ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1))).
Definition term43 (x0 : real) (x1 : real) := ~ ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1)).
Definition term126 (x0 : real) (x1 : real) (x2 : real) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term105 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term61 (x0 : real) := ~ (real_le (real_of_num (NUMERAL 0)) x0).
Definition term123 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term83 := (~ ((sqrt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (sqrt (real_of_num (NUMERAL (BIT1 0)))))) -> (sqrt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (sqrt (real_of_num (NUMERAL (BIT1 0)))).
Definition term65 (x0 : real) (x1 : real) := (~ (x0 = x1)) \/ ((sqrt x0) = (sqrt x1)).
Definition term54 := forall y0 : real, forall y1 : real, ((~ (real_le (real_of_num (NUMERAL 0)) y1)) \/ (~ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0))) \/ ((sqrt y0) = y1).
Definition term18 := forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (sqrt y0) = y1.
Definition term81 := ((real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))) -> (sqrt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (sqrt (real_of_num (NUMERAL (BIT1 0)))).
Definition term124 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term100 (x0 : real) (x1 : real) := (~ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = x0)) \/ (~ (real_le (real_of_num (NUMERAL 0)) x1)).
Definition term50 (x0 : real) (x1 : real) := (real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1).
Definition term94 (x0 : real) (x1 : real) := ((sqrt x0) = x1) \/ (~ (real_le (real_of_num (NUMERAL 0)) x1)).
Definition term60 (x0 : real) (x1 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x1)) \/ ((~ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = x0)) \/ ((sqrt x0) = x1)).
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term26 := (forall y0 : nat, real_le (real_of_num (NUMERAL 0)) (real_of_num y0)) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (sqrt y0) = y1) -> False.
Definition term74 (x0 : real) (x1 : real) := @eq Prop (((sqrt x0) = (sqrt x1)) \/ (~ (x0 = x1))).
Definition term114 := (real_le (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) /\ ((real_pow (real_of_num (NUMERAL (BIT1 0))) (NUMERAL (BIT0 (BIT1 0)))) = (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term62 (x0 : real) (x1 : real) := ~ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1).
Definition term44 (x0 : real) (x1 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (~ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1)).
Definition term87 := (~ (real_le (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))))) -> real_le (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term111 (x0 : real) (x1 : real) := ~ (~ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1)).
Definition term138 := ((sqrt (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))) -> False.
Definition term110 (x0 : real) := and (real_le (real_of_num (NUMERAL 0)) x0).
Definition term11 := ~ ((sqrt (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term66 (x0 : real) (x1 : real) (x2 : real) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term71 (x0 : real) (x1 : real) := ((sqrt x0) = (sqrt x1)) \/ (~ (x0 = x1)).
Definition term56 (x0 : real) := (fun y0 : real => (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) x0.
Definition term117 := ~ ((sqrt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term40 (x0 : nat) := real_le (real_of_num (NUMERAL 0)) (real_of_num x0).
Definition term16 := (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (sqrt y0) = y1) -> False.
Definition term34 (x0 : real) := real_pow x0 (NUMERAL (BIT0 (BIT1 0))).
Definition term89 := real_pow (real_of_num (NUMERAL (BIT1 0))) (NUMERAL (BIT0 (BIT1 0))).
Definition term72 (x0 : real) (x1 : real) := ~ (x0 = x1).
Definition term15 := (((~ ((sqrt (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))))) -> (forall y0 : nat, real_le (real_of_num (NUMERAL 0)) (real_of_num y0)) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (sqrt y0) = y1) -> False) -> (~ ((sqrt (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))))) -> (forall y0 : nat, real_le (real_of_num (NUMERAL 0)) (real_of_num y0)) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (sqrt y0) = y1) -> False) -> ((~ ((sqrt (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))))) -> (forall y0 : nat, real_le (real_of_num (NUMERAL 0)) (real_of_num y0)) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (sqrt y0) = y1) -> False) -> (~ ((sqrt (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))))) -> (forall y0 : nat, real_le (real_of_num (NUMERAL 0)) (real_of_num y0)) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (sqrt y0) = y1) -> False.
Definition term25 := imp (forall y0 : nat, real_le (real_of_num (NUMERAL 0)) (real_of_num y0)).
Definition term17 := ~ (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (sqrt y0) = y1).
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term119 (x0 : real) (x1 : real) (x2 : real) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term21 := (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> ~ (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (sqrt y0) = y1).
Definition term104 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term103 (x0 : real) (x1 : real) := (~ ((~ (real_le (real_of_num (NUMERAL 0)) x1)) \/ (~ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = x0)))) -> (sqrt x0) = x1.
Definition term37 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term39 := forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0.
Definition term93 (x0 : real) (x1 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x1)) \/ ((sqrt x0) = x1).
Definition term29 := (~ ((sqrt (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))))) -> (forall y0 : nat, real_le (real_of_num (NUMERAL 0)) (real_of_num y0)) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> ~ (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (sqrt y0) = y1).
Definition term53 := fun y0 : real => forall y1 : real, ((~ (real_le (real_of_num (NUMERAL 0)) y1)) \/ (~ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0))) \/ ((sqrt y0) = y1).
Definition term33 := fun y0 : real => forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (sqrt y0) = y1.
Definition term48 (x0 : real) (x1 : real) := (~ ((real_le (real_of_num (NUMERAL 0)) x1) /\ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = x0))) \/ ((sqrt x0) = x1).
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term49 (x0 : real) (x1 : real) := ((~ (real_le (real_of_num (NUMERAL 0)) x1)) \/ (~ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = x0))) \/ ((sqrt x0) = x1).
Definition term82 := sqrt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term58 (x0 : real) := (fun y0 : real => forall y1 : real, ((~ (real_le (real_of_num (NUMERAL 0)) y1)) \/ (~ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0))) \/ ((sqrt y0) = y1)) x0.
Definition term67 := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term91 := ~ ((real_pow (real_of_num (NUMERAL (BIT1 0))) (NUMERAL (BIT0 (BIT1 0)))) = (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term51 (x0 : real) := fun y0 : real => ((~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ (~ ((real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0))) \/ ((sqrt x0) = y0).
Definition term47 (x0 : real) (x1 : real) := or ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (~ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1))).
Definition term12 := (~ ((sqrt (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))))) -> (forall y0 : nat, real_le (real_of_num (NUMERAL 0)) (real_of_num y0)) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (sqrt y0) = y1) -> False.
Definition term45 (x0 : real) := real_le (real_of_num (NUMERAL 0)) x0.
Definition term32 (x0 : real) := forall y0 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0)) -> (sqrt x0) = y0.
Definition term113 (x0 : real) (x1 : real) := imp ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1)).
Definition term131 (x0 : real) (x1 : real) (x2 : real) := (x1 = x0) /\ (x1 = x2).
Definition term122 (x0 : real) (x1 : real) (x2 : real) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term59 (x0 : real) (x1 : real) := (fun y0 : real => ((~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ (~ ((real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0))) \/ ((sqrt x0) = y0)) x1.
Definition term121 (x0 : real) (x1 : real) (x2 : real) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term109 (x0 : real) := and (~ (~ (real_le (real_of_num (NUMERAL 0)) x0))).
Definition term1 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term8 := sqrt (real_of_num (NUMERAL (BIT1 0))).
Definition term95 (x0 : real) (x1 : real) := or (~ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1)).
Definition term129 (x0 : real) (x1 : real) := and (~ (~ (x0 = x1))).
Definition term23 := (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (sqrt y0) = y1) -> False.
Definition term137 := (~ ((sqrt (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))))) -> (sqrt (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))).
Definition term35 := fun y0 : real => (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0).
Definition term22 := imp (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0).
Definition term14 := (((~ ((sqrt (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))))) -> (forall y0 : nat, real_le (real_of_num (NUMERAL 0)) (real_of_num y0)) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (sqrt y0) = y1) -> False) -> (~ ((sqrt (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))))) -> (forall y0 : nat, real_le (real_of_num (NUMERAL 0)) (real_of_num y0)) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (sqrt y0) = y1) -> False) -> (~ ((sqrt (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))))) -> (forall y0 : nat, real_le (real_of_num (NUMERAL 0)) (real_of_num y0)) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (sqrt y0) = y1) -> False.
Definition term101 (x0 : real) (x1 : real) := or ((sqrt x0) = x1).
Definition term13 := ((~ ((sqrt (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))))) -> (forall y0 : nat, real_le (real_of_num (NUMERAL 0)) (real_of_num y0)) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (sqrt y0) = y1) -> False) -> (~ ((sqrt (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))))) -> (forall y0 : nat, real_le (real_of_num (NUMERAL 0)) (real_of_num y0)) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (sqrt y0) = y1) -> False.
Definition term10 := (~ ((sqrt (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))))) -> False.
Definition term73 (x0 : real) (x1 : real) := @eq Prop ((~ (x0 = x1)) \/ ((sqrt x0) = (sqrt x1))).
Definition term63 (x0 : real) (x1 : real) := (x0 = x1) -> (sqrt x0) = (sqrt x1).
Definition term96 (x0 : real) (x1 : real) := (~ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = x0)) \/ (((sqrt x0) = x1) \/ (~ (real_le (real_of_num (NUMERAL 0)) x1))).
Definition term134 (x0 : real) (x1 : real) (x2 : real) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term127 (x0 : real) (x1 : real) (x2 : real) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term106 (x0 : real) (x1 : real) := ~ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (~ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1))).
Definition term9 := real_of_num (NUMERAL (BIT1 0)).
Definition term125 (x0 : real) (x1 : real) (x2 : real) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term130 (x0 : real) (x1 : real) := and (x0 = x1).
Definition term135 := ((sqrt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (sqrt (real_of_num (NUMERAL (BIT1 0))))) /\ ((sqrt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term64 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term19 := imp (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)).
Definition term116 := (~ ((sqrt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_of_num (NUMERAL (BIT1 0))))) -> (sqrt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_of_num (NUMERAL (BIT1 0))).
Definition term24 := (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> ~ (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (sqrt y0) = y1).
Definition term133 (x0 : real) (x1 : real) (x2 : real) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term85 := real_le (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term107 (x0 : real) (x1 : real) := (~ (~ (real_le (real_of_num (NUMERAL 0)) x0))) /\ (~ (~ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1))).
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term99 (x0 : real) (x1 : real) := @eq Prop (((sqrt x0) = x1) \/ ((~ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = x0)) \/ (~ (real_le (real_of_num (NUMERAL 0)) x1)))).
Definition term118 (x0 : real) (x1 : real) (x2 : real) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term76 (x0 : real) (x1 : real) := (~ (~ (x0 = x1))) -> (sqrt x0) = (sqrt x1).
Definition term78 (x0 : real) (x1 : real) := ~ (~ (x0 = x1)).
Definition term120 (x0 : real) (x1 : real) := or (~ (x0 = x1)).
Definition term52 (x0 : real) := forall y0 : real, ((~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ (~ ((real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0))) \/ ((sqrt x0) = y0).
Definition term108 (x0 : real) := ~ (~ (real_le (real_of_num (NUMERAL 0)) x0)).
Definition term30 (x0 : real) (x1 : real) := ((real_le (real_of_num (NUMERAL 0)) x1) /\ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = x0)) -> (sqrt x0) = x1.
Definition term80 (x0 : real) (x1 : real) := imp (x0 = x1).
Definition term102 (x0 : real) (x1 : real) := ((sqrt x1) = x0) \/ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (~ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1))).
Definition term86 := NUMERAL (BIT1 0).
Definition term41 := fun y0 : nat => real_le (real_of_num (NUMERAL 0)) (real_of_num y0).
Definition term28 := imp (~ ((sqrt (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))))).
Definition term136 := (((sqrt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (sqrt (real_of_num (NUMERAL (BIT1 0))))) /\ ((sqrt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_of_num (NUMERAL (BIT1 0))))) -> (sqrt (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))).
Definition term90 := (~ ((real_pow (real_of_num (NUMERAL (BIT1 0))) (NUMERAL (BIT0 (BIT1 0)))) = (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_pow (real_of_num (NUMERAL (BIT1 0))) (NUMERAL (BIT0 (BIT1 0)))) = (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term79 (x0 : real) (x1 : real) := imp (~ (~ (x0 = x1))).
