Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term160 (x0 : real) := ~ ((real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = x0).
Definition term128 (x0 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ ((real_le (real_of_num (NUMERAL 0)) (sqrt x0)) /\ ((real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = x0)).
Definition term47 (x0 : real -> Prop) := ~ (all x0).
Definition term163 := (~ False) -> False.
Definition term130 := fun y0 : real => (~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ ((real_le (real_of_num (NUMERAL 0)) (sqrt y0)) /\ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0)).
Definition term154 (x0 : Prop) := ~ (~ x0).
Definition term26 := fun y0 : real => (real_le (real_of_num (NUMERAL 0)) y0) = (exists y1 : real, (real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0).
Definition term41 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) /\ (forall y0 : real, ~ ((real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0)).
Definition term81 (x0 : Prop) (x1 : real -> Prop) := x0 /\ (exists y0 : real, x1 y0).
Definition term56 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term145 (x0 : real) := @eq Prop ((fun y0 : real => ~ (real_le (real_of_num (NUMERAL 0)) y0)) x0).
Definition term157 (x0 : real) := imp (real_le (real_of_num (NUMERAL 0)) x0).
Definition term120 (x0 : real) := @eq Prop (((real_le (real_of_num (NUMERAL 0)) x0) /\ (forall y0 : real, ~ ((real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0))) \/ (exists y0 : real, (~ (real_le (real_of_num (NUMERAL 0)) x0)) /\ ((real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0))).
Definition term119 (x0 : real) := @eq Prop (((real_le (real_of_num (NUMERAL 0)) x0) /\ (forall y0 : real, ~ ((real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0))) \/ (exists y0 : real, (fun y1 : real => (~ (real_le (real_of_num (NUMERAL 0)) x0)) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = x0)) y0)).
Definition term12 := (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (real_le (real_of_num (NUMERAL 0)) (sqrt y0)) /\ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) -> False.
Definition term117 (x0 : real) := fun y0 : real => (fun y1 : real => (~ (real_le (real_of_num (NUMERAL 0)) x0)) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = x0)) y0.
Definition term75 := fun y0 : real => (fun y1 : real => (~ (real_le (real_of_num (NUMERAL 0)) y1)) /\ (exists y2 : real, (real_pow y2 (NUMERAL (BIT0 (BIT1 0)))) = y1)) y0.
Definition term70 := fun y0 : real => (fun y1 : real => (real_le (real_of_num (NUMERAL 0)) y1) /\ (forall y2 : real, ~ ((real_pow y2 (NUMERAL (BIT0 (BIT1 0)))) = y1))) y0.
Definition term80 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term153 (x0 : real) := (~ (~ (real_le (real_of_num (NUMERAL 0)) x0))) -> (real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = x0.
Definition term9 := ~ (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term3 := ~ (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) = (exists y1 : real, (real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)).
Definition term16 (x0 : real) := real_le (real_of_num (NUMERAL 0)) (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term24 (x0 : real) := @eq Prop (real_le (real_of_num (NUMERAL 0)) x0).
Definition term158 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) -> (real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = x0.
Definition term123 (x0 : real) := fun y0 : real => ((real_le (real_of_num (NUMERAL 0)) x0) /\ (forall y1 : real, ~ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = x0))) \/ ((fun y1 : real => (~ (real_le (real_of_num (NUMERAL 0)) x0)) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = x0)) y0).
Definition term91 (x0 : real) (x1 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x1)) /\ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1).
Definition term86 (x0 : real) := fun y0 : real => (fun y1 : real => (real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = x0) y0.
Definition term132 (x0 : real) := ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (real_le (real_of_num (NUMERAL 0)) (sqrt x0))) /\ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ ((real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = x0)).
Definition term152 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term79 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term131 := forall y0 : real, (~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ ((real_le (real_of_num (NUMERAL 0)) (sqrt y0)) /\ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0)).
Definition term148 (x0 : Prop) := (~ x0) -> x0.
Definition term10 := forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term5 := ((~ (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) = (exists y1 : real, (real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (real_le (real_of_num (NUMERAL 0)) (sqrt y0)) /\ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) -> False) -> (~ (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) = (exists y1 : real, (real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (real_le (real_of_num (NUMERAL 0)) (sqrt y0)) /\ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) -> False.
Definition term140 (x0 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ ((real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = x0).
Definition term37 (x0 : real) := and (~ (real_le (real_of_num (NUMERAL 0)) x0)).
Definition term85 (x0 : real) := ~ (real_le (real_of_num (NUMERAL 0)) x0).
Definition term118 (x0 : real) := exists y0 : real, (fun y1 : real => (~ (real_le (real_of_num (NUMERAL 0)) x0)) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = x0)) y0.
Definition term76 := exists y0 : real, (fun y1 : real => (~ (real_le (real_of_num (NUMERAL 0)) y1)) /\ (exists y2 : real, (real_pow y2 (NUMERAL (BIT0 (BIT1 0)))) = y1)) y0.
Definition term71 := exists y0 : real, (fun y1 : real => (real_le (real_of_num (NUMERAL 0)) y1) /\ (forall y2 : real, ~ ((real_pow y2 (NUMERAL (BIT0 (BIT1 0)))) = y1))) y0.
Definition term92 (x0 : real) := fun y0 : real => (~ (real_le (real_of_num (NUMERAL 0)) x0)) /\ ((fun y1 : real => (real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = x0) y0).
Definition term97 := (exists y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) /\ (forall y1 : real, ~ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0))) \/ (exists y0 : real, exists y1 : real, (~ (real_le (real_of_num (NUMERAL 0)) y0)) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)).
Definition term77 := exists y0 : real, (~ (real_le (real_of_num (NUMERAL 0)) y0)) /\ (exists y1 : real, (real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0).
Definition term89 (x0 : real) := @eq Prop ((~ (real_le (real_of_num (NUMERAL 0)) x0)) /\ (exists y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0)).
Definition term88 (x0 : real) := @eq Prop ((~ (real_le (real_of_num (NUMERAL 0)) x0)) /\ (exists y0 : real, (fun y1 : real => (real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = x0) y0)).
Definition term136 := forall y0 : real, ((~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ (real_le (real_of_num (NUMERAL 0)) (sqrt y0))) /\ ((~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0)).
Definition term127 := exists y0 : real, exists y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (forall y2 : real, ~ ((real_pow y2 (NUMERAL (BIT0 (BIT1 0)))) = y0))) \/ ((~ (real_le (real_of_num (NUMERAL 0)) y0)) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)).
Definition term96 := exists y0 : real, exists y1 : real, (~ (real_le (real_of_num (NUMERAL 0)) y0)) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0).
Definition term28 (x0 : real -> Prop) := forall y0 : real, ~ (x0 y0).
Definition term108 := fun y0 : real => ((real_le (real_of_num (NUMERAL 0)) y0) /\ (forall y1 : real, ~ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0))) \/ (exists y1 : real, (~ (real_le (real_of_num (NUMERAL 0)) y0)) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)).
Definition term82 (x0 : Prop) (x1 : real -> Prop) := exists y0 : real, x0 /\ (x1 y0).
Definition term73 := or (exists y0 : real, (fun y1 : real => (real_le (real_of_num (NUMERAL 0)) y1) /\ (forall y2 : real, ~ ((real_pow y2 (NUMERAL (BIT0 (BIT1 0)))) = y1))) y0).
Definition term125 (x0 : real) := exists y0 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ (forall y1 : real, ~ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = x0))) \/ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) /\ ((real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0)).
Definition term15 := (~ (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) = (exists y1 : real, (real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (real_le (real_of_num (NUMERAL 0)) (sqrt y0)) /\ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> ~ (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term1 := forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) = (exists y1 : real, (real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0).
Definition term147 (x0 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x0)) -> real_le (real_of_num (NUMERAL 0)) x0.
Definition term19 := fun y0 : real => (real_le (real_of_num (NUMERAL 0)) y0) -> (real_le (real_of_num (NUMERAL 0)) (sqrt y0)) /\ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0).
Definition term162 (x0 : real) := ((real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = x0) -> False.
Definition term49 := exists y0 : real, ~ ((fun y1 : real => (real_le (real_of_num (NUMERAL 0)) y1) = (exists y2 : real, (real_pow y2 (NUMERAL (BIT0 (BIT1 0)))) = y1)) y0).
Definition term100 (x0 : real) := (fun y0 : real => exists y1 : real, (~ (real_le (real_of_num (NUMERAL 0)) y0)) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)) x0.
Definition term146 (x0 : real) := @eq Prop (~ (real_le (real_of_num (NUMERAL 0)) x0)).
Definition term150 (x0 : real) := @eq Prop ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ ((real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = x0)).
Definition term33 (x0 : real) (x1 : real) := ~ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1).
Definition term45 (x0 : real) := ((real_le (real_of_num (NUMERAL 0)) x0) /\ (forall y0 : real, ~ ((real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0))) \/ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) /\ (exists y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0)).
Definition term115 (x0 : real) := exists y0 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ (forall y1 : real, ~ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = x0))) \/ ((fun y1 : real => (~ (real_le (real_of_num (NUMERAL 0)) x0)) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = x0)) y0).
Definition term39 (x0 : real) := and (real_le (real_of_num (NUMERAL 0)) x0).
Definition term84 (x0 : real) := exists y0 : real, (~ (real_le (real_of_num (NUMERAL 0)) x0)) /\ ((fun y1 : real => (real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = x0) y0).
Definition term46 (x0 : real) := ~ ((real_le (real_of_num (NUMERAL 0)) x0) = (exists y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0)).
Definition term164 (x0 : real) := (~ (real_le (real_of_num (NUMERAL 0)) (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))))) -> real_le (real_of_num (NUMERAL 0)) (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term31 (x0 : real) (x1 : real) := (fun y0 : real => (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0) x1.
Definition term54 := exists y0 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (forall y1 : real, ~ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0))) \/ ((~ (real_le (real_of_num (NUMERAL 0)) y0)) /\ (exists y1 : real, (real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)).
Definition term21 (x0 : real) := real_pow x0 (NUMERAL (BIT0 (BIT1 0))).
Definition term57 (x0 : real -> Prop) (x1 : real -> Prop) := exists y0 : real, (x0 y0) \/ (x1 y0).
Definition term78 := (exists y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) /\ (forall y1 : real, ~ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0))) \/ (exists y0 : real, (~ (real_le (real_of_num (NUMERAL 0)) y0)) /\ (exists y1 : real, (real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)).
Definition term133 (x0 : real) := real_le (real_of_num (NUMERAL 0)) (sqrt x0).
Definition term34 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => (real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = x0) y0).
Definition term106 (x0 : real) := ((real_le (real_of_num (NUMERAL 0)) x0) /\ (forall y0 : real, ~ ((real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0))) \/ (exists y0 : real, (~ (real_le (real_of_num (NUMERAL 0)) x0)) /\ ((real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0)).
Definition term109 := exists y0 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (forall y1 : real, ~ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0))) \/ (exists y1 : real, (~ (real_le (real_of_num (NUMERAL 0)) y0)) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)).
Definition term101 := fun y0 : real => (fun y1 : real => exists y2 : real, (~ (real_le (real_of_num (NUMERAL 0)) y1)) /\ ((real_pow y2 (NUMERAL (BIT0 (BIT1 0)))) = y1)) y0.
Definition term111 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 \/ (x1 y0).
Definition term13 := (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (real_le (real_of_num (NUMERAL 0)) (sqrt y0)) /\ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> ~ (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term58 (x0 : real -> Prop) (x1 : real -> Prop) := (exists y0 : real, x0 y0) \/ (exists y0 : real, x1 y0).
Definition term141 := fun y0 : real => ~ (real_le (real_of_num (NUMERAL 0)) y0).
Definition term50 (x0 : real) := (fun y0 : real => (real_le (real_of_num (NUMERAL 0)) y0) = (exists y1 : real, (real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)) x0.
Definition term105 (x0 : real) := ((fun y0 : real => (real_le (real_of_num (NUMERAL 0)) y0) /\ (forall y1 : real, ~ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0))) x0) \/ ((fun y0 : real => exists y1 : real, (~ (real_le (real_of_num (NUMERAL 0)) y0)) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)) x0).
Definition term110 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 \/ (exists y0 : a0, x1 y0).
Definition term63 (x0 : real) := (fun y0 : real => (real_le (real_of_num (NUMERAL 0)) y0) /\ (forall y1 : real, ~ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0))) x0.
Definition term126 := fun y0 : real => exists y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (forall y2 : real, ~ ((real_pow y2 (NUMERAL (BIT0 (BIT1 0)))) = y0))) \/ ((~ (real_le (real_of_num (NUMERAL 0)) y0)) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)).
Definition term27 (x0 : real -> Prop) := ~ (ex x0).
Definition term165 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) -> False.
Definition term114 (x0 : real) := ((real_le (real_of_num (NUMERAL 0)) x0) /\ (forall y0 : real, ~ ((real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0))) \/ (exists y0 : real, (fun y1 : real => (~ (real_le (real_of_num (NUMERAL 0)) x0)) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = x0)) y0).
Definition term143 (x0 : real) := (fun y0 : real => ~ (real_le (real_of_num (NUMERAL 0)) y0)) (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term6 := (((~ (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) = (exists y1 : real, (real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (real_le (real_of_num (NUMERAL 0)) (sqrt y0)) /\ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) -> False) -> (~ (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) = (exists y1 : real, (real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (real_le (real_of_num (NUMERAL 0)) (sqrt y0)) /\ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) -> False) -> (~ (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) = (exists y1 : real, (real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (real_le (real_of_num (NUMERAL 0)) (sqrt y0)) /\ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) -> False.
Definition term36 (x0 : real) := forall y0 : real, ~ ((real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0).
Definition term69 := @eq Prop (exists y0 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (forall y1 : real, ~ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0))) \/ ((~ (real_le (real_of_num (NUMERAL 0)) y0)) /\ (exists y1 : real, (real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0))).
Definition term68 := @eq Prop (exists y0 : real, ((fun y1 : real => (real_le (real_of_num (NUMERAL 0)) y1) /\ (forall y2 : real, ~ ((real_pow y2 (NUMERAL (BIT0 (BIT1 0)))) = y1))) y0) \/ ((fun y1 : real => (~ (real_le (real_of_num (NUMERAL 0)) y1)) /\ (exists y2 : real, (real_pow y2 (NUMERAL (BIT0 (BIT1 0)))) = y1)) y0)).
Definition term138 (x0 : real) (x1 : real) := (fun y0 : real => ~ ((real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0)) x1.
Definition term48 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term8 := (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) -> False.
Definition term142 (x0 : real) := (fun y0 : real => ~ (real_le (real_of_num (NUMERAL 0)) y0)) x0.
Definition term112 (x0 : Prop) (x1 : real -> Prop) := x0 \/ (exists y0 : real, x1 y0).
Definition term61 := fun y0 : real => (real_le (real_of_num (NUMERAL 0)) y0) /\ (forall y1 : real, ~ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)).
Definition term144 (x0 : real) := ~ (real_le (real_of_num (NUMERAL 0)) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term129 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) (sqrt x0)) /\ ((real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = x0).
Definition term124 (x0 : real) := fun y0 : real => ((real_le (real_of_num (NUMERAL 0)) x0) /\ (forall y1 : real, ~ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = x0))) \/ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) /\ ((real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0)).
Definition term25 (x0 : real) := real_le (real_of_num (NUMERAL 0)) x0.
Definition term2 := (~ (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) = (exists y1 : real, (real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0))) -> False.
Definition term35 (x0 : real) := fun y0 : real => ~ ((real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0).
Definition term65 (x0 : real) := (fun y0 : real => (~ (real_le (real_of_num (NUMERAL 0)) y0)) /\ (exists y1 : real, (real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)) x0.
Definition term94 (x0 : real) := exists y0 : real, (~ (real_le (real_of_num (NUMERAL 0)) x0)) /\ ((real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0).
Definition term7 := (((~ (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) = (exists y1 : real, (real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (real_le (real_of_num (NUMERAL 0)) (sqrt y0)) /\ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) -> False) -> (~ (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) = (exists y1 : real, (real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (real_le (real_of_num (NUMERAL 0)) (sqrt y0)) /\ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) -> False) -> ((~ (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) = (exists y1 : real, (real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (real_le (real_of_num (NUMERAL 0)) (sqrt y0)) /\ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) -> False) -> (~ (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) = (exists y1 : real, (real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (real_le (real_of_num (NUMERAL 0)) (sqrt y0)) /\ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) -> False.
Definition term116 (x0 : real) (x1 : real) := (fun y0 : real => (~ (real_le (real_of_num (NUMERAL 0)) x0)) /\ ((real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0)) x1.
Definition term62 := fun y0 : real => (~ (real_le (real_of_num (NUMERAL 0)) y0)) /\ (exists y1 : real, (real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0).
Definition term32 (x0 : real) (x1 : real) := ~ ((fun y0 : real => (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0) x1).
Definition term67 := fun y0 : real => ((fun y1 : real => (real_le (real_of_num (NUMERAL 0)) y1) /\ (forall y2 : real, ~ ((real_pow y2 (NUMERAL (BIT0 (BIT1 0)))) = y1))) y0) \/ ((fun y1 : real => (~ (real_le (real_of_num (NUMERAL 0)) y1)) /\ (exists y2 : real, (real_pow y2 (NUMERAL (BIT0 (BIT1 0)))) = y1)) y0).
Definition term159 (x0 : real) := (~ ((real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = x0)) -> (real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = x0.
Definition term20 := forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (real_le (real_of_num (NUMERAL 0)) (sqrt y0)) /\ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0).
Definition term99 := exists y0 : real, ((fun y1 : real => (real_le (real_of_num (NUMERAL 0)) y1) /\ (forall y2 : real, ~ ((real_pow y2 (NUMERAL (BIT0 (BIT1 0)))) = y1))) y0) \/ ((fun y1 : real => exists y2 : real, (~ (real_le (real_of_num (NUMERAL 0)) y1)) /\ ((real_pow y2 (NUMERAL (BIT0 (BIT1 0)))) = y1)) y0).
Definition term59 := exists y0 : real, ((fun y1 : real => (real_le (real_of_num (NUMERAL 0)) y1) /\ (forall y2 : real, ~ ((real_pow y2 (NUMERAL (BIT0 (BIT1 0)))) = y1))) y0) \/ ((fun y1 : real => (~ (real_le (real_of_num (NUMERAL 0)) y1)) /\ (exists y2 : real, (real_pow y2 (NUMERAL (BIT0 (BIT1 0)))) = y1)) y0).
Definition term113 (x0 : Prop) (x1 : real -> Prop) := exists y0 : real, x0 \/ (x1 y0).
Definition term139 (x0 : real) := (fun y0 : real => real_le (real_of_num (NUMERAL 0)) (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) x0.
Definition term44 (x0 : real) := ((real_le (real_of_num (NUMERAL 0)) x0) /\ (~ (exists y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0))) \/ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) /\ (exists y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0)).
Definition term93 (x0 : real) := fun y0 : real => (~ (real_le (real_of_num (NUMERAL 0)) x0)) /\ ((real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0).
Definition term95 := fun y0 : real => exists y1 : real, (~ (real_le (real_of_num (NUMERAL 0)) y0)) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0).
Definition term66 (x0 : real) := ((fun y0 : real => (real_le (real_of_num (NUMERAL 0)) y0) /\ (forall y1 : real, ~ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0))) x0) \/ ((fun y0 : real => (~ (real_le (real_of_num (NUMERAL 0)) y0)) /\ (exists y1 : real, (real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)) x0).
Definition term134 (x0 : real) := real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0))).
Definition term29 (x0 : real) := ~ (exists y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0).
Definition term149 (x0 : real) := ((real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = x0) \/ (~ (real_le (real_of_num (NUMERAL 0)) x0)).
Definition term17 := fun y0 : real => real_le (real_of_num (NUMERAL 0)) (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term43 (x0 : real) := or ((real_le (real_of_num (NUMERAL 0)) x0) /\ (forall y0 : real, ~ ((real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0))).
Definition term161 (x0 : real) (x1 : real) := ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1) -> False.
Definition term151 (x0 : real) := @eq Prop (((real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = x0) \/ (~ (real_le (real_of_num (NUMERAL 0)) x0))).
Definition term18 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) -> (real_le (real_of_num (NUMERAL 0)) (sqrt x0)) /\ ((real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = x0).
Definition term30 (x0 : real) := forall y0 : real, ~ ((fun y1 : real => (real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = x0) y0).
Definition term11 := imp (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (real_le (real_of_num (NUMERAL 0)) (sqrt y0)) /\ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0)).
Definition term51 (x0 : real) := ~ ((fun y0 : real => (real_le (real_of_num (NUMERAL 0)) y0) = (exists y1 : real, (real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)) x0).
Definition term52 := fun y0 : real => ~ ((fun y1 : real => (real_le (real_of_num (NUMERAL 0)) y1) = (exists y2 : real, (real_pow y2 (NUMERAL (BIT0 (BIT1 0)))) = y1)) y0).
Definition term90 (x0 : real) (x1 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x0)) /\ ((fun y0 : real => (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0) x1).
Definition term23 (x0 : real) := exists y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0.
Definition term64 (x0 : real) := or ((fun y0 : real => (real_le (real_of_num (NUMERAL 0)) y0) /\ (forall y1 : real, ~ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0))) x0).
Definition term72 := exists y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) /\ (forall y1 : real, ~ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)).
Definition term83 (x0 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x0)) /\ (exists y0 : real, (fun y1 : real => (real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = x0) y0).
Definition term135 := fun y0 : real => ((~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ (real_le (real_of_num (NUMERAL 0)) (sqrt y0))) /\ ((~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0)).
Definition term42 (x0 : real) := or ((real_le (real_of_num (NUMERAL 0)) x0) /\ (~ (exists y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0))).
Definition term121 (x0 : real) (x1 : real) := ((real_le (real_of_num (NUMERAL 0)) x0) /\ (forall y0 : real, ~ ((real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0))) \/ ((fun y0 : real => (~ (real_le (real_of_num (NUMERAL 0)) x0)) /\ ((real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0)) x1).
Definition term122 (x0 : real) (x1 : real) := ((real_le (real_of_num (NUMERAL 0)) x1) /\ (forall y0 : real, ~ ((real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x1))) \/ ((~ (real_le (real_of_num (NUMERAL 0)) x1)) /\ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1)).
Definition term40 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) /\ (~ (exists y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0)).
Definition term137 (x0 : real) := (fun y0 : real => ((~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ (real_le (real_of_num (NUMERAL 0)) (sqrt y0))) /\ ((~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0))) x0.
Definition term107 := fun y0 : real => ((fun y1 : real => (real_le (real_of_num (NUMERAL 0)) y1) /\ (forall y2 : real, ~ ((real_pow y2 (NUMERAL (BIT0 (BIT1 0)))) = y1))) y0) \/ ((fun y1 : real => exists y2 : real, (~ (real_le (real_of_num (NUMERAL 0)) y1)) /\ ((real_pow y2 (NUMERAL (BIT0 (BIT1 0)))) = y1)) y0).
Definition term74 := or (exists y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) /\ (forall y1 : real, ~ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0))).
Definition term155 (x0 : real) := ~ (~ (real_le (real_of_num (NUMERAL 0)) x0)).
Definition term55 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term4 := (~ (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) = (exists y1 : real, (real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (real_le (real_of_num (NUMERAL 0)) (sqrt y0)) /\ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) -> False.
Definition term38 (x0 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x0)) /\ (exists y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0).
Definition term22 (x0 : real) := fun y0 : real => (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0.
Definition term98 := (exists y0 : real, (fun y1 : real => (real_le (real_of_num (NUMERAL 0)) y1) /\ (forall y2 : real, ~ ((real_pow y2 (NUMERAL (BIT0 (BIT1 0)))) = y1))) y0) \/ (exists y0 : real, (fun y1 : real => exists y2 : real, (~ (real_le (real_of_num (NUMERAL 0)) y1)) /\ ((real_pow y2 (NUMERAL (BIT0 (BIT1 0)))) = y1)) y0).
Definition term60 := (exists y0 : real, (fun y1 : real => (real_le (real_of_num (NUMERAL 0)) y1) /\ (forall y2 : real, ~ ((real_pow y2 (NUMERAL (BIT0 (BIT1 0)))) = y1))) y0) \/ (exists y0 : real, (fun y1 : real => (~ (real_le (real_of_num (NUMERAL 0)) y1)) /\ (exists y2 : real, (real_pow y2 (NUMERAL (BIT0 (BIT1 0)))) = y1)) y0).
Definition term14 := imp (~ (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) = (exists y1 : real, (real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0))).
Definition term156 (x0 : real) := imp (~ (~ (real_le (real_of_num (NUMERAL 0)) x0))).
Definition term87 (x0 : real) := exists y0 : real, (fun y1 : real => (real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = x0) y0.
Definition term102 := exists y0 : real, (fun y1 : real => exists y2 : real, (~ (real_le (real_of_num (NUMERAL 0)) y1)) /\ ((real_pow y2 (NUMERAL (BIT0 (BIT1 0)))) = y1)) y0.
Definition term53 := fun y0 : real => ((real_le (real_of_num (NUMERAL 0)) y0) /\ (forall y1 : real, ~ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0))) \/ ((~ (real_le (real_of_num (NUMERAL 0)) y0)) /\ (exists y1 : real, (real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)).
Definition term104 := @eq Prop ((exists y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) /\ (forall y1 : real, ~ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0))) \/ (exists y0 : real, exists y1 : real, (~ (real_le (real_of_num (NUMERAL 0)) y0)) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0))).
Definition term103 := @eq Prop ((exists y0 : real, (fun y1 : real => (real_le (real_of_num (NUMERAL 0)) y1) /\ (forall y2 : real, ~ ((real_pow y2 (NUMERAL (BIT0 (BIT1 0)))) = y1))) y0) \/ (exists y0 : real, (fun y1 : real => exists y2 : real, (~ (real_le (real_of_num (NUMERAL 0)) y1)) /\ ((real_pow y2 (NUMERAL (BIT0 (BIT1 0)))) = y1)) y0)).
