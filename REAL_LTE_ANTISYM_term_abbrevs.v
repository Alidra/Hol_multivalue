Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term100 (x0 : real) (x1 : real) := (~ (real_le x0 x1)) -> real_le x0 x1.
Definition term23 (x0 : real -> Prop) := ~ (all x0).
Definition term104 := (~ False) -> False.
Definition term4 := (~ (forall y0 : real, forall y1 : real, ~ ((real_lt y0 y1) /\ (real_le y1 y0)))) -> (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False.
Definition term47 (x0 : real) := fun y0 : real => ((real_lt y0 x0) \/ (real_le x0 y0)) /\ ((~ (real_lt y0 x0)) \/ (~ (real_le x0 y0))).
Definition term44 (x0 : real) (x1 : real) := and ((real_lt x1 x0) \/ (real_le x0 x1)).
Definition term92 := and (forall y0 : real, forall y1 : real, (real_lt y1 y0) \/ (real_le y0 y1)).
Definition term70 (x0 : real) := and (forall y0 : real, (real_lt y0 x0) \/ (real_le x0 y0)).
Definition term38 (x0 : real) (x1 : real) := ~ (~ (real_le x0 x1)).
Definition term82 (x0 : real) := and ((fun y0 : real => forall y1 : real, (real_lt y1 y0) \/ (real_le y0 y1)) x0).
Definition term17 (x0 : real) (x1 : real) := ~ ((real_lt x1 x0) /\ (real_le x0 x1)).
Definition term91 := and (forall y0 : real, (fun y1 : real => forall y2 : real, (real_lt y2 y1) \/ (real_le y1 y2)) y0).
Definition term69 (x0 : real) := and (forall y0 : real, (fun y1 : real => (real_lt y1 x0) \/ (real_le x0 y1)) y0).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term45 (x0 : real) (x1 : real) := ((real_lt x1 x0) \/ (~ (~ (real_le x0 x1)))) /\ ((~ (real_lt x1 x0)) \/ (~ (real_le x0 x1))).
Definition term75 := fun y0 : real => (forall y1 : real, (real_lt y1 y0) \/ (real_le y0 y1)) /\ (forall y1 : real, (~ (real_lt y1 y0)) \/ (~ (real_le y0 y1))).
Definition term29 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => ~ ((real_lt x0 y1) /\ (real_le y1 x0))) y0).
Definition term59 (x0 : real) (x1 : real) := (fun y0 : real => (real_lt y0 x0) \/ (real_le x0 y0)) x1.
Definition term96 := (forall y0 : real, forall y1 : real, (real_lt y1 y0) \/ (real_le y0 y1)) /\ (forall y0 : real, forall y1 : real, (~ (real_lt y1 y0)) \/ (~ (real_le y0 y1))).
Definition term97 (x0 : real) (x1 : real) := (~ (real_lt x0 x1)) -> real_lt x0 x1.
Definition term18 (x0 : real) := fun y0 : real => ~ ((real_lt x0 y0) /\ (real_le y0 x0)).
Definition term40 (x0 : real) (x1 : real) := or (real_lt x0 x1).
Definition term78 := (forall y0 : real, (fun y1 : real => forall y2 : real, (real_lt y2 y1) \/ (real_le y1 y2)) y0) /\ (forall y0 : real, (fun y1 : real => forall y2 : real, (~ (real_lt y2 y1)) \/ (~ (real_le y1 y2))) y0).
Definition term56 (x0 : real) := (forall y0 : real, (fun y1 : real => (real_lt y1 x0) \/ (real_le x0 y1)) y0) /\ (forall y0 : real, (fun y1 : real => (~ (real_lt y1 x0)) \/ (~ (real_le x0 y1))) y0).
Definition term101 (x0 : Prop) (x1 : Prop) := (~ x0) \/ (~ x1).
Definition term99 (x0 : Prop) := (~ x0) -> x0.
Definition term20 := fun y0 : real => forall y1 : real, ~ ((real_lt y0 y1) /\ (real_le y1 y0)).
Definition term93 := fun y0 : real => (fun y1 : real => forall y2 : real, (~ (real_lt y2 y1)) \/ (~ (real_le y1 y2))) y0.
Definition term88 := fun y0 : real => (fun y1 : real => forall y2 : real, (real_lt y2 y1) \/ (real_le y1 y2)) y0.
Definition term28 (x0 : real) (x1 : real) := ~ ((fun y0 : real => ~ ((real_lt x0 y0) /\ (real_le y0 x0))) x1).
Definition term21 (x0 : real) (x1 : real) := ~ (~ ((real_lt x1 x0) /\ (real_le x0 x1))).
Definition term102 (x0 : Prop) (x1 : Prop) := ~ (x0 /\ x1).
Definition term95 := forall y0 : real, forall y1 : real, (~ (real_lt y1 y0)) \/ (~ (real_le y0 y1)).
Definition term90 := forall y0 : real, forall y1 : real, (real_lt y1 y0) \/ (real_le y0 y1).
Definition term50 := forall y0 : real, forall y1 : real, ((real_lt y1 y0) \/ (real_le y0 y1)) /\ ((~ (real_lt y1 y0)) \/ (~ (real_le y0 y1))).
Definition term10 := forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1)).
Definition term1 := forall y0 : real, forall y1 : real, ~ ((real_lt y0 y1) /\ (real_le y1 y0)).
Definition term37 := exists y0 : real, exists y1 : real, (real_lt y0 y1) /\ (real_le y1 y0).
Definition term52 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term41 (x0 : real) (x1 : real) := (real_lt x1 x0) \/ (~ (~ (real_le x0 x1))).
Definition term68 (x0 : real) := forall y0 : real, (real_lt y0 x0) \/ (real_le x0 y0).
Definition term33 (x0 : real) := (fun y0 : real => forall y1 : real, ~ ((real_lt y0 y1) /\ (real_le y1 y0))) x0.
Definition term32 := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, ~ ((real_lt y1 y2) /\ (real_le y2 y1))) y0).
Definition term26 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => ~ ((real_lt x0 y1) /\ (real_le y1 x0))) y0).
Definition term35 := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, ~ ((real_lt y1 y2) /\ (real_le y2 y1))) y0).
Definition term87 := @eq Prop (forall y0 : real, (forall y1 : real, (real_lt y1 y0) \/ (real_le y0 y1)) /\ (forall y1 : real, (~ (real_lt y1 y0)) \/ (~ (real_le y0 y1)))).
Definition term86 := @eq Prop (forall y0 : real, ((fun y1 : real => forall y2 : real, (real_lt y2 y1) \/ (real_le y1 y2)) y0) /\ ((fun y1 : real => forall y2 : real, (~ (real_lt y2 y1)) \/ (~ (real_le y1 y2))) y0)).
Definition term65 (x0 : real) := @eq Prop (forall y0 : real, ((real_lt y0 x0) \/ (real_le x0 y0)) /\ ((~ (real_lt y0 x0)) \/ (~ (real_le x0 y0)))).
Definition term64 (x0 : real) := @eq Prop (forall y0 : real, ((fun y1 : real => (real_lt y1 x0) \/ (real_le x0 y1)) y0) /\ ((fun y1 : real => (~ (real_lt y1 x0)) \/ (~ (real_le x0 y1))) y0)).
Definition term39 (x0 : real) (x1 : real) := (~ (real_lt x1 x0)) \/ (~ (real_le x0 x1)).
Definition term49 := fun y0 : real => forall y1 : real, ((real_lt y1 y0) \/ (real_le y0 y1)) /\ ((~ (real_lt y1 y0)) \/ (~ (real_le y0 y1))).
Definition term8 := (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False.
Definition term9 := ~ (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))).
Definition term3 := ~ (forall y0 : real, forall y1 : real, ~ ((real_lt y0 y1) /\ (real_le y1 y0))).
Definition term30 (x0 : real) := fun y0 : real => (real_lt x0 y0) /\ (real_le y0 x0).
Definition term98 (x0 : real) (x1 : real) := ~ (real_lt x0 x1).
Definition term6 := (((~ (forall y0 : real, forall y1 : real, ~ ((real_lt y0 y1) /\ (real_le y1 y0)))) -> (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False) -> (~ (forall y0 : real, forall y1 : real, ~ ((real_lt y0 y1) /\ (real_le y1 y0)))) -> (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False) -> (~ (forall y0 : real, forall y1 : real, ~ ((real_lt y0 y1) /\ (real_le y1 y0)))) -> (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False.
Definition term103 (x0 : real) (x1 : real) := ((real_lt x1 x0) /\ (real_le x0 x1)) -> False.
Definition term74 (x0 : real) := (forall y0 : real, (real_lt y0 x0) \/ (real_le x0 y0)) /\ (forall y0 : real, (~ (real_lt y0 x0)) \/ (~ (real_le x0 y0))).
Definition term48 (x0 : real) := forall y0 : real, ((real_lt y0 x0) \/ (real_le x0 y0)) /\ ((~ (real_lt y0 x0)) \/ (~ (real_le x0 y0))).
Definition term31 (x0 : real) := exists y0 : real, (real_lt x0 y0) /\ (real_le y0 x0).
Definition term34 (x0 : real) := ~ ((fun y0 : real => forall y1 : real, ~ ((real_lt y0 y1) /\ (real_le y1 y0))) x0).
Definition term73 (x0 : real) := forall y0 : real, (~ (real_lt y0 x0)) \/ (~ (real_le x0 y0)).
Definition term71 (x0 : real) := fun y0 : real => (fun y1 : real => (~ (real_lt y1 x0)) \/ (~ (real_le x0 y1))) y0.
Definition term79 := fun y0 : real => forall y1 : real, (real_lt y1 y0) \/ (real_le y0 y1).
Definition term24 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term53 (x0 : real -> Prop) (x1 : real -> Prop) := forall y0 : real, (x0 y0) /\ (x1 y0).
Definition term22 (x0 : real) (x1 : real) := (real_lt x1 x0) /\ (real_le x0 x1).
Definition term83 (x0 : real) := (fun y0 : real => forall y1 : real, (~ (real_lt y1 y0)) \/ (~ (real_le y0 y1))) x0.
Definition term81 (x0 : real) := (fun y0 : real => forall y1 : real, (real_lt y1 y0) \/ (real_le y0 y1)) x0.
Definition term25 (x0 : real) := ~ (forall y0 : real, ~ ((real_lt x0 y0) /\ (real_le y0 x0))).
Definition term2 := (~ (forall y0 : real, forall y1 : real, ~ ((real_lt y0 y1) /\ (real_le y1 y0)))) -> False.
Definition term72 (x0 : real) := forall y0 : real, (fun y1 : real => (~ (real_lt y1 x0)) \/ (~ (real_le x0 y1))) y0.
Definition term67 (x0 : real) := forall y0 : real, (fun y1 : real => (real_lt y1 x0) \/ (real_le x0 y1)) y0.
Definition term85 := fun y0 : real => ((fun y1 : real => forall y2 : real, (real_lt y2 y1) \/ (real_le y1 y2)) y0) /\ ((fun y1 : real => forall y2 : real, (~ (real_lt y2 y1)) \/ (~ (real_le y1 y2))) y0).
Definition term43 (x0 : real) (x1 : real) := and ((real_lt x1 x0) \/ (~ (~ (real_le x0 x1)))).
Definition term62 (x0 : real) (x1 : real) := ((fun y0 : real => (real_lt y0 x0) \/ (real_le x0 y0)) x1) /\ ((fun y0 : real => (~ (real_lt y0 x0)) \/ (~ (real_le x0 y0))) x1).
Definition term61 (x0 : real) (x1 : real) := (fun y0 : real => (~ (real_lt y0 x0)) \/ (~ (real_le x0 y0))) x1.
Definition term15 (x0 : real) := forall y0 : real, (real_lt y0 x0) = (~ (real_le x0 y0)).
Definition term27 (x0 : real) (x1 : real) := (fun y0 : real => ~ ((real_lt x0 y0) /\ (real_le y0 x0))) x1.
Definition term36 := fun y0 : real => exists y1 : real, (real_lt y0 y1) /\ (real_le y1 y0).
Definition term57 (x0 : real) := fun y0 : real => (real_lt y0 x0) \/ (real_le x0 y0).
Definition term13 (x0 : real) (x1 : real) := ~ (real_le x0 x1).
Definition term76 := forall y0 : real, (forall y1 : real, (real_lt y1 y0) \/ (real_le y0 y1)) /\ (forall y1 : real, (~ (real_lt y1 y0)) \/ (~ (real_le y0 y1))).
Definition term12 := (~ (forall y0 : real, forall y1 : real, ~ ((real_lt y0 y1) /\ (real_le y1 y0)))) -> ~ (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))).
Definition term94 := forall y0 : real, (fun y1 : real => forall y2 : real, (~ (real_lt y2 y1)) \/ (~ (real_le y1 y2))) y0.
Definition term89 := forall y0 : real, (fun y1 : real => forall y2 : real, (real_lt y2 y1) \/ (real_le y1 y2)) y0.
Definition term14 (x0 : real) := fun y0 : real => (real_lt y0 x0) = (~ (real_le x0 y0)).
Definition term42 (x0 : real) (x1 : real) := (real_lt x1 x0) \/ (real_le x0 x1).
Definition term84 (x0 : real) := ((fun y0 : real => forall y1 : real, (real_lt y1 y0) \/ (real_le y0 y1)) x0) /\ ((fun y0 : real => forall y1 : real, (~ (real_lt y1 y0)) \/ (~ (real_le y0 y1))) x0).
Definition term63 (x0 : real) := fun y0 : real => ((fun y1 : real => (real_lt y1 x0) \/ (real_le x0 y1)) y0) /\ ((fun y1 : real => (~ (real_lt y1 x0)) \/ (~ (real_le x0 y1))) y0).
Definition term66 (x0 : real) := fun y0 : real => (fun y1 : real => (real_lt y1 x0) \/ (real_le x0 y1)) y0.
Definition term19 (x0 : real) := forall y0 : real, ~ ((real_lt x0 y0) /\ (real_le y0 x0)).
Definition term54 (x0 : real -> Prop) (x1 : real -> Prop) := (forall y0 : real, x0 y0) /\ (forall y0 : real, x1 y0).
Definition term51 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term58 (x0 : real) := fun y0 : real => (~ (real_lt y0 x0)) \/ (~ (real_le x0 y0)).
Definition term5 := ((~ (forall y0 : real, forall y1 : real, ~ ((real_lt y0 y1) /\ (real_le y1 y0)))) -> (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False) -> (~ (forall y0 : real, forall y1 : real, ~ ((real_lt y0 y1) /\ (real_le y1 y0)))) -> (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False.
Definition term7 := (((~ (forall y0 : real, forall y1 : real, ~ ((real_lt y0 y1) /\ (real_le y1 y0)))) -> (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False) -> (~ (forall y0 : real, forall y1 : real, ~ ((real_lt y0 y1) /\ (real_le y1 y0)))) -> (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False) -> ((~ (forall y0 : real, forall y1 : real, ~ ((real_lt y0 y1) /\ (real_le y1 y0)))) -> (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False) -> (~ (forall y0 : real, forall y1 : real, ~ ((real_lt y0 y1) /\ (real_le y1 y0)))) -> (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False.
Definition term60 (x0 : real) (x1 : real) := and ((fun y0 : real => (real_lt y0 x0) \/ (real_le x0 y0)) x1).
Definition term77 := forall y0 : real, ((fun y1 : real => forall y2 : real, (real_lt y2 y1) \/ (real_le y1 y2)) y0) /\ ((fun y1 : real => forall y2 : real, (~ (real_lt y2 y1)) \/ (~ (real_le y1 y2))) y0).
Definition term55 (x0 : real) := forall y0 : real, ((fun y1 : real => (real_lt y1 x0) \/ (real_le x0 y1)) y0) /\ ((fun y1 : real => (~ (real_lt y1 x0)) \/ (~ (real_le x0 y1))) y0).
Definition term11 := imp (~ (forall y0 : real, forall y1 : real, ~ ((real_lt y0 y1) /\ (real_le y1 y0)))).
Definition term80 := fun y0 : real => forall y1 : real, (~ (real_lt y1 y0)) \/ (~ (real_le y0 y1)).
Definition term16 := fun y0 : real => forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1)).
Definition term46 (x0 : real) (x1 : real) := ((real_lt x1 x0) \/ (real_le x0 x1)) /\ ((~ (real_lt x1 x0)) \/ (~ (real_le x0 x1))).
