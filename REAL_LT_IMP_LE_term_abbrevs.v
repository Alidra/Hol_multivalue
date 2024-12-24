Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term124 (x0 : real) (x1 : real) := (~ (real_le x0 x1)) -> real_le x0 x1.
Definition term31 (x0 : real -> Prop) := ~ (all x0).
Definition term126 := (~ False) -> False.
Definition term55 (x0 : real) := fun y0 : real => ((real_lt y0 x0) \/ (real_le x0 y0)) /\ ((~ (real_lt y0 x0)) \/ (~ (real_le x0 y0))).
Definition term11 := imp (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)).
Definition term115 (x0 : Prop) := ~ (~ x0).
Definition term52 (x0 : real) (x1 : real) := and ((real_lt x1 x0) \/ (real_le x0 x1)).
Definition term100 := and (forall y0 : real, forall y1 : real, (real_lt y1 y0) \/ (real_le y0 y1)).
Definition term78 (x0 : real) := and (forall y0 : real, (real_lt y0 x0) \/ (real_le x0 y0)).
Definition term46 (x0 : real) (x1 : real) := ~ (~ (real_le x0 x1)).
Definition term90 (x0 : real) := and ((fun y0 : real => forall y1 : real, (real_lt y1 y0) \/ (real_le y0 y1)) x0).
Definition term22 (x0 : real) := forall y0 : real, (real_le x0 y0) \/ (real_le y0 x0).
Definition term99 := and (forall y0 : real, (fun y1 : real => forall y2 : real, (real_lt y2 y1) \/ (real_le y1 y2)) y0).
Definition term77 (x0 : real) := and (forall y0 : real, (fun y1 : real => (real_lt y1 x0) \/ (real_le x0 y1)) y0).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term30 (x0 : real) (x1 : real) := (real_lt x0 x1) /\ (~ (real_le x0 x1)).
Definition term33 (x0 : real) := ~ (forall y0 : real, (real_lt x0 y0) -> real_le x0 y0).
Definition term53 (x0 : real) (x1 : real) := ((real_lt x1 x0) \/ (~ (~ (real_le x0 x1)))) /\ ((~ (real_lt x1 x0)) \/ (~ (real_le x0 x1))).
Definition term83 := fun y0 : real => (forall y1 : real, (real_lt y1 y0) \/ (real_le y0 y1)) /\ (forall y1 : real, (~ (real_lt y1 y0)) \/ (~ (real_le y0 y1))).
Definition term20 (x0 : real) (x1 : real) := (real_le x1 x0) \/ (real_le x0 x1).
Definition term67 (x0 : real) (x1 : real) := (fun y0 : real => (real_lt y0 x0) \/ (real_le x0 y0)) x1.
Definition term119 (x0 : real) (x1 : real) := (real_lt x1 x0) -> ~ (real_le x0 x1).
Definition term104 := (forall y0 : real, forall y1 : real, (real_lt y1 y0) \/ (real_le y0 y1)) /\ (forall y0 : real, forall y1 : real, (~ (real_lt y1 y0)) \/ (~ (real_le y0 y1))).
Definition term107 (x0 : real) (x1 : real) := (~ (real_lt x0 x1)) -> real_lt x0 x1.
Definition term26 (x0 : real) := fun y0 : real => (real_lt x0 y0) -> real_le x0 y0.
Definition term36 (x0 : real) (x1 : real) := ~ ((fun y0 : real => (real_lt x0 y0) -> real_le x0 y0) x1).
Definition term48 (x0 : real) (x1 : real) := or (real_lt x0 x1).
Definition term113 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term86 := (forall y0 : real, (fun y1 : real => forall y2 : real, (real_lt y2 y1) \/ (real_le y1 y2)) y0) /\ (forall y0 : real, (fun y1 : real => forall y2 : real, (~ (real_lt y2 y1)) \/ (~ (real_le y1 y2))) y0).
Definition term64 (x0 : real) := (forall y0 : real, (fun y1 : real => (real_lt y1 x0) \/ (real_le x0 y1)) y0) /\ (forall y0 : real, (fun y1 : real => (~ (real_lt y1 x0)) \/ (~ (real_le x0 y1))) y0).
Definition term109 (x0 : Prop) := (~ x0) -> x0.
Definition term5 := ((~ (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False) -> (~ (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False.
Definition term112 (x0 : real) (x1 : real) := @eq Prop ((~ (real_le x1 x0)) \/ (~ (real_lt x0 x1))).
Definition term111 (x0 : real) (x1 : real) := @eq Prop ((~ (real_lt x1 x0)) \/ (~ (real_le x0 x1))).
Definition term101 := fun y0 : real => (fun y1 : real => forall y2 : real, (~ (real_lt y2 y1)) \/ (~ (real_le y1 y2))) y0.
Definition term96 := fun y0 : real => (fun y1 : real => forall y2 : real, (real_lt y2 y1) \/ (real_le y1 y2)) y0.
Definition term103 := forall y0 : real, forall y1 : real, (~ (real_lt y1 y0)) \/ (~ (real_le y0 y1)).
Definition term98 := forall y0 : real, forall y1 : real, (real_lt y1 y0) \/ (real_le y0 y1).
Definition term58 := forall y0 : real, forall y1 : real, ((real_lt y1 y0) \/ (real_le y0 y1)) /\ ((~ (real_lt y1 y0)) \/ (~ (real_le y0 y1))).
Definition term24 := forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0).
Definition term10 := forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1)).
Definition term1 := forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1.
Definition term45 := exists y0 : real, exists y1 : real, (real_lt y0 y1) /\ (~ (real_le y0 y1)).
Definition term25 (x0 : real) (x1 : real) := (real_lt x0 x1) -> real_le x0 x1.
Definition term60 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term12 := (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False.
Definition term49 (x0 : real) (x1 : real) := (real_lt x1 x0) \/ (~ (~ (real_le x0 x1))).
Definition term15 := (~ (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> ~ (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))).
Definition term76 (x0 : real) := forall y0 : real, (real_lt y0 x0) \/ (real_le x0 y0).
Definition term40 := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, (real_lt y1 y2) -> real_le y1 y2) y0).
Definition term34 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => (real_lt x0 y1) -> real_le x0 y1) y0).
Definition term43 := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, (real_lt y1 y2) -> real_le y1 y2) y0).
Definition term95 := @eq Prop (forall y0 : real, (forall y1 : real, (real_lt y1 y0) \/ (real_le y0 y1)) /\ (forall y1 : real, (~ (real_lt y1 y0)) \/ (~ (real_le y0 y1)))).
Definition term94 := @eq Prop (forall y0 : real, ((fun y1 : real => forall y2 : real, (real_lt y2 y1) \/ (real_le y1 y2)) y0) /\ ((fun y1 : real => forall y2 : real, (~ (real_lt y2 y1)) \/ (~ (real_le y1 y2))) y0)).
Definition term73 (x0 : real) := @eq Prop (forall y0 : real, ((real_lt y0 x0) \/ (real_le x0 y0)) /\ ((~ (real_lt y0 x0)) \/ (~ (real_le x0 y0)))).
Definition term72 (x0 : real) := @eq Prop (forall y0 : real, ((fun y1 : real => (real_lt y1 x0) \/ (real_le x0 y1)) y0) /\ ((fun y1 : real => (~ (real_lt y1 x0)) \/ (~ (real_le x0 y1))) y0)).
Definition term44 := fun y0 : real => exists y1 : real, (real_lt y0 y1) /\ (~ (real_le y0 y1)).
Definition term47 (x0 : real) (x1 : real) := (~ (real_lt x1 x0)) \/ (~ (real_le x0 x1)).
Definition term57 := fun y0 : real => forall y1 : real, ((real_lt y1 y0) \/ (real_le y0 y1)) /\ ((~ (real_lt y1 y0)) \/ (~ (real_le y0 y1))).
Definition term8 := (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False.
Definition term9 := ~ (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))).
Definition term3 := ~ (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1).
Definition term108 (x0 : real) (x1 : real) := ~ (real_lt x0 x1).
Definition term120 (x0 : real) (x1 : real) := (real_le x0 x1) -> ~ (real_le x0 x1).
Definition term82 (x0 : real) := (forall y0 : real, (real_lt y0 x0) \/ (real_le x0 y0)) /\ (forall y0 : real, (~ (real_lt y0 x0)) \/ (~ (real_le x0 y0))).
Definition term56 (x0 : real) := forall y0 : real, ((real_lt y0 x0) \/ (real_le x0 y0)) /\ ((~ (real_lt y0 x0)) \/ (~ (real_le x0 y0))).
Definition term42 (x0 : real) := ~ ((fun y0 : real => forall y1 : real, (real_lt y0 y1) -> real_le y0 y1) x0).
Definition term81 (x0 : real) := forall y0 : real, (~ (real_lt y0 x0)) \/ (~ (real_le x0 y0)).
Definition term79 (x0 : real) := fun y0 : real => (fun y1 : real => (~ (real_lt y1 x0)) \/ (~ (real_le x0 y1))) y0.
Definition term6 := (((~ (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False) -> (~ (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False) -> (~ (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False.
Definition term87 := fun y0 : real => forall y1 : real, (real_lt y1 y0) \/ (real_le y0 y1).
Definition term28 := fun y0 : real => forall y1 : real, (real_lt y0 y1) -> real_le y0 y1.
Definition term23 := fun y0 : real => forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0).
Definition term32 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term61 (x0 : real -> Prop) (x1 : real -> Prop) := forall y0 : real, (x0 y0) /\ (x1 y0).
Definition term118 (x0 : real) (x1 : real) := imp (real_lt x0 x1).
Definition term105 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) x0.
Definition term91 (x0 : real) := (fun y0 : real => forall y1 : real, (~ (real_lt y1 y0)) \/ (~ (real_le y0 y1))) x0.
Definition term89 (x0 : real) := (fun y0 : real => forall y1 : real, (real_lt y1 y0) \/ (real_le y0 y1)) x0.
Definition term41 (x0 : real) := (fun y0 : real => forall y1 : real, (real_lt y0 y1) -> real_le y0 y1) x0.
Definition term27 (x0 : real) := forall y0 : real, (real_lt x0 y0) -> real_le x0 y0.
Definition term2 := (~ (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1)) -> False.
Definition term80 (x0 : real) := forall y0 : real, (fun y1 : real => (~ (real_lt y1 x0)) \/ (~ (real_le x0 y1))) y0.
Definition term75 (x0 : real) := forall y0 : real, (fun y1 : real => (real_lt y1 x0) \/ (real_le x0 y1)) y0.
Definition term35 (x0 : real) (x1 : real) := (fun y0 : real => (real_lt x0 y0) -> real_le x0 y0) x1.
Definition term21 (x0 : real) := fun y0 : real => (real_le x0 y0) \/ (real_le y0 x0).
Definition term93 := fun y0 : real => ((fun y1 : real => forall y2 : real, (real_lt y2 y1) \/ (real_le y1 y2)) y0) /\ ((fun y1 : real => forall y2 : real, (~ (real_lt y2 y1)) \/ (~ (real_le y1 y2))) y0).
Definition term122 (x0 : real) (x1 : real) := @eq Prop ((real_le x1 x0) \/ (real_le x0 x1)).
Definition term114 (x0 : real) (x1 : real) := (~ (~ (real_lt x1 x0))) -> ~ (real_le x0 x1).
Definition term51 (x0 : real) (x1 : real) := and ((real_lt x1 x0) \/ (~ (~ (real_le x0 x1)))).
Definition term7 := (((~ (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False) -> (~ (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False) -> ((~ (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False) -> (~ (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False.
Definition term70 (x0 : real) (x1 : real) := ((fun y0 : real => (real_lt y0 x0) \/ (real_le x0 y0)) x1) /\ ((fun y0 : real => (~ (real_lt y0 x0)) \/ (~ (real_le x0 y0))) x1).
Definition term69 (x0 : real) (x1 : real) := (fun y0 : real => (~ (real_lt y0 x0)) \/ (~ (real_le x0 y0))) x1.
Definition term18 (x0 : real) := forall y0 : real, (real_lt y0 x0) = (~ (real_le x0 y0)).
Definition term29 (x0 : real) (x1 : real) := ~ ((real_lt x0 x1) -> real_le x0 x1).
Definition term116 (x0 : real) (x1 : real) := ~ (~ (real_lt x0 x1)).
Definition term65 (x0 : real) := fun y0 : real => (real_lt y0 x0) \/ (real_le x0 y0).
Definition term16 (x0 : real) (x1 : real) := ~ (real_le x0 x1).
Definition term110 (x0 : real) (x1 : real) := (~ (real_le x1 x0)) \/ (~ (real_lt x0 x1)).
Definition term39 (x0 : real) := exists y0 : real, (real_lt x0 y0) /\ (~ (real_le x0 y0)).
Definition term84 := forall y0 : real, (forall y1 : real, (real_lt y1 y0) \/ (real_le y0 y1)) /\ (forall y1 : real, (~ (real_lt y1 y0)) \/ (~ (real_le y0 y1))).
Definition term38 (x0 : real) := fun y0 : real => (real_lt x0 y0) /\ (~ (real_le x0 y0)).
Definition term102 := forall y0 : real, (fun y1 : real => forall y2 : real, (~ (real_lt y2 y1)) \/ (~ (real_le y1 y2))) y0.
Definition term97 := forall y0 : real, (fun y1 : real => forall y2 : real, (real_lt y2 y1) \/ (real_le y1 y2)) y0.
Definition term17 (x0 : real) := fun y0 : real => (real_lt y0 x0) = (~ (real_le x0 y0)).
Definition term50 (x0 : real) (x1 : real) := (real_lt x1 x0) \/ (real_le x0 x1).
Definition term92 (x0 : real) := ((fun y0 : real => forall y1 : real, (real_lt y1 y0) \/ (real_le y0 y1)) x0) /\ ((fun y0 : real => forall y1 : real, (~ (real_lt y1 y0)) \/ (~ (real_le y0 y1))) x0).
Definition term13 := (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> ~ (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))).
Definition term71 (x0 : real) := fun y0 : real => ((fun y1 : real => (real_lt y1 x0) \/ (real_le x0 y1)) y0) /\ ((fun y1 : real => (~ (real_lt y1 x0)) \/ (~ (real_le x0 y1))) y0).
Definition term74 (x0 : real) := fun y0 : real => (fun y1 : real => (real_lt y1 x0) \/ (real_le x0 y1)) y0.
Definition term37 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => (real_lt x0 y1) -> real_le x0 y1) y0).
Definition term62 (x0 : real -> Prop) (x1 : real -> Prop) := (forall y0 : real, x0 y0) /\ (forall y0 : real, x1 y0).
Definition term59 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term66 (x0 : real) := fun y0 : real => (~ (real_lt y0 x0)) \/ (~ (real_le x0 y0)).
Definition term68 (x0 : real) (x1 : real) := and ((fun y0 : real => (real_lt y0 x0) \/ (real_le x0 y0)) x1).
Definition term125 (x0 : real) (x1 : real) := (real_le x0 x1) -> False.
Definition term4 := (~ (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False.
Definition term85 := forall y0 : real, ((fun y1 : real => forall y2 : real, (real_lt y2 y1) \/ (real_le y1 y2)) y0) /\ ((fun y1 : real => forall y2 : real, (~ (real_lt y2 y1)) \/ (~ (real_le y1 y2))) y0).
Definition term63 (x0 : real) := forall y0 : real, ((fun y1 : real => (real_lt y1 x0) \/ (real_le x0 y1)) y0) /\ ((fun y1 : real => (~ (real_lt y1 x0)) \/ (~ (real_le x0 y1))) y0).
Definition term123 (x0 : real) (x1 : real) := (~ (real_le x1 x0)) -> real_le x0 x1.
Definition term106 (x0 : real) (x1 : real) := (fun y0 : real => (real_le x0 y0) \/ (real_le y0 x0)) x1.
Definition term14 := imp (~ (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1)).
Definition term121 (x0 : Prop) := x0 -> ~ x0.
Definition term88 := fun y0 : real => forall y1 : real, (~ (real_lt y1 y0)) \/ (~ (real_le y0 y1)).
Definition term19 := fun y0 : real => forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1)).
Definition term54 (x0 : real) (x1 : real) := ((real_lt x1 x0) \/ (real_le x0 x1)) /\ ((~ (real_lt x1 x0)) \/ (~ (real_le x0 x1))).
Definition term117 (x0 : real) (x1 : real) := imp (~ (~ (real_lt x0 x1))).
