Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term16 (x0 : real) := forall y0 : real, ((real_inv x0) = (real_inv y0)) = (x0 = y0).
Definition term139 (x0 : real) (x1 : real) := (~ ((real_inv (real_inv x0)) = x1)) -> (real_inv (real_inv x0)) = x1.
Definition term20 (x0 : real -> Prop) := ~ (all x0).
Definition term145 := (~ False) -> False.
Definition term4 := (~ (forall y0 : real, forall y1 : real, ((real_inv y0) = (real_inv y1)) = (y0 = y1))) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> False.
Definition term46 (x0 : real) (x1 : real) := or (((real_inv x0) = (real_inv x1)) /\ (~ (x0 = x1))).
Definition term83 := (exists y0 : real, exists y1 : real, ((real_inv y0) = (real_inv y1)) /\ (~ (y0 = y1))) \/ (exists y0 : real, exists y1 : real, (~ ((real_inv y0) = (real_inv y1))) /\ (y0 = y1)).
Definition term53 (x0 : real) := fun y0 : real => (fun y1 : real => ((real_inv x0) = (real_inv y1)) /\ (~ (x0 = y1))) y0.
Definition term108 (x0 : Prop) := ~ (~ x0).
Definition term130 (x0 : real) (x1 : real) (x2 : real) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term36 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term107 (x0 : real) (x1 : real) := (~ (~ (x0 = x1))) -> (real_inv x0) = (real_inv x1).
Definition term8 := (forall y0 : real, (real_inv (real_inv y0)) = y0) -> False.
Definition term58 (x0 : real) := fun y0 : real => (fun y1 : real => (~ ((real_inv x0) = (real_inv y1))) /\ (x0 = y1)) y0.
Definition term41 (x0 : real) := fun y0 : real => ((real_inv x0) = (real_inv y0)) /\ (~ (x0 = y0)).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term134 (x0 : real) (x1 : real) (x2 : real) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term22 (x0 : real) := ~ (forall y0 : real, ((real_inv x0) = (real_inv y0)) = (x0 = y0)).
Definition term144 (x0 : real) (x1 : real) := (x0 = x1) -> False.
Definition term69 (x0 : real) := or ((fun y0 : real => exists y1 : real, ((real_inv y0) = (real_inv y1)) /\ (~ (y0 = y1))) x0).
Definition term9 := ~ (forall y0 : real, (real_inv (real_inv y0)) = y0).
Definition term25 (x0 : real) (x1 : real) := ~ ((fun y0 : real => ((real_inv x0) = (real_inv y0)) = (x0 = y0)) x1).
Definition term106 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term14 := fun y0 : real => (real_inv (real_inv y0)) = y0.
Definition term141 (x0 : real) (x1 : real) := ((real_inv (real_inv x1)) = x0) /\ ((real_inv (real_inv x1)) = x1).
Definition term93 (x0 : real) := (fun y0 : real => ~ ((real_inv y0) = (real_inv x0))) x0.
Definition term102 (x0 : Prop) := (~ x0) -> x0.
Definition term147 (x0 : real) := ((real_inv x0) = (real_inv x0)) -> False.
Definition term126 (x0 : real) (x1 : real) (x2 : real) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term128 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term48 (x0 : real) (x1 : real) := (~ ((real_inv x0) = (real_inv x1))) /\ (x0 = x1).
Definition term123 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term59 (x0 : real) := exists y0 : real, (fun y1 : real => (~ ((real_inv x0) = (real_inv y1))) /\ (x0 = y1)) y0.
Definition term54 (x0 : real) := exists y0 : real, (fun y1 : real => ((real_inv x0) = (real_inv y1)) /\ (~ (x0 = y1))) y0.
Definition term1 := forall y0 : real, forall y1 : real, ((real_inv y0) = (real_inv y1)) = (y0 = y1).
Definition term124 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term114 (x0 : real) (x1 : real) := ~ ((real_inv (real_inv x0)) = (real_inv (real_inv x1))).
Definition term82 := exists y0 : real, exists y1 : real, (~ ((real_inv y0) = (real_inv y1))) /\ (y0 = y1).
Definition term77 := exists y0 : real, exists y1 : real, ((real_inv y0) = (real_inv y1)) /\ (~ (y0 = y1)).
Definition term34 := exists y0 : real, exists y1 : real, (((real_inv y0) = (real_inv y1)) /\ (~ (y0 = y1))) \/ ((~ ((real_inv y0) = (real_inv y1))) /\ (y0 = y1)).
Definition term143 (x0 : real) (x1 : real) := (~ (x0 = x1)) -> x0 = x1.
Definition term78 := or (exists y0 : real, (fun y1 : real => exists y2 : real, ((real_inv y1) = (real_inv y2)) /\ (~ (y1 = y2))) y0).
Definition term56 (x0 : real) := or (exists y0 : real, (fun y1 : real => ((real_inv x0) = (real_inv y1)) /\ (~ (x0 = y1))) y0).
Definition term28 (x0 : real) := exists y0 : real, (((real_inv x0) = (real_inv y0)) /\ (~ (x0 = y0))) \/ ((~ ((real_inv x0) = (real_inv y0))) /\ (x0 = y0)).
Definition term121 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term10 := forall y0 : real, (real_inv (real_inv y0)) = y0.
Definition term105 (x0 : real) (x1 : real) := @eq Prop (((real_inv x0) = (real_inv x1)) \/ (~ (x0 = x1))).
Definition term29 := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, ((real_inv y1) = (real_inv y2)) = (y1 = y2)) y0).
Definition term23 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => ((real_inv x0) = (real_inv y1)) = (x0 = y1)) y0).
Definition term70 (x0 : real) := (fun y0 : real => exists y1 : real, (~ ((real_inv y0) = (real_inv y1))) /\ (y0 = y1)) x0.
Definition term68 (x0 : real) := (fun y0 : real => exists y1 : real, ((real_inv y0) = (real_inv y1)) /\ (~ (y0 = y1))) x0.
Definition term138 (x0 : real) (x1 : real) := (((real_inv (real_inv x1)) = (real_inv (real_inv x0))) /\ ((real_inv (real_inv x1)) = x1)) -> (real_inv (real_inv x0)) = x1.
Definition term32 := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, ((real_inv y1) = (real_inv y2)) = (y1 = y2)) y0).
Definition term137 (x0 : real) (x1 : real) := ((real_inv (real_inv x1)) = (real_inv (real_inv x0))) /\ ((real_inv (real_inv x1)) = x1).
Definition term100 (x0 : real) (x1 : real) (x2 : real) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term66 := fun y0 : real => exists y1 : real, ((real_inv y0) = (real_inv y1)) /\ (~ (y0 = y1)).
Definition term71 (x0 : real) := ((fun y0 : real => exists y1 : real, ((real_inv y0) = (real_inv y1)) /\ (~ (y0 = y1))) x0) \/ ((fun y0 : real => exists y1 : real, (~ ((real_inv y0) = (real_inv y1))) /\ (y0 = y1)) x0).
Definition term140 (x0 : real) (x1 : real) := ~ ((real_inv (real_inv x0)) = x1).
Definition term27 (x0 : real) := fun y0 : real => (((real_inv x0) = (real_inv y0)) /\ (~ (x0 = y0))) \/ ((~ ((real_inv x0) = (real_inv y0))) /\ (x0 = y0)).
Definition term89 (x0 : real) (x1 : real) := ~ (x0 = x1).
Definition term37 (x0 : real -> Prop) (x1 : real -> Prop) := exists y0 : real, (x0 y0) \/ (x1 y0).
Definition term61 (x0 : real) := (exists y0 : real, ((real_inv x0) = (real_inv y0)) /\ (~ (x0 = y0))) \/ (exists y0 : real, (~ ((real_inv x0) = (real_inv y0))) /\ (x0 = y0)).
Definition term3 := ~ (forall y0 : real, forall y1 : real, ((real_inv y0) = (real_inv y1)) = (y0 = y1)).
Definition term6 := (((~ (forall y0 : real, forall y1 : real, ((real_inv y0) = (real_inv y1)) = (y0 = y1))) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> False) -> (~ (forall y0 : real, forall y1 : real, ((real_inv y0) = (real_inv y1)) = (y0 = y1))) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> False) -> (~ (forall y0 : real, forall y1 : real, ((real_inv y0) = (real_inv y1)) = (y0 = y1))) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> False.
Definition term55 (x0 : real) := exists y0 : real, ((real_inv x0) = (real_inv y0)) /\ (~ (x0 = y0)).
Definition term118 (x0 : real) (x1 : real) (x2 : real) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term80 := fun y0 : real => (fun y1 : real => exists y2 : real, (~ ((real_inv y1) = (real_inv y2))) /\ (y1 = y2)) y0.
Definition term75 := fun y0 : real => (fun y1 : real => exists y2 : real, ((real_inv y1) = (real_inv y2)) /\ (~ (y1 = y2))) y0.
Definition term38 (x0 : real -> Prop) (x1 : real -> Prop) := (exists y0 : real, x0 y0) \/ (exists y0 : real, x1 y0).
Definition term13 (x0 : real) := real_inv (real_inv x0).
Definition term127 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term99 (x0 : real) (x1 : real) := (~ (x0 = x1)) \/ ((real_inv x0) = (real_inv x1)).
Definition term31 (x0 : real) := ~ ((fun y0 : real => forall y1 : real, ((real_inv y0) = (real_inv y1)) = (y0 = y1)) x0).
Definition term33 := fun y0 : real => exists y1 : real, (((real_inv y0) = (real_inv y1)) /\ (~ (y0 = y1))) \/ ((~ ((real_inv y0) = (real_inv y1))) /\ (y0 = y1)).
Definition term88 (x0 : real) := (fun y0 : real => (real_inv (real_inv y0)) = y0) x0.
Definition term44 (x0 : real) (x1 : real) := ((real_inv x0) = (real_inv x1)) /\ (~ (x0 = x1)).
Definition term74 := @eq Prop (exists y0 : real, (exists y1 : real, ((real_inv y0) = (real_inv y1)) /\ (~ (y0 = y1))) \/ (exists y1 : real, (~ ((real_inv y0) = (real_inv y1))) /\ (y0 = y1))).
Definition term73 := @eq Prop (exists y0 : real, ((fun y1 : real => exists y2 : real, ((real_inv y1) = (real_inv y2)) /\ (~ (y1 = y2))) y0) \/ ((fun y1 : real => exists y2 : real, (~ ((real_inv y1) = (real_inv y2))) /\ (y1 = y2)) y0)).
Definition term52 (x0 : real) := @eq Prop (exists y0 : real, (((real_inv x0) = (real_inv y0)) /\ (~ (x0 = y0))) \/ ((~ ((real_inv x0) = (real_inv y0))) /\ (x0 = y0))).
Definition term51 (x0 : real) := @eq Prop (exists y0 : real, ((fun y1 : real => ((real_inv x0) = (real_inv y1)) /\ (~ (x0 = y1))) y0) \/ ((fun y1 : real => (~ ((real_inv x0) = (real_inv y1))) /\ (x0 = y1)) y0)).
Definition term91 (x0 : real) := fun y0 : real => ~ ((real_inv y0) = (real_inv x0)).
Definition term17 := fun y0 : real => forall y1 : real, ((real_inv y0) = (real_inv y1)) = (y0 = y1).
Definition term21 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term104 (x0 : real) (x1 : real) := @eq Prop ((~ (x0 = x1)) \/ ((real_inv x0) = (real_inv x1))).
Definition term30 (x0 : real) := (fun y0 : real => forall y1 : real, ((real_inv y0) = (real_inv y1)) = (y0 = y1)) x0.
Definition term92 (x0 : real) (x1 : real) := (fun y0 : real => ~ ((real_inv y0) = (real_inv x0))) x1.
Definition term2 := (~ (forall y0 : real, forall y1 : real, ((real_inv y0) = (real_inv y1)) = (y0 = y1))) -> False.
Definition term146 (x0 : real) := (~ ((real_inv x0) = (real_inv x0))) -> (real_inv x0) = (real_inv x0).
Definition term133 (x0 : real) (x1 : real) (x2 : real) := (x1 = x0) /\ (x1 = x2).
Definition term115 (x0 : real) := (~ ((real_inv (real_inv x0)) = x0)) -> (real_inv (real_inv x0)) = x0.
Definition term122 (x0 : real) (x1 : real) (x2 : real) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term120 (x0 : real) (x1 : real) (x2 : real) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term97 (x0 : real) (x1 : real) := (x0 = x1) -> (real_inv x0) = (real_inv x1).
Definition term24 (x0 : real) (x1 : real) := (fun y0 : real => ((real_inv x0) = (real_inv y0)) = (x0 = y0)) x1.
Definition term131 (x0 : real) (x1 : real) := and (~ (~ (x0 = x1))).
Definition term50 (x0 : real) := fun y0 : real => ((fun y1 : real => ((real_inv x0) = (real_inv y1)) /\ (~ (x0 = y1))) y0) \/ ((fun y1 : real => (~ ((real_inv x0) = (real_inv y1))) /\ (x0 = y1)) y0).
Definition term103 (x0 : real) (x1 : real) := ((real_inv x0) = (real_inv x1)) \/ (~ (x0 = x1)).
Definition term64 := exists y0 : real, ((fun y1 : real => exists y2 : real, ((real_inv y1) = (real_inv y2)) /\ (~ (y1 = y2))) y0) \/ ((fun y1 : real => exists y2 : real, (~ ((real_inv y1) = (real_inv y2))) /\ (y1 = y2)) y0).
Definition term39 (x0 : real) := exists y0 : real, ((fun y1 : real => ((real_inv x0) = (real_inv y1)) /\ (~ (x0 = y1))) y0) \/ ((fun y1 : real => (~ ((real_inv x0) = (real_inv y1))) /\ (x0 = y1)) y0).
Definition term67 := fun y0 : real => exists y1 : real, (~ ((real_inv y0) = (real_inv y1))) /\ (y0 = y1).
Definition term18 (x0 : real) (x1 : real) := ~ (((real_inv x0) = (real_inv x1)) = (x0 = x1)).
Definition term45 (x0 : real) (x1 : real) := or ((fun y0 : real => ((real_inv x0) = (real_inv y0)) /\ (~ (x0 = y0))) x1).
Definition term116 (x0 : real) := ~ ((real_inv (real_inv x0)) = x0).
Definition term136 (x0 : real) (x1 : real) (x2 : real) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term129 (x0 : real) (x1 : real) (x2 : real) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term125 (x0 : real) (x1 : real) (x2 : real) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term95 (x0 : real) (x1 : real) := @eq Prop ((fun y0 : real => ~ ((real_inv y0) = (real_inv x0))) x1).
Definition term12 := (~ (forall y0 : real, forall y1 : real, ((real_inv y0) = (real_inv y1)) = (y0 = y1))) -> ~ (forall y0 : real, (real_inv (real_inv y0)) = y0).
Definition term112 (x0 : real) (x1 : real) := ((real_inv x0) = (real_inv x1)) -> (real_inv (real_inv x0)) = (real_inv (real_inv x1)).
Definition term49 (x0 : real) (x1 : real) := ((fun y0 : real => ((real_inv x0) = (real_inv y0)) /\ (~ (x0 = y0))) x1) \/ ((fun y0 : real => (~ ((real_inv x0) = (real_inv y0))) /\ (x0 = y0)) x1).
Definition term132 (x0 : real) (x1 : real) := and (x0 = x1).
Definition term98 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term142 (x0 : real) (x1 : real) := (((real_inv (real_inv x1)) = x0) /\ ((real_inv (real_inv x1)) = x1)) -> x0 = x1.
Definition term15 (x0 : real) := fun y0 : real => ((real_inv x0) = (real_inv y0)) = (x0 = y0).
Definition term26 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => ((real_inv x0) = (real_inv y1)) = (x0 = y1)) y0).
Definition term43 (x0 : real) (x1 : real) := (fun y0 : real => ((real_inv x0) = (real_inv y0)) /\ (~ (x0 = y0))) x1.
Definition term113 (x0 : real) (x1 : real) := (~ ((real_inv (real_inv x0)) = (real_inv (real_inv x1)))) -> (real_inv (real_inv x0)) = (real_inv (real_inv x1)).
Definition term135 (x0 : real) (x1 : real) (x2 : real) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term47 (x0 : real) (x1 : real) := (fun y0 : real => (~ ((real_inv x0) = (real_inv y0))) /\ (x0 = y0)) x1.
Definition term19 (x0 : real) (x1 : real) := (((real_inv x0) = (real_inv x1)) /\ (~ (x0 = x1))) \/ ((~ ((real_inv x0) = (real_inv x1))) /\ (x0 = x1)).
Definition term101 (x0 : real) (x1 : real) := (~ ((real_inv x0) = (real_inv x1))) -> (real_inv x0) = (real_inv x1).
Definition term5 := ((~ (forall y0 : real, forall y1 : real, ((real_inv y0) = (real_inv y1)) = (y0 = y1))) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> False) -> (~ (forall y0 : real, forall y1 : real, ((real_inv y0) = (real_inv y1)) = (y0 = y1))) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> False.
Definition term117 (x0 : real) (x1 : real) (x2 : real) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term109 (x0 : real) (x1 : real) := ~ (~ (x0 = x1)).
Definition term7 := (((~ (forall y0 : real, forall y1 : real, ((real_inv y0) = (real_inv y1)) = (y0 = y1))) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> False) -> (~ (forall y0 : real, forall y1 : real, ((real_inv y0) = (real_inv y1)) = (y0 = y1))) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> False) -> ((~ (forall y0 : real, forall y1 : real, ((real_inv y0) = (real_inv y1)) = (y0 = y1))) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> False) -> (~ (forall y0 : real, forall y1 : real, ((real_inv y0) = (real_inv y1)) = (y0 = y1))) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> False.
Definition term90 (x0 : real) (x1 : real) := ~ ((real_inv x0) = (real_inv x1)).
Definition term63 := exists y0 : real, (exists y1 : real, ((real_inv y0) = (real_inv y1)) /\ (~ (y0 = y1))) \/ (exists y1 : real, (~ ((real_inv y0) = (real_inv y1))) /\ (y0 = y1)).
Definition term119 (x0 : real) (x1 : real) := or (~ (x0 = x1)).
Definition term72 := fun y0 : real => ((fun y1 : real => exists y2 : real, ((real_inv y1) = (real_inv y2)) /\ (~ (y1 = y2))) y0) \/ ((fun y1 : real => exists y2 : real, (~ ((real_inv y1) = (real_inv y2))) /\ (y1 = y2)) y0).
Definition term96 (x0 : real) (x1 : real) := @eq Prop (~ ((real_inv x0) = (real_inv x1))).
Definition term57 (x0 : real) := or (exists y0 : real, ((real_inv x0) = (real_inv y0)) /\ (~ (x0 = y0))).
Definition term42 (x0 : real) := fun y0 : real => (~ ((real_inv x0) = (real_inv y0))) /\ (x0 = y0).
Definition term79 := or (exists y0 : real, exists y1 : real, ((real_inv y0) = (real_inv y1)) /\ (~ (y0 = y1))).
Definition term35 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term111 (x0 : real) (x1 : real) := imp (x0 = x1).
Definition term62 := fun y0 : real => (exists y1 : real, ((real_inv y0) = (real_inv y1)) /\ (~ (y0 = y1))) \/ (exists y1 : real, (~ ((real_inv y0) = (real_inv y1))) /\ (y0 = y1)).
Definition term94 (x0 : real) := ~ ((real_inv x0) = (real_inv x0)).
Definition term65 := (exists y0 : real, (fun y1 : real => exists y2 : real, ((real_inv y1) = (real_inv y2)) /\ (~ (y1 = y2))) y0) \/ (exists y0 : real, (fun y1 : real => exists y2 : real, (~ ((real_inv y1) = (real_inv y2))) /\ (y1 = y2)) y0).
Definition term40 (x0 : real) := (exists y0 : real, (fun y1 : real => ((real_inv x0) = (real_inv y1)) /\ (~ (x0 = y1))) y0) \/ (exists y0 : real, (fun y1 : real => (~ ((real_inv x0) = (real_inv y1))) /\ (x0 = y1)) y0).
Definition term11 := imp (~ (forall y0 : real, forall y1 : real, ((real_inv y0) = (real_inv y1)) = (y0 = y1))).
Definition term60 (x0 : real) := exists y0 : real, (~ ((real_inv x0) = (real_inv y0))) /\ (x0 = y0).
Definition term110 (x0 : real) (x1 : real) := imp (~ (~ (x0 = x1))).
Definition term81 := exists y0 : real, (fun y1 : real => exists y2 : real, (~ ((real_inv y1) = (real_inv y2))) /\ (y1 = y2)) y0.
Definition term76 := exists y0 : real, (fun y1 : real => exists y2 : real, ((real_inv y1) = (real_inv y2)) /\ (~ (y1 = y2))) y0.
Definition term87 (x0 : real) := @eq Prop ((exists y0 : real, ((real_inv x0) = (real_inv y0)) /\ (~ (x0 = y0))) \/ (exists y0 : real, (~ ((real_inv x0) = (real_inv y0))) /\ (x0 = y0))).
Definition term86 (x0 : real) := @eq Prop ((exists y0 : real, (fun y1 : real => ((real_inv x0) = (real_inv y1)) /\ (~ (x0 = y1))) y0) \/ (exists y0 : real, (fun y1 : real => (~ ((real_inv x0) = (real_inv y1))) /\ (x0 = y1)) y0)).
Definition term85 := @eq Prop ((exists y0 : real, exists y1 : real, ((real_inv y0) = (real_inv y1)) /\ (~ (y0 = y1))) \/ (exists y0 : real, exists y1 : real, (~ ((real_inv y0) = (real_inv y1))) /\ (y0 = y1))).
Definition term84 := @eq Prop ((exists y0 : real, (fun y1 : real => exists y2 : real, ((real_inv y1) = (real_inv y2)) /\ (~ (y1 = y2))) y0) \/ (exists y0 : real, (fun y1 : real => exists y2 : real, (~ ((real_inv y1) = (real_inv y2))) /\ (y1 = y2)) y0)).
