Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term78 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => ~ (x0 y0)) x1.
Definition term84 := (~ False) -> False.
Definition term8 (x0 : Prop) := ~ (~ x0).
Definition term92 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0 -> Prop, (~ ((exists y2 : a0, (y1 y2) /\ (y0 = y2)) = (y1 y0))) -> False) x0.
Definition term32 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (~ (exists y0 : a0, (x0 y0) /\ (x1 = y0))).
Definition term74 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : a0 => (((x0 y0) /\ (x1 = y0)) /\ (~ (x0 x1))) \/ ((forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 = y1))) /\ (x0 x1)).
Definition term37 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (exists y0 : a0, (x0 y0) /\ (x1 = y0)) /\ (~ (x0 x1)).
Definition term56 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := exists y0 : a0, ((x0 y0) /\ (x1 = y0)) /\ (~ (x0 x1)).
Definition term45 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : a0 => (fun y1 : a0 => (x0 y1) /\ (x1 = y1)) y0.
Definition term31 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (x0 x1).
Definition term22 (a0 : Type') (x0 : a0 -> Prop) := ~ (ex x0).
Definition term50 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := and ((fun y0 : a0 => (x0 y0) /\ (x1 = y0)) x2).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term59 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) \/ x1.
Definition term80 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop (~ (x0 x1)).
Definition term73 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : a0 => ((fun y1 : a0 => ((x0 y1) /\ (x1 = y1)) /\ (~ (x0 x1))) y0) \/ ((forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 = y1))) /\ (x0 x1)).
Definition term72 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (((x1 x0) /\ (x2 = x0)) /\ (~ (x1 x2))) \/ ((forall y0 : a0, (~ (x1 y0)) \/ (~ (x2 = y0))) /\ (x1 x2)).
Definition term66 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := or (exists y0 : a0, (fun y1 : a0 => ((x0 y1) /\ (x1 = y1)) /\ (~ (x0 x1))) y0).
Definition term49 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop ((exists y0 : a0, (x0 y0) /\ (x1 = y0)) /\ (~ (x0 x1))).
Definition term48 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop ((exists y0 : a0, (fun y1 : a0 => (x0 y1) /\ (x1 = y1)) y0) /\ (~ (x0 x1))).
Definition term14 (a0 : Type') := fun y0 : a0 => forall y1 : a0 -> Prop, (exists y2 : a0, (y1 y2) /\ (y0 = y2)) = (y1 y0).
Definition term44 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := exists y0 : a0, ((fun y1 : a0 => (x0 y1) /\ (x1 = y1)) y0) /\ (~ (x0 x1)).
Definition term87 (x0 : Prop) (x1 : Prop) := (~ x0) \/ (~ x1).
Definition term3 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ ((exists y0 : a0, (x0 y0) /\ (x1 = y0)) = (x0 x1)).
Definition term82 (x0 : Prop) := (~ x0) -> x0.
Definition term29 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : a0 => (~ (x0 y0)) \/ (~ (x1 = y0)).
Definition term63 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (fun y0 : a0 => ((x0 y0) /\ (x1 = y0)) /\ (~ (x0 x1))) x2.
Definition term38 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := or ((exists y0 : a0, (x0 y0) /\ (x1 = y0)) /\ (~ (x0 x1))).
Definition term20 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := ~ ((x0 x2) /\ (x1 = x2)).
Definition term88 (x0 : Prop) (x1 : Prop) := ~ (x0 /\ x1).
Definition term76 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (fun y0 : a0 => (~ (x0 y0)) \/ (~ (x1 = y0))) x2.
Definition term77 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => ~ (x0 y0).
Definition term13 (a0 : Type') := fun y0 : a0 => forall y1 : a0 -> Prop, (~ ((exists y2 : a0, (y1 y2) /\ (y0 = y2)) = (y1 y0))) -> False.
Definition term65 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := exists y0 : a0, (fun y1 : a0 => ((x0 y1) /\ (x1 = y1)) /\ (~ (x0 x1))) y0.
Definition term46 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := exists y0 : a0, (fun y1 : a0 => (x0 y1) /\ (x1 = y1)) y0.
Definition term21 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (~ (x0 x2)) \/ (~ (x1 = x2)).
Definition term28 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : a0 => ~ ((fun y1 : a0 => (x0 y1) /\ (x1 = y1)) y0).
Definition term86 (a0 : Type') (x0 : a0) := ~ (x0 = x0).
Definition term90 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (x0 x1) /\ (x1 = x1).
Definition term23 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, ~ (x0 y0).
Definition term4 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ((~ ((exists y0 : a0, (x0 y0) /\ (x1 = y0)) = (x0 x1))) -> False) -> (~ ((exists y0 : a0, (x0 y0) /\ (x1 = y0)) = (x0 x1))) -> False.
Definition term2 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ ((exists y0 : a0, (x0 y0) /\ (x1 = y0)) = (x0 x1))) -> False.
Definition term35 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (forall y0 : a0, (~ (x0 y0)) \/ (~ (x1 = y0))) /\ (x0 x1).
Definition term40 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ((exists y0 : a0, (x0 y0) /\ (x1 = y0)) /\ (~ (x0 x1))) \/ ((forall y0 : a0, (~ (x0 y0)) \/ (~ (x1 = y0))) /\ (x0 x1)).
Definition term17 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (x0 x2) /\ (x1 = x2).
Definition term42 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term1 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := exists y0 : a0, (x0 y0) /\ (x1 = y0).
Definition term24 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (exists y0 : a0, (x0 y0) /\ (x1 = y0)).
Definition term89 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := ((x0 x2) /\ (x1 = x2)) -> False.
Definition term79 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop ((fun y0 : a0 => ~ (x0 y0)) x1).
Definition term53 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := ((x1 x0) /\ (x2 = x0)) /\ (~ (x1 x2)).
Definition term60 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) \/ x1.
Definition term39 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ((exists y0 : a0, (x0 y0) /\ (x1 = y0)) /\ (~ (x0 x1))) \/ ((~ (exists y0 : a0, (x0 y0) /\ (x1 = y0))) /\ (x0 x1)).
Definition term93 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ ((exists y1 : a0, (y0 y1) /\ (x0 = y1)) = (y0 x0))) -> False) x1.
Definition term36 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (exists y0 : a0, (x0 y0) /\ (x1 = y0)).
Definition term12 (a0 : Type') (x0 : a0) := forall y0 : a0 -> Prop, (exists y1 : a0, (y0 y1) /\ (x0 = y1)) = (y0 x0).
Definition term5 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (((~ ((exists y0 : a0, (x0 y0) /\ (x1 = y0)) = (x0 x1))) -> False) -> (~ ((exists y0 : a0, (x0 y0) /\ (x1 = y0)) = (x0 x1))) -> False) -> (~ ((exists y0 : a0, (x0 y0) /\ (x1 = y0)) = (x0 x1))) -> False.
Definition term11 (a0 : Type') (x0 : a0) := forall y0 : a0 -> Prop, (~ ((exists y1 : a0, (y0 y1) /\ (x0 = y1)) = (y0 x0))) -> False.
Definition term30 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := forall y0 : a0, (~ (x0 y0)) \/ (~ (x1 = y0)).
Definition term15 (a0 : Type') := forall y0 : a0, forall y1 : a0 -> Prop, (~ ((exists y2 : a0, (y1 y2) /\ (y0 = y2)) = (y1 y0))) -> False.
Definition term7 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (~ ((exists y0 : a0, (x0 y0) /\ (x1 = y0)) = (x0 x1))).
Definition term64 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : a0 => (fun y1 : a0 => ((x0 y1) /\ (x1 = y1)) /\ (~ (x0 x1))) y0.
Definition term33 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (forall y0 : a0, (~ (x0 y0)) \/ (~ (x1 = y0))).
Definition term61 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (exists y0 : a0, (fun y1 : a0 => ((x0 y1) /\ (x1 = y1)) /\ (~ (x0 x1))) y0) \/ ((forall y0 : a0, (~ (x0 y0)) \/ (~ (x1 = y0))) /\ (x0 x1)).
Definition term43 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (exists y0 : a0, (fun y1 : a0 => (x0 y1) /\ (x1 = y1)) y0) /\ (~ (x0 x1)).
Definition term51 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := and ((x0 x2) /\ (x1 = x2)).
Definition term71 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := ((fun y0 : a0 => ((x1 y0) /\ (x2 = y0)) /\ (~ (x1 x2))) x0) \/ ((forall y0 : a0, (~ (x1 y0)) \/ (~ (x2 = y0))) /\ (x1 x2)).
Definition term54 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : a0 => ((fun y1 : a0 => (x0 y1) /\ (x1 = y1)) y0) /\ (~ (x0 x1)).
Definition term62 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := exists y0 : a0, ((fun y1 : a0 => ((x0 y1) /\ (x1 = y1)) /\ (~ (x0 x1))) y0) \/ ((forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 = y1))) /\ (x0 x1)).
Definition term85 (a0 : Type') (x0 : a0) := (~ (x0 = x0)) -> x0 = x0.
Definition term70 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := or (((x1 x0) /\ (x2 = x0)) /\ (~ (x1 x2))).
Definition term69 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := or ((fun y0 : a0 => ((x0 y0) /\ (x1 = y0)) /\ (~ (x0 x1))) x2).
Definition term68 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop ((exists y0 : a0, ((x0 y0) /\ (x1 = y0)) /\ (~ (x0 x1))) \/ ((forall y0 : a0, (~ (x0 y0)) \/ (~ (x1 = y0))) /\ (x0 x1))).
Definition term67 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop ((exists y0 : a0, (fun y1 : a0 => ((x0 y1) /\ (x1 = y1)) /\ (~ (x0 x1))) y0) \/ ((forall y0 : a0, (~ (x0 y0)) \/ (~ (x1 = y0))) /\ (x0 x1))).
Definition term91 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ((x0 x1) /\ (x1 = x1)) -> False.
Definition term83 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (x0 x1) -> False.
Definition term27 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := ~ ((fun y0 : a0 => (x0 y0) /\ (x1 = y0)) x2).
Definition term26 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (fun y0 : a0 => (x0 y0) /\ (x1 = y0)) x2.
Definition term10 (a0 : Type') (x0 : a0) := fun y0 : a0 -> Prop => (exists y1 : a0, (y0 y1) /\ (x0 = y1)) = (y0 x0).
Definition term19 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop (exists y0 : a0, (x0 y0) /\ (x1 = y0)).
Definition term34 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (exists y0 : a0, (x0 y0) /\ (x1 = y0))) /\ (x0 x1).
Definition term6 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (((~ ((exists y0 : a0, (x0 y0) /\ (x1 = y0)) = (x0 x1))) -> False) -> (~ ((exists y0 : a0, (x0 y0) /\ (x1 = y0)) = (x0 x1))) -> False) -> ((~ ((exists y0 : a0, (x0 y0) /\ (x1 = y0)) = (x0 x1))) -> False) -> (~ ((exists y0 : a0, (x0 y0) /\ (x1 = y0)) = (x0 x1))) -> False.
Definition term9 (a0 : Type') (x0 : a0) := fun y0 : a0 -> Prop => (~ ((exists y1 : a0, (y0 y1) /\ (x0 = y1)) = (y0 x0))) -> False.
Definition term41 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term47 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (exists y0 : a0, (fun y1 : a0 => (x0 y1) /\ (x1 = y1)) y0).
Definition term25 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := forall y0 : a0, ~ ((fun y1 : a0 => (x0 y1) /\ (x1 = y1)) y0).
Definition term18 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : a0 => (x0 y0) /\ (x1 = y0).
Definition term75 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := exists y0 : a0, (((x0 y0) /\ (x1 = y0)) /\ (~ (x0 x1))) \/ ((forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 = y1))) /\ (x0 x1)).
Definition term16 (a0 : Type') := forall y0 : a0, forall y1 : a0 -> Prop, (exists y2 : a0, (y1 y2) /\ (y0 = y2)) = (y1 y0).
Definition term81 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (x0 x1)) -> x0 x1.
Definition term57 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := or (exists y0 : a0, ((x0 y0) /\ (x1 = y0)) /\ (~ (x0 x1))).
Definition term58 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (exists y0 : a0, ((x0 y0) /\ (x1 = y0)) /\ (~ (x0 x1))) \/ ((forall y0 : a0, (~ (x0 y0)) \/ (~ (x1 = y0))) /\ (x0 x1)).
Definition term52 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := ((fun y0 : a0 => (x1 y0) /\ (x2 = y0)) x0) /\ (~ (x1 x2)).
Definition term55 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : a0 => ((x0 y0) /\ (x1 = y0)) /\ (~ (x0 x1)).
