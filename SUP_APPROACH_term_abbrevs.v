Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term87 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => (~ (@IN real y0 x0)) \/ (real_le y0 x1)) x2.
Definition term99 (x0 : real) (x1 : real) := (~ (real_le x0 x1)) -> real_le x0 x1.
Definition term101 := (~ False) -> False.
Definition term71 (x0 : real -> Prop) (x1 : real) := (~ (x0 = (@EMPTY real))) -> (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> (forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le y0 x1)) -> forall y0 : real, (@IN real y0 x0) -> real_le y0 x1.
Definition term43 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (~ (@IN real y0 x0)) \/ (real_le y0 x1).
Definition term63 (x0 : Prop) := ~ (~ x0).
Definition term10 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ (exists y1 : a0, y0 y1)) = (forall y1 : a0, ~ (y0 y1))) x0.
Definition term32 (x0 : real -> Prop) (x1 : real) := @eq Prop (~ (exists y0 : real, (@IN real y0 x0) /\ (real_lt x1 y0))).
Definition term31 (x0 : real -> Prop) (x1 : real) := @eq Prop (~ (exists y0 : real, (fun y1 : real => (@IN real y1 x0) /\ (real_lt x1 y1)) y0)).
Definition term19 (x0 : real -> Prop) (x1 : real) := exists y0 : real, (@IN real y0 x0) /\ (real_lt x1 y0).
Definition term29 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (fun y1 : real => (@IN real y1 x0) /\ (real_lt x1 y1)) y0.
Definition term86 (x0 : real -> Prop) := exists y0 : real, forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 y0).
Definition term17 (x0 : real -> Prop) := exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0.
Definition term18 (x0 : Prop) := (~ x0) -> False.
Definition term81 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (@IN real y0 x0) -> real_le y0 x1.
Definition term59 (x0 : real -> Prop) (x1 : real) := ((~ (x0 = (@EMPTY real))) -> (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> (forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le y0 x1)) -> (~ (forall y0 : real, (@IN real y0 x0) -> real_le y0 x1)) -> False) -> (~ (x0 = (@EMPTY real))) -> (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> (forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le y0 x1)) -> (~ (forall y0 : real, (@IN real y0 x0) -> real_le y0 x1)) -> False.
Definition term57 (x0 : real -> Prop) (x1 : real) := ~ (forall y0 : real, (@IN real y0 x0) -> real_le y0 x1).
Definition term42 (x0 : real -> Prop) (x1 : real) (x2 : real) := (~ (@IN real x1 x0)) \/ (real_le x1 x2).
Definition term22 (x0 : real -> Prop) := ~ (exists y0 : real, x0 y0).
Definition term44 (x0 : real -> Prop) (x1 : real) := forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le y0 x1).
Definition term34 (x0 : real -> Prop) (x1 : real) (x2 : real) := ~ ((@IN real x2 x0) /\ (real_lt x1 x2)).
Definition term60 (x0 : real -> Prop) (x1 : real) := (((~ (x0 = (@EMPTY real))) -> (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> (forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le y0 x1)) -> (~ (forall y0 : real, (@IN real y0 x0) -> real_le y0 x1)) -> False) -> (~ (x0 = (@EMPTY real))) -> (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> (forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le y0 x1)) -> (~ (forall y0 : real, (@IN real y0 x0) -> real_le y0 x1)) -> False) -> (~ (x0 = (@EMPTY real))) -> (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> (forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le y0 x1)) -> (~ (forall y0 : real, (@IN real y0 x0) -> real_le y0 x1)) -> False.
Definition term58 (x0 : real -> Prop) (x1 : real) := (~ (x0 = (@EMPTY real))) -> (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> (forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le y0 x1)) -> (~ (forall y0 : real, (@IN real y0 x0) -> real_le y0 x1)) -> False.
Definition term94 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term8 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => ((~ (x0 /\ y0)) = ((~ x0) \/ (~ y0))) /\ ((~ (x0 \/ y0)) = ((~ x0) /\ (~ y0)))) x1.
Definition term70 (x0 : real -> Prop) := imp (~ (x0 = (@EMPTY real))).
Definition term39 (x0 : Prop) (x1 : Prop) := (~ x0) \/ (~ x1).
Definition term90 (x0 : Prop) := (~ x0) -> x0.
Definition term9 (x0 : Prop) (x1 : Prop) := ((~ (x0 /\ x1)) = ((~ x0) \/ (~ x1))) /\ ((~ (x0 \/ x1)) = ((~ x0) /\ (~ x1))).
Definition term0 (x0 : real -> Prop) := (fun y0 : real -> Prop => ((~ (y0 = (@EMPTY real))) /\ (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> (forall y1 : real, (@IN real y1 y0) -> real_le y1 (sup y0)) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> real_le (sup y0) y1)) x0.
Definition term106 (x0 : real -> Prop) := forall y0 : real, ((~ (x0 = (@EMPTY real))) /\ ((exists y1 : real, forall y2 : real, (@IN real y2 x0) -> real_le y2 y1) /\ (real_lt y0 (sup x0)))) -> exists y1 : real, (@IN real y1 x0) /\ (real_lt y0 y1).
Definition term30 (x0 : real -> Prop) (x1 : real) := exists y0 : real, (fun y1 : real => (@IN real y1 x0) /\ (real_lt x1 y1)) y0.
Definition term20 (x0 : real -> Prop) (x1 : real) := (~ (exists y0 : real, (@IN real y0 x0) /\ (real_lt x1 y0))) -> False.
Definition term6 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((~ (y0 /\ y1)) = ((~ y0) \/ (~ y1))) /\ ((~ (y0 \/ y1)) = ((~ y0) /\ (~ y1)))) x0.
Definition term38 (x0 : Prop) (x1 : Prop) := ~ (x0 /\ x1).
Definition term79 := forall y0 : real, forall y1 : real -> Prop, (~ (y1 = (@EMPTY real))) -> (exists y2 : real, forall y3 : real, (@IN real y3 y1) -> real_le y3 y2) -> (forall y2 : real, (~ (@IN real y2 y1)) \/ (real_le y2 y0)) -> forall y2 : real, (@IN real y2 y1) -> real_le y2 y0.
Definition term78 := forall y0 : real, forall y1 : real -> Prop, (~ (y1 = (@EMPTY real))) -> (exists y2 : real, forall y3 : real, (@IN real y3 y1) -> real_le y3 y2) -> (forall y2 : real, (~ (@IN real y2 y1)) \/ (real_le y2 y0)) -> (~ (forall y2 : real, (@IN real y2 y1) -> real_le y2 y0)) -> False.
Definition term23 (x0 : real -> Prop) := forall y0 : real, ~ (x0 y0).
Definition term7 (x0 : Prop) := forall y0 : Prop, ((~ (x0 /\ y0)) = ((~ x0) \/ (~ y0))) /\ ((~ (x0 \/ y0)) = ((~ x0) /\ (~ y0))).
Definition term91 (x0 : real) (x1 : real) (x2 : real -> Prop) := (real_le x1 x0) \/ (~ (@IN real x1 x2)).
Definition term103 (x0 : real) (x1 : real -> Prop) := (fun y0 : real -> Prop => (~ (y0 = (@EMPTY real))) -> (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> (forall y1 : real, (~ (@IN real y1 y0)) \/ (real_le y1 x0)) -> (~ (forall y1 : real, (@IN real y1 y0) -> real_le y1 x0)) -> False) x1.
Definition term53 (x0 : real -> Prop) (x1 : real) := forall y0 : real, (@IN real y0 x0) -> real_le y0 x1.
Definition term95 (x0 : real -> Prop) (x1 : real) (x2 : real) := (~ (~ (@IN real x1 x0))) -> real_le x1 x2.
Definition term3 (x0 : real) := forall y0 : real, (~ (real_lt x0 y0)) = (real_le y0 x0).
Definition term61 (x0 : real -> Prop) (x1 : real) := (((~ (x0 = (@EMPTY real))) -> (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> (forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le y0 x1)) -> (~ (forall y0 : real, (@IN real y0 x0) -> real_le y0 x1)) -> False) -> (~ (x0 = (@EMPTY real))) -> (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> (forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le y0 x1)) -> (~ (forall y0 : real, (@IN real y0 x0) -> real_le y0 x1)) -> False) -> ((~ (x0 = (@EMPTY real))) -> (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> (forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le y0 x1)) -> (~ (forall y0 : real, (@IN real y0 x0) -> real_le y0 x1)) -> False) -> (~ (x0 = (@EMPTY real))) -> (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> (forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le y0 x1)) -> (~ (forall y0 : real, (@IN real y0 x0) -> real_le y0 x1)) -> False.
Definition term89 (x0 : real) (x1 : real -> Prop) := ~ (@IN real x0 x1).
Definition term5 (x0 : real) (x1 : real) := ~ (real_lt x0 x1).
Definition term50 (x0 : real -> Prop) := forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> real_le (sup x0) y0.
Definition term40 (x0 : real -> Prop) (x1 : real) (x2 : real) := (~ (@IN real x2 x0)) \/ (~ (real_lt x1 x2)).
Definition term67 (x0 : real -> Prop) := imp (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0).
Definition term12 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, ~ (x0 y0).
Definition term49 (x0 : real -> Prop) := (forall y0 : real, (@IN real y0 x0) -> real_le y0 (sup x0)) /\ (forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> real_le (sup x0) y0).
Definition term13 (x0 : real) (x1 : real -> Prop) := (~ (x1 = (@EMPTY real))) /\ ((exists y0 : real, forall y1 : real, (@IN real y1 x1) -> real_le y1 y0) /\ (real_lt x0 (sup x1))).
Definition term105 (x0 : real -> Prop) (x1 : real) := ((~ (x0 = (@EMPTY real))) /\ ((exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) /\ (real_lt x1 (sup x0)))) -> exists y0 : real, (@IN real y0 x0) /\ (real_lt x1 y0).
Definition term15 (x0 : real -> Prop) := ~ (x0 = (@EMPTY real)).
Definition term47 (x0 : real -> Prop) (x1 : real) := real_le (sup x0) x1.
Definition term85 (x0 : real -> Prop) := fun y0 : real => forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 y0).
Definition term82 (x0 : real -> Prop) := fun y0 : real => forall y1 : real, (@IN real y1 x0) -> real_le y1 y0.
Definition term33 (x0 : real -> Prop) (x1 : real) (x2 : real) := ~ ((fun y0 : real => (@IN real y0 x0) /\ (real_lt x1 y0)) x2).
Definition term2 (x0 : real) := (fun y0 : real => forall y1 : real, (~ (real_lt y0 y1)) = (real_le y1 y0)) x0.
Definition term98 (x0 : real) (x1 : real -> Prop) := imp (@IN real x0 x1).
Definition term65 (x0 : real -> Prop) (x1 : real) := (forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le y0 x1)) -> (~ (forall y0 : real, (@IN real y0 x0) -> real_le y0 x1)) -> False.
Definition term11 (a0 : Type') (x0 : a0 -> Prop) := ~ (exists y0 : a0, x0 y0).
Definition term96 (x0 : real) (x1 : real -> Prop) := ~ (~ (@IN real x0 x1)).
Definition term62 (x0 : real -> Prop) (x1 : real) := ~ (~ (forall y0 : real, (@IN real y0 x0) -> real_le y0 x1)).
Definition term72 (x0 : real) := fun y0 : real -> Prop => (~ (y0 = (@EMPTY real))) -> (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> (forall y1 : real, (~ (@IN real y1 y0)) \/ (real_le y1 x0)) -> (~ (forall y1 : real, (@IN real y1 y0) -> real_le y1 x0)) -> False.
Definition term56 (x0 : real -> Prop) (x1 : real) := (~ (forall y0 : real, (@IN real y0 x0) -> real_le y0 x1)) -> False.
Definition term24 (x0 : real -> Prop) (x1 : real) := ~ (exists y0 : real, (fun y1 : real => (@IN real y1 x0) /\ (real_lt x1 y1)) y0).
Definition term66 (x0 : real -> Prop) (x1 : real) := (forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le y0 x1)) -> forall y0 : real, (@IN real y0 x0) -> real_le y0 x1.
Definition term55 (x0 : real -> Prop) := (forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> real_le (sup x0) y0) -> forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> real_le (sup x0) y0.
Definition term80 (x0 : real -> Prop) (x1 : real) (x2 : real) := (@IN real x1 x0) -> real_le x1 x2.
Definition term54 (x0 : real -> Prop) (x1 : real) := (forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> real_le (sup x0) y0) -> real_le (sup x0) x1.
Definition term52 (x0 : real -> Prop) (x1 : real) := (forall y0 : real, (@IN real y0 x0) -> real_le y0 x1) -> real_le (sup x0) x1.
Definition term75 (x0 : real) := forall y0 : real -> Prop, (~ (y0 = (@EMPTY real))) -> (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> (forall y1 : real, (~ (@IN real y1 y0)) \/ (real_le y1 x0)) -> forall y1 : real, (@IN real y1 y0) -> real_le y1 x0.
Definition term74 (x0 : real) := forall y0 : real -> Prop, (~ (y0 = (@EMPTY real))) -> (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> (forall y1 : real, (~ (@IN real y1 y0)) \/ (real_le y1 x0)) -> (~ (forall y1 : real, (@IN real y1 y0) -> real_le y1 x0)) -> False.
Definition term36 (x0 : real -> Prop) (x1 : real) := fun y0 : real => ~ ((@IN real y0 x0) /\ (real_lt x1 y0)).
Definition term68 (x0 : real -> Prop) (x1 : real) := (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> (forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le y0 x1)) -> (~ (forall y0 : real, (@IN real y0 x0) -> real_le y0 x1)) -> False.
Definition term83 (x0 : real) (x1 : real) := (~ (real_le x0 x1)) -> False.
Definition term107 := forall y0 : real -> Prop, forall y1 : real, ((~ (y0 = (@EMPTY real))) /\ ((exists y2 : real, forall y3 : real, (@IN real y3 y0) -> real_le y3 y2) /\ (real_lt y1 (sup y0)))) -> exists y2 : real, (@IN real y2 y0) /\ (real_lt y1 y2).
Definition term4 (x0 : real) (x1 : real) := (fun y0 : real => (~ (real_lt x0 y0)) = (real_le y0 x0)) x1.
Definition term45 (x0 : real) (x1 : real -> Prop) := (real_lt x0 (sup x1)) -> False.
Definition term93 (x0 : real) (x1 : real) (x2 : real -> Prop) := @eq Prop ((real_le x1 x0) \/ (~ (@IN real x1 x2))).
Definition term84 (x0 : real) (x1 : real) := ~ (real_le x0 x1).
Definition term28 (x0 : real -> Prop) (x1 : real) (x2 : real) := (@IN real x2 x0) /\ (real_lt x1 x2).
Definition term46 (x0 : real) (x1 : real -> Prop) := ~ (real_lt x0 (sup x1)).
Definition term51 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> real_le (sup x0) y0) x1.
Definition term37 (x0 : real -> Prop) (x1 : real) := forall y0 : real, ~ ((@IN real y0 x0) /\ (real_lt x1 y0)).
Definition term25 (x0 : real -> Prop) (x1 : real) := forall y0 : real, ~ ((fun y1 : real => (@IN real y1 x0) /\ (real_lt x1 y1)) y0).
Definition term64 (x0 : real -> Prop) (x1 : real) := imp (forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le y0 x1)).
Definition term88 (x0 : real) (x1 : real -> Prop) := (~ (@IN real x0 x1)) -> @IN real x0 x1.
Definition term35 (x0 : real -> Prop) (x1 : real) := fun y0 : real => ~ ((fun y1 : real => (@IN real y1 x0) /\ (real_lt x1 y1)) y0).
Definition term16 (x0 : real) (x1 : real -> Prop) := real_lt x0 (sup x1).
Definition term14 (x0 : real) (x1 : real -> Prop) := (exists y0 : real, forall y1 : real, (@IN real y1 x1) -> real_le y1 y0) /\ (real_lt x0 (sup x1)).
Definition term92 (x0 : real -> Prop) (x1 : real) (x2 : real) := @eq Prop ((~ (@IN real x1 x0)) \/ (real_le x1 x2)).
Definition term77 := fun y0 : real => forall y1 : real -> Prop, (~ (y1 = (@EMPTY real))) -> (exists y2 : real, forall y3 : real, (@IN real y3 y1) -> real_le y3 y2) -> (forall y2 : real, (~ (@IN real y2 y1)) \/ (real_le y2 y0)) -> forall y2 : real, (@IN real y2 y1) -> real_le y2 y0.
Definition term76 := fun y0 : real => forall y1 : real -> Prop, (~ (y1 = (@EMPTY real))) -> (exists y2 : real, forall y3 : real, (@IN real y3 y1) -> real_le y3 y2) -> (forall y2 : real, (~ (@IN real y2 y1)) \/ (real_le y2 y0)) -> (~ (forall y2 : real, (@IN real y2 y1) -> real_le y2 y0)) -> False.
Definition term104 (x0 : real -> Prop) (x1 : real) := ((forall y0 : real, (@IN real y0 x0) -> real_le y0 (sup x0)) /\ (forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> real_le (sup x0) y0)) -> real_le (sup x0) x1.
Definition term100 (x0 : real) (x1 : real) := (real_le x0 x1) -> False.
Definition term41 (x0 : real) (x1 : real -> Prop) := or (~ (@IN real x0 x1)).
Definition term73 (x0 : real) := fun y0 : real -> Prop => (~ (y0 = (@EMPTY real))) -> (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> (forall y1 : real, (~ (@IN real y1 y0)) \/ (real_le y1 x0)) -> forall y1 : real, (@IN real y1 y0) -> real_le y1 x0.
Definition term69 (x0 : real -> Prop) (x1 : real) := (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> (forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le y0 x1)) -> forall y0 : real, (@IN real y0 x0) -> real_le y0 x1.
Definition term1 (x0 : real -> Prop) := ((~ (x0 = (@EMPTY real))) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0)) -> (forall y0 : real, (@IN real y0 x0) -> real_le y0 (sup x0)) /\ (forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> real_le (sup x0) y0).
Definition term27 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => (@IN real y0 x0) /\ (real_lt x1 y0)) x2.
Definition term102 (x0 : real) := (fun y0 : real => forall y1 : real -> Prop, (~ (y1 = (@EMPTY real))) -> (exists y2 : real, forall y3 : real, (@IN real y3 y1) -> real_le y3 y2) -> (forall y2 : real, (~ (@IN real y2 y1)) \/ (real_le y2 y0)) -> (~ (forall y2 : real, (@IN real y2 y1) -> real_le y2 y0)) -> False) x0.
Definition term26 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (@IN real y0 x0) /\ (real_lt x1 y0).
Definition term48 (x0 : real -> Prop) := (~ (x0 = (@EMPTY real))) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0).
Definition term21 (x0 : real -> Prop) (x1 : real) := ~ (exists y0 : real, (@IN real y0 x0) /\ (real_lt x1 y0)).
Definition term97 (x0 : real) (x1 : real -> Prop) := imp (~ (~ (@IN real x0 x1))).
