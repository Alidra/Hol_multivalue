Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term184 (x0 : real -> Prop) (x1 : real) := fun y0 : real -> real => (fun y1 : real -> real => (forall y2 : real, (forall y3 : real, (~ (@IN real y3 x0)) \/ (real_le y3 y2)) \/ (~ (real_le x1 y2))) /\ (forall y2 : real, ((@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le x1 y2))) y0.
Definition term219 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => (~ (@IN real y0 x0)) \/ (real_le y0 x1)) x2.
Definition term264 (x0 : real) (x1 : real) := (~ (real_le x0 x1)) -> real_le x0 x1.
Definition term52 (x0 : real -> Prop) := ~ (all x0).
Definition term266 := (~ False) -> False.
Definition term202 (x0 : real) (x1 : real) (x2 : real -> Prop) := exists y0 : real -> real, (fun y1 : real -> real => ((forall y2 : real, (forall y3 : real, (~ (@IN real y3 x2)) \/ (real_le y3 y2)) \/ (~ (real_le x0 y2))) /\ (forall y2 : real, ((@IN real (y1 y2) x2) /\ (~ (real_le (y1 y2) y2))) \/ (real_le x0 y2))) /\ (@IN real x1 x2)) y0.
Definition term185 (x0 : real -> Prop) (x1 : real) := exists y0 : real -> real, (fun y1 : real -> real => (forall y2 : real, (forall y3 : real, (~ (@IN real y3 x0)) \/ (real_le y3 y2)) \/ (~ (real_le x1 y2))) /\ (forall y2 : real, ((@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le x1 y2))) y0.
Definition term165 (x0 : real -> Prop) (x1 : real) (x2 : real -> real) := (fun y0 : real -> real => forall y1 : real, ((@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) \/ (real_le x1 y1)) x2.
Definition term144 (x0 : real -> Prop) (x1 : real) (x2 : real) := exists y0 : real, (fun y1 : real => fun y2 : real => ((@IN real y2 x0) /\ (~ (real_le y2 y1))) \/ (real_le x1 y1)) x2 y0.
Definition term216 (x0 : real -> Prop) (x1 : Prop) := forall y0 : real, (x0 y0) \/ x1.
Definition term8 (x0 : real -> Prop) := forall y0 : real, (has_sup x0 y0) = (forall y1 : real, (forall y2 : real, (@IN real y2 x0) -> real_le y2 y1) = (real_le y0 y1)).
Definition term176 (x0 : real) (x1 : real) (x2 : real -> Prop) := (exists y0 : real -> real, (forall y1 : real, (forall y2 : real, (~ (@IN real y2 x2)) \/ (real_le y2 y1)) \/ (~ (real_le x0 y1))) /\ (forall y1 : real, ((@IN real (y0 y1) x2) /\ (~ (real_le (y0 y1) y1))) \/ (real_le x0 y1))) /\ (@IN real x1 x2).
Definition term228 (x0 : real -> Prop) (x1 : real) (x2 : real) (x3 : real) := ((~ (@IN real x1 x0)) \/ (real_le x1 x3)) \/ (~ (real_le x2 x3)).
Definition term17 (x0 : real -> Prop) (x1 : real) (x2 : real) := ((has_sup x0 x2) /\ (@IN real x1 x0)) -> real_le x1 x2.
Definition term226 (x0 : real -> Prop) (x1 : real) (x2 : real) := or ((~ (@IN real x1 x0)) \/ (real_le x1 x2)).
Definition term61 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (~ (@IN real y0 x0)) \/ (real_le y0 x1).
Definition term119 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (fun y1 : real => (@IN real y1 x0) /\ (~ (real_le y1 x1))) y0.
Definition term188 (x0 : real) (x1 : real) (x2 : real -> Prop) := @eq Prop ((exists y0 : real -> real, (forall y1 : real, (forall y2 : real, (~ (@IN real y2 x2)) \/ (real_le y2 y1)) \/ (~ (real_le x0 y1))) /\ (forall y1 : real, ((@IN real (y0 y1) x2) /\ (~ (real_le (y0 y1) y1))) \/ (real_le x0 y1))) /\ (@IN real x1 x2)).
Definition term187 (x0 : real) (x1 : real) (x2 : real -> Prop) := @eq Prop ((exists y0 : real -> real, (fun y1 : real -> real => (forall y2 : real, (forall y3 : real, (~ (@IN real y3 x2)) \/ (real_le y3 y2)) \/ (~ (real_le x0 y2))) /\ (forall y2 : real, ((@IN real (y1 y2) x2) /\ (~ (real_le (y1 y2) y2))) \/ (real_le x0 y2))) y0) /\ (@IN real x1 x2)).
Definition term253 (x0 : Prop) := ~ (~ x0).
Definition term194 (x0 : real) (x1 : real) (x2 : real -> Prop) := fun y0 : real -> real => ((forall y1 : real, (forall y2 : real, (~ (@IN real y2 x2)) \/ (real_le y2 y1)) \/ (~ (real_le x0 y1))) /\ (forall y1 : real, ((@IN real (y0 y1) x2) /\ (~ (real_le (y0 y1) y1))) \/ (real_le x0 y1))) /\ (@IN real x1 x2).
Definition term199 (x0 : real -> Prop) (x1 : real) (x2 : real) := exists y0 : real -> real, ((fun y1 : real -> real => ((forall y2 : real, (forall y3 : real, (~ (@IN real y3 x0)) \/ (real_le y3 y2)) \/ (~ (real_le x2 y2))) /\ (forall y2 : real, ((@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le x2 y2))) /\ (@IN real x1 x0)) y0) /\ (~ (real_le x1 x2)).
Definition term172 (x0 : real -> Prop) (x1 : real) := fun y0 : real -> real => (forall y1 : real, (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y2 y1)) \/ (~ (real_le x1 y1))) /\ ((fun y1 : real -> real => forall y2 : real, ((@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le x1 y2)) y0).
Definition term252 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real) := (~ (~ (@IN real x0 x1))) /\ (~ (~ (real_le x2 x3))).
Definition term16 (x0 : real) (x1 : real) (x2 : real -> Prop) := imp ((forall y0 : real, (forall y1 : real, (@IN real y1 x2) -> real_le y1 y0) = (real_le x0 y0)) /\ (@IN real x1 x2)).
Definition term103 (x0 : real -> Prop) (x1 : real) := and (forall y0 : real, (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 y0)) \/ (~ (real_le x1 y0))).
Definition term78 (x0 : real -> Prop) (x1 : real) := and (forall y0 : real, ((forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 y0)) \/ (~ (real_le x1 y0))) /\ ((exists y1 : real, (@IN real y1 x0) /\ (~ (real_le y1 y0))) \/ (real_le x1 y0))).
Definition term12 (x0 : real -> Prop) (x1 : real) := and (forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) = (real_le x1 y0)).
Definition term206 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real -> real) := and ((fun y0 : real -> real => ((forall y1 : real, (forall y2 : real, (~ (@IN real y2 x2)) \/ (real_le y2 y1)) \/ (~ (real_le x0 y1))) /\ (forall y1 : real, ((@IN real (y0 y1) x2) /\ (~ (real_le (y0 y1) y1))) \/ (real_le x0 y1))) /\ (@IN real x1 x2)) x3).
Definition term22 (x0 : real -> Prop) (x1 : real) (x2 : real) := (~ (((forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) = (real_le x2 y0)) /\ (@IN real x1 x0)) -> real_le x1 x2)) -> (forall y0 : real, real_le y0 y0) -> False.
Definition term257 (x0 : real) (x1 : real) := ~ (~ (real_le x0 x1)).
Definition term32 (x0 : real) (x1 : real) := fun y0 : real -> Prop => (~ (((forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) = (real_le x1 y1)) /\ (@IN real x0 y0)) -> real_le x0 x1)) -> ~ (forall y1 : real, real_le y1 y1).
Definition term81 (x0 : real) (x1 : real) (x2 : real -> Prop) := and ((forall y0 : real, ((forall y1 : real, (~ (@IN real y1 x2)) \/ (real_le y1 y0)) \/ (~ (real_le x0 y0))) /\ ((exists y1 : real, (@IN real y1 x2) /\ (~ (real_le y1 y0))) \/ (real_le x0 y0))) /\ (@IN real x1 x2)).
Definition term80 (x0 : real) (x1 : real) (x2 : real -> Prop) := and ((forall y0 : real, (forall y1 : real, (@IN real y1 x2) -> real_le y1 y0) = (real_le x0 y0)) /\ (@IN real x1 x2)).
Definition term66 (x0 : real -> Prop) (x1 : real) (x2 : real) := (~ (forall y0 : real, (@IN real y0 x0) -> real_le y0 x2)) \/ (real_le x1 x2).
Definition term26 := (forall y0 : real, real_le y0 y0) -> False.
Definition term24 (x0 : real -> Prop) (x1 : real) (x2 : real) := (((~ (((forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) = (real_le x2 y0)) /\ (@IN real x1 x0)) -> real_le x1 x2)) -> (forall y0 : real, real_le y0 y0) -> False) -> (~ (((forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) = (real_le x2 y0)) /\ (@IN real x1 x0)) -> real_le x1 x2)) -> (forall y0 : real, real_le y0 y0) -> False) -> (~ (((forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) = (real_le x2 y0)) /\ (@IN real x1 x0)) -> real_le x1 x2)) -> (forall y0 : real, real_le y0 y0) -> False.
Definition term183 (x0 : real -> Prop) (x1 : real) (x2 : real -> real) := (fun y0 : real -> real => (forall y1 : real, (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y2 y1)) \/ (~ (real_le x1 y1))) /\ (forall y1 : real, ((@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) \/ (real_le x1 y1))) x2.
Definition term224 (x0 : real -> Prop) (x1 : real) (x2 : real) := @eq Prop ((forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le y0 x2)) \/ (~ (real_le x1 x2))).
Definition term223 (x0 : real -> Prop) (x1 : real) (x2 : real) := @eq Prop ((forall y0 : real, (fun y1 : real => (~ (@IN real y1 x0)) \/ (real_le y1 x2)) y0) \/ (~ (real_le x1 x2))).
Definition term3 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term139 (x0 : real -> Prop) (x1 : real) := fun y0 : real => fun y1 : real => ((@IN real y1 x0) /\ (~ (real_le y1 y0))) \/ (real_le x1 y0).
Definition term102 (x0 : real -> Prop) (x1 : real) := and (forall y0 : real, (fun y1 : real => (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y2 y1)) \/ (~ (real_le x1 y1))) y0).
Definition term207 (x0 : real -> real) (x1 : real) (x2 : real) (x3 : real -> Prop) := and (((forall y0 : real, (forall y1 : real, (~ (@IN real y1 x3)) \/ (real_le y1 y0)) \/ (~ (real_le x1 y0))) /\ (forall y0 : real, ((@IN real (x0 y0) x3) /\ (~ (real_le (x0 y0) y0))) \/ (real_le x1 y0))) /\ (@IN real x2 x3)).
Definition term160 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term19 (x0 : Prop) := (~ x0) -> False.
Definition term237 (x0 : real -> Prop) (x1 : real) (x2 : real) (x3 : real) := (~ (@IN real x1 x0)) \/ ((real_le x1 x3) \/ (~ (real_le x2 x3))).
Definition term45 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (@IN real y0 x0) -> real_le y0 x1.
Definition term112 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) \/ x1.
Definition term259 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real) := imp (~ ((~ (@IN real x0 x1)) \/ (~ (real_le x2 x3)))).
Definition term236 (x0 : real -> Prop) (x1 : real) (x2 : real) (x3 : real) := (fun y0 : real => ((~ (@IN real y0 x0)) \/ (real_le y0 x2)) \/ (~ (real_le x1 x2))) x3.
Definition term126 (x0 : real -> Prop) (x1 : real) (x2 : real) (x3 : real) := ((fun y0 : real => (@IN real y0 x0) /\ (~ (real_le y0 x3))) x1) \/ (real_le x2 x3).
Definition term54 (x0 : real -> Prop) (x1 : real) := ~ (forall y0 : real, (@IN real y0 x0) -> real_le y0 x1).
Definition term51 (x0 : real -> Prop) (x1 : real) (x2 : real) := (~ (@IN real x1 x0)) \/ (real_le x1 x2).
Definition term62 (x0 : real -> Prop) (x1 : real) := forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le y0 x1).
Definition term195 (x0 : real) (x1 : real) (x2 : real -> Prop) := exists y0 : real -> real, ((forall y1 : real, (forall y2 : real, (~ (@IN real y2 x2)) \/ (real_le y2 y1)) \/ (~ (real_le x0 y1))) /\ (forall y1 : real, ((@IN real (y0 y1) x2) /\ (~ (real_le (y0 y1) y1))) \/ (real_le x0 y1))) /\ (@IN real x1 x2).
Definition term30 (x0 : real -> Prop) (x1 : real) (x2 : real) := (~ (((forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) = (real_le x2 y0)) /\ (@IN real x1 x0)) -> real_le x1 x2)) -> ~ (forall y0 : real, real_le y0 y0).
Definition term161 (x0 : Prop) (x1 : type1028) := x0 /\ (exists y0 : real -> real, x1 y0).
Definition term27 := ~ (forall y0 : real, real_le y0 y0).
Definition term166 (x0 : real -> Prop) (x1 : real) := fun y0 : real -> real => (fun y1 : real -> real => forall y2 : real, ((@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le x1 y2)) y0.
Definition term153 (x0 : real -> Prop) (x1 : real) (x2 : real -> real) := forall y0 : real, (fun y1 : real => fun y2 : real => ((@IN real y2 x0) /\ (~ (real_le y2 y1))) \/ (real_le x1 y1)) y0 (x2 y0).
Definition term246 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term89 (x0 : real -> Prop) (x1 : real) := (forall y0 : real, (fun y1 : real => (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y2 y1)) \/ (~ (real_le x1 y1))) y0) /\ (forall y0 : real, (fun y1 : real => (exists y2 : real, (@IN real y2 x0) /\ (~ (real_le y2 y1))) \/ (real_le x1 y1)) y0).
Definition term247 (x0 : real -> Prop) (x1 : real) (x2 : real) (x3 : real) := (~ ((~ (@IN real x2 x0)) \/ (~ (real_le x1 x3)))) -> real_le x2 x3.
Definition term174 (x0 : real -> Prop) (x1 : real) := exists y0 : real -> real, (forall y1 : real, (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y2 y1)) \/ (~ (real_le x1 y1))) /\ (forall y1 : real, ((@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) \/ (real_le x1 y1)).
Definition term145 (x0 : real -> Prop) (x1 : real) := fun y0 : real => exists y1 : real, (fun y2 : real => fun y3 : real => ((@IN real y3 x0) /\ (~ (real_le y3 y2))) \/ (real_le x1 y2)) y0 y1.
Definition term270 (x0 : real -> Prop) (x1 : real) := forall y0 : real, ((has_sup x0 x1) /\ (@IN real y0 x0)) -> real_le y0 x1.
Definition term272 := forall y0 : real -> Prop, forall y1 : real, forall y2 : real, ((has_sup y0 y1) /\ (@IN real y2 y0)) -> real_le y2 y1.
Definition term114 (x0 : real -> Prop) (x1 : Prop) := (exists y0 : real, x0 y0) \/ x1.
Definition term159 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term196 (x0 : real) (x1 : real) (x2 : real -> Prop) := and (exists y0 : real -> real, ((forall y1 : real, (forall y2 : real, (~ (@IN real y2 x2)) \/ (real_le y2 y1)) \/ (~ (real_le x0 y1))) /\ (forall y1 : real, ((@IN real (y0 y1) x2) /\ (~ (real_le (y0 y1) y1))) \/ (real_le x0 y1))) /\ (@IN real x1 x2)).
Definition term240 (x0 : Prop) := (~ x0) -> x0.
Definition term175 (x0 : real -> Prop) (x1 : real) := and (exists y0 : real -> real, (forall y1 : real, (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y2 y1)) \/ (~ (real_le x1 y1))) /\ (forall y1 : real, ((@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) \/ (real_le x1 y1))).
Definition term150 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) (x3 : real) := ((@IN real (x1 x3) x0) /\ (~ (real_le (x1 x3) x3))) \/ (real_le x2 x3).
Definition term127 (x0 : real -> Prop) (x1 : real) (x2 : real) (x3 : real) := ((@IN real x1 x0) /\ (~ (real_le x1 x3))) \/ (real_le x2 x3).
Definition term106 (x0 : real -> Prop) (x1 : real) := forall y0 : real, (exists y1 : real, (@IN real y1 x0) /\ (~ (real_le y1 y0))) \/ (real_le x1 y0).
Definition term250 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term73 (x0 : real -> Prop) (x1 : real) (x2 : real) := and ((forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le y0 x2)) \/ (~ (real_le x1 x2))).
Definition term72 (x0 : real -> Prop) (x1 : real) (x2 : real) := and ((forall y0 : real, (@IN real y0 x0) -> real_le y0 x2) \/ (~ (real_le x1 x2))).
Definition term133 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term158 (x0 : real -> Prop) (x1 : real) := (forall y0 : real, (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 y0)) \/ (~ (real_le x1 y0))) /\ (exists y0 : real -> real, forall y1 : real, ((@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) \/ (real_le x1 y1)).
Definition term201 (x0 : real) (x1 : real) (x2 : real -> Prop) := fun y0 : real -> real => (fun y1 : real -> real => ((forall y2 : real, (forall y3 : real, (~ (@IN real y3 x2)) \/ (real_le y3 y2)) \/ (~ (real_le x0 y2))) /\ (forall y2 : real, ((@IN real (y1 y2) x2) /\ (~ (real_le (y1 y2) y2))) \/ (real_le x0 y2))) /\ (@IN real x1 x2)) y0.
Definition term120 (x0 : real -> Prop) (x1 : real) := exists y0 : real, (fun y1 : real => (@IN real y1 x0) /\ (~ (real_le y1 x1))) y0.
Definition term271 (x0 : real -> Prop) := forall y0 : real, forall y1 : real, ((has_sup x0 y0) /\ (@IN real y1 x0)) -> real_le y1 y0.
Definition term233 (x0 : real -> Prop) (x1 : real) := forall y0 : real, forall y1 : real, ((~ (@IN real y1 x0)) \/ (real_le y1 y0)) \/ (~ (real_le x1 y0)).
Definition term42 := forall y0 : real, forall y1 : real, forall y2 : real -> Prop, (~ (((forall y3 : real, (forall y4 : real, (@IN real y4 y2) -> real_le y4 y3) = (real_le y0 y3)) /\ (@IN real y1 y2)) -> real_le y1 y0)) -> ~ (forall y3 : real, real_le y3 y3).
Definition term41 := forall y0 : real, forall y1 : real, forall y2 : real -> Prop, (~ (((forall y3 : real, (forall y4 : real, (@IN real y4 y2) -> real_le y4 y3) = (real_le y0 y3)) /\ (@IN real y1 y2)) -> real_le y1 y0)) -> (forall y3 : real, real_le y3 y3) -> False.
Definition term38 (x0 : real) := forall y0 : real, forall y1 : real -> Prop, (~ (((forall y2 : real, (forall y3 : real, (@IN real y3 y1) -> real_le y3 y2) = (real_le x0 y2)) /\ (@IN real y0 y1)) -> real_le y0 x0)) -> ~ (forall y2 : real, real_le y2 y2).
Definition term37 (x0 : real) := forall y0 : real, forall y1 : real -> Prop, (~ (((forall y2 : real, (forall y3 : real, (@IN real y3 y1) -> real_le y3 y2) = (real_le x0 y2)) /\ (@IN real y0 y1)) -> real_le y0 x0)) -> (forall y2 : real, real_le y2 y2) -> False.
Definition term28 := forall y0 : real, real_le y0 y0.
Definition term64 (x0 : real -> Prop) (x1 : real) := or (~ (forall y0 : real, (@IN real y0 x0) -> real_le y0 x1)).
Definition term157 (x0 : real -> Prop) (x1 : real) := exists y0 : real -> real, forall y1 : real, ((@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) \/ (real_le x1 y1).
Definition term138 (x0 : real -> Prop) (x1 : real) := exists y0 : real -> real, forall y1 : real, (fun y2 : real => fun y3 : real => ((@IN real y3 x0) /\ (~ (real_le y3 y2))) \/ (real_le x1 y2)) y1 (y0 y1).
Definition term136 (x0 : type1626) := exists y0 : real -> real, forall y1 : real, x0 y1 (y0 y1).
Definition term77 (x0 : real -> Prop) (x1 : real) := forall y0 : real, ((forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 y0)) \/ (~ (real_le x1 y0))) /\ ((exists y1 : real, (@IN real y1 x0) /\ (~ (real_le y1 y0))) \/ (real_le x1 y0)).
Definition term225 (x0 : real -> Prop) (x1 : real) (x2 : real) := or ((fun y0 : real => (~ (@IN real y0 x0)) \/ (real_le y0 x1)) x2).
Definition term124 (x0 : real -> Prop) (x1 : real) (x2 : real) := or ((fun y0 : real => (@IN real y0 x0) /\ (~ (real_le y0 x1))) x2).
Definition term85 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term9 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => (has_sup x0 y0) = (forall y1 : real, (forall y2 : real, (@IN real y2 x0) -> real_le y2 y1) = (real_le y0 y1))) x1.
Definition term69 (x0 : real -> Prop) (x1 : real) := or (forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le y0 x1)).
Definition term68 (x0 : real -> Prop) (x1 : real) := or (forall y0 : real, (@IN real y0 x0) -> real_le y0 x1).
Definition term243 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real) := (real_le x0 x3) \/ ((~ (@IN real x0 x1)) \/ (~ (real_le x2 x3))).
Definition term260 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real) := imp ((@IN real x0 x1) /\ (real_le x2 x3)).
Definition term213 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (forall y0 : a0, x0 y0) \/ x1.
Definition term121 (x0 : real -> Prop) (x1 : real) := or (exists y0 : real, (fun y1 : real => (@IN real y1 x0) /\ (~ (real_le y1 x1))) y0).
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term263 (x0 : real -> Prop) (x1 : real) (x2 : real) := ((@IN real x1 x0) /\ (real_le x2 x2)) -> real_le x1 x2.
Definition term211 (x0 : real -> Prop) (x1 : real) (x2 : real) := fun y0 : real -> real => (((forall y1 : real, (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y2 y1)) \/ (~ (real_le x2 y1))) /\ (forall y1 : real, ((@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) \/ (real_le x2 y1))) /\ (@IN real x1 x0)) /\ (~ (real_le x1 x2)).
Definition term162 (x0 : Prop) (x1 : type1028) := exists y0 : real -> real, x0 /\ (x1 y0).
Definition term192 (x0 : real -> real) (x1 : real) (x2 : real) (x3 : real -> Prop) := ((forall y0 : real, (forall y1 : real, (~ (@IN real y1 x3)) \/ (real_le y1 y0)) \/ (~ (real_le x1 y0))) /\ (forall y0 : real, ((@IN real (x0 y0) x3) /\ (~ (real_le (x0 y0) y0))) \/ (real_le x1 y0))) /\ (@IN real x2 x3).
Definition term242 (x0 : real) := ~ (real_le x0 x0).
Definition term55 (x0 : real -> Prop) (x1 : real) := exists y0 : real, ~ ((fun y1 : real => (@IN real y1 x0) -> real_le y1 x1) y0).
Definition term205 (x0 : real -> Prop) (x1 : real) (x2 : real) := @eq Prop ((exists y0 : real -> real, ((forall y1 : real, (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y2 y1)) \/ (~ (real_le x2 y1))) /\ (forall y1 : real, ((@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) \/ (real_le x2 y1))) /\ (@IN real x1 x0)) /\ (~ (real_le x1 x2))).
Definition term204 (x0 : real -> Prop) (x1 : real) (x2 : real) := @eq Prop ((exists y0 : real -> real, (fun y1 : real -> real => ((forall y2 : real, (forall y3 : real, (~ (@IN real y3 x0)) \/ (real_le y3 y2)) \/ (~ (real_le x2 y2))) /\ (forall y2 : real, ((@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le x2 y2))) /\ (@IN real x1 x0)) y0) /\ (~ (real_le x1 x2))).
Definition term7 (x0 : real -> Prop) := (fun y0 : real -> Prop => forall y1 : real, (has_sup y0 y1) = (forall y2 : real, (forall y3 : real, (@IN real y3 y0) -> real_le y3 y2) = (real_le y1 y2))) x0.
Definition term258 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real) := (@IN real x0 x1) /\ (real_le x2 x3).
Definition term56 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => (@IN real y0 x0) -> real_le y0 x1) x2.
Definition term245 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real) := @eq Prop ((real_le x0 x3) \/ ((~ (@IN real x0 x1)) \/ (~ (real_le x2 x3)))).
Definition term98 (x0 : real -> Prop) (x1 : real) := @eq Prop (forall y0 : real, ((forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 y0)) \/ (~ (real_le x1 y0))) /\ ((exists y1 : real, (@IN real y1 x0) /\ (~ (real_le y1 y0))) \/ (real_le x1 y0))).
Definition term97 (x0 : real -> Prop) (x1 : real) := @eq Prop (forall y0 : real, ((fun y1 : real => (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y2 y1)) \/ (~ (real_le x1 y1))) y0) /\ ((fun y1 : real => (exists y2 : real, (@IN real y2 x0) /\ (~ (real_le y2 y1))) \/ (real_le x1 y1)) y0)).
Definition term47 (x0 : real -> Prop) (x1 : real) := @eq Prop (forall y0 : real, (@IN real y0 x0) -> real_le y0 x1).
Definition term10 (x0 : real -> Prop) (x1 : real) := forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) = (real_le x1 y0).
Definition term34 (x0 : real) (x1 : real) := forall y0 : real -> Prop, (~ (((forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) = (real_le x1 y1)) /\ (@IN real x0 y0)) -> real_le x0 x1)) -> ~ (forall y1 : real, real_le y1 y1).
Definition term190 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) := and ((forall y0 : real, (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 y0)) \/ (~ (real_le x2 y0))) /\ (forall y0 : real, ((@IN real (x1 y0) x0) /\ (~ (real_le (x1 y0) y0))) \/ (real_le x2 y0))).
Definition term108 (x0 : real -> Prop) (x1 : real) := and ((forall y0 : real, (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 y0)) \/ (~ (real_le x1 y0))) /\ (forall y0 : real, (exists y1 : real, (@IN real y1 x0) /\ (~ (real_le y1 y0))) \/ (real_le x1 y0))).
Definition term123 (x0 : real -> Prop) (x1 : real) (x2 : real) := @eq Prop ((exists y0 : real, (@IN real y0 x0) /\ (~ (real_le y0 x2))) \/ (real_le x1 x2)).
Definition term122 (x0 : real -> Prop) (x1 : real) (x2 : real) := @eq Prop ((exists y0 : real, (fun y1 : real => (@IN real y1 x0) /\ (~ (real_le y1 x2))) y0) \/ (real_le x1 x2)).
Definition term189 (x0 : real -> Prop) (x1 : real) (x2 : real -> real) := and ((fun y0 : real -> real => (forall y1 : real, (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y2 y1)) \/ (~ (real_le x1 y1))) /\ (forall y1 : real, ((@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) \/ (real_le x1 y1))) x2).
Definition term248 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real) := (~ (@IN real x0 x1)) \/ (~ (real_le x2 x3)).
Definition term33 (x0 : real) (x1 : real) := forall y0 : real -> Prop, (~ (((forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) = (real_le x1 y1)) /\ (@IN real x0 y0)) -> real_le x0 x1)) -> (forall y1 : real, real_le y1 y1) -> False.
Definition term241 (x0 : real) := (~ (real_le x0 x0)) -> real_le x0 x0.
Definition term140 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => fun y1 : real => ((@IN real y1 x0) /\ (~ (real_le y1 y0))) \/ (real_le x1 y0)) x2.
Definition term116 (x0 : real -> Prop) (x1 : real) (x2 : real) := (exists y0 : real, (fun y1 : real => (@IN real y1 x0) /\ (~ (real_le y1 x2))) y0) \/ (real_le x1 x2).
Definition term67 (x0 : real -> Prop) (x1 : real) (x2 : real) := (exists y0 : real, (@IN real y0 x0) /\ (~ (real_le y0 x2))) \/ (real_le x1 x2).
Definition term46 (x0 : real -> Prop) (x1 : real) := forall y0 : real, (@IN real y0 x0) -> real_le y0 x1.
Definition term79 (x0 : real) (x1 : real) (x2 : real -> Prop) := (forall y0 : real, ((forall y1 : real, (~ (@IN real y1 x2)) \/ (real_le y1 y0)) \/ (~ (real_le x0 y0))) /\ ((exists y1 : real, (@IN real y1 x2) /\ (~ (real_le y1 y0))) \/ (real_le x0 y0))) /\ (@IN real x1 x2).
Definition term14 (x0 : real) (x1 : real) (x2 : real -> Prop) := (forall y0 : real, (forall y1 : real, (@IN real y1 x2) -> real_le y1 y0) = (real_le x0 y0)) /\ (@IN real x1 x2).
Definition term170 (x0 : real -> Prop) (x1 : real) (x2 : real -> real) := (forall y0 : real, (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 y0)) \/ (~ (real_le x1 y0))) /\ ((fun y0 : real -> real => forall y1 : real, ((@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) \/ (real_le x1 y1)) x2).
Definition term167 (x0 : real -> Prop) (x1 : real) := exists y0 : real -> real, (fun y1 : real -> real => forall y2 : real, ((@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le x1 y2)) y0.
Definition term92 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 y0)) \/ (~ (real_le x1 y0))) x2.
Definition term11 (x0 : real -> Prop) (x1 : real) := and (has_sup x0 x1).
Definition term15 (x0 : real) (x1 : real) (x2 : real -> Prop) := imp ((has_sup x2 x0) /\ (@IN real x1 x2)).
Definition term143 (x0 : real -> Prop) (x1 : real) (x2 : real) := fun y0 : real => (fun y1 : real => fun y2 : real => ((@IN real y2 x0) /\ (~ (real_le y2 y1))) \/ (real_le x1 y1)) x2 y0.
Definition term115 (x0 : real -> Prop) (x1 : Prop) := exists y0 : real, (x0 y0) \/ x1.
Definition term238 (x0 : real) (x1 : real -> Prop) := ~ (@IN real x0 x1).
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term212 (x0 : real -> Prop) (x1 : real) (x2 : real) := exists y0 : real -> real, (((forall y1 : real, (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y2 y1)) \/ (~ (real_le x2 y1))) /\ (forall y1 : real, ((@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) \/ (real_le x2 y1))) /\ (@IN real x1 x0)) /\ (~ (real_le x1 x2)).
Definition term147 (x0 : real -> Prop) (x1 : real) := @eq Prop (forall y0 : real, exists y1 : real, ((@IN real y1 x0) /\ (~ (real_le y1 y0))) \/ (real_le x1 y0)).
Definition term146 (x0 : real -> Prop) (x1 : real) := @eq Prop (forall y0 : real, exists y1 : real, (fun y2 : real => fun y3 : real => ((@IN real y3 x0) /\ (~ (real_le y3 y2))) \/ (real_le x1 y2)) y0 y1).
Definition term210 (x0 : real -> Prop) (x1 : real) (x2 : real) := fun y0 : real -> real => ((fun y1 : real -> real => ((forall y2 : real, (forall y3 : real, (~ (@IN real y3 x0)) \/ (real_le y3 y2)) \/ (~ (real_le x2 y2))) /\ (forall y2 : real, ((@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le x2 y2))) /\ (@IN real x1 x0)) y0) /\ (~ (real_le x1 x2)).
Definition term269 (x0 : real) (x1 : real) (x2 : real -> Prop) := (fun y0 : real -> Prop => (~ (((forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) = (real_le x1 y1)) /\ (@IN real x0 y0)) -> real_le x0 x1)) -> (forall y1 : real, real_le y1 y1) -> False) x2.
Definition term249 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term171 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) := (forall y0 : real, (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 y0)) \/ (~ (real_le x2 y0))) /\ (forall y0 : real, ((@IN real (x1 y0) x0) /\ (~ (real_le (x1 y0) y0))) \/ (real_le x2 y0)).
Definition term107 (x0 : real -> Prop) (x1 : real) := (forall y0 : real, (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 y0)) \/ (~ (real_le x1 y0))) /\ (forall y0 : real, (exists y1 : real, (@IN real y1 x0) /\ (~ (real_le y1 y0))) \/ (real_le x1 y0)).
Definition term71 (x0 : real -> Prop) (x1 : real) (x2 : real) := (forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le y0 x2)) \/ (~ (real_le x1 x2)).
Definition term70 (x0 : real -> Prop) (x1 : real) (x2 : real) := (forall y0 : real, (@IN real y0 x0) -> real_le y0 x2) \/ (~ (real_le x1 x2)).
Definition term163 (x0 : real -> Prop) (x1 : real) := (forall y0 : real, (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 y0)) \/ (~ (real_le x1 y0))) /\ (exists y0 : real -> real, (fun y1 : real -> real => forall y2 : real, ((@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le x1 y2)) y0).
Definition term203 (x0 : real) (x1 : real) (x2 : real -> Prop) := and (exists y0 : real -> real, (fun y1 : real -> real => ((forall y2 : real, (forall y3 : real, (~ (@IN real y3 x2)) \/ (real_le y3 y2)) \/ (~ (real_le x0 y2))) /\ (forall y2 : real, ((@IN real (y1 y2) x2) /\ (~ (real_le (y1 y2) y2))) \/ (real_le x0 y2))) /\ (@IN real x1 x2)) y0).
Definition term186 (x0 : real -> Prop) (x1 : real) := and (exists y0 : real -> real, (fun y1 : real -> real => (forall y2 : real, (forall y3 : real, (~ (@IN real y3 x0)) \/ (real_le y3 y2)) \/ (~ (real_le x1 y2))) /\ (forall y2 : real, ((@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le x1 y2))) y0).
Definition term178 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term215 (x0 : real -> Prop) (x1 : Prop) := (forall y0 : real, x0 y0) \/ x1.
Definition term262 (x0 : real) (x1 : real -> Prop) (x2 : real) := (@IN real x0 x1) /\ (real_le x2 x2).
Definition term222 (x0 : real -> Prop) (x1 : real) := or (forall y0 : real, (fun y1 : real => (~ (@IN real y1 x0)) \/ (real_le y1 x1)) y0).
Definition term218 (x0 : real -> Prop) (x1 : real) (x2 : real) := forall y0 : real, ((fun y1 : real => (~ (@IN real y1 x0)) \/ (real_le y1 x2)) y0) \/ (~ (real_le x1 x2)).
Definition term230 (x0 : real -> Prop) (x1 : real) (x2 : real) := fun y0 : real => ((~ (@IN real y0 x0)) \/ (real_le y0 x2)) \/ (~ (real_le x1 x2)).
Definition term109 (x0 : real) (x1 : real) (x2 : real -> Prop) := ((forall y0 : real, (forall y1 : real, (~ (@IN real y1 x2)) \/ (real_le y1 y0)) \/ (~ (real_le x0 y0))) /\ (forall y0 : real, (exists y1 : real, (@IN real y1 x2) /\ (~ (real_le y1 y0))) \/ (real_le x0 y0))) /\ (@IN real x1 x2).
Definition term137 (x0 : real -> Prop) (x1 : real) := forall y0 : real, exists y1 : real, (fun y2 : real => fun y3 : real => ((@IN real y3 x0) /\ (~ (real_le y3 y2))) \/ (real_le x1 y2)) y0 y1.
Definition term135 (x0 : type1626) := forall y0 : real, exists y1 : real, x0 y0 y1.
Definition term132 (x0 : real -> Prop) (x1 : real) := forall y0 : real, exists y1 : real, ((@IN real y1 x0) /\ (~ (real_le y1 y0))) \/ (real_le x1 y0).
Definition term99 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (fun y1 : real => (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y2 y1)) \/ (~ (real_le x1 y1))) y0.
Definition term256 (x0 : real) (x1 : real -> Prop) := and (@IN real x0 x1).
Definition term198 (x0 : real -> Prop) (x1 : real) (x2 : real) := (exists y0 : real -> real, (fun y1 : real -> real => ((forall y2 : real, (forall y3 : real, (~ (@IN real y3 x0)) \/ (real_le y3 y2)) \/ (~ (real_le x2 y2))) /\ (forall y2 : real, ((@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le x2 y2))) /\ (@IN real x1 x0)) y0) /\ (~ (real_le x1 x2)).
Definition term193 (x0 : real) (x1 : real) (x2 : real -> Prop) := fun y0 : real -> real => ((fun y1 : real -> real => (forall y2 : real, (forall y3 : real, (~ (@IN real y3 x2)) \/ (real_le y3 y2)) \/ (~ (real_le x0 y2))) /\ (forall y2 : real, ((@IN real (y1 y2) x2) /\ (~ (real_le (y1 y2) y2))) \/ (real_le x0 y2))) y0) /\ (@IN real x1 x2).
Definition term180 (x0 : type1028) (x1 : Prop) := exists y0 : real -> real, (x0 y0) /\ x1.
Definition term94 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => (exists y1 : real, (@IN real y1 x0) /\ (~ (real_le y1 y0))) \/ (real_le x1 y0)) x2.
Definition term53 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term86 (x0 : real -> Prop) (x1 : real -> Prop) := forall y0 : real, (x0 y0) /\ (x1 y0).
Definition term57 (x0 : real -> Prop) (x1 : real) (x2 : real) := ~ ((fun y0 : real => (@IN real y0 x0) -> real_le y0 x1) x2).
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term113 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) \/ x1.
Definition term101 (x0 : real -> Prop) (x1 : real) := forall y0 : real, (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 y0)) \/ (~ (real_le x1 y0)).
Definition term261 (x0 : real -> Prop) (x1 : real) (x2 : real) (x3 : real) := ((@IN real x2 x0) /\ (real_le x1 x3)) -> real_le x2 x3.
Definition term254 (x0 : real) (x1 : real -> Prop) := ~ (~ (@IN real x0 x1)).
Definition term43 := fun y0 : real => real_le y0 y0.
Definition term74 (x0 : real -> Prop) (x1 : real) (x2 : real) := ((forall y0 : real, (@IN real y0 x0) -> real_le y0 x2) \/ (~ (real_le x1 x2))) /\ ((~ (forall y0 : real, (@IN real y0 x0) -> real_le y0 x2)) \/ (real_le x1 x2)).
Definition term91 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (exists y1 : real, (@IN real y1 x0) /\ (~ (real_le y1 y0))) \/ (real_le x1 y0).
Definition term221 (x0 : real -> Prop) (x1 : real) := forall y0 : real, (fun y1 : real => (~ (@IN real y1 x0)) \/ (real_le y1 x1)) y0.
Definition term105 (x0 : real -> Prop) (x1 : real) := forall y0 : real, (fun y1 : real => (exists y2 : real, (@IN real y2 x0) /\ (~ (real_le y2 y1))) \/ (real_le x1 y1)) y0.
Definition term100 (x0 : real -> Prop) (x1 : real) := forall y0 : real, (fun y1 : real => (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y2 y1)) \/ (~ (real_le x1 y1))) y0.
Definition term110 (x0 : real) (x1 : real) (x2 : real -> Prop) := and (((forall y0 : real, (forall y1 : real, (~ (@IN real y1 x2)) \/ (real_le y1 y0)) \/ (~ (real_le x0 y0))) /\ (forall y0 : real, (exists y1 : real, (@IN real y1 x2) /\ (~ (real_le y1 y0))) \/ (real_le x0 y0))) /\ (@IN real x1 x2)).
Definition term44 (x0 : real -> Prop) (x1 : real) (x2 : real) := (@IN real x1 x0) -> real_le x1 x2.
Definition term214 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := forall y0 : a0, (x0 y0) \/ x1.
Definition term128 (x0 : real -> Prop) (x1 : real) (x2 : real) := fun y0 : real => ((fun y1 : real => (@IN real y1 x0) /\ (~ (real_le y1 x2))) y0) \/ (real_le x1 x2).
Definition term93 (x0 : real -> Prop) (x1 : real) (x2 : real) := and ((fun y0 : real => (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 y0)) \/ (~ (real_le x1 y0))) x2).
Definition term142 (x0 : real -> Prop) (x1 : real) (x2 : real) (x3 : real) := (fun y0 : real => ((@IN real y0 x0) /\ (~ (real_le y0 x2))) \/ (real_le x1 x2)) x3.
Definition term95 (x0 : real -> Prop) (x1 : real) (x2 : real) := ((fun y0 : real => (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 y0)) \/ (~ (real_le x1 y0))) x2) /\ ((fun y0 : real => (exists y1 : real, (@IN real y1 x0) /\ (~ (real_le y1 y0))) \/ (real_le x1 y0)) x2).
Definition term181 (x0 : real) (x1 : real) (x2 : real -> Prop) := (exists y0 : real -> real, (fun y1 : real -> real => (forall y2 : real, (forall y3 : real, (~ (@IN real y3 x2)) \/ (real_le y3 y2)) \/ (~ (real_le x0 y2))) /\ (forall y2 : real, ((@IN real (y1 y2) x2) /\ (~ (real_le (y1 y2) y2))) \/ (real_le x0 y2))) y0) /\ (@IN real x1 x2).
Definition term268 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real -> Prop, (~ (((forall y2 : real, (forall y3 : real, (@IN real y3 y1) -> real_le y3 y2) = (real_le x0 y2)) /\ (@IN real y0 y1)) -> real_le y0 x0)) -> (forall y2 : real, real_le y2 y2) -> False) x1.
Definition term1 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term117 (x0 : real -> Prop) (x1 : real) (x2 : real) := exists y0 : real, ((fun y1 : real => (@IN real y1 x0) /\ (~ (real_le y1 x2))) y0) \/ (real_le x1 x2).
Definition term255 (x0 : real) (x1 : real -> Prop) := and (~ (~ (@IN real x0 x1))).
Definition term164 (x0 : real -> Prop) (x1 : real) := exists y0 : real -> real, (forall y1 : real, (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y2 y1)) \/ (~ (real_le x1 y1))) /\ ((fun y1 : real -> real => forall y2 : real, ((@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le x1 y2)) y0).
Definition term29 (x0 : real -> Prop) (x1 : real) (x2 : real) := imp (~ (((forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) = (real_le x2 y0)) /\ (@IN real x1 x0)) -> real_le x1 x2)).
Definition term229 (x0 : real -> Prop) (x1 : real) (x2 : real) := fun y0 : real => ((fun y1 : real => (~ (@IN real y1 x0)) \/ (real_le y1 x2)) y0) \/ (~ (real_le x1 x2)).
Definition term197 (x0 : real -> Prop) (x1 : real) (x2 : real) := (exists y0 : real -> real, ((forall y1 : real, (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y2 y1)) \/ (~ (real_le x2 y1))) /\ (forall y1 : real, ((@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) \/ (real_le x2 y1))) /\ (@IN real x1 x0)) /\ (~ (real_le x1 x2)).
Definition term217 (x0 : real -> Prop) (x1 : real) (x2 : real) := (forall y0 : real, (fun y1 : real => (~ (@IN real y1 x0)) \/ (real_le y1 x2)) y0) \/ (~ (real_le x1 x2)).
Definition term173 (x0 : real -> Prop) (x1 : real) := fun y0 : real -> real => (forall y1 : real, (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y2 y1)) \/ (~ (real_le x1 y1))) /\ (forall y1 : real, ((@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) \/ (real_le x1 y1)).
Definition term227 (x0 : real -> Prop) (x1 : real) (x2 : real) (x3 : real) := ((fun y0 : real => (~ (@IN real y0 x0)) \/ (real_le y0 x3)) x1) \/ (~ (real_le x2 x3)).
Definition term179 (x0 : type1028) (x1 : Prop) := (exists y0 : real -> real, x0 y0) /\ x1.
Definition term48 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) = (real_le x1 y0).
Definition term235 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => forall y1 : real, ((~ (@IN real y1 x0)) \/ (real_le y1 y0)) \/ (~ (real_le x1 y0))) x2.
Definition term21 (x0 : real -> Prop) (x1 : real) (x2 : real) := ~ (((forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) = (real_le x2 y0)) /\ (@IN real x1 x0)) -> real_le x1 x2).
Definition term111 (x0 : real -> Prop) (x1 : real) (x2 : real) := (((forall y0 : real, (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 y0)) \/ (~ (real_le x2 y0))) /\ (forall y0 : real, (exists y1 : real, (@IN real y1 x0) /\ (~ (real_le y1 y0))) \/ (real_le x2 y0))) /\ (@IN real x1 x0)) /\ (~ (real_le x1 x2)).
Definition term131 (x0 : real -> Prop) (x1 : real) := fun y0 : real => exists y1 : real, ((@IN real y1 x0) /\ (~ (real_le y1 y0))) \/ (real_le x1 y0).
Definition term40 := fun y0 : real => forall y1 : real, forall y2 : real -> Prop, (~ (((forall y3 : real, (forall y4 : real, (@IN real y4 y2) -> real_le y4 y3) = (real_le y0 y3)) /\ (@IN real y1 y2)) -> real_le y1 y0)) -> ~ (forall y3 : real, real_le y3 y3).
Definition term39 := fun y0 : real => forall y1 : real, forall y2 : real -> Prop, (~ (((forall y3 : real, (forall y4 : real, (@IN real y4 y2) -> real_le y4 y3) = (real_le y0 y3)) /\ (@IN real y1 y2)) -> real_le y1 y0)) -> (forall y3 : real, real_le y3 y3) -> False.
Definition term23 (x0 : real -> Prop) (x1 : real) (x2 : real) := ((~ (((forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) = (real_le x2 y0)) /\ (@IN real x1 x0)) -> real_le x1 x2)) -> (forall y0 : real, real_le y0 y0) -> False) -> (~ (((forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) = (real_le x2 y0)) /\ (@IN real x1 x0)) -> real_le x1 x2)) -> (forall y0 : real, real_le y0 y0) -> False.
Definition term234 (x0 : real) := (fun y0 : real => real_le y0 y0) x0.
Definition term156 (x0 : real -> Prop) (x1 : real) := fun y0 : real -> real => forall y1 : real, ((@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) \/ (real_le x1 y1).
Definition term155 (x0 : real -> Prop) (x1 : real) := fun y0 : real -> real => forall y1 : real, (fun y2 : real => fun y3 : real => ((@IN real y3 x0) /\ (~ (real_le y3 y2))) \/ (real_le x1 y2)) y1 (y0 y1).
Definition term130 (x0 : real -> Prop) (x1 : real) (x2 : real) := exists y0 : real, ((@IN real y0 x0) /\ (~ (real_le y0 x2))) \/ (real_le x1 x2).
Definition term148 (x0 : real -> Prop) (x1 : real) (x2 : real -> real) (x3 : real) := (fun y0 : real => fun y1 : real => ((@IN real y1 x0) /\ (~ (real_le y1 y0))) \/ (real_le x1 y0)) x3 (x2 x3).
Definition term63 (x0 : real) (x1 : real) := ~ (real_le x0 x1).
Definition term60 (x0 : real -> Prop) (x1 : real) := exists y0 : real, (@IN real y0 x0) /\ (~ (real_le y0 x1)).
Definition term141 (x0 : real -> Prop) (x1 : real) (x2 : real) (x3 : real) := (fun y0 : real => fun y1 : real => ((@IN real y1 x0) /\ (~ (real_le y1 y0))) \/ (real_le x1 y0)) x2 x3.
Definition term35 (x0 : real) := fun y0 : real => forall y1 : real -> Prop, (~ (((forall y2 : real, (forall y3 : real, (@IN real y3 y1) -> real_le y3 y2) = (real_le x0 y2)) /\ (@IN real y0 y1)) -> real_le y0 x0)) -> (forall y2 : real, real_le y2 y2) -> False.
Definition term251 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real) := ~ ((~ (@IN real x0 x1)) \/ (~ (real_le x2 x3))).
Definition term149 (x0 : real -> Prop) (x1 : real) (x2 : real -> real) (x3 : real) := (fun y0 : real => ((@IN real y0 x0) /\ (~ (real_le y0 x3))) \/ (real_le x1 x3)) (x2 x3).
Definition term200 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real -> real) := (fun y0 : real -> real => ((forall y1 : real, (forall y2 : real, (~ (@IN real y2 x2)) \/ (real_le y2 y1)) \/ (~ (real_le x0 y1))) /\ (forall y1 : real, ((@IN real (y0 y1) x2) /\ (~ (real_le (y0 y1) y1))) \/ (real_le x0 y1))) /\ (@IN real x1 x2)) x3.
Definition term244 (x0 : real -> Prop) (x1 : real) (x2 : real) (x3 : real) := @eq Prop ((~ (@IN real x1 x0)) \/ ((real_le x1 x3) \/ (~ (real_le x2 x3)))).
Definition term208 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) (x3 : real) := ((fun y0 : real -> real => ((forall y1 : real, (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y2 y1)) \/ (~ (real_le x3 y1))) /\ (forall y1 : real, ((@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) \/ (real_le x3 y1))) /\ (@IN real x2 x0)) x1) /\ (~ (real_le x2 x3)).
Definition term182 (x0 : real) (x1 : real) (x2 : real -> Prop) := exists y0 : real -> real, ((fun y1 : real -> real => (forall y2 : real, (forall y3 : real, (~ (@IN real y3 x2)) \/ (real_le y3 y2)) \/ (~ (real_le x0 y2))) /\ (forall y2 : real, ((@IN real (y1 y2) x2) /\ (~ (real_le (y1 y2) y2))) \/ (real_le x0 y2))) y0) /\ (@IN real x1 x2).
Definition term151 (x0 : real -> Prop) (x1 : real) (x2 : real -> real) := fun y0 : real => (fun y1 : real => fun y2 : real => ((@IN real y2 x0) /\ (~ (real_le y2 y1))) \/ (real_le x1 y1)) y0 (x2 y0).
Definition term96 (x0 : real -> Prop) (x1 : real) := fun y0 : real => ((fun y1 : real => (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y2 y1)) \/ (~ (real_le x1 y1))) y0) /\ ((fun y1 : real => (exists y2 : real, (@IN real y2 x0) /\ (~ (real_le y2 y1))) \/ (real_le x1 y1)) y0).
Definition term220 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (fun y1 : real => (~ (@IN real y1 x0)) \/ (real_le y1 x1)) y0.
Definition term104 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (fun y1 : real => (exists y2 : real, (@IN real y2 x0) /\ (~ (real_le y2 y1))) \/ (real_le x1 y1)) y0.
Definition term118 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => (@IN real y0 x0) /\ (~ (real_le y0 x1))) x2.
Definition term31 (x0 : real) (x1 : real) := fun y0 : real -> Prop => (~ (((forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) = (real_le x1 y1)) /\ (@IN real x0 y0)) -> real_le x0 x1)) -> (forall y1 : real, real_le y1 y1) -> False.
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term239 (x0 : real) (x1 : real -> Prop) := (~ (@IN real x0 x1)) -> @IN real x0 x1.
Definition term58 (x0 : real -> Prop) (x1 : real) := fun y0 : real => ~ ((fun y1 : real => (@IN real y1 x0) -> real_le y1 x1) y0).
Definition term87 (x0 : real -> Prop) (x1 : real -> Prop) := (forall y0 : real, x0 y0) /\ (forall y0 : real, x1 y0).
Definition term152 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) := fun y0 : real => ((@IN real (x1 y0) x0) /\ (~ (real_le (x1 y0) y0))) \/ (real_le x2 y0).
Definition term13 (x0 : real) (x1 : real) (x2 : real -> Prop) := (has_sup x2 x0) /\ (@IN real x1 x2).
Definition term50 (x0 : real -> Prop) (x1 : real) (x2 : real) := (@IN real x1 x0) /\ (~ (real_le x1 x2)).
Definition term191 (x0 : real) (x1 : real -> real) (x2 : real) (x3 : real -> Prop) := ((fun y0 : real -> real => (forall y1 : real, (forall y2 : real, (~ (@IN real y2 x3)) \/ (real_le y2 y1)) \/ (~ (real_le x0 y1))) /\ (forall y1 : real, ((@IN real (y0 y1) x3) /\ (~ (real_le (y0 y1) y1))) \/ (real_le x0 y1))) x1) /\ (@IN real x2 x3).
Definition term169 (x0 : real -> Prop) (x1 : real) := @eq Prop ((forall y0 : real, (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 y0)) \/ (~ (real_le x1 y0))) /\ (exists y0 : real -> real, forall y1 : real, ((@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) \/ (real_le x1 y1))).
Definition term168 (x0 : real -> Prop) (x1 : real) := @eq Prop ((forall y0 : real, (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 y0)) \/ (~ (real_le x1 y0))) /\ (exists y0 : real -> real, (fun y1 : real -> real => forall y2 : real, ((@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le x1 y2)) y0)).
Definition term84 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term90 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 y0)) \/ (~ (real_le x1 y0)).
Definition term20 (x0 : real -> Prop) (x1 : real) (x2 : real) := (~ (((forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) = (real_le x2 y0)) /\ (@IN real x1 x0)) -> real_le x1 x2)) -> False.
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term36 (x0 : real) := fun y0 : real => forall y1 : real -> Prop, (~ (((forall y2 : real, (forall y3 : real, (@IN real y3 y1) -> real_le y3 y2) = (real_le x0 y2)) /\ (@IN real y0 y1)) -> real_le y0 x0)) -> ~ (forall y2 : real, real_le y2 y2).
Definition term18 (x0 : real -> Prop) (x1 : real) (x2 : real) := ((forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) = (real_le x2 y0)) /\ (@IN real x1 x0)) -> real_le x1 x2.
Definition term177 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term83 (x0 : real -> Prop) (x1 : real) (x2 : real) := ((forall y0 : real, ((forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 y0)) \/ (~ (real_le x2 y0))) /\ ((exists y1 : real, (@IN real y1 x0) /\ (~ (real_le y1 y0))) \/ (real_le x2 y0))) /\ (@IN real x1 x0)) /\ (~ (real_le x1 x2)).
Definition term82 (x0 : real -> Prop) (x1 : real) (x2 : real) := ((forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) = (real_le x2 y0)) /\ (@IN real x1 x0)) /\ (~ (real_le x1 x2)).
Definition term76 (x0 : real -> Prop) (x1 : real) := fun y0 : real => ((forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 y0)) \/ (~ (real_le x1 y0))) /\ ((exists y1 : real, (@IN real y1 x0) /\ (~ (real_le y1 y0))) \/ (real_le x1 y0)).
Definition term125 (x0 : real -> Prop) (x1 : real) (x2 : real) := or ((@IN real x1 x0) /\ (~ (real_le x1 x2))).
Definition term75 (x0 : real -> Prop) (x1 : real) (x2 : real) := ((forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le y0 x2)) \/ (~ (real_le x1 x2))) /\ ((exists y0 : real, (@IN real y0 x0) /\ (~ (real_le y0 x2))) \/ (real_le x1 x2)).
Definition term25 (x0 : real -> Prop) (x1 : real) (x2 : real) := (((~ (((forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) = (real_le x2 y0)) /\ (@IN real x1 x0)) -> real_le x1 x2)) -> (forall y0 : real, real_le y0 y0) -> False) -> (~ (((forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) = (real_le x2 y0)) /\ (@IN real x1 x0)) -> real_le x1 x2)) -> (forall y0 : real, real_le y0 y0) -> False) -> ((~ (((forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) = (real_le x2 y0)) /\ (@IN real x1 x0)) -> real_le x1 x2)) -> (forall y0 : real, real_le y0 y0) -> False) -> (~ (((forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) = (real_le x2 y0)) /\ (@IN real x1 x0)) -> real_le x1 x2)) -> (forall y0 : real, real_le y0 y0) -> False.
Definition term59 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (@IN real y0 x0) /\ (~ (real_le y0 x1)).
Definition term129 (x0 : real -> Prop) (x1 : real) (x2 : real) := fun y0 : real => ((@IN real y0 x0) /\ (~ (real_le y0 x2))) \/ (real_le x1 x2).
Definition term209 (x0 : real -> real) (x1 : real -> Prop) (x2 : real) (x3 : real) := (((forall y0 : real, (forall y1 : real, (~ (@IN real y1 x1)) \/ (real_le y1 y0)) \/ (~ (real_le x3 y0))) /\ (forall y0 : real, ((@IN real (x0 y0) x1) /\ (~ (real_le (x0 y0) y0))) \/ (real_le x3 y0))) /\ (@IN real x2 x1)) /\ (~ (real_le x2 x3)).
Definition term134 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term49 (x0 : real -> Prop) (x1 : real) (x2 : real) := ~ ((@IN real x1 x0) -> real_le x1 x2).
Definition term265 (x0 : real) (x1 : real) := (real_le x0 x1) -> False.
Definition term65 (x0 : real -> Prop) (x1 : real) := or (exists y0 : real, (@IN real y0 x0) /\ (~ (real_le y0 x1))).
Definition term267 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real -> Prop, (~ (((forall y3 : real, (forall y4 : real, (@IN real y4 y2) -> real_le y4 y3) = (real_le y0 y3)) /\ (@IN real y1 y2)) -> real_le y1 y0)) -> (forall y3 : real, real_le y3 y3) -> False) x0.
Definition term231 (x0 : real -> Prop) (x1 : real) (x2 : real) := forall y0 : real, ((~ (@IN real y0 x0)) \/ (real_le y0 x2)) \/ (~ (real_le x1 x2)).
Definition term88 (x0 : real -> Prop) (x1 : real) := forall y0 : real, ((fun y1 : real => (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y2 y1)) \/ (~ (real_le x1 y1))) y0) /\ ((fun y1 : real => (exists y2 : real, (@IN real y2 x0) /\ (~ (real_le y2 y1))) \/ (real_le x1 y1)) y0).
Definition term232 (x0 : real -> Prop) (x1 : real) := fun y0 : real => forall y1 : real, ((~ (@IN real y1 x0)) \/ (real_le y1 y0)) \/ (~ (real_le x1 y0)).
Definition term154 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) := forall y0 : real, ((@IN real (x1 y0) x0) /\ (~ (real_le (x1 y0) y0))) \/ (real_le x2 y0).
