Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term316 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) (x3 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((~ (@I ((a0 -> Prop) -> Prop) x0 y0)) \/ (~ (@I (a0 -> Prop) y0 x2))) \/ (@I (a0 -> Prop) x1 x2)) x3.
Definition term135 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (forall y0 : a0, (forall y1 : a0 -> Prop, (~ (x0 y1)) \/ (~ (y1 y0))) \/ (x1 y0)) /\ ((fun y0 : a0 -> Prop => exists y1 : a0, ((x0 y0) /\ (y0 y1)) /\ (~ (x1 y1))) x2).
Definition term208 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (exists y0 : a0 -> Prop, exists y1 : a0, (forall y2 : a0, (forall y3 : a0 -> Prop, (~ (x0 y3)) \/ (~ (y3 y2))) \/ (x1 y2)) /\ (((x0 y0) /\ (y0 y1)) /\ (~ (x1 y1)))) \/ (exists y0 : a0, exists y1 : a0 -> Prop, (((x0 y1) /\ (y1 y0)) /\ (~ (x1 y0))) /\ (forall y2 : a0 -> Prop, forall y3 : a0, ((~ (x0 y2)) \/ (~ (y2 y3))) \/ (x1 y3))).
Definition term344 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := imp ((@I ((a0 -> Prop) -> Prop) x0 x1) /\ (@I (a0 -> Prop) x1 x2)).
Definition term55 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := ~ ((forall y0 : a0, (exists y1 : a0 -> Prop, (x0 y1) /\ (y1 y0)) -> x1 y0) = (forall y0 : a0 -> Prop, forall y1 : a0, ((x0 y0) /\ (y0 y1)) -> x1 y1)).
Definition term59 (a0 : Type') (x0 : type686 a0) := forall y0 : a0 -> Prop, ~ (x0 y0).
Definition term101 (a0 : Type') (x0 : type686 a0) := ~ (all x0).
Definition term347 := (~ False) -> False.
Definition term244 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : type686 a0) (x3 : a0 -> Prop) := ((forall y0 : a0, (forall y1 : a0 -> Prop, (~ (x2 y1)) \/ (~ (y1 y0))) \/ (x3 y0)) /\ (((x2 x0) /\ (x0 x1)) /\ (~ (x3 x1)))) \/ (exists y0 : a0 -> Prop, (((x2 y0) /\ (y0 x1)) /\ (~ (x3 x1))) /\ (forall y1 : a0 -> Prop, forall y2 : a0, ((~ (x2 y1)) \/ (~ (y1 y2))) \/ (x3 y2))).
Definition term100 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := forall y0 : a0, ((~ (x0 x1)) \/ (~ (x1 y0))) \/ (x2 y0).
Definition term323 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (~ (@I (a0 -> Prop) x1 x3)) \/ ((~ (@I ((a0 -> Prop) -> Prop) x0 x1)) \/ (@I (a0 -> Prop) x2 x3)).
Definition term147 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (forall y0 : a0, (forall y1 : a0 -> Prop, (~ (x0 y1)) \/ (~ (y1 y0))) \/ (x2 y0)) /\ ((fun y0 : a0 => ((x0 x1) /\ (x1 y0)) /\ (~ (x2 y0))) x3).
Definition term159 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := (exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (x0 y1) /\ (y1 x2)) y0) /\ (~ (x1 x2)).
Definition term28 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ((@IN (a0 -> Prop) x1 x0) /\ (@IN a0 x3 x1)) -> x2 x3.
Definition term335 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (~ ((~ (@I ((a0 -> Prop) -> Prop) x0 x1)) \/ (~ (@I (a0 -> Prop) x1 x3)))) -> @I (a0 -> Prop) x2 x3.
Definition term281 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := (@I ((a0 -> Prop) -> Prop) x0 x1) /\ (@I (a0 -> Prop) x1 x2).
Definition term174 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := and (exists y0 : a0, exists y1 : a0 -> Prop, ((x0 y1) /\ (y1 y0)) /\ (~ (x1 y0))).
Definition term30 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := fun y0 : a0 => ((@IN (a0 -> Prop) x1 x0) /\ (@IN a0 y0 x1)) -> x2 y0.
Definition term118 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (forall y0 : a0, (exists y1 : a0 -> Prop, (x0 y1) /\ (y1 y0)) -> x1 y0) /\ (~ (forall y0 : a0 -> Prop, forall y1 : a0, ((x0 y0) /\ (y0 y1)) -> x1 y1)).
Definition term53 (x0 : Prop) := ~ (~ x0).
Definition term312 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := forall y0 : a0 -> Prop, ((~ (@I ((a0 -> Prop) -> Prop) x0 y0)) \/ (~ (@I (a0 -> Prop) y0 x2))) \/ (@I (a0 -> Prop) x1 x2).
Definition term193 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) (x3 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((x0 y0) /\ (y0 x2)) /\ (~ (x1 x2))) x3.
Definition term8 (a0 : Type') (x0 : type686 a0) (x1 : a0) := exists y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) /\ (@IN a0 x1 y0).
Definition term272 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := or (~ (@I ((a0 -> Prop) -> Prop) x0 x1)).
Definition term309 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ((fun y0 : a0 -> Prop => (~ (@I ((a0 -> Prop) -> Prop) x0 y0)) \/ (~ (@I (a0 -> Prop) y0 x3))) x1) \/ (@I (a0 -> Prop) x2 x3).
Definition term261 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : type686 a0) (x3 : a0 -> Prop) := fun y0 : a0 -> Prop => ((forall y1 : a0, (forall y2 : a0 -> Prop, (~ (x2 y2)) \/ (~ (y2 y1))) \/ (x3 y1)) /\ (((x2 x0) /\ (x0 x1)) /\ (~ (x3 x1)))) \/ ((fun y1 : a0 -> Prop => (((x2 y1) /\ (y1 x1)) /\ (~ (x3 x1))) /\ (forall y2 : a0 -> Prop, forall y3 : a0, ((~ (x2 y2)) \/ (~ (y2 y3))) \/ (x3 y3))) y0).
Definition term178 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := (fun y0 : a0 => exists y1 : a0 -> Prop, ((x0 y1) /\ (y1 y0)) /\ (~ (x1 y0))) x2.
Definition term43 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : type686 a0, (forall y2 : a0, (exists y3 : a0 -> Prop, (y1 y3) /\ (y3 y2)) -> y0 y2) = (forall y2 : a0 -> Prop, forall y3 : a0, ((y1 y2) /\ (y2 y3)) -> y0 y3).
Definition term42 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : type686 a0, (forall y2 : a0, (@IN a0 y2 (@UNIONS a0 y1)) -> y0 y2) = (forall y2 : a0 -> Prop, forall y3 : a0, ((@IN (a0 -> Prop) y2 y1) /\ (@IN a0 y3 y2)) -> y0 y3).
Definition term136 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (forall y0 : a0, (forall y1 : a0 -> Prop, (~ (x0 y1)) \/ (~ (y1 y0))) \/ (x2 y0)) /\ (exists y0 : a0, ((x0 x1) /\ (x1 y0)) /\ (~ (x2 y0))).
Definition term86 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ~ (((x0 x1) /\ (x1 x3)) -> x2 x3).
Definition term214 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := exists y0 : a0 -> Prop, ((fun y1 : a0 -> Prop => exists y2 : a0, (forall y3 : a0, (forall y4 : a0 -> Prop, (~ (x0 y4)) \/ (~ (y4 y3))) \/ (x1 y3)) /\ (((x0 y1) /\ (y1 y2)) /\ (~ (x1 y2)))) y0) \/ (exists y1 : a0, exists y2 : a0 -> Prop, (((x0 y2) /\ (y2 y1)) /\ (~ (x1 y1))) /\ (forall y3 : a0 -> Prop, forall y4 : a0, ((~ (x0 y3)) \/ (~ (y3 y4))) \/ (x1 y4))).
Definition term17 (a0 : Type') (x0 : type686 a0) (x1 : a0) := imp (exists y0 : a0 -> Prop, (x0 y0) /\ (y0 x1)).
Definition term237 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := fun y0 : a0 => (fun y1 : a0 => exists y2 : a0 -> Prop, (((x0 y2) /\ (y2 y1)) /\ (~ (x1 y1))) /\ (forall y3 : a0 -> Prop, forall y4 : a0, ((~ (x0 y3)) \/ (~ (y3 y4))) \/ (x1 y4))) y0.
Definition term179 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := fun y0 : a0 => (fun y1 : a0 => exists y2 : a0 -> Prop, ((x0 y2) /\ (y2 y1)) /\ (~ (x1 y1))) y0.
Definition term339 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := (~ (~ (@I ((a0 -> Prop) -> Prop) x0 x1))) /\ (~ (~ (@I (a0 -> Prop) x1 x2))).
Definition term98 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := exists y0 : a0, ((x0 x1) /\ (x1 y0)) /\ (~ (x2 y0)).
Definition term228 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term293 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (forall y0 : a0, (forall y1 : a0 -> Prop, (~ (@I ((a0 -> Prop) -> Prop) x0 y1)) \/ (~ (@I (a0 -> Prop) y1 y0))) \/ (@I (a0 -> Prop) x2 y0)) /\ (((@I ((a0 -> Prop) -> Prop) x0 x1) /\ (@I (a0 -> Prop) x1 x3)) /\ (~ (@I (a0 -> Prop) x2 x3))).
Definition term192 (a0 : Type') (x0 : a0) (x1 : type686 a0) (x2 : a0 -> Prop) := exists y0 : a0 -> Prop, ((fun y1 : a0 -> Prop => ((x1 y1) /\ (y1 x0)) /\ (~ (x2 x0))) y0) /\ (forall y1 : a0 -> Prop, forall y2 : a0, ((~ (x1 y1)) \/ (~ (y1 y2))) \/ (x2 y2)).
Definition term67 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (x0 x1).
Definition term313 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := fun y0 : a0 => forall y1 : a0 -> Prop, ((~ (@I ((a0 -> Prop) -> Prop) x0 y1)) \/ (~ (@I (a0 -> Prop) y1 y0))) \/ (@I (a0 -> Prop) x1 y0).
Definition term75 (a0 : Type') (x0 : a0 -> Prop) := ~ (all x0).
Definition term3 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term7 (a0 : Type') (x0 : a0) (x1 : type686 a0) := @IN a0 x0 (@UNIONS a0 x1).
Definition term63 (a0 : Type') (x0 : type686 a0) (x1 : a0) (x2 : a0 -> Prop) := ~ ((fun y0 : a0 -> Prop => (x0 y0) /\ (y0 x1)) x2).
Definition term125 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term46 (x0 : Prop) := (~ x0) -> False.
Definition term216 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => exists y2 : a0, (forall y3 : a0, (forall y4 : a0 -> Prop, (~ (x0 y4)) \/ (~ (y4 y3))) \/ (x1 y3)) /\ (((x0 y1) /\ (y1 y2)) /\ (~ (x1 y2)))) y0.
Definition term131 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => exists y2 : a0, ((x0 y1) /\ (y1 y2)) /\ (~ (x1 y2))) y0.
Definition term209 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) \/ x1.
Definition term343 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := imp (~ ((~ (@I ((a0 -> Prop) -> Prop) x0 x1)) \/ (~ (@I (a0 -> Prop) x1 x2)))).
Definition term23 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := forall y0 : a0, (exists y1 : a0 -> Prop, (x0 y1) /\ (y1 y0)) -> x1 y0.
Definition term275 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ((~ (@I ((a0 -> Prop) -> Prop) x0 x1)) \/ (~ (@I (a0 -> Prop) x1 x3))) \/ (@I (a0 -> Prop) x2 x3).
Definition term176 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (exists y0 : a0, (fun y1 : a0 => exists y2 : a0 -> Prop, ((x0 y2) /\ (y2 y1)) /\ (~ (x1 y1))) y0) /\ (forall y0 : a0 -> Prop, forall y1 : a0, ((~ (x0 y0)) \/ (~ (y0 y1))) \/ (x1 y1)).
Definition term235 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := or (exists y0 : a0, (fun y1 : a0 => (forall y2 : a0, (forall y3 : a0 -> Prop, (~ (x0 y3)) \/ (~ (y3 y2))) \/ (x2 y2)) /\ (((x0 x1) /\ (x1 y1)) /\ (~ (x2 y1)))) y0).
Definition term285 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : type686 a0) (x3 : a0 -> Prop) := (((@I ((a0 -> Prop) -> Prop) x2 x0) /\ (@I (a0 -> Prop) x0 x1)) /\ (~ (@I (a0 -> Prop) x3 x1))) /\ (forall y0 : a0 -> Prop, forall y1 : a0, ((~ (@I ((a0 -> Prop) -> Prop) x2 y0)) \/ (~ (@I (a0 -> Prop) y0 y1))) \/ (@I (a0 -> Prop) x3 y1)).
Definition term126 (a0 : Type') (x0 : Prop) (x1 : type686 a0) := x0 /\ (exists y0 : a0 -> Prop, x1 y0).
Definition term246 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) (x2 : a0 -> Prop) := fun y0 : a0 => ((forall y1 : a0, (forall y2 : a0 -> Prop, (~ (x1 y2)) \/ (~ (y2 y1))) \/ (x2 y1)) /\ (((x1 x0) /\ (x0 y0)) /\ (~ (x2 y0)))) \/ (exists y1 : a0 -> Prop, (((x1 y1) /\ (y1 y0)) /\ (~ (x2 y0))) /\ (forall y2 : a0 -> Prop, forall y3 : a0, ((~ (x1 y2)) \/ (~ (y2 y3))) \/ (x2 y3))).
Definition term151 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := exists y0 : a0, (forall y1 : a0, (forall y2 : a0 -> Prop, (~ (x0 y2)) \/ (~ (y2 y1))) \/ (x2 y1)) /\ (((x0 x1) /\ (x1 y0)) /\ (~ (x2 y0))).
Definition term334 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term165 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop ((exists y0 : a0 -> Prop, (x0 y0) /\ (y0 x2)) /\ (~ (x1 x2))).
Definition term164 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop ((exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (x0 y1) /\ (y1 x2)) y0) /\ (~ (x1 x2))).
Definition term154 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := or (exists y0 : a0 -> Prop, exists y1 : a0, (forall y2 : a0, (forall y3 : a0 -> Prop, (~ (x0 y3)) \/ (~ (y3 y2))) \/ (x1 y2)) /\ (((x0 y0) /\ (y0 y1)) /\ (~ (x1 y1)))).
Definition term11 (a0 : Type') (x0 : type686 a0) (x1 : a0) (x2 : a0 -> Prop) := (@IN (a0 -> Prop) x2 x0) /\ (@IN a0 x1 x2).
Definition term191 (a0 : Type') (x0 : a0) (x1 : type686 a0) (x2 : a0 -> Prop) := (exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => ((x1 y1) /\ (y1 x0)) /\ (~ (x2 x0))) y0) /\ (forall y0 : a0 -> Prop, forall y1 : a0, ((~ (x1 y0)) \/ (~ (y0 y1))) \/ (x2 y1)).
Definition term166 (a0 : Type') (x0 : type686 a0) (x1 : a0) (x2 : a0 -> Prop) := and ((fun y0 : a0 -> Prop => (x0 y0) /\ (y0 x1)) x2).
Definition term307 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop ((forall y0 : a0 -> Prop, (~ (@I ((a0 -> Prop) -> Prop) x0 y0)) \/ (~ (@I (a0 -> Prop) y0 x2))) \/ (@I (a0 -> Prop) x1 x2)).
Definition term306 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop ((forall y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (~ (@I ((a0 -> Prop) -> Prop) x0 y1)) \/ (~ (@I (a0 -> Prop) y1 x2))) y0) \/ (@I (a0 -> Prop) x1 x2)).
Definition term264 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) (x2 : a0 -> Prop) := fun y0 : a0 => exists y1 : a0 -> Prop, ((forall y2 : a0, (forall y3 : a0 -> Prop, (~ (x1 y3)) \/ (~ (y3 y2))) \/ (x2 y2)) /\ (((x1 x0) /\ (x0 y0)) /\ (~ (x2 y0)))) \/ ((((x1 y1) /\ (y1 y0)) /\ (~ (x2 y0))) /\ (forall y2 : a0 -> Prop, forall y3 : a0, ((~ (x1 y2)) \/ (~ (y2 y3))) \/ (x2 y3))).
Definition term211 (a0 : Type') (x0 : type686 a0) (x1 : Prop) := (exists y0 : a0 -> Prop, x0 y0) \/ x1.
Definition term124 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term322 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (@I (a0 -> Prop) x0 x1)) -> @I (a0 -> Prop) x0 x1.
Definition term142 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (fun y0 : a0 => ((x0 x1) /\ (x1 y0)) /\ (~ (x2 y0))) x3.
Definition term13 (a0 : Type') (x0 : type686 a0) (x1 : a0) := fun y0 : a0 -> Prop => (@IN (a0 -> Prop) y0 x0) /\ (@IN a0 x1 y0).
Definition term299 (a0 : Type') (x0 : type686 a0) (x1 : Prop) := forall y0 : a0 -> Prop, (x0 y0) \/ x1.
Definition term103 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := ~ (forall y0 : a0 -> Prop, forall y1 : a0, ((x0 y0) /\ (y0 y1)) -> x1 y1).
Definition term48 (a0 : Type') := ~ (forall y0 : a0 -> Prop, forall y1 : type686 a0, (forall y2 : a0, (exists y3 : a0 -> Prop, (y1 y3) /\ (y3 y2)) -> y0 y2) = (forall y2 : a0 -> Prop, forall y3 : a0, ((y1 y2) /\ (y2 y3)) -> y0 y3)).
Definition term321 (x0 : Prop) := (~ x0) -> x0.
Definition term345 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ((@I ((a0 -> Prop) -> Prop) x0 x1) /\ (@I (a0 -> Prop) x1 x3)) -> @I (a0 -> Prop) x2 x3.
Definition term89 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := or ((~ (x0 x1)) \/ (~ (x1 x2))).
Definition term107 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := fun y0 : a0 -> Prop => ~ ((fun y1 : a0 -> Prop => forall y2 : a0, ((x0 y1) /\ (y1 y2)) -> x1 y2) y0).
Definition term230 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) (x2 : a0 -> Prop) := (exists y0 : a0, (fun y1 : a0 => (forall y2 : a0, (forall y3 : a0 -> Prop, (~ (x1 y3)) \/ (~ (y3 y2))) \/ (x2 y2)) /\ (((x1 x0) /\ (x0 y1)) /\ (~ (x2 y1)))) y0) \/ (exists y0 : a0, (fun y1 : a0 => exists y2 : a0 -> Prop, (((x1 y2) /\ (y2 y1)) /\ (~ (x2 y1))) /\ (forall y3 : a0 -> Prop, forall y4 : a0, ((~ (x1 y3)) \/ (~ (y3 y4))) \/ (x2 y4))) y0).
Definition term57 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := (~ (x0 x1)) \/ (~ (x1 x2)).
Definition term65 (a0 : Type') (x0 : type686 a0) (x1 : a0) := fun y0 : a0 -> Prop => (~ (x0 y0)) \/ (~ (y0 x1)).
Definition term184 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := and ((fun y0 : a0 => exists y1 : a0 -> Prop, ((x0 y1) /\ (y1 y0)) /\ (~ (x1 y0))) x2).
Definition term337 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term222 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := or (exists y0 : a0, (forall y1 : a0, (forall y2 : a0 -> Prop, (~ (x0 y2)) \/ (~ (y2 y1))) \/ (x2 y1)) /\ (((x0 x1) /\ (x1 y0)) /\ (~ (x2 y0)))).
Definition term223 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) (x2 : a0 -> Prop) := ((fun y0 : a0 -> Prop => exists y1 : a0, (forall y2 : a0, (forall y3 : a0 -> Prop, (~ (x1 y3)) \/ (~ (y3 y2))) \/ (x2 y2)) /\ (((x1 y0) /\ (y0 y1)) /\ (~ (x2 y1)))) x0) \/ (exists y0 : a0, exists y1 : a0 -> Prop, (((x1 y1) /\ (y1 y0)) /\ (~ (x2 y0))) /\ (forall y2 : a0 -> Prop, forall y3 : a0, ((~ (x1 y2)) \/ (~ (y2 y3))) \/ (x2 y3))).
Definition term122 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := ((forall y0 : a0, (exists y1 : a0 -> Prop, (x0 y1) /\ (y1 y0)) -> x1 y0) /\ (~ (forall y0 : a0 -> Prop, forall y1 : a0, ((x0 y0) /\ (y0 y1)) -> x1 y1))) \/ ((~ (forall y0 : a0, (exists y1 : a0 -> Prop, (x0 y1) /\ (y1 y0)) -> x1 y0)) /\ (forall y0 : a0 -> Prop, forall y1 : a0, ((x0 y0) /\ (y0 y1)) -> x1 y1)).
Definition term215 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => exists y1 : a0, (forall y2 : a0, (forall y3 : a0 -> Prop, (~ (x0 y3)) \/ (~ (y3 y2))) \/ (x1 y2)) /\ (((x0 y0) /\ (y0 y1)) /\ (~ (x1 y1)))) x2.
Definition term130 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => exists y1 : a0, ((x0 y0) /\ (y0 y1)) /\ (~ (x1 y1))) x2.
Definition term170 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := fun y0 : a0 -> Prop => ((x0 y0) /\ (y0 x2)) /\ (~ (x1 x2)).
Definition term66 (a0 : Type') (x0 : type686 a0) (x1 : a0) := forall y0 : a0 -> Prop, (~ (x0 y0)) \/ (~ (y0 x1)).
Definition term296 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (forall y0 : a0, x0 y0) \/ x1.
Definition term79 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := (fun y0 : a0 => (exists y1 : a0 -> Prop, (x0 y1) /\ (y1 y0)) -> x1 y0) x2.
Definition term330 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : type686 a0) (x3 : a0 -> Prop) := @eq Prop ((@I (a0 -> Prop) x0 x1) \/ ((~ (@I (a0 -> Prop) x3 x1)) \/ (~ (@I ((a0 -> Prop) -> Prop) x2 x3)))).
Definition term340 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := ~ (~ (@I ((a0 -> Prop) -> Prop) x0 x1)).
Definition term329 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := @eq Prop ((~ (@I ((a0 -> Prop) -> Prop) x0 x1)) \/ ((~ (@I (a0 -> Prop) x1 x3)) \/ (@I (a0 -> Prop) x2 x3))).
Definition term91 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ((~ (x0 x1)) \/ (~ (x1 x3))) \/ (x2 x3).
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term238 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := exists y0 : a0, (fun y1 : a0 => exists y2 : a0 -> Prop, (((x0 y2) /\ (y2 y1)) /\ (~ (x1 y1))) /\ (forall y3 : a0 -> Prop, forall y4 : a0, ((~ (x0 y3)) \/ (~ (y3 y4))) \/ (x1 y4))) y0.
Definition term180 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := exists y0 : a0, (fun y1 : a0 => exists y2 : a0 -> Prop, ((x0 y2) /\ (y2 y1)) /\ (~ (x1 y1))) y0.
Definition term187 (a0 : Type') (x0 : a0) (x1 : type686 a0) (x2 : a0 -> Prop) := (exists y0 : a0 -> Prop, ((x1 y0) /\ (y0 x0)) /\ (~ (x2 x0))) /\ (forall y0 : a0 -> Prop, forall y1 : a0, ((~ (x1 y0)) \/ (~ (y0 y1))) \/ (x2 y1)).
Definition term234 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := exists y0 : a0, (fun y1 : a0 => (forall y2 : a0, (forall y3 : a0 -> Prop, (~ (x0 y3)) \/ (~ (y3 y2))) \/ (x2 y2)) /\ (((x0 x1) /\ (x1 y1)) /\ (~ (x2 y1)))) y0.
Definition term144 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := exists y0 : a0, (fun y1 : a0 => ((x0 x1) /\ (x1 y1)) /\ (~ (x2 y1))) y0.
Definition term250 (a0 : Type') (x0 : Prop) (x1 : type686 a0) := x0 \/ (exists y0 : a0 -> Prop, x1 y0).
Definition term245 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) (x2 : a0 -> Prop) := fun y0 : a0 => ((fun y1 : a0 => (forall y2 : a0, (forall y3 : a0 -> Prop, (~ (x1 y3)) \/ (~ (y3 y2))) \/ (x2 y2)) /\ (((x1 x0) /\ (x0 y1)) /\ (~ (x2 y1)))) y0) \/ ((fun y1 : a0 => exists y2 : a0 -> Prop, (((x1 y2) /\ (y2 y1)) /\ (~ (x2 y1))) /\ (forall y3 : a0 -> Prop, forall y4 : a0, ((~ (x1 y3)) \/ (~ (y3 y4))) \/ (x2 y4))) y0).
Definition term282 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := and ((@I ((a0 -> Prop) -> Prop) x0 x1) /\ (@I (a0 -> Prop) x1 x2)).
Definition term96 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := fun y0 : a0 => ~ ((fun y1 : a0 => ((x0 x1) /\ (x1 y1)) -> x2 y1) y0).
Definition term81 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := fun y0 : a0 => ~ ((fun y1 : a0 => (exists y2 : a0 -> Prop, (x0 y2) /\ (y2 y1)) -> x1 y1) y0).
Definition term117 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := and (forall y0 : a0, (forall y1 : a0 -> Prop, (~ (x0 y1)) \/ (~ (y1 y0))) \/ (x1 y0)).
Definition term116 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := and (forall y0 : a0, (exists y1 : a0 -> Prop, (x0 y1) /\ (y1 y0)) -> x1 y0).
Definition term233 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := fun y0 : a0 => (fun y1 : a0 => (forall y2 : a0, (forall y3 : a0 -> Prop, (~ (x0 y3)) \/ (~ (y3 y2))) \/ (x2 y2)) /\ (((x0 x1) /\ (x1 y1)) /\ (~ (x2 y1)))) y0.
Definition term16 (a0 : Type') (x0 : a0) (x1 : type686 a0) := imp (@IN a0 x0 (@UNIONS a0 x1)).
Definition term83 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := exists y0 : a0, (exists y1 : a0 -> Prop, (x0 y1) /\ (y1 y0)) /\ (~ (x1 y0)).
Definition term143 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := fun y0 : a0 => (fun y1 : a0 => ((x0 x1) /\ (x1 y1)) /\ (~ (x2 y1))) y0.
Definition term303 (a0 : Type') (x0 : type686 a0) (x1 : a0) := fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => (~ (@I ((a0 -> Prop) -> Prop) x0 y1)) \/ (~ (@I (a0 -> Prop) y1 x1))) y0.
Definition term194 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => ((x0 y1) /\ (y1 x2)) /\ (~ (x1 x2))) y0.
Definition term128 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (forall y0 : a0, (forall y1 : a0 -> Prop, (~ (x0 y1)) \/ (~ (y1 y0))) \/ (x1 y0)) /\ (exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => exists y2 : a0, ((x0 y1) /\ (y1 y2)) /\ (~ (x1 y2))) y0).
Definition term328 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : type686 a0) (x3 : a0 -> Prop) := (@I (a0 -> Prop) x0 x1) \/ ((~ (@I (a0 -> Prop) x3 x1)) \/ (~ (@I ((a0 -> Prop) -> Prop) x2 x3))).
Definition term277 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := forall y0 : a0, ((~ (@I ((a0 -> Prop) -> Prop) x0 x1)) \/ (~ (@I (a0 -> Prop) x1 y0))) \/ (@I (a0 -> Prop) x2 y0).
Definition term85 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := forall y0 : a0, (forall y1 : a0 -> Prop, (~ (x0 y1)) \/ (~ (y1 y0))) \/ (x1 y0).
Definition term308 (a0 : Type') (x0 : type686 a0) (x1 : a0) (x2 : a0 -> Prop) := or ((fun y0 : a0 -> Prop => (~ (@I ((a0 -> Prop) -> Prop) x0 y0)) \/ (~ (@I (a0 -> Prop) y0 x1))) x2).
Definition term177 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := exists y0 : a0, ((fun y1 : a0 => exists y2 : a0 -> Prop, ((x0 y2) /\ (y2 y1)) /\ (~ (x1 y1))) y0) /\ (forall y1 : a0 -> Prop, forall y2 : a0, ((~ (x0 y1)) \/ (~ (y1 y2))) \/ (x1 y2)).
Definition term41 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : type686 a0, (forall y1 : a0, (exists y2 : a0 -> Prop, (y0 y2) /\ (y2 y1)) -> x0 y1) = (forall y1 : a0 -> Prop, forall y2 : a0, ((y0 y1) /\ (y1 y2)) -> x0 y2).
Definition term40 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : type686 a0, (forall y1 : a0, (@IN a0 y1 (@UNIONS a0 y0)) -> x0 y1) = (forall y1 : a0 -> Prop, forall y2 : a0, ((@IN (a0 -> Prop) y1 y0) /\ (@IN a0 y2 y1)) -> x0 y2).
Definition term247 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) (x2 : a0 -> Prop) := exists y0 : a0, ((forall y1 : a0, (forall y2 : a0 -> Prop, (~ (x1 y2)) \/ (~ (y2 y1))) \/ (x2 y1)) /\ (((x1 x0) /\ (x0 y0)) /\ (~ (x2 y0)))) \/ (exists y1 : a0 -> Prop, (((x1 y1) /\ (y1 y0)) /\ (~ (x2 y0))) /\ (forall y2 : a0 -> Prop, forall y3 : a0, ((~ (x1 y2)) \/ (~ (y2 y3))) \/ (x2 y3))).
Definition term201 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : type686 a0) (x3 : a0 -> Prop) := ((fun y0 : a0 -> Prop => ((x2 y0) /\ (y0 x0)) /\ (~ (x3 x0))) x1) /\ (forall y0 : a0 -> Prop, forall y1 : a0, ((~ (x2 y0)) \/ (~ (y0 y1))) \/ (x3 y1)).
Definition term266 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := fun y0 : a0 -> Prop => exists y1 : a0, exists y2 : a0 -> Prop, ((forall y3 : a0, (forall y4 : a0 -> Prop, (~ (x0 y4)) \/ (~ (y4 y3))) \/ (x1 y3)) /\ (((x0 y0) /\ (y0 y1)) /\ (~ (x1 y1)))) \/ ((((x0 y2) /\ (y2 y1)) /\ (~ (x1 y1))) /\ (forall y3 : a0 -> Prop, forall y4 : a0, ((~ (x0 y3)) \/ (~ (y3 y4))) \/ (x1 y4))).
Definition term324 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (~ (@I ((a0 -> Prop) -> Prop) x0 x1)) \/ (@I (a0 -> Prop) x2 x3).
Definition term121 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := or ((forall y0 : a0, (forall y1 : a0 -> Prop, (~ (x0 y1)) \/ (~ (y1 y0))) \/ (x1 y0)) /\ (exists y0 : a0 -> Prop, exists y1 : a0, ((x0 y0) /\ (y0 y1)) /\ (~ (x1 y1)))).
Definition term251 (a0 : Type') (x0 : Prop) (x1 : type686 a0) := exists y0 : a0 -> Prop, x0 \/ (x1 y0).
Definition term26 (a0 : Type') (x0 : type686 a0) (x1 : a0) (x2 : a0 -> Prop) := imp ((@IN (a0 -> Prop) x2 x0) /\ (@IN a0 x1 x2)).
Definition term320 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (~ (@I ((a0 -> Prop) -> Prop) x0 x1)) -> @I ((a0 -> Prop) -> Prop) x0 x1.
Definition term326 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := or (~ (@I (a0 -> Prop) x0 x1)).
Definition term10 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := and (x0 x1).
Definition term104 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := exists y0 : a0 -> Prop, ~ ((fun y1 : a0 -> Prop => forall y2 : a0, ((x0 y1) /\ (y1 y2)) -> x1 y2) y0).
Definition term317 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, ((~ (@I ((a0 -> Prop) -> Prop) x0 y0)) \/ (~ (@I (a0 -> Prop) y0 y1))) \/ (@I (a0 -> Prop) x1 y1)) x2.
Definition term105 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, ((x0 y0) /\ (y0 y1)) -> x1 y1) x2.
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term97 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := fun y0 : a0 => ((x0 x1) /\ (x1 y0)) /\ (~ (x2 y0)).
Definition term49 (a0 : Type') := ((~ (forall y0 : a0 -> Prop, forall y1 : type686 a0, (forall y2 : a0, (exists y3 : a0 -> Prop, (y1 y3) /\ (y3 y2)) -> y0 y2) = (forall y2 : a0 -> Prop, forall y3 : a0, ((y1 y2) /\ (y2 y3)) -> y0 y3))) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : type686 a0, (forall y2 : a0, (exists y3 : a0 -> Prop, (y1 y3) /\ (y3 y2)) -> y0 y2) = (forall y2 : a0 -> Prop, forall y3 : a0, ((y1 y2) /\ (y2 y3)) -> y0 y3))) -> False.
Definition term225 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := fun y0 : a0 -> Prop => ((fun y1 : a0 -> Prop => exists y2 : a0, (forall y3 : a0, (forall y4 : a0 -> Prop, (~ (x0 y4)) \/ (~ (y4 y3))) \/ (x1 y3)) /\ (((x0 y1) /\ (y1 y2)) /\ (~ (x1 y2)))) y0) \/ (exists y1 : a0, exists y2 : a0 -> Prop, (((x0 y2) /\ (y2 y1)) /\ (~ (x1 y1))) /\ (forall y3 : a0 -> Prop, forall y4 : a0, ((~ (x0 y3)) \/ (~ (y3 y4))) \/ (x1 y4))).
Definition term271 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := or (~ (x0 x1)).
Definition term167 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := and ((x0 x1) /\ (x1 x2)).
Definition term189 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := fun y0 : a0 => (exists y1 : a0 -> Prop, ((x0 y1) /\ (y1 y0)) /\ (~ (x1 y0))) /\ (forall y1 : a0 -> Prop, forall y2 : a0, ((~ (x0 y1)) \/ (~ (y1 y2))) \/ (x1 y2)).
Definition term22 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 (@UNIONS a0 x0)) -> x1 y0.
Definition term249 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 \/ (x1 y0).
Definition term243 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) (x2 : a0 -> Prop) (x3 : a0) := ((fun y0 : a0 => (forall y1 : a0, (forall y2 : a0 -> Prop, (~ (x1 y2)) \/ (~ (y2 y1))) \/ (x2 y1)) /\ (((x1 x0) /\ (x0 y0)) /\ (~ (x2 y0)))) x3) \/ ((fun y0 : a0 => exists y1 : a0 -> Prop, (((x1 y1) /\ (y1 y0)) /\ (~ (x2 y0))) /\ (forall y2 : a0 -> Prop, forall y3 : a0, ((~ (x1 y2)) \/ (~ (y2 y3))) \/ (x2 y3))) x3).
Definition term99 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := fun y0 : a0 => ((~ (x0 x1)) \/ (~ (x1 y0))) \/ (x2 y0).
Definition term342 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (~ (@I (a0 -> Prop) x0 x1)).
Definition term20 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 (@UNIONS a0 x0)) -> x1 y0.
Definition term175 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (exists y0 : a0, exists y1 : a0 -> Prop, ((x0 y1) /\ (y1 y0)) /\ (~ (x1 y0))) /\ (forall y0 : a0 -> Prop, forall y1 : a0, ((~ (x0 y0)) \/ (~ (y0 y1))) \/ (x1 y1)).
Definition term336 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term61 (a0 : Type') (x0 : type686 a0) (x1 : a0) := forall y0 : a0 -> Prop, ~ ((fun y1 : a0 -> Prop => (x0 y1) /\ (y1 x1)) y0).
Definition term76 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, ~ (x0 y0).
Definition term226 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := fun y0 : a0 -> Prop => (exists y1 : a0, (forall y2 : a0, (forall y3 : a0 -> Prop, (~ (x0 y3)) \/ (~ (y3 y2))) \/ (x1 y2)) /\ (((x0 y0) /\ (y0 y1)) /\ (~ (x1 y1)))) \/ (exists y1 : a0, exists y2 : a0 -> Prop, (((x0 y2) /\ (y2 y1)) /\ (~ (x1 y1))) /\ (forall y3 : a0 -> Prop, forall y4 : a0, ((~ (x0 y3)) \/ (~ (y3 y4))) \/ (x1 y4))).
Definition term304 (a0 : Type') (x0 : type686 a0) (x1 : a0) := forall y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (~ (@I ((a0 -> Prop) -> Prop) x0 y1)) \/ (~ (@I (a0 -> Prop) y1 x1))) y0.
Definition term64 (a0 : Type') (x0 : type686 a0) (x1 : a0) := fun y0 : a0 -> Prop => ~ ((fun y1 : a0 -> Prop => (x0 y1) /\ (y1 x1)) y0).
Definition term248 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 \/ (exists y0 : a0, x1 y0).
Definition term123 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := ((forall y0 : a0, (forall y1 : a0 -> Prop, (~ (x0 y1)) \/ (~ (y1 y0))) \/ (x1 y0)) /\ (exists y0 : a0 -> Prop, exists y1 : a0, ((x0 y0) /\ (y0 y1)) /\ (~ (x1 y1)))) \/ ((exists y0 : a0, (exists y1 : a0 -> Prop, (x0 y1) /\ (y1 y0)) /\ (~ (x1 y0))) /\ (forall y0 : a0 -> Prop, forall y1 : a0, ((~ (x0 y0)) \/ (~ (y0 y1))) \/ (x1 y1))).
Definition term196 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := and (exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => ((x0 y1) /\ (y1 x2)) /\ (~ (x1 x2))) y0).
Definition term163 (a0 : Type') (x0 : type686 a0) (x1 : a0) := and (exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (x0 y1) /\ (y1 x1)) y0).
Definition term156 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term298 (a0 : Type') (x0 : type686 a0) (x1 : Prop) := (forall y0 : a0 -> Prop, x0 y0) \/ x1.
Definition term58 (a0 : Type') (x0 : type686 a0) := ~ (ex x0).
Definition term331 (a0 : Type') (x0 : a0) (x1 : type686 a0) (x2 : a0 -> Prop) := (~ (@I (a0 -> Prop) x2 x0)) \/ (~ (@I ((a0 -> Prop) -> Prop) x1 x2)).
Definition term149 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := fun y0 : a0 => (forall y1 : a0, (forall y2 : a0 -> Prop, (~ (x0 y2)) \/ (~ (y2 y1))) \/ (x2 y1)) /\ ((fun y1 : a0 => ((x0 x1) /\ (x1 y1)) /\ (~ (x2 y1))) y0).
Definition term310 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := fun y0 : a0 -> Prop => ((fun y1 : a0 -> Prop => (~ (@I ((a0 -> Prop) -> Prop) x0 y1)) \/ (~ (@I (a0 -> Prop) y1 x2))) y0) \/ (@I (a0 -> Prop) x1 x2).
Definition term204 (a0 : Type') (x0 : a0) (x1 : type686 a0) (x2 : a0 -> Prop) := fun y0 : a0 -> Prop => (((x1 y0) /\ (y0 x0)) /\ (~ (x2 x0))) /\ (forall y1 : a0 -> Prop, forall y2 : a0, ((~ (x1 y1)) \/ (~ (y1 y2))) \/ (x2 y2)).
Definition term206 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := fun y0 : a0 => exists y1 : a0 -> Prop, (((x0 y1) /\ (y1 y0)) /\ (~ (x1 y0))) /\ (forall y2 : a0 -> Prop, forall y3 : a0, ((~ (x0 y2)) \/ (~ (y2 y3))) \/ (x1 y3)).
Definition term295 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) (x3 : type686 a0) (x4 : a0 -> Prop) := ((forall y0 : a0, (forall y1 : a0 -> Prop, (~ (@I ((a0 -> Prop) -> Prop) x3 y1)) \/ (~ (@I (a0 -> Prop) y1 y0))) \/ (@I (a0 -> Prop) x4 y0)) /\ (((@I ((a0 -> Prop) -> Prop) x3 x0) /\ (@I (a0 -> Prop) x0 x2)) /\ (~ (@I (a0 -> Prop) x4 x2)))) \/ ((((@I ((a0 -> Prop) -> Prop) x3 x1) /\ (@I (a0 -> Prop) x1 x2)) /\ (~ (@I (a0 -> Prop) x4 x2))) /\ (forall y0 : a0 -> Prop, forall y1 : a0, ((~ (@I ((a0 -> Prop) -> Prop) x3 y0)) \/ (~ (@I (a0 -> Prop) y0 y1))) \/ (@I (a0 -> Prop) x4 y1))).
Definition term260 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) (x3 : type686 a0) (x4 : a0 -> Prop) := ((forall y0 : a0, (forall y1 : a0 -> Prop, (~ (x3 y1)) \/ (~ (y1 y0))) \/ (x4 y0)) /\ (((x3 x0) /\ (x0 x2)) /\ (~ (x4 x2)))) \/ ((((x3 x1) /\ (x1 x2)) /\ (~ (x4 x2))) /\ (forall y0 : a0 -> Prop, forall y1 : a0, ((~ (x3 y0)) \/ (~ (y0 y1))) \/ (x4 y1))).
Definition term9 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := and (@IN (a0 -> Prop) x0 x1).
Definition term148 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (forall y0 : a0, (forall y1 : a0 -> Prop, (~ (x0 y1)) \/ (~ (y1 y0))) \/ (x2 y0)) /\ (((x0 x1) /\ (x1 x3)) /\ (~ (x2 x3))).
Definition term113 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := and (exists y0 : a0, (exists y1 : a0 -> Prop, (x0 y1) /\ (y1 y0)) /\ (~ (x1 y0))).
Definition term153 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := exists y0 : a0 -> Prop, exists y1 : a0, (forall y2 : a0, (forall y3 : a0 -> Prop, (~ (x0 y3)) \/ (~ (y3 y2))) \/ (x1 y2)) /\ (((x0 y0) /\ (y0 y1)) /\ (~ (x1 y1))).
Definition term109 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := exists y0 : a0 -> Prop, exists y1 : a0, ((x0 y0) /\ (y0 y1)) /\ (~ (x1 y1)).
Definition term199 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) (x3 : a0 -> Prop) := and ((fun y0 : a0 -> Prop => ((x0 y0) /\ (y0 x2)) /\ (~ (x1 x2))) x3).
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term200 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := and (((x0 x1) /\ (x1 x3)) /\ (~ (x2 x3))).
Definition term190 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := exists y0 : a0, (exists y1 : a0 -> Prop, ((x0 y1) /\ (y1 y0)) /\ (~ (x1 y0))) /\ (forall y1 : a0 -> Prop, forall y2 : a0, ((~ (x0 y1)) \/ (~ (y1 y2))) \/ (x1 y2)).
Definition term171 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := exists y0 : a0 -> Prop, ((x0 y0) /\ (y0 x2)) /\ (~ (x1 x2)).
Definition term332 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := or (@I (a0 -> Prop) x0 x1).
Definition term210 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) \/ x1.
Definition term212 (a0 : Type') (x0 : type686 a0) (x1 : Prop) := exists y0 : a0 -> Prop, (x0 y0) \/ x1.
Definition term12 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := (x0 x1) /\ (x1 x2).
Definition term262 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : type686 a0) (x3 : a0 -> Prop) := fun y0 : a0 -> Prop => ((forall y1 : a0, (forall y2 : a0 -> Prop, (~ (x2 y2)) \/ (~ (y2 y1))) \/ (x3 y1)) /\ (((x2 x0) /\ (x0 x1)) /\ (~ (x3 x1)))) \/ ((((x2 y0) /\ (y0 x1)) /\ (~ (x3 x1))) /\ (forall y1 : a0 -> Prop, forall y2 : a0, ((~ (x2 y1)) \/ (~ (y1 y2))) \/ (x3 y2))).
Definition term129 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := exists y0 : a0 -> Prop, (forall y1 : a0, (forall y2 : a0 -> Prop, (~ (x0 y2)) \/ (~ (y2 y1))) \/ (x1 y1)) /\ ((fun y1 : a0 -> Prop => exists y2 : a0, ((x0 y1) /\ (y1 y2)) /\ (~ (x1 y2))) y0).
Definition term141 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := exists y0 : a0, (forall y1 : a0, (forall y2 : a0 -> Prop, (~ (x0 y2)) \/ (~ (y2 y1))) \/ (x2 y1)) /\ ((fun y1 : a0 => ((x0 x1) /\ (x1 y1)) /\ (~ (x2 y1))) y0).
Definition term52 (a0 : Type') := ~ (~ (forall y0 : a0 -> Prop, forall y1 : type686 a0, (forall y2 : a0, (exists y3 : a0 -> Prop, (y1 y3) /\ (y3 y2)) -> y0 y2) = (forall y2 : a0 -> Prop, forall y3 : a0, ((y1 y2) /\ (y2 y3)) -> y0 y3))).
Definition term274 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := or ((~ (@I ((a0 -> Prop) -> Prop) x0 x1)) \/ (~ (@I (a0 -> Prop) x1 x2))).
Definition term106 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := ~ ((fun y0 : a0 -> Prop => forall y1 : a0, ((x0 y0) /\ (y0 y1)) -> x1 y1) x2).
Definition term288 (a0 : Type') (x0 : type686 a0) (x1 : a0) := or (forall y0 : a0 -> Prop, (~ (@I ((a0 -> Prop) -> Prop) x0 y0)) \/ (~ (@I (a0 -> Prop) y0 x1))).
Definition term72 (a0 : Type') (x0 : type686 a0) (x1 : a0) := or (forall y0 : a0 -> Prop, (~ (x0 y0)) \/ (~ (y0 x1))).
Definition term47 (a0 : Type') := (~ (forall y0 : a0 -> Prop, forall y1 : type686 a0, (forall y2 : a0, (exists y3 : a0 -> Prop, (y1 y3) /\ (y3 y2)) -> y0 y2) = (forall y2 : a0 -> Prop, forall y3 : a0, ((y1 y2) /\ (y2 y3)) -> y0 y3))) -> False.
Definition term137 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := fun y0 : a0 -> Prop => (forall y1 : a0, (forall y2 : a0 -> Prop, (~ (x0 y2)) \/ (~ (y2 y1))) \/ (x1 y1)) /\ ((fun y1 : a0 -> Prop => exists y2 : a0, ((x0 y1) /\ (y1 y2)) /\ (~ (x1 y2))) y0).
Definition term186 (a0 : Type') (x0 : a0) (x1 : type686 a0) (x2 : a0 -> Prop) := ((fun y0 : a0 => exists y1 : a0 -> Prop, ((x1 y1) /\ (y1 y0)) /\ (~ (x2 y0))) x0) /\ (forall y0 : a0 -> Prop, forall y1 : a0, ((~ (x1 y0)) \/ (~ (y0 y1))) \/ (x2 y1)).
Definition term158 (a0 : Type') (x0 : type686 a0) (x1 : Prop) := exists y0 : a0 -> Prop, (x0 y0) /\ x1.
Definition term152 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := fun y0 : a0 -> Prop => exists y1 : a0, (forall y2 : a0, (forall y3 : a0 -> Prop, (~ (x0 y3)) \/ (~ (y3 y2))) \/ (x1 y2)) /\ (((x0 y0) /\ (y0 y1)) /\ (~ (x1 y1))).
Definition term297 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := forall y0 : a0, (x0 y0) \/ x1.
Definition term280 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := and (@I ((a0 -> Prop) -> Prop) x0 x1).
Definition term50 (a0 : Type') := (((~ (forall y0 : a0 -> Prop, forall y1 : type686 a0, (forall y2 : a0, (exists y3 : a0 -> Prop, (y1 y3) /\ (y3 y2)) -> y0 y2) = (forall y2 : a0 -> Prop, forall y3 : a0, ((y1 y2) /\ (y2 y3)) -> y0 y3))) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : type686 a0, (forall y2 : a0, (exists y3 : a0 -> Prop, (y1 y3) /\ (y3 y2)) -> y0 y2) = (forall y2 : a0 -> Prop, forall y3 : a0, ((y1 y2) /\ (y2 y3)) -> y0 y3))) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : type686 a0, (forall y2 : a0, (exists y3 : a0 -> Prop, (y1 y3) /\ (y3 y2)) -> y0 y2) = (forall y2 : a0 -> Prop, forall y3 : a0, ((y1 y2) /\ (y2 y3)) -> y0 y3))) -> False.
Definition term284 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := and (((@I ((a0 -> Prop) -> Prop) x0 x1) /\ (@I (a0 -> Prop) x1 x3)) /\ (~ (@I (a0 -> Prop) x2 x3))).
Definition term1 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term21 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := fun y0 : a0 => (exists y1 : a0 -> Prop, (x0 y1) /\ (y1 y0)) -> x1 y0.
Definition term224 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) (x2 : a0 -> Prop) := (exists y0 : a0, (forall y1 : a0, (forall y2 : a0 -> Prop, (~ (x1 y2)) \/ (~ (y2 y1))) \/ (x2 y1)) /\ (((x1 x0) /\ (x0 y0)) /\ (~ (x2 y0)))) \/ (exists y0 : a0, exists y1 : a0 -> Prop, (((x1 y1) /\ (y1 y0)) /\ (~ (x2 y0))) /\ (forall y2 : a0 -> Prop, forall y3 : a0, ((~ (x1 y2)) \/ (~ (y2 y3))) \/ (x2 y3))).
Definition term82 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := fun y0 : a0 => (exists y1 : a0 -> Prop, (x0 y1) /\ (y1 y0)) /\ (~ (x1 y0)).
Definition term160 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := exists y0 : a0 -> Prop, ((fun y1 : a0 -> Prop => (x0 y1) /\ (y1 x2)) y0) /\ (~ (x1 x2)).
Definition term341 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := and (~ (~ (@I ((a0 -> Prop) -> Prop) x0 x1))).
Definition term268 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (@I (a0 -> Prop) x0 x1).
Definition term150 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := fun y0 : a0 => (forall y1 : a0, (forall y2 : a0 -> Prop, (~ (x0 y2)) \/ (~ (y2 y1))) \/ (x2 y1)) /\ (((x0 x1) /\ (x1 y0)) /\ (~ (x2 y0))).
Definition term29 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ((x0 x1) /\ (x1 x3)) -> x2 x3.
Definition term45 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : type686 a0, (forall y2 : a0, (exists y3 : a0 -> Prop, (y1 y3) /\ (y3 y2)) -> y0 y2) = (forall y2 : a0 -> Prop, forall y3 : a0, ((y1 y2) /\ (y2 y3)) -> y0 y3).
Definition term44 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : type686 a0, (forall y2 : a0, (@IN a0 y2 (@UNIONS a0 y1)) -> y0 y2) = (forall y2 : a0 -> Prop, forall y3 : a0, ((@IN (a0 -> Prop) y2 y1) /\ (@IN a0 y3 y2)) -> y0 y3).
Definition term102 (a0 : Type') (x0 : type686 a0) := exists y0 : a0 -> Prop, ~ (x0 y0).
Definition term236 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := (fun y0 : a0 => exists y1 : a0 -> Prop, (((x0 y1) /\ (y1 y0)) /\ (~ (x1 y0))) /\ (forall y2 : a0 -> Prop, forall y3 : a0, ((~ (x0 y2)) \/ (~ (y2 y3))) \/ (x1 y3))) x2.
Definition term33 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := forall y0 : a0, ((x0 x1) /\ (x1 y0)) -> x2 y0.
Definition term32 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := forall y0 : a0, ((@IN (a0 -> Prop) x1 x0) /\ (@IN a0 y0 x1)) -> x2 y0.
Definition term258 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : type686 a0) (x3 : a0 -> Prop) := @eq Prop (((forall y0 : a0, (forall y1 : a0 -> Prop, (~ (x2 y1)) \/ (~ (y1 y0))) \/ (x3 y0)) /\ (((x2 x0) /\ (x0 x1)) /\ (~ (x3 x1)))) \/ (exists y0 : a0 -> Prop, (((x2 y0) /\ (y0 x1)) /\ (~ (x3 x1))) /\ (forall y1 : a0 -> Prop, forall y2 : a0, ((~ (x2 y1)) \/ (~ (y1 y2))) \/ (x3 y2)))).
Definition term257 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : type686 a0) (x3 : a0 -> Prop) := @eq Prop (((forall y0 : a0, (forall y1 : a0 -> Prop, (~ (x2 y1)) \/ (~ (y1 y0))) \/ (x3 y0)) /\ (((x2 x0) /\ (x0 x1)) /\ (~ (x3 x1)))) \/ (exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (((x2 y1) /\ (y1 x1)) /\ (~ (x3 x1))) /\ (forall y2 : a0 -> Prop, forall y3 : a0, ((~ (x2 y2)) \/ (~ (y2 y3))) \/ (x3 y3))) y0)).
Definition term19 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := (exists y0 : a0 -> Prop, (x0 y0) /\ (y0 x2)) -> x1 x2.
Definition term94 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (fun y0 : a0 => ((x0 x1) /\ (x1 y0)) -> x2 y0) x3.
Definition term292 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := and (forall y0 : a0, (forall y1 : a0 -> Prop, (~ (@I ((a0 -> Prop) -> Prop) x0 y1)) \/ (~ (@I (a0 -> Prop) y1 y0))) \/ (@I (a0 -> Prop) x1 y0)).
Definition term73 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := (~ (exists y0 : a0 -> Prop, (x0 y0) /\ (y0 x2))) \/ (x1 x2).
Definition term286 (a0 : Type') (x0 : type686 a0) (x1 : a0) := fun y0 : a0 -> Prop => (~ (@I ((a0 -> Prop) -> Prop) x0 y0)) \/ (~ (@I (a0 -> Prop) y0 x1)).
Definition term185 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := and (exists y0 : a0 -> Prop, ((x0 y0) /\ (y0 x2)) /\ (~ (x1 x2))).
Definition term157 (a0 : Type') (x0 : type686 a0) (x1 : Prop) := (exists y0 : a0 -> Prop, x0 y0) /\ x1.
Definition term325 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : type686 a0) (x3 : a0 -> Prop) := (@I (a0 -> Prop) x0 x1) \/ (~ (@I ((a0 -> Prop) -> Prop) x2 x3)).
Definition term114 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (~ (forall y0 : a0, (exists y1 : a0 -> Prop, (x0 y1) /\ (y1 y0)) -> x1 y0)) /\ (forall y0 : a0 -> Prop, forall y1 : a0, ((x0 y0) /\ (y0 y1)) -> x1 y1).
Definition term267 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := exists y0 : a0 -> Prop, exists y1 : a0, exists y2 : a0 -> Prop, ((forall y3 : a0, (forall y4 : a0 -> Prop, (~ (x0 y4)) \/ (~ (y4 y3))) \/ (x1 y3)) /\ (((x0 y0) /\ (y0 y1)) /\ (~ (x1 y1)))) \/ ((((x0 y2) /\ (y2 y1)) /\ (~ (x1 y1))) /\ (forall y3 : a0 -> Prop, forall y4 : a0, ((~ (x0 y3)) \/ (~ (y3 y4))) \/ (x1 y4))).
Definition term300 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := (forall y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (~ (@I ((a0 -> Prop) -> Prop) x0 y1)) \/ (~ (@I (a0 -> Prop) y1 x2))) y0) \/ (@I (a0 -> Prop) x1 x2).
Definition term140 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (forall y0 : a0, (forall y1 : a0 -> Prop, (~ (x0 y1)) \/ (~ (y1 y0))) \/ (x2 y0)) /\ (exists y0 : a0, (fun y1 : a0 => ((x0 x1) /\ (x1 y1)) /\ (~ (x2 y1))) y0).
Definition term80 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := ~ ((fun y0 : a0 => (exists y1 : a0 -> Prop, (x0 y1) /\ (y1 y0)) -> x1 y0) x2).
Definition term202 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : type686 a0) (x3 : a0 -> Prop) := (((x2 x0) /\ (x0 x1)) /\ (~ (x3 x1))) /\ (forall y0 : a0 -> Prop, forall y1 : a0, ((~ (x2 y0)) \/ (~ (y0 y1))) \/ (x3 y1)).
Definition term291 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := forall y0 : a0, (forall y1 : a0 -> Prop, (~ (@I ((a0 -> Prop) -> Prop) x0 y1)) \/ (~ (@I (a0 -> Prop) y1 y0))) \/ (@I (a0 -> Prop) x1 y0).
Definition term119 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (forall y0 : a0, (forall y1 : a0 -> Prop, (~ (x0 y1)) \/ (~ (y1 y0))) \/ (x1 y0)) /\ (exists y0 : a0 -> Prop, exists y1 : a0, ((x0 y0) /\ (y0 y1)) /\ (~ (x1 y1))).
Definition term139 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := exists y0 : a0 -> Prop, (forall y1 : a0, (forall y2 : a0 -> Prop, (~ (x0 y2)) \/ (~ (y2 y1))) \/ (x1 y1)) /\ (exists y1 : a0, ((x0 y0) /\ (y0 y1)) /\ (~ (x1 y1))).
Definition term169 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := fun y0 : a0 -> Prop => ((fun y1 : a0 -> Prop => (x0 y1) /\ (y1 x2)) y0) /\ (~ (x1 x2)).
Definition term273 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := (~ (@I ((a0 -> Prop) -> Prop) x0 x1)) \/ (~ (@I (a0 -> Prop) x1 x2)).
Definition term115 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (exists y0 : a0, (exists y1 : a0 -> Prop, (x0 y1) /\ (y1 y0)) /\ (~ (x1 y0))) /\ (forall y0 : a0 -> Prop, forall y1 : a0, ((~ (x0 y0)) \/ (~ (y0 y1))) \/ (x1 y1)).
Definition term93 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := exists y0 : a0, ~ ((fun y1 : a0 => ((x0 x1) /\ (x1 y1)) -> x2 y1) y0).
Definition term78 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := exists y0 : a0, ~ ((fun y1 : a0 => (exists y2 : a0 -> Prop, (x0 y2) /\ (y2 y1)) -> x1 y1) y0).
Definition term232 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (fun y0 : a0 => (forall y1 : a0, (forall y2 : a0 -> Prop, (~ (x0 y2)) \/ (~ (y2 y1))) \/ (x2 y1)) /\ (((x0 x1) /\ (x1 y0)) /\ (~ (x2 y0)))) x3.
Definition term62 (a0 : Type') (x0 : type686 a0) (x1 : a0) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (x0 y0) /\ (y0 x1)) x2.
Definition term302 (a0 : Type') (x0 : type686 a0) (x1 : a0) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ (@I ((a0 -> Prop) -> Prop) x0 y0)) \/ (~ (@I (a0 -> Prop) y0 x1))) x2.
Definition term70 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := ~ ((exists y0 : a0 -> Prop, (x0 y0) /\ (y0 x2)) -> x1 x2).
Definition term217 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => exists y2 : a0, (forall y3 : a0, (forall y4 : a0 -> Prop, (~ (x0 y4)) \/ (~ (y4 y3))) \/ (x1 y3)) /\ (((x0 y1) /\ (y1 y2)) /\ (~ (x1 y2)))) y0.
Definition term132 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => exists y2 : a0, ((x0 y1) /\ (y1 y2)) /\ (~ (x1 y2))) y0.
Definition term346 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (@I (a0 -> Prop) x0 x1) -> False.
Definition term290 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := fun y0 : a0 => (forall y1 : a0 -> Prop, (~ (@I ((a0 -> Prop) -> Prop) x0 y1)) \/ (~ (@I (a0 -> Prop) y1 y0))) \/ (@I (a0 -> Prop) x1 y0).
Definition term315 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := (fun y0 : a0 => forall y1 : a0 -> Prop, ((~ (@I ((a0 -> Prop) -> Prop) x0 y1)) \/ (~ (@I (a0 -> Prop) y1 y0))) \/ (@I (a0 -> Prop) x1 y0)) x2.
Definition term218 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := or (exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => exists y2 : a0, (forall y3 : a0, (forall y4 : a0 -> Prop, (~ (x0 y4)) \/ (~ (y4 y3))) \/ (x1 y3)) /\ (((x0 y1) /\ (y1 y2)) /\ (~ (x1 y2)))) y0).
Definition term127 (a0 : Type') (x0 : Prop) (x1 : type686 a0) := exists y0 : a0 -> Prop, x0 /\ (x1 y0).
Definition term253 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : type686 a0) (x3 : a0 -> Prop) := exists y0 : a0 -> Prop, ((forall y1 : a0, (forall y2 : a0 -> Prop, (~ (x2 y2)) \/ (~ (y2 y1))) \/ (x3 y1)) /\ (((x2 x0) /\ (x0 x1)) /\ (~ (x3 x1)))) \/ ((fun y1 : a0 -> Prop => (((x2 y1) /\ (y1 x1)) /\ (~ (x3 x1))) /\ (forall y2 : a0 -> Prop, forall y3 : a0, ((~ (x2 y2)) \/ (~ (y2 y3))) \/ (x3 y3))) y0).
Definition term305 (a0 : Type') (x0 : type686 a0) (x1 : a0) := or (forall y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (~ (@I ((a0 -> Prop) -> Prop) x0 y1)) \/ (~ (@I (a0 -> Prop) y1 x1))) y0).
Definition term188 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := fun y0 : a0 => ((fun y1 : a0 => exists y2 : a0 -> Prop, ((x0 y2) /\ (y2 y1)) /\ (~ (x1 y1))) y0) /\ (forall y1 : a0 -> Prop, forall y2 : a0, ((~ (x0 y1)) \/ (~ (y1 y2))) \/ (x1 y2)).
Definition term95 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ~ ((fun y0 : a0 => ((x0 x1) /\ (x1 y0)) -> x2 y0) x3).
Definition term120 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := or ((forall y0 : a0, (exists y1 : a0 -> Prop, (x0 y1) /\ (y1 y0)) -> x1 y0) /\ (~ (forall y0 : a0 -> Prop, forall y1 : a0, ((x0 y0) /\ (y0 y1)) -> x1 y1))).
Definition term88 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := or (~ ((x0 x1) /\ (x1 x2))).
Definition term255 (a0 : Type') (x0 : a0) (x1 : type686 a0) (x2 : a0 -> Prop) := fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => (((x1 y1) /\ (y1 x0)) /\ (~ (x2 x0))) /\ (forall y2 : a0 -> Prop, forall y3 : a0, ((~ (x1 y2)) \/ (~ (y2 y3))) \/ (x2 y3))) y0.
Definition term231 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) (x2 : a0 -> Prop) := exists y0 : a0, ((fun y1 : a0 => (forall y2 : a0, (forall y3 : a0 -> Prop, (~ (x1 y3)) \/ (~ (y3 y2))) \/ (x2 y2)) /\ (((x1 x0) /\ (x0 y1)) /\ (~ (x2 y1)))) y0) \/ ((fun y1 : a0 => exists y2 : a0 -> Prop, (((x1 y2) /\ (y2 y1)) /\ (~ (x2 y1))) /\ (forall y3 : a0 -> Prop, forall y4 : a0, ((~ (x1 y3)) \/ (~ (y3 y4))) \/ (x2 y4))) y0).
Definition term263 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : type686 a0) (x3 : a0 -> Prop) := exists y0 : a0 -> Prop, ((forall y1 : a0, (forall y2 : a0 -> Prop, (~ (x2 y2)) \/ (~ (y2 y1))) \/ (x3 y1)) /\ (((x2 x0) /\ (x0 x1)) /\ (~ (x3 x1)))) \/ ((((x2 y0) /\ (y0 x1)) /\ (~ (x3 x1))) /\ (forall y1 : a0 -> Prop, forall y2 : a0, ((~ (x2 y1)) \/ (~ (y1 y2))) \/ (x3 y2))).
Definition term338 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := ~ ((~ (@I ((a0 -> Prop) -> Prop) x0 x1)) \/ (~ (@I (a0 -> Prop) x1 x2))).
Definition term205 (a0 : Type') (x0 : a0) (x1 : type686 a0) (x2 : a0 -> Prop) := exists y0 : a0 -> Prop, (((x1 y0) /\ (y0 x0)) /\ (~ (x2 x0))) /\ (forall y1 : a0 -> Prop, forall y2 : a0, ((~ (x1 y1)) \/ (~ (y1 y2))) \/ (x2 y2)).
Definition term294 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := or ((forall y0 : a0, (forall y1 : a0 -> Prop, (~ (@I ((a0 -> Prop) -> Prop) x0 y1)) \/ (~ (@I (a0 -> Prop) y1 y0))) \/ (@I (a0 -> Prop) x2 y0)) /\ (((@I ((a0 -> Prop) -> Prop) x0 x1) /\ (@I (a0 -> Prop) x1 x3)) /\ (~ (@I (a0 -> Prop) x2 x3)))).
Definition term242 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := or ((forall y0 : a0, (forall y1 : a0 -> Prop, (~ (x0 y1)) \/ (~ (y1 y0))) \/ (x2 y0)) /\ (((x0 x1) /\ (x1 x3)) /\ (~ (x2 x3)))).
Definition term319 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (~ (@I ((a0 -> Prop) -> Prop) x0 x1)) \/ ((~ (@I (a0 -> Prop) x1 x3)) \/ (@I (a0 -> Prop) x2 x3)).
Definition term31 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := fun y0 : a0 => ((x0 x1) /\ (x1 y0)) -> x2 y0.
Definition term283 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ((@I ((a0 -> Prop) -> Prop) x0 x1) /\ (@I (a0 -> Prop) x1 x3)) /\ (~ (@I (a0 -> Prop) x2 x3)).
Definition term254 (a0 : Type') (x0 : a0) (x1 : type686 a0) (x2 : a0 -> Prop) (x3 : a0 -> Prop) := (fun y0 : a0 -> Prop => (((x1 y0) /\ (y0 x0)) /\ (~ (x2 x0))) /\ (forall y1 : a0 -> Prop, forall y2 : a0, ((~ (x1 y1)) \/ (~ (y1 y2))) \/ (x2 y2))) x3.
Definition term87 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ((x0 x1) /\ (x1 x3)) /\ (~ (x2 x3)).
Definition term241 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := or ((fun y0 : a0 => (forall y1 : a0, (forall y2 : a0 -> Prop, (~ (x0 y2)) \/ (~ (y2 y1))) \/ (x2 y1)) /\ (((x0 x1) /\ (x1 y0)) /\ (~ (x2 y0)))) x3).
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term278 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : a0, ((~ (@I ((a0 -> Prop) -> Prop) x0 y0)) \/ (~ (@I (a0 -> Prop) y0 y1))) \/ (@I (a0 -> Prop) x1 y1).
Definition term301 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := forall y0 : a0 -> Prop, ((fun y1 : a0 -> Prop => (~ (@I ((a0 -> Prop) -> Prop) x0 y1)) \/ (~ (@I (a0 -> Prop) y1 x2))) y0) \/ (@I (a0 -> Prop) x1 x2).
Definition term39 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : type686 a0 => (forall y1 : a0, (exists y2 : a0 -> Prop, (y0 y2) /\ (y2 y1)) -> x0 y1) = (forall y1 : a0 -> Prop, forall y2 : a0, ((y0 y1) /\ (y1 y2)) -> x0 y2).
Definition term38 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : type686 a0 => (forall y1 : a0, (@IN a0 y1 (@UNIONS a0 y0)) -> x0 y1) = (forall y1 : a0 -> Prop, forall y2 : a0, ((@IN (a0 -> Prop) y1 y0) /\ (@IN a0 y2 y1)) -> x0 y2).
Definition term318 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (fun y0 : a0 => ((~ (@I ((a0 -> Prop) -> Prop) x0 x1)) \/ (~ (@I (a0 -> Prop) x1 y0))) \/ (@I (a0 -> Prop) x2 y0)) x3.
Definition term112 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := and (~ (forall y0 : a0, (exists y1 : a0 -> Prop, (x0 y1) /\ (y1 y0)) -> x1 y0)).
Definition term333 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) (x2 : a0 -> Prop) (x3 : a0) := (@I (a0 -> Prop) x0 x3) \/ ((~ (@I ((a0 -> Prop) -> Prop) x1 x2)) \/ (~ (@I (a0 -> Prop) x2 x3))).
Definition term287 (a0 : Type') (x0 : type686 a0) (x1 : a0) := forall y0 : a0 -> Prop, (~ (@I ((a0 -> Prop) -> Prop) x0 y0)) \/ (~ (@I (a0 -> Prop) y0 x1)).
Definition term265 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) (x2 : a0 -> Prop) := exists y0 : a0, exists y1 : a0 -> Prop, ((forall y2 : a0, (forall y3 : a0 -> Prop, (~ (x1 y3)) \/ (~ (y3 y2))) \/ (x2 y2)) /\ (((x1 x0) /\ (x0 y0)) /\ (~ (x2 y0)))) \/ ((((x1 y1) /\ (y1 y0)) /\ (~ (x2 y0))) /\ (forall y2 : a0 -> Prop, forall y3 : a0, ((~ (x1 y2)) \/ (~ (y2 y3))) \/ (x2 y3))).
Definition term207 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := exists y0 : a0, exists y1 : a0 -> Prop, (((x0 y1) /\ (y1 y0)) /\ (~ (x1 y0))) /\ (forall y2 : a0 -> Prop, forall y3 : a0, ((~ (x0 y2)) \/ (~ (y2 y3))) \/ (x1 y3)).
Definition term173 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := exists y0 : a0, exists y1 : a0 -> Prop, ((x0 y1) /\ (y1 y0)) /\ (~ (x1 y0)).
Definition term161 (a0 : Type') (x0 : type686 a0) (x1 : a0) := fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => (x0 y1) /\ (y1 x1)) y0.
Definition term259 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : type686 a0) (x3 : a0 -> Prop) (x4 : a0 -> Prop) := ((forall y0 : a0, (forall y1 : a0 -> Prop, (~ (x2 y1)) \/ (~ (y1 y0))) \/ (x3 y0)) /\ (((x2 x0) /\ (x0 x1)) /\ (~ (x3 x1)))) \/ ((fun y0 : a0 -> Prop => (((x2 y0) /\ (y0 x1)) /\ (~ (x3 x1))) /\ (forall y1 : a0 -> Prop, forall y2 : a0, ((~ (x2 y1)) \/ (~ (y1 y2))) \/ (x3 y2))) x4).
Definition term146 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @eq Prop ((forall y0 : a0, (forall y1 : a0 -> Prop, (~ (x0 y1)) \/ (~ (y1 y0))) \/ (x2 y0)) /\ (exists y0 : a0, ((x0 x1) /\ (x1 y0)) /\ (~ (x2 y0)))).
Definition term145 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @eq Prop ((forall y0 : a0, (forall y1 : a0 -> Prop, (~ (x0 y1)) \/ (~ (y1 y0))) \/ (x2 y0)) /\ (exists y0 : a0, (fun y1 : a0 => ((x0 x1) /\ (x1 y1)) /\ (~ (x2 y1))) y0)).
Definition term134 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := @eq Prop ((forall y0 : a0, (forall y1 : a0 -> Prop, (~ (x0 y1)) \/ (~ (y1 y0))) \/ (x1 y0)) /\ (exists y0 : a0 -> Prop, exists y1 : a0, ((x0 y0) /\ (y0 y1)) /\ (~ (x1 y1)))).
Definition term133 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := @eq Prop ((forall y0 : a0, (forall y1 : a0 -> Prop, (~ (x0 y1)) \/ (~ (y1 y0))) \/ (x1 y0)) /\ (exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => exists y2 : a0, ((x0 y1) /\ (y1 y2)) /\ (~ (x1 y2))) y0)).
Definition term311 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := fun y0 : a0 -> Prop => ((~ (@I ((a0 -> Prop) -> Prop) x0 y0)) \/ (~ (@I (a0 -> Prop) y0 x2))) \/ (@I (a0 -> Prop) x1 x2).
Definition term198 (a0 : Type') (x0 : a0) (x1 : type686 a0) (x2 : a0 -> Prop) := @eq Prop ((exists y0 : a0 -> Prop, ((x1 y0) /\ (y0 x0)) /\ (~ (x2 x0))) /\ (forall y0 : a0 -> Prop, forall y1 : a0, ((~ (x1 y0)) \/ (~ (y0 y1))) \/ (x2 y1))).
Definition term197 (a0 : Type') (x0 : a0) (x1 : type686 a0) (x2 : a0 -> Prop) := @eq Prop ((exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => ((x1 y1) /\ (y1 x0)) /\ (~ (x2 x0))) y0) /\ (forall y0 : a0 -> Prop, forall y1 : a0, ((~ (x1 y0)) \/ (~ (y0 y1))) \/ (x2 y1))).
Definition term183 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := @eq Prop ((exists y0 : a0, exists y1 : a0 -> Prop, ((x0 y1) /\ (y1 y0)) /\ (~ (x1 y0))) /\ (forall y0 : a0 -> Prop, forall y1 : a0, ((~ (x0 y0)) \/ (~ (y0 y1))) \/ (x1 y1))).
Definition term182 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := @eq Prop ((exists y0 : a0, (fun y1 : a0 => exists y2 : a0 -> Prop, ((x0 y2) /\ (y2 y1)) /\ (~ (x1 y1))) y0) /\ (forall y0 : a0 -> Prop, forall y1 : a0, ((~ (x0 y0)) \/ (~ (y0 y1))) \/ (x1 y1))).
Definition term51 (a0 : Type') := (((~ (forall y0 : a0 -> Prop, forall y1 : type686 a0, (forall y2 : a0, (exists y3 : a0 -> Prop, (y1 y3) /\ (y3 y2)) -> y0 y2) = (forall y2 : a0 -> Prop, forall y3 : a0, ((y1 y2) /\ (y2 y3)) -> y0 y3))) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : type686 a0, (forall y2 : a0, (exists y3 : a0 -> Prop, (y1 y3) /\ (y3 y2)) -> y0 y2) = (forall y2 : a0 -> Prop, forall y3 : a0, ((y1 y2) /\ (y2 y3)) -> y0 y3))) -> False) -> ((~ (forall y0 : a0 -> Prop, forall y1 : type686 a0, (forall y2 : a0, (exists y3 : a0 -> Prop, (y1 y3) /\ (y3 y2)) -> y0 y2) = (forall y2 : a0 -> Prop, forall y3 : a0, ((y1 y2) /\ (y2 y3)) -> y0 y3))) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : type686 a0, (forall y2 : a0, (exists y3 : a0 -> Prop, (y1 y3) /\ (y3 y2)) -> y0 y2) = (forall y2 : a0 -> Prop, forall y3 : a0, ((y1 y2) /\ (y2 y3)) -> y0 y3))) -> False.
Definition term269 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := ~ (x0 x1).
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term221 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := or ((fun y0 : a0 -> Prop => exists y1 : a0, (forall y2 : a0, (forall y3 : a0 -> Prop, (~ (x0 y3)) \/ (~ (y3 y2))) \/ (x1 y2)) /\ (((x0 y0) /\ (y0 y1)) /\ (~ (x1 y1)))) x2).
Definition term69 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := (exists y0 : a0 -> Prop, (x0 y0) /\ (y0 x2)) /\ (~ (x1 x2)).
Definition term18 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := (@IN a0 x2 (@UNIONS a0 x0)) -> x1 x2.
Definition term71 (a0 : Type') (x0 : type686 a0) (x1 : a0) := or (~ (exists y0 : a0 -> Prop, (x0 y0) /\ (y0 x1))).
Definition term60 (a0 : Type') (x0 : type686 a0) (x1 : a0) := ~ (exists y0 : a0 -> Prop, (x0 y0) /\ (y0 x1)).
Definition term155 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term289 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := (forall y0 : a0 -> Prop, (~ (@I ((a0 -> Prop) -> Prop) x0 y0)) \/ (~ (@I (a0 -> Prop) y0 x2))) \/ (@I (a0 -> Prop) x1 x2).
Definition term14 (a0 : Type') (x0 : type686 a0) (x1 : a0) := fun y0 : a0 -> Prop => (x0 y0) /\ (y0 x1).
Definition term54 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (~ ((forall y0 : a0, (exists y1 : a0 -> Prop, (x0 y1) /\ (y1 y0)) -> x1 y0) = (forall y0 : a0 -> Prop, forall y1 : a0, ((x0 y0) /\ (y0 y1)) -> x1 y1))) -> False.
Definition term27 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := imp ((x0 x1) /\ (x1 x2)).
Definition term252 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : type686 a0) (x3 : a0 -> Prop) := ((forall y0 : a0, (forall y1 : a0 -> Prop, (~ (x2 y1)) \/ (~ (y1 y0))) \/ (x3 y0)) /\ (((x2 x0) /\ (x0 x1)) /\ (~ (x3 x1)))) \/ (exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (((x2 y1) /\ (y1 x1)) /\ (~ (x3 x1))) /\ (forall y2 : a0 -> Prop, forall y3 : a0, ((~ (x2 y2)) \/ (~ (y2 y3))) \/ (x3 y3))) y0).
Definition term181 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := and (exists y0 : a0, (fun y1 : a0 => exists y2 : a0 -> Prop, ((x0 y2) /\ (y2 y1)) /\ (~ (x1 y1))) y0).
Definition term25 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := @eq Prop (forall y0 : a0, (exists y1 : a0 -> Prop, (x0 y1) /\ (y1 y0)) -> x1 y0).
Definition term24 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := @eq Prop (forall y0 : a0, (@IN a0 y0 (@UNIONS a0 x0)) -> x1 y0).
Definition term108 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := fun y0 : a0 -> Prop => exists y1 : a0, ((x0 y0) /\ (y0 y1)) /\ (~ (x1 y1)).
Definition term227 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := exists y0 : a0 -> Prop, (exists y1 : a0, (forall y2 : a0, (forall y3 : a0 -> Prop, (~ (x0 y3)) \/ (~ (y3 y2))) \/ (x1 y2)) /\ (((x0 y0) /\ (y0 y1)) /\ (~ (x1 y1)))) \/ (exists y1 : a0, exists y2 : a0 -> Prop, (((x0 y2) /\ (y2 y1)) /\ (~ (x1 y1))) /\ (forall y3 : a0 -> Prop, forall y4 : a0, ((~ (x0 y3)) \/ (~ (y3 y4))) \/ (x1 y4))).
Definition term84 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := fun y0 : a0 => (forall y1 : a0 -> Prop, (~ (x0 y1)) \/ (~ (y1 y0))) \/ (x1 y0).
Definition term314 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := forall y0 : a0, forall y1 : a0 -> Prop, ((~ (@I ((a0 -> Prop) -> Prop) x0 y1)) \/ (~ (@I (a0 -> Prop) y1 y0))) \/ (@I (a0 -> Prop) x1 y0).
Definition term203 (a0 : Type') (x0 : a0) (x1 : type686 a0) (x2 : a0 -> Prop) := fun y0 : a0 -> Prop => ((fun y1 : a0 -> Prop => ((x1 y1) /\ (y1 x0)) /\ (~ (x2 x0))) y0) /\ (forall y1 : a0 -> Prop, forall y2 : a0, ((~ (x1 y1)) \/ (~ (y1 y2))) \/ (x2 y2)).
Definition term229 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term172 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := fun y0 : a0 => exists y1 : a0 -> Prop, ((x0 y1) /\ (y1 y0)) /\ (~ (x1 y0)).
Definition term327 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : type686 a0) (x3 : a0 -> Prop) := (~ (@I (a0 -> Prop) x3 x1)) \/ ((@I (a0 -> Prop) x0 x1) \/ (~ (@I ((a0 -> Prop) -> Prop) x2 x3))).
Definition term56 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := ~ ((x0 x1) /\ (x1 x2)).
Definition term74 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := (forall y0 : a0 -> Prop, (~ (x0 y0)) \/ (~ (y0 x2))) \/ (x1 x2).
Definition term92 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := ~ (forall y0 : a0, ((x0 x1) /\ (x1 y0)) -> x2 y0).
Definition term77 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := ~ (forall y0 : a0, (exists y1 : a0 -> Prop, (x0 y1) /\ (y1 y0)) -> x1 y0).
Definition term256 (a0 : Type') (x0 : a0) (x1 : type686 a0) (x2 : a0 -> Prop) := exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (((x1 y1) /\ (y1 x0)) /\ (~ (x2 x0))) /\ (forall y2 : a0 -> Prop, forall y3 : a0, ((~ (x1 y2)) \/ (~ (y2 y3))) \/ (x2 y3))) y0.
Definition term195 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => ((x0 y1) /\ (y1 x2)) /\ (~ (x1 x2))) y0.
Definition term162 (a0 : Type') (x0 : type686 a0) (x1 : a0) := exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (x0 y1) /\ (y1 x1)) y0.
Definition term15 (a0 : Type') (x0 : type686 a0) (x1 : a0) := exists y0 : a0 -> Prop, (x0 y0) /\ (y0 x1).
Definition term90 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (~ ((x0 x1) /\ (x1 x3))) \/ (x2 x3).
Definition term168 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ((fun y0 : a0 -> Prop => (x0 y0) /\ (y0 x3)) x1) /\ (~ (x2 x3)).
Definition term270 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := ~ (@I ((a0 -> Prop) -> Prop) x0 x1).
Definition term279 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0, ((~ (@I ((a0 -> Prop) -> Prop) x0 y0)) \/ (~ (@I (a0 -> Prop) y0 y1))) \/ (@I (a0 -> Prop) x1 y1).
Definition term111 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0, ((~ (x0 y0)) \/ (~ (y0 y1))) \/ (x1 y1).
Definition term37 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0, ((x0 y0) /\ (y0 y1)) -> x1 y1.
Definition term36 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0, ((@IN (a0 -> Prop) y0 x0) /\ (@IN a0 y1 y0)) -> x1 y1.
Definition term68 (a0 : Type') (x0 : type686 a0) (x1 : a0) := and (exists y0 : a0 -> Prop, (x0 y0) /\ (y0 x1)).
Definition term213 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => exists y2 : a0, (forall y3 : a0, (forall y4 : a0 -> Prop, (~ (x0 y4)) \/ (~ (y4 y3))) \/ (x1 y3)) /\ (((x0 y1) /\ (y1 y2)) /\ (~ (x1 y2)))) y0) \/ (exists y0 : a0, exists y1 : a0 -> Prop, (((x0 y1) /\ (y1 y0)) /\ (~ (x1 y0))) /\ (forall y2 : a0 -> Prop, forall y3 : a0, ((~ (x0 y2)) \/ (~ (y2 y3))) \/ (x1 y3))).
Definition term138 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := fun y0 : a0 -> Prop => (forall y1 : a0, (forall y2 : a0 -> Prop, (~ (x0 y2)) \/ (~ (y2 y1))) \/ (x1 y1)) /\ (exists y1 : a0, ((x0 y0) /\ (y0 y1)) /\ (~ (x1 y1))).
Definition term110 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : a0, ((~ (x0 y0)) \/ (~ (y0 y1))) \/ (x1 y1).
Definition term35 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : a0, ((x0 y0) /\ (y0 y1)) -> x1 y1.
Definition term34 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : a0, ((@IN (a0 -> Prop) y0 x0) /\ (@IN a0 y1 y0)) -> x1 y1.
Definition term276 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := fun y0 : a0 => ((~ (@I ((a0 -> Prop) -> Prop) x0 x1)) \/ (~ (@I (a0 -> Prop) x1 y0))) \/ (@I (a0 -> Prop) x2 y0).
Definition term240 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) (x2 : a0 -> Prop) := @eq Prop ((exists y0 : a0, (forall y1 : a0, (forall y2 : a0 -> Prop, (~ (x1 y2)) \/ (~ (y2 y1))) \/ (x2 y1)) /\ (((x1 x0) /\ (x0 y0)) /\ (~ (x2 y0)))) \/ (exists y0 : a0, exists y1 : a0 -> Prop, (((x1 y1) /\ (y1 y0)) /\ (~ (x2 y0))) /\ (forall y2 : a0 -> Prop, forall y3 : a0, ((~ (x1 y2)) \/ (~ (y2 y3))) \/ (x2 y3)))).
Definition term239 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) (x2 : a0 -> Prop) := @eq Prop ((exists y0 : a0, (fun y1 : a0 => (forall y2 : a0, (forall y3 : a0 -> Prop, (~ (x1 y3)) \/ (~ (y3 y2))) \/ (x2 y2)) /\ (((x1 x0) /\ (x0 y1)) /\ (~ (x2 y1)))) y0) \/ (exists y0 : a0, (fun y1 : a0 => exists y2 : a0 -> Prop, (((x1 y2) /\ (y2 y1)) /\ (~ (x2 y1))) /\ (forall y3 : a0 -> Prop, forall y4 : a0, ((~ (x1 y3)) \/ (~ (y3 y4))) \/ (x2 y4))) y0)).
Definition term220 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := @eq Prop ((exists y0 : a0 -> Prop, exists y1 : a0, (forall y2 : a0, (forall y3 : a0 -> Prop, (~ (x0 y3)) \/ (~ (y3 y2))) \/ (x1 y2)) /\ (((x0 y0) /\ (y0 y1)) /\ (~ (x1 y1)))) \/ (exists y0 : a0, exists y1 : a0 -> Prop, (((x0 y1) /\ (y1 y0)) /\ (~ (x1 y0))) /\ (forall y2 : a0 -> Prop, forall y3 : a0, ((~ (x0 y2)) \/ (~ (y2 y3))) \/ (x1 y3)))).
Definition term219 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := @eq Prop ((exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => exists y2 : a0, (forall y3 : a0, (forall y4 : a0 -> Prop, (~ (x0 y4)) \/ (~ (y4 y3))) \/ (x1 y3)) /\ (((x0 y1) /\ (y1 y2)) /\ (~ (x1 y2)))) y0) \/ (exists y0 : a0, exists y1 : a0 -> Prop, (((x0 y1) /\ (y1 y0)) /\ (~ (x1 y0))) /\ (forall y2 : a0 -> Prop, forall y3 : a0, ((~ (x0 y2)) \/ (~ (y2 y3))) \/ (x1 y3)))).