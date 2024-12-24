Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term102 (x0 : real -> Prop) (x1 : real -> Prop) := (~ (forall y0 : real, ~ (x0 y0))) /\ (forall y0 : real, (x0 y0) -> real_le (inf x1) y0).
Definition term42 (x0 : real -> Prop) (x1 : real -> Prop) := (~ (forall y0 : real, (@IN real y0 x0) = (@IN real y0 (@EMPTY real)))) /\ (forall y0 : real, (@IN real y0 x0) -> real_le (inf x1) y0).
Definition term82 (x0 : real -> Prop) := forall y0 : real, (@IN real y0 x0) -> real_le (inf x0) y0.
Definition term40 (x0 : real -> Prop) (x1 : real -> Prop) := forall y0 : real, (@IN real y0 x0) -> real_le (inf x1) y0.
Definition term131 (x0 : real -> Prop) (x1 : real -> Prop) := fun y0 : real => (~ (x0 y0)) \/ (x1 y0).
Definition term65 (x0 : real -> Prop) := fun y0 : real => ~ (x0 y0).
Definition term315 (x0 : real -> Prop) := fun y0 : real -> real => (fun y1 : real -> real => (forall y2 : real, (~ (x0 y2)) \/ (real_le (inf x0) y2)) /\ (forall y2 : real, ((x0 (y1 y2)) /\ (~ (real_le y2 (y1 y2)))) \/ (real_le y2 (inf x0)))) y0.
Definition term311 (x0 : real -> Prop) := fun y0 : real -> real => (fun y1 : real -> real => (forall y2 : real, ~ (x0 y2)) \/ (forall y2 : real, (x0 (y1 y2)) /\ (~ (real_le y2 (y1 y2))))) y0.
Definition term341 (x0 : real -> Prop) (x1 : real -> Prop) (x2 : real) := (fun y0 : real => (x0 y0) /\ (~ (real_le (inf x1) y0))) x2.
Definition term213 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => (x0 y0) /\ (~ (real_le x1 y0))) x2.
Definition term143 (x0 : real -> Prop) (x1 : real -> Prop) := (forall y0 : real, (~ (x1 y0)) \/ (x0 y0)) /\ (exists y0 : real, x1 y0).
Definition term55 (x0 : real -> Prop) (x1 : real) (x2 : real -> Prop) := (@IN real x1 x0) -> @IN real x1 x2.
Definition term340 (x0 : real -> Prop) (x1 : real -> Prop) := exists y0 : real, (forall y1 : real, ~ (x0 y1)) \/ ((fun y1 : real => (x0 y1) /\ (~ (real_le (inf x1) y1))) y0).
Definition term134 (x0 : real -> Prop) := ~ (all x0).
Definition term397 := (~ False) -> False.
Definition term316 (x0 : real -> Prop) := exists y0 : real -> real, (fun y1 : real -> real => (forall y2 : real, (~ (x0 y2)) \/ (real_le (inf x0) y2)) /\ (forall y2 : real, ((x0 (y1 y2)) /\ (~ (real_le y2 (y1 y2)))) \/ (real_le y2 (inf x0)))) y0.
Definition term312 (x0 : real -> Prop) := exists y0 : real -> real, (fun y1 : real -> real => (forall y2 : real, ~ (x0 y2)) \/ (forall y2 : real, (x0 (y1 y2)) /\ (~ (real_le y2 (y1 y2))))) y0.
Definition term424 (x0 : real -> Prop) (x1 : real) := (~ (~ (@I (real -> Prop) x0 x1))) -> real_le (inf x0) x1.
Definition term333 (x0 : real -> Prop) (x1 : real -> Prop) := fun y0 : real => (x0 y0) /\ (~ (real_le (inf x1) y0)).
Definition term419 (x0 : real -> real) (x1 : real) := (~ (real_le x1 (x0 x1))) -> real_le x1 (x0 x1).
Definition term323 (x0 : real -> Prop) := fun y0 : real -> real => ((fun y1 : real -> real => (forall y2 : real, ~ (x0 y2)) \/ (forall y2 : real, (x0 (y1 y2)) /\ (~ (real_le y2 (y1 y2))))) y0) \/ ((fun y1 : real -> real => (forall y2 : real, (~ (x0 y2)) \/ (real_le (inf x0) y2)) /\ (forall y2 : real, ((x0 (y1 y2)) /\ (~ (real_le y2 (y1 y2)))) \/ (real_le y2 (inf x0)))) y0).
Definition term342 (x0 : real -> Prop) (x1 : real -> Prop) := fun y0 : real => (fun y1 : real => (x0 y1) /\ (~ (real_le (inf x1) y1))) y0.
Definition term253 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (fun y1 : real => (x0 y1) /\ (~ (real_le x1 y1))) y0.
Definition term351 (x0 : real -> real) (x1 : real) := ~ (real_le x1 (x0 x1)).
Definition term257 (x0 : real) (x1 : real -> Prop) := @eq Prop ((exists y0 : real, (x1 y0) /\ (~ (real_le x0 y0))) \/ (real_le x0 (inf x1))).
Definition term256 (x0 : real) (x1 : real -> Prop) := @eq Prop ((exists y0 : real, (fun y1 : real => (x1 y1) /\ (~ (real_le x0 y1))) y0) \/ (real_le x0 (inf x1))).
Definition term19 (x0 : real -> Prop) (x1 : real -> Prop) := and (@SUBSET real x0 x1).
Definition term112 (x0 : Prop) := ~ (~ x0).
Definition term359 (x0 : real -> real) (x1 : real) (x2 : real -> Prop) := ((@I (real -> Prop) x2 (x0 x1)) /\ (~ (real_le x1 (x0 x1)))) \/ (real_le x1 (inf x2)).
Definition term364 (x0 : real -> Prop) (x1 : real) := or (~ (@I (real -> Prop) x0 x1)).
Definition term375 (x0 : real -> Prop) (x1 : real -> real) := (forall y0 : real, ~ (@I (real -> Prop) x0 y0)) \/ (forall y0 : real, (@I (real -> Prop) x0 (x1 y0)) /\ (~ (real_le y0 (x1 y0)))).
Definition term242 (x0 : real -> Prop) (x1 : real -> real) := (forall y0 : real, ~ (x0 y0)) \/ (forall y0 : real, (x0 (x1 y0)) /\ (~ (real_le y0 (x1 y0)))).
Definition term59 (x0 : real -> Prop) (x1 : real -> Prop) := forall y0 : real, (x0 y0) -> x1 y0.
Definition term300 (x0 : real -> Prop) := fun y0 : real -> real => (forall y1 : real, (~ (x0 y1)) \/ (real_le (inf x0) y1)) /\ ((fun y1 : real -> real => forall y2 : real, ((x0 (y1 y2)) /\ (~ (real_le y2 (y1 y2)))) \/ (real_le y2 (inf x0))) y0).
Definition term148 (x0 : Prop) (x1 : real -> Prop) := x0 /\ (exists y0 : real, x1 y0).
Definition term270 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => fun y1 : real => ((x0 y1) /\ (~ (real_le y0 y1))) \/ (real_le y0 (inf x0))) x1.
Definition term377 (x0 : real -> real) (x1 : real -> Prop) := ((forall y0 : real, ~ (@I (real -> Prop) x1 y0)) \/ (forall y0 : real, (@I (real -> Prop) x1 (x0 y0)) /\ (~ (real_le y0 (x0 y0))))) \/ ((forall y0 : real, (~ (@I (real -> Prop) x1 y0)) \/ (real_le (inf x1) y0)) /\ (forall y0 : real, ((@I (real -> Prop) x1 (x0 y0)) /\ (~ (real_le y0 (x0 y0)))) \/ (real_le y0 (inf x1)))).
Definition term322 (x0 : real -> real) (x1 : real -> Prop) := ((forall y0 : real, ~ (x1 y0)) \/ (forall y0 : real, (x1 (x0 y0)) /\ (~ (real_le y0 (x0 y0))))) \/ ((forall y0 : real, (~ (x1 y0)) \/ (real_le (inf x1) y0)) /\ (forall y0 : real, ((x1 (x0 y0)) /\ (~ (real_le y0 (x0 y0)))) \/ (real_le y0 (inf x1)))).
Definition term203 (x0 : real -> Prop) := ((forall y0 : real, ~ (x0 y0)) \/ (forall y0 : real, exists y1 : real, (x0 y1) /\ (~ (real_le y0 y1)))) \/ ((forall y0 : real, (~ (x0 y0)) \/ (real_le (inf x0) y0)) /\ (forall y0 : real, (exists y1 : real, (x0 y1) /\ (~ (real_le y0 y1))) \/ (real_le y0 (inf x0)))).
Definition term411 (x0 : real) (x1 : real -> Prop) (x2 : real) := @eq Prop ((real_le x0 x2) \/ (~ (@I (real -> Prop) x1 x2))).
Definition term4 (x0 : real) (x1 : real -> Prop) := ((~ (x1 = (@EMPTY real))) /\ (forall y0 : real, (@IN real y0 x1) -> real_le x0 y0)) -> real_le x0 (inf x1).
Definition term386 (x0 : real -> Prop) (x1 : real) := and (forall y0 : real, (~ (@I (real -> Prop) x0 y0)) \/ (real_le x1 y0)).
Definition term381 (x0 : real -> Prop) (x1 : real -> Prop) := and (forall y0 : real, (~ (x0 y0)) \/ (@I (real -> Prop) x1 y0)).
Definition term368 (x0 : real -> Prop) := and (forall y0 : real, (~ (@I (real -> Prop) x0 y0)) \/ (real_le (inf x0) y0)).
Definition term198 (x0 : real -> Prop) := and (forall y0 : real, (~ (x0 y0)) \/ (real_le (inf x0) y0)).
Definition term144 (x0 : real -> Prop) (x1 : real) := and (forall y0 : real, (~ (x0 y0)) \/ (real_le x1 y0)).
Definition term142 (x0 : real -> Prop) (x1 : real -> Prop) := and (forall y0 : real, (~ (x0 y0)) \/ (x1 y0)).
Definition term85 (x0 : real -> Prop) := and (forall y0 : real, (x0 y0) -> real_le (inf x0) y0).
Definition term84 (x0 : real -> Prop) := and (forall y0 : real, (@IN real y0 x0) -> real_le (inf x0) y0).
Definition term60 (x0 : real -> Prop) (x1 : real -> Prop) := and (forall y0 : real, (x0 y0) -> x1 y0).
Definition term54 (x0 : real -> Prop) (x1 : real) := and (forall y0 : real, (x0 y0) -> real_le x1 y0).
Definition term26 (x0 : real -> Prop) (x1 : real) := and (forall y0 : real, (@IN real y0 x0) -> real_le x1 y0).
Definition term20 (x0 : real -> Prop) (x1 : real -> Prop) := and (forall y0 : real, (@IN real y0 x0) -> @IN real y0 x1).
Definition term79 (x0 : real -> Prop) (x1 : real) := (x0 x1) -> real_le (inf x0) x1.
Definition term279 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) := (fun y0 : real => ((x0 y0) /\ (~ (real_le x2 y0))) \/ (real_le x2 (inf x0))) (x1 x2).
Definition term137 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => ~ (x0 y0)) x1.
Definition term187 (x0 : real -> Prop) := (forall y0 : real, ~ (x0 y0)) \/ (forall y0 : real, exists y1 : real, (x0 y1) /\ (~ (real_le y0 y1))).
Definition term394 (x0 : real -> Prop) (x1 : real) := (~ (x0 x1)) -> x0 x1.
Definition term304 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term107 (x0 : real) (x1 : real -> Prop) (x2 : real -> Prop) := ~ (((forall y0 : real, (x2 y0) -> real_le x0 y0) /\ ((forall y0 : real, (x1 y0) -> x2 y0) /\ (~ (forall y0 : real, ~ (x1 y0))))) -> (((~ (forall y0 : real, ~ (x2 y0))) /\ (exists y0 : real, forall y1 : real, (x2 y1) -> real_le y0 y1)) -> (forall y0 : real, (x2 y0) -> real_le (inf x2) y0) /\ (forall y0 : real, (forall y1 : real, (x2 y1) -> real_le y0 y1) -> real_le y0 (inf x2))) -> (~ (forall y0 : real, ~ (x1 y0))) /\ (forall y0 : real, (x1 y0) -> real_le (inf x2) y0)).
Definition term425 (x0 : real -> Prop) (x1 : real) := (@I (real -> Prop) x0 x1) -> real_le (inf x0) x1.
Definition term355 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) := and (@I (real -> Prop) x0 (x1 x2)).
Definition term407 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) := (~ (@I (real -> Prop) x0 (x1 x2))) -> @I (real -> Prop) x0 (x1 x2).
Definition term356 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) := (@I (real -> Prop) x0 (x1 x2)) /\ (~ (real_le x2 (x1 x2))).
Definition term303 (x0 : real -> Prop) := (exists y0 : real -> real, (forall y1 : real, ~ (x0 y1)) \/ (forall y1 : real, (x0 (y0 y1)) /\ (~ (real_le y1 (y0 y1))))) \/ (exists y0 : real -> real, (forall y1 : real, (~ (x0 y1)) \/ (real_le (inf x0) y1)) /\ (forall y1 : real, ((x0 (y0 y1)) /\ (~ (real_le y1 (y0 y1)))) \/ (real_le y1 (inf x0)))).
Definition term74 (x0 : real -> Prop) := exists y0 : real, forall y1 : real, (x0 y1) -> real_le y0 y1.
Definition term12 (x0 : real -> Prop) := exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y0 y1.
Definition term56 (x0 : real -> Prop) (x1 : real -> Prop) (x2 : real) := (x0 x2) -> x1 x2.
Definition term147 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term10 (x0 : real -> Prop) (x1 : real -> Prop) := (@SUBSET real x0 x1) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x1) -> real_le y0 y1).
Definition term105 (x0 : Prop) := (~ x0) -> False.
Definition term247 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) \/ x1.
Definition term328 (x0 : real -> Prop) (x1 : real -> Prop) := ~ (forall y0 : real, (x0 y0) -> real_le (inf x1) y0).
Definition term169 (x0 : real -> Prop) (x1 : real) := ~ (forall y0 : real, (x0 y0) -> real_le x1 y0).
Definition term24 (x0 : real -> Prop) := ~ (forall y0 : real, (@IN real y0 x0) = (@IN real y0 (@EMPTY real))).
Definition term96 (x0 : real -> Prop) := imp (((~ (forall y0 : real, ~ (x0 y0))) /\ (exists y0 : real, forall y1 : real, (x0 y1) -> real_le y0 y1)) -> (forall y0 : real, (x0 y0) -> real_le (inf x0) y0) /\ (forall y0 : real, (forall y1 : real, (x0 y1) -> real_le y0 y1) -> real_le y0 (inf x0))).
Definition term39 (x0 : real -> Prop) := imp (((~ (forall y0 : real, (@IN real y0 x0) = (@IN real y0 (@EMPTY real)))) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y0 y1)) -> (forall y0 : real, (@IN real y0 x0) -> real_le (inf x0) y0) /\ (forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y0 y1) -> real_le y0 (inf x0))).
Definition term38 (x0 : real -> Prop) := imp (((~ (x0 = (@EMPTY real))) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y0 y1)) -> (forall y0 : real, (@IN real y0 x0) -> real_le (inf x0) y0) /\ (forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y0 y1) -> real_le y0 (inf x0))).
Definition term163 (x0 : real) (x1 : real -> Prop) (x2 : real -> Prop) := fun y0 : real => (forall y1 : real, (~ (x1 y1)) \/ (real_le x0 y1)) /\ ((fun y1 : real => (forall y2 : real, (~ (x2 y2)) \/ (x1 y2)) /\ (x2 y1)) y0).
Definition term106 (x0 : real) (x1 : real -> Prop) (x2 : real -> Prop) := (~ (((forall y0 : real, (x2 y0) -> real_le x0 y0) /\ ((forall y0 : real, (x1 y0) -> x2 y0) /\ (~ (forall y0 : real, ~ (x1 y0))))) -> (((~ (forall y0 : real, ~ (x2 y0))) /\ (exists y0 : real, forall y1 : real, (x2 y1) -> real_le y0 y1)) -> (forall y0 : real, (x2 y0) -> real_le (inf x2) y0) /\ (forall y0 : real, (forall y1 : real, (x2 y1) -> real_le y0 y1) -> real_le y0 (inf x2))) -> (~ (forall y0 : real, ~ (x1 y0))) /\ (forall y0 : real, (x1 y0) -> real_le (inf x2) y0))) -> False.
Definition term417 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) := (@I (real -> Prop) x0 (x1 x2)) -> real_le x2 (x1 x2).
Definition term174 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (x0 y0) /\ (~ (real_le x1 y0)).
Definition term293 (x0 : real -> Prop) (x1 : real -> real) := (fun y0 : real -> real => forall y1 : real, ((x0 (y0 y1)) /\ (~ (real_le y1 (y0 y1)))) \/ (real_le y1 (inf x0))) x1.
Definition term236 (x0 : real -> Prop) (x1 : real -> real) := (fun y0 : real -> real => forall y1 : real, (x0 (y0 y1)) /\ (~ (real_le y1 (y0 y1)))) x1.
Definition term325 (x0 : real -> Prop) := exists y0 : real -> real, ((forall y1 : real, ~ (x0 y1)) \/ (forall y1 : real, (x0 (y0 y1)) /\ (~ (real_le y1 (y0 y1))))) \/ ((forall y1 : real, (~ (x0 y1)) \/ (real_le (inf x0) y1)) /\ (forall y1 : real, ((x0 (y0 y1)) /\ (~ (real_le y1 (y0 y1)))) \/ (real_le y1 (inf x0)))).
Definition term111 (x0 : real) (x1 : real -> Prop) (x2 : real -> Prop) := ~ (~ (((forall y0 : real, (x2 y0) -> real_le x0 y0) /\ ((forall y0 : real, (x1 y0) -> x2 y0) /\ (~ (forall y0 : real, ~ (x1 y0))))) -> (((~ (forall y0 : real, ~ (x2 y0))) /\ (exists y0 : real, forall y1 : real, (x2 y1) -> real_le y0 y1)) -> (forall y0 : real, (x2 y0) -> real_le (inf x2) y0) /\ (forall y0 : real, (forall y1 : real, (x2 y1) -> real_le y0 y1) -> real_le y0 (inf x2))) -> (~ (forall y0 : real, ~ (x1 y0))) /\ (forall y0 : real, (x1 y0) -> real_le (inf x2) y0))).
Definition term139 (x0 : real -> Prop) := fun y0 : real => ~ ((fun y1 : real => ~ (x0 y1)) y0).
Definition term194 (x0 : real) (x1 : real -> Prop) := (~ (forall y0 : real, (x1 y0) -> real_le x0 y0)) \/ (real_le x0 (inf x1)).
Definition term432 (x0 : real -> Prop) (x1 : real -> Prop) := ((~ (x1 = (@EMPTY real))) /\ ((@SUBSET real x1 x0) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y0 y1))) -> real_le (inf x0) (inf x1).
Definition term200 (x0 : real -> Prop) := or (~ ((~ (forall y0 : real, ~ (x0 y0))) /\ (exists y0 : real, forall y1 : real, (x0 y1) -> real_le y0 y1))).
Definition term298 (x0 : real -> Prop) (x1 : real -> real) := (forall y0 : real, (~ (x0 y0)) \/ (real_le (inf x0) y0)) /\ ((fun y0 : real -> real => forall y1 : real, ((x0 (y0 y1)) /\ (~ (real_le y1 (y0 y1)))) \/ (real_le y1 (inf x0))) x1).
Definition term289 (x0 : Prop) (x1 : type1028) := x0 /\ (exists y0 : real -> real, x1 y0).
Definition term421 (x0 : real -> Prop) (x1 : real) := (real_le (inf x0) x1) \/ (~ (@I (real -> Prop) x0 x1)).
Definition term294 (x0 : real -> Prop) := fun y0 : real -> real => (fun y1 : real -> real => forall y2 : real, ((x0 (y1 y2)) /\ (~ (real_le y2 (y1 y2)))) \/ (real_le y2 (inf x0))) y0.
Definition term237 (x0 : real -> Prop) := fun y0 : real -> real => (fun y1 : real -> real => forall y2 : real, (x0 (y1 y2)) /\ (~ (real_le y2 (y1 y2)))) y0.
Definition term152 (x0 : real) (x1 : real -> Prop) (x2 : real -> Prop) := (forall y0 : real, (~ (x1 y0)) \/ (real_le x0 y0)) /\ (exists y0 : real, (fun y1 : real => (forall y2 : real, (~ (x2 y2)) \/ (x1 y2)) /\ (x2 y1)) y0).
Definition term324 (x0 : real -> Prop) := fun y0 : real -> real => ((forall y1 : real, ~ (x0 y1)) \/ (forall y1 : real, (x0 (y0 y1)) /\ (~ (real_le y1 (y0 y1))))) \/ ((forall y1 : real, (~ (x0 y1)) \/ (real_le (inf x0) y1)) /\ (forall y1 : real, ((x0 (y0 y1)) /\ (~ (real_le y1 (y0 y1)))) \/ (real_le y1 (inf x0)))).
Definition term416 (x0 : real -> Prop) (x1 : real) (x2 : real) := (@I (real -> Prop) x0 x2) -> real_le x1 x2.
Definition term401 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term61 (x0 : real) (x1 : real -> Prop) := @eq Prop (@IN real x0 x1).
Definition term220 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) := (fun y0 : real => (x0 y0) /\ (~ (real_le x2 y0))) (x1 x2).
Definition term197 (x0 : real -> Prop) := forall y0 : real, (exists y1 : real, (x0 y1) /\ (~ (real_le y0 y1))) \/ (real_le y0 (inf x0)).
Definition term302 (x0 : real -> Prop) := exists y0 : real -> real, (forall y1 : real, (~ (x0 y1)) \/ (real_le (inf x0) y1)) /\ (forall y1 : real, ((x0 (y0 y1)) /\ (~ (real_le y1 (y0 y1)))) \/ (real_le y1 (inf x0))).
Definition term275 (x0 : real -> Prop) := fun y0 : real => exists y1 : real, (fun y2 : real => fun y3 : real => ((x0 y3) /\ (~ (real_le y2 y3))) \/ (real_le y2 (inf x0))) y0 y1.
Definition term216 (x0 : real -> Prop) := fun y0 : real => exists y1 : real, (fun y2 : real => fun y3 : real => (x0 y3) /\ (~ (real_le y2 y3))) y0 y1.
Definition term229 (x0 : real -> Prop) := (forall y0 : real, ~ (x0 y0)) \/ (exists y0 : real -> real, forall y1 : real, (x0 (y0 y1)) /\ (~ (real_le y1 (y0 y1)))).
Definition term91 (x0 : real -> Prop) := fun y0 : real => (forall y1 : real, (x0 y1) -> real_le y0 y1) -> real_le y0 (inf x0).
Definition term90 (x0 : real -> Prop) := fun y0 : real => (forall y1 : real, (@IN real y1 x0) -> real_le y0 y1) -> real_le y0 (inf x0).
Definition term124 := forall y0 : real -> Prop, forall y1 : real -> Prop, forall y2 : real, ((forall y3 : real, (y0 y3) -> real_le y2 y3) /\ ((forall y3 : real, (y1 y3) -> y0 y3) /\ (~ (forall y3 : real, ~ (y1 y3))))) -> (((~ (forall y3 : real, ~ (y0 y3))) /\ (exists y3 : real, forall y4 : real, (y0 y4) -> real_le y3 y4)) -> (forall y3 : real, (y0 y3) -> real_le (inf y0) y3) /\ (forall y3 : real, (forall y4 : real, (y0 y4) -> real_le y3 y4) -> real_le y3 (inf y0))) -> (~ (forall y3 : real, ~ (y1 y3))) /\ (forall y3 : real, (y1 y3) -> real_le (inf y0) y3).
Definition term123 := forall y0 : real -> Prop, forall y1 : real -> Prop, forall y2 : real, (~ (((forall y3 : real, (y0 y3) -> real_le y2 y3) /\ ((forall y3 : real, (y1 y3) -> y0 y3) /\ (~ (forall y3 : real, ~ (y1 y3))))) -> (((~ (forall y3 : real, ~ (y0 y3))) /\ (exists y3 : real, forall y4 : real, (y0 y4) -> real_le y3 y4)) -> (forall y3 : real, (y0 y3) -> real_le (inf y0) y3) /\ (forall y3 : real, (forall y4 : real, (y0 y4) -> real_le y3 y4) -> real_le y3 (inf y0))) -> (~ (forall y3 : real, ~ (y1 y3))) /\ (forall y3 : real, (y1 y3) -> real_le (inf y0) y3))) -> False.
Definition term249 (x0 : real -> Prop) (x1 : Prop) := (exists y0 : real, x0 y0) \/ x1.
Definition term155 (x0 : real -> Prop) (x1 : real -> Prop) (x2 : real) := (fun y0 : real => (forall y1 : real, (~ (x1 y1)) \/ (x0 y1)) /\ (x1 y0)) x2.
Definition term146 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term243 (x0 : real -> Prop) := fun y0 : real -> real => (forall y1 : real, ~ (x0 y1)) \/ ((fun y1 : real -> real => forall y2 : real, (x0 (y1 y2)) /\ (~ (real_le y2 (y1 y2)))) y0).
Definition term426 (x0 : real -> Prop) (x1 : real) := (~ (real_le (inf x0) x1)) -> real_le (inf x0) x1.
Definition term64 (x0 : real -> Prop) := fun y0 : real => (@IN real y0 x0) = (@IN real y0 (@EMPTY real)).
Definition term165 (x0 : real) (x1 : real -> Prop) (x2 : real -> Prop) := exists y0 : real, (forall y1 : real, (~ (x1 y1)) \/ (real_le x0 y1)) /\ ((forall y1 : real, (~ (x2 y1)) \/ (x1 y1)) /\ (x2 y0)).
Definition term21 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term57 (x0 : real -> Prop) (x1 : real -> Prop) := fun y0 : real => (@IN real y0 x0) -> @IN real y0 x1.
Definition term89 (x0 : real) (x1 : real -> Prop) := (forall y0 : real, (x1 y0) -> real_le x0 y0) -> real_le x0 (inf x1).
Definition term88 (x0 : real) (x1 : real -> Prop) := (forall y0 : real, (@IN real y0 x1) -> real_le x0 y0) -> real_le x0 (inf x1).
Definition term7 (x0 : real) (x1 : real -> Prop) := (forall y0 : real, ((~ (x1 = (@EMPTY real))) /\ (forall y1 : real, (@IN real y1 x1) -> real_le y0 y1)) -> real_le y0 (inf x1)) -> real_le x0 (inf x1).
Definition term395 (x0 : Prop) := (~ x0) -> x0.
Definition term264 (x0 : real) (x1 : real -> Prop) := exists y0 : real, ((x1 y0) /\ (~ (real_le x0 y0))) \/ (real_le x0 (inf x1)).
Definition term233 (x0 : Prop) (x1 : type1028) := exists y0 : real -> real, x0 \/ (x1 y0).
Definition term97 (x0 : real -> Prop) (x1 : real -> Prop) (x2 : real) := (@IN real x2 x0) -> real_le (inf x1) x2.
Definition term52 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (x0 y0) -> real_le x1 y0.
Definition term347 (x0 : real -> Prop) (x1 : real -> Prop) (x2 : real) := (forall y0 : real, ~ (x0 y0)) \/ ((x0 x2) /\ (~ (real_le (inf x1) x2))).
Definition term0 (x0 : real -> Prop) := (fun y0 : real -> Prop => ((~ (y0 = (@EMPTY real))) /\ (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y1 y2)) -> (forall y1 : real, (@IN real y1 y0) -> real_le (inf y0) y1) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y1 y2) -> real_le y1 (inf y0))) x0.
Definition term43 (x0 : real -> Prop) (x1 : real -> Prop) := (((~ (x1 = (@EMPTY real))) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x1) -> real_le y0 y1)) -> (forall y0 : real, (@IN real y0 x1) -> real_le (inf x1) y0) /\ (forall y0 : real, (forall y1 : real, (@IN real y1 x1) -> real_le y0 y1) -> real_le y0 (inf x1))) -> (~ (x0 = (@EMPTY real))) /\ (forall y0 : real, (@IN real y0 x0) -> real_le (inf x1) y0).
Definition term138 (x0 : real -> Prop) (x1 : real) := ~ ((fun y0 : real => ~ (x0 y0)) x1).
Definition term34 (x0 : real -> Prop) := imp ((~ (x0 = (@EMPTY real))) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y0 y1)).
Definition term241 (x0 : real -> Prop) (x1 : real -> real) := (forall y0 : real, ~ (x0 y0)) \/ ((fun y0 : real -> real => forall y1 : real, (x0 (y0 y1)) /\ (~ (real_le y1 (y0 y1)))) x1).
Definition term361 (x0 : real -> real) (x1 : real -> Prop) := forall y0 : real, ((@I (real -> Prop) x1 (x0 y0)) /\ (~ (real_le y0 (x0 y0)))) \/ (real_le y0 (inf x1)).
Definition term284 (x0 : real -> real) (x1 : real -> Prop) := forall y0 : real, ((x1 (x0 y0)) /\ (~ (real_le y0 (x0 y0)))) \/ (real_le y0 (inf x1)).
Definition term405 (x0 : real -> Prop) (x1 : real) := (~ (@I (real -> Prop) x0 x1)) -> @I (real -> Prop) x0 x1.
Definition term204 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term288 (x0 : real -> Prop) := (forall y0 : real, (~ (x0 y0)) \/ (real_le (inf x0) y0)) /\ (exists y0 : real -> real, forall y1 : real, ((x0 (y0 y1)) /\ (~ (real_le y1 (y0 y1)))) \/ (real_le y1 (inf x0))).
Definition term2 (x0 : real -> Prop) := forall y0 : real, ((~ (x0 = (@EMPTY real))) /\ (forall y1 : real, (@IN real y1 x0) -> real_le y0 y1)) -> real_le y0 (inf x0).
Definition term126 (x0 : real -> Prop) (x1 : real -> Prop) := ~ ((~ (forall y0 : real, ~ (x0 y0))) /\ (forall y0 : real, (x0 y0) -> real_le (inf x1) y0)).
Definition term188 (x0 : real -> Prop) := ~ ((~ (forall y0 : real, ~ (x0 y0))) /\ (exists y0 : real, forall y1 : real, (x0 y1) -> real_le y0 y1)).
Definition term343 (x0 : real -> Prop) (x1 : real -> Prop) := exists y0 : real, (fun y1 : real => (x0 y1) /\ (~ (real_le (inf x1) y1))) y0.
Definition term254 (x0 : real -> Prop) (x1 : real) := exists y0 : real, (fun y1 : real => (x0 y1) /\ (~ (real_le x1 y1))) y0.
Definition term158 (x0 : real -> Prop) (x1 : real -> Prop) := exists y0 : real, (fun y1 : real => (forall y2 : real, (~ (x1 y2)) \/ (x0 y2)) /\ (x1 y1)) y0.
Definition term192 (x0 : real -> Prop) (x1 : real) := or (~ (forall y0 : real, (x0 y0) -> real_le x1 y0)).
Definition term287 (x0 : real -> Prop) := exists y0 : real -> real, forall y1 : real, ((x0 (y0 y1)) /\ (~ (real_le y1 (y0 y1)))) \/ (real_le y1 (inf x0)).
Definition term268 (x0 : real -> Prop) := exists y0 : real -> real, forall y1 : real, (fun y2 : real => fun y3 : real => ((x0 y3) /\ (~ (real_le y2 y3))) \/ (real_le y2 (inf x0))) y1 (y0 y1).
Definition term228 (x0 : real -> Prop) := exists y0 : real -> real, forall y1 : real, (x0 (y0 y1)) /\ (~ (real_le y1 (y0 y1))).
Definition term209 (x0 : real -> Prop) := exists y0 : real -> real, forall y1 : real, (fun y2 : real => fun y3 : real => (x0 y3) /\ (~ (real_le y2 y3))) y1 (y0 y1).
Definition term207 (x0 : type1626) := exists y0 : real -> real, forall y1 : real, x0 y1 (y0 y1).
Definition term258 (x0 : real -> Prop) (x1 : real) (x2 : real) := or ((fun y0 : real => (x0 y0) /\ (~ (real_le x1 y0))) x2).
Definition term66 (x0 : real -> Prop) := forall y0 : real, ~ (x0 y0).
Definition term14 (x0 : real -> Prop) (x1 : real -> Prop) := ((~ (x1 = (@EMPTY real))) /\ (forall y0 : real, (@IN real y0 x1) -> real_le (inf x0) y0)) -> real_le (inf x0) (inf x1).
Definition term149 (x0 : Prop) (x1 : real -> Prop) := exists y0 : real, x0 /\ (x1 y0).
Definition term255 (x0 : real -> Prop) (x1 : real) := or (exists y0 : real, (fun y1 : real => (x0 y1) /\ (~ (real_le x1 y1))) y0).
Definition term252 (x0 : real) (x1 : real -> Prop) := exists y0 : real, ((fun y1 : real => (x1 y1) /\ (~ (real_le x0 y1))) y0) \/ (real_le x0 (inf x1)).
Definition term319 (x0 : real -> Prop) (x1 : real -> real) := or ((fun y0 : real -> real => (forall y1 : real, ~ (x0 y1)) \/ (forall y1 : real, (x0 (y0 y1)) /\ (~ (real_le y1 (y0 y1))))) x1).
Definition term413 (x0 : real -> Prop) (x1 : real) := ~ (~ (@I (real -> Prop) x0 x1)).
Definition term281 (x0 : real -> Prop) (x1 : real -> real) := fun y0 : real => (fun y1 : real => fun y2 : real => ((x0 y2) /\ (~ (real_le y1 y2))) \/ (real_le y1 (inf x0))) y0 (x1 y0).
Definition term222 (x0 : real -> Prop) (x1 : real -> real) := fun y0 : real => (fun y1 : real => fun y2 : real => (x0 y2) /\ (~ (real_le y1 y2))) y0 (x1 y0).
Definition term290 (x0 : Prop) (x1 : type1028) := exists y0 : real -> real, x0 /\ (x1 y0).
Definition term3 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => ((~ (x0 = (@EMPTY real))) /\ (forall y1 : real, (@IN real y1 x0) -> real_le y0 y1)) -> real_le y0 (inf x0)) x1.
Definition term329 (x0 : real -> Prop) (x1 : real -> Prop) := exists y0 : real, ~ ((fun y1 : real => (x0 y1) -> real_le (inf x1) y1) y0).
Definition term170 (x0 : real -> Prop) (x1 : real) := exists y0 : real, ~ ((fun y1 : real => (x0 y1) -> real_le x1 y1) y0).
Definition term136 (x0 : real -> Prop) := exists y0 : real, ~ ((fun y1 : real => ~ (x0 y1)) y0).
Definition term360 (x0 : real -> real) (x1 : real -> Prop) := fun y0 : real => ((@I (real -> Prop) x1 (x0 y0)) /\ (~ (real_le y0 (x0 y0)))) \/ (real_le y0 (inf x1)).
Definition term282 (x0 : real -> real) (x1 : real -> Prop) := fun y0 : real => ((x1 (x0 y0)) /\ (~ (real_le y0 (x0 y0)))) \/ (real_le y0 (inf x1)).
Definition term433 (x0 : real -> Prop) := forall y0 : real -> Prop, ((~ (y0 = (@EMPTY real))) /\ ((@SUBSET real y0 x0) /\ (exists y1 : real, forall y2 : real, (@IN real y2 x0) -> real_le y1 y2))) -> real_le (inf x0) (inf y0).
Definition term127 (x0 : real -> Prop) (x1 : real) (x2 : real) := (~ (x0 x2)) \/ (real_le x1 x2).
Definition term232 (x0 : Prop) (x1 : type1028) := x0 \/ (exists y0 : real -> real, x1 y0).
Definition term177 (x0 : real -> Prop) := ~ (exists y0 : real, forall y1 : real, (x0 y1) -> real_le y0 y1).
Definition term278 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) := (fun y0 : real => fun y1 : real => ((x0 y1) /\ (~ (real_le y0 y1))) \/ (real_le y0 (inf x0))) x2 (x1 x2).
Definition term219 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) := (fun y0 : real => fun y1 : real => (x0 y1) /\ (~ (real_le y0 y1))) x2 (x1 x2).
Definition term114 (x0 : real -> Prop) (x1 : real -> Prop) := fun y0 : real => ((forall y1 : real, (x1 y1) -> real_le y0 y1) /\ ((forall y1 : real, (x0 y1) -> x1 y1) /\ (~ (forall y1 : real, ~ (x0 y1))))) -> (((~ (forall y1 : real, ~ (x1 y1))) /\ (exists y1 : real, forall y2 : real, (x1 y2) -> real_le y1 y2)) -> (forall y1 : real, (x1 y1) -> real_le (inf x1) y1) /\ (forall y1 : real, (forall y2 : real, (x1 y2) -> real_le y1 y2) -> real_le y1 (inf x1))) -> (~ (forall y1 : real, ~ (x0 y1))) /\ (forall y1 : real, (x0 y1) -> real_le (inf x1) y1).
Definition term23 (x0 : real -> Prop) := forall y0 : real, (@IN real y0 x0) = (@IN real y0 (@EMPTY real)).
Definition term140 (x0 : real -> Prop) := fun y0 : real => x0 y0.
Definition term234 (x0 : real -> Prop) := (forall y0 : real, ~ (x0 y0)) \/ (exists y0 : real -> real, (fun y1 : real -> real => forall y2 : real, (x0 (y1 y2)) /\ (~ (real_le y2 (y1 y2)))) y0).
Definition term75 (x0 : real -> Prop) := (~ (forall y0 : real, ~ (x0 y0))) /\ (exists y0 : real, forall y1 : real, (x0 y1) -> real_le y0 y1).
Definition term33 (x0 : real -> Prop) := (~ (forall y0 : real, (@IN real y0 x0) = (@IN real y0 (@EMPTY real)))) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y0 y1).
Definition term181 (x0 : real -> Prop) := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, (x0 y2) -> real_le y1 y2) y0).
Definition term182 (x0 : real -> Prop) := fun y0 : real => exists y1 : real, (x0 y1) /\ (~ (real_le y0 y1)).
Definition term352 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) := x0 (x1 x2).
Definition term141 (x0 : real -> Prop) := exists y0 : real, x0 y0.
Definition term387 (x0 : real) (x1 : real -> Prop) (x2 : real -> Prop) (x3 : real) := (forall y0 : real, (~ (@I (real -> Prop) x1 y0)) \/ (real_le x0 y0)) /\ ((forall y0 : real, (~ (x2 y0)) \/ (@I (real -> Prop) x1 y0)) /\ (x2 x3)).
Definition term162 (x0 : real) (x1 : real -> Prop) (x2 : real -> Prop) (x3 : real) := (forall y0 : real, (~ (x1 y0)) \/ (real_le x0 y0)) /\ ((forall y0 : real, (~ (x2 y0)) \/ (x1 y0)) /\ (x2 x3)).
Definition term245 (x0 : real -> Prop) := exists y0 : real -> real, (forall y1 : real, ~ (x0 y1)) \/ (forall y1 : real, (x0 (y0 y1)) /\ (~ (real_le y1 (y0 y1)))).
Definition term399 (x0 : real -> Prop) (x1 : real -> Prop) (x2 : real) := @eq Prop ((~ (x0 x2)) \/ (@I (real -> Prop) x1 x2)).
Definition term18 (x0 : real -> Prop) (x1 : real -> Prop) := forall y0 : real, (@IN real y0 x0) -> @IN real y0 x1.
Definition term113 (x0 : real -> Prop) (x1 : real -> Prop) := fun y0 : real => (~ (((forall y1 : real, (x1 y1) -> real_le y0 y1) /\ ((forall y1 : real, (x0 y1) -> x1 y1) /\ (~ (forall y1 : real, ~ (x0 y1))))) -> (((~ (forall y1 : real, ~ (x1 y1))) /\ (exists y1 : real, forall y2 : real, (x1 y2) -> real_le y1 y2)) -> (forall y1 : real, (x1 y1) -> real_le (inf x1) y1) /\ (forall y1 : real, (forall y2 : real, (x1 y2) -> real_le y1 y2) -> real_le y1 (inf x1))) -> (~ (forall y1 : real, ~ (x0 y1))) /\ (forall y1 : real, (x0 y1) -> real_le (inf x1) y1))) -> False.
Definition term101 (x0 : real -> Prop) (x1 : real -> Prop) := forall y0 : real, (x0 y0) -> real_le (inf x1) y0.
Definition term83 (x0 : real -> Prop) := forall y0 : real, (x0 y0) -> real_le (inf x0) y0.
Definition term335 (x0 : real -> Prop) (x1 : real -> Prop) := (~ (~ (forall y0 : real, ~ (x0 y0)))) \/ (~ (forall y0 : real, (x0 y0) -> real_le (inf x1) y0)).
Definition term412 (x0 : real -> Prop) (x1 : real) (x2 : real) := (~ (~ (@I (real -> Prop) x0 x2))) -> real_le x1 x2.
Definition term295 (x0 : real -> Prop) := exists y0 : real -> real, (fun y1 : real -> real => forall y2 : real, ((x0 (y1 y2)) /\ (~ (real_le y2 (y1 y2)))) \/ (real_le y2 (inf x0))) y0.
Definition term238 (x0 : real -> Prop) := exists y0 : real -> real, (fun y1 : real -> real => forall y2 : real, (x0 (y1 y2)) /\ (~ (real_le y2 (y1 y2)))) y0.
Definition term115 (x0 : real -> Prop) (x1 : real -> Prop) := forall y0 : real, (~ (((forall y1 : real, (x1 y1) -> real_le y0 y1) /\ ((forall y1 : real, (x0 y1) -> x1 y1) /\ (~ (forall y1 : real, ~ (x0 y1))))) -> (((~ (forall y1 : real, ~ (x1 y1))) /\ (exists y1 : real, forall y2 : real, (x1 y2) -> real_le y1 y2)) -> (forall y1 : real, (x1 y1) -> real_le (inf x1) y1) /\ (forall y1 : real, (forall y2 : real, (x1 y2) -> real_le y1 y2) -> real_le y1 (inf x1))) -> (~ (forall y1 : real, ~ (x0 y1))) /\ (forall y1 : real, (x0 y1) -> real_le (inf x1) y1))) -> False.
Definition term196 (x0 : real -> Prop) := fun y0 : real => (exists y1 : real, (x0 y1) /\ (~ (real_le y0 y1))) \/ (real_le y0 (inf x0)).
Definition term327 (x0 : real -> Prop) (x1 : real -> Prop) (x2 : real) := (x0 x2) /\ (~ (real_le (inf x1) x2)).
Definition term53 (x0 : real -> Prop) (x1 : real) := forall y0 : real, (x0 y0) -> real_le x1 y0.
Definition term367 (x0 : real -> Prop) := forall y0 : real, (~ (@I (real -> Prop) x0 y0)) \/ (real_le (inf x0) y0).
Definition term191 (x0 : real -> Prop) := forall y0 : real, (~ (x0 y0)) \/ (real_le (inf x0) y0).
Definition term250 (x0 : real -> Prop) (x1 : Prop) := exists y0 : real, (x0 y0) \/ x1.
Definition term353 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) := @I (real -> Prop) x0 (x1 x2).
Definition term422 (x0 : real -> Prop) (x1 : real) := @eq Prop ((~ (@I (real -> Prop) x0 x1)) \/ (real_le (inf x0) x1)).
Definition term108 (x0 : real) (x1 : real -> Prop) (x2 : real -> Prop) := ((~ (((forall y0 : real, (x2 y0) -> real_le x0 y0) /\ ((forall y0 : real, (x1 y0) -> x2 y0) /\ (~ (forall y0 : real, ~ (x1 y0))))) -> (((~ (forall y0 : real, ~ (x2 y0))) /\ (exists y0 : real, forall y1 : real, (x2 y1) -> real_le y0 y1)) -> (forall y0 : real, (x2 y0) -> real_le (inf x2) y0) /\ (forall y0 : real, (forall y1 : real, (x2 y1) -> real_le y0 y1) -> real_le y0 (inf x2))) -> (~ (forall y0 : real, ~ (x1 y0))) /\ (forall y0 : real, (x1 y0) -> real_le (inf x2) y0))) -> False) -> (~ (((forall y0 : real, (x2 y0) -> real_le x0 y0) /\ ((forall y0 : real, (x1 y0) -> x2 y0) /\ (~ (forall y0 : real, ~ (x1 y0))))) -> (((~ (forall y0 : real, ~ (x2 y0))) /\ (exists y0 : real, forall y1 : real, (x2 y1) -> real_le y0 y1)) -> (forall y0 : real, (x2 y0) -> real_le (inf x2) y0) /\ (forall y0 : real, (forall y1 : real, (x2 y1) -> real_le y0 y1) -> real_le y0 (inf x2))) -> (~ (forall y0 : real, ~ (x1 y0))) /\ (forall y0 : real, (x1 y0) -> real_le (inf x2) y0))) -> False.
Definition term363 (x0 : real -> Prop) (x1 : real) := or (~ (x0 x1)).
Definition term277 (x0 : real -> Prop) := @eq Prop (forall y0 : real, exists y1 : real, ((x0 y1) /\ (~ (real_le y0 y1))) \/ (real_le y0 (inf x0))).
Definition term276 (x0 : real -> Prop) := @eq Prop (forall y0 : real, exists y1 : real, (fun y2 : real => fun y3 : real => ((x0 y3) /\ (~ (real_le y2 y3))) \/ (real_le y2 (inf x0))) y0 y1).
Definition term218 (x0 : real -> Prop) := @eq Prop (forall y0 : real, exists y1 : real, (x0 y1) /\ (~ (real_le y0 y1))).
Definition term217 (x0 : real -> Prop) := @eq Prop (forall y0 : real, exists y1 : real, (fun y2 : real => fun y3 : real => (x0 y3) /\ (~ (real_le y2 y3))) y0 y1).
Definition term403 (x0 : real -> Prop) (x1 : real) := imp (~ (~ (x0 x1))).
Definition term150 (x0 : real -> Prop) (x1 : real -> Prop) := exists y0 : real, (forall y1 : real, (~ (x1 y1)) \/ (x0 y1)) /\ (x1 y0).
Definition term390 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => (~ (@I (real -> Prop) x0 y0)) \/ (real_le x1 y0)) x2.
Definition term388 (x0 : real -> Prop) (x1 : real -> Prop) (x2 : real) := (fun y0 : real => (~ (x0 y0)) \/ (@I (real -> Prop) x1 y0)) x2.
Definition term231 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 \/ (x1 y0).
Definition term374 (x0 : real -> Prop) := or (forall y0 : real, ~ (@I (real -> Prop) x0 y0)).
Definition term185 (x0 : real -> Prop) := or (forall y0 : real, ~ (x0 y0)).
Definition term408 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) := ~ (@I (real -> Prop) x0 (x1 x2)).
Definition term345 (x0 : real -> Prop) (x1 : real -> Prop) := @eq Prop ((forall y0 : real, ~ (x0 y0)) \/ (exists y0 : real, (x0 y0) /\ (~ (real_le (inf x1) y0)))).
Definition term344 (x0 : real -> Prop) (x1 : real -> Prop) := @eq Prop ((forall y0 : real, ~ (x0 y0)) \/ (exists y0 : real, (fun y1 : real => (x0 y1) /\ (~ (real_le (inf x1) y1))) y0)).
Definition term240 (x0 : real -> Prop) := @eq Prop ((forall y0 : real, ~ (x0 y0)) \/ (exists y0 : real -> real, forall y1 : real, (x0 (y0 y1)) /\ (~ (real_le y1 (y0 y1))))).
Definition term239 (x0 : real -> Prop) := @eq Prop ((forall y0 : real, ~ (x0 y0)) \/ (exists y0 : real -> real, (fun y1 : real -> real => forall y2 : real, (x0 (y1 y2)) /\ (~ (real_le y2 (y1 y2)))) y0)).
Definition term78 (x0 : real -> Prop) (x1 : real) := (@IN real x1 x0) -> real_le (inf x0) x1.
Definition term369 (x0 : real -> real) (x1 : real -> Prop) := (forall y0 : real, (~ (@I (real -> Prop) x1 y0)) \/ (real_le (inf x1) y0)) /\ (forall y0 : real, ((@I (real -> Prop) x1 (x0 y0)) /\ (~ (real_le y0 (x0 y0)))) \/ (real_le y0 (inf x1))).
Definition term299 (x0 : real -> real) (x1 : real -> Prop) := (forall y0 : real, (~ (x1 y0)) \/ (real_le (inf x1) y0)) /\ (forall y0 : real, ((x1 (x0 y0)) /\ (~ (real_le y0 (x0 y0)))) \/ (real_le y0 (inf x1))).
Definition term199 (x0 : real -> Prop) := (forall y0 : real, (~ (x0 y0)) \/ (real_le (inf x0) y0)) /\ (forall y0 : real, (exists y1 : real, (x0 y1) /\ (~ (real_le y0 y1))) \/ (real_le y0 (inf x0))).
Definition term94 (x0 : real -> Prop) := (forall y0 : real, (x0 y0) -> real_le (inf x0) y0) /\ (forall y0 : real, (forall y1 : real, (x0 y1) -> real_le y0 y1) -> real_le y0 (inf x0)).
Definition term36 (x0 : real -> Prop) := (forall y0 : real, (@IN real y0 x0) -> real_le (inf x0) y0) /\ (forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y0 y1) -> real_le y0 (inf x0)).
Definition term291 (x0 : real -> Prop) := (forall y0 : real, (~ (x0 y0)) \/ (real_le (inf x0) y0)) /\ (exists y0 : real -> real, (fun y1 : real -> real => forall y2 : real, ((x0 (y1 y2)) /\ (~ (real_le y2 (y1 y2)))) \/ (real_le y2 (inf x0))) y0).
Definition term30 (x0 : real -> Prop) := and (~ (x0 = (@EMPTY real))).
Definition term210 (x0 : real -> Prop) := fun y0 : real => fun y1 : real => (x0 y1) /\ (~ (real_le y0 y1)).
Definition term41 (x0 : real -> Prop) (x1 : real -> Prop) := (~ (x0 = (@EMPTY real))) /\ (forall y0 : real, (@IN real y0 x0) -> real_le (inf x1) y0).
Definition term5 (x0 : real -> Prop) (x1 : real) := (~ (x0 = (@EMPTY real))) /\ (forall y0 : real, (@IN real y0 x0) -> real_le x1 y0).
Definition term308 (x0 : real -> Prop) := (exists y0 : real -> real, (fun y1 : real -> real => (forall y2 : real, ~ (x0 y2)) \/ (forall y2 : real, (x0 (y1 y2)) /\ (~ (real_le y2 (y1 y2))))) y0) \/ (exists y0 : real -> real, (fun y1 : real -> real => (forall y2 : real, (~ (x0 y2)) \/ (real_le (inf x0) y2)) /\ (forall y2 : real, ((x0 (y1 y2)) /\ (~ (real_le y2 (y1 y2)))) \/ (real_le y2 (inf x0)))) y0).
Definition term230 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 \/ (exists y0 : a0, x1 y0).
Definition term221 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) := (x0 (x1 x2)) /\ (~ (real_le x2 (x1 x2))).
Definition term271 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => fun y1 : real => ((x0 y1) /\ (~ (real_le y0 y1))) \/ (real_le y0 (inf x0))) x1 x2.
Definition term212 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => fun y1 : real => (x0 y1) /\ (~ (real_le y0 y1))) x1 x2.
Definition term265 (x0 : real -> Prop) := fun y0 : real => exists y1 : real, ((x0 y1) /\ (~ (real_le y0 y1))) \/ (real_le y0 (inf x0)).
Definition term418 (x0 : real -> real) (x1 : real) := real_le x1 (x0 x1).
Definition term184 (x0 : real -> Prop) := or (~ (~ (forall y0 : real, ~ (x0 y0)))).
Definition term176 (x0 : real -> Prop) := ~ (ex x0).
Definition term186 (x0 : real -> Prop) := (~ (~ (forall y0 : real, ~ (x0 y0)))) \/ (~ (exists y0 : real, forall y1 : real, (x0 y1) -> real_le y0 y1)).
Definition term396 (x0 : real -> Prop) (x1 : real) := (x0 x1) -> False.
Definition term280 (x0 : real -> real) (x1 : real) (x2 : real -> Prop) := ((x2 (x0 x1)) /\ (~ (real_le x1 (x0 x1)))) \/ (real_le x1 (inf x2)).
Definition term378 (x0 : real -> Prop) (x1 : real -> Prop) (x2 : real) := (~ (x0 x2)) \/ (@I (real -> Prop) x1 x2).
Definition term267 (x0 : real -> Prop) := forall y0 : real, exists y1 : real, (fun y2 : real => fun y3 : real => ((x0 y3) /\ (~ (real_le y2 y3))) \/ (real_le y2 (inf x0))) y0 y1.
Definition term266 (x0 : real -> Prop) := forall y0 : real, exists y1 : real, ((x0 y1) /\ (~ (real_le y0 y1))) \/ (real_le y0 (inf x0)).
Definition term208 (x0 : real -> Prop) := forall y0 : real, exists y1 : real, (fun y2 : real => fun y3 : real => (x0 y3) /\ (~ (real_le y2 y3))) y0 y1.
Definition term206 (x0 : type1626) := forall y0 : real, exists y1 : real, x0 y0 y1.
Definition term183 (x0 : real -> Prop) := forall y0 : real, exists y1 : real, (x0 y1) /\ (~ (real_le y0 y1)).
Definition term51 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (@IN real y0 x0) -> real_le x1 y0.
Definition term154 (x0 : real -> Prop) (x1 : real -> Prop) := fun y0 : real => (forall y1 : real, (~ (x1 y1)) \/ (x0 y1)) /\ (x1 y0).
Definition term431 (x0 : real -> Prop) (x1 : real -> Prop) := real_le (inf x0) (inf x1).
Definition term306 (x0 : type1028) (x1 : type1028) := (exists y0 : real -> real, x0 y0) \/ (exists y0 : real -> real, x1 y0).
Definition term11 (x0 : real -> Prop) := ~ (x0 = (@EMPTY real)).
Definition term334 (x0 : real -> Prop) (x1 : real -> Prop) := exists y0 : real, (x0 y0) /\ (~ (real_le (inf x1) y0)).
Definition term175 (x0 : real -> Prop) (x1 : real) := exists y0 : real, (x0 y0) /\ (~ (real_le x1 y0)).
Definition term6 (x0 : real) (x1 : real -> Prop) := real_le x0 (inf x1).
Definition term9 (x0 : real -> Prop) (x1 : real -> Prop) := (~ (x0 = (@EMPTY real))) /\ ((@SUBSET real x0 x1) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x1) -> real_le y0 y1)).
Definition term145 (x0 : real) (x1 : real -> Prop) (x2 : real -> Prop) := (forall y0 : real, (~ (x1 y0)) \/ (real_le x0 y0)) /\ ((forall y0 : real, (~ (x2 y0)) \/ (x1 y0)) /\ (exists y0 : real, x2 y0)).
Definition term321 (x0 : real -> Prop) (x1 : real -> real) := ((fun y0 : real -> real => (forall y1 : real, ~ (x0 y1)) \/ (forall y1 : real, (x0 (y0 y1)) /\ (~ (real_le y1 (y0 y1))))) x1) \/ ((fun y0 : real -> real => (forall y1 : real, (~ (x0 y1)) \/ (real_le (inf x0) y1)) /\ (forall y1 : real, ((x0 (y0 y1)) /\ (~ (real_le y1 (y0 y1)))) \/ (real_le y1 (inf x0)))) x1).
Definition term73 (x0 : real -> Prop) := fun y0 : real => forall y1 : real, (x0 y1) -> real_le y0 y1.
Definition term72 (x0 : real -> Prop) := fun y0 : real => forall y1 : real, (@IN real y1 x0) -> real_le y0 y1.
Definition term430 (x0 : real -> Prop) (x1 : real -> Prop) (x2 : real) := (fun y0 : real => (~ (((forall y1 : real, (x1 y1) -> real_le y0 y1) /\ ((forall y1 : real, (x0 y1) -> x1 y1) /\ (~ (forall y1 : real, ~ (x0 y1))))) -> (((~ (forall y1 : real, ~ (x1 y1))) /\ (exists y1 : real, forall y2 : real, (x1 y2) -> real_le y1 y2)) -> (forall y1 : real, (x1 y1) -> real_le (inf x1) y1) /\ (forall y1 : real, (forall y2 : real, (x1 y2) -> real_le y1 y2) -> real_le y1 (inf x1))) -> (~ (forall y1 : real, ~ (x0 y1))) /\ (forall y1 : real, (x0 y1) -> real_le (inf x1) y1))) -> False) x2.
Definition term251 (x0 : real) (x1 : real -> Prop) := (exists y0 : real, (fun y1 : real => (x1 y1) /\ (~ (real_le x0 y1))) y0) \/ (real_le x0 (inf x1)).
Definition term135 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term404 (x0 : real -> Prop) (x1 : real -> Prop) (x2 : real) := (x0 x2) -> @I (real -> Prop) x1 x2.
Definition term331 (x0 : real -> Prop) (x1 : real -> Prop) (x2 : real) := ~ ((fun y0 : real => (x0 y0) -> real_le (inf x1) y0) x2).
Definition term172 (x0 : real -> Prop) (x1 : real) (x2 : real) := ~ ((fun y0 : real => (x0 y0) -> real_le x1 y0) x2).
Definition term427 (x0 : real -> Prop) (x1 : real) := (real_le (inf x0) x1) -> False.
Definition term248 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) \/ x1.
Definition term47 (x0 : real) (x1 : real -> Prop) := imp (@IN real x0 x1).
Definition term337 (x0 : Prop) (x1 : real -> Prop) := x0 \/ (exists y0 : real, x1 y0).
Definition term67 (x0 : real -> Prop) := ~ (forall y0 : real, ~ (x0 y0)).
Definition term70 (x0 : real) (x1 : real -> Prop) (x2 : real -> Prop) := imp ((forall y0 : real, (x1 y0) -> real_le x0 y0) /\ ((forall y0 : real, (x2 y0) -> x1 y0) /\ (~ (forall y0 : real, ~ (x2 y0))))).
Definition term29 (x0 : real) (x1 : real -> Prop) (x2 : real -> Prop) := imp ((forall y0 : real, (@IN real y0 x1) -> real_le x0 y0) /\ ((forall y0 : real, (@IN real y0 x2) -> @IN real y0 x1) /\ (~ (forall y0 : real, (@IN real y0 x2) = (@IN real y0 (@EMPTY real)))))).
Definition term202 (x0 : real -> Prop) := (~ ((~ (forall y0 : real, ~ (x0 y0))) /\ (exists y0 : real, forall y1 : real, (x0 y1) -> real_le y0 y1))) \/ ((forall y0 : real, (x0 y0) -> real_le (inf x0) y0) /\ (forall y0 : real, (forall y1 : real, (x0 y1) -> real_le y0 y1) -> real_le y0 (inf x0))).
Definition term272 (x0 : real) (x1 : real -> Prop) (x2 : real) := (fun y0 : real => ((x1 y0) /\ (~ (real_le x0 y0))) \/ (real_le x0 (inf x1))) x2.
Definition term13 (x0 : real -> Prop) (x1 : real) := forall y0 : real, (@IN real y0 x0) -> real_le x1 y0.
Definition term166 (x0 : real -> Prop) := ~ (~ (forall y0 : real, ~ (x0 y0))).
Definition term365 (x0 : real -> Prop) (x1 : real) := (~ (@I (real -> Prop) x0 x1)) \/ (real_le (inf x0) x1).
Definition term16 (x0 : real) (x1 : real -> Prop) (x2 : real -> Prop) := (forall y0 : real, (@IN real y0 x1) -> real_le x0 y0) /\ ((@SUBSET real x2 x1) /\ (~ (x2 = (@EMPTY real)))).
Definition term171 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => (x0 y0) -> real_le x1 y0) x2.
Definition term406 (x0 : real -> Prop) (x1 : real) := (@I (real -> Prop) x0 x1) -> False.
Definition term153 (x0 : real) (x1 : real -> Prop) (x2 : real -> Prop) := exists y0 : real, (forall y1 : real, (~ (x1 y1)) \/ (real_le x0 y1)) /\ ((fun y1 : real => (forall y2 : real, (~ (x2 y2)) \/ (x1 y2)) /\ (x2 y1)) y0).
Definition term330 (x0 : real -> Prop) (x1 : real -> Prop) (x2 : real) := (fun y0 : real => (x0 y0) -> real_le (inf x1) y0) x2.
Definition term263 (x0 : real) (x1 : real -> Prop) := fun y0 : real => ((x1 y0) /\ (~ (real_le x0 y0))) \/ (real_le x0 (inf x1)).
Definition term8 (x0 : real -> Prop) := (forall y0 : real, ((~ (x0 = (@EMPTY real))) /\ (forall y1 : real, (@IN real y1 x0) -> real_le y0 y1)) -> real_le y0 (inf x0)) -> forall y0 : real, ((~ (x0 = (@EMPTY real))) /\ (forall y1 : real, (@IN real y1 x0) -> real_le y0 y1)) -> real_le y0 (inf x0).
Definition term151 (x0 : real) (x1 : real -> Prop) (x2 : real -> Prop) := (forall y0 : real, (~ (x1 y0)) \/ (real_le x0 y0)) /\ (exists y0 : real, (forall y1 : real, (~ (x2 y1)) \/ (x1 y1)) /\ (x2 y0)).
Definition term307 (x0 : type1028) (x1 : type1028) := exists y0 : real -> real, (x0 y0) \/ (x1 y0).
Definition term133 (x0 : real -> Prop) (x1 : real) := ~ (~ (x0 x1)).
Definition term195 (x0 : real) (x1 : real -> Prop) := (exists y0 : real, (x1 y0) /\ (~ (real_le x0 y0))) \/ (real_le x0 (inf x1)).
Definition term168 (x0 : real -> Prop) (x1 : real) (x2 : real) := (x0 x2) /\ (~ (real_le x1 x2)).
Definition term349 (x0 : real -> Prop) (x1 : real -> Prop) := fun y0 : real => (forall y1 : real, ~ (x0 y1)) \/ ((x0 y0) /\ (~ (real_le (inf x1) y0))).
Definition term190 (x0 : real -> Prop) := fun y0 : real => (~ (x0 y0)) \/ (real_le (inf x0) y0).
Definition term366 (x0 : real -> Prop) := fun y0 : real => (~ (@I (real -> Prop) x0 y0)) \/ (real_le (inf x0) y0).
Definition term69 (x0 : real) (x1 : real -> Prop) (x2 : real -> Prop) := (forall y0 : real, (x1 y0) -> real_le x0 y0) /\ ((forall y0 : real, (x2 y0) -> x1 y0) /\ (~ (forall y0 : real, ~ (x2 y0)))).
Definition term27 (x0 : real) (x1 : real -> Prop) (x2 : real -> Prop) := (forall y0 : real, (@IN real y0 x1) -> real_le x0 y0) /\ ((forall y0 : real, (@IN real y0 x2) -> @IN real y0 x1) /\ (~ (forall y0 : real, (@IN real y0 x2) = (@IN real y0 (@EMPTY real))))).
Definition term109 (x0 : real) (x1 : real -> Prop) (x2 : real -> Prop) := (((~ (((forall y0 : real, (x2 y0) -> real_le x0 y0) /\ ((forall y0 : real, (x1 y0) -> x2 y0) /\ (~ (forall y0 : real, ~ (x1 y0))))) -> (((~ (forall y0 : real, ~ (x2 y0))) /\ (exists y0 : real, forall y1 : real, (x2 y1) -> real_le y0 y1)) -> (forall y0 : real, (x2 y0) -> real_le (inf x2) y0) /\ (forall y0 : real, (forall y1 : real, (x2 y1) -> real_le y0 y1) -> real_le y0 (inf x2))) -> (~ (forall y0 : real, ~ (x1 y0))) /\ (forall y0 : real, (x1 y0) -> real_le (inf x2) y0))) -> False) -> (~ (((forall y0 : real, (x2 y0) -> real_le x0 y0) /\ ((forall y0 : real, (x1 y0) -> x2 y0) /\ (~ (forall y0 : real, ~ (x1 y0))))) -> (((~ (forall y0 : real, ~ (x2 y0))) /\ (exists y0 : real, forall y1 : real, (x2 y1) -> real_le y0 y1)) -> (forall y0 : real, (x2 y0) -> real_le (inf x2) y0) /\ (forall y0 : real, (forall y1 : real, (x2 y1) -> real_le y0 y1) -> real_le y0 (inf x2))) -> (~ (forall y0 : real, ~ (x1 y0))) /\ (forall y0 : real, (x1 y0) -> real_le (inf x2) y0))) -> False) -> (~ (((forall y0 : real, (x2 y0) -> real_le x0 y0) /\ ((forall y0 : real, (x1 y0) -> x2 y0) /\ (~ (forall y0 : real, ~ (x1 y0))))) -> (((~ (forall y0 : real, ~ (x2 y0))) /\ (exists y0 : real, forall y1 : real, (x2 y1) -> real_le y0 y1)) -> (forall y0 : real, (x2 y0) -> real_le (inf x2) y0) /\ (forall y0 : real, (forall y1 : real, (x2 y1) -> real_le y0 y1) -> real_le y0 (inf x2))) -> (~ (forall y0 : real, ~ (x1 y0))) /\ (forall y0 : real, (x1 y0) -> real_le (inf x2) y0))) -> False.
Definition term189 (x0 : real -> Prop) (x1 : real) := (~ (x0 x1)) \/ (real_le (inf x0) x1).
Definition term62 (x0 : real -> Prop) (x1 : real) := @eq Prop (x0 x1).
Definition term179 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => forall y1 : real, (x0 y1) -> real_le y0 y1) x1.
Definition term292 (x0 : real -> Prop) := exists y0 : real -> real, (forall y1 : real, (~ (x0 y1)) \/ (real_le (inf x0) y1)) /\ ((fun y1 : real -> real => forall y2 : real, ((x0 (y1 y2)) /\ (~ (real_le y2 (y1 y2)))) \/ (real_le y2 (inf x0))) y0).
Definition term273 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (fun y1 : real => fun y2 : real => ((x0 y2) /\ (~ (real_le y1 y2))) \/ (real_le y1 (inf x0))) x1 y0.
Definition term214 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (fun y1 : real => fun y2 : real => (x0 y2) /\ (~ (real_le y1 y2))) x1 y0.
Definition term98 (x0 : real -> Prop) (x1 : real -> Prop) (x2 : real) := (x0 x2) -> real_le (inf x1) x2.
Definition term104 (x0 : real) (x1 : real -> Prop) (x2 : real -> Prop) := ((forall y0 : real, (x2 y0) -> real_le x0 y0) /\ ((forall y0 : real, (x1 y0) -> x2 y0) /\ (~ (forall y0 : real, ~ (x1 y0))))) -> (((~ (forall y0 : real, ~ (x2 y0))) /\ (exists y0 : real, forall y1 : real, (x2 y1) -> real_le y0 y1)) -> (forall y0 : real, (x2 y0) -> real_le (inf x2) y0) /\ (forall y0 : real, (forall y1 : real, (x2 y1) -> real_le y0 y1) -> real_le y0 (inf x2))) -> (~ (forall y0 : real, ~ (x1 y0))) /\ (forall y0 : real, (x1 y0) -> real_le (inf x2) y0).
Definition term46 (x0 : real) (x1 : real -> Prop) (x2 : real -> Prop) := ((forall y0 : real, (@IN real y0 x2) -> real_le x0 y0) /\ ((forall y0 : real, (@IN real y0 x1) -> @IN real y0 x2) /\ (~ (forall y0 : real, (@IN real y0 x1) = (@IN real y0 (@EMPTY real)))))) -> (((~ (forall y0 : real, (@IN real y0 x2) = (@IN real y0 (@EMPTY real)))) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x2) -> real_le y0 y1)) -> (forall y0 : real, (@IN real y0 x2) -> real_le (inf x2) y0) /\ (forall y0 : real, (forall y1 : real, (@IN real y1 x2) -> real_le y0 y1) -> real_le y0 (inf x2))) -> (~ (forall y0 : real, (@IN real y0 x1) = (@IN real y0 (@EMPTY real)))) /\ (forall y0 : real, (@IN real y0 x1) -> real_le (inf x2) y0).
Definition term45 (x0 : real) (x1 : real -> Prop) (x2 : real -> Prop) := ((forall y0 : real, (@IN real y0 x2) -> real_le x0 y0) /\ ((@SUBSET real x1 x2) /\ (~ (x1 = (@EMPTY real))))) -> (((~ (x2 = (@EMPTY real))) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x2) -> real_le y0 y1)) -> (forall y0 : real, (@IN real y0 x2) -> real_le (inf x2) y0) /\ (forall y0 : real, (forall y1 : real, (@IN real y1 x2) -> real_le y0 y1) -> real_le y0 (inf x2))) -> (~ (x1 = (@EMPTY real))) /\ (forall y0 : real, (@IN real y0 x1) -> real_le (inf x2) y0).
Definition term384 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (~ (@I (real -> Prop) x0 y0)) \/ (real_le x1 y0).
Definition term164 (x0 : real) (x1 : real -> Prop) (x2 : real -> Prop) := fun y0 : real => (forall y1 : real, (~ (x1 y1)) \/ (real_le x0 y1)) /\ ((forall y1 : real, (~ (x2 y1)) \/ (x1 y1)) /\ (x2 y0)).
Definition term283 (x0 : real -> Prop) (x1 : real -> real) := forall y0 : real, (fun y1 : real => fun y2 : real => ((x0 y2) /\ (~ (real_le y1 y2))) \/ (real_le y1 (inf x0))) y0 (x1 y0).
Definition term224 (x0 : real -> Prop) (x1 : real -> real) := forall y0 : real, (fun y1 : real => fun y2 : real => (x0 y2) /\ (~ (real_le y1 y2))) y0 (x1 y0).
Definition term398 (x0 : real -> Prop) (x1 : real -> Prop) (x2 : real) := (@I (real -> Prop) x0 x2) \/ (~ (x1 x2)).
Definition term409 (x0 : real) (x1 : real -> Prop) (x2 : real) := (real_le x0 x2) \/ (~ (@I (real -> Prop) x1 x2)).
Definition term350 (x0 : real -> Prop) (x1 : real -> Prop) := exists y0 : real, (forall y1 : real, ~ (x0 y1)) \/ ((x0 y0) /\ (~ (real_le (inf x1) y0))).
Definition term301 (x0 : real -> Prop) := fun y0 : real -> real => (forall y1 : real, (~ (x0 y1)) \/ (real_le (inf x0) y1)) /\ (forall y1 : real, ((x0 (y0 y1)) /\ (~ (real_le y1 (y0 y1)))) \/ (real_le y1 (inf x0))).
Definition term348 (x0 : real -> Prop) (x1 : real -> Prop) := fun y0 : real => (forall y1 : real, ~ (x0 y1)) \/ ((fun y1 : real => (x0 y1) /\ (~ (real_le (inf x1) y1))) y0).
Definition term357 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) := or ((x0 (x1 x2)) /\ (~ (real_le x2 (x1 x2)))).
Definition term338 (x0 : Prop) (x1 : real -> Prop) := exists y0 : real, x0 \/ (x1 y0).
Definition term434 := forall y0 : real -> Prop, forall y1 : real -> Prop, ((~ (y1 = (@EMPTY real))) /\ ((@SUBSET real y1 y0) /\ (exists y2 : real, forall y3 : real, (@IN real y3 y0) -> real_le y2 y3))) -> real_le (inf y0) (inf y1).
Definition term120 (x0 : real -> Prop) := forall y0 : real -> Prop, forall y1 : real, ((forall y2 : real, (x0 y2) -> real_le y1 y2) /\ ((forall y2 : real, (y0 y2) -> x0 y2) /\ (~ (forall y2 : real, ~ (y0 y2))))) -> (((~ (forall y2 : real, ~ (x0 y2))) /\ (exists y2 : real, forall y3 : real, (x0 y3) -> real_le y2 y3)) -> (forall y2 : real, (x0 y2) -> real_le (inf x0) y2) /\ (forall y2 : real, (forall y3 : real, (x0 y3) -> real_le y2 y3) -> real_le y2 (inf x0))) -> (~ (forall y2 : real, ~ (y0 y2))) /\ (forall y2 : real, (y0 y2) -> real_le (inf x0) y2).
Definition term389 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => ~ (@I (real -> Prop) x0 y0)) x1.
Definition term393 (x0 : real -> Prop) (x1 : real) := ~ (real_le (inf x0) x1).
Definition term259 (x0 : real -> Prop) (x1 : real) (x2 : real) := or ((x0 x2) /\ (~ (real_le x1 x2))).
Definition term76 (x0 : real -> Prop) := imp ((~ (forall y0 : real, ~ (x0 y0))) /\ (exists y0 : real, forall y1 : real, (x0 y1) -> real_le y0 y1)).
Definition term35 (x0 : real -> Prop) := imp ((~ (forall y0 : real, (@IN real y0 x0) = (@IN real y0 (@EMPTY real)))) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y0 y1)).
Definition term157 (x0 : real -> Prop) (x1 : real -> Prop) := fun y0 : real => (fun y1 : real => (forall y2 : real, (~ (x1 y2)) \/ (x0 y2)) /\ (x1 y1)) y0.
Definition term100 (x0 : real -> Prop) (x1 : real -> Prop) := fun y0 : real => (x0 y0) -> real_le (inf x1) y0.
Definition term81 (x0 : real -> Prop) := fun y0 : real => (x0 y0) -> real_le (inf x0) y0.
Definition term370 (x0 : real -> Prop) (x1 : real -> real) := fun y0 : real => (@I (real -> Prop) x0 (x1 y0)) /\ (~ (real_le y0 (x1 y0))).
Definition term180 (x0 : real -> Prop) (x1 : real) := ~ ((fun y0 : real => forall y1 : real, (x0 y1) -> real_le y0 y1) x1).
Definition term286 (x0 : real -> Prop) := fun y0 : real -> real => forall y1 : real, ((x0 (y0 y1)) /\ (~ (real_le y1 (y0 y1)))) \/ (real_le y1 (inf x0)).
Definition term285 (x0 : real -> Prop) := fun y0 : real -> real => forall y1 : real, (fun y2 : real => fun y3 : real => ((x0 y3) /\ (~ (real_le y2 y3))) \/ (real_le y2 (inf x0))) y1 (y0 y1).
Definition term227 (x0 : real -> Prop) := fun y0 : real -> real => forall y1 : real, (x0 (y0 y1)) /\ (~ (real_le y1 (y0 y1))).
Definition term226 (x0 : real -> Prop) := fun y0 : real -> real => forall y1 : real, (fun y2 : real => fun y3 : real => (x0 y3) /\ (~ (real_le y2 y3))) y1 (y0 y1).
Definition term118 (x0 : real -> Prop) := fun y0 : real -> Prop => forall y1 : real, ((forall y2 : real, (x0 y2) -> real_le y1 y2) /\ ((forall y2 : real, (y0 y2) -> x0 y2) /\ (~ (forall y2 : real, ~ (y0 y2))))) -> (((~ (forall y2 : real, ~ (x0 y2))) /\ (exists y2 : real, forall y3 : real, (x0 y3) -> real_le y2 y3)) -> (forall y2 : real, (x0 y2) -> real_le (inf x0) y2) /\ (forall y2 : real, (forall y3 : real, (x0 y3) -> real_le y2 y3) -> real_le y2 (inf x0))) -> (~ (forall y2 : real, ~ (y0 y2))) /\ (forall y2 : real, (y0 y2) -> real_le (inf x0) y2).
Definition term117 (x0 : real -> Prop) := fun y0 : real -> Prop => forall y1 : real, (~ (((forall y2 : real, (x0 y2) -> real_le y1 y2) /\ ((forall y2 : real, (y0 y2) -> x0 y2) /\ (~ (forall y2 : real, ~ (y0 y2))))) -> (((~ (forall y2 : real, ~ (x0 y2))) /\ (exists y2 : real, forall y3 : real, (x0 y3) -> real_le y2 y3)) -> (forall y2 : real, (x0 y2) -> real_le (inf x0) y2) /\ (forall y2 : real, (forall y3 : real, (x0 y3) -> real_le y2 y3) -> real_le y2 (inf x0))) -> (~ (forall y2 : real, ~ (y0 y2))) /\ (forall y2 : real, (y0 y2) -> real_le (inf x0) y2))) -> False.
Definition term15 (x0 : real -> Prop) (x1 : real -> Prop) := (@SUBSET real x1 x0) /\ (~ (x1 = (@EMPTY real))).
Definition term428 (x0 : real -> Prop) := (fun y0 : real -> Prop => forall y1 : real -> Prop, forall y2 : real, (~ (((forall y3 : real, (y0 y3) -> real_le y2 y3) /\ ((forall y3 : real, (y1 y3) -> y0 y3) /\ (~ (forall y3 : real, ~ (y1 y3))))) -> (((~ (forall y3 : real, ~ (y0 y3))) /\ (exists y3 : real, forall y4 : real, (y0 y4) -> real_le y3 y4)) -> (forall y3 : real, (y0 y3) -> real_le (inf y0) y3) /\ (forall y3 : real, (forall y4 : real, (y0 y4) -> real_le y3 y4) -> real_le y3 (inf y0))) -> (~ (forall y3 : real, ~ (y1 y3))) /\ (forall y3 : real, (y1 y3) -> real_le (inf y0) y3))) -> False) x0.
Definition term313 (x0 : real -> Prop) := or (exists y0 : real -> real, (fun y1 : real -> real => (forall y2 : real, ~ (x0 y2)) \/ (forall y2 : real, (x0 (y1 y2)) /\ (~ (real_le y2 (y1 y2))))) y0).
Definition term400 (x0 : real -> Prop) (x1 : real -> Prop) (x2 : real) := @eq Prop ((@I (real -> Prop) x0 x2) \/ (~ (x1 x2))).
Definition term161 (x0 : real) (x1 : real -> Prop) (x2 : real -> Prop) (x3 : real) := (forall y0 : real, (~ (x1 y0)) \/ (real_le x0 y0)) /\ ((fun y0 : real => (forall y1 : real, (~ (x2 y1)) \/ (x1 y1)) /\ (x2 y0)) x3).
Definition term373 (x0 : real -> Prop) := forall y0 : real, ~ (@I (real -> Prop) x0 y0).
Definition term244 (x0 : real -> Prop) := fun y0 : real -> real => (forall y1 : real, ~ (x0 y1)) \/ (forall y1 : real, (x0 (y0 y1)) /\ (~ (real_le y1 (y0 y1)))).
Definition term385 (x0 : real -> Prop) (x1 : real) := forall y0 : real, (~ (@I (real -> Prop) x0 y0)) \/ (real_le x1 y0).
Definition term380 (x0 : real -> Prop) (x1 : real -> Prop) := forall y0 : real, (~ (x0 y0)) \/ (@I (real -> Prop) x1 y0).
Definition term129 (x0 : real -> Prop) (x1 : real) := forall y0 : real, (~ (x0 y0)) \/ (real_le x1 y0).
Definition term99 (x0 : real -> Prop) (x1 : real -> Prop) := fun y0 : real => (@IN real y0 x0) -> real_le (inf x1) y0.
Definition term80 (x0 : real -> Prop) := fun y0 : real => (@IN real y0 x0) -> real_le (inf x0) y0.
Definition term261 (x0 : real) (x1 : real) (x2 : real -> Prop) := ((x2 x0) /\ (~ (real_le x1 x0))) \/ (real_le x1 (inf x2)).
Definition term314 (x0 : real -> Prop) (x1 : real -> real) := (fun y0 : real -> real => (forall y1 : real, (~ (x0 y1)) \/ (real_le (inf x0) y1)) /\ (forall y1 : real, ((x0 (y0 y1)) /\ (~ (real_le y1 (y0 y1)))) \/ (real_le y1 (inf x0)))) x1.
Definition term379 (x0 : real -> Prop) (x1 : real -> Prop) := fun y0 : real => (~ (x0 y0)) \/ (@I (real -> Prop) x1 y0).
Definition term309 (x0 : real -> Prop) := exists y0 : real -> real, ((fun y1 : real -> real => (forall y2 : real, ~ (x0 y2)) \/ (forall y2 : real, (x0 (y1 y2)) /\ (~ (real_le y2 (y1 y2))))) y0) \/ ((fun y1 : real -> real => (forall y2 : real, (~ (x0 y2)) \/ (real_le (inf x0) y2)) /\ (forall y2 : real, ((x0 (y1 y2)) /\ (~ (real_le y2 (y1 y2)))) \/ (real_le y2 (inf x0)))) y0).
Definition term429 (x0 : real -> Prop) (x1 : real -> Prop) := (fun y0 : real -> Prop => forall y1 : real, (~ (((forall y2 : real, (x0 y2) -> real_le y1 y2) /\ ((forall y2 : real, (y0 y2) -> x0 y2) /\ (~ (forall y2 : real, ~ (y0 y2))))) -> (((~ (forall y2 : real, ~ (x0 y2))) /\ (exists y2 : real, forall y3 : real, (x0 y3) -> real_le y2 y3)) -> (forall y2 : real, (x0 y2) -> real_le (inf x0) y2) /\ (forall y2 : real, (forall y3 : real, (x0 y3) -> real_le y2 y3) -> real_le y2 (inf x0))) -> (~ (forall y2 : real, ~ (y0 y2))) /\ (forall y2 : real, (y0 y2) -> real_le (inf x0) y2))) -> False) x1.
Definition term128 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (~ (x0 y0)) \/ (real_le x1 y0).
Definition term346 (x0 : real -> Prop) (x1 : real -> Prop) (x2 : real) := (forall y0 : real, ~ (x0 y0)) \/ ((fun y0 : real => (x0 y0) /\ (~ (real_le (inf x1) y0))) x2).
Definition term376 (x0 : real -> Prop) (x1 : real -> real) := or ((forall y0 : real, ~ (@I (real -> Prop) x0 y0)) \/ (forall y0 : real, (@I (real -> Prop) x0 (x1 y0)) /\ (~ (real_le y0 (x1 y0))))).
Definition term320 (x0 : real -> Prop) (x1 : real -> real) := or ((forall y0 : real, ~ (x0 y0)) \/ (forall y0 : real, (x0 (x1 y0)) /\ (~ (real_le y0 (x1 y0))))).
Definition term201 (x0 : real -> Prop) := or ((forall y0 : real, ~ (x0 y0)) \/ (forall y0 : real, exists y1 : real, (x0 y1) /\ (~ (real_le y0 y1)))).
Definition term178 (x0 : real -> Prop) := forall y0 : real, ~ ((fun y1 : real => forall y2 : real, (x0 y2) -> real_le y1 y2) y0).
Definition term87 (x0 : real -> Prop) (x1 : real) := imp (forall y0 : real, (x0 y0) -> real_le x1 y0).
Definition term86 (x0 : real -> Prop) (x1 : real) := imp (forall y0 : real, (@IN real y0 x0) -> real_le x1 y0).
Definition term402 (x0 : real -> Prop) (x1 : real -> Prop) (x2 : real) := (~ (~ (x0 x2))) -> @I (real -> Prop) x1 x2.
Definition term332 (x0 : real -> Prop) (x1 : real -> Prop) := fun y0 : real => ~ ((fun y1 : real => (x0 y1) -> real_le (inf x1) y1) y0).
Definition term173 (x0 : real -> Prop) (x1 : real) := fun y0 : real => ~ ((fun y1 : real => (x0 y1) -> real_le x1 y1) y0).
Definition term17 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) -> @IN a0 y0 x1.
Definition term415 (x0 : real -> Prop) (x1 : real) := imp (@I (real -> Prop) x0 x1).
Definition term260 (x0 : real) (x1 : real) (x2 : real -> Prop) := ((fun y0 : real => (x2 y0) /\ (~ (real_le x1 y0))) x0) \/ (real_le x1 (inf x2)).
Definition term71 (x0 : real -> Prop) := and (~ (forall y0 : real, ~ (x0 y0))).
Definition term31 (x0 : real -> Prop) := and (~ (forall y0 : real, (@IN real y0 x0) = (@IN real y0 (@EMPTY real)))).
Definition term93 (x0 : real -> Prop) := forall y0 : real, (forall y1 : real, (x0 y1) -> real_le y0 y1) -> real_le y0 (inf x0).
Definition term92 (x0 : real -> Prop) := forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y0 y1) -> real_le y0 (inf x0).
Definition term225 (x0 : real -> Prop) (x1 : real -> real) := forall y0 : real, (x0 (x1 y0)) /\ (~ (real_le y0 (x1 y0))).
Definition term49 (x0 : real -> Prop) (x1 : real) (x2 : real) := (@IN real x2 x0) -> real_le x1 x2.
Definition term297 (x0 : real -> Prop) := @eq Prop ((forall y0 : real, (~ (x0 y0)) \/ (real_le (inf x0) y0)) /\ (exists y0 : real -> real, forall y1 : real, ((x0 (y0 y1)) /\ (~ (real_le y1 (y0 y1)))) \/ (real_le y1 (inf x0)))).
Definition term296 (x0 : real -> Prop) := @eq Prop ((forall y0 : real, (~ (x0 y0)) \/ (real_le (inf x0) y0)) /\ (exists y0 : real -> real, (fun y1 : real -> real => forall y2 : real, ((x0 (y1 y2)) /\ (~ (real_le y2 (y1 y2)))) \/ (real_le y2 (inf x0))) y0)).
Definition term160 (x0 : real) (x1 : real -> Prop) (x2 : real -> Prop) := @eq Prop ((forall y0 : real, (~ (x1 y0)) \/ (real_le x0 y0)) /\ (exists y0 : real, (forall y1 : real, (~ (x2 y1)) \/ (x1 y1)) /\ (x2 y0))).
Definition term159 (x0 : real) (x1 : real -> Prop) (x2 : real -> Prop) := @eq Prop ((forall y0 : real, (~ (x1 y0)) \/ (real_le x0 y0)) /\ (exists y0 : real, (fun y1 : real => (forall y2 : real, (~ (x2 y2)) \/ (x1 y2)) /\ (x2 y1)) y0)).
Definition term223 (x0 : real -> Prop) (x1 : real -> real) := fun y0 : real => (x0 (x1 y0)) /\ (~ (real_le y0 (x1 y0))).
Definition term410 (x0 : real -> Prop) (x1 : real) (x2 : real) := @eq Prop ((~ (@I (real -> Prop) x0 x2)) \/ (real_le x1 x2)).
Definition term50 (x0 : real -> Prop) (x1 : real) (x2 : real) := (x0 x2) -> real_le x1 x2.
Definition term211 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => fun y1 : real => (x0 y1) /\ (~ (real_le y0 y1))) x1.
Definition term116 (x0 : real -> Prop) (x1 : real -> Prop) := forall y0 : real, ((forall y1 : real, (x1 y1) -> real_le y0 y1) /\ ((forall y1 : real, (x0 y1) -> x1 y1) /\ (~ (forall y1 : real, ~ (x0 y1))))) -> (((~ (forall y1 : real, ~ (x1 y1))) /\ (exists y1 : real, forall y2 : real, (x1 y2) -> real_le y1 y2)) -> (forall y1 : real, (x1 y1) -> real_le (inf x1) y1) /\ (forall y1 : real, (forall y2 : real, (x1 y2) -> real_le y1 y2) -> real_le y1 (inf x1))) -> (~ (forall y1 : real, ~ (x0 y1))) /\ (forall y1 : real, (x0 y1) -> real_le (inf x1) y1).
Definition term392 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => (~ (@I (real -> Prop) x0 y0)) \/ (real_le (inf x0) y0)) x1.
Definition term269 (x0 : real -> Prop) := fun y0 : real => fun y1 : real => ((x0 y1) /\ (~ (real_le y0 y1))) \/ (real_le y0 (inf x0)).
Definition term110 (x0 : real) (x1 : real -> Prop) (x2 : real -> Prop) := (((~ (((forall y0 : real, (x2 y0) -> real_le x0 y0) /\ ((forall y0 : real, (x1 y0) -> x2 y0) /\ (~ (forall y0 : real, ~ (x1 y0))))) -> (((~ (forall y0 : real, ~ (x2 y0))) /\ (exists y0 : real, forall y1 : real, (x2 y1) -> real_le y0 y1)) -> (forall y0 : real, (x2 y0) -> real_le (inf x2) y0) /\ (forall y0 : real, (forall y1 : real, (x2 y1) -> real_le y0 y1) -> real_le y0 (inf x2))) -> (~ (forall y0 : real, ~ (x1 y0))) /\ (forall y0 : real, (x1 y0) -> real_le (inf x2) y0))) -> False) -> (~ (((forall y0 : real, (x2 y0) -> real_le x0 y0) /\ ((forall y0 : real, (x1 y0) -> x2 y0) /\ (~ (forall y0 : real, ~ (x1 y0))))) -> (((~ (forall y0 : real, ~ (x2 y0))) /\ (exists y0 : real, forall y1 : real, (x2 y1) -> real_le y0 y1)) -> (forall y0 : real, (x2 y0) -> real_le (inf x2) y0) /\ (forall y0 : real, (forall y1 : real, (x2 y1) -> real_le y0 y1) -> real_le y0 (inf x2))) -> (~ (forall y0 : real, ~ (x1 y0))) /\ (forall y0 : real, (x1 y0) -> real_le (inf x2) y0))) -> False) -> ((~ (((forall y0 : real, (x2 y0) -> real_le x0 y0) /\ ((forall y0 : real, (x1 y0) -> x2 y0) /\ (~ (forall y0 : real, ~ (x1 y0))))) -> (((~ (forall y0 : real, ~ (x2 y0))) /\ (exists y0 : real, forall y1 : real, (x2 y1) -> real_le y0 y1)) -> (forall y0 : real, (x2 y0) -> real_le (inf x2) y0) /\ (forall y0 : real, (forall y1 : real, (x2 y1) -> real_le y0 y1) -> real_le y0 (inf x2))) -> (~ (forall y0 : real, ~ (x1 y0))) /\ (forall y0 : real, (x1 y0) -> real_le (inf x2) y0))) -> False) -> (~ (((forall y0 : real, (x2 y0) -> real_le x0 y0) /\ ((forall y0 : real, (x1 y0) -> x2 y0) /\ (~ (forall y0 : real, ~ (x1 y0))))) -> (((~ (forall y0 : real, ~ (x2 y0))) /\ (exists y0 : real, forall y1 : real, (x2 y1) -> real_le y0 y1)) -> (forall y0 : real, (x2 y0) -> real_le (inf x2) y0) /\ (forall y0 : real, (forall y1 : real, (x2 y1) -> real_le y0 y1) -> real_le y0 (inf x2))) -> (~ (forall y0 : real, ~ (x1 y0))) /\ (forall y0 : real, (x1 y0) -> real_le (inf x2) y0))) -> False.
Definition term122 := fun y0 : real -> Prop => forall y1 : real -> Prop, forall y2 : real, ((forall y3 : real, (y0 y3) -> real_le y2 y3) /\ ((forall y3 : real, (y1 y3) -> y0 y3) /\ (~ (forall y3 : real, ~ (y1 y3))))) -> (((~ (forall y3 : real, ~ (y0 y3))) /\ (exists y3 : real, forall y4 : real, (y0 y4) -> real_le y3 y4)) -> (forall y3 : real, (y0 y3) -> real_le (inf y0) y3) /\ (forall y3 : real, (forall y4 : real, (y0 y4) -> real_le y3 y4) -> real_le y3 (inf y0))) -> (~ (forall y3 : real, ~ (y1 y3))) /\ (forall y3 : real, (y1 y3) -> real_le (inf y0) y3).
Definition term121 := fun y0 : real -> Prop => forall y1 : real -> Prop, forall y2 : real, (~ (((forall y3 : real, (y0 y3) -> real_le y2 y3) /\ ((forall y3 : real, (y1 y3) -> y0 y3) /\ (~ (forall y3 : real, ~ (y1 y3))))) -> (((~ (forall y3 : real, ~ (y0 y3))) /\ (exists y3 : real, forall y4 : real, (y0 y4) -> real_le y3 y4)) -> (forall y3 : real, (y0 y3) -> real_le (inf y0) y3) /\ (forall y3 : real, (forall y4 : real, (y0 y4) -> real_le y3 y4) -> real_le y3 (inf y0))) -> (~ (forall y3 : real, ~ (y1 y3))) /\ (forall y3 : real, (y1 y3) -> real_le (inf y0) y3))) -> False.
Definition term423 (x0 : real -> Prop) (x1 : real) := @eq Prop ((real_le (inf x0) x1) \/ (~ (@I (real -> Prop) x0 x1))).
Definition term130 (x0 : real -> Prop) (x1 : real -> Prop) (x2 : real) := (~ (x0 x2)) \/ (x1 x2).
Definition term310 (x0 : real -> Prop) (x1 : real -> real) := (fun y0 : real -> real => (forall y1 : real, ~ (x0 y1)) \/ (forall y1 : real, (x0 (y0 y1)) /\ (~ (real_le y1 (y0 y1))))) x1.
Definition term125 (x0 : real -> Prop) (x1 : real -> Prop) := (~ ((~ (forall y0 : real, ~ (x0 y0))) /\ (forall y0 : real, (x0 y0) -> real_le (inf x1) y0))) -> False.
Definition term119 (x0 : real -> Prop) := forall y0 : real -> Prop, forall y1 : real, (~ (((forall y2 : real, (x0 y2) -> real_le y1 y2) /\ ((forall y2 : real, (y0 y2) -> x0 y2) /\ (~ (forall y2 : real, ~ (y0 y2))))) -> (((~ (forall y2 : real, ~ (x0 y2))) /\ (exists y2 : real, forall y3 : real, (x0 y3) -> real_le y2 y3)) -> (forall y2 : real, (x0 y2) -> real_le (inf x0) y2) /\ (forall y2 : real, (forall y3 : real, (x0 y3) -> real_le y2 y3) -> real_le y2 (inf x0))) -> (~ (forall y2 : real, ~ (y0 y2))) /\ (forall y2 : real, (y0 y2) -> real_le (inf x0) y2))) -> False.
Definition term420 (x0 : real -> real) (x1 : real) := (real_le x1 (x0 x1)) -> False.
Definition term274 (x0 : real -> Prop) (x1 : real) := exists y0 : real, (fun y1 : real => fun y2 : real => ((x0 y2) /\ (~ (real_le y1 y2))) \/ (real_le y1 (inf x0))) x1 y0.
Definition term215 (x0 : real -> Prop) (x1 : real) := exists y0 : real, (fun y1 : real => fun y2 : real => (x0 y2) /\ (~ (real_le y1 y2))) x1 y0.
Definition term28 (x0 : real) (x1 : real -> Prop) (x2 : real -> Prop) := imp ((forall y0 : real, (@IN real y0 x1) -> real_le x0 y0) /\ ((@SUBSET real x2 x1) /\ (~ (x2 = (@EMPTY real))))).
Definition term48 (x0 : real -> Prop) (x1 : real) := imp (x0 x1).
Definition term235 (x0 : real -> Prop) := exists y0 : real -> real, (forall y1 : real, ~ (x0 y1)) \/ ((fun y1 : real -> real => forall y2 : real, (x0 (y1 y2)) /\ (~ (real_le y2 (y1 y2)))) y0).
Definition term372 (x0 : real -> Prop) := fun y0 : real => ~ (@I (real -> Prop) x0 y0).
Definition term246 (x0 : real -> Prop) := or (exists y0 : real -> real, (forall y1 : real, ~ (x0 y1)) \/ (forall y1 : real, (x0 (y0 y1)) /\ (~ (real_le y1 (y0 y1))))).
Definition term103 (x0 : real -> Prop) (x1 : real -> Prop) := (((~ (forall y0 : real, ~ (x1 y0))) /\ (exists y0 : real, forall y1 : real, (x1 y1) -> real_le y0 y1)) -> (forall y0 : real, (x1 y0) -> real_le (inf x1) y0) /\ (forall y0 : real, (forall y1 : real, (x1 y1) -> real_le y0 y1) -> real_le y0 (inf x1))) -> (~ (forall y0 : real, ~ (x0 y0))) /\ (forall y0 : real, (x0 y0) -> real_le (inf x1) y0).
Definition term44 (x0 : real -> Prop) (x1 : real -> Prop) := (((~ (forall y0 : real, (@IN real y0 x1) = (@IN real y0 (@EMPTY real)))) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x1) -> real_le y0 y1)) -> (forall y0 : real, (@IN real y0 x1) -> real_le (inf x1) y0) /\ (forall y0 : real, (forall y1 : real, (@IN real y1 x1) -> real_le y0 y1) -> real_le y0 (inf x1))) -> (~ (forall y0 : real, (@IN real y0 x0) = (@IN real y0 (@EMPTY real)))) /\ (forall y0 : real, (@IN real y0 x0) -> real_le (inf x1) y0).
Definition term326 (x0 : real -> Prop) (x1 : real -> Prop) (x2 : real) := ~ ((x0 x2) -> real_le (inf x1) x2).
Definition term77 (x0 : real -> Prop) (x1 : real) := real_le (inf x0) x1.
Definition term336 (x0 : real -> Prop) (x1 : real -> Prop) := (forall y0 : real, ~ (x0 y0)) \/ (exists y0 : real, (x0 y0) /\ (~ (real_le (inf x1) y0))).
Definition term68 (x0 : real -> Prop) (x1 : real -> Prop) := (forall y0 : real, (x1 y0) -> x0 y0) /\ (~ (forall y0 : real, ~ (x1 y0))).
Definition term25 (x0 : real -> Prop) (x1 : real -> Prop) := (forall y0 : real, (@IN real y0 x1) -> @IN real y0 x0) /\ (~ (forall y0 : real, (@IN real y0 x1) = (@IN real y0 (@EMPTY real)))).
Definition term383 (x0 : real -> Prop) (x1 : real) (x2 : real) := (~ (@I (real -> Prop) x0 x2)) \/ (real_le x1 x2).
Definition term205 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term262 (x0 : real) (x1 : real -> Prop) := fun y0 : real => ((fun y1 : real => (x1 y1) /\ (~ (real_le x0 y1))) y0) \/ (real_le x0 (inf x1)).
Definition term167 (x0 : real -> Prop) (x1 : real) (x2 : real) := ~ ((x0 x2) -> real_le x1 x2).
Definition term358 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) := or ((@I (real -> Prop) x0 (x1 x2)) /\ (~ (real_le x2 (x1 x2)))).
Definition term362 (x0 : real -> Prop) (x1 : real) := ~ (@I (real -> Prop) x0 x1).
Definition term193 (x0 : real -> Prop) (x1 : real) := or (exists y0 : real, (x0 y0) /\ (~ (real_le x1 y0))).
Definition term354 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) := and (x0 (x1 x2)).
Definition term305 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term371 (x0 : real -> Prop) (x1 : real -> real) := forall y0 : real, (@I (real -> Prop) x0 (x1 y0)) /\ (~ (real_le y0 (x1 y0))).
Definition term391 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) := (fun y0 : real => (@I (real -> Prop) x0 (x1 y0)) /\ (~ (real_le y0 (x1 y0)))) x2.
Definition term95 (x0 : real -> Prop) := ((~ (forall y0 : real, ~ (x0 y0))) /\ (exists y0 : real, forall y1 : real, (x0 y1) -> real_le y0 y1)) -> (forall y0 : real, (x0 y0) -> real_le (inf x0) y0) /\ (forall y0 : real, (forall y1 : real, (x0 y1) -> real_le y0 y1) -> real_le y0 (inf x0)).
Definition term37 (x0 : real -> Prop) := ((~ (forall y0 : real, (@IN real y0 x0) = (@IN real y0 (@EMPTY real)))) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y0 y1)) -> (forall y0 : real, (@IN real y0 x0) -> real_le (inf x0) y0) /\ (forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y0 y1) -> real_le y0 (inf x0)).
Definition term1 (x0 : real -> Prop) := ((~ (x0 = (@EMPTY real))) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y0 y1)) -> (forall y0 : real, (@IN real y0 x0) -> real_le (inf x0) y0) /\ (forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y0 y1) -> real_le y0 (inf x0)).
Definition term63 (x0 : real -> Prop) (x1 : real) := ~ (x0 x1).
Definition term132 (x0 : real -> Prop) (x1 : real -> Prop) := forall y0 : real, (~ (x0 y0)) \/ (x1 y0).
Definition term58 (x0 : real -> Prop) (x1 : real -> Prop) := fun y0 : real => (x0 y0) -> x1 y0.
Definition term382 (x0 : real -> Prop) (x1 : real -> Prop) (x2 : real) := (forall y0 : real, (~ (x1 y0)) \/ (@I (real -> Prop) x0 y0)) /\ (x1 x2).
Definition term156 (x0 : real -> Prop) (x1 : real -> Prop) (x2 : real) := (forall y0 : real, (~ (x1 y0)) \/ (x0 y0)) /\ (x1 x2).
Definition term339 (x0 : real -> Prop) (x1 : real -> Prop) := (forall y0 : real, ~ (x0 y0)) \/ (exists y0 : real, (fun y1 : real => (x0 y1) /\ (~ (real_le (inf x1) y1))) y0).
Definition term32 (x0 : real -> Prop) := (~ (x0 = (@EMPTY real))) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y0 y1).
Definition term414 (x0 : real -> Prop) (x1 : real) := imp (~ (~ (@I (real -> Prop) x0 x1))).
Definition term22 (x0 : real -> Prop) (x1 : real -> Prop) := forall y0 : real, (@IN real y0 x0) = (@IN real y0 x1).
Definition term318 (x0 : real -> Prop) := @eq Prop ((exists y0 : real -> real, (forall y1 : real, ~ (x0 y1)) \/ (forall y1 : real, (x0 (y0 y1)) /\ (~ (real_le y1 (y0 y1))))) \/ (exists y0 : real -> real, (forall y1 : real, (~ (x0 y1)) \/ (real_le (inf x0) y1)) /\ (forall y1 : real, ((x0 (y0 y1)) /\ (~ (real_le y1 (y0 y1)))) \/ (real_le y1 (inf x0))))).
Definition term317 (x0 : real -> Prop) := @eq Prop ((exists y0 : real -> real, (fun y1 : real -> real => (forall y2 : real, ~ (x0 y2)) \/ (forall y2 : real, (x0 (y1 y2)) /\ (~ (real_le y2 (y1 y2))))) y0) \/ (exists y0 : real -> real, (fun y1 : real -> real => (forall y2 : real, (~ (x0 y2)) \/ (real_le (inf x0) y2)) /\ (forall y2 : real, ((x0 (y1 y2)) /\ (~ (real_le y2 (y1 y2)))) \/ (real_le y2 (inf x0)))) y0)).
