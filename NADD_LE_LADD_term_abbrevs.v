Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term314 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, nadd_eq (nadd_add y0 y1) (nadd_add y1 y0)) x0.
Definition term273 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (forall y2 : nadd, ~ (nadd_le (nadd_add y0 y2) (nadd_add y1 y2))) \/ (nadd_le y0 y1)) x0.
Definition term271 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (forall y2 : nadd, nadd_le (nadd_add y0 y2) (nadd_add y1 y2)) \/ (~ (nadd_le y0 y1))) x0.
Definition term333 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (nadd_le x0 x1) \/ ((~ (nadd_eq x2 x0)) \/ ((~ (nadd_eq x3 x1)) \/ (~ (nadd_le x2 x3)))).
Definition term353 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := imp (~ ((~ (nadd_eq x2 x0)) \/ ((~ (nadd_eq x3 x1)) \/ (~ (nadd_le x2 x3))))).
Definition term282 := and (forall y0 : nadd, forall y1 : nadd, (forall y2 : nadd, nadd_le (nadd_add y0 y2) (nadd_add y1 y2)) \/ (~ (nadd_le y0 y1))).
Definition term54 (x0 : nadd -> Prop) := ~ (all x0).
Definition term370 := (~ False) -> False.
Definition term112 (x0 : nadd) (x1 : nadd) := ((fun y0 : nadd => exists y1 : nadd, (nadd_le (nadd_add x0 y0) (nadd_add x0 y1)) /\ (~ (nadd_le y0 y1))) x1) \/ ((fun y0 : nadd => exists y1 : nadd, (~ (nadd_le (nadd_add x0 y0) (nadd_add x0 y1))) /\ (nadd_le y0 y1)) x1).
Definition term190 (x0 : nadd) (x1 : nadd) (x2 : nadd) := ((fun y0 : nadd => (nadd_le (nadd_add x0 y0) (nadd_add x1 y0)) \/ (~ (nadd_le x0 x1))) x2) /\ ((fun y0 : nadd => (~ (nadd_le (nadd_add x0 y0) (nadd_add x1 y0))) \/ (nadd_le x0 x1)) x2).
Definition term378 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (nadd_le (nadd_add x1 x0) (nadd_add x1 x2)) -> False.
Definition term320 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := ((~ (nadd_eq x0 x2)) \/ (~ (nadd_eq x1 x3))) \/ ((~ (nadd_le x0 x1)) \/ (nadd_le x2 x3)).
Definition term306 (x0 : nadd) := fun y0 : nadd => forall y1 : nadd, (nadd_le (nadd_add x0 y1) (nadd_add y0 y1)) \/ (~ (nadd_le x0 y0)).
Definition term269 := fun y0 : nadd => forall y1 : nadd, (forall y2 : nadd, nadd_le (nadd_add y0 y2) (nadd_add y1 y2)) \/ (~ (nadd_le y0 y1)).
Definition term52 (x0 : nadd) (x1 : nadd) (x2 : nadd) := ~ ((nadd_le (nadd_add x0 x1) (nadd_add x0 x2)) = (nadd_le x1 x2)).
Definition term239 (x0 : nadd) (x1 : nadd) := or (forall y0 : nadd, (fun y1 : nadd => ~ (nadd_le (nadd_add x0 y1) (nadd_add x1 y1))) y0).
Definition term221 (x0 : nadd) (x1 : nadd) := or (forall y0 : nadd, (fun y1 : nadd => nadd_le (nadd_add x0 y1) (nadd_add x1 y1)) y0).
Definition term94 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => (fun y1 : nadd => (nadd_le (nadd_add x0 x1) (nadd_add x0 y1)) /\ (~ (nadd_le x1 y1))) y0.
Definition term98 (x0 : nadd) (x1 : nadd) := or (exists y0 : nadd, (nadd_le (nadd_add x0 x1) (nadd_add x0 y0)) /\ (~ (nadd_le x1 y0))).
Definition term100 (x0 : nadd) (x1 : nadd) := exists y0 : nadd, (fun y1 : nadd => (~ (nadd_le (nadd_add x0 x1) (nadd_add x0 y1))) /\ (nadd_le x1 y1)) y0.
Definition term95 (x0 : nadd) (x1 : nadd) := exists y0 : nadd, (fun y1 : nadd => (nadd_le (nadd_add x0 x1) (nadd_add x0 y1)) /\ (~ (nadd_le x1 y1))) y0.
Definition term286 := (forall y0 : nadd, forall y1 : nadd, (forall y2 : nadd, nadd_le (nadd_add y0 y2) (nadd_add y1 y2)) \/ (~ (nadd_le y0 y1))) /\ (forall y0 : nadd, forall y1 : nadd, (forall y2 : nadd, ~ (nadd_le (nadd_add y0 y2) (nadd_add y1 y2))) \/ (nadd_le y0 y1)).
Definition term91 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => ((fun y1 : nadd => (nadd_le (nadd_add x0 x1) (nadd_add x0 y1)) /\ (~ (nadd_le x1 y1))) y0) \/ ((fun y1 : nadd => (~ (nadd_le (nadd_add x0 x1) (nadd_add x0 y1))) /\ (nadd_le x1 y1)) y0).
Definition term344 (x0 : Prop) := ~ (~ x0).
Definition term161 (x0 : nadd) (x1 : nadd) (x2 : nadd) := fun y0 : nadd => ((~ (nadd_eq x0 x2)) \/ (~ (nadd_eq x1 y0))) \/ (((nadd_le x0 x1) \/ (~ (nadd_le x2 y0))) /\ ((~ (nadd_le x0 x1)) \/ (nadd_le x2 y0))).
Definition term179 (x0 : nadd -> Prop) (x1 : nadd -> Prop) := (forall y0 : nadd, x0 y0) /\ (forall y0 : nadd, x1 y0).
Definition term25 := (~ (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le (nadd_add y0 y1) (nadd_add y0 y2)) = (nadd_le y1 y2))) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y2 y3)) -> (nadd_le y0 y2) = (nadd_le y1 y3)) -> (forall y0 : nadd, forall y1 : nadd, nadd_eq (nadd_add y0 y1) (nadd_add y1 y0)) -> ~ (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le (nadd_add y0 y2) (nadd_add y1 y2)) = (nadd_le y0 y1)).
Definition term252 (x0 : nadd) (x1 : nadd) := ((fun y0 : nadd => (forall y1 : nadd, nadd_le (nadd_add x0 y1) (nadd_add y0 y1)) \/ (~ (nadd_le x0 y0))) x1) /\ ((fun y0 : nadd => (forall y1 : nadd, ~ (nadd_le (nadd_add x0 y1) (nadd_add y0 y1))) \/ (nadd_le x0 y0)) x1).
Definition term325 (x0 : nadd) (x1 : nadd) := ~ (nadd_eq (nadd_add x1 x0) (nadd_add x0 x1)).
Definition term264 (x0 : nadd) := (forall y0 : nadd, (forall y1 : nadd, nadd_le (nadd_add x0 y1) (nadd_add y0 y1)) \/ (~ (nadd_le x0 y0))) /\ (forall y0 : nadd, (forall y1 : nadd, ~ (nadd_le (nadd_add x0 y1) (nadd_add y0 y1))) \/ (nadd_le x0 y0)).
Definition term202 (x0 : nadd) (x1 : nadd) := (forall y0 : nadd, (nadd_le (nadd_add x0 y0) (nadd_add x1 y0)) \/ (~ (nadd_le x0 x1))) /\ (forall y0 : nadd, (~ (nadd_le (nadd_add x0 y0) (nadd_add x1 y0))) \/ (nadd_le x0 x1)).
Definition term360 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (nadd_le x0 x1) \/ (~ (nadd_le (nadd_add x0 x2) (nadd_add x1 x2))).
Definition term300 (x0 : nadd) := fun y0 : nadd => forall y1 : nadd, (~ (nadd_le (nadd_add x0 y1) (nadd_add y0 y1))) \/ (nadd_le x0 y0).
Definition term270 := fun y0 : nadd => forall y1 : nadd, (forall y2 : nadd, ~ (nadd_le (nadd_add y0 y2) (nadd_add y1 y2))) \/ (nadd_le y0 y1).
Definition term49 (x0 : nadd) := fun y0 : nadd => forall y1 : nadd, (nadd_le (nadd_add x0 y0) (nadd_add x0 y1)) = (nadd_le y0 y1).
Definition term35 := fun y0 : nadd => forall y1 : nadd, nadd_eq (nadd_add y0 y1) (nadd_add y1 y0).
Definition term29 (x0 : nadd) := fun y0 : nadd => forall y1 : nadd, (nadd_le (nadd_add x0 y1) (nadd_add y0 y1)) = (nadd_le x0 y0).
Definition term366 (x0 : nadd) (x1 : nadd) (x2 : nadd) := imp (nadd_le (nadd_add x0 x2) (nadd_add x1 x2)).
Definition term323 (x0 : nadd) (x1 : nadd) (x2 : nadd) := ~ (nadd_le (nadd_add x1 x0) (nadd_add x1 x2)).
Definition term46 (x0 : nadd) (x1 : nadd) (x2 : nadd) := nadd_le (nadd_add x1 x0) (nadd_add x1 x2).
Definition term349 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (~ (~ (nadd_eq x2 x0))) /\ (~ (~ (nadd_le x1 x2))).
Definition term77 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term229 (x0 : nadd) (x1 : nadd) (x2 : nadd) := ~ (nadd_le (nadd_add x0 x2) (nadd_add x1 x2)).
Definition term23 := (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y2 y3)) -> (nadd_le y0 y2) = (nadd_le y1 y3)) -> (forall y0 : nadd, forall y1 : nadd, nadd_eq (nadd_add y0 y1) (nadd_add y1 y0)) -> ~ (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le (nadd_add y0 y2) (nadd_add y1 y2)) = (nadd_le y0 y1)).
Definition term233 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => ((fun y1 : nadd => ~ (nadd_le (nadd_add x0 y1) (nadd_add x1 y1))) y0) \/ (nadd_le x0 x1).
Definition term305 (x0 : nadd) (x1 : nadd) := @eq Prop ((forall y0 : nadd, nadd_le (nadd_add x0 y0) (nadd_add x1 y0)) \/ (~ (nadd_le x0 x1))).
Definition term304 (x0 : nadd) (x1 : nadd) := @eq Prop ((forall y0 : nadd, (fun y1 : nadd => nadd_le (nadd_add x0 y1) (nadd_add x1 y1)) y0) \/ (~ (nadd_le x0 x1))).
Definition term3 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term355 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := ((nadd_eq x0 x2) /\ ((nadd_eq x1 x3) /\ (nadd_le x0 x1))) -> nadd_le x2 x3.
Definition term309 := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le (nadd_add y0 y2) (nadd_add y1 y2)) \/ (~ (nadd_le y0 y1)).
Definition term307 (x0 : nadd) := forall y0 : nadd, forall y1 : nadd, (nadd_le (nadd_add x0 y1) (nadd_add y0 y1)) \/ (~ (nadd_le x0 y0)).
Definition term303 := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (~ (nadd_le (nadd_add y0 y2) (nadd_add y1 y2))) \/ (nadd_le y0 y1).
Definition term301 (x0 : nadd) := forall y0 : nadd, forall y1 : nadd, (~ (nadd_le (nadd_add x0 y1) (nadd_add y0 y1))) \/ (nadd_le x0 y0).
Definition term297 := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, (((~ (nadd_eq y0 y1)) \/ (~ (nadd_eq y2 y3))) \/ ((nadd_le y0 y2) \/ (~ (nadd_le y1 y3)))) /\ (((~ (nadd_eq y0 y1)) \/ (~ (nadd_eq y2 y3))) \/ ((~ (nadd_le y0 y2)) \/ (nadd_le y1 y3))).
Definition term295 (x0 : nadd) := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (((~ (nadd_eq x0 y0)) \/ (~ (nadd_eq y1 y2))) \/ ((nadd_le x0 y1) \/ (~ (nadd_le y0 y2)))) /\ (((~ (nadd_eq x0 y0)) \/ (~ (nadd_eq y1 y2))) \/ ((~ (nadd_le x0 y1)) \/ (nadd_le y0 y2))).
Definition term293 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, forall y1 : nadd, (((~ (nadd_eq x0 x1)) \/ (~ (nadd_eq y0 y1))) \/ ((nadd_le x0 y0) \/ (~ (nadd_le x1 y1)))) /\ (((~ (nadd_eq x0 x1)) \/ (~ (nadd_eq y0 y1))) \/ ((~ (nadd_le x0 y0)) \/ (nadd_le x1 y1))).
Definition term285 := forall y0 : nadd, forall y1 : nadd, (forall y2 : nadd, ~ (nadd_le (nadd_add y0 y2) (nadd_add y1 y2))) \/ (nadd_le y0 y1).
Definition term280 := forall y0 : nadd, forall y1 : nadd, (forall y2 : nadd, nadd_le (nadd_add y0 y2) (nadd_add y1 y2)) \/ (~ (nadd_le y0 y1)).
Definition term175 := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, ((nadd_le (nadd_add y0 y2) (nadd_add y1 y2)) \/ (~ (nadd_le y0 y1))) /\ ((~ (nadd_le (nadd_add y0 y2) (nadd_add y1 y2))) \/ (nadd_le y0 y1)).
Definition term173 (x0 : nadd) := forall y0 : nadd, forall y1 : nadd, ((nadd_le (nadd_add x0 y1) (nadd_add y0 y1)) \/ (~ (nadd_le x0 y0))) /\ ((~ (nadd_le (nadd_add x0 y1) (nadd_add y0 y1))) \/ (nadd_le x0 y0)).
Definition term168 := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((~ (nadd_eq y0 y1)) \/ (~ (nadd_eq y2 y3))) \/ (((nadd_le y0 y2) \/ (~ (nadd_le y1 y3))) /\ ((~ (nadd_le y0 y2)) \/ (nadd_le y1 y3))).
Definition term166 (x0 : nadd) := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, ((~ (nadd_eq x0 y0)) \/ (~ (nadd_eq y1 y2))) \/ (((nadd_le x0 y1) \/ (~ (nadd_le y0 y2))) /\ ((~ (nadd_le x0 y1)) \/ (nadd_le y0 y2))).
Definition term164 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, forall y1 : nadd, ((~ (nadd_eq x0 x1)) \/ (~ (nadd_eq y0 y1))) \/ (((nadd_le x0 y0) \/ (~ (nadd_le x1 y1))) /\ ((~ (nadd_le x0 y0)) \/ (nadd_le x1 y1))).
Definition term50 (x0 : nadd) := forall y0 : nadd, forall y1 : nadd, (nadd_le (nadd_add x0 y0) (nadd_add x0 y1)) = (nadd_le y0 y1).
Definition term45 := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y2 y3)) -> (nadd_le y0 y2) = (nadd_le y1 y3).
Definition term43 (x0 : nadd) := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, ((nadd_eq x0 y0) /\ (nadd_eq y1 y2)) -> (nadd_le x0 y1) = (nadd_le y0 y2).
Definition term41 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, forall y1 : nadd, ((nadd_eq x0 x1) /\ (nadd_eq y0 y1)) -> (nadd_le x0 y0) = (nadd_le x1 y1).
Definition term36 := forall y0 : nadd, forall y1 : nadd, nadd_eq (nadd_add y0 y1) (nadd_add y1 y0).
Definition term30 (x0 : nadd) := forall y0 : nadd, forall y1 : nadd, (nadd_le (nadd_add x0 y1) (nadd_add y0 y1)) = (nadd_le x0 y0).
Definition term17 := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le (nadd_add y0 y2) (nadd_add y1 y2)) = (nadd_le y0 y1).
Definition term8 := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le (nadd_add y0 y1) (nadd_add y0 y2)) = (nadd_le y1 y2).
Definition term27 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => (nadd_le (nadd_add x0 y0) (nadd_add x1 y0)) = (nadd_le x0 x1).
Definition term7 (x0 : Prop) := (~ x0) -> False.
Definition term37 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := ((nadd_eq x0 x2) /\ (nadd_eq x1 x3)) -> (nadd_le x0 x1) = (nadd_le x2 x3).
Definition term373 (x0 : nadd) (x1 : nadd) := imp (nadd_le x0 x1).
Definition term371 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (~ (~ (nadd_le x0 x1))) -> nadd_le (nadd_add x0 x2) (nadd_add x1 x2).
Definition term99 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => (fun y1 : nadd => (~ (nadd_le (nadd_add x0 x1) (nadd_add x0 y1))) /\ (nadd_le x1 y1)) y0.
Definition term213 (x0 : nadd) (x1 : nadd) (x2 : nadd) := or (nadd_le (nadd_add x0 x2) (nadd_add x1 x2)).
Definition term60 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => ~ ((fun y1 : nadd => (nadd_le (nadd_add x0 x1) (nadd_add x0 y1)) = (nadd_le x1 y1)) y0).
Definition term356 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (nadd_eq (nadd_add x1 x2) (nadd_add x2 x1)) /\ (nadd_le (nadd_add x1 x0) (nadd_add x1 x2)).
Definition term160 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (nadd_eq x0 x1) /\ (nadd_eq x2 x3).
Definition term275 := fun y0 : nadd => ((fun y1 : nadd => forall y2 : nadd, (forall y3 : nadd, nadd_le (nadd_add y1 y3) (nadd_add y2 y3)) \/ (~ (nadd_le y1 y2))) y0) /\ ((fun y1 : nadd => forall y2 : nadd, (forall y3 : nadd, ~ (nadd_le (nadd_add y1 y3) (nadd_add y2 y3))) \/ (nadd_le y1 y2)) y0).
Definition term357 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (nadd_eq (nadd_add x1 x0) (nadd_add x0 x1)) /\ ((nadd_eq (nadd_add x1 x2) (nadd_add x2 x1)) /\ (nadd_le (nadd_add x1 x0) (nadd_add x1 x2))).
Definition term322 (x0 : nadd) (x1 : nadd) := ~ (nadd_eq x0 x1).
Definition term337 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term211 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (fun y0 : nadd => nadd_le (nadd_add x0 y0) (nadd_add x1 y0)) x2.
Definition term375 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (nadd_eq (nadd_add x1 x2) (nadd_add x2 x1)) /\ (nadd_le (nadd_add x0 x2) (nadd_add x1 x2)).
Definition term218 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => (fun y1 : nadd => nadd_le (nadd_add x0 y1) (nadd_add x1 y1)) y0.
Definition term182 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => (nadd_le (nadd_add x0 y0) (nadd_add x1 y0)) \/ (~ (nadd_le x0 x1)).
Definition term186 (x0 : nadd) (x1 : nadd) (x2 : nadd) := and ((fun y0 : nadd => (nadd_le (nadd_add x0 y0) (nadd_add x1 y0)) \/ (~ (nadd_le x0 x1))) x2).
Definition term58 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (fun y0 : nadd => (nadd_le (nadd_add x0 x1) (nadd_add x0 y0)) = (nadd_le x1 y0)) x2.
Definition term110 (x0 : nadd) (x1 : nadd) := or ((fun y0 : nadd => exists y1 : nadd, (nadd_le (nadd_add x0 y0) (nadd_add x0 y1)) /\ (~ (nadd_le y0 y1))) x1).
Definition term290 (x0 : nadd) (x1 : nadd) (x2 : nadd) := fun y0 : nadd => (((~ (nadd_eq x0 x2)) \/ (~ (nadd_eq x1 y0))) \/ ((nadd_le x0 x1) \/ (~ (nadd_le x2 y0)))) /\ (((~ (nadd_eq x0 x2)) \/ (~ (nadd_eq x1 y0))) \/ ((~ (nadd_le x0 x1)) \/ (nadd_le x2 y0))).
Definition term326 (x0 : Prop) := (~ x0) -> x0.
Definition term368 (x0 : nadd) (x1 : nadd) := (~ (nadd_le x0 x1)) -> nadd_le x0 x1.
Definition term158 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (~ ((nadd_eq x0 x2) /\ (nadd_eq x1 x3))) \/ ((nadd_le x0 x1) = (nadd_le x2 x3)).
Definition term324 (x0 : nadd) (x1 : nadd) := (~ (nadd_eq (nadd_add x1 x0) (nadd_add x0 x1))) -> nadd_eq (nadd_add x1 x0) (nadd_add x0 x1).
Definition term185 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (nadd_le (nadd_add x1 x0) (nadd_add x2 x0)) \/ (~ (nadd_le x1 x2)).
Definition term134 (x0 : nadd) := ((fun y0 : nadd => exists y1 : nadd, exists y2 : nadd, (nadd_le (nadd_add y0 y1) (nadd_add y0 y2)) /\ (~ (nadd_le y1 y2))) x0) \/ ((fun y0 : nadd => exists y1 : nadd, exists y2 : nadd, (~ (nadd_le (nadd_add y0 y1) (nadd_add y0 y2))) /\ (nadd_le y1 y2)) x0).
Definition term341 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term224 (x0 : nadd) (x1 : nadd) := and ((forall y0 : nadd, nadd_le (nadd_add x0 y0) (nadd_add x1 y0)) \/ (~ (nadd_le x0 x1))).
Definition term265 := fun y0 : nadd => (forall y1 : nadd, (forall y2 : nadd, nadd_le (nadd_add y0 y2) (nadd_add y1 y2)) \/ (~ (nadd_le y0 y1))) /\ (forall y1 : nadd, (forall y2 : nadd, ~ (nadd_le (nadd_add y0 y2) (nadd_add y1 y2))) \/ (nadd_le y0 y1)).
Definition term261 (x0 : nadd) := fun y0 : nadd => (fun y1 : nadd => (forall y2 : nadd, ~ (nadd_le (nadd_add x0 y2) (nadd_add y1 y2))) \/ (nadd_le x0 y1)) y0.
Definition term199 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => (fun y1 : nadd => (~ (nadd_le (nadd_add x0 y1) (nadd_add x1 y1))) \/ (nadd_le x0 x1)) y0.
Definition term334 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (~ (nadd_eq x2 x0)) \/ (~ (nadd_le x1 x2)).
Definition term22 := (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y2 y3)) -> (nadd_le y0 y2) = (nadd_le y1 y3)) -> (forall y0 : nadd, forall y1 : nadd, nadd_eq (nadd_add y0 y1) (nadd_add y1 y0)) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le (nadd_add y0 y2) (nadd_add y1 y2)) = (nadd_le y0 y1)) -> False.
Definition term374 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (nadd_le x0 x1) -> nadd_le (nadd_add x0 x2) (nadd_add x1 x2).
Definition term85 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (nadd_le (nadd_add x0 x1) (nadd_add x0 x2)) /\ (~ (nadd_le x1 x2)).
Definition term177 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term19 := (forall y0 : nadd, forall y1 : nadd, nadd_eq (nadd_add y0 y1) (nadd_add y1 y0)) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le (nadd_add y0 y2) (nadd_add y1 y2)) = (nadd_le y0 y1)) -> False.
Definition term204 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (forall y0 : a0, x0 y0) \/ x1.
Definition term249 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (forall y1 : nadd, nadd_le (nadd_add x0 y1) (nadd_add y0 y1)) \/ (~ (nadd_le x0 y0))) x1.
Definition term144 := exists y0 : nadd, (fun y1 : nadd => exists y2 : nadd, exists y3 : nadd, (~ (nadd_le (nadd_add y1 y2) (nadd_add y1 y3))) /\ (nadd_le y2 y3)) y0.
Definition term139 := exists y0 : nadd, (fun y1 : nadd => exists y2 : nadd, exists y3 : nadd, (nadd_le (nadd_add y1 y2) (nadd_add y1 y3)) /\ (~ (nadd_le y2 y3))) y0.
Definition term122 (x0 : nadd) := exists y0 : nadd, (fun y1 : nadd => exists y2 : nadd, (~ (nadd_le (nadd_add x0 y1) (nadd_add x0 y2))) /\ (nadd_le y1 y2)) y0.
Definition term117 (x0 : nadd) := exists y0 : nadd, (fun y1 : nadd => exists y2 : nadd, (nadd_le (nadd_add x0 y1) (nadd_add x0 y2)) /\ (~ (nadd_le y1 y2))) y0.
Definition term376 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (nadd_eq (nadd_add x0 x2) (nadd_add x2 x0)) /\ ((nadd_eq (nadd_add x1 x2) (nadd_add x2 x1)) /\ (nadd_le (nadd_add x0 x2) (nadd_add x1 x2))).
Definition term128 := (exists y0 : nadd, (fun y1 : nadd => exists y2 : nadd, exists y3 : nadd, (nadd_le (nadd_add y1 y2) (nadd_add y1 y3)) /\ (~ (nadd_le y2 y3))) y0) \/ (exists y0 : nadd, (fun y1 : nadd => exists y2 : nadd, exists y3 : nadd, (~ (nadd_le (nadd_add y1 y2) (nadd_add y1 y3))) /\ (nadd_le y2 y3)) y0).
Definition term106 (x0 : nadd) := (exists y0 : nadd, (fun y1 : nadd => exists y2 : nadd, (nadd_le (nadd_add x0 y1) (nadd_add x0 y2)) /\ (~ (nadd_le y1 y2))) y0) \/ (exists y0 : nadd, (fun y1 : nadd => exists y2 : nadd, (~ (nadd_le (nadd_add x0 y1) (nadd_add x0 y2))) /\ (nadd_le y1 y2)) y0).
Definition term81 (x0 : nadd) (x1 : nadd) := (exists y0 : nadd, (fun y1 : nadd => (nadd_le (nadd_add x0 x1) (nadd_add x0 y1)) /\ (~ (nadd_le x1 y1))) y0) \/ (exists y0 : nadd, (fun y1 : nadd => (~ (nadd_le (nadd_add x0 x1) (nadd_add x0 y1))) /\ (nadd_le x1 y1)) y0).
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term141 := or (exists y0 : nadd, (fun y1 : nadd => exists y2 : nadd, exists y3 : nadd, (nadd_le (nadd_add y1 y2) (nadd_add y1 y3)) /\ (~ (nadd_le y2 y3))) y0).
Definition term119 (x0 : nadd) := or (exists y0 : nadd, (fun y1 : nadd => exists y2 : nadd, (nadd_le (nadd_add x0 y1) (nadd_add x0 y2)) /\ (~ (nadd_le y1 y2))) y0).
Definition term97 (x0 : nadd) (x1 : nadd) := or (exists y0 : nadd, (fun y1 : nadd => (nadd_le (nadd_add x0 x1) (nadd_add x0 y1)) /\ (~ (nadd_le x1 y1))) y0).
Definition term350 (x0 : nadd) (x1 : nadd) := ~ (~ (nadd_le x0 x1)).
Definition term101 (x0 : nadd) (x1 : nadd) := exists y0 : nadd, (~ (nadd_le (nadd_add x0 x1) (nadd_add x0 y0))) /\ (nadd_le x1 y0).
Definition term227 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => ~ (nadd_le (nadd_add x0 y0) (nadd_add x1 y0)).
Definition term70 := exists y0 : nadd, ~ ((fun y1 : nadd => forall y2 : nadd, forall y3 : nadd, (nadd_le (nadd_add y1 y2) (nadd_add y1 y3)) = (nadd_le y2 y3)) y0).
Definition term64 (x0 : nadd) := exists y0 : nadd, ~ ((fun y1 : nadd => forall y2 : nadd, (nadd_le (nadd_add x0 y1) (nadd_add x0 y2)) = (nadd_le y1 y2)) y0).
Definition term57 (x0 : nadd) (x1 : nadd) := exists y0 : nadd, ~ ((fun y1 : nadd => (nadd_le (nadd_add x0 x1) (nadd_add x0 y1)) = (nadd_le x1 y1)) y0).
Definition term207 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, ((fun y1 : nadd => nadd_le (nadd_add x0 y1) (nadd_add x1 y1)) y0) \/ (~ (nadd_le x0 x1)).
Definition term83 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => (~ (nadd_le (nadd_add x0 x1) (nadd_add x0 y0))) /\ (nadd_le x1 y0).
Definition term133 (x0 : nadd) := (fun y0 : nadd => exists y1 : nadd, exists y2 : nadd, (~ (nadd_le (nadd_add y0 y1) (nadd_add y0 y2))) /\ (nadd_le y1 y2)) x0.
Definition term131 (x0 : nadd) := (fun y0 : nadd => exists y1 : nadd, exists y2 : nadd, (nadd_le (nadd_add y0 y1) (nadd_add y0 y2)) /\ (~ (nadd_le y1 y2))) x0.
Definition term338 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (~ ((~ (nadd_eq x0 x2)) \/ ((~ (nadd_eq x1 x3)) \/ (~ (nadd_le x0 x1))))) -> nadd_le x2 x3.
Definition term237 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, (fun y1 : nadd => ~ (nadd_le (nadd_add x0 y1) (nadd_add x1 y1))) y0.
Definition term311 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, (((~ (nadd_eq x0 y0)) \/ (~ (nadd_eq y1 y2))) \/ ((nadd_le x0 y1) \/ (~ (nadd_le y0 y2)))) /\ (((~ (nadd_eq x0 y0)) \/ (~ (nadd_eq y1 y2))) \/ ((~ (nadd_le x0 y1)) \/ (nadd_le y0 y2)))) x1.
Definition term88 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (fun y0 : nadd => (~ (nadd_le (nadd_add x0 x1) (nadd_add x0 y0))) /\ (nadd_le x1 y0)) x2.
Definition term248 (x0 : nadd) := fun y0 : nadd => (forall y1 : nadd, ~ (nadd_le (nadd_add x0 y1) (nadd_add y0 y1))) \/ (nadd_le x0 y0).
Definition term354 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := imp ((nadd_eq x2 x0) /\ ((nadd_eq x3 x1) /\ (nadd_le x2 x3))).
Definition term146 := (exists y0 : nadd, exists y1 : nadd, exists y2 : nadd, (nadd_le (nadd_add y0 y1) (nadd_add y0 y2)) /\ (~ (nadd_le y1 y2))) \/ (exists y0 : nadd, exists y1 : nadd, exists y2 : nadd, (~ (nadd_le (nadd_add y0 y1) (nadd_add y0 y2))) /\ (nadd_le y1 y2)).
Definition term124 (x0 : nadd) := (exists y0 : nadd, exists y1 : nadd, (nadd_le (nadd_add x0 y0) (nadd_add x0 y1)) /\ (~ (nadd_le y0 y1))) \/ (exists y0 : nadd, exists y1 : nadd, (~ (nadd_le (nadd_add x0 y0) (nadd_add x0 y1))) /\ (nadd_le y0 y1)).
Definition term53 (x0 : nadd) (x1 : nadd) (x2 : nadd) := ((nadd_le (nadd_add x0 x1) (nadd_add x0 x2)) /\ (~ (nadd_le x1 x2))) \/ ((~ (nadd_le (nadd_add x0 x1) (nadd_add x0 x2))) /\ (nadd_le x1 x2)).
Definition term73 := fun y0 : nadd => ~ ((fun y1 : nadd => forall y2 : nadd, forall y3 : nadd, (nadd_le (nadd_add y1 y2) (nadd_add y1 y3)) = (nadd_le y2 y3)) y0).
Definition term67 (x0 : nadd) := fun y0 : nadd => ~ ((fun y1 : nadd => forall y2 : nadd, (nadd_le (nadd_add x0 y1) (nadd_add x0 y2)) = (nadd_le y1 y2)) y0).
Definition term363 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (~ (~ (nadd_le (nadd_add x1 x0) (nadd_add x2 x0)))) -> nadd_le x1 x2.
Definition term267 := forall y0 : nadd, ((fun y1 : nadd => forall y2 : nadd, (forall y3 : nadd, nadd_le (nadd_add y1 y3) (nadd_add y2 y3)) \/ (~ (nadd_le y1 y2))) y0) /\ ((fun y1 : nadd => forall y2 : nadd, (forall y3 : nadd, ~ (nadd_le (nadd_add y1 y3) (nadd_add y2 y3))) \/ (nadd_le y1 y2)) y0).
Definition term245 (x0 : nadd) := forall y0 : nadd, ((fun y1 : nadd => (forall y2 : nadd, nadd_le (nadd_add x0 y2) (nadd_add y1 y2)) \/ (~ (nadd_le x0 y1))) y0) /\ ((fun y1 : nadd => (forall y2 : nadd, ~ (nadd_le (nadd_add x0 y2) (nadd_add y1 y2))) \/ (nadd_le x0 y1)) y0).
Definition term180 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, ((fun y1 : nadd => (nadd_le (nadd_add x0 y1) (nadd_add x1 y1)) \/ (~ (nadd_le x0 x1))) y0) /\ ((fun y1 : nadd => (~ (nadd_le (nadd_add x0 y1) (nadd_add x1 y1))) \/ (nadd_le x0 x1)) y0).
Definition term240 (x0 : nadd) (x1 : nadd) := or (forall y0 : nadd, ~ (nadd_le (nadd_add x0 y0) (nadd_add x1 y0))).
Definition term111 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => exists y1 : nadd, (~ (nadd_le (nadd_add x0 y0) (nadd_add x0 y1))) /\ (nadd_le y0 y1)) x1.
Definition term109 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => exists y1 : nadd, (nadd_le (nadd_add x0 y0) (nadd_add x0 y1)) /\ (~ (nadd_le y0 y1))) x1.
Definition term59 (x0 : nadd) (x1 : nadd) (x2 : nadd) := ~ ((fun y0 : nadd => (nadd_le (nadd_add x0 x1) (nadd_add x0 y0)) = (nadd_le x1 y0)) x2).
Definition term107 (x0 : nadd) := fun y0 : nadd => exists y1 : nadd, (nadd_le (nadd_add x0 y0) (nadd_add x0 y1)) /\ (~ (nadd_le y0 y1)).
Definition term364 (x0 : nadd) (x1 : nadd) (x2 : nadd) := ~ (~ (nadd_le (nadd_add x0 x2) (nadd_add x1 x2))).
Definition term377 (x0 : nadd) (x1 : nadd) (x2 : nadd) := ((nadd_eq (nadd_add x0 x1) (nadd_add x1 x0)) /\ ((nadd_eq (nadd_add x2 x1) (nadd_add x1 x2)) /\ (nadd_le (nadd_add x0 x1) (nadd_add x2 x1)))) -> nadd_le (nadd_add x1 x0) (nadd_add x1 x2).
Definition term201 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, (~ (nadd_le (nadd_add x0 y0) (nadd_add x1 y0))) \/ (nadd_le x0 x1).
Definition term84 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (fun y0 : nadd => (nadd_le (nadd_add x0 x1) (nadd_add x0 y0)) /\ (~ (nadd_le x1 y0))) x2.
Definition term34 (x0 : nadd) := forall y0 : nadd, nadd_eq (nadd_add x0 y0) (nadd_add y0 x0).
Definition term15 := (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le (nadd_add y0 y2) (nadd_add y1 y2)) = (nadd_le y0 y1)) -> False.
Definition term288 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (nadd_le x0 x1) \/ (~ (nadd_le x2 x3)).
Definition term272 (x0 : nadd) := and ((fun y0 : nadd => forall y1 : nadd, (forall y2 : nadd, nadd_le (nadd_add y0 y2) (nadd_add y1 y2)) \/ (~ (nadd_le y0 y1))) x0).
Definition term209 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => nadd_le (nadd_add x0 y0) (nadd_add x1 y0).
Definition term332 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (~ (nadd_eq x2 x0)) \/ ((nadd_le x0 x1) \/ ((~ (nadd_eq x3 x1)) \/ (~ (nadd_le x2 x3)))).
Definition term262 (x0 : nadd) := forall y0 : nadd, (fun y1 : nadd => (forall y2 : nadd, ~ (nadd_le (nadd_add x0 y2) (nadd_add y1 y2))) \/ (nadd_le x0 y1)) y0.
Definition term257 (x0 : nadd) := forall y0 : nadd, (fun y1 : nadd => (forall y2 : nadd, nadd_le (nadd_add x0 y2) (nadd_add y1 y2)) \/ (~ (nadd_le x0 y1))) y0.
Definition term219 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, (fun y1 : nadd => nadd_le (nadd_add x0 y1) (nadd_add x1 y1)) y0.
Definition term200 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, (fun y1 : nadd => (~ (nadd_le (nadd_add x0 y1) (nadd_add x1 y1))) \/ (nadd_le x0 x1)) y0.
Definition term195 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, (fun y1 : nadd => (nadd_le (nadd_add x0 y1) (nadd_add x1 y1)) \/ (~ (nadd_le x0 x1))) y0.
Definition term228 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (fun y0 : nadd => ~ (nadd_le (nadd_add x0 y0) (nadd_add x1 y0))) x2.
Definition term14 := (((~ (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le (nadd_add y0 y1) (nadd_add y0 y2)) = (nadd_le y1 y2))) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y2 y3)) -> (nadd_le y0 y2) = (nadd_le y1 y3)) -> (forall y0 : nadd, forall y1 : nadd, nadd_eq (nadd_add y0 y1) (nadd_add y1 y0)) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le (nadd_add y0 y2) (nadd_add y1 y2)) = (nadd_le y0 y1)) -> False) -> (~ (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le (nadd_add y0 y1) (nadd_add y0 y2)) = (nadd_le y1 y2))) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y2 y3)) -> (nadd_le y0 y2) = (nadd_le y1 y3)) -> (forall y0 : nadd, forall y1 : nadd, nadd_eq (nadd_add y0 y1) (nadd_add y1 y0)) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le (nadd_add y0 y2) (nadd_add y1 y2)) = (nadd_le y0 y1)) -> False) -> ((~ (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le (nadd_add y0 y1) (nadd_add y0 y2)) = (nadd_le y1 y2))) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y2 y3)) -> (nadd_le y0 y2) = (nadd_le y1 y3)) -> (forall y0 : nadd, forall y1 : nadd, nadd_eq (nadd_add y0 y1) (nadd_add y1 y0)) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le (nadd_add y0 y2) (nadd_add y1 y2)) = (nadd_le y0 y1)) -> False) -> (~ (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le (nadd_add y0 y1) (nadd_add y0 y2)) = (nadd_le y1 y2))) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y2 y3)) -> (nadd_le y0 y2) = (nadd_le y1 y3)) -> (forall y0 : nadd, forall y1 : nadd, nadd_eq (nadd_add y0 y1) (nadd_add y1 y0)) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le (nadd_add y0 y2) (nadd_add y1 y2)) = (nadd_le y0 y1)) -> False.
Definition term62 (x0 : nadd) (x1 : nadd) := exists y0 : nadd, ((nadd_le (nadd_add x0 x1) (nadd_add x0 y0)) /\ (~ (nadd_le x1 y0))) \/ ((~ (nadd_le (nadd_add x0 x1) (nadd_add x0 y0))) /\ (nadd_le x1 y0)).
Definition term205 (x0 : nadd -> Prop) (x1 : Prop) := forall y0 : nadd, (x0 y0) \/ x1.
Definition term89 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (~ (nadd_le (nadd_add x0 x1) (nadd_add x0 x2))) /\ (nadd_le x1 x2).
Definition term12 := ((~ (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le (nadd_add y0 y1) (nadd_add y0 y2)) = (nadd_le y1 y2))) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y2 y3)) -> (nadd_le y0 y2) = (nadd_le y1 y3)) -> (forall y0 : nadd, forall y1 : nadd, nadd_eq (nadd_add y0 y1) (nadd_add y1 y0)) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le (nadd_add y0 y2) (nadd_add y1 y2)) = (nadd_le y0 y1)) -> False) -> (~ (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le (nadd_add y0 y1) (nadd_add y0 y2)) = (nadd_le y1 y2))) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y2 y3)) -> (nadd_le y0 y2) = (nadd_le y1 y3)) -> (forall y0 : nadd, forall y1 : nadd, nadd_eq (nadd_add y0 y1) (nadd_add y1 y0)) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le (nadd_add y0 y2) (nadd_add y1 y2)) = (nadd_le y0 y1)) -> False.
Definition term187 (x0 : nadd) (x1 : nadd) (x2 : nadd) := and ((nadd_le (nadd_add x1 x0) (nadd_add x2 x0)) \/ (~ (nadd_le x1 x2))).
Definition term137 := @eq Prop (exists y0 : nadd, (exists y1 : nadd, exists y2 : nadd, (nadd_le (nadd_add y0 y1) (nadd_add y0 y2)) /\ (~ (nadd_le y1 y2))) \/ (exists y1 : nadd, exists y2 : nadd, (~ (nadd_le (nadd_add y0 y1) (nadd_add y0 y2))) /\ (nadd_le y1 y2))).
Definition term136 := @eq Prop (exists y0 : nadd, ((fun y1 : nadd => exists y2 : nadd, exists y3 : nadd, (nadd_le (nadd_add y1 y2) (nadd_add y1 y3)) /\ (~ (nadd_le y2 y3))) y0) \/ ((fun y1 : nadd => exists y2 : nadd, exists y3 : nadd, (~ (nadd_le (nadd_add y1 y2) (nadd_add y1 y3))) /\ (nadd_le y2 y3)) y0)).
Definition term115 (x0 : nadd) := @eq Prop (exists y0 : nadd, (exists y1 : nadd, (nadd_le (nadd_add x0 y0) (nadd_add x0 y1)) /\ (~ (nadd_le y0 y1))) \/ (exists y1 : nadd, (~ (nadd_le (nadd_add x0 y0) (nadd_add x0 y1))) /\ (nadd_le y0 y1))).
Definition term114 (x0 : nadd) := @eq Prop (exists y0 : nadd, ((fun y1 : nadd => exists y2 : nadd, (nadd_le (nadd_add x0 y1) (nadd_add x0 y2)) /\ (~ (nadd_le y1 y2))) y0) \/ ((fun y1 : nadd => exists y2 : nadd, (~ (nadd_le (nadd_add x0 y1) (nadd_add x0 y2))) /\ (nadd_le y1 y2)) y0)).
Definition term93 (x0 : nadd) (x1 : nadd) := @eq Prop (exists y0 : nadd, ((nadd_le (nadd_add x0 x1) (nadd_add x0 y0)) /\ (~ (nadd_le x1 y0))) \/ ((~ (nadd_le (nadd_add x0 x1) (nadd_add x0 y0))) /\ (nadd_le x1 y0))).
Definition term92 (x0 : nadd) (x1 : nadd) := @eq Prop (exists y0 : nadd, ((fun y1 : nadd => (nadd_le (nadd_add x0 x1) (nadd_add x0 y1)) /\ (~ (nadd_le x1 y1))) y0) \/ ((fun y1 : nadd => (~ (nadd_le (nadd_add x0 x1) (nadd_add x0 y1))) /\ (nadd_le x1 y1)) y0)).
Definition term132 (x0 : nadd) := or ((fun y0 : nadd => exists y1 : nadd, exists y2 : nadd, (nadd_le (nadd_add y0 y1) (nadd_add y0 y2)) /\ (~ (nadd_le y1 y2))) x0).
Definition term365 (x0 : nadd) (x1 : nadd) (x2 : nadd) := imp (~ (~ (nadd_le (nadd_add x0 x2) (nadd_add x1 x2)))).
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term188 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (fun y0 : nadd => (~ (nadd_le (nadd_add x0 y0) (nadd_add x1 y0))) \/ (nadd_le x0 x1)) x2.
Definition term330 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (~ (nadd_eq x3 x1)) \/ ((nadd_le x0 x1) \/ (~ (nadd_le x2 x3))).
Definition term155 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := ((nadd_le x0 x1) \/ (~ (nadd_le x2 x3))) /\ ((~ (nadd_le x0 x1)) \/ (nadd_le x2 x3)).
Definition term336 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := @eq Prop ((nadd_le x0 x1) \/ ((~ (nadd_eq x2 x0)) \/ ((~ (nadd_eq x3 x1)) \/ (~ (nadd_le x2 x3))))).
Definition term126 := exists y0 : nadd, (exists y1 : nadd, exists y2 : nadd, (nadd_le (nadd_add y0 y1) (nadd_add y0 y2)) /\ (~ (nadd_le y1 y2))) \/ (exists y1 : nadd, exists y2 : nadd, (~ (nadd_le (nadd_add y0 y1) (nadd_add y0 y2))) /\ (nadd_le y1 y2)).
Definition term104 (x0 : nadd) := exists y0 : nadd, (exists y1 : nadd, (nadd_le (nadd_add x0 y0) (nadd_add x0 y1)) /\ (~ (nadd_le y0 y1))) \/ (exists y1 : nadd, (~ (nadd_le (nadd_add x0 y0) (nadd_add x0 y1))) /\ (nadd_le y0 y1)).
Definition term358 (x0 : nadd) (x1 : nadd) (x2 : nadd) := ((nadd_eq (nadd_add x2 x0) (nadd_add x0 x2)) /\ ((nadd_eq (nadd_add x2 x1) (nadd_add x1 x2)) /\ (nadd_le (nadd_add x2 x0) (nadd_add x2 x1)))) -> nadd_le (nadd_add x0 x2) (nadd_add x1 x2).
Definition term232 (x0 : nadd) (x1 : nadd) (x2 : nadd) := ((fun y0 : nadd => ~ (nadd_le (nadd_add x1 y0) (nadd_add x2 y0))) x0) \/ (nadd_le x1 x2).
Definition term56 (x0 : nadd) (x1 : nadd) := ~ (forall y0 : nadd, (nadd_le (nadd_add x0 x1) (nadd_add x0 y0)) = (nadd_le x1 y0)).
Definition term143 := fun y0 : nadd => (fun y1 : nadd => exists y2 : nadd, exists y3 : nadd, (~ (nadd_le (nadd_add y1 y2) (nadd_add y1 y3))) /\ (nadd_le y2 y3)) y0.
Definition term138 := fun y0 : nadd => (fun y1 : nadd => exists y2 : nadd, exists y3 : nadd, (nadd_le (nadd_add y1 y2) (nadd_add y1 y3)) /\ (~ (nadd_le y2 y3))) y0.
Definition term121 (x0 : nadd) := fun y0 : nadd => (fun y1 : nadd => exists y2 : nadd, (~ (nadd_le (nadd_add x0 y1) (nadd_add x0 y2))) /\ (nadd_le y1 y2)) y0.
Definition term116 (x0 : nadd) := fun y0 : nadd => (fun y1 : nadd => exists y2 : nadd, (nadd_le (nadd_add x0 y1) (nadd_add x0 y2)) /\ (~ (nadd_le y1 y2))) y0.
Definition term369 (x0 : nadd) (x1 : nadd) := (nadd_le x0 x1) -> False.
Definition term318 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, (nadd_le (nadd_add y0 y2) (nadd_add y1 y2)) \/ (~ (nadd_le y0 y1))) x0.
Definition term316 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, (~ (nadd_le (nadd_add y0 y2) (nadd_add y1 y2))) \/ (nadd_le y0 y1)) x0.
Definition term310 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, (((~ (nadd_eq y0 y1)) \/ (~ (nadd_eq y2 y3))) \/ ((nadd_le y0 y2) \/ (~ (nadd_le y1 y3)))) /\ (((~ (nadd_eq y0 y1)) \/ (~ (nadd_eq y2 y3))) \/ ((~ (nadd_le y0 y2)) \/ (nadd_le y1 y3)))) x0.
Definition term71 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, (nadd_le (nadd_add y0 y1) (nadd_add y0 y2)) = (nadd_le y1 y2)) x0.
Definition term108 (x0 : nadd) := fun y0 : nadd => exists y1 : nadd, (~ (nadd_le (nadd_add x0 y0) (nadd_add x0 y1))) /\ (nadd_le y0 y1).
Definition term340 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term28 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, (nadd_le (nadd_add x0 y0) (nadd_add x1 y0)) = (nadd_le x0 x1).
Definition term21 := imp (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y2 y3)) -> (nadd_le y0 y2) = (nadd_le y1 y3)).
Definition term18 := imp (forall y0 : nadd, forall y1 : nadd, nadd_eq (nadd_add y0 y1) (nadd_add y1 y0)).
Definition term82 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => (nadd_le (nadd_add x0 x1) (nadd_add x0 y0)) /\ (~ (nadd_le x1 y0)).
Definition term308 := fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, (nadd_le (nadd_add y0 y2) (nadd_add y1 y2)) \/ (~ (nadd_le y0 y1)).
Definition term302 := fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, (~ (nadd_le (nadd_add y0 y2) (nadd_add y1 y2))) \/ (nadd_le y0 y1).
Definition term296 := fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, (((~ (nadd_eq y0 y1)) \/ (~ (nadd_eq y2 y3))) \/ ((nadd_le y0 y2) \/ (~ (nadd_le y1 y3)))) /\ (((~ (nadd_eq y0 y1)) \/ (~ (nadd_eq y2 y3))) \/ ((~ (nadd_le y0 y2)) \/ (nadd_le y1 y3))).
Definition term294 (x0 : nadd) := fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, (((~ (nadd_eq x0 y0)) \/ (~ (nadd_eq y1 y2))) \/ ((nadd_le x0 y1) \/ (~ (nadd_le y0 y2)))) /\ (((~ (nadd_eq x0 y0)) \/ (~ (nadd_eq y1 y2))) \/ ((~ (nadd_le x0 y1)) \/ (nadd_le y0 y2))).
Definition term174 := fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, ((nadd_le (nadd_add y0 y2) (nadd_add y1 y2)) \/ (~ (nadd_le y0 y1))) /\ ((~ (nadd_le (nadd_add y0 y2) (nadd_add y1 y2))) \/ (nadd_le y0 y1)).
Definition term167 := fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((~ (nadd_eq y0 y1)) \/ (~ (nadd_eq y2 y3))) \/ (((nadd_le y0 y2) \/ (~ (nadd_le y1 y3))) /\ ((~ (nadd_le y0 y2)) \/ (nadd_le y1 y3))).
Definition term165 (x0 : nadd) := fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, ((~ (nadd_eq x0 y0)) \/ (~ (nadd_eq y1 y2))) \/ (((nadd_le x0 y1) \/ (~ (nadd_le y0 y2))) /\ ((~ (nadd_le x0 y1)) \/ (nadd_le y0 y2))).
Definition term51 := fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, (nadd_le (nadd_add y0 y1) (nadd_add y0 y2)) = (nadd_le y1 y2).
Definition term44 := fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y2 y3)) -> (nadd_le y0 y2) = (nadd_le y1 y3).
Definition term42 (x0 : nadd) := fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, ((nadd_eq x0 y0) /\ (nadd_eq y1 y2)) -> (nadd_le x0 y1) = (nadd_le y0 y2).
Definition term31 := fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, (nadd_le (nadd_add y0 y2) (nadd_add y1 y2)) = (nadd_le y0 y1).
Definition term206 (x0 : nadd -> Prop) (x1 : Prop) := (forall y0 : nadd, x0 y0) \/ x1.
Definition term329 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (~ (nadd_eq x1 x3)) \/ ((~ (nadd_le x0 x1)) \/ (nadd_le x2 x3)).
Definition term220 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, nadd_le (nadd_add x0 y0) (nadd_add x1 y0).
Definition term13 := (((~ (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le (nadd_add y0 y1) (nadd_add y0 y2)) = (nadd_le y1 y2))) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y2 y3)) -> (nadd_le y0 y2) = (nadd_le y1 y3)) -> (forall y0 : nadd, forall y1 : nadd, nadd_eq (nadd_add y0 y1) (nadd_add y1 y0)) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le (nadd_add y0 y2) (nadd_add y1 y2)) = (nadd_le y0 y1)) -> False) -> (~ (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le (nadd_add y0 y1) (nadd_add y0 y2)) = (nadd_le y1 y2))) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y2 y3)) -> (nadd_le y0 y2) = (nadd_le y1 y3)) -> (forall y0 : nadd, forall y1 : nadd, nadd_eq (nadd_add y0 y1) (nadd_add y1 y0)) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le (nadd_add y0 y2) (nadd_add y1 y2)) = (nadd_le y0 y1)) -> False) -> (~ (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le (nadd_add y0 y1) (nadd_add y0 y2)) = (nadd_le y1 y2))) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y2 y3)) -> (nadd_le y0 y2) = (nadd_le y1 y3)) -> (forall y0 : nadd, forall y1 : nadd, nadd_eq (nadd_add y0 y1) (nadd_add y1 y0)) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le (nadd_add y0 y2) (nadd_add y1 y2)) = (nadd_le y0 y1)) -> False.
Definition term367 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (nadd_le (nadd_add x1 x0) (nadd_add x2 x0)) -> nadd_le x1 x2.
Definition term335 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := @eq Prop ((~ (nadd_eq x0 x2)) \/ ((~ (nadd_eq x1 x3)) \/ ((~ (nadd_le x0 x1)) \/ (nadd_le x2 x3)))).
Definition term291 (x0 : nadd) (x1 : nadd) (x2 : nadd) := forall y0 : nadd, (((~ (nadd_eq x0 x2)) \/ (~ (nadd_eq x1 y0))) \/ ((nadd_le x0 x1) \/ (~ (nadd_le x2 y0)))) /\ (((~ (nadd_eq x0 x2)) \/ (~ (nadd_eq x1 y0))) \/ ((~ (nadd_le x0 x1)) \/ (nadd_le x2 y0))).
Definition term347 (x0 : nadd) (x1 : nadd) := and (nadd_eq x0 x1).
Definition term153 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := ~ ((nadd_eq x0 x1) /\ (nadd_eq x2 x3)).
Definition term362 (x0 : nadd) (x1 : nadd) (x2 : nadd) := @eq Prop ((nadd_le x0 x1) \/ (~ (nadd_le (nadd_add x0 x2) (nadd_add x1 x2)))).
Definition term222 (x0 : nadd) (x1 : nadd) := or (forall y0 : nadd, nadd_le (nadd_add x0 y0) (nadd_add x1 y0)).
Definition term328 (x0 : nadd) (x1 : nadd) := or (~ (nadd_eq x0 x1)).
Definition term212 (x0 : nadd) (x1 : nadd) (x2 : nadd) := or ((fun y0 : nadd => nadd_le (nadd_add x0 y0) (nadd_add x1 y0)) x2).
Definition term86 (x0 : nadd) (x1 : nadd) (x2 : nadd) := or ((fun y0 : nadd => (nadd_le (nadd_add x0 x1) (nadd_add x0 y0)) /\ (~ (nadd_le x1 y0))) x2).
Definition term183 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => (~ (nadd_le (nadd_add x0 y0) (nadd_add x1 y0))) \/ (nadd_le x0 x1).
Definition term312 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (fun y0 : nadd => forall y1 : nadd, (((~ (nadd_eq x0 x1)) \/ (~ (nadd_eq y0 y1))) \/ ((nadd_le x0 y0) \/ (~ (nadd_le x1 y1)))) /\ (((~ (nadd_eq x0 x1)) \/ (~ (nadd_eq y0 y1))) \/ ((~ (nadd_le x0 y0)) \/ (nadd_le x1 y1)))) x2.
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term225 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, ((fun y1 : nadd => ~ (nadd_le (nadd_add x0 y1) (nadd_add x1 y1))) y0) \/ (nadd_le x0 x1).
Definition term231 (x0 : nadd) (x1 : nadd) (x2 : nadd) := or (~ (nadd_le (nadd_add x0 x2) (nadd_add x1 x2))).
Definition term135 := fun y0 : nadd => ((fun y1 : nadd => exists y2 : nadd, exists y3 : nadd, (nadd_le (nadd_add y1 y2) (nadd_add y1 y3)) /\ (~ (nadd_le y2 y3))) y0) \/ ((fun y1 : nadd => exists y2 : nadd, exists y3 : nadd, (~ (nadd_le (nadd_add y1 y2) (nadd_add y1 y3))) /\ (nadd_le y2 y3)) y0).
Definition term113 (x0 : nadd) := fun y0 : nadd => ((fun y1 : nadd => exists y2 : nadd, (nadd_le (nadd_add x0 y1) (nadd_add x0 y2)) /\ (~ (nadd_le y1 y2))) y0) \/ ((fun y1 : nadd => exists y2 : nadd, (~ (nadd_le (nadd_add x0 y1) (nadd_add x0 y2))) /\ (nadd_le y1 y2)) y0).
Definition term61 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => ((nadd_le (nadd_add x0 x1) (nadd_add x0 y0)) /\ (~ (nadd_le x1 y0))) \/ ((~ (nadd_le (nadd_add x0 x1) (nadd_add x0 y0))) /\ (nadd_le x1 y0)).
Definition term342 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := ~ ((~ (nadd_eq x2 x0)) \/ ((~ (nadd_eq x3 x1)) \/ (~ (nadd_le x2 x3)))).
Definition term223 (x0 : nadd) (x1 : nadd) := (forall y0 : nadd, nadd_le (nadd_add x0 y0) (nadd_add x1 y0)) \/ (~ (nadd_le x0 x1)).
Definition term157 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := or ((~ (nadd_eq x0 x1)) \/ (~ (nadd_eq x2 x3))).
Definition term258 (x0 : nadd) := forall y0 : nadd, (forall y1 : nadd, nadd_le (nadd_add x0 y1) (nadd_add y0 y1)) \/ (~ (nadd_le x0 y0)).
Definition term9 := (~ (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le (nadd_add y0 y1) (nadd_add y0 y2)) = (nadd_le y1 y2))) -> False.
Definition term277 := @eq Prop (forall y0 : nadd, (forall y1 : nadd, (forall y2 : nadd, nadd_le (nadd_add y0 y2) (nadd_add y1 y2)) \/ (~ (nadd_le y0 y1))) /\ (forall y1 : nadd, (forall y2 : nadd, ~ (nadd_le (nadd_add y0 y2) (nadd_add y1 y2))) \/ (nadd_le y0 y1))).
Definition term276 := @eq Prop (forall y0 : nadd, ((fun y1 : nadd => forall y2 : nadd, (forall y3 : nadd, nadd_le (nadd_add y1 y3) (nadd_add y2 y3)) \/ (~ (nadd_le y1 y2))) y0) /\ ((fun y1 : nadd => forall y2 : nadd, (forall y3 : nadd, ~ (nadd_le (nadd_add y1 y3) (nadd_add y2 y3))) \/ (nadd_le y1 y2)) y0)).
Definition term255 (x0 : nadd) := @eq Prop (forall y0 : nadd, ((forall y1 : nadd, nadd_le (nadd_add x0 y1) (nadd_add y0 y1)) \/ (~ (nadd_le x0 y0))) /\ ((forall y1 : nadd, ~ (nadd_le (nadd_add x0 y1) (nadd_add y0 y1))) \/ (nadd_le x0 y0))).
Definition term254 (x0 : nadd) := @eq Prop (forall y0 : nadd, ((fun y1 : nadd => (forall y2 : nadd, nadd_le (nadd_add x0 y2) (nadd_add y1 y2)) \/ (~ (nadd_le x0 y1))) y0) /\ ((fun y1 : nadd => (forall y2 : nadd, ~ (nadd_le (nadd_add x0 y2) (nadd_add y1 y2))) \/ (nadd_le x0 y1)) y0)).
Definition term235 (x0 : nadd) (x1 : nadd) := @eq Prop (forall y0 : nadd, (~ (nadd_le (nadd_add x0 y0) (nadd_add x1 y0))) \/ (nadd_le x0 x1)).
Definition term234 (x0 : nadd) (x1 : nadd) := @eq Prop (forall y0 : nadd, ((fun y1 : nadd => ~ (nadd_le (nadd_add x0 y1) (nadd_add x1 y1))) y0) \/ (nadd_le x0 x1)).
Definition term217 (x0 : nadd) (x1 : nadd) := @eq Prop (forall y0 : nadd, (nadd_le (nadd_add x0 y0) (nadd_add x1 y0)) \/ (~ (nadd_le x0 x1))).
Definition term216 (x0 : nadd) (x1 : nadd) := @eq Prop (forall y0 : nadd, ((fun y1 : nadd => nadd_le (nadd_add x0 y1) (nadd_add x1 y1)) y0) \/ (~ (nadd_le x0 x1))).
Definition term193 (x0 : nadd) (x1 : nadd) := @eq Prop (forall y0 : nadd, ((nadd_le (nadd_add x0 y0) (nadd_add x1 y0)) \/ (~ (nadd_le x0 x1))) /\ ((~ (nadd_le (nadd_add x0 y0) (nadd_add x1 y0))) \/ (nadd_le x0 x1))).
Definition term192 (x0 : nadd) (x1 : nadd) := @eq Prop (forall y0 : nadd, ((fun y1 : nadd => (nadd_le (nadd_add x0 y1) (nadd_add x1 y1)) \/ (~ (nadd_le x0 x1))) y0) /\ ((fun y1 : nadd => (~ (nadd_le (nadd_add x0 y1) (nadd_add x1 y1))) \/ (nadd_le x0 x1)) y0)).
Definition term263 (x0 : nadd) := forall y0 : nadd, (forall y1 : nadd, ~ (nadd_le (nadd_add x0 y1) (nadd_add y0 y1))) \/ (nadd_le x0 y0).
Definition term78 (x0 : nadd -> Prop) (x1 : nadd -> Prop) := exists y0 : nadd, (x0 y0) \/ (x1 y0).
Definition term250 (x0 : nadd) (x1 : nadd) := and ((fun y0 : nadd => (forall y1 : nadd, nadd_le (nadd_add x0 y1) (nadd_add y0 y1)) \/ (~ (nadd_le x0 y0))) x1).
Definition term238 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, ~ (nadd_le (nadd_add x0 y0) (nadd_add x1 y0)).
Definition term321 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (~ (nadd_eq x0 x2)) \/ ((~ (nadd_eq x1 x3)) \/ ((~ (nadd_le x0 x1)) \/ (nadd_le x2 x3))).
Definition term33 (x0 : nadd) := fun y0 : nadd => nadd_eq (nadd_add x0 y0) (nadd_add y0 x0).
Definition term11 := (~ (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le (nadd_add y0 y1) (nadd_add y0 y2)) = (nadd_le y1 y2))) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y2 y3)) -> (nadd_le y0 y2) = (nadd_le y1 y3)) -> (forall y0 : nadd, forall y1 : nadd, nadd_eq (nadd_add y0 y1) (nadd_add y1 y0)) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le (nadd_add y0 y2) (nadd_add y1 y2)) = (nadd_le y0 y1)) -> False.
Definition term352 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (nadd_eq x2 x0) /\ ((nadd_eq x3 x1) /\ (nadd_le x2 x3)).
Definition term203 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := forall y0 : a0, (x0 y0) \/ x1.
Definition term361 (x0 : nadd) (x1 : nadd) (x2 : nadd) := @eq Prop ((~ (nadd_le (nadd_add x1 x0) (nadd_add x2 x0))) \/ (nadd_le x1 x2)).
Definition term32 (x0 : nadd) (x1 : nadd) := nadd_eq (nadd_add x1 x0) (nadd_add x0 x1).
Definition term260 (x0 : nadd) := and (forall y0 : nadd, (forall y1 : nadd, nadd_le (nadd_add x0 y1) (nadd_add y0 y1)) \/ (~ (nadd_le x0 y0))).
Definition term198 (x0 : nadd) (x1 : nadd) := and (forall y0 : nadd, (nadd_le (nadd_add x0 y0) (nadd_add x1 y0)) \/ (~ (nadd_le x0 x1))).
Definition term47 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => (nadd_le (nadd_add x0 x1) (nadd_add x0 y0)) = (nadd_le x1 y0).
Definition term1 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term162 (x0 : nadd) (x1 : nadd) (x2 : nadd) := forall y0 : nadd, ((~ (nadd_eq x0 x2)) \/ (~ (nadd_eq x1 y0))) \/ (((nadd_le x0 x1) \/ (~ (nadd_le x2 y0))) /\ ((~ (nadd_le x0 x1)) \/ (nadd_le x2 y0))).
Definition term346 (x0 : nadd) (x1 : nadd) := and (~ (~ (nadd_eq x0 x1))).
Definition term142 := or (exists y0 : nadd, exists y1 : nadd, exists y2 : nadd, (nadd_le (nadd_add y0 y1) (nadd_add y0 y2)) /\ (~ (nadd_le y1 y2))).
Definition term120 (x0 : nadd) := or (exists y0 : nadd, exists y1 : nadd, (nadd_le (nadd_add x0 y0) (nadd_add x0 y1)) /\ (~ (nadd_le y0 y1))).
Definition term266 := forall y0 : nadd, (forall y1 : nadd, (forall y2 : nadd, nadd_le (nadd_add y0 y2) (nadd_add y1 y2)) \/ (~ (nadd_le y0 y1))) /\ (forall y1 : nadd, (forall y2 : nadd, ~ (nadd_le (nadd_add y0 y2) (nadd_add y1 y2))) \/ (nadd_le y0 y1)).
Definition term26 (x0 : nadd) (x1 : nadd) (x2 : nadd) := nadd_le (nadd_add x0 x2) (nadd_add x1 x2).
Definition term351 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (nadd_eq x2 x0) /\ (nadd_le x1 x2).
Definition term68 (x0 : nadd) := fun y0 : nadd => exists y1 : nadd, ((nadd_le (nadd_add x0 y0) (nadd_add x0 y1)) /\ (~ (nadd_le y0 y1))) \/ ((~ (nadd_le (nadd_add x0 y0) (nadd_add x0 y1))) /\ (nadd_le y0 y1)).
Definition term196 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, (nadd_le (nadd_add x0 y0) (nadd_add x1 y0)) \/ (~ (nadd_le x0 x1)).
Definition term87 (x0 : nadd) (x1 : nadd) (x2 : nadd) := or ((nadd_le (nadd_add x0 x1) (nadd_add x0 x2)) /\ (~ (nadd_le x1 x2))).
Definition term230 (x0 : nadd) (x1 : nadd) (x2 : nadd) := or ((fun y0 : nadd => ~ (nadd_le (nadd_add x0 y0) (nadd_add x1 y0))) x2).
Definition term127 := exists y0 : nadd, ((fun y1 : nadd => exists y2 : nadd, exists y3 : nadd, (nadd_le (nadd_add y1 y2) (nadd_add y1 y3)) /\ (~ (nadd_le y2 y3))) y0) \/ ((fun y1 : nadd => exists y2 : nadd, exists y3 : nadd, (~ (nadd_le (nadd_add y1 y2) (nadd_add y1 y3))) /\ (nadd_le y2 y3)) y0).
Definition term105 (x0 : nadd) := exists y0 : nadd, ((fun y1 : nadd => exists y2 : nadd, (nadd_le (nadd_add x0 y1) (nadd_add x0 y2)) /\ (~ (nadd_le y1 y2))) y0) \/ ((fun y1 : nadd => exists y2 : nadd, (~ (nadd_le (nadd_add x0 y1) (nadd_add x0 y2))) /\ (nadd_le y1 y2)) y0).
Definition term80 (x0 : nadd) (x1 : nadd) := exists y0 : nadd, ((fun y1 : nadd => (nadd_le (nadd_add x0 x1) (nadd_add x0 y1)) /\ (~ (nadd_le x1 y1))) y0) \/ ((fun y1 : nadd => (~ (nadd_le (nadd_add x0 x1) (nadd_add x0 y1))) /\ (nadd_le x1 y1)) y0).
Definition term145 := exists y0 : nadd, exists y1 : nadd, exists y2 : nadd, (~ (nadd_le (nadd_add y0 y1) (nadd_add y0 y2))) /\ (nadd_le y1 y2).
Definition term140 := exists y0 : nadd, exists y1 : nadd, exists y2 : nadd, (nadd_le (nadd_add y0 y1) (nadd_add y0 y2)) /\ (~ (nadd_le y1 y2)).
Definition term123 (x0 : nadd) := exists y0 : nadd, exists y1 : nadd, (~ (nadd_le (nadd_add x0 y0) (nadd_add x0 y1))) /\ (nadd_le y0 y1).
Definition term118 (x0 : nadd) := exists y0 : nadd, exists y1 : nadd, (nadd_le (nadd_add x0 y0) (nadd_add x0 y1)) /\ (~ (nadd_le y0 y1)).
Definition term75 := exists y0 : nadd, exists y1 : nadd, exists y2 : nadd, ((nadd_le (nadd_add y0 y1) (nadd_add y0 y2)) /\ (~ (nadd_le y1 y2))) \/ ((~ (nadd_le (nadd_add y0 y1) (nadd_add y0 y2))) /\ (nadd_le y1 y2)).
Definition term69 (x0 : nadd) := exists y0 : nadd, exists y1 : nadd, ((nadd_le (nadd_add x0 y0) (nadd_add x0 y1)) /\ (~ (nadd_le y0 y1))) \/ ((~ (nadd_le (nadd_add x0 y0) (nadd_add x0 y1))) /\ (nadd_le y0 y1)).
Definition term253 (x0 : nadd) := fun y0 : nadd => ((fun y1 : nadd => (forall y2 : nadd, nadd_le (nadd_add x0 y2) (nadd_add y1 y2)) \/ (~ (nadd_le x0 y1))) y0) /\ ((fun y1 : nadd => (forall y2 : nadd, ~ (nadd_le (nadd_add x0 y2) (nadd_add y1 y2))) \/ (nadd_le x0 y1)) y0).
Definition term191 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => ((fun y1 : nadd => (nadd_le (nadd_add x0 y1) (nadd_add x1 y1)) \/ (~ (nadd_le x0 x1))) y0) /\ ((fun y1 : nadd => (~ (nadd_le (nadd_add x0 y1) (nadd_add x1 y1))) \/ (nadd_le x0 x1)) y0).
Definition term287 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (((~ (nadd_eq x0 x2)) \/ (~ (nadd_eq x1 x3))) \/ ((nadd_le x0 x1) \/ (~ (nadd_le x2 x3)))) /\ (((~ (nadd_eq x0 x2)) \/ (~ (nadd_eq x1 x3))) \/ ((~ (nadd_le x0 x1)) \/ (nadd_le x2 x3))).
Definition term154 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (~ (nadd_eq x0 x1)) \/ (~ (nadd_eq x2 x3)).
Definition term72 (x0 : nadd) := ~ ((fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, (nadd_le (nadd_add y0 y1) (nadd_add y0 y2)) = (nadd_le y1 y2)) x0).
Definition term247 (x0 : nadd) := fun y0 : nadd => (forall y1 : nadd, nadd_le (nadd_add x0 y1) (nadd_add y0 y1)) \/ (~ (nadd_le x0 y0)).
Definition term284 := forall y0 : nadd, (fun y1 : nadd => forall y2 : nadd, (forall y3 : nadd, ~ (nadd_le (nadd_add y1 y3) (nadd_add y2 y3))) \/ (nadd_le y1 y2)) y0.
Definition term279 := forall y0 : nadd, (fun y1 : nadd => forall y2 : nadd, (forall y3 : nadd, nadd_le (nadd_add y1 y3) (nadd_add y2 y3)) \/ (~ (nadd_le y1 y2))) y0.
Definition term170 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => ((nadd_le (nadd_add x0 y0) (nadd_add x1 y0)) \/ (~ (nadd_le x0 x1))) /\ ((~ (nadd_le (nadd_add x0 y0) (nadd_add x1 y0))) \/ (nadd_le x0 x1)).
Definition term283 := fun y0 : nadd => (fun y1 : nadd => forall y2 : nadd, (forall y3 : nadd, ~ (nadd_le (nadd_add y1 y3) (nadd_add y2 y3))) \/ (nadd_le y1 y2)) y0.
Definition term278 := fun y0 : nadd => (fun y1 : nadd => forall y2 : nadd, (forall y3 : nadd, nadd_le (nadd_add y1 y3) (nadd_add y2 y3)) \/ (~ (nadd_le y1 y2))) y0.
Definition term169 (x0 : nadd) (x1 : nadd) (x2 : nadd) := ((nadd_le (nadd_add x1 x0) (nadd_add x2 x0)) \/ (~ (nadd_le x1 x2))) /\ ((~ (nadd_le (nadd_add x1 x0) (nadd_add x2 x0))) \/ (nadd_le x1 x2)).
Definition term208 (x0 : nadd) (x1 : nadd) := (forall y0 : nadd, (fun y1 : nadd => nadd_le (nadd_add x0 y1) (nadd_add x1 y1)) y0) \/ (~ (nadd_le x0 x1)).
Definition term331 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (nadd_le x0 x1) \/ ((~ (nadd_eq x3 x1)) \/ (~ (nadd_le x2 x3))).
Definition term55 (x0 : nadd -> Prop) := exists y0 : nadd, ~ (x0 y0).
Definition term345 (x0 : nadd) (x1 : nadd) := ~ (~ (nadd_eq x0 x1)).
Definition term292 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => forall y1 : nadd, (((~ (nadd_eq x0 x1)) \/ (~ (nadd_eq y0 y1))) \/ ((nadd_le x0 y0) \/ (~ (nadd_le x1 y1)))) /\ (((~ (nadd_eq x0 x1)) \/ (~ (nadd_eq y0 y1))) \/ ((~ (nadd_le x0 y0)) \/ (nadd_le x1 y1))).
Definition term172 (x0 : nadd) := fun y0 : nadd => forall y1 : nadd, ((nadd_le (nadd_add x0 y1) (nadd_add y0 y1)) \/ (~ (nadd_le x0 y0))) /\ ((~ (nadd_le (nadd_add x0 y1) (nadd_add y0 y1))) \/ (nadd_le x0 y0)).
Definition term163 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => forall y1 : nadd, ((~ (nadd_eq x0 x1)) \/ (~ (nadd_eq y0 y1))) \/ (((nadd_le x0 y0) \/ (~ (nadd_le x1 y1))) /\ ((~ (nadd_le x0 y0)) \/ (nadd_le x1 y1))).
Definition term40 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => forall y1 : nadd, ((nadd_eq x0 x1) /\ (nadd_eq y0 y1)) -> (nadd_le x0 y0) = (nadd_le x1 y1).
Definition term159 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := ((~ (nadd_eq x0 x2)) \/ (~ (nadd_eq x1 x3))) \/ (((nadd_le x0 x1) \/ (~ (nadd_le x2 x3))) /\ ((~ (nadd_le x0 x1)) \/ (nadd_le x2 x3))).
Definition term299 (x0 : nadd) (x1 : nadd) := @eq Prop ((forall y0 : nadd, ~ (nadd_le (nadd_add x0 y0) (nadd_add x1 y0))) \/ (nadd_le x0 x1)).
Definition term298 (x0 : nadd) (x1 : nadd) := @eq Prop ((forall y0 : nadd, (fun y1 : nadd => ~ (nadd_le (nadd_add x0 y1) (nadd_add x1 y1))) y0) \/ (nadd_le x0 x1)).
Definition term48 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, (nadd_le (nadd_add x0 x1) (nadd_add x0 y0)) = (nadd_le x1 y0).
Definition term79 (x0 : nadd -> Prop) (x1 : nadd -> Prop) := (exists y0 : nadd, x0 y0) \/ (exists y0 : nadd, x1 y0).
Definition term339 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (~ (nadd_eq x2 x0)) \/ ((~ (nadd_eq x3 x1)) \/ (~ (nadd_le x2 x3))).
Definition term348 (x0 : nadd) (x1 : nadd) (x2 : nadd) := ~ ((~ (nadd_eq x2 x0)) \/ (~ (nadd_le x1 x2))).
Definition term96 (x0 : nadd) (x1 : nadd) := exists y0 : nadd, (nadd_le (nadd_add x0 x1) (nadd_add x0 y0)) /\ (~ (nadd_le x1 y0)).
Definition term281 := and (forall y0 : nadd, (fun y1 : nadd => forall y2 : nadd, (forall y3 : nadd, nadd_le (nadd_add y1 y3) (nadd_add y2 y3)) \/ (~ (nadd_le y1 y2))) y0).
Definition term259 (x0 : nadd) := and (forall y0 : nadd, (fun y1 : nadd => (forall y2 : nadd, nadd_le (nadd_add x0 y2) (nadd_add y1 y2)) \/ (~ (nadd_le x0 y1))) y0).
Definition term197 (x0 : nadd) (x1 : nadd) := and (forall y0 : nadd, (fun y1 : nadd => (nadd_le (nadd_add x0 y1) (nadd_add x1 y1)) \/ (~ (nadd_le x0 x1))) y0).
Definition term315 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => nadd_eq (nadd_add x0 y0) (nadd_add y0 x0)) x1.
Definition term39 (x0 : nadd) (x1 : nadd) (x2 : nadd) := forall y0 : nadd, ((nadd_eq x0 x2) /\ (nadd_eq x1 y0)) -> (nadd_le x0 x1) = (nadd_le x2 y0).
Definition term20 := (forall y0 : nadd, forall y1 : nadd, nadd_eq (nadd_add y0 y1) (nadd_add y1 y0)) -> ~ (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le (nadd_add y0 y2) (nadd_add y1 y2)) = (nadd_le y0 y1)).
Definition term319 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => forall y1 : nadd, (nadd_le (nadd_add x0 y1) (nadd_add y0 y1)) \/ (~ (nadd_le x0 y0))) x1.
Definition term317 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => forall y1 : nadd, (~ (nadd_le (nadd_add x0 y1) (nadd_add y0 y1))) \/ (nadd_le x0 y0)) x1.
Definition term65 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => forall y1 : nadd, (nadd_le (nadd_add x0 y0) (nadd_add x0 y1)) = (nadd_le y0 y1)) x1.
Definition term343 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (~ (~ (nadd_eq x2 x0))) /\ (~ ((~ (nadd_eq x3 x1)) \/ (~ (nadd_le x2 x3)))).
Definition term184 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (fun y0 : nadd => (nadd_le (nadd_add x0 y0) (nadd_add x1 y0)) \/ (~ (nadd_le x0 x1))) x2.
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term327 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (~ (nadd_le (nadd_add x1 x0) (nadd_add x1 x2))) -> nadd_le (nadd_add x1 x0) (nadd_add x1 x2).
Definition term243 (x0 : nadd) := fun y0 : nadd => ((forall y1 : nadd, nadd_le (nadd_add x0 y1) (nadd_add y0 y1)) \/ (~ (nadd_le x0 y0))) /\ ((forall y1 : nadd, ~ (nadd_le (nadd_add x0 y1) (nadd_add y0 y1))) \/ (nadd_le x0 y0)).
Definition term268 := (forall y0 : nadd, (fun y1 : nadd => forall y2 : nadd, (forall y3 : nadd, nadd_le (nadd_add y1 y3) (nadd_add y2 y3)) \/ (~ (nadd_le y1 y2))) y0) /\ (forall y0 : nadd, (fun y1 : nadd => forall y2 : nadd, (forall y3 : nadd, ~ (nadd_le (nadd_add y1 y3) (nadd_add y2 y3))) \/ (nadd_le y1 y2)) y0).
Definition term246 (x0 : nadd) := (forall y0 : nadd, (fun y1 : nadd => (forall y2 : nadd, nadd_le (nadd_add x0 y2) (nadd_add y1 y2)) \/ (~ (nadd_le x0 y1))) y0) /\ (forall y0 : nadd, (fun y1 : nadd => (forall y2 : nadd, ~ (nadd_le (nadd_add x0 y2) (nadd_add y1 y2))) \/ (nadd_le x0 y1)) y0).
Definition term181 (x0 : nadd) (x1 : nadd) := (forall y0 : nadd, (fun y1 : nadd => (nadd_le (nadd_add x0 y1) (nadd_add x1 y1)) \/ (~ (nadd_le x0 x1))) y0) /\ (forall y0 : nadd, (fun y1 : nadd => (~ (nadd_le (nadd_add x0 y1) (nadd_add x1 y1))) \/ (nadd_le x0 x1)) y0).
Definition term103 (x0 : nadd) := fun y0 : nadd => (exists y1 : nadd, (nadd_le (nadd_add x0 y0) (nadd_add x0 y1)) /\ (~ (nadd_le y0 y1))) \/ (exists y1 : nadd, (~ (nadd_le (nadd_add x0 y0) (nadd_add x0 y1))) /\ (nadd_le y0 y1)).
Definition term256 (x0 : nadd) := fun y0 : nadd => (fun y1 : nadd => (forall y2 : nadd, nadd_le (nadd_add x0 y2) (nadd_add y1 y2)) \/ (~ (nadd_le x0 y1))) y0.
Definition term194 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => (fun y1 : nadd => (nadd_le (nadd_add x0 y1) (nadd_add x1 y1)) \/ (~ (nadd_le x0 x1))) y0.
Definition term176 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term359 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (~ (nadd_le (nadd_add x0 x2) (nadd_add x1 x2))) -> nadd_le (nadd_add x0 x2) (nadd_add x1 x2).
Definition term251 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (forall y1 : nadd, ~ (nadd_le (nadd_add x0 y1) (nadd_add y0 y1))) \/ (nadd_le x0 y0)) x1.
Definition term38 (x0 : nadd) (x1 : nadd) (x2 : nadd) := fun y0 : nadd => ((nadd_eq x0 x2) /\ (nadd_eq x1 y0)) -> (nadd_le x0 x1) = (nadd_le x2 y0).
Definition term215 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => ((fun y1 : nadd => nadd_le (nadd_add x0 y1) (nadd_add x1 y1)) y0) \/ (~ (nadd_le x0 x1)).
Definition term178 (x0 : nadd -> Prop) (x1 : nadd -> Prop) := forall y0 : nadd, (x0 y0) /\ (x1 y0).
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term90 (x0 : nadd) (x1 : nadd) (x2 : nadd) := ((fun y0 : nadd => (nadd_le (nadd_add x0 x1) (nadd_add x0 y0)) /\ (~ (nadd_le x1 y0))) x2) \/ ((fun y0 : nadd => (~ (nadd_le (nadd_add x0 x1) (nadd_add x0 y0))) /\ (nadd_le x1 y0)) x2).
Definition term210 (x0 : nadd) (x1 : nadd) := ~ (nadd_le x0 x1).
Definition term130 := fun y0 : nadd => exists y1 : nadd, exists y2 : nadd, (~ (nadd_le (nadd_add y0 y1) (nadd_add y0 y2))) /\ (nadd_le y1 y2).
Definition term129 := fun y0 : nadd => exists y1 : nadd, exists y2 : nadd, (nadd_le (nadd_add y0 y1) (nadd_add y0 y2)) /\ (~ (nadd_le y1 y2)).
Definition term74 := fun y0 : nadd => exists y1 : nadd, exists y2 : nadd, ((nadd_le (nadd_add y0 y1) (nadd_add y0 y2)) /\ (~ (nadd_le y1 y2))) \/ ((~ (nadd_le (nadd_add y0 y1) (nadd_add y0 y2))) /\ (nadd_le y1 y2)).
Definition term289 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (~ (nadd_le x0 x1)) \/ (nadd_le x2 x3).
Definition term63 (x0 : nadd) := ~ (forall y0 : nadd, forall y1 : nadd, (nadd_le (nadd_add x0 y0) (nadd_add x0 y1)) = (nadd_le y0 y1)).
Definition term16 := ~ (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le (nadd_add y0 y2) (nadd_add y1 y2)) = (nadd_le y0 y1)).
Definition term10 := ~ (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le (nadd_add y0 y1) (nadd_add y0 y2)) = (nadd_le y1 y2)).
Definition term156 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := or (~ ((nadd_eq x0 x1) /\ (nadd_eq x2 x3))).
Definition term274 (x0 : nadd) := ((fun y0 : nadd => forall y1 : nadd, (forall y2 : nadd, nadd_le (nadd_add y0 y2) (nadd_add y1 y2)) \/ (~ (nadd_le y0 y1))) x0) /\ ((fun y0 : nadd => forall y1 : nadd, (forall y2 : nadd, ~ (nadd_le (nadd_add y0 y2) (nadd_add y1 y2))) \/ (nadd_le y0 y1)) x0).
Definition term236 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => (fun y1 : nadd => ~ (nadd_le (nadd_add x0 y1) (nadd_add x1 y1))) y0.
Definition term76 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term214 (x0 : nadd) (x1 : nadd) (x2 : nadd) := ((fun y0 : nadd => nadd_le (nadd_add x1 y0) (nadd_add x2 y0)) x0) \/ (~ (nadd_le x1 x2)).
Definition term189 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (~ (nadd_le (nadd_add x1 x0) (nadd_add x2 x0))) \/ (nadd_le x1 x2).
Definition term313 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (fun y0 : nadd => (((~ (nadd_eq x0 x2)) \/ (~ (nadd_eq x1 y0))) \/ ((nadd_le x0 x1) \/ (~ (nadd_le x2 y0)))) /\ (((~ (nadd_eq x0 x2)) \/ (~ (nadd_eq x1 y0))) \/ ((~ (nadd_le x0 x1)) \/ (nadd_le x2 y0)))) x3.
Definition term102 (x0 : nadd) (x1 : nadd) := (exists y0 : nadd, (nadd_le (nadd_add x0 x1) (nadd_add x0 y0)) /\ (~ (nadd_le x1 y0))) \/ (exists y0 : nadd, (~ (nadd_le (nadd_add x0 x1) (nadd_add x0 y0))) /\ (nadd_le x1 y0)).
Definition term125 := fun y0 : nadd => (exists y1 : nadd, exists y2 : nadd, (nadd_le (nadd_add y0 y1) (nadd_add y0 y2)) /\ (~ (nadd_le y1 y2))) \/ (exists y1 : nadd, exists y2 : nadd, (~ (nadd_le (nadd_add y0 y1) (nadd_add y0 y2))) /\ (nadd_le y1 y2)).
Definition term244 (x0 : nadd) := forall y0 : nadd, ((forall y1 : nadd, nadd_le (nadd_add x0 y1) (nadd_add y0 y1)) \/ (~ (nadd_le x0 y0))) /\ ((forall y1 : nadd, ~ (nadd_le (nadd_add x0 y1) (nadd_add y0 y1))) \/ (nadd_le x0 y0)).
Definition term171 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, ((nadd_le (nadd_add x0 y0) (nadd_add x1 y0)) \/ (~ (nadd_le x0 x1))) /\ ((~ (nadd_le (nadd_add x0 y0) (nadd_add x1 y0))) \/ (nadd_le x0 x1)).
Definition term24 := imp (~ (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le (nadd_add y0 y1) (nadd_add y0 y2)) = (nadd_le y1 y2))).
Definition term66 (x0 : nadd) (x1 : nadd) := ~ ((fun y0 : nadd => forall y1 : nadd, (nadd_le (nadd_add x0 y0) (nadd_add x0 y1)) = (nadd_le y0 y1)) x1).
Definition term242 (x0 : nadd) (x1 : nadd) := ((forall y0 : nadd, nadd_le (nadd_add x0 y0) (nadd_add x1 y0)) \/ (~ (nadd_le x0 x1))) /\ ((forall y0 : nadd, ~ (nadd_le (nadd_add x0 y0) (nadd_add x1 y0))) \/ (nadd_le x0 x1)).
Definition term241 (x0 : nadd) (x1 : nadd) := (forall y0 : nadd, ~ (nadd_le (nadd_add x0 y0) (nadd_add x1 y0))) \/ (nadd_le x0 x1).
Definition term226 (x0 : nadd) (x1 : nadd) := (forall y0 : nadd, (fun y1 : nadd => ~ (nadd_le (nadd_add x0 y1) (nadd_add x1 y1))) y0) \/ (nadd_le x0 x1).
Definition term372 (x0 : nadd) (x1 : nadd) := imp (~ (~ (nadd_le x0 x1))).
Definition term152 (x0 : nadd) (x1 : nadd) := @eq Prop ((exists y0 : nadd, (nadd_le (nadd_add x0 x1) (nadd_add x0 y0)) /\ (~ (nadd_le x1 y0))) \/ (exists y0 : nadd, (~ (nadd_le (nadd_add x0 x1) (nadd_add x0 y0))) /\ (nadd_le x1 y0))).
Definition term151 (x0 : nadd) (x1 : nadd) := @eq Prop ((exists y0 : nadd, (fun y1 : nadd => (nadd_le (nadd_add x0 x1) (nadd_add x0 y1)) /\ (~ (nadd_le x1 y1))) y0) \/ (exists y0 : nadd, (fun y1 : nadd => (~ (nadd_le (nadd_add x0 x1) (nadd_add x0 y1))) /\ (nadd_le x1 y1)) y0)).
Definition term150 (x0 : nadd) := @eq Prop ((exists y0 : nadd, exists y1 : nadd, (nadd_le (nadd_add x0 y0) (nadd_add x0 y1)) /\ (~ (nadd_le y0 y1))) \/ (exists y0 : nadd, exists y1 : nadd, (~ (nadd_le (nadd_add x0 y0) (nadd_add x0 y1))) /\ (nadd_le y0 y1))).
Definition term149 (x0 : nadd) := @eq Prop ((exists y0 : nadd, (fun y1 : nadd => exists y2 : nadd, (nadd_le (nadd_add x0 y1) (nadd_add x0 y2)) /\ (~ (nadd_le y1 y2))) y0) \/ (exists y0 : nadd, (fun y1 : nadd => exists y2 : nadd, (~ (nadd_le (nadd_add x0 y1) (nadd_add x0 y2))) /\ (nadd_le y1 y2)) y0)).
Definition term148 := @eq Prop ((exists y0 : nadd, exists y1 : nadd, exists y2 : nadd, (nadd_le (nadd_add y0 y1) (nadd_add y0 y2)) /\ (~ (nadd_le y1 y2))) \/ (exists y0 : nadd, exists y1 : nadd, exists y2 : nadd, (~ (nadd_le (nadd_add y0 y1) (nadd_add y0 y2))) /\ (nadd_le y1 y2))).
Definition term147 := @eq Prop ((exists y0 : nadd, (fun y1 : nadd => exists y2 : nadd, exists y3 : nadd, (nadd_le (nadd_add y1 y2) (nadd_add y1 y3)) /\ (~ (nadd_le y2 y3))) y0) \/ (exists y0 : nadd, (fun y1 : nadd => exists y2 : nadd, exists y3 : nadd, (~ (nadd_le (nadd_add y1 y2) (nadd_add y1 y3))) /\ (nadd_le y2 y3)) y0)).
