Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term254 (x0 : real) := (fun y0 : real => (real_ge y0 (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 y0) (real_of_num (NUMERAL 0))))) (real_abs x0).
Definition term132 (x0 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_abs x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term104 (x0 : real) := fun y0 : real => (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 y0) (real_of_num (NUMERAL 0))).
Definition term206 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term128 (x0 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_abs x0)) (real_of_num (NUMERAL 0)).
Definition term23 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0)).
Definition term0 (x0 : real -> Prop) := ~ (all x0).
Definition term64 (x0 : real) := (fun y0 : real => real_gt (real_add (real_abs y0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_abs y0)))) (real_of_num (NUMERAL 0))) x0.
Definition term30 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term136 (x0 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_abs x0)).
Definition term326 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term314 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term293 (x0 : real) := real_add (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term215 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term279 (x0 : real) := real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0).
Definition term366 (x0 : real) := (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_neg x0)) (real_of_num (NUMERAL 0))).
Definition term361 (x0 : real) := (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_abs x0)) (real_of_num (NUMERAL 0))).
Definition term356 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0).
Definition term349 (x0 : real) := real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0).
Definition term112 (x0 : real) := and (real_ge (real_abs x0) (real_of_num (NUMERAL 0))).
Definition term42 := real_of_num (NUMERAL 0).
Definition term256 (x0 : real) := fun y0 : real => (real_ge y0 (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 y0) (real_of_num (NUMERAL 0)))).
Definition term121 (x0 : real) := real_sub (real_abs x0) (real_of_num (NUMERAL 0)).
Definition term130 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_abs x0).
Definition term89 (x0 : real) := real_gt (real_add x0 (real_abs (real_abs x0))).
Definition term373 (x0 : real) := ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_of_num (NUMERAL 0)) x0) /\ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_neg x0)) (real_of_num (NUMERAL 0))))).
Definition term350 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_abs x0).
Definition term35 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_abs x0).
Definition term45 (x0 : real) := real_gt (real_sub (real_abs (real_abs x0)) (real_abs x0)).
Definition term18 (x0 : real) := real_neg (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0)) (real_abs (real_abs x0))).
Definition term319 (x0 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg x0)) (real_of_num (NUMERAL 0)).
Definition term55 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term398 (x0 : real) := or ((((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))))) \/ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))))))) \/ (((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))) /\ (((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))) /\ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0))))))).
Definition term368 (x0 : real) := (real_gt (real_of_num (NUMERAL 0)) x0) /\ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_neg x0)) (real_of_num (NUMERAL 0)))).
Definition term139 (x0 : real) := real_add x0 (real_abs x0).
Definition term161 (x0 : real) := real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0))).
Definition term239 := real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term108 (x0 : real) := (real_gt (real_of_num (NUMERAL 0)) (real_abs x0)) /\ ((fun y0 : real => (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 y0) (real_of_num (NUMERAL 0)))) (real_neg (real_abs x0))).
Definition term377 (x0 : real) := real_gt (real_sub (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term288 (x0 : real) := real_gt (real_sub (real_add x0 x0) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term278 (x0 : real) := real_gt (real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term180 (x0 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0))) (real_of_num (NUMERAL 0)).
Definition term252 (x0 : real) := ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))) /\ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))).
Definition term2 := ~ (forall y0 : real, (real_abs (real_abs y0)) = (real_abs y0)).
Definition term310 (x0 : real) := real_sub (real_neg x0).
Definition term330 (x0 : real) := real_gt (real_add x0 (real_neg x0)) (real_of_num (NUMERAL 0)).
Definition term24 (x0 : real) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_abs x0).
Definition term173 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0)).
Definition term357 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) (real_abs x0).
Definition term316 (x0 : real) := real_ge (real_sub (real_neg x0) (real_of_num (NUMERAL 0))).
Definition term341 (x0 : real) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))))).
Definition term318 (x0 : real) := real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)).
Definition term38 (x0 : real) := real_add (real_abs x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_abs x0))).
Definition term241 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0.
Definition term238 := real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term156 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg (real_abs x0)).
Definition term302 (x0 : real) := real_gt (real_sub (real_of_num (NUMERAL 0)) x0) (real_of_num (NUMERAL 0)).
Definition term344 (x0 : real) := or (((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))))) \/ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))))))).
Definition term154 (x0 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg (real_abs x0))) (real_of_num (NUMERAL 0)).
Definition term86 (x0 : real) := real_add (real_abs (real_abs x0)) x0.
Definition term301 (x0 : real) := real_gt (real_of_num (NUMERAL 0)) x0.
Definition term214 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) x0.
Definition term115 (x0 : real) := or ((real_ge (real_abs x0) (real_of_num (NUMERAL 0))) /\ ((fun y0 : real => (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 y0) (real_of_num (NUMERAL 0)))) (real_abs x0))).
Definition term271 (x0 : real) := real_ge x0 (real_of_num (NUMERAL 0)).
Definition term336 (x0 : real) := and (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg x0)) (real_of_num (NUMERAL 0))).
Definition term187 (x0 : real) := and (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0)) (real_of_num (NUMERAL 0))).
Definition term146 (x0 : real) := and (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_abs x0)) (real_of_num (NUMERAL 0))).
Definition term122 (x0 : real) := real_add (real_abs x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term141 (x0 : real) := real_add (real_add x0 (real_abs x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term163 (x0 : real) := real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0))) (real_of_num (NUMERAL 0)).
Definition term323 (x0 : real) := real_sub (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0).
Definition term311 (x0 : real) := real_sub (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term290 (x0 : real) := real_sub (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0).
Definition term328 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0)).
Definition term315 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)).
Definition term295 (x0 : real) := real_add (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0)).
Definition term20 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_abs x0))).
Definition term283 := real_add (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term264 (x0 : real) := and (real_ge x0 (real_of_num (NUMERAL 0))).
Definition term387 := real_neg (real_of_num (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (NUMERAL (BIT1 0)))).
Definition term275 (x0 : real) := real_add x0 (real_of_num (NUMERAL 0)).
Definition term81 (x0 : real) (x1 : real) (x2 : real) := (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) x2) /\ (real_gt (real_add x0 (real_mul (real_of_num (NUMERAL (BIT1 0))) x1)) x2).
Definition term142 (x0 : real) := real_add (real_add x0 (real_abs x0)).
Definition term404 := forall y0 : real, (real_abs (real_abs y0)) = (real_abs y0).
Definition term397 (x0 : real) := ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))))).
Definition term189 (x0 : real) := ((real_ge (real_abs x0) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_abs x0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_abs x0)) (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0)) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0))) (real_of_num (NUMERAL 0))))).
Definition term116 (x0 : real) := or ((real_ge (real_abs x0) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_abs x0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_abs x0)) (real_of_num (NUMERAL 0))))).
Definition term235 (x0 : real) := (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_mul (real_of_num (NUMERAL (BIT1 0))) x0)) (real_of_num (NUMERAL 0))).
Definition term143 (x0 : real) := real_add (real_add x0 (real_abs x0)) (real_of_num (NUMERAL 0)).
Definition term22 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_abs x0)).
Definition term403 := ((~ (forall y0 : real, (real_abs (real_abs y0)) = (real_abs y0))) -> False) -> forall y0 : real, (real_abs (real_abs y0)) = (real_abs y0).
Definition term305 (x0 : real) := real_gt (real_sub (real_of_num (NUMERAL 0)) x0).
Definition term14 (x0 : real) := real_add (real_abs (real_abs x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0)).
Definition term75 := exists y0 : real, (fun y1 : real => real_gt (real_add (real_abs y1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_abs y1)))) (real_of_num (NUMERAL 0))) y0.
Definition term70 := exists y0 : real, (fun y1 : real => real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y1)) (real_abs (real_abs y1))) (real_of_num (NUMERAL 0))) y0.
Definition term396 (x0 : real) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0)))).
Definition term399 (x0 : real) := ((((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))))) \/ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))))))) \/ (((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))) /\ (((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))) /\ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0))))))) \/ (((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0)))))).
Definition term123 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term178 (x0 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term84 (x0 : real) := real_add (real_abs (real_abs x0)).
Definition term48 (x0 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0)) (real_abs (real_abs x0))) (real_of_num (NUMERAL 0)).
Definition term200 (x0 : real) := (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_of_num (NUMERAL (BIT1 0))) x0)) (real_of_num (NUMERAL 0))).
Definition term82 (x0 : real) := (real_gt (real_add (real_abs (real_abs x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_abs (real_abs x0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) x0)) (real_of_num (NUMERAL 0))).
Definition term333 (x0 : real) := real_sub (real_add x0 (real_neg x0)).
Definition term27 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term169 (x0 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0))) (real_of_num (NUMERAL 0)).
Definition term107 (x0 : real) := and (real_gt (real_of_num (NUMERAL 0)) (real_abs x0)).
Definition term186 (x0 : real) := (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0))) (real_of_num (NUMERAL 0))).
Definition term359 (x0 : real) := real_gt (real_add (real_abs x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0))) (real_of_num (NUMERAL 0)).
Definition term353 (x0 : real) := real_gt (real_add (real_abs x0) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_abs x0))) (real_of_num (NUMERAL 0)).
Definition term72 := or (exists y0 : real, (fun y1 : real => real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y1)) (real_abs (real_abs y1))) (real_of_num (NUMERAL 0))) y0).
Definition term273 (x0 : real) := real_sub x0 (real_of_num (NUMERAL 0)).
Definition term240 := real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term339 (x0 : real) := and (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term219 := Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term152 (x0 : real) := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0)).
Definition term17 (x0 : real) := real_neg (real_sub (real_abs (real_abs x0)) (real_abs x0)).
Definition term199 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x1))) x2.
Definition term393 (x0 : real) := real_sub (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_neg x0)) (real_of_num (NUMERAL 0)).
Definition term386 := real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term312 (x0 : real) := real_sub (real_neg x0) (real_of_num (NUMERAL 0)).
Definition term3 := exists y0 : real, ~ ((fun y1 : real => (real_abs (real_abs y1)) = (real_abs y1)) y0).
Definition term381 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_neg x0).
Definition term177 (x0 : real) := real_sub (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0))) (real_of_num (NUMERAL 0)).
Definition term274 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term340 (x0 : real) := (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))).
Definition term253 (x0 : real) := ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))) /\ (((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))) /\ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0))))).
Definition term10 := fun y0 : real => ~ ((real_abs (real_abs y0)) = (real_abs y0)).
Definition term6 (x0 : real) := real_abs (real_abs x0).
Definition term91 (x0 : real) := real_gt (real_add x0 (real_abs (real_abs x0))) (real_of_num (NUMERAL 0)).
Definition term40 (x0 : real) := real_gt (real_neg (real_sub (real_abs (real_abs x0)) (real_abs x0))).
Definition term334 (x0 : real) := real_sub (real_add x0 (real_neg x0)) (real_of_num (NUMERAL 0)).
Definition term80 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0)) x1) x2.
Definition term250 := and (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term216 := real_neg (real_of_num (Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term13 (x0 : real) := real_sub (real_abs (real_abs x0)) (real_abs x0).
Definition term92 (x0 : real) := real_add (real_abs (real_abs x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term85 (x0 : real) := real_add (real_abs (real_abs x0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) x0).
Definition term342 (x0 : real) := or ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))))).
Definition term268 (x0 : real) := or ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 x0) (real_of_num (NUMERAL 0)))))).
Definition term204 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term31 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term191 (x0 : real) (x1 : real) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) x0) x1).
Definition term162 (x0 : real) := real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg (real_abs x0))) (real_of_num (NUMERAL 0)).
Definition term261 (x0 : real) := (real_gt (real_of_num (NUMERAL 0)) x0) /\ ((real_ge (real_neg x0) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg x0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_neg x0)) (real_of_num (NUMERAL 0))))).
Definition term102 (x0 : real) := (fun y0 : real => (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 y0) (real_of_num (NUMERAL 0)))) (real_abs (real_abs x0)).
Definition term61 := fun y0 : real => real_gt (real_add (real_abs y0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_abs y0)))) (real_of_num (NUMERAL 0)).
Definition term337 (x0 : real) := (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg x0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_neg x0)) (real_of_num (NUMERAL 0))).
Definition term111 (x0 : real) := (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_abs x0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_abs x0)) (real_of_num (NUMERAL 0))).
Definition term12 (x0 : real) := (real_gt (real_sub (real_abs (real_abs x0)) (real_abs x0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub (real_abs (real_abs x0)) (real_abs x0))) (real_of_num (NUMERAL 0))).
Definition term56 (x0 : real -> Prop) (x1 : real -> Prop) := exists y0 : real, (x0 y0) \/ (x1 y0).
Definition term77 := (exists y0 : real, real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y0)) (real_abs (real_abs y0))) (real_of_num (NUMERAL 0))) \/ (exists y0 : real, real_gt (real_add (real_abs y0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_abs y0)))) (real_of_num (NUMERAL 0))).
Definition term401 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term124 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term354 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_abs x0)) (real_of_num (NUMERAL 0)).
Definition term153 (x0 : real) := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0)) (real_of_num (NUMERAL 0)).
Definition term176 (x0 : real) := real_sub (real_add x0 (real_neg (real_abs x0))) (real_of_num (NUMERAL 0)).
Definition term374 (x0 : real) := @eq Prop ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_abs x0)) (real_of_num (NUMERAL 0)))).
Definition term118 (x0 : real) := @eq Prop ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_abs (real_abs x0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_abs (real_abs x0))) (real_of_num (NUMERAL 0)))).
Definition term159 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0)).
Definition term280 := real_sub (real_of_num (NUMERAL 0)).
Definition term181 (x0 : real) := real_gt (real_sub (real_add x0 (real_neg (real_abs x0))) (real_of_num (NUMERAL 0))).
Definition term363 (x0 : real) := ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((fun y0 : real => (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) y0) (real_of_num (NUMERAL 0)))) x0)) \/ ((real_gt (real_of_num (NUMERAL 0)) x0) /\ ((fun y0 : real => (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) y0) (real_of_num (NUMERAL 0)))) (real_neg x0))).
Definition term255 (x0 : real) := ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((fun y0 : real => (real_ge y0 (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 y0) (real_of_num (NUMERAL 0))))) x0)) \/ ((real_gt (real_of_num (NUMERAL 0)) x0) /\ ((fun y0 : real => (real_ge y0 (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 y0) (real_of_num (NUMERAL 0))))) (real_neg x0))).
Definition term76 := exists y0 : real, real_gt (real_add (real_abs y0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_abs y0)))) (real_of_num (NUMERAL 0)).
Definition term71 := exists y0 : real, real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y0)) (real_abs (real_abs y0))) (real_of_num (NUMERAL 0)).
Definition term389 := Nat.mul (NUMERAL (BIT0 (BIT1 0))) (NUMERAL (BIT1 0)).
Definition term131 (x0 : real) := real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_abs x0)) (real_of_num (NUMERAL 0)).
Definition term195 (x0 : real) := real_gt x0 (real_of_num (NUMERAL 0)).
Definition term57 (x0 : real -> Prop) (x1 : real -> Prop) := (exists y0 : real, x0 y0) \/ (exists y0 : real, x1 y0).
Definition term168 (x0 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0))).
Definition term212 := real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term179 (x0 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0))).
Definition term126 (x0 : real) := real_ge (real_sub (real_abs x0) (real_of_num (NUMERAL 0))).
Definition term223 := real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term43 (x0 : real) := real_gt (real_neg (real_sub (real_abs (real_abs x0)) (real_abs x0))) (real_of_num (NUMERAL 0)).
Definition term83 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term270 (x0 : real) := @eq Prop ((real_ge (real_abs x0) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_abs x0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_abs x0)) (real_of_num (NUMERAL 0))))).
Definition term372 (x0 : real) := or ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0))))).
Definition term296 (x0 : real) := real_gt (real_sub (real_add x0 x0) (real_of_num (NUMERAL 0))).
Definition term249 (x0 : real) := and (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0))).
Definition term348 (x0 : real) := real_add (real_abs x0) (real_abs x0).
Definition term202 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0.
Definition term174 (x0 : real) := real_sub (real_add x0 (real_neg (real_abs x0))).
Definition term379 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_neg x0)) (real_of_num (NUMERAL 0)).
Definition term262 (x0 : real) := (fun y0 : real => (real_ge y0 (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 y0) (real_of_num (NUMERAL 0))))) x0.
Definition term33 := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term281 (x0 : real) := real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_of_num (NUMERAL 0)).
Definition term68 := @eq Prop (exists y0 : real, (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y0)) (real_abs (real_abs y0))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add (real_abs y0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_abs y0)))) (real_of_num (NUMERAL 0)))).
Definition term67 := @eq Prop (exists y0 : real, ((fun y1 : real => real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y1)) (real_abs (real_abs y1))) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_add (real_abs y1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_abs y1)))) (real_of_num (NUMERAL 0))) y0)).
Definition term36 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0))).
Definition term8 (x0 : real) := ~ ((real_abs (real_abs x0)) = (real_abs x0)).
Definition term370 (x0 : real) := (real_ge x0 (real_of_num (NUMERAL 0))) /\ ((fun y0 : real => (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) y0) (real_of_num (NUMERAL 0)))) x0).
Definition term265 (x0 : real) := (real_ge x0 (real_of_num (NUMERAL 0))) /\ ((fun y0 : real => (real_ge y0 (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 y0) (real_of_num (NUMERAL 0))))) x0).
Definition term1 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term52 := fun y0 : real => (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y0)) (real_abs (real_abs y0))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add (real_abs y0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_abs y0)))) (real_of_num (NUMERAL 0))).
Definition term224 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term60 := fun y0 : real => real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y0)) (real_abs (real_abs y0))) (real_of_num (NUMERAL 0)).
Definition term400 (x0 : nat) (x1 : nat) := real_gt (real_of_num x0) (real_of_num x1).
Definition term388 := Nat.mul (BIT0 (BIT1 0)) (BIT1 0).
Definition term113 (x0 : real) := (real_ge (real_abs x0) (real_of_num (NUMERAL 0))) /\ ((fun y0 : real => (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 y0) (real_of_num (NUMERAL 0)))) (real_abs x0)).
Definition term165 (x0 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0))).
Definition term390 := real_of_num (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (NUMERAL (BIT1 0))).
Definition term225 := real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term237 (x0 : real) := real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term203 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term335 (x0 : real) := real_gt (real_sub (real_add x0 (real_neg x0)) (real_of_num (NUMERAL 0))).
Definition term144 (x0 : real) := real_gt (real_sub (real_add x0 (real_abs x0)) (real_of_num (NUMERAL 0))).
Definition term365 (x0 : real) := (fun y0 : real => (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) y0) (real_of_num (NUMERAL 0)))) (real_neg x0).
Definition term21 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term233 (x0 : real) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term49 (x0 : real) := or (real_gt (real_sub (real_abs (real_abs x0)) (real_abs x0)) (real_of_num (NUMERAL 0))).
Definition term402 := (~ (forall y0 : real, (real_abs (real_abs y0)) = (real_abs y0))) -> False.
Definition term343 (x0 : real) := ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))))) \/ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))))).
Definition term147 (x0 : real) := real_gt (real_of_num (NUMERAL 0)) (real_abs x0).
Definition term222 := real_of_num (NUMERAL (BIT0 (BIT1 0))).
Definition term133 (x0 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_abs x0)).
Definition term338 (x0 : real) := and (real_ge (real_neg x0) (real_of_num (NUMERAL 0))).
Definition term394 (x0 : real) := real_gt (real_sub (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_neg x0)) (real_of_num (NUMERAL 0))).
Definition term329 (x0 : real) := real_gt (real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg x0)) (real_of_num (NUMERAL 0))).
Definition term135 (x0 : real) := real_gt (real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_abs x0)) (real_of_num (NUMERAL 0))).
Definition term324 (x0 : real) := real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg x0)) (real_of_num (NUMERAL 0)).
Definition term367 (x0 : real) := (real_gt (real_of_num (NUMERAL 0)) x0) /\ ((fun y0 : real => (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) y0) (real_of_num (NUMERAL 0)))) (real_neg x0)).
Definition term260 (x0 : real) := (real_gt (real_of_num (NUMERAL 0)) x0) /\ ((fun y0 : real => (real_ge y0 (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 y0) (real_of_num (NUMERAL 0))))) (real_neg x0)).
Definition term297 (x0 : real) := and (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_of_num (NUMERAL 0))).
Definition term232 (x0 : real) := and (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))).
Definition term196 (x0 : real) := and (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term384 (x0 : nat) (x1 : nat) := real_mul (real_of_num x0) (real_neg (real_of_num x1)).
Definition term5 (x0 : real) := (fun y0 : real => (real_abs (real_abs y0)) = (real_abs y0)) x0.
Definition term231 (x0 : real) := and (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0))).
Definition term99 (x0 : real) := and (real_gt (real_add (real_abs (real_abs x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0))).
Definition term39 (x0 : real) := @eq real (real_neg (real_sub (real_abs (real_abs x0)) (real_abs x0))).
Definition term207 := real_mul (real_of_num (NUMERAL 0)).
Definition term332 (x0 : real) := real_add x0 (real_neg x0).
Definition term164 (x0 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term190 (x0 : real) (x1 : real) := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0)) x1.
Definition term306 (x0 : real) := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term243 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0).
Definition term228 (x0 : real) := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0).
Definition term193 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) x0).
Definition term198 (x0 : real) := and ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))).
Definition term226 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0.
Definition term94 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term119 (x0 : real) := real_ge (real_abs x0) (real_of_num (NUMERAL 0)).
Definition term220 := NUMERAL (BIT0 (BIT1 0)).
Definition term289 (x0 : real) := real_sub (real_add x0 x0).
Definition term106 (x0 : real) := (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg (real_abs x0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_neg (real_abs x0))) (real_of_num (NUMERAL 0))).
Definition term101 (x0 : real) := (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_abs (real_abs x0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_abs (real_abs x0))) (real_of_num (NUMERAL 0))).
Definition term103 (x0 : real) := ((real_ge (real_abs x0) (real_of_num (NUMERAL 0))) /\ ((fun y0 : real => (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 y0) (real_of_num (NUMERAL 0)))) (real_abs x0))) \/ ((real_gt (real_of_num (NUMERAL 0)) (real_abs x0)) /\ ((fun y0 : real => (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 y0) (real_of_num (NUMERAL 0)))) (real_neg (real_abs x0)))).
Definition term303 (x0 : real) := real_sub (real_of_num (NUMERAL 0)) x0.
Definition term172 (x0 : real) := real_add x0 (real_neg (real_abs x0)).
Definition term229 (x0 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term211 (x0 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_of_num (NUMERAL (BIT1 0))) x0)) (real_of_num (NUMERAL 0)).
Definition term95 (x0 : real) := real_gt (real_add (real_abs (real_abs x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term88 (x0 : real) := real_gt (real_add (real_abs (real_abs x0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) x0)).
Definition term16 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0).
Definition term382 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term192 (x0 : real) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) x0) (real_of_num (NUMERAL 0))).
Definition term34 := real_mul (real_of_num (NUMERAL (BIT1 0))).
Definition term66 := fun y0 : real => ((fun y1 : real => real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y1)) (real_abs (real_abs y1))) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_add (real_abs y1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_abs y1)))) (real_of_num (NUMERAL 0))) y0).
Definition term287 (x0 : real) := real_gt (real_add x0 x0) (real_of_num (NUMERAL 0)).
Definition term160 (x0 : real) := real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg (real_abs x0))).
Definition term11 := exists y0 : real, ~ ((real_abs (real_abs y0)) = (real_abs y0)).
Definition term346 (x0 : real) := (real_gt (real_add (real_abs x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_abs x0) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_abs x0))) (real_of_num (NUMERAL 0))).
Definition term184 (x0 : real) := and (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg (real_abs x0))) (real_of_num (NUMERAL 0))).
Definition term100 (x0 : real) := and (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_abs (real_abs x0))) (real_of_num (NUMERAL 0))).
Definition term62 (x0 : real) := (fun y0 : real => real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y0)) (real_abs (real_abs y0))) (real_of_num (NUMERAL 0))) x0.
Definition term58 := exists y0 : real, ((fun y1 : real => real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y1)) (real_abs (real_abs y1))) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_add (real_abs y1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_abs y1)))) (real_of_num (NUMERAL 0))) y0).
Definition term97 (x0 : real) := real_gt (real_add (real_abs (real_abs x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term90 (x0 : real) := real_gt (real_add (real_abs (real_abs x0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) x0)) (real_of_num (NUMERAL 0)).
Definition term217 := Nat.add (BIT1 0) (BIT1 0).
Definition term105 (x0 : real) := (fun y0 : real => (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 y0) (real_of_num (NUMERAL 0)))) (real_neg (real_abs x0)).
Definition term109 (x0 : real) := (real_gt (real_of_num (NUMERAL 0)) (real_abs x0)) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg (real_abs x0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_neg (real_abs x0))) (real_of_num (NUMERAL 0)))).
Definition term385 (x0 : nat) (x1 : nat) := real_neg (real_of_num (Nat.mul x0 x1)).
Definition term247 (x0 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term242 (x0 : real) := real_gt (real_add x0 (real_mul (real_of_num (NUMERAL (BIT1 0))) x0)).
Definition term304 (x0 : real) := real_add (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term65 (x0 : real) := ((fun y0 : real => real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y0)) (real_abs (real_abs y0))) (real_of_num (NUMERAL 0))) x0) \/ ((fun y0 : real => real_gt (real_add (real_abs y0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_abs y0)))) (real_of_num (NUMERAL 0))) x0).
Definition term25 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_neg (real_of_num x1)).
Definition term392 (x0 : real) := real_sub (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_neg x0)).
Definition term150 (x0 : real) := real_add (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0)).
Definition term317 (x0 : real) := real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term322 (x0 : real) := real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg x0)).
Definition term96 (x0 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_abs (real_abs x0))).
Definition term358 (x0 : real) := real_gt (real_add (real_abs x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0))).
Definition term351 (x0 : real) := real_gt (real_add (real_abs x0) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_abs x0))).
Definition term127 (x0 : real) := real_ge (real_abs x0).
Definition term46 (x0 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0)) (real_abs (real_abs x0))).
Definition term188 (x0 : real) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0)) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0))) (real_of_num (NUMERAL 0)))).
Definition term375 := real_gt (real_sub (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term28 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term345 (x0 : real) := (((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))))) \/ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))))))) \/ (((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))) /\ (((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))) /\ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))))).
Definition term44 (x0 : real) := real_gt (real_add (real_abs x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_abs x0)))) (real_of_num (NUMERAL 0)).
Definition term157 (x0 : real) := real_neg (real_abs x0).
Definition term32 := real_of_num (NUMERAL (BIT1 0)).
Definition term327 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0).
Definition term294 (x0 : real) := real_add (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0).
Definition term158 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term369 (x0 : real) := (fun y0 : real => (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) y0) (real_of_num (NUMERAL 0)))) x0.
Definition term218 := BIT0 (BIT1 0).
Definition term50 (x0 : real) := or (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0)) (real_abs (real_abs x0))) (real_of_num (NUMERAL 0))).
Definition term364 := fun y0 : real => (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) y0) (real_of_num (NUMERAL 0))).
Definition term248 (x0 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term244 (x0 : real) := real_gt (real_add x0 (real_mul (real_of_num (NUMERAL (BIT1 0))) x0)) (real_of_num (NUMERAL 0)).
Definition term140 (x0 : real) := real_sub (real_add x0 (real_abs x0)) (real_of_num (NUMERAL 0)).
Definition term182 (x0 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0))).
Definition term371 (x0 : real) := or ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((fun y0 : real => (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) y0) (real_of_num (NUMERAL 0)))) x0)).
Definition term267 (x0 : real) := or ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((fun y0 : real => (real_ge y0 (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 y0) (real_of_num (NUMERAL 0))))) x0)).
Definition term87 (x0 : real) := real_add x0 (real_abs (real_abs x0)).
Definition term74 := fun y0 : real => (fun y1 : real => real_gt (real_add (real_abs y1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_abs y1)))) (real_of_num (NUMERAL 0))) y0.
Definition term69 := fun y0 : real => (fun y1 : real => real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y1)) (real_abs (real_abs y1))) (real_of_num (NUMERAL 0))) y0.
Definition term208 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term37 (x0 : real) := real_add (real_abs x0).
Definition term98 (x0 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_abs (real_abs x0))) (real_of_num (NUMERAL 0)).
Definition term148 (x0 : real) := real_gt (real_sub (real_of_num (NUMERAL 0)) (real_abs x0)) (real_of_num (NUMERAL 0)).
Definition term47 (x0 : real) := real_gt (real_sub (real_abs (real_abs x0)) (real_abs x0)) (real_of_num (NUMERAL 0)).
Definition term125 (x0 : real) := real_add (real_abs x0) (real_of_num (NUMERAL 0)).
Definition term391 := real_mul (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term383 (x0 : real) := real_mul (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) x0.
Definition term145 (x0 : real) := real_gt (real_add x0 (real_abs x0)).
Definition term277 (x0 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_of_num (NUMERAL 0)).
Definition term7 (x0 : real) := ~ ((fun y0 : real => (real_abs (real_abs y0)) = (real_abs y0)) x0).
Definition term257 (x0 : real) := (fun y0 : real => (real_ge y0 (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 y0) (real_of_num (NUMERAL 0))))) (real_neg x0).
Definition term19 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0)) (real_abs (real_abs x0))).
Definition term9 := fun y0 : real => ~ ((fun y1 : real => (real_abs (real_abs y1)) = (real_abs y1)) y0).
Definition term352 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_abs x0)).
Definition term376 := real_gt (real_sub (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term321 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg x0).
Definition term380 (x0 : real) := real_gt (real_sub (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_neg x0)) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term331 (x0 : real) := real_gt (real_sub (real_add x0 (real_neg x0)) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term320 (x0 : real) := real_gt (real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg x0)) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term171 (x0 : real) := real_gt (real_sub (real_add x0 (real_neg (real_abs x0))) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term155 (x0 : real) := real_gt (real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg (real_abs x0))) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term138 (x0 : real) := real_gt (real_sub (real_add x0 (real_abs x0)) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term129 (x0 : real) := real_gt (real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_abs x0)) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term213 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term201 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_of_num (NUMERAL (BIT1 0))) x0).
Definition term151 (x0 : real) := real_gt (real_sub (real_of_num (NUMERAL 0)) (real_abs x0)).
Definition term221 := real_of_num (Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term259 (x0 : real) := and (real_gt (real_of_num (NUMERAL 0)) x0).
Definition term234 (x0 : real) := and ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))).
Definition term26 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term298 (x0 : real) := (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 x0) (real_of_num (NUMERAL 0))).
Definition term63 (x0 : real) := or ((fun y0 : real => real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y0)) (real_abs (real_abs y0))) (real_of_num (NUMERAL 0))) x0).
Definition term4 := fun y0 : real => (real_abs (real_abs y0)) = (real_abs y0).
Definition term149 (x0 : real) := real_sub (real_of_num (NUMERAL 0)) (real_abs x0).
Definition term197 (x0 : real) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0))).
Definition term325 (x0 : real) := real_sub (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0)).
Definition term313 (x0 : real) := real_sub (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)).
Definition term292 (x0 : real) := real_sub (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0)).
Definition term285 := real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term134 (x0 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_abs x0)) (real_of_num (NUMERAL 0)).
Definition term360 (x0 : real) := and (real_gt (real_add (real_abs x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0))) (real_of_num (NUMERAL 0))).
Definition term185 (x0 : real) := and (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0))) (real_of_num (NUMERAL 0))).
Definition term291 (x0 : real) := real_sub (real_add x0 x0) (real_of_num (NUMERAL 0)).
Definition term308 (x0 : real) := real_ge (real_neg x0) (real_of_num (NUMERAL 0)).
Definition term183 (x0 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0))) (real_of_num (NUMERAL 0)).
Definition term362 (x0 : real) := (fun y0 : real => (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) y0) (real_of_num (NUMERAL 0)))) (real_abs x0).
Definition term110 (x0 : real) := (fun y0 : real => (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 y0) (real_of_num (NUMERAL 0)))) (real_abs x0).
Definition term307 (x0 : real) := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)).
Definition term245 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0)).
Definition term230 (x0 : real) := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0)).
Definition term194 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) x0) (real_of_num (NUMERAL 0)).
Definition term258 (x0 : real) := (real_ge (real_neg x0) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg x0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_neg x0)) (real_of_num (NUMERAL 0)))).
Definition term114 (x0 : real) := (real_ge (real_abs x0) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_abs x0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_abs x0)) (real_of_num (NUMERAL 0)))).
Definition term227 (x0 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term209 (x0 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_of_num (NUMERAL (BIT1 0))) x0)).
Definition term41 (x0 : real) := real_gt (real_add (real_abs x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_abs x0)))).
Definition term205 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term299 (x0 : real) := (real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))).
Definition term263 (x0 : real) := (real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 x0) (real_of_num (NUMERAL 0)))).
Definition term395 (x0 : real) := (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))).
Definition term251 (x0 : real) := (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term117 (x0 : real) := ((real_ge (real_abs x0) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_abs x0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_abs x0)) (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_of_num (NUMERAL 0)) (real_abs x0)) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg (real_abs x0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_neg (real_abs x0))) (real_of_num (NUMERAL 0))))).
Definition term167 (x0 : real) := real_gt (real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg (real_abs x0))) (real_of_num (NUMERAL 0))).
Definition term284 := real_add (real_of_num (NUMERAL 0)).
Definition term73 := or (exists y0 : real, real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y0)) (real_abs (real_abs y0))) (real_of_num (NUMERAL 0))).
Definition term276 (x0 : real) := real_ge (real_sub x0 (real_of_num (NUMERAL 0))).
Definition term54 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term272 (x0 : real) := real_ge (real_sub x0 (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term378 (x0 : real) := real_gt (real_sub (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term286 (x0 : real) := real_gt (real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_of_num (NUMERAL 0))).
Definition term166 (x0 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0))) (real_of_num (NUMERAL 0)).
Definition term93 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_abs (real_abs x0)).
Definition term51 (x0 : real) := (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0)) (real_abs (real_abs x0))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add (real_abs x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_abs x0)))) (real_of_num (NUMERAL 0))).
Definition term137 (x0 : real) := real_gt (real_add x0 (real_abs x0)) (real_of_num (NUMERAL 0)).
Definition term15 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0)) (real_abs (real_abs x0)).
Definition term170 (x0 : real) := real_gt (real_add x0 (real_neg (real_abs x0))) (real_of_num (NUMERAL 0)).
Definition term29 := NUMERAL (BIT1 0).
Definition term175 (x0 : real) := real_sub (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0))).
Definition term59 := (exists y0 : real, (fun y1 : real => real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y1)) (real_abs (real_abs y1))) (real_of_num (NUMERAL 0))) y0) \/ (exists y0 : real, (fun y1 : real => real_gt (real_add (real_abs y1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_abs y1)))) (real_of_num (NUMERAL 0))) y0).
Definition term282 := real_sub (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term53 := exists y0 : real, (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y0)) (real_abs (real_abs y0))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add (real_abs y0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_abs y0)))) (real_of_num (NUMERAL 0))).
Definition term246 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term236 (x0 : real) := real_add x0 (real_mul (real_of_num (NUMERAL (BIT1 0))) x0).
Definition term355 (x0 : real) := real_add (real_abs x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0)).
Definition term347 (x0 : real) := real_add (real_abs x0) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_abs x0)).
Definition term269 (x0 : real) := ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 x0) (real_of_num (NUMERAL 0)))))) \/ ((real_gt (real_of_num (NUMERAL 0)) x0) /\ ((real_ge (real_neg x0) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg x0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_neg x0)) (real_of_num (NUMERAL 0)))))).
Definition term300 (x0 : real) := (real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0))))).
Definition term266 (x0 : real) := (real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 x0) (real_of_num (NUMERAL 0))))).
Definition term309 (x0 : real) := real_ge (real_sub (real_neg x0) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term120 (x0 : real) := real_ge (real_sub (real_abs x0) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term210 := real_gt (real_of_num (NUMERAL 0)).
Definition term79 := @eq Prop ((exists y0 : real, real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y0)) (real_abs (real_abs y0))) (real_of_num (NUMERAL 0))) \/ (exists y0 : real, real_gt (real_add (real_abs y0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_abs y0)))) (real_of_num (NUMERAL 0)))).
Definition term78 := @eq Prop ((exists y0 : real, (fun y1 : real => real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y1)) (real_abs (real_abs y1))) (real_of_num (NUMERAL 0))) y0) \/ (exists y0 : real, (fun y1 : real => real_gt (real_add (real_abs y1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_abs y1)))) (real_of_num (NUMERAL 0))) y0)).
