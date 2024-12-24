Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term106 (x0 : real) (x1 : real) := (fun y0 : real => (real_mul (real_abs x0) (real_abs y0)) = (real_abs (real_mul x0 y0))) x1.
Definition term310 (x0 : real) (x1 : real) := or ((real_ge (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0))) /\ (((real_ge x1 (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))) /\ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x1) (real_of_num (NUMERAL 0)))))).
Definition term181 (x0 : real) (x1 : real) := or ((real_ge (real_sub x0 x1) (real_of_num (NUMERAL 0))) /\ (((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_sub x0 x1))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_add x1 (real_sub x0 x1))) (real_of_num (NUMERAL 0)))))).
Definition term277 (x0 : real) (x1 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term335 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term41 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term268 (x0 : real) (x1 : real) := real_add (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))).
Definition term48 (x0 : real) (x1 : real) := real_sub (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term60 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term396 (x0 : real) (x1 : real) := real_abs (real_add (sqrt x0) (sqrt x1)).
Definition term88 (x0 : real) (x1 : real) := or (real_gt (real_sub (real_mul (real_sub x0 x1) (real_add x0 x1)) (real_sub (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0))).
Definition term250 (x0 : real) := real_add (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term228 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term204 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term325 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0)) (real_of_num (NUMERAL 0)).
Definition term315 (x0 : real) := (real_gt (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0))).
Definition term125 (x0 : real) (x1 : real) := real_sub (real_abs (real_sub x0 x1)) (real_abs (real_add x0 x1)).
Definition term173 (x0 : real) (x1 : real) := (real_gt (real_of_num (NUMERAL 0)) (real_sub x0 x1)) /\ ((fun y0 : real => ((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) y0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_add x1 y0)) (real_of_num (NUMERAL 0))))) (real_neg (real_sub x0 x1))).
Definition term38 := real_of_num (NUMERAL 0).
Definition term413 (x0 : real) (x1 : real) := real_add (sqrt x0) (sqrt x1).
Definition term150 (x0 : real) (x1 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x0 x1).
Definition term33 (x0 : real) (x1 : real) := real_add (real_mul x0 x1) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term187 (x0 : real) (x1 : real) := real_sub (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term259 (x0 : real) (x1 : real) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x1) (real_of_num (NUMERAL 0))).
Definition term342 (x0 : real) := (fun y0 : real => real_le (real_of_num (NUMERAL 0)) (real_abs y0)) x0.
Definition term10 (x0 : real) (x1 : real) := real_add (real_mul x0 (real_add x0 x1)) (real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_add x0 x1)).
Definition term72 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term188 (x0 : real) (x1 : real) := real_sub (real_sub x0 x1) (real_of_num (NUMERAL 0)).
Definition term343 (x0 : real) := real_le (real_of_num (NUMERAL 0)) (real_abs x0).
Definition term142 (x0 : real) (x1 : real) := real_add x0 (real_add (real_abs (real_sub x0 x1)) x1).
Definition term364 (x0 : real) (x1 : real) := (real_le (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) x1) -> real_le x0 (sqrt x1).
Definition term9 (x0 : real) (x1 : real) := real_mul (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_add x0 x1).
Definition term129 (x0 : real) (x1 : real) := real_gt (real_sub (real_abs (real_sub x0 x1)) (real_abs (real_add x0 x1))).
Definition term431 (x0 : real) (x1 : real) := real_le (real_abs (real_sub (sqrt x0) (sqrt x1))) (sqrt (real_abs (real_sub x0 x1))).
Definition term286 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x1).
Definition term25 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term26 (x0 : real) (x1 : real) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1.
Definition term422 (x0 : real) := (fun y0 : real => (real_le (real_of_num (NUMERAL 0)) y0) -> (real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0) x0.
Definition term243 := real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term159 (x0 : real) (x1 : real) := real_gt (real_add (real_abs (real_sub x0 x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x0 x1))).
Definition term146 (x0 : real) (x1 : real) := real_gt (real_add (real_abs (real_sub x0 x1)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 x1))).
Definition term32 (x0 : real) (x1 : real) := real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_add (real_mul x0 x1) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))))).
Definition term67 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))).
Definition term402 (x0 : real) (x1 : real) := True /\ (real_le (real_abs (real_sub (sqrt x0) (sqrt x1))) (real_abs (real_add (sqrt x0) (sqrt x1)))).
Definition term314 := S (Nat.add (BIT1 0) 0).
Definition term134 (x0 : real) (x1 : real) := ((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_add x0 x1))) (real_abs (real_sub x0 x1))) (real_of_num (NUMERAL 0))).
Definition term226 (x0 : real) (x1 : real) := real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_sub x0 x1))) (real_of_num (NUMERAL 0)).
Definition term17 (x0 : real) (x1 : real) := real_add (real_mul x0 (real_add x0 x1)).
Definition term308 (x0 : real) (x1 : real) := and (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))).
Definition term391 := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> forall y0 : real, forall y1 : real, (exists y2 : real, (real_le y0 y2) /\ (real_le y2 y1)) -> real_le y0 y1.
Definition term368 := (forall y0 : real, forall y1 : real, (real_le (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) y1) -> real_le y0 (sqrt y1)) -> forall y0 : real, forall y1 : real, (real_le (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) y1) -> real_le y0 (sqrt y1).
Definition term356 := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y1 y2)) -> real_le (real_mul y0 y1) (real_mul y0 y2)) -> forall y0 : real, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y0 y2)) -> real_le (real_mul y1 y0) (real_mul y1 y2).
Definition term386 (x0 : real) (x1 : real) := exists y0 : real, (real_le x0 y0) /\ (real_le y0 x1).
Definition term337 (x0 : real) (x1 : real) := (~ (((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) x1)) -> real_le (real_abs (real_sub x0 x1)) (real_abs (real_add x0 x1)))) -> False.
Definition term93 (x0 : real) (x1 : real) := (~ ((real_mul (real_sub x0 x1) (real_add x0 x1)) = (real_sub (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))))) -> False.
Definition term97 (x0 : real) := fun y0 : real => (real_abs (real_mul x0 y0)) = (real_mul (real_abs x0) (real_abs y0)).
Definition term218 (x0 : real) (x1 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x1).
Definition term387 (x0 : real) (x1 : real) := fun y0 : real => (real_le x0 y0) /\ (real_le y0 x1).
Definition term200 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term423 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) -> (real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = x0.
Definition term318 (x0 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0)).
Definition term185 (x0 : real) (x1 : real) := real_ge (real_sub (real_sub x0 x1) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term295 (x0 : real) (x1 : real) := real_add x1 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term370 (x0 : real) (x1 : real) := real_abs (real_sub (sqrt x0) (sqrt x1)).
Definition term245 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0.
Definition term242 := real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term78 := real_neg (real_of_num (NUMERAL 0)).
Definition term405 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) -> real_le (real_of_num (NUMERAL 0)) (sqrt x0).
Definition term22 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x0).
Definition term417 (x0 : real) (x1 : real) := real_le (real_mul (real_abs (real_sub (sqrt x0) (sqrt x1))) (real_abs (real_add (sqrt x0) (sqrt x1)))).
Definition term374 (x0 : real) (x1 : real) := real_le (real_mul (real_abs (real_sub (sqrt x0) (sqrt x1))) (real_abs (real_sub (sqrt x0) (sqrt x1)))).
Definition term18 (x0 : real) (x1 : real) := real_add (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul x0 x1)).
Definition term36 (x0 : real) (x1 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1).
Definition term121 (x0 : real) (x1 : real) := ~ (real_le (real_abs (real_sub x0 x1)) (real_abs (real_add x0 x1))).
Definition term201 (x0 : real) (x1 : real) := real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term359 (x0 : real) := (fun y0 : real => (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) x0.
Definition term203 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) x0.
Definition term117 (x0 : real) := real_ge x0 (real_of_num (NUMERAL 0)).
Definition term109 (x0 : real) (x1 : real) := (real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) x1).
Definition term313 := Peano.lt (NUMERAL 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term400 (x0 : real) (x1 : real) := real_le (real_abs (real_sub (sqrt x0) (sqrt x1))) (real_abs (real_add (sqrt x0) (sqrt x1))).
Definition term307 (x0 : real) (x1 : real) := ((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) /\ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x1) (real_of_num (NUMERAL 0)))).
Definition term260 (x0 : real) (x1 : real) := ((real_ge x1 (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))) /\ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x1) (real_of_num (NUMERAL 0)))).
Definition term394 (x0 : real) (x1 : real) := (exists y0 : real, (real_le (real_mul (real_abs (real_sub (sqrt x0) (sqrt x1))) (real_abs (real_sub (sqrt x0) (sqrt x1)))) y0) /\ (real_le y0 (real_abs (real_sub x0 x1)))) -> real_le (real_mul (real_abs (real_sub (sqrt x0) (sqrt x1))) (real_abs (real_sub (sqrt x0) (sqrt x1)))) (real_abs (real_sub x0 x1)).
Definition term247 (x0 : real) := real_sub (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0).
Definition term225 (x0 : real) := real_sub (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0).
Definition term287 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)).
Definition term252 (x0 : real) := real_add (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0)).
Definition term230 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0)).
Definition term138 (x0 : real) (x1 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 x1).
Definition term34 (x0 : real) (x1 : real) := real_add (real_add (real_mul x0 x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term274 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1.
Definition term119 (x0 : real) := and (real_ge x0 (real_of_num (NUMERAL 0))).
Definition term371 (x0 : real) (x1 : real) := real_pow (real_abs (real_sub (sqrt x0) (sqrt x1))) (NUMERAL (BIT0 (BIT1 0))).
Definition term352 (x0 : real) (x1 : real) (x2 : real) := real_le (real_mul x1 x0) (real_mul x1 x2).
Definition term115 (x0 : real) := real_add x0 (real_of_num (NUMERAL 0)).
Definition term136 (x0 : real) (x1 : real) (x2 : real) := (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) x2) /\ (real_gt (real_add x0 (real_mul (real_of_num (NUMERAL (BIT1 0))) x1)) x2).
Definition term293 (x0 : real) (x1 : real) := real_add x0 (real_add x1 (real_neg (real_sub x0 x1))).
Definition term108 (x0 : real) (x1 : real) := ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) x1)) /\ (~ (real_le (real_abs (real_sub x0 x1)) (real_abs (real_add x0 x1)))).
Definition term8 (x0 : real) (x1 : real) := real_mul (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term275 (x0 : real) (x1 : real) := real_add (real_of_num (NUMERAL 0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term94 (x0 : real) (x1 : real) := ((~ ((real_mul (real_sub x0 x1) (real_add x0 x1)) = (real_sub (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))))) -> False) -> (real_mul (real_sub x0 x1) (real_add x0 x1)) = (real_sub (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term44 (x0 : real) (x1 : real) := real_add (real_add (real_mul x0 x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1))).
Definition term320 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term75 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term80 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term434 := forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_abs (real_sub (sqrt y0) (sqrt y1))) (sqrt (real_abs (real_sub y0 y1))).
Definition term390 := forall y0 : real, forall y1 : real, (exists y2 : real, (real_le y0 y2) /\ (real_le y2 y1)) -> real_le y0 y1.
Definition term379 (x0 : real) := forall y0 : real, forall y1 : real, ((real_le x0 y0) /\ (real_le y0 y1)) -> real_le x0 y1.
Definition term377 := forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2.
Definition term360 := forall y0 : real, forall y1 : real, (real_le (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) y1) -> real_le y0 (sqrt y1).
Definition term355 := forall y0 : real, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y0 y2)) -> real_le (real_mul y1 y0) (real_mul y1 y2).
Definition term354 (x0 : real) := forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le x0 y1)) -> real_le (real_mul y0 x0) (real_mul y0 y1).
Definition term346 (x0 : real) := forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le y0 y1)) -> real_le (real_mul x0 y0) (real_mul x0 y1).
Definition term344 := forall y0 : real, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y1 y2)) -> real_le (real_mul y0 y1) (real_mul y0 y2).
Definition term104 := forall y0 : real, forall y1 : real, (real_mul (real_abs y0) (real_abs y1)) = (real_abs (real_mul y0 y1)).
Definition term103 := forall y0 : real, forall y1 : real, (real_abs (real_mul y0 y1)) = (real_mul (real_abs y0) (real_abs y1)).
Definition term271 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term222 (x0 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0).
Definition term53 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term58 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term429 (x0 : real) (x1 : real) := exists y0 : real, (real_le (real_mul (real_abs (real_sub (sqrt x0) (sqrt x1))) (real_abs (real_sub (sqrt x0) (sqrt x1)))) y0) /\ (real_le y0 (real_abs (real_sub x0 x1))).
Definition term306 (x0 : real) (x1 : real) := (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_neg (real_sub x0 x1)))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_add x1 (real_neg (real_sub x0 x1)))) (real_of_num (NUMERAL 0))).
Definition term258 (x0 : real) (x1 : real) := (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_sub x0 x1))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_add x1 (real_sub x0 x1))) (real_of_num (NUMERAL 0))).
Definition term165 (x0 : real) (x1 : real) := (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_abs (real_sub x0 x1)))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_add x1 (real_abs (real_sub x0 x1)))) (real_of_num (NUMERAL 0))).
Definition term294 (x0 : real) (x1 : real) := real_add x1 (real_neg (real_sub x0 x1)).
Definition term113 (x0 : real) := real_sub x0 (real_of_num (NUMERAL 0)).
Definition term426 (x0 : real) (x1 : real) := real_le (real_abs (real_sub x0 x1)).
Definition term432 (x0 : real) (x1 : real) := ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) x1)) -> real_le (real_abs (real_sub (sqrt x0) (sqrt x1))) (sqrt (real_abs (real_sub x0 x1))).
Definition term244 := real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term266 (x0 : real) (x1 : real) := real_sub (real_of_num (NUMERAL 0)) (real_sub x0 x1).
Definition term174 (x0 : real) (x1 : real) := (real_gt (real_of_num (NUMERAL 0)) (real_sub x0 x1)) /\ (((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_neg (real_sub x0 x1)))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_add x1 (real_neg (real_sub x0 x1)))) (real_of_num (NUMERAL 0))))).
Definition term126 (x0 : real) (x1 : real) := real_add (real_abs (real_sub x0 x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_add x0 x1))).
Definition term383 (x0 : real) (x1 : real) (x2 : real) := ((real_le x1 x0) /\ (real_le x0 x2)) -> real_le x1 x2.
Definition term208 := Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term326 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0).
Definition term366 (x0 : real) (x1 : real) := real_le x0 (sqrt x1).
Definition term348 (x0 : real) (x1 : real) := forall y0 : real, ((real_le (real_of_num (NUMERAL 0)) x1) /\ (real_le x0 y0)) -> real_le (real_mul x1 x0) (real_mul x1 y0).
Definition term35 (x0 : real) (x1 : real) := real_add (real_mul x0 x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1)).
Definition term46 (x0 : real) := real_add (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term154 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_abs (real_sub x0 x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term114 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term156 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_abs (real_sub x0 x1)).
Definition term415 (x0 : real) (x1 : real) := real_sub (real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (sqrt x1) (NUMERAL (BIT0 (BIT1 0)))).
Definition term403 (x0 : real) (x1 : real) := ((real_le (real_of_num (NUMERAL 0)) (sqrt x0)) /\ (real_le (real_of_num (NUMERAL 0)) (sqrt x1))) -> real_le (real_abs (real_sub (sqrt x0) (sqrt x1))) (real_abs (real_add (sqrt x0) (sqrt x1))).
Definition term373 (x0 : real) (x1 : real) := real_le (real_pow (real_abs (real_sub (sqrt x0) (sqrt x1))) (NUMERAL (BIT0 (BIT1 0)))).
Definition term193 (x0 : real) (x1 : real) := real_ge (real_sub (real_sub x0 x1) (real_of_num (NUMERAL 0))).
Definition term198 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_sub x0 x1)).
Definition term182 (x0 : real) (x1 : real) := ((real_ge (real_sub x0 x1) (real_of_num (NUMERAL 0))) /\ (((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_sub x0 x1))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_add x1 (real_sub x0 x1))) (real_of_num (NUMERAL 0)))))) \/ ((real_gt (real_of_num (NUMERAL 0)) (real_sub x0 x1)) /\ (((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_neg (real_sub x0 x1)))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_add x1 (real_neg (real_sub x0 x1)))) (real_of_num (NUMERAL 0)))))).
Definition term118 (x0 : real) := and (real_le (real_of_num (NUMERAL 0)) x0).
Definition term414 (x0 : real) (x1 : real) := real_mul (real_sub (sqrt x0) (sqrt x1)) (real_add (sqrt x0) (sqrt x1)).
Definition term420 (x0 : real) (x1 : real) := real_le (real_abs (real_sub (real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (sqrt x1) (NUMERAL (BIT0 (BIT1 0)))))) (real_abs (real_sub x0 x1)).
Definition term433 (x0 : real) := forall y0 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) y0)) -> real_le (real_abs (real_sub (sqrt x0) (sqrt y0))) (sqrt (real_abs (real_sub x0 y0))).
Definition term135 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0)) x1) x2.
Definition term145 (x0 : real) (x1 : real) := real_add x0 (real_add x1 (real_abs (real_sub x0 x1))).
Definition term169 (x0 : real) (x1 : real) := fun y0 : real => ((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) y0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_add x1 y0)) (real_of_num (NUMERAL 0)))).
Definition term205 := real_neg (real_of_num (Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term276 (x0 : real) (x1 : real) := real_gt (real_sub (real_of_num (NUMERAL 0)) (real_sub x0 x1)).
Definition term289 (x0 : real) (x1 : real) := real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_neg (real_sub x0 x1)))) (real_of_num (NUMERAL 0)).
Definition term101 := fun y0 : real => forall y1 : real, (real_abs (real_mul y0 y1)) = (real_mul (real_abs y0) (real_abs y1)).
Definition term195 (x0 : real) (x1 : real) := real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)).
Definition term19 (x0 : real) (x1 : real) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_add x0 x1).
Definition term328 (x0 : real) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term37 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term61 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term66 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term90 := (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term177 (x0 : real) (x1 : real) := and (real_ge (real_sub x0 x1) (real_of_num (NUMERAL 0))).
Definition term5 (x0 : real) := real_pow x0 (NUMERAL (BIT0 (BIT1 0))).
Definition term1 (x0 : real) (x1 : real) := (real_gt (real_sub (real_mul (real_sub x0 x1) (real_add x0 x1)) (real_sub (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub (real_mul (real_sub x0 x1) (real_add x0 x1)) (real_sub (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))))) (real_of_num (NUMERAL 0))).
Definition term385 (x0 : real) (x1 : real) := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> real_le x0 x1.
Definition term139 (x0 : real) (x1 : real) := real_add (real_abs (real_sub x0 x1)).
Definition term92 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term79 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term389 (x0 : real) := forall y0 : real, (exists y1 : real, (real_le x0 y1) /\ (real_le y1 y0)) -> real_le x0 y0.
Definition term406 (x0 : real) := real_le (real_of_num (NUMERAL 0)) (sqrt x0).
Definition term153 (x0 : real) (x1 : real) := real_add (real_abs (real_sub x0 x1)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term51 (x0 : real) (x1 : real) := real_add (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))))).
Definition term265 := real_sub (real_of_num (NUMERAL 0)).
Definition term388 (x0 : real) (x1 : real) := (exists y0 : real, (real_le x0 y0) /\ (real_le y0 x1)) -> real_le x0 x1.
Definition term297 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x1).
Definition term151 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term246 (x0 : real) (x1 : real) := real_sub (real_add x0 (real_add x1 (real_sub x0 x1))).
Definition term263 (x0 : real) (x1 : real) := real_gt (real_of_num (NUMERAL 0)) (real_sub x0 x1).
Definition term85 := real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term288 (x0 : real) (x1 : real) := real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_neg (real_sub x0 x1)))).
Definition term340 (x0 : real) (x1 : real) := (((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) x1)) -> real_le (real_abs (real_sub x0 x1)) (real_abs (real_add x0 x1))) -> real_le (real_abs (real_sub x0 x1)) (real_abs (real_add x0 x1)).
Definition term212 := real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term416 (x0 : real) (x1 : real) := real_abs (real_sub (real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (sqrt x1) (NUMERAL (BIT0 (BIT1 0))))).
Definition term95 (x0 : real) (x1 : real) := real_abs (real_mul x0 x1).
Definition term317 (x0 : real) := ((real_gt (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0)).
Definition term351 (x0 : real) (x1 : real) (x2 : real) := (real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x1 x2).
Definition term273 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term300 (x0 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term408 (x0 : real) := and (real_le (real_of_num (NUMERAL 0)) (sqrt x0)).
Definition term338 (x0 : real) (x1 : real) := ((~ (((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) x1)) -> real_le (real_abs (real_sub x0 x1)) (real_abs (real_add x0 x1)))) -> False) -> ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) x1)) -> real_le (real_abs (real_sub x0 x1)) (real_abs (real_add x0 x1)).
Definition term127 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_add x0 x1))) (real_abs (real_sub x0 x1)).
Definition term29 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1)).
Definition term296 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add x1 x1).
Definition term219 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0.
Definition term63 := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term316 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_ge (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term179 (x0 : real) (x1 : real) := (real_ge (real_sub x0 x1) (real_of_num (NUMERAL 0))) /\ (((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_sub x0 x1))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_add x1 (real_sub x0 x1))) (real_of_num (NUMERAL 0))))).
Definition term180 (x0 : real) (x1 : real) := or ((real_ge (real_sub x0 x1) (real_of_num (NUMERAL 0))) /\ ((fun y0 : real => ((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) y0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_add x1 y0)) (real_of_num (NUMERAL 0))))) (real_sub x0 x1))).
Definition term110 (x0 : real) (x1 : real) := real_le (real_abs (real_sub x0 x1)) (real_abs (real_add x0 x1)).
Definition term327 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0)).
Definition term264 (x0 : real) (x1 : real) := real_gt (real_sub (real_of_num (NUMERAL 0)) (real_sub x0 x1)) (real_of_num (NUMERAL 0)).
Definition term30 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term73 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term131 (x0 : real) (x1 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_add x0 x1))) (real_abs (real_sub x0 x1))) (real_of_num (NUMERAL 0)).
Definition term86 (x0 : real) (x1 : real) := real_gt (real_sub (real_mul (real_sub x0 x1) (real_add x0 x1)) (real_sub (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term132 (x0 : real) (x1 : real) := and ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) x1)).
Definition term213 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term392 (x0 : real) := (fun y0 : real => forall y1 : real, (exists y2 : real, (real_le y0 y2) /\ (real_le y2 y1)) -> real_le y0 y1) x0.
Definition term361 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) y1) -> real_le y0 (sqrt y1)) x0.
Definition term105 (x0 : real) := (fun y0 : real => forall y1 : real, (real_mul (real_abs y0) (real_abs y1)) = (real_abs (real_mul y0 y1))) x0.
Definition term65 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term13 (x0 : real) (x1 : real) := real_add (real_mul x0 x0) (real_mul x0 x1).
Definition term91 (x0 : nat) (x1 : nat) := real_gt (real_of_num x0) (real_of_num x1).
Definition term21 (x0 : real) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0.
Definition term147 (x0 : real) (x1 : real) := real_gt (real_add x0 (real_add x1 (real_abs (real_sub x0 x1)))).
Definition term395 (x0 : real) (x1 : real) := ((real_le (real_of_num (NUMERAL 0)) (real_abs (real_sub (sqrt x0) (sqrt x1)))) /\ (real_le (real_abs (real_sub (sqrt x0) (sqrt x1))) (real_abs (real_add (sqrt x0) (sqrt x1))))) -> real_le (real_mul (real_abs (real_sub (sqrt x0) (sqrt x1))) (real_abs (real_sub (sqrt x0) (sqrt x1)))) (real_mul (real_abs (real_sub (sqrt x0) (sqrt x1))) (real_abs (real_add (sqrt x0) (sqrt x1)))).
Definition term152 (x0 : real) (x1 : real) := real_add (real_abs (real_sub x0 x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x0 x1)).
Definition term194 (x0 : real) (x1 : real) := real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term321 := S (Nat.add 0 0).
Definition term404 (x0 : real) := (fun y0 : real => (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0)) x0.
Definition term214 := real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term24 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term333 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0.
Definition term241 (x0 : real) := real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term220 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term98 (x0 : real) := fun y0 : real => (real_mul (real_abs x0) (real_abs y0)) = (real_abs (real_mul x0 y0)).
Definition term412 (x0 : real) (x1 : real) := real_abs (real_mul (real_sub (sqrt x0) (sqrt x1)) (real_add (sqrt x0) (sqrt x1))).
Definition term238 (x0 : real) (x1 : real) := real_add x1 (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term111 (x0 : real) := real_le (real_of_num (NUMERAL 0)) x0.
Definition term23 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term398 (x0 : real) (x1 : real) := real_sub (sqrt x0) (sqrt x1).
Definition term192 (x0 : real) (x1 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)).
Definition term178 (x0 : real) (x1 : real) := (real_ge (real_sub x0 x1) (real_of_num (NUMERAL 0))) /\ ((fun y0 : real => ((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) y0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_add x1 y0)) (real_of_num (NUMERAL 0))))) (real_sub x0 x1)).
Definition term130 (x0 : real) (x1 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_add x0 x1))) (real_abs (real_sub x0 x1))).
Definition term312 := real_gt (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term311 (x0 : real) (x1 : real) := ((real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ (((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) /\ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x1) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))))) \/ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ (((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) /\ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x1) (real_of_num (NUMERAL 0)))))).
Definition term211 := real_of_num (NUMERAL (BIT0 (BIT1 0))).
Definition term248 (x0 : real) (x1 : real) := real_sub (real_add x0 (real_add x1 (real_sub x0 x1))) (real_of_num (NUMERAL 0)).
Definition term2 (x0 : real) (x1 : real) := real_mul (real_sub x0 x1) (real_add x0 x1).
Definition term341 (x0 : real) (x1 : real) := (((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) x1)) -> real_le (real_abs (real_sub x0 x1)) (real_abs (real_add x0 x1))) -> ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) x1)) -> real_le (real_abs (real_sub x0 x1)) (real_abs (real_add x0 x1)).
Definition term353 (x0 : real) (x1 : real) (x2 : real) := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y1 y2)) -> real_le (real_mul y0 y1) (real_mul y0 y2)) -> real_le (real_mul x1 x0) (real_mul x1 x2).
Definition term160 (x0 : real) (x1 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_abs (real_sub x0 x1)))).
Definition term397 (x0 : real) (x1 : real) := real_le (real_of_num (NUMERAL 0)) (real_abs (real_sub (sqrt x0) (sqrt x1))).
Definition term77 (x0 : real) (x1 : real) := real_neg (real_sub (real_mul (real_sub x0 x1) (real_add x0 x1)) (real_sub (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term168 (x0 : real) (x1 : real) := ((real_ge (real_sub x0 x1) (real_of_num (NUMERAL 0))) /\ ((fun y0 : real => ((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) y0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_add x1 y0)) (real_of_num (NUMERAL 0))))) (real_sub x0 x1))) \/ ((real_gt (real_of_num (NUMERAL 0)) (real_sub x0 x1)) /\ ((fun y0 : real => ((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) y0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_add x1 y0)) (real_of_num (NUMERAL 0))))) (real_neg (real_sub x0 x1)))).
Definition term262 (x0 : real) (x1 : real) := (real_ge (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0))) /\ (((real_ge x1 (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))) /\ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x1) (real_of_num (NUMERAL 0))))).
Definition term122 (x0 : real) (x1 : real) := real_gt (real_sub (real_abs (real_sub x0 x1)) (real_abs (real_add x0 x1))) (real_of_num (NUMERAL 0)).
Definition term257 (x0 : real) := and (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))).
Definition term410 (x0 : real) (x1 : real) := real_le (real_mul (real_abs (real_sub (sqrt x0) (sqrt x1))) (real_abs (real_sub (sqrt x0) (sqrt x1)))) (real_mul (real_abs (real_sub (sqrt x0) (sqrt x1))) (real_abs (real_add (sqrt x0) (sqrt x1)))).
Definition term143 (x0 : real) (x1 : real) := real_add (real_abs (real_sub x0 x1)) x1.
Definition term303 (x0 : real) (x1 : real) := real_sub (real_add x0 (real_add x1 (real_neg (real_sub x0 x1)))) (real_of_num (NUMERAL 0)).
Definition term123 (x0 : real) (x1 : real) := real_abs (real_sub x0 x1).
Definition term367 (x0 : real) (x1 : real) := (forall y0 : real, forall y1 : real, (real_le (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) y1) -> real_le y0 (sqrt y1)) -> real_le x0 (sqrt x1).
Definition term14 (x0 : real) := real_add (real_mul x0 x0).
Definition term42 := real_mul (real_of_num (NUMERAL 0)).
Definition term299 (x0 : real) (x1 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x1).
Definition term254 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0).
Definition term232 (x0 : real) := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0).
Definition term380 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((real_le x0 y0) /\ (real_le y0 y1)) -> real_le x0 y1) x1.
Definition term358 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le x0 y1)) -> real_le (real_mul y0 x0) (real_mul y0 y1)) x1.
Definition term347 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le y0 y1)) -> real_le (real_mul x0 y0) (real_mul x0 y1)) x1.
Definition term4 (x0 : real) (x1 : real) := real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term215 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0.
Definition term11 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term399 (x0 : real) (x1 : real) := and (real_le (real_of_num (NUMERAL 0)) (real_abs (real_sub (sqrt x0) (sqrt x1)))).
Definition term209 := NUMERAL (BIT0 (BIT1 0)).
Definition term141 (x0 : real) (x1 : real) := real_add (real_abs (real_sub x0 x1)) (real_add x0 x1).
Definition term339 (x0 : real) (x1 : real) := ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) x1)) -> real_le (real_abs (real_sub x0 x1)) (real_abs (real_add x0 x1)).
Definition term349 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((real_le (real_of_num (NUMERAL 0)) x1) /\ (real_le x0 y0)) -> real_le (real_mul x1 x0) (real_mul x1 y0)) x2.
Definition term375 (x0 : real) (x1 : real) := real_le (real_pow (real_abs (real_sub (sqrt x0) (sqrt x1))) (NUMERAL (BIT0 (BIT1 0)))) (real_abs (real_sub x0 x1)).
Definition term71 (x0 : real) := real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term331 (x0 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term189 (x0 : real) (x1 : real) := real_sub (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)).
Definition term100 (x0 : real) := forall y0 : real, (real_mul (real_abs x0) (real_abs y0)) = (real_abs (real_mul x0 y0)).
Definition term64 := real_mul (real_of_num (NUMERAL (BIT1 0))).
Definition term382 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((real_le x1 x0) /\ (real_le x0 y0)) -> real_le x1 y0) x2.
Definition term158 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_abs (real_sub x0 x1))).
Definition term27 (x0 : real) (x1 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1).
Definition term428 (x0 : real) (x1 : real) := (real_le (real_mul (real_abs (real_sub (sqrt x0) (sqrt x1))) (real_abs (real_sub (sqrt x0) (sqrt x1)))) (real_mul (real_abs (real_sub (sqrt x0) (sqrt x1))) (real_abs (real_add (sqrt x0) (sqrt x1))))) /\ (real_le (real_mul (real_abs (real_sub (sqrt x0) (sqrt x1))) (real_abs (real_add (sqrt x0) (sqrt x1)))) (real_abs (real_sub x0 x1))).
Definition term236 (x0 : real) (x1 : real) := real_add x0 (real_add x1 (real_sub x0 x1)).
Definition term137 (x0 : real) (x1 : real) := (real_gt (real_add (real_abs (real_sub x0 x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x0 x1))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_abs (real_sub x0 x1)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 x1))) (real_of_num (NUMERAL 0))).
Definition term430 (x0 : real) (x1 : real) := fun y0 : real => (real_le (real_mul (real_abs (real_sub (sqrt x0) (sqrt x1))) (real_abs (real_sub (sqrt x0) (sqrt x1)))) y0) /\ (real_le y0 (real_abs (real_sub x0 x1))).
Definition term190 (x0 : real) (x1 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term196 (x0 : real) (x1 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_sub x0 x1))) (real_of_num (NUMERAL 0)).
Definition term3 (x0 : real) (x1 : real) := real_sub (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))).
Definition term206 := Nat.add (BIT1 0) (BIT1 0).
Definition term401 (x0 : real) (x1 : real) := (real_le (real_of_num (NUMERAL 0)) (real_abs (real_sub (sqrt x0) (sqrt x1)))) /\ (real_le (real_abs (real_sub (sqrt x0) (sqrt x1))) (real_abs (real_add (sqrt x0) (sqrt x1)))).
Definition term407 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) -> (real_le (real_of_num (NUMERAL 0)) (sqrt x0)) = True.
Definition term175 (x0 : real) (x1 : real) := (fun y0 : real => ((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) y0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_add x1 y0)) (real_of_num (NUMERAL 0))))) (real_sub x0 x1).
Definition term120 (x0 : real) (x1 : real) := (real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0))).
Definition term284 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_neg (real_sub x0 x1)).
Definition term301 (x0 : real) := real_add (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0).
Definition term223 (x0 : real) := real_add (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0).
Definition term20 (x0 : real) (x1 : real) := real_add (real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x0) (real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x1).
Definition term56 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_neg (real_of_num x1)).
Definition term170 (x0 : real) (x1 : real) := (fun y0 : real => ((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) y0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_add x1 y0)) (real_of_num (NUMERAL 0))))) (real_neg (real_sub x0 x1)).
Definition term191 (x0 : real) (x1 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term393 (x0 : real) (x1 : real) := (fun y0 : real => (exists y1 : real, (real_le x0 y1) /\ (real_le y1 y0)) -> real_le x0 y0) x1.
Definition term421 (x0 : real) := (fun y0 : real => real_le y0 y0) x0.
Definition term424 (x0 : real) := real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0))).
Definition term334 := real_add (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term291 (x0 : real) (x1 : real) := real_gt (real_add x0 (real_add x1 (real_neg (real_sub x0 x1)))) (real_of_num (NUMERAL 0)).
Definition term149 (x0 : real) (x1 : real) := real_gt (real_add x0 (real_add x1 (real_abs (real_sub x0 x1)))) (real_of_num (NUMERAL 0)).
Definition term350 (x0 : real) (x1 : real) (x2 : real) := ((real_le (real_of_num (NUMERAL 0)) x1) /\ (real_le x0 x2)) -> real_le (real_mul x1 x0) (real_mul x1 x2).
Definition term31 (x0 : real) (x1 : real) := real_add (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul x0 x1)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term363 (x0 : real) (x1 : real) := (fun y0 : real => (real_le (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) y0) -> real_le x0 (sqrt y0)) x1.
Definition term99 (x0 : real) := forall y0 : real, (real_abs (real_mul x0 y0)) = (real_mul (real_abs x0) (real_abs y0)).
Definition term128 (x0 : real) (x1 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_add x0 x1)).
Definition term224 (x0 : real) (x1 : real) := real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_sub x0 x1))).
Definition term372 (x0 : real) (x1 : real) := real_mul (real_abs (real_sub (sqrt x0) (sqrt x1))) (real_abs (real_sub (sqrt x0) (sqrt x1))).
Definition term59 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term12 (x0 : real) (x1 : real) := real_mul x0 (real_add x0 x1).
Definition term62 := real_of_num (NUMERAL (BIT1 0)).
Definition term50 (x0 : real) (x1 : real) := real_sub (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term381 (x0 : real) (x1 : real) := forall y0 : real, ((real_le x1 x0) /\ (real_le x0 y0)) -> real_le x1 y0.
Definition term251 (x0 : real) := real_add (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0).
Definition term229 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0).
Definition term157 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term281 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_neg (real_sub x0 x1))).
Definition term207 := BIT0 (BIT1 0).
Definition term47 (x0 : real) (x1 : real) := real_sub (real_mul (real_sub x0 x1) (real_add x0 x1)).
Definition term0 (x0 : real) (x1 : real) := ~ ((real_mul (real_sub x0 x1) (real_add x0 x1)) = (real_sub (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term172 (x0 : real) (x1 : real) := and (real_gt (real_of_num (NUMERAL 0)) (real_sub x0 x1)).
Definition term221 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term49 (x0 : real) (x1 : real) := real_sub (real_mul (real_sub x0 x1) (real_add x0 x1)) (real_sub (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term183 (x0 : real) (x1 : real) := @eq Prop (((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_abs (real_sub x0 x1)))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_add x1 (real_abs (real_sub x0 x1)))) (real_of_num (NUMERAL 0))))).
Definition term272 (x0 : real) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) x0.
Definition term133 (x0 : real) (x1 : real) := and ((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))).
Definition term419 (x0 : real) (x1 : real) := real_le (real_mul (real_abs (real_sub (sqrt x0) (sqrt x1))) (real_abs (real_add (sqrt x0) (sqrt x1)))) (real_abs (real_sub x0 x1)).
Definition term376 (x0 : real) (x1 : real) := real_le (real_mul (real_abs (real_sub (sqrt x0) (sqrt x1))) (real_abs (real_sub (sqrt x0) (sqrt x1)))) (real_abs (real_sub x0 x1)).
Definition term74 (x0 : real) := real_add (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term68 (x0 : real) (x1 : real) := real_add (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term384 (x0 : real) (x1 : real) (x2 : real) := (real_le x0 x1) /\ (real_le x1 x2).
Definition term369 (x0 : real) (x1 : real) := (real_le (real_pow (real_abs (real_sub (sqrt x0) (sqrt x1))) (NUMERAL (BIT0 (BIT1 0)))) (real_abs (real_sub x0 x1))) -> real_le (real_abs (real_sub (sqrt x0) (sqrt x1))) (sqrt (real_abs (real_sub x0 x1))).
Definition term52 (x0 : real) (x1 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term161 (x0 : real) (x1 : real) := real_gt (real_add (real_abs (real_sub x0 x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x0 x1))) (real_of_num (NUMERAL 0)).
Definition term148 (x0 : real) (x1 : real) := real_gt (real_add (real_abs (real_sub x0 x1)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 x1))) (real_of_num (NUMERAL 0)).
Definition term418 (x0 : real) (x1 : real) := real_le (real_abs (real_sub (real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (sqrt x1) (NUMERAL (BIT0 (BIT1 0)))))).
Definition term84 (x0 : real) (x1 : real) := real_gt (real_neg (real_sub (real_mul (real_sub x0 x1) (real_add x0 x1)) (real_sub (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))))) (real_of_num (NUMERAL 0)).
Definition term87 (x0 : real) (x1 : real) := real_gt (real_sub (real_mul (real_sub x0 x1) (real_add x0 x1)) (real_sub (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term96 (x0 : real) (x1 : real) := real_mul (real_abs x0) (real_abs x1).
Definition term267 (x0 : real) (x1 : real) := real_sub (real_of_num (NUMERAL 0)) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term290 (x0 : real) (x1 : real) := real_gt (real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_neg (real_sub x0 x1)))) (real_of_num (NUMERAL 0))).
Definition term231 (x0 : real) (x1 : real) := real_gt (real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_sub x0 x1))) (real_of_num (NUMERAL 0))).
Definition term292 (x0 : real) (x1 : real) := real_gt (real_sub (real_add x0 (real_add x1 (real_neg (real_sub x0 x1)))) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term280 (x0 : real) (x1 : real) := real_gt (real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_neg (real_sub x0 x1)))) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term235 (x0 : real) (x1 : real) := real_gt (real_sub (real_add x0 (real_add x1 (real_sub x0 x1))) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term197 (x0 : real) (x1 : real) := real_gt (real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_sub x0 x1))) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term362 (x0 : real) := forall y0 : real, (real_le (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) y0) -> real_le x0 (sqrt y0).
Definition term332 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0).
Definition term202 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term261 (x0 : real) (x1 : real) := and (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))).
Definition term176 (x0 : real) (x1 : real) := ((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_sub x0 x1))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_add x1 (real_sub x0 x1))) (real_of_num (NUMERAL 0)))).
Definition term171 (x0 : real) (x1 : real) := ((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_neg (real_sub x0 x1)))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_add x1 (real_neg (real_sub x0 x1)))) (real_of_num (NUMERAL 0)))).
Definition term166 (x0 : real) (x1 : real) := ((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_abs (real_sub x0 x1)))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_add x1 (real_abs (real_sub x0 x1)))) (real_of_num (NUMERAL 0)))).
Definition term210 := real_of_num (Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term282 (x0 : real) (x1 : real) := real_neg (real_sub x0 x1).
Definition term89 := or (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term15 (x0 : real) := real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term43 (x0 : real) (x1 : real) := real_mul (real_of_num (NUMERAL 0)) (real_mul x0 x1).
Definition term57 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term144 (x0 : real) (x1 : real) := real_add x1 (real_abs (real_sub x0 x1)).
Definition term82 (x0 : real) (x1 : real) := real_gt (real_neg (real_sub (real_mul (real_sub x0 x1) (real_add x0 x1)) (real_sub (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))))).
Definition term411 (x0 : real) (x1 : real) := real_mul (real_abs (real_sub (sqrt x0) (sqrt x1))) (real_abs (real_add (sqrt x0) (sqrt x1))).
Definition term249 (x0 : real) := real_sub (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0)).
Definition term227 (x0 : real) := real_sub (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0)).
Definition term76 := real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term298 (x0 : real) (x1 : real) := real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x1)).
Definition term305 (x0 : real) (x1 : real) := and (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_neg (real_sub x0 x1)))) (real_of_num (NUMERAL 0))).
Definition term256 (x0 : real) (x1 : real) := and (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_sub x0 x1))) (real_of_num (NUMERAL 0))).
Definition term164 (x0 : real) (x1 : real) := and (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_abs (real_sub x0 x1)))) (real_of_num (NUMERAL 0))).
Definition term163 (x0 : real) (x1 : real) := and (real_gt (real_add (real_abs (real_sub x0 x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x0 x1))) (real_of_num (NUMERAL 0))).
Definition term124 (x0 : real) (x1 : real) := real_abs (real_add x0 x1).
Definition term107 (x0 : real) (x1 : real) := ~ (((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) x1)) -> real_le (real_abs (real_sub x0 x1)) (real_abs (real_add x0 x1))).
Definition term302 (x0 : real) (x1 : real) := real_sub (real_add x0 (real_add x1 (real_neg (real_sub x0 x1)))).
Definition term239 (x0 : real) (x1 : real) := real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term237 (x0 : real) (x1 : real) := real_add x1 (real_sub x0 x1).
Definition term285 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term255 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0)).
Definition term233 (x0 : real) := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0)).
Definition term186 (x0 : real) (x1 : real) := real_sub (real_sub x0 x1).
Definition term7 (x0 : real) (x1 : real) := real_mul (real_sub x0 x1).
Definition term269 (x0 : real) (x1 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term336 (x0 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0)).
Definition term279 (x0 : real) (x1 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_neg (real_sub x0 x1)))) (real_of_num (NUMERAL 0)).
Definition term162 (x0 : real) (x1 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_abs (real_sub x0 x1)))) (real_of_num (NUMERAL 0)).
Definition term199 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_sub x0 x1).
Definition term140 (x0 : real) (x1 : real) := real_add (real_abs (real_sub x0 x1)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 x1)).
Definition term216 (x0 : real) (x1 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x1).
Definition term6 (x0 : real) (x1 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term55 (x0 : real) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term39 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term234 (x0 : real) (x1 : real) := real_gt (real_add x0 (real_add x1 (real_sub x0 x1))) (real_of_num (NUMERAL 0)).
Definition term365 (x0 : real) (x1 : real) := real_le (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) x1.
Definition term167 (x0 : real) (x1 : real) := (fun y0 : real => ((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) y0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_add x1 y0)) (real_of_num (NUMERAL 0))))) (real_abs (real_sub x0 x1)).
Definition term322 (x0 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))).
Definition term54 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term217 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x1)).
Definition term45 := real_add (real_of_num (NUMERAL 0)).
Definition term81 (x0 : real) (x1 : real) := @eq real (real_neg (real_sub (real_mul (real_sub x0 x1) (real_add x0 x1)) (real_sub (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))))).
Definition term116 (x0 : real) := real_ge (real_sub x0 (real_of_num (NUMERAL 0))).
Definition term378 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) x0.
Definition term357 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y0 y2)) -> real_le (real_mul y1 y0) (real_mul y1 y2)) x0.
Definition term345 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y1 y2)) -> real_le (real_mul y0 y1) (real_mul y0 y2)) x0.
Definition term112 (x0 : real) := real_ge (real_sub x0 (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term330 (x0 : real) := ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) -> real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term324 (x0 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0)))) -> real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0)) (real_of_num (NUMERAL 0)).
Definition term425 (x0 : real) := real_sub (real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))).
Definition term278 (x0 : real) (x1 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)).
Definition term270 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term28 (x0 : real) (x1 : real) := real_add (real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term304 (x0 : real) (x1 : real) := real_gt (real_sub (real_add x0 (real_add x1 (real_neg (real_sub x0 x1)))) (real_of_num (NUMERAL 0))).
Definition term253 (x0 : real) (x1 : real) := real_gt (real_sub (real_add x0 (real_add x1 (real_sub x0 x1))) (real_of_num (NUMERAL 0))).
Definition term155 (x0 : real) (x1 : real) := real_add (real_abs (real_sub x0 x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term40 := NUMERAL (BIT1 0).
Definition term283 (x0 : real) (x1 : real) := real_neg (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term329 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term323 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_gt x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term309 (x0 : real) (x1 : real) := (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ (((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) /\ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x1) (real_of_num (NUMERAL 0))))).
Definition term240 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term427 (x0 : real) (x1 : real) := real_le (real_abs (real_sub x0 x1)) (real_abs (real_sub x0 x1)).
Definition term319 := real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term102 := fun y0 : real => forall y1 : real, (real_mul (real_abs y0) (real_abs y1)) = (real_abs (real_mul y0 y1)).
Definition term16 (x0 : real) (x1 : real) := real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul x0 x1).
Definition term409 (x0 : real) (x1 : real) := (real_le (real_of_num (NUMERAL 0)) (sqrt x0)) /\ (real_le (real_of_num (NUMERAL 0)) (sqrt x1)).
Definition term184 (x0 : real) (x1 : real) := real_ge (real_sub x0 x1) (real_of_num (NUMERAL 0)).
Definition term83 := real_gt (real_of_num (NUMERAL 0)).
Definition term70 (x0 : real) (x1 : real) := real_add (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term69 (x0 : real) (x1 : real) := real_add (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))).
