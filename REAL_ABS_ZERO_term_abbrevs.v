Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term147 (x0 : real) := fun y0 : real => (y0 = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term227 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term244 (x0 : real) := @eq real (real_mul (real_of_num (NUMERAL (BIT1 0))) x0).
Definition term137 (x0 : real) := @eq real (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term3 (x0 : real -> Prop) := ~ (all x0).
Definition term221 (x0 : real) := (((real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) = (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))) -> real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_of_num (NUMERAL 0)).
Definition term214 (x0 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))) -> real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) x0) (real_of_num (NUMERAL 0)).
Definition term256 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term115 (x0 : real) := (real_ge x0 (real_of_num (NUMERAL 0))) /\ ((x0 = (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))).
Definition term133 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term241 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term2 := real_of_num (NUMERAL 0).
Definition term65 (x0 : real) := or (((real_abs x0) = (real_of_num (NUMERAL 0))) /\ (~ (x0 = (real_of_num (NUMERAL 0))))).
Definition term260 (x0 : real) := @eq real (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term13 (x0 : real) := real_sub (real_abs x0) (real_of_num (NUMERAL 0)).
Definition term49 (x0 : real) := real_gt (real_neg (real_sub (real_abs x0) (real_of_num (NUMERAL 0)))).
Definition term149 (x0 : real) := ((real_neg x0) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term145 (x0 : real) := ((real_abs x0) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term243 (x0 : real) := (fun y0 : real => (real_mul y0 x0) = (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term158 (x0 : real) := ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((x0 = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_of_num (NUMERAL 0)) x0) /\ (((real_neg x0) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))))).
Definition term151 (x0 : real) := (real_gt (real_of_num (NUMERAL 0)) x0) /\ (((real_neg x0) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))).
Definition term205 (x0 : real) := (((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0)))))) \/ (((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))) /\ (x0 = (real_of_num (NUMERAL 0)))).
Definition term71 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term217 (x0 : real) := forall y0 : real, (real_mul y0 x0) = (real_of_num (NUMERAL 0)).
Definition term207 (x0 : real) := ((((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((x0 = (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (((real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) = (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))))) \/ (((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((x0 = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (((real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))))))) \/ ((((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0)))))) \/ (((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))) /\ (x0 = (real_of_num (NUMERAL 0))))).
Definition term99 (x0 : real) := ((((real_abs x0) = (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))) \/ (((real_abs x0) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))))) \/ (((real_gt (real_abs x0) (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0)) (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0))))).
Definition term249 (x0 : real) := (fun y0 : real => (real_mul y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) = (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term38 (x0 : real) := or (real_gt x0 (real_of_num (NUMERAL 0))).
Definition term177 (x0 : real) := (real_gt x0 (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0))).
Definition term160 (x0 : real) := real_gt (real_sub (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term5 := ~ (forall y0 : real, ((real_abs y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0)))).
Definition term130 (x0 : real) := real_sub (real_neg x0).
Definition term234 (x0 : real) := ((real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) = (real_of_num (NUMERAL 0))) -> forall y0 : real, (real_mul y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) = (real_of_num (NUMERAL 0)).
Definition term105 (x0 : real) := fun y0 : real => (y0 = (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0))).
Definition term92 := exists y0 : real, ((real_gt (real_abs y0) (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y0)) (real_of_num (NUMERAL 0)))) /\ (y0 = (real_of_num (NUMERAL 0))).
Definition term125 (x0 : real) := real_gt (real_sub (real_of_num (NUMERAL 0)) x0) (real_of_num (NUMERAL 0)).
Definition term188 (x0 : real) := and (real_gt (real_neg x0) (real_of_num (NUMERAL 0))).
Definition term60 (x0 : real) := @eq real (real_sub x0 (real_of_num (NUMERAL 0))).
Definition term204 (x0 : real) := or (((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0)))))).
Definition term166 (x0 : real) := or (((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((x0 = (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (((real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) = (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))))).
Definition term218 (x0 : real) := (fun y0 : real => (real_mul y0 x0) = (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term124 (x0 : real) := real_gt (real_of_num (NUMERAL 0)) x0.
Definition term120 (x0 : real) := real_ge x0 (real_of_num (NUMERAL 0)).
Definition term199 (x0 : real) := and (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0)) (real_of_num (NUMERAL 0))).
Definition term14 (x0 : real) := real_add (real_abs x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term42 (x0 : real) := ((real_abs x0) = (real_of_num (NUMERAL 0))) /\ ((real_gt x0 (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))).
Definition term34 (x0 : real) := real_gt (real_sub x0 (real_of_num (NUMERAL 0))).
Definition term175 (x0 : real) := (real_gt (real_of_num (NUMERAL 0)) x0) /\ ((real_gt (real_neg x0) (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0)))).
Definition term131 (x0 : real) := real_sub (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term135 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)).
Definition term245 (x0 : real) := ((x0 = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) -> real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term59 (x0 : real) := (real_gt (real_abs x0) (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0)) (real_of_num (NUMERAL 0))).
Definition term113 (x0 : real) := and (real_ge x0 (real_of_num (NUMERAL 0))).
Definition term136 (x0 : real) := @eq real (real_sub (real_neg x0) (real_of_num (NUMERAL 0))).
Definition term26 (x0 : real) := real_add x0 (real_of_num (NUMERAL 0)).
Definition term35 (x0 : real) := real_gt (real_sub x0 (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term186 (x0 : real) := real_gt (real_sub (real_neg x0) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term55 (x0 : real) := real_gt (real_sub (real_abs x0) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term164 (x0 : real) := ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((x0 = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (((real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))))).
Definition term41 (x0 : real) := ((real_abs x0) = (real_of_num (NUMERAL 0))) /\ (~ (x0 = (real_of_num (NUMERAL 0)))).
Definition term172 (x0 : real) := (fun y0 : real => (real_gt y0 (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0)))) (real_neg x0).
Definition term106 (x0 : real) := (fun y0 : real => (y0 = (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))) (real_neg x0).
Definition term210 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term262 := ((~ (forall y0 : real, ((real_abs y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0))))) -> False) -> forall y0 : real, ((real_abs y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0))).
Definition term128 (x0 : real) := real_gt (real_sub (real_of_num (NUMERAL 0)) x0).
Definition term91 := exists y0 : real, (fun y1 : real => ((real_gt (real_abs y1) (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y1)) (real_of_num (NUMERAL 0)))) /\ (y1 = (real_of_num (NUMERAL 0)))) y0.
Definition term86 := exists y0 : real, (fun y1 : real => ((real_abs y1) = (real_of_num (NUMERAL 0))) /\ ((real_gt y1 (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_of_num (NUMERAL 0))))) y0.
Definition term163 (x0 : real) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (((real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))).
Definition term167 (x0 : real) := (((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((x0 = (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (((real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) = (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))))) \/ (((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((x0 = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (((real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))))).
Definition term15 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term45 (x0 : real) := real_neg (real_sub (real_abs x0) (real_of_num (NUMERAL 0))).
Definition term250 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term142 (x0 : real) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (((real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) = (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))).
Definition term254 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term238 (x0 : real) := @eq real (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term88 := or (exists y0 : real, (fun y1 : real => ((real_abs y1) = (real_of_num (NUMERAL 0))) /\ ((real_gt y1 (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_of_num (NUMERAL 0))))) y0).
Definition term24 (x0 : real) := real_sub x0 (real_of_num (NUMERAL 0)).
Definition term171 (x0 : real) := fun y0 : real => (real_gt y0 (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0))).
Definition term32 (x0 : real) := real_gt (real_neg (real_sub x0 (real_of_num (NUMERAL 0)))) (real_of_num (NUMERAL 0)).
Definition term50 (x0 : real) := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0)).
Definition term162 (x0 : real) := ((real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term237 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term236 (x0 : real) := (fun y0 : real => (real_mul y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) = (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term119 (x0 : real) := @eq Prop (((real_abs x0) = (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))).
Definition term22 (x0 : real) := ~ (x0 = (real_of_num (NUMERAL 0))).
Definition term129 (x0 : real) := real_sub (real_neg x0) (real_of_num (NUMERAL 0)).
Definition term6 := exists y0 : real, ~ ((fun y1 : real => ((real_abs y1) = (real_of_num (NUMERAL 0))) = (y1 = (real_of_num (NUMERAL 0)))) y0).
Definition term97 (x0 : real) := (((real_abs x0) = (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))) \/ (((real_abs x0) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))).
Definition term76 := fun y0 : real => ((real_abs y0) = (real_of_num (NUMERAL 0))) /\ ((real_gt y0 (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0)))).
Definition term25 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term190 (x0 : real) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0)))).
Definition term187 (x0 : real) := real_gt (real_sub (real_neg x0) (real_of_num (NUMERAL 0))).
Definition term56 (x0 : real) := real_gt (real_abs x0) (real_of_num (NUMERAL 0)).
Definition term37 (x0 : real) := or (real_gt (real_sub x0 (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0))).
Definition term138 (x0 : real) := and ((real_neg x0) = (real_of_num (NUMERAL 0))).
Definition term225 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term257 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term193 (x0 : real) (x1 : real) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) x0) x1).
Definition term48 (x0 : real) := @eq real (real_neg (real_sub (real_abs x0) (real_of_num (NUMERAL 0)))).
Definition term44 (x0 : real) := (real_gt (real_sub (real_abs x0) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub (real_abs x0) (real_of_num (NUMERAL 0)))) (real_of_num (NUMERAL 0))).
Definition term23 (x0 : real) := (real_gt (real_sub x0 (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub x0 (real_of_num (NUMERAL 0)))) (real_of_num (NUMERAL 0))).
Definition term72 (x0 : real -> Prop) (x1 : real -> Prop) := exists y0 : real, (x0 y0) \/ (x1 y0).
Definition term93 := (exists y0 : real, ((real_abs y0) = (real_of_num (NUMERAL 0))) /\ ((real_gt y0 (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0))))) \/ (exists y0 : real, ((real_gt (real_abs y0) (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y0)) (real_of_num (NUMERAL 0)))) /\ (y0 = (real_of_num (NUMERAL 0)))).
Definition term233 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term16 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term52 (x0 : real) := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0)) (real_of_num (NUMERAL 0)).
Definition term29 (x0 : real) := @eq real (real_neg (real_sub x0 (real_of_num (NUMERAL 0)))).
Definition term139 (x0 : real) := and ((real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) = (real_of_num (NUMERAL 0))).
Definition term0 (x0 : real) := ~ (((real_abs x0) = (real_of_num (NUMERAL 0))) = (x0 = (real_of_num (NUMERAL 0)))).
Definition term170 (x0 : real) := ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((fun y0 : real => (real_gt y0 (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0)))) x0)) \/ ((real_gt (real_of_num (NUMERAL 0)) x0) /\ ((fun y0 : real => (real_gt y0 (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0)))) (real_neg x0))).
Definition term146 (x0 : real) := ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((fun y0 : real => (y0 = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) x0)) \/ ((real_gt (real_of_num (NUMERAL 0)) x0) /\ ((fun y0 : real => (y0 = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) (real_neg x0))).
Definition term104 (x0 : real) := ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((fun y0 : real => (y0 = (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))) x0)) \/ ((real_gt (real_of_num (NUMERAL 0)) x0) /\ ((fun y0 : real => (y0 = (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))) (real_neg x0))).
Definition term206 (x0 : real) := or ((((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((x0 = (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (((real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) = (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))))) \/ (((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((x0 = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (((real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))))))).
Definition term36 (x0 : real) := real_gt x0 (real_of_num (NUMERAL 0)).
Definition term11 := fun y0 : real => (((real_abs y0) = (real_of_num (NUMERAL 0))) /\ (~ (y0 = (real_of_num (NUMERAL 0))))) \/ ((~ ((real_abs y0) = (real_of_num (NUMERAL 0)))) /\ (y0 = (real_of_num (NUMERAL 0)))).
Definition term73 (x0 : real -> Prop) (x1 : real -> Prop) := (exists y0 : real, x0 y0) \/ (exists y0 : real, x1 y0).
Definition term96 (x0 : real) := ((real_gt (real_abs x0) (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0)) (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0)))).
Definition term232 := real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term40 (x0 : real) := and ((real_abs x0) = (real_of_num (NUMERAL 0))).
Definition term195 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term157 (x0 : real) := or ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((x0 = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))))).
Definition term68 := fun y0 : real => (((real_abs y0) = (real_of_num (NUMERAL 0))) /\ ((real_gt y0 (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0))))) \/ (((real_gt (real_abs y0) (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y0)) (real_of_num (NUMERAL 0)))) /\ (y0 = (real_of_num (NUMERAL 0)))).
Definition term43 (x0 : real) := ~ ((real_abs x0) = (real_of_num (NUMERAL 0))).
Definition term223 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0.
Definition term80 (x0 : real) := (fun y0 : real => ((real_gt (real_abs y0) (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y0)) (real_of_num (NUMERAL 0)))) /\ (y0 = (real_of_num (NUMERAL 0)))) x0.
Definition term61 (x0 : real) := and (~ ((real_abs x0) = (real_of_num (NUMERAL 0)))).
Definition term7 := fun y0 : real => ((real_abs y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0))).
Definition term258 := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term184 (x0 : real) := and (real_gt x0 (real_of_num (NUMERAL 0))).
Definition term84 := @eq Prop (exists y0 : real, (((real_abs y0) = (real_of_num (NUMERAL 0))) /\ ((real_gt y0 (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0))))) \/ (((real_gt (real_abs y0) (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y0)) (real_of_num (NUMERAL 0)))) /\ (y0 = (real_of_num (NUMERAL 0))))).
Definition term83 := @eq Prop (exists y0 : real, ((fun y1 : real => ((real_abs y1) = (real_of_num (NUMERAL 0))) /\ ((real_gt y1 (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_of_num (NUMERAL 0))))) y0) \/ ((fun y1 : real => ((real_gt (real_abs y1) (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y1)) (real_of_num (NUMERAL 0)))) /\ (y1 = (real_of_num (NUMERAL 0)))) y0)).
Definition term62 (x0 : real) := and ((real_gt (real_abs x0) (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0)) (real_of_num (NUMERAL 0)))).
Definition term242 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term30 (x0 : real) := real_gt (real_neg (real_sub x0 (real_of_num (NUMERAL 0)))).
Definition term178 (x0 : real) := (real_ge x0 (real_of_num (NUMERAL 0))) /\ ((fun y0 : real => (real_gt y0 (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0)))) x0).
Definition term154 (x0 : real) := (real_ge x0 (real_of_num (NUMERAL 0))) /\ ((fun y0 : real => (y0 = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) x0).
Definition term114 (x0 : real) := (real_ge x0 (real_of_num (NUMERAL 0))) /\ ((fun y0 : real => (y0 = (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))) x0).
Definition term67 (x0 : real) := (((real_abs x0) = (real_of_num (NUMERAL 0))) /\ ((real_gt x0 (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))))) \/ (((real_gt (real_abs x0) (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0)) (real_of_num (NUMERAL 0)))) /\ (x0 = (real_of_num (NUMERAL 0)))).
Definition term4 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term21 (x0 : real) := @eq real (real_abs x0).
Definition term51 (x0 : real) := real_gt (real_neg (real_sub (real_abs x0) (real_of_num (NUMERAL 0)))) (real_of_num (NUMERAL 0)).
Definition term208 (x0 : nat) (x1 : nat) := real_gt (real_of_num x0) (real_of_num x1).
Definition term203 (x0 : real) := or ((real_gt (real_abs x0) (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0)))).
Definition term211 := S (Nat.add 0 0).
Definition term224 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term191 (x0 : real) := ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0))))).
Definition term143 (x0 : real) := ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((x0 = (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (((real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) = (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0))))).
Definition term181 (x0 : real) := or ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0))))).
Definition term117 (x0 : real) := or ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((x0 = (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0))))).
Definition term148 (x0 : real) := (fun y0 : real => (y0 = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) (real_neg x0).
Definition term219 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term261 := (~ (forall y0 : real, ((real_abs y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0))))) -> False.
Definition term77 := fun y0 : real => ((real_gt (real_abs y0) (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y0)) (real_of_num (NUMERAL 0)))) /\ (y0 = (real_of_num (NUMERAL 0))).
Definition term176 (x0 : real) := (fun y0 : real => (real_gt y0 (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0)))) x0.
Definition term98 (x0 : real) := or ((((real_abs x0) = (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))) \/ (((real_abs x0) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))))).
Definition term174 (x0 : real) := (real_gt (real_of_num (NUMERAL 0)) x0) /\ ((fun y0 : real => (real_gt y0 (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0)))) (real_neg x0)).
Definition term150 (x0 : real) := (real_gt (real_of_num (NUMERAL 0)) x0) /\ ((fun y0 : real => (y0 = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) (real_neg x0)).
Definition term109 (x0 : real) := (real_gt (real_of_num (NUMERAL 0)) x0) /\ ((fun y0 : real => (y0 = (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))) (real_neg x0)).
Definition term141 (x0 : real) := and (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term107 (x0 : real) := ((real_neg x0) = (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0))).
Definition term103 (x0 : real) := ((real_abs x0) = (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0))).
Definition term1 (x0 : real) := (((real_abs x0) = (real_of_num (NUMERAL 0))) /\ (~ (x0 = (real_of_num (NUMERAL 0))))) \/ ((~ ((real_abs x0) = (real_of_num (NUMERAL 0)))) /\ (x0 = (real_of_num (NUMERAL 0)))).
Definition term185 (x0 : real) := real_gt (real_neg x0) (real_of_num (NUMERAL 0)).
Definition term53 (x0 : real) := real_gt (real_sub (real_abs x0) (real_of_num (NUMERAL 0))).
Definition term228 := real_mul (real_of_num (NUMERAL 0)).
Definition term159 (x0 : real) := @eq Prop (((real_abs x0) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))).
Definition term192 (x0 : real) (x1 : real) := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0)) x1.
Definition term196 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) x0).
Definition term31 (x0 : real) := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term200 (x0 : real) := and ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))).
Definition term28 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term126 (x0 : real) := real_sub (real_of_num (NUMERAL 0)) x0.
Definition term39 (x0 : real) := (real_gt x0 (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term47 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0).
Definition term194 (x0 : real) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) x0) (real_of_num (NUMERAL 0))).
Definition term259 := real_mul (real_of_num (NUMERAL (BIT1 0))).
Definition term82 := fun y0 : real => ((fun y1 : real => ((real_abs y1) = (real_of_num (NUMERAL 0))) /\ ((real_gt y1 (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_of_num (NUMERAL 0))))) y0) \/ ((fun y1 : real => ((real_gt (real_abs y1) (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y1)) (real_of_num (NUMERAL 0)))) /\ (y1 = (real_of_num (NUMERAL 0)))) y0).
Definition term78 (x0 : real) := (fun y0 : real => ((real_abs y0) = (real_of_num (NUMERAL 0))) /\ ((real_gt y0 (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0))))) x0.
Definition term74 := exists y0 : real, ((fun y1 : real => ((real_abs y1) = (real_of_num (NUMERAL 0))) /\ ((real_gt y1 (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_of_num (NUMERAL 0))))) y0) \/ ((fun y1 : real => ((real_gt (real_abs y1) (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y1)) (real_of_num (NUMERAL 0)))) /\ (y1 = (real_of_num (NUMERAL 0)))) y0).
Definition term87 := exists y0 : real, ((real_abs y0) = (real_of_num (NUMERAL 0))) /\ ((real_gt y0 (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0)))).
Definition term64 (x0 : real) := ((real_gt (real_abs x0) (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0)) (real_of_num (NUMERAL 0)))) /\ (x0 = (real_of_num (NUMERAL 0))).
Definition term140 (x0 : real) := ((real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) = (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0))).
Definition term248 (x0 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term179 (x0 : real) := (real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0)))).
Definition term127 (x0 : real) := real_add (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term165 (x0 : real) := or (((real_abs x0) = (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))).
Definition term81 (x0 : real) := ((fun y0 : real => ((real_abs y0) = (real_of_num (NUMERAL 0))) /\ ((real_gt y0 (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0))))) x0) \/ ((fun y0 : real => ((real_gt (real_abs y0) (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y0)) (real_of_num (NUMERAL 0)))) /\ (y0 = (real_of_num (NUMERAL 0)))) x0).
Definition term182 (x0 : real) := ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_of_num (NUMERAL 0)) x0) /\ ((real_gt (real_neg x0) (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0))))).
Definition term118 (x0 : real) := ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((x0 = (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_of_num (NUMERAL 0)) x0) /\ (((real_neg x0) = (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0))))).
Definition term252 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_neg (real_of_num x1)).
Definition term183 (x0 : real) := @eq Prop ((real_gt (real_abs x0) (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0)))).
Definition term58 (x0 : real) := or (real_gt (real_abs x0) (real_of_num (NUMERAL 0))).
Definition term255 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term66 (x0 : real) := or (((real_abs x0) = (real_of_num (NUMERAL 0))) /\ ((real_gt x0 (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))))).
Definition term46 (x0 : real) := real_neg (real_abs x0).
Definition term215 := real_of_num (NUMERAL (BIT1 0)).
Definition term134 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term202 (x0 : real) := ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))) /\ (x0 = (real_of_num (NUMERAL 0))).
Definition term57 (x0 : real) := or (real_gt (real_sub (real_abs x0) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0))).
Definition term246 (x0 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term90 := fun y0 : real => (fun y1 : real => ((real_gt (real_abs y1) (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y1)) (real_of_num (NUMERAL 0)))) /\ (y1 = (real_of_num (NUMERAL 0)))) y0.
Definition term85 := fun y0 : real => (fun y1 : real => ((real_abs y1) = (real_of_num (NUMERAL 0))) /\ ((real_gt y1 (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_of_num (NUMERAL 0))))) y0.
Definition term180 (x0 : real) := or ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((fun y0 : real => (real_gt y0 (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0)))) x0)).
Definition term156 (x0 : real) := or ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((fun y0 : real => (y0 = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) x0)).
Definition term116 (x0 : real) := or ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((fun y0 : real => (y0 = (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))) x0)).
Definition term27 (x0 : real) := real_neg (real_sub x0 (real_of_num (NUMERAL 0))).
Definition term263 := forall y0 : real, ((real_abs y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0))).
Definition term229 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term18 (x0 : real) := real_add (real_abs x0).
Definition term19 (x0 : real) := real_add (real_abs x0) (real_of_num (NUMERAL 0)).
Definition term251 (x0 : real) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) x0.
Definition term230 (x0 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0).
Definition term222 (x0 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_of_num (NUMERAL 0)).
Definition term173 (x0 : real) := (real_gt (real_neg x0) (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0))).
Definition term169 (x0 : real) := (real_gt (real_abs x0) (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0))).
Definition term9 (x0 : real) := ~ ((fun y0 : real => ((real_abs y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0)))) x0).
Definition term235 (x0 : real) := forall y0 : real, (real_mul y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) = (real_of_num (NUMERAL 0)).
Definition term10 := fun y0 : real => ~ ((fun y1 : real => ((real_abs y1) = (real_of_num (NUMERAL 0))) = (y1 = (real_of_num (NUMERAL 0)))) y0).
Definition term101 := exists y0 : real, ((((real_abs y0) = (real_of_num (NUMERAL 0))) /\ (real_gt y0 (real_of_num (NUMERAL 0)))) \/ (((real_abs y0) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0))))) \/ (((real_gt (real_abs y0) (real_of_num (NUMERAL 0))) /\ (y0 = (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y0)) (real_of_num (NUMERAL 0))) /\ (y0 = (real_of_num (NUMERAL 0))))).
Definition term69 := exists y0 : real, (((real_abs y0) = (real_of_num (NUMERAL 0))) /\ ((real_gt y0 (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0))))) \/ (((real_gt (real_abs y0) (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y0)) (real_of_num (NUMERAL 0)))) /\ (y0 = (real_of_num (NUMERAL 0)))).
Definition term12 := exists y0 : real, (((real_abs y0) = (real_of_num (NUMERAL 0))) /\ (~ (y0 = (real_of_num (NUMERAL 0))))) \/ ((~ ((real_abs y0) = (real_of_num (NUMERAL 0)))) /\ (y0 = (real_of_num (NUMERAL 0)))).
Definition term153 (x0 : real) := (x0 = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term155 (x0 : real) := (real_ge x0 (real_of_num (NUMERAL 0))) /\ ((x0 = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))).
Definition term108 (x0 : real) := and (real_gt (real_of_num (NUMERAL 0)) x0).
Definition term168 (x0 : real) := (fun y0 : real => (real_gt y0 (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0)))) (real_abs x0).
Definition term102 (x0 : real) := (fun y0 : real => (y0 = (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))) (real_abs x0).
Definition term189 (x0 : real) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0))).
Definition term253 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term79 (x0 : real) := or ((fun y0 : real => ((real_abs y0) = (real_of_num (NUMERAL 0))) /\ ((real_gt y0 (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0))))) x0).
Definition term123 (x0 : real) := and (x0 = (real_of_num (NUMERAL 0))).
Definition term20 (x0 : real) := @eq real (real_sub (real_abs x0) (real_of_num (NUMERAL 0))).
Definition term198 (x0 : real) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0))).
Definition term132 (x0 : real) := real_sub (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)).
Definition term216 (x0 : real) := (x0 = (real_of_num (NUMERAL 0))) -> forall y0 : real, (real_mul y0 x0) = (real_of_num (NUMERAL 0)).
Definition term112 (x0 : real) := (x0 = (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0))).
Definition term144 (x0 : real) := (fun y0 : real => (y0 = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) (real_abs x0).
Definition term197 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) x0) (real_of_num (NUMERAL 0)).
Definition term33 (x0 : real) := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)).
Definition term100 := fun y0 : real => ((((real_abs y0) = (real_of_num (NUMERAL 0))) /\ (real_gt y0 (real_of_num (NUMERAL 0)))) \/ (((real_abs y0) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0))))) \/ (((real_gt (real_abs y0) (real_of_num (NUMERAL 0))) /\ (y0 = (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y0)) (real_of_num (NUMERAL 0))) /\ (y0 = (real_of_num (NUMERAL 0))))).
Definition term201 (x0 : real) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0)) (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0))).
Definition term226 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term8 (x0 : real) := (fun y0 : real => ((real_abs y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0)))) x0.
Definition term54 (x0 : real) := real_gt (real_abs x0).
Definition term239 (x0 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term89 := or (exists y0 : real, ((real_abs y0) = (real_of_num (NUMERAL 0))) /\ ((real_gt y0 (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0))))).
Definition term122 (x0 : real) := real_ge (real_sub x0 (real_of_num (NUMERAL 0))).
Definition term70 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term121 (x0 : real) := real_ge (real_sub x0 (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term161 (x0 : real) := real_gt (real_sub (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term240 (x0 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) -> real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term152 (x0 : real) := (fun y0 : real => (y0 = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) x0.
Definition term212 (x0 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0))).
Definition term63 (x0 : real) := (~ ((real_abs x0) = (real_of_num (NUMERAL 0)))) /\ (x0 = (real_of_num (NUMERAL 0))).
Definition term17 := NUMERAL (BIT1 0).
Definition term75 := (exists y0 : real, (fun y1 : real => ((real_abs y1) = (real_of_num (NUMERAL 0))) /\ ((real_gt y1 (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_of_num (NUMERAL 0))))) y0) \/ (exists y0 : real, (fun y1 : real => ((real_gt (real_abs y1) (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y1)) (real_of_num (NUMERAL 0)))) /\ (y1 = (real_of_num (NUMERAL 0)))) y0).
Definition term220 (x0 : real) (x1 : real) := ((x0 = (real_of_num (NUMERAL 0))) /\ (real_gt x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term213 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_gt x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term247 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term209 := real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term111 (x0 : real) := (fun y0 : real => (y0 = (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))) x0.
Definition term110 (x0 : real) := (real_gt (real_of_num (NUMERAL 0)) x0) /\ (((real_neg x0) = (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))).
Definition term231 := real_gt (real_of_num (NUMERAL 0)).
Definition term95 := @eq Prop ((exists y0 : real, ((real_abs y0) = (real_of_num (NUMERAL 0))) /\ ((real_gt y0 (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0))))) \/ (exists y0 : real, ((real_gt (real_abs y0) (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y0)) (real_of_num (NUMERAL 0)))) /\ (y0 = (real_of_num (NUMERAL 0))))).
Definition term94 := @eq Prop ((exists y0 : real, (fun y1 : real => ((real_abs y1) = (real_of_num (NUMERAL 0))) /\ ((real_gt y1 (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_of_num (NUMERAL 0))))) y0) \/ (exists y0 : real, (fun y1 : real => ((real_gt (real_abs y1) (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y1)) (real_of_num (NUMERAL 0)))) /\ (y1 = (real_of_num (NUMERAL 0)))) y0)).
